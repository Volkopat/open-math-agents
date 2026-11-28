import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1_H1_R1_H2_R1

/-!
FAR nonhalting certificates for holeA 1 (write-1 transition at state 1 blank, hole at (1, 1)).
Every machine in this branch either halts at the missing (1, 1) entry within
107 steps or hits a leaf certified by a finite automaton invariant.
-/

namespace OMA.BB4HoleA1

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
   some ⟨2, 1, false⟩, none,
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
private theorem tv_0_0_3 : checkTree 4 (baseTable 0 0 3) 107 startPos 0 [51136422218208, 224859258915296, 431567445297632, 224859258915296, 150092468259296, 12845253756016041012839556785893446735444313571, 150092468259296, 275742580527299580474514617537106045667361237603577646981703390856216672148108320498148401691631973, 275742580527299580473628343683563733976123717498414759778917421366674900250870761322612180832622405, 275742580527299580473627914339720595107060430649333273336586670335257069815265631675452966096213829, 275742580527299580474957915469460187701654385989642535274446107277109047961260824793548225538826597, 275742580527299580473682441007799356442609196168078126083624773457471101640258798620768778717744965, 275742580527299580474514617537155615515179874767434570505886029076475344961064349460502852283802245, 124540760022735477788942223610178569393825238504607559414071821220122608916660505194738762642424111214403691666324416168319499959019935692578175132305683120074293936614183, 275742580527299580474956842108280087920915733191434481847750956978740816121640863105032775771759237, 275742580527299580474067241685052515790874547910369321851397388570186372557015159113945329040499333, 275742580527299580473635321359509745656182132600024846705625260130420636927889718431942761955598981, 137871292318092087499256115519162751517729534040929761586992105717330707769470677222495704093724005, 431567445035488, 12845253756021882346805408466975966581720371683, 431567445035488, 137871290263649797891087056128804870016022273012672334540996151450880685843270750289027533889923269, 431567445166560, 431567445166560, 431567445166560, 12845253756014093901517606225534862993152573923, 51136422218208, 265834218059235537506082906778547720171301473363880697894523456802250167452037839785939610215208152452, 249081520052390671618669554392016087839965381189084606797959610361388810890184539635239912736227347772742012117977236040604560843385781591966377178992468749627048558848807, 249081520052390671618669554392016087817251671058813106238071697634760020713563930263142795752141107809992692766276224997490053414994725771300660588953099751249461172497191, 249081520052720181906355823658335219089678143130632239749179692912642018571697118421447609264638967885575169789454677048801572632871336585151339333973685211235092532296487, 265783403364727454827494188309494632949222383642869943814098266465216746085639532012064426181672728644, 398658885390295171482403377922040161510041343811073001625362148644261617859220171191950375586701408324, 265783403364727454827494188309507735483302618853810151983430558005724133737828886730290242536253847620, 265783403364727454827494188309507735483302618853810151983430558005724133737828886730290242536253847620, 265899098668354856614116907810431646938409384003634254265071375781059365045797665999584641958278297508, 275742578593706851719652727386911615948204133897056302232608032540727802145174214793478175126069605, 137871292197242555457847221823461661980127967283421619377497504692760873214771702599521051187870373, 267632504629437842963345219817105098059176003427230138115339732319893307622343833365809343364334789, 145981366161511564213322982207804523301385703307186762925830699428645486721305076308119468541202245, 265834218059235537506082028341044648448322688715044047085838096060249762479053300614613053285044809092, 275742580527299594880017025726685091797026825728374259924176746359094501153306142726944261433998469, 275742580527299594881335969940737362542816063628261003756913404048510240696160913206500559389998213, 266807300447059094033968827426352204500070764946368403033331911048357126340907791532263184714442173828, 282409058769719146602126285501768028501447401569956041553851580816461151323927193412931091260749805636, 265783403364727454827494188309494632949222383642869943814098266465216731345487475275923873134958508100, 398658885390295200986687178600300426099369053693266396256916016748630582130969087365418654094091253828, 265783403364727454827494188309507735483302618853810151983430558005724118997676829994149689489539627076, 265783403364727454827494188309507735483302618853810151983430558005724118997676829994149689489539627076, 137871290384499358745053697512029737359381463869397769080036832911566518570386383919302141337603557, 266028859877884774531216799413540354351539517256988236629610156633225756263098386777205045134017916292, 265899098668354856614116028943584748070865833230071251716244138745474450378451016316099744628288485284, 265750963061619406012821008204607148161800190732154957827466156672472724030224271435266452379732766084, 275742580527299594880896321865010563971833538635494840219957072399540604586297014281155249260477573, 265783403364727454827494188309494632949222383642869943814098266465216731345487468552085691665492637764, 269919542258563977366716237427246598621342489926720243831828753782482028062740645402134129015008750980, 298969835424260383363489992586866475207447941298760117752231673729598198998384716903145714044221222276, 12845275534085576841579267881518745821277880803, 265750963061619406012821008204620250695880425943095165996798448212980112735281692321531998863233346948, 12845275534085576841579267881518745825572848099, 84121771051488, 84121771051488, 150092468718048, 505818840041952, 184115303530668794702474443015920409885890707939, 505818840041952, 431086409091552, 184115303531167256151631736639431388965261301219, 431086409091552, 281621547190752, 9131526624, 281621547190752, 9131526624, 284009433568, 9131526624, 284009433568, 9131526624, 150092468718048, 50621025651168, 431052049222112, 50621025651168, 83606374517216, 365375409332819191251211128139143248974269409698, 83606374517216, 5798197835099826768350768271456357228831861154, 149577072249312, 505818839976416, 149577072249312, 43490740704, 281518467713504, 43490740704, 281518467713504, 43490740704, 61834487350388381963301181139232583142596290712458311479103378916085922407994630928428036575578240991729840468995901167662981774285986965853992708348040811438320720337086247, 431430006344160, 149680151398880, 149680151398880, 431430006082016, 431430006213088, 431430006082016, 431430006344160, 431430006213088, 431430006213088, 431430006213088, 431430006344160, 50621025651168, 431052049222112, 50621025651168, 83606374517216, 83606374517216, 149577072249312, 505818839976416, 149577072249312, 43490740704, 281518467713504, 43490740704, 281518467713504, 43490740704, 8308772757540641003219715800596197722881939825354408093550440809354258659446390426728381762377086597, 149680151857632, 9131526624, 149680151857632, 9131526624, 284009433568, 9131526624, 284009433568, 9131526624, 282033864051168, 558887340512, 282033864051168, 558887340512] = some [] := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem tv_0_1_0 : checkTree 4 (baseTable 0 1 0) 107 startPos 0 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_0 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨0, 0, false⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [1464361707945243228186994016477744492021216733602] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_1 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨0, 0, true⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [1464361708243571846315263224471366064687782324642, 1464361710630200712747079674270152749730942183842, 1464361708243571846315263224471366082280035477922, 1464361709266412789071755988670845650350266935714, 1464361709266412789071755988670845720719279548834, 1464361710630200712747079674270151905304938310050, 1464361707902624865396432303071540662033527630242, 1464361710630200712747079674270152186780988762530, 368230604344011345520503838794568906109866764706, 25690549672367375420112365358699669863871310242, 1464357526512900140904593265124363414570133383586, 48526599867948665277291587493791164947670002082, 1464356132716325232740646919141971374043244292514, 94198698895323321316326346164667548317680429474, 368229904718148044087883294604759109301294885282, 185542899677648480745043234705033528652875196834, 2854495385422314536962086425688354387311749538, 368231298514722952251829640587151149828183976354, 66437869465218867665908017077805928968472918143540540877157369499741307872954765676364864707524410725, 66437868475219390543418729320906390548847059343075250213400818716669294239700697218785433390919302501, 1464361707902624865396432303071540662037822597538, 400702877445959597942042030212068794482960205128334270708371559522332028758106682374478593169763089541, 5798215870065435837366236601831537006017137059, 265751216501007756991034555084419925356706708492409869580614056644432220586078403160667863123010534533, 129887934301692149381361582033438502425966169972302196772687918438860200478562259557659955713660741, 434959841472588349892444336324292761208998336681546944203991901194579180423600590933132222527447252101, 265751220461005694985275506790278343624537853576464426867194127881089254130995649900594419943535033477, 91433404103495110542511490394619635344966048163, 398626698526575473645944184346305568857093224804939329010202117777128209091320737236998188048421239941, 182777604885809885377511309279872388399529861539, 166094481123613362168984073652915871929411483173960055256762435411954336242394940252205722519569815365, 66437869465218867665908017168265825606374315854904119243799240887136873565600429625058257700041479141, 66437868475219390543418729411366287186748457054438606614481520473134871491641096376505389836837540837, 5798215870075820470697538630525805280608029091, 265751089781071852901160856524779823345668721350250328436536867510088559510456899155706508162128424421, 129887934301692149381361541782453807943389224138811678107269007100245014209549399236894566903420741, 89377545752199267619197130026633885346955683, 91433404103505495175842792422737442867245128099, 332188831536355339354677749939072309186140659141821035807923218008534065328206172119623649058686211045, 182777604885809885417125541652733134929150484899, 66437869465218867665908017154848830508284653158433043889303111643119918595583675913611756910427411429, 66437868475219390543418729344281311696300143572083451807562043883980085082262736052127170875537200101] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_2 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨0, 1, false⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [1464361707987861601118760531709780156265631083426] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_3 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨0, 1, true⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [1464361707945243308999719781027364351411491989922, 1978643219271028827039652706902412209779451533432305415049193868118648447718643468013071024681585145888365905230301173776733497667667546755928986616508794963893022006643931943, 1464361707987861681614573646202342682873983691682, 265751093741069849903969409567033271647334719098614072850731917397199403338802407187220102291241472325, 1464361707902624936384865915852386582901101193634, 291054652925283949780443337519026038969563931569783390385510331997120266907214028669103044357388200805, 720721987871111411052288963278651073195862883462696068979664958101379698204306774702865113518840687408425192844477092553410298156535941656640316976092963380445432342037423830366017670896169140495402528817690779197959277553091808731473140463813746277541218820123098760, 1038216434862208565738037366107398127609377405384853732507448647977784556434464601982329224390728325, 4152485765266025336726686356114471757393219956613582873777830144901601921486562502652336625396177541, 8337158146751818376677207735526759486017296607328966521097796097522433682190658396784174962627654052, 8304844439346339896591447583295638715745444269385120821717526598670348226815021967965898588107528837, 8304844315596404334271417842487563144875720985508415906511899372524815928536358007343193687466138245, 132875610230502854868722772226398851219167741990366255096145366516820059917067588278348424849023649605, 66437868475219390543418729320801563826939361726519636675956033564045723933132476152854780780343281477, 8563507976936080604544369915287134155828128162, 185542898313860628058153161886573405672815225250, 14272520568449775683693040624038304204763196322, 25690545751477165841990382041540644302633332130, 1464357529240476059243674249103823111980686797218, 48526596117531946158585064876545324498373601698, 1464356132716325303729080531922818983762825603490, 94198696849641506791774430546554684889854146978, 1464356132716325303729080531922818983762825603490, 185542898313860628058153161886573405672815225250, 1464356132716325303729080531922818983762825603490, 368231301242298870590910624566610847238737389986, 5798215870148512904015443900945375321460459939, 129887934301692149381361139272600465396043901178723870775217530294571443569699911608852767581738821, 130679933842084142787662681229521547434775613847814240469298645387326741138563912776524259929573, 15473245945367478039067996807196828509275027232073951430704004912413009663952203240016464284876947937589525120273697495572074275388353285968691801592189380931162926473771814, 132875610245971618942225626503008790775340675852894066218896608401380425912781684111231213890931332069, 66437869465218867665908017154848824110562981960325255083389980238167087705923513467985116719840400357, 66437868475219390543418729397949285690937123159859786847184493750351083320105233177626936165956228069, 8563507976936080604544369915288260060029938082, 14272520568449775683693040624039430108965006242, 2860070571722018181181083136105252101471365538, 25690545751477165841990382041541770206835142050, 48526596117531946158585064876546450402575411618, 94198696849641506791774430546555810794055956898, 185542898313860628058153161886574531577017035170, 368231301242298870590910624566611973142939199906, 132875610230502854868722772290129576985431822154602836876182854760262030530417203840819819398023993157, 66437868475219390543418729344281304898720864944922594757991401117591088702639107401697698800851457861, 5798215870158897537346745929639643596051351971, 265751089781071852901160856524779816947947050152142539630623736105135728620796700849609655861498621413, 129887934301692149381361112438610669074325937289730191664938256068827183773944269589735352167012165, 332188831536355339354677749939072302788418987943713247002010086603581234438545973813526796758056408037, 1236652014808525652423842921631284508083024177879895834628899010722215402549770366752969792901718581078022179369189934323660488292071433117173029898978873333646507330822158119, 66437869465218867665908017154848824110562981960325255083389980238167087705923477607514904609797608421, 66437868475219390543418729344281305298578472373975663001648912479027254192602537746030318574907397093] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_4 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨1, 0, false⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [1464361708073098346982293562173851484754459782562] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_5 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨1, 0, true⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_6 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨1, 1, false⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [1464361708243571838709359623101994141732117178786] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_7 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨1, 1, true⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_8 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨2, 0, false⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [1464361708584518822163491744958279455687431977378] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_9 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨2, 0, true⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [1464361707902624855255227501245708827776802384290] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_10 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨2, 1, false⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [1464361709266412789071755988670850083598061562274] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_11 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨2, 1, true⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [8563507976935999791818605365661680429050128802, 8563509298105550852288425789991081666199710114, 8563508019554372406672470540640011891541830562, 8563510704511847142465976564278254135986383266, 8563507934317627176964740190687852566185798050, 8563508658829961629480448165314966236664199586, 8563507934317627176964740190683489704046782882, 8563509298105550852288425789989955766292867490, 8563507976935999791818605365661680429050128802, 8563510704511847142465976564274876436265855394, 64880610566681330271951132539029890538271083978229383269387585561107604167903958593898067869843588, 64880610566681330271951132539029890538271083978229383269387585561107604168046840155963994415579268, 1464356829614612686822620092133171897921348594082, 14272520525831322573026060956491886981922449826, 291962732323023098716987049541827705870394414120192243320067241564281738756319528364868922471695300, 14272520568449695187879926131470218444414151586, 14272521250343657025541768931123486659775069090, 14272521847000873633495881380820162319165188514, 14272520483212949958172195781513555519564966306, 14272523296025542538527297330083396859376724898, 14272520483212949958172195781513555536610617762, 1464357529240475998396445438148815217851538368930, 1464356132716325222599442117316140665686425889186, 94198696849641430732738416852793972800267254178, 2854495385422304395757284599857646030493346210, 185542896950072633394395863506424255722407618978, 2854495385422304395757284599857646030493346210, 368231301242298809743681813611602953109588961698, 66437869465218867665908044126363220045307417541214989943636595846950166493421025228376138770440864741, 66437868475219390543418756369463681625681558740749699279880045063878152860166956770796707453835756517] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_12 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨3, 0, false⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [1464361710630200722888284476095991339419320740258] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_13 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨3, 0, true⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [8563508275264699049726227965973920933729036706, 48527122541664357250819485495538487884266891682, 368230604344011436791347055227085250922544130466, 48527122541664357250819485495538505476520044962, 185542899677648572015886451137548817932510849442, 185542899677648572015886451137548888301523462562, 368230604344011436791347055227084406496540256674, 5798215875301887145700303867927197833891043747, 368230604344011436791347055227084687972590709154, 5798215875304483294129571281885859746184063395, 368230604344011436791347055227085250924691614114, 5798215875299290997271036453969661825799834019, 5798215875309675590988106109804309474971912611, 14272520824160021514021033499746777112425556386, 259775868603384269922246441273176153133182131939944581403028682992240386468794040181385321779313797, 259775868603384269922246441273176153133182131939944581403028682992240386468794040181385321779313797, 129887934301692149381800304408562072198364389826958627036164401171337955838092954751700054227038533, 25690546944791619340308210592607234329169389986, 48526597140372909197487432727698659043955468706, 94198698895323412587169562597187552321161161122, 91433404108721177266413073718139661281178704291, 185542899677648572015886451137553251180305476002, 182777604891043740556604252937906000048515213731, 368231298514723023240263253368002137256075749794, 66437869465218867665908236562972938804312710782282479604048632108842473525649242165647993418155774949, 66437868475219390543418948738988424894238538499461812167811435105685685042311584453187118703694287845] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_14 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨3, 1, false⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_15 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨3, 1, true⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [8563507976936080921457019972343376218055272866, 8563509298105641806218992165450639054654695842, 8563508019554453853223535204379058054722775970, 8563508104791198449105965440221020231354576290, 8563510661893555657250525995981636054752979362, 8563508275264688908521426140134346081321380258, 8563507934317707989690504740312197981015140770, 8563508616211669827352347539960997781254994338, 8563507934317707989690504740312197981015140770, 8563509298105641806218992165449513154747853218, 8563507976936080921457019972347879817682643362, 8563510661893555657250525995978258355032451490, 550918307646586367750279171891479935508229941666, 185542896950072704382829476287266306289992493474, 185542896950072704382829476287266376659005106594, 368230602980223502974818567801943150675281078690, 5798215880629204004966640667046371767233976739, 368230602980223502974818567801943432151331531170, 5798215880631800153395908081005033679526996387, 2855192283709839607368872197731984368190122402, 5798215880616223262820303597255314014172498339, 5798215880626607856537373253089961663344576931, 14272520525831403385751825506116232396751792546, 14272523210788878438457981586808464905757288866, 14272520568449776317518340738151914233419295650, 14272520653686520913400770973993876410051095970, 14272520824160011372816231673907202260017899938, 14272521165106992291647153073733853959951514018, 332188831536355339354677969333776146750583400638011527540649329894390240456831037385559206753711395813, 14272521847000964270513797699222369333444372898, 332188831536355339354677969333776146750583400638011527540649329894390240456831032903000430239956046821, 14272523210788878438457981586808464907904772514, 14272520824160011372816231673907202278808381858, 14272520483213030453985310274080550577264159138, 259775866667903252597752567965250758190197657825078697461268904149194785381809852146323590911900517, 259775866667903252597752567965250758190197657825078697461268904149194785381809852146323590911900517, 129887934301692149381580480360874971237961523097237568562819873085408772808266575406182109185847621, 91433404114038109531962340862001774221863197091, 185542896950072704382829476287270739537787120034, 182777604896360672822153520081768112989199706531, 368231301242298890873320228218284648898594105762, 66437869465218867665908236549552668072727394654623535622029223528976103049610991593083326816125359077, 66437868475219390543418948738985149260742885068273943540288155769836269536290051731598740781235147749] = some [] := by
  decide +kernel

private theorem solve_0_1_1 (N : Machine4) (h11 : N 1 1 = none)
    (hAlive : ∀ q a, ¬ (q = 1 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 0 1 1)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 0 1 1) (q1 := 2) (a1 := 1) (rem1 := 102) (cur1 := ⟨2, [1, 1, 1], 1, []⟩) (step1 := 5) rfl ?_ N h11 hAlive h107 hm
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_0 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨0, 0, false⟩) 102 ⟨3, [0, 1, 1], 1, []⟩ 5 [8563507998120651787366466639694936891651549602] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_1 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨0, 0, true⟩) 102 ⟨3, [0, 1, 1], 1, []⟩ 5 [1464356830997009873427366212733977724428286454178] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_2 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨0, 1, false⟩) 102 ⟨3, [0, 1, 1], 1, []⟩ 5 [14272520589551270116778580106389618999319096226] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_3 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨0, 1, true⟩) 102 ⟨3, [0, 1, 1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_4 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨1, 0, false⟩) 102 ⟨3, [0, 1, 1], 1, []⟩ 5 [25690545772412506775602807039778983214654188962] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_5 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨1, 0, true⟩) 102 ⟨3, [0, 1, 1], 1, []⟩ 5 [1464357529256426795193093239578672174416656361890] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_6 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨1, 1, false⟩) 102 ⟨3, [0, 1, 1], 1, []⟩ 5 [48526596138134980093251260906557711645324372386] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_7 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨1, 1, true⟩) 102 ⟨3, [0, 1, 1], 1, []⟩ 5 [1464356154537015078471270294204151205564005771682, 1464445510262638199672537276662687501108754016674, 1462216657701417048433653207368802385458585692578, 1464445510262638199672537276662687518701007169954, 1461859147516165180706091777285936892032517695906, 1461859147516165180706091777285936962401530309026, 1462216657701417048433653207368801541032581818786, 1461501637330913312978530347203073509670385641890, 1462216657701417048433653207368801822508632271266, 1461501637330913312978530347203072383770478799266, 1461501637330913312978530347203073509674680609186, 1461501637330913312978530347203074635578882419106, 1464356176357704934343098471092161745441585654690, 1464367304909614424595566826612907389135034018210, 1464356132716325303729080531922818983760678119842, 1464378477102903545462053121302996920411444243362, 1039103474413537195050885686138549763537813375864016734180702489829889719023921133265526958245972613, 1464356132716325303729080531922818420810724698530, 1039103474413537195050885682784300989015397701746258993834728660372150548964715200685053494017612421, 1464356132716325303729080531922818983762825603490, 1464356219999084646086754824868182825196745420194, 1464356307281844069574067532420224984707064949154, 1461680392423539241771708661331591500346986363298, 1461501637330913302837325545377241675413660395938, 1461859147516165180706091777285941325280312322466, 1461501637330913302837325545377241675413660395938, 1462216657701417058574858009194640975146964248994] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_8 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨2, 0, false⟩) 102 ⟨3, [0, 1, 1], 1, []⟩ 5 [94198696869579926728548168640115168506664745378] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_9 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨2, 0, true⟩) 102 ⟨3, [0, 1, 1], 1, []⟩ 5 [1464356132737592951661639185889283274439916546466] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_10 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨2, 1, false⟩) 102 ⟨3, [0, 1, 1], 1, []⟩ 5 [185542898332469819999141984107230082229345479074] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_11 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨2, 1, true⟩) 102 ⟨3, [0, 1, 1], 1, []⟩ 5 [1464356132737592951661639185889283274439916546466] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_12 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨3, 0, false⟩) 102 ⟨3, [0, 1, 1], 1, []⟩ 5 [368231301258249606540329615041459909674706954658] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_13 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨3, 0, true⟩) 102 ⟨3, [0, 1, 1], 1, []⟩ 5 [544301746522592, 435450095733216, 544301746522592, 508017862838752, 713623846446441640819062944797241628477647266, 508017862838752, 593748459881477033270720488355455757434236201378, 435450095471072, 508017863231968, 435450095471072, 43490740704, 290314560735712, 43490740704, 290314560735712, 43490740704, 435828052855264, 435553174620640, 435553174620640, 66438755514785817989966574740523119145039909728703992469404236219412871742165290911631490934108322469, 435828052593120, 435828052855264, 435828052593120, 435828052855264, 435828052724192, 435828052855264, 435828052724192, 435828052855264, 544301746522592, 435450095733216, 544301746522592, 508017862838752, 508017862838752, 435450095471072, 508017863231968, 435450095471072, 43490740704, 290314560735712, 43490740704, 290314560735712, 43490740704, 417622555274056424207895570159874801517706884226255790401963017115980713437939245061709443741497325636, 365733616413777941819159458113360138481162125731, 966141935080809282645816417594368922870563584084772430398104278792734163398105081549108623941990408110094791764130846818700628047117728370546179597822911883007392053992486, 66439769274257944515650211869622038848682209867002345505558886222562213939203968167755529018132399301, 731109025746503671370080744211478407271300473315, 365733616413777941819159455752176879454220452259, 731109025746503671370080744211478407272374215139, 731109025746503671370080744211478407272374215139, 365733616413777941819159606867905457186943295907, 365733616413777941819159606867905457182782546339, 365733616413777941819159757983634034919808754083, 435553175079392, 9131526624, 435553175079392, 9131526624, 284009433568, 9131526624, 284009433568, 9131526624] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_14 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨3, 1, false⟩) 102 ⟨3, [0, 1, 1], 1, []⟩ 5 [291414072134112, 294712607377888, 291414072134112, 292513583794656, 731467235549565587805569586681716551409923582370, 292513583794656, 730764762075811873176611211556128128018257340834, 294712607115744, 292513584056800, 294712607115744, 290314560735712, 290314560735712, 290314560735712, 290314560735712, 290314560735712, 132907923813676895252732306310260704843780560417929362442712580710517524404441890236813661067168627460, 295090564499936, 132907923813678783526895553153668383671706880507029695494555188422590983682374231192101895413840905988, 294815686265312, 294815686265312, 295090564237792, 295090564499936, 295090564237792, 295090564499936, 295090564368864, 295090564499936, 295090564368864, 295090564499936, 291414072134112, 294712607377888, 291414072134112, 292513583794656, 292513583794656, 294712607115744, 292513584056800, 294712607115744, 290314560735712, 290314560735712, 290314560735712, 290314560735712, 290314560735712, 132907923813795856525017516917087532306105353431854649836051177577874265567552211949240618726544816900, 294815686724064, 290555079166432, 294815686724064, 290555079166432, 290555079166432, 290555079166432, 290555079166432, 290555079166432] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_15 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨3, 1, true⟩) 102 ⟨3, [0, 1, 1], 1, []⟩ 5 [36327374490080, 280287985237557760108451067146856702135053089058, 36327374490080, 713623846446441640819062944797241628477647266, 5720162964123345341272801285903500344478951842, 181462909454816, 93461700289919960068131193852291490, 181462909454816, 43490740704, 8839584025056, 43490740704, 8839584025056, 43490740704, 435828052855264, 145282104887776, 145282104887776, 66438756504785309864597762833198541134789409469572689099871086684778135920895037958206351254999005861, 435828052593120, 435828052855264, 435828052593120, 435828052855264, 145282105084384, 145282105084384, 145282105084384, 435828052855264, 36327374490080, 713623846529518707468270243907702242052958626, 36327374490080, 181462909454816, 181462909454816, 43490740704, 8839584025056, 43490740704, 8839584025056, 43490740704, 266042957470542558802394779847248247205669211383061092207489598777715549535626136320027720425199269956, 731110419543078579534027012274822933917739385251, 132877510039526832901229969921983626459683290906909590122847864671679082873563499015711411500295928677, 132877511029541423593096155114349458485592243398521194850245979145184862645188701590726387133420143813, 731110419543078579534027090193870447793894597091, 731110419543078579534027009913639674890797711779, 731110419543078579534027090193870447794968338915, 731110419543078579534027090193870447794968338915, 731110419543078579534027161029368252623537365411, 731110419543078579534027312145096830347921891747, 731110419543078579534027312145096830356377608611, 145282105346528, 9131526624, 145282105346528, 9131526624, 284009433568, 9131526624, 284009433568, 9131526624] = some [] := by
  decide +kernel

private theorem solve_0_1_2 (N : Machine4) (h11 : N 1 1 = none)
    (hAlive : ∀ q a, ¬ (q = 1 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 0 1 2)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 0 1 2) (q1 := 3) (a1 := 1) (rem1 := 102) (cur1 := ⟨3, [0, 1, 1], 1, []⟩) (step1 := 5) rfl ?_ N h11 hAlive h107 hm
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
private theorem tv_0_1_3_0 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨0, 0, false⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [36842770565600, 6255382890582281822300401525759605557620144418, 66908126157359467718930542664620521680581722353736201893385741088877088946039295468464020777679620, 139898808151059412164185259217323260025394269851739111083178383702162474221177440221898383954953188, 799787360840113155356383012240128192380587293676289630860106490148976863393642622942180967313260198766138402178253347956922338576323853099862428166770716889720967057680259740386385434589553908259559330142796624394394299632855040712809372278366088699674818756892835371515361083529553665050482647894208587323769596949750452603285300229218894085085734369210331749401362574122, 139898808152475615920753902808520949290335998485005957373357600469707804173461270519890417861394020, 139898808154363890112138223900893203591840630269242505761440074939431164564752871783695366798297700, 6244232476693876645350435220408889441990506786, 6065824472082197068200089687090508005767145890, 6244232476693881715952836133326495428803328290, 6255382894569981021462351883223844698899642658, 6065828603322828250128226323793996583957195170, 139898808156252164303522544997337608023277805815473576891656658597611194026885234722984333405964900, 6065831330898695883185201174078760026289269154, 6244232479352342778125068792051715536176838946, 36842770565600, 6422639181320647333286745392517553628338219426, 5720162964123345341272801285903500344478951842, 5887419192387918991332047653483326722995681698, 5709012548905707097935518194731511919244503458, 6065825835870130884728577112235141526746851746, 5709012548905707414848168251788862293420304802, 6422639165369850536638943962660597063220226466, 7136265739298698110225061797667856278224955810, 5709012548905707097935518194731511919244503458, 40725421099488, 49899471243744, 40725421099488, 64943970057844156319653884285927600700498936679096724024939687836955159330907442360946625305979236, 5887421977120585372538004125707713846105373090, 65007330024852064188949916862902621969414571368258442805200537863720089256062928867998793910728292, 39728988686816, 5887419196375602978686757493258662684585384226, 39728988686816, 40862860052960, 49762032290272, 64880610090836241134721848342071758165672994361323653249437131550732057380756288922910994337120388, 49762032290272, 39728988686816, 5709012570173436160132586767874120672735160738, 40725421099488, 49899471243744, 40725421099488, 6065825833211745881592320368337926002314344738, 65134049966420976411690750536734064793517940699877479560072278373332110258523530946590644042730628, 65007330039958257607447096857043699708585251814754444819048399875976810800540937686669543447213668, 39728988686816, 6065824472082197068200089687089945055813724578, 39728988686816, 40862860052960, 49762032290272, 65007330032405160701674093780774282964017829613681691944065199008180523033344142885132361800106116, 49762032290272, 39728988686816, 5720162985307997336820662559932270782526286242, 45638863817184, 5709012570173436160132586767869757810596145570, 45638863817184, 35743258905056] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_1 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨0, 0, true⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [1876879211026163284456373008440935555586239391308724799758051693179710347930802599083054300014637597727473122572926229111680641122266637056033374856740510843283644168122593243302699523835575224052375542468961230198645162506373185024432013234275119314010629076442760, 435828052855264, 1367032118989309047794436020977738341771908504713273243939618636672132078340236265116185602366947975159004204032580228144926984339748643102381770757874539800892656448955223898356713460105417522194822081436009442669847346195199463470209318685791503516815925311818563963162577849619432947372383487870293966907636639148519334493780083819241472590606669469838667884684211500922661353159273139098928353472876803928827782381711339304920988584994370083337254216912994887182324706342897680375741727047622387231115275669695905524271397570447101583650624151430878075755849451683405658654012391423978400604850711903508111311278875157435233679489424562474747730666817087182170015376656029898074307193041688147425769759212685364324190556477199430829452773208147275903454821594573587012334903374005081741605441866059205095341445315831128840556684487474615026200953255431010263701857263685853116565983152698590249340129676087278572479035977846005327711023847709669659396778847014082333728092128557057279466756469566079999295027038025330, 548420624184350927817222369619108107045934492066, 564597443787052312662726471705979019486663080484683893167268655938758926346004490418965511101530691167743066435165022706953570469796177625854109468568201891234167170028806769264190744001725355812226190532350592701188594566474713302999876229778244924837104562660077387190459900301478060183740631562766860540822328412169540418825227655026791127628672174480142075688201314692235380679470109238102389919135463676168107878016127020409340867604661975536210243837350072695251020001636587774145010973020577115533257729343637710684860500889510091194442328644215414458809243493422735623733843806312895093462168491751178318507388183369201536472440817750956425256900833411912925227615814260594758453075238623203161143427265165007002982130365901226900386183749703224694348851311905165867151488536395421881165416579274686623385101667595816507024, 435553174948320, 435828052855264, 435553174948320, 435828052855264, 435690613901792, 435828052855264, 435690613901792, 435828052855264, 8304781141253001588605165029757976211984105896324029618771579179211240065073331018836720170295437668, 145282104887776, 24914184838217169879914098046138238934253297911174825277752307771929976236212051916866846792903181284, 145282104887776, 140746619423200, 145282104887776, 145282104887776, 154215636863456, 154353075816928, 154215636863456, 140746619423200, 249081520042175852700593400708079712985015908102923458904710884871403459282228588581340895169033331883777724826301326483994650499469890457559977454937030917485681928301351, 122653778810654217400501322244972705105523689178064941675140646332160971873229894902809238541912747803989698125840423976761240341500548923933431455706735560873623100812071, 122653778810654217400501322244972705105346234933065636316591242855276642735235376150038137055584251721027777463819469127608863742676892604124765190725685079319580198529831, 32078680625152043864978359557147320113615241705122165470382571744777977468181562748981356190913011807684725795608845903178461404730676696687596372129507452242680961710887, 137871292197242541952077247384775200974135599442339461451287962103950362663711445698541149392899429, 16609451278816636180199392119224910170593342207588202154380733880307430342239948726980608457688614692, 145282104887776, 16609467118808624191433604798084546294269619654109821974048486060460061100424541439407214534575670244, 145282104887776, 140746619423200, 145282104887776, 145282104887776, 154215636863456, 154353075816928, 154215636863456, 140746619423200, 137871290384499345238185623365095320377698725576309223468403355450188182938232581059442089553820325, 145981366161511550707279650749548978143952344375978592823150056803517006895552183304772937570321605, 7446115018805182963688482605248666733847299085565748071518476015899056128179234197429215171268032988729272775006282940548743978879044913840406435925637749986140050141834538339241118601902452907553607278398974652434383789740902245750378900964159235555344124977161, 145981366161511550707306275099196674842107805980559582830605633499839655544672230937949072347509957, 122653778810654217400501322244972705105346235186911128332046704853672183000815732260999593149606522529131626720129398383752554852682569802312709764545588861169258019384103, 3029820533684153898357878746518690944845397930084095990195552043918709077111410364060217335722943297936188901314621685749048559175687425236854717699781547563080513024938734886, 62270380013509555764636448949160402850509134124716973201282462508311786435666634877337330776623807192591399736775916879211675753567292012862338056561002209066203877141287, 137871292197242541952077247384775200974135599442339461451287962103950362663710885378694085173480805, 436549607098848, 435828052593120, 436549607098848, 30916314933377064517992150842509555422602268640794695181513387487486375471930460852508273320014002618681652533330416316152598527609474049479286901984347979996486895888129062, 435553174686176, 435828052593120, 435553174686176, 435828052593120, 435690613639648, 435828052593120, 435690613639648, 435828052593120, 145981366161511550708158090768297685431922226191734491092370658578449491277677335315052437000317125, 436549607098848, 435828052593120, 436549607098848, 365732918154200139366438079930265559841402546594, 30916314983764899016875950329987586708685265460135302906494853778214837885183041756028937467587258303045230133409530515248044245002502554265233439314441146991823923909909542, 435553174686176, 435828052593120, 435553174686176, 435828052593120, 435690613639648, 435828052593120, 435690613639648, 435828052593120, 365744069930547164163890802268254282204637587874, 435828052855264, 365409907967348257746778508060480357964870352674, 435553174948320, 435828052855264, 435553174948320, 435828052855264, 435690613901792, 435828052855264, 435690613901792, 435828052855264, 145981366161511550708158141082028503552931307959471196634697286767526448062449328748979744320731333, 12845256478273029308639395189672898439030014435, 471733979318752, 145282105084384, 471733979318752, 696898297919845252300258834119999626439074, 145282105084384, 140746619619808, 145282105084384, 145282105084384, 435690613770720, 435828052724192, 435690613770720, 140746619619808, 12845256478273029308639395189672898443324981731] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_2 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨0, 1, false⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [36842770565600, 60383398804174214440273364834078372219975991067215155539075947641598293444526900259436032249265839030362258086189737138480790990447068218321930251252892382792790563249190, 36842770565600, 40725421099488, 49899471243744, 40725421099488, 64943968146910717523712898018937793405856705736514986567994329964648772650652669487370350438459748, 11596434568551203701950117592402395953772919714, 64943968146910717537781636861220529376450995552760120067115393478876983899860317169513390651287908, 39728988686816, 5887440974447085918748419149233538317750917410, 39728988686816, 40862860052960, 49762032290272, 133816252284506550180192558994927938338642981627192143215760804625557769662641869194934942382923076, 49762032290272, 39728988686816, 315643516668866131397283240156652135669496540684384191479985476569473847226371193730773049296713796, 291962729422633983071963876932635092311784651638760399381236314264278698579782748857630957683243076, 130014654248925891409577644711439799298743335096802036619564153962744282187088975438843845550804100, 65387489851447090003622707043844999564770695801415758570525917066570667094717456434212128947825188, 45226546989536, 35193503091168, 45226546989536, 35468380998112, 30206441446337572363620378822039724902477799445719155756648005117434420164364848650933769096877414589881317121667629700017643430482838072629407273085278374624762826087462, 35468380998112, 35193503091168, 40725421099488, 49899471243744, 40725421099488, 11774837020977600662133309827544497023515388322, 261549947707929809520019789022086037960901446304267600135331886957400983670017329918873593116753508, 65387489851447090003622707043844999564770695801415758570525917066570667094716896112202565874739748, 39728988686816, 11774837020977519532494895220862801234510244258, 39728988686816, 40862860052960, 49762032290272, 261549947709818083711404110117733926037958614208132564646513465552081224205196346630578295338289764, 49762032290272, 39728988686816, 36327374490080, 36327374490080, 40828500347360, 11418025097801029562230323728499864498447870370, 40828500347360, 36327374490080, 36567892658656, 36567892658656, 36327374490080, 45638863817184, 45638863817184, 35743258905056] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_3 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨0, 1, true⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [265815851588798648142811443745152469674530559194358220971750027045841597459369824074037637917235703172, 425928286118720143335469878308858866376384824075503929434487147661489655301804428098792573152700823620, 460968090272219108370601204517313375458238470292851142732297892994016755652608360599444468412233185348, 229111340596548157968305412537055607618378875697149253618400102501043397696547925581504842168277299253054066376018381269893539417119221556563087067907795772985833796189927926051073315798982175730428574767639643127995309426568188614753509135212364171780107050760, 282394866136867672460836890937156208354696124672860617907610875158265734813684767721452963448817612868, 265783403364727454827494188309494632949222383642869943814098266465216746085639532012064426181672728644, 265783403364727454827494188309507735483302618853810151983430558005724133737828886730290242536253847620, 229111340596548157973038112310871801908144395071561355488182621662086453459055793840179252187106285757063697137055359919055986536738681426833778134081141916509569683006300062792983286793663872800698729044699455274949816435334455272657541598160370010628107050760, 265783403364727454827494188309507735483302618853810151983430558005724133737828886730290242536253847620, 275742578472857306172466157071993274071296719698946664741660773317193537315562439135867842443885413, 275742578472857306172477750600326022477985182656161968968370930630065820008784639988879271242375525, 137871292318092102805824661776591096104267438633428835281424883607126610872528600818192430689155749, 275742580527299595780416257810846638015289957299583643733348609338720626794483279888293714712593605, 137871290263649813197050489198815058108555048482010824518075620742642872188356150548197262971998021, 266044984989516611223731574627836465934139404026779041210424063397586380665748587947674705013087041604, 1978643212245530320642245544064366009631333374187139395208078916313336052158886898883622384970121740287434377781791428913289287090325941503719857136536722932068744551892278310, 282394866136897888535484260560449680899937007774170894947716047545146350636616592038457025748930033732, 265783403364727454827494188309494632949222383642869943814098266465216731345487475275923873134958508100, 1978643447658837518563163048757026624248902956940110498080283820341995481300114702282269777723965995810073008505102278268253226107373187701533563756399809043752234190163696678, 275742580527299595780635223170847848648243523355453621808267300078129313344464438150894760563521733, 275742580527299595780855047218534549799849704126473266243684981263524793744594594623754930102679749, 137871290263649813197874829377642186815787529270807295533738025524002867552408405259735758357925349, 1978643212015194724735037584416541876896524973960849110874765458581583517679811551047971440899459293716768551048077363837557876746824377766824713955310087172722416653093575718, 275742578472857306172467445247631372200817333887647250500825291544412856637086807199422019572611941, 265750963061619406012821008204607148161800190732154957827466156672472724030224271435266452379732766084, 265783403364727454827494188309494632949222383642869943814098266465216731345487468552085691665492637764, 275742578472857306172467445247631372200912667370253435714926047596277823070781361722734817096776549, 137871290263649813196995962530730024006789739693285645088953566796776358995442570916455580633674053, 12845278256344512248701056845647774072195547619, 265750963061619406012821008204620250695880425943095165996798448212980112735281692321531998863233346948, 12845278256344512248701056845647774076490514915] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_4 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨1, 0, false⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_5 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨1, 0, true⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_6 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨1, 1, false⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_7 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨1, 1, true⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_8 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨2, 0, false⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [141880490756576, 91355353239247383831325627293808887561924409634, 141880490756576, 4152422405297247179034302302942662769817474444883733061697831244836088034558578026565492929911400804, 91355354600376851515079518926242417346836724130, 8304725577533349390534168382094473681747474875112590185061935773989415958267139943987551038378469924, 91355351197553182305694884292496343024926747042, 146278537365984, 91355351155017886440577576359570154233749596578, 146278537365984, 146278537365984, 155074630519264, 4152359045330239263960053390735378942147689905576989625414807651986415936938284889252253028814438532, 155074630519264, 141880490756576, 4152485765279243263044474085027812225326221085299882362898950633689271937538912351860801575464484996, 154353076144608, 4152485765279243263044474085027812225326221085299882362898950633689271939889064075151659808065863812, 145282104887776, 145282104887776, 154353075882464, 154353076144608, 154353075882464, 154353076144608, 145282105084384, 145282105084384, 145282105084384, 154353076144608, 141880490756576, 4152374699697205915595485341372377083414639446553031484436379292275324714274331615458992116338318276, 141880490756576, 4152612485198388919719359780662084298413343495525549398842526689679109628938819218387530965712374916, 8304765177514735624268510877049870867843148022587539978867112426920682661266902512543627480672372516, 146278537365984, 8304765177514735624272028061760454347279138991257178874068155502704901493399601106699996090549012260, 146278537365984, 146278537365984, 155074630519264, 91366505015511413008680206996422677037891747618, 155074630519264, 141880490756576, 92057828052779861427239636437926513414482459042, 145282105346528, 140746619881952, 145282105346528, 145282105346528, 154215637322208, 154353076275680, 154215637322208, 140746619881952] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_9 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨2, 0, true⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [4160469121227983000542321015014426958852287496427698896943190147415218460156877188199630723898681989, 4160469121227983000542322517717945120972557582098631506327285466574487355667370178476421506548694405, 290417640212960, 9131526624, 290417640212960, 9131526624, 284009433568, 9131526624, 284009433568, 9131526624] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_10 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨2, 1, false⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [141880490756576, 91355701688391110872312213789406897692572940578, 141880490756576, 4152422281547666590128749472453395539296760681146307307374679649379834473213494384674042664584554852, 182699556063266744785673334393357331069517457826, 16609451278816516319018314386107917440961593061820425302084800100034702449330658088780807378638326372, 182699551979878341734411772832862041884071061922, 146278537365984, 182699551937343045869294464899935853092893911458, 146278537365984, 146278537365984, 155074630519264, 4152422281547666595003567481322098037580243257265816056020382686307135809133719407316024057863154020, 155074630519264, 141880490756576, 154353076144608, 145282104887776, 145282104887776, 154353075882464, 154353076144608, 154353075882464, 154353076144608, 145282105084384, 145282105084384, 145282105084384, 154353076144608, 141880490756576, 16609467118804845791829911182318115869443557528810376879461806046515060949862372390606981505360935684, 141880490756576, 16609467118806734073224486369351678204975277576738367228520466018048592455854446690904313326120879076, 16609467118808622347415867255693279757436637786472734809576369303936999912180730632556662562444166116, 146278537365984, 16609467118808622347415867255693279757436637786472734809576369303936999912180730772638771172196893668, 146278537365984, 146278537365984, 155074630519264, 182710706478484383029010617484525941797782842274, 155074630519264, 141880490756576, 182699551979878422547137537382481901291459078562, 183045214851625198266301161440037352131951356322, 182710702395096060473562170416596556934703770530, 182688401564660784620712904348367808600315292066, 183045214851625198266301161440036789184145418658, 183045214851625198266301161440036789184145418658, 183045214851625198266301161440037915088347228578, 182688401564660784620712904348367245648214387106, 145282105346528, 140746619881952, 145282105346528, 145282105346528, 154215637322208, 154353076275680, 154215637322208, 140746619881952] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_11 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨2, 1, true⟩) 102 ⟨3, [1], 1, [1, 1]⟩ 5 [36327374490080, 280287985237557760108451067146856702135053089058, 36327374490080, 365375409332819191251211128139143248974269409698, 5720141186051862401211139629928624711313418658, 146278537365984, 93461700289919960068131193852291490, 146278537365984, 43490740704, 290314560735712, 43490740704, 290314560735712, 43490740704, 435828052855264, 145282104887776, 145282104887776, 435828052593120, 435828052855264, 435828052593120, 435828052855264, 145282105084384, 145282105084384, 145282105084384, 435828052855264, 36327374490080, 365375409332902268317860335438253709587844721058, 36327374490080, 146278537365984, 146278537365984, 43490740704, 290314560735712, 43490740704, 290314560735712, 43490740704, 8312827795308297560407083744899111729449375394448712717921137179770173556393120945058853481278076549, 145282105346528, 9131526624, 145282105346528, 9131526624, 284009433568, 9131526624, 284009433568, 9131526624] = some [] := by
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

private theorem solve_0_1_3 (N : Machine4) (h11 : N 1 1 = none)
    (hAlive : ∀ q a, ¬ (q = 1 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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
private theorem tv_1_0_0_3 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨0, 1, true⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_4 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨1, 0, false⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [567906886814176] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_5 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨1, 0, true⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_6 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨1, 1, false⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [567906886814176] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_7 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨1, 1, true⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_8 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨2, 0, false⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [576702979901920] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_9 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨2, 0, true⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [576187584154080, 576565541210592, 576187584154080, 265815340747613980202295127639476568089478826327114915118247387754707142424150541082391784593450809412, 576221943826912, 576221943826912, 576290663303648, 576565541210592, 576290663303648, 7493073539303366290841746450581401172838492578, 435828052855264, 261549947947740621470797158530990617038159611157386114928993323308213340924118074932225506695936772, 5576547449869606511101356409973747800385954, 154078198237664, 435828052855264, 154078198237664, 13203270928864, 294953125546464, 435828052855264, 294953125546464, 13203270928864, 576428102257120, 48868679354848, 435828052855264, 48868679354848, 83984331966944, 45694314077291049373000326914872125033227503075, 83984331966944, 1038121394910280498306824205789064653275146754676293329869400768662209204184974721120849667781957445, 154353076144608, 435828052855264, 154353076144608, 435828052855264, 295090564499936, 435828052855264, 295090564499936, 435828052855264, 576428102257120, 48903039158752, 435828052855264, 48903039158752, 2076195269844596732406596323700148427597543490237855966209816463437657647360151708133354844249654469, 154078198237664, 435828052855264, 154078198237664, 13203270928864, 294953125546464, 435828052855264, 294953125546464, 13203270928864] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_10 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨2, 1, false⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [576702979901920] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_11 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨2, 1, true⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [41824932628960, 435450095733216, 41824932628960, 5576547532946673160308655523812063243708834, 74810281495008, 74810281495008, 153975118760416, 505818839976416, 153975118760416, 4441537251808, 285916514224608, 435450095733216, 285916514224608, 23139304796957436586381930525606032746914, 435828052855264, 5576547449879747715903182245185721426028962, 83984332032480, 83984332032480, 154353076144608, 435828052855264, 154353076144608, 435828052855264, 295090564499936, 435828052855264, 295090564499936, 435828052855264, 265750967021617344000308086828655326919999166619372285085269071667527591869712314058642045943116167940, 5798228460512930505152288002995677204971559202, 11440304107624334927060349587849364425349800419, 295320807192543195087686723398378434275380900792007546973141865063925637399547501771006956737345604, 11440325885695817867122011243824240058515333603, 494661038826059787693575837325765650543791366470772861830009755129721081278727260620291514807172569559115506348974558474376094234506252033676583472352837682530899732508534054, 33218880282637318031623276885777603535510629261799579840825939003151473779801665815025211352000764549, 50724104997344, 435553174948320, 50724104997344, 92776676574666494941687006156448852135822535074, 83709453863392, 83709453863392, 154078197975520, 435553174948320, 154078197975520, 154078197975520, 294815686592992, 435553174948320, 294815686592992, 154078197975520, 435828052855264, 3665779701566514157073037722496366311324389393617834646458554668640146373138176478390806735461109153038052103961741490857496405349035782852986265857562335894268592979568837433464453559883364765161492583607675200242553195478257139366385098190993225712132107050760, 5576547449869606511101356409973747800385954, 83984332032480, 83984332032480, 154353076144608, 435828052855264, 154353076144608, 435828052855264, 295090564499936, 435828052855264, 295090564499936, 435828052855264, 265767187173171368411246328122060787453883417068631577545951226907230624857925589061110689780112521988, 41824932628960, 435828052855264, 41824932628960, 5576547449869606511101356409973747800385954, 154078197975520, 435828052855264, 154078197975520, 4407177513440, 286157032393184, 435828052855264, 286157032393184, 4407177513440, 42065450797536, 435690613901792, 42065450797536, 75050799663584, 265750967021617314496024395203731219603449948987201150761853703136951163779237308369816610976822426372, 75050799663584, 265752994540561545419178818094546174291000449611489435517184775227075600908108701183132478876889086724, 154215636928992, 435690613901792, 154215636928992, 4682055420384, 286157032393184, 435690613901792, 286157032393184, 286157032393184, 435828052855264, 83984332032480, 83984332032480, 1038105570387034432362395950454059048873616783576484792789501770964317888190769925606670106613775013, 154353076144608, 435828052855264, 154353076144608, 4682055420384, 295090564499936, 435828052855264, 295090564499936, 435828052855264, 42065450797536, 435690613901792, 42065450797536, 5576558083734137609635642981278124545714594, 75050799663584, 75050799663584, 154215636928992, 435690613901792, 154215636928992, 4682055420384, 286157032393184, 435690613901792, 286157032393184, 286157032393184, 5798228800795297743003401523427652603101616418, 435828052855264, 332188720656411659310282510104438617839764254268328499357743546770722489688474964540155210686011156325, 2076195269844596732406596323700148477579744791265905927077997964715221636690068698665276721902912709, 154078197975520, 435828052855264, 154078197975520, 4407177513440, 286157032393184, 435828052855264, 286157032393184, 4407177513440] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_12 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨3, 0, false⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [567906887010784] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_13 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨3, 0, true⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [40141305743840, 145694421944800, 40141305743840, 129769134362136116504877348293895818029162603708883541253324689883584443898980093328425764349225605, 84121770920416, 84121770920416, 145694421944800, 505818839910880, 435828052855264, 505818839910880, 145213385607648, 182710353903927749908929429740349031701375636963, 145213385607648, 435553174948320, 435828052855264, 435553174948320, 435828052855264, 145419544037856, 145419544037856, 145419544037856, 145144666130912, 145694421944800, 435450095733216, 145282105084384, 435450095733216, 145282105084384, 435828052855264, 145282105084384, 4407177775584, 4682055682528, 4682055682528, 4682055682528, 4407177775584, 295228003453408, 435965491808736, 295228003453408, 920935081349262680620161473125200319161478195618, 145282105084384, 2027518974465496054922791531171718301039146161076545322279252848208759088006286938109577853631236, 1361150318080364132033523507455018969506, 145282105084384, 435828052855264, 145282105084384, 4407177775584, 294953125546464, 435828052855264, 294953125546464, 4407177775584] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_14 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨3, 1, false⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [567906887010784] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_15 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨3, 1, true⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [5709013910045569556225324786449879809746053538, 5709013910045640544658937567296363625125554594, 39660269144544, 39660269144544, 5709013910045559415020522960614667836120410530, 5709013910045559731933173017672018210296211874, 39866427771360, 39935147313632, 39866427771360, 39591549602272, 435828052855264, 698259437772162337305024719527707726096802, 145213385411040, 145213385411040, 435553174948320, 435828052855264, 435553174948320, 435828052855264, 145419544037856, 145419544037856, 145419544037856, 145144665868768, 259522429214974276387664824788162192650597395996647205241791463317759333029190091953306052232182532, 11429175514275208438636829439568838839393882531, 11429175515604441505024184004322114843650859427, 11429175518262907637798746740467697893154783651, 11429175523579839903348013883753350081527447971, 11429175523579839903348013883753350081527447971, 4152485580124520179459016361989217527007887137620066163294772601291775036116537274163229979808332548, 154353076144608, 4152612300060424269332715002131300522881676384870035714485732925543463191176376882753978901839955716, 145213385411040, 4152358860188616089586197447381726074040063283256832743524919912660609996145847716107446215138048772, 145213385411040, 154078197975520, 154353076144608, 154078197975520, 154078197975520, 145419544037856, 145419544037856, 145419544037856, 145144665868768, 435828052855264, 145213385411040, 145213385411040, 435553174948320, 435828052855264, 435553174948320, 435828052855264, 145419544037856, 145419544037856, 145419544037856, 145144665868768, 16609562159240172045475696334777792084091935771637666072670418475590789518409134306256478207850281732, 154353076144608, 16609688879176076135349394974919875079965725018887635623861378799842477678169277571548886766005470980, 182688402925800636937797909114254905164717664674, 145213385411040, 145213385411040, 154078197975520, 154353076144608, 154078197975520, 154078197975520, 145419544037856, 145419544037856, 145419544037856, 145144665868768, 15458150323313202431919006572162375984440133962932193702241368933313352032902646474656549387805985464307870687911884525898364481023587826324480393347255348346613509695088423, 435828052855264, 487174734566999988799251017049380838160140348745252902552624421593479257771416018757057284, 154078197975520, 435828052855264, 154078197975520, 4407177513440, 4682055682528, 4682055682528, 4682055682528, 4407177513440, 33220898397069394464367111715644841756157038975906500304072013416756350243297812334371109579265374980, 33218880282637318031624155776104249872557402118614543757398821240229834670003590046358855245813836421, 132875483511050356341133278098443285083283145012113968850080707242747294713841466095594603837956258564, 247330401761035016939758681372259324959931102472879683804362718731216567364222961370570669080837792986695349918029956413340262909242973509379036500839968543848192902238465191, 435828052855264, 266241052405943060237449087309158480886730103645094965850724224021627101754078039953208042995586177860, 1361150318080364132033523507446429034914, 154078197975520, 435828052855264, 154078197975520, 4407177513440, 286157032393184, 435828052855264, 286157032393184, 4407177513440] = some [] := by
  decide +kernel

private theorem solve_1_0_0 (N : Machine4) (h11 : N 1 1 = none)
    (hAlive : ∀ q a, ¬ (q = 1 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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

set_option maxHeartbeats 0 in
private theorem tv_1_0_1 : checkTree 4 (baseTable 1 0 1) 107 startPos 0 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_0 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨0, 0, false⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [565192467941856] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_1 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨0, 0, true⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [576359382419936, 572167494699488, 576359382419936, 571892616464864, 571892616464864, 572167494437344, 572167494568416, 572167494437344, 265751980780636284726475655235570891989100614416299901364090604277679584392484014490487208238862346085, 572167494568416, 44401913301472, 431430006213088, 44401913301472, 79586285455840, 46028825882825888476990511675046829416843335139, 79586285455840, 2078206948827074159261904541285963143385724758122264224254102127311923270024780167913625706058644101, 149955029502432, 290692517857760, 149955029502432, 431430006213088, 290692517857760, 290692517857760, 290692517857760, 9217541147104, 572167494568416, 48868679453152, 431430006344160, 48868679453152, 149955029633504, 290692517857760, 149955029633504, 431430006344160, 290692517857760, 290692517857760, 290692517857760, 8942662978016] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_2 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨0, 1, false⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [565192467941856] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_3 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨0, 1, true⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [265751093741551359822799672894113895135077878112691192468132577297108134480551190555754046812016835332, 480492077962468498913440731323836685411759769168854143617241257094919323918318453772294349331964052018213789006538848413056797719929305759447771848498134112650404177089835862672884098780449257694832031890086819832030477471606617302837560660969141727141036032623495561, 5887419191214617685426690609184947226636583331, 149175448158882680526609150318052669547259370245433347358638746189983026977523461330997213316210357236924617241252248005027753006597295112049251874739129750608142763900822355533144141540109683944384945163655183798559812413872526990148514407801824463962377206783244662393178852263676410348806873796849016116820417324063494593744734395837461155669913211945098496683064018777025387422868189629686499175724399524655552441539408159392946324160275715787626396437781612675926071221378936534695625214344363836300, 11596431740109940149721496142957803405333103011, 520058617418676956820345925524929672394985092913769872657834489313939865638366350198854336689384196, 2078206949280259965981172595482038407136386128074139467287357206680113495881670372973633705954474756, 91522607424644616909125602829141181485094666659, 5887419191214617685426690609184947226636583331, 182866808206969776337842491369506880344238981539, 266012516964950083557456542498053903355252731663271221220969561308890131475705278130175507968006306757, 5887440969286100625488352265159822859802116515, 265751220461485375638538265603283712249466114982179713668877273169992984052493808521733501355575166724, 265750967021617344007061080614287921159558752196793055846437262553280635828600196711197567737228655364, 65007327600308038471861828168846803878711944587319721223264936606053020819451403055111856750557956, 5887419191214779944703517461356072578450456995, 259775869083005914616964732569642256852276120391981341502574147219474373344983305699717814349678340, 520058617418676956820345925524929672394985092913769872657834489313935954985728456976980583966223108, 265750967021617314502777719584123030772200658791153470161449670603638378598449356534028558215389870852, 2078206949280259965981169160731293296183498499351062834892308174221306775189983678133828244756200196, 265750967021617284998493479257767391980903332432406266583329526344542678406437118949792538438831143684, 178406642319132961855053500856433243733361059, 265752994540085692953632770211654439233300001777368301011147828734857992289855173895884748117717826501, 508859765274150970539759712876094346630692049111816448212106237383172885413014858017313988291205, 65007327600308038471861828168846803878711944587319721223264936606056630652659749929979580974856964, 259775869083005914616965161913485395721387073982365920551955276276828296830644059483401152072468228, 11596431740109777890444664568402145601126400419, 520058617418676956820345925524929672394985092913769872657834489313939564818936803851848308190522116, 2078206949280259965981172595482038407136386128074139467287357206680112894242811280279220876968426244, 178406642319132961855053500856433243733361059, 266012516964950083557456542498053903354862245718516286584012863228441607434132408822048818920285027269, 178450198462098841978376812806184510064427427, 130774975801719700642468651000925476499299168570026302315562816644973085174755314599740555075299173, 1017719485170713343086122287444633783174250141686880234214028169655260553685791006907754528911013, 508859742585385540595755960704243239131594946335599952690065417906337323624782670412405914219781] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_4 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨1, 0, false⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [567425850935776] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_5 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨1, 0, true⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_6 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨1, 1, false⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [567425850935776] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_7 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨1, 1, true⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_8 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨2, 0, false⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [571892616923616] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_9 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨2, 0, true⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [562959084947936] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_10 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨2, 1, false⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [571892616923616] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_11 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨2, 1, true⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [37426886117856, 7225469009874868069327458629892573015653263778, 37426886117856, 5798215880709482177699809725930237392743082402, 5798215869992581461683925500643292960642869666, 46360418191840, 30916418122263414820415535472422160244349393318892577602248160815232024506511902686725071603113039556721129087045491070629802747369194267560607875400787649100025644580662439, 46360418191840, 37426886117856, 37701764254176, 30191699400769066069276550187192960626631436090916440078657199323576503183492925910095129952389180773392344882318022448989643033842106450362066392173208662644115110519846, 37701764254176, 431430006344160, 149680151398880, 121002670249362310806301819530343950945141893122108623812784827994726622419306173041943623646669840024971894126067877991023889776320445881485709554625467630093001057594151, 149680151398880, 130774973853020764175325444499559946687808218971584445669271658540063017658937681376271874348180677, 431430006082016, 431430006213088, 431430006082016, 431430006344160, 431430006213088, 431430006213088, 431430006213088, 431430006344160, 37426886117856, 259522428735352638529035042150899980433478710654087561862363161793268988389820606979236612944395012, 37426886117856, 46360418191840, 259522428735352638529035042150899980433478710654087561862363161793268988389750006677863616233044740, 46360418191840, 37426886117856, 37701764254176, 37701764254176, 11507228418887904242891381091468995931067689378, 5803769278303807927144205016288581351747135906, 5575186320401922757247502913795822688709026, 11512760049210724518026556193200417804974598562, 260536188218808809248462052399418194511544731935193550523229388806563422300195730930915066136126661, 5575186320401922757247502911825496777992610, 5575186320401922757247502911544020727540130, 5575186320401922757247502912106972828445090, 5575186320401922757247502911544020727540130, 11596431742612474502207129344526156773636207011, 5575186320401922757247502913795829131159970, 11596431742622859095924198999784343670504862115, 149680151857632, 9131526624, 149680151857632, 9131526624, 281758986144224, 9131526624, 281758986144224, 9131526624] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_12 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨3, 0, false⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [563233962854880] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_13 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨3, 0, true⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [39935147510240, 220323773450720, 422496474368480, 220323773450720, 141021497330144, 11774815934116946388038647330471950070179169763, 141021497330144, 261549947706041513832042192611464638426105979853238126950234984499334079993211095526179742098268805, 422496474106336, 141021497264608, 422496474106336, 422496474368480, 141021497526752, 141021497526752, 141021497526752, 141021497526752, 39935147510240, 261549945772448785077180408958667225354293630316625497681084560323631667972336076640556802379889509, 11596431745260718320348492267063823318024061347, 261549945772448785077180408958667225354293630316625497681084560323631667972336076640556802379889509, 11774837712204655255783076845888386730897240547, 11774837712191674513636588661085942339877249507, 11774837712191674513636588661085942340950991331, 11596431745270940654788732708949593845374407075, 11596431745260556061071663053691406952800715171, 11596431745281325248505802364207780742243078563, 79586285586912, 79586285586912, 141021497788896, 9131526624, 141021497788896, 9131526624, 281484108237280, 9131526624, 281484108237280, 9131526624] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_14 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨3, 1, false⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [563233962854880] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_15 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨3, 1, true⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [65007327600308038471861828168846803878711944587319721223264936606051819891867115780808167692401412, 81100759222204911464489730415104134892212169910954409351583326283221513793494877539493987350706948, 65134047534323854210454107994820779397837860485456342918579680433551078182032674851447097752241924, 39660269144544, 5709012559549915697545996090351198199507626402, 39660269144544, 5709012548916091731266669107120741708674935202, 249873308773424563167545884362286185700343638962452352644645201587911774607894356133537590687947358456861190961143536936952519192807398742091956732028319477964391174437841561158162167851037081276365571501187673025350462179229096675742972239939095614373336370661963573423143738894439219074827197283809234673288126134283248562355203711165054338371071228917570464810510164266, 35193503091168, 81100759222204911464462252409143247269111140126341350191191066612797228564464430688193961400695556, 65007327600308038471861828168846803878711944587319721223264936606051819892010522642734630732790532, 35468381260256, 39935147313632, 35468381260256, 35193503091168, 431430006344160, 140746619423200, 130774975801719700642688072486349119750729988125816583617964966582683540770035307871930315931028837, 140746619423200, 130774975801719700642688072486349104131292197928431105350093429026583044254221647983336892582235493, 431430006082016, 140746619357664, 431430006082016, 431430006344160, 140746619619808, 140746619619808, 140746619619808, 140746619357664, 259649149148990098878372452743668281333150204493844719807259403391973921177688944407265171255556868, 11418025108445238161840801624121802571948009890, 259775869083005914616965161913485395721387073982365920551955276276823493120306910386719714813888260, 39660269144544, 39660269144544, 1947557337176421980693737272891758908875164762978305127750160236087551646904656198881895564366418200830083084963920051957759618121667234291239814692829966248567654022210400272034023794517201856688191407982730688864115172188679544574184202428637891297572089593640, 35193503091168, 275742580772775246062381241331527164808153639775756266812632213035344271981636541142961778316245764, 11418025097811414195561474640889094287878302114, 35468381260256, 39935147313632, 35468381260256, 35193503091168, 261549945772448785077180408955391591858643178300088313445740705062389330398942459879182034863668069, 11596431750577650625511840667481644303168700835, 261549945772448785077180408955391591858643178300088313445740705062389330398942459879182034863668069, 11774837712191694835660273569890791282851226083, 11774837712191694835660273569888535083900510691, 11774837712191694835660273569888535084974252515, 11596431750587872959952081109367414830519079331, 11596431750577488366235011454109227942240321955, 11596431750598257553669150764625601727387701667, 140746619881952, 9131526624, 140746619881952, 9131526624, 281758986144224, 9131526624, 281758986144224, 9131526624] = some [] := by
  decide +kernel

private theorem solve_1_0_2 (N : Machine4) (h11 : N 1 1 = none)
    (hAlive : ∀ q a, ¬ (q = 1 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 1 0 2)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 1 0 2) (q1 := 2) (a1 := 1) (rem1 := 103) (cur1 := ⟨2, [1, 1], 1, []⟩) (step1 := 4) rfl ?_ N h11 hAlive h107 hm
  intro m hmem N h11 hAlive h107 hm' hsum1 hrun1
  simp only [moves16, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkTree_sound tv_1_0_2_0 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_2_1 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_2_2 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_2_3 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_2_4 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_2_5 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_2_6 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_2_7 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_2_8 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_2_9 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_2_10 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_2_11 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_2_12 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_2_13 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_2_14 N h11 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_2_15 N h11 hAlive h107 hm' hsum1 hrun1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_0 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨0, 0, false⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [51136422218208] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_1 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨0, 0, true⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [224859258915296, 431567445297632, 224859258915296, 150092468259296, 150092468259296, 431567445035488, 431052049156576, 431430006213088, 431052049156576, 431086408960480, 12845253735356785467407626486040848822555907555, 431086408960480, 431155128306144, 431292567259616, 431155128306144, 431430006213088, 431292567259616, 431292567259616, 431292567259616, 431430006213088, 431567445035488, 431052049222112, 431430006344160, 431052049222112, 275742580527299580473634300934206802446461534369351593402798014207181764835196846632607455705771333, 431155128437216, 431292567390688, 431155128437216, 431430006344160, 431292567390688, 431292567390688, 431292567390688, 431430006344160, 431567445166560, 431567445166560, 431567445166560, 249081520040034035830639043818036221017021971579148765925543103089955282935629851553614805618084996628904839844807264003962153332849373509948518054637029668283228292637479, 431430006344160, 249081520052720181906560410571322773693724364583180697042400004779765678981901855576676505801385602608064353672935061665927819420920327387543008549326627444874886872301351, 1427950035532135094657152554664312025327380898, 431086409026016, 431086409026016, 431155128437216, 431292567390688, 431155128437216, 431430006344160, 431292567390688, 431292567390688, 431292567390688, 431430006344160] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_2 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨0, 1, false⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [51136422218208] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_3 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨0, 1, true⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [65007327600367036685750478250439357481397421869627116068047781528535248425661088474816209138973444, 133816252495993256010506871710141320717938610121001559409754388005091143374346916736211348445997701, 259775869083064898424464593429381471201398450038181703350228015452945035642267500788984398730446596, 65007327600367036684871396731612522781524639921037286588888020410249420099322742294206053971360516, 16625655590858349541444860746195490465834382349661832683695094040563066736245236179190654149676202756, 130014654717276867756838122576392873048286039172731664977819622862893363459221519382139375694857988, 520058617418735853738435829283487634758233769836427296232227633797294315066036246925263763505588996, 132875483511050400604311973760153962484279748194922005924175040707891190635669640479428577137452612356, 1040117234354014502314169636041730436892324963849982323343680453418445861945226463628730337290582788, 12131651666402560238173887988965674254038204835, 12131651669061026370948597118472226262552158627, 275742580346025275209528077816257348938356913614513365626623641656476068856119226362161867731778501, 133816252495993256009627575519393014998123448653036481580751742321780911877459763244770198196071045, 137871290384499358744394198607046574710744015339578529479955827034433714009237091701305279467269605, 12845275523394901242804537374920527221629157859, 12845275523394921525214141026590951168880443875, 65007327600367036684871396731612522781524639921037286588888020410249871328473785653564519499397892, 12131651666485637304823095288079512552301658531, 259775869083064898423586155926319344805239765216471835052190325946617605190150600540122552076814084, 12131651666568714371472302587193350867744981411, 520058617418735853738435829283487634758233769836427296232227633797294766295187290284622229033626372, 2078206949280318747648153902841142210947954772199903683938646078088236637188601809377086489649969924, 12131651666402560238173887988965674236858335651, 12131651669066218667807131946389550069954126243, 12131651666402560871999188103080374985209938339, 483457201561108528310428570556881430372215597779455186149468663156533058773114565277481732, 12131651666490829601681705673869569490465989027, 483457201561109172326193278860595527499095558960577257761426616852058946397994384287300356, 145981366161511564213274842081801964187574641224387496196871320333592649820484889411637368350518597, 12131651666407762676237224642718210035065815459, 12131651669066218667807131946389550069954126243, 12845275523394901242804537374920527222702899683, 12131651669066209160427630234669038844680085923, 12845275523394921525214141026590951169954185699, 483457201561987609829255405256754212320805427258614947267759452653381053556037887347358468] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_4 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨1, 0, false⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [84121771051488] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_5 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨1, 0, true⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_6 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨1, 1, false⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [84121771051488] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_7 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨1, 1, true⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_8 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨2, 0, false⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [150092468718048] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_9 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨2, 0, true⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [505818840041952, 431223847553504, 281896424966624, 431223847553504, 281621546732000, 184115303530643319966301010831739318746068026851, 281621546732000, 16625655590616592352086360695460516926661002736989403389336592512202690466218924948559483892985370437, 281896424704480, 281621546928608, 281896424704480, 281896424966624, 281621546928608, 281621546666464, 281621546928608, 281621546928608, 505818840041952, 487961467665237523218907322056735526203837492994220068558310357250943235959602902091029676344480053316, 92057827351103553398818821122948063074650816931, 529490124417697534926310075785282620262118035160034117075121600887970859635900268156074010867600144452, 7730018540240292457518330921915674515120160489401811610659482545008635784711972902664716689223576921280512189192117777496390964935015492490930303402745129159063073872034599, 8312827795308296637497814802377175202103399109555515153130025685904015608889125688141600553705931973, 265783407324241935634580420329932455778517737749349722227011820718555666083612501013820914998326802500, 92057827351103553398818818761755796848454402467, 8312827795308296637497814802377175202103399109555523650250696534235884604448514063879336145868378309, 92057827351103553398818969878060835333482762659, 92057827351103553398819120994365873818643255715, 431086409091552, 431086409091552, 281621547190752, 9131526624, 281621547190752, 9131526624, 284009433568, 9131526624, 284009433568, 9131526624] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_10 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨2, 1, false⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [150092468718048] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_11 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨2, 1, true⟩) 103 ⟨3, [1, 1], 1, []⟩ 4 [50621025651168, 431052049222112, 50621025651168, 83606374517216, 730753606258705121763356179195387314727166192034, 83606374517216, 5798222675722996630189752010191929537341729186, 149577072249312, 505818839976416, 149577072249312, 43490740704, 281518467713504, 43490740704, 281518467713504, 43490740704, 431430006344160, 149680151398880, 149680151398880, 8312827919058233121826712884984630816181715164186293262454313210590660885571479814802489494525442725, 431430006082016, 431430006213088, 431430006082016, 431430006344160, 431430006213088, 431430006213088, 431430006213088, 431430006344160, 50621025651168, 431052049222112, 50621025651168, 83606374517216, 83606374517216, 149577072249312, 505818839976416, 149577072249312, 43490740704, 281518467713504, 43490740704, 281518467713504, 43490740704, 16625655466866657711775199725952888497956523414477084882266220226248936651010200875331204687966780261, 183402028133428712837439229977596804132988125603, 16625655466866657711775199725952888497956523414477084882266220226248936651010200875331204687966780261, 15460037075081449014429810145961174111998595747319430901952314737170771190147506509663952727614435922918649139212119250600411152604629293838187706684227158849114482791865511, 16617545514718731522178557707968102713728101700711348854907384139659561511213331636098960854568142021, 183402028133428712837439227616404537906791711139, 184115651979786885074827212382581459799800578531, 184115651979786885074827212382581459804095545827, 149680151857632, 9131526624, 149680151857632, 9131526624, 284009433568, 9131526624, 284009433568, 9131526624] = some [] := by
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

private theorem solve_1_0_3 (N : Machine4) (h11 : N 1 1 = none)
    (hAlive : ∀ q a, ¬ (q = 1 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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
private theorem tv_1_1_0_3 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨0, 1, true⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_4 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 0, false⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_5 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 0, true⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_6 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 1, false⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_7 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 1, true⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_8 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 0, false⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [1461518373821466315246093086704165347307201534242, 1461864035340069385674221611348610325209257388450, 1461529524151623746352912861363682607961685928866, 1461551824896988431109352811680182932954078555554, 1462934471120232709974909058286433538964664134050, 1461596426727657475950507839374143314518302824738, 1461685630049730888896152333071745173684711627042, 1461507223406259061596472911047182282969293302178, 1461864035332094017699512116111187482847575320994, 5720173854405238096966034222934340858601838882, 732178774156135248332975104006689430825375672738, 11440336733541068417817171658280945633050274722, 5586075356143392788078330899263313360759202, 22880662596302511040674242167658137121971023266, 45761314282280863411787135967524260056472267170, 91522618314853497465399004966259690797546903842, 10889056510737002694401331101222984264098, 183045224376883329705905844800260084698994223522, 10889046126143285586967142177135725156642, 732180864850997610578894622980277491609266858402, 1462934476548789460166788375791392649062332274978] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_9 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 0, true⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [265783407324241994643148104120469639257280246251130636760098707173822550422352818381235603941926058052, 265783407324241994643148021686452984957173157513736511490119556927293624107414446833038578106534934596, 265751030381584351914916309625397986000138655717580468170293981486010582110594850703102239298296192516, 265751220461485375638481996658728180522463332529214257615586377418443856197006335349482234471582746372, 5720173811880331579255584580063664953357281698, 707788673197885363184178350504855137724834, 12867584426080879236179443942422340457846582178, 5586076685376459175395116722646684217158050, 519108217913558338766848719654810597159657324559830622329528254481917573571986921366939194928373252, 2076432870204038545584615597457459272690127438430780366844903348306904539886405066853335132733392644, 91522617634299148217239185473701370346106567074, 732180864841692979114183405479529570611967863202, 183223630339800797616220645506429442991494052258, 91522617634299148217239185473701370346106567074, 1978658307634536437350233535058906511135625379045827306157829813144706293433189985129995657875154915300968755931963755188512105768181396453213279092626519831691002142102903078, 732180864841692979114183405479529570611967863202, 1978658307634536437350233535058906511135625379045827306157829813144706293433189985129995657875154915300968755931963755188512105768181396453213279092626519831691002142102903078, 1461507223406259061596472911047182001493242849698, 5720173813209564645642901365885078000450447778, 707790002430951750500964171917902230890914, 12867584427410112302566760728243753504939748258, 5586078014609525562711902544059731310324130, 519108217913558338766889936663751928597359540680148137921340837647229016641115960608981306822598148, 2076432870204038545584656814466400604127829654551097882436715931472215982955534106095377244627617540, 91879429558804871253891073751885157179442903458, 732180864843022212180570722265350983659061029282, 183045224379541785697475676546069669145465629090, 183045224379541785697475676546069669145465629090, 732180864843022212180570722265350983659061029282, 707787343964818975867392526840008230873506, 16609455362560969215448367255953181027969739880398672618397533325139825769285459903316302286264688293, 5586075356143392788078330898981837310306722, 91522617634299148217239185473701370346106567074, 10889056510737002694401330819746933811618, 183045224376883329705905844800262055024904939938, 10889056510737002694401330819746933811618, 730753617158291650697836337010827714996833659298, 30199070421569835150192140777262965188721843035753563530401535718808533030354250244617201469045606047749756998367227322121186354694792235958343364811717068559200452895782, 5731313384483973241862500541445074279282643363, 60390769833263542897613602488303893521951144927968636173694885755466877163248334837436072679770881460951880138245206980982733337822886261242283289821134480965752897299494, 966141752000502952930022391737293721610345486411905971249824631253883802365068933360404301496066313871025214475247739003824415943382398304533425530445973992288014914184230, 1038105570387270466634559968891467453231090396826827762363779223628737810614296063355611061801974437, 16641875741928917676433504717361361842130253839194629829928506642777118809487723670829784943422552132, 265783407324241935634580420329932455778517737749349722227011820718555666083612501013820914998326802500, 132907922328675780236131977629040974143624297815136026404165628099260606536398309235361168053269379140, 1461507223416892926127571445333753305869988178338, 291962731839624904820332670532826333609421934698248998321800621417127132507790449763276528491378756, 5731313389800905507411767685307187219958731171, 2076211109836584743642567165571229953261798740734478042972560364007775437963152249773038158701921477, 265783407324241935634580420329932455778517737749349722227011820718555666083612501013820914998326802500, 25088434052803222580384341320905403461009827] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_10 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 1, false⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [1461518373821466315246093086704165347308275276066, 1462934471109598855585015325825697728037594900898, 1461518373864001611428123044694144523611422103842, 1461507223406248758132394218219675054672113080610, 1461551824896988431109352811680183214430129008034, 1461596426387717800622232712313183864414914259362, 1461685630049730888896152333071745173685785368866, 1461507223406259061596472911047182564445343754658, 1461685630730295627808631660911411994536134613282, 6065835363786779480044553230331577156563413410, 732178774156135248332975104006689712301426125218, 11774847912682102261252008821161783709435734434, 5586075356143392788078330899544789411211682, 91522618314853497465399004966259690798620645666, 10889056510737002694401331382699034716578, 182688412453706839735641273307897992390948989346, 10889046126143285586967142177136798898466, 732180864850997610578894622980277773085317310882, 5798232884765285896231022393974024158982478114, 732178774156135329462613518613371408090431269282, 11507238968305983426894122710936499795222636962, 23192873010472868250473941684615339001984887202, 23014564368301985558456989546902106880819108130, 92771464819229061848813125784204090206367815970, 265783407324241935634580420329932455778517737749349722227011820718555657059029473422796265569279752260, 184115660157046735136231706344765275719456565666, 365378207814921753151737901717678708884975425826, 1462934471109598886008629731303203363958471829922, 6065835363786870433975119605791134545018399138, 732178774156135329462613518613371408090431269282, 5887453220624702395635653901657061241042016546, 265783407324241935634580420329932455778517737749349722227011820718555657059029473422796265569279752260, 91344560120515093742627476609787581915596888354, 732180864850997691708533037586959468874322454946] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_11 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 1, true⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [5720173853159086850917675592086757855791716642, 707787427041885625074691640678323674196386, 11440336732128763355383048486263053965782461346, 5586075439220459437285630012820152753629602, 91355362086588923815339758598679864420036811042, 91355710535732650856326345094278437502786246946, 10889129203209934794266255733975118027042, 732180864840446823114445295992821995880318020002, 707787343974960180669218362051981856516514, 5586075356153533992880156734193810935949730, 49961045869575098987712747650622293261318369318586800851952904548266707321479332565014455661245010950442584717308319247986665077976392181581506316790860104649990352658849875742379072618337754253428063989110811332453877476765305959748000047986009916998442941003339578004762809202579213305874895594720415123226268741399948652841394382143290268226986353791266962064516891234034251404415219921376869945259217137461934449610866412471102341638501033899725884285350915910790356896651103681463923597935950074100328619232039507380962998721181576311686097902033448945376753997575574109585998735561041527279888735674990588862974077342469881501067658699887974463388080268198155456741352597622911247203825534081510002025112045604580260888243264714678678520195568736588415844643538813269739645689622146206884757091827440125610286777896104430996861167680229512995815566257281196734581698161656848771666764241776076315330761465440404642608175682440295132650715197324024260222479699261741972823869326342334581179789768457852963439913544524285792745750399564023307793984643825962810611161621263696412976112333060431298923100673028290931141884536407855785549718651406482726834712479101983730233239235266908984915369226772845011489112487823500379605, 2076179430336006914163692683516528596074458259060764287277088874682293727645176363346869925824396036, 93306677263473883097013602577469760281131399586, 732180864850997580155280217502773826020743096738, 184472472082881569544813289498750183714044553634, 10889056520878207496227166031720559454626, 732180864850997580155280217502773826020743096738, 265750967021617344007061081472975607437101826465078963871271777173227749564493480357983539663717235460, 5720173810623871798526132208793763349091359010, 11440304150159630792177657520771190354320826851, 292010248914609752511470019406159825823786702149993426368123332550138744276545574983920190002247748, 11440325928231113732239319176746065987486360035, 132928197518239160296252839338300567627568738030203427658482351144328527584321037353393469287076935748, 5898580454022925812547689818803172297919207714, 823701032441600294241126474296888415124857076130, 11596441949764633717111908000879413518578792866, 91527844371455053832037982907669551980997556642, 91522618314853497465399004966259690797546903842, 732359619252424951140302277721306797309827266978, 91522966763997224506385591461857700930342918434, 91522618314853497465399004966259690797546903842, 732359270803281224099315691225708787179178736034, 707787343964818975867392526840008230873506, 11418035986847155665592305468876532104461068706, 5586075356143392788078330898981837310306722, 91344211671381670165719582941696518607151868322, 10889056510737002694401330819746933811618, 182688412453706829594436471482062217467369925026, 10889056510737002694401330819746933811618, 732180864850997610578894622980279461941620025762, 265752994540561597058428408969809996064162095662804941228978620234122557569294439463672538740909374212, 5720173853159086850917675592086757855791716642, 707787343964818975867392526840008230873506, 11418035986847156299417605582991232852812671394, 5586075356143392788078330898981837310306722, 91522618314853497465399004966259690797546903842, 10889056510737002694401330819746933811618, 182688412453706839735641273307897429440995568034, 10889046126143285586967141895659674704162, 732180864850997610578894622980279461941620025762, 5720173858392942049817735436258571728721058082, 11440336737362618554283108330434867838711802786, 10894363058408834854110427547848047368482, 732180864845680678313345355836993809753247361442, 5731313384486569400195288269542663202692800931, 1932504634386032361707086030194444149743980552182718685723170262244698542969344767462045446918035440460224718257049889036835116557238509589071738407608061294864945197638694, 1038105570387270466634559968891467553195492998882927684100142226144436183365767621861644450547366565, 61856187637031277878416942294789128161730217739853117269727239717553383533270336278533452709884253991192796387218850863897044862657908969429381440008060864660742978109675814, 17819990986512642115880798852713962645229839383340353649254971575414069806029461652410086730373, 132936307594016172501722152760385591613218619609478603005418309010169742455128372566128604945781569604, 5720173858392962332227339087928995675972344098, 707797977829350074401679098144384976202146, 11440336742679550819832375473720520027084467106, 5586085990007923886612617470286214055635362, 92771464813912068736035047685907166175167551778, 10899690375268101228687902124123679140258, 184115660157046654006593291738083579930451421602, 10894363078691244457762097971795298654498, 732180864850997610578894622980279461941620025762, 5720173853159167980556090198772957244424231202, 5731313389803501665744555413404776143368888739, 2076211109836584743642567165571230003244000414158944434251734446343952522683451436006489998720500933, 25088434052803232483904655604229078704456099, 33659982948707628332269549280260643689603751189296800509297998648934251067411124267180846232837] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_12 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 0, false⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [5720173874343738846465536866116636605787707682, 1461859157062691102055122340174315968105951570338, 11440336753313415350930909760292915123525299106, 22880662596302590902662056546111275842424319394, 1462931683527082934211835573624991150242129815970, 22925351539257566236413130635741758442607515938, 1461512820370713254258969163931840003436430010786, 1461523992521467079577250800746065041565791857570, 1461501648219959510070325941724296661096073308578, 1461546336822974730213814074374515117824515550626, 1461591025425990031486940621631415270341962934690, 1461680402632020634033193716145215575376857708962, 1461501648219959428940687527117614965307068164514, 1461859157044081839125699905172816185446647245218, 1462931683516449069680737039338419845865384487330, 91522618334791993461208756753581730932095752482, 1461501648241227158002884595690757574060558821794, 183045224398151048626898111547568325907010595234, 91522618314853497465399004966260535225698261282, 10889056510737002694401331945651135621538, 183045224379541785697475676546068543247706270114, 10889046126143285586967143021563876514082, 10894363058408834854110428673752249178402, 10894363078691244457762099097699500464418, 366805460973413231700370257067583680321212684578] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_13 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 0, true⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [519052777942426419393511313305895973143628104996819535908851560343164516280865074939585951721290500, 519076537930054384839222192472170288434212706451043216570401051897323739479871402123815043294806148, 519108217914502475848458402355669567308597516704717432675814811231216006254966906406499054889704964, 519298297818358610659010548671264665093423018904391507139548763086474934340416846328160981465122564, 521072376921960005972452285278619102906956827965293202521392433177699350731381077515166088168700676, 520058617434727286982840838262111915016119055762164400999816743718614569170803390047579062946409220, 535265009743218071827012543509719737521497458943481087785907075448867635210030067142313651391920900, 2076187350331882902645596309904467792779134184249019524580807294630541627386873732857458692134763268, 2092399582135506966323962653106794666660779382380998752746802045749470430460083828781784486429031172, 2076211110319510868091307189070742108069718785703243205242356786184700850585880060041687783708278916, 2076179430336006914163692683528812221957719055921085057099563813488705805905109154258698180228250372, 2076242790303958959100543398954241386944103595956917421347770545518593117360975564324371795303177732, 2076432870207815093911095545269836484728929098156591495811504497373852045446425504246033721878595332, 2077446629676165071268266036215311554179815796118811508277519007022272338598056389165344050871958116, 2078206949314248900469402394862591498002611597783377820364686186887061604330789057880934817903901444, 2078206949314248900469402394862591498301577399236374651784657165535596340396912042989867853684112132, 2092399582135506966323962653093692132617152228761565705629200829158229888809438047508082381127121668, 966134611155815996728911913910814637124828098555683973129559459350704553517515596847529092917206651577284286844954125475084552429497868080740192026289787051699615954396198, 7729075510322420313168934848811817987312839888191942705291475208817400617282119524663547106521746494304546316440412153700949024585865080103282780704356754095490545920654119, 483067420947368064795291694447182024475908287555480546811381051022451915412064451695554568803681218960275268179585578761756123252133655588672831034238742107116361996592166, 30916536060389669022523146876659773503125081801858590815488542774221420370832341349728204433175011756814128476693055778671753370160389448813041033002825307934495189802705958, 91366501615257940251649851529595696430865981859, 16611462958278733400335040002511673749445595651139278538299857532005190985549425161256165064934914820, 182710702395002680576659683741463340071499473315, 483398192993507815805664100205175763112306295852841049023468593050113127182468726683564804, 182710702394919451391938297938517409570716909987, 182710702397583099680366740069817280101934440867, 483398192993616869141821372983668013134566603991340622816014701365135885466397923962223364, 182710702394919461533143175322216347458665972131] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_14 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 1, false⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [5720173874343738846465536866116636610082674978, 6633485738870509858579736895467394593495330, 5720195694950517651644506455013338172219234594, 5586096613487861268039469853792412038633762, 22880662596302590902662056546112401746626129314, 45761314282280942006124350117749123184424167842, 91522618334791993461208756753581730936390719778, 45766889787667904993583228802473072281355589922, 732180864850997580155280217502773826020743096738, 45761314261179367077225696142834191061820156322, 183045224377215627831297872170882196319495039394, 91528891759573128354771528379386489020122962210, 732186445472500097911267097388901401623469791522, 10889056510737002694401333071555337431458, 732180864843022212180570722265350983659061029282, 10889056510737002694401333071555337431458, 5586080662711347029841691667259794171926818, 91522967464500454344072270175928955930575673634, 732180870284954309255743603972625664801443453218, 10889056520878207496227168283528963074466, 732180864840529900181094503291935834195761342882, 91522618314853497465399004966260535229993228578, 10889056510737002694401333071555337431458, 91523316574270424301728432723872591205175957794, 10889046126143285586967143021568171481378, 10894363058408834854110428673756544145698, 10894363078691244457762099097703795431714, 732180864861631475109993157266850766318365354402] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_15 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 1, true⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [259522429214974283140659469108442709753257241703325991244496969017917027810356391294799772833250052, 22344386515934567120772441828479428009656739, 4152374700180604107572525903714734250790445324095921519219991707544126762805989633442275854806123460, 129777052424183327556005896185476620299156926182496045454536276219773951976017440457488902387673733, 22344386432857500471262911259737455272657315, 33659982945077218026790883021839487643161748202385644993038989774316067802845398050704877065477, 8304749337519443125992669722283302300998920564792503342504764587750666262501390329336899041599961189, 91366501615257940291263932786728991131839766947, 16609467119288243984823418126019098593820753351878907627346867363423107524675660558814064477579231364, 22300830269122432913800288795864203624710563, 182710702397583099719980821326950574802908225955, 16610449198791500681344686649334222595267328015355112258061613395173563869227566787086348669908331268, 22300835586054698463067432081516391997374883, 22300830269162997733007592136712098127282595, 22300840902986964012334575367168580370039203, 182710702395002680616273916114900547353423520163, 483398192993507815805664100205175763112306295852841049023468593050113127182468726683564804, 182710702394919451431552379195650704271690695075, 182710702397583099719980821326950574802908225955, 483398192993616869141821372983668013134566603991340622816014701365135885466397923962223364, 182710702394919481855166860231020066106891043235, 132891703662846079851719616246932306409355424073576115157342709086332917882435354649661994372716264196] = some [] := by
  decide +kernel

private theorem solve_1_1_0 (N : Machine4) (h11 : N 1 1 = none)
    (hAlive : ∀ q a, ¬ (q = 1 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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

set_option maxHeartbeats 0 in
private theorem tv_1_1_1 : checkTree 4 (baseTable 1 1 1) 107 startPos 0 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_0 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨0, 0, false⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [1461518373821466315246093086704165083423404235042, 1461864035329518628633386689838661028344696449442, 1461529524151540669286263654064568523354698460066, 1461551824896739199909405189782841206900710747554, 1462934471099048098544180404315749838553286224290, 1461596426727408243482909617248572186968500246818, 1461518373778941403974692886205436667589133642146, 1461685630048484732896414223585037598953061783842, 1461507223406342138663122118346295980546174527906, 1461864035329518628633386689838658776544882764194, 36327374490080, 435450095733216, 36327374490080, 5575186403478989406454802025382336170863010, 72611258239456, 72611258239456, 145179025738208, 72611258239456, 145179025738208, 43490740704, 290314560735712, 43490740704, 290314560735712, 43490740704, 45123467741664, 435450095602144, 45123467741664, 81407351458272, 81407351458272, 153975118891488, 362882328168928, 153975118891488, 290314560735712, 290314560735712, 290314560735712, 290314560735712, 8839584025056, 51720537737696, 435450095733216, 51720537737696, 130774973853020778695088272469983844462392764031071647811508399752433011888417047095115908607269509, 85805398165984, 85805398165984, 153975119022560, 508017863231968, 153975119022560, 43490740704, 290314560735712, 43490740704, 290314560735712, 43490740704, 1462934476543555584685478712295551255674597972258, 36327374457312, 65894369570515863697201378295277710050749197486712190885515311965335646930967741815963528630688389, 36327374457312, 130774973853020778695088272469983444555974591883636574534409939761398690015903132952116919737571973, 146278537267680, 146278537267680, 43490740704, 290314560735712, 43490740704, 290314560735712, 43490740704] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_1 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨0, 0, true⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [265815340747621533298836416920543777401891162575442522747176074427069114028492418627162159524488624196, 1461864035332094017699512116111187271740537481634, 1461864035332094017699512116111187342109550094754, 49899471243744, 435828052593120, 49899471243744, 184477340840329018340778691716823170057189239202, 86183354960352, 86183354960352, 154353075882464, 435828052593120, 154353075882464, 435828052593120, 295090564237792, 435828052593120, 295090564237792, 435828052593120, 1461507223406259071737677712873019465266682177954, 49899471243744, 435828052593120, 49899471243744, 732183646999629525748157494053562499301337246114, 86183354960352, 86183354960352, 154353075882464, 435828052593120, 154353075882464, 435828052593120, 295090564237792, 435828052593120, 295090564237792, 435828052593120, 265751980780621178533282257877106503731585806591927209352448194705124930142323646959981609831537616741, 49933831113184, 145282105084384, 49933831113184, 145282105084384, 435828052724192, 145282105084384, 145282105084384, 295090564368864, 435828052724192, 295090564368864, 145282105084384, 6065824517286343699423182104043404662915770786, 145282105084384, 11774837108716962028835295570738086770583316898, 400964861357581235234391152719768365390734289479046921677199108969971571155508091591163240301701616207252102481425279446088649843626871901538439262877410899559068483270806980832000213615281360057573058299736510761076479592617580264378970688222200346752628515604769804756818879278339522928366886758021961724578625691522180515685646068090928249262442298757454494910200373959541231138445301431371730637742664340760266890624627755712246346243034169627481612545663448206093394987569340630565897180477438224548093083481211495202945309358984277764531316632632353460612502600872906084505770680439774407673727950995400480682119738004024643377660057400397996315983539780846442726632994026693333286699549727177272643623607801949582269644321191991902300858978817536002026160238023780555055260624063213641341588226208643827586687396172933617830539416501935966804872566416163606875783076616644978852078944063246035993070008340663274658081279162592457402434173548005258802921226259197873026797938963231572623998716665533598067890, 2140996653027932319358838278766224939804670634180214044520545317249805727349476622275245302776601412, 145282105084384, 435828052855264, 145282105084384, 145282105084384, 295090564499936, 435828052855264, 295090564499936, 145282105084384, 1461507223406259071737677712873019465275272112546, 5709012591451397737588778865873276011644234146, 435828052855264, 11418025182882016067000892332567958119311780258, 154353076144608, 435828052855264, 154353076144608, 435828052855264, 295090564499936, 435828052855264, 295090564499936, 435828052855264] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_2 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨0, 1, false⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [1461518373821466315563005736761222433797580036386, 1462934471099131175610829611614861425062473410978, 1461518373864001611428123044694144259726618171682, 1461551824896822276976054397081955045216154070434, 1461596426387219338222337468518500412308178643362, 1461685630048484733213326873642094949327237585186, 1461596426387219338222337468518500412308178643362, 1461685630729049467055203800568844164191847749922, 1461507223406331754386317660969164266112782735650, 45123467741664, 435450095602144, 45123467741664, 81407351458272, 81407351458272, 153975118891488, 362882328168928, 153975118891488, 290314560735712, 290314560735712, 290314560735712, 290314560735712, 8839584025056, 51720537737696, 435450095733216, 51720537737696, 85805398165984, 85805398165984, 153975119022560, 508017863231968, 153975119022560, 43490740704, 290314560735712, 43490740704, 290314560735712, 43490740704, 1462934471099131175610829611614861425068915861922, 36327374457312, 36327374457312, 146278537267680, 146278537267680, 43490740704, 290314560735712, 43490740704, 290314560735712, 43490740704] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_3 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨0, 1, true⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [265750974941613219995542984240676679264655597841697362709122095591123377475972200165043419305779362564, 66908126610545266899107467605273382148916190332068193913416257520349343808137690550603583233161988, 6065825833367596512435903282115348982220849571, 259522429214974275943621113751581657514724297695297674876573863167444751391623239061230031700458244, 11774838382262918976730708815888205160917369251, 91701014066797595736134815502071583240678932899, 6065825833367596512435903282115348982220849571, 183045214849122755164851704042437282099823247779, 356813284472111788864268534979101225514041763, 365733616413783134097448892352275418407061578147, 6065847611439079452497564938090224615386382755, 731110419543094156406033516169571735588609106339, 265750998701600847960988695119842953579946134776410283297176594704651604223004814700018473625198248068, 265750967021617344007061080614287921159558752196793055846437262553280635828600196711197567737228655364, 68935645615223092390569189795691495976205596186951773089144791365569822794462163821490854248130244, 6065825833367434253159071707559691177879929251, 263577467103480378678167483428044777738179415971574553820139070912445636277496911630640490852155524, 265750967021617284998493479257767391980903332432406266583329526344542678406437118949792538438831143684, 356813284472111788864266173786834999183409571, 356813284472111788864266173786834999183409571, 132891703662604380755222203323064246391346892512746351362337674260526682905781885082313451296724843268, 6065825833377818846876292479130797854953726371, 1017719485170713455635925742562127696717030999396767176653037211145532243164559114029340175642085, 365733616413783134097449041106811729913579594147, 356813284472111788864417290091873484335481251, 365733616413783134097449041106811729913579594147, 731110419543094156406033664924684507847430545827, 275742580768998686881808309832806693884988585161943506848359210376849545545142719796876479831440132, 11774838382262756717453877241332547356710666659, 356813284472111788864266173786834999317627299, 356813284472111788864266173786834999317627299, 365733616413783134097449041106811729909418844579, 356856840615077668987589485736586265648693667, 731110419543094156406033816039836624819520053667, 6065825833388203440593513250692897332772643235, 2031478972403432445220431380499017442878548933617726948986173129478830774479174737011982274148549, 731110419543094156406033816039836624827975770531, 356813284472111788864568406396911969487552931, 365733616413783134097449192223693229151035089315, 731107675506087305958264447387002295049118589347, 731110419543094156406033816039836624827975770531] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_4 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨1, 0, false⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_5 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨1, 0, true⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_6 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨1, 1, false⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_7 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨1, 1, true⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_8 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨2, 0, false⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [1461685630049730888896152333071749395825468414242] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_9 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨2, 0, true⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [1461507223406259061596472911047186505110050089378] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_10 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨2, 1, false⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [1461685630730295627808631660911416216675817658658] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_11 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨2, 1, true⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [36327374490080, 6255382894569981061076433140358265295485335842, 36327374490080, 7147410667473513821941565150972681761057712546, 5709012591451387913296627097099918011821762978, 40862860052960, 5709012591451387913296627097095555149682747810, 40862860052960, 36327374490080, 45398345648608, 64912290066787098416287190085261056885186523403598982248938568984754788118499548236965037214449796, 45398345648608, 36327374457312, 435828052855264, 145282104887776, 120884733923607232032024263195018584427111955398887253382780254673215543322889195444002574780446588204844762010508919176415118721511473861346958713345014223239849270012711, 145282104887776, 131788733340253483277459324248777589200121162177578673003341266909562433068848832659478573142402245, 435828052593120, 435828052855264, 435828052593120, 435828052855264, 145282105084384, 145282105084384, 145282105084384, 435828052855264, 36327374490080, 259522428731576090153307638888863834382740228524630190152642741584891815207508839449432629244558084, 36327374490080, 40862860052960, 259522428731576090153307638888863834382740228524630190152642741584891815207438239148042933700360964, 40862860052960, 36327374490080, 45398345648608, 45398345648608, 36327374457312, 5725716372361879690327674471881530583679019426, 5575186320401922757247502913795822688709026, 11445857558403357457898101440851517146630499234, 261549947706041528350595932148635837023857675141187777857298997176062837710106882214121764930348229, 5575186320401922757247502911825496777992610, 5575186320401922757247502911544020727540130, 5575186320401922757247502912106972828445090, 5575186320401922757247502911544020727540130, 11774838384765453329216342017456558529220469155, 5575186320401922757247502913795829131159970, 11774838384775837922933411672714745426089124259, 145282105346528, 9131526624, 145282105346528, 9131526624, 290555079166432, 9131526624, 290555079166432, 9131526624] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_12 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨3, 0, false⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [36567893150176, 1461859157046740305258474538744462389253439007138, 36567893150176, 72851776866784, 1462931683511132137415187772195137571389617252770, 72851776866784, 145419544300000, 284009433568, 145419544300000, 284009433568, 290555079166432, 284009433568, 290555079166432, 284009433568] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_13 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨3, 0, true⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [1041764593067529537051566567926732729382798141337285372305719698836055472270739016277304556260454084, 435828052855264, 2078460388698885796486337513710055995389205519672574754804412409934215313262430910968425137523083012, 145419543841248, 145419543841248, 458669945569742708424877744462805872108036101343564081920653030177688985211435795598859504835904552018944564823767689764445139069660613802550501561609547210565027488194307826767738474968765457331978929441197946390343564769277486129068529558238091280388076738761, 435828052593120, 435828052855264, 435828052593120, 435828052855264, 145419544037856, 145419544037856, 145419544037856, 145419544037856, 11774838387413697147357704939994225073608327587, 11774838392756408395127596844969582199136362979, 11774838392756408395127596844967326000185647587, 11774838392756408395127596844967326001259389411, 11774838387423919481797945381879995600958677411, 11774838387413534888080875726621808708384981411, 11774838387434304075515015037138182497827332515, 23237465143094363306388944011657040166187498786, 46118115638094835062693326547341983627307166114, 145419544300000, 9131526624, 145419544300000, 9131526624, 290555079166432, 9131526624, 290555079166432, 9131526624] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_14 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨3, 1, false⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [36567893150176, 217987311241696, 435690613901792, 217987311241696, 145419543841248, 145419543841248, 435690613639648, 435690613901792, 435690613639648, 435690613901792, 145419544037856, 145419544037856, 145419544037856, 145419544037856, 36567893150176, 5725749044692594988012723017497157766348839202, 732183646999629556171771899531069824072074439074, 5725770907834669658309000539315685257523534114, 732186445476487817392838651398035220279554251042, 5575196954266453855781789482848397472868770, 732183646999629556171771899531068135222214175138, 5575196954266453855781789482848397472868770, 11774838387423919481797945381879995600958677411, 5586080662711347029841691667259794171926818, 11774838392751236380678363437556003482971972003, 72851776866784, 72851776866784, 145419544300000, 284009433568, 145419544300000, 284009433568, 290555079166432, 284009433568, 290555079166432, 284009433568] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_15 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨3, 1, true⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [36327374490080, 6255382894569981061076433140358265295485335842, 36327374490080, 5720162974684517439053279185750196203734215074, 5709012591451387596383977040042567637645961634, 40828500314592, 5709012591451387596383977040038064038018591138, 40828500314592, 36327374490080, 36567892888032, 46374922023309795812986947974242578698492527585361168145650251003766652607000259479598789151985212707530657082405529314572644564068446063605126261445104590501085455506631847, 36567892888032, 36293014718944, 435828052855264, 145144665934304, 130774975786613507449290713969550725914981302536209874470873954760432075718258359805866176659230053, 145144665934304, 130774975786613507449290713969550710295543512338824396203002417204331579202444699917272753310436709, 435828052593120, 435828052855264, 435828052593120, 435828052855264, 145144666130912, 145144666130912, 145144666130912, 145144665868768, 36327374490080, 324395112058961727331733549695246224629798562918614349023682197313824206235749857754834914693560388, 36327374490080, 40828500314592, 11418025182882005925796090506732746145686137250, 40828500314592, 36327374490080, 36567892888032, 36567892888032, 36293014718944, 261549945757342591883783077272582994344606498256812570242319316144175097727373726398671148227246949, 11774838392730629452521053340412046058752967075, 261549945757342591883783077272582994344606498256812570242319316144175097727373726398671148227246949, 11774838392756428677537200496640006146387648995, 11774838392756428677537200496637749947436933603, 11774838392756428677537200496637749948510675427, 11774838392740851786961293782297816586103316899, 11774838392730467193244224127039629697824588195, 11774838392751236380678363437556003482971972003, 145144666393056, 9131526624, 145144666393056, 9131526624, 290555079166432, 9131526624, 290555079166432, 9131526624] = some [] := by
  decide +kernel

private theorem solve_1_1_2 (N : Machine4) (h11 : N 1 1 = none)
    (hAlive : ∀ q a, ¬ (q = 1 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 1 1 2)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 1 1 2) (q1 := 2) (a1 := 1) (rem1 := 103) (cur1 := ⟨2, [1, 1], 1, [1]⟩) (step1 := 4) rfl ?_ N h11 hAlive h107 hm
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
private theorem tv_1_1_3_0 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨0, 0, false⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [36842770565600, 6065835382396052233759140000611473215131265442, 36842770565600, 5753624949616623509777639944791651771145563554, 7136265749942947274654746996628390444400683426, 5798226780285667083282067410522631838935062818, 5720162964133729974603952198292730133909383586, 5731324183316517957737450251608504517784546210, 5753624928681202714177400568108829510311390626, 5798226419410572227057301201109479495365077410, 5887419192398303624663198565872556512426113442, 5709012548916091731266669107120741708674935202, 6065825835880515518059728024624371316177283490, 5709012548916092048179319164178092082850736546, 6422639165380235169970094875049826852650674594, 5798226419410660962599317177167584264589453730, 7136265739309082743556212710057086067655354786, 5709012548916091731266669107120741708674935202, 5887430101362156496786673746988043823496599842, 5709012570183820793463737680263350462165592482, 6065835382396052233759140000609221415317580194, 5720162985318381970151813472321500571956717986, 45638863817184, 5709012570183820793463737680258987600026577314, 45638863817184, 35743258905056] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_1 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨0, 0, true⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [1980482370878150337191020468434182870725235469136385147869904435764686807476443847553881176836, 182699911488198993745512465366330666018675923234, 145282104887776, 182710713369212697811345653530249916542511786914, 182733013944436199107316372115062937819020307874, 182777615435165568620196272748063587803805559202, 145282104887776, 140746619423200, 145282104887776, 145282104887776, 154215636863456, 154353075816928, 154215636863456, 140746619423200, 91356059325158744818251395053250281006332680482, 145282104887776, 182710713539353881271814885261937290627408505762, 182733013944436199107316372115063008188032920994, 182777615435165568620196272748063658172818172322, 145282104887776, 140746619423200, 145282104887776, 145282104887776, 154215636863456, 154353075816928, 154215636863456, 140746619423200, 436549607098848, 435828052593120, 436549607098848, 732223381080748624049771885767112495341706980770, 732267982571477993562651786400113145326492232098, 435553174686176, 435828052593120, 435553174686176, 435828052593120, 435690613639648, 435828052593120, 435690613639648, 435828052593120, 1598529622822652379215801378791917215412504271138, 435828052855264, 7729075279978912907975792634401932325060650714593504981485648629548741490637364620982196041541983129979461026256944894059414546412433919415917400605742433861970547995862054, 145981365194715179127532749405150223356949185985683839186595701448347753316508031464311850757273701, 435553174948320, 140746619357664, 435553174948320, 435828052855264, 435690613901792, 435828052855264, 435690613901792, 140746619357664, 132891703662604369698319631828134674358212929857174999167090607159558565152613626581302547956448328452, 11847270990565727165011722789564687844420002, 435828052855264, 22997643672908105384986881039727184040733602, 267632504629437829457361834759207133575339923375257024415692523262516660033648437172926220980137285, 435553174948320, 435828052855264, 435553174948320, 435828052855264, 435690613901792, 435828052855264, 435690613901792, 435828052855264, 471733979318752, 145282105084384, 471733979318752, 183045214851635582899632312352426018973575850402, 145282105084384, 140746619619808, 145282105084384, 145282105084384, 435690613770720, 435828052724192, 435690613770720, 140746619619808, 72990685981144898199987908473765029307090593778901051947958961800523114829609833092237183951202949, 471733979318752, 145282105084384, 471733979318752, 696898308304478583451171223349789056870818, 145282105084384, 140746619619808, 145282105084384, 145282105084384, 435690613770720, 435828052724192, 435690613770720, 140746619619808, 435828052855264, 696898308304478583451171221097980653250978, 290697872951062421569639183739410523481576235329776111327429253134317564566748533579236746164131018820, 435553174948320, 140746619357664, 435553174948320, 435828052855264, 435690613901792, 435828052855264, 435690613901792, 140746619357664] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_2 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨0, 1, false⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [36842770565600, 12845278341373565604066860463320820745812093346, 36842770565600, 11462637498511945974072445478564507949842083234, 11507238988909007220355516915109875041866656162, 5887451879433639436848335402962919456662133026, 5798248537172498027795867792468807419977308450, 12845278330739670649353920699243880454632286626, 11507238967807432291456862940194942919262644642, 11774848080497137362922937889382125818180839842, 5887453730051237974060245303065406356505794850, 45226546989536, 35193503091168, 45226546989536, 259522428735352645675954374056530194367127047360322610381893155325935882033151006814277803869174532, 35468380998112, 261549948431138814527620256272980899206387809751419521768937890468059250592038774515119623402388228, 35468380998112, 35193503091168, 5887452559998373278725262329712134321272297762, 36327374490080, 15460037188453747126526333398283978424251842081492665368894545119539232409372691564956806091868696410778584541419583083296505544577806117195609345908579175345413562592541479, 36327374490080, 40828500347360, 11418025097811414195561474640889094287878302114, 40828500347360, 36327374490080, 36567892658656, 36567892658656, 36327374490080, 45638863817184, 11507238988909007220355516915109875060657138082, 45638863817184, 35743258905056] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_3 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨0, 1, true⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [64888527662227205379023630576346916515516727786609533056464310015793043044320180216412651197266692, 137871290263649813197874802596060429124515197270809344225972630229429418220793017001882451358526085, 259554109198537216830131692817621450291804274184021850450012398259908253549970947697541158618513540, 132891703662604425018851758099872670463104764400098880442014935658140674720595575911587443990120856324, 12845278235014475546210738680687281276375269795, 12845278237672941678985447810193833284889223587, 275742580527299595780415295141447514448277581479657280727355968757467456709261595261273190355187813, 137871290263649813197215330466108157009042296699804186446875511480159574526150106027960154172534245, 12845278245653836610312245081917386675774849507, 12845278245653856892721848733587810623026135523, 65894367138477742804977658573102794829917290552459787782155509974033331420510362051976498801453828, 12845278235097552612859945979801119574638723491, 261549948159286314719112650912051678599611942572963004241391684278497974375622057056083104352140036, 12845278235180629679509153278914957890082046371, 12845278235014475546210738680687281259195400611, 12845278237678133975843982638111157092291191203, 12845278235014476180036038794801982007547003299, 483457201561108528310428570556881430372215597779455186149468663156533058773114565277481732, 12845278235102744909718556365591176512803053987, 483457201561109172326193278860595527499095558960577257761426616852058946397994384287300356, 137871290263649813197002375906802295316453012774210907034250552150880938884945935294755820002291013, 12845278235019677984274075334439817057402880419, 12845278237678133975843982638111157092291191203, 12845278245653836610312245081917386676848591331, 12845278237678124468464480926390645867017150883, 12845278245653856892721848733587810624099877347, 483457201561987609829255405256754212320805427258614947267759452653381053556037887347358468] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_4 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨1, 0, false⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_5 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨1, 0, true⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_6 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨1, 1, false⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_7 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨1, 1, true⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_8 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨2, 0, false⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [91355362086588923815339758598684086560793598242, 91701023615825818209747610226359520945092209058, 91366512416746354922159533258201347215277992866, 91388813162111039678599483574701672207670619554, 92771454621402181651017241693707774173501237666, 91433414992780084519754511268662053771894888738, 145282105346528, 140746619881952, 145282105346528, 145282105346528, 154215637322208, 154353076275680, 154215637322208, 140746619881952] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_9 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨2, 0, true⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [16611591410683584059192077539395479132527943913347340842963795346372637477049196820087750948298128132, 290692517988832, 16611718130619488379596133640756118683642957175005254122536041832310303497925497996796045438773315332, 290417639754208, 290417639754208, 8312827795429146184845791812934050549217151406186313887622918370541032689089063790643317023917210277, 290692517726688, 290692517857760, 290692517726688, 290692517988832, 290692517857760, 290692517857760, 290692517857760, 290692517857760, 92771453919715468706855671814669670096987881891, 15460037076880685021907034573432239055852890857448400491104682941893493809300865927988616793106099594941010560836925503094774374192027422544032079066912773578321295076670631, 8320937871206158390314885840370916342201897069257222515637693836685135474178422540571224247189636293, 265783407324241935634580420329932455778517737749349722227011820718555666083612501013820914998326802500, 92771453919715468706855669453477403870791467427, 265783407324241935634580420329932455778517737749349722227011820718555661270501556551321714789120686148, 92771453919715468706855820569782442355819860387, 92771453919715468706855971686087480840980304291, 8304781079860899187339320055543320192894524613527288690522013865185282404734916782151686356826562052, 16609688879172357219330207012467171383320423992142402863912656686824952755236476345021912283505706756, 290417640212960, 9131526624, 290417640212960, 9131526624, 284009433568, 9131526624, 284009433568, 9131526624] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_10 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨2, 1, false⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [91355710535732650856326345094282096691442129186, 91433765483950335297125310251481992194107152674, 154353076144608, 182777615435165576226099874117439961599518484898, 145282104887776, 145282104887776, 154353075882464, 154353076144608, 154353075882464, 154353076144608, 145282105084384, 145282105084384, 145282105084384, 154353076144608, 91355710578267947038356303084261272994588956962, 91355710535732731985964759700959306455893186850, 183045214851635582899632312352427707821288630690, 91355710620803324033112025623860308688078149922, 16641875556304015254961889229252783185694980687190625475883746715110751061024483306377964779972278340, 91344560120515093742627476609787581915596888354, 183045214851635582899632312352426018973575850402, 183045214851635582899632312352427144877777660322, 91522968125126778390380260834956276863532570914, 182688401564671169254044055260756475437644818850, 182733013944436199107316372115067371066814934434, 182777615435165568620196272748068021051600185762, 145282105346528, 140746619881952, 145282105346528, 145282105346528, 154215637322208, 154353076275680, 154215637322208, 140746619881952] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_11 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨2, 1, true⟩) 103 ⟨3, [1, 1], 1, [1]⟩ 4 [36327374490080, 280287985237557760148065148403991122731638782242, 36327374490080, 732180859395928952379429880578830528771840321954, 5720162964133729974603952198292730133909383586, 146278537365984, 103846333621070872457360983282723234, 146278537365984, 43490740704, 290314560735712, 43490740704, 290314560735712, 43490740704, 435828052855264, 145282104887776, 145282104887776, 8312827919179082669174690324937759488077282281182727669844270189024891441828204903149269331304774309, 435828052593120, 435828052855264, 435828052593120, 435828052855264, 145282105084384, 145282105084384, 145282105084384, 435828052855264, 36327374490080, 732180859396012029446079087877942115281027508642, 36327374490080, 146278537365984, 146278537365984, 43490740704, 290314560735712, 43490740704, 290314560735712, 43490740704, 16625655466745808166228020861172750071810747930453522731566721165336289439652538444725337417062562661, 184115654702040628145476080669318411155325190563, 16625655466745808166228020861172750071810747930453522731566721165336289439652538444725337417062562661, 15460037075081229340904692359791325924395828433276811501136628274509350090561299955737023651914727408942027662819435821172172761112430709312055617666810280943476199385652391, 16625655590616593274995628745961843853826600032809472647826044871518970469140778175414120776307311813, 184115654702040628145476078308126144929128776099, 184115654702045820442334920089578319253946270179, 184115654702045820442334920089578319258241237475, 145282105346528, 9131526624, 145282105346528, 9131526624, 284009433568, 9131526624, 284009433568, 9131526624] = some [] := by
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

private theorem solve_1_1_3 (N : Machine4) (h11 : N 1 1 = none)
    (hAlive : ∀ q a, ¬ (q = 1 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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

end OMA.BB4HoleA1

open Turing Turing.BusyBeaver OMA.BB4HoleA1 in
theorem OMA.solution :
    OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1_H1_R1_H2_R1.H2 := by
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
  · exact solve_0_1_1 N h11 hAlive h107 hm
  · exact solve_0_1_2 N h11 hAlive h107 hm
  · exact solve_0_1_3 N h11 hAlive h107 hm
  · exact solve_1_0_0 N h11 hAlive h107 hm
  · exact checkTree_sound tv_1_0_1 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact solve_1_0_2 N h11 hAlive h107 hm
  · exact solve_1_0_3 N h11 hAlive h107 hm
  · exact solve_1_1_0 N h11 hAlive h107 hm
  · exact checkTree_sound tv_1_1_1 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact solve_1_1_2 N h11 hAlive h107 hm
  · exact solve_1_1_3 N h11 hAlive h107 hm
