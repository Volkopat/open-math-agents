import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1_H1_R1_H1_R1

/-!
FAR nonhalting certificates for hole0 0 (write-0 transition at state 1 blank).
Every machine in this branch either halts at the missing (0, 1) entry within
107 steps or hits a leaf certified by a finite automaton invariant.
-/

namespace OMA.BB4Hole00

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
  | halted01
  | done
  | missing (q : State) (a : Symbol) (rem : ℕ) (cur : Position) (step : ℕ)

def stepLoop (tb : Table) : ℕ → Position → ℕ → StepRes
  | 0, _, _ => .done
  | rem + 1, cur, step =>
    match tb.get cur.state cur.head with
    | none =>
      if Nat.beq cur.state.val 0 && Nat.beq cur.head.val 1 then .halted01
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
    | .halted01 => some certs
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
    (h01 : N 0 1 = none)
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    {rem : ℕ} {cur : Position} {step : ℕ}
    (hsum : step + rem = 107)
    (hrun : N.multiStep (Machine.init []) step = some cur.view) :
    match stepLoop tb rem cur step with
    | .halted01 => False
    | .done => True
    | .missing q a rem' cur' step' =>
      tb.get q a = none ∧ cur'.state = q ∧ cur'.head = a ∧ ¬ (q = 0 ∧ a = 1) ∧
      step' + rem' = 107 ∧ N.multiStep (Machine.init []) step' = some cur'.view := by
  induction rem generalizing cur step with
  | zero => simp [stepLoop]
  | succ rem ih =>
    unfold stepLoop
    cases ht : tb.get cur.state cur.head with
    | none =>
      simp only []
      by_cases h0 : (Nat.beq cur.state.val 0 && Nat.beq cur.head.val 1) = true
      · rw [if_pos h0]
        simp only [Bool.and_eq_true] at h0
        have hs : cur.state = 0 := Fin.ext (Nat.beq_eq.mp h0.1)
        have ha : cur.head = 1 := Fin.ext (Nat.beq_eq.mp h0.2)
        have hnone : N.multiStep (Machine.init []) (step + 1) = none := by
          rw [Machine.multiStep_succ, hrun]
          simp [Machine.step, Position.view, hs, ha, h01]
        have hnone107 := Machine.multiStep_eq_none_mono hnone (by omega : step + 1 ≤ 107)
        obtain ⟨r0, T0, hr0⟩ := h107
        rw [hnone107] at hr0
        contradiction
      · rw [if_neg h0]
        have hne : ¬ (cur.state = 0 ∧ cur.head = 1) := by
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
    (h01 : N 0 1 = none)
    (hAlive : ∀ q a, ¬ (q = 0 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N tb)
    (hsum : step + rem = 107)
    (hrun : N.multiStep (Machine.init []) step = some cur.view) :
    CertProp N := by
  induction holesLeft generalizing tb rem cur step a b with
  | zero => simp [checkTree] at hCheck
  | succ holesLeft ih =>
    unfold checkTree at hCheck
    have hstep := stepLoop_sound hm h01 h107 hsum hrun
    cases hsl : stepLoop tb rem cur step with
    | halted01 => rw [hsl] at hstep; exact hstep.elim
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
      N 0 1 = none →
      (∀ q a, ¬ (q = 0 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d)) →
      (∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩) →
      Matches N (tb.set q1 a1 m) →
      step1 + rem1 = 107 →
      N.multiStep (Machine.init []) step1 = some cur1.view →
      CertProp N)
    (N : Machine4)
    (h01 : N 0 1 = none)
    (hAlive : ∀ q a, ¬ (q = 0 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N tb) : CertProp N := by
  have hstep := stepLoop_sound hm h01 h107 (rem := 107) (cur := startPos) (step := 0) (Nat.zero_add 107) rfl
  rw [hsl] at hstep
  obtain ⟨_, _, _, hne, hsum1, hrun1⟩ := hstep
  obtain ⟨q', w, d, hNqa⟩ := hAlive q1 a1 hne
  let m : Move := ⟨q', w, match d with | .left => true | .right => false⟩
  have hm_cmd : N q1 a1 = m.command := by cases d <;> simpa [m, Move.command] using hNqa
  exact hbranches m (mem_moves16 m) N h01 hAlive h107 (matches_set hm hm_cmd) hsum1 hrun1

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
private theorem tv_0_0_3 : checkTree 4 (baseTable 0 0 3) 107 startPos 0 [51136422218208, 12845253756014580679348398458832883851408310755, 51136422218208, 275742580527299594880895463177335482441862617321122554647059734070044067339242318715840127894583621, 267877834424728777550606397787958930280836336678054975308008101361268067839468090805426279168533516836, 398658890834808893782269112532125432001401740271565980644248130658663915183954310339008613717639877156, 12131651666570012483763281655103656328896449443, 6422660901228610327455508829472338303278927651, 6422660895911678061906241686186686114906263331, 6422660895911679963381990912803336531314233123, 6422660895911679329556681353955670043672203043, 6422660901228610327455508829472338303278927651, 12131651667733091416852316068886855501129993123, 12131651669062324483239500628518805792196135843, 6422660895911700245791745680201212307212357411, 6422660900896302060858670188284019302215208739, 6422660900896322343268273839954443249466494755, 282409062914737679354124477203977430472010270410344048456105595074363198162815930187960294112626397732, 275742580346025275209529090799372135091887623479270312745525659844591776369448817089662747267332229, 398658890834808893782269167488137353776458800701644535297793015090354061183084582970178143045473194532, 265783407324241935627377226042670592627422026887847208341317793067520492140078834609866402066613326372, 12131651671729877135526373818151430115947725731, 12131651666735517579964183069517634447146764195, 415284546425304637509015491266743011663566802824416617978812173469642049681395097089093099132170195492, 12131651667068474883668178003699102329753308067, 6422660900906037612531169979638829845324251939, 12131651667734389491076621219244393580906959779, 398658890834808893782268288191946605372519567748536917404660462780900618822862053620923766600563872292, 12131651669066218705893129861304576887753024419, 12131651671729877135526373818151430115947725731, 6422660900906037612531169979638829845324251939, 265783407324241935627376786394575218425501221154387766224371104011348633774019181851175366176530944548, 12131651677057193994792710616694145496002118563, 145981366161511564213268455539724288271881429846542257345921347165125922597158215216167798993088005, 6422660895578741669499737020668215455710987043, 6422660895911678079251909456697849955851462435, 6422660895578721387089982253270339679804457763, 6422660895911679349378229203037594434416176931, 6422660900906037612531170053425806140162458403, 12131651667734389491095964106145203942540465059, 12131651669066218705912472748205387249386529699, 6422660895578741669499737020668215455710987043, 6422660900906037612531170053425806140162458403, 6422660900906057974168936219360567680966116131, 398658890834808893782269112532125432001401740268656633640885544779124240749598645248232413665369444900, 265783407324241935627377226042670592627617269860224675659796141461739943396285282273611011396102443556, 265783407324241935627377226042670592627617269860224675659796141461739943396285282273611011396102443556, 84121771051488, 47099263715181964460818972740890008150495217123, 84121771051488, 266061430859474523585696293692852176158101581907293639967096377796995765407699722950918855787767298500, 282409062914737679354124532159989352247067330843150115967300782879916166577862828878990763139875394084, 3872085448091902035521382213226048046959657324396786882457633193082726142346884888099663026341105324767197964056563411072200104542699793624426927512284101577161757086967591, 120989300558304, 543202168277472, 120989300558304, 50620623489504, 543202168277472, 50620623489504, 50620757707232, 543202168277472, 50620757707232, 2092399581527482679457669467722148107008580298106980133936834838111037580251437006993077225286181413, 2092399581467057906232562305940393817152819106794186735352167771535374538301889644358568023399997893, 79210280921441, 79210012477793, 79210012477793, 79210012477793, 79210280921441, 265783407324241935627377226042670592627422026887847208341317793067520492140078834609866402066613326372, 1054309866722027980569944732688254368036664903925529856480654038995902273577787659499500531068589061, 79210280921441, 79210213812577, 79210012477793, 79210213812577, 267877834393662890902574256826906000056169375740195075443506923768977155333688181672444026952784181700, 46385726960117187922632912377470430283100604835, 267877834393662891017825365423305530987382444819041920914385015486212466998212745066267542033841682884, 46385726960439111595512520802941270723568601507, 46385726965101811921585350324300729209699977635, 46385726961114112722423399966836490068420479395, 282409062667177383456259804305160573558310008875690348699606260001169395104441423455094394772020165060, 46385726962432961195093495981673390294208350627, 46385726965101811921585350324300729209699977635, 46385726965101811921585350324300729209699977635, 398658888854809924785148197031100848465441315307720584974537413345552857176497276920577294205071030724, 46385726970418744187134617467586381398072641955, 150092468718048, 184115303551770369948286087058711806107543687651, 150092468718048, 184115652000903712395555452783325302867133243875, 282033864051168, 558887340512, 282033864051168, 558887340512] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_0 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨0, 0, false⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1464361707966427880182233562712715619175492508066] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_1 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨0, 0, true⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_2 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨0, 1, false⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1464361708008963176047352079576068745752065629090] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_3 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨0, 1, true⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [] = some [] := by
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
private theorem tv_0_1_0_7 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨1, 1, true⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1464361708604457242099975301969248428021896993186, 1464361707923892503187476631242680796809914243490, 1464361708073098346981988873926087743413494504866, 1978643213742763555983185601363957702722776201882800570436150790737774918132755934102367742928740747292704012974262552363181897845853097508908507781602747883961321380962630951, 36354818312289, 1982507751266005760017608113074030216992459428305450490290723121820881475053676086405937511088838621904971671133151550585890938969270300909867025405260665390469061619970211111, 36354818312289, 1170446223457, 71539190401121, 71539190401121, 71539190401121, 1170446223457, 141907934578785, 71539190401121, 141907934578785, 71539190401121, 282646498773089, 282646498773089, 1464361707903289471788111635706024078516394416546, 1464361707902624855254917977276219883845428730274, 1464361708584518822163201563875691322117691824546, 1464361707902624855254917977276219883845428730274, 1464361709266412789071485150475162760389954927010, 36423539886177, 36423539886177, 71607911975009, 71607911975009, 71607911975009, 71607911975009, 71607911975009, 141976656152673, 212345400330337, 141976656152673, 71607911975009, 1978643213742763555983185601363957702722798915592936130263418037528815959459588763731680017216790440888521567732570163143574821504487520104700620348933334820968465652492795175, 36354818312289, 1982507751266005760017608113074030216992482142015586050117990368611922516380508916035249785376888315500789225891459161366283862627904723505659137972591252327476205891500375335, 36354818312289, 1170446223457, 71539190401121, 71539190401121, 71539190401121, 1170446223457, 141907934578785, 71539190401121, 141907934578785, 71539190401121, 282680858511457, 282680858511457, 1978643213742763555983185601363957702722798871230221021748130406187280427989445319651717334140159002014278085320541204108089824441936260279822750277530288425963031941509807399, 1982507751266005760017608113074030216992482142015586047535740490525013931199704726938280308313322079354219033313371127220808834204943961347014517459447581314927921444103912743, 559595260034724369045381705416062454647927085471940053823217882874708830164547208761542563454293412, 48526596127501115561852874647350190729308690850, 2857282989205985254438987472019897879758920098, 4192909424698580460411050536406131657304561282875621916457206846265121447158496693093300536902234532, 8345268222528830582595841504395374236508709808155498483470314110133047188197967325763214819972690340, 2854495396056168926546295507235816834570672546, 368231301247615742008998928628150807992474818978] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_8 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨2, 0, false⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1464361708604457318159011315663012517824089315746] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_9 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨2, 0, true⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1464361708242990299242515319482158734773457017250, 265750998701117921836539516307040573723322589464009286307112863670835762805302116086125265035871665285, 1464361708243073376309164526781272573088900340130, 1464361708583521897363411076286325262332371949986, 1464361707902624875537327580927890307792680016290, 1464361708583854205630007905482780615594145241506, 1464361707902624855254917977276219883845428730274, 1464361710626213023688890373316641397793201609122, 1464361707902624855254917977276219883845428730274, 1464361710627542256755277690102462810840294775202, 282360433892438859628675657841622392862339951230628583777107375283638761565845689325104120605563698309, 36425756577953, 282360433892438859628675657841622392862339951230628583777107375283638761565845689325104120605563698309, 36425756577953, 141978872844449, 71610128666785, 141978872844449, 71610128666785, 141978872844449, 141978872844449, 141978872844449, 141978872844449, 141978872844449, 1464361707907941787520467244419505536033801394594] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_10 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨2, 1, false⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1464361709285022052000907585476662543049259252130] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_11 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨2, 1, true⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1978643213742763555983185601362787047016407663205669750366770880660035202439962339008425093865467340518626591817261701292285323606638431423287340470655399583366719442944785191, 8563507977185230991457912223950038116162623906, 36284018458657, 14272520568615849320871234621076020871432264610, 36284018458657, 1099646369825, 71468390547489, 1099646369825, 71468390547489, 1099646369825, 141837134725153, 1099646369825, 141837134725153, 1099646369825, 8563507977517557005163144615617012331780790690, 36354885421153, 14272520568948175334576467012742995087050431394, 36354885421153, 71539257509985, 71539257509985, 71539257509985, 71539257509985, 1170513332321, 141908001687649, 141908001687649, 141908001687649, 71539257509985, 365399103959902392855908768665907111637444208547, 730775907089203030570776322827369907074021468067, 1464361707903289471788111636849722211086386616738, 265750982861125933825305306526566344403230507920474919524452909458835999422518541084238751037116133701, 1464361708584518822163201564982495966540264921506, 1464361707902624855254917978456811504562840033698, 1464361709266412789071485151508180428517689817506, 36425756577953, 36425756577953, 141978872844449, 71610128666785, 141978872844449, 71610128666785, 141978872844449, 141978872844449, 141978872844449, 141978872844449, 141978872844449, 8563507982169854990410350170780337042761996706, 36284018458657, 14272520573600473319823672567906319798031637410, 36284018458657, 1099646369825, 71468390547489, 1099646369825, 71468390547489, 1099646369825, 141837134725153, 1099646369825, 141837134725153, 1099646369825, 8563507987486787255959617314065989231134661026, 14272520578917405585372939711191971986404301730, 25690545761778642244199584505443937496943582626, 2855889192631077090492641194479952177811970466, 48526596127501115561852874093947868518022142370, 2857282989205985254438987472019897879758920098, 94198696858946062197159453270955730560179263906, 185542898321835955467772611624971454644493515170, 2854495396056168926546294916940006475865020834, 368231301247615742008998928333002902813121993122] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_12 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨3, 0, false⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1464361710646151519684700125103962593499599100322] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_13 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨3, 0, true⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [8563508295867722842887770861594288508722239906, 259554108715552098212705728623475626724630521594603134533357242422868125915871867969826322575801477, 14272520844763045307182576395367144687418759586, 25690546282836057156720322554205310394492279202, 519060720658253167091715036827436429918439096505822265461197216345135704539925336824765031565503109, 48526596478417347013899544689296735109278357922, 50969930178927962024203641799229466582230935458945682420565987045328083178010088670865980955526246820, 45694401221514779139412934858162254402279178659, 2076211109836584743643453385868175345478104665934181969773637946154096805167203277429838328899845253, 45694401221599154280276794753721214414431996835, 45694401221599156181752695096065316659486804899, 71539391727713, 71539391727713, 71539391727713, 71470672250977, 45694401222762233213365696941314950830638517155, 45694401224090168205538361130691242181022187939, 71539391727713, 94198698911274128253946798179068731329845680546, 48528167200638402070376401678698182275314506146, 4152374885322109258062580100180822539604234733700997537702522669477687434271808003146548939441580677, 48528167200721479137025608977812020590757829026, 91366501612763032073801651777490706915171505059, 94199744237769888581306318289175506230073907618, 91366501612929186207100066375718383546058413475, 141979007062177, 91366501613261494473696857793241873850670516643, 141979007062177, 141979007062177, 141841568108705, 141979007062177, 141979007062177, 4152374885322109258062689797537648374383950987679078022736190188743574274492242353957959805436215109, 4152374885322109258062799709556578474620672274262135610687943449012415606974856461248151926886989637, 185542899693599287682663686719434430188989995426, 8304733559402423817928220410557931123334961368206360961785574567001546463502684904544808777231116933, 368231298535990671172512384545565727006598912418] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_14 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨3, 1, false⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_15 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨3, 1, true⟩) 102 ⟨1, [1, 0, 1], 1, []⟩ 5 [1978658307636336002868050864758374850535177631883901214068831768622633537495068014867582885643807225336196911236033527688925922937632910193487791105957686834612562456250099494, 5731313379247521885093877531856671395272458659, 1978658307636336002868050864758374850535223060690504536580072358327084688372309855743046341294899247314712604438298055046370323110506562192944096871479350524184700559095179046, 1978658307636336002868050864758374850535859063982951051737440614189400800653695627999534720410187555013932309270001438050591925530737690185332377588782642178194633998046537510, 5731313379496753085041499429198186341602427299, 5731313379247521568181227474799321021096657315, 5731313379829061351638328625653539603375718819, 5731313379164444818444670232742833079829135779, 5731313381822910951219303804385659174015467939, 5731313379164445135357320289800183454004937123, 519060720658253167091715037456358065769729361648138919397474527811293060142614503770350416109251205, 48526595797852613172003274654285780999593810338, 45694401221514779139490306405765495848813199779, 45694401221599154280354166301324455860974422947, 45694401221599156181830066643668558106029231011, 71539391727713, 71539391727713, 71539391727713, 71470672250977, 45694401222762233213443068488918192277180943267, 2076211086633117774303174599481588791034548470941636706690844424492820715034954271880815166091305029, 45694401224090168205615732678294483627556209059, 71539391727713, 94198696210365836755932374509181300549264365986, 1134140325921, 94198696252984209687700098667036579422853421986, 1134140325921, 1134140325921, 1168500064289, 1099780587553, 1168500064289, 1099780587553, 1237219541025, 1099780587553, 1237219541025, 1099780587553, 48526421552096097655962120132458005496222210466, 4152374885322109258062580105212195701387858245241319160220484219345737385274869049263848107908278917, 48526421552179174722611327431571843811665533346, 91366501612763032073879023325093948361705526179, 91366501612763036510656124123896853600168579491, 91366501612929186207177437923321624992592434595, 141979007062177, 91366501613261494473774229340845115297204537763, 141979007062177, 141979007062177, 141841568108705, 141979007062177, 141979007062177, 4152374885322109258062689802569021536167574499219399645254151738611624225495303400075258973904406341, 4152374885322109258062799714587951636404295785802457233205904998880465557977917507365451095355180869, 185542896992690996184649263049546999408408680866, 185542897035309369116416987207402278281997736866, 185542897120546114979952435523112836029175848354, 1099780587553, 1099780587553, 141979007062177, 1099780587553, 141979007062177, 1099780587553, 185542899677648572015654299748685216823200733602, 185542896950072704382519953498373416323824769442, 8304733559402423817928220410557931123334961368570029326367735716208723664944423239291009003889371781, 368231301258249606540097463800165827907278625186] = some [] := by
  decide +kernel

private theorem solve_0_1_0 (N : Machine4) (h01 : N 0 1 = none)
    (hAlive : ∀ q a, ¬ (q = 0 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 0 1 0)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 0 1 0) (q1 := 1) (a1 := 1) (rem1 := 102) (cur1 := ⟨1, [1, 0, 1], 1, []⟩) (step1 := 5) rfl ?_ N h01 hAlive h107 hm
  intro m hmem N h01 hAlive h107 hm' hsum1 hrun1
  simp only [moves16, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkTree_sound tv_0_1_0_0 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_1 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_2 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_3 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_4 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_5 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_6 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_7 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_8 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_9 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_10 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_11 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_12 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_13 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_14 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_0_15 N h01 hAlive h107 hm' hsum1 hrun1

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
private theorem tv_0_1_1_3 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨0, 1, true⟩) 102 ⟨2, [0, 0, 1], 1, []⟩ 5 [1464361707966427799369507798163091273760663165346, 1464361708008963095551538965083501750711412087714, 1461551814199018829399767798421969011063156399522, 1464361707923892503187476631537828701989267069346, 1461596415859557075374175537540156215589164046754, 1461507212538480583425360059303781806537148750242, 1461685619180633567322991015776530624641179343266, 1464361709285021981012473972695816059233879751074, 1464361710646151458837471314148951321657845242274, 5798215891249846979000126464971378168970631586, 259775868603384255515419077315554859628040130175772315154547246164857244383613264793466844185902213, 11507228440145169443294931998744234347667151266, 354088120756577, 72613144045921, 2233651953697, 72613144045921, 2233651953697, 91433404103570399133930106529839607573515604899, 183045216231363797043582874137294921141155027362, 182777604885892962424121285749461831702529975203, 2233651953697, 283719376576865, 283719376576865, 283719376576865, 5720168387290531641744781863380854846151252386, 11440331308785119417610355256290035205600762786, 2233383518241, 72602127695905, 2233383518241, 72602127695905, 2233383518241, 183045218953622752693577557043565445989086067106, 2233383518241, 283719376576865, 2233383518241, 283719376576865, 354088120756577, 72613144045921, 2233651953697, 72613144045921, 2233651953697, 91433404103570399134007478077442849020049626019, 182777604885892962424198657297065073149063996323, 2233651953697, 283719376576865, 283719376576865, 283719376576865] = some [] := by
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
private theorem tv_0_1_1_11 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨2, 1, true⟩) 102 ⟨2, [0, 0, 1], 1, []⟩ 5 [8563507998120570974640664310994613331584637346, 1464356481847362916548692909745233325582466439586, 14272520589551189620965427834746645813427985314, 1464356154558199649653784075889497987303452203426, 1464356176378806428775876904465883339887366658978, 37520834822177, 37523051513953, 37520834822177, 37523051513953, 37520834822177, 37525268205729, 37525268205729, 37525268205729, 37520834822177, 25690545772412426913614954882250710777114680738, 1464357529240475998396445400369739239706300799394, 48526596138134901498914008977258840704488069538, 1464356132716325222599442079537064687541188319650, 94198696849641430732738379073717994655029680546, 2854495385422304395757246820781667885255776674, 185542898311202101078149679580846707304242903458, 2854495385422304395757246820781667885255776674, 368231301242298809743681775832526974964351392162, 365466006453036891340314415753593278265355796899, 508464070134240, 8863091168, 508464070134240, 8594655712, 8728873440, 8594655712, 8728873440, 8594655712, 8863091168, 8594655712, 8863091168, 8594655712, 132907923813795856525017077268992158104160142326848007656877358548351224751618509613216216915132805892, 292753632659936, 290554810730976, 292753632659936, 290554810730976, 290554676513248, 290554810730976, 290554676513248, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 730842809582337529055181969915056073701933056419, 72645148674528, 8863091168, 72645148674528, 8594655712, 8728873440, 8594655712, 8728873440, 8594655712, 8863091168, 8594655712, 8863091168, 8594655712] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_12 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨3, 0, false⟩) 102 ⟨2, [0, 0, 1], 1, []⟩ 5 [1464361710630200722888284438316915361274083170722] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_13 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨3, 0, true⟩) 102 ⟨2, [0, 0, 1], 1, []⟩ 5 [265751093741069849903969628955451174890729657689484768061452866597671800023918629345388275563213399909, 1461551817431701339234044605660386410102315309474, 6701399454010997844059480510268830845854833058, 37660490467425, 12421562375505585619925053903178011205304342946, 37660490467425, 86252007721440, 290554810730976, 86252007721440, 8863091168, 154352942057952, 8863091168, 154352942057952, 8863091168, 290554810730976, 8863091168, 290554810730976, 8863091168, 1461596418922098400480332512818656909415735646626, 1461507212538480583425360059303781806537148750242, 1461507212538480583425379402190682616898782255522, 265783407324241994635944827399191121606148642937707463482596690906925202020431751154574505858285599172, 51067300088288, 282409062914737679354124916852056426506184349900845129873882928690140793970324053595987275387857719844, 51067300088288, 83983929444832, 281483705584096, 83983929444832, 8728873440, 149817188157920, 8728873440, 149817188157920, 8728873440, 281483705584096, 8728873440, 281483705584096, 8728873440, 282409062914737679354124916852056426506184349903754476920598163235623999791825155008791890207754080804, 11507228424194451206351019023039263127533283747, 86252007721440, 290554810730976, 86252007721440, 8594655712, 149817188157920, 8594655712, 149817188157920, 8594655712, 290554810730976, 8594655712, 290554810730976, 8594655712, 52201305672160, 37660490467425, 52201305672160, 37660490467425, 86251806394848, 290554810730976, 86251806394848, 8863091168, 154352807840224, 8863091168, 154352807840224, 8863091168, 290554810730976, 8863091168, 290554810730976, 8863091168, 265783407324241994635944827399191121606148642937707463525949339572868733407577187476602920625911527876, 52201305672160, 52201305672160, 86251806394848, 290554810730976, 86251806394848, 8863091168, 154352807840224, 8863091168, 154352807840224, 8863091168, 290554810730976, 8863091168, 290554810730976, 8863091168, 265783407324241994635944827399191121606148642937707463525949339572868733407577187476602920625911527876] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_14 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨3, 1, false⟩) 102 ⟨2, [0, 0, 1], 1, []⟩ 5 [265783407324362844184192764436707262067272322618928033760363760662637854743290679683421168160701674244, 574228609370592, 105438906063949064503574939516963260931740825534957748011266091957259310441302616689025577887200004, 265792024279762565116150339279884493939199149066668175148185010821841653355950946162733190805710697220, 304935685084730081452079659553639456680891665114369546505697037652422371963421164017868075572657092, 265783407324362799927767063419316865183280757793455931527996532667628757510255328628447453762650370820, 86045849291232, 290554810730976, 86045849291232, 290554810730976, 154215503104480, 290554810730976, 154215503104480, 9079834020320, 290554810730976, 290554810730976, 290554810730976, 9079834020320, 574228609370592, 97320910291060870552577929759514207084318515453328651684100852478209261547912253819626033420169988, 291962731840096982364696693457510756471275361680589228946264999914006115548103409120734841579780228, 81647668562400, 290554810730976, 81647668562400, 290554810730976, 154215503104480, 290554810730976, 154215503104480, 9079834020320, 290554810730976, 290554810730976, 290554810730976, 9079834020320, 572029653223904, 97320910291060870552577929759514207084318515453328651684100852478209261547912253819626033420169988, 291962731840096982364696693457510756471275361680589228946264999914006115548103409120734841579780228, 81647668562400, 290554810730976, 81647668562400, 290554810730976, 154215503104480, 290554810730976, 154215503104480, 9079834020320, 290554810730976, 290554810730976, 290554810730976, 9079834020320, 572029653223904, 265783407324362786097634031851382366157033393788359788079492082832161427313610639267628781038559294212, 81647400126944, 290554810730976, 81647400126944, 290554810730976, 149817188157920, 290554810730976, 149817188157920, 9079565584864, 290554810730976, 290554810730976, 290554810730976, 9079565584864, 45363717736928, 1461680397196797010129326214897700193236553882018, 45363717736928, 1462216660428992926207682831623037784304643004834, 81647601453536, 290554810730976, 81647601453536, 290554810730976, 154215368886752, 290554810730976, 154215368886752, 9079834020320, 290554810730976, 290554810730976, 290554810730976, 9079834020320, 265799627475796019048683373518995713911825477452024455085589783605196154291679658348967786622480284100, 45363717736928, 45363717736928, 81647601453536, 290554810730976, 81647601453536, 290554810730976, 154215368886752, 290554810730976, 154215368886752, 9079834020320, 290554810730976, 290554810730976, 290554810730976, 9079834020320, 81647400126944, 290554810730976, 81647400126944, 290554810730976, 154215503104480, 290554810730976, 154215503104480, 9079565584864, 290554810730976, 290554810730976, 290554810730976, 9079565584864] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_15 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨3, 1, true⟩) 102 ⟨2, [0, 0, 1], 1, []⟩ 5 [265751093741069849903969628955447899257234004258296899433929587261822384517897096623799897640754259813, 1461551814199018829399767798421969011063156399522, 37660490467425, 37660490467425, 86252007721440, 290554810730976, 86252007721440, 8863091168, 145144532175328, 8863091168, 145144532175328, 8863091168, 290554810730976, 8863091168, 290554810730976, 8863091168, 1461596415859557075374175537540156215589164046754, 1461507212538480583425360059303781806537148750242, 1461507212538480583425379402190682616898782255522, 265783407324241994635944827399191121606148642937707463482596690906925202020431751154574505858285599172, 282392842763062805396738711853839345015064850475415316293034184577993486975832443103965758775446131236, 74912958515680, 290554676513248, 74912958515680, 8728873440, 140746217228768, 8728873440, 140746217228768, 8728873440, 290554676513248, 8728873440, 290554676513248, 8728873440, 282392842763062805396738711853839345015064850478324663339749419123476692797333544516770373595342492196, 11507228429521768065617355821581978507587660195, 72645148674528, 290554810730976, 72645148674528, 8594655712, 140746217228768, 8594655712, 140746217228768, 8594655712, 290554810730976, 8594655712, 290554810730976, 8594655712, 37660490467425, 37660490467425, 81716320930272, 290554810730976, 81716320930272, 8863091168, 145144397957600, 8863091168, 145144397957600, 8863091168, 290554810730976, 8863091168, 290554810730976, 8863091168, 265783407324241994635944827399191121606148642937707463525949339572868733407577187476602920625911527876, 81716320930272, 290554810730976, 81716320930272, 8863091168, 145144397957600, 8863091168, 145144397957600, 8863091168, 290554810730976, 8863091168, 290554810730976, 8863091168, 265783407324241994635944827399191121606148642937707463525949339572868733407577187476602920625911527876] = some [] := by
  decide +kernel

private theorem solve_0_1_1 (N : Machine4) (h01 : N 0 1 = none)
    (hAlive : ∀ q a, ¬ (q = 0 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 0 1 1)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 0 1 1) (q1 := 2) (a1 := 1) (rem1 := 102) (cur1 := ⟨2, [0, 0, 1], 1, []⟩) (step1 := 5) rfl ?_ N h01 hAlive h107 hm
  intro m hmem N h01 hAlive h107 hm' hsum1 hrun1
  simp only [moves16, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkTree_sound tv_0_1_1_0 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_1 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_2 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_3 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_4 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_5 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_6 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_7 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_8 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_9 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_10 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_11 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_12 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_13 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_14 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_1_15 N h01 hAlive h107 hm' hsum1 hrun1

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
private theorem tv_0_1_2_3 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨0, 1, true⟩) 102 ⟨3, [0, 0, 1], 1, []⟩ 5 [1464356154558199730466509840439122332718281546146, 1464356176378806509271690018958450334928020200354, 1464356220020020066882050375997106339347497508258, 1464356132737592951661329662214942235687895718306, 1464356307302447182102771090074418348186452122018, 39618995554401, 39618995554401, 39584633718881, 39653353195617, 39653353195617, 39653353195617, 39584633718881, 39722074769505, 39653353195617, 39722074769505, 39653353195617, 39868105763297, 39868105763297, 1464356481867301412544212518229042365864361351586, 1464356307281262530107223228800389577748404787618, 11774838382179841909172385832431749912265228707, 1464356307281345607173872436099503416063848110498, 39582553341985, 39653420304481, 39582553341985, 39653420304481, 39582553341985, 39724291461281, 39582553341985, 39724291461281, 39582553341985, 39866025386401, 39866025386401, 1464356830997009873427095374538290401220179818914, 11774838382179841909191728719332560273898733987, 39582553341985, 39653420304481, 39582553341985, 39653420304481, 39582553341985, 39724291461281, 39582553341985, 39724291461281, 39582553341985, 39866025386401, 39866025386401, 1464357529256426795192861087156786471931816728994, 1462931678061619258047733987047641862726990485922, 1462931678061951566314330816244097215988763777442, 1461682836331498467951598474413739614267975457186, 265750967021617314499175682752139188333409686778175578701427336973878131178466541098127994352861541124, 1461861242294415946003118076945742214207116474786, 1462931678066603882046686424994472161653589858722] = some [] := by
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
private theorem tv_0_1_2_7 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨1, 1, true⟩) 102 ⟨3, [0, 0, 1], 1, []⟩ 5 [1464356154537015078471270256425075227418768202146, 1464534887828889581470598933584971618378719451554, 1464356176357704934343098433313085767296348085154, 1464356154558199649653784075889497987303452203426, 1464356176378806428775876904465883339887366658978, 74801150951457, 74803367643233, 74801150951457, 74803367643233, 74801150951457, 1464356830997009802438661761757443917404800317858, 74801150951457, 46028913675635989580919068515465717706152503715, 46028913675635989580996440063068959152694929827, 1464356219999084646086754787089106847051507850658, 1465071153102779714286393533829309671997856307618, 1464356307281844069574067494641149006561827379618, 1464356132737592870532000733503525600505673832866, 1461680392423539241771708623552515522201748789666, 1461501637330913302837325507598165697268422826402, 1461859147516165180706091739506865347135074761122, 1461501637330913302837325507598165697268422826402, 1462216657701417058574857971415564997001726679458, 46028913680790661950901273964093354513348452771, 46028913675551614435027285845593304316686369187, 363122376837600, 290554810730976, 363122376837600, 290554810730976, 290554676513248, 290554810730976, 290554676513248, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 46028913686107594216450541107379006701729522083] = some [] := by
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
private theorem tv_0_1_2_13 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨3, 0, true⟩) 102 ⟨3, [0, 0, 1], 1, []⟩ 5 [493152800340355611003444616353388846231033216485973132312116941581842425570278213373376068545327845924, 365733616413777941818854814728496792933445150627, 365733616413777941818859659894954961400583424931, 66439769274257944515650211869622038848682209864183913126310926270656913314489260171168089479899558469, 66439769274257944515650211869622038848682209864274830221520774776277864783526417575172043569617744453, 66439769274257944515650211869622038848682209864274830222875545087463900511341532099688570987121521221, 365733616413777941818927492225369319940519388067, 1978658307634536437343529631093544991039956491992290361622019866666456950943156454709660673155881810684598497952949090100946175117601082675622752956162484896107205353721027622, 365733616413777941819004863772972561387053409187, 544335603436000, 365555211813490510967745050586174228234461272482, 544335603436000, 508051753273824, 290348652300768, 508051753273824, 508051753273824, 435484052949472, 435484321384928, 435484052949472, 77314132448, 290348652300768, 77314132448, 290348652300768, 77314132448, 365733616413944095952457945908543001593746302371, 544335603436000, 544335603436000, 508051753273824, 290348652300768, 508051753273824, 508051753273824, 435484052949472, 435484321384928, 435484052949472, 77314132448, 290348652300768, 77314132448, 290348652300768, 77314132448, 365733616414276404219054699547134628941196691875, 435553175079392, 9131526624, 435553175079392, 9131526624, 284009433568, 9131526624, 284009433568, 9131526624] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_14 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨3, 1, false⟩) 102 ⟨3, [0, 0, 1], 1, []⟩ 5 [132907923813682560075222912397671509287678051109115462533821751657214337202297824540127040998618428164, 132907923813675951115651560467372241278268368157378427151495855611356182726360312069470963053807855108, 132907923813678783526896425580357641853729660849752632958588249782077216261792367176022108466049171204, 132907923813675006978569938763043774419781270593253691882465057553608019456800318291465307511060427524, 132907923813682560075222912397671509287678051106251574034711442015593325613280268515510551853039350532, 132907923813795856525017516917087532306105353429308954522758010997159485081832438962714285052019077892, 291447929047520, 730932017665050084050120312454633883125184256418, 291447929047520, 292547474229728, 290348652300768, 292547474229728, 292547474229728, 294746564594144, 294746833029600, 294746564594144, 290348652300768, 290348652300768, 290348652300768, 290348652300768, 290348652300768, 132907923813795856525017516917087532306105353431854633188633841789711495383181377651262275403644924676, 291447929047520, 291447929047520, 292547474229728, 290348652300768, 292547474229728, 292547474229728, 294746564594144, 294746833029600, 294746564594144, 290348652300768, 290348652300768, 290348652300768, 290348652300768, 290348652300768, 132907923813675006978569938763043774419781270596163038929180292745096031229770533935520153627204252420, 294815686724064, 290555079166432, 294815686724064, 290555079166432, 290555079166432, 290555079166432, 290555079166432, 290555079166432] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_2_15 : checkTree 3 ((baseTable 0 1 2).set 3 1 ⟨3, 1, true⟩) 102 ⟨3, [0, 0, 1], 1, []⟩ 5 [268898052637889362199852833742574968439710238859908379855629044018116147644529081498704711624428278308, 731110419543078579533722368889959588370022410147, 731110419543078579533727214056417756837160684451, 132877511029541423593096155114349458485592243395702762470997853816046774131613906716123226164805284421, 132877511029541423593096155114349458485592243395793679566207702321667725600651064120127180254523470405, 132877511029541423593096155114349458485592243395793679566207702341855375786634473939853749982531203653, 731110419543078579533795197502559569404775146403, 1978658307634536437343529631093544991039956491992290361622019866666456950943156454709660673155881810684598497952949090100946175117601082675622752956162484896107205353721027622, 731110419543078579533872569050162810851309167523, 114358657790543304473612058051608215497089244578, 72645148674528, 8873675590112, 72645148674528, 72645148674528, 217780750649824, 217780817758688, 217780750649824, 77314132448, 8873675590112, 77314132448, 8873675590112, 77314132448, 731110419543244733667325500070005797030323561891, 72645148674528, 8873675590112, 72645148674528, 72645148674528, 217780750649824, 217780817758688, 217780750649824, 77314132448, 8873675590112, 77314132448, 8873675590112, 77314132448, 731110419543577041933922253708597424377773951395, 145282105346528, 9131526624, 145282105346528, 9131526624, 284009433568, 9131526624, 284009433568, 9131526624] = some [] := by
  decide +kernel

private theorem solve_0_1_2 (N : Machine4) (h01 : N 0 1 = none)
    (hAlive : ∀ q a, ¬ (q = 0 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 0 1 2)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 0 1 2) (q1 := 3) (a1 := 1) (rem1 := 102) (cur1 := ⟨3, [0, 0, 1], 1, []⟩) (step1 := 5) rfl ?_ N h01 hAlive h107 hm
  intro m hmem N h01 hAlive h107 hm' hsum1 hrun1
  simp only [moves16, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkTree_sound tv_0_1_2_0 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_1 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_2 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_3 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_4 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_5 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_6 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_7 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_8 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_9 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_10 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_11 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_12 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_13 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_14 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_2_15 N h01 hAlive h107 hm' hsum1 hrun1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_0 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨0, 0, false⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_1 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨0, 0, true⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [145981365194715179126654310487015194338644540159662711044156589204996299767480860273682974296008741, 145981365194715179126654311115936839561597339419452843865298922059433866527919172776344949775679781, 32078680625261880627239962284127814376757091751078737692195685749415435980360364170884188086230961749779844522166619631258590357502592092207177544106008250499399017978919, 282393096202932725302321992010758841043504976245541567230504502768023817018119153054828951084127146532, 26201135451843916001640837336806061275857478491771672621977775892822521120718517767245280343396295447792563637812386453755168373766506122312149721190927090582684142616827227962367648632428046375041101139510205430128516944874539915991712504291309527330680878933717639767900112829439333531457058140986538903156117216658163867381800067834823893353788029017404794856579818285961514, 282393286282834693162969295596291384757886656510365992151254202260932354294607450834244016745412042020, 282395123721892084546995212679524463908838718964652054230513260784421062447411438872160461056616616484, 282396834440994689099514997680061887602486381667985903437321018868351003454023094957178436091735186724, 69576771379183008211035528450460993759715238630185603299520371095041520115743792451230488704164320663351211113340122255784884088865897633182110587017685127104145916198378534, 32078680625261880627239962284127814376757091751078737692195685749415435980360366203941578764728280224998996767714957627897166025705220639312593690529416257128944311622695, 26201135451843916001640837336806061275857478491771672621977775892822521120718517767245280343396295447792563637812386453755168373766506122312149721190927090582684142616827227962367648632428046375041101139510204941167749618125445436138010697684647066103378874090413172682866465843827604138784713620476041747494506106067391407983921150869632449269984386822826702541905531953221930, 472541914655058258789627028590114585992490640028300795224311902830844778482465921643452564362218018495728181861384728894802470725272819557439104665949897804174656047691662236431381637258096659359649150118033759013925460900141798304050044412402631704576201638761, 282393096202932725302321992010758841043504976248450914233867088646301763315850855031872240528397095460, 472541914656516886946819141369378261600366505462375812279769547586017130064134526924415513893216627535596249646772076457345204756649792325668740721583488964699067249565363446112370728151226127205742439805322601409636416740668394276922152017768776466433076922761, 68935648092638795464561839991892486836653331041736177673670137999632927941520901513851119181273573, 3201491998481280926669090456827455100323767876368674496560480327916803895690680021146036838125130157097854853126105666385763937396012449170037929306198054387266405791620352929920663853009091157299778257631056801656973304280997916843260930217075878206709673702226871859136971821426585835144165060352034605946264418512957166480028874791220179164497468822755100320758289600811, 145981365194715179126660321929740783730676025406533139412732205306168943293441132054223171081748773, 68935648092638795464561839991892486836653331041736166835507971513750081155161821006747427274791397, 68935648092638795464561839991892486836653331087194716472588766095651811012985210227628516010138085, 145981365194715179126653451589688368192771700066554607933264283603144083458360378722999910583006501, 26201135451843916001640837336806061275857478491771690129278540848952453738206326426842912541314896330144244564119780469925569597092886362497656336721812356223856735662390540800990111408672551808887652486421799167148738553820452260511102374017599816145735643907670104530484259910115553449278369611723640858725375896836224397332786540315555273988830099226213665678092814692127018, 72990685981144898199108639012198745929219380360958359606575908369506056945778132792484931172344837, 72990685981144898199112073762931061439241282463498591282292304797980448741135299019899559010673669, 282394870282022164641411108182438834331598840835597544049986774028933185791131932515213885744335213092, 282392842763062805396738711853839345015064850478142829149329717590201148198975430089993746737338700324, 32078680625261880627239962284127814382435519284638166524612277998540471404998448037880260530368901123805007274581422323319831938979335554438633232975878018847742221769767, 137871292197242541952077247388050829783957693571081231719991538862604671553921566648148352784443237, 282392842763062805396738711853839345015064850478142829149329717590201148198975430089993746737338700324] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_2 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨0, 1, false⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_3 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨0, 1, true⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [267859840193964464254131564352664027350999370047361459307387735739067009657478003316621504856334193188, 137871290263649813197874829377640090687236081877744851890776808687185710933523429371650448972503621, 12845278235181927831414213604533892900308913059, 12845278245649638229214616634794435230841473955, 12845278235348081964712911544678484115869436835, 12845278235680390865134757513331623541320453027, 12845278235680390231309438509678933720349019043, 12845278245649638229214616634794435230841473955, 12845278236345006764503399134044543901189311395, 12845278237674239830890432577949042363608599459, 12845278235680428260827747588015882278738889635, 12845278240332705963665349491508783042468809635, 12845278245649638229214616634794435230841473955, 282395123721892084546995212679524463908838718964652054230513260784421062447411438872160461056616616484, 7446115018805182963688482247314431338727380779235194519995902625645826407709586757146666296117372711388821168725472359450569596751966518032404494167812051823206079237964240154176225547708800636342025897741835379264245008463346947597814586716634681966593119702761, 275742580527299595780415291787211560354502060748352179734084519258819393127450513653555048106471045, 275742580527299595780422161288688986817411589391958758768423554530087464414765184617464250443542149, 282394870282022164641411108182438834331598840832870031192336470735820964119148945734259224956950467108, 282392842763062805396738711853839345015064850475415316291679414297088926526992443309039085949953954340, 249081520052720181906560410571328913993193789330737681096854481598882023028790877516283987749914677760034919749687015892381120413084493355899592636784833071042131932374055, 249081520052720181906560410571328913996033003118836299203469768348647233326867034064040584839572113295506883506976436734845364215215828093918203467511023248789487091641511, 282392842763062805396738711853839345015064850475415316291679414297088926526992443309039085949953954340, 267859840193964464254130685915160958826881444833858701451325051766833932076425434788386587452572881444, 137871292318092102805824554545458564780657953034478879503622060117857319640937240038677372115920933, 12845278245669109342443793681851833896061404067, 12845278235347432927615266134675322847206082467, 69576771379183008211035528363052034339964842015030446766168603487701221548521575668556090535626975453736925870659610421009081052559319238931795120857493563339591425622531110, 12845278235680390231319109953129338901165771683, 12845278245669109342443793681851833896061404067, 12845278236346304838727704284402081980966278051, 12845278237678134053544061810734813459165488035, 12845278245669109342443793681851833896061404067, 12845278240341792483177456883309118516007060387, 265783407324241935627376786394575218425501221154387766224371104011348633774019181851175366176530944548, 12845278245669109342443793681851833896061404067, 30931514087135767885790887542085358284177137918983560197119776401871428608841410275371425739369179321433202403451731337903091160600716162706877783504042727777123865914465318, 282392842515562936116115510618436814340370584318605049781465947743946180716036722084032781539430791620, 2071407208302122830763227807840839868814799196631136887665716793965921232546848558502264091558242008435281635746614855069033870850996798814892121746861950146592966758823353382, 30931396149010424764082009428750551024943207737725818123668940867538195660968166105523225869041325532721316801828848259789307748948677086514367296150720819331171044916190246, 275742580527299595780416150579707714436717166770240709430617406960443726074196569835239658671354437, 12845278235014516188749670275008061392088728483, 12845278235347432927634609021576133208839587747, 12845278235014476257755460854327010588644082595, 12845278235680390231338452840030149262799276963, 12845278245669109342463136568752644257694909347, 12845278236346304838747047171302892342599783331, 12845278237678134053563404697635623820798993315, 12845278235014516188749670275008061392088728483, 12845278240341792483196799770209928877640565667, 12845278245669109342463136568752644257694909347, 137871292318092102806703421392357432324208727234255892876498805044871605752881491887487826579728421, 275742580527299595781294588082769840832875852865144708743252433290097995806034301227746738907951685] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_4 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨1, 0, false⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [23014456859012306320990163462478378611585866146, 23014457008218145044895169511242516637944929698, 23014459756729352343913969131530587983175507362, 23014456178447567408510835622811557761236621730, 23014456839073886384216425368921272707380697506, 23014456157179919475952181656350644796751108514, 23014457520967853292480669081491900618010294690, 23014457009547373040680085384146323698225274274, 23014459735461704411355315165069675018689994146, 23014459731474026762253568687505261321364987298, 23014462463037572044412290015352186661208382882, 23014456158509147471737097529254451857031453090, 73126185011680, 23549676955612502321315111887108190062880251298, 73126185011680, 360684989196641, 360684989196641, 72645148674528, 86252007721440, 72645148674528, 70377338833376, 74912958515680, 70377338833376, 74912958515680, 72645148674528, 81647668562400, 86252007721440, 81647668562400, 70377338833376, 290314296762657, 290314296762657, 77043262294496, 86045513746912, 77043262294496, 74775519562208, 74912958515680, 86251672177120, 74912958515680, 77180701247968, 86045513746912, 86251672177120, 86045513746912, 74912958515680, 22836050216859403553016964409525090363355716002, 77043262294496, 86045513746912, 77043262294496, 74775519562208, 74912958515680, 86251672177120, 74912958515680, 77180701247968, 86045513746912, 86251672177120, 86045513746912, 74912958515680, 22880651877397648259769267596204434875961335202, 81922479360480, 22836050216859403552726822212817579361426233762, 81922479360480, 70927094647264] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_5 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨1, 0, true⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [398675109006424366594140062068643631235359227541975554177834674265490359425994121906920023705671596484] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_6 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨1, 1, false⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [73126185011680, 45672100412440693409886701829943075188769839522, 73126185011680, 79210012477793, 79210012477793, 72645148674528, 86252007721440, 72645148674528, 70377338833376, 74912958515680, 70377338833376, 74912958515680, 72645148674528, 81647668562400, 86252007721440, 81647668562400, 70377338833376, 8839320043553, 8839320043553, 77043262294496, 86045513746912, 77043262294496, 74775519562208, 74912958515680, 86251672177120, 74912958515680, 77180701247968, 86045513746912, 86251672177120, 86045513746912, 74912958515680, 72610788936160, 10997242916722250839388602244746978897983385526526078547573790495683462790872411185077842018528433010396427714988876316730870710601428537904821493047808814797056273721729571948678006699449594210401424339334055851898000785353244451556294508526527811300766171064353227997540681006151198367528462708976589196515110370363711663649362709304700124873131186208140025650487665172838384044185511912566409930755688892886351879436154466882706468521775648827156781039097523613371329201547561341186703471110391137058766749384879083982091054315841758779235689112364657837305039634050178621114761567416491975692671194613977432447416050064280106867225102927361350221109806, 72610788936160, 275746542458830361995395577626483424878076168460166774877225440530229075913208756950827000117899845, 77043329403360, 70652216740320, 77043329403360, 70377338833376, 81510229608928, 70377338833376, 81510229608928, 86252007721440, 70652216740320, 86252007721440, 70652216740320, 70377338833376, 77043262294496, 86045513746912, 77043262294496, 74775519562208, 74912958515680, 86251672177120, 74912958515680, 77180701247968, 86045513746912, 86251672177120, 86045513746912, 74912958515680, 275746540525237618834145112873947107762295898479677678457819858713105994032343163666785907439088197, 72645148674528, 86252007721440, 72645148674528, 72645148674528, 77112048880096, 86252007721440, 77112048880096, 72645148674528, 72851307104736, 86252007721440, 72851307104736, 72645148674528, 81922479360480, 8839320043553, 8839320043553, 85839690861024, 86252007721440, 85839690861024, 86252007721440, 85908410337760, 86252007721440, 85908410337760, 86252007721440, 86045849291232, 86252007721440, 86045849291232, 86252007721440, 81922479360480, 70927094647264] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_7 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨1, 1, true⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [79210280921441, 79210012477793, 79210012477793, 79210012477793, 79210280921441, 79210280921441, 79210213812577, 79210012477793, 79210213812577, 79210280921441, 79210012477793, 79210012477793, 79210012477793, 79210280921441, 1046199806413757721291254084594871978834843688155977183117832388746838367539566221257720692360901669, 2092399581648332226804328661177723208960128812576584942614992189549438231686907424274636706765110853, 79210280921441, 79210213812577, 79210012477793, 79210213812577, 47099353529071834159807623881240912700153825699, 72645148674528, 508052155927008, 72645148674528, 72645148674528, 77043262294496, 217780817758688, 77043262294496, 72645148674528, 81441443023328, 508052155927008, 81441443023328, 70446058310112, 47099353528739487864001065097885179675818363299, 72645148674528, 508052155927008, 72645148674528, 72645148674528, 77043262294496, 217780817758688, 77043262294496, 72645148674528, 81441443023328, 508052155927008, 81441443023328, 70446058310112, 47099353529051026943163452752371507294981065123, 47099353539041044128502770188001130790790400419, 47099353529736412663791552687251239461138237859, 217849403017696, 145281971128800, 217849403017696, 145281702693344, 145281702693344, 145281971128800, 145281702693344, 145281702693344, 145281836911072, 145281836911072, 145281836911072, 145281702693344, 47099353531044876542744427931103626865620814243, 47099353539041044128502770188001130790790400419, 47099353533724111862953503044715478602417736099, 1046199790824166229553675245086128487816993179916484051651483219040765625153770238619913838909329541, 363122376837600, 290554810730976, 363122376837600, 290554810730976, 290554676513248, 290554810730976, 290554676513248, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 47099353539041044128502770188001130790790400419] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_8 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨2, 0, false⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [91522607445756175892527830974557297178517199266, 290314296762657, 360684989196641, 290314296762657, 360684989196641, 290314296762657, 275748522457828805774117864284209659926808141390104113070738279090592516085530491795770943705494085, 275748520524236062612867399531673342811027871409615016651332697273469434204664898511729851026682437, 290314296762657, 290314296762657, 290314296762657, 290314296762657, 91388803123770830877583621606880900613267283362, 143013892852192, 156208435038688, 143013892852192, 143013892852192, 147412006472160, 147412073581024, 147412006472160, 147412006472160, 156208233712096, 156208435038688, 156208233712096, 143013892852192, 92057828052779861427239598658850535269244885410, 143013892852192, 156208435038688, 143013892852192, 143013892852192, 147412006472160, 147412073581024, 147412006472160, 147412006472160, 156208233712096, 156208435038688, 156208233712096, 143013892852192, 91344200803603191994916217388709289436120111522, 145282105346528, 140746619881952, 145282105346528, 145282105346528, 154215637322208, 154353076275680, 154215637322208, 140746619881952] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_9 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨2, 0, true⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [184115306274018920761690655252432781739705803235] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_3_10 : checkTree 3 ((baseTable 0 1 3).set 3 1 ⟨2, 1, false⟩) 101 ⟨3, [], 1, [1, 1, 1]⟩ 6 [182733003906095990306300510147246599472411598242, 143013892852192, 156208435038688, 143013892852192, 143013892852192, 147412006472160, 147412073581024, 147412006472160, 147412006472160, 156208233712096, 156208435038688, 156208233712096, 143013892852192, 2815208608941454542145100114833047331147428300081729450200309017089283399406337031482191916083482791902173039837153284854765583291062843911370005852222429409820375115583118181572901712023899527598992159074205715247109166210570608738578641866338579887130166593450307107944130293383227642114074916441883181310957379570905612016724761309856218332116827486206676126278128235744419195598616381508716578072721534825088527886168188504573507920560227969299705799081732385901628611532872639299521961928382765240762730658547005096022605513984692961819003344582017443009957760653178855007977208320094046823942182921383083465318767073430932022464539423052177864131811886, 154352606513632, 154352942057952, 154352606513632, 154352942057952, 154215234669024, 154352942057952, 154215234669024, 154215234669024, 154352807840224, 154352942057952, 154352807840224, 154352942057952, 143013892852192, 156208435038688, 143013892852192, 143013892852192, 147412006472160, 147412073581024, 147412006472160, 147412006472160, 156208233712096, 156208435038688, 156208233712096, 143013892852192, 16641875741928918598441933800213912047250555367663905373215421239486110274985491956626804112108473188, 143013892852192, 145281971128800, 143013892852192, 140746083011040, 140746217228768, 140746083011040, 140746217228768, 140746217228768, 145281836911072, 145281836911072, 145281836911072, 140746083011040, 145282105346528, 140746619881952, 145282105346528, 145282105346528, 154215637322208, 154353076275680, 154215637322208, 140746619881952] = some [] := by
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

private theorem solve_0_1_3 (N : Machine4) (h01 : N 0 1 = none)
    (hAlive : ∀ q a, ¬ (q = 0 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 0 1 3)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 0 1 3) (q1 := 3) (a1 := 1) (rem1 := 101) (cur1 := ⟨3, [], 1, [1, 1, 1]⟩) (step1 := 6) rfl ?_ N h01 hAlive h107 hm
  intro m hmem N h01 hAlive h107 hm' hsum1 hrun1
  simp only [moves16, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkTree_sound tv_0_1_3_0 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_1 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_2 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_3 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_4 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_5 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_6 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_7 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_8 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_9 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_10 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_11 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_12 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_13 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_14 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_0_1_3_15 N h01 hAlive h107 hm' hsum1 hrun1

set_option maxHeartbeats 0 in
private theorem tv_1_0_0 : checkTree 4 (baseTable 1 0 0) 107 startPos 0 [] = some [] := by
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
private theorem tv_1_0_1_3 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨0, 1, true⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [] = some [] := by
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
private theorem tv_1_0_1_7 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨1, 1, true⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [265783407324243882911907990298147970559631235670119628938687261655727140700640365878094949614472082180, 1462934465675714803745386655399432666719699638690, 265783407324245771186071234350820668984908382227623765319315942407111471433076153369901662722142437124, 1461507217983008838793706625630164755234870565282, 576221474195936, 265783407324241994637745625970996761143131008551467653690527810062402279291809095897974322367062815492, 576221474195936, 571754641099232, 571892214270432, 1461507217961741190861147971663703842270385052066, 571892214270432, 97320910292831127581058313721749062936746978328181795385811040149825243377345583921679608307725060, 291962731843401462150812346953504257364760698835872491238515321101349607209961626948166748817784580, 83640264952288, 290554810730976, 83640264952288, 8804687677920, 149679749204448, 290554810730976, 149679749204448, 8804687677920, 290554810730976, 290554810730976, 290554810730976, 8804687677920, 265783407324362844184192434740886716710039687021035923633203080197447905474229329956502249864385737476, 1461507217983008838793706625630164755234870565282, 265783407324241994637745186322914489475241627285854052913293825448182945763887185941572950499189273348, 51173900519636599227525940566175921277657187376315769919534960678449460327679749774373424313245308238241640699228891267376423512607435388756447021451169446502606450217153677499151762908515806061785485005810097204077498939785780890233436709393463566477979091112001171479207711806562583353479063096766628453590484154732870550281342428495443278191409444911921149835639696422699, 83640264952288, 290554810730976, 83640264952288, 8804687677920, 149679749204448, 290554810730976, 149679749204448, 8804687677920, 290554810730976, 290554810730976, 290554810730976, 8804687677920] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_8 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨2, 0, false⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [572304531130848] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_9 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨2, 0, true⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [576187517110752, 1461596415668350741310561062359225751496946745827, 576187517110752, 265751220461005753993829038824317256017160829254141866735554266710039513100153328857399044583949102597, 571823763229152, 572029787441632, 571823763229152, 1461507217961741190861147971663703842270385052066, 571892348488160, 572029787441632, 571892348488160, 282360655652323859374720315775989799728435406586390606183613235446395762293147737900875689036543388613, 79654870845920, 290554810730976, 79654870845920, 8804956113376, 149679883422176, 290554810730976, 149679883422176, 8804956113376, 290554810730976, 290554810730976, 290554810730976, 8804956113376, 572029787441632, 1461596415678818431742864249703605486726399677923, 572029787441632, 488421460994649976970710816934778498532510358465968722870978789950619449975962554146756547081962407621, 79654870845920, 290554810730976, 79654870845920, 8804956113376, 149679883422176, 290554810730976, 149679883422176, 8804956113376, 290554810730976, 290554810730976, 290554810730976, 8804956113376] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_10 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨2, 1, false⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [572304531130848] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_11 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨2, 1, true⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [97320910292831127581058313721749063131942283964346021257109056343344016366945970404632539034759940, 291962731843401462150812346953504257559813004248127439288662203217070930549020181646150483258572548, 551485160578754158249126678266815253934631402135609079167151442206714596388018875611413757980521220, 1038216434862208450472860463563702014687078972798410510074852032309127638645415159196726676081914437, 290348652300768, 290554810730976, 290348652300768, 290554810730976, 290417505995232, 290554810730976, 290417505995232, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 2108619732968210641501211674865387073570137481387809067839107180279275816546482845821801610487214852, 2076306149788512811057953326762567897312569219244016287991970656849299809214188840378174081575465541, 83640264952288, 290554810730976, 83640264952288, 8804687677920, 149679749204448, 290554810730976, 149679749204448, 8804687677920, 290554810730976, 290554810730976, 290554810730976, 8804687677920, 4184799162934116273470436306276958591399712921086944642559602995241322656398185856013564165314786052, 1070530018041966096240601261464402594782422855839994827549761784401849212291803655470681236525232900, 2108619732968270341574586172279579077141766761316796149325849483207053763249480072950379958367367940, 431086274873824, 290554810730976, 431086274873824, 290554810730976, 290417505995232, 290554810730976, 290417505995232, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 149611029727712, 149817188157920, 149611029727712, 149542310250976, 149679749204448, 149817188157920, 149679749204448, 149679749204448, 149817188157920, 149817188157920, 149817188157920, 149679749204448, 8873407154656, 9079565584864, 8873407154656, 8804687677920, 149679749204448, 9079565584864, 149679749204448, 8804687677920, 9079565584864, 9079565584864, 9079565584864, 8804687677920, 33251311180870641596884077175029921143872784091614547814871049204482941538591738515925425347079910148, 33218935722611754430795465746279040733141405270160937516561120920800246274342540932758696127007362437, 290348652300768, 290554810730976, 290348652300768, 290554810730976, 290417505995232, 290554810730976, 290417505995232, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 66437805115254270909713555563728376999745610915912846933776852868596844005879720152806271826084537989] = some [] := by
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
private theorem tv_1_0_1_15 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨3, 1, true⟩) 103 ⟨1, [0, 1], 1, []⟩ 4 [85804962023904, 354088120756577, 85804962023904, 354088120756577, 83640264952288, 83984264989152, 83640264952288, 83640264952288, 83709118646752, 83984264989152, 83709118646752, 83640264952288, 83846691817952, 83984264989152, 83846691817952, 83640264952288, 290829688637920, 85804962023904, 283717229093217, 85804962023904, 283717229093217, 83640264952288, 83984264989152, 83640264952288, 83640264952288, 83709118646752, 83984264989152, 83709118646752, 83640264952288, 83846691817952, 83984264989152, 83846691817952, 83640264952288, 265799623515798081054442861461232670445896795195103067541527664569941472998258955464357488710878706116, 16658095707978888284936390092739011560132949983119440263989784339057190394188305010008999196300097988, 508017829743072, 469219808793067172204750668955621712545155182518698988177397395983456359741921808924919384149626677357633646462946995344816987793243086217473680820520270949661574777430321867012113638678532546442033634937561387142503556673738706398483632227396507072991240076838761, 508017829743072, 91388802443029882866704208122140090680396257187, 435484388493792, 290554810730976, 435484388493792, 290554810730976, 290417371777504, 290554810730976, 290417371777504, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 151775726799328, 151775726799328, 154009143347680, 149817456593376, 154009143347680, 149542310250976, 149679749204448, 149817456593376, 149679749204448, 149679749204448, 149817456593376, 149817456593376, 149817456593376, 149679749204448, 182733003225355042295421134441581768234533955491, 8873407154656, 9079565584864, 8873407154656, 8804687677920, 149679749204448, 9079565584864, 149679749204448, 8804687677920, 9079565584864, 9079565584864, 9079565584864, 8804687677920, 290829688637920, 290829688637920, 290829688637920, 9354443491808] = some [] := by
  decide +kernel

private theorem solve_1_0_1 (N : Machine4) (h01 : N 0 1 = none)
    (hAlive : ∀ q a, ¬ (q = 0 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 1 0 1)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 1 0 1) (q1 := 1) (a1 := 1) (rem1 := 103) (cur1 := ⟨1, [0, 1], 1, []⟩) (step1 := 4) rfl ?_ N h01 hAlive h107 hm
  intro m hmem N h01 hAlive h107 hm' hsum1 hrun1
  simp only [moves16, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkTree_sound tv_1_0_1_0 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_1 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_2 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_3 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_4 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_5 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_6 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_7 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_8 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_9 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_10 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_11 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_12 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_13 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_14 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_1_15 N h01 hAlive h107 hm' hsum1 hrun1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2 : checkTree 4 (baseTable 1 0 2) 107 startPos 0 [565192467941856, 1461864025121151791382348477326858099428379591139, 565192467941856, 265783407324243882917339402572807689643305968769445871975796724827561534756218353760814531801384170244, 265783407324245771191530783459149291195767471979406279704092760132362323224059540141706588681828499204, 265783407324249547739913545231832494300690383065843068395858076063424987540027670071159623945862460164, 265783407324241994643148021686466088090844560892969491012327444363431724464270670326932566545856148228, 265783407324249547739913545231832494300691527067651389573779132214724035932966325855262940164113249028, 265783407324241994643148021686466088090844560892969491012327444201930522976403391769120008721794282244, 265783407324362844191396398412328587448374664987457872674361404242315276884560959237569485815547114244, 97320910298495955585734165887445969491598231675302708255783225846290934185673863306399017263641348, 291962731847178015992244790462267446946799159454041825453815125990426539681290805513126427660333828, 91522258975500889867906899329545675609227657635, 23014456837910807412519240093312799293988689827, 4433748951073, 45850507033492097269698471673173218682523114403, 4433748951073, 91522607424644616908893523604219664434869834659, 182866808206969776337610449923661341989007532963, 365555209771630155270207713791219090122005042083, 730932012900941177578792488724242861331222664099, 265882752040042480690309073072312829681224124211012662892171891713181654047711220544583576202119663109, 23014456837921192006313681296173101733189556131, 4433748951073, 45850507033502481863492912876033521121723980707, 4433748951073, 91522607424644616908970895151822905881403855779, 182866808206969776337687821471264583435541554083, 131788731406660754409992995905682648293619900224050565559667287649849027419782893501030817865937221, 365555209771630155270285085338822331568539063203, 730932012900941177578869860271846102777756685219, 567425850935776, 1461864025121651226389023656289477498078922539491, 567425850935776, 265783407324241994643148021686466088090844560895878838059042679393418534749373607413174854837938107140, 571892616923616, 562959084947936, 571892616923616, 97320910292831133011591506862641312106802604250635985796320696830791990654985658342414945538487044, 291962731843401467609483017779064342022744074115437843257369583582918960315203726632983498550869764, 551485160578754163764072304461711009373608637682354176780749546592929804832786358606262845325914884, 1070656737975936739060448245733048103378793107835764321121577438546561247826621613786326511554605828, 2108873172836256800133024577686521880102334320425248212799226850232824056506244739191276105948672772, 431429536713184, 281758717708768, 431429536713184, 281758717708768, 281758583491040, 281758449273312, 281758583491040, 281758717708768, 281758717708768, 281758449273312, 281758717708768, 281758717708768, 2108619732968210647016157301060282829010258718725828388021914353502686212323695641897672444121133828, 74844171930080, 8863091168, 74844171930080, 8594655712, 8728873440, 8594655712, 8728873440, 8594655712, 8863091168, 8594655712, 8863091168, 8594655712, 149680151857632, 9131526624, 149680151857632, 9131526624, 281758986144224, 9131526624, 281758986144224, 9131526624, 563233962854880, 1461864025131639926522527348878805181746420666851, 563233962854880, 265751980780636284726475874657056309611839796676833200885980282565267410378516828953741049368388570597] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_0 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨0, 0, false⟩) 103 ⟨3, [0, 1], 1, []⟩ 4 [51136422218208] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_1 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨0, 0, true⟩) 103 ⟨3, [0, 1], 1, []⟩ 4 [12845253755993649193642009381884802845974200803] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_2 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨0, 1, false⟩) 103 ⟨3, [0, 1], 1, []⟩ 4 [51136422218208] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_3 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨0, 1, true⟩) 103 ⟨3, [0, 1], 1, []⟩ 4 [265783407324243823925091538273394505047843838937819720671400158273792476601127160218155098115355652868, 265783407324245712242502084883385901909762222160078963352292357680996476865917269083047745611360567044, 265783407324249488848397851043530160752009262265485754001085847323501754282904276219512543467465290500, 265783407324241935634580420329945558912384384100960169067698056548913217696675172171459512767137133316, 265783407324249489194151176832728523227665446365684754799776216294026497051434311875620584610200761092, 265783407324362786104837665827003691538135736156889626993489726411838849454880918821777098693404734212, 265783407324241935634580420329945558912189141128582701749219707993192564952601445949902345613586150148, 265783407324249488848396973464714784903351611488292631846528874160265721786819887052242071337157473028, 265783407324241935634579547903256300730156446100782086602590059799595103615535637774841342580846965508, 265783407324241935634579541033754810508249908175475083856087155683739122592378916600647969168676827908, 265783407324362786104836800269815923578008053718674315629937370232220617131536866493604821880447120132, 145981366161511564213322928592235066978899565543433229410997796071760786573451083792492608327144453, 265783407324241935634579650945778654058766717666160719507538518352448835038366178006179121302507565828, 145981366161511564213707620675687493723668682631801545618363747662642016307368731024329212326696773, 145981366161511564213487796628000392763265815902080487144357710655418528904569551441963909878454085, 265783407324362786104837665827003691538327928457823696385116850612398621785209140740775698502120583940, 265783407324249488963648080558410788075861450850270164437836811206974709424990586228735270962407355140, 265783407324249489194150298395225461101269287680863044931478179258095343799956827144610237804573831940, 265783407324362786104836788248188315689670277680630574230559878246574771635469439452704730628118229764, 275742580527299594880022982820099307000546018067782587562087576756114896896062058650500942363427909, 265783407324362786104836793400314433356099990457645613920008854819470435265033646553703769180196778756, 145981366161511564213271407331058402683297131285204851865312361645515558910246967798410153050551301, 265783407324241950386721455111887923246728364303634822389974319341794108467930495405731879099675390724, 145981366161511564213322928592235066978899565713929141339857471464472324754560121024572245844321797, 145981366161511564213707620677325310483698084170017698579783292682516895894831364720505485856878085, 145981366161511564213707620675687493723668682802491677413246850119093439371162024942278441534238213, 145981366161511564213487796628000392763265816072637439602539034553876887985857432025383643159784965, 265783407324241935634579547903256300730156446100782086602590060443076453293756825778625752661093462788, 265783407324362786104836800269815923578008053718674315629937370868131597990014275814991768312690717444, 145981366161511564213322928592235066978899565623006496990977161238697524806723991963376983060958725, 265783407324241935634579650945778654058766717666160719507538518917703040245901652958523073686724096772, 145981366161511564213707620675687493723668682711530189091161854480570662446789044543909260434304517, 145981366161511564213487796628000392763265815981720344392687965101351799055652922738524294041890309] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_4 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨1, 0, false⟩) 103 ⟨3, [0, 1], 1, []⟩ 4 [84121771051488] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_5 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨1, 0, true⟩) 103 ⟨3, [0, 1], 1, []⟩ 4 [47099263715152108716743742955705732899067134435] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_6 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨1, 1, false⟩) 103 ⟨3, [0, 1], 1, []⟩ 4 [84121771051488] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_7 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨1, 1, true⟩) 103 ⟨3, [0, 1], 1, []⟩ 4 [265783407324243823925090659191875678213143966158779767598829906742445530519837212023373298334947291908, 265783407324362786104837665827003691538135736159753515492600036053459861043898474846393587838983811844, 265783407324245712213688429296782976243728048136481929884539370512106232307789747090805840444402368260, 265783407324243823925091538273394505047648643632183556445528860257598957828137559831672145184628617988, 265783407324245712242502084883385901909567169854666708404242210798880755542578210528349761876919779076, 79201344946209, 79201414154337, 79201344946209, 79201414154337, 79201344946209, 79210280921441, 79210213812577, 79201414154337, 79210213812577, 265783407324249488848396973464714784903351611491196296574793493658020358536796020243867122831980704516, 265783407324241950386722320669075691206901806815683112941331464335419929045573759964697759839154287364, 265783407324249488963648087213240356728333385634938654212021977528198713490625465520294320882317472516, 265783407324241935634580420329945558912189141131492048795934943184680576725571661593957191729729975044, 265783407324362786104836800269815923578008053721538204129047679873841628720554422518221311026026197764, 1978658307749707751789734961775451259153398309878422119076333187397063250485152884542641564562978936994537768037888631273769715928254239926824240561370656828292219194246689958, 506196327401952, 8863091168, 506196327401952, 8594655712, 8728873440, 8594655712, 8728873440, 8594655712, 8863091168, 8594655712, 8863091168, 8594655712, 1978658307749707971463312472991373591242409203705153481138424918678212679573373447250252065622081510881507348197770193929342547563098205001955522134550817884299024538176218150, 224446472784352, 149679883422176, 224446472784352, 149679749204448, 149679749204448, 149679883422176, 149679749204448, 149679749204448, 149679883422176, 149679883422176, 149679883422176, 149679749204448, 83640264952288, 8863091168, 83640264952288, 8594655712, 8728873440, 8594655712, 8728873440, 8594655712, 8863091168, 8594655712, 8863091168, 8594655712, 398658888854809917409077246861530869467591308384273408647113751133273790493333495694141042732885555652, 265783407324241935627377226042657490493199402085131399902283520160409073529463277148678386174864341444, 265783407324241950386721881020980317004932190339129303994765188180693207865462495290070571616699626244, 265783407324241935627377226042657490493199402085131399902283520160409073529463277148678386174864341444] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_8 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨2, 0, false⟩) 103 ⟨3, [0, 1], 1, []⟩ 4 [150092468718048] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_9 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨2, 0, true⟩) 103 ⟨3, [0, 1], 1, []⟩ 4 [505818840041952, 184115303530643319966301664879636666853642863075, 505818840041952, 16625655404810414688934948853339997148698313978719944250049752611969148602669298947383256116826241157, 16625655590616592352086360695565330801971699171344686586427652221624401061133470629318139535594911781, 92057827351103553398514177737967623936622204835, 92057827351103553398519022904461821200779447203, 16625655590616592352086360695565337198131474257174039936464830000923604446369917067767195055227959621, 16625655590616592352086360266116673786620481613148025771589385274540674915057806905009229145084292613, 16625655590616592352086360266116673786620481613057108676379534205088149826127602395722369795966397957, 16625655404810414688934948853339997148698313977493989569061495811274458809781740194726257648769962117, 92057827351103553398586741898008531625916502947, 16625655590616592352086360695565337198131474254263272353510758483747436030356851749895889436525754693, 92057827351103553398664113445611773072450524067, 431086409091552, 92057827351270032050670929565772723998763259299, 431086409091552, 92057827351602989354375037836749780615416514979, 281621547190752, 9131526624, 281621547190752, 9131526624, 284009433568, 9131526624, 284009433568, 9131526624] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_10 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨2, 1, false⟩) 103 ⟨3, [0, 1], 1, []⟩ 4 [150092468718048] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_11 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨2, 1, true⟩) 103 ⟨3, [0, 1], 1, []⟩ 4 [50654882564576, 92771453919902067578359243807731529144939354530, 50654882564576, 83640264952288, 281552559278560, 83640264952288, 83640264952288, 149611029727712, 431086274873824, 149611029727712, 77314132448, 281552559278560, 77314132448, 281552559278560, 77314132448, 50929760471520, 183402028133595191488983032826132816309638005155, 50929760471520, 431429536713184, 283740998112, 431429536713184, 283740998112, 283606780384, 283472562656, 283606780384, 283472562656, 283740998112, 283472562656, 283740998112, 283472562656, 50654882564576, 50654882564576, 83640264952288, 281552559278560, 83640264952288, 83640264952288, 149611029727712, 431086274873824, 149611029727712, 77314132448, 281552559278560, 77314132448, 281552559278560, 77314132448, 183402028133928148792687169431344798941180985763, 83640264952288, 8863091168, 83640264952288, 8594655712, 8728873440, 8594655712, 8728873440, 8594655712, 8863091168, 8594655712, 8863091168, 8594655712, 149680151857632, 9131526624, 149680151857632, 9131526624, 284009433568, 9131526624, 284009433568, 9131526624] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_12 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨3, 0, false⟩) 103 ⟨3, [0, 1], 1, []⟩ 4 [282033864051168] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_13 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨3, 0, true⟩) 103 ⟨3, [0, 1], 1, []⟩ 4 [558887340512] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_14 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨3, 1, false⟩) 103 ⟨3, [0, 1], 1, []⟩ 4 [282033864051168] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_3_15 : checkTree 3 ((baseTable 1 0 3).set 3 1 ⟨3, 1, true⟩) 103 ⟨3, [0, 1], 1, []⟩ 4 [558887340512] = some [] := by
  decide +kernel

private theorem solve_1_0_3 (N : Machine4) (h01 : N 0 1 = none)
    (hAlive : ∀ q a, ¬ (q = 0 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 1 0 3)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 1 0 3) (q1 := 3) (a1 := 1) (rem1 := 103) (cur1 := ⟨3, [0, 1], 1, []⟩) (step1 := 4) rfl ?_ N h01 hAlive h107 hm
  intro m hmem N h01 hAlive h107 hm' hsum1 hrun1
  simp only [moves16, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkTree_sound tv_1_0_3_0 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_1 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_2 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_3 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_4 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_5 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_6 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_7 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_8 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_9 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_10 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_11 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_12 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_13 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_14 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_0_3_15 N h01 hAlive h107 hm' hsum1 hrun1

set_option maxHeartbeats 0 in
private theorem tv_1_1_0 : checkTree 4 (baseTable 1 1 0) 107 startPos 0 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_0 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨0, 0, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_1 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨0, 0, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [265783407324242112653080909623068645468459262263995656150121642139896576426620405737777782594728047364, 265783407324249547732710350944557528415783548570839248938381296888640694283903264082086227370477564676, 265783407324242230670217871572480760273791811374230934085118758166876559843986172525895108810810801092, 265783407324242938773039640263546547133703329360509909641755786425355008152613606406237356812816098820, 265783407324362844184193204125043794662950744818347116577504638291459782556365898687355549105904628484, 265783407324243882910135335858843465576363722242392133121732714641194875491539740711175966541475951364, 265783407324241994635944827399178019671854821849518172517974168010919998030940265987597832082472252164, 265783407324249547732709485387369760455655866132623937574828940709022461960559211753913950557519950596, 97320910291060868753977638642423971764773572204209006820191524319260969357385443604512588563690244, 291962731840096980571372179406295740305859871659837204673318991287056911304471805493277979631384708, 89203323734955546899418858186530169930383779, 2108619732964434091430201241102113839178034463836635854173887939734722308632000118788181336911183620, 89203323734955546899418858186530169930383779, 91433404106065307272474917784332715815883252131, 182777604888390466701191806324698414675027567011, 89203323734955546899418858186530169930383779, 33218999082576874064500666548764917250806651441741588024387190485332728588366148159492657070946077189, 66437868475219390543418756366214253517410857087493495360676447976761114041442241209496348726108359173, 265783407324302419410068246377955467031276160309536161039414174978362092424124054535326700515155243780, 265783407324362844184192764476958247361541304749998463757937580792113602115396650051397723149385806596] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_2 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨0, 1, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_3 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨0, 1, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_4 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨1, 0, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [1461551825088054650771400524885540911831374142754] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_5 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨1, 0, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [5898579793396687966191580854945041509352773922, 5898601571468170906253242510919917142518307106, 527154933241108587672889629050949409171781224997201203442549169656320491646010182536242366284829124, 2798503463671533065861904811818459654560034, 519551760406105089476593666674244076923503013267295718511694635535890902439711804989278063144921796, 5586096613487860958553869595899504842807586, 91522617654227259619041687039688457232453769506, 1038216434862208580118046850718779155577510809907305285761959643281271412767607470757880589902356164, 142974162307169, 519551760406106494102117788484357875595495070992473213183646188328701815201512712150710188442577604, 142974162307169, 508052155927008, 290554810730976, 508052155927008, 8863091168, 435553040861664, 8863091168, 435553040861664, 8863091168, 290554810730976, 8863091168, 290554810730976, 8863091168, 91522966103370986660028273535286467363102300450, 142974162307169, 142974162307169, 508052155927008, 9079834020320, 508052155927008, 8863091168, 145281971128800, 8863091168, 145281971128800, 8863091168, 9079834020320, 8863091168, 9079834020320, 8863091168, 33255374138694598913076819247762908429268548341288425257309551889799844154066977197716900417877570308, 72604344387681, 33264252454071582001292303018707721354717536373079636105138536004283318072383945193047689348140760004, 72604344387681, 296945923394016, 290554810730976, 296945923394016, 290554810730976, 294815552506336, 290554810730976, 294815552506336, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 91525220155120114825979701587579150886658677026, 283719166855265, 91525133085369479247763012953658824657143372066, 283719166855265, 508052155927008, 290554810730976, 508052155927008, 8863091168, 435553040861664, 8863091168, 435553040861664, 8863091168, 290554810730976, 8863091168, 290554810730976, 8863091168, 732180864861631475109838376392570557088463362466, 283719166855265, 283719166855265, 508052155927008, 9079834020320, 508052155927008, 8863091168, 145281971128800, 8863091168, 145281971128800, 8863091168, 9079834020320, 8863091168, 9079834020320, 8863091168] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_6 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨1, 1, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [1461551825258195834231869756635674959620967800098] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_7 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨1, 1, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [1461685619180643951956322166688919854430609775010, 1461507212538490968058691210216171036326579181986, 565226357918176, 97320910291060870553021052843468297282678054492246819985591256291367374217569958279262552526631684, 291962731840096982365143251292168372431349907923486689261622846824004813736584077020589722626914436, 86252007721440, 290554810730976, 86252007721440, 290554810730976, 154352942057952, 290554810730976, 154352942057952, 9079834020320, 290554810730976, 290554810730976, 290554810730976, 9079834020320, 565226357918176, 562958548077024, 567494167759328, 562958548077024, 567494167759328, 72645148674528, 290554810730976, 72645148674528, 8594655712, 145281702693344, 8594655712, 145281702693344, 8594655712, 290554810730976, 8594655712, 290554810730976, 8594655712, 97320910291060869651848948029598114237994938133661353056392835120862571640166705705902280966091524, 1462394018315584507070148876757645493018452613538, 291962731839860947193562285645477949003272726813764877866443862123409590497444976557243219394902980, 1461501640058499555103404147465572378093588355490, 81647668562400, 290554810730976, 81647668562400, 290554810730976, 154215503104480, 290554810730976, 154215503104480, 9079834020320, 290554810730976, 290554810730976, 290554810730976, 9079834020320, 1461507212538490968058691210216171036326579181986, 97320910291060870552577970010499501353300646523758649257920981953956633653882621796181022104302340, 291962731840096982364696733708496050740257492751019226520085129389753487654073777097289830263912580, 81647668562400, 290554810730976, 81647668562400, 290554810730976, 154215503104480, 290554810730976, 154215503104480, 9079834020320, 290554810730976, 290554810730976, 290554810730976, 9079834020320, 1461507212538490968058691210216171036326579181986] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_8 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨2, 0, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [564092553660896, 1461685619180643951956322166688919854430609775010, 564092553660896, 1461685619180643951956322166688919854430609775010, 565226425027040, 572029653223904, 565226425027040, 562958682294752, 567494167759328, 562958682294752, 567494167759328, 5720162985318301157135867840109021604499986850, 11440325949348185115031399222997378267096325026, 77180701247968, 290554676513248, 77180701247968, 8728873440, 145281702693344, 8728873440, 145281702693344, 8728873440, 290554676513248, 8728873440, 290554676513248, 8728873440, 572029653223904, 1461507212538490968058710553103071846688212687266, 572029653223904, 1461507212538490968058710553103071846688212687266] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_9 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨2, 0, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [1461596415540635815550474885798286786233348692386, 12893424910204183797279510262190397650436019802628112916614506592100303721414469241715478454982973825369117281558808226101275869957133520388072940400987028862333394659647946789235237739277327935157607321769524005300241996417249082362119674461370576098840451985296053767436641727710768471728597190681911199863259623836228245377179396892804773683510070397120040736791678147114, 519171600602169245754942001392088978264663682253040712412566497197734480150596796425425119500577413, 1038216434862208565738037154789734929279768230375887464574284882182316043771600508361308816125209221, 4850287357029081957596622856696485984581426219065831157646514499117666221948731012409867645317828886153903308156206097994334807068716543877393783124649729140922437205482681339771211971074040021339904413663634661906035112171700910594958440507787193036373974647496564439060840991907554482443743052616544540660965348944330144137142857187589833268528984052925894688436679179080073748756923358350900854060639162560420627064400051343319868203660532936313025039302149017689032135525913286255895515203628055429260044, 33218999082576874064500639292034564705633178290100867639458547334143690272079830833921731071543249541, 66437868475219390543418729109483900972237383935852774975747143316640924169568691884779359527831767685, 1461596415583254188482241401030322450477763041698, 265751093741069849903969409567033271647334719095886582017581578503775337491395621436236552768149024261, 569624538647008, 1461507217961741231425967178967044690164887624098, 569624538647008, 562958548077024, 85908410337760, 435553040861664, 85908410337760, 145281971128800, 145281971128800, 435553040861664, 145281971128800, 145281971128800, 294815552506336, 435553040861664, 294815552506336, 145281971128800, 562958548077024, 85908410337760, 435553040861664, 85908410337760, 145281971128800, 145281971128800, 435553040861664, 145281971128800, 145281971128800, 294815552506336, 435553040861664, 294815552506336, 145281971128800, 299847055467515784966667068184747484868370978179127825400111181892329601501851590647276775650626413210777510744790920068936726620321734877785504425065254961983161374377458972467300952561161117894063732960038358512314618084644703784351914444562757415643262547556274432778064842516246569831354066557955342999116443605643449599179855971267306082536541555191266479882828496682, 86252007721440, 290554810730976, 86252007721440, 8594655712, 145281971128800, 8594655712, 145281971128800, 8594655712, 290554810730976, 8594655712, 290554810730976, 8594655712, 1462394018315584507070129534018318635246495521186, 1462216657701427443207957007685144502451555064226, 81647668562400, 290554810730976, 81647668562400, 290554810730976, 154215503104480, 290554810730976, 154215503104480, 9079834020320, 290554810730976, 290554810730976, 290554810730976, 9079834020320, 265751093741069849903969628961740391342959187078545081150803747004652403265579087214258216081945129957, 1461507217972375055392246505950275146647130380706, 265751093741069849903969628961737115709463533647357212523280467668802987759557554481726091064975684581] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_10 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨2, 1, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [564092553660896, 564092553660896, 565226425027040, 572029653223904, 565226425027040, 562958682294752, 567494167759328, 562958682294752, 567494167759328, 77180701247968, 290554676513248, 77180701247968, 8728873440, 145281702693344, 8728873440, 145281702693344, 8728873440, 290554676513248, 8728873440, 290554676513248, 8728873440, 572029653223904, 51067300088288, 265783407324362786104837665826993864637816562792849282730551995684986294225993305656630989752243532548, 51067300088288, 83983929444832, 281483705584096, 83983929444832, 8728873440, 149817188157920, 8728873440, 149817188157920, 8728873440, 281483705584096, 8728873440, 281483705584096, 8728873440, 572029653223904, 74912958515680, 290554676513248, 74912958515680, 8728873440, 140746217228768, 8728873440, 140746217228768, 8728873440, 290554676513248, 8728873440, 290554676513248, 8728873440] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_11 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨2, 1, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [551485160572145204080170463423771658209745667380554639902860468115542086395020162706340615150642692, 1038343154798112540360627198532354220001118742392888541710847750239924048473790709019429630976766533, 508052155927008, 290554810730976, 508052155927008, 290554810730976, 435553040861664, 290554810730976, 435553040861664, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 72645148674528, 86252007721440, 72645148674528, 72645148674528, 77112048880096, 86252007721440, 77112048880096, 72645148674528, 81647400126944, 86252007721440, 81647400126944, 72645148674528, 2076432869724416900945720061731220102626608988838494319627966374782560531809408068157386627501568581, 72645148674528, 290554810730976, 72645148674528, 8594655712, 145281702693344, 8594655712, 145281702693344, 8594655712, 290554810730976, 8594655712, 290554810730976, 8594655712, 4184799162813384742358141804291982496201621729247227599318626892632987345355841119957978391085527812, 89203321159566499999540037951247966055432611, 4184799162813502759495103753704097301534170839482505534315742919612970762721607908075304607168281540, 143013959961056, 149817188157920, 143013959961056, 140746217228768, 145281702693344, 140746217228768, 145281702693344, 145281702693344, 149817188157920, 149817188157920, 149817188157920, 140746217228768, 217780817758688, 290554810730976, 217780817758688, 8594655712, 435553040861664, 8594655712, 435553040861664, 8594655712, 290554810730976, 8594655712, 290554810730976, 8594655712, 16641875741929036608374821777080557053285670363264827508694272797213477106623552881641081211139076868, 16641875741929390659782189152574788573239898531047262496122333659145292619197102946629059860054374532, 143013959961056, 149817188157920, 143013959961056, 140746217228768, 145281702693344, 140746217228768, 145281702693344, 145281702693344, 149817188157920, 149817188157920, 149817188157920, 140746217228768, 2276337388000, 9079565584864, 2276337388000, 8594655712, 145281702693344, 8594655712, 145281702693344, 8594655712, 9079565584864, 8594655712, 9079565584864, 8594655712, 33251311180810216821860369037025765634513692103073457667736478432067706553138021020321536161565635332, 89203321159566499999540037951247966055432611, 33251311180810216821862128273396822082535401684535157076518122041571773922899896170003536161232124868, 292547675556320, 290554810730976, 292547675556320, 290554810730976, 294815552506336, 290554810730976, 294815552506336, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 5898949868139659203499771953441952733244265451295893776248822694930170321850532248597801575286532640449807016626168309943023942323373432719387988341296528629594672302409344572564840928635385574084254236848259863218654495372637228434064931900371063341926643344593086587873019913257746279689110349990564577391141223832892350492470936366429642597222375630559374246124419098588007210, 247330430964384240480789279468615489714209956720644319028889248240617308900596395056401334035567537617496812802480411789500215413070551748120061698505453399323012642699650855, 66437995195155287257221477600186400471473549562313613655075234470220688669769310435861836449498136133, 508052155927008, 290554810730976, 508052155927008, 8594655712, 435553040861664, 8594655712, 435553040861664, 8594655712, 290554810730976, 8594655712, 290554810730976, 8594655712, 292547675556320, 290554810730976, 292547675556320, 290554810730976, 294815552506336, 290554810730976, 294815552506336, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 989321635434085678447492215219005423799035556362553008770332847509744555949434541084941507813463722167734990652686250604975951825117364729580889095924500621102153158666222375, 132875736950438766334667420871747810554473907916382862549062145822172197573529634594567519534109392453, 2276337388000, 9079565584864, 2276337388000, 8594655712, 145281702693344, 8594655712, 145281702693344, 8594655712, 9079565584864, 8594655712, 9079565584864, 8594655712] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_12 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨3, 0, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [5720173874343738846233422223166174790715218210, 1461680402651959130028771315510654446311020992930, 5731346067549782962983159671199200533604769570, 1462216655016469948506666548066897655053451057570, 1462216655675683962419938014640989724623871465890, 1462216655059088321438433063298933319297865407394, 1462216657717378179157375998159990187174919199138, 1462216655144325067301966093763004647786694106530, 1462216660429003310841013982535427014094073420194, 1462216655314798559029032154691147304764351502754, 1462216654979168487558039696326477219050158086562, 1462216655655745542483164276547432618719666297250, 1462216657701427443207957007685144502451555064226, 1462216656337639509391428520260003246630295894434, 1462216657701427443207957007685144502451555064226, 1462216654995119223507458686801322903773522221474, 1462216660429003310841013982535427014094073420194, 1462216657722695091140515661651605415416040577442, 22880662766433389769182066200659193655976828194, 1462931683527082934211603421203108825469895612834, 22925351539257566236181015992791296627535026466, 36327106546144, 72602127695905, 36327106546144, 72602127695905, 72645350001120, 290554810730976, 72645350001120, 8863091168, 145281836911072, 8863091168, 145281836911072, 8863091168, 290554810730976, 8863091168, 290554810730976, 8863091168, 91522618334791993460976642110631269117023263010, 1461501648241227158002652443268875249288324618658, 183045224398151048626665959125686001134776400290, 182777604885810047597484598875140645669058904483, 292547675556320, 9079834020320, 292547675556320, 8863091168, 145281836911072, 8863091168, 145281836911072, 8863091168, 9079834020320, 8863091168, 9079834020320, 8863091168, 291413804190176, 2233383518241, 291413804190176, 2233383518241, 292547675556320, 290554810730976, 292547675556320, 290554810730976, 294815418288608, 290554810730976, 294815418288608, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 544301478578656, 283719166855265, 544301478578656, 283719166855265, 508051954600416, 290554810730976, 508051954600416, 8863091168, 435552906643936, 8863091168, 435552906643936, 8863091168, 290554810730976, 8863091168, 290554810730976, 8863091168, 366805460973413231700138142424633218506140195106, 283719166855265, 283719166855265, 292547675556320, 9079834020320, 292547675556320, 8863091168, 145281836911072, 8863091168, 145281836911072, 8863091168, 9079834020320, 8863091168, 9079834020320, 8863091168] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_13 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨3, 0, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [5809366285199834794091636427249307442998188322, 37004748116916890930044771014220329375896115334236096975944125430567402702716868703533844325626299977109579640237557640827215283354298971573780041243346427183132966915346674565015472588407208641853870368673383004118374415957512711475636404697282766430279914774016133623158439949481721872234797130346592955790872888954934265994248279370956475747528016810801072402303119744111055471295636701022301979860297663503991224603692183402615084330050578171247941003876927689006065662798158756246811982134158123213, 11518378493823174931165048152904617320023890338, 916458909231211080024136608503375299624872205406724691390554186479769258399972868165454523592585879857950399157910577909994771430975729915843664136794854965733216946870303119250050289820542939025519967629690014329020036141468367963738297026021672624161205593161, 23070208062794619004896475871681886108458720546, 91525045930548251305486408376673633968753514786, 23070295175080550765143122495581388641120853282, 1103104962041096370566309839603713661807562644688093400147242681950633054262539253406571809594356484, 4152366965484612265583708562642237195957609522079781939406229148191847240734709457139327484901080388, 3289984392160513165293126642687495384596236999590684125957673244743987507693291023082959811394528263255063174575079514405675551855119701457414342984284832746265246734230748198, 4152865925360874218503570676122835167845057575774585460936385729384583381469163238775256272341069508, 132939261752357177292885716203629495234981758438535760747586169463998873024975081692735615911420180932, 91525220155120114825979701624472639034077780258, 730753606301240417628163963195713684880772602274, 5987772565730111365273995529700827962501274018, 11707935487224699141139568922610008321950784418, 354088120756577, 72610996562273, 283717229093217, 72610996562273, 354088120756577, 157373273724723817972607464809744429208098297335481372063936456583993567266955313400613316999924013439081918335866696190709773670493180591854133537931793766720159690589889477964801571288751453485120887497889568407416668767034239094090257595272110123475934913141236581177498162523230806588196812521049478886760145437858182035477959695195448422564410757384258673713318481536365828108809400275758411185500803904228572726468109515535660554220249593266339443756601405002621904564289690132448086971367360767049697938999595100954372241918182131070458239846813109312576911499964620711953811173573682143934359052672777234054228105796476157823257915286772138968805278356268564425784100371533966794904527245034629781547709223014853925670104365925462378395853319338698465836029148898581385743075237676038707336731847856809371759551630378001, 183045214189679964939553413078286929826071755170, 354088120756577, 283717229093217, 283717229093217, 283717229093217, 5820516360145490710207525710303749566494710690, 11529528909040813174502331244076605745191230370, 23081358478022641841950828618110935663723454370, 494660803867586613243661171024528858939526350427366968667206074843296085271213054225945687155117254243700736602699116946816898032081547006376131739568605503484229217239718950, 45962010164000992945413122189747657101521492898, 28816294561899373882967312237124875024300229896982137180413468101891215730208349892, 620846106895971135335570106579700401632777166881058830365710195040162431635235689337170947725875233145048401887220125452101900337171823160495554507554713825624502582534140462631652769958573684105427642108012997844831590933309098265077781079830172253805688998846839321417630895554510981920918301664004529002434349670494207067573419616118877221149143286661076242101889869255338915350872244792551874841934229890343730331252893488165349752950986305593913902849369569216185357727534811279674691153223895463360291021, 519821040273679233410212847566651670628769685758551442365217151449430175629203051721829236238395268, 16611462958037506368780139006520946874219927284917552438266069052945953945588334129818731525170583684, 5162890291892643612578337617500187109960363822647542704783145555597826694372988758809866412927650472968387267063800074698331336034249691225028250020605496250778379438768106741003616582367221546666794103004389973578941381558095860552585204739193467190358734999679186147696993137705411465234147069588187779034068391533360763674518748026012540684600813530666234123853591125856002410, 730753606343858790559930478427749349125186951586, 5798215891260231612331277377360607958401063330, 1832903834622305650840023757141568944603126912411314816997772825934063160341618317616315902661269971477539766810945763616838092990665976274996981151415950004346828681518680651480246923450168606275980954587601930684338968300843809539887032966633658261536080593161, 11507228440155554076626082911133464137097583010, 129887936237173166705855066297646753387060132336347388671140830631263040319497098849512741018661925, 354088120756577, 72610996562273, 283717229093217, 72610996562273, 354088120756577, 91433404103568127533765058485673309672996887459, 182777604885893286962481984805114987227134585763, 354088120756577, 283717229093217, 283717229093217, 283717229093217, 265783407324242938773039641980921894098292897715475085913011613050441373470331082920075674725361396068, 265799627475796019048684252815166809114430771711472694533498106294669395020026431599152152251004565956, 265783660764111914541556245033782234717557007622065650297984523127032304682238308793560386326667409860, 265783407324241994635944827399178019671854821849518178067113197241598190492564410297371637474587260516, 5987772886063673755721651244261268359966923042, 11707935467286279204365830829052902417745615778, 77112250206688, 435553040861664, 77112250206688, 145281836911072, 145281836911072, 435553040861664, 145281836911072, 145281836911072, 294815552506336, 435553040861664, 294815552506336, 145281836911072, 265751093741069849903969464140660832427277771977904772760599977763409104655856402008696054690551764805, 6166179528216657653333264534961370923011209506, 11886342110768491097762360287804717220423056290, 77112250206688, 435553040861664, 77112250206688, 145281836911072, 145281836911072, 435553040861664, 145281836911072, 145281836911072, 294815552506336, 435553040861664, 294815552506336, 145281836911072, 5809365966112423649692339343536186164545362338, 11529528930142307607587870726424542827141700514, 86252007721440, 290554810730976, 86252007721440, 8594655712, 145281836911072, 8594655712, 145281836911072, 8594655712, 290554810730976, 8594655712, 290554810730976, 8594655712, 6522992816510309435911239325368807588646410530, 12243155397732914884555418910160441646425103266, 129887934301692149381361139272600465396043899724051561289118887051963101059701198460458907957810181, 86045849291232, 290554810730976, 86045849291232, 290554810730976, 154215503104480, 290554810730976, 154215503104480, 9079834020320, 290554810730976, 290554810730976, 290554810730976, 9079834020320, 265783407324241994635944827399191122205935057060458397334723547263649613253985463454871634341406128580, 265799627475796019048683373518995714511611891574775388894363991295977034138087934327236500337966922180, 265783407324241994635944827399191122205935057060458397334723547263649613253985463454871634341406128580] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_14 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨3, 1, false⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [5720173874343738846233422518314079970068044066, 5720195694950517651412392107210781532204603682, 22880662766433389769182066495807098835329654050, 8379134281174923944032500829035725503633698, 22880750048860504989897944851393905083875892514, 5586096613487861035925122051235772024002850, 91522618334791993460976642405779174296376088866, 108894873979360, 91433404103484888168767710339386632828341977507, 108894873979360, 217780884867552, 290554810730976, 217780884867552, 8863091168, 435552906643936, 8863091168, 435552906643936, 8863091168, 290554810730976, 8863091168, 290554810730976, 8863091168, 91522967464500454343840155828126399290561042722, 182777604885810047597484598879752331687486292387, 292547675556320, 9079834020320, 292547675556320, 8863091168, 145281836911072, 8863091168, 145281836911072, 8863091168, 9079834020320, 8863091168, 9079834020320, 8863091168, 291413804190176, 2233383518241, 291413804190176, 2233383518241, 292547675556320, 290554810730976, 292547675556320, 290554810730976, 294815418288608, 290554810730976, 294815418288608, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 544301478578656, 283717229093217, 544301478578656, 283717229093217, 508051954600416, 290554810730976, 508051954600416, 8863091168, 435552906643936, 8863091168, 435552906643936, 8863091168, 290554810730976, 8863091168, 290554810730976, 8863091168, 732180864861631475109838376392570557088463362466, 283717229093217, 283717229093217, 292547675556320, 9079834020320, 292547675556320, 8863091168, 145281836911072, 8863091168, 145281836911072, 8863091168, 9079834020320, 8863091168, 9079834020320, 8863091168] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_15 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨3, 1, true⟩) 103 ⟨1, [0, 1], 1, [1]⟩ 4 [354088120756577, 72610996562273, 283717229093217, 72610996562273, 354088120756577, 354088120756577, 283717229093217, 283717229093217, 283717229093217, 259775868603384269921807651760668755950822598679707787450424337044304540173298084030297949693509189, 354088120756577, 72610996562273, 283717229093217, 72610996562273, 354088120756577, 91433404103568127573456511290408719916311288739, 182777604885893287002173437609850397470448987043, 354088120756577, 283717229093217, 283717229093217, 283717229093217, 265783407324242938773039641980921894098292897715475085913011613040347548377339378010212389861357529444, 86252007721440, 290554810730976, 86252007721440, 290554810730976, 154352942057952, 290554810730976, 154352942057952, 9079565584864, 290554810730976, 290554810730976, 290554810730976, 9079565584864, 259775866667903252598853056560288063160100594479625128466076871648057102638115016935161636687961637, 72645081565664, 508052155927008, 72645081565664, 72645081565664, 143013892852192, 213382637029856, 143013892852192, 2276337388000, 292547675556320, 508052155927008, 292547675556320, 2276337388000, 265783407324241994635944827399178019671854821849518178067113197241598190492564410297371637474587260516, 265783407324249547732709499126372536172372412972345308900902349024309261619988079327160862065050203748, 265751093741069849903969464113826842630956054013288442319810889933563162091174482523631528996134164293, 74912958515680, 435553040861664, 74912958515680, 145281702693344, 145281702693344, 435553040861664, 145281702693344, 145281702693344, 294815552506336, 435553040861664, 294815552506336, 145281702693344, 72645081565664, 290554810730976, 72645081565664, 8594655712, 145281702693344, 8594655712, 145281702693344, 8594655712, 290554810730976, 8594655712, 290554810730976, 8594655712, 265784928087260488518372846037484733809632023625566305630421062182118465035980280563648196195098031716, 129887934301692149381361112438610669074325935107721120501354075048609145123727313869627928346350597, 81647400126944, 290554810730976, 81647400126944, 290554810730976, 154215503104480, 290554810730976, 154215503104480, 9079565584864, 290554810730976, 290554810730976, 290554810730976, 9079565584864, 265783407324241994635944827399191122205935057060458397334723547263649613253985463454871634341406128580, 81647400126944, 290554810730976, 81647400126944, 290554810730976, 154215503104480, 290554810730976, 154215503104480, 9079565584864, 290554810730976, 290554810730976, 290554810730976, 9079565584864, 265783407324241994635944827399191122205935057060458397334723547263649613253985463454871634341406128580] = some [] := by
  decide +kernel

private theorem solve_1_1_1 (N : Machine4) (h01 : N 0 1 = none)
    (hAlive : ∀ q a, ¬ (q = 0 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 1 1 1)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 1 1 1) (q1 := 1) (a1 := 1) (rem1 := 103) (cur1 := ⟨1, [0, 1], 1, [1]⟩) (step1 := 4) rfl ?_ N h01 hAlive h107 hm
  intro m hmem N h01 hAlive h107 hm' hsum1 hrun1
  simp only [moves16, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkTree_sound tv_1_1_1_0 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_1 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_2 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_3 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_4 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_5 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_6 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_7 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_8 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_9 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_10 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_11 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_12 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_13 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_14 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_1_15 N h01 hAlive h107 hm' hsum1 hrun1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_0 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨0, 0, false⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_1 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨0, 0, true⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [265783407324249547739800995321093822958741341408831261663684138305536840721900898017781742209352282884] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_2 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨0, 1, false⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_3 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨0, 1, true⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [265783407324242938780229643390794554949331658457094226281358242259678686245963385547125664264541709828, 265783407324241994643148021686466088090844560892969491012327444363431724464270670326932566545856148228, 265783407324245771191474508503779955524792951149468432088450636430399719781395440653676809676783025924, 265783407324241994643148021686466088090844560892969491012327444201930522976403391769120008721794282244, 265783407324249547739800995321093822958741341405967373164573828663915829132883341993165253063773205252, 97320910291060868753977638642423971789131274464410663147104538929730450294814757149888436605498116, 265783407324249489653242262735768927048523767275821122804895199038126155472019499126663431380996928260, 291962731839860946300966753324179025708395516148972530748136036867896847383576010383032198554401732, 356813284472111788554779983378364033761542563, 23192863480053401645734002118469788748547621283, 356813284472111788554779983378364033761542563, 46028913675634691502913224253561213463333700003, 356813284472111788554779983378364033761542563, 356813284472111788554779983378364033761542563, 132907923813795856526818315529157259071601711519234498863265885928155274505880053677181905032863494916, 97320910292831125782018334258299331428081502029450879344030944835339107624646902364457535231177476, 291962731843401460357048144555929745010701343189904758791186140793915996229504073173586166258532100, 183044517950835301082646414047243766093307707811, 23192863480063786239528452766387316237648816035, 4433748951073, 46028913675645076096707684346247735626183240611, 4433748951073, 91701014066797595735902736277150066190454100899, 183045214849122755164619662596591743744591799203, 356813284472111788632151530981605480295563683, 365733616413783134097216926464293607065665168291, 731110419543094156405801701397317378274882790307, 97320910291060868753977638642423971862347390196966050094698222068827598368784939762126404655985412, 291962731840096980571372179406295740403290689428684970126674554958826090665329469865922599437432964, 551485160572145196891044914991139690946584218995245666374022255560394019548777779004077233129399812, 2108619732964434091430201241102113839274130612848997026629832918680381957921134019834446791378927364, 32440303108078326161054420281443458463737725419177879322948607367582835815473158050679268978144004, 4184799162820819821987583125780865443620478849381482596608614523492925388988720492939683860916155140, 33251311180810216822759888812098671465011635892471378038485352666953176344508262204424536883214676740, 1978658307634536437343529631093544991039956491992290361619498138269997792207140255562844722185413602566153114037795079521536209841285780536152309406362991826194890159530433574, 1978658307634536437343529631093544991039956491992290361619498138269997792207140255562844722185413602566153114037795079521536209841285780536152309406362991826194890159530433574, 61833072117178394709638826688070690519177454331279056736501499326531702487699574656420040489269723769770235884207135068391423452843279360361110676189064163300741302463655079, 23192863480074170833322893969247618676849682339, 4433748951073, 46028913675655460690502125549108038065384106915, 4433748951073, 91701014066797595735980107824753307636988122019, 183045214849122755164697034144194985191125820323, 356813284472111788709523078584846926829584803, 365733616413783134097294298011896848512199189411, 731110419543094156405879072944920619721416811427] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_4 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨1, 0, false⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [1461518373821715546445732431341385304067678443810, 1461685629368179614848201987103942422696060557730, 1461529524236850107622420507138055140195829849890, 1461551825067119229975800285508853656339656776994, 1462934476543804815885271591097545550248094505250, 1461596426727657474682552588695533000852262394146, 1461551825067119229975800285508853656339656776994, 1461685630048733964096071702178727065427570104610, 1461507223406591369862779559087266748507245025698, 1461864035329767859833063473540316908947812432290, 36361231403488, 36361231403488, 72645148674528, 290348652300768, 72645148674528, 72645148674528, 145212983216608, 145212983216608, 145212983216608, 77314132448, 290348652300768, 77314132448, 290348652300768, 77314132448, 45157559306720, 45157559306720, 81441443023328, 290348652300768, 81441443023328, 81441443023328, 154009210456544, 435484187167200, 154009210456544, 290348652300768, 290348652300768, 290348652300768, 290348652300768, 8873675590112, 51754863954400, 51754863954400, 85839690861024, 290348652300768, 85839690861024, 508052155927008, 154009344674272, 435484321384928, 154009344674272, 77314132448, 290348652300768, 77314132448, 290348652300768, 77314132448, 1462934476543804815885194219845090213980913309986, 72645081565664, 290348652300768, 72645081565664, 72645081565664, 147411939363296, 217780683540960, 147411939363296, 77314132448, 290348652300768, 77314132448, 290348652300768, 77314132448] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_5 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨1, 0, true⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [97320910291060868753977638642423971813536648557272743832728880759172158669559403665954954417484548, 291962731840096980571372179406295740354479947788991663864705213649170650966103933769751149198932100, 551485160572145196891044914991139690897773477355552360112052914250738579849552242907905782890898948, 364290574387680, 23192863480219718039548394899777546676038795683, 364290574387680, 435827583224288, 290554810730976, 435827583224288, 290554810730976, 290554676513248, 290554810730976, 290554676513248, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 2108619732964434091430201241102113839225319871209303720367863577370726518221908483738275341140426500, 46028913675801007896727617034868971390824874403, 508395350657504, 290554810730976, 508395350657504, 290554810730976, 290554676513248, 290554810730976, 290554676513248, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 356813284638265923400620811304395521776419235, 91701014066964074389224826205123660692961886627, 146587272088032, 146587272088032, 154352606513632, 154352942057952, 154352606513632, 154352942057952, 145419141646816, 145419141646816, 145419141646816, 145419141646816, 154352807840224, 154352942057952, 154352807840224, 154352942057952, 183045214849289233817941714745489359552106201507, 356813284638265923400620811304395521776419235, 365733616413949288231985320186176208241487799715, 291722806954464, 989336701799703738652773076954372151821016097563143278150728409456497491862284355043023545732374399923079571706111001087633974326246378715597675744327146695472877114670081062, 291722806954464, 295090094868960, 290554810730976, 295090094868960, 290554810730976, 290554676513248, 290554810730976, 290554676513248, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 731110419543260310540569944002896064670723515811] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_6 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨1, 1, false⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [1461518373821715547713383031569614705564381649186, 1461518373864250843578500339507148217511780063522, 1461551825067119231243450885737083057836359982370, 1461507228851098857271709162851414784074052573474, 1461551825237260414703920117487217105625953639714, 1461507223746863353457632210347393350386242853154, 1461685630048733965363722302406956466924273309986, 1461685630048733965363722303587548087641684613410, 1461685630729298699205599229407492658082647939362, 1461507223406580986536693748027716875524466841890, 45157559306720, 45157559306720, 81441443023328, 290348652300768, 81441443023328, 81441443023328, 154009210456544, 435484187167200, 154009210456544, 290348652300768, 290348652300768, 290348652300768, 290348652300768, 8873675590112, 51754863954400, 265783407324362786103035994828495691884872614501654388043670622524202775403273071668920935825652527876, 51754863954400, 85839690861024, 290348652300768, 85839690861024, 508052155927008, 154009344674272, 435484321384928, 154009344674272, 77314132448, 290348652300768, 77314132448, 290348652300768, 77314132448, 1462934471099629638010570074535264245731673807266, 265783407324243824830751660083108867715546369497887233607805609666867113276625625575891192873276879620, 72645081565664, 290348652300768, 72645081565664, 72645081565664, 147411939363296, 217780683540960, 147411939363296, 77314132448, 290348652300768, 77314132448, 290348652300768, 77314132448] = some [] := by
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
private theorem tv_1_1_2_11 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨2, 1, true⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [551485160571319076944625923690631854454091585352261610859453038782577437458689811970037332337439492, 23059057819390085078417380806331635347131243938, 551485160571437094079828636731693410625790546552516955753997232582458770967894383312563229445012420, 72645148674528, 86252007721440, 72645148674528, 72645148674528, 77180701247968, 86252007721440, 77180701247968, 72645148674528, 81716320930272, 86252007721440, 81716320930272, 72645081565664, 1070530018034485836516478538663349795338045272505581980814937933363605975416622557091005089894839044, 2108619732961144133284208422270614073397462381669968280576725024452543489556024920152115076754012292, 435827583224288, 290554810730976, 435827583224288, 290554810730976, 290554676513248, 290554810730976, 290554676513248, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 2108619732960775560238917136816205427322633290431402564513134755102959830541981384632331266886415108, 2108619732961129611644525275939390095837730174027906860358805566833436632136014816204018296218417284, 72645148674528, 86252007721440, 72645148674528, 72645148674528, 77180701247968, 86252007721440, 77180701247968, 72645148674528, 81716320930272, 86252007721440, 81716320930272, 72645081565664, 72645148674528, 8863091168, 72645148674528, 8594655712, 8728873440, 8594655712, 8728873440, 8594655712, 8863091168, 8594655712, 8863091168, 8594655712, 145282105346528, 9131526624, 145282105346528, 9131526624, 290555079166432, 9131526624, 290555079166432, 9131526624] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_12 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨3, 0, false⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [36567893150176, 1461680402636008333232355628723607214085505063330, 36567893150176, 1461512820375947109457560908736957551738193222050, 1461523992526617857709194547182500052199713840034, 1461546336827959354212461824073585053122755075490, 1461501648225276361205927270881710861635378256290, 1461591025430642347218996377855755054968837544354, 1461501648225276361205927270586562956456025430434, 1461680402636008333232065485420095058661002484130, 1461859157046740305258203700548775066045332371874, 1461501648225276361205927271472006671994083908002, 1462931683511132137415032991320855110351311640994, 72851776866784, 1462931683511132137415187734416061593244379683234, 72851776866784, 46028913675468699944567557816900207953429135779, 363122376837600, 290554810730976, 363122376837600, 290554810730976, 290554676513248, 290554810730976, 290554676513248, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 145419544300000, 284009433568, 145419544300000, 284009433568, 290555079166432, 284009433568, 290555079166432, 284009433568] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_13 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨3, 0, true⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [36361231403488, 36361231403488, 1599184301784178489905497686659692740611092225357259589534108107344822880471396142872601467039538772794739450765781403731701877202527197383803753642008254128917278902011253034711133186647082280562792643365494078746956575599369116126247342306190531966855197104927206072497469362541499300321567586783088769760406656192378132116220997463602147739952293172206561818963954127530, 5709012592105619535551042398503079475607017762, 30191929757018575137346184090149466659800196195237821680598969415766630400392620544221113315276186286657090176200872163226753283899850337683462030970467800703963042028582, 5709012592105619535551041845100757264320469282, 41034256484832, 41034290039264, 41034256484832, 36361231403488, 199898227615972830991092359522677080200538766240434561485764476736064902691036221211318408347190463526601475735047119255734714524274356153188558907429416223474221929641151646047890056101203486395715012314402612125789491930280767511723901128614054422305262560786956390642730232676005543590987715993269794123827262873716816601744633124732082638910328109517988591187109264170, 81100758978735554311667992595209663078039282795177499193254096473611655858194742237321348905311940, 36361231403488, 36361231403488, 60384320181721053086282576270161220609137169117337711352326751487997483085260947942255929478204470095020414188331802015232065277442522295855242516932511088346842362731558, 11418025183546622458680225520454822713371957666, 30192620783147864168643720590656225942215136936443356969579949750858618824950114873433634370292284656723176018988464060733435832424691332839733774310184332763402086145062, 11418025183546622458680224967052500502085409186, 41034256484832, 41034290039264, 41034256484832, 36361231403488, 30192620783147864168643720590656225942215136936443356969579949750858618824950122957920165447783939534617001898579071680408687466845758637431291288406395593410045533510694, 275742580527771662527468864723328294600448970311095162525558050719493723548580279896955083067914372, 519298320541849883997552647440459305506057156257070955415332360905933266644714406482486105624214884, 66445977576463772151956562088257272859641656196127114688229267390818282135948552110200388404635103076, 1932386697890668727143911152070343230158396392478276586037214450126149040248304342046690509637363285483180297712672609307956367827766037812949081539777998708420926738492199, 66437867500686759715985251297417752224281205033466400288287690336860831120270725959454904752788861060, 435827583224288, 290554810730976, 435827583224288, 290554810730976, 290554676513248, 290554810730976, 290554676513248, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 1038216434860320291574793551587181601815865763216270824933832198995668716120758525851152255242858628, 1039103474413537195050995215782945670626053139232990752382295144590476181981693980821417620041677317, 508464070134240, 8863091168, 508464070134240, 8594655712, 8728873440, 8594655712, 8728873440, 8594655712, 8863091168, 8594655712, 8863091168, 8594655712, 145419544300000, 9131526624, 145419544300000, 9131526624, 290555079166432, 9131526624, 290555079166432, 9131526624] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_14 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨3, 1, false⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [36567893150176, 36567893150176, 72851776866784, 363122343283168, 23192863479970486837743862943507961317360140707, 363122343283168, 435690144270816, 290554810730976, 435690144270816, 290554810730976, 290554676513248, 290554810730976, 290554676513248, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 72851776866784, 46028913675551776694923085078599386032146219427, 363122376837600, 290554810730976, 363122376837600, 290554810730976, 290554676513248, 290554810730976, 290554676513248, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 145419544300000, 284009433568, 145419544300000, 284009433568, 290555079166432, 284009433568, 290555079166432, 284009433568] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_15 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨3, 1, true⟩) 103 ⟨2, [0, 1], 1, [1]⟩ 4 [23014456328660720636139881086248591349158812066, 72645148674528, 86252007721440, 72645148674528, 72576362088928, 77111981771232, 86252007721440, 77111981771232, 72645148674528, 72851508431328, 86252007721440, 72851508431328, 72576362088928, 435827583224288, 290554810730976, 435827583224288, 290554810730976, 290554676513248, 290554810730976, 290554676513248, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 72645148674528, 86252007721440, 72645148674528, 72576362088928, 77111981771232, 86252007721440, 77111981771232, 72645148674528, 72851508431328, 86252007721440, 72851508431328, 72576362088928, 1039103474413537195051105100967885974541056461926965875000624296123883396116382763622209424303274501, 72645148674528, 8863091168, 72645148674528, 8594655712, 8728873440, 8594655712, 8728873440, 8594655712, 8863091168, 8594655712, 8863091168, 8594655712, 145144666393056, 9131526624, 145144666393056, 9131526624, 290555079166432, 9131526624, 290555079166432, 9131526624] = some [] := by
  decide +kernel

private theorem solve_1_1_2 (N : Machine4) (h01 : N 0 1 = none)
    (hAlive : ∀ q a, ¬ (q = 0 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 1 1 2)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 1 1 2) (q1 := 2) (a1 := 1) (rem1 := 103) (cur1 := ⟨2, [0, 1], 1, [1]⟩) (step1 := 4) rfl ?_ N h01 hAlive h107 hm
  intro m hmem N h01 hAlive h107 hm' hsum1 hrun1
  simp only [moves16, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkTree_sound tv_1_1_2_0 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_1 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_2 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_3 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_4 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_5 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_6 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_7 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_8 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_9 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_10 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_11 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_12 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_13 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_14 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_2_15 N h01 hAlive h107 hm' hsum1 hrun1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_0 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨0, 0, false⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_1 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨0, 0, true⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [265783407324242054573723612732663423703411841784513048393385662613519188647118002767279481692813996804, 265783407324249489653354812646507598390454123575691460629245838900155415920467210373645046649219920644, 265783407324242172590858816089720246769026395410413506880782257102607062648417420293339687728240344004, 265783407324242054573724491814182250537916519257916837240084616128672615955418350575578328542495322884, 265783407324242408625130099953305425609849180844463612965971165400012745147347357463897221719025744004, 265783407324242880693684979544311992956836693501204536181290736732339134144814139227790238587650582020, 265783407324241936556589289101141192180605632062401245331455766532955297034590629911140179423713768196, 265783407324245713104972050873824395285529877817614408730795647812470793665838576623712268335645654788, 265783407324241936556589289101141192180605632062401245331455766371454095546723351353327621599651902212, 265783407324249489653354812646507598390454123572827572130135529258534404331449654349028557503640843012, 265783407324242880693670033226654283190629940490683565751816156133732854460646758601339214646307202564, 265783407324362786103036867255184950066954120272549370052434344156835002880130216671092665658422539012, 265783407324243824830751660083108867715546369497887233650988912046435846471042098809820862929715802884, 265783407324241936556589289101141192180605632065310592378171001562942107319693566997382467715795727108, 265783407324249489653353947089319830430326441137476149265693482720537183597123158045472769836262306564, 265783407324362786103036427607089575864984503795995561105868068002108281700018951996465477435967877892] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_2 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨0, 1, false⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_3 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨0, 1, true⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [265783407324242879886927219369515813847167125572560353124456131021372286265429141445444480239235507716, 265783407324241935634580420329945558912384384100960169067698056548913217696675172171459512767137133316, 265783407324245712643967616488226578651515349987360905294730354920729640162044958713371234911715262212, 265783407324249489653354812646507598390454123572827572130135529258534404331449654349028557503640843012, 265783407324241935634580420329945558912189141128582701749219707993192564952601445949902345613586150148, 265783407324242879886926341790700437998509474795367230969899157858136253769344752278174008108927690244, 265783407324241935634579547903256300730156446100782086602590059799595103615535637774841342580846965508, 265783407324241935634579541033754810508249908175475083856087155683739122592378916600647969168676827908, 265783407324249489653353947089319830430326441134612260766583173078916172008105602020856280690683228932, 137871290263649813197050462417235398107777937093256640248377027889049075637912129675611059978916869, 265783407324241935634579650945778654058766717666160719507538518352448835038366178006179121302507565828, 137871292318092102806044056480433842271078564951012210551782863909802622163646540749774725403671205, 137871292318092102806044056483709475815542739233158881468858428119211459637258063607166167526963877, 265783407324242054573723612732663423703411841781649159894275352971898177058100446742662992547234919172, 265783407324249489653354812646507598390454123572827572130135529258534404331449654349028557503640843012, 265783407324242172590858816089720246769026395407549618381671947460986051059399864268723198582661266372, 265783407324249489653354812646507598390454123572827572130135529258534404331449654349028557503640843012, 265783407324242880693796651876235288450325615359926677479943397220343720828406349444835378507989394948, 265783407324362786103036207783041888763999695554854768133474620283123909520945763634535394179161469700, 265783407324243824830892347471532206892986008241808900959920325436183588167332483749773988236649247492, 265783407324241936556588409804950443776666399109339085985928139611867653370453481623511602125307327236, 265783407324249489653353947089319830430326441134612260766583173078916172008105602020856280690683228932, 265783407324362786103036427607089575864984503793131672606757758360487270111001395971848988290388800260, 265783407324243824139273139327567241947249994262211947351735046540219076297133599976209315262755975940, 265783407324245712643966738050723516525119191302539195426432317879751574364071621527429245674086399748, 265783407324242880693684101965496617108373904362498232833510019432421427195261369108299543986223457796, 62270380013180045476745592769853717008101113541469863263575994634180275890045241063793032874360594188279876204136884908264858683036640799899331492667370434762870324083495, 265783407324243824830892347471532206892986008241808900959920326074618025299057819298626755884893811460, 137871290263649813196998941156058733812175502835028262702691593462803847974708013681528604702323717, 137871290263649813197050462417235398107777937263752552177236703281760613819021166907690697496094213, 137871290263649813197215330453000723892144187622460850438595248528576568304372877434807379989491205, 137871292318092102806044056480433842271078565030564668691655774711215358274138508698905602925864997, 275742580527299595780855047218533751646566728811272854629376996952262341072512651912216712535323205, 265783407324242057339750219046250323508661314583241166283798304736096119206340731991527321689118683908, 265783407324242411391155827829389263288897547266688781823625844060135825302847932794458180157377575044, 265783407324242883459935808100560859597526799158947128515899727409636665604892987465355399211883177476, 265783407324245715871447984403676722276551974245420608869799315761554945619035681721484534417726045956, 265783407324241939322615016118537343581915871910931092375451091376065595518693766872375931267191091972, 265783407324249492419380553402906730235575913936204267156106124843114114156345887269720609832566993668, 249081520041846342413335485290846695165735325221663421746006181494228830069412658415674411923163514418090789320495308267586814375542688149604319575243482211279723259967271, 265783407324241935634579547903256300730156446100782086602590060443076453293756825778625752661093462788, 265783407324249489653353947089319830430326441134612260766583173714827152866583011342243227122926826244, 137871290263649813197050462417235398107777937172829907828356393055985813871185037846495434712731141, 265783407324241935634579650945778654058766717666160719507538518917703040245901652958523073686724096772, 137871292318092102806044056480433842271078565030564670045764546694481502741165501199981652112910373, 137871292318092102806044056483709475815542739312711340964163128746478948960722628908566646846466085] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_4 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨1, 0, false⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [22847211521029706239041676207312802527872850210, 23014467067493774641511231969869921156254964130, 22858361936164267415729752003982638656024256290, 73126185011680, 24263303524224417669019236867172914607590250786, 73126185011680, 22847211457320142972401852739620997730501958050, 79201414154337, 22858361830002485350621827902482846245125659554, 79201414154337, 72645148674528, 86252007721440, 72645148674528, 70377338833376, 74912958515680, 70377338833376, 74912958515680, 72645148674528, 81647668562400, 86252007721440, 81647668562400, 70377338833376, 23014467748048123889380947044654563887764511010, 22836050216869788186348115321914320152786147746, 23192873029082019626372718406244407408006838690, 22880651877408032893100418508593664665391766946, 81922479360480, 22836050216869788186057973125206809150856665506, 81922479360480, 70927094647264] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_5 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨1, 0, true⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [45775252290554934916679733180278901733871098146, 265791514430141358644759077213584989381887065798658143568818874538143536259411256810027831825222808324, 22894687759397811438581394170075194776133606690, 4184799162820833659211259070251659012923257179391391509784503435001346132817003178714626110588662532, 290829688637920, 4184799162820833659211259070251659012923257179408438465136350513678014928551324308538188758549476100, 265783403379714642611933737007956389267849369049824910847979256070344956330981425808306178551852512004, 79201414154337, 265783403395185272831386984778230097139485231017813635343008640224997478600702046295190729772103040772, 79201414154337, 437683009096160, 290554810730976, 437683009096160, 290279664388576, 290417237559776, 290554810730976, 290417237559776, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290829554420192, 527154956564126909571455927133096701090765029579903256765285879597368666388635758943301977252793989, 290829554420192, 527154956564126909570577060286191460816595855529092443922486038583092212042905052057432167284238149, 290348652300768, 290554810730976, 290348652300768, 290554810730976, 290417505995232, 290554810730976, 290417505995232, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290829688637920, 290829688637920, 290829688637920, 290829688637920] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_6 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨1, 1, false⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [22847298633315637999288322831212305060534982946, 22847298675850933864405630768745817007933397282, 73126185011680, 22836142943804389548052855016712249469507246370, 73126185011680, 79201414154337, 79201414154337, 72645148674528, 86252007721440, 72645148674528, 70377338833376, 74912958515680, 70377338833376, 74912958515680, 72645148674528, 81647668562400, 86252007721440, 81647668562400, 70377338833376, 23014554860334055649627593668554066420426643746, 72610788936160, 2108619733081507096754486865106970176441876178368690162569871676707983008383806342647245931458802436, 72610788936160, 77043329403360, 70652216740320, 77043329403360, 70377338833376, 81510229608928, 70377338833376, 81510229608928, 86252007721440, 70652216740320, 86252007721440, 70652216740320, 70377338833376, 23014555540898789491504520669090257578801273122, 2108619732968210647016157301060282829011784054447527308772262278836468561068257858455367553380463364, 72645148674528, 86252007721440, 72645148674528, 72645148674528, 77112048880096, 86252007721440, 77112048880096, 72645148674528, 72851307104736, 86252007721440, 72851307104736, 72645148674528, 81922479360480, 23014560474993109845112242585122520120719087906, 81922479360480, 70927094647264] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_7 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨1, 1, true⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [265783407324249489653354812646507598390454123575691460629245838900155415920467210373645046649219920644, 79201344946209, 79201414154337, 79201344946209, 79201414154337, 79201344946209, 79210280921441, 79210213812577, 79201414154337, 79210213812577, 265783407324242053766965854060570695579589634219268653676942389900651262962466894566793692855107007236, 47099353528386572594661943954566789212355428771, 265783407324242171784101056773611753936900473748044363072576843202961762609537576346456964402518637508, 72645148674528, 508052155927008, 72645148674528, 72645148674528, 77043262294496, 217780817758688, 77043262294496, 72645148674528, 81441443023328, 508052155927008, 81441443023328, 70446058310112, 47099353528718880861258773151022142474128720291, 508395350657504, 290554810730976, 508395350657504, 290554810730976, 290554676513248, 290554810730976, 290554676513248, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 265783407324242053882216967809096267404571408363011011314170873770829617916296339843220890905443775236, 265783407324242407933622575948219442476503926949333877762236271908091949658574804899754814885687949444, 72645148674528, 508052155927008, 72645148674528, 72645148674528, 77043262294496, 217780817758688, 77043262294496, 72645148674528, 81441443023328, 508052155927008, 81441443023328, 70446058310112, 265783407324241935634580420329945558912189141131492048795934943184680576725571661593957191729729975044, 265783407324249489653353947089319830430326441137476149265693482720537183597123158045472769836262306564, 1978658307749707751789734961775451259153398309878422119076333187397063250485152884542641564562978936994537768037888631273769715928254239926824240561370656828292219194246689958, 508464070134240, 8863091168, 508464070134240, 8594655712, 8728873440, 8594655712, 8728873440, 8594655712, 8863091168, 8594655712, 8863091168, 8594655712, 217849403017696, 145281971128800, 217849403017696, 145281702693344, 145281702693344, 145281971128800, 145281702693344, 145281702693344, 145281836911072, 145281836911072, 145281836911072, 145281702693344, 72645148674528, 8863091168, 72645148674528, 8594655712, 8728873440, 8594655712, 8728873440, 8594655712, 8863091168, 8594655712, 8863091168, 8594655712, 398675109006424366594139622420543344182725099383239817072874441628912227873539483485450334902444620228, 265783407324241935627377226042657490493199402085131399902283520160409073529463277148678386174864341444, 47099353528469651879699701653082080147029361059, 363122376837600, 290554810730976, 363122376837600, 290554810730976, 290554676513248, 290554810730976, 290554676513248, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 265783407324241935627377226042657490493199402085131399902283520160409073529463277148678386174864341444] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_8 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨2, 0, false⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [91355362086588923815339758598539971372717742370, 91522607445766560525858981886946526967947631010, 91366512501723485308940484447655471856617561890, 91355362065248583726453339785297966458528111010, 91366512437847849354937966631922941661058997154, 8830453284897, 79201414154337, 8830453284897, 79201414154337, 8830453284897, 91701023615825818209476772030672197736985573794, 8830721720353, 8830721720353, 8830453284897, 8830721720353, 91388813332241838545351607872055936648219761954, 92771454621402181651017203914631796028263668130, 91433414992780084519754511268517938583819032866, 91344200803613576628247368301098519225550543266, 145282105346528, 140746619881952, 145282105346528, 145282105346528, 154215637322208, 154353076275680, 154215637322208, 140746619881952] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_9 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨2, 0, true⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [72610788936160, 45672100391256041453952922108194378589408368930, 72610788936160, 26201085477334691778134359223238538211370055604716084236484387964837805092985830088891709897677354286656186417371356937831608484375565197472124216940836012404803598546673806855582235442993746634117787982864848748456284651676052068367080080773810859486154164123893321703590633494212297342324853030326654084175714443746934361605011435518402429579384894961450103362127874722798379, 72610788936160, 26201085477334691778134359223238538211370055604716084236484387964837805092985830088891709897677354286656186417371356937831608484375565197472124216940836012404803598546673806855582224393074456342256235685221518582584114112564230554842622744473969495969969947218175486141852655279631079424876598074622006215244179835869335215331488756291478196247944261080068361716439656573868843, 362882059995616, 1038089714926304245333984535139313735848877779473341797750412839366036851979729374895267652674204420, 362882059995616, 70411698571744, 72610788936160, 45671926166777639593825905814766272969624820130, 72610788936160, 26201085477334691778134359223238538211370055604716084236484387964837805092985830088891709897677354286656186417371356937831608484375565197472124216940836012404803598546673806855582235442993746634117787982864848748456284651676052068367080080773810859486154164123893321703590633494212297342324853030326654084175714443746934361605011435518402429579384894961450103362127874722798379, 72610788936160, 26201085477334691778134359223238538211370055604716084236484387964837805092985830088891709897677354286656186417371356937831608484375565197472124216940836012404803598546673806855582224393074456342256235685221518582584114112564230554842622744473969495969969947218175486141852655279631079424876598074622006215244179835869335215331488756291478196247944261080068361716439656573868843, 362882059995616, 117304953946060064340235644496470037642322098015690549335945211642255074072225028214932924536619380158263635167765052916825034364080378968211638874444922731472875531907078074075651360578784176929784038131663286609886083359205233628470200899742687884771605106782760, 362882059995616, 70411698571744, 1876893526653240986460184327312966599273601958309186372605719373044156268503740387246088755950315549901209206271913865280355716273208304245992092427598623538534836068155264287598271592628996219341398561725881435275781139284048973809660327108353296059858945080593161, 92771453919715468706551028429689230958959269795, 92771453919715468706555873596183428223116512163, 16617545514718730601070087799941674117749361101887098473659742249596642465847928325887932055128927749, 16617545514718730601070087799941674117749361101796181378449891180144117376917723816601072706011033093, 16617545514718730601070087799941674117749361102432601036790558007878354969351675579570540913142189573, 92771453919715468706623592589730138648253567907, 1978658307749707751789734961775451259153409666733489898989966926265725482090633381134076084581760620789186553904570452131076082146007593834887352278062565132399348792867943590, 92771453919715468706700964137333380094787589027, 469219802018897949542320277787188588693372836892195866055761683114360860129805044782755600226592149761603537964833002951944519972074191257783919755414230867765011881188634053049410638492404432069920014338325932470407399589396062466071276844347219280691460106582760, 91567296197655392256293704889350819827407691170, 469219802237395446478927342640237194763838682052206818654755941012862886338447730438482351889017803417476578355984472111956518184041205642463267848559635679276032026616167254552528148782229314963217610849938389403258257425382919810138454845408998959644948231782760, 213382637029856, 508052155927008, 213382637029856, 213382637029856, 217780750649824, 217780817758688, 217780750649824, 217780817758688, 508051954600416, 508052155927008, 508051954600416, 213382637029856, 92771453919881947358707780257494331021100324259, 1876879208075271733498759788092203812639504769497528149263869684502823616951994276955332644367107242349024359440393880627426377469312358756198419820851999116913466202693210406754891122493985757847142949224305386983375653189586502961182799993462887192494372356582760, 1876879208949581785934786721940391268395726591038037872449558331885070058252123609924874920562249865083348815032265021214592107132361735205638712171470288262529631267778833527763084968916691564774008561731363761465421939419543072156576780920788271696478484606782760, 213382637029856, 508052155927008, 213382637029856, 213382637029856, 217780750649824, 217780817758688, 217780750649824, 217780817758688, 508051954600416, 508052155927008, 508051954600416, 213382637029856, 92771453920214904662411888528471387637753579939, 290417640212960, 9131526624, 290417640212960, 9131526624, 284009433568, 9131526624, 284009433568, 9131526624] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_10 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨2, 1, false⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [91355710535732650856326345094137981503366273314, 91355710578267947038356303084117157806513101090, 91389161781385565586338194367653946778868292898, 91433769609874059566207907049365842936305064226, 16641875742049768145339711637466616029266124783895409550612947023435344626204275227724954354824983300, 91389168204215283051213222515049932324592459042, 154352606513632, 154352942057952, 154352606513632, 154352942057952, 154215234669024, 154352942057952, 154215234669024, 154215234669024, 154352807840224, 154352942057952, 154352807840224, 154352942057952, 91389161951526750314458026327570651991455604002, 16641875741928918598441933840464897141590733784207801248283017844035591639734875787835536075512820484, 143013892852192, 145281971128800, 143013892852192, 140746083011040, 140746217228768, 140746083011040, 140746217228768, 140746217228768, 145281836911072, 145281836911072, 145281836911072, 140746083011040, 145282105346528, 140746619881952, 145282105346528, 145282105346528, 154215637322208, 154353076275680, 154215637322208, 140746619881952] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_3_11 : checkTree 3 ((baseTable 1 1 3).set 3 1 ⟨2, 1, true⟩) 103 ⟨3, [0, 1], 1, [1]⟩ 4 [91388803123781215510914772519270130402697715106, 72645148674528, 290348652300768, 72645148674528, 72645148674528, 147412006472160, 217780817758688, 147412006472160, 77314132448, 290348652300768, 77314132448, 290348652300768, 77314132448, 184115654702207106797019883517854423331975070115, 435827583224288, 283740998112, 435827583224288, 283740998112, 283606780384, 283472562656, 283606780384, 283472562656, 283740998112, 283472562656, 283740998112, 283472562656, 72645148674528, 290348652300768, 72645148674528, 72645148674528, 147412006472160, 217780817758688, 147412006472160, 77314132448, 290348652300768, 77314132448, 290348652300768, 77314132448, 184115654702540064100724020123066405963518050723, 72645148674528, 8863091168, 72645148674528, 8594655712, 8728873440, 8594655712, 8728873440, 8594655712, 8863091168, 8594655712, 8863091168, 8594655712, 145282105346528, 9131526624, 145282105346528, 9131526624, 284009433568, 9131526624, 284009433568, 9131526624] = some [] := by
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

private theorem solve_1_1_3 (N : Machine4) (h01 : N 0 1 = none)
    (hAlive : ∀ q a, ¬ (q = 0 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
    (h107 : ∃ r T, N.multiStep (Machine.init []) 107 = some ⟨some r, T⟩)
    (hm : Matches N (baseTable 1 1 3)) : CertProp N := by
  refine branch_one_sound (tb := baseTable 1 1 3) (q1 := 3) (a1 := 1) (rem1 := 103) (cur1 := ⟨3, [0, 1], 1, [1]⟩) (step1 := 4) rfl ?_ N h01 hAlive h107 hm
  intro m hmem N h01 hAlive h107 hm' hsum1 hrun1
  simp only [moves16, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkTree_sound tv_1_1_3_0 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_1 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_2 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_3 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_4 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_5 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_6 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_7 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_8 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_9 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_10 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_11 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_12 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_13 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_14 N h01 hAlive h107 hm' hsum1 hrun1
  · exact checkTree_sound tv_1_1_3_15 N h01 hAlive h107 hm' hsum1 hrun1

end OMA.BB4Hole00

open Turing Turing.BusyBeaver OMA.BB4Hole00 in
theorem OMA.solution :
    OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1_H1_R1_H1_R1.H1 := by
  intro b c q u v N h107
  have h01 : N 0 1 = none := rfl
  have hAlive : ∀ r s, ¬ (r = 0 ∧ s = 1) →
      ∃ r' w d, N r s = some (some r', Stmt.write w d) := by
    intro r s hne
    fin_cases s
    · cases hs : (v r).2 with
      | write w d => exact ⟨(v r).1, w, d, by simp [N, hs]⟩
    · have hr0 : r ≠ 0 := fun h => hne ⟨h, rfl⟩
      cases hs : (u r).2 with
      | write w d => exact ⟨(u r).1, w, d, by simp [N, hr0, hs]⟩
  have hm : Matches N (baseTable b c q) := by
    intro r s m hget
    fin_cases r <;> fin_cases s <;> simp [baseTable, Table.get] at hget <;> subst hget <;> rfl
  fin_cases b <;> fin_cases c <;> fin_cases q
  · exact checkTree_sound tv_0_0_0 N h01 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact checkTree_sound tv_0_0_1 N h01 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact checkTree_sound tv_0_0_2 N h01 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact checkTree_sound tv_0_0_3 N h01 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact solve_0_1_0 N h01 hAlive h107 hm
  · exact solve_0_1_1 N h01 hAlive h107 hm
  · exact solve_0_1_2 N h01 hAlive h107 hm
  · exact solve_0_1_3 N h01 hAlive h107 hm
  · exact checkTree_sound tv_1_0_0 N h01 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact solve_1_0_1 N h01 hAlive h107 hm
  · exact checkTree_sound tv_1_0_2 N h01 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact solve_1_0_3 N h01 hAlive h107 hm
  · exact checkTree_sound tv_1_1_0 N h01 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact solve_1_1_1 N h01 hAlive h107 hm
  · exact solve_1_1_2 N h01 hAlive h107 hm
  · exact solve_1_1_3 N h01 hAlive h107 hm
