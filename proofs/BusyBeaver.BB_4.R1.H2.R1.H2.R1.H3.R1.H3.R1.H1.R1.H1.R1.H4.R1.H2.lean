import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1_H1_R1_H4_R1

/-!
FAR nonhalting certificates for write-1 transition at state 1 blank, hole at (3, 1).
Every machine in this branch either halts at the missing (1, 1) entry within
107 steps or hits a leaf certified by a finite automaton invariant.
-/

namespace OMA.BB4HoleS3A1

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
   some ⟨2, 1, false⟩, none,
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
private theorem tv_0_0_0 : checkTree 4 (baseTable 0 0 0) 107 startPos 0 [1464361709285022052001178423672349866257365887394] = some [] := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem tv_0_0_1 : checkTree 4 (baseTable 0 0 1) 107 startPos 0 [1464361710646151519684932277525848295984438733218] = some [] := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem tv_0_0_2 : checkTree 4 (baseTable 0 0 2) 107 startPos 0 [1464361707923892584317424569818851436530293041570] = some [] := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem tv_0_0_3 : checkTree 4 (baseTable 0 0 3) 107 startPos 0 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_0 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨0, 0, false⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [1464361707966427880182233600491791597320730077602] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_1 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨0, 0, true⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [571205086120416, 1464361710646151519684700162735461241340407343522, 571205086120416, 1461507212538480664554998511837108929444260637090, 567906484160992, 1464361707923892584317115083776009045621227940258, 567906484160992, 265751101661063955635873471718125492671285460667866820957381504406478374854059188023404302308275469060, 1461507212517212945634006245089801532664395622818, 1978643211900008465631029899522488823202203152502649878658387275820126195456968396231013972404038296051017350284607785422209801006718170179453102479376708596979071473802961958, 1461507212517212935492801443263966320690769979810, 567425447823840, 1464361707907941787520467282346152089056109947298, 567425447823840, 567356728281568, 1461507212517212935492801443263966320690769979810, 1464361707907941787520467282346152089056109947298, 1464361710646151519684700162735460396914403469730, 1465621704770378049422337841058280378162167707938, 1464361707902624865396122817028701648837067958690, 1465644005515576580362392026833610306529105312034, 1461507212517212935492801443263966320690769979810, 1465655156058566260017471834263144955274889035042, 1461507212522529867758350710407251972879142644130, 1465744359209501567238162644799430430975490816290, 1461507212517212935492801443263966320690769979810, 1464361707903954088321305331988687849910535481762, 1461507212517212935492801443263966320690769979810, 1464361707905283321387692648774509262957628647842, 1461507212522529867758350710407251972879142644130, 1461507212527846800023899977550537625067515308450, 1464361710646151519684700162735460678390453922210, 265750982861125933825306182390928212796108543268270685881818606055480123477886040566229079935722467653, 265750998701117921836540449707145313358748052043800171904057111233247819952056034538043195757114178693, 265750998701117921836540394751134210491881864684914686599763477972100621314340564245055549726993169541, 1464361707923892584317115083776009045621227940258] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_2 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨0, 1, false⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [1464361708008963176047352117355144723897303198626] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_3 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨0, 1, true⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [564607848581600, 1978643212360697238219068824983734034857852596935827151626556170206389317735969852699412692579117444647265104672358661120507433900024519919223343038582160081670004747816024871, 564607848581600, 563508303366624, 563508303432160, 563508303432160, 564092452506080, 1461507212517212945634006244942227580074719209890, 564092452506080, 562958547552736, 563027267095008, 1461507212517212955775211046768062792048344852898, 563027267095008, 562958547552736, 567494167366112, 562958547552736, 567494167366112, 564092452604384, 576565406730720, 564092452604384, 562958547683808, 565226357524960, 572029787048416, 565226357524960, 562958547683808, 567494167366112, 562958547683808, 567494167366112, 572029787048416, 1461507212538480583425360097082853562541629532578, 572029787048416, 1461507212538480583425360097082853562541629532578, 562992907356640, 265750982861125933825305303956792501928528029845510052385816434231016183244466245416569241315074543941, 562992907356640, 562958547552736, 565226357590496, 563233425459680, 565226357590496, 562958547552736, 562958547552736, 563233425459680, 563233425459680, 564092452604384, 576565406730720, 564092452604384, 562958547683808, 565226357524960, 572029787048416, 565226357524960, 562958547683808, 567494167366112, 562958547683808, 567494167366112, 572029787048416, 572029787048416, 265750982861125933825306182390928212796108543268269265302205952132519927773371506120771472758392500549, 265750998701117685802269989328406342501800399628060820896377999221716326456750450133072572544607861605] = some [] := by
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
private theorem tv_0_1_0_7 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨1, 1, true⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [564092452506080, 1464729671602148451152313618048984966273069771170, 564092452506080, 564092452506080, 566291542903264, 566291542903264, 564092452506080, 568490633333216, 566291542936032, 568490633333216, 1978643212360697238219068824988416657683303872439214342801178581703817507441667463188483076712895530029242473252780431269271353544238284979449301717408975879426005873603589927, 1978643213742763555902738753787814087244437501563487898662117985956750812971283097826552341895271384589045832072233907748807095317309097923729870060297681657405799919908763431, 570861488736736, 570861488736736, 1461507212517212945634006244942227580074719209890, 567494167300576, 1464361707902624865396122816881126570351779670434, 567494167300576, 1461507212517212945634006244942227580074719209890, 1464361707902624865396122816881127696247391545762, 1464361707902624865396122816881127696251686513058, 265750982861125933825305303950503285570015127197733514590030312156635439106942290593401971362506085381, 265750982861125933825305303950503285570015127197733514590028327629871553787267899961441962776344646661, 564092452506080, 265783407324242466704484759773601308214708517329128691845476941029785019446923425448086165841317280516, 564092452506080, 564092452506080, 566291542903264, 265750967021617343999857887145449656257923340495678729455246502646814686279962699637492166102808869636, 566291542903264, 564092452506080, 568490633333216, 566291542936032, 568490633333216, 1464361707902791009388216429662742407058780350882, 564092452506080, 564092452506080, 562958547552736, 562958547618272, 562958547618272, 562958547552736, 562958547683808, 562958547552736, 562958547683808, 265750982861125933825305303521159442431146063910884433103587319896682726972133712663517964790362625029, 265750982861125933825305303521159442431146063910884433103585996878840135956832294831794803561608238085, 1464361708073098346981988911705163721558732074402, 1464361707902624875537327618706966285937917585826, 1464361707903289471788111673485100056661631986082, 1464361707902624855254918015055295861990666299810, 1464361708584518822163201601654767300262929398178, 1464361707902624855254918015055295861990666299810, 1464361709266412789071485188254238738535192488354] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_8 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨2, 0, false⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [1464361708604457318159011353442088495969326889378] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_9 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨2, 0, true⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [1464361708242990299242515357261234712918694586786, 577458793384416, 1465075334476553692687376702612067772959531493794, 577458793384416, 571892348029408, 1464361710630200712746847559627343025393487604130, 571892348029408, 576565406730720, 1464361710630200712746847559627343025393487604130, 576565406730720, 1978643212360697238219068824983734034857829883572288524845157895757994763624027742101589397103421084505635867774377318967946898335687481444205766184870699258346878760311733031, 1464361710630200712746847559627343025393487604130, 1464361708243073376309164564560348551234137909666, 579967121394144, 579967121394144, 562958547552736, 562958547618272, 265750982861125933825305303520792571476899477923267359208931375535900475326164520366473953845654244869, 562958547618272, 562958547552736, 562958547683808, 562958547552736, 562958547683808, 265783407324725392821735140015366153751133763937864709226657980576437630180031517837354519787150407748, 1464361709264086631205307383879051265702779447714, 1464361707902624875537327618706966285937917585826, 1464361709264418939471904213075506618964552739234, 1464361707902624855254918015055295861990666299810, 1464361710626213023688890411095717375938439178658, 1464361707902624855254918015055295861990666299810, 1464361710627542256755277727881538788985532344738, 1464361707907941787520467282198581514179038964130, 564332970674656, 1978643212360697238219068824983734034857829884612026438940391661819617894782728483694124232033599822454788923041138937099407103479843568959800332830696174621407512289776122663, 564332970674656, 563233425459680, 563233425525216, 563233425525216, 572029787048416, 563233425459680, 572029787048416] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_10 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨2, 1, false⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [1464361709285022052000907623255738521194496813474] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_11 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨2, 1, true⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [1461518362932430573736139936313975609465100069282, 1464372859636436665316930530873860928300137867682, 1461529513347565134912829221031853391796251945890, 1461507212517296012559450651596097827133948193186, 1464361708072849115782041290969962650008309231010, 1464361710624966867689152302494454642631869753762, 1461596415838372501972964929339120085783163201954, 1464372858317842493498256508252879103337492933026, 1461518363570460011712917689195097481721083361698, 1461507212517296012559450651596097967871436548514, 1461518364251024745554813958934960812127465531810, 1464361710624966867689152302494450139032242383266, 1461518363230759191864417606788338970560442689954, 1978643212360697238219068824983734034857829883572275303725781321215582201988194969249403326060956481461355919559236374900170290410314423373220468658733976499303210022326647591, 1461529513603358457175988374647475312333448833442, 1461507212517212945634006246122819200792130513314, 1464361709266412789071485189287251973415132752290, 1461864025804177359279633188840715427295475558818, 1464361707902624865396122818061719316964802849186, 1978643212360697238219068824983734034857829883572275303725781321215582201988194969249403341359474007738972353101729440659184219103949115743076756468979008953697100830605982503, 1464361707902624865396122818061719316969097816482, 1461518362932513650802789143613089447780543392162, 1464384011370248475378943045511836625707044202914, 1461529513347648211979478428330967230111695268770, 1461507212517379089626099858895211665449391516066, 1464361708072932192848690498269076488323752553890, 1461596415838455579039614136638233924098606524834, 1461529513943142354091137664353347644217279674786, 1461596415838455579039614136638233924098606524834, 1461529514623707087933033934093210974623661844898, 1464361707902791009388216430834110655739336878498, 1464361710625049944755801509793563977347685706146, 1461518362932430573736139936313975609465100069282, 1461529513347648211979478428330967230111695268770, 1461507212517212935492801444296983988818504870306, 1461507212517212935492801444296984129556530096546, 1461507212517212935492801444296984270294555322786, 1461507212517212935492801444296983988818504870306, 1461507212517212935492801444296984551770605775266, 265783407324725392821735140015366153751133763937864709226657980576437630180031517837354519787150407748, 1464361707903289471788111674628798189231624186274, 1464361708584518822163201602761571944685502495138, 1464361707902624855254918016235887482708077603234, 1464361709266412789071485189287256406662927378850] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_12 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨3, 0, false⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [1464361710646151519684700162883038571644836669858] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_13 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨3, 0, true⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_14 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨3, 1, false⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [573404176484832, 3353732544361657240607343334147479876368021123065900902962536684619967624146613620902284394655876924402619437592223975271872365373566497234105791886599826198114283880040660064985947750033590292937033912706604631012775294544687707231463477532744815883888283695032234067805629069055336646636565029245698509757878662883960266538508953937160387042666692299515200539646479713370905130, 573404176484832, 572304664889824, 572304664889824, 572888780507616, 576565272512992, 572888780507616, 572029787048416, 574022651873760, 572029787048416, 574022651873760, 576290394606048, 572029787048416, 576290394606048, 572029787048416, 1461507217982998454160530255592053764342988990882, 572029787048416, 265767187173171368414397670841152599528444642605183397535262892959064152779101385022348939221602941700, 3353732544361669155458739953653663610046641905403828088427576622173506440759559791109780482401942816825455853858636049206666246690604027546602179190064566204205471043181618368476517333971301813411443923938246282921821280387409774901447287500312924400701962893204356429763408545728509187114595795789870761169379482150696861694448767691040271951019420463187834322391634703795625259, 265767187173171368414397671485168364236748356702310277496444015030676110770399340163587096129601288964, 1978643213742763555902738753787814087244437501563485915544626789967414100469730772797660050372642459121376273005051029787383483627501099177534442908015812289186203256601130791, 265751030381584351911314712441509517763414921667345135963494433996249543260253205262302500543147302404, 265751220461485375634880399474839712285739598478978925408786829928682817346664689908682483192309221124, 265750967021617344003459483430399452922737396660368989980398540866409870748516459380715165723499969284, 572888780507616, 576565272512992, 572888780507616, 572029787048416, 574022651873760, 572029787048416, 574022651873760, 576290394606048, 572029787048416, 576290394606048, 572029787048416, 572029787048416, 1978643211900009694429811114048356054822413901818494994149761929465943209454815610024168773789391901997823768404714678349182294345813195046930583108918389766335687280749598502, 265750967021617344003459484289087139200378092414843631664472229683466710714151834917184873808578755332, 265751473901353407266301315519279971648840947119499293459839905284895327982987238039724420319873061636, 265752994540561597054826811785921527827438361612569609022179072744361518718952794022873872885770894084] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_0_15 : checkTree 3 ((baseTable 0 1 0).set 1 1 ⟨3, 1, true⟩) 102 ⟨1, [1, 1, 1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

private theorem solve_0_1_0 (N : Machine4) (h11 : N 3 1 = none)
    (hAlive : ∀ q a, ¬ (q = 3 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_0 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨0, 0, false⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [1464361707945243228186994016477744492021216733602] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_1 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨0, 0, true⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [1464361708243571846315263224471366064687782324642, 1464361710630200712747079674270152749730942183842, 1464361708243571846315263224471366082280035477922, 570861320964576, 1461507212517212945634006245089801532664395622818, 570861320964576, 567494033017312, 569693123447264, 1464361707902624865396122817176274475526837528994, 569693123447264, 1461507212517212945634006244942227580074719209890, 620836633681299075381525494769967414407150501990144068707872254814395341738557287205687270509903743521669906673362738225063532692053449419291184092702719563279652180743480663025045489120786372752600613930777973874675199682299579106486769546837687852175512133101537927277566544626261887681437587972353951025007692137683348540370337276655852368813586413487555943972428057548633354539876405351600156733154890523159402360693228452074320241330770102928515098956439401198881790364061259975455375781685739431058099308, 265750967021194370588191762033519825930522072197260425246138658195576652741399108589470426847625689860, 1464361707902624865396122818061718191064896006562, 1464361709266412789071755988670845650350266935714, 578832780560864, 567494167497184, 578832780560864, 578832814180832, 1464361707902624865396122817176274475531132496290, 578832814180832, 567494167497184, 567494167497184, 1464361707902624865396200188133581906618960865698, 567494167497184, 1464361707902624865396200188428729811798313691554, 1464361709266412789071755988670845720719279548834, 576565037894112, 1461507212517212945634006245089801532664395622818, 576565037894112, 1461507212517212945634006244942227580074719209890, 578832814246368, 578832814246368, 1461507212517212945634006244942227580074719209890, 576565138557408, 576565138557408, 1464361710630200712747079674270151905304938310050, 1464361707902624865396432303071540662033527630242, 1464361710630200712747079674270152186780988762530, 1464361707902624865396432303071540662037822597538, 576565037763040, 567494167497184, 576565037763040, 569761843120608, 1978643219271028827039652706902412209779451533085880356837653868217969797053577971891675524154871956128075204273475903541871074773113686596276297851311812237150696992898956071, 569761843120608, 567494167497184, 567494167497184, 265751093741069849903969409996377114786203782382735641654289309789703498906572755868361163565294326085, 567494167497184] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_2 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨0, 1, false⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [1464361707987861601118760531709780156265631083426] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_3 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨0, 1, true⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [1464361707945243308999719781027364351411491989922, 1978643219271028827039652706902412209779451533432305415049193868118648447718643468013071024681585145888365905230301173776733497667667546755928986616508794963893022006643931943, 1464361707987861681614573646202342682873983691682, 564092452506080, 1461507212517212935492801443263966320690769979810, 564092452506080, 562958547552736, 565226357459424, 1464361707902624855254918015350439263553211885986, 565226357459424, 562958547552736, 567494167366112, 562958547552736, 567494167366112, 1464361707902624855254918016235882979091270363554, 566291475794400, 567494167300576, 566291475794400, 562958547618272, 565226357459424, 1464361710630200722888052361453177181831924050338, 565226357459424, 562958547618272, 567494167300576, 562958547618272, 567494167300576, 1464361710630200722888052361453177181831924050338, 1978643213973108436851016204678656184699275112470856703347163044666980888771389104900392765899633343495597787608912561828917757084450621798451604979417098328503706527302556710, 1978643241384089911265521135391818923843049136889245929348006446375083403329235975251217056879185259462092286256525504377334461599473444614491855471867921705036406628048366630, 1978643219271028827039652706902412209779451533432464068481712762627599187348636741990848965493491372652737042805125376353739540095924696841151617789881235403262407262373296935, 265751093741069849903969409561163336391884893523261916689267659846688757701103970939645956231566208485, 265751093741069849903969409561163336379389343291285864650276533082979870256430012704114155116882849285, 265751093741069849903969409561163336379389343291194936456788623531980845745464544955825811303314255365, 566291475794400, 567494167300576, 566291475794400, 562958547618272, 565226357459424, 1464361707902624855254918015350439404291237112226, 565226357459424, 562958547618272, 567494167300576, 562958547618272, 567494167300576, 1464361707902624855254918016235883119829295589794, 1464361710630200722888052361453177252200936663458, 564092452506080, 1461507212517212935492801443263966320690769979810, 564092452506080, 562958547552736, 565226357459424, 565226357459424, 562958547552736, 567494167366112, 562958547552736, 567494167366112, 265751093741069849903969409560744055288821816448009170930552525418321068491409826414140611889865453061, 568490499115488, 1465075334476553702828581504290328187917476850082, 568490499115488, 562958547683808, 565226357524960, 1464361707902624855254918015350439545029262338466, 565226357524960, 562958547683808, 567494167366112, 562958547683808, 567494167366112, 1464361707902624855254918016235883260567320816034, 1464361710630200722888052361453177392938961889698, 265751093741069849903969409567033271647334719098614072850731917397199403338802407187220102291241472325, 1464361707902624936384865915852386582901101193634] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_4 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨1, 0, false⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [1464361708073098346982293562173851484754459782562] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_5 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨1, 0, true⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [1464361708243571856456159749037224097547428063650, 578764228561376, 1465075334476553702828581504290329032343480723874, 578764228561376, 1462220839091141783066387561098973579901479709090, 572029652765152, 1465075334476553702828581504290329032345628207522, 572029652765152, 1978643211900008465631029899522488824684965504148085359958880263305128499804954719553270282511070325129547569746752445661640729071337506238238580971427761493208108497711553574, 1465075334476553702828581504290328187917476850082, 1465075334476553702828581504290329032345628207522, 1465075334476553702828581504290328469393527302562, 1465075334476553702828581504290329032345628207522, 265750967021133945814967972956497946987384436150779977340801975083641306706970028133493591589875694340, 1464361708243571856456160957967655398195030157730, 575396806429152, 575396806429152, 572029518481888, 572029518547424, 572029518547424, 1461507212517212955775211046768062792048344852898, 1464361707902624875537404990254565305243694819746, 1461507212517212955775211046768062792048344852898, 1461507212517212955775211046768063355000445757858, 578764094835168, 1464361707902624875537327619002114191117270411682, 578764094835168, 1461507212517212955775211046768067295665152092578, 572029653223904, 1461507212517212955775211046768067295665152092578, 572029653223904, 1464361707902624875537404990254569527384451606946] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_6 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨1, 1, false⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [1464361708243571838709359623101994141732117178786] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_7 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨1, 1, true⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [564092452506080, 576565037894112, 564092452506080, 564092452506080, 565226323904992, 574297295096288, 565226323904992, 562958581107168, 567494066702816, 562958581107168, 567494066702816, 572029552298464, 1461507212517212935492802652046828172348323031458, 572029552298464, 1461507212517212935492802652046828172348323031458, 569761977108960, 1978643219271028827039652706902412209779451543829816768607464406749548977699471457550005621617763185423378715640066230983659238336425875021843714202613492484214525686155197223, 569761977108960, 1461507212517212935492801443263966320690769979810, 562958681836000, 562958682032608, 562958681836000, 562958681770464, 562958681770464, 562958682032608, 562958682032608, 564092452506080, 576565037894112, 564092452506080, 564092452506080, 565226323904992, 574297295096288, 565226323904992, 562958581107168, 567494066702816, 562958581107168, 567494066702816, 1461507212517212935492803860977254969413477624226, 572029552298464, 572029552298464, 564092452506080, 564092452506080, 562958547552736, 562958547618272, 562958547618272, 562958547552736, 562958547683808, 562958547552736, 562958547683808, 565226357918176, 1978643219271028827039652706902412209779451543829975422039983301258499717329464731788520188829767600984942739193284461716124656562760778951241151694386579130720189801577462567, 565226357918176, 562958548077024, 562958682294752, 562958548077024, 562958682294752] = some [] := by
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
private theorem tv_0_1_1_11 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨2, 1, true⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_12 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨3, 0, false⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [1464361710630200722888284476095991339419320740258] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_13 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨3, 0, true⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_14 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨3, 1, false⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [573129063696864, 576427598940640, 573129063696864, 573129063696864, 574228575357408, 574228575619552, 574228575357408, 572029552298464, 576427598678496, 572029552298464, 576427598678496, 572029552298464, 1461507217972364670758916601747393195633359776162, 572029552298464, 578626789607904, 3353732544361657240607343334147479876368021123065900902962536684619952074539886987373177630003262173539543914353661769305881216049182234440107281057918922777607192697264636583828992806279283149331140995737620696865048235544686520651364893691318831157994776952618730192747831590222187029810264154393052557984979842433027119166821639515635303923921843421678721683675936428493380138, 578626789607904, 1462934465665070630639973678933980839112189471138, 572029652765152, 572029652765152, 265750967021375644910564766770407311352058847464084936884700101538038159595155098720037343197815388932, 265750967021375644910564766770407311352058847464084936884700101538038159595155098720037343197815388932, 573129063696864, 576427598940640, 573129063696864, 573129063696864, 574228575357408, 574228575619552, 574228575357408, 572029552298464, 576427598678496, 572029552298464, 576427598678496, 572029552298464, 572029552298464, 573129063696864, 573129063696864, 572029518481888, 572029518547424, 572029518547424, 574228609370592, 480481077043610063518716283642188224135453159039945750625164473070738567822471282720270390737958462582538349026423348357464002261112815737403030036967589562164349675114456959394478930478997348823533004922061052138391683743140535637350135217160529778114077188119722760, 574228609370592, 572029653223904, 572029653223904] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_0_1_1_15 : checkTree 3 ((baseTable 0 1 1).set 2 1 ⟨3, 1, true⟩) 102 ⟨2, [1, 1, 1], 1, []⟩ 5 [] = some [] := by
  decide +kernel

private theorem solve_0_1_1 (N : Machine4) (h11 : N 3 1 = none)
    (hAlive : ∀ q a, ¬ (q = 3 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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

set_option maxHeartbeats 0 in
private theorem tv_0_1_2 : checkTree 4 (baseTable 0 1 2) 107 startPos 0 [] = some [] := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem tv_0_1_3 : checkTree 4 (baseTable 0 1 3) 107 startPos 0 [] = some [] := by
  decide +kernel

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
private theorem tv_1_0_0_3 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨0, 1, true⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [570105406720480, 1461507213899620516872083516602996588960763914658, 570105406720480, 567906349877728, 567906417052128, 1461507213899620516872083517045718446729793153442, 567906417052128, 569590010644960, 1461507213878352797951091249708115239591222487458, 569590010644960, 567356594063840, 567425380714976, 1461507213878352828374705655185620875512099416482, 567425380714976, 567356594063840, 576290260388320, 1461507213878352787809886447882280027617596844450, 576290260388320, 578386204461536, 3353732544361657240607424131048968563170360243000394486873513708472883269864853205696889027366732994441200121184064924640904981735052341096325715711420677129797439792397024077338053015776968251028045785561089699434570458203692008252159458100417153560794583661856703159061664046359722182641496503881805891684809687888315265136051907514052260427931649341757556829534953770971179818, 578386204461536, 576290260388320, 576221540977120, 576221540977120, 576152821434848, 576290260388320, 1978643212821386010807107750444979246519135399340784739261953044005887577617553146476215361114800845612007085651458769923584263776335632933815501334027146419976404946434880295, 576290260388320, 1461864025801612354846809898227887250078235142562, 1461864025801695431913459105527001088393678465442, 1461507213878352787809886447882280027617596844450, 265751980780847771433096568052176660966250375486503047414146525953454364769358869493720203167813869988, 1461507213878352828374705655185620875512099416482, 1463291273494899854194441650101100737833183783330, 1461507213878352787809886447882280027617596844450, 1461507213878352787809886447882280027617596844450, 1978643212130352852018904017765050920136865750343099261756770443925785577570790186278441693876367458131721473607132770192798343791371654954838657454772358689379632513430469415, 1461507213888986652340984982168851331994342173090, 578386204461536, 265750967021375644907412929661886676136713814738936270988444207195369709089668232526819965136635394820, 578386204461536, 576290260388320, 576221540977120, 576221540977120, 576152821434848, 576290260388320, 265750967021375644907412929661880124869759115933881308855612338847587025188163876020595323540996324100, 576290260388320, 1461507213878435864876535656361985486650451470754, 1461507213878352797951091250888706860308633790882, 1461507213878518941943184863661099324965894793634, 1461507213878352787809886449062871648335008147874, 1461507213879017404343080107455782354858554730914, 1462934461572387980757351394631256672061329811874, 1461507213878352787809886449062871648335008147874, 1462934461573717213823758054230192200651268729250] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_4 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨1, 0, false⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [567906886814176] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_5 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨1, 0, true⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [567906383759840, 567906484357600, 567906383759840, 576702510402016, 576702845946336, 576702510402016, 1978643212821386010807107750444979246519157780330556987816908465507729378562449576593094228997275944073106023984899349296663459743333305477734170216122103322846689090524239655, 567494167497184, 265752994540108411252496942150501387975921659161854728100136226537553996363740520342836709953614609156, 576221474064864, 1461507213878352828374705655185620875520689351074, 576221474064864, 567356594325984, 567494167497184, 1461507213878352787809886447882280027626186779042, 567494167497184, 567906484357600, 576187516979680, 576565406992864, 576187516979680, 265750998701117921836537757178739221567941854524022599582357209107210362047951962479603707221925981701, 567425448020448, 567631606450656, 567425448020448, 567356728543712, 576290529085920, 576565406992864, 576290529085920, 567631606450656, 1461529513315613058048016149059385122587137819107, 567631606450656, 567906484357600, 265750982861125933825303545465064671931264275721938176532664521415225102305868701541953250720893416005, 265750998701117921836538636045573024298931645979026090348411329167114646975006964630419522547976515909, 265750998701117921836538691108920086351090782703074600672111440907922075481604314055246149950705253221, 576702711728608, 576702711728608] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_6 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨1, 1, false⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [567906886814176] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_7 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨1, 1, true⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [569590010644960, 576565037894112, 569590010644960, 569590010644960, 567425347160544, 567700225329632, 567425347160544, 567356627618272, 576290159725024, 576565037894112, 576290159725024, 567631505787360, 567631505787360, 265753121260014102955758744964101002083613100849008033842415396886906220190957782137540806120211446532, 1461507213878352797951091249855689192180898900386, 1978643211900008467347229314655037205691528429023416149143232059302004055144940705148008715392291711843601725037522377801632132648502849642847449287173974519225700637094077478, 1461507213878352787809886448029853980207273257378, 567425447823840, 567631606450656, 567425447823840, 567356728281568, 1461507213878352787809886448029853980207273257378, 567631606450656, 567631606450656, 265750967021617344000308965266158389046395325301287489066077182012097163596773526507026911235509811972, 569590010644960, 1461507213878352797951091249708115239591222487458, 569590010644960, 567356594063840, 567425313606112, 1461507213878352828374705655185620875512099416482, 567425313606112, 567356594063840, 576290260388320, 1461507213878352787809886447882280027617596844450, 576290260388320, 265751980781089470525992601965913465611168466819256995589800726443479870660042938559680220796937218820, 265752994540561597051676238665668542175941608337240707909650810106357127010996068991122245132651559684, 569590010644960, 1461507213878352797951091249708115239591222487458, 569590010644960, 567356594063840, 567425380714976, 1461507213878352828374705655185620875512099416482, 567425380714976, 567356594063840, 576290260388320, 1461507213878352787809886447882280027617596844450, 576290260388320, 569590111308256, 576565138557408, 569590111308256, 576290260388320, 567425447823840, 567631606450656, 567425447823840, 567356728281568, 576290260388320, 576565138557408, 576290260388320, 567631606450656, 567631606450656, 1461774823841654948523342038421412036874767210786, 1461953228782489554406025248436985205171090925986, 1461507213878352787809886447882280027617596844450, 567425447823840, 567631606450656, 567425447823840, 567356728281568, 1461507213878352787809886447882280027617596844450, 567631606450656, 1978643212130352852018904017765050920136865750343178588473029891180260947385786823397669167288912969931255377361278700547842825910923716743074208519951997298742333504649575207, 567631606450656, 569590111308256, 576565138557408, 569590111308256, 576290260388320, 567425447823840, 567631606450656, 567425447823840, 567356728281568, 576290260388320, 576565138557408, 576290260388320, 567631606450656, 567631606450656, 1461596428769102445008232121949434237960586303778, 265750982861125933825303545465064671937512050884566684165057822085231592640200558870686414999548637765, 265750982861125933825303544606390088193853968854752952267550319870322010082963994903905510053946338981, 1462934478586495942210557460439589599456946854178, 265815340747613980202295993196651438242426034260047380159717317864147299405337671197770321261706295364, 265750998701117921836538691108920086351090782749624152725912814980556866431294954947345503722812750693] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_8 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨2, 0, false⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [576702979901920] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_9 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨2, 0, true⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [576187584154080, 576565541210592, 576187584154080, 265815340747613980202295127639476568089478826327114915118247387754707142424150541082391784593450809412, 576221943826912, 576496318417376, 576565406992864, 576496318417376, 1461507213878352828374705655185620875512099416482, 576565071448544, 576565406992864, 576565071448544, 1461507213878352828374705655185620875512099416482, 576427699603936, 576565406992864, 576427699603936, 576565272775136, 1461529513305647723295058271724320054664803402211, 576565272775136, 576221943826912, 576565037894112, 1461507213878352787809886448029853980207273257378, 576565037894112, 1461507213878352787809886447882280027617596844450, 576221474064864, 576221474064864, 576152687479264, 576152821696992, 1461507213878352787809886447882280027617596844450, 576152821696992, 576290663303648, 576565541210592, 576290663303648, 576428102257120, 576428102257120] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_10 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨2, 1, false⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [576702979901920] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_11 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨2, 1, true⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [265750967021617344000308086828655326919999166619372285085269071667527591869712314058642045943116167940, 265751093741551359816018542274812397768334317213838069212663507537051620940924394704529141849052642052, 265767187173171368411246274883424238234107938813012845129300627995607945182319690195833593988482562820, 265751220461485375631728996862281782338930959903586033252644767994911277980093232351757735254893741828, 265751980781089470525991724387098089762510816042063873435243753280243838163958549392409748666629401348, 265750967021617344000308087687343013197737674524091525752294901325312283412193588470099352485197216516, 265752994540561597051675361086853166327283957560047585755093836943121094477309250570238495913355213572, 265751980781089470525991724387098089762510816042063873435243753280243838163958549392409748666629401348, 265767187173171368411246274883424238234107938811740005774686388528799626455037396318084581181048978180, 265752994540561597051675361086853166327283957560388524862130778569647053295877430805503584167236172548, 1978643219271029705733753254767183976014411839046003409860458922574790714761125484934945829926027468179939050710791154123529906529949316183531656704157400829417910520515159078, 1978643219271029707020902816066647285962963079698327234836282384903651486236515896114771333139135329822043575848968545986787115439583488655899822268840919168725505160243733542, 1978650759824858987407834930496422565934243020096490431734700462326426750095272195657796879400829785633617029643587637518643732349203677445611808292732979433033447120749618214, 265750982861125933825303548041127730858195854883185428073166294164658789847221223486847479102570756773, 1978650759824858987407834930496422565934243374998211299857001515463618642417744836920452682072790059310312527707047741110855911641569671538353648968569575204513008037649081382, 1978643212130352852018904017765050920136864336282903155843883730934835113480301796981653900327414037534397044415302744948139602825017473318748064714919011775355629956428872487, 265751093741551359816018547426938515434764029990853108902112484109947284570488601805528180401131191044, 265751220461485375631729002014407900005360672680601072942093744567806941614357743109458433443095856900, 265751980781089470525991729539224207428940528819078913124692729853139501793522756493408787218707950340, 265750967021617344000308092839469130864167387301106565441743877898207942228646851108598923646744099588, 265752994540561597051675366238979283993713670337062625444542813516016758144475886924850811554422291204, 265750967021617344000308092839469130864167387301106565441743877580252451799408146447905450430622300932, 265767187173171368411246280035550355900537651588755045464135366050514849126641298975138613661399218948, 265767187173171368411246280035550355900537651588755045464135365101695290385421037447989836445035756292, 265750967021617344000308092839469130864167387301106565441743878221210345204381408224224039294867831556, 265752994540561597051675366238979283993713670337403564551579755142542716925441637906502622719314721540, 265750967021617344000308092839469130864167387302561238965101495009448348464641067719688140623162080004, 265750967021617344000308085969967640642260849375802403854466281308424269980344549494027925461111372548, 265751980781089470525991724387098089762510816042063873435243753280243838163958549392409748666629401348, 265752994540561597051675366238979283993714433004923474926255619564431677875945443361037313934615608068, 265750967021617344000308085969967640642260849375799562695240973461873014503003499046246255802451196676, 265750967021617344000308085969967640642260849375845021242845899011740014686956158665684612773015943940, 265750967021617344000308085969967640642260849375981396885660675641153365052830727704273113956702452484, 265767187173171368411246328122060787453883417068631577545951226907230624857925589061110689780112521988] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_12 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨3, 0, false⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [567906887010784] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_13 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨3, 0, true⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_14 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨3, 1, false⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [567906887010784] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_0_15 : checkTree 3 ((baseTable 1 0 0).set 0 1 ⟨3, 1, true⟩) 103 ⟨0, [1, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

private theorem solve_1_0_0 (N : Machine4) (h11 : N 3 1 = none)
    (hAlive : ∀ q a, ¬ (q = 3 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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
private theorem tv_1_0_1_1 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨0, 0, true⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [576702644259296, 572304799435232, 576702644259296, 1462934465675714879804403364132941373278365198754, 572304530672096, 572304799304160, 572304530672096, 265769214691873922372869787972826222179660552842636861873799450874812029056654220106009960225904491268, 1462934465654447160883411097385633976498500184482, 1978643683645311595782889595812614433079059924238974505852957603491200774161850685902598968053067716920074930149807657989498623557705972788328088409192744237037372975761744934, 1462934465654447150742206295559798764524874541474, 571823494334944, 265750967021375644910564327162569473711447141467166028849993378381595742427296021967494811890971015940, 571823494334944, 571754774792672, 265750967021375644910564327162562922444407023861695924765327232611342048601201344608380834988378258180, 265750967021375644910564766810658296646327829595155366882273921667513906967261069088013898186499521284, 572304799173088, 571789403294176, 572167360350688, 571789403294176, 265751220461005753993829039354393381164878241549295941686381124285542583041979609476247464516157182277, 571823763098080, 572029921397216, 571823763098080, 265750967021375644910564327162562922444309402375507191106088058414232322973098120776509599048935897860, 571892482443744, 572029921397216, 571892482443744, 572029921397216, 1461596415678813563955238526830096818090020984291, 572029921397216, 572304799173088, 265751093741071738178118584230191790533088314017139663765178206647209782073668898250188969352182671205, 265811792589582386909636948282058288203835983689492721447000187147836906036521638095140999895881824324, 265811792589582386915039350008328326158268529216590583651792092690622692449180653202483476411927705668, 265811792589582386915039398094838757711611625355135624548799387359941935731572364568574639326867175492, 265811792589582386909637002379381919116647537124500857172653752733351380435249742650669896396347488324, 572304799304160, 572304799304160] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_2 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨0, 1, false⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [574503453723104] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_3 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨0, 1, true⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [574503453231584, 574503453231584, 572304396388832, 572304396454368, 572304396454368, 573988057156064, 1461507217961741201002352811268610528772441024930, 573988057156064, 571754640574944, 571823360117216, 1461507217961741231425967216746116164693317953954, 571823360117216, 571754640574944, 571892213877216, 1461507217961741190861148009442775316798815381922, 571892213877216, 573988057254368, 572167360219616, 573988057254368, 571754640706016, 576221473802720, 572029787048416, 576221473802720, 571754640706016, 571892213877216, 572029787048416, 571892213877216, 572029787048416, 1461507217983008838793706663409236511239351347618, 572029787048416, 1461507217961824267927797216741889295851747060130, 1461507217961907344994446424041003134167190383010, 1461507217961741190861148009442775316798815381922, 1461864029885249989098014245853318809387193641378, 1461507217961741231425967216746116164693317953954, 1461864029885582297364615910771499365239375309218, 1461507217961741190861148009442775316798815381922, 1461507217961741190861148009442775316798815381922, 1978643215585518647837015791403482374244004112514479273816953802274377039054439927518277247171246180463341391425213961882747608305289980084587136011556773092136672194897525543, 1461507217972375055392246543729346621175560710562, 573988057254368, 572167360219616, 573988057254368, 571754640706016, 576221473802720, 572029787048416, 576221473802720, 571754640706016, 571892213877216, 572029787048416, 571892213877216, 572029787048416, 572029787048416, 265751093741071738178118584230191790532307342133448488497968816544087624194697303558400430527868872549, 265751093741069849903955340499487658862570146466765009346141865241596411445229905600055373409663594149, 265751220461005753993829972747894443623871210758390929035012159444996790577332689027575594079305612133] = some [] := by
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
private theorem tv_1_0_1_7 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨1, 1, true⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [573988057156064, 1463023668635324350301461540141091167967261010338, 573988057156064, 573988057156064, 578386170808800, 578386170808800, 573988057156064, 573988191472096, 1978643226642049188448275514282335596360334153916591704809245597000178149845854746521492828789934933161270421961981379775748844899091799023247315448847311254320997738356634407, 573988191472096, 322300464592135056412894659938510404800785950888399028190130971378885432955078246152704173589167284572346639166154747518617506917489659868774143937510522885442755485267809298143164423747926922125831616231275361869604818461340579177502189602765309784765491692206459557812828752454206338184181482059717970822417176476013783445440466082659854753540042896385832674118065053508812098215018738731448661934149919286593671578530126148977051739168116103241698671127235433582450047586552212867876676897902201999185587322697375719764869499344098618395845887500777975314023843536427386226184032630245926011941600596109803386530650619628241533781879635123816884424646166080255932731861187654711085515587590586215931129294316114535023306283734765580965525396602782147261585109126845808325219734536304684252614571011710820044291732465358999119408, 265759077096912846295500709477192152405479098098687398663926118648466433459655928113209429817394118788, 576359046875616, 576359046875616, 1461507217961741201002352811268610528772441024930, 571892213811680, 1461507217961741201002352811268610528781030959522, 571892213811680, 1461507217961741201002352811268610528772441024930, 1461507217961741201002352811268612780572254710178, 1978643215585518647837015791403482374244002693254258261546528810725360982369058905988622327870275620152009199981440387884031682838127072874777169581425847556196579280090184487, 1461507217961741201002352811268612780580844644770, 573988057156064, 265750967021137722365995658530476960383395229608636257599008527757207700293736410697586230074350467844, 573988057156064, 573988057156064, 578386170808800, 265750967021137722365995658530476960383395229608636257599008527757207700293736340097285909104108468996, 578386170808800, 573988057156064, 573988191472096, 1461953232865877957457286809822236390470246771106, 573988191472096, 1461596420942701467487012566923316958929760594338, 573988057156064, 573988057156064, 571754640574944, 571754640640480, 571754640640480, 571754640574944, 571754640706016, 1461507217961741190861148009442775316798815381922, 571754640706016, 265751093741071738178118584230558655094299060149707263791203785561886032393394010393429704312364536805, 576221474195936, 1461507217961741231425967216746120668310125193634, 576221474195936, 571754641099232, 571892214270432, 1461507217961741190861148009442779820415622621602, 571892214270432] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_8 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨2, 0, false⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [572304531130848] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_9 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨2, 0, true⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [576187517110752, 571961201691104, 572167226264032, 571961201691104, 265751220461005753993829039360997058341316740563176249542393969662049536023722240673794159924349532485, 571892348029408, 572167226132960, 571892348029408, 265751220461005753993829039253661099156029892540990926372261687913664455957942294231847724912683915077, 572167226001888, 572167226132960, 572167226001888, 572167226132960, 1461596415668350741310561437787223784230276318691, 572167226132960, 576187517110752, 576668552956384, 576668552956384, 1461507217961741190861148009442775316798815381922, 572029786982880, 572029786982880, 1461507217961741190861148009442775316798815381922, 572029787048416, 1461507217961741190861148009442775316798815381922, 572029787048416, 1978643215585518647837015791403482374244002693601434279338934058678447895303911853192952880017803334709404727295977509869163868722502605487877725798136162078428893493564422951, 571823763229152, 572029787441632, 571823763229152, 1461507217961741190861148009442779820415622621602, 571892348488160, 572029787441632, 571892348488160, 572029787441632, 572029787441632] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_10 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨2, 1, false⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [572304531130848] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_11 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨2, 1, true⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [265751093741551359819169938272791744356940003137079051637875917487676530985911876787907536688235379460, 265767187173171368414397670881403584822713624734980988199898798459394606843410974404546403865671727876, 265751220461485375634880392860261128927536645826825595098244524022260560291110492867946955422708483844, 265750967021617344003459483685322359786343360447332508177507310953092501685413564364569777589886089988, 265751980781089470529143120385077436351116501965304855860456163229764736089400063751271850376681401092, 265750967021617344003459483685322359786343360448787181700864928225834104596164258512855070890609834756, 265752994540561597054826757084832512915889643483277203543405015506436970530988992391587200252463250180, 265751093741551359819169938272791744356940003137079051637875917487676530985912020194769463151275768580, 265767187173171368414397670881403584822713624734890071104688947379848252450016988580709158890503371524, 265767187173171368414397670881403584822713624735162822390318500618487303597421584895972225339679275780, 265752994540561597054826760304911336457420130654237376501073220370979881030823734466249966850539748100, 265752994540561597054826763739662081568373018282949088496905730586198073613315644250445060698283408132, 265750967021617344003459483470650438216920959989569604502780466785176609748883393862837751467467832068, 265767187173171368414397698144737624140914325306911780489122495471602780004406118690135474532043160324, 265767187173171368414397725622743585028537426336787310643492738810819550316488626031869737817259342596, 265751093741069849903955340928818399565761528687644606355527579134625937872468932875620271471787768485, 265751093741551359819169938916807509065243717234205931599057039559288488939607402675532416507245198084, 265750967021617344003459484329338124494647074544459388160364757357676225332681880134149956966108330756, 265751220461485375634880393504276893635840359923953895639038300016990429966398548590246056245048329988, 265750967021617344003459484329338124494647074544459388138688433024704459639109090252194657408895908612, 265751980781089470529143121029093201059420216062431735821637285301376694043095589638896730195691219716, 265752994540561597054826757728848277624193357580415448141487368962992222257424756956605848098113288964, 265752994540561597054826757728848277624193357580415448141487368962992222257424756956608110789964036868, 265767187173171368414397671525419349531017338832107868161079920531006560585634423887484182922634951428, 265750967021617344003459484329338124494647074544459388138688433024704459639109090252196794859500305156, 265767187173171368414397671525419349531017338832289702351499622690099261551117110783597105158689094404, 265750967021617344003459484329338124494647074545914061662046050297446067362970585421096966572026854148, 265751093741551359819169938272791744356940003137079051637875917487676530985911876787907536688235379460, 265751220461485375634880393504276893635840455257436501824252400773042294932832243144769369042572494596, 265750967021617344003459483470650438216908757303796012795375570010537894045370490883853713384374762244, 265750967021617344003459483470650438216908757303796012795375570010537894120575349391080275911768242948, 265751093741069849903955341358162242704630687308067211121039073362310307396766633011621550862759101637, 265750967021617344003459483470650438216908757303796012795375570010537894195780207898306855137994570500, 265750967021617344003459483470650438216908757303796012795375570010537894647009358941666213603522607876, 1978643226642049188019225660524172489173965312383957894321869079287458216771485269188217232061887179574476699187022605452410708679454459096140787714686184167140022636382219047, 265750967021617344003459490340151928438815295229103015541878474123870428421501174755582337812211661572, 265767187173171368414397725622743585028531324993900514789790290423500202015749204960152228479987055364] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_12 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨3, 0, false⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [572304665348576] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_13 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨3, 0, true⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_14 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨3, 1, false⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [572304665348576] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_1_15 : checkTree 3 ((baseTable 1 0 1).set 1 1 ⟨3, 1, true⟩) 103 ⟨1, [1, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

private theorem solve_1_0_1 (N : Machine4) (h11 : N 3 1 = none)
    (hAlive : ∀ q a, ¬ (q = 3 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_0 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨0, 0, false⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [565192467941856] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_1 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨0, 0, true⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [576359382419936, 572167494699488, 576359382419936, 576358879103456, 1462934465654447160883411097385633976498500184482, 576358879103456, 571892079528416, 571892146702816, 265750967021375644910564327162562922444321605061280782813492955471498141280378761231664544598835034884, 571892146702816, 1462934465654447160883411097238060023908823771554, 480481077043610063492669352263751293377328736635846046558837232977958635953844081462051168754603171478008675441250226770661773227350199475576779300757226797160077427326197041474895327234637052745355518280630720817922767681373204703341633565120374698535846404119722760, 265750967021375644910564327162569473711361722666932721088578803098029782680566110133179328872915892996, 1462934465654447160883411098418651644626235074978, 571892616464864, 572166991317472, 572167360350688, 572166991317472, 572167024937440, 572167226132960, 572167024937440, 265750967021375644910564327162562922444321605061280782813492955148495738304644204116040497676013501188, 572167091915232, 572167226132960, 572167091915232, 572167226132960, 1461864025121151791382193762270734281088876696035, 572167226132960, 571892616464864, 572166991383008, 1462934465654447160883411097385633976498500184482, 572166991383008, 1462934465654447160883411097238060023908823771554, 572167025002976, 572167025002976, 1462934465654447160883411097238060023908823771554, 572167092046304, 572167092046304, 1978643270868171380926804169618385639958216487996256483569328859538473416626832534923463011540942082014060931802157120052716550268484970589411748336274209577512871542682958631, 572167494437344, 572167494568416, 572167494437344, 265751980780636284726475655235570891989100614416299901364090604277679584392484014490487208238862346085, 572167494568416, 572167494568416] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_2 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨0, 1, false⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [565192467941856] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_3 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨0, 1, true⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [265751093741551359822799672894113895135077878112691192468132577297108134480551190555754046812016835332, 265751220461485375638538265603283712249466114982179713668877273169992984052493808521733501355575166724, 565191964133856, 1461507212517223320126132594176355550480200411554, 565191964133856, 562958547552736, 567425380714976, 1461507212517223320126132594619077408249229650338, 567425380714976, 562958547552736, 571892213877216, 562958547552736, 571892213877216, 1461507212517223320126132595209373218607935302050, 565191964166624, 571892213811680, 565191964166624, 562958547618272, 567425380714976, 563233693960672, 567425380714976, 562958547618272, 571892213811680, 562958547618272, 571892213811680, 563233693960672, 563233693960672, 1461596426748675891415159993955051505176080849186, 1978643219271029707020902765044788982422881322212719132397529693962406140610645460490916279363223787855744842422815195215370451593936896793393196721103284273610276797051200550, 265751980780636284726475655235570885590597971331591581963917996635301199449097585650924872985842036197, 265752994540108411252159291935325962154590140960230212201569893145866976031627994659279128842528017925, 565191964166624, 571892213811680, 565191964166624, 562958547618272, 567425380714976, 563233693960672, 567425380714976, 562958547618272, 571892213811680, 562958547618272, 571892213811680, 1461507212517223320126132595209373359345960528290, 563233693960672, 563233693960672, 565191964133856, 1461507212517223320126132594176355550480200411554, 565191964133856, 562958547552736, 567425380714976, 567425380714976, 562958547552736, 571892213877216, 562958547552736, 571892213877216, 565191964232160, 572167360219616, 565191964232160, 562958547683808, 567425380780512, 563233694026208, 567425380780512, 562958547683808, 571892213877216, 562958547683808, 571892213877216, 1461507212517223320126132595209373500083985754530, 563233694026208, 563233694026208, 565191964166624, 1461507212517223320126132594176355550480200411554, 565191964166624, 562958547552736, 567425380780512, 563233693895136, 567425380780512, 562958547552736, 562958547552736, 1461507212517223320126132595209373218607935302050, 563233693895136, 563233693895136, 265750967021617344007061080614287921159558752196793055846437262553280635828600196711197567737228655364, 1462934476564740160621700416572302936469610207522, 265751980780621178533169708502942808043426501670188856283054950417326512458749952262398381150736265797, 265811792589582386910538308439487384962535497385409487464631744950380693468847721776567898021069797444, 265751980780621178533169708502942808043426501670279773378264801506966687733663566591403260425444307525] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_4 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨1, 0, false⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [567425850935776] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_5 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨1, 0, true⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [567700225526240, 572167158794720, 563233828506080, 572167158794720, 1461507212527857184657231128462926854856945740194, 563233559742944, 563233559939552, 563233559742944, 563233559939552, 563233828243936, 563233559677408, 563233828243936, 563233559939552, 1461864025121651226388716595038871933857665406435, 563233559939552, 1978643270868171380926804169618385639958216493195051825824861866631274767012391703101895100348951068992213003047799144374912005951847747477799019210606245406898559752048622375, 567700225526240, 567700225034720, 265751980780636284726475658241344709710416949209852277586524564953127370818463317409258567701885921125, 567700225034720, 563233425459680, 563233425525216, 563233425525216, 1461507212517223360690951801332122445785026570658, 563233694026208, 563233425459680, 563233694026208, 1978643270868171380926804169618385639958216493195051825824861866631274767012391703101899078965195159221306388083889253774105882113821697679546434481831007885997193641779149607, 1978643270868171380926804169618385639958216493195051825824861866631274767012391703101899078965195159221306388083889253774106069186031210700739360966171224520292713481704717095, 572167025068512, 563233694419424, 572167025068512, 1461507212517223360690951801332126949401833810338, 563233560201696, 563233425983968, 563233560201696, 563233694419424, 563233694419424] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_6 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨1, 1, false⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [567425850935776] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_7 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨1, 1, true⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [565191964133856, 572166991383008, 565191964133856, 565191964133856, 567425347160544, 567700225329632, 567425347160544, 562958581107168, 571892113213920, 562958581107168, 571892113213920, 563233459276256, 1461507212517223320126133802959217402137753463202, 563233459276256, 1461507212517223320126133802959217402137753463202, 576359046875616, 576359046875616, 1461507212517223320126132594176355550480200411554, 562958681836000, 562958682032608, 562958681836000, 562958681770464, 562958681770464, 562958682032608, 265751980780636284726475658241344658522395804555460565175145504704234166436616191356414610481536986469, 562958682032608, 265751980780636284726475658241344658522395804555460565175145504704234166436616155485000651276983889253, 565191964133856, 572166991383008, 565191964133856, 565191964133856, 567425347160544, 567700225329632, 567425347160544, 562958581107168, 571892113213920, 562958581107168, 571892113213920, 1461507212517223320126135011889644199202908055970, 563233459276256, 563233459276256, 565191964133856, 265751980780636284726475658241344658522395804555460565001713739171117074452266047173075451589522663269, 565191964133856, 562958547552736, 562958547618272, 562958547618272, 562958547552736, 562958547683808, 562958547552736, 562958547683808, 265752994540108411252159294941099735080921170957348276174904827140295226562646994391375286971885925381, 265752994540108411252159294941099735080921170957348276174904827140295224155797753181581966665450140677, 567425381173728, 567425381173728, 562958548077024, 562958682294752, 562958548077024, 562958682294752] = some [] := by
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
private theorem tv_1_0_2_11 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨2, 1, true⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_12 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨3, 0, false⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [563233962854880] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_13 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨3, 0, true⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_14 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨3, 1, false⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [563233962854880] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_0_2_15 : checkTree 3 ((baseTable 1 0 2).set 2 1 ⟨3, 1, true⟩) 103 ⟨2, [1, 1], 1, []⟩ 4 [] = some [] := by
  decide +kernel

private theorem solve_1_0_2 (N : Machine4) (h11 : N 3 1 = none)
    (hAlive : ∀ q a, ¬ (q = 3 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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

set_option maxHeartbeats 0 in
private theorem tv_1_0_3 : checkTree 4 (baseTable 1 0 3) 107 startPos 0 [] = some [] := by
  decide +kernel

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
private theorem tv_1_1_0_3 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨0, 1, true⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [564607848581600, 1461507212538491049188329662749498159233691068834, 564607848581600, 563508303366624, 565707393796576, 1461507212538491049188329663192220017002720307618, 565707393796576, 564092452506080, 1461507212517223330267337395854616809864149641634, 564092452506080, 562958547552736, 565226357459424, 1461507212517223360690951801332122445785026570658, 565226357459424, 562958547552736, 567494167366112, 562958547552736, 567494167366112, 568490599811552, 3353732544361657240607424997968512433190889769820025547139940841096103655111277525005426702533114753424632485973506054563673705186967665372962149437160937587795851775263371538913966409368633124009116461935234426607999422202408131160322827264940790840766505659296719800392990083728271197997571990813146382055512622457959454696575728770485536609309715405215615654310205474559109930, 568490599811552, 567494167366112, 569624471210464, 569624471210464, 567356728412640, 567494167366112, 1461685619169999743396325770050572229865588693282, 567494167366112, 265752994540078198865885046726481874564558149074635873459782574064726969720765796476380441768830353540, 1461507213219055701900587517808892536081253181858, 565191997721056, 565191997721056, 562958547552736, 569624538319328, 563233425459680, 569624538319328, 562958547552736, 562958547552736, 563233425459680, 265750982861126169859575928448862081204969987162066179843411320814853601431300035576679350333776472101, 563233425459680, 265750998701117921836539955096343441376522809218598627603911141227225537287229267742786689752101007941, 568490599811552, 265750967021133945814517773353799160364114459810647449299156696204693643596898157011271873916126329604, 568490599811552, 567494167366112, 569624471210464, 569624471210464, 567356728412640, 567494167366112, 1461507213878352787809925133656081648343011338658, 567494167366112, 1461507212517306397192781802508487056923378624930, 1461507212517223330267337397035208430581560945058, 1461507212517389474259431009807600895238821947810, 1461507212517223320126132595209373218607935302050, 1461507212517887936659326253602283925131481885090, 1461685619160705532019548467481239148953458489762, 1461507212517223320126132595209373218607935302050, 1461864025804187743912964339753105079298981669282, 265750982861126169859575928448862081204969987162066179844766091095758161880140035369417273740366587941, 265750982861126169859575928448865356838514451336348415301908957530162440200213180011319302833002129445] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_4 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 0, false⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [564607848614368, 567906484160992, 564607848614368, 563508303432160, 565707393796576, 572304664889824, 565707393796576, 566291542903264, 567494167300576, 566291542903264, 562958547618272, 565226357459424, 1461507212517223360690951801332122516154039183778, 565226357459424, 562958547618272, 567494167300576, 562958547618272, 567494167300576, 1462934471109598886008629730712907061016677886370, 567906484160992, 1461507223427526790658669978439733059898334816674, 567906484160992, 572304664889824, 572304664889824] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_5 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 0, true⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [265750974941613338005477630300065905616797038484469579321684123694553741885876361654183641967388075716, 265750998701600847953793413639492216780109623921349446563386324356541859182596344895270565726966497412, 265750974941613338005490819957389412699841129577204517101653424968589034646358079139526750206259382724, 265750967021617343999872394713944112127139670817627318578067274917474997699891888831913711735846173444, 265750998701601320022347414108728982194497131084871995682969157307129389849404697932862849768474329924, 265751030381585296044808805741042836196977263975804017024604394264109060672661940070501158466439104964, 265751980781104576719086666294098154369979464421793808002022405960591979076110319200129562310952896964, 265751220461485375631292871110295548555297792565568691096389711017745926266974984839442582317326354180, 265751030381585296044808805741042836196977263975804017024604394264109060672661940070501158466439104964, 265752994540591809438301336345583677091746110527425645839656569023083879834853577159919449536892783044, 265755022059566274876730800099579703986088303526502568875778761670542833549287896142016738702720518596, 265767187173413067507307005585439285249961075452251602509433719003204697509156718330099714556757559748, 265750967021617343999858765623203703678588481311570869321118360788168300582181622088246522251631098628, 265750974941613219988396064908771049050526754196468345661818495162319224454386102946085235149772126980, 265767187173171368410852788126558890183781944334616782192469570023025386589175350378304020477107206916, 265750998701600847953841775787937323365817338797922569342480044653873383677585109273269455891929219204, 265750967021617343999914161282395393479511621431484642839284515383787776839637003576114878418179554052, 265751030381584351907769390293492355786205007377987615348861679073399947563529071670069480075695463940, 265752994540561597051281489637904365850319967466514026213083043631302290497755998744113852604306651908, 265751220461485375631335077326822550308529684189621404794154075005833221349121122287543246012949153540, 265751220461485375631335077326822550308530446857482254275866881054248141080590678723729748393142470404, 265752994540561597051281489637904365850228447323212088407546317821511922721409226401733566981108628228, 265755022059505850102648817993426440755039236447375032815970920671212011421822819796935114742102755076, 265767187173171368410852788126558890183818552391937557314684260346941533699714059315256134726386416388, 3353732544361847878231020834507066273040199985159653436299919727713741974793226070965028184488941738332954640198625311008646723179941148212667958748791408732227321344394160151145783558399126594994711247208353109119188327106530282260465916280153106769556521856716873713082496160043045712402701363601484152860390935736543795409973336363412316440389158979523274506426065030578552107, 265750967021617343999857886327012955274466208071859375816912356536131719693530990938606458912201997060, 265750967021617343999857887185700641552192322626749159452820322776290433652068670005469522635485575940, 265751030381585296044808805741042836196977263975804017024604394264109060672661940070501158466439104964, 265750967021617343999857886327012955274551626872274517768746633958602729618121311791494725493853485828, 265751220461485375631278802371453214637553828690884453197134923025922588161126535681698871793690298116, 265750967021617343999857886286761970579971437377766271273290759600482083800465960700672086388797941444, 1978643212130353731048199763876046305252582055413052191333544882170520160588348120272211821492763902562461483107139127685013561656251445760073559389275846747063621834821362726, 1978643212360697238219068824983734034857829883572433957158300215724532941618188243486839754776819169551325374403428921818115909105058076684044635260753512373698195625645587239, 1978643212130353734024733124325644172780837486487887775303897627117189629335171444166959086496204247902170989127717145468640816423256373287594105035234697419089635473088865318, 265750982861126169859575709054158243644456558221537495310758146047754748975051211180138638787818334245, 265783407324725392821734480502970469936961150161156124804160726124983058254578316668131096749022194212, 265750982861126169859575928448862081208874846679439854293680507433369890979210810727591203427854198821, 265750998701117921836539955096343441381208640625482171328093724006638817156255004963311704198763229765, 265750998701117921836539516306935753456928530646587934232817646807334433259269306170962961043838513733, 265750982861126169859575708624827496641945868280555974576274803005373834971725044842745140549498449573, 265750982861126169859575928448862081208874846679439854295035443091507239316910897398344848264826333221, 265750982861126169859575928448865356842419310853722089752178309525911517636984042044624376195265996837] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_6 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 1, false⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [564607848614368, 567906484160992, 564607848614368, 563508303432160, 565707393796576, 572304664889824, 565707393796576, 566291542903264, 567494167300576, 566291542903264, 562958547618272, 565226357459424, 1461507212517223360690951801332122586523051796898, 565226357459424, 562958547618272, 567494167300576, 562958547618272, 567494167300576, 567906484160992, 565191997721056, 571892348029408, 565191997721056, 562958547618272, 567425447823840, 563233425525216, 567425447823840, 562958547618272, 571892348029408, 562958547618272, 571892348029408, 563233425525216, 563233425525216, 567906484160992, 1461596426727408243482609803682201247080592218402, 1461864025804187743912964339753104657084905990562, 1461596415838465963672945287550623153888036956578, 1461507212517223320126132595209373359345960528290, 1461507223406580986536693748027856557465016506658, 1461685630049730888895862190948824427870850947362, 1461507212517223320126132595209373359345960528290, 1461685631410860361650218445789027439879574821154, 572304664889824, 572304664889824] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_7 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨1, 1, true⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [564092452506080, 1461507212559758626132455912717969936440722762146, 564092452506080, 564092452506080, 564126812277216, 1461518362933022535865533543991063940810518079906, 564126812277216, 564058092734944, 568593578330592, 1461507212559758615991251110892134724467097119138, 568593578330592, 265751101661063955635873471758376477965554442798937250954955324535954122226165158391380857296975526660, 1461507212517223330267337396002190762453826054562, 1978643211900008465631029899522488823202203152578465065611416331830829727909975753157663373743071606521491686015443725867257158392185677274501636379037501604574601734848930854, 1461507212517223320126132594176355550480200411554, 567425447823840, 265750967021617343999857886327019506541591744477744621853412779769231723816182808790060773127159511812, 567425447823840, 567356728281568, 1461507212517223320126132594176355550480200411554, 1978643211900009344325130447387260589256908860927750366157019045599890284995288395128169532637320400556717014404424149145726311004934592642314716823779617460267593470724170790, 265750967021617343999865799992624870637460463248912988270745754463285590748053512468632625710095366916, 564092452506080, 1461507212517223330267337395854616809864149641634, 564092452506080, 562958547552736, 563027267095008, 1461507212517223360690951801332122445785026570658, 563027267095008, 562958547552736, 567494167366112, 562958547552736, 567494167366112, 265751030381585296044809683319858212045634914752997139179161367427345092886728109835672256990035331524, 265751220461485375631335949753511808490757622189799487259262071596173589689207294803229869070641219332, 564092452506080, 1461507212517223330267337395854616809864149641634, 564092452506080, 562958547552736, 565226357459424, 1461507212517223360690951801332122445785026570658, 565226357459424, 562958547552736, 567494167366112, 562958547552736, 567494167366112, 568490599680480, 265767187173171368410909063081928225854757799833353733789488722013029844268522782801316865959395556100, 568490599680480, 567494167366112, 567425447823840, 567425447823840, 567356728281568, 567494167366112, 1461507213197788053968028863842431623115693926818, 567494167366112, 566291542936032, 566291542936032, 562958547552736, 567425447823840, 1461507212517223360690951801332122445785026570658, 567425447823840, 562958547552736, 562958547552736, 265783407324725392821734480502970469936961150161156124804160726124983058254578298737895322740686924324, 265750982861126169859575928448862081221370397004696866783897552808684353275804744672404457601447372837, 265750998701117921836539955096343441387456415834660229627003620766930839291845042361590885678765552197, 568490599680480, 1461507213878352797951129935481916860314489498018, 568490599680480, 567494167366112, 567425447823840, 567425447823840, 567356728281568, 567494167366112, 1461507213878352787809925133656081648340863855010, 567494167366112, 1461518373821466315245784810624779542601908918562, 265750998701117921836539516306935753463176305855765993919012321549973250230524961274158816567789400645, 265783407324241994635943951510917180298401513314271751806334185024594361348703276932368489803245285604, 1461685630049730888895862190948829142577247721762, 265783407324241994643148021686452984956977914541359044128288559867130641464062562847265554009419888708, 265750998701117685802270071753618093900187719605941219191862537610307147941107328184022712193474640741, 265750982861126169859575928448862081221370397004696866785252653844049560876831230865260804686739023909, 265750998701117921836539955096343441387456415834751146722213637233803802455618743564242537348469076549] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_8 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 0, false⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [1461518373821466315246093086704165347307201534242, 1461864035340069385674221611348610325209257388450, 1461529524151623746352912861363682607961685928866, 564092452604384, 576565406730720, 564092452604384, 562958547683808, 565226357524960, 572029787048416, 565226357524960, 562958547683808, 567494167366112, 562958547683808, 567494167366112, 1461507212517223320126132595209373500083985754530, 572029787048416, 572029787048416, 1461551824896988431109352811680182932954078555554, 1462934471120232709974909058286433538964664134050, 1461596426727657475950507839374143314518302824738, 568593578330592, 568593578330592, 562958547683808, 565226357524960, 1978643212360697238219068824983734034857829894316529022360629648765062861894075003382729500557296615660698212849883923273122807904131292095552301356682212301746079357624531751, 565226357524960, 562958547683808, 567356728412640, 562958547683808, 567356728412640, 1461685630049730888896152333071745173684711627042, 1461507223406259061596472911047182282969293302178, 1461864035332094017699512116111187482847575320994, 573129063795168, 576427967777248, 573129063795168, 572029787048416, 574228608977376, 572029787048416, 574228608977376, 576427699341792, 572029787048416, 576427699341792, 572029787048416, 572029787048416, 1463380475177702889509023974779133244135670065570, 1461507217983008838793861406061721136363390151074, 1463380475220238185374142491642486370712243186082, 1461507212538490968058691247995242792331059964322, 1463291272324514652076512182039643227425959094690, 1461507212538490968058691248585538602689765616034, 1463291272494655835536986249493055733732251576738, 1462934460911761702346465011081683160587115211170, 265750982861125933825305742739544102540024293484295358204890294125245740939477616838592312529308364293, 1462934461592326436188361280895333185812285139362, 265750982861125933825305742739544102540024293484204441109680443055793214647269694141726809378010131973, 1462220839107102903649215073886238064747182352802, 1461507217983008838793861406504442994132419389858, 1462934476548789460166788375791392649062332274978, 1461685618542614513979544451517694711786493753762, 1461685618585149809844662968381047838363066874274, 1461507212538490968058691247995242792331059964322, 1461551814199029214033098987113429996857067613602, 1461507212538490968058691248585538602689765616034, 1461596415859567460007506726231617201383075260834, 1461507213219055701900587517808892817556229892514, 265750982861125933825305522915496415439063890617565637146416949597159808146614635896510863177726160389, 265750982861125933825305522915496415439063890617474720051207098527707283057684431387224003828608265733] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_9 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 0, true⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [566291475827168, 265750967021133945814517773568464530666496742662940248886507854080922021219222899457103929164610894596, 566291475827168, 562992907356640, 565191997721056, 1461507212517306397192781801918191387302161328546, 565191997721056, 566291542936032, 570689623132640, 565191997721056, 570689623132640, 1461507212517306397192781802508487197660866980258, 265755022059566274876716621663385448087262133305032859088043756427204080344156743127435565678177625796, 265767187173171368414397670881403584822713624736253827532836713088539900151207355390327631660891470596, 265783407324241994643148104120469639257280246251130636760098707173822550422352818381235603941926058052, 566291475827168, 265752994540112659873022111918986307452542489614309840265412751481786145770725390595071391814038813444, 566291475827168, 562992907356640, 565191997721056, 1461507212517389474259431009217305225617604651426, 565191997721056, 566291542936032, 570689623132640, 565191997721056, 570689623132640, 1461596415838465963672945287550623153888036956578, 265755022059566274876716621663385457683844759269047800028431079479698157867887944993408123439924717252, 265767187173171368414397671525419349531017338833380707494017835160151858142505310531565788568889817860, 265783407324241994643148021686452984957173157513736511490119556927293624107414446833038578106534934596, 265751030381584351914916309625397986000138655717580468170293981486010582110594850703102239298296192516, 1461607565913816658358099686864155114798748576162, 1461507212527857184657231128462926854856945740194, 1461975528252127709505053543079006956934571010978, 563233425459680, 1461507212517223360690951801922418256143732222370, 1461507212517223360690951801332122445785026570658, 1461507213208421918499127398129002927492439255458, 563233425459680, 1461507213888986652341023667942652952717609183650, 1461507217961741231426121959841322647586385996194, 265751220461485375638481996658728180522463332529214257615586377418443856197006335349482234471582746372, 1461507212559758615991251110892134724467097119138, 1461507212517223320126132594176355550480200411554, 1461507212602293911856369627755487851043670239650, 562958547552736, 565226357590496, 565226357590496, 562958547552736, 567356728412640, 562958547552736, 567356728412640, 1461507223406259061596472911047182001493242849698, 564332970674656, 1461507212522540252391681861319641202668573075874, 564332970674656, 563233425459680, 565432515889632, 1461507212522540252391681861762363060437602314658, 565432515889632, 563233425459680, 265755022059505850103042742681011790451870224938533693995104984565914827351783879573504872000735165188, 1461507223416892926127571445333753305869988178338] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_10 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 1, false⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [1461518373821466315246093086704165347308275276066, 1462934471109598855585015325825697728037594900898, 1461518373864001611428123044694144523611422103842, 1461507223406248758132394218219675054672113080610, 1461551824896988431109352811680183214430129008034, 575396806527456, 576565406730720, 575396806527456, 572029787048416, 578764094441952, 572029787048416, 578764094441952, 1461507212517223360690951801332123008737127475618, 576427699341792, 572029787048416, 576427699341792, 572029787048416, 572029787048416, 1461596426387717800622232712313183864414914259362, 568593578330592, 568593578330592, 562958547683808, 565226357524960, 265750967021617343999857886327026057808729483569403459597318100019222246475787315515029393655148542724, 565226357524960, 562958547683808, 567356728412640, 562958547683808, 567356728412640, 1461685630049730888896152333071745173685785368866, 1461507223406259061596472911047182564445343754658, 1461685630730295627808631660911411994536134613282, 573129063795168, 576427967777248, 573129063795168, 572029787048416, 574228608977376, 572029787048416, 574228608977376, 576427699341792, 572029787048416, 576427699341792, 572029787048416, 572029787048416, 1462934471109598886008629731303203363958471829922] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_11 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨2, 1, true⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [265750967021617344007061081472975607437101826465078963871271777173227749564493480357983539663717235460, 265751030381584351918517906769035468942593407633836023354480797543651323718617446287805389953449565700, 265750982861609095976828729237243167860127392807938095262509066246677692436338413917770040498009375684, 265751030381585296044808805741042836196977263975804017024604394264109060390643720668401784859727514052, 265751220461485375631335072174696432642099971412606365104705098432937557155520476382346119851344873220, 265751030381585296044808805741042836196977263975804017024604394264109060390643720668401784859727514052, 265751030381584351907825665248861691457180862876724566945880831063404404791647353049724069215423667716, 265751030381584351908163314981077705483035995869146276527995742968102763192670697417732753441094344196, 1978643212130353730713004565629822689175150736265365357355641534799008076777640250828008456267157694092994562510171718062197603488452737548905930951328629917034461455687640102, 1978643447772660923130655603006860760960038739568945692225293640362172553650706229957456807283242884376604656292945070623188459408626003688979832714622003649247364779879457830, 265750982861126169859575712059565139362517731098491870964476934619838908142396221183102453446504348325, 265750998701600847953792541212802958597881685921171364098278327766201490250271911635176965968309502084, 265751030381585296044808805741042912969638271687923544547702978684061680730903045886797140442526796228, 265750967021617343999857893196514445496360543311392786856010364197827931715661440021976157398704028420, 265751220461485375631335077326822550308529684189621404794154075005833220822687112736958435492411950852, 265750967021617343999857893196514445496360543311392786856010363879872441286422735361282684182582229764, 265751093741551359815680897694722501408908896998612523220610947422812605139887507989548016895893142276, 265751220461485375631729002014407900005360672680780065973288139531400105591063738930568040090497926916, 265751220461485375631729002014407900005360672680780065973288138900536037279082182064112736090256262916, 265750967021617343999857893196514445496360543311392786856010364520830334691395997137601273046827760388, 265750967021617343999864920696434122233325987323427903059134853759612697131624535455633639935696927492, 265751030381585296044808805741042836196977263975804017024604394264109060390643720668401784859727514052, 265751220461485375631335077326822550308530446857482254275866881054248140554156669173144937872605267716, 265750967021617343999857886286761970579971437377766271273290759600482083800465960700672353570123491012, 265750967021617343999970436237751626616405716383559687303545763736455006802217100350717538086985890564, 265750967021617344000308085969967640642260849375981396885660675641153365052830727704273113956702452484, 265752994540561597058428408969809996064162095662804941228978620234122557569294439463672538740909374212] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_12 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 0, false⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_13 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 0, true⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_14 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 1, false⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_0_15 : checkTree 3 ((baseTable 1 1 0).set 0 1 ⟨3, 1, true⟩) 103 ⟨0, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

private theorem solve_1_1_0 (N : Machine4) (h11 : N 3 1 = none)
    (hAlive : ∀ q a, ¬ (q = 3 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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
private theorem tv_1_1_1_0 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨0, 0, false⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [1461518373842650967241332670718212188722917579042, 1461864035350703280628626273852708133644209793442, 1461529524172725321281503238078615628654211804066, 1461518373842650967241332670718212188722917579042, 1461551824917923851904644773796888312200224091554, 1462934471120232750539419988329792580990660553122, 1461596426748592895478149201262619292268013590818, 564092452506080, 576565037894112, 564092452506080, 564092452506080, 565226323904992, 574297295096288, 565226323904992, 562958581107168, 567494066702816, 562958581107168, 567494066702816, 572029552298464, 572029552298464, 1461685630069669384891653807599084704252575127842, 1461507223427526790658361702360347448707826887074, 1461864035350703280628626273852705881844396108194, 572888545757664, 576565037763040, 572888545757664, 574022417123808, 574297295030752, 574022417123808, 572029552298464, 576290159856096, 572029552298464, 576290159856096, 572029552298464, 572029552298464, 1463380475156518265401789318526155528759944456610, 265751093741069849903969409990087898427690879739495014491428539512574301404997596058565861145064888133, 1463380475199136638333555833758191193004358805922, 265751093741069849903969409560744055288821816452282264629565223936928529221960920713428550654356690757, 1463291272303579261704522721349171928046626711970, 1463291272474052791461106789124196629925380270498, 1463291272474052753431588782277314585024284109218, 1461507212517223320126133802959217402137753463202, 1462934460891823246915456332641237525193355733410, 1461507212517223320126133802959217402137753463202, 1462934461573717213823720576353808153103985322402, 1462220839091152167699719920794224661352758176162, 1461507217972375055392247752659782425422790175138, 1462934476564740236680718296309598360974111316258, 1461507212559841693057900318191253066382167812514, 265751093741069849903969409990087898427690879738404009365165585038731235940638913180845940803209238341, 265751093741069849903969409560744055288821816451554927878723254287699818110203308051198781588472829765, 1461518363060296077164770631746496383296230959522, 1461518363230769606921354699521521085174984518050, 1461518363230769568891836692674639040273888356770, 1461507212517223320126133802959217402137753463202, 1461685619160705532019530332417969216941504641442, 1461507212517223320126133802959217402137753463202, 1461864025804187743912926861876721031745255811490] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_1 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨0, 0, true⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [265751093741551359822772414497948054134094627836748524500318090669589733398622748181432153926186269444, 1978643211900009344325130447387260592234061569810792723141069077064811340884380038433381240822193995156379270470644010262427762808077107679454376881553276854600574942890058790, 265751220461485375638482869085417438704691270526505722307781601627558100615765338021528230185634580228, 265750967021617344007061959910478669563497985146991326692854579711621366186180461998037737302861773572, 564092553202144, 567494167300576, 564092553202144, 567494167300576, 565226424568288, 572029652765152, 565226424568288, 562958681836000, 567494167300576, 562958681836000, 567494167300576, 572029652765152, 572029652765152, 265750967021617344007061959910478669563497985146991326692854579711621366186180533718979764610900654852, 564092553202144, 567494167300576, 564092553202144, 567494167300576, 565226424568288, 572029652765152, 565226424568288, 562958681836000, 567494167300576, 562958681836000, 567494167300576, 572029652765152, 572029652765152, 265751101661063955635396893230092416501977666544201180655213987767192470472184508373901288339089357572, 1461507212517223330267337396002190762453826054562, 1978643211900008465631029899528732320297565556290085110114520066835138891321241795594398631725281546055071582416862203129269257216830545286428921343182967765915052443654054950, 1461507212517223320126132594176355550480200411554, 565226424568288, 265750967021133945817669170854481957938847786538877207160705867390919676934525946451946720670461950724, 565226424568288, 562958681770464, 562958681770464, 265750967021375644910564766810658296646327829595155366882273921667513906967261069088013898186499521284, 1461518380286831286744108857199453094230516341026, 1461507212517223330267337396002193014253639739810, 265815839707354521521129159807065729490616919972539922936726979509887769168328923865005119891762599940, 1461507212517223320126132594176355550480200411554, 265750967021133945817669170854481957938847786538877207160705867390919676934525946451945651945159752452, 562958681770464, 1461685630049730888896326417430540958803579410722, 562958681770464, 265750967021375644910564766810658296646327829595155366882273921667513906967261069088013898186499521284, 265751093741069849903969409560429600870179786292657877624039501709999597855428835549241177066720765797, 265751093741071738178132652646986926496506570912310952072459199739061328329714014582080581291978272421, 265783407324241994643148021686452984956977914541631795453206450323370036470951290008287511384833603652, 1462231986778793938310000229178073027006935656866, 567494167497184, 1462243137194011576553338721195064630061277703074, 569624538384864, 480481492307716881405653747714549340034089738956234003689237449950291080909569019071116419729812165483248959730395010937826192802623451847309049485272032691502849233852584883688628629200771075971804951194237037240755359605325707009680191284558601147169903108123098760, 569624538384864, 562958682032608, 567494167497184, 562958682032608, 567494167497184, 567494167497184, 569624538384864, 265750967021133945817669170854481957938847786538877207160705867390919681747636890914445653698342517508, 569624538384864, 562958682032608, 567494167497184, 562958682032608, 567494167497184] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_2 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨0, 1, false⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [1461518373842650967241332670722823874741344966946, 1462934471120232750539421197260225992694145526178, 1461518373885186263106449978655745700670383102242, 1461507223427526790658362911290774245755935828386, 1461551824917923851904645982727319612847826185634, 1461596426408320913150929054163864979947903822242, 1461596426408320913150929054163864979939850758562, 1461507223427516406064644594930765707056547666210, 1461685630069669384891653807603696390271002515746, 566291475827168, 576565037894112, 566291475827168, 1461596415583254188482234185226806261858606033314, 569624370547168, 578695341738464, 569624370547168, 562958581107168, 576290159987168, 562958581107168, 576290159987168, 572029552298464, 572029552298464, 1461685630750234118733530734530445605135612680482, 1978643219271028827039652706902412209779451533085721703405134973709019057423584697655194029647123020120437438514849629572033320990970471989501575178349555288632287168823966503, 1461507223533937641981361307512559764779589212450, 1461529513432895342476342608536059539726443522978, 265750998701600847953841781798751127310082418300874192808619298975875359796763501670264087666981585028, 1461518374374674393959908034702349757840201128226, 1461507212517223320126135011889644199202908055970, 1461685630049730888895844055816375194581784893730, 1461507212517223320126135011889644199202908055970, 1461685631410860361650200310582791230296744302882, 572888545757664, 576565037763040, 572888545757664, 574022417123808, 574297295030752, 574022417123808, 572029552298464, 576290159856096, 572029552298464, 576290159856096, 572029552298464, 572029552298464, 1462934471120232750539421197260225992700587977122] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_3 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨0, 1, true⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [1461518373842650967241332670718212188722917579042, 1461529524172725321281504447009046929301813898146, 1461507223427516406064643385995722720373338315042, 1461507223427516406064643385995722790742350928162, 1461507223427516406064643385995722790742619363618, 564092452506080, 1461507212517223330267337395854616809864149641634, 564092452506080, 562958547552736, 565226290350560, 1461507212517223360690951801332122445785026570658, 565226290350560, 562958547552736, 567494167366112, 562958547552736, 567494167366112, 568490499115488, 1462934465665080984849729109995092382590383991202, 568490499115488, 562958547683808, 565226357524960, 565226357524960, 562958547683808, 567494167366112, 562958547683808, 567494167366112, 566291542936032, 566291542936032, 562958547552736, 565226357590496, 1461507212517223360690951801332122445785026570658, 565226357590496, 562958547552736, 562958547552736, 1461507217972375055392246543729346621175560710562, 568490499115488, 568490499115488, 562958547683808, 565226357524960, 1461507212517223360690951801332123008737127475618, 565226357524960, 562958547683808, 567494167366112, 562958547683808, 567494167366112, 265751093741069849903969409560377190733077873547749787659325430167609842761565831439892172510459897701, 265751220461005753993843107234456311067884185503205463109997870330398532568804316047504691350892198085, 265751220461003865719680825556137805394395776695895803525844755861122159071853092050235218856463317861] = some [] := by
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
private theorem tv_1_1_1_7 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨1, 1, true⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [564092452506080, 1462053582858889510256839645295693117668184881442, 564092452506080, 564092452506080, 566291542903264, 566291542903264, 564092452506080, 568490633333216, 566291542936032, 568490633333216, 265750998701117449768002221914964377800614300145497441068601268538551740679134065149803583114033414276, 1461507212559841693057899109265433451752993106338, 569761977108960, 569761977108960, 1461507212517223330267337395854616809864149641634, 567494167300576, 567494167497184, 567494167300576, 1461507212517223330267337395854616809864149641634, 1461507212517223330267337395854619061663963326882, 567494167497184, 265751093741071738178132653076317667119257847954999922775332780725952815333161711977596812590361442981, 567494167497184, 265751220461005753993843107663787051683606715528678255177543582456324906993291361377276687546813187269, 564092452506080, 265750967021133945814074608938946776965865594707510793864647386946506740330793986622902141887335070468, 564092452506080, 564092452506080, 566291542903264, 265750967021133945814074608938946776965865594707510793864647386946506740330793916022601820917093071620, 566291542903264, 564092452506080, 568490633333216, 566291542936032, 568490633333216, 1461507212602460065989665624502076298433387342242, 564092452506080, 564092452506080, 562958547552736, 562958547618272, 562958547618272, 562958547552736, 562958547683808, 562958547552736, 562958547683808, 265751093741071738178132653076317673516979614486590317766459351378036216884882632037980130331112340133, 265751093741071738178132653076317673516979614486590317766460674395878805493628613498924571518612372133, 565226357918176, 1461507212517223360690951801332126949401833810338, 565226357918176, 562958548077024, 567494167759328, 562958548077024, 567494167759328] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_8 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨2, 0, false⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [564092553660896, 1461864035350703209640210795028332848407754353058, 564092553660896, 1461685629389114959584476108369234055528893692322, 565226425027040, 572029653223904, 565226425027040, 562958682294752, 567494167759328, 562958682294752, 567494167759328, 572029653223904, 572029653223904] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_9 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨2, 0, true⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [1461596415540635815550474923577362764378586261922, 1978643219271029705733753305714120317171405055193670200084933032391912399116403362351036040508604841401616710267589771200739809398459480942846996605681291239677559747935495206, 265815340747613980203984241857734784005224808695652499836240452839839941563275664464753626220494796868, 1978643219271029707020902863741991146236160305256002681222160206639761365127109408658048673737920202916834936842652535404078915370745252894810135273642602497095445313282008102, 480481077057593903270577991264115677705841762477734585907303639110016901315349039182504342291868288163252795003890770827776834169569383898808307526963700635859897176032475942724974743652984330425316393425071860574291294976264376609154002020819097363786498048201738761, 265751093741071738178132653076317667150496724094068784823967350916293387924971391472405691396750834341, 265811285709725474105637918806275621294573924274482359170999370593789664695159593820175728529090230340, 265815340747613980202183443285912766900477373934062333450973325153193052598286681438706073742023538756, 265751093741069849903969409996377114786203782382735641654288979035242851152672820596950866632495870277, 265751093741071738178132653076317667150496724094068870835624226658562173962554048998479306905901431461, 265786955482394437483040846308615182950898031378976687098528469682911773116361984447033289934318549060, 265751220461005753993843107663787051721093366783814792792410312575018236375942031625704671880400012485, 1461596415583254188482241438809398428623000611234, 1978651003068531353252845655897003240255257933743224784846005047342022177384718309162299465738872551543239512867792429583484170889978785182953982539508755010011879108883670054, 1978643219271030525406683291589159029952064349900383004799592386853872126196896018670350177987154181801522220652665085774714813546090120715089111410900761124277560830994310182, 562958547552736, 562958547618272, 562958547618272, 562958547552736, 562958547683808, 562958547552736, 562958547683808, 265751093741071738178132653076317673548218490625659265826750799894664837825038981683872113659521890981, 265751093741071738178132653076317673548218490625659265826752122912507426433784963144816554847021922981, 569624538647008, 1461507212517223360690951801332126949401833810338, 569624538647008, 562958548077024, 562958548077024, 1461507217972375055392246543729351124792367950242] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_10 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨2, 1, false⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [564092553660896, 569761910000096, 576565138557408, 569761910000096, 265750967021375644910564327162569473711361722666932721088578803098029782680566110133179328872915892996, 567494167300576, 567494167497184, 567494167300576, 576565138557408, 576565138295264, 576565138557408, 576565138295264, 567494167497184, 567494167497184, 564092553660896, 568628038633952, 1978643211900009344325130447387260592234038856100658485425739410695814836473168072372568629663498079996219891940093173245198324078563214684869978953766705647229884448407184422, 568628038633952, 567494167366112, 567494167300576, 567494167300576, 567494167366112, 567494167366112, 265786955482394437483153396219353854292849742370813730419360952693930081859979870055694662741738600516, 567494167366112, 565226425027040, 572029653223904, 565226425027040, 562958682294752, 567494167759328, 562958682294752, 567494167759328, 572029653223904, 572029653223904] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_11 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨2, 1, true⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [265750974941613338005476751218547078782097165702520989492204964579440261825707294927886626326964938436, 265750974941613219988341548545757005119268894182248047702819567520351299905977321293616849401372965636, 265750998701601320022335103962241930419888536730509056870540222365095320780162107742594123578805896004, 265750967021617343999859645134040168583606604013957098939239722887944526997596624933644767786221927172, 265751093741553248089761480567600170012182038905129151491542436973313837728909628132368605406824310468, 265750974941613338005476751218547078782097165702520989492204964579440261825707438369768543492438304452, 265750974941613338005476751218547078782097165702565737750003563167590590279845259426873570383584110276, 265750974941613338005476751218547078782097165702611196297608488717457590463797925770150175618946115268, 265751093741551359815596481826917752791503666139696761418379261778837446023723598801434485904962190084, 265750967021617343999914168151883781167347838828019751405257837027304315825925201100893684386424388356, 265750967021617343999857886327012955274466208071859375816912357182136525645000105169855621483147262724, 265751980781089470525766650326251335410765872614558460628647593955743888674788054222486536857667676932, 265752994540561597051675414325489715547065537157257545440382830729351251742178432528730729321174629124, 265751093741071738178132653076317667250461126696124884747058484199713646746562858344369654110143904421, 265750967021617343999857886327012955274466208071859375816912357182136526848277841285480755512105728772, 265751093741071738178132653076317667250461126696124970758715359941982432784145515869348894909843471013, 265751220461005753993843107663787051771075568457330176278899337746994588434756511112049577589179090117, 265750974941613219988346824966838645046726594732198262106188879008105836152472108832982062629815286532, 1978643211900009344325130447387260589257452573201742739073888905951766066950121964718635419208066400313701209277528296488959227651878912769262446321465262447381579365004239910, 265750998701600847953792535201989154653713465236527736695088287312724905011414839509605225033981476996, 265750967021617343999864921555121808511064304564088437243222409573232813199491198607441008147200965380, 265751220461485375631285830730060577652257589943602832858149431489169547694880325824754743241443067652, 265750982861609095976828728378555481582388884900352124937147620059634122620530857291175449289479914436, 265751220461485375631285830730060577652257589943602832858149431489169547694880325824756889041463887620, 265750998701600847953792535201989154653713465236706729726282681625581782524311859422966251356788605060, 265750967021617343999864921555121808511064304564088437243222409573232813199491198607443145597805361924, 265750974941613219988341548545757005119268894182066923802206192322817549950577535159185822268836248324, 265750998701600847953792535201989154653713560570010342880302388068776769977848534064128537831505641604, 265750967021617343999857886327012955274454005386085784109507460407497809941487202190871583400054192900, 265750967021617343999857886327012955274454005386085784109507460407497810016692060698098145927447673604, 265751220461005753993843108093130894909944727077661689152675069080243568119361852239400763408685204677, 265750967021617343999857886327012955274454005386085784109507460407497810091896919205324725153674001156, 265750967021617343999857886327012955274454005386085784109507460407497810543126070248684083619202038532, 265751093741071738178132653076317673648182893227715365749841935762104281947619349779742612822991665829, 265751220461005753993843108093130894909944727077661863950557094855939722151135769021698958427906573509, 265750967021617343999914168151883781167336398810107009179227053733377845631741062448428053608896101124, 265752994540561597051675414325489715547059435814370749586680382342031903441439011457013219983902341892] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_12 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨3, 0, false⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_13 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨3, 0, true⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_14 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨3, 1, false⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_1_15 : checkTree 3 ((baseTable 1 1 1).set 1 1 ⟨3, 1, true⟩) 103 ⟨1, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

private theorem solve_1_1_1 (N : Machine4) (h11 : N 3 1 = none)
    (hAlive : ∀ q a, ¬ (q = 3 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_0 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨0, 0, false⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [1461518373821466315246093086704165083423404235042, 1461864035329518628633386689838661028344696449442, 1461529524151540669286263654064568523354698460066, 1461518373821466315245784809444183418284870244642, 1461507223406342138662812632303456826612226501026, 1461529524151540669285956585735018123679394474914, 1461507223406331754069095524721693949935290980642, 1461551824896739199909100539314153443704983039394, 1461507223406342138662812632746178684381255739810, 1461596426387136261155388446472424013387415988642, 1461518373821466315245784809444183418284870244642, 1461685630048484732896124080281525179645768538402, 1461596426387136261155388446472424013387415988642, 1461864035329518628633115889422047449074199734690, 1461507223406342138662812633336474494739961391522, 1462934471099048098544025661220543355660218182050, 1461551824896739199909405189782841206900710747554, 1462934471099048098544180404315749838553286224290, 1461596426727408243482909617248572186968500246818, 1461518373778941403974692886205436667589133642146, 1461685630048484732896414223585037598953061783842, 1461507223406342138663122118346295980546174527906, 1461864035329518628633386689838658776544882764194, 1462934476543555584685478712295551255674597972258] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_1 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨0, 0, true⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [1461607576760317073539398804281714387077504739746, 1461596426387717808227836499046277631872223717794, 1461618727132916338850970781071282011905859824546, 1461607576760317073539398804281714387077504739746, 1461641027878114869474114734650417261562569993634, 1463380486003600258079352785081949699229684378018, 1461596426387717808227836498935597167429966408098, 1461596426387717808227826827529040250396568758690, 1461774832349306053212978456125228759502831008162, 1463380486003600258079343113859860222933382244770, 1461953238310894298198130084758310756756512352674, 1461596426387717808227836500079295299999958608290, 1463023674080423768109039856556802740278600444322, 265815340747621533298836416920543777401891162575442522747176074427069114028492418627162159524488624196, 1461607576760317073539398804281714404669757893026, 1461596426387717808227836499046277649464476871074, 1461618727132916338850970781071282029498112977826, 1461618727132916338850970781071282029498112977826, 1461641027878114869474114734650417279154823146914, 1463380486003600258079352785081949716821937531298, 1461596426387717808227836498935597185022219561378, 1461596426387717808227826827529040267988821911970, 1461774832349306053212978456125228777095084161442, 1463380486003600258079343113859860240525635398050, 1461953238310894298198130084758310774348765505954, 1461596426387717808227836500079295317592211761570, 1463023674080423768109039856556802757870853597602, 1461607576760317073539398804281714387077504739746, 1461507223406259071737368226830178200270408821154, 1461618727132916338850970781071281994313740888994, 1461507223406259071737368226682604247680732408226, 1461864035332094017699207465642499508544809773474, 1461507223406259071737368227272900058039438059938, 1461864035332094017699212301364224781504230762914, 1461507223406259071737368226682604247680732408226, 1978643211900009344325130396240532343856822137101245186411927325393411403509187185413167865115674272577909192399138327574367413755547592898370283620332189442863930851971589158, 1461507223406259071737368227863195868398143711650, 1461864035332094017699512116111187271740537481634, 1461864035332094017699203838851205676979069168034, 1461507223406259071737368226830180452078812440994, 1461864035332094017699205047781636977626671262114, 1461507223406259071737368227272900058048027994530, 1461507223406259071737368226682604247689322342818, 1461507223406259071737387569569507309850769533346, 1461507223406259071737522969187514920223684733346, 1461507223406259071737406912456408120212403038626, 1461507223406259071737522969777810730582390385058, 1461864035332094017699512116111187342109550094754, 1461507223406259071737369435613035548328334502306, 1461507223406259071737368226830178200270408821154, 1461507223406259071737370644543466848975936596386, 1461507223406259071737368226682604247680732408226, 1978643329836334268763387797993092153471100323758076164244412208086574143186675989277104268692484599531557526773349037524775356154296343591795321211011407820065309158976219943, 1978643447772660936860250874518854832157715002499968327317517778573018763077171775324621353061976295480459115044521426959388185768558344749302373004889367547235657675789067302, 1461507223406259071737368226682604247680732408226, 265751980780621178533282257877106503731585806589108769691304134997658108613640318311675369313089292133, 1461507223406259071737406912456405868403999418786, 1461507223406259071737677712873019465266682177954, 265751980780621178533282257877106503731585806591927209352448194705124930142323646959981609831537616741, 1461507223406259071737677712873019465275272112546] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_2 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨0, 1, false⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [1461518373821466315563005736761222433797580036386, 1462934471099131175610829611614861425062473410978, 1461518373864001611428123044694144259726618171682, 1461518373821466315562697459501240768659046045986, 1461507223406425215729461839602570664927669823906, 1461507223406425215729464257315859313633331816866, 1461507223406331754386008174778751300309466781986, 1461551824896822276975749746613267282020426362274, 1461507223406425215729461840045292522696699062690, 1461596426387219338222037653771537851702859311522, 1461507223406425215729461839464220084374848186786, 1461529524151623746352622718060170206246578727842, 1461596426387219338222037653771537851702859311522, 1461529524151623746352642060947071016609285974946, 1461507223406425215729461840635588333055404714402, 1461551824896822276976054397081955045216154070434, 1461596434894185049902037113166638520948208212258, 1462934471099131175610674868076933084406818580898, 1461596426387219338222030400188950047825299810722, 1461864035329601705699731246669084851671040829858, 1461507223406425215729461840045292522705288997282, 1461685638895826273157422273239593723445151570210, 265750967021137722369597255674114443325849981526346486284876637360247784397619628790268039088429038340, 1462934479265814520369608926756094435982618695970, 1463291283022307665580794369061238075998608599458, 1462934471099131175610558811198250080006046788002, 1461507231573108560488608669742493025327855474978, 1461596426387219338222337468518500412308178643362, 1461529524151623746352604584103700696531607792546, 1978643211900008465631029899528732323274151841961669228636638391088489460632991577949137918093054284249584627063255048630853157652370787149141637951244532948222629763238224934, 1461507223533937641981361307512559764762610669858, 1461507223406425215729461839454996712338127628706, 1461551824896822276975749746613267282020292144546, 265750967021617344007061081472975607437101826462169616824556542304742140767257965271433590997920217860, 1461596426387219338222037653771537851702456658338, 1461507223406425215729461839464220084374982404514, 1461529524151623746352622718060170206245639203746, 1461596426387219338222037653771537851702456658338, 1461518373906536907292950209397340906525991934242, 1461685630048484733213326873642094949327237585186, 1461596426387219338222337468518500412308178643362, 1461685630729049467055203800568844164191847749922, 1461507223406331754386317660969164266112782735650, 1462934471099131175610829611614861425068915861922] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_3 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨0, 1, true⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [265750974941613219995542984240676679264655597841697362709122095591123377475972200165043419305779362564, 265750998701600847960988695119842953579946134776410283297176594704651604223004814700018473625198248068, 1461518373821466315245784809444183418284870244642, 1461507223406259061596163425004342988296783178146, 1461507223406259062229991142831746337750796773794, 1461507223406248677002446317422580111619847657762, 1461551824896988431109048161211494958651313008034, 1461507223406259061596163425447064846065812416930, 1461596426387717800621932897566220881595519248802, 1461507223406248677002446317422580111619847657762, 1461685630049730888895862189768233018260209047842, 1461507223406259061596163424856769035707106765218, 1461507223406259071737406912456405868406146902434, 1461507223406259061596163426037360656424518068642, 1461551824896739199909096912522859541762176757154, 1461864035332094017699241315694575926677668407714, 1461551824896822276975747328752404680725222174114, 1461507223406248677002446317422580181988860270882, 1461551824896988431109048161211494958651313008034, 1461596426387717800621932897566220811226506635682, 1461507223406248677002446317422580181988860270882, 1461685630049730888895862189768232807153171208482, 1461507223406259061596163424856769106076119378338, 1461864035332094017699241315694575926677668407714, 1978644184874696993628760277409663786314211807006501194360658863595599270734569786095870597245664015707545680688603795284500516996053572226457289164305491882338739718300721446, 1978643219271029707020902765044788982412705580072580635929839160651974077129694481441293826519282925067215892389227624288803776883944206875542521418615557782540792374250595366, 265783724124078922456587411868048564422060980397875922987217153170997464664403815448472674239231768644, 265751980780621178533282257877054087195981250756673940127924565549844137067761052290014518648984489477, 1461596426727408243482601339988590521829966256418, 1461864035332094017699241315694575997046681020834, 1461596426387219338222030400188950047817246747042, 1461507223406248677002446317422580181989128706338, 1461551824896988431109048161211495029020325621154, 1461507223406259061596163425447064986803837643170, 1461596426387717800621932897566220881595519248802, 1461507223406248677002446317422580181989128706338, 1461685630049730888895862189768232807153439643938, 1461507223406259061596163424856769176445131991458, 1461864035332094017699241315694575997046681020834, 1461507223406259061596163426037360797162543294882, 1461518373821466315245784809444183418284870244642, 1461507223406259061596163425004342988296783178146, 1461507223406259062229991142831746337750662556066, 1461507223406248677002446317422580111619847657762, 1461551824896988431109048161211494958651313008034, 1461596426387717800621932897566220881595519248802, 1461507223406248677002446317422580111619847657762, 1461685630049730888895862189768233018260209047842, 1461507223406259061596163424856769035707106765218, 1461507223406259071737406912456405868403999418786, 1461685630048484732896105946325055933814527793442, 1461685630048650887029404360927895296463841827106, 1461507223406248677002446317422580393095898110242, 1461551824896988431109048161211495169758350847394, 1461507223406259061596163425447065127541862869410, 1461596426387717800621932897566221022333544475042, 1461507223406248677002446317422580393095898110242, 1461685630049730888895862189768233018260209047842, 1461507223406259061596163424856769317183157217698, 1461864035332094017699241315694576137784706247074, 1461507223406259061596163426037360937900568521122, 1461507223406342138662813841086314315407640537506, 1461507223406259061596163425004342988296783178146, 1461596426387219338222030400188950047817246747042, 1461507223406259061596163424856769035707106765218, 1461551824896988431109048161211495451232522251682, 1461507223406259061596163425447064846065812416930, 1461596426387717800621932897566221303807984314786, 1461507223406259061596163424856769035707106765218, 1461507223406259061596163424856769035707106765218, 1461507223406259061596163426037360656424518068642, 265750967021617344007061080614287921159558752196793055846437262553280635828600196711197567737228655364, 265783724124078922456587411868048564422060980397875922987217153170997466563326462778832929424471701572, 1461685629389104574990759000935040909316983920930, 265751980780636284726588205253593112380799252163041305793625442923980508855042750484789873962554271781, 265786448602665927316851987854375706353573635854752353842388254766966558246790969002200013912502646852, 265752994540108411252271842382692025685938813880330322758227229471338229691445874867084053952089600581] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_4 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨1, 0, false⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [1461518373821715546445732431341529419255754299682, 1461864035329767859833334310702986564028184177058, 1461529524151789900485904207632364142242397465506, 1461518373821715546445732431341524933231200213282, 1978643329836334248168994817601263008525420638664415946175568185642469592970175690571133158811707156167807654980981683335103490893442364151952063550774200986998886464204978983, 1461529524151789900485904207632359673810096532386, 1461507223406580985269043146619035464881620949282, 1461507223406580985269043146619035535250633562402, 1461507223406580985269043146619035535250901997858, 1461507223406580985269043146619035464881889384738, 1461551824896988431109048161211495169758350847394, 1461551824896988431109048161211495451232522251682, 1461551824896988431109048161211495451234401299874, 1461551824896988431109048161211499391899107634594, 1462934471099297329743973283117884870615138085282, 1461596426727657474682552588695677116040338250018, 1461551824896988431109048161211499391899107634594, 1461685630048733964096071702178871180615645960482, 1461507223406591369862798939679456560719277894050, 1461864035329767859833063511319392887093049993634, 1462934476543804815885194219845234329168989165858] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_5 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨1, 0, true⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [265750974941613219995542987460755502806076308504527876635844371632172448929038151144136351845562153732, 1978643447772660909401060283544808962892058180985533286876091517782920553137189214438018750431765161638193746077377919565599086871457850569851566270596199227158128152940143654, 1978643211900009344325130447387260592234038856100657163313801791720095259625709444768627902248225273217811285820564407480161301681343434229969050322858523627626924828846351398, 1978643447772660923130655603006860763928448089592204233228732128292111783820500342936924846611455084598760365877873943486262049828039948051271622692807253680421268651711947814, 265751980780636284726588208259000007959066455491056891513897107066100985905341787867712746901734467621, 1978643211900009344325130447387260592234038856100657163313801791720095259625709444768627902248225273217369574054369811397765477306157704601012174278037218242656706360498873382, 265750998701600847960988701130656757524016066637580427857138828969408036307228040980194163007692456068, 265750974941613219995542987460755502806076308504527876635844371632172439305166414047486109953794734852, 265751980780621178533282260883247192407148727413997988457414925455445897072542815801676229418190677861, 265750998701600847960988701130656757524016066637580427857138828969723458724562750147029638743949033604, 265750967021617344007061080614287921159461130707694975140482853164682897825887889177457916737192426244, 265750967021617344007061080614287921159461130707694975140482853164682897844689103804264559456394902276, 265750967021617344007061080614287921159461130707694975140482853164682897901092747684684479264585906948, 265750967021617344007061080614287921159461130707694975140482853164682897825887889177457916737192426244, 265750967021617344007061080614287921159461130709149648663840470760426903862782714013938481548884146948, 265750967021617344007061080614287921159461130707694975140482853164682898427526757235270416956340271876, 265751980781089470532744744792048958611857373255451935882592097702287290047675980018251528908356889348, 265750967021617344007061080614287921159461130707694975140482853487685310427844335218084104616983886596, 265752994540561597058428408969809996064253615803220261261602573624834966415982420611437836874491853572, 265750967021617344007061080614287921159461130707694975140482853164682907452109778102458988968860154628] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_6 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨1, 1, false⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [1461518373821715547713383031569758820752457505058, 1461596428769351677475838805628789063504310081826, 1462934471099629638010570111871616114293036067234, 1461596426387717800621932897676901240484257638818, 1461507223406923678129357083397253694820329761186, 1461864035330100168099660340515843807107028658594, 1461507223406923678129357083397255946628733381026, 1461685631409863433047476156408168531181572233506, 1461864035330100168099660340515843877476041271714, 1462934478585499018678552972327523418267240667426, 1462934471099629638010570111871614425449618254242, 1462934471099629638010570111871614425443175803298, 1461507225448275188062324529029466186479356123426, 1461518373864250843578500339507292332699855919394, 1461518373821715547713383031569754334727903418658, 1978643211900009344325130396340428297466933932911494370251233953057185649838208807914988356201064706041264354748957199139482564686265183589199692880285875539625711443062449190, 1461518373906786139443617647444821358622767356194, 1461507223406580986536693746847264866378324154658, 1461507223406580986536693746847264936747336767778, 1461507223406580986536693746847264936747605203234, 1461507223406580986536693746847264866379129461026, 1461596426727657475950208024627180753912983492898, 1461596426387717800621932897566221303807984314786, 1461596426387717800621932897566221303809594927522, 1461551824897320739375644990407954745160880926114, 1461507223406923678129357083839980056206166239650, 1461596426387717800621932897566225244474301262242, 1461507223406923678129357083286577733994879691170, 1461685630048733965363722302407100582112349165858, 1461685631409863433047476157588764585146509728034, 1461685630729298699205599229407636773270723795234, 1461507223406580986536693748027860990712542697762, 1462934471099629638010570112314340223876911376802] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_7 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨1, 1, true⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [1461518373821466315245784809444183418284870244642, 1461864035332094017699203838851208350984905468322, 1461518373821549392312434016743297256600380676386, 1461518373821466315245784809444183418284870244642, 1461518373821715546445732431341524986007959673122, 1461518373822047854712329260537980339270001400098, 1461507223406248677002447526353011412267449751842, 1461685630049730888895844055811763508546177636642, 1461507223406259061596164633787200336354708859298, 1461864035332094017699203838851206099185091783074, 1461596426727989782949154253816767370678770899234, 1461596426387717800621932897676901240484257638818, 1461507223406259061596163425004342988296783178146, 1461507223406248677002485003270168779006965487906, 1461507223406259061596163425004345240105186797986, 1461507223406248677002465660457054944940438624546, 1461507223406248677002446317643941040504362277154, 1461507223406259061596163425004342988296783178146, 1461507223406259061596163425004345240105186797986, 1461518373821466315245784809448795104303297632546, 1978643211900009344325130447387260592234038856100657163313801791720095258505837073679757625656636211951673230436446161913455912751626888747857275034406605529053854522804167718, 1461529524151623746352605793034131997179209886626, 1461507223406259061596165842717631637002445171106, 1461529524151789900485904207632359708994602838946, 1461529524152122208752501036828815132633441807266, 1461529524152122208752501036828815132625388743586, 1461507223406248677002447526357623098285877139746, 1461685630049730888895844055816375194564605024546, 1461507223406259061596165842717631637002310953378, 1461864035332094017699205047781637399832693877154, 1461507223406259061596165842717631637019490822562, 1461518373821466315245784809444183418284870244642, 265751980780621178533282260882827860128560055869870958292566648159294822987214270225009387450250864485, 1461529524151623746352605793034131997179209886626, 1461507223406248677002446317422580111619847657762, 1461507223406248677002446317422580181988860270882, 1461507223406248677002446317422580181989128706338, 1461507223406248677002446317422580111619847657762, 1461507223406248677002446317422580393095898110242, 1461507223406259061596163424856769035707106765218, 1461507223406248677002446317422580393096971852066, 1461551824896988431109048161211499391899107634594, 1461596426387717800621932897566225244474301262242, 1461507223406248677002446317422584615236654897442, 1461507223406248677002465660309485425598288402722, 1461507223406259061596163424856773539323914004898, 1461507223406248677002465660383272401893126609186] = some [] := by
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
private theorem tv_1_1_2_11 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨2, 1, true⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_12 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨3, 0, false⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_13 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨3, 0, true⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_14 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨3, 1, false⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_1_1_2_15 : checkTree 3 ((baseTable 1 1 2).set 2 1 ⟨3, 1, true⟩) 103 ⟨2, [1, 1], 1, [1]⟩ 4 [] = some [] := by
  decide +kernel

private theorem solve_1_1_2 (N : Machine4) (h11 : N 3 1 = none)
    (hAlive : ∀ q a, ¬ (q = 3 ∧ a = 1) → ∃ q' w d, N q a = some (some q', Stmt.write w d))
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

set_option maxHeartbeats 0 in
private theorem tv_1_1_3 : checkTree 4 (baseTable 1 1 3) 107 startPos 0 [] = some [] := by
  decide +kernel

end OMA.BB4HoleS3A1

open Turing Turing.BusyBeaver OMA.BB4HoleS3A1 in
theorem OMA.solution :
    OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1_H1_R1_H4_R1.H2 := by
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
  · exact solve_1_0_1 N h11 hAlive h107 hm
  · exact solve_1_0_2 N h11 hAlive h107 hm
  · exact checkTree_sound tv_1_0_3 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
  · exact solve_1_1_0 N h11 hAlive h107 hm
  · exact solve_1_1_1 N h11 hAlive h107 hm
  · exact solve_1_1_2 N h11 hAlive h107 hm
  · exact checkTree_sound tv_1_1_3 N h11 hAlive h107 hm (Nat.zero_add 107) rfl
