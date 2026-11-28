import FormalConjectures.Wikipedia.BusyBeaver

-- Problem: Busy Beaver — BB 2
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/BusyBeaver.lean:79 (declaration BusyBeaver.BB_2)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
--
-- Strategy. Every candidate is conjugate to a machine on Bool states and Bool symbols, and such a
-- machine is given by four table entries, each one of 13 codes. For each of the 13^4 tables the kernel
-- checks that either the machine halts within 7 steps, or a small abstract interpretation of the tape
-- (first cell of each side, plus whether the rest is blank or unknown) has a closed set of reachable
-- abstract configurations with no halting transition, so the machine never halts.

open Turing Turing.BusyBeaver

namespace OMA.BB2

/-! ### Table codes -/

abbrev Code := Option (Option Bool × Bool × Bool)

def dirOf (b : Bool) : Dir := match b with
  | true => Dir.right
  | false => Dir.left

def dirCode (d : Dir) : Bool := match d with
  | Dir.right => true
  | Dir.left => false

def dec (e : Code) : Option (Option Bool × Stmt Bool) :=
  e.map fun x => (x.1, ⟨x.2.1, dirOf x.2.2⟩)

def enc (x : Option (Option Bool × Stmt Bool)) : Code :=
  x.map fun p => (p.1, p.2.symbol, dirCode p.2.dir)

lemma dec_enc (x : Option (Option Bool × Stmt Bool)) : dec (enc x) = x := by
  rcases x with _ | ⟨q, ⟨a, d⟩⟩
  · rfl
  · cases d <;> rfl

abbrev Table := Code × Code × Code × Code

def entry (e : Table) (q a : Bool) : Code := match q, a with
  | false, false => e.1
  | false, true => e.2.1
  | true, false => e.2.2.1
  | true, true => e.2.2.2

def mkM (e : Table) : Machine Bool Bool := fun q a => dec (entry e q a)

def tableOf (M : Machine Bool Bool) : Table :=
  (enc (M false false), enc (M false true), enc (M true false), enc (M true true))

lemma mkM_tableOf (M : Machine Bool Bool) : mkM (tableOf M) = M := by
  funext q a
  cases q <;> cases a <;> simp [mkM, tableOf, entry, dec_enc]

def init0 : Cfg Bool Bool := Machine.init []

/-! ### Abstract interpretation -/

/-- `none`: nothing known. `some (b, tb)`: the first cell is `b`, and if `tb` the rest is blank. -/
abbrev Side := Option (Bool × Bool)

abbrev ACfg := Bool × Side × Bool × Side

def emp : ListBlank Bool := ListBlank.mk []

def gam (s : Side) (l : ListBlank Bool) : Prop := match s with
  | none => True
  | some (b, tb) => l.head = b ∧ (tb = true → l.tail = emp)

def blankSide : Side := some (false, true)

def push (w : Bool) (s : Side) : Side := some (w, s == blankSide)

def pop (s : Side) : List (Bool × Side) := match s with
  | none => [(false, none), (true, none)]
  | some (b, true) => [(b, blankSide)]
  | some (b, false) => [(b, none)]

lemma eq_emp_of (l : ListBlank Bool) (h1 : l.head = false) (h2 : l.tail = emp) : l = emp := by
  rw [← ListBlank.cons_head_tail l, h1, h2]
  exact ListBlank.cons_head_tail emp

lemma gam_blank (l : ListBlank Bool) : gam blankSide l ↔ l = emp :=
  ⟨fun h => eq_emp_of l h.1 (h.2 rfl), fun h => h.symm ▸ ⟨rfl, fun _ => rfl⟩⟩

lemma gam_push (w : Bool) (s : Side) (l : ListBlank Bool) (h : gam s l) :
    gam (push w s) (l.cons w) := by
  refine ⟨ListBlank.head_cons w l, fun hb => ?_⟩
  rw [ListBlank.tail_cons]
  have hs : s = blankSide := by simpa using hb
  subst hs
  exact (gam_blank l).1 h

lemma gam_pop (s : Side) (l : ListBlank Bool) (h : gam s l) :
    ∃ p ∈ pop s, l.head = p.1 ∧ gam p.2 l.tail := by
  rcases s with _ | ⟨b, tb⟩
  · exact ⟨(l.head, none), by cases l.head <;> simp [pop], rfl, trivial⟩
  · cases tb
    · exact ⟨(b, none), by simp [pop], h.1, trivial⟩
    · exact ⟨(b, blankSide), by simp [pop], h.1, (gam_blank _).2 (h.2 rfl)⟩

def astep (e : Table) (c : ACfg) : Option (List ACfg) :=
  match entry e c.1 c.2.2.1 with
  | none => none
  | some (none, _, _) => none
  | some (some q', w, true) => some ((pop c.2.2.2).map fun p => (q', push w c.2.1, p.1, p.2))
  | some (some q', w, false) => some ((pop c.2.1).map fun p => (q', p.2, p.1, push w c.2.2.2))

def gamC (a : ACfg) (c : Cfg Bool Bool) : Prop :=
  c.q = some a.1 ∧ gam a.2.1 c.tape.left ∧ c.tape.head = a.2.2.1 ∧ gam a.2.2.2 c.tape.right

lemma astep_sound (e : Table) (a : ACfg) (c : Cfg Bool Bool) (h : gamC a c) (ss : List ACfg)
    (hs : astep e a = some ss) :
    ∃ c', Machine.step (mkM e) c = some c' ∧ ∃ a' ∈ ss, gamC a' c' := by
  obtain ⟨q, L, hd, R⟩ := a
  obtain ⟨cq, ⟨th, tl, tr⟩⟩ := c
  obtain ⟨hq, hL, hh, hR⟩ := h
  simp only at hq hL hh hR
  subst hq
  subst hh
  unfold astep at hs
  simp only at hs
  rcases he : entry e q th with _ | ⟨q', w, d⟩
  · rw [he] at hs
    simp at hs
  · rw [he] at hs
    rcases q' with _ | q'
    · simp at hs
    · cases d
      · simp only [Option.some.injEq] at hs
        subst hs
        obtain ⟨p, hp, hp1, hp2⟩ := gam_pop L tl hL
        refine ⟨⟨some q', ⟨tl.head, tl.tail, tr.cons w⟩⟩, ?_, (q', p.2, p.1, push w R), ?_, ?_⟩
        · simp [Machine.step, mkM, he, dec, dirOf, Tape.write, Tape.move]
        · exact List.mem_map.2 ⟨p, hp, rfl⟩
        · exact ⟨rfl, hp2, hp1, gam_push w R tr hR⟩
      · simp only [Option.some.injEq] at hs
        subst hs
        obtain ⟨p, hp, hp1, hp2⟩ := gam_pop R tr hR
        refine ⟨⟨some q', ⟨tr.head, tl.cons w, tr.tail⟩⟩, ?_, (q', push w L, p.1, p.2), ?_, ?_⟩
        · simp [Machine.step, mkM, he, dec, dirOf, Tape.write, Tape.move]
        · exact List.mem_map.2 ⟨p, hp, rfl⟩
        · exact ⟨rfl, gam_push w L tl hL, hp1, hp2⟩

def a0 : ACfg := (false, blankSide, false, blankSide)

lemma gamC_init : gamC a0 init0 :=
  ⟨rfl, (gam_blank _).2 rfl, rfl, (gam_blank _).2 rfl⟩

/-- Untrusted search for a closed set of abstract configurations. -/
def bfs (e : Table) : Nat → List ACfg → List ACfg → List ACfg
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | n + 1, c :: todo, seen =>
    match astep e c with
    | none => seen
    | some ss =>
      let new := ss.filter fun x => !(seen.contains x)
      bfs e n (new ++ todo) (new ++ seen)

/-- Trusted check that a set of abstract configurations is closed and never halts. -/
def check (e : Table) (S : List ACfg) : Bool :=
  S.contains a0 && S.all fun c =>
    match astep e c with
    | none => false
    | some ss => ss.all fun x => S.contains x

lemma check_sound (e : Table) (S : List ACfg) (h : check e S = true) (n : ℕ) :
    ∃ c a, Machine.multiStep (mkM e) init0 n = some c ∧ a ∈ S ∧ gamC a c := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨h0, hS⟩ := h
  induction n with
  | zero => exact ⟨init0, a0, rfl, h0, gamC_init⟩
  | succ n ih =>
    obtain ⟨c, a, hc, ha, hg⟩ := ih
    have hSa := hS a ha
    rcases hst : astep e a with _ | ss
    · rw [hst] at hSa
      simp at hSa
    · rw [hst] at hSa
      obtain ⟨c', hc', a', ha', hg'⟩ := astep_sound e a c hg ss hst
      refine ⟨c', a', ?_, ?_, hg'⟩
      · rw [Machine.multiStep_succ, hc]
        exact hc'
      · have := List.all_eq_true.1 hSa a' ha'
        simpa using this

def halts7 (e : Table) : Bool := (Machine.multiStep (mkM e) init0 7).isNone

def ok (e : Table) : Bool := halts7 e || check e (bfs e 40 [a0] [a0])

def allE : List Code :=
  none :: ([none, some false, some true].flatMap fun q =>
    [false, true].flatMap fun w => [false, true].map fun d => some (q, w, d))

lemma mem_allE (e : Code) : e ∈ allE := by
  rcases e with _ | ⟨q, w, d⟩
  · simp [allE]
  · rcases q with _ | q <;> [skip; cases q] <;> cases w <;> cases d <;> simp [allE]

def bigCheck : Bool :=
  allE.all fun e1 => allE.all fun e2 => allE.all fun e3 => allE.all fun e4 => ok (e1, e2, e3, e4)

set_option maxRecDepth 100000 in
lemma bigCheck_true : bigCheck = true := by decide +kernel

lemma ok_all (e : Table) : ok e = true := by
  have h := bigCheck_true
  simp only [bigCheck, List.all_eq_true] at h
  exact h e.1 (mem_allE _) e.2.1 (mem_allE _) e.2.2.1 (mem_allE _) e.2.2.2 (mem_allE _)

/-- A two-state, two-symbol machine on `Bool` that ever halts, halts within 7 steps. -/
lemma key (M : Machine Bool Bool) (n : ℕ) (h : Machine.multiStep M init0 (n + 1) = none) :
    Machine.multiStep M init0 7 = none := by
  rw [← mkM_tableOf M] at h ⊢
  have hok := ok_all (tableOf M)
  simp only [ok, Bool.or_eq_true] at hok
  rcases hok with h7 | hc
  · simpa [halts7] using h7
  · obtain ⟨c, a, hc', -, -⟩ := check_sound _ _ hc (n + 1)
    rw [h] at hc'
    simp at hc'

/-! ### Transfer from arbitrary two-element types to `Bool` -/

section Transfer

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]

def conjM (eΓ : Γ ≃ Bool) (eΛ : Λ ≃ Bool) (M : Machine Γ Λ) : Machine Bool Bool :=
  fun q a => (M (eΛ.symm q) (eΓ.symm a)).map fun p => (p.1.map eΛ, ⟨eΓ p.2.symbol, p.2.dir⟩)

def mapCfg (f : PointedMap Γ Bool) (eΛ : Λ ≃ Bool) (c : Cfg Γ Λ) : Cfg Bool Bool :=
  ⟨c.q.map eΛ, c.tape.map f⟩

lemma step_conj (eΓ : Γ ≃ Bool) (eΛ : Λ ≃ Bool) (hΓ : eΓ default = default) (M : Machine Γ Λ)
    (c : Cfg Γ Λ) :
    Machine.step (conjM eΓ eΛ M) (mapCfg ⟨eΓ, hΓ⟩ eΛ c) =
      (Machine.step M c).map (mapCfg ⟨eΓ, hΓ⟩ eΛ) := by
  obtain ⟨q, T⟩ := c
  rcases q with _ | q
  · rfl
  · simp only [mapCfg, Option.map_some, Machine.step, conjM, Tape.map_fst, Equiv.symm_apply_apply]
    rcases hM : M q T.head with _ | ⟨q', ⟨a, d⟩⟩
    · rfl
    · simp [Tape.map_write, Tape.map_move, mapCfg]

lemma multiStep_conj (eΓ : Γ ≃ Bool) (eΛ : Λ ≃ Bool) (hΓ : eΓ default = default) (M : Machine Γ Λ)
    (c : Cfg Γ Λ) (n : ℕ) :
    Machine.multiStep (conjM eΓ eΛ M) (mapCfg ⟨eΓ, hΓ⟩ eΛ c) n =
      (Machine.multiStep M c n).map (mapCfg ⟨eΓ, hΓ⟩ eΛ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
    rcases Machine.multiStep M c n with _ | c'
    · rfl
    · exact step_conj eΓ eΛ hΓ M c'

lemma mapCfg_init (eΓ : Γ ≃ Bool) (eΛ : Λ ≃ Bool) (hΓ : eΓ default = default)
    (hΛ : eΛ default = default) :
    mapCfg ⟨eΓ, hΓ⟩ eΛ (Machine.init ([] : List Γ)) = init0 := by
  simp [mapCfg, Machine.init, init0, hΛ, Tape.map_mk₁]

end Transfer

lemma exists_equiv (α : Type) [Fintype α] [Inhabited α] (h : Fintype.card α = 2) :
    ∃ e : α ≃ Bool, e default = default := by
  let e := Fintype.equivOfCardEq (h.trans Fintype.card_bool.symm)
  exact ⟨e.trans (Equiv.swap (e default) default), by simp⟩

lemma halts_within (C : _root_.BusyBeaver.Candidate 2) :
    Machine.HaltsAfter C.M (Machine.init []) 6 := by
  obtain ⟨n, hn⟩ := (Machine.isHalting_iff_exists_haltsAt C.M).1 C.M_isHalting
  obtain ⟨eΓ, hΓ⟩ := exists_equiv C.Γ C.Γ_card
  obtain ⟨eΛ, hΛ⟩ := exists_equiv C.Λ C.Λ_card
  have h1 : Machine.multiStep (conjM eΓ eΛ C.M) init0 (n + 1) = none := by
    rw [← mapCfg_init eΓ eΛ hΓ hΛ, multiStep_conj, hn]
    rfl
  have h2 := key _ n h1
  rw [← mapCfg_init eΓ eΛ hΓ hΛ, multiStep_conj] at h2
  simpa [Machine.HaltsAfter] using h2

/-! ### The champion: 1RB1LB_1LA1RZ -/

def champT : Table :=
  (some (some true, true, true), some (some true, true, false),
    some (some false, true, false), some (none, true, true))

lemma champ7 : Machine.multiStep (mkM champT) init0 7 = none :=
  Option.isNone_iff_eq_none.1 (by decide +kernel)

def champ : _root_.BusyBeaver.Candidate 2 :=
  ⟨Bool, Bool, inferInstance, rfl, inferInstance, inferInstance, rfl, inferInstance,
    mkM champT, (Machine.isHalting_iff_exists_haltsAt _).2 ⟨6, champ7⟩⟩

lemma champ_number : champ.M.haltingNumber = ((6 : ℕ) : ENat) :=
  Machine.haltingNumber_def (mkM champT) 6 (Option.isSome_iff_exists.1 (by decide +kernel)) champ7

end OMA.BB2

theorem OMA.solution : type_of% @BusyBeaver.BB_2 := by
  unfold BusyBeaver.BB
  refine IsGreatest.csSup_eq ⟨⟨OMA.BB2.champ, OMA.BB2.champ_number⟩, ?_⟩
  rintro N ⟨C, hC⟩
  have h := OMA.BB2.halts_within C
  have hle : C.M.haltingNumber ≤ ((6 : ℕ) : ENat) := sInf_le ⟨6, h, rfl⟩
  rw [hC] at hle
  exact_mod_cast hle
