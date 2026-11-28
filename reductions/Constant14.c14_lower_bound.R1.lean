import FormalConjectures.OptimizationConstants.«14»

/-!
The tree enumeration in section 3 of Blanchard et al., arXiv:2509.12337, branches
only on a transition actually read by the machine. We extract a partial table
from a finite run, name states in order of first visit, and orient the first
move to the right. Nonhalting certificates are needed only for these tables.
Their ZFC proofs must still be transported to the original encodings.
The coordinate-change argument adapts the four-state reflection proof in
BusyBeaver.BB_4.R1.H2.R1 by @Halldon.
-/

-- Credit: @yuka30240
namespace OMA.R_Constant14_c14_lower_bound_R1

open Turing BusyBeaver FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

/-- The separately registered four-state lower bound also supplies nonemptiness
of the set whose natural infimum defines C14. -/
def H1 : Prop := 5 ≤ Constant14.C14

/-- Internalize a bounded halting trace. An explicit move into the halt state
leaves one last configuration, so the empty outer option is tested one step later. -/
def H2 : Prop := ∀ M : Machine (Fin 2) (Fin 5),
  M.HaltsAfter (Machine.init []) 47176870 →
  Entailment.Provable 𝗭𝗙𝗖 (Constant14.halts M)

/-- Certify the surviving partial tables in ZFC. Every defined instruction is
used before the cutoff, and every smaller state label has already appeared when
a state is first read. Unused entries are immediate halts. -/
def H3 : Prop := ∀ P : Machine (Fin 2) (Fin 5),
  (∃ q b, P 0 0 = some (some q, Stmt.write b Dir.right)) →
  (∃ q T, P.multiStep (Machine.init []) 47176870 = some ⟨some q, T⟩) →
  (∀ q a out, P q a = some out →
    out.1 ≠ none ∧ ∃ j < 47176870, ∃ T : Tape (Fin 2),
      P.multiStep (Machine.init []) j = some ⟨some q, T⟩ ∧ T.head = a) →
  (∀ j ≤ 47176870, ∀ q (T : Tape (Fin 2)),
    P.multiStep (Machine.init []) j = some ⟨some q, T⟩ →
    ∀ r < q, ∃ i < j, ∃ U : Tape (Fin 2),
      P.multiStep (Machine.init []) i = some ⟨some r, U⟩) →
  Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts P)

/-- Transport a ZFC nonhalting proof through a table extension, a state
permutation fixing the start, and an optional reflection of the tape.
An extension agrees on each defined instruction of the partial table. -/
def H4 : Prop := ∀ (P M : Machine (Fin 2) (Fin 5)) (e : Equiv.Perm (Fin 5)) (mirror : Bool),
  e 0 = 0 →
  (∀ q a out, P q a = some out →
    ((M (e.symm q) a).map fun (next, act) =>
      (next.map e, Stmt.write act.symbol
        (if mirror then (match act.dir with | .left => .right | .right => .left) else act.dir)))
        = some out) →
  Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts P) → Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts M)

/-- Sort labels by first visit, with a sentinel time for all unvisited labels. -/
lemma order_visits {n : ℕ} [NeZero n] (state : ℕ → Option (Fin n)) (k : ℕ)
    (start : state 0 = some 0) :
    ∃ e : Equiv.Perm (Fin n), e 0 = 0 ∧
      ∀ j ≤ k, ∀ q, state j = some q → ∀ r < e q,
        ∃ i < j, state i = some (e.symm r) := by
  classical
  let first (q : Fin n) := if h : ∃ j, j ≤ k ∧ state j = some q then Nat.find h else k + 1
  have first_le {q j} (hj : j ≤ k) (hq : state j = some q) : first q ≤ j := by
    have h : ∃ i, i ≤ k ∧ state i = some q := ⟨j, hj, hq⟩
    simpa only [first, dif_pos h] using Nat.find_min' h ⟨hj, hq⟩
  have at_first {q} (h : first q ≤ k) : state (first q) = some q := by
    unfold first at *
    split at h
    · rename_i hit
      simpa only [dif_pos hit] using (Nat.find_spec hit).2
    · omega
  let e := (Tuple.sort first).symm
  have sorted {r s} (h : r ≤ s) : first (e.symm r) ≤ first (e.symm s) :=
    Tuple.monotone_sort first h
  have earlier {j q} (hj : j ≤ k) (hq : state j = some q) {r} (hr : r < e q) :
      ∃ i < j, state i = some (e.symm r) := by
    have hrj := sorted hr.le
    rw [Equiv.symm_apply_apply] at hrj
    have hi := hrj.trans (first_le hj hq)
    have hv := at_first (hi.trans hj)
    refine ⟨_, lt_of_le_of_ne hi ?_, hv⟩
    intro eqTime
    rw [eqTime, hq] at hv
    have eqState := congrArg e (Option.some.inj hv)
    exact hr.ne (by simpa using eqState.symm)
  refine ⟨e, ?_, fun _ hj _ hq _ hr => earlier hj hq hr⟩
  by_contra hn
  obtain ⟨i, hi, _⟩ := earlier (Nat.zero_le k) start (Fin.pos_iff_ne_zero.mpr hn)
  omega

/-- Retain precisely the entries queried during the first k transitions. The
partial machine replays the entire prefix. A live configuration at k rules out
both ways of halting at each earlier transition. -/
lemma trim_trace (M : Machine (Fin 2) (Fin 5)) (k : ℕ)
    (live : ∃ q T, M.multiStep (Machine.init []) k = some ⟨some q, T⟩) :
    ∃ P : Machine (Fin 2) (Fin 5),
      (∀ j ≤ k, P.multiStep (Machine.init []) j = M.multiStep (Machine.init []) j) ∧
      (∀ q a out, P q a = some out → M q a = some out) ∧
      (∀ q a out, P q a = some out →
        out.1 ≠ none ∧ ∃ j < k, ∃ T : Tape (Fin 2),
          P.multiStep (Machine.init []) j = some ⟨some q, T⟩ ∧ T.head = a) ∧
      (∀ q a, (∃ j < k, ∃ T : Tape (Fin 2),
        M.multiStep (Machine.init []) j = some ⟨some q, T⟩ ∧ T.head = a) → P q a = M q a) := by
  classical
  let seen (q : Fin 5) (a : Fin 2) := ∃ j < k, ∃ T : Tape (Fin 2),
    M.multiStep (Machine.init []) j = some ⟨some q, T⟩ ∧ T.head = a
  let P : Machine (Fin 2) (Fin 5) := fun q a => if seen q a then M q a else none
  have replay (j : ℕ) (hj : j ≤ k) :
      P.multiStep (Machine.init []) j = M.multiStep (Machine.init []) j := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Machine.multiStep_succ, Machine.multiStep_succ, ih (by omega)]
      cases h : M.multiStep (Machine.init []) j with
      | none => rfl
      | some c =>
        obtain ⟨s, T⟩ := c
        cases s with
        | none => rfl
        | some q =>
          have used : seen q T.head := ⟨j, by omega, T, h, rfl⟩
          simp [Machine.step, P, used]
  have definedAt {q a out} (h : P q a = some out) : seen q a ∧ M q a = some out := by
    by_cases used : seen q a
    · exact ⟨used, by simpa [P, used] using h⟩
    · simp [P, used] at h
  refine ⟨P, replay, fun _ _ _ h => (definedAt h).2, ?_,
    fun q a h => if_pos (show seen q a from h)⟩
  intro q a out h
  obtain ⟨⟨j, hj, T, atJ, rfl⟩, entry⟩ := definedAt h
  refine ⟨?_, j, hj, T, (replay j hj.le).trans atJ, rfl⟩
  rintro terminal
  obtain ⟨s, cmd⟩ := out
  change s = none at terminal
  subst s
  have lastCfg : M.multiStep (Machine.init []) (j + 1) =
      some ⟨none, (T.write cmd.symbol).move cmd.dir⟩ := by
    simp [Machine.multiStep_succ, atJ, Machine.step, entry]
  obtain ⟨r, U, atK⟩ := live
  by_cases last : k = j + 1
  · rw [last, lastCfg] at atK
    cases atK
  · have past : M.multiStep (Machine.init []) (j + 1 + 1) = none := by
      rw [Machine.multiStep_succ, lastCfg]
      rfl
    have empty := Machine.multiStep_eq_none_mono past (show j + 1 + 1 ≤ k by omega)
    rw [atK] at empty
    contradiction

/-- Choose the first direction from an actual running successor, which excludes
both conventions for a halting instruction. -/
lemma first_running (M : Machine (Fin 2) (Fin 5)) {k : ℕ} (hk : 0 < k)
    (long : ¬ M.HaltsAfter (Machine.init []) k) :
    ∃ q a d, M 0 0 = some (some q, Stmt.write a d) := by
  have alive : ¬ M.HaltsAfter (Machine.init []) 1 :=
    fun h => long (Machine.multiStep_eq_none_mono h (by omega : 1 + 1 ≤ k + 1))
  obtain ⟨q, T, h⟩ := M.exists_of_not_haltsAfter (Machine.init []) 1 alive
  change (M 0 0).map _ = some (⟨some q, T⟩ : Cfg (Fin 2) (Fin 5)) at h
  cases ht : M 0 0 with
  | none => rw [ht] at h; cases h
  | some entry =>
    obtain ⟨s, a, d⟩ := entry
    rw [ht] at h
    cases s with
    | none => cases h
    | some r => exact ⟨r, a, d, rfl⟩

/-- Replay with a change of coordinates on the states and the tape. The state
and tape equations here also apply at intermediate times used to name states. -/
lemma certify_survivor (M : Machine (Fin 2) (Fin 5))
    (long : ¬ M.HaltsAfter (Machine.init []) 47176870) (cert : H3) (extend : H4) :
    Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts M) := by
  classical
  let k : ℕ := 47176870
  have positive : 0 < k := by decide
  change ¬ M.HaltsAfter (Machine.init []) k at long
  obtain ⟨q₁, a₁, d₁, first⟩ := first_running M positive long
  let state (j : ℕ) := (M.multiStep (Machine.init []) j).bind Cfg.q
  obtain ⟨e, e0, ordered⟩ := order_visits state k (by rfl)
  let mirror := match d₁ with | .left => true | .right => false
  let turn (d : Dir) := if mirror then (match d with | .left => Dir.right | .right => Dir.left) else d
  let N : Machine (Fin 2) (Fin 5) := fun q a =>
    (M (e.symm q) a).map fun (s, act) => (s.map e, Stmt.write act.symbol (turn act.dir))
  let image (c : Cfg (Fin 2) (Fin 5)) : Cfg (Fin 2) (Fin 5) :=
    ⟨c.q.map e, if mirror then ⟨c.tape.head, c.tape.right, c.tape.left⟩ else c.tape⟩
  have step (c : Cfg (Fin 2) (Fin 5)) : N.step (image c) = (M.step c).map image := by
    obtain ⟨s, ⟨a, l, r⟩⟩ := c
    cases s with
    | none => rfl
    | some q =>
      cases d₁ <;>
        simp only [Machine.step, image, mirror, Option.map_some, N, Equiv.symm_apply_apply,
          Bool.false_eq_true, if_false, if_true]
      all_goals
        cases h : M q a with
        | none => rfl
        | some entry =>
          obtain ⟨next, b, d⟩ := entry
          cases d <;> rfl
  have start : image (Machine.init []) = Machine.init [] := by
    cases d₁ <;> simpa [image, Machine.init, Tape.mk₁, Tape.mk₂, Tape.mk'] using e0
  have trace (j : ℕ) : N.multiStep (Machine.init []) j =
      (M.multiStep (Machine.init []) j).map image := by
    induction j with
    | zero => exact congrArg some start.symm
    | succ j ih =>
      rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
      cases h : M.multiStep (Machine.init []) j with
      | none => rfl
      | some c => exact step c
  have stateTrace (j : ℕ) :
      (N.multiStep (Machine.init []) j).bind Cfg.q = (state j).map e := by
    rw [trace]
    unfold state
    cases M.multiStep (Machine.init []) j <;> rfl
  have stateRun {j r} (h : state j = some r) :
      ∃ U, N.multiStep (Machine.init []) j = some ⟨some (e r), U⟩ := by
    have hs := stateTrace j
    rw [h] at hs
    cases hc : N.multiStep (Machine.init []) j with
    | none => rw [hc] at hs; cases hs
    | some c =>
      obtain ⟨s, U⟩ := c
      rw [hc] at hs
      exact ⟨U, by simpa using hs⟩
  obtain ⟨q, T, atK⟩ := M.exists_of_not_haltsAfter (Machine.init []) k long
  have hitsK : state k = some q := by simp only [state, atK, Option.bind_some]
  obtain ⟨U, atK'⟩ := stateRun hitsK
  obtain ⟨P, replay, agrees, used, retain⟩ := trim_trace N k ⟨e q, U, atK'⟩
  apply extend P M e mirror e0 agrees
  apply cert P
  · have e0' : e.symm 0 = 0 := e.symm_apply_eq.mpr e0.symm
    have hfirst : N 0 0 = some (some (e q₁), Stmt.write a₁ Dir.right) := by
      cases d₁ <;> simp [N, first, e0', turn, mirror]
    exact ⟨e q₁, a₁, (retain 0 0 ⟨0, positive, Tape.mk₁ [], rfl, rfl⟩).trans hfirst⟩
  · exact ⟨e q, U, (replay k le_rfl).trans atK'⟩
  · exact used
  · intro j hj r T atJ s hsr
    have atN := (replay j hj).symm.trans atJ
    have hs := stateTrace j
    rw [atN] at hs
    have hs' : (state j).map e = some r := hs.symm
    obtain ⟨old, hold, eqOld⟩ := Option.map_eq_some_iff.mp hs'
    subst r
    obtain ⟨i, hi, hiState⟩ := ordered j hj old hold s hsr
    obtain ⟨V, hiN⟩ := stateRun hiState
    exact ⟨i, hi, V, by simpa using (replay i (hi.le.trans hj)).trans hiN⟩

theorem main : H1 → H2 → H3 → H4 → type_of% @Constant14.c14_lower_bound := by
  classical
  intro four trace cert extend
  let sizes : Set ℕ := {n | ∃ _ : NeZero n, ∃ M : Machine (Fin 2) (Fin n),
    𝗭𝗙𝗖 ⊬ Constant14.halts M ∧ 𝗭𝗙𝗖 ⊬ ∼Constant14.halts M}
  change 5 ≤ sInf sizes at four
  change 6 ≤ sInf sizes
  have nonempty : sizes.Nonempty := by
    by_contra empty
    rw [Set.not_nonempty_iff_eq_empty.mp empty, Nat.sInf_empty] at four
    omega
  have five : 5 ∉ sizes := by
    rintro ⟨hn, M, noPos, noNeg⟩
    by_cases h : M.HaltsAfter (Machine.init []) 47176870
    · exact noPos (trace M h)
    · exact noNeg (certify_survivor M h cert extend)
  by_contra small
  have eqFive : sInf sizes = 5 := by omega
  exact five (eqFive ▸ Nat.sInf_mem nonempty)

end OMA.R_Constant14_c14_lower_bound_R1
