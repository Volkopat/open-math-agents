import OMAStatements.S_oeis_a227259

/-!
Proof by @etaubman, ported from the complete proof linked in statement PR #20481:
https://github.com/etaubman/open-math-agents/blob/003821fe2a6778c0dd8c89a497ad3c609f96dc44/verified/oeis-a227259.lean

The 32-state parent-array automaton, its 19 reachable subsets, seven-state
quotient, and simultaneous ternary-count invariant are retained. This port
uses the registered definitions and omits the unused coefficient appendix.
The conjectures are Colin Barker's: https://oeis.org/A227259.
-/

open OMA.S_oeis_a227259

namespace OMA.A227259Proof

abbrev Flag := Fin 4
abbrev State := Row × Flag

/-- Flags record which adjacent column pairs already have a strict prefix. -/
def columnsGood (f : Flag) (rs : List Row) : Prop :=
  (f.val % 2 = 1 ∨ lexLE (column rs 0) (column rs 1)) ∧
  (f.val / 2 = 1 ∨ lexLE (column rs 1) (column rs 2))

/-- Finite update table for the two strict-prefix flags. -/
def advance (f : Flag) (r : Row) : Option Flag :=
  ![![some 0, some 2, none, some 1, none, none, none, some 0],
  ![some 1, some 3, none, some 1, some 1, some 3, none, some 1],
  ![some 2, some 2, some 3, some 3, none, none, some 2, some 2],
  ![some 3, some 3, some 3, some 3, some 3, some 3, some 3, some 3]] f r

instance instDecidableLexLE : (xs ys : List ℕ) → Decidable (lexLE xs ys)
  | [], _ => isTrue trivial
  | _ :: _, [] => isFalse id
  | x :: xs, y :: ys => by
    change Decidable (x < y ∨ (x = y ∧ lexLE xs ys))
    letI := instDecidableLexLE xs ys
    infer_instance

instance (r s : Row) : Decidable (rowLex r s) :=
  inferInstanceAs (Decidable (lexLE _ _))

lemma rowLex_iff_le (r s : Row) : rowLex r s ↔ r.val ≤ s.val := by
  exact (by decide : ∀ r s : Row, rowLex r s ↔ r.val ≤ s.val) r s

lemma columnsGood_zero (rs : List Row) :
    columnsGood 0 rs ↔ columnsOrdered rs := by
  simp [columnsGood, columnsOrdered]

lemma columnsGood_nil (f : Flag) : columnsGood f [] := by
  simp [columnsGood, column, lexLE]

/-- The finite flag table implements two independent lexicographic comparisons. -/
lemma advance_certificate :
    ∀ (f : Flag) (r : Row) (p q : Bool),
      ((f.val % 2 = 1 ∨
          (bits r 0).val < (bits r 1).val ∨
          ((bits r 0).val = (bits r 1).val ∧ p = true)) ∧
       (f.val / 2 = 1 ∨
          (bits r 1).val < (bits r 2).val ∨
          ((bits r 1).val = (bits r 2).val ∧ q = true))) ↔
      ∃ g : Flag, advance f r = some g ∧
        (g.val % 2 = 1 ∨ p = true) ∧ (g.val / 2 = 1 ∨ q = true) := by
  decide

lemma columnsGood_cons (f : Flag) (r : Row) (rs : List Row) :
    columnsGood f (r :: rs) ↔
      ∃ g : Flag, advance f r = some g ∧ columnsGood g rs := by
  have h := advance_certificate f r
    (decide (lexLE (column rs 0) (column rs 1)))
    (decide (lexLE (column rs 1) (column rs 2)))
  simp only [decide_eq_true_eq] at h
  simpa only [columnsGood, column, List.map_cons, lexLE] using h

def edge (q q' : State) (o : Symbol) : Prop :=
  q.1.val ≤ q'.1.val ∧ label q.1 q'.1 = o ∧ advance q.2 q'.1 = some q'.2

instance (q q' : State) (o : Symbol) : Decidable (edge q q' o) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def nfaRun (q : State) : List Symbol → Prop
  | [] => True
  | o :: w => ∃ q' : State, edge q q' o ∧ nfaRun q' w

lemma nfaRun_semantics (w : List Symbol) (q : State) :
    nfaRun q w ↔
      ∃ rs : List Row, rs.length = w.length ∧ rowsOrdered (q.1 :: rs) ∧
        columnsGood q.2 rs ∧ thresholds (q.1 :: rs) = w := by
  induction w generalizing q with
  | nil => simp [nfaRun, rowsOrdered, thresholds, columnsGood_nil]
  | cons o w ih =>
    constructor
    · rintro ⟨⟨s,g⟩, hedge, hrun⟩
      rcases (ih (s,g)).mp hrun with ⟨rs, hlen, hrows, hcols, hout⟩
      refine ⟨s :: rs, by simpa using congrArg Nat.succ hlen, ?_, ?_, ?_⟩
      · exact ⟨(rowLex_iff_le _ _).mpr hedge.1, hrows⟩
      · exact (columnsGood_cons _ _ _).mpr ⟨g, hedge.2.2, hcols⟩
      · simp only [thresholds, hedge.2.1, hout]
    · rintro ⟨rs, hlen, hrows, hcols, hout⟩
      cases rs with
      | nil => simp at hlen
      | cons s rs =>
        have hlen' : rs.length = w.length := by simpa using hlen
        rcases (columnsGood_cons _ _ _).mp hcols with ⟨g, hg, hcols'⟩
        have hout' : label q.1 s = o ∧ thresholds (s :: rs) = w := by
          simpa only [thresholds, List.cons.injEq] using hout
        refine ⟨(s,g), ⟨(rowLex_iff_le _ _).mp hrows.1, hout'.1, hg⟩, ?_⟩
        exact (ih (s,g)).mpr ⟨rs, hlen', hrows.2, hcols', hout'.2⟩

def initial : Finset State := Finset.univ.filter (fun q => advance 0 q.1 = some q.2)

def nfaFrom (S : Finset State) (w : List Symbol) : Prop :=
  ∃ q ∈ S, nfaRun q w

lemma actualImage_iff_nfa (w : List Symbol) : actualImage w ↔ nfaFrom initial w := by
  constructor
  · rintro ⟨rs, hlen, hrows, hcols, hout⟩
    cases rs with
    | nil => simp at hlen
    | cons r rs =>
      have hlen' : rs.length = w.length := by simpa using hlen
      have hc := (columnsGood_zero (r :: rs)).mpr hcols
      rcases (columnsGood_cons 0 r rs).mp hc with ⟨g, hg, hc'⟩
      refine ⟨(r,g), ?_, (nfaRun_semantics w (r,g)).mpr ⟨rs,hlen',hrows,hc',hout⟩⟩
      simpa [initial] using hg
  · rintro ⟨⟨r,g⟩, hinit, hrun⟩
    have hg : advance 0 r = some g := by simpa [initial] using hinit
    rcases (nfaRun_semantics w (r,g)).mp hrun with ⟨rs,hlen,hrows,hcols,hout⟩
    refine ⟨r :: rs, by simpa using congrArg Nat.succ hlen, hrows, ?_, hout⟩
    exact (columnsGood_zero (r :: rs)).mp
      ((columnsGood_cons 0 r rs).mpr ⟨g,hg,hcols⟩)


def nextSet (S : Finset State) (o : Symbol) : Finset State :=
  Finset.univ.filter (fun q' => ∃ q ∈ S, edge q q' o)

lemma nfaFrom_nil (S : Finset State) : nfaFrom S [] ↔ S.Nonempty := by
  simp [nfaFrom, nfaRun, Finset.Nonempty]

lemma nfaFrom_cons (S : Finset State) (o : Symbol) (w : List Symbol) :
    nfaFrom S (o :: w) ↔ nfaFrom (nextSet S o) w := by
  simp only [nfaFrom, nfaRun, nextSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨q, hq, q', he, hw⟩ => ⟨q', ⟨q, hq, he⟩, hw⟩,
    fun ⟨q', ⟨q, hq, he⟩, hw⟩ => ⟨q, hq, q', he, hw⟩⟩

/-- The reachable subsets of the 32-state source-array automaton. -/
def reachableStates (i : Fin 19) : Finset State :=
  ![{(0,0), (1,2), (3,1), (7,0)},
    {(7,0), (7,1)},
    ∅,
    {(3,1), (3,3), (5,3), (7,2)},
    {(0,0), (1,2), (2,3), (3,1), (4,1), (6,2), (7,0)},
    {(6,3), (7,1), (7,2), (7,3)},
    {(6,3)},
    {(3,1), (3,3), (5,3)},
    {(4,1), (4,3), (5,3)},
    {(7,0), (7,1), (7,2), (7,3)},
    {(6,2), (6,3), (7,1)},
    {(0,0), (1,2), (2,3), (3,1), (4,1), (4,3), (5,3), (6,2), (7,0)},
    {(7,1), (7,2), (7,3)},
    {(7,3)},
    {(6,3), (7,1), (7,3)},
    {(6,2), (6,3)},
    {(6,2), (6,3), (7,1), (7,3)},
    {(7,1), (7,3)},
    {(7,2), (7,3)}] i

def reachableStep (i : Fin 19) (o : Symbol) : Fin 19 :=
  ![![1,2,3,4],
    ![1,2,2,2],
    ![2,2,2,2],
    ![5,6,7,8],
    ![9,10,3,11],
    ![12,6,2,2],
    ![13,6,2,2],
    ![14,6,7,8],
    ![13,14,2,8],
    ![9,2,2,2],
    ![12,15,2,2],
    ![9,16,3,11],
    ![12,2,2,2],
    ![13,2,2,2],
    ![17,6,2,2],
    ![18,15,2,2],
    ![12,15,2,2],
    ![17,2,2,2],
    ![18,2,2,2]] i o

def collapse (i : Fin 19) : Fin 7 :=
  ![0,1,6,3,2,4,4,3,5,1,4,2,1,1,4,4,4,1,1] i

def dfaStep (q : Fin 7) (o : Fin 4) : Fin 7 :=
  ![![1,6,3,2],![1,6,6,6],![1,4,3,2],![4,4,3,5],![1,4,6,6],![1,4,6,5],![6,6,6,6]] q o

lemma initial_certificate : initial = reachableStates 0 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma transition_certificate :
    ∀ (i : Fin 19) (o : Symbol),
      nextSet (reachableStates i) o = reachableStates (reachableStep i o) := by
  decide

lemma accepting_certificate :
    ∀ i : Fin 19, (reachableStates i).Nonempty ↔ collapse i ≠ 6 := by decide

lemma collapse_certificate :
    ∀ (i : Fin 19) (o : Symbol),
      collapse (reachableStep i o) = dfaStep (collapse i) o := by decide

lemma nfaFrom_reachable_iff_dfa (w : List Symbol) (i : Fin 19) :
    nfaFrom (reachableStates i) w ↔ w.foldl dfaStep (collapse i) ≠ 6 := by
  induction w generalizing i with
  | nil => simpa only [List.foldl_nil, nfaFrom_nil] using accepting_certificate i
  | cons o w ih =>
    rw [nfaFrom_cons, transition_certificate]
    simpa only [List.foldl_cons, collapse_certificate] using ih (reachableStep i o)

lemma nfaFrom_initial_iff_dfa (w : List Symbol) :
    nfaFrom initial w ↔ w.foldl dfaStep (0 : Fin 7) ≠ 6 := by
  rw [initial_certificate]
  simpa only [collapse, Matrix.cons_val_zero] using nfaFrom_reachable_iff_dfa w 0


open Finset

def transfer (f : Fin 7 → ℤ) (q : Fin 7) : ℤ := ∑ o : Fin 4, f (dfaStep q o)

def terminal (q : Fin 7) : ℤ := if q = 6 then 0 else 1

def countVec : ℕ → Fin 7 → ℤ
  | 0 => terminal
  | n+1 => transfer (countVec n)

def dfaCount (n : ℕ) : ℤ := countVec n 0

def budget (n k : ℕ) : ℤ :=
  ∑ w : Fin n → Fin 3, if (∑ i, (w i).val) ≤ k then 1 else 0

def budgetVec (n : ℕ) (k : Fin 5) : ℤ := budget n k.val

def budgetTransfer (v : Fin 5 → ℤ) (k : Fin 5) : ℤ :=
  if k.val = 0 then v 0
  else if k.val = 1 then v 1 + v 0
  else if k.val = 2 then v 2 + v 1 + v 0
  else if k.val = 3 then v 3 + v 2 + v 1
  else v 4 + v 3 + v 2

def embed (v : Fin 5 → ℤ) (q : Fin 7) : ℤ :=
  if q.val = 0 then v 4
  else if q.val = 1 then v 0
  else if q.val = 2 then v 4 + v 1 - v 0
  else if q.val = 3 then v 3 + v 2 - v 1
  else if q.val = 4 then v 1
  else if q.val = 5 then v 2
  else 0

def gfSequence (n : ℕ) : ℤ := if n = 0 then 0 else dfaCount n

lemma countVec_word_sum (n : ℕ) (q : Fin 7) :
    countVec n q = ∑ w : Fin n → Fin 4,
      terminal ((List.ofFn w).foldl dfaStep q) := by
  induction n generalizing q with
  | zero => simp [countVec]
  | succ n ih =>
    rw [countVec, transfer, ← (Fin.consEquiv (fun _ : Fin (n+1) => Fin 4)).sum_comp]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro o ho
    rw [ih]
    apply Finset.sum_congr rfl
    intro w hw
    change terminal ((List.ofFn w).foldl dfaStep (dfaStep q o)) =
      terminal ((List.ofFn (Fin.cons o w)).foldl dfaStep q)
    rw [List.ofFn_succ]
    rfl

lemma budget_zero (k : ℕ) : budget 0 k = 1 := by simp [budget]

lemma budget_succ (n k : ℕ) : budget (n+1) k =
    ∑ c : Fin 3, if c.val ≤ k then budget n (k-c.val) else 0 := by
  unfold budget
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Fin 3)).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c hc
  change (∑ w : Fin n → Fin 3,
    if (∑ i : Fin (n+1), (Fin.cons (α := fun _ => Fin 3) c w i).val) ≤ k then (1 : ℤ) else 0) = _
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  by_cases h : c.val ≤ k
  · rw [if_pos h]
    apply Finset.sum_congr rfl
    intro w hw
    have he : c.val + (∑ i, (w i).val) ≤ k ↔ (∑ i, (w i).val) ≤ k-c.val := by omega
    simp only [he]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro w hw
    have he : ¬ c.val + (∑ i, (w i).val) ≤ k := by omega
    simp only [he, if_false]

lemma budgetVec_succ (n : ℕ) : budgetVec (n+1) = budgetTransfer (budgetVec n) := by
  funext k
  unfold budgetVec
  rw [budget_succ]
  fin_cases k <;> norm_num [Fin.sum_univ_three, budgetTransfer]

lemma budgetVec_iterate (n : ℕ) : budgetVec n = budgetTransfer^[n] (fun _ => 1) := by
  induction n with
  | zero => funext k; simp [budgetVec, budget_zero]
  | succ n ih => rw [budgetVec_succ, ih, Function.iterate_succ_apply']

lemma transfer_embed (v : Fin 5 → ℤ) : transfer (embed v) = embed (budgetTransfer v) := by
  funext q
  unfold transfer
  rw [Fin.sum_univ_four]
  fin_cases q
  · change v 0 + 0 + (v 3 + v 2 - v 1) + (v 4 + v 1 - v 0) = v 4 + v 3 + v 2
    ring
  · change v 0 + 0 + 0 + 0 = v 0
    ring
  · change v 0 + v 1 + (v 3 + v 2 - v 1) + (v 4 + v 1 - v 0) =
      (v 4 + v 3 + v 2) + (v 1 + v 0) - v 0
    ring
  · change v 1 + v 1 + (v 3 + v 2 - v 1) + v 2 =
      (v 3 + v 2 + v 1) + (v 2 + v 1 + v 0) - (v 1 + v 0)
    ring
  · change v 0 + v 1 + 0 + 0 = v 1 + v 0
    ring
  · change v 0 + v 1 + 0 + v 2 = v 2 + v 1 + v 0
    ring
  · change (0 : ℤ) + 0 + 0 + 0 = 0
    ring

lemma countVec_embed (n : ℕ) : countVec n = embed (budgetVec n) := by
  induction n with
  | zero =>
    funext q
    fin_cases q <;> norm_num [countVec, terminal, embed, budgetVec, budget_zero, Fin.ext_iff]
  | succ n ih => rw [countVec, ih, transfer_embed, ← budgetVec_succ]

lemma dfaCount_budget (n : ℕ) : dfaCount n = budget n 4 := by
  rw [dfaCount, countVec_embed]
  simp [embed, budgetVec]

lemma dfaCount_eq_ternaryCount (n : ℕ) : dfaCount n = (ternaryCount n : ℤ) := by
  rw [dfaCount_budget]
  simp [budget, ternaryCount]

set_option maxHeartbeats 2000000 in
lemma budgetTransfer_relation (v : Fin 5 → ℤ) :
    (budgetTransfer^[5] v) 4 - 5*(budgetTransfer^[4] v) 4 +
      10*(budgetTransfer^[3] v) 4 - 10*(budgetTransfer^[2] v) 4 +
      5*(budgetTransfer^[1] v) 4 - v 4 = 0 := by
  norm_num [Function.iterate_succ_apply', budgetTransfer]
  ring

lemma dfaCount_iterate (n : ℕ) : dfaCount n = (budgetTransfer^[n] (fun _ => 1)) 4 := by
  rw [dfaCount, countVec_embed, budgetVec_iterate]
  simp [embed]

lemma dfa_recurrence (n : ℕ) :
    dfaCount (n+5) - 5*dfaCount (n+4) + 10*dfaCount (n+3) -
      10*dfaCount (n+2) + 5*dfaCount (n+1) - dfaCount n = 0 := by
  simp only [dfaCount_iterate]
  simpa only [← Function.iterate_add_apply, Nat.add_comm] using
    budgetTransfer_relation (budgetTransfer^[n] (fun _ => 1))

lemma dfa_initial : dfaCount 0 = 1 ∧ dfaCount 1 = 3 ∧ dfaCount 2 = 9 ∧
    dfaCount 3 = 23 ∧ dfaCount 4 = 50 ∧ dfaCount 5 = 96 := by
  norm_num [dfaCount_iterate, Function.iterate_succ_apply', budgetTransfer]

def dfaGeneratingSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (gfSequence n : ℚ))

lemma dfaGeneratingSeries_mul :
    dfaGeneratingSeries * (1 - PowerSeries.X)^5 =
      PowerSeries.X * (3 - 6*PowerSeries.X + 8*PowerSeries.X^2 -
        5*PowerSeries.X^3 + PowerSeries.X^4) := by
  have he : dfaGeneratingSeries * (1 - PowerSeries.X)^5 =
      dfaGeneratingSeries - PowerSeries.C 5 * (dfaGeneratingSeries * PowerSeries.X^1) +
      PowerSeries.C 10 * (dfaGeneratingSeries * PowerSeries.X^2) -
      PowerSeries.C 10 * (dfaGeneratingSeries * PowerSeries.X^3) +
      PowerSeries.C 5 * (dfaGeneratingSeries * PowerSeries.X^4) -
      dfaGeneratingSeries * PowerSeries.X^5 := by
    simp only [map_ofNat]
    ring
  have hp : (PowerSeries.X : PowerSeries ℚ) * (3 - 6*PowerSeries.X +
      8*PowerSeries.X^2 - 5*PowerSeries.X^3 + PowerSeries.X^4) =
      PowerSeries.C 3 * PowerSeries.X^1 - PowerSeries.C 6 * PowerSeries.X^2 +
      PowerSeries.C 8 * PowerSeries.X^3 - PowerSeries.C 5 * PowerSeries.X^4 +
      PowerSeries.C 1 * PowerSeries.X^5 := by
    simp only [map_ofNat, map_one]
    ring
  rw [he, hp]
  apply PowerSeries.ext
  intro n
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mul_X_pow', dfaGeneratingSeries, PowerSeries.coeff_mk]
  by_cases hn : n < 6
  · interval_cases n <;>
      norm_num [gfSequence, dfa_initial.1, dfa_initial.2.1, dfa_initial.2.2.1,
        dfa_initial.2.2.2.1, dfa_initial.2.2.2.2.1, dfa_initial.2.2.2.2.2]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 6 ≤ n by omega)
    have hr : (dfaCount (k+6) : ℚ) - 5*dfaCount (k+5) + 10*dfaCount (k+4) -
        10*dfaCount (k+3) + 5*dfaCount (k+2) - dfaCount (k+1) = 0 := by
      exact_mod_cast (show dfaCount (k+6) - 5*dfaCount (k+5) + 10*dfaCount (k+4) -
        10*dfaCount (k+3) + 5*dfaCount (k+2) - dfaCount (k+1) = 0 by
          simpa only [Nat.add_assoc, Nat.reduceAdd] using dfa_recurrence (k+1))
    norm_num [gfSequence, show 6+k=k+6 by omega,
      show 1 ≤ k+6 by omega, show 2 ≤ k+6 by omega, show 3 ≤ k+6 by omega,
      show 4 ≤ k+6 by omega, show 5 ≤ k+6 by omega,
      show k+6-1=k+5 by omega, show k+6-2=k+4 by omega,
      show k+6-3=k+3 by omega, show k+6-4=k+2 by omega, show k+6-5=k+1 by omega,
      show k+6 ≠ 0 by omega, show k+5 ≠ 0 by omega, show k+4 ≠ 0 by omega,
      show k+3 ≠ 0 by omega, show k+2 ≠ 0 by omega, show k+1 ≠ 0 by omega,
      show k+6 ≠ 1 by omega, show k+6 ≠ 2 by omega, show k+6 ≠ 3 by omega,
      show k+6 ≠ 4 by omega, show k+6 ≠ 5 by omega]
    linarith

lemma actualImage_iff_dfa (w : List Symbol) :
    actualImage w ↔ w.foldl dfaStep (0 : Fin 7) ≠ 6 :=
  (actualImage_iff_nfa w).trans (nfaFrom_initial_iff_dfa w)

lemma arrayCount_eq_dfaCount (n : ℕ) : (arrayCount n : ℤ) = dfaCount n := by
  classical
  calc
    (arrayCount n : ℤ) = ∑ w : Fin n → Symbol,
        if actualImage (List.ofFn w) then 1 else 0 := by simp [arrayCount]
    _ = ∑ w : Fin n → Symbol,
        terminal ((List.ofFn w).foldl dfaStep 0) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [actualImage_iff_dfa]
      simp [terminal]
    _ = dfaCount n := (countVec_word_sum n 0).symm

lemma arrayCount_eq_ternaryCount (n : ℕ) : arrayCount n = ternaryCount n := by
  exact_mod_cast (arrayCount_eq_dfaCount n).trans (dfaCount_eq_ternaryCount n)

lemma generatingSeries_eq_dfaGeneratingSeries : generatingSeries = dfaGeneratingSeries := by
  apply PowerSeries.ext
  intro n
  simp only [generatingSeries, dfaGeneratingSeries, PowerSeries.coeff_mk, gfSequence]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ↓reduceIte]
    exact_mod_cast arrayCount_eq_dfaCount n

end OMA.A227259Proof

open OMA.A227259Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a227259.main :=
  ⟨fun n _ => arrayCount_eq_ternaryCount n,
    generatingSeries_eq_dfaGeneratingSeries.trans
      ((PowerSeries.eq_mul_inv_iff_mul_eq (by simp)).2 dfaGeneratingSeries_mul)⟩
