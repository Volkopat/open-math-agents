import OMAReductions.R_opg_general_position_subsets_R1
import Mathlib

-- Extracted from @grp06's merged proof of opg-general-position-subsets (PR #20915).
-- The original source notices for the included arguments are retained.

/-! Formalization of Pham, Le Quang-Ham and Xue, General-position sets and linear hypergraphs, §§2.2–2.4, https://arxiv.org/abs/2610.34254v1. -/

/-! A finite law for state-dependent binary selection, as in Section 2.2 of
arXiv:2610.34254v1. The accepted list records the selected vertices in order. -/

namespace OMA.OnlineSelection

structure Rule (V State : Type*) where
  chance : V → State → ℝ
  next : V → Bool → State → State

namespace Rule

variable {V State : Type*} (R : Rule V State)

/-- The cap and state invariant are required only on valid states. -/
structure Capped (I : State → Prop) (τ : ℝ) : Prop where
  cap_nonneg : 0 ≤ τ
  cap_le_one : τ ≤ 1
  chance_bounds : ∀ x s, I s → 0 ≤ R.chance x s ∧ R.chance x s ≤ τ
  next_valid : ∀ x b s, I s → I (R.next x b s)

/-- Expectation over the two branches at each step. The callback sees both the
vertices accepted by this run and its terminal state. -/
def expect : List V → State → (List V → State → ℝ) → ℝ
  | [], s, f => f [] s
  | x :: xs, s, f =>
      R.chance x s * expect xs (R.next x true s) (fun A t => f (x :: A) t) +
      (1 - R.chance x s) * expect xs (R.next x false s) f

theorem expect_const (xs : List V) (s : State) (c : ℝ) :
    R.expect xs s (fun _ _ => c) = c := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [expect, ih]
      ring

theorem expect_congr (xs : List V) (s : State) {f g : List V → State → ℝ}
    (h : ∀ A, A.Sublist xs → ∀ t, f A t = g A t) :
    R.expect xs s f = R.expect xs s g := by
  induction xs generalizing s f g with
  | nil => exact h [] List.Sublist.slnil s
  | cons x xs ih =>
      simp only [expect]
      rw [ih _ (fun A hA t => h _ (hA.cons_cons x) t), ih _ (fun A hA t => h _ (hA.cons x) t)]

/-- The finite tower law for a split of the processing order. -/
theorem expect_append (xs ys : List V) (s : State) (f : List V → State → ℝ) :
    R.expect (xs ++ ys) s f =
      R.expect xs s (fun A t => R.expect ys t (fun B u => f (A ++ B) u)) := by
  induction xs generalizing s f with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, expect, ih]

theorem expect_mono {I : State → Prop} {τ : ℝ} (hR : R.Capped I τ)
    (xs : List V) {s : State} (hs : I s) {f g : List V → State → ℝ}
    (h : ∀ A, A.Sublist xs → ∀ t, I t → f A t ≤ g A t) :
    R.expect xs s f ≤ R.expect xs s g := by
  induction xs generalizing s f g with
  | nil => exact h [] List.Sublist.slnil s hs
  | cons x xs ih =>
      obtain ⟨hq0, hqτ⟩ := hR.chance_bounds x s hs
      simp only [expect]
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (ih (hR.next_valid x true s hs) (fun A hA t ht => h _ (hA.cons_cons x) t ht)) hq0)
        (mul_le_mul_of_nonneg_left
          (ih (hR.next_valid x false s hs) (fun A hA t ht => h _ (hA.cons x) t ht))
          (sub_nonneg.mpr (hqτ.trans hR.cap_le_one)))

theorem expect_nonneg {I : State → Prop} {τ : ℝ} (hR : R.Capped I τ)
    (xs : List V) {s : State} (hs : I s) {f : List V → State → ℝ}
    (h : ∀ A, A.Sublist xs → ∀ t, I t → 0 ≤ f A t) :
    0 ≤ R.expect xs s f := by
  rw [← R.expect_const xs s 0]
  exact R.expect_mono hR xs hs h

section Joint

variable [DecidableEq V]

/-- Mass of the event that every requested vertex is accepted. -/
def joint (xs : List V) (s : State) (T : Finset V) : ℝ :=
  R.expect xs s (fun A _ => if T ⊆ A.toFinset then 1 else 0)

private theorem subset_toFinset_cons_iff {x : V} {A : List V} {T : Finset V} :
    T ⊆ (x :: A).toFinset ↔ T.erase x ⊆ A.toFinset := by
  rw [List.toFinset_cons]
  constructor
  · intro h y hy
    have hy' := Finset.mem_erase.mp hy
    exact (Finset.mem_insert.mp (h hy'.2)).resolve_left hy'.1
  · intro h y hy
    by_cases hyx : y = x
    · exact Finset.mem_insert.mpr (Or.inl hyx)
    · exact Finset.mem_insert.mpr (Or.inr (h (Finset.mem_erase.mpr ⟨hyx, hy⟩)))

theorem joint_cons_of_mem {x : V} {xs : List V} (hx : x ∉ xs)
    (s : State) {T : Finset V} (hT : x ∈ T) :
    R.joint (x :: xs) s T = R.chance x s * R.joint xs (R.next x true s) (T.erase x) := by
  have reject :
      R.expect xs (R.next x false s)
        (fun A _ => if T ⊆ A.toFinset then 1 else 0) = 0 := by
    calc
      _ = R.expect xs (R.next x false s) (fun _ _ => 0) := by
        apply R.expect_congr
        intro A hA _
        exact if_neg (fun h => hx (hA.subset (List.mem_toFinset.mp (h hT))))
      _ = _ := R.expect_const _ _ _
  simp only [joint, expect, subset_toFinset_cons_iff, reject, mul_zero, add_zero]

theorem joint_cons_of_notMem {x : V} (xs : List V) (s : State)
    {T : Finset V} (hT : x ∉ T) :
    R.joint (x :: xs) s T =
      R.chance x s * R.joint xs (R.next x true s) T +
        (1 - R.chance x s) * R.joint xs (R.next x false s) T := by
  simp only [joint, expect, subset_toFinset_cons_iff, Finset.erase_eq_of_notMem hT]

/-- Under an adaptive cap, any k specified distinct vertices are jointly
accepted with probability at most τ^k. The requested set need not be contained
in the processing order. -/
theorem joint_le_pow {I : State → Prop} {τ : ℝ} (hR : R.Capped I τ)
    {xs : List V} (hxs : xs.Nodup) {s : State} (hs : I s) (T : Finset V) :
    R.joint xs s T ≤ τ ^ T.card := by
  induction xs generalizing s T with
  | nil =>
      by_cases hT : T = ∅
      · simp [hT, joint, expect]
      · have hnot : ¬ T ⊆ ([] : List V).toFinset := by
          simpa only [List.toFinset_nil, Finset.subset_empty] using hT
        simpa only [joint, expect, if_neg hnot] using pow_nonneg hR.cap_nonneg T.card
  | cons x xs ih =>
      obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hxs
      obtain ⟨hq0, hqτ⟩ := hR.chance_bounds x s hs
      have hq1 : 0 ≤ 1 - R.chance x s := sub_nonneg.mpr (hqτ.trans hR.cap_le_one)
      have hyes := hR.next_valid x true s hs
      have hno := hR.next_valid x false s hs
      by_cases hT : x ∈ T
      · have hcard : (T.erase x).card + 1 = T.card := by
          have hpos := Finset.card_pos.mpr ⟨x, hT⟩
          rw [Finset.card_erase_of_mem hT]
          omega
        rw [R.joint_cons_of_mem hx s hT]
        calc
          _ ≤ R.chance x s * τ ^ (T.erase x).card :=
            mul_le_mul_of_nonneg_left (ih hxs hyes _) hq0
          _ ≤ τ * τ ^ (T.erase x).card :=
            mul_le_mul_of_nonneg_right hqτ (pow_nonneg hR.cap_nonneg _)
          _ = _ := by rw [← hcard, pow_succ']
      · rw [R.joint_cons_of_notMem xs s hT]
        calc
          _ ≤ R.chance x s * τ ^ T.card + (1 - R.chance x s) * τ ^ T.card :=
            add_le_add (mul_le_mul_of_nonneg_left (ih hxs hyes _) hq0)
              (mul_le_mul_of_nonneg_left (ih hxs hno _) hq1)
          _ = _ := by ring

end Joint
end Rule
end OMA.OnlineSelection

/-! Explicit path weights and the prefix identity used in Summing the losses. -/

namespace OMA.OnlineSelection

structure Outcome (V State : Type*) where
  weight : ℝ
  accepted : List V
  state : State

namespace Rule

variable {V State : Type*} (R : Rule V State)

/-- One entry for each binary path, including paths of weight zero. -/
def outcomes : List V → State → List (Outcome V State)
  | [], s => [⟨1, [], s⟩]
  | x :: xs, s =>
      (outcomes xs (R.next x true s)).map
        (fun o => ⟨R.chance x s * o.weight, x :: o.accepted, o.state⟩) ++
      (outcomes xs (R.next x false s)).map
        (fun o => ⟨(1 - R.chance x s) * o.weight, o.accepted, o.state⟩)

theorem expect_eq_outcomes_sum (xs : List V) (s : State) (f : List V → State → ℝ) :
    R.expect xs s f = ((R.outcomes xs s).map (fun o => o.weight * f o.accepted o.state)).sum := by
  induction xs generalizing s f with
  | nil => simp [expect, outcomes]
  | cons x xs ih =>
      simp only [expect, outcomes, List.map_append, List.sum_append, List.map_map, Function.comp_def,
        mul_assoc, List.sum_map_mul_left, ih]

theorem outcomes_normalized (xs : List V) (s : State) :
    ((R.outcomes xs s).map Outcome.weight).sum = 1 := by
  simpa [R.expect_const] using (R.expect_eq_outcomes_sum xs s (fun _ _ => 1)).symm

theorem outcomes_valid {I : State → Prop} {τ : ℝ} (hR : R.Capped I τ)
    {xs : List V} {s : State} (hs : I s) {o : Outcome V State} (ho : o ∈ R.outcomes xs s) :
    0 ≤ o.weight ∧ o.accepted.Sublist xs ∧ I o.state := by
  induction xs generalizing s o with
  | nil =>
      simp only [outcomes, List.mem_singleton] at ho
      subst o
      exact ⟨zero_le_one, List.Sublist.slnil, hs⟩
  | cons x xs ih =>
      obtain ⟨hq0, hqτ⟩ := hR.chance_bounds x s hs
      simp only [outcomes, List.mem_append, List.mem_map] at ho
      rcases ho with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
      · obtain ⟨hw, hsub, hvalid⟩ := ih (hR.next_valid x true s hs) hr
        exact ⟨mul_nonneg hq0 hw, hsub.cons_cons x, hvalid⟩
      · obtain ⟨hw, hsub, hvalid⟩ := ih (hR.next_valid x false s hs) hr
        exact ⟨mul_nonneg (sub_nonneg.mpr (hqτ.trans hR.cap_le_one)) hw, hsub.cons x, hvalid⟩

/-- A state invariant may use the fact that each traversed branch has
positive mass. This permits zero-probability transitions to be ignored. -/
theorem outcomes_positive_invariant {I : State → Prop} {τ : ℝ} (hR : R.Capped I τ)
    {P : List V → State → Prop}
    (hstep : ∀ x xs s b, P (x :: xs) s →
      0 < (if b then R.chance x s else 1 - R.chance x s) → P xs (R.next x b s))
    {xs : List V} {s : State} (hs : I s) (hP : P xs s)
    {o : Outcome V State} (ho : o ∈ R.outcomes xs s) (hpos : 0 < o.weight) :
    P [] o.state := by
  induction xs generalizing s o with
  | nil =>
      simp only [outcomes, List.mem_singleton] at ho
      subst o
      exact hP
  | cons x xs ih =>
      obtain ⟨hq0, hqτ⟩ := hR.chance_bounds x s hs
      simp only [outcomes, List.mem_append, List.mem_map] at ho
      rcases ho with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
      · have hvalid := hR.next_valid x true s hs
        have hr0 := (R.outcomes_valid hR hvalid hr).1
        have hbranch : 0 < R.chance x s := pos_of_mul_pos_left hpos hr0
        exact ih (o := r) hvalid (hstep x xs s true hP (by simpa using hbranch)) hr
          (pos_of_mul_pos_right hpos hq0)
      · have hvalid := hR.next_valid x false s hs
        have hr0 := (R.outcomes_valid hR hvalid hr).1
        have hbranch : 0 < 1 - R.chance x s := pos_of_mul_pos_left hpos hr0
        exact ih (o := r) hvalid (hstep x xs s false hP (by simpa using hbranch)) hr
          (pos_of_mul_pos_right hpos (sub_nonneg.mpr (hqτ.trans hR.cap_le_one)))

section Joint

variable [DecidableEq V]

/-- Mass of accepting x and every specified earlier vertex equals the
expectation of the pre-step chance of x times the earlier event's indicator.
This equality does not require the chance cap. -/
theorem expect_chance_eq_joint (before after : List V) (x : V) (s : State)
    (horder : (before ++ x :: after).Nodup) {T : Finset V} (hT : T ⊆ before.toFinset) :
    R.expect before s (fun A t => if T ⊆ A.toFinset then R.chance x t else 0) =
      R.joint (before ++ x :: after) s (insert x T) := by
  have hdis := List.disjoint_iff_ne.mp horder.disjoint
  have hxBefore : x ∉ before := fun hx => hdis x hx x (by simp) rfl
  have htail := (List.nodup_append'.mp horder).2.1
  have hxAfter := (List.nodup_cons.mp htail).1
  rw [joint, expect_append]
  symm
  apply R.expect_congr
  intro A hA t
  have haccept (B : List V) (hB : B.Sublist after) :
      insert x T ⊆ (A ++ x :: B).toFinset ↔ T ⊆ A.toFinset := by
    constructor
    · intro h y hy
      have hyBefore := List.mem_toFinset.mp (hT hy)
      have hyNot : y ∉ x :: after := fun hy' => hdis y hyBefore y hy' rfl
      have hy' := List.mem_toFinset.mp (h (Finset.mem_insert_of_mem hy))
      exact List.mem_toFinset.mpr ((List.mem_append.mp hy').resolve_right
        (fun hb => hyNot ((hB.cons_cons x).subset hb)))
    · intro h y hy
      apply List.mem_toFinset.mpr
      rcases Finset.mem_insert.mp hy with rfl | hyt
      · exact List.mem_append.mpr (Or.inr (by simp))
      · exact List.mem_append.mpr (Or.inl (List.mem_toFinset.mp (h hyt)))
  have hreject (B : List V) (hB : B.Sublist after) :
      ¬ insert x T ⊆ (A ++ B).toFinset := by
    intro h
    have hx := List.mem_toFinset.mp (h (Finset.mem_insert_self x T))
    rcases List.mem_append.mp hx with hx | hx
    · exact hxBefore (hA.subset hx)
    · exact hxAfter (hB.subset hx)
  have hyes : R.expect after (R.next x true t)
      (fun B _ => if insert x T ⊆ (A ++ x :: B).toFinset then 1 else 0) =
        (if T ⊆ A.toFinset then 1 else 0 : ℝ) := by
    calc
      _ = R.expect after (R.next x true t) (fun _ _ => if T ⊆ A.toFinset then 1 else 0) :=
        R.expect_congr _ _ (fun B hB _ => by simp only [haccept B hB])
      _ = _ := R.expect_const _ _ _
  have hno : R.expect after (R.next x false t)
      (fun B _ => if insert x T ⊆ (A ++ B).toFinset then 1 else 0) = 0 := by
    calc
      _ = R.expect after (R.next x false t) (fun _ _ => 0) :=
        R.expect_congr _ _ (fun B hB _ => if_neg (hreject B hB))
      _ = _ := R.expect_const _ _ _
  simp only [expect, hyes, hno, mul_zero, add_zero]
  by_cases ht : T ⊆ A.toFinset <;> simp [ht]

/-- The particular pre-step expectation used for an ordered tuple in the loss
sum, with two distinct selected witnesses before the current vertex. -/
theorem expect_two_witnesses_le_cube {I : State → Prop} {τ : ℝ} (hR : R.Capped I τ)
    (before after : List V) (x y₁ y₂ : V) {s : State} (hs : I s)
    (horder : (before ++ x :: after).Nodup) (hy₁ : y₁ ∈ before) (hy₂ : y₂ ∈ before)
    (hy : y₁ ≠ y₂) :
    R.expect before s (fun A t =>
      if ({y₁, y₂} : Finset V) ⊆ A.toFinset then R.chance x t else 0) ≤ τ ^ (3 : ℕ) := by
  have hT : ({y₁, y₂} : Finset V) ⊆ before.toFinset := by
    intro y hy'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
    rcases hy' with rfl | rfl
    · exact List.mem_toFinset.mpr hy₁
    · exact List.mem_toFinset.mpr hy₂
  have hx : x ∉ ({y₁, y₂} : Finset V) := by
    intro hx
    have hxBefore := List.mem_toFinset.mp (hT hx)
    exact (List.disjoint_iff_ne.mp horder.disjoint) x hxBefore x (by simp) rfl
  rw [R.expect_chance_eq_joint before after x s horder hT]
  have hcard : (insert x ({y₁, y₂} : Finset V)).card = 3 := by
    rw [Finset.card_insert_of_notMem hx, Finset.card_pair hy]
  simpa only [hcard] using R.joint_le_pow hR horder hs (insert x ({y₁, y₂} : Finset V))

end Joint
end Rule
end OMA.OnlineSelection

/-! The capped hypergraph update of Section 2.2 and its independent support. -/

namespace OMA.OnlineSelection

open Finset

structure HypergraphState (V : Type*) where
  selected : Finset V
  remaining : Finset V
  weight : V → ℝ

namespace HypergraphState

variable {V : Type*} [DecidableEq V]

/-- The initial state conditional on the retained set Q. -/
def initial (Q : Finset V) (a : ℝ) : HypergraphState V :=
  ⟨∅, Q, fun _ => a⟩

def Affected (E : Finset (Finset V)) (s : HypergraphState V) (x u : V) : Prop :=
  u ∈ s.remaining.erase x ∧
    ∃ y ∈ s.selected, ∃ B ∈ E, x ∈ B ∧ y ∈ B ∧ u ∈ B

noncomputable def updateWeight (E : Finset (Finset V)) (τ : ℝ)
    (s : HypergraphState V) (x : V) (accept : Bool) (u : V) : ℝ := by
  classical
  exact if Affected E s x u then
    if accept then 0 else min (s.weight u / (1 - s.weight x)) τ
  else s.weight u

noncomputable def advance (E : Finset (Finset V)) (τ : ℝ)
    (x : V) (accept : Bool) (s : HypergraphState V) : HypergraphState V :=
  ⟨if accept then insert x s.selected else s.selected, s.remaining.erase x,
    updateWeight E τ s x accept⟩

noncomputable def process (E : Finset (Finset V)) (τ : ℝ) : Rule V (HypergraphState V) :=
  ⟨fun x s => s.weight x, advance E τ⟩

def WeightsIn (τ : ℝ) (s : HypergraphState V) : Prop :=
  ∀ u, 0 ≤ s.weight u ∧ s.weight u ≤ τ

theorem process_capped (E : Finset (Finset V)) {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ < 1) :
    (process E τ).Capped (WeightsIn τ) τ := by
  refine ⟨hτ, hτ1.le, fun x s hs => hs x, ?_⟩
  intro x b s hs u
  have hden : 0 ≤ 1 - s.weight x := sub_nonneg.mpr ((hs x).2.trans hτ1.le)
  change 0 ≤ updateWeight E τ s x b u ∧ updateWeight E τ s x b u ≤ τ
  by_cases h : Affected E s x u
  · cases b
    · simpa [updateWeight, h] using
        (show 0 ≤ min (s.weight u / (1 - s.weight x)) τ ∧
          min (s.weight u / (1 - s.weight x)) τ ≤ τ from
            ⟨le_min (div_nonneg (hs u).1 hden) hτ, min_le_right _ _⟩)
    · simp [updateWeight, h, hτ]
  · simpa [updateWeight, h] using hs u

theorem updateWeight_of_zero {E : Finset (Finset V)} {τ : ℝ} (hτ : 0 ≤ τ)
    {s : HypergraphState V} (x : V) (b : Bool) {u : V} (hu : s.weight u = 0) :
    updateWeight E τ s x b u = 0 := by
  by_cases h : Affected E s x u <;> cases b <;>
    simp [updateWeight, h, hu, min_eq_left hτ]

theorem updateWeight_accept_of_affected {E : Finset (Finset V)} {τ : ℝ}
    {s : HypergraphState V} {x u : V} (h : Affected E s x u) :
    updateWeight E τ s x true u = 0 := by
  simp [updateWeight, h]

theorem updateWeight_reject_of_affected {E : Finset (Finset V)} {τ : ℝ}
    {s : HypergraphState V} {x u : V} (h : Affected E s x u) :
    updateWeight E τ s x false u = min (s.weight u / (1 - s.weight x)) τ := by
  simp [updateWeight, h]

/-- Affected weights have local expected update at most their prior value. -/
theorem affected_weight_mean_le {E : Finset (Finset V)} {τ : ℝ}
    {s : HypergraphState V} {x u : V} (h : Affected E s x u) (hq : s.weight x < 1) :
    s.weight x * updateWeight E τ s x true u +
        (1 - s.weight x) * updateWeight E τ s x false u ≤ s.weight u := by
  rw [updateWeight_accept_of_affected h, updateWeight_reject_of_affected h, mul_zero, zero_add]
  have hd := sub_pos.mpr hq
  calc
    _ ≤ (1 - s.weight x) * (s.weight u / (1 - s.weight x)) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hd.le
    _ = _ := by rw [mul_comm, div_mul_cancel₀ _ hd.ne']

/-- The local expectation is exactly preserved when rejection is unclipped. -/
theorem affected_weight_mean_eq_of_unclipped {E : Finset (Finset V)} {τ : ℝ}
    {s : HypergraphState V} {x u : V} (h : Affected E s x u) (hq : s.weight x < 1)
    (hclip : s.weight u / (1 - s.weight x) ≤ τ) :
    s.weight x * updateWeight E τ s x true u +
        (1 - s.weight x) * updateWeight E τ s x false u = s.weight u := by
  rw [updateWeight_accept_of_affected h, updateWeight_reject_of_affected h,
    mul_zero, zero_add, min_eq_left hclip, mul_comm, div_mul_cancel₀ _ (sub_pos.mpr hq).ne']

/-- A weight is either zero or still at least its original positive floor. -/
theorem updateWeight_zero_or_ge {E : Finset (Finset V)} {τ a : ℝ}
    (hτ : 0 ≤ τ) (hτ1 : τ < 1) (haτ : a ≤ τ)
    {s : HypergraphState V} (hs : WeightsIn τ s) (x : V) (b : Bool) {u : V}
    (hu : s.weight u = 0 ∨ a ≤ s.weight u) :
    updateWeight E τ s x b u = 0 ∨ a ≤ updateWeight E τ s x b u := by
  rcases hu with hz | ha
  · exact Or.inl (updateWeight_of_zero hτ x b hz)
  by_cases h : Affected E s x u
  · cases b
    · right
      rw [updateWeight_reject_of_affected h]
      have hd : 0 < 1 - s.weight x := sub_pos.mpr ((hs x).2.trans_lt hτ1)
      have hden : 1 - s.weight x ≤ 1 := sub_le_self _ (hs x).1
      have hscale : s.weight u ≤ s.weight u / (1 - s.weight x) :=
        (le_div_iff₀ hd).mpr (by simpa using mul_le_mul_of_nonneg_left hden (hs u).1)
      exact le_min (ha.trans hscale) haτ
    · exact Or.inl (updateWeight_accept_of_affected h)
  · exact Or.inr (by simpa [updateWeight, h] using ha)

def Independent (E : Finset (Finset V)) (J : Finset V) : Prop :=
  ∀ B ∈ E, (J ∩ B).card ≤ 2

/-- All unprocessed vertices on an edge with two selected vertices have zero
weight. Positive-probability acceptance therefore cannot create a third. -/
structure Safe (E : Finset (Finset V)) (s : HypergraphState V) : Prop where
  disjoint : Disjoint s.selected s.remaining
  independent : Independent E s.selected
  saturated : ∀ B ∈ E, (s.selected ∩ B).card = 2 →
    ∀ u ∈ s.remaining, u ∈ B → s.weight u = 0

theorem initial_safe (E : Finset (Finset V)) (Q : Finset V) (a : ℝ) :
    Safe E (initial Q a) := by
  refine ⟨by simp [initial], ?_, ?_⟩
  · intro B _
    simp [initial]
  · intro B _ h
    simp [initial] at h

theorem advance_safe {E : Finset (Finset V)} {τ : ℝ} (hτ : 0 ≤ τ)
    {s : HypergraphState V} (hs : Safe E s) {x : V} (hx : x ∈ s.remaining)
    (b : Bool) (haccept : b = true → 0 < s.weight x) :
    Safe E (advance E τ x b s) := by
  cases b
  · refine ⟨hs.disjoint.mono_right (erase_subset _ _), hs.independent, ?_⟩
    intro B hB hb u hu huB
    exact updateWeight_of_zero hτ x false
      (hs.saturated B hB hb u (mem_of_mem_erase hu) huB)
  · have hxJ : x ∉ s.selected := fun hxJ => Finset.disjoint_left.mp hs.disjoint hxJ hx
    have hq := haccept rfl
    have inter_mem {B : Finset V} (h : x ∈ B) :
        (insert x s.selected) ∩ B = insert x (s.selected ∩ B) := by
      ext y
      simp only [mem_inter, mem_insert]
      constructor
      · rintro ⟨rfl | hJ, hB⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hJ, hB⟩
      · rintro (rfl | ⟨hJ, hB⟩)
        · exact ⟨Or.inl rfl, h⟩
        · exact ⟨Or.inr hJ, hB⟩
    have inter_notMem {B : Finset V} (h : x ∉ B) :
        (insert x s.selected) ∩ B = s.selected ∩ B := by
      ext y
      simp only [mem_inter, mem_insert]
      constructor
      · rintro ⟨rfl | hJ, hB⟩
        · exact (h hB).elim
        · exact ⟨hJ, hB⟩
      · rintro ⟨hJ, hB⟩
        exact ⟨Or.inr hJ, hB⟩
    have card_insert {B : Finset V} (h : x ∈ B) :
        ((insert x s.selected) ∩ B).card = (s.selected ∩ B).card + 1 := by
      rw [inter_mem h, card_insert_of_notMem (fun h => hxJ (mem_inter.mp h).1)]
    refine ⟨?_, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro u hu huR
      change u ∈ insert x s.selected at hu
      rcases mem_insert.mp hu with rfl | huJ
      · exact (mem_erase.mp huR).1 rfl
      · exact Finset.disjoint_left.mp hs.disjoint huJ (mem_of_mem_erase huR)
    · intro B hB
      change ((insert x s.selected) ∩ B).card ≤ 2
      by_cases h : x ∈ B
      · have hprev : (s.selected ∩ B).card ≤ 1 := by
          have hle := hs.independent B hB
          by_contra! hlarge
          have hfull : (s.selected ∩ B).card = 2 := by omega
          exact hq.ne' (hs.saturated B hB hfull x hx h)
        rw [card_insert h]
        omega
      · rw [inter_notMem h]
        exact hs.independent B hB
    · intro B hB hcard u hu huB
      change ((insert x s.selected) ∩ B).card = 2 at hcard
      by_cases h : x ∈ B
      · rw [card_insert h] at hcard
        have hpos : 0 < (s.selected ∩ B).card := by omega
        obtain ⟨y, hy⟩ := card_pos.mp hpos
        obtain ⟨hyJ, hyB⟩ := mem_inter.mp hy
        exact updateWeight_accept_of_affected ⟨hu, y, hyJ, B, hB, h, hyB, huB⟩
      · rw [inter_notMem h] at hcard
        exact updateWeight_of_zero hτ x true
          (hs.saturated B hB hcard u (mem_of_mem_erase hu) huB)

theorem outcome_selected_eq (E : Finset (Finset V)) (τ : ℝ)
    {xs : List V} {s : HypergraphState V} {o : Outcome V (HypergraphState V)}
    (ho : o ∈ (process E τ).outcomes xs s) :
    o.state.selected = s.selected ∪ o.accepted.toFinset := by
  induction xs generalizing s o with
  | nil =>
      simp only [Rule.outcomes, List.mem_singleton] at ho
      subst o
      simp
  | cons x xs ih =>
      simp only [Rule.outcomes, List.mem_append, List.mem_map] at ho
      rcases ho with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
      · have he := ih hr
        change r.state.selected = insert x s.selected ∪ r.accepted.toFinset at he
        change r.state.selected = s.selected ∪ (x :: r.accepted).toFinset
        rw [he, List.toFinset_cons]
        ext u
        simp only [mem_union, mem_insert]
        tauto
      · exact ih (s := (process E τ).next x false s) (o := r) hr

/-- When the initial remaining set is the given Nodup schedule, every
positive-weight outcome of the capped process is independent. -/
theorem positive_outcome_independent (E : Finset (Finset V)) {τ a : ℝ}
    (hτ : 0 ≤ τ) (hτ1 : τ < 1) (ha0 : 0 ≤ a) (haτ : a ≤ τ)
    {xs : List V} (hxs : xs.Nodup) {o : Outcome V (HypergraphState V)}
    (ho : o ∈ (process E τ).outcomes xs (initial xs.toFinset a)) (hpos : 0 < o.weight) :
    Independent E o.accepted.toFinset := by
  let P (ys : List V) (s : HypergraphState V) :=
    s.remaining = ys.toFinset ∧ ys.Nodup ∧ Safe E s
  have hstep (x : V) (ys : List V) (s : HypergraphState V) (b : Bool)
      (hp : P (x :: ys) s)
      (hm : 0 < (if b then (process E τ).chance x s else 1 - (process E τ).chance x s)) :
      P ys ((process E τ).next x b s) := by
    obtain ⟨hr, hnodup, hsafe⟩ := hp
    obtain ⟨hx, hys⟩ := List.nodup_cons.mp hnodup
    have hxrem : x ∈ s.remaining := by rw [hr]; simp
    have hxerase : s.remaining.erase x = ys.toFinset := by
      rw [hr, List.toFinset_cons, erase_insert (fun h => hx (List.mem_toFinset.mp h))]
    refine ⟨hxerase, hys, advance_safe hτ hsafe hxrem b ?_⟩
    rintro rfl
    exact hm
  have hf := (process E τ).outcomes_positive_invariant (process_capped E hτ hτ1) hstep
    (fun _ => ⟨ha0, haτ⟩) (show P xs (initial xs.toFinset a) from
      ⟨rfl, hxs, initial_safe E _ _⟩) ho hpos
  have he : o.state.selected = o.accepted.toFinset := by
    simpa [initial] using outcome_selected_eq E τ ho
  exact he ▸ hf.2.2.independent

end HypergraphState
end OMA.OnlineSelection

/-! The local product estimates in the proof of Lemma 9, §2.3 of
Thang Pham, Le Quang-Ham and Boqing Xue, "General-position sets and
linear hypergraphs", arXiv:2610.34254v1. -/

namespace OMA.GeneralPositionProducts
open Finset
open scoped Classical

variable {V : Type*} [DecidableEq V]

/-- The total weight of monomials that contain a prescribed set of factors. -/
theorem sum_monomials_containing {A P : Finset V} (hP : P ⊆ A) (t : V → ℝ) :
    ∑ S ∈ A.powerset.filter (P ⊆ ·), ∏ x ∈ S, t x =
      (∏ x ∈ P, t x) * ∏ x ∈ A \ P, (1 + t x) := by
  classical
  rw [prod_one_add, mul_sum]
  apply sum_bij' (fun S _ => S \ P) (fun T _ => T ∪ P)
  · intro S hS
    exact mem_powerset.mpr (sdiff_subset_sdiff (mem_powerset.mp (mem_filter.mp hS).1) (by rfl))
  · intro T hT
    refine mem_filter.mpr ⟨mem_powerset.mpr (union_subset ((mem_powerset.mp hT).trans sdiff_subset) hP), subset_union_right⟩
  · intro S hS
    exact sdiff_union_of_subset (mem_filter.mp hS).2
  · intro T hT
    have hs := mem_powerset.mp hT
    ext x
    simp only [mem_sdiff, mem_union]
    exact ⟨fun h => h.1.resolve_right h.2, fun h => ⟨Or.inl h, (mem_sdiff.mp (hs h)).2⟩⟩
  · intro S hS
    rw [mul_comm, prod_sdiff (mem_filter.mp hS).2]

/-- Count each monomial once for every marked k-subset of its indices.
Keeping the complementary factors makes this an exact identity. -/
theorem marked_monomial_sum (A : Finset V) (k : ℕ) (t : V → ℝ) :
    ∑ S ∈ A.powerset, (S.card.choose k : ℝ) * ∏ x ∈ S, t x =
      ∑ P ∈ A.powersetCard k, (∏ x ∈ P, t x) * ∏ x ∈ A \ P, (1 + t x) := by
  classical
  calc
    _ = ∑ S ∈ A.powerset, ∑ P ∈ A.powersetCard k, if P ⊆ S then ∏ x ∈ S, t x else 0 := by
      apply sum_congr rfl
      intro S hS
      have heq : (A.powersetCard k).filter (· ⊆ S) = S.powersetCard k := by
        ext P
        simp only [mem_filter, mem_powersetCard]
        exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans (mem_powerset.mp hS), h.2⟩, h.1⟩⟩
      rw [← sum_filter, heq]
      simp
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro P hP
      rw [← sum_filter, sum_monomials_containing (mem_powersetCard.mp hP).1]

/-- In particular k=2 bounds the pair-marked sum of elementary symmetric
polynomials in the paper's one-step product estimate. -/
theorem marked_monomial_le (A : Finset V) (k : ℕ) (t : V → ℝ) (ht : ∀ x ∈ A, 0 ≤ t x) :
    ∑ S ∈ A.powerset, (S.card.choose k : ℝ) * ∏ x ∈ S, t x ≤
      (∑ P ∈ A.powersetCard k, ∏ x ∈ P, t x) * ∏ x ∈ A, (1 + t x) := by
  classical
  rw [marked_monomial_sum, sum_mul]
  apply sum_le_sum
  intro P hP
  apply mul_le_mul_of_nonneg_left _ (prod_nonneg (fun x hx => ht x ((mem_powersetCard.mp hP).1 hx)))
  apply prod_le_prod_of_subset_of_one_le sdiff_subset (fun x hx => by linarith [ht x (sdiff_subset hx)])
  intro x hx _
  linarith [ht x hx]

end OMA.GeneralPositionProducts


namespace OMA.GeneralPositionProducts
open Finset
open scoped Classical

variable {V : Type*} [DecidableEq V]

/-- The degree-j elementary symmetric sum of t on A. -/
def elementary (A : Finset V) (t : V → ℝ) (j : ℕ) : ℝ := ∑ S ∈ A.powersetCard j, ∏ x ∈ S, t x

/-- The displayed elementary-symmetric inequality in §2.3. The j=0,1 terms
vanish for k=2. More generally, it holds for every marked degree k. -/
theorem elementary_choose_le (A : Finset V) (t : V → ℝ) (ht : ∀ x ∈ A, 0 ≤ t x) (k : ℕ) :
    ∑ j ∈ range (A.card+1), (j.choose k : ℝ) * elementary A t j ≤
      elementary A t k * ∏ x ∈ A, (1+t x) := by
  classical
  have hmap (S : Finset V) (hS : S ∈ A.powerset) : S.card ∈ range (A.card+1) :=
    mem_range.mpr (Nat.lt_succ_of_le (card_le_card (mem_powerset.mp hS)))
  calc
    _ = ∑ j ∈ range (A.card+1), ∑ S ∈ A.powerset.filter (·.card = j),
        (S.card.choose k : ℝ) * ∏ x ∈ S, t x := by
      apply sum_congr rfl
      intro j _
      rw [elementary, powersetCard_eq_filter, mul_sum]
      apply sum_congr rfl
      intro S hS
      rw [(mem_filter.mp hS).2]
    _ = _ := sum_fiberwise_of_maps_to hmap _
    _ ≤ _ := marked_monomial_le A k t ht

end OMA.GeneralPositionProducts


namespace OMA.GeneralPositionProducts
open Finset
open scoped Classical

variable {V : Type*} [DecidableEq V]

private theorem power_loss (s : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) (k : ℕ) :
    1 - s ^ k ≤ k * (1 - s) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpow : s^k ≤ 1 := pow_le_one₀ hs hs'
    have h := mul_le_mul_of_nonneg_right hpow (sub_nonneg.mpr hs')
    rw [pow_succ, Nat.cast_succ]
    linarith

private theorem bernoulli_coefficient (s : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) (k : ℕ) :
    (if k = 0 then 1 - s else 0) + s - s ^ k ≤ (1 - s) * s * (k.choose 2 : ℝ) := by
  cases k with
  | zero => simp
  | succ k =>
    have hc : k ≤ (k+1).choose 2 := by
      rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right]
      omega
    have h1 := mul_le_mul_of_nonneg_left (power_loss s hs hs' k) hs
    have h2 := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hc : (k : ℝ) ≤ _) (mul_nonneg (sub_nonneg.mpr hs') hs)
    rw [if_neg (Nat.succ_ne_zero k), zero_add, pow_succ]
    linarith

/-- With probability 1-s all affected factors become one, with probability s
they become 1+t. The old factors are 1+s*t. Only pairs contribute to the
expected excess. A and its weights need no geometric structure. -/
theorem bernoulli_product (A : Finset V) (t : V → ℝ) (ht : ∀ x ∈ A, 0 ≤ t x)
    (s : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) :
    (1-s) + s * (∏ x ∈ A, (1 + t x)) - ∏ x ∈ A, (1 + s * t x) ≤
      (1-s) * s * (∑ P ∈ A.powersetCard 2, ∏ x ∈ P, t x) * ∏ x ∈ A, (1 + t x) := by
  classical
  let w (S : Finset V) := ∏ x ∈ S, t x
  have hzero : (1-s) = ∑ S ∈ A.powerset, (if S.card = 0 then 1-s else 0) * w S := by
    simp [card_eq_zero, ite_mul, w]
  have hscaled : (∏ x ∈ A, (1 + s * t x)) = ∑ S ∈ A.powerset, s^S.card * w S := by
    rw [prod_one_add]
    simp only [prod_mul_distrib, prod_const, w]
  calc
    _ = ∑ S ∈ A.powerset, ((if S.card = 0 then 1-s else 0) + s - s^S.card) * w S := by
      conv_lhs => rw [hzero, hscaled, prod_one_add, mul_sum]
      simp only [sub_mul, add_mul, sum_sub_distrib, sum_add_distrib, w]
    _ ≤ ∑ S ∈ A.powerset, ((1-s) * s * (S.card.choose 2 : ℝ)) * w S := by
      apply sum_le_sum
      intro S hS
      exact mul_le_mul_of_nonneg_right (bernoulli_coefficient s hs hs' S.card)
        (prod_nonneg (fun x hx => ht x (mem_powerset.mp hS hx)))
    _ = ((1-s) * s) * (∑ S ∈ A.powerset, (S.card.choose 2 : ℝ) * w S) := by
      simp only [mul_sum, mul_assoc]
    _ ≤ _ := by
      rw [mul_assoc ((1-s) * s)]
      exact mul_le_mul_of_nonneg_left (marked_monomial_le A 2 t ht) (mul_nonneg (sub_nonneg.mpr hs') hs)

end OMA.GeneralPositionProducts


namespace OMA.GeneralPositionProducts
open Finset
open scoped Classical

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- Rejecting the vertex inflates the product on A by at most a factor two
when the local mass lies in the paper's logarithmic range. -/
theorem product_inflation (A : Finset V) (r : V → ℝ) (hr : ∀ x ∈ A, 0 ≤ r x)
    {q : ℝ} (hq : 0 ≤ q) (hhalf : q ≤ 1 / 2)
    (hsmall : 2 * q * (∑ x ∈ A, r x) ≤ Real.log 2) :
    (∏ x ∈ A, (1 + r x / (1 - q))) ≤ 2 * ∏ x ∈ A, (1 + r x) := by
  have hs : 0 < 1 - q := by linarith
  calc
    _ ≤ ∏ x ∈ A, ((1 + r x) * Real.exp (2 * q * r x)) := by
      apply prod_le_prod
      · intro x hx
        have := hr x hx
        positivity
      · intro x hx
        have hx₀ := hr x hx
        have h2 : 1 / (1-q) ≤ 2 := (div_le_iff₀ hs).mpr (by linarith)
        have hd : r x / (1-q) = r x + q * r x * (1 / (1-q)) := by field_simp; ring
        have hb := mul_le_mul_of_nonneg_left h2 (mul_nonneg hq hx₀)
        have he := Real.add_one_le_exp (2*q*r x)
        calc
          _ ≤ 1 + r x + 2*q*r x := by rw [hd]; linarith
          _ ≤ (1+r x) * (2*q*r x + 1) := by nlinarith [mul_nonneg hq (sq_nonneg (r x))]
          _ ≤ _ := mul_le_mul_of_nonneg_left he (by linarith)
    _ = (∏ x ∈ A, (1 + r x)) * Real.exp (2 * q * ∑ x ∈ A, r x) := by
      rw [prod_mul_distrib, ← Real.exp_sum, mul_sum]
    _ ≤ _ := by
      rw [mul_comm (2 : ℝ) (∏ x ∈ A, (1+r x))]
      apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun x hx => by linarith [hr x hx])
      exact (Real.exp_le_exp.mpr hsmall).trans_eq (Real.exp_log (by norm_num))

/-- The paper's compensated G bound. H is the unchanged product outside A.
On selection the affected factors become one. On rejection they are at most
the uncapped factors shown here. -/
theorem mixed_edge_compensation (A : Finset V) (r : V → ℝ) (hr : ∀ x ∈ A, 0 ≤ r x)
    {q H : ℝ} (hq : 0 ≤ q) (hhalf : q ≤ 1 / 2) (hH : 0 ≤ H)
    (hsmall : 2 * q * (∑ x ∈ A, r x) ≤ Real.log 2) :
    q * H + (1-q) * (H * ∏ x ∈ A, (1 + r x / (1-q))) - H * (∏ x ∈ A, (1 + r x)) ≤
      4*q * (H * ∏ x ∈ A, (1 + r x)) * ∑ P ∈ A.powersetCard 2, ∏ x ∈ P, r x := by
  classical
  let s := 1-q
  have hs : 0 < s := by dsimp [s]; linarith
  have hs' : s ≤ 1 := by dsimp [s]; linarith
  have hq' : 1-s = q := by dsimp [s]; ring
  let G := ∏ x ∈ A, (1 + r x)
  let T := ∏ x ∈ A, (1 + r x / s)
  let E := ∑ P ∈ A.powersetCard 2, ∏ x ∈ P, r x
  have hG : 0 ≤ G := prod_nonneg (fun x hx => by linarith [hr x hx])
  have hE : 0 ≤ E := sum_nonneg (fun P hP => prod_nonneg (fun x hx => hr x ((mem_powersetCard.mp hP).1 hx)))
  have hT : T ≤ 2*G := product_inflation A r hr hq hhalf hsmall
  have hb := bernoulli_product A (fun x => r x / s) (fun x hx => div_nonneg (hr x hx) hs.le) s hs.le hs'
  have hcancel (x : V) : s * (r x / s) = r x := by field_simp
  simp only [hcancel, hq'] at hb
  have hpair : (∑ P ∈ A.powersetCard 2, ∏ x ∈ P, (r x / s)) = E / s^2 := by
    rw [show E = _ from rfl, sum_div]
    apply sum_congr rfl
    intro P hP
    rw [prod_div_distrib, prod_const, (mem_powersetCard.mp hP).2]
  rw [hpair] at hb
  change q + s*T - G ≤ q*s*(E/s^2)*T at hb
  have hcoef : q*s*(E/s^2) ≤ 2*q*E := by
    have hu : 1/s ≤ 2 := (div_le_iff₀ hs).mpr (by dsimp [s]; linarith)
    calc
      _ = q*E*(1/s) := by field_simp
      _ ≤ q*E*2 := mul_le_mul_of_nonneg_left hu (mul_nonneg hq hE)
      _ = _ := by ring
  have hT₀ : 0 ≤ T := prod_nonneg (fun x hx => by have := div_nonneg (hr x hx) hs.le; linarith)
  have hbound := hb.trans (mul_le_mul hcoef hT hT₀ (by positivity))
  change q*H + s*(H*T) - H*G ≤ 4*q*(H*G)*E
  calc
    _ = H*(q+s*T-G) := by ring
    _ ≤ H*(2*q*E*(2*G)) := mul_le_mul_of_nonneg_left hbound hH
    _ = _ := by ring

end OMA.GeneralPositionProducts


namespace OMA.GeneralPositionProducts
open Finset
open scoped Classical

variable {V : Type*} [DecidableEq V]

def onSelect (A : Finset V) (z : V → ℝ) (x : V) : ℝ :=
  if x ∈ A then 0 else z x

noncomputable def onReject (A : Finset V) (z : V → ℝ) (q τ : ℝ) (x : V) : ℝ :=
  if x ∈ A then min (z x / (1-q)) τ else z x

noncomputable def edgeProduct (U : Finset V) (z : V → ℝ) (σ : ℝ) : ℝ := ∏ x ∈ U, (1+z x/σ)

def pairSum (U : Finset V) (z : V → ℝ) : ℝ := ∑ P ∈ U.powersetCard 2, ∏ x ∈ P, z x

/-- The mixed-edge estimate in the paper's original z and σ, including the
actual capped update on just the affected vertices. -/
theorem capped_product {A U : Finset V} (hA : A ⊆ U) (z : V → ℝ) (hz : ∀ x ∈ U, 0 ≤ z x)
    {q σ τ : ℝ} (hq : 0 ≤ q) (hhalf : q ≤ 1/2) (hσ : 0 < σ) (hτ : 0 ≤ τ)
    (hmass : 2*q*(∑ x ∈ U, z x)/σ ≤ Real.log 2) :
    q * edgeProduct U (onSelect A z) σ + (1-q) * edgeProduct U (onReject A z q τ) σ -
      edgeProduct U z σ ≤ 4*q*edgeProduct U z σ / σ^2 * pairSum A z := by
  classical
  let r (x : V) := z x / σ
  let H := ∏ x ∈ U \ A, (1+r x)
  have hr : ∀ x ∈ U, 0 ≤ r x := fun x hx => div_nonneg (hz x hx) hσ.le
  have hH : 0 ≤ H := prod_nonneg fun x hx => by linarith [hr x (mem_sdiff.mp hx).1]
  have hs : 0 < 1-q := by linarith
  have hmass' : 2*q*(∑ x ∈ A, r x) ≤ Real.log 2 := by
    have hle := sum_le_sum_of_subset_of_nonneg (f := r) hA (fun x hx _ => hr x hx)
    calc
      _ ≤ 2*q*(∑ x ∈ U, r x) := mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 2*q*(∑ x ∈ U, z x)/σ := by simp [r, ← sum_div]; ring
      _ ≤ _ := hmass
  have hold : edgeProduct U z σ = H * ∏ x ∈ A, (1+r x) := (prod_sdiff hA).symm
  have hsel : edgeProduct U (onSelect A z) σ = H := by
    rw [edgeProduct, ← prod_sdiff hA]
    simp +contextual [onSelect, H, r]
    apply prod_congr rfl
    intro x hx
    rw [if_neg (mem_sdiff.mp hx).2]
  have hrej : edgeProduct U (onReject A z q τ) σ ≤ H * ∏ x ∈ A, (1+r x/(1-q)) := by
    rw [edgeProduct, ← prod_sdiff hA]
    have hout : (∏ x ∈ U \ A, (1 + onReject A z q τ x / σ)) = H := by
      apply prod_congr rfl
      intro x hx
      simp [onReject, (mem_sdiff.mp hx).2, r]
    rw [hout]
    apply mul_le_mul_of_nonneg_left _ hH
    apply prod_le_prod
    · intro x hx
      have h := le_min (div_nonneg (hz x (hA hx)) hs.le) hτ
      simpa [onReject, hx] using (show 0 ≤ 1 + min (z x / (1-q)) τ / σ by positivity)
    · intro x hx
      simp only [onReject, hx, if_true, r, add_le_add_iff_left]
      calc
        _ ≤ (z x / (1-q)) / σ := div_le_div_of_nonneg_right (min_le_left _ _) hσ.le
        _ = _ := by ring
  have hpair : pairSum A r = pairSum A z / σ^2 := by
    unfold pairSum
    rw [sum_div]
    apply sum_congr rfl
    intro P hP
    simp [r, prod_div_distrib, (mem_powersetCard.mp hP).2]
  have hb := mixed_edge_compensation A r (fun x hx => hr x (hA hx)) hq hhalf hH hmass'
  change _ ≤ 4*q*(H*∏ x ∈ A, (1+r x))*pairSum A r at hb
  rw [hpair] at hb
  rw [hsel, hold]
  calc
    _ ≤ _ := sub_le_sub_right (add_le_add_right (mul_le_mul_of_nonneg_left hrej hs.le) _) _
    _ ≤ _ := hb
    _ = _ := by ring

end OMA.GeneralPositionProducts


namespace OMA.GeneralPositionProducts
open Finset
open scoped Classical
variable {V : Type*} [DecidableEq V]

/-- An individual unprocessed weight is a supermartingale for this two-branch update. -/
theorem capped_vertex (A : Finset V) (z : V → ℝ) (x : V) {q τ : ℝ} (hq : q < 1) :
    q * onSelect A z x + (1-q) * onReject A z q τ x ≤ z x := by
  have hs : 0 < 1-q := sub_pos.mpr hq
  by_cases hx : x ∈ A
  · simp [onSelect, onReject, hx]
    calc
      _ ≤ (1-q) * (z x / (1-q)) := mul_le_mul_of_nonneg_left (min_le_left _ _) hs.le
      _ = _ := by field_simp
  · simp only [onSelect, onReject, if_neg hx]
    linarith

/-- Φ₁ is twice the sum of the vertex weights. -/
theorem capped_phi_one (U A : Finset V) (z : V → ℝ) {q τ : ℝ} (hq : q < 1) :
    q * (2 * ∑ x ∈ U, onSelect A z x) + (1-q) * (2 * ∑ x ∈ U, onReject A z q τ x)
      ≤ 2 * ∑ x ∈ U, z x := by
  have h := sum_le_sum (s := U) (fun x _ => capped_vertex A z x (τ := τ) hq)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at h
  linarith

private theorem pair_two_weights (z : V → ℝ) (A : Finset V) (x y : V)
    (hx : 0 ≤ z x) (hy : 0 ≤ z y) {q τ : ℝ} (hq' : q < 1) (hτ : 0 ≤ τ) :
    q * (onSelect A z x * onSelect A z y) + (1-q) * (onReject A z q τ x * onReject A z q τ y)
      - z x * z y ≤ if x ∈ A ∧ y ∈ A then (q/(1-q)) * (z x*z y) else 0 := by
  have hs : 0 < 1-q := sub_pos.mpr hq'
  by_cases hxa : x ∈ A <;> by_cases hya : y ∈ A
  · simp only [onSelect, onReject, hxa, hya, and_self, if_true, mul_zero, zero_add]
    have h := mul_le_mul (min_le_left (z x / (1-q)) τ) (min_le_left (z y / (1-q)) τ)
      (le_min (div_nonneg hy hs.le) hτ) (div_nonneg hx hs.le)
    calc
      _ ≤ (1-q)*((z x/(1-q))*(z y/(1-q))) - z x*z y :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left h hs.le) _
      _ = _ := by field_simp; ring
  · have h := mul_le_mul_of_nonneg_right (capped_vertex A z x (τ := τ) hq') hy
    simp only [onSelect, onReject, if_pos hxa] at h
    simp [onSelect, onReject, hxa, hya]
    linarith
  · have h := mul_le_mul_of_nonneg_left (capped_vertex A z y (τ := τ) hq') hx
    simp only [onSelect, onReject, if_pos hya] at h
    simp [onSelect, onReject, hxa, hya]
    linarith
  · simp [onSelect, onReject, hxa, hya]
    linarith

/-- Φ₀ is twice the pair sum. Only pairs of two affected vertices can
increase in expectation. -/
theorem capped_phi_zero {A U : Finset V} (hA : A ⊆ U) (z : V → ℝ) (hz : ∀ x ∈ U, 0 ≤ z x)
    {q τ : ℝ} (hq' : q < 1) (hτ : 0 ≤ τ) :
    q * (2 * pairSum U (onSelect A z)) + (1-q) * (2 * pairSum U (onReject A z q τ))
      - 2 * pairSum U z ≤ (2*q/(1-q))*pairSum A z := by
  classical
  have hterm (P : Finset V) (hP : P ∈ U.powersetCard 2) :
      q * (∏ x ∈ P, onSelect A z x) + (1-q) * (∏ x ∈ P, onReject A z q τ x) - (∏ x ∈ P, z x)
        ≤ if P ⊆ A then q/(1-q) * ∏ x ∈ P, z x else 0 := by
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hP
    obtain ⟨x,y,hne,rfl⟩ := card_eq_two.mp hcard
    have hx := hz x (hsub (by simp))
    have hy := hz y (hsub (by simp))
    simpa [hne, Finset.insert_subset_iff] using pair_two_weights z A x y hx hy hq' hτ
  have hs := sum_le_sum hterm
  rw [← sum_filter, sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum] at hs
  have heq : (U.powersetCard 2).filter (· ⊆ A) = A.powersetCard 2 := by
    ext P
    simp only [mem_filter, mem_powersetCard]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans hA, h.2⟩, h.1⟩⟩
  rw [heq] at hs
  unfold pairSum
  linear_combination (norm := (ring_nf; exact le_rfl)) 2 * hs

end OMA.GeneralPositionProducts

/-! Finite product weights for the sparsification step in §2.3 of
Pham, Le Quang-Ham and Xue, "General-position sets and linear hypergraphs",
arXiv:2610.34254v1. -/

namespace OMA.GeneralPositionSelection

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

def sampleWeight (p : ℝ) (V S : Finset α) : ℝ :=
  p ^ S.card * (1 - p) ^ (V \ S).card

lemma sum_products_with_fixed {V U : Finset α} (hU : U ⊆ V) (f g : α → ℝ) :
    ∑ S ∈ V.powerset.filter (U ⊆ ·), (∏ x ∈ S, f x) * ∏ x ∈ V \ S, g x =
      ∏ x ∈ V, (f x + if x ∈ U then 0 else g x) := by
  classical
  rw [Finset.prod_add, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases h : U ⊆ S
  · rw [if_pos h]
    congr 1
    apply Finset.prod_congr rfl
    intro x hx
    exact (if_neg fun hxU => (Finset.mem_sdiff.mp hx).2 (h hxU)).symm
  · rw [if_neg h]
    have hex : ∃ x, x ∈ U ∧ x ∉ S := by
      by_contra! hn
      exact h (fun {_} hx => hn _ hx)
    obtain ⟨x, hxU, hxS⟩ := hex
    have hxV : x ∈ V := hU hxU
    have hz : (∏ j ∈ V \ S, if j ∈ U then 0 else g j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨hxV, hxS⟩) (if_pos hxU)
    rw [hz, mul_zero]

theorem sample_fixed (p : ℝ) {V U : Finset α} (hU : U ⊆ V) :
    ∑ S ∈ V.powerset.filter (U ⊆ ·), sampleWeight p V S = p ^ U.card := by
  simp only [sampleWeight, ← Finset.prod_const]
  rw [sum_products_with_fixed hU]
  rw [← Finset.prod_subset hU]
  · apply Finset.prod_congr rfl
    intro x hx
    simp [hx]
  · intro x _ hx
    simp [hx]

open scoped Classical in
theorem sample_count (p : ℝ) {V : Finset α} {T : Finset (Finset α)}
    (f : Finset α → ℝ) (hT : ∀ U ∈ T, U ⊆ V) :
    ∑ S ∈ V.powerset, sampleWeight p V S * (∑ U ∈ T.filter (· ⊆ S), f U) =
      ∑ U ∈ T, (p ^ U.card) * f U := by
  simp only [Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  simp only [mul_ite, mul_zero, ← Finset.sum_filter, ← Finset.sum_mul]
  rw [sample_fixed p (hT U hU)]

theorem sample_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (V S : Finset α) :
    0 ≤ sampleWeight p V S :=
  mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp') _)

theorem exists_ge_of_sample_expectation {p c : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (V : Finset α) (f : Finset α → ℝ)
    (hc : c ≤ ∑ S ∈ V.powerset, sampleWeight p V S * f S) :
    ∃ S ⊆ V, c ≤ f S := by
  by_contra! h
  have hmass : ∑ S ∈ V.powerset, sampleWeight p V S = 1 := by
    simpa using sample_fixed (α := α) p (Finset.empty_subset V)
  have hlt : (∑ S ∈ V.powerset, sampleWeight p V S * f S) <
      ∑ S ∈ V.powerset, sampleWeight p V S * c := by
    have hex : ∃ S ∈ V.powerset, 0 < sampleWeight p V S := by
      by_contra! hn
      have : ∑ S ∈ V.powerset, sampleWeight p V S ≤ 0 :=
        Finset.sum_nonpos hn
      linarith
    obtain ⟨S, hS, hw⟩ := hex
    apply Finset.sum_lt_sum
    · intro T hT
      exact mul_le_mul_of_nonneg_left
        (h T (Finset.mem_powerset.mp hT)).le (sample_nonneg hp hp' V T)
    · exact ⟨S, hS, mul_lt_mul_of_pos_left (h S (Finset.mem_powerset.mp hS)) hw⟩
  rw [← Finset.sum_mul, hmass, one_mul] at hlt
  linarith

theorem sample_prod (p : ℝ) {V U : Finset α} (hU : U ⊆ V) (f : α → ℝ) :
    ∑ S ∈ V.powerset.filter (U ⊆ ·), sampleWeight p V S * ∏ x ∈ S, f x =
      (∏ x ∈ U, p * f x) * ∏ x ∈ V \ U, (p * f x + (1 - p)) := by
  simp only [sampleWeight, ← Finset.prod_const]
  calc
    _ = ∑ S ∈ V.powerset.filter (U ⊆ ·),
          (∏ x ∈ S, p * f x) * ∏ _x ∈ V \ S, (1 - p) := by
        apply Finset.sum_congr rfl
        intro S _
        rw [Finset.prod_mul_distrib]
        ring
    _ = _ := by
        rw [sum_products_with_fixed hU, ← Finset.prod_sdiff hU
          (f := fun x => p * f x + if x ∈ U then 0 else 1 - p)]
        rw [mul_comm]
        congr 1
        · exact Finset.prod_congr rfl (by simp +contextual)
        · apply Finset.prod_congr rfl
          intro x hx
          simp [(Finset.mem_sdiff.mp hx).2]

open scoped Classical in
noncomputable def sampleMass (p : ℝ) (V : Finset α) (ok : Finset α → Prop) : ℝ :=
  ∑ S ∈ V.powerset.filter ok, sampleWeight p V S

open scoped Classical in
theorem sample_mass_mono {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) {V : Finset α}
    {f g : Finset α → Prop} (h : ∀ S ∈ V.powerset, f S → g S) :
    sampleMass p V f ≤ sampleMass p V g := by
  unfold sampleMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro S hS
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hS).1,
      h S (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hS).2⟩
  · intro S _ _
    exact sample_nonneg hp hp' V S

open scoped Classical in
theorem sample_mass_markov {p c : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) {V : Finset α}
    (f : Finset α → Prop) [DecidablePred f] (g : Finset α → ℝ)
    (hg : ∀ S ∈ V.powerset, f S → 0 ≤ g S) :
    c * sampleMass p V (fun S => f S ∧ c ≤ g S) ≤
      ∑ S ∈ V.powerset.filter f, sampleWeight p V S * g S := by
  let bad := @Finset.filter (Finset α) (fun S => f S ∧ c ≤ g S)
    (fun _ => Classical.propDecidable _) V.powerset
  have hbad (S : Finset α) : S ∈ bad ↔ S ∈ V.powerset ∧ f S ∧ c ≤ g S := by
    simp only [bad, Finset.mem_filter]
  change c * (∑ S ∈ bad, sampleWeight p V S) ≤ _
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ S ∈ bad, sampleWeight p V S * g S := by
      apply Finset.sum_le_sum
      intro S hS
      have hgt := ((hbad S).mp hS).2.2
      rw [mul_comm c]
      exact mul_le_mul_of_nonneg_left hgt (sample_nonneg hp hp' V S)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro S hS
        obtain ⟨hSV, hf, _⟩ := (hbad S).mp hS
        exact Finset.mem_filter.mpr ⟨hSV, hf⟩
      · intro S hS _
        exact mul_nonneg (sample_nonneg hp hp' V S)
          (hg S (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hS).2)

theorem sample_edge_moment (p : ℝ) {V U B : Finset α} (hU : U ⊆ V) (hB : B ⊆ V \ U) :
    ∑ S ∈ V.powerset.filter (U ⊆ ·), sampleWeight p V S * (2 : ℝ) ^ (S ∩ B).card =
      p ^ U.card * (1 + p) ^ B.card := by
  classical
  let f : α → ℝ := fun x => if x ∈ B then 2 else 1
  calc
    _ = ∑ S ∈ V.powerset.filter (U ⊆ ·), sampleWeight p V S * ∏ x ∈ S, f x := by
      apply Finset.sum_congr rfl
      intro S _
      have hinter : S.filter (· ∈ B) = S ∩ B := by ext x; simp
      simp only [f, ← Finset.prod_filter, hinter, Finset.prod_const]
    _ = (∏ x ∈ U, p * f x) * ∏ x ∈ V \ U, (p * f x + (1 - p)) :=
      sample_prod p hU f
    _ = _ := by
      congr 1
      · rw [← Finset.prod_const]
        apply Finset.prod_congr rfl
        intro x hx
        have hxB : x ∉ B := fun h => (Finset.mem_sdiff.mp (hB h)).2 hx
        simp [f, hxB]
      · rw [← Finset.prod_const, ← Finset.prod_subset hB]
        · apply Finset.prod_congr rfl
          intro x hx
          simp [f, hx]
          ring
        · intro x _ hx
          simp [f, hx]

open scoped Classical in
set_option maxHeartbeats 500000 in
theorem sample_edge_tail {p t : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    {V U B : Finset α} (hU : U ⊆ V) (hB : B ⊆ V \ U)
    (hsize : p * B.card ≤ t) :
    sampleMass p V (fun S => U ⊆ S ∧ 3 * t ≤ (S ∩ B).card) ≤
      p ^ U.card * Real.exp (-t / 2) := by
  have hlog : 1 / 2 ≤ Real.log (2 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (2 : ℝ)⁻¹ by positivity)
    rw [Real.log_inv] at h
    linarith
  have ht' : 0 < Real.exp (3 * t / 2) := Real.exp_pos _
  rw [← mul_le_mul_iff_of_pos_left ht']
  calc
    _ ≤ Real.exp (3 * t / 2) * sampleMass p V
        (fun S => U ⊆ S ∧ Real.exp (3 * t / 2) ≤ (2 : ℝ) ^ (S ∩ B).card) := by
      apply mul_le_mul_of_nonneg_left _ ht'.le
      apply sample_mass_mono hp hp'
      intro S _ hS
      refine ⟨hS.1, ?_⟩
      have hexp : (2 : ℝ) ^ (S ∩ B).card =
          Real.exp (((S ∩ B).card : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      rw [hexp]
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ ((S ∩ B).card : ℝ) * (1 / 2) := by linarith [hS.2]
        _ ≤ _ := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
    _ ≤ ∑ S ∈ V.powerset.filter (U ⊆ ·),
        sampleWeight p V S * (2 : ℝ) ^ (S ∩ B).card :=
      sample_mass_markov (V := V) (c := Real.exp (3 * t / 2)) hp hp'
        (U ⊆ ·) (fun S => (2 : ℝ) ^ (S ∩ B).card)
        (fun _ _ _ => by positivity)
    _ = p ^ U.card * (1 + p) ^ B.card := sample_edge_moment p hU hB
    _ ≤ p ^ U.card * Real.exp t := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hp _)
      calc
        _ ≤ (Real.exp p) ^ B.card :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp p]) _
        _ = Real.exp ((B.card : ℝ) * p) := (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp t := Real.exp_le_exp.mpr (by simpa only [mul_comm] using hsize)
    _ = Real.exp (3 * t / 2) * (p ^ U.card * Real.exp (-t / 2)) := by
      rw [mul_left_comm, ← Real.exp_add, show 3 * t / 2 + -t / 2 = t by ring]

open scoped Classical in
set_option maxHeartbeats 800000 in
theorem sample_degree_tail {p D : ℝ} (hp : 0 < p) (hp' : p ≤ 1) (hD : 0 < D)
    {V : Finset α} {T : Finset (Finset α)} (v : α)
    (hT : ∀ U ∈ T, U ⊆ V ∧ U.card = 3) (hsize : (T.card : ℝ) ≤ D) :
    sampleMass p V (fun S => v ∈ S ∧ 20 * p ^ 2 * D ≤ (T.filter (· ⊆ S)).card) ≤
      p / 20 := by
  let g : Finset α → ℝ := fun S => (T.filter (· ⊆ S)).card
  let c : ℝ := 20 * p ^ 2 * D
  have hc : 0 < c := by dsimp [c]; positivity
  change sampleMass p V (fun S => v ∈ S ∧ c ≤ g S) ≤ _
  rw [← mul_le_mul_iff_of_pos_left hc]
  calc
    _ ≤ ∑ S ∈ V.powerset.filter (v ∈ ·), sampleWeight p V S * g S :=
      sample_mass_markov (V := V) (c := c) hp.le hp'
        (v ∈ ·) g (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ ∑ S ∈ V.powerset, sampleWeight p V S * g S := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro S _ _
      exact mul_nonneg (sample_nonneg hp.le hp' V S) (Nat.cast_nonneg _)
    _ = ∑ U ∈ T, (p ^ U.card) * 1 := by
      simpa [g] using sample_count p (fun _ => 1) (fun U hU => (hT U hU).1)
    _ = p ^ 3 * T.card := by
      rw [Finset.sum_congr rfl (g := fun _ => p ^ 3)]
      · simp [mul_comm]
      · intro U hU
        rw [(hT U hU).2, mul_one]
    _ ≤ p ^ 3 * D := mul_le_mul_of_nonneg_left hsize (pow_nonneg hp.le _)
    _ = c * (p / 20) := by dsimp [c]; ring

open scoped Classical in
theorem sample_mass_partition (p : ℝ) (V : Finset α) (f g : Finset α → Prop) :
    sampleMass p V f =
      sampleMass p V (fun S => f S ∧ g S) + sampleMass p V (fun S => f S ∧ ¬g S) := by
  simp only [sampleMass, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hf : f S <;> by_cases hg : g S <;> simp [hf, hg]

open scoped Classical in
theorem sample_mass_union_bound {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (V : Finset α) {β : Type*} (A : Finset β) (f : β → Finset α → Prop) :
    sampleMass p V (fun S => ∃ b ∈ A, f b S) ≤ ∑ b ∈ A, sampleMass p V (f b) := by
  simp only [sampleMass, Finset.sum_filter]
  rw [Finset.sum_comm (s := A)]
  apply Finset.sum_le_sum
  intro S _
  have hS := sample_nonneg hp hp' V S
  by_cases he : ∃ b ∈ A, f b S
  · obtain ⟨b, hb, hf⟩ := he
    rw [if_pos ⟨b, hb, hf⟩]
    calc
      _ = if f b S then sampleWeight p V S else 0 := (if_pos hf).symm
      _ ≤ _ := Finset.single_le_sum
        (f := fun x : β => if f x S then sampleWeight p V S else 0)
        (fun x _ => by split <;> simp_all) hb
  · rw [if_neg he]
    exact Finset.sum_nonneg (fun b _ => by split <;> simp_all)

open scoped Classical in
noncomputable def retained (D p t : ℝ) (E : Finset (Finset α))
    (triples : α → Finset (Finset α)) (S : Finset α) : Finset α :=
  S.filter fun v =>
    ((triples v).filter (· ⊆ S)).card ≤ 20 * p ^ 2 * D ∧
      ∀ B ∈ E, v ∈ B → ((S ∩ B.erase v).card : ℝ) ≤ 3 * t

open scoped Classical in
set_option maxHeartbeats 1200000 in
theorem sample_retained_vertex {D p t : ℝ} (hp : 0 < p) (hp' : p ≤ 1) (hD : 0 < D)
    {V : Finset α} {E : Finset (Finset α)} {triples : α → Finset (Finset α)}
    {v : α} (hv : v ∈ V)
    (hT : ∀ U ∈ triples v, U ⊆ V ∧ U.card = 3)
    (hdegree : ((triples v).card : ℝ) ≤ D)
    (hedges : ∀ B ∈ E, B ⊆ V ∧ p * B.card ≤ t)
    (hincidence : ((E.filter (v ∈ ·)).card : ℝ) ≤ D)
    (hsmall : D * Real.exp (-t / 2) ≤ 1 / 4) :
    p / 2 ≤ sampleMass p V (v ∈ retained D p t E triples ·) := by
  let dGood : Finset α → Prop := fun S =>
    ((triples v).filter (· ⊆ S)).card ≤ 20 * p ^ 2 * D
  let A := E.filter (v ∈ ·)
  let eGood : Finset α → Prop := fun S =>
    ∀ B ∈ A, ((S ∩ B.erase v).card : ℝ) ≤ 3 * t
  have hsingle : sampleMass p V (v ∈ ·) = p := by
    calc
      _ = ∑ S ∈ V.powerset.filter (({v} : Finset α) ⊆ ·), sampleWeight p V S := by
        unfold sampleMass
        apply Finset.sum_congr _ (fun _ _ => rfl)
        ext S
        simp [Finset.singleton_subset_iff]
      _ = _ := (sample_fixed p (Finset.singleton_subset_iff.mpr hv)).trans (by simp)
  have hsplit₁ := sample_mass_partition p V (v ∈ ·) dGood
  have hsplit₂ := sample_mass_partition p V (fun S => v ∈ S ∧ dGood S) eGood
  have hdBad : sampleMass p V (fun S => v ∈ S ∧ ¬dGood S) ≤ p / 20 := by
    refine le_trans ?_ (sample_degree_tail hp hp' hD v hT hdegree)
    apply sample_mass_mono hp.le hp'
    intro S _ h
    exact ⟨h.1, (lt_of_not_ge h.2).le⟩
  have heBad : sampleMass p V (fun S => (v ∈ S ∧ dGood S) ∧ ¬eGood S) ≤
      p * (D * Real.exp (-t / 2)) := by
    calc
      _ ≤ sampleMass p V (fun S => ∃ B ∈ A,
          ({v} : Finset α) ⊆ S ∧ 3 * t ≤ (S ∩ B.erase v).card) := by
        apply sample_mass_mono hp.le hp'
        intro S _ h
        obtain ⟨B, hB⟩ := not_forall.mp h.2
        obtain ⟨hBA, hlarge⟩ := Classical.not_imp.mp hB
        refine ⟨B, hBA, Finset.singleton_subset_iff.mpr h.1.1, (lt_of_not_ge hlarge).le⟩
      _ ≤ ∑ B ∈ A, sampleMass p V (fun S =>
          ({v} : Finset α) ⊆ S ∧ 3 * t ≤ (S ∩ B.erase v).card) :=
        sample_mass_union_bound hp.le hp' _ _ _
      _ ≤ ∑ _B ∈ A, p * Real.exp (-t / 2) := by
        apply Finset.sum_le_sum
        intro B hBA
        have hB := hedges B (Finset.mem_filter.mp hBA).1
        have hsub : B.erase v ⊆ V \ {v} := by
          intro x hx
          have hx' := Finset.mem_erase.mp hx
          exact Finset.mem_sdiff.mpr ⟨hB.1 hx'.2, by simpa using hx'.1⟩
        have hsize : p * (B.erase v).card ≤ t :=
          (mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_erase_le) hp.le).trans hB.2
        simpa only [Finset.card_singleton, pow_one] using
          sample_edge_tail hp.le hp' (Finset.singleton_subset_iff.mpr hv) hsub hsize
      _ = p * (A.card * Real.exp (-t / 2)) := by simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hincidence (Real.exp_pos _).le) hp.le
  have hgood : sampleMass p V (fun S => (v ∈ S ∧ dGood S) ∧ eGood S) ≤
      sampleMass p V (v ∈ retained D p t E triples ·) := by
    apply sample_mass_mono hp.le hp'
    intro S _ h
    have hm : v ∈ retained D p t E triples S := by
      simpa only [retained, Finset.mem_filter] using
        (show v ∈ S ∧ dGood S ∧
          (∀ B ∈ E, v ∈ B → ((S ∩ B.erase v).card : ℝ) ≤ 3 * t) from
          ⟨h.1.1, h.1.2, fun B hBE hvB => h.2 B (Finset.mem_filter.mpr ⟨hBE, hvB⟩)⟩)
    exact hm
  have heBad' := heBad.trans (mul_le_mul_of_nonneg_left hsmall hp.le)
  linarith

end OMA.GeneralPositionSelection

/-! Finite weighted codegree estimates for Section 2.1 of arXiv:2610.34254v1. -/

namespace OMA.GeneralPositionCodegrees

open scoped BigOperators
open Finset

variable {V : Type*} [DecidableEq V]

/-- Two distinct edges meet in at most one vertex. -/
def Linear (E : Finset (Finset V)) : Prop :=
  ∀ e ∈ E, ∀ f ∈ E, e ≠ f → (e ∩ f).card ≤ 1

/-- Edges through the given vertex. -/
def incident (E : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  E.filter (v ∈ ·)

/-- Sum of the edge weights over the common edges of a distinct pair.
In a linear family this is a single edge weight or zero. -/
def pairWeight (E : Finset (Finset V)) (a : Finset V → ℝ) (v x : V) : ℝ :=
  if v = x then 0 else ∑ e ∈ (incident E v).filter (x ∈ ·), a e

theorem Linear.edge_eq_of_pair {E : Finset (Finset V)} (hE : Linear E)
    {e f : Finset V} (he : e ∈ E) (hf : f ∈ E)
    {v x : V} (hvx : v ≠ x) (hve : v ∈ e) (hvf : v ∈ f)
    (hxe : x ∈ e) (hxf : x ∈ f) : e = f := by
  by_contra hne
  exact hvx (card_le_one_iff.mp (hE e he f hf hne)
    (mem_inter.mpr ⟨hve, hvf⟩) (mem_inter.mpr ⟨hxe, hxf⟩))

theorem common_card_le_one {E : Finset (Finset V)} (hE : Linear E)
    {v x : V} (hvx : v ≠ x) : ((incident E v).filter (x ∈ ·)).card ≤ 1 := by
  apply card_le_one_iff.mpr
  intro e f he hf
  obtain ⟨he, hxe⟩ := mem_filter.mp he
  obtain ⟨hf, hxf⟩ := mem_filter.mp hf
  obtain ⟨he, hve⟩ := mem_filter.mp he
  obtain ⟨hf, hvf⟩ := mem_filter.mp hf
  exact hE.edge_eq_of_pair he hf hvx hve hvf hxe hxf

theorem common_eq_singleton {E : Finset (Finset V)} (hE : Linear E)
    {v x : V} (hvx : v ≠ x) {e : Finset V}
    (he : e ∈ (incident E v).filter (x ∈ ·)) :
    (incident E v).filter (x ∈ ·) = {e} := by
  ext f
  simp only [mem_singleton]
  exact ⟨fun hf => card_le_one_iff.mp (common_card_le_one hE hvx) hf he,
    fun eq => eq ▸ he⟩

@[simp] theorem pairWeight_self (E : Finset (Finset V)) (a : Finset V → ℝ) (v : V) :
    pairWeight E a v v = 0 := by simp [pairWeight]

theorem pairWeight_nonneg {E : Finset (Finset V)} {a : Finset V → ℝ}
    (ha : ∀ e ∈ E, 0 ≤ a e) (v x : V) : 0 ≤ pairWeight E a v x := by
  unfold pairWeight
  split
  · exact le_rfl
  · exact sum_nonneg (fun e he => ha e (mem_filter.mp (mem_filter.mp he).1).1)

theorem pairWeight_of_mem {E : Finset (Finset V)} {a : Finset V → ℝ}
    (hE : Linear E) {e : Finset V} (he : e ∈ E) {v x : V}
    (hvx : v ≠ x) (hv : v ∈ e) (hx : x ∈ e) : pairWeight E a v x = a e := by
  have h := common_eq_singleton hE hvx (mem_filter.mpr ⟨mem_filter.mpr ⟨he, hv⟩, hx⟩)
  simp [pairWeight, hvx, h]

private theorem pairWeight_sq_eq {E : Finset (Finset V)} (hE : Linear E)
    (a : Finset V → ℝ) {v x : V} (hvx : v ≠ x) :
    pairWeight E a v x ^ 2 = ∑ e ∈ (incident E v).filter (x ∈ ·), a e ^ 2 := by
  rcases eq_empty_or_nonempty ((incident E v).filter (x ∈ ·)) with h | ⟨e, he⟩
  · simp [pairWeight, hvx, h]
  · simp [pairWeight, hvx, common_eq_singleton hE hvx he]

/-- The sum of squared pair weights along an edge avoiding v is bounded by the
squared-weight budget on the edges through v. -/
theorem pairWeight_sum_sq_le {E : Finset (Finset V)} (hE : Linear E)
    (a : Finset V → ℝ) {B : Finset V} (hB : B ∈ E) {v : V} (hv : v ∉ B) :
    ∑ x ∈ B, pairWeight E a v x ^ 2 ≤ ∑ e ∈ incident E v, a e ^ 2 := by
  calc
    _ = ∑ x ∈ B, ∑ e ∈ incident E v, if x ∈ e then a e ^ 2 else 0 := by
      refine sum_congr rfl (fun x hx => ?_)
      have hvx : v ≠ x := fun eq => hv (eq.symm ▸ hx)
      rw [pairWeight_sq_eq hE a hvx, sum_filter]
    _ = ∑ e ∈ incident E v, ∑ x ∈ B, if x ∈ e then a e ^ 2 else 0 := sum_comm
    _ ≤ _ := by
      refine sum_le_sum (fun e he => ?_)
      obtain ⟨he, hve⟩ := mem_filter.mp he
      have hne : B ≠ e := fun eq => hv (eq.symm ▸ hve)
      have hcard : ((B ∩ e).card : ℝ) ≤ 1 := by exact_mod_cast hE B hB e he hne
      rw [← sum_filter, filter_mem_eq_inter, sum_const, nsmul_eq_mul]
      simpa using mul_le_mul_of_nonneg_right hcard (sq_nonneg (a e))

/-- Lemma 6 with arbitrary real edge weights. -/
theorem pairWeight_sum_le_sqrt {E : Finset (Finset V)} (hE : Linear E)
    (a : Finset V → ℝ) {B : Finset V} (hB : B ∈ E) {v : V} (hv : v ∉ B)
    {D : ℝ} (hbudget : ∑ e ∈ incident E v, a e ^ 2 ≤ 2 * D) :
    ∑ x ∈ B, pairWeight E a v x ≤ Real.sqrt (2 * B.card * D) := by
  apply Real.le_sqrt_of_sq_le
  calc
    _ ≤ (B.card : ℝ) * ∑ x ∈ B, pairWeight E a v x ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ (B.card : ℝ) * (2 * D) :=
      mul_le_mul_of_nonneg_left ((pairWeight_sum_sq_le hE a hB hv).trans hbudget) (by positivity)
    _ = _ := by ring

end OMA.GeneralPositionCodegrees

/-! The finite incidence rearrangement and threshold estimate of Lemma 7. -/

namespace OMA.GeneralPositionCodegrees

open scoped BigOperators
open Finset

variable {V : Type*} [DecidableEq V]

/-- Expand a weighted sum over neighbors as a sum over incident edges.
The diagonal has weight zero, so it is removed from the inner sum. -/
theorem weighted_pairWeight_sum (E : Finset (Finset V)) (a : Finset V → ℝ)
    (S : Finset V) (v : V) (f : V → ℝ) :
    ∑ x ∈ S, pairWeight E a v x * f x =
      ∑ e ∈ incident E v, a e * ∑ x ∈ S.erase v ∩ e, f x := by
  calc
    _ = ∑ x ∈ S.erase v, pairWeight E a v x * f x := by
      symm
      refine sum_subset (erase_subset _ _) (fun x hx hxe => ?_)
      have hxv : x = v := by
        by_contra hne
        exact hxe (mem_erase.mpr ⟨hne, hx⟩)
      simp [hxv]
    _ = ∑ x ∈ S.erase v, ∑ e ∈ incident E v, if x ∈ e then a e * f x else 0 := by
      refine sum_congr rfl (fun x hx => ?_)
      have hvx := (mem_erase.mp hx).1.symm
      rw [pairWeight, if_neg hvx, sum_mul, sum_filter]
    _ = ∑ e ∈ incident E v, ∑ x ∈ S.erase v, if x ∈ e then a e * f x else 0 := sum_comm
    _ = _ := by
      refine sum_congr rfl (fun e _ => ?_)
      rw [← sum_filter, filter_mem_eq_inter, mul_sum]

/-- Off the central vertex, a nonnegative point weight is counted at most once
as the incident edges range over a linear family. -/
theorem incident_inter_sum_le {E : Finset (Finset V)} (hE : Linear E)
    (S : Finset V) (v : V) {f : V → ℝ} (hf : ∀ x ∈ S, 0 ≤ f x) :
    ∑ e ∈ incident E v, ∑ x ∈ S.erase v ∩ e, f x ≤ ∑ x ∈ S, f x := by
  calc
    _ = ∑ e ∈ incident E v, ∑ x ∈ S.erase v, if x ∈ e then f x else 0 := by
      refine sum_congr rfl (fun e _ => ?_)
      rw [← sum_filter, filter_mem_eq_inter]
    _ = ∑ x ∈ S.erase v, ∑ e ∈ incident E v, if x ∈ e then f x else 0 := sum_comm
    _ ≤ ∑ x ∈ S.erase v, f x := by
      refine sum_le_sum (fun x hx => ?_)
      obtain ⟨hxv, hxS⟩ := mem_erase.mp hx
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      have hcard : (((incident E v).filter (x ∈ ·)).card : ℝ) ≤ 1 := by
        exact_mod_cast common_card_le_one hE hxv.symm
      simpa using mul_le_mul_of_nonneg_right hcard (hf x hxS)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun x hx _ => hf x hx)

/-- The small/large split in Lemma 7, with the threshold supplied independently
of the cube-root identity. Only large indices need the square-root envelope. -/
theorem cutoff_product_sum_le {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ) {D T : ℝ} (hT : 1 ≤ T) (hcube : D ≤ T ^ 3)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hA : ∑ i ∈ s, a i ^ 2 ≤ 2 * D) (hB : ∑ i ∈ s, b i ≤ 2 * D)
    (hlarge : ∀ i ∈ s, T ≤ a i → b i ≤ Real.sqrt (6 * a i * D)) :
    ∑ i ∈ s, a i * b i ≤ 7 * (T * D) := by
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have pointwise (i : ι) (hi : i ∈ s) :
      a i * b i ≤ T * b i + (5 / 2 * T) * a i ^ 2 := by
    have hale := ha i hi
    have hble := hb i hi
    by_cases h : T ≤ a i
    · have hsquare : 6 * a i * D ≤ ((5 / 2 : ℝ) * T * a i) ^ 2 := by
        have hD' : D ≤ a i * T ^ 2 :=
          hcube.trans (by simpa [pow_succ, mul_comm] using
            mul_le_mul_of_nonneg_right h (sq_nonneg T))
        calc
          _ ≤ 6 * a i * (a i * T ^ 2) :=
            mul_le_mul_of_nonneg_left hD' (by positivity)
          _ ≤ _ := by
            nlinarith only [mul_nonneg (sq_nonneg T) (sq_nonneg (a i))]
      have hroot : Real.sqrt (6 * a i * D) ≤ (5 / 2 : ℝ) * T * a i :=
        (Real.sqrt_le_left (by positivity)).mpr hsquare
      calc
        _ ≤ a i * ((5 / 2 : ℝ) * T * a i) :=
          mul_le_mul_of_nonneg_left ((hlarge i hi h).trans hroot) hale
        _ = (5 / 2 * T) * a i ^ 2 := by ring
        _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hT0 hble)
    · calc
        _ ≤ T * b i := mul_le_mul_of_nonneg_right (le_of_not_ge h) hble
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
  calc
    _ ≤ ∑ i ∈ s, (T * b i + (5 / 2 * T) * a i ^ 2) := sum_le_sum pointwise
    _ = T * (∑ i ∈ s, b i) + (5 / 2 * T) * ∑ i ∈ s, a i ^ 2 := by
      rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ T * (2 * D) + (5 / 2 * T) * (2 * D) :=
      add_le_add (mul_le_mul_of_nonneg_left hB hT0)
        (mul_le_mul_of_nonneg_left hA (by positivity))
    _ = _ := by ring

/-- Lemma 7 on any finite sampling domain disjoint from all common edges.
The mass and squared-weight budget are separate inputs, for use with restricted
hypergraphs or other nonnegative edge weights. -/
theorem pairWeight_product_sum_le {E : Finset (Finset V)} (hE : Linear E)
    {a : Finset V → ℝ} (ha : ∀ e ∈ E, 0 ≤ a e)
    (hsize : ∀ e ∈ E, (e.card : ℝ) ≤ a e + 2)
    (S : Finset V) (u v : V)
    (havoid : ∀ e ∈ E, u ∈ e → v ∈ e → Disjoint S e)
    {D : ℝ} (hD : 1 ≤ D)
    (hbudgetU : ∑ e ∈ incident E u, a e ^ 2 ≤ 2 * D)
    (hbudgetV : ∑ e ∈ incident E v, a e ^ 2 ≤ 2 * D)
    (hmass : ∑ x ∈ S, pairWeight E a v x ≤ 2 * D) :
    ∑ x ∈ S, pairWeight E a u x * pairWeight E a v x ≤ 7 * D ^ (4 / 3 : ℝ) := by
  let F := (incident E u).filter (v ∉ ·)
  let b (e : Finset V) := ∑ x ∈ S.erase u ∩ e, pairWeight E a v x
  have hF : F ⊆ incident E u := filter_subset _ _
  have hn i : 0 ≤ pairWeight E a v i := pairWeight_nonneg ha v i
  have hb e : 0 ≤ b e := sum_nonneg (fun x _ => hn x)
  have hsum : ∑ x ∈ S, pairWeight E a u x * pairWeight E a v x =
      ∑ e ∈ F, a e * b e := by
    rw [weighted_pairWeight_sum, show F = (incident E u).filter (v ∉ ·) from rfl, sum_filter]
    refine sum_congr rfl (fun e he => ?_)
    obtain ⟨he, hue⟩ := mem_filter.mp he
    by_cases hv : v ∈ e
    · have hdisjoint : Disjoint (S.erase u) e :=
        (havoid e he hue hv).mono_left (erase_subset _ _)
      simp [hv, disjoint_iff_inter_eq_empty.mp hdisjoint]
    · simp [hv, b]
  have hbudgetF : ∑ e ∈ F, a e ^ 2 ≤ 2 * D :=
    (sum_le_sum_of_subset_of_nonneg hF (fun e _ _ => sq_nonneg (a e))).trans hbudgetU
  have hsumB : ∑ e ∈ F, b e ≤ 2 * D :=
    (sum_le_sum_of_subset_of_nonneg hF (fun e _ _ => hb e)).trans
      ((incident_inter_sum_le hE S u (fun x _ => hn x)).trans hmass)
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  let T : ℝ := D ^ (1 / 3 : ℝ)
  have hT : 1 ≤ T := Real.one_le_rpow hD (by norm_num)
  have hcube : T ^ 3 = D := by
    change (D ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = D
    rw [← Real.rpow_mul_natCast hD0]
    norm_num
  have hlarge (e : Finset V) (he : e ∈ F) (hTe : T ≤ a e) :
      b e ≤ Real.sqrt (6 * a e * D) := by
    obtain ⟨he, hv⟩ := mem_filter.mp he
    have heE := (mem_filter.mp he).1
    have hsub : b e ≤ ∑ x ∈ e, pairWeight E a v x :=
      sum_le_sum_of_subset_of_nonneg inter_subset_right (fun x _ _ => hn x)
    have heBound : (e.card : ℝ) ≤ 3 * a e := by linarith [hsize e heE]
    calc
      b e ≤ _ := hsub.trans (pairWeight_sum_le_sqrt hE a heE hv hbudgetV)
      _ ≤ _ := Real.sqrt_le_sqrt (by
        have scaled := mul_le_mul_of_nonneg_right heBound (show 0 ≤ 2 * D by positivity)
        nlinarith only [scaled])
  rw [hsum]
  calc
    _ ≤ 7 * (T * D) :=
      cutoff_product_sum_le F a b hT hcube.ge
        (fun e he => ha e (mem_filter.mp (hF he)).1) (fun e _ => hb e)
        hbudgetF hsumB hlarge
    _ = _ := by
      congr 1
      change D ^ (1 / 3 : ℝ) * D = D ^ (4 / 3 : ℝ)
      rw [show (4 / 3 : ℝ) = 1 / 3 + 1 by norm_num,
        Real.rpow_add (zero_lt_one.trans_le hD), Real.rpow_one]

end OMA.GeneralPositionCodegrees

/-! Specialize the real edge weights to the forbidden triples in the paper. -/

namespace OMA.GeneralPositionCodegrees

open scoped BigOperators
open Finset

variable {V : Type*} [DecidableEq V]

/-- Number of choices for the third point through two points of one edge. -/
def edgeExcess (e : Finset V) : ℝ :=
  (e.card - 2 : ℕ)

/-- The paper's pair codegree, extended by zero on the diagonal. -/
def codegree (E : Finset (Finset V)) (u v : V) : ℝ :=
  pairWeight E edgeExcess u v

/-- The degree in the 3-uniform hypergraph of forbidden triples, as an
incident-edge sum. In a linear family each forbidden triple has one edge. -/
def tripleDegree (E : Finset (Finset V)) (v : V) : ℕ :=
  ∑ e ∈ incident E v, (e.card - 1).choose 2

omit [DecidableEq V] in
theorem edgeExcess_nonneg (e : Finset V) : 0 ≤ edgeExcess e := by
  unfold edgeExcess
  positivity

omit [DecidableEq V] in
theorem card_le_edgeExcess_add_two (e : Finset V) :
    (e.card : ℝ) ≤ edgeExcess e + 2 := by
  change (e.card : ℝ) ≤ ((e.card - 2 : ℕ) : ℝ) + 2
  exact_mod_cast (show e.card ≤ (e.card - 2) + 2 by omega)

theorem codegree_nonneg (E : Finset (Finset V)) (u v : V) :
    0 ≤ codegree E u v :=
  pairWeight_nonneg (fun e _ => edgeExcess_nonneg e) u v

theorem twice_tripleDegree (E : Finset (Finset V)) (v : V) :
    2 * (tripleDegree E v : ℝ) =
      ∑ e ∈ incident E v, ((e.erase v).card : ℝ) * edgeExcess e := by
  rw [tripleDegree, Nat.cast_sum, mul_sum]
  refine sum_congr rfl (fun e he => ?_)
  have hv := (mem_filter.mp he).2
  rw [Nat.cast_choose_two, card_erase_of_mem hv]
  unfold edgeExcess
  by_cases hc : e.card = 1
  · simp [hc]
  · have hcard : 0 < e.card := card_pos.mpr ⟨v, hv⟩
    have hsub : 1 ≤ e.card - 1 := by omega
    rw [show e.card - 2 = e.card - 1 - 1 by omega, Nat.cast_sub hsub]
    push_cast
    ring

/-- The squared-edge budget in (2.1). -/
theorem edgeExcess_sq_sum_le_twice_tripleDegree (E : Finset (Finset V)) (v : V) :
    ∑ e ∈ incident E v, edgeExcess e ^ 2 ≤ 2 * (tripleDegree E v : ℝ) := by
  rw [twice_tripleDegree]
  refine sum_le_sum (fun e he => ?_)
  have hv := (mem_filter.mp he).2
  have hcard : edgeExcess e ≤ (e.erase v).card := by
    rw [edgeExcess, card_erase_of_mem hv]
    exact_mod_cast (show e.card - 2 ≤ e.card - 1 by omega)
  simpa [pow_two] using mul_le_mul_of_nonneg_right hcard (edgeExcess_nonneg e)

/-- The mass bound in (2.1), valid even when the sum is restricted to a subset. -/
theorem codegree_sum_le_twice_tripleDegree (E : Finset (Finset V)) (S : Finset V) (v : V) :
    ∑ x ∈ S, codegree E v x ≤ 2 * (tripleDegree E v : ℝ) := by
  calc
    _ = ∑ e ∈ incident E v, edgeExcess e * ((S.erase v ∩ e).card : ℝ) := by
      simpa [codegree, sum_const, nsmul_eq_mul] using
        weighted_pairWeight_sum E edgeExcess S v (fun _ => 1)
    _ ≤ _ := by
      rw [twice_tripleDegree]
      refine sum_le_sum (fun e _ => ?_)
      have hsub : S.erase v ∩ e ⊆ e.erase v := by
        intro x hx
        obtain ⟨hxS, hxe⟩ := mem_inter.mp hx
        exact mem_erase.mpr ⟨(mem_erase.mp hxS).1, hxe⟩
      have hcard : ((S.erase v ∩ e).card : ℝ) ≤ (e.erase v).card := by
        exact_mod_cast card_le_card hsub
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hcard (edgeExcess_nonneg e)

/-- The exact mass identity in (2.1) when the ambient set contains all edges. -/
theorem codegree_sum_eq_twice_tripleDegree {E : Finset (Finset V)} {S : Finset V}
    (hS : ∀ e ∈ E, e ⊆ S) (v : V) :
    ∑ x ∈ S, codegree E v x = 2 * (tripleDegree E v : ℝ) := by
  rw [twice_tripleDegree]
  calc
    _ = ∑ e ∈ incident E v, edgeExcess e * ((S.erase v ∩ e).card : ℝ) := by
      simpa [codegree, sum_const, nsmul_eq_mul] using
        weighted_pairWeight_sum E edgeExcess S v (fun _ => 1)
    _ = _ := by
      refine sum_congr rfl (fun e he => ?_)
      have hSe : S.erase v ∩ e = e.erase v := by
        ext x
        simp only [mem_inter, mem_erase]
        exact ⟨fun ⟨⟨hn, _⟩, hx⟩ => ⟨hn, hx⟩,
          fun ⟨hn, hx⟩ => ⟨⟨hn, hS e (mem_filter.mp he).1 hx⟩, hx⟩⟩
      rw [hSe, mul_comm]

/-- Lemma 6 with the paper's triple degree budget. -/
theorem codegree_sum_le_sqrt {E : Finset (Finset V)} (hE : Linear E)
    {B : Finset V} (hB : B ∈ E) {v : V} (hv : v ∉ B)
    {D : ℝ} (hdeg : (tripleDegree E v : ℝ) ≤ D) :
    ∑ x ∈ B, codegree E v x ≤ Real.sqrt (2 * B.card * D) :=
  pairWeight_sum_le_sqrt hE edgeExcess hB hv
    ((edgeExcess_sq_sum_le_twice_tripleDegree E v).trans
      (mul_le_mul_of_nonneg_left hdeg (by norm_num)))

/-- Lemma 7 with the paper's triple degree budget, on any domain avoiding all
edges through the two endpoints. This includes the case of no common edge. -/
theorem codegree_product_sum_le {E : Finset (Finset V)} (hE : Linear E)
    (S : Finset V) (u v : V)
    (havoid : ∀ e ∈ E, u ∈ e → v ∈ e → Disjoint S e)
    {D : ℝ} (hD : 1 ≤ D)
    (hu : (tripleDegree E u : ℝ) ≤ D) (hv : (tripleDegree E v : ℝ) ≤ D) :
    ∑ x ∈ S, codegree E u x * codegree E v x ≤ 7 * D ^ (4 / 3 : ℝ) :=
  pairWeight_product_sum_le hE (fun e _ => edgeExcess_nonneg e)
    (fun e _ => card_le_edgeExcess_add_two e) S u v havoid hD
    ((edgeExcess_sq_sum_le_twice_tripleDegree E u).trans
      (mul_le_mul_of_nonneg_left hu (by norm_num)))
    ((edgeExcess_sq_sum_le_twice_tripleDegree E v).trans
      (mul_le_mul_of_nonneg_left hv (by norm_num)))
    ((codegree_sum_le_twice_tripleDegree E S v).trans
      (mul_le_mul_of_nonneg_left hv (by norm_num)))

/-- Lemma 7 in the common-edge case, summing outside that edge. -/
theorem codegree_product_sum_sdiff_le {E : Finset (Finset V)} (hE : Linear E)
    (S : Finset V) {B : Finset V} (hB : B ∈ E) {u v : V}
    (huv : u ≠ v) (huB : u ∈ B) (hvB : v ∈ B)
    {D : ℝ} (hD : 1 ≤ D)
    (hu : (tripleDegree E u : ℝ) ≤ D) (hv : (tripleDegree E v : ℝ) ≤ D) :
    ∑ x ∈ S \ B, codegree E u x * codegree E v x ≤ 7 * D ^ (4 / 3 : ℝ) := by
  refine codegree_product_sum_le hE _ _ _ (fun e he hue hve => ?_) hD hu hv
  rw [hE.edge_eq_of_pair he hB huv hue huB hve hvB]
  exact disjoint_left.mpr (fun _ hx => (mem_sdiff.mp hx).2)

end OMA.GeneralPositionCodegrees

namespace OMA.GeneralPositionSelection

open Finset
open OMA.GeneralPositionCodegrees
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

def edgeTriples (B : Finset α) (v : α) : Finset (Finset α) :=
  (B.powersetCard 3).filter (v ∈ ·)

theorem mem_edgeTriples {v : α} {B T : Finset α} :
    T ∈ edgeTriples B v ↔ T ⊆ B ∧ T.card = 3 ∧ v ∈ T := by
  simp only [edgeTriples, mem_filter, mem_powersetCard, and_assoc]

def incidentTriples (E : Finset (Finset α)) (v : α) : Finset (Finset α) :=
  (incident E v).biUnion (edgeTriples · v)

theorem mem_incidentTriples {E : Finset (Finset α)} {v : α} {T : Finset α} :
    T ∈ incidentTriples E v ↔ ∃ B ∈ E, T ⊆ B ∧ T.card = 3 ∧ v ∈ T := by
  simp only [incidentTriples, mem_biUnion, incident, mem_filter, mem_edgeTriples]
  constructor
  · rintro ⟨B, ⟨hB, _⟩, hT⟩
    exact ⟨B, hB, hT⟩
  · rintro ⟨B, hB, hTB, hT, hv⟩
    exact ⟨B, ⟨hB, hTB hv⟩, hTB, hT, hv⟩

theorem card_incidentTriples {E : Finset (Finset α)} (hE : Linear E) (v : α) :
    (incidentTriples E v).card = tripleDegree E v := by
  rw [incidentTriples, card_biUnion, tripleDegree]
  · refine sum_congr rfl fun B hB => ?_
    have hv := (mem_filter.mp hB).2
    simpa only [edgeTriples, singleton_subset_iff, card_singleton] using
      (card_filter_powersetCard_subset ({v} : Finset α) B 3
        (singleton_subset_iff.mpr hv) (by simp))
  · intro B hB C hC hBC
    change Disjoint (edgeTriples B v) (edgeTriples C v)
    rw [disjoint_left]
    intro T hTB hTC
    obtain ⟨hsubB, hcard, hv⟩ := mem_edgeTriples.mp hTB
    have hsubC := (mem_edgeTriples.mp hTC).1
    obtain ⟨x, hxT, hxv⟩ : ∃ x ∈ T, x ≠ v := by
      by_contra! hnone
      have hle := card_le_card (show T ⊆ {v} from fun x hx =>
        mem_singleton.mpr (hnone x hx))
      simp only [hcard, card_singleton] at hle
      omega
    exact hBC (hE.edge_eq_of_pair (mem_filter.mp hB).1 (mem_filter.mp hC).1 hxv
      (hsubB hxT) (hsubC hxT) (hsubB hv) (hsubC hv))

def trace (E : Finset (Finset α)) (S : Finset α) : Finset (Finset α) :=
  (E.image (· ∩ S)).filter (fun B => 3 ≤ B.card)

theorem mem_trace {E : Finset (Finset α)} {S B : Finset α} :
    B ∈ trace E S ↔ (∃ C ∈ E, C ∩ S = B) ∧ 3 ≤ B.card := by
  simp only [trace, mem_filter, mem_image]

theorem linear_trace {E : Finset (Finset α)} (hE : Linear E) (S : Finset α) :
    Linear (trace E S) := by
  intro B hB C hC hne
  obtain ⟨⟨B', hB', rfl⟩, _⟩ := mem_trace.mp hB
  obtain ⟨⟨C', hC', rfl⟩, _⟩ := mem_trace.mp hC
  have hne' : B' ≠ C' := fun h => hne (congrArg (· ∩ S) h)
  exact (card_le_card (inter_subset_inter inter_subset_left inter_subset_left)).trans
    (hE B' hB' C' hC' hne')

theorem incidentTriples_trace {E : Finset (Finset α)} {S : Finset α} (v : α) :
    incidentTriples (trace E S) v = (incidentTriples E v).filter (· ⊆ S) := by
  ext T
  simp only [mem_filter, mem_incidentTriples]
  constructor
  · rintro ⟨B, hB, hTB, hT, hv⟩
    obtain ⟨⟨C, hC, rfl⟩, _⟩ := mem_trace.mp hB
    exact ⟨⟨C, hC, hTB.trans inter_subset_left, hT, hv⟩, hTB.trans inter_subset_right⟩
  · rintro ⟨⟨B, hB, hTB, hT, hv⟩, hTS⟩
    have hsub : T ⊆ B ∩ S := subset_inter hTB hTS
    have hcard := card_le_card hsub
    rw [hT] at hcard
    exact ⟨B ∩ S, mem_trace.mpr ⟨⟨B, hB, rfl⟩, hcard⟩, hsub, hT, hv⟩

set_option maxHeartbeats 800000 in
theorem trace_degree_of_retained {E : Finset (Finset α)} (hE : Linear E)
    {S : Finset α} {D p t : ℝ} {v : α}
    (hv : v ∈ retained D p t E (incidentTriples E) S) :
    (tripleDegree (trace E (retained D p t E (incidentTriples E) S)) v : ℝ)
      ≤ 20 * p ^ 2 * D := by
  let R := retained D p t E (incidentTriples E) S
  have hR : R ⊆ S := filter_subset _ _
  have hbound := (mem_filter.mp hv).2.1
  rw [← card_incidentTriples (linear_trace hE R), incidentTriples_trace]
  have hsub : ((incidentTriples E v).filter (· ⊆ R)) ⊆
      ((incidentTriples E v).filter (· ⊆ S)) := by
    intro T hT
    obtain ⟨hTE, hTR⟩ := mem_filter.mp hT
    exact mem_filter.mpr ⟨hTE, hTR.trans hR⟩
  exact (Nat.cast_le.mpr (card_le_card hsub)).trans hbound

theorem trace_card_of_retained {E : Finset (Finset α)} {S : Finset α}
    {D p t : ℝ} {B : Finset α}
    (hB : B ∈ trace E (retained D p t E (incidentTriples E) S)) :
    (B.card : ℝ) ≤ 3 * t + 1 := by
  obtain ⟨⟨C, hC, rfl⟩, hc⟩ := mem_trace.mp hB
  obtain ⟨v, hv⟩ := card_pos.mp (show 0 < (C ∩ retained D p t E (incidentTriples E) S).card by omega)
  obtain ⟨hvC, hvR⟩ := mem_inter.mp hv
  have hcut := (mem_filter.mp hvR).2.2 C hC hvC
  rw [← card_erase_add_one hv, Nat.cast_add, Nat.cast_one]
  refine add_le_add (le_trans (Nat.cast_le.mpr (card_le_card ?_)) hcut) le_rfl
  intro x hx
  obtain ⟨hne, hx⟩ := mem_erase.mp hx
  obtain ⟨hxC, hxR⟩ := mem_inter.mp hx
  exact mem_inter.mpr ⟨(mem_filter.mp hxR).1, mem_erase.mpr ⟨hne, hxC⟩⟩

end OMA.GeneralPositionSelection

/-! The live, pre-turn potential of Lemma 9 in §2.3 of Thang Pham,
Le Quang-Ham and Boqing Xue, "General-position sets and linear hypergraphs",
arXiv:2610.34254v1. -/

namespace OMA.GeneralPositionPotential
open Finset OMA.OnlineSelection OMA.OnlineSelection.HypergraphState
open OMA.GeneralPositionProducts

variable {V : Type*} [DecidableEq V]

/-- Vertices of B still awaiting processing, except for the tracked vertex v. -/
def unprocessed (s : HypergraphState V) (v : V) (B : Finset V) : Finset V :=
  (s.remaining ∩ B).erase v

def mass (s : HypergraphState V) (v : V) (B : Finset V) : ℝ :=
  ∑ u ∈ unprocessed s v B, s.weight u

noncomputable def edgeG (s : HypergraphState V) (v : V) (σ : ℝ) (B : Finset V) : ℝ :=
  edgeProduct (unprocessed s v B) s.weight σ

def edgePhi (s : HypergraphState V) (v : V) (B : Finset V) : ℝ :=
  if (s.selected ∩ B).card = 0 then 2 * pairSum (unprocessed s v B) s.weight
  else 2 * mass s v B

noncomputable def sumG (E : Finset (Finset V)) (s : HypergraphState V) (v : V) (σ : ℝ) : ℝ :=
  ∑ B ∈ E.filter (v ∈ ·), edgeG s v σ B

def sumPhi (E : Finset (Finset V)) (s : HypergraphState V) (v : V) : ℝ :=
  ∑ B ∈ E.filter (v ∈ ·), edgePhi s v B

/-- The caller supplies the history flag before v's turn. A dead history or
an absent vertex contributes zero. -/
noncomputable def potential (live : Bool) (E : Finset (Finset V)) (s : HypergraphState V) (v : V)
    (a τ σ lam : ℝ) : ℝ :=
  if live = true ∧ v ∈ s.remaining then
    s.weight v * max (1 - lam * sumG E s v σ -
      (Real.log (s.weight v/a) + sumPhi E s v) / Real.log (τ/a)) 0
  else 0

/-- The positive floor is needed for nonnegativity of log(z_v/a). -/
def WeightFloor (a : ℝ) (s : HypergraphState V) : Prop :=
  ∀ u, s.weight u = 0 ∨ a ≤ s.weight u

omit [DecidableEq V] in
theorem initial_floor (Q : Finset V) (a : ℝ) : WeightFloor a (initial Q a) :=
  fun _ => Or.inr le_rfl

theorem advance_floor {E : Finset (Finset V)} {τ a : ℝ} (hτ : 0 ≤ τ)
    (hτ1 : τ < 1) (haτ : a ≤ τ) {s : HypergraphState V} (hs : WeightsIn τ s)
    (hf : WeightFloor a s) (x : V) (b : Bool) : WeightFloor a (advance E τ x b s) :=
  fun u => updateWeight_zero_or_ge hτ hτ1 haτ hs x b (hf u)

theorem edgePhi_nonneg (s : HypergraphState V) (v : V) (B : Finset V)
    (hw : ∀ u, 0 ≤ s.weight u) : 0 ≤ edgePhi s v B := by
  unfold edgePhi
  split
  · exact mul_nonneg (by norm_num) (sum_nonneg fun P _ => prod_nonneg fun u _ => hw u)
  · exact mul_nonneg (by norm_num) (sum_nonneg fun u _ => hw u)

theorem edgeG_pos (s : HypergraphState V) (v : V) (B : Finset V) {σ : ℝ} (hσ : 0 < σ)
    (hw : ∀ u, 0 ≤ s.weight u) : 0 < edgeG s v σ B :=
  prod_pos fun u _ => add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (hw u) hσ.le)

/-- The factorwise inequality log(1+t) ≥ t/2 for 0≤t≤1, summed over U_B. -/
theorem mass_le_log_product (s : HypergraphState V) (v : V) (B : Finset V) {τ σ : ℝ}
    (hs : WeightsIn τ s) (hτσ : τ ≤ σ) (hσ : 0 < σ) :
    mass s v B / (2*σ) ≤ Real.log (edgeG s v σ B) := by
  have hlog (u : V) : (s.weight u/σ)/2 ≤ Real.log (1+s.weight u/σ) := by
    have ht := div_nonneg (hs u).1 hσ.le
    have h₁ : s.weight u/σ ≤ 1 := (div_le_one hσ).mpr ((hs u).2.trans hτσ)
    apply le_trans _ (Real.le_log_one_add_of_nonneg ht)
    apply (le_div_iff₀ (by linarith : 0 < s.weight u/σ + 2)).mpr
    nlinarith [mul_nonneg ht (sub_nonneg.mpr h₁)]
  unfold edgeG edgeProduct
  rw [Real.log_prod (fun u _ => (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (hs u).1 hσ.le)).ne')]
  calc
    _ = ∑ u ∈ unprocessed s v B, (s.weight u/σ)/2 := by
      unfold mass
      rw [← sum_div, ← sum_div]
      ring
    _ ≤ _ := sum_le_sum fun u _ => hlog u

/-- All local consequences of a positive pre-turn potential. The bound on lamG
is strict, so its weak form is available by .le. -/
theorem positive_consequences {live : Bool} {E : Finset (Finset V)} {s : HypergraphState V}
    {v : V} {a τ σ η lam : ℝ} (ha : 0 < a) (haτ : a < τ) (hτσ : τ ≤ σ)
    (hlam : lam = Real.exp (-(η/(2*σ)))) (hs : WeightsIn τ s) (hf : WeightFloor a s)
    (hC : 0 < potential live E s v a τ σ lam) :
    live = true ∧ v ∈ s.remaining ∧ 0 < s.weight v ∧ s.weight v < τ ∧
      (∀ B ∈ E, v ∈ B → mass s v B < η ∧ lam * edgeG s v σ B < 1) := by
  classical
  have hτ := ha.trans haτ
  have hσ := hτ.trans_le hτσ
  have hΛ : 0 < Real.log (τ/a) := Real.log_pos ((one_lt_div ha).mpr haτ)
  have hlampos : 0 < lam := hlam ▸ Real.exp_pos _
  have hactive : live = true ∧ v ∈ s.remaining := by
    by_contra h
    simp [potential, h] at hC
  rw [potential, if_pos hactive] at hC
  have hv : 0 < s.weight v := by
    by_contra! h
    rw [le_antisymm h (hs v).1, zero_mul] at hC
    exact hC.false
  have hfloor := (hf v).resolve_left hv.ne'
  have hlog : 0 ≤ Real.log (s.weight v/a) := Real.log_nonneg ((one_le_div ha).mpr hfloor)
  have hphi : 0 ≤ sumPhi E s v := sum_nonneg fun B _ => edgePhi_nonneg s v B fun u => (hs u).1
  have hG : 0 ≤ sumG E s v σ := sum_nonneg fun B _ => (edgeG_pos s v B hσ fun u => (hs u).1).le
  have hbr : 0 < 1 - lam * sumG E s v σ -
      (Real.log (s.weight v/a) + sumPhi E s v) / Real.log (τ/a) := by
    by_contra! hn
    rw [max_eq_right hn, mul_zero] at hC
    exact hC.false
  have hcost := mul_nonneg hlampos.le hG
  have hfrac := div_nonneg (add_nonneg hlog hphi) hΛ.le
  have hcost_lt : lam * sumG E s v σ < 1 := by linarith
  have hfrac_lt : (Real.log (s.weight v/a) + sumPhi E s v) / Real.log (τ/a) < 1 := by linarith
  have hl := (div_lt_one hΛ).mp hfrac_lt
  have hvτ : s.weight v < τ := by
    apply (div_lt_div_iff_of_pos_right ha).mp
    exact (Real.log_lt_log_iff (div_pos hv ha) (div_pos hτ ha)).mp (by linarith)
  refine ⟨hactive.1, hactive.2, hv, hvτ, ?_⟩
  intro B hB hvB
  have hGB := edgeG_pos s v B hσ fun u => (hs u).1
  have hle : edgeG s v σ B ≤ sumG E s v σ := single_le_sum
    (fun D _ => (edgeG_pos s v D hσ fun u => (hs u).1).le) (mem_filter.mpr ⟨hB,hvB⟩)
  have hbound := (mul_le_mul_of_nonneg_left hle hlampos.le).trans_lt hcost_lt
  refine ⟨?_, hbound⟩
  by_contra! hlarge
  have hlogG := (div_le_div_of_nonneg_right hlarge (by positivity : 0 ≤ 2*σ)).trans
    (mass_le_log_product s v B hs hτσ hσ)
  have he : 1 ≤ lam * edgeG s v σ B := by
    rw [hlam, ← Real.exp_log hGB, ← Real.exp_add]
    exact Real.one_le_exp (by linarith)
  exact (not_lt_of_ge he) hbound

/-- On a safe state the nonzero-weight tracked vertex sees only edge counts
zero and one, so edgePhi agrees with the relevant branch of the paper. -/
theorem selected_card_le_one {E : Finset (Finset V)} {s : HypergraphState V}
    (hsafe : Safe E s) {v : V} (hv : v ∈ s.remaining) (hw : 0 < s.weight v)
    {B : Finset V} (hB : B ∈ E) (hvB : v ∈ B) : (s.selected ∩ B).card ≤ 1 := by
  have h := hsafe.independent B hB
  by_contra! ht
  exact hw.ne' (hsafe.saturated B hB (by omega) v hv hvB)

end OMA.GeneralPositionPotential

namespace OMA.GeneralPositionPotential
open Finset OMA.OnlineSelection OMA.OnlineSelection.HypergraphState
open OMA.GeneralPositionProducts
variable {V : Type*} [DecidableEq V]

theorem initial_unprocessed {Q B : Finset V} (hB : B ⊆ Q) (v : V) (a : ℝ) :
    unprocessed (initial Q a) v B = B.erase v := by
  simp [unprocessed, initial, inter_eq_right.mpr hB]

/-- Conditional initial Φ-sum exactly equals 2a² times the incident triple
degree, using the same incident-edge sum as the codegree and restriction ports. -/
theorem initial_sumPhi {Q : Finset V} {E : Finset (Finset V)} (hE : ∀ B ∈ E, B ⊆ Q)
    (v : V) (a : ℝ) :
    sumPhi E (initial Q a) v = 2*a^2 *
      ((∑ B ∈ E.filter (v ∈ ·), (B.card-1).choose 2 : ℕ) : ℝ) := by
  unfold sumPhi
  rw [Nat.cast_sum, mul_sum]
  apply sum_congr rfl
  intro B hB
  obtain ⟨he,hv⟩ := mem_filter.mp hB
  simp only [edgePhi, unprocessed, initial, inter_eq_right.mpr (hE B he), empty_inter, card_empty,
    if_true, pairSum]
  have hsum : (∑ P ∈ (B.erase v).powersetCard 2, ∏ _u ∈ P, a) =
      ∑ _P ∈ (B.erase v).powersetCard 2, a^2 := by
    exact sum_congr rfl fun P hP => by rw [prod_const, (mem_powersetCard.mp hP).2]
  rw [hsum, sum_const, nsmul_eq_mul, card_powersetCard, card_erase_of_mem hv]
  ring

/-- Initially the number of incident edges is at most the triple degree if
each edge has size at least three, as in the pruned trace family. -/
theorem incident_card_le_degree (E : Finset (Finset V)) (v : V)
    (hsize : ∀ B ∈ E, 3 ≤ B.card) :
    (E.filter (v ∈ ·)).card ≤ ∑ B ∈ E.filter (v ∈ ·), (B.card-1).choose 2 := by
  calc
    _ = ∑ _B ∈ E.filter (v ∈ ·), 1 := by simp
    _ ≤ _ := by
      apply sum_le_sum
      intro B hB
      have hb := hsize B (mem_filter.mp hB).1
      exact Nat.choose_pos (by omega)

/-- The exponential initial G cost, expressed in the scalar parameters of
the paper. The size input is the number of other vertices of each edge. -/
theorem initial_sumG_le {Q : Finset V} {E : Finset (Finset V)} (hE : ∀ B ∈ E, B ⊆ Q)
    (v : V) {a σ η lam D : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ)
    (hlam : lam = Real.exp (-(η/(2*σ))))
    (hsize : ∀ B ∈ E, v ∈ B → a * (B.erase v).card ≤ η/4)
    (hcount : ((E.filter (v ∈ ·)).card : ℝ) ≤ D) :
    lam * sumG E (initial Q a) v σ ≤ D * Real.exp (-(η/(4*σ))) := by
  classical
  have hbound (B) (hB : B ∈ E.filter (v ∈ ·)) :
      edgeG (initial Q a) v σ B ≤ Real.exp (η/(4*σ)) := by
    obtain ⟨he,hv⟩ := mem_filter.mp hB
    rw [edgeG, initial_unprocessed (hE B he)]
    change (∏ _ ∈ B.erase v, (1+a/σ)) ≤ _
    apply le_trans (Real.prod_one_add_le_exp_sum (B.erase v) (f := fun _ => a/σ)
      (fun _ => div_nonneg ha hσ.le))
    apply Real.exp_le_exp.mpr
    rw [sum_const, nsmul_eq_mul]
    calc
      _ = a * (B.erase v).card / σ := by ring
      _ ≤ (η/4)/σ := div_le_div_of_nonneg_right (hsize B he hv) hσ.le
      _ = _ := by ring
  have hsum : sumG E (initial Q a) v σ ≤ (E.filter (v ∈ ·)).card * Real.exp (η/(4*σ)) := by
    calc
      _ ≤ ∑ _B ∈ E.filter (v ∈ ·), Real.exp (η/(4*σ)) := sum_le_sum hbound
      _ = _ := by simp
  have hpos : 0 ≤ lam := hlam ▸ (Real.exp_pos _).le
  calc
    _ ≤ lam * (D * Real.exp (η/(4*σ))) := mul_le_mul_of_nonneg_left
      (hsum.trans (mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le)) hpos
    _ = _ := by
      rw [hlam, mul_left_comm, ← Real.exp_add]
      congr 2
      ring

/-- Finite part of the 3a/4 initial lower bound. Only the scalar cost
estimates remain as hypotheses, with the exact exponents from §2.3. -/
theorem initial_potential_lower {Q : Finset V} {E : Finset (Finset V)} {v : V} (hv : v ∈ Q)
    (hE : ∀ B ∈ E, B ⊆ Q) (hthree : ∀ B ∈ E, 3 ≤ B.card)
    {a τ σ η lam D : ℝ} (ha : 0 < a) (haτ : a < τ) (hσ : 0 < σ)
    (hlam : lam = Real.exp (-(η/(2*σ))))
    (hsize : ∀ B ∈ E, v ∈ B → a * (B.erase v).card ≤ η/4)
    (hdegree : ((∑ B ∈ E.filter (v ∈ ·), (B.card-1).choose 2 : ℕ) : ℝ) ≤ D)
    (hscalar : D * Real.exp (-(η/(4*σ))) + (2*a^2*D)/Real.log (τ/a) ≤ 1/4) :
    3*a/4 ≤ potential true E (initial Q a) v a τ σ lam := by
  have hcount : ((E.filter (v ∈ ·)).card : ℝ) ≤ D :=
    (Nat.cast_le.mpr (incident_card_le_degree E v hthree)).trans hdegree
  have hG := initial_sumG_le hE v ha.le hσ hlam hsize hcount
  have hΛ : 0 < Real.log (τ/a) := Real.log_pos ((one_lt_div ha).mpr haτ)
  have hphi : sumPhi E (initial Q a) v / Real.log (τ/a) ≤ (2*a^2*D)/Real.log (τ/a) := by
    rw [initial_sumPhi hE]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdegree (by positivity)) hΛ.le
  rw [potential, if_pos (show true = true ∧ v ∈ (initial Q a).remaining from ⟨rfl,hv⟩)]
  change _ ≤ a * max (1-lam*sumG E (initial Q a) v σ -
    (Real.log (a/a) + sumPhi E (initial Q a) v)/Real.log (τ/a)) 0
  rw [div_self ha.ne', Real.log_one, zero_add]
  calc
    _ = a * (3/4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ((by linarith : (3/4 : ℝ) ≤
      1-lam*sumG E (initial Q a) v σ - sumPhi E (initial Q a) v / Real.log (τ/a)).trans
      (le_max_left _ _)) ha.le

end OMA.GeneralPositionPotential

/-! Connect the pre-turn potential to the finite sample and retained trace
of Section 2.3. The size and degree bounds are obtained from the actual sample. -/

namespace OMA.GeneralPositionPotential
open Finset OMA.OnlineSelection OMA.OnlineSelection.HypergraphState
open OMA.GeneralPositionSelection OMA.GeneralPositionCodegrees
open scoped Classical

variable {V : Type*} [DecidableEq V]

theorem retained_initial_lower {S : Finset V} {E : Finset (Finset V)} (hE : Linear E)
    {D p t a τ σ η lam : ℝ} {v : V} (hv : v ∈ retained D p t E (incidentTriples E) S)
    (ha : 0 < a) (haτ : a < τ) (hσ : 0 < σ) (hlam : lam = Real.exp (-(η/(2*σ))))
    (hsize : a * (3*t+1) ≤ η/4)
    (hscalar : (20*p^2*D) * Real.exp (-(η/(4*σ))) +
      (2*a^2*(20*p^2*D))/Real.log (τ/a) ≤ 1/4) :
    let Q := retained D p t E (incidentTriples E) S
    3*a/4 ≤ potential true (trace E Q) (initial Q a) v a τ σ lam := by
  let Q := retained D p t E (incidentTriples E) S
  change 3*a/4 ≤ potential true (trace E Q) (initial Q a) v a τ σ lam
  apply initial_potential_lower (D := 20*p^2*D) hv _ _ ha haτ hσ hlam _ _ hscalar
  · intro B hB
    obtain ⟨⟨C, _, rfl⟩, _⟩ := mem_trace.mp hB
    exact inter_subset_right
  · intro B hB
    exact (mem_trace.mp hB).2
  · intro B hB _
    have hc : ((B.erase v).card : ℝ) ≤ 3*t+1 :=
      (Nat.cast_le.mpr (card_le_card (erase_subset v B))).trans (trace_card_of_retained hB)
    exact (mul_le_mul_of_nonneg_left hc ha.le).trans hsize
  · exact trace_degree_of_retained hE hv

/-- Averaging only at the initial state gives 3pa/8. This is before the
fixed-order selection and uses no estimate on any subsequent loss. -/
theorem sampled_initial_lower {U : Finset V} {E : Finset (Finset V)} (hE : Linear E)
    {D p t a τ σ η lam : ℝ} {v : V} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ha : 0 < a) (haτ : a < τ) (hσ : 0 < σ) (hlam : lam = Real.exp (-(η/(2*σ))))
    (hsize : a * (3*t+1) ≤ η/4)
    (hscalar : (20*p^2*D)*Real.exp (-(η/(4*σ))) + (2*a^2*(20*p^2*D))/Real.log (τ/a) ≤ 1/4)
    (hretain : p/2 ≤ sampleMass p U (v ∈ retained D p t E (incidentTriples E) ·)) :
    3*p*a/8 ≤ ∑ S ∈ U.powerset, sampleWeight p U S *
      (let Q := retained D p t E (incidentTriples E) S
       potential true (trace E Q) (initial Q a) v a τ σ lam) := by
  classical
  let Q := retained D p t E (incidentTriples E)
  calc
    _ = (3*a/4)*(p/2) := by ring
    _ ≤ (3*a/4)*sampleMass p U (v ∈ Q ·) := mul_le_mul_of_nonneg_left hretain (by positivity)
    _ = ∑ S ∈ U.powerset, if v ∈ Q S then sampleWeight p U S*(3*a/4) else 0 := by
      rw [sampleMass, mul_sum, sum_filter]
      apply sum_congr rfl
      intro S _
      split <;> simp_all [mul_comm]
    _ ≤ _ := by
      apply sum_le_sum
      intro S _
      have hw := sample_nonneg hp hp1 U S
      by_cases hv : v ∈ Q S
      · rw [if_pos hv]
        exact mul_le_mul_of_nonneg_left (retained_initial_lower hE hv ha haτ hσ hlam hsize hscalar) hw
      · rw [if_neg hv]
        have hzero : potential true (trace E (Q S)) (initial (Q S) a) v a τ σ lam = 0 := by
          simp [potential, initial, hv]
        change 0 ≤ sampleWeight p U S * potential true (trace E (Q S)) (initial (Q S) a) v a τ σ lam
        rw [hzero, mul_zero]

end OMA.GeneralPositionPotential

namespace OMA.GeneralPositionPotential
open Finset OMA.OnlineSelection OMA.OnlineSelection.HypergraphState
open OMA.GeneralPositionSelection OMA.GeneralPositionCodegrees
open scoped Classical

variable {V : Type*} [DecidableEq V]

/-- The unconditional 3pa/8 bound directly from the original hypergraph and
the paper's scalar inequalities, using its Bernoulli sample and actual prune. -/
theorem initial_expectation {U : Finset V} {E : Finset (Finset V)} (hE : Linear E)
    {D p t a τ σ η lam : ℝ} {v : V} (hv : v ∈ U)
    (hD : 0 < D) (hp : 0 < p) (hp1 : p ≤ 1)
    (ha : 0 < a) (haτ : a < τ) (hσ : 0 < σ) (hlam : lam = Real.exp (-(η/(2*σ))))
    (hedges : ∀ B ∈ E, B ⊆ U ∧ 3 ≤ B.card ∧ p*B.card ≤ t)
    (hdeg : (tripleDegree E v : ℝ) ≤ D)
    (hsmall : D*Real.exp (-t/2) ≤ 1/4) (hsize : a*(3*t+1) ≤ η/4)
    (hscalar : (20*p^2*D)*Real.exp (-(η/(4*σ))) + (2*a^2*(20*p^2*D))/Real.log (τ/a) ≤ 1/4) :
    3*p*a/8 ≤ ∑ S ∈ U.powerset, sampleWeight p U S *
      (let Q := retained D p t E (incidentTriples E) S
       potential true (trace E Q) (initial Q a) v a τ σ lam) := by
  apply sampled_initial_lower hE hp.le hp1 ha haτ hσ hlam hsize hscalar
  apply sample_retained_vertex hp hp1 hD hv _ _ _ _ hsmall
  · intro T hT
    obtain ⟨B,hB,hsub,hcard,_⟩ := mem_incidentTriples.mp hT
    exact ⟨hsub.trans (hedges B hB).1,hcard⟩
  · rwa [card_incidentTriples hE]
  · exact fun B hB => ⟨(hedges B hB).1,(hedges B hB).2.2⟩
  · exact (Nat.cast_le.mpr (incident_card_le_degree E v (fun B hB => (hedges B hB).2.1))).trans hdeg

/-- At a vertex's own processing step the selection indicator has mean
z_v, which dominates the old live potential. The same holds if the vertex
is dead or absent. -/
theorem potential_le_weight {E : Finset (Finset V)} {s : HypergraphState V} (live : Bool)
    (v : V) {a τ σ lam : ℝ} (ha : 0 < a) (haτ : a < τ) (hσ : 0 < σ)
    (hlam : 0 ≤ lam) (hs : WeightsIn τ s) (hf : WeightFloor a s) :
    0 ≤ potential live E s v a τ σ lam ∧ potential live E s v a τ σ lam ≤ s.weight v := by
  rw [potential]
  split
  · by_cases hv : s.weight v = 0
    · simp [hv]
    have hlog := Real.log_nonneg ((one_le_div ha).mpr ((hf v).resolve_left hv))
    have hΛ := Real.log_pos ((one_lt_div ha).mpr haτ)
    have hG : 0 ≤ sumG E s v σ := sum_nonneg (fun B _ => (edgeG_pos s v B hσ (fun u => (hs u).1)).le)
    have hΦ : 0 ≤ sumPhi E s v := sum_nonneg (fun B _ => edgePhi_nonneg s v B (fun u => (hs u).1))
    have hcost := mul_nonneg hlam hG
    have hfrac := div_nonneg (add_nonneg hlog hΦ) hΛ.le
    exact ⟨mul_nonneg (hs v).1 (le_max_right _ _),
      mul_le_of_le_one_right (hs v).1 (max_le (by linarith) zero_le_one)⟩
  · exact ⟨le_rfl,(hs v).1⟩

end OMA.GeneralPositionPotential

/-! The ordered six-vertex configurations and cardinality bound of Lemma 8. -/

namespace OMA.GeneralPositionCodegrees

open scoped BigOperators
open Finset

variable {V : Type*} [DecidableEq V]

/-- Possible third vertices of a forbidden triple through u and x. -/
def link (E : Finset (Finset V)) (u x : V) : Finset V :=
  if u = x then ∅ else
    ((incident E u).filter (x ∈ ·)).biUnion (fun e => (e.erase u).erase x)

theorem mem_link {E : Finset (Finset V)} {u x y : V} :
    y ∈ link E u x ↔
      u ≠ x ∧ y ≠ u ∧ y ≠ x ∧ ∃ e ∈ E, u ∈ e ∧ x ∈ e ∧ y ∈ e := by
  by_cases h : u = x
  · simp [link, h]
  · rw [link, if_neg h, mem_biUnion]
    simp only [incident, mem_filter, mem_erase]
    constructor
    · rintro ⟨e, ⟨⟨he, hu⟩, hx⟩, hyx, hyu, hy⟩
      exact ⟨h, hyu, hyx, e, he, hu, hx, hy⟩
    · rintro ⟨_, hyu, hyx, e, he, hu, hx, hy⟩
      exact ⟨e, ⟨⟨he, hu⟩, hx⟩, hyx, hyu, hy⟩

theorem codegree_eq_card_link {E : Finset (Finset V)} (hE : Linear E) (u x : V) :
    codegree E u x = (link E u x).card := by
  by_cases h : u = x
  · simp [link, codegree, pairWeight, h]
  · rcases eq_empty_or_nonempty ((incident E u).filter (x ∈ ·)) with hs | ⟨e, he⟩
    · simp [link, codegree, pairWeight, h, hs]
    · have hs := common_eq_singleton hE h he
      obtain ⟨heInc, hxe⟩ := mem_filter.mp he
      have hue := (mem_filter.mp heInc).2
      have hx' : x ∈ e.erase u := mem_erase.mpr ⟨fun eq => h eq.symm, hxe⟩
      rw [link, if_neg h, hs, singleton_biUnion, card_erase_of_mem hx',
        card_erase_of_mem hue, codegree, pairWeight, if_neg h, hs, sum_singleton, edgeExcess]
      congr 1

/-- A third vertex on an edge through an exterior point is outside the anchor
edge, by uniqueness of the edge through any distinct pair. -/
theorem link_disjoint_edge {E : Finset (Finset V)} (hE : Linear E)
    {B : Finset V} (hB : B ∈ E) {u x : V} (hu : u ∈ B) (hx : x ∉ B) :
    Disjoint (link E u x) B := by
  apply disjoint_left.mpr
  intro y hy hyB
  obtain ⟨_, hyu, _, e, he, hue, hxe, hye⟩ := mem_link.mp hy
  have heB := hE.edge_eq_of_pair he hB hyu.symm hue hu hye hyB
  exact hx (heB ▸ hxe)

/-- The links from two different vertices of the same anchor edge to an
exterior vertex have no third vertex in common. -/
theorem links_disjoint {E : Finset (Finset V)} (hE : Linear E)
    {B : Finset V} (hB : B ∈ E) {u v x : V}
    (hu : u ∈ B) (hv : v ∈ B) (huv : u ≠ v) (hx : x ∉ B) :
    Disjoint (link E u x) (link E v x) := by
  apply disjoint_left.mpr
  intro y hy hz
  obtain ⟨_, _, hyx, e, he, hue, hxe, hye⟩ := mem_link.mp hy
  obtain ⟨_, _, _, f, hf, hvf, hxf, hyf⟩ := mem_link.mp hz
  have hef := hE.edge_eq_of_pair he hf hyx.symm hxe hxf hye hyf
  have heB := hE.edge_eq_of_pair he hB huv hue hu (hef.symm ▸ hvf) hv
  exact hx (heB ▸ hxe)

/-- The two choices of endpoints for the additional forbidden triples. -/
inductive SixVertexPattern
  | twoNeighbors
  | centerAndNeighbor

def SixVertexPattern.endpoints (pattern : SixVertexPattern) (v : V) (p : V × V) : V × V :=
  match pattern with
  | .twoNeighbors => p
  | .centerAndNeighbor => (v, p.1)

abbrev Anchor (V : Type*) := Σ _ : Finset V, V × V
abbrev Completion (V : Type*) := Σ _ : V, V × V
abbrev SixVertexTuple (V : Type*) := V × V × V × V × V

/-- A supporting edge and the ordered pair of its other vertices. -/
def anchorChoices (E : Finset (Finset V)) (v : V) : Finset (Anchor V) :=
  (incident E v).sigma (fun e => (e.erase v).offDiag)

theorem mem_anchorChoices {E : Finset (Finset V)} {v : V} {a : Anchor V} :
    a ∈ anchorChoices E v ↔
      a.1 ∈ E ∧ v ∈ a.1 ∧ a.2.1 ∈ a.1 ∧ a.2.2 ∈ a.1 ∧
        a.2.1 ≠ v ∧ a.2.2 ≠ v ∧ a.2.1 ≠ a.2.2 := by
  simp only [anchorChoices, mem_sigma, incident, mem_filter, mem_offDiag, mem_erase]
  tauto

theorem card_anchorChoices (E : Finset (Finset V)) (v : V) :
    ((anchorChoices E v).card : ℝ) = 2 * (tripleDegree E v : ℝ) := by
  rw [twice_tripleDegree, anchorChoices, card_sigma, Nat.cast_sum]
  refine sum_congr rfl (fun e he => ?_)
  have hv := (mem_filter.mp he).2
  rw [offDiag_card, ← Nat.mul_sub_one, Nat.cast_mul, card_erase_of_mem hv, edgeExcess]
  rw [show e.card - 1 - 1 = e.card - 2 by omega]

/-- The exterior vertex and the two third vertices completing the given anchor. -/
def completionChoices (E : Finset (Finset V)) (S B : Finset V) (u v : V) :
    Finset (Completion V) :=
  (S \ B).sigma (fun x => link E u x ×ˢ link E v x)

def sixVertexWitnesses (E : Finset (Finset V)) (S : Finset V) (v : V)
    (pattern : SixVertexPattern) : Finset (Σ _ : Anchor V, Completion V) :=
  (anchorChoices E v).sigma (fun a =>
    let p := pattern.endpoints v a.2
    completionChoices E S a.1 p.1 p.2)

/-- Forget the supporting edge and retain the ordered five vertices besides v. -/
def forgetAnchor (a : Σ _ : Anchor V, Completion V) : SixVertexTuple V :=
  (a.1.2.1, a.1.2.2, a.2.1, a.2.2.1, a.2.2.2)

def sixVertexTuples (E : Finset (Finset V)) (S : Finset V) (v : V)
    (pattern : SixVertexPattern) : Finset (SixVertexTuple V) :=
  (sixVertexWitnesses E S v pattern).image forgetAnchor

theorem mem_sixVertexTuples_iff {E : Finset (Finset V)} {S : Finset V} {v : V}
    {pattern : SixVertexPattern} {u₁ u₂ x y₁ y₂ : V} :
    (u₁, u₂, x, y₁, y₂) ∈ sixVertexTuples E S v pattern ↔
      ∃ B ∈ E, v ∈ B ∧ u₁ ∈ B ∧ u₂ ∈ B ∧ u₁ ≠ v ∧ u₂ ≠ v ∧ u₁ ≠ u₂ ∧
        x ∈ S ∧ x ∉ B ∧ y₁ ∈ link E (pattern.endpoints v (u₁, u₂)).1 x ∧
        y₂ ∈ link E (pattern.endpoints v (u₁, u₂)).2 x := by
  constructor
  · rintro ht
    obtain ⟨⟨⟨B, u₁', u₂'⟩, ⟨x', y₁', y₂'⟩⟩, hw, hp⟩ := mem_image.mp ht
    simp only [forgetAnchor, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨ha, hc⟩ := mem_sigma.mp hw
    obtain ⟨hB, hv, hu₁, hu₂, h₁, h₂, h₁₂⟩ := mem_anchorChoices.mp ha
    obtain ⟨hx, hy⟩ := mem_sigma.mp hc
    obtain ⟨hxS, hxB⟩ := mem_sdiff.mp hx
    obtain ⟨hy₁, hy₂⟩ := mem_product.mp hy
    exact ⟨B, hB, hv, hu₁, hu₂, h₁, h₂, h₁₂, hxS, hxB, hy₁, hy₂⟩
  · rintro ⟨B, hB, hv, hu₁, hu₂, h₁, h₂, h₁₂, hxS, hxB, hy₁, hy₂⟩
    refine mem_image.mpr ⟨⟨⟨B, u₁, u₂⟩, ⟨x, y₁, y₂⟩⟩, ?_, rfl⟩
    exact mem_sigma.mpr ⟨mem_anchorChoices.mpr ⟨hB, hv, hu₁, hu₂, h₁, h₂, h₁₂⟩,
      mem_sigma.mpr ⟨mem_sdiff.mpr ⟨hxS, hxB⟩, mem_product.mpr ⟨hy₁, hy₂⟩⟩⟩

omit [DecidableEq V] in
private theorem endpoints_mem {B : Finset V} {v u₁ u₂ : V}
    (pattern : SixVertexPattern) (hv : v ∈ B) (h₁ : u₁ ∈ B) (h₂ : u₂ ∈ B)
    (hn : u₁ ≠ v) (hn₁₂ : u₁ ≠ u₂) :
    let p := pattern.endpoints v (u₁, u₂)
    p.1 ∈ B ∧ p.2 ∈ B ∧ p.1 ≠ p.2 := by
  cases pattern
  · exact ⟨h₁, h₂, hn₁₂⟩
  · exact ⟨hv, h₁, hn.symm⟩

/-- Every tuple counted by either pattern really has six distinct vertices. -/
theorem sixVertexTuples_nodup {E : Finset (Finset V)} (hE : Linear E)
    {S : Finset V} {v u₁ u₂ x y₁ y₂ : V} {pattern : SixVertexPattern}
    (ht : (u₁, u₂, x, y₁, y₂) ∈ sixVertexTuples E S v pattern) :
    [v, u₁, u₂, x, y₁, y₂].Nodup := by
  obtain ⟨B, hB, hv, hu₁, hu₂, h₁, h₂, h₁₂, _, hx, hy₁, hy₂⟩ :=
    mem_sixVertexTuples_iff.mp ht
  obtain ⟨hp, hq, hpq⟩ := endpoints_mem pattern hv hu₁ hu₂ h₁ h₁₂
  have hy₁B := disjoint_left.mp (link_disjoint_edge hE hB hp hx) hy₁
  have hy₂B := disjoint_left.mp (link_disjoint_edge hE hB hq hx) hy₂
  have hy₁x := (mem_link.mp hy₁).2.2.1
  have hy₂x := (mem_link.mp hy₂).2.2.1
  have hy₁₂ : y₁ ≠ y₂ := fun eq =>
    disjoint_left.mp (links_disjoint hE hB hp hq hpq hx) hy₁ (eq.symm ▸ hy₂)
  have neq_of_mem (z t : V) (hz : z ∈ B) (ht : t ∉ B) : z ≠ t :=
    fun eq => ht (eq ▸ hz)
  simp [h₁.symm, h₂.symm, h₁₂, neq_of_mem _ _ hv hx, neq_of_mem _ _ hu₁ hx,
    neq_of_mem _ _ hu₂ hx, neq_of_mem _ _ hv hy₁B, neq_of_mem _ _ hu₁ hy₁B,
    neq_of_mem _ _ hu₂ hy₁B, neq_of_mem _ _ hv hy₂B, neq_of_mem _ _ hu₁ hy₂B,
    neq_of_mem _ _ hu₂ hy₂B, hy₁x.symm, hy₂x.symm, hy₁₂]

/-- The supporting anchor edge is uniquely determined by the ordered tuple. -/
theorem card_sixVertexTuples_eq_witnesses {E : Finset (Finset V)} (hE : Linear E)
    (S : Finset V) (v : V) (pattern : SixVertexPattern) :
    (sixVertexTuples E S v pattern).card = (sixVertexWitnesses E S v pattern).card := by
  apply card_image_iff.mpr
  intro a ha b hb hab
  rcases a with ⟨⟨A, u₁, u₂⟩, ⟨x, y₁, y₂⟩⟩
  rcases b with ⟨⟨B, u₁', u₂'⟩, ⟨x', y₁', y₂'⟩⟩
  simp only [forgetAnchor, Prod.mk.injEq] at hab
  rcases hab with ⟨rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨hA, hvA, huA, _, hn, _, _⟩ := mem_anchorChoices.mp (mem_sigma.mp ha).1
  obtain ⟨hB, hvB, huB, _, _, _, _⟩ := mem_anchorChoices.mp (mem_sigma.mp hb).1
  have hAB : A = B := hE.edge_eq_of_pair hA hB hn huA huB hvA hvB
  subst B
  rfl

/-- Lemma 8 for either ordered pattern. The type of vertices need not be finite;
all enumerated choices belong to the supplied finite sets. -/
theorem sixVertexTuples_card_le {E : Finset (Finset V)} (hE : Linear E)
    (S : Finset V) (v : V) (pattern : SixVertexPattern) {D : ℝ}
    (hD : 1 ≤ D) (hdeg : ∀ u : V, (tripleDegree E u : ℝ) ≤ D) :
    ((sixVertexTuples E S v pattern).card : ℝ) ≤ 14 * D ^ (7 / 3 : ℝ) := by
  have fiber (a : Anchor V) (ha : a ∈ anchorChoices E v) :
      let p := pattern.endpoints v a.2
      ((completionChoices E S a.1 p.1 p.2).card : ℝ) ≤ 7 * D ^ (4 / 3 : ℝ) := by
    obtain ⟨hB, hv, hu₁, hu₂, h₁, _, h₁₂⟩ := mem_anchorChoices.mp ha
    obtain ⟨hp, hq, hpq⟩ := endpoints_mem pattern hv hu₁ hu₂ h₁ h₁₂
    dsimp only
    rw [completionChoices, card_sigma, Nat.cast_sum]
    simp_rw [card_product, Nat.cast_mul, ← codegree_eq_card_link hE]
    exact codegree_product_sum_sdiff_le hE S hB hpq hp hq hD (hdeg _) (hdeg _)
  rw [card_sixVertexTuples_eq_witnesses hE, sixVertexWitnesses, card_sigma, Nat.cast_sum]
  calc
    _ ≤ ∑ a ∈ anchorChoices E v, 7 * D ^ (4 / 3 : ℝ) := sum_le_sum fiber
    _ = (2 * (tripleDegree E v : ℝ)) * (7 * D ^ (4 / 3 : ℝ)) := by
      rw [sum_const, nsmul_eq_mul, card_anchorChoices]
    _ ≤ (2 * D) * (7 * D ^ (4 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hdeg v) (by norm_num))
        (by have hD0 := zero_le_one.trans hD; positivity)
    _ = _ := by
      rw [show (7 / 3 : ℝ) = 1 + 4 / 3 by norm_num,
        Real.rpow_add (zero_lt_one.trans_le hD), Real.rpow_one]
      ring

end OMA.GeneralPositionCodegrees

/-! A finite incidence-to-configuration map for the two local losses in
arXiv:2610.34254v1, (2.5) and (2.6). -/

namespace OMA.GeneralPositionLoss

open Finset OMA.GeneralPositionCodegrees OMA.OnlineSelection

variable {V : Type*} [DecidableEq V]

abbrev LossWitness (V : Type*) := Σ _ : Anchor V, Completion V
abbrev Incidence (V : Type*) := Σ _ : Finset V, Finset V

def current (w : LossWitness V) : V := w.2.1

def firstWitness (w : LossWitness V) : V := w.2.2.1

def secondWitness (w : LossWitness V) : V := w.2.2.2

/-- All vertices whose retention is required for the tuple. -/
def vertices (v : V) (w : LossWitness V) : Finset V :=
  {v, w.1.2.1, w.1.2.2, current w, firstWitness w, secondWitness w}

/-- Configurations supported entirely on the realized retained set Q. -/
def eligible (E : Finset (Finset V)) (Q : Finset V) (v : V) (p : SixVertexPattern) :
    Finset (LossWitness V) :=
  (sixVertexWitnesses E Q v p).filter (fun w => vertices v w ⊆ Q)

/-- The witnessed configurations for a fixed current vertex and accepted set. -/
def seen (E : Finset (Finset V)) (Q A : Finset V) (v x : V) (p : SixVertexPattern) :
    Finset (LossWitness V) :=
  (eligible E Q v p).filter (fun w => current w = x ∧ firstWitness w ∈ A ∧ secondWitness w ∈ A)

def HasWitness (E : Finset (Finset V)) (A : Finset V) (x u : V) : Prop :=
  (A ∩ link E u x).Nonempty

noncomputable def targets (E : Finset (Finset V)) (A L B : Finset V) (v x : V) : Finset V := by
  classical
  exact B.filter (fun u => u ∈ L ∧ u ≠ v ∧ HasWitness E A x u)

def markCount : SixVertexPattern → ℕ
  | .twoNeighbors => 2
  | .centerAndNeighbor => 1

def centerGate (E : Finset (Finset V)) (A : Finset V) (v x : V) :
    SixVertexPattern → Prop
  | .twoNeighbors => True
  | .centerAndNeighbor => HasWitness E A x v

/-- One incidence per edge and unordered pair in (2.5), or per edge and affected
vertex in (2.6). L comprises vertices later than x. Edges are indexed by their
original labels, with the retained trace required to have size at least three. -/
noncomputable def incidences (E : Finset (Finset V)) (Q A L : Finset V) (v x : V)
    (p : SixVertexPattern) : Finset (Incidence V) := by
  classical
  exact (E.filter fun B => v ∈ B ∧ x ∉ B ∧ 3 ≤ (B ∩ Q).card ∧ centerGate E A v x p).sigma
    (fun B => (targets E A L B v x).powersetCard (markCount p))

/-- Forget the witnesses and, in (2.6), the auxiliary second anchor vertex. -/
def decode (p : SixVertexPattern) (w : LossWitness V) : Incidence V :=
  ⟨w.1.1, match p with
    | .twoNeighbors => {w.1.2.1, w.1.2.2}
    | .centerAndNeighbor => {w.1.2.1}⟩

/-- The process's affected predicate agrees with existence of a selected link
witness whenever the current vertex is unprocessed and the state is disjoint. -/
theorem affected_iff_hasWitness {E : Finset (Finset V)} {s : HypergraphState V} {x u : V}
    (hd : Disjoint s.selected s.remaining) (hx : x ∈ s.remaining) :
    HypergraphState.Affected E s x u ↔
      u ∈ s.remaining.erase x ∧ HasWitness E s.selected x u := by
  constructor
  · rintro ⟨hu, y, hy, B, hB, hxB, hyB, huB⟩
    have hyu : y ≠ u := fun h => Finset.disjoint_left.mp hd (h ▸ hy) (mem_of_mem_erase hu)
    have hyx : y ≠ x := fun h => Finset.disjoint_left.mp hd (h ▸ hy) hx
    exact ⟨hu, y, mem_inter.mpr ⟨hy, mem_link.mpr
      ⟨(mem_erase.mp hu).1, hyu, hyx, B, hB, huB, hxB, hyB⟩⟩⟩
  · rintro ⟨hu, y, hy⟩
    obtain ⟨hyA, hyLink⟩ := mem_inter.mp hy
    obtain ⟨_, _, _, B, hB, huB, hxB, hyB⟩ := mem_link.mp hyLink
    exact ⟨hu, y, hyA, B, hB, hxB, hyB, huB⟩

/-- Given the unique common edge in (2.6), excluding it is equivalent to
requiring that x is outside the anchor edge. -/
theorem notMem_iff_ne_common {E : Finset (Finset V)} (hE : Linear E)
    {B C : Finset V} (hB : B ∈ E) (hC : C ∈ E) {v x : V} (hvx : v ≠ x)
    (hvB : v ∈ B) (hvC : v ∈ C) (hxC : x ∈ C) :
    x ∉ B ↔ B ≠ C := by
  exact ⟨fun h heq => h (heq.symm ▸ hxC),
    fun h hxB => h (hE.edge_eq_of_pair hB hC hvx hvB hvC hxB hxC)⟩

theorem seen_of_vertices {E : Finset (Finset V)} {Q A B : Finset V}
    {v u₁ u₂ x y₁ y₂ : V} {p : SixVertexPattern}
    (hB : B ∈ E) (hvB : v ∈ B) (hu₁B : u₁ ∈ B) (hu₂B : u₂ ∈ B)
    (h₁ : u₁ ≠ v) (h₂ : u₂ ≠ v) (h₁₂ : u₁ ≠ u₂) (hxB : x ∉ B)
    (hvQ : v ∈ Q) (hu₁Q : u₁ ∈ Q) (hu₂Q : u₂ ∈ Q) (hxQ : x ∈ Q)
    (hAQ : A ⊆ Q) (hy₁ : y₁ ∈ A) (hy₂ : y₂ ∈ A)
    (hy₁l : y₁ ∈ link E (p.endpoints v (u₁, u₂)).1 x)
    (hy₂l : y₂ ∈ link E (p.endpoints v (u₁, u₂)).2 x) :
    (⟨⟨B, u₁, u₂⟩, ⟨x, y₁, y₂⟩⟩ : LossWitness V) ∈ seen E Q A v x p := by
  refine mem_filter.mpr ⟨mem_filter.mpr ⟨?_, ?_⟩, rfl, hy₁, hy₂⟩
  · exact mem_sigma.mpr ⟨mem_anchorChoices.mpr ⟨hB, hvB, hu₁B, hu₂B, h₁, h₂, h₁₂⟩,
      mem_sigma.mpr ⟨mem_sdiff.mpr ⟨hxQ, hxB⟩, mem_product.mpr ⟨hy₁l, hy₂l⟩⟩⟩
  · simp [vertices, current, firstWitness, secondWitness, insert_subset_iff,
      hvQ, hu₁Q, hu₂Q, hxQ, hAQ hy₁, hAQ hy₂]

/-- Every local incidence has a witnessed configuration that decodes to it.
The projection fixes its original edge and marked vertex set, so choosing
one ordered witness per incidence introduces no multiplicity. -/
theorem decode_surjOn_seen {E : Finset (Finset V)} {Q A L : Finset V} {v x : V}
    (hvQ : v ∈ Q) (hxQ : x ∈ Q) (hAQ : A ⊆ Q) (hLQ : L ⊆ Q) (p : SixVertexPattern) :
    Set.SurjOn (decode p) (↑(seen E Q A v x p) : Set (LossWitness V))
      (↑(incidences E Q A L v x p) : Set (Incidence V)) := by
  classical
  rintro ⟨B, U⟩ hi
  obtain ⟨hB, hU⟩ := mem_sigma.mp hi
  obtain ⟨hBE, hvB, hxB, hsize, hcenter⟩ := mem_filter.mp hB
  obtain ⟨hUsub, hcard⟩ := mem_powersetCard.mp hU
  have mark {u : V} (hu : u ∈ U) :
      u ∈ B ∧ u ∈ Q ∧ u ≠ v ∧ HasWitness E A x u := by
    obtain ⟨huB, huL, huv, hw⟩ := mem_filter.mp (hUsub hu)
    exact ⟨huB, hLQ huL, huv, hw⟩
  cases p
  · obtain ⟨u₁, u₂, h₁₂, rfl⟩ := card_eq_two.mp hcard
    obtain ⟨h₁B, h₁Q, h₁, y₁, hy₁⟩ := mark (mem_insert_self _ _)
    obtain ⟨h₂B, h₂Q, h₂, y₂, hy₂⟩ := mark (mem_insert_of_mem (mem_singleton_self _))
    obtain ⟨hy₁A, hy₁l⟩ := mem_inter.mp hy₁
    obtain ⟨hy₂A, hy₂l⟩ := mem_inter.mp hy₂
    exact ⟨⟨⟨B, u₁, u₂⟩, ⟨x, y₁, y₂⟩⟩,
      seen_of_vertices hBE hvB h₁B h₂B h₁ h₂ h₁₂ hxB hvQ h₁Q h₂Q hxQ
        hAQ hy₁A hy₂A hy₁l hy₂l, rfl⟩
  · obtain ⟨u₁, rfl⟩ := card_eq_one.mp hcard
    obtain ⟨h₁B, h₁Q, h₁, y₂, hy₂⟩ := mark (mem_singleton_self _)
    change 3 ≤ (B ∩ Q).card at hsize
    have hlt : ({v, u₁} : Finset V).card < (B ∩ Q).card := by
      rw [card_pair h₁.symm]
      omega
    obtain ⟨u₂, h₂, h₂not⟩ := exists_mem_notMem_of_card_lt_card hlt
    obtain ⟨h₂B, h₂Q⟩ := mem_inter.mp h₂
    have h₂v : u₂ ≠ v := fun h => h₂not (mem_insert.mpr (Or.inl h))
    have h₁₂ : u₁ ≠ u₂ := fun h => h₂not (mem_insert.mpr (Or.inr (mem_singleton.mpr h.symm)))
    obtain ⟨y₁, hy₁⟩ : HasWitness E A x v := hcenter
    obtain ⟨hy₁A, hy₁l⟩ := mem_inter.mp hy₁
    obtain ⟨hy₂A, hy₂l⟩ := mem_inter.mp hy₂
    exact ⟨⟨⟨B, u₁, u₂⟩, ⟨x, y₁, y₂⟩⟩,
      seen_of_vertices hBE hvB h₁B h₂B h₁ h₂v h₁₂ hxB hvQ h₁Q h₂Q hxQ
        hAQ hy₁A hy₂A hy₁l hy₂l, rfl⟩

theorem incidences_card_le_seen {E : Finset (Finset V)} {Q A L : Finset V} {v x : V}
    (hvQ : v ∈ Q) (hxQ : x ∈ Q) (hAQ : A ⊆ Q) (hLQ : L ⊆ Q) (p : SixVertexPattern) :
    (incidences E Q A L v x p).card ≤ (seen E Q A v x p).card :=
  card_le_card_of_surjOn (decode p) (decode_surjOn_seen hvQ hxQ hAQ hLQ p)

theorem eligible_card_le {E : Finset (Finset V)} (hE : Linear E)
    (Q : Finset V) (v : V) (p : SixVertexPattern) {D : ℝ}
    (hD : 1 ≤ D) (hdeg : ∀ u : V, (tripleDegree E u : ℝ) ≤ D) :
    ((eligible E Q v p).card : ℝ) ≤ 14 * D ^ (7 / 3 : ℝ) := by
  refine le_trans ?_ (sixVertexTuples_card_le hE Q v p hD hdeg)
  rw [card_sixVertexTuples_eq_witnesses hE]
  exact_mod_cast card_le_card (filter_subset _ _)

/-- The same original configuration is eligible exactly when all six vertices
survive. The ambient domain S may be larger than the realized retained set Q. -/
theorem eligible_eq_filter_original (E : Finset (Finset V)) {Q S : Finset V}
    (hQS : Q ⊆ S) (v : V) (p : SixVertexPattern) :
    eligible E Q v p = (sixVertexWitnesses E S v p).filter (fun w => vertices v w ⊆ Q) := by
  ext w
  simp only [eligible, mem_filter]
  constructor
  · rintro ⟨hw, hkeep⟩
    obtain ⟨hanchor, hcomp⟩ := mem_sigma.mp hw
    obtain ⟨hx, hy⟩ := mem_sigma.mp hcomp
    obtain ⟨hxQ, hxB⟩ := mem_sdiff.mp hx
    exact ⟨mem_sigma.mpr ⟨hanchor, mem_sigma.mpr ⟨mem_sdiff.mpr ⟨hQS hxQ, hxB⟩, hy⟩⟩, hkeep⟩
  · rintro ⟨hw, hkeep⟩
    obtain ⟨hanchor, hcomp⟩ := mem_sigma.mp hw
    obtain ⟨hx, hy⟩ := mem_sigma.mp hcomp
    have hxQ : current w ∈ Q := hkeep (by simp [vertices])
    exact ⟨mem_sigma.mpr ⟨hanchor, mem_sigma.mpr
      ⟨mem_sdiff.mpr ⟨hxQ, (mem_sdiff.mp hx).2⟩, hy⟩⟩, hkeep⟩

/-- Each original configuration requires six distinct retained vertices. -/
theorem vertices_card_of_mem {E : Finset (Finset V)} (hE : Linear E)
    {S : Finset V} {v : V} {p : SixVertexPattern} {w : LossWitness V}
    (hw : w ∈ sixVertexWitnesses E S v p) :
    (vertices v w).card = 6 := by
  have ht : forgetAnchor w ∈ sixVertexTuples E S v p := mem_image.mpr ⟨w, hw, rfl⟩
  have hn := sixVertexTuples_nodup hE ht
  simpa [vertices, current, firstWitness, secondWitness] using List.toFinset_card_of_nodup hn

theorem witnesses_ne {E : Finset (Finset V)} (hE : Linear E) {Q : Finset V} {v : V}
    {p : SixVertexPattern} {w : LossWitness V} (hw : w ∈ eligible E Q v p) :
    firstWitness w ≠ secondWitness w := by
  have ht : forgetAnchor w ∈ sixVertexTuples E Q v p :=
    mem_image.mpr ⟨w, (mem_filter.mp hw).1, rfl⟩
  have hn := sixVertexTuples_nodup hE ht
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  tauto

end OMA.GeneralPositionLoss

/-! Finite telescoping of one-step expected potential losses. -/

namespace OMA.OnlineSelection.Rule

variable {V State : Type*} (R : Rule V State)

/-- Expected sum of pre-step losses. The loss may depend on the current
vertex, the remaining order, and the state. -/
def expectedLosses (loss : V → List V → State → ℝ) : List V → State → ℝ
  | [], _ => 0
  | x :: xs, s =>
      loss x xs s +
      R.chance x s * expectedLosses loss xs (R.next x true s) +
      (1 - R.chance x s) * expectedLosses loss xs (R.next x false s)

theorem expect_add (xs : List V) (s : State) (f g : List V → State → ℝ) :
    R.expect xs s (fun A t => f A t + g A t) = R.expect xs s f + R.expect xs s g := by
  induction xs generalizing s f g with
  | nil => rfl
  | cons x xs ih =>
      simp only [expect, ih]
      ring

/-- Sum the prefix expectations for every step in the suffix. The first
prefix can already contain processing steps whose losses are omitted. -/
def expectedLossesFrom (loss : V → List V → State → ℝ) : List V → List V → State → ℝ
  | _, [], _ => 0
  | before, x :: xs, s =>
      R.expect before s (fun _ t => loss x xs t) +
        expectedLossesFrom loss (before ++ [x]) xs s

/-- The prefix-by-prefix loss sum equals the iterated expected loss. -/
theorem expectedLossesFrom_eq_expect (loss : V → List V → State → ℝ)
    (before xs : List V) (s : State) :
    R.expectedLossesFrom loss before xs s =
      R.expect before s (fun _ t => R.expectedLosses loss xs t) := by
  induction xs generalizing before with
  | nil => simp [expectedLossesFrom, expectedLosses, expect_const]
  | cons x xs ih =>
      rw [expectedLossesFrom, ih, expect_append, ← expect_add]
      apply R.expect_congr
      intro _ _ t
      simp only [expect, expectedLosses]
      ring

theorem expectedLosses_eq_prefix_sum (loss : V → List V → State → ℝ)
    (xs : List V) (s : State) :
    R.expectedLosses loss xs s = R.expectedLossesFrom loss [] xs s :=
  (R.expectedLossesFrom_eq_expect loss [] xs s).symm

/-- Sum a one-step potential bound over the finite law. The auxiliary
invariant need only persist along positive-weight branches. -/
theorem potential_le_terminal_add_losses {I : State → Prop} {τ : ℝ}
    (hR : R.Capped I τ) {P : List V → State → Prop}
    (hstep : ∀ x xs s b, P (x :: xs) s →
      0 < (if b then R.chance x s else 1 - R.chance x s) → P xs (R.next x b s))
    (φ : List V → State → ℝ) (loss : V → List V → State → ℝ)
    (hlocal : ∀ x xs s, I s → P (x :: xs) s →
      φ (x :: xs) s ≤ R.chance x s * φ xs (R.next x true s) +
        (1 - R.chance x s) * φ xs (R.next x false s) + loss x xs s)
    (xs : List V) {s : State} (hs : I s) (hp : P xs s) :
    φ xs s ≤ R.expect xs s (fun _ t => φ [] t) + R.expectedLosses loss xs s := by
  induction xs generalizing s with
  | nil => simp [expect, expectedLosses]
  | cons x xs ih =>
      obtain ⟨hq0, hqτ⟩ := hR.chance_bounds x s hs
      have hbranch (b : Bool) (r : ℝ)
          (hr : r = (if b then R.chance x s else 1 - R.chance x s))
          (hr0 : 0 ≤ r) :
          r * φ xs (R.next x b s) ≤
            r * (R.expect xs (R.next x b s) (fun _ t => φ [] t) +
              R.expectedLosses loss xs (R.next x b s)) := by
        by_cases hrPos : 0 < r
        · exact mul_le_mul_of_nonneg_left
            (ih (hR.next_valid x b s hs) (hstep x xs s b hp (hr ▸ hrPos))) hr0
        · have hrZero : r = 0 := le_antisymm (le_of_not_gt hrPos) hr0
          simp [hrZero]
      calc
        _ ≤ _ := hlocal x xs s hs hp
        _ ≤ R.chance x s * (R.expect xs (R.next x true s) (fun _ t => φ [] t) +
                R.expectedLosses loss xs (R.next x true s)) +
            (1 - R.chance x s) * (R.expect xs (R.next x false s) (fun _ t => φ [] t) +
                R.expectedLosses loss xs (R.next x false s)) + loss x xs s :=
          add_le_add (add_le_add (hbranch true _ rfl hq0)
            (hbranch false _ rfl (sub_nonneg.mpr (hqτ.trans hR.cap_le_one)))) le_rfl
        _ = _ := by
          simp only [expect, expectedLosses]
          ring

end OMA.OnlineSelection.Rule

/-! Expected loss on a fixed realized retained order. -/

namespace OMA.GeneralPositionLoss

open scoped BigOperators
open Finset OMA.GeneralPositionCodegrees OMA.OnlineSelection

variable {V : Type*}

section Generic

variable {State : Type*} (R : Rule V State)

/-- Compare terminal payoffs only along the paths that carry positive mass. -/
theorem expect_mono_on_outcomes {I : State → Prop} {τ : ℝ} (hR : R.Capped I τ)
    (before : List V) {s : State} (hs : I s) {f g : List V → State → ℝ}
    (h : ∀ o ∈ R.outcomes before s, 0 < o.weight → f o.accepted o.state ≤ g o.accepted o.state) :
    R.expect before s f ≤ R.expect before s g := by
  rw [R.expect_eq_outcomes_sum, R.expect_eq_outcomes_sum]
  refine List.sum_le_sum (fun o ho => ?_)
  have hw := (R.outcomes_valid hR hs ho).1
  by_cases hp : 0 < o.weight
  · exact mul_le_mul_of_nonneg_left (h o ho hp) hw
  · simp [le_antisymm (le_of_not_gt hp) hw]

theorem expect_const_mul (xs : List V) (s : State) (c : ℝ) (f : List V → State → ℝ) :
    R.expect xs s (fun A t => c * f A t) = c * R.expect xs s f := by
  induction xs generalizing s f with
  | nil => rfl
  | cons x xs ih =>
      simp only [Rule.expect, ih]
      ring

theorem expect_finset_sum {α : Type*} (B : Finset α) (xs : List V) (s : State)
    (f : α → List V → State → ℝ) :
    R.expect xs s (fun A t => ∑ b ∈ B, f b A t) = ∑ b ∈ B, R.expect xs s (f b) := by
  classical
  induction B using Finset.induction_on with
  | empty => simp [Rule.expect_const]
  | insert b B hb ih => simp only [sum_insert hb, Rule.expect_add, ih]

/-- A prefix-by-prefix comparison on a fixed schedule. -/
theorem expectedLossesFrom_mono {I : State → Prop} {τ : ℝ} (hR : R.Capped I τ)
    (order before xs : List V) {s : State} (hs : I s) (horder : before ++ xs = order)
    {f g : V → List V → State → ℝ}
    (h : ∀ before x after, before ++ x :: after = order →
      ∀ o ∈ R.outcomes before s, 0 < o.weight → f x after o.state ≤ g x after o.state) :
    R.expectedLossesFrom f before xs s ≤ R.expectedLossesFrom g before xs s := by
  induction xs generalizing before with
  | nil => simp [Rule.expectedLossesFrom]
  | cons x xs ih =>
      have hv : (before ++ [x]) ++ xs = order := by simpa [List.append_assoc] using horder
      simp only [Rule.expectedLossesFrom]
      exact add_le_add
        (expect_mono_on_outcomes R hR before hs (fun o ho hp => h before x xs horder o ho hp))
        (ih _ hv)

theorem expectedLosses_add (xs : List V) (s : State) (f g : V → List V → State → ℝ) :
    R.expectedLosses (fun x tail t => f x tail t + g x tail t) xs s =
      R.expectedLosses f xs s + R.expectedLosses g xs s := by
  induction xs generalizing s with
  | nil => simp [Rule.expectedLosses]
  | cons x xs ih =>
      simp only [Rule.expectedLosses, ih]
      ring

/-- A process with auxiliary state preserves expected losses that depend only
on the projected state, when updates and chances commute with projection. -/
theorem expectedLosses_project {Small : Type*} (R' : Rule V Small) (project : State → Small)
    (hc : ∀ x s, R.chance x s = R'.chance x (project s))
    (hn : ∀ x b s, project (R.next x b s) = R'.next x b (project s))
    (loss : V → List V → Small → ℝ) (xs : List V) (s : State) :
    R.expectedLosses (fun x tail t => loss x tail (project t)) xs s =
      R'.expectedLosses loss xs (project s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp only [Rule.expectedLosses, hc, ih, hn]

end Generic

variable [DecidableEq V]

/-- The coefficient times q times the local incidence count, before any
averaging over retention. -/
noncomputable def localLoss (E : Finset (Finset V)) (Q : Finset V) (v : V)
    (p : SixVertexPattern) (c : ℝ) (x : V) (after : List V) (s : HypergraphState V) : ℝ :=
  c * s.weight x * ((incidences E Q s.selected after.toFinset v x p).card : ℝ)

theorem expected_localLoss_le {E : Finset (Finset V)} (hE : Linear E)
    {Q : Finset V} {v : V} (hv : v ∈ Q)
    {τ a c : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ < 1) (ha0 : 0 ≤ a) (haτ : a ≤ τ) (hc : 0 ≤ c)
    (p : SixVertexPattern) (before after : List V) (x : V)
    (horder : (before ++ x :: after).Nodup) (hQ : (before ++ x :: after).toFinset ⊆ Q) :
    (HypergraphState.process E τ).expect before (HypergraphState.initial Q a)
        (fun _ t => localLoss E Q v p c x after t) ≤
      c * τ ^ 3 * (((eligible E Q v p).filter (fun w => current w = x)).card : ℝ) := by
  let R := HypergraphState.process E τ
  let s := HypergraphState.initial Q a
  let F := (eligible E Q v p).filter (fun w => current w = x)
  let S := F.filter (fun w => firstWitness w ∈ before ∧ secondWitness w ∈ before)
  let term (w : LossWitness V) (A : List V) (t : HypergraphState V) : ℝ :=
    if firstWitness w ∈ A ∧ secondWitness w ∈ A then R.chance x t else 0
  have hR := HypergraphState.process_capped E hτ hτ1
  have hs : HypergraphState.WeightsIn τ s := fun _ => ⟨ha0, haτ⟩
  have hxQ : x ∈ Q := hQ (List.mem_toFinset.mpr (List.mem_append.mpr (Or.inr (by simp))))
  have htailQ : after.toFinset ⊆ Q := by
    intro u hu
    exact hQ (List.mem_toFinset.mpr (List.mem_append.mpr
      (Or.inr (List.mem_cons_of_mem x (List.mem_toFinset.mp hu)))))
  change R.expect before s _ ≤ c * τ ^ 3 * (F.card : ℝ)
  calc
    _ ≤ R.expect before s (fun A t => c * ∑ w ∈ S, term w A t) := by
      apply expect_mono_on_outcomes R hR before hs
      intro o ho _
      have hvalid := R.outcomes_valid hR hs ho
      have hselected : o.state.selected = o.accepted.toFinset := by
        simpa [s, HypergraphState.initial] using HypergraphState.outcome_selected_eq E τ ho
      have hAQ : o.state.selected ⊆ Q := by
        rw [hselected]
        intro u hu
        exact hQ (List.mem_toFinset.mpr (List.mem_append.mpr
          (Or.inl (hvalid.2.1.subset (List.mem_toFinset.mp hu)))))
      have hq0 : 0 ≤ R.chance x o.state := (hvalid.2.2 x).1
      let W := S.filter (fun w => firstWitness w ∈ o.accepted ∧ secondWitness w ∈ o.accepted)
      have hsub : seen E Q o.state.selected v x p ⊆ W := by
        intro w hw
        obtain ⟨hEligible, hcurr, hw₁, hw₂⟩ := mem_filter.mp hw
        rw [hselected] at hw₁ hw₂
        have h₁ := List.mem_toFinset.mp hw₁
        have h₂ := List.mem_toFinset.mp hw₂
        exact mem_filter.mpr ⟨mem_filter.mpr
          ⟨mem_filter.mpr ⟨hEligible, hcurr⟩, hvalid.2.1.subset h₁, hvalid.2.1.subset h₂⟩, h₁, h₂⟩
      have hcard : ((incidences E Q o.state.selected after.toFinset v x p).card : ℝ) ≤ W.card := by
        exact_mod_cast (incidences_card_le_seen hv hxQ hAQ htailQ p).trans (card_le_card hsub)
      have hsum : ∑ w ∈ S, term w o.accepted o.state = R.chance x o.state * (W.card : ℝ) := by
        simp only [term, ← sum_filter, sum_const, nsmul_eq_mul, W, mul_comm]
      rw [hsum, localLoss, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcard hq0) hc
    _ = c * ∑ w ∈ S, R.expect before s (term w) := by
      rw [expect_const_mul, expect_finset_sum]
    _ ≤ c * ∑ w ∈ S, τ ^ 3 := by
      apply mul_le_mul_of_nonneg_left _ hc
      refine sum_le_sum (fun w hw => ?_)
      obtain ⟨hwF, hw₁, hw₂⟩ := mem_filter.mp hw
      have hwE : w ∈ eligible E Q v p := (mem_filter.mp hwF).1
      have hwne := witnesses_ne hE hwE
      simpa [term, insert_subset_iff] using
        R.expect_two_witnesses_le_cube hR before after x (firstWitness w) (secondWitness w)
          hs horder hw₁ hw₂ hwne
    _ = c * τ ^ 3 * (S.card : ℝ) := by
      rw [sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      have hcard : (S.card : ℝ) ≤ F.card := by exact_mod_cast card_le_card (filter_subset _ _)
      exact mul_le_mul_of_nonneg_left hcard (mul_nonneg hc (pow_nonneg hτ _))

theorem expected_localLossesFrom_le {E : Finset (Finset V)} (hE : Linear E)
    {Q : Finset V} {v : V} (hv : v ∈ Q)
    {τ a c : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ < 1) (ha0 : 0 ≤ a) (haτ : a ≤ τ) (hc : 0 ≤ c)
    (p : SixVertexPattern) (before xs : List V)
    (horder : (before ++ xs).Nodup) (hQ : (before ++ xs).toFinset ⊆ Q) :
    (HypergraphState.process E τ).expectedLossesFrom (localLoss E Q v p c) before xs
        (HypergraphState.initial Q a) ≤
      c * τ ^ 3 * (((eligible E Q v p).filter (fun w => current w ∈ xs)).card : ℝ) := by
  induction xs generalizing before with
  | nil => simp [Rule.expectedLossesFrom]
  | cons x xs ih =>
      have hx : x ∉ xs := (List.nodup_cons.mp (List.nodup_append'.mp horder).2.1).1
      have heq : (before ++ [x]) ++ xs = before ++ x :: xs := by simp [List.append_assoc]
      let C := eligible E Q v p
      let Cx := C.filter (fun w => current w = x)
      let Cr := C.filter (fun w => current w ∈ xs)
      have hsplit : C.filter (fun w => current w ∈ x :: xs) = Cx ∪ Cr := by
        ext w
        simp only [Cx, Cr, mem_filter, mem_union, List.mem_cons]
        tauto
      have hd : Disjoint Cx Cr := by
        apply Finset.disjoint_left.mpr
        intro w hw hw'
        exact hx ((mem_filter.mp hw).2 ▸ (mem_filter.mp hw').2)
      rw [Rule.expectedLossesFrom]
      calc
        _ ≤ c * τ ^ 3 * (Cx.card : ℝ) + c * τ ^ 3 * (Cr.card : ℝ) :=
          add_le_add (expected_localLoss_le hE hv hτ hτ1 ha0 haτ hc p before xs x horder hQ)
            (ih _ (by simpa only [heq] using horder) (by simpa only [heq] using hQ))
        _ = _ := by
          change _ = c * τ ^ 3 * ((C.filter (fun w => current w ∈ x :: xs)).card : ℝ)
          rw [hsplit, card_union_of_disjoint hd, Nat.cast_add]
          ring

/-- The aggregate contribution of either local loss, for the fixed realized Q. -/
theorem expected_localLosses_le {E : Finset (Finset V)} (hE : Linear E)
    {Q : Finset V} {v : V} (hv : v ∈ Q)
    {τ a c : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ < 1) (ha0 : 0 ≤ a) (haτ : a ≤ τ) (hc : 0 ≤ c)
    (p : SixVertexPattern) (xs : List V) (hxs : xs.Nodup) (hQ : xs.toFinset = Q) :
    (HypergraphState.process E τ).expectedLosses (localLoss E Q v p c) xs
        (HypergraphState.initial Q a) ≤
      c * τ ^ 3 * ((eligible E Q v p).card : ℝ) := by
  rw [Rule.expectedLosses_eq_prefix_sum]
  refine (expected_localLossesFrom_le hE hv hτ hτ1 ha0 haτ hc p [] xs hxs (by simpa only [List.nil_append, hQ] using (Subset.rfl : Q ⊆ Q))).trans ?_
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hc (pow_nonneg hτ _))
  exact_mod_cast card_le_card (filter_subset _ _)

/-- Combine the two losses with arbitrary nonnegative coefficients. The local
premise need only hold at positive-weight prefixes. -/
theorem expected_both_losses_le {E : Finset (Finset V)} (hE : Linear E)
    {Q : Finset V} {v : V} (hv : v ∈ Q)
    {τ a cG cH : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ < 1) (ha0 : 0 ≤ a) (haτ : a ≤ τ)
    (hcG : 0 ≤ cG) (hcH : 0 ≤ cH) (order : List V) (horder : order.Nodup)
    (hQ : order.toFinset = Q) (loss : V → List V → HypergraphState V → ℝ)
    (hlocal : ∀ before x after, before ++ x :: after = order →
      ∀ o ∈ (HypergraphState.process E τ).outcomes before (HypergraphState.initial Q a),
      0 < o.weight →
      loss x after o.state ≤
        localLoss E Q v .twoNeighbors cG x after o.state +
        localLoss E Q v .centerAndNeighbor cH x after o.state) :
    (HypergraphState.process E τ).expectedLosses loss order (HypergraphState.initial Q a) ≤
      cG * τ ^ 3 * ((eligible E Q v .twoNeighbors).card : ℝ) +
      cH * τ ^ 3 * ((eligible E Q v .centerAndNeighbor).card : ℝ) := by
  let R := HypergraphState.process E τ
  let s := HypergraphState.initial Q a
  let g := localLoss E Q v .twoNeighbors cG
  let h := localLoss E Q v .centerAndNeighbor cH
  have hs : HypergraphState.WeightsIn τ s := fun _ => ⟨ha0, haτ⟩
  calc
    _ ≤ R.expectedLosses (fun x after t => g x after t + h x after t) order s := by
      simp only [Rule.expectedLosses_eq_prefix_sum]
      exact expectedLossesFrom_mono R (HypergraphState.process_capped E hτ hτ1) order [] order
        hs rfl hlocal
    _ = R.expectedLosses g order s + R.expectedLosses h order s :=
      expectedLosses_add R order s g h
    _ ≤ _ := add_le_add
      (expected_localLosses_le hE hv hτ hτ1 ha0 haτ hcG .twoNeighbors order horder hQ)
      (expected_localLosses_le hE hv hτ hτ1 ha0 haτ hcH .centerAndNeighbor order horder hQ)

/-- The paper's numerical coefficients after averaging over online selection
only. The two cardinalities remain as retention events for the outer law. -/
theorem expected_paperLoss_le {E : Finset (Finset V)} (hE : Linear E)
    {Q : Finset V} {v : V} (hv : v ∈ Q)
    {τ a σ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ < 1) (ha0 : 0 ≤ a) (haτ : a ≤ τ)
    (hσ : 0 < σ) (order : List V) (horder : order.Nodup) (hQ : order.toFinset = Q)
    (loss : V → List V → HypergraphState V → ℝ)
    (hlocal : ∀ before x after, before ++ x :: after = order →
      ∀ o ∈ (HypergraphState.process E τ).outcomes before (HypergraphState.initial Q a),
      0 < o.weight →
      loss x after o.state ≤
        localLoss E Q v .twoNeighbors (8 * τ ^ 3 / σ ^ 2) x after o.state +
        localLoss E Q v .centerAndNeighbor (16 * τ ^ 2 / σ) x after o.state) :
    (HypergraphState.process E τ).expectedLosses loss order (HypergraphState.initial Q a) ≤
      (8 * τ ^ 6 / σ ^ 2) * ((eligible E Q v .twoNeighbors).card : ℝ) +
      (16 * τ ^ 5 / σ) * ((eligible E Q v .centerAndNeighbor).card : ℝ) := by
  have hcG : 0 ≤ 8 * τ ^ 3 / σ ^ 2 := by positivity
  have hcH : 0 ≤ 16 * τ ^ 2 / σ := by positivity
  refine (expected_both_losses_le hE hv hτ hτ1 ha0 haτ hcG hcH order horder hQ loss hlocal).trans_eq ?_
  ring

end OMA.GeneralPositionLoss

/-! The counts are unchanged when original labels are replaced by retained
traces, as in the one-step inequalities of the paper. -/

namespace OMA.GeneralPositionLoss

open Finset OMA.GeneralPositionCodegrees OMA.OnlineSelection

variable {V : Type*} [DecidableEq V]

def retainedEdges (E : Finset (Finset V)) (Q : Finset V) : Finset (Finset V) :=
  (E.image (· ∩ Q)).filter fun B => 3 ≤ B.card

theorem link_mem_retained_iff {E : Finset (Finset V)} {Q : Finset V} {u x y : V}
    (hu : u ∈ Q) (hx : x ∈ Q) (hy : y ∈ Q) :
    y ∈ link (retainedEdges E Q) u x ↔ y ∈ link E u x := by
  rw [mem_link, mem_link]
  constructor
  · rintro ⟨hux, hyu, hyx, B, hB, huB, hxB, hyB⟩
    obtain ⟨C, hC, rfl⟩ := mem_image.mp (mem_filter.mp hB).1
    exact ⟨hux, hyu, hyx, C, hC, (mem_inter.mp huB).1, (mem_inter.mp hxB).1, (mem_inter.mp hyB).1⟩
  · rintro ⟨hux, hyu, hyx, B, hB, huB, hxB, hyB⟩
    have hsub : ({u, x, y} : Finset V) ⊆ B ∩ Q := by
      simp [insert_subset_iff, hu, hx, hy, huB, hxB, hyB]
    have hcard : ({u, x, y} : Finset V).card = 3 := by
      rw [card_insert_of_notMem (by simp [hux, hyu.symm]), card_pair hyx.symm]
    have hsize : 3 ≤ (B ∩ Q).card := hcard ▸ card_le_card hsub
    exact ⟨hux, hyu, hyx, B ∩ Q, mem_filter.mpr ⟨mem_image_of_mem _ hB, hsize⟩,
      mem_inter.mpr ⟨huB, hu⟩, mem_inter.mpr ⟨hxB, hx⟩, mem_inter.mpr ⟨hyB, hy⟩⟩

theorem hasWitness_retained_iff {E : Finset (Finset V)} {Q A : Finset V} {x u : V}
    (hA : A ⊆ Q) (hx : x ∈ Q) (hu : u ∈ Q) :
    HasWitness (retainedEdges E Q) A x u ↔ HasWitness E A x u := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨hyA, hy⟩ := mem_inter.mp hy
    exact ⟨y, mem_inter.mpr ⟨hyA, (link_mem_retained_iff hu hx (hA hyA)).mp hy⟩⟩
  · rintro ⟨y, hy⟩
    obtain ⟨hyA, hy⟩ := mem_inter.mp hy
    exact ⟨y, mem_inter.mpr ⟨hyA, (link_mem_retained_iff hu hx (hA hyA)).mpr hy⟩⟩

theorem affected_retained_iff {E : Finset (Finset V)} {Q : Finset V}
    {s : HypergraphState V} {x u : V} (hS : s.selected ⊆ Q) (hR : s.remaining ⊆ Q)
    (hd : Disjoint s.selected s.remaining) (hx : x ∈ s.remaining) :
    HypergraphState.Affected (retainedEdges E Q) s x u ↔ HypergraphState.Affected E s x u := by
  rw [affected_iff_hasWitness hd hx, affected_iff_hasWitness hd hx]
  exact and_congr_right (fun hu => hasWitness_retained_iff hS (hR hx) (hR (mem_of_mem_erase hu)))

private theorem target_retained_eq {E : Finset (Finset V)} {Q A L B : Finset V} {v x : V}
    (hA : A ⊆ Q) (hL : L ⊆ Q) (hx : x ∈ Q) :
    targets (retainedEdges E Q) A L (B ∩ Q) v x = targets E A L B v x := by
  ext u
  simp only [targets, mem_filter, mem_inter]
  constructor
  · rintro ⟨⟨huB, huQ⟩, huL, huv, hw⟩
    exact ⟨huB, huL, huv, (hasWitness_retained_iff hA hx huQ).mp hw⟩
  · rintro ⟨huB, huL, huv, hw⟩
    exact ⟨⟨huB, hL huL⟩, huL, huv, (hasWitness_retained_iff hA hx (hL huL)).mpr hw⟩

private theorem gate_retained_iff {E : Finset (Finset V)} {Q A : Finset V} {v x : V}
    (hA : A ⊆ Q) (hx : x ∈ Q) (hv : v ∈ Q) (p : SixVertexPattern) :
    centerGate (retainedEdges E Q) A v x p ↔ centerGate E A v x p := by
  cases p
  · rfl
  · exact hasWitness_retained_iff hA hx hv

def traceIncidence (Q : Finset V) (i : Incidence V) : Incidence V := ⟨i.1 ∩ Q, i.2⟩

private theorem trace_incidence_mem_iff {E : Finset (Finset V)} {Q A L B U : Finset V}
    {v x : V} (hA : A ⊆ Q) (hL : L ⊆ Q) (hx : x ∈ Q) (hv : v ∈ Q)
    (hB : B ∈ E) (p : SixVertexPattern) :
    (⟨B ∩ Q, U⟩ : Incidence V) ∈ incidences (retainedEdges E Q) Q A L v x p ↔
      (⟨B, U⟩ : Incidence V) ∈ incidences E Q A L v x p := by
  simp only [incidences, mem_sigma, mem_filter]
  rw [target_retained_eq hA hL hx, gate_retained_iff hA hx hv p, inter_assoc, inter_self]
  simp [retainedEdges, mem_image_of_mem _ hB, hB, hv, hx, and_assoc, and_left_comm, and_comm]

theorem image_incidences_retained {E : Finset (Finset V)} {Q A L : Finset V}
    {v x : V} (hA : A ⊆ Q) (hL : L ⊆ Q) (hx : x ∈ Q) (hv : v ∈ Q)
    (p : SixVertexPattern) :
    (incidences E Q A L v x p).image (traceIncidence Q) =
      incidences (retainedEdges E Q) Q A L v x p := by
  classical
  ext i
  rw [mem_image]
  constructor
  · rintro ⟨⟨B, U⟩, hi, rfl⟩
    have hB := (mem_filter.mp (mem_sigma.mp hi).1).1
    exact (trace_incidence_mem_iff hA hL hx hv hB p).mpr hi
  · rcases i with ⟨C, U⟩
    intro hi
    have hC := (mem_filter.mp (mem_sigma.mp hi).1).1
    obtain ⟨B, hB, rfl⟩ := mem_image.mp (mem_filter.mp hC).1
    exact ⟨⟨B, U⟩, (trace_incidence_mem_iff hA hL hx hv hB p).mp hi, rfl⟩

/-- An original edge with a retained trace of size at least three is determined
by that trace. Consequently the G and H incidence counts are exactly the
counts on the retained edge family used by the local inequalities. -/
theorem card_incidences_retained {E : Finset (Finset V)} (hE : Linear E)
    {Q A L : Finset V} {v x : V} (hA : A ⊆ Q) (hL : L ⊆ Q) (hx : x ∈ Q) (hv : v ∈ Q)
    (p : SixVertexPattern) :
    (incidences (retainedEdges E Q) Q A L v x p).card =
      (incidences E Q A L v x p).card := by
  classical
  rw [← image_incidences_retained hA hL hx hv p]
  apply card_image_iff.mpr
  rintro ⟨B, U⟩ hBU ⟨C, W⟩ hCW h
  have heq : B ∩ Q = C ∩ Q := congrArg Sigma.fst h
  have hUW : U = W := congrArg (fun i : Incidence V => i.2) h
  have hB := mem_filter.mp (mem_sigma.mp hBU).1
  have hC := mem_filter.mp (mem_sigma.mp hCW).1
  have hBC : B = C := by
    by_contra hn
    have hsub : B ∩ Q ⊆ B ∩ C := subset_inter inter_subset_left (heq.symm ▸ inter_subset_left)
    have hlarge : 3 ≤ (B ∩ Q).card := hB.2.2.2.1
    have hsmall := hE B hB.1 C hC.1 hn
    exact (by omega : ¬ 3 ≤ (B ∩ C).card) (hlarge.trans (card_le_card hsub))
  subst C
  subst W
  rfl

end OMA.GeneralPositionLoss

/-! The history flag in the proof of Lemma 9 of Thang Pham, Le Quang-Ham
and Boqing Xue, "General-position sets and linear hypergraphs", §2.3,
arXiv:2610.34254v1. It is auxiliary to the original selection process. -/

namespace OMA.GeneralPositionHistory
open Finset OMA.OnlineSelection OMA.OnlineSelection.HypergraphState
open OMA.GeneralPositionPotential

variable {V : Type*} [DecidableEq V]

structure History (V : Type*) where
  base : HypergraphState V
  live : Bool

/-- Before v is processed, retain the flag only on paths with positive
current potential. On v's own step retain the flag only on acceptance.
After its turn, freeze the flag. The base keeps running either way. -/
noncomputable def nextFlag (E : Finset (Finset V)) (v : V) (a τ σ lam : ℝ)
    (x : V) (b : Bool) (t : History V) : Bool := by
  classical
  exact if v ∈ t.base.remaining then
    decide (0 < potential t.live E t.base v a τ σ lam) && (decide (x ≠ v) || b)
    else t.live

noncomputable def lifted (E : Finset (Finset V)) (v : V) (a τ σ lam : ℝ) :
    Rule V (History V) where
  chance x t := t.base.weight x
  next x b t := ⟨advance E τ x b t.base, nextFlag E v a τ σ lam x b t⟩

theorem expect_project (E : Finset (Finset V)) (v : V) (a τ σ lam : ℝ)
    (xs : List V) (t : History V) (f : List V → HypergraphState V → ℝ) :
    (lifted E v a τ σ lam).expect xs t (fun A u => f A u.base) =
      (process E τ).expect xs t.base f := by
  induction xs generalizing t f with
  | nil => rfl
  | cons x xs ih =>
    rw [Rule.expect, Rule.expect]
    rw [ih _ (fun A s => f (x::A) s), ih _ f]
    rfl

theorem losses_project (E : Finset (Finset V)) (v : V) (a τ σ lam : ℝ)
    (xs : List V) (t : History V) (loss : V → List V → HypergraphState V → ℝ) :
    (lifted E v a τ σ lam).expectedLosses (fun x ys u => loss x ys u.base) xs t =
      (process E τ).expectedLosses loss xs t.base :=
  OMA.GeneralPositionLoss.expectedLosses_project (lifted E v a τ σ lam) (process E τ)
    History.base (fun _ _ => rfl) (fun _ _ _ => rfl) loss xs t

theorem lifted_capped (E : Finset (Finset V)) (v : V) {a τ σ lam : ℝ}
    (hτ : 0 ≤ τ) (hτ1 : τ < 1) :
    (lifted E v a τ σ lam).Capped (fun t => WeightsIn τ t.base) τ := by
  have h := process_capped E hτ hτ1
  exact ⟨h.cap_nonneg, h.cap_le_one, fun x t ht => h.chance_bounds x t.base ht,
    fun x b t ht => h.next_valid x b t.base ht⟩

/-- Before v's turn use the displayed positive-part potential. After the
turn the flag gates the persistent indicator of membership in the selected set. -/
noncomputable def value (E : Finset (Finset V)) (v : V) (a τ σ lam : ℝ)
    (xs : List V) (t : History V) : ℝ :=
  if v ∈ xs then potential t.live E t.base v a τ σ lam
  else if t.live = true ∧ v ∈ t.base.selected then 1 else 0

theorem dead_absorbing (E : Finset (Finset V)) (v : V) (a τ σ lam : ℝ)
    (x : V) (b : Bool) (s : HypergraphState V) :
    nextFlag E v a τ σ lam x b ⟨s,false⟩ = false := by
  by_cases hv : v ∈ s.remaining <;> simp [nextFlag, hv, potential]

theorem terminal_value_le (E : Finset (Finset V)) (v : V) (a τ σ lam : ℝ) (t : History V) :
    value E v a τ σ lam [] t ≤ if v ∈ t.base.selected then (1:ℝ) else 0 := by
  by_cases h : v ∈ t.base.selected <;> cases hl : t.live <;> simp [value, h, hl]

/-- The base's terminal selected set equals the accepted list, when started
with empty selection. Thus bounding by its indicator gives the usual marginal. -/
theorem terminal_selection_eq_joint (E : Finset (Finset V)) (v : V) (τ a : ℝ)
    (Q : Finset V) (xs : List V) :
    (process E τ).expect xs (initial Q a) (fun _ t => if v ∈ t.selected then (1:ℝ) else 0) =
      (process E τ).joint xs (initial Q a) {v} := by
  rw [Rule.joint, Rule.expect_eq_outcomes_sum, Rule.expect_eq_outcomes_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro o ho
  have he := outcome_selected_eq E τ (s := initial Q a) ho
  simp only [initial, empty_union] at he
  simp [he]

end OMA.GeneralPositionHistory

namespace OMA.GeneralPositionHistory
open Finset OMA.OnlineSelection OMA.OnlineSelection.HypergraphState
open OMA.GeneralPositionPotential

variable {V : Type*} [DecidableEq V]

/-- Invariants available along positive-weight branches of the actual order. -/
structure Valid (E : Finset (Finset V)) (a : ℝ) (xs : List V) (s : HypergraphState V) : Prop where
  remaining : s.remaining = xs.toFinset
  nodup : xs.Nodup
  safe : Safe E s
  floor : WeightFloor a s

theorem initial_valid (E : Finset (Finset V)) (a : ℝ) {xs : List V} (hxs : xs.Nodup) :
    Valid E a xs (initial xs.toFinset a) :=
  ⟨rfl,hxs,initial_safe E _ _,initial_floor _ _⟩

theorem next_valid {E : Finset (Finset V)} {a τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ < 1) (haτ : a ≤ τ)
    {x : V} {xs : List V} {s : HypergraphState V} (hs : WeightsIn τ s) (hv : Valid E a (x::xs) s)
    (b : Bool) (hb : 0 < (if b then s.weight x else 1-s.weight x)) :
    Valid E a xs (advance E τ x b s) := by
  obtain ⟨hx,hxs⟩ := List.nodup_cons.mp hv.nodup
  have hrem : x ∈ s.remaining := by rw [hv.remaining]; simp
  refine ⟨?_,hxs,advance_safe hτ hv.safe hrem b (by rintro rfl; exact hb),advance_floor hτ hτ1 haτ hs hv.floor x b⟩
  change s.remaining.erase x = xs.toFinset
  rw [hv.remaining,List.toFinset_cons,erase_insert (fun h => hx (List.mem_toFinset.mp h))]

/-- Only the two live pre-turn estimates (2.5) and (2.6) are external.
Their premises refer entirely to the original hypergraph state. -/
def LocalBound (kind : Bool) (E : Finset (Finset V)) (v : V) (a τ σ lam : ℝ)
    (loss : V → List V → HypergraphState V → ℝ) : Prop :=
  ∀ (x : V) (tail : List V) (s : HypergraphState V), WeightsIn τ s → Valid E a (x::tail) s →
    v ∈ tail → (Affected E s x v ↔ kind = true) →
    0 < potential true E s v a τ σ lam →
    potential true E s v a τ σ lam ≤
      s.weight x * potential true E (advance E τ x true s) v a τ σ lam +
      (1-s.weight x) * potential true E (advance E τ x false s) v a τ σ lam +
      loss x tail s

omit [DecidableEq V] in
private theorem weighted_const (q c : ℝ) : q*c + (1-q)*c = c := by ring

/-- The stopped value meets the telescope's local premise at every step.
The tracked vertex's own step and the already-frozen suffix require no local
geometric estimates. -/
theorem step_bound {E : Finset (Finset V)} {v : V} {a τ σ lam : ℝ}
    (ha : 0 < a) (haτ : a < τ) (hσ : 0 < σ) (hlam : 0 ≤ lam)
    (loss : V → List V → HypergraphState V → ℝ)
    (hzero : ∀ x tail s, WeightsIn τ s → Valid E a (x::tail) s → 0 ≤ loss x tail s)
    (case1 : LocalBound false E v a τ σ lam loss) (case2 : LocalBound true E v a τ σ lam loss)
    (x : V) (tail : List V) (t : History V) (hs : WeightsIn τ t.base) (hvalid : Valid E a (x::tail) t.base) :
    value E v a τ σ lam (x::tail) t ≤
      t.base.weight x * value E v a τ σ lam tail ((lifted E v a τ σ lam).next x true t) +
      (1-t.base.weight x) * value E v a τ σ lam tail ((lifted E v a τ σ lam).next x false t) +
      loss x tail t.base := by
  classical
  have hloss := hzero x tail t.base hs hvalid
  have hown := potential_le_weight t.live v ha haτ hσ hlam hs hvalid.floor (E := E)
  by_cases hin : v ∈ x::tail
  · have hrem : v ∈ t.base.remaining := by simpa [hvalid.remaining] using hin
    have hvalue : value E v a τ σ lam (x::tail) t = potential t.live E t.base v a τ σ lam := if_pos hin
    rw [hvalue]
    by_cases hp : 0 < potential t.live E t.base v a τ σ lam
    · have hflag : t.live = true := by
        cases hh : t.live <;> simp_all [potential]
      by_cases heq : x = v
      · subst x
        have htail := (List.nodup_cons.mp hvalid.nodup).1
        have hyes : value E v a τ σ lam tail ((lifted E v a τ σ lam).next v true t) = 1 := by
          simp [value, htail, lifted, nextFlag, hrem, hp, advance]
        have hno : value E v a τ σ lam tail ((lifted E v a τ σ lam).next v false t) = 0 := by
          simp [value, htail, lifted, nextFlag, hrem, hp, advance]
        rw [hyes,hno]
        linarith [hown.2]
      · have htail : v ∈ tail := (List.mem_cons.mp hin).resolve_left (Ne.symm heq)
        have hbranch (b : Bool) :
            value E v a τ σ lam tail ((lifted E v a τ σ lam).next x b t) =
              potential true E (advance E τ x b t.base) v a τ σ lam := by
          simp [value, htail, lifted, nextFlag, hrem, hp, heq]
        rw [hbranch,hbranch,hflag]
        rw [hflag] at hp
        by_cases hA : Affected E t.base x v
        · exact case2 x tail t.base hs hvalid htail (by simp [hA]) hp
        · exact case1 x tail t.base hs hvalid htail (by simp [hA]) hp
    · have he := le_antisymm (le_of_not_gt hp) hown.1
      have hbranch (b : Bool) : value E v a τ σ lam tail ((lifted E v a τ σ lam).next x b t) = 0 := by
        have hf : nextFlag E v a τ σ lam x b t = false := by simp [nextFlag, hrem, hp]
        by_cases htail : v ∈ tail <;> simp [value, htail, lifted, hf, potential]
      rw [hbranch,hbranch,he]
      simpa using hloss
  · have hrem : v ∉ t.base.remaining := by simpa [hvalid.remaining] using hin
    have htail : v ∉ tail := fun hv => hin (List.mem_cons_of_mem _ hv)
    have hne : v ≠ x := fun h => hin (List.mem_cons.mpr (Or.inl h))
    have hbranch (b : Bool) : value E v a τ σ lam tail ((lifted E v a τ σ lam).next x b t) =
        value E v a τ σ lam (x::tail) t := by
      cases b <;> simp [value, htail, hin, lifted, nextFlag, hrem, advance, hne]
    rw [hbranch,hbranch,weighted_const]
    linarith

end OMA.GeneralPositionHistory

namespace OMA.GeneralPositionHistory
open Finset OMA.OnlineSelection OMA.OnlineSelection.HypergraphState
open OMA.GeneralPositionPotential

variable {V : Type*} [DecidableEq V]

/-- Fixed-order bridge for any retained set, including v outside that set.
The loss and the terminal singleton probability both use the original rule. -/
theorem initial_le_joint_add_losses {E : Finset (Finset V)} {v : V} {a τ σ lam : ℝ}
    (ha : 0 < a) (haτ : a < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hlam : 0 ≤ lam)
    (loss : V → List V → HypergraphState V → ℝ)
    (hzero : ∀ x tail s, WeightsIn τ s → Valid E a (x::tail) s → 0 ≤ loss x tail s)
    (case1 : LocalBound false E v a τ σ lam loss) (case2 : LocalBound true E v a τ σ lam loss)
    {Q : Finset V} (xs : List V) (hxs : xs.Nodup) (hQ : xs.toFinset = Q) :
    potential true E (initial Q a) v a τ σ lam ≤ (process E τ).joint xs (initial Q a) {v} +
      (process E τ).expectedLosses loss xs (initial Q a) := by
  classical
  subst Q
  let R := lifted E v a τ σ lam
  let t : History V := ⟨initial xs.toFinset a,true⟩
  let I (s : History V) := WeightsIn τ s.base
  let P (ys : List V) (s : History V) := I s ∧ Valid E a ys s.base
  have hc : R.Capped I τ := lifted_capped E v (ha.trans haτ).le hτ1
  have hi : I t := fun _ => ⟨ha.le,haτ.le⟩
  have hp : P xs t := ⟨hi,initial_valid E a hxs⟩
  have hn (x : V) (ys : List V) (s : History V) (b : Bool) (h : P (x::ys) s)
      (hb : 0 < (if b then R.chance x s else 1-R.chance x s)) : P ys (R.next x b s) :=
    ⟨hc.next_valid x b s h.1, next_valid (ha.trans haτ).le hτ1 haτ.le h.1 h.2 b hb⟩
  have ht := R.potential_le_terminal_add_losses hc hn (value E v a τ σ lam)
    (fun x ys s => loss x ys s.base)
    (fun x ys s hw h => step_bound ha haτ hσ hlam loss hzero case1 case2 x ys s hw h.2) xs hi hp
  have hi_eq : potential true E (initial xs.toFinset a) v a τ σ lam = value E v a τ σ lam xs t := by
    by_cases hv : v ∈ xs
    · simp [value,hv,t]
    · simp [value,hv,t,potential,initial]
  have hterm : R.expect xs t (fun _ s => value E v a τ σ lam [] s) ≤
      (process E τ).joint xs t.base {v} := by
    calc
      _ ≤ R.expect xs t (fun _ s => if v ∈ s.base.selected then 1 else 0) :=
        R.expect_mono hc xs hi (fun _ _ s _ => terminal_value_le E v a τ σ lam s)
      _ = (process E τ).expect xs t.base (fun _ s => if v ∈ s.selected then 1 else 0) :=
        expect_project E v a τ σ lam xs t (fun _ s => if v ∈ s.selected then (1:ℝ) else 0)
      _ = _ := terminal_selection_eq_joint E v τ a xs.toFinset xs
  rw [hi_eq]
  exact ht.trans <| add_le_add hterm (losses_project E v a τ σ lam xs t loss).le

end OMA.GeneralPositionHistory

/-! Use the existing fixed-order configuration bound on the original edge
labels, even though the stopped potential and its branch premises use traces. -/

namespace OMA.GeneralPositionHistory
open Finset OMA.OnlineSelection OMA.OnlineSelection.HypergraphState
open OMA.GeneralPositionPotential OMA.GeneralPositionLoss OMA.GeneralPositionCodegrees

variable {V : Type*} [DecidableEq V]

private structure InOrder (Q : Finset V) (xs : List V) (s : HypergraphState V) : Prop where
  selected : s.selected ⊆ Q
  remaining : s.remaining = xs.toFinset
  within : s.remaining ⊆ Q
  disjoint : Disjoint s.selected s.remaining
  nodup : xs.Nodup

private theorem InOrder.advance {Q : Finset V} {xs : List V} {x : V} {s : HypergraphState V}
    (h : InOrder Q (x::xs) s) (E : Finset (Finset V)) (τ : ℝ) (b : Bool) :
    InOrder Q xs (HypergraphState.advance E τ x b s) := by
  have hx : x ∈ s.remaining := by rw [h.remaining]; simp
  have hel : s.remaining.erase x = xs.toFinset := by
    rw [h.remaining,List.toFinset_cons,erase_insert (by simpa using (List.nodup_cons.mp h.nodup).1)]
  refine ⟨?_,hel,(erase_subset _ _).trans h.within,?_,(List.nodup_cons.mp h.nodup).2⟩
  · cases b
    · exact h.selected
    · exact insert_subset (h.within hx) h.selected
  · cases b
    · exact h.disjoint.mono_right (erase_subset _ _)
    · apply disjoint_left.mpr
      intro u hu hrem
      rcases mem_insert.mp hu with heq | hsel
      · exact (mem_erase.mp hrem).1 heq
      · exact disjoint_left.mp h.disjoint hsel (mem_of_mem_erase hrem)

private theorem advance_trace_eq (E : Finset (Finset V)) {Q : Finset V} {x : V} {xs : List V}
    {s : HypergraphState V} (h : InOrder Q (x::xs) s) (τ : ℝ) (b : Bool) :
    advance (retainedEdges E Q) τ x b s = advance E τ x b s := by
  have hx : x ∈ s.remaining := by rw [h.remaining]; simp
  unfold advance
  congr 1
  funext u
  have he := affected_retained_iff (E := E) (u := u) h.selected h.within h.disjoint hx
  by_cases hu : Affected E s x u
  · simp [updateWeight, hu, he.mpr hu]
  · have ht := mt he.mp hu
    simp [updateWeight, hu, ht]

/-- The nonnegative sum of the two incidence costs from (2.5) and (2.6). -/
noncomputable def paperLoss (E : Finset (Finset V)) (Q : Finset V) (v : V) (τ σ : ℝ)
    (x : V) (xs : List V) (s : HypergraphState V) : ℝ :=
  localLoss E Q v .twoNeighbors (8*τ^3/σ^2) x xs s +
  localLoss E Q v .centerAndNeighbor (16*τ^2/σ) x xs s

private theorem paperLoss_nonneg (E : Finset (Finset V)) (Q : Finset V) (v : V) {τ σ : ℝ}
    (hτ : 0 ≤ τ) (hσ : 0 < σ) (x : V) (xs : List V) (s : HypergraphState V) (hs : WeightsIn τ s) :
    0 ≤ paperLoss E Q v τ σ x xs s := by
  have := (hs x).1
  unfold paperLoss localLoss
  positivity

omit [DecidableEq V] in
private theorem losses_eq_on {S : Type*} (L R : Rule V S)
    (I : List V → S → Prop) (f g : V → List V → S → ℝ)
    (hchance : ∀ x s, L.chance x s = R.chance x s)
    (hnext : ∀ x tail s b, I (x::tail) s → L.next x b s = R.next x b s)
    (hinv : ∀ x tail s b, I (x::tail) s → I tail (R.next x b s))
    (hloss : ∀ x tail s, I (x::tail) s → f x tail s = g x tail s)
    (xs : List V) (s : S) (hs : I xs s) : L.expectedLosses f xs s = R.expectedLosses g xs s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x tail ih =>
    rw [Rule.expectedLosses,Rule.expectedLosses, hchance, hloss x tail s hs,
      hnext x tail s true hs,hnext x tail s false hs,
      ih _ (hinv x tail s true hs),ih _ (hinv x tail s false hs)]

private theorem paperLoss_trace_eq {E : Finset (Finset V)} (hE : Linear E) {v : V} {Q : Finset V}
    (hv : v ∈ Q) (τ σ : ℝ) (x : V) (tail : List V) (s : HypergraphState V) (hs : InOrder Q (x::tail) s) :
    paperLoss (retainedEdges E Q) Q v τ σ x tail s = paperLoss E Q v τ σ x tail s := by
  have hx : x ∈ s.remaining := by rw [hs.remaining]; simp
  have ht : tail.toFinset ⊆ Q := by
    intro u hu
    apply hs.within
    rw [hs.remaining,List.toFinset_cons]
    exact mem_insert_of_mem hu
  unfold paperLoss localLoss
  rw [card_incidences_retained hE hs.selected ht (hs.within hx) hv .twoNeighbors,
    card_incidences_retained hE hs.selected ht (hs.within hx) hv .centerAndNeighbor]

private theorem losses_trace_eq {E : Finset (Finset V)} (hE : Linear E) {v : V} {Q : Finset V}
    (hv : v ∈ Q) (τ σ : ℝ) (xs : List V) {s : HypergraphState V} (hs : InOrder Q xs s) :
    (process (retainedEdges E Q) τ).expectedLosses (paperLoss (retainedEdges E Q) Q v τ σ) xs s =
      (process E τ).expectedLosses (paperLoss E Q v τ σ) xs s :=
  losses_eq_on (process (retainedEdges E Q) τ) (process E τ) (InOrder Q) _ _ (fun _ _ => rfl)
    (fun _ _ _ b h => advance_trace_eq E h τ b)
    (fun _ _ _ b h => h.advance E τ b) (paperLoss_trace_eq hE hv τ σ) xs s hs

/-- Counts are for the original edges, the terminal probability is for the
process on retained traces, and both local hypotheses use the retained traces.
There is no assumption that v belongs to Q. -/
theorem fixed_order_bound {E : Finset (Finset V)} (hE : Linear E) {Q : Finset V} {v : V}
    {a τ σ lam : ℝ} (ha : 0 < a) (haτ : a < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hlam : 0 ≤ lam)
    (xs : List V) (hxs : xs.Nodup) (hQ : xs.toFinset = Q)
    (case1 : LocalBound false (retainedEdges E Q) v a τ σ lam (paperLoss (retainedEdges E Q) Q v τ σ))
    (case2 : LocalBound true (retainedEdges E Q) v a τ σ lam (paperLoss (retainedEdges E Q) Q v τ σ)) :
    potential true (retainedEdges E Q) (initial Q a) v a τ σ lam ≤
      (process (retainedEdges E Q) τ).joint xs (initial Q a) {v} +
      ((8*τ^6/σ^2)*((eligible E Q v .twoNeighbors).card : ℝ) +
       (16*τ^5/σ)*((eligible E Q v .centerAndNeighbor).card : ℝ)) := by
  classical
  let F := retainedEdges E Q
  have hτ := (ha.trans haτ).le
  by_cases hv : v ∈ Q
  · have hlocal := initial_le_joint_add_losses ha haτ hτ1 hσ hlam
      (paperLoss F Q v τ σ) (fun x ys s hs _ => paperLoss_nonneg F Q v hτ hσ x ys s hs)
      case1 case2 xs hxs hQ
    have hs : InOrder Q xs (initial Q a) := ⟨empty_subset _,hQ.symm,Subset.rfl,by simp [initial],hxs⟩
    have hcount := expected_paperLoss_le hE hv hτ hτ1 ha.le haτ.le hσ xs hxs hQ
      (paperLoss E Q v τ σ) (fun _ _ _ _ _ _ _ => le_rfl)
    exact hlocal.trans (add_le_add le_rfl ((losses_trace_eq hE hv τ σ xs hs).le.trans hcount))
  · have hC : potential true F (initial Q a) v a τ σ lam = 0 := by simp [potential,initial,hv]
    change potential true F _ _ _ _ _ _ ≤ _
    rw [hC]
    have hprob : 0 ≤ (process F τ).joint xs (initial Q a) {v} :=
      (process F τ).expect_nonneg (process_capped F hτ hτ1) xs (fun _ => ⟨ha.le,haτ.le⟩)
        (fun _ _ _ _ => by split <;> norm_num)
    positivity

end OMA.GeneralPositionHistory

/-! Interfaces for using the fixed-order bound in the potential and outer
retention arguments. -/

namespace OMA.GeneralPositionLoss

open scoped BigOperators Classical
open Finset OMA.GeneralPositionCodegrees OMA.OnlineSelection

variable {V : Type*} [DecidableEq V]

theorem card_incidences_eq_sum (E : Finset (Finset V)) (Q A L : Finset V) (v x : V)
    (p : SixVertexPattern) :
    (incidences E Q A L v x p).card =
      ∑ B ∈ E.filter (fun B => v ∈ B ∧ x ∉ B ∧ 3 ≤ (B ∩ Q).card ∧ centerGate E A v x p),
        (targets E A L B v x).card.choose (markCount p) := by
  simp only [incidences, card_sigma, card_powersetCard]

/-- Rewrite eligible configurations as a sum of survival indicators over the
original configuration family. -/
theorem eligible_card_eq_sum_original (E : Finset (Finset V)) {Q S : Finset V}
    (hQS : Q ⊆ S) (v : V) (p : SixVertexPattern) :
    ((eligible E Q v p).card : ℝ) =
      ∑ w ∈ sixVertexWitnesses E S v p, if vertices v w ⊆ Q then 1 else 0 := by
  rw [eligible_eq_filter_original E hQS v p, ← sum_filter]
  simp

theorem eligible_eq_empty_of_notMem {E : Finset (Finset V)} {Q : Finset V} {v : V}
    (hv : v ∉ Q) (p : SixVertexPattern) : eligible E Q v p = ∅ := by
  apply eq_empty_of_forall_notMem
  intro w hw
  exact hv ((mem_filter.mp hw).2 (by simp [vertices]))

/-- The remaining set in a prefix outcome is the initial set minus the
processed prefix, regardless of which branches were taken. -/
theorem outcome_remaining_eq (E : Finset (Finset V)) (τ : ℝ)
    {xs : List V} {s : HypergraphState V} {o : Outcome V (HypergraphState V)}
    (ho : o ∈ (HypergraphState.process E τ).outcomes xs s) :
    o.state.remaining = s.remaining \ xs.toFinset := by
  induction xs generalizing s o with
  | nil =>
      simp only [Rule.outcomes, List.mem_singleton] at ho
      subst o
      simp
  | cons x xs ih =>
      simp only [Rule.outcomes, List.mem_append, List.mem_map] at ho
      rcases ho with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
      · have hh := ih hr
        change r.state.remaining = s.remaining.erase x \ xs.toFinset at hh
        rw [hh, List.toFinset_cons]
        ext u
        simp only [mem_sdiff, mem_erase, mem_insert]
        tauto
      · have hh := ih hr
        change r.state.remaining = s.remaining.erase x \ xs.toFinset at hh
        rw [hh, List.toFinset_cons]
        ext u
        simp only [mem_sdiff, mem_erase, mem_insert]
        tauto

/-- Immediately before processing x, the unprocessed set is x and the tail. -/
theorem prefix_remaining (E : Finset (Finset V)) (τ a : ℝ) {Q : Finset V}
    {before after : List V} {x : V} {o : Outcome V (HypergraphState V)}
    (horder : (before ++ x :: after).Nodup) (hQ : (before ++ x :: after).toFinset = Q)
    (ho : o ∈ (HypergraphState.process E τ).outcomes before (HypergraphState.initial Q a)) :
    o.state.remaining = (x :: after).toFinset := by
  rw [outcome_remaining_eq E τ ho]
  change Q \ before.toFinset = (x :: after).toFinset
  rw [← hQ, List.toFinset_append]
  ext u
  simp only [mem_sdiff, mem_union]
  constructor
  · rintro ⟨hb | ht, hn⟩
    · exact (hn hb).elim
    · exact ht
  · intro ht
    refine ⟨Or.inr ht, fun hb => ?_⟩
    exact (List.disjoint_iff_ne.mp horder.disjoint) u (List.mem_toFinset.mp hb)
      u (List.mem_toFinset.mp ht) rfl

/-- Transfer the fixed-retention estimate to a process that stores auxiliary
state, for example the absorbing flag of the stopped potential. -/
theorem expected_both_losses_le_projected {State : Type*} (R : Rule V State)
    {E : Finset (Finset V)} (hE : Linear E) {Q : Finset V} {v : V} (hv : v ∈ Q)
    {τ a cG cH : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ < 1) (ha0 : 0 ≤ a) (haτ : a ≤ τ)
    (hcG : 0 ≤ cG) (hcH : 0 ≤ cH) (order : List V) (horder : order.Nodup) (hQ : order.toFinset = Q)
    (project : State → HypergraphState V) (s : State) (hs : project s = HypergraphState.initial Q a)
    (hchance : ∀ x t, R.chance x t = (project t).weight x)
    (hnext : ∀ x b t, project (R.next x b t) = HypergraphState.advance E τ x b (project t))
    (loss : V → List V → State → ℝ)
    (hlocal : ∀ before x after, before ++ x :: after = order →
      ∀ o ∈ R.outcomes before s, 0 < o.weight →
      loss x after o.state ≤
        localLoss E Q v .twoNeighbors cG x after (project o.state) +
        localLoss E Q v .centerAndNeighbor cH x after (project o.state)) :
    R.expectedLosses loss order s ≤
      cG * τ ^ 3 * ((eligible E Q v .twoNeighbors).card : ℝ) +
      cH * τ ^ 3 * ((eligible E Q v .centerAndNeighbor).card : ℝ) := by
  let P := HypergraphState.process E τ
  let I (t : State) := HypergraphState.WeightsIn τ (project t)
  let raw (x : V) (after : List V) (t : HypergraphState V) :=
    localLoss E Q v .twoNeighbors cG x after t + localLoss E Q v .centerAndNeighbor cH x after t
  have hBase := HypergraphState.process_capped E hτ hτ1
  have hR : R.Capped I τ := by
    refine ⟨hτ, hτ1.le, ?_, ?_⟩
    · intro x t ht
      rw [hchance]
      exact ht x
    · intro x b t ht
      change HypergraphState.WeightsIn τ (project (R.next x b t))
      rw [hnext]
      exact hBase.next_valid x b (project t) ht
  have hi : I s := by
    change HypergraphState.WeightsIn τ (project s)
    rw [hs]
    exact fun _ => ⟨ha0, haτ⟩
  calc
    _ ≤ R.expectedLosses (fun x after t => raw x after (project t)) order s := by
      simp only [Rule.expectedLosses_eq_prefix_sum]
      exact expectedLossesFrom_mono R hR order [] order hi rfl hlocal
    _ = P.expectedLosses raw order (project s) :=
      expectedLosses_project R P project hchance hnext raw order s
    _ ≤ _ := by
      rw [hs]
      exact expected_both_losses_le hE hv hτ hτ1 ha0 haτ hcG hcH order horder hQ raw (by
        intros
        exact le_rfl)

end OMA.GeneralPositionLoss

/-! Parameter limits for Lemma 9 of Pham, Le Quang-Ham and Xue,
General-position sets and linear hypergraphs, arXiv:2610.34254v1. -/

namespace OMA.GeneralPositionSelection

open Filter
open scoped Topology

theorem tendsto_rpow_log {a : ℝ} (ha : a < 0) (b : ℝ) :
    Tendsto (fun n : ℝ => n ^ a * Real.log n ^ b) atTop (𝓝 0) := by
  refine ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero b (-a)
    (neg_pos.mpr ha)).comp Real.tendsto_log_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
  simp only [Function.comp_apply]
  rw [mul_comm, neg_neg, mul_comm a, ← Real.rpow_def_of_pos hn]

theorem sparsification_error_eventually {K : ℝ} (hK : 0 < K) :
    ∀ᶠ n : ℝ in atTop,
      K * n ^ 2 * Real.log n * Real.exp (-(K * n ^ (1 / 6 : ℝ)) / 2) ≤ 1 / 4 := by
  have hbase := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 18 (K / 2)
    (by positivity)).comp (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 6 by norm_num))
  have h := (tendsto_const_nhds (x := K)).mul hbase
  have h' : Tendsto (fun n : ℝ => K * n ^ 3 * Real.exp (-(K * n ^ (1 / 6 : ℝ)) / 2))
      atTop (𝓝 0) := by
    rw [show (0 : ℝ) = K * 0 by ring]
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    simp only [Function.comp_apply]
    rw [← Real.rpow_mul hn.le, show (1 / 6 : ℝ) * 18 = 3 by norm_num,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [show -(K / 2) * n ^ (1 / 6 : ℝ) = -(K * n ^ (1 / 6 : ℝ)) / 2 by ring]
    ring
  filter_upwards [h'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    eventually_gt_atTop (0 : ℝ)] with n hn hpos
  refine le_trans ?_ hn.le
  have hl := (Real.log_le_sub_one_of_pos hpos).trans (by linarith : n - 1 ≤ n)
  calc
    _ ≤ K * n ^ 2 * n * Real.exp (-(K * n ^ (1 / 6 : ℝ)) / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl (by positivity))
        (Real.exp_pos _).le
    _ = _ := by ring

end OMA.GeneralPositionSelection

namespace OMA.GeneralPositionSelection

open Filter
open scoped Topology

noncomputable def gamma (K : ℝ) : ℝ := 1 / (1000 * K)
noncomputable def p (n : ℝ) : ℝ := n ^ (-5/6 : ℝ)
noncomputable def a (K n : ℝ) : ℝ := gamma K * n ^ (-1/6 : ℝ)
noncomputable def tau (n : ℝ) : ℝ := n ^ (-19/120 : ℝ)
noncomputable def sigma (n : ℝ) : ℝ := 1 / (128 * Real.log n)
noncomputable def degreeLimit (K n : ℝ) : ℝ := K * n ^ 2 * Real.log n
noncomputable def sampledDegree (K n : ℝ) : ℝ := 20 * p n ^ 2 * degreeLimit K n
noncomputable def edgeLimit (K n : ℝ) : ℝ := 3 * K * n ^ (1/6 : ℝ) + 1

lemma gamma_pos {K : ℝ} (hK : 0 < K) : 0 < gamma K := by
  unfold gamma
  positivity

lemma pow_rpow_nat {n : ℝ} (hn : 0 ≤ n) (q : ℝ) (k : ℕ) :
    (n ^ q) ^ k = n ^ (q * (k : ℝ)) := by
  rw [Real.rpow_mul hn, Real.rpow_natCast]

theorem initial_scale {K n : ℝ} (hn : 0 < n) : p n * a K n = gamma K / n := by
  unfold p a
  rw [mul_left_comm, ← Real.rpow_add hn, show (-5/6 : ℝ) + -1/6 = -1 by ring,
    Real.rpow_neg hn.le, Real.rpow_one, div_eq_mul_inv]

lemma sampledDegree_eq {K n : ℝ} (hn : 0 < n) :
    sampledDegree K n = 20 * K * (n ^ (1/3 : ℝ) * Real.log n) := by
  unfold sampledDegree p degreeLimit
  rw [pow_rpow_nat hn.le, show n ^ (2 : ℕ) = n ^ (2 : ℝ) from (Real.rpow_natCast n 2).symm]
  norm_num only [Nat.cast_ofNat]
  calc
    _ = 20 * K * (n ^ (-5/6 * 2 : ℝ) * n ^ (2 : ℝ)) * Real.log n := by ring
    _ = _ := by
      rw [← Real.rpow_add hn, show (-5/6 * 2 + 2 : ℝ) = 1/3 by norm_num]
      ring

lemma log_ratio {K n : ℝ} (hK : 0 < K) (hn : 0 < n) :
    Real.log (tau n / a K n) = Real.log n / 120 - Real.log (gamma K) := by
  have hg := gamma_pos hK
  unfold tau a
  rw [Real.log_div (Real.rpow_pos_of_pos hn _).ne' (mul_pos hg (Real.rpow_pos_of_pos hn _)).ne',
    Real.log_mul hg.ne' (Real.rpow_pos_of_pos hn _).ne', Real.log_rpow hn, Real.log_rpow hn]
  ring

theorem initial_edge_mass_eventually {K : ℝ} (hK : 1 ≤ K) :
    ∀ᶠ n : ℝ in atTop, a K n * edgeLimit K n ≤ 1 / 32 := by
  have hK' : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hlim := tendsto_rpow_log (show (-1/6 : ℝ) < 0 by norm_num) 0
  have ha : Tendsto (a K) atTop (𝓝 0) := by
    change Tendsto (fun n : ℝ => gamma K * n ^ (-1/6 : ℝ)) atTop (𝓝 0)
    simpa only [Real.rpow_zero, mul_one, mul_zero] using
      ((tendsto_const_nhds (x := gamma K)).mul hlim)
  filter_upwards [ha.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 40)),
    eventually_gt_atTop (0 : ℝ)] with n han hn
  have heq : a K n * edgeLimit K n = 3/1000 + a K n := by
    unfold a edgeLimit gamma
    calc
      _ = (3 * K * (1 / (1000 * K))) * (n ^ (-1/6 : ℝ) * n ^ (1/6 : ℝ)) +
          (1 / (1000 * K)) * n ^ (-1/6 : ℝ) := by ring
      _ = _ := by
        rw [← Real.rpow_add hn, show (-1/6 : ℝ) + 1/6 = 0 by norm_num, Real.rpow_zero]
        have hs : (3 * K * (1 / (1000 * K)) : ℝ) = 3 / 1000 := by field_simp
        rw [hs, mul_one]
  rw [heq]
  linarith

theorem loss_scale_eventually {K : ℝ} (hK : 0 < K) :
    ∀ᶠ n : ℝ in atTop,
      256 * p n ^ 6 * degreeLimit K n ^ (7/3 : ℝ) *
        (tau n ^ 6 / sigma n ^ 2 + tau n ^ 5 / sigma n) ≤ p n * a K n / 16 := by
  let c := 256 * K ^ (7/3 : ℝ) / gamma K
  have h1 := tendsto_rpow_log (show (-17/60 : ℝ) < 0 by norm_num) (13/3)
  have h2 := tendsto_rpow_log (show (-1/8 : ℝ) < 0 by norm_num) (10/3)
  have h1' := (tendsto_const_nhds (x := (128 : ℝ)^2)).mul h1
  have h2' := (tendsto_const_nhds (x := (128 : ℝ))).mul h2
  have hnorm : Tendsto (fun n : ℝ =>
      c * ((128:ℝ)^2 * (n ^ (-17/60 : ℝ) * Real.log n ^ (13/3 : ℝ)) +
           128 * (n ^ (-1/8 : ℝ) * Real.log n ^ (10/3 : ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (tendsto_const_nhds (x := c)).mul (h1'.add h2')
  filter_upwards [hnorm.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/16)),
    eventually_gt_atTop (1 : ℝ)] with n hnormn hn
  have hn' : 0 < n := zero_lt_one.trans hn
  have hl := Real.log_pos hn
  have hg := gamma_pos hK
  have hden : 0 < p n * a K n := by rw [initial_scale hn']; positivity
  rw [show p n * a K n / 16 = (1/16) * (p n * a K n) by ring]
  apply (div_le_iff₀ hden).mp
  refine le_trans ?_ hnormn.le
  · apply le_of_eq
    rw [initial_scale hn']
    unfold p degreeLimit tau sigma
    rw [pow_rpow_nat hn'.le, pow_rpow_nat hn'.le, pow_rpow_nat hn'.le]
    norm_num only [Nat.cast_ofNat]
    rw [Real.mul_rpow (by positivity) hl.le, Real.mul_rpow hK.le (by positivity),
      show n ^ (2 : ℕ) = n ^ (2 : ℝ) from (Real.rpow_natCast n 2).symm,
      ← Real.rpow_mul hn'.le]
    have hlog2 : Real.log n ^ (2 : ℕ) = Real.log n ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
    have hx1 : n ^ (-5/6 * 6 : ℝ) * n ^ (2 * (7/3) : ℝ) * n ^ (-19/120 * 6 : ℝ) * n =
        n ^ (-17/60 : ℝ) := by
      rw [← Real.rpow_add hn', ← Real.rpow_add hn', ← Real.rpow_add_one hn'.ne']
      norm_num
    have hx2 : n ^ (-5/6 * 6 : ℝ) * n ^ (2 * (7/3) : ℝ) * n ^ (-19/120 * 5 : ℝ) * n =
        n ^ (-1/8 : ℝ) := by
      rw [← Real.rpow_add hn', ← Real.rpow_add hn', ← Real.rpow_add_one hn'.ne']
      norm_num
    have hy1 : Real.log n ^ (7/3 : ℝ) * Real.log n ^ (2 : ℕ) =
        Real.log n ^ (13/3 : ℝ) := by
      rw [hlog2, ← Real.rpow_add hl]
      norm_num
    have hy2 : Real.log n ^ (7/3 : ℝ) * Real.log n =
        Real.log n ^ (10/3 : ℝ) := by
      rw [← Real.rpow_add_one hl.ne']
      norm_num
    have hh : (128 : ℝ) * Real.log n ≠ 0 := by positivity
    dsimp [c]
    calc
      _ = (256 * K ^ (7/3 : ℝ) / gamma K) *
          ((128 : ℝ)^2 *
            ((n ^ (-5/6 * 6 : ℝ) * n ^ (2 * (7/3) : ℝ) * n ^ (-19/120 * 6 : ℝ) * n) *
             (Real.log n ^ (7/3 : ℝ) * Real.log n ^ (2 : ℕ))) +
           128 *
            ((n ^ (-5/6 * 6 : ℝ) * n ^ (2 * (7/3) : ℝ) * n ^ (-19/120 * 5 : ℝ) * n) *
             (Real.log n ^ (7/3 : ℝ) * Real.log n))) := by
          field_simp
          <;> ring
      _ = _ := by
        rw [hx1, hx2, hy1, hy2]
        norm_num [neg_div]

end OMA.GeneralPositionSelection

/-! Bounds for the two loss counts after the Bernoulli sample. -/

namespace OMA.GeneralPositionOuter

open Finset OMA.GeneralPositionSelection OMA.GeneralPositionCodegrees OMA.GeneralPositionLoss
open OMA.OnlineSelection OMA.OnlineSelection.HypergraphState
open OMA.GeneralPositionPotential OMA.GeneralPositionHistory
open scoped BigOperators Classical

variable {V : Type*} [DecidableEq V]

/-- Deleting vertices after sampling can only lower the probability of retaining all six
vertices of a witness. -/
theorem expected_eligible_le {E : Finset (Finset V)} (hE : Linear E)
    (U : Finset V) (v : V) (pattern : SixVertexPattern)
    (Q : Finset V → Finset V) (hQ : ∀ S, Q S ⊆ S)
    {p D : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hD : 1 ≤ D)
    (hdeg : ∀ u : V, (tripleDegree E u : ℝ) ≤ D) :
    ∑ S ∈ U.powerset, sampleWeight p U S * ((eligible E (Q S) v pattern).card : ℝ) ≤
      p ^ 6 * (14 * D ^ (7 / 3 : ℝ)) := by
  classical
  let W := sixVertexWitnesses E U v pattern
  have hfixed (T : Finset V) (hT : T.card = 6) :
      (∑ S ∈ U.powerset, if T ⊆ S then sampleWeight p U S else 0) ≤ p ^ 6 := by
    by_cases hs : T ⊆ U
    · rw [← Finset.sum_filter, sample_fixed p hs, hT]
    · rw [Finset.sum_eq_zero (fun S hS => if_neg fun h => hs (h.trans (mem_powerset.mp hS)))]
      positivity
  calc
    _ ≤ ∑ S ∈ U.powerset, sampleWeight p U S *
        (∑ w ∈ W, if vertices v w ⊆ S then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro S hS
      rw [eligible_card_eq_sum_original E ((hQ S).trans (mem_powerset.mp hS))]
      apply mul_le_mul_of_nonneg_left _ (sample_nonneg hp hp1 _ _)
      apply Finset.sum_le_sum
      intro w _
      by_cases h : vertices v w ⊆ Q S
      · simp [h, h.trans (hQ S)]
      · simp only [if_neg h]
        split <;> norm_num
    _ = ∑ w ∈ W, ∑ S ∈ U.powerset, if vertices v w ⊆ S then sampleWeight p U S else 0 := by
      simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_comm]
    _ ≤ ∑ _w ∈ W, p ^ 6 := by
      exact Finset.sum_le_sum (fun w hw => hfixed _ (vertices_card_of_mem hE hw))
    _ = p ^ 6 * (W.card : ℝ) := by simp [mul_comm]
    _ ≤ _ := by
      gcongr
      rw [show W = sixVertexWitnesses E U v pattern by rfl, ← card_sixVertexTuples_eq_witnesses hE]
      exact sixVertexTuples_card_le hE U v pattern hD hdeg


/-- Average the same fixed schedule on every retained set, using the
finite sampling and two independent witness-count estimates. -/
theorem sampled_joint_lower {U : Finset V} {E : Finset (Finset V)} (hE : Linear E)
    {D p t a τ σ η lam : ℝ} {v : V} (hv : v ∈ U)
    (hD : 1 ≤ D) (hp : 0 < p) (hp1 : p ≤ 1) (ha : 0 < a)
    (haτ : a < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hlam : lam = Real.exp (-(η/(2*σ))))
    (hedges : ∀ B ∈ E, B ⊆ U ∧ 3 ≤ B.card ∧ p * B.card ≤ t)
    (hdeg : ∀ u : V, (tripleDegree E u : ℝ) ≤ D)
    (hsmall : D * Real.exp (-t/2) ≤ 1/4) (hsize : a*(3*t+1) ≤ η/4)
    (hscalar : (20*p^2*D)*Real.exp (-(η/(4*σ))) + (2*a^2*(20*p^2*D))/Real.log (τ/a) ≤ 1/4)
    (hloss : 256 * p^6 * D^(7/3 : ℝ) * (τ^6/σ^2 + τ^5/σ) ≤ p*a/16)
    (case1 : ∀ S ∈ U.powerset, let Q := retained D p t E (incidentTriples E) S
      LocalBound false (retainedEdges E Q) v a τ σ lam (paperLoss (retainedEdges E Q) Q v τ σ))
    (case2 : ∀ S ∈ U.powerset, let Q := retained D p t E (incidentTriples E) S
      LocalBound true (retainedEdges E Q) v a τ σ lam (paperLoss (retainedEdges E Q) Q v τ σ)) :
    p*a/4 ≤ ∑ S ∈ U.powerset, sampleWeight p U S *
      (let Q := retained D p t E (incidentTriples E) S
       (process (retainedEdges E Q) τ).joint Q.toList (initial Q a) {v}) := by
  classical
  let Q := retained D p t E (incidentTriples E)
  let w := sampleWeight p U
  let prob S := (process (retainedEdges E (Q S)) τ).joint (Q S).toList (initial (Q S) a) {v}
  let A S := ((eligible E (Q S) v .twoNeighbors).card : ℝ)
  let B S := ((eligible E (Q S) v .centerAndNeighbor).card : ℝ)
  have hQ (S : Finset V) : Q S ⊆ S := filter_subset _ _
  have hτ := ha.le.trans haτ.le
  have hlam0 : 0 ≤ lam := hlam ▸ (Real.exp_pos _).le
  have hc₁ : 0 ≤ 8*τ^6/σ^2 := by positivity
  have hc₂ : 0 ≤ 16*τ^5/σ := by positivity
  have hb₁ := expected_eligible_le hE U v .twoNeighbors Q hQ hp.le hp1 hD hdeg
  have hb₂ := expected_eligible_le hE U v .centerAndNeighbor Q hQ hp.le hp1 hD hdeg
  change ∑ S ∈ U.powerset, w S * A S ≤ _ at hb₁
  change ∑ S ∈ U.powerset, w S * B S ≤ _ at hb₂
  have hf := initial_expectation hE hv (zero_lt_one.trans_le hD) hp hp1 ha haτ hσ hlam
    hedges (hdeg v) hsmall hsize hscalar
  have hcomp :
      3*p*a/8 ≤ (∑ S ∈ U.powerset, w S * prob S) + p*a/16 := calc
    _ ≤ ∑ S ∈ U.powerset, w S *
        (prob S + ((8*τ^6/σ^2)*A S + (16*τ^5/σ)*B S)) := by
      refine hf.trans (sum_le_sum fun S hS => mul_le_mul_of_nonneg_left ?_ (sample_nonneg hp.le hp1 U S))
      exact fixed_order_bound hE ha haτ hτ1 hσ hlam0 (Q S).toList
        (nodup_toList _) (toList_toFinset _) (case1 S hS) (case2 S hS)
    _ = (∑ S ∈ U.powerset, w S * prob S) +
        ((8*τ^6/σ^2)*(∑ S ∈ U.powerset, w S * A S) +
         (16*τ^5/σ)*(∑ S ∈ U.powerset, w S * B S)) := by
      simp only [mul_add, sum_add_distrib, Finset.mul_sum]
      congr 2 <;> exact sum_congr rfl (fun _ _ => by ring)
    _ ≤ (∑ S ∈ U.powerset, w S * prob S) +
        ((8*τ^6/σ^2)*(p^6*(14*D^(7/3 : ℝ))) + (16*τ^5/σ)*(p^6*(14*D^(7/3 : ℝ)))) :=
      add_le_add_right (add_le_add (mul_le_mul_of_nonneg_left hb₁ hc₁)
        (mul_le_mul_of_nonneg_left hb₂ hc₂)) _
    _ ≤ _ := by
      apply add_le_add_right
      refine le_trans ?_ hloss
      have h₁ : 0 ≤ p^6 * D^(7/3 : ℝ) * (τ^6/σ^2) := by
        have : 0 ≤ D := zero_le_one.trans hD
        positivity
      have h₂ : 0 ≤ p^6 * D^(7/3 : ℝ) * (τ^5/σ) := by
        have : 0 ≤ D := zero_le_one.trans hD
        positivity
      linear_combination 144*h₁ + 32*h₂
  change p*a/4 ≤ ∑ S ∈ U.powerset, w S * prob S
  have hpa := mul_pos hp ha
  linarith


end OMA.GeneralPositionOuter

/-! Turn the averaged singleton probabilities into a large independent set. -/

namespace OMA.GeneralPositionOuter

open Finset OMA.OnlineSelection OMA.OnlineSelection.HypergraphState
open OMA.GeneralPositionSelection OMA.GeneralPositionCodegrees OMA.GeneralPositionLoss
open scoped BigOperators Classical

variable {V : Type*} [DecidableEq V]

private theorem independent_from_trace {E : Finset (Finset V)} {Q I : Finset V}
    (hIQ : I ⊆ Q) (hI : Independent (retainedEdges E Q) I) : Independent E I := by
  intro B hB
  by_cases hc : 3 ≤ (B ∩ Q).card
  · have hB' : B ∩ Q ∈ retainedEdges E Q := mem_trace.mpr ⟨⟨B, hB, rfl⟩, hc⟩
    have heq : I ∩ (B ∩ Q) = I ∩ B := by
      ext x
      simp only [mem_inter]
      exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hIQ h.1⟩⟩
    simpa only [heq] using hI _ hB'
  · have hsub : I ∩ B ⊆ B ∩ Q := fun x hx =>
      mem_inter.mpr ⟨(mem_inter.mp hx).2, hIQ (mem_inter.mp hx).1⟩
    exact (card_le_card hsub).trans (by omega)

private theorem sum_singletons (R : Rule V (HypergraphState V)) (xs : List V)
    (s : HypergraphState V) (U : Finset V) (hU : xs.toFinset ⊆ U) :
    ∑ v ∈ U, R.joint xs s {v} =
      ((R.outcomes xs s).map (fun o => o.weight * (o.accepted.toFinset.card : ℝ))).sum := by
  classical
  simp only [Rule.joint, Rule.expect_eq_outcomes_sum, singleton_subset_iff]
  have h (L : List (Outcome V (HypergraphState V)))
      (hL : ∀ o ∈ L, o.accepted.toFinset ⊆ U) :
      (∑ v ∈ U, (L.map (fun o => o.weight * (if v ∈ o.accepted.toFinset then 1 else 0))).sum) =
        (L.map (fun o => o.weight * (o.accepted.toFinset.card : ℝ))).sum := by
    induction L with
    | nil => simp
    | cons o L ih =>
      simp only [List.map_cons, List.sum_cons, sum_add_distrib]
      rw [ih (fun r hr => hL r (List.mem_cons_of_mem o hr))]
      congr 1
      rw [← mul_sum]
      congr 1
      rw [← sum_filter]
      have hsub := hL o (by simp)
      have hf : U.filter (· ∈ o.accepted.toFinset) = o.accepted.toFinset := by
        ext x
        exact ⟨fun hx => (mem_filter.mp hx).2, fun hx => mem_filter.mpr ⟨hsub hx, hx⟩⟩
      rw [hf]
      simp
  apply h
  intro o ho
  -- Accepting a slot always records a member of the schedule, including zero-weight paths.
  have hsub (ys : List V) (r : HypergraphState V) (t : Outcome V (HypergraphState V))
      (ht : t ∈ R.outcomes ys r) : t.accepted.Sublist ys := by
    induction ys generalizing r t with
    | nil => simp [Rule.outcomes] at ht
             subst t
             exact List.Sublist.slnil
    | cons x ys ih =>
      simp only [Rule.outcomes, List.mem_append, List.mem_map] at ht
      rcases ht with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
      · exact (ih _ _ hz).cons_cons x
      · exact (ih _ _ hz).cons x
  exact fun _ hx => hU (List.mem_toFinset.mpr ((hsub _ _ _ ho).subset (List.mem_toFinset.mp hx)))

theorem exists_large_from_joint {U : Finset V} {E : Finset (Finset V)}
    {D p t a τ q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hτ : 0 ≤ τ) (hτ1 : τ < 1) (ha : 0 ≤ a) (haτ : a ≤ τ)
    (hj : ∀ v ∈ U, q ≤ ∑ S ∈ U.powerset, sampleWeight p U S *
      (let Q := retained D p t E (incidentTriples E) S
       (process (retainedEdges E Q) τ).joint Q.toList (initial Q a) {v})) :
    ∃ I ⊆ U, q * U.card ≤ I.card ∧ Independent E I := by
  classical
  let F := U.powerset.filter (Independent E)
  have hF : F.Nonempty := ⟨∅, mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),
    fun B hB => by simp⟩⟩
  obtain ⟨J, hJ, hmax⟩ := F.exists_max_image Finset.card hF
  refine ⟨J, mem_powerset.mp (mem_filter.mp hJ).1, ?_, (mem_filter.mp hJ).2⟩
  let Q := retained D p t E (incidentTriples E)
  have hQ S (hS : S ∈ U.powerset) : Q S ⊆ U :=
    (filter_subset _ _).trans (mem_powerset.mp hS)
  let P S := process (retainedEdges E (Q S)) τ
  let O S := (P S).outcomes (Q S).toList (initial (Q S) a)
  have hlocal S (hS : S ∈ U.powerset) :
      ∑ v ∈ U, (P S).joint (Q S).toList (initial (Q S) a) {v} ≤ J.card := by
    rw [sum_singletons _ _ _ _ (by simpa using hQ S hS)]
    change ((O S).map (fun o => o.weight * (o.accepted.toFinset.card : ℝ))).sum ≤ _
    have hn : ((O S).map Outcome.weight).sum = 1 := (P S).outcomes_normalized _ _
    have hterm o (ho : o ∈ O S) : o.weight * (o.accepted.toFinset.card : ℝ) ≤ o.weight * J.card := by
      have hvalid := (P S).outcomes_valid (process_capped _ hτ hτ1) (fun _ => ⟨ha, haτ⟩) ho
      rcases eq_or_lt_of_le hvalid.1 with hz | hpos
      · simp [← hz]
      · have hsub : o.accepted.toFinset ⊆ Q S := by
          intro v hv
          simpa using hvalid.2.1.subset (List.mem_toFinset.mp hv)
        have ho' : o ∈ (P S).outcomes (Q S).toList (initial (Q S).toList.toFinset a) := by simpa using ho
        have hi : Independent E o.accepted.toFinset :=
          independent_from_trace hsub (positive_outcome_independent _ hτ hτ1 ha haτ (nodup_toList _) ho' hpos)
        have hm := hmax o.accepted.toFinset (mem_filter.mpr ⟨mem_powerset.mpr (hsub.trans (hQ S hS)), hi⟩)
        exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hm) hvalid.1
    calc
      _ ≤ ((O S).map (fun o => o.weight * (J.card : ℝ))).sum := List.sum_le_sum hterm
      _ = J.card := by
        rw [show (O S).map (fun o => o.weight * (J.card : ℝ)) =
          ((O S).map Outcome.weight).map (fun w => w * (J.card : ℝ)) by simp]
        rw [List.sum_map_mul_right, show (fun w : ℝ => w) = id from rfl, List.map_id, hn, one_mul]
  have hmass : ∑ S ∈ U.powerset, sampleWeight p U S = 1 := by
    simpa using sample_fixed p (empty_subset U)
  calc
    _ = ∑ _v ∈ U, q := by simp [mul_comm]
    _ ≤ ∑ v ∈ U, ∑ S ∈ U.powerset, sampleWeight p U S *
        (P S).joint (Q S).toList (initial (Q S) a) {v} := sum_le_sum hj
    _ = ∑ S ∈ U.powerset, sampleWeight p U S *
        (∑ v ∈ U, (P S).joint (Q S).toList (initial (Q S) a) {v}) := by
      simp only [mul_sum]
      rw [sum_comm]
    _ ≤ ∑ S ∈ U.powerset, sampleWeight p U S * (J.card : ℝ) :=
      sum_le_sum (fun S hS => mul_le_mul_of_nonneg_left (hlocal S hS) (sample_nonneg hp hp1 U S))
    _ = _ := by rw [← sum_mul, hmass, one_mul]


end OMA.GeneralPositionOuter

namespace OMA.GeneralPositionOuter

open Filter OMA.GeneralPositionSelection
open scoped Topology

private theorem initial_product_eventually (K : ℝ) :
    ∀ᶠ n : ℝ in atTop, sampledDegree K n * Real.exp (-((1/8 : ℝ)/(4*sigma n))) ≤ 1/16 := by
  have h := (tendsto_const_nhds (x := 20*K)).mul
    (tendsto_rpow_log (show (-11/3 : ℝ) < 0 by norm_num) 1)
  simp only [Real.rpow_one, mul_zero] at h
  filter_upwards [h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/16)),
    eventually_gt_atTop (1 : ℝ)] with n hn h1
  have hn0 := zero_lt_one.trans h1
  have hlog := Real.log_pos h1
  have heq : -((1/8 : ℝ)/(4*sigma n)) = -4 * Real.log n := by
    unfold sigma
    field_simp
    ring
  rw [sampledDegree_eq hn0, heq, mul_comm (-4 : ℝ), ← Real.rpow_def_of_pos hn0]
  calc
    _ = 20*K * (n ^ (1/3 : ℝ) * n ^ (-4 : ℝ)) * Real.log n := by ring
    _ = 20*K * (n ^ (-11/3 : ℝ) * Real.log n) := by
      rw [← Real.rpow_add hn0, show (1/3 : ℝ) + -4 = -11/3 by norm_num]
      ring
    _ ≤ _ := hn.le

private theorem initial_phi_small {K n : ℝ} (hK : 1 ≤ K) (hn : 1 < n)
    (hL : 1 ≤ Real.log (tau n / a K n)) :
    2 * a K n ^ 2 * sampledDegree K n / Real.log (tau n / a K n) ≤ 1/16 := by
  have hk := zero_lt_one.trans_le hK
  have hn0 := zero_lt_one.trans hn
  have hlog := Real.log_pos hn
  have hg := gamma_pos hk
  have hg1 : gamma K ≤ 1 := by
    unfold gamma
    exact (div_le_one (by positivity)).2 (by linarith)
  have hlogγ := Real.log_nonpos hg.le hg1
  have hratio : Real.log n ≤ 120 * Real.log (tau n / a K n) := by
    rw [log_ratio hk hn0]
    linarith
  have hnum : 2 * a K n ^ 2 * sampledDegree K n = 40*K*gamma K^2*Real.log n := by
    rw [sampledDegree_eq hn0, a, mul_pow, pow_rpow_nat hn0.le]
    norm_num only [Nat.cast_ofNat]
    calc
      _ = 40*K*gamma K^2*(n ^ (-1/6*2 : ℝ) * n ^ (1/3 : ℝ))*Real.log n := by ring
      _ = _ := by rw [← Real.rpow_add hn0, show (-1/6*2 : ℝ) + 1/3 = 0 by norm_num, Real.rpow_zero, mul_one]
  have hγ : 4800*K*gamma K^2 ≤ 1/16 := by
    calc
      _ = 4800 / (1000000*K) := by
        unfold gamma
        field_simp
        ring
      _ ≤ _ := (div_le_iff₀ (by positivity)).2 (by linarith)
  rw [hnum]
  apply (div_le_iff₀ (by linarith : 0 < Real.log (tau n / a K n))).2
  calc
    _ ≤ (40*K*gamma K^2)*(120 * Real.log (tau n / a K n)) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = (4800*K*gamma K^2)*Real.log (tau n / a K n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hγ (by linarith)

theorem selection_parameters_eventually {K : ℝ} (hK : 1 ≤ K) :
    ∀ᶠ n : ℝ in atTop,
      1 < n ∧ 1 ≤ degreeLimit K n ∧
      0 < p n ∧ p n ≤ 1 ∧
      0 < a K n ∧ a K n < tau n ∧ tau n ≤ 1/4 ∧ tau n ≤ sigma n ∧ sigma n ≤ 1 ∧
      2*tau n*(1/8)/sigma n ≤ Real.log 2 ∧ 1 ≤ Real.log (tau n / a K n) ∧
      degreeLimit K n * Real.exp (-(K * n ^ (1/6 : ℝ))/2) ≤ 1/4 ∧
      a K n * (3*(K * n ^ (1/6 : ℝ))+1) ≤ (1/8)/4 ∧
      sampledDegree K n * Real.exp (-((1/8)/(4*sigma n))) +
        2*a K n^2*sampledDegree K n/Real.log (tau n/a K n) ≤ 1/4 ∧
      256 * p n^6 * degreeLimit K n^(7/3 : ℝ) *
        (tau n^6/sigma n^2 + tau n^5/sigma n) ≤ p n*a K n/16 := by
  have hk := zero_lt_one.trans_le hK
  have hg := gamma_pos hk
  have hg1 : gamma K ≤ 1 := by
    unfold gamma
    exact (div_le_one (by positivity)).2 (by linarith)
  have hτ := tendsto_rpow_log (show (-19/120 : ℝ) < 0 by norm_num) 0
  have htlog := tendsto_rpow_log (show (-19/120 : ℝ) < 0 by norm_num) 1
  simp only [Real.rpow_zero, mul_one] at hτ
  simp only [Real.rpow_one] at htlog
  filter_upwards [eventually_gt_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (120 : ℝ),
      hτ.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4)),
      htlog.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/128)),
      sparsification_error_eventually hk, initial_edge_mass_eventually hK,
      initial_product_eventually K, loss_scale_eventually hk] with
    n hn hl ht htl hsmall hmass hprod hloss
  have hn0 := zero_lt_one.trans hn
  have hlog := Real.log_pos hn
  have hL : 1 ≤ Real.log (tau n / a K n) := by
    rw [log_ratio hk hn0]
    linarith [Real.log_nonpos hg.le hg1]
  have ha0 : 0 < a K n := by unfold a; positivity
  have ht0 : 0 < tau n := Real.rpow_pos_of_pos hn0 _
  have haτ : a K n < tau n := by
    by_contra! h
    have hle := Real.log_nonpos (div_nonneg ht0.le ha0.le) ((div_le_one ha0).2 h)
    linarith
  have hσ : 0 < sigma n := by unfold sigma; positivity
  have hτσ : tau n ≤ sigma n := by
    unfold sigma
    apply (le_div_iff₀ (by positivity : 0 < 128*Real.log n)).2
    change n ^ (-19/120 : ℝ) * (128 * Real.log n) ≤ 1
    linarith [show n ^ (-19/120 : ℝ) * (128 * Real.log n) =
      128 * (n ^ (-19/120 : ℝ) * Real.log n) by ring]
  have hσ1 : sigma n ≤ 1 := by
    unfold sigma
    apply (div_le_one (by positivity : 0 < 128*Real.log n)).2
    linarith
  have hscale : 2*tau n*(1/8)/sigma n ≤ Real.log 2 := by
    have hlog2 : (1/2 : ℝ) ≤ Real.log 2 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < (2:ℝ)⁻¹)
      rw [Real.log_inv] at h
      norm_num at h ⊢
      linarith
    apply (div_le_iff₀ hσ).2
    calc
      _ ≤ (1/2 : ℝ) * sigma n := by linarith [hτσ, ht0.le, hσ.le]
      _ ≤ _ := mul_le_mul_of_nonneg_right hlog2 hσ.le
  have hD : 1 ≤ degreeLimit K n := by
    unfold degreeLimit
    have hnn : (1 : ℝ) ≤ n^2 := by nlinarith
    have hln : (1 : ℝ) ≤ Real.log n := by linarith
    calc
      (1 : ℝ) = 1*1*1 := by ring
      _ ≤ _ := by gcongr
  have hscalar := initial_phi_small hK hn hL
  refine ⟨hn,hD,Real.rpow_pos_of_pos hn0 _, ?_,ha0,haτ,ht.le,hτσ,hσ1,hscale,hL,?_,?_,?_,hloss⟩
  · exact Real.rpow_le_one_of_one_le_of_nonpos hn.le (by norm_num)
  · exact hsmall
  · calc
      _ = a K n * edgeLimit K n := by unfold edgeLimit; ring
      _ ≤ 1/32 := hmass
      _ = (1/8)/4 := by norm_num
  · linarith


end OMA.GeneralPositionOuter

/-! Common-edge terms in the proof of Lemma 9, §2.3 ("Changes in one step")
of Thang Pham, Le Quang-Ham and Boqing Xue, "General-position sets and
linear hypergraphs", arXiv:2610.34254v1. -/

namespace OMA.GeneralPositionCommonEdge
open Finset
open OMA.GeneralPositionProducts
open scoped Classical

variable {V : Type*} [DecidableEq V]

private theorem log_half {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) :
    r / 2 ≤ Real.log (1 + r) := by
  apply le_trans _ (Real.le_log_one_add_of_nonneg hr)
  apply (le_div_iff₀ (by linarith : 0 < r + 2)).mpr
  nlinarith [mul_nonneg hr (sub_nonneg.mpr hr')]

/-- Removing the current vertex x saves the factor 1+q/σ. It pays for
inflation of every remaining factor on rejection, including the actual cap. -/
theorem reject_product (R : Finset V) (z : V → ℝ) (hz : ∀ x ∈ R, 0 ≤ z x)
    {q τ σ : ℝ} (hq : 0 ≤ q) (hquarter : q ≤ 1/4) (hσ : 0 < σ)
    (hqσ : q ≤ σ) (hτ : 0 ≤ τ) (hmass : (∑ x ∈ R, z x) + q < 1/8) :
    edgeProduct R (onReject R z q τ) σ ≤ (1 + q/σ) * edgeProduct R z σ := by
  classical
  have hs : 0 < 1-q := by linarith
  let b := fun x => 1 + z x / σ
  let a := fun x => 1 + onReject R z q τ x / σ
  have hb (x) (hx : x ∈ R) : 0 < b x := by dsimp [b]; have := hz x hx; positivity
  have ha (x) (hx : x ∈ R) : 0 < a x := by
    simp only [a, onReject, if_pos hx]
    have h := le_min (div_nonneg (hz x hx) hs.le) hτ
    positivity
  have hqσ₀ : 0 ≤ q/σ := div_nonneg hq hσ.le
  have hqσ' : q/σ ≤ 1 := (div_le_one hσ).mpr hqσ
  have hdiff (x) (hx : x ∈ R) :
      Real.log (a x) - Real.log (b x) ≤ (q / (σ*(1-q))) * z x := by
    have hstep : (a x - b x) ≤ (q / (σ*(1-q))) * z x := by
      simp only [a, b, onReject, if_pos hx]
      have h := div_le_div_of_nonneg_right (min_le_left (z x/(1-q)) τ) hσ.le
      calc
        _ ≤ (z x/(1-q))/σ - z x/σ := by linarith
        _ = _ := by field_simp; ring
    have hcoef : 0 ≤ q/(σ*(1-q))*z x := by have := hz x hx; positivity
    have hb' : 1 ≤ b x := by dsimp [b]; linarith [div_nonneg (hz x hx) hσ.le]
    rw [← Real.log_div (ha x hx).ne' (hb x hx).ne']
    apply le_trans (Real.log_le_sub_one_of_pos (div_pos (ha x hx) (hb x hx)))
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ (hb x hx)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hb' hcoef]
  have hsum : ∑ x ∈ R, (Real.log (a x) - Real.log (b x)) ≤ q/σ / 2 := by
    have hm : (∑ x ∈ R, z x) / (1-q) ≤ 1/2 := (div_le_iff₀ hs).mpr (by linarith)
    calc
      _ ≤ ∑ x ∈ R, (q/(σ*(1-q))) * z x := sum_le_sum hdiff
      _ = (q/σ)*((∑ x ∈ R, z x)/(1-q)) := by rw [← mul_sum]; field_simp
      _ ≤ _ := by simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hm hqσ₀
  have hbG := prod_pos hb
  have haG := prod_pos ha
  change (∏ x ∈ R, a x) ≤ (1+q/σ)*(∏ x ∈ R, b x)
  apply (Real.log_le_log_iff haG (mul_pos (by linarith) hbG)).mp
  rw [Real.log_mul (by linarith : 1+q/σ ≠ 0) hbG.ne', Real.log_prod (fun x hx => (ha x hx).ne'),
    Real.log_prod (fun x hx => (hb x hx).ne')]
  rw [sum_sub_distrib] at hsum
  linarith [log_half hqσ₀ hqσ']

private theorem neg_log_le_odds {q : ℝ} (hq : q < 1) : -Real.log (1-q) ≤ q/(1-q) := by
  have hs : 0 < 1-q := sub_pos.mpr hq
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hs)
  rw [Real.log_inv] at h
  calc
    _ ≤ (1-q)⁻¹ - 1 := h
    _ = _ := by field_simp; ring

/-- The common edge starts with Φ₁ = 2(q+∑z). After rejection, x is gone
and the remaining weights are capped. Its drop pays for the log increment. -/
theorem reject_phi_one (R : Finset V) (z : V → ℝ) {q τ : ℝ}
    (hq : 0 ≤ q) (hquarter : q ≤ 1/4) (hmass : (∑ x ∈ R, z x) + q < 1/8) :
    -Real.log (1-q) ≤ 2*(q + ∑ x ∈ R, z x) - 2*∑ x ∈ R, onReject R z q τ x := by
  have hs : 0 < 1-q := by linarith
  let M := ∑ x ∈ R, z x
  have hsum : (∑ x ∈ R, onReject R z q τ x) ≤ M/(1-q) := by
    unfold M
    rw [sum_div]
    exact sum_le_sum (fun x hx => by simp [onReject, hx])
  apply le_trans (neg_log_le_odds (by linarith : q < 1))
  change q/(1-q) ≤ 2*(q+M) - 2*∑ x ∈ R, onReject R z q τ x
  calc
    _ ≤ 2*q*(1-(q+M))/(1-q) := by
      apply div_le_div_of_nonneg_right _ hs.le
      have h : q + M ≤ 1/2 := by dsimp [M]; linarith
      nlinarith [mul_le_mul_of_nonneg_left h hq]
    _ = 2*(q+M)-2*(M/(1-q)) := by field_simp; ring
    _ ≤ _ := by linarith

/-- When the old potential is positive, the logarithmic budget is smaller
than log(τ/a). The common-edge term alone covers the compensation cost. -/
theorem inactive_cap {q z a τ Φ : ℝ} (hquarter : q ≤ 1/4) (hq : 0 ≤ q)
    (hz : 0 < z) (ha : 0 < a) (hτ : 0 < τ)
    (hPhi : 2*q ≤ Φ) (hbudget : Real.log (z/a) + Φ < Real.log (τ/a)) :
    z/(1-q) < τ ∧ min (z/(1-q)) τ = z/(1-q) := by
  have hs : 0 < 1-q := by linarith
  have hlog : -Real.log (1-q) ≤ 2*q := by
    apply le_trans (neg_log_le_odds (by linarith : q < 1))
    apply (div_le_iff₀ hs).mpr
    nlinarith [mul_le_mul_of_nonneg_left hquarter hq]
  have hlt : Real.log ((z/(1-q))/a) < Real.log (τ/a) := by
    rw [Real.log_div (div_pos hz hs).ne' ha.ne', Real.log_div hz.ne' hs.ne']
    rw [Real.log_div hz.ne' ha.ne'] at hbudget
    linarith
  have hcap := (div_lt_div_iff_of_pos_right ha).mp
    ((Real.log_lt_log_iff (div_pos (div_pos hz hs) ha) (div_pos hτ ha)).mp hlt)
  exact ⟨hcap, min_eq_left hcap.le⟩

end OMA.GeneralPositionCommonEdge


namespace OMA.GeneralPositionCommonEdge
open Finset
open OMA.GeneralPositionProducts
open scoped Classical

variable {V : Type*} [DecidableEq V]

/-- Extract the scalar log budget from the positive part in the paper's C_v.
Here cost denotes λ times the sum of the old products. -/
theorem log_budget_of_positive_potential {z a τ cost Φ : ℝ}
    (hcost : 0 ≤ cost) (hΛ : 0 < Real.log (τ/a))
    (hC : 0 < z * max (1-cost-(Real.log (z/a)+Φ)/Real.log (τ/a)) 0) :
    Real.log (z/a) + Φ < Real.log (τ/a) := by
  have hp : 0 < 1-cost-(Real.log (z/a)+Φ)/Real.log (τ/a) := by
    by_contra! h
    rw [max_eq_right h, mul_zero] at hC
    exact hC.false
  have hlt : (Real.log (z/a)+Φ)/Real.log (τ/a) < 1 := by linarith
  exact (div_lt_one hΛ).mp hlt

/-- Case 2 as a single interface on the real common edge. The distinguished
vertex x has old weight q; all members of R are affected, and v also receives
the capped compensation. Φ is the global old sum of the edge potentials. -/
theorem common_case_two {R : Finset V} {x : V} (hx : x ∉ R) (z : V → ℝ)
    {q τ σ a zv cost Φ : ℝ} (hqx : z x = q) (hz : ∀ u ∈ R, 0 ≤ z u)
    (hq : 0 ≤ q) (hquarter : q ≤ 1/4) (hσ : 0 < σ) (hqσ : q ≤ σ)
    (hτ : 0 < τ) (ha : 0 < a) (hv : 0 < zv)
    (hmass : q + (∑ u ∈ R, z u) < 1/8)
    (hcost : 0 ≤ cost) (hΦ : 2*(∑ u ∈ insert x R, z u) ≤ Φ)
    (hΛ : 0 < Real.log (τ/a))
    (hC : 0 < zv * max (1-cost-(Real.log (zv/a)+Φ)/Real.log (τ/a)) 0) :
    let w := onReject R z q τ
    let zv' := min (zv/(1-q)) τ
    edgeProduct R w σ ≤ edgeProduct (insert x R) z σ ∧
    -Real.log (1-q) ≤ 2*(∑ u ∈ insert x R, z u) - 2*(∑ u ∈ R, w u) ∧
    zv' = zv/(1-q) ∧ zv' < τ ∧ (1-q)*zv' = zv ∧
    Real.log (zv'/a) + 2*(∑ u ∈ R, w u) ≤
      Real.log (zv/a) + 2*(∑ u ∈ insert x R, z u) := by
  dsimp only
  have hs : 0 < 1-q := by linarith
  have hm : (∑ u ∈ R, z u) + q < 1/8 := by linarith
  have hG := reject_product R z hz hq hquarter hσ hqσ hτ.le hm
  have hP := reject_phi_one R z (τ := τ) hq hquarter hm
  have hqΦ : 2*q ≤ Φ := by
    rw [sum_insert hx, hqx] at hΦ
    linarith [sum_nonneg hz]
  obtain ⟨hcap, hmin⟩ := inactive_cap hquarter hq hv ha hτ hqΦ
    (log_budget_of_positive_potential hcost hΛ hC)
  rw [hmin, sum_insert hx, hqx]
  refine ⟨?_, hP, rfl, hcap, ?_, ?_⟩
  · simpa only [edgeProduct, prod_insert hx, hqx] using hG
  · field_simp
  · rw [Real.log_div (div_pos hv hs).ne' ha.ne', Real.log_div hv.ne' hs.ne', Real.log_div hv.ne' ha.ne']
    linarith

/-- Splitting the unordered pairs in insert x R according to whether x
belongs gives the quadratic potential before a Case 1 common-edge step. -/
theorem pairSum_insert {x : V} {R : Finset V} (hx : x ∉ R) (z : V → ℝ) :
    pairSum (insert x R) z = pairSum R z + z x * ∑ u ∈ R, z u := by
  classical
  unfold pairSum
  rw [powersetCard_succ_insert hx 1]
  have hd : Disjoint (R.powersetCard 2) ((R.powersetCard 1).image (insert x)) := by
    apply disjoint_left.mpr
    intro P hP hP'
    obtain ⟨T, _, rfl⟩ := mem_image.mp hP'
    exact hx ((mem_powersetCard.mp hP).1 (mem_insert_self _ _))
  rw [sum_union hd]
  congr 1
  rw [sum_image]
  · rw [powersetCard_one, sum_map, mul_sum]
    apply sum_congr rfl
    intro u hu
    have hne : x ≠ u := fun h => hx (h ▸ hu)
    simp [hne]
  · intro P hP T hT heq
    have hxP : x ∉ P := fun h => hx ((mem_powersetCard.mp hP).1 h)
    have hxT : x ∉ T := fun h => hx ((mem_powersetCard.mp hT).1 h)
    simpa [hxP,hxT] using congrArg (fun S : Finset V => S.erase x) heq

/-- Case 1 common edge. Its remaining weights stay fixed. Both branches have
the same product and the average switched potential does not increase. -/
theorem common_case_one {x : V} {R : Finset V} (hx : x ∉ R) (z : V → ℝ)
    {q σ : ℝ} (hqx : z x = q) (hz : ∀ u ∈ R, 0 ≤ z u) (hq : 0 ≤ q) (hσ : 0 < σ) :
    edgeProduct R z σ = edgeProduct (insert x R) z σ / (1+q/σ) ∧
    (1-q)*(2*pairSum R z) + q*(2*∑ u ∈ R, z u) ≤ 2*pairSum (insert x R) z := by
  refine ⟨?_, ?_⟩
  · rw [edgeProduct, edgeProduct, prod_insert hx, hqx]
    have h : 1+q/σ ≠ 0 := by positivity
    field_simp
  · rw [pairSum_insert hx, hqx]
    have h₂ : 0 ≤ pairSum R z := sum_nonneg (fun P hP => prod_nonneg
      (fun u hu => hz u ((mem_powersetCard.mp hP).1 hu)))
    nlinarith [mul_nonneg hq h₂]

end OMA.GeneralPositionCommonEdge

/-! Unaffected-case state identifications for Pham, Le Quang-Ham and Xue,
“General-position sets and linear hypergraphs”, §2.3, (2.5). -/

namespace OMA.GeneralPositionUnaffected
open Finset OMA.OnlineSelection OMA.OnlineSelection.HypergraphState
open OMA.GeneralPositionProducts OMA.GeneralPositionPotential OMA.GeneralPositionHistory
open OMA.GeneralPositionLoss OMA.GeneralPositionCodegrees OMA.GeneralPositionCommonEdge
open scoped BigOperators Classical
variable {V : Type*} [DecidableEq V]

noncomputable def activeSet (E : Finset (Finset V)) (s : HypergraphState V) (x v : V) (B : Finset V) : Finset V :=
  (unprocessed s v B).filter (Affected E s x)

theorem active_eq_targets {E : Finset (Finset V)} {s : HypergraphState V} {x v : V} {B : Finset V}
    {tail : List V} {a : ℝ} (h : Valid E a (x::tail) s) :
    activeSet E s x v B = targets E s.selected tail.toFinset B v x := by
  have hx : x ∈ s.remaining := by rw [h.remaining]; simp
  have hel : s.remaining.erase x = tail.toFinset := by
    rw [h.remaining,List.toFinset_cons,erase_insert (by simpa using (List.nodup_cons.mp h.nodup).1)]
  ext u
  simp only [activeSet, unprocessed, targets, mem_filter, mem_erase, mem_inter,
    affected_iff_hasWitness h.safe.disjoint hx, hel]
  constructor
  · rintro ⟨⟨huv, _, huB⟩, hut, hw⟩
    exact ⟨huB,hut,huv,hw⟩
  · rintro ⟨huB,hut,huv,hw⟩
    exact ⟨⟨huv,mem_of_mem_erase (hel.symm ▸ hut),huB⟩,hut,hw⟩

theorem unprocessed_advance (E : Finset (Finset V)) (s : HypergraphState V)
    (x v : V) (τ : ℝ) (b : Bool) (B : Finset V) :
    unprocessed (advance E τ x b s) v B = (unprocessed s v B).erase x := by
  ext u
  simp [unprocessed,advance,and_comm,and_left_comm]

omit [DecidableEq V] in
theorem edgeProduct_congr {U : Finset V} {f g : V → ℝ} (h : ∀ u ∈ U, f u = g u) (σ : ℝ) :
    edgeProduct U f σ = edgeProduct U g σ :=
  prod_congr rfl (fun u hu => by rw [h u hu])

omit [DecidableEq V] in
theorem pairSum_congr {U : Finset V} {f g : V → ℝ} (h : ∀ u ∈ U, f u = g u) :
    pairSum U f = pairSum U g :=
  sum_congr rfl (fun _ hP => prod_congr rfl fun u hu => h u ((mem_powersetCard.mp hP).1 hu))

theorem weight_update_on (E : Finset (Finset V)) (s : HypergraphState V) (x v : V) (B : Finset V)
    (τ : ℝ) {u : V} (hu : u ∈ unprocessed s v B) :
    (advance E τ x true s).weight u = onSelect (activeSet E s x v B) s.weight u ∧
    (advance E τ x false s).weight u = onReject (activeSet E s x v B) s.weight (s.weight x) τ u := by
  by_cases h : Affected E s x u <;> simp [advance,updateWeight,onSelect,onReject,activeSet,hu,h]

theorem common_unaffected {E : Finset (Finset V)} (hE : Linear E)
    {s : HypergraphState V} {x v : V} {B : Finset V} (hB : B ∈ E)
    (hvB : v ∈ B) (hxB : x ∈ B) (hv : v ∈ s.remaining.erase x)
    (hna : ¬Affected E s x v) :
    s.selected ∩ B = ∅ ∧
    ∀ u ∈ (unprocessed s v B).erase x, ¬Affected E s x u := by
  have hem : s.selected ∩ B = ∅ := eq_empty_of_forall_notMem (fun y hy =>
    hna ⟨hv,y,(mem_inter.mp hy).1,B,hB,hxB,(mem_inter.mp hy).2,hvB⟩)
  refine ⟨hem,?_⟩
  rintro u hu ⟨_,y,hy,C,hC,hxC,hyC,huC⟩
  have huB := (mem_inter.mp (mem_erase.mp (mem_of_mem_erase hu)).2).2
  have hCB := hE.edge_eq_of_pair hC hB (mem_erase.mp hu).1 huC huB hxC hxB
  subst C
  have hin : y ∈ s.selected ∩ B := mem_inter.mpr ⟨hy,hyC⟩
  simp [hem] at hin

end OMA.GeneralPositionUnaffected

namespace OMA.GeneralPositionUnaffected
open Finset OMA.OnlineSelection OMA.OnlineSelection.HypergraphState
open OMA.GeneralPositionProducts OMA.GeneralPositionPotential OMA.GeneralPositionHistory
open OMA.GeneralPositionLoss OMA.GeneralPositionCodegrees OMA.GeneralPositionCommonEdge
open scoped BigOperators Classical
variable {V : Type*} [DecidableEq V]

theorem mixed_drift {E : Finset (Finset V)} {s : HypergraphState V} {x v : V} {B : Finset V}
    (hx : x ∉ B) {τ σ : ℝ} (hs : WeightsIn τ s) (hq : s.weight x ≤ 1/2)
    (hσ : 0 < σ) (hτ : 0 ≤ τ) (hmass : 2*s.weight x*mass s v B/σ ≤ Real.log 2) :
    let q := s.weight x
    let Y := advance E τ x true s
    let N := advance E τ x false s
    let A := activeSet E s x v B
    (q * edgeG Y v σ B + (1-q) * edgeG N v σ B - edgeG s v σ B ≤
      4*q*edgeG s v σ B/σ^2 * pairSum A s.weight) ∧
    (q * edgePhi Y v B + (1-q) * edgePhi N v B - edgePhi s v B ≤
      2*q/(1-q) * pairSum A s.weight) := by
  let U := unprocessed s v B
  let A := activeSet E s x v B
  let q := s.weight x
  let yes := advance E τ x true s
  let no := advance E τ x false s
  let y := onSelect A s.weight
  let n := onReject A s.weight q τ
  have hU (b : Bool) : unprocessed (advance E τ x b s) v B = U := by
    rw [unprocessed_advance,erase_eq_of_notMem]
    exact fun h => hx (mem_inter.mp (mem_of_mem_erase h)).2
  have hB (b : Bool) : (advance E τ x b s).selected ∩ B = s.selected ∩ B := by
    cases b
    · rfl
    · ext u
      simp only [advance,if_true,mem_inter,mem_insert]
      aesop
  have hy (u : V) (hu : u ∈ U) : yes.weight u = y u := (weight_update_on E s x v B τ hu).1
  have hn (u : V) (hu : u ∈ U) : no.weight u = n u := (weight_update_on E s x v B τ hu).2
  have hA : A ⊆ U := filter_subset _ _
  have hz (u : V) (_ : u ∈ U) : 0 ≤ s.weight u := (hs u).1
  have hq1 : q < 1 := lt_of_le_of_lt hq (by norm_num)
  have hG1 : edgeG yes v σ B = edgeProduct U y σ := by
    unfold edgeG
    rw [hU true]
    exact edgeProduct_congr hy _
  have hG0 : edgeG no v σ B = edgeProduct U n σ := by
    unfold edgeG
    rw [hU false]
    exact edgeProduct_congr hn _
  constructor
  · rw [hG1,hG0]
    exact capped_product hA s.weight hz (hs x).1 hq hσ hτ hmass
  · unfold edgePhi mass
    rw [hB true,hB false,hU true,hU false]
    by_cases hc : (s.selected ∩ B).card = 0
    · simp only [hc,if_true]
      rw [pairSum_congr hy,pairSum_congr hn]
      exact capped_phi_zero hA s.weight hz hq1 hτ
    · simp only [hc,if_false]
      rw [sum_congr rfl hy,sum_congr rfl hn]
      have hh := capped_phi_one U A s.weight (τ := τ) hq1
      have hp : 0 ≤ pairSum A s.weight := sum_nonneg fun P hP => prod_nonneg fun u _ => (hs u).1
      have hfac : 0 ≤ 2*q/(1-q) := div_nonneg (mul_nonneg (by norm_num) (hs x).1) (by linarith)
      exact (sub_nonpos.mpr hh).trans (mul_nonneg hfac hp)

theorem common_drift {E : Finset (Finset V)} (hE : Linear E) {s : HypergraphState V}
    {x v : V} {B : Finset V} (hB : B ∈ E) (hvB : v ∈ B) (hxB : x ∈ B)
    (hx : x ∈ s.remaining) (hv : v ∈ s.remaining.erase x) (hna : ¬Affected E s x v)
    {τ σ : ℝ} (hs : WeightsIn τ s) (hσ : 0 < σ) :
    let q := s.weight x
    let Y := advance E τ x true s
    let N := advance E τ x false s
    (q*edgeG Y v σ B + (1-q)*edgeG N v σ B ≤ edgeG s v σ B) ∧
    (q*edgePhi Y v B + (1-q)*edgePhi N v B ≤ edgePhi s v B) := by
  let U := unprocessed s v B
  let R := U.erase x
  have hU : x ∈ U := mem_erase.mpr ⟨(mem_erase.mp hv).1.symm,mem_inter.mpr ⟨hx,hxB⟩⟩
  have hR : insert x R = U := insert_erase hU
  obtain ⟨hem,hnaR⟩ := common_unaffected hE hB hvB hxB hv hna
  have hw (b : Bool) (u : V) (hu : u ∈ R) : (advance E τ x b s).weight u = s.weight u := by
    simp [advance,updateWeight,hnaR u hu]
  have hur (b : Bool) : unprocessed (advance E τ x b s) v B = R := unprocessed_advance _ _ _ _ _ _ _
  have hprod (b : Bool) : edgeG (advance E τ x b s) v σ B = edgeProduct R s.weight σ := by
    unfold edgeG
    rw [hur]
    exact edgeProduct_congr (hw b) _
  have hc := common_case_one (R := R) (x := x) (notMem_erase x U) s.weight rfl
    (fun u _ => (hs u).1) (hs x).1 hσ
  rw [hR] at hc
  constructor
  · rw [hprod,hprod]
    have he : s.weight x * edgeProduct R s.weight σ + (1-s.weight x)*edgeProduct R s.weight σ =
        edgeProduct R s.weight σ := by ring
    rw [he,hc.1]
    have hG := (edgeG_pos s v B hσ fun u => (hs u).1).le
    exact div_le_self hG (by linarith [div_nonneg (hs x).1 hσ.le])
  · have hsel : ((advance E τ x true s).selected ∩ B).Nonempty :=
      ⟨x,mem_inter.mpr ⟨mem_insert_self _ _,hxB⟩⟩
    have hno : (advance E τ x false s).selected ∩ B = ∅ := hem
    simp only [edgePhi, ne_of_gt (card_pos.mpr hsel), if_false, hno, hem, card_empty, if_true,mass,hur]
    rw [sum_congr rfl (hw true),pairSum_congr (hw false),add_comm]
    exact hc.2

end OMA.GeneralPositionUnaffected

namespace OMA.GeneralPositionUnaffected
open Finset OMA.OnlineSelection OMA.OnlineSelection.HypergraphState
open OMA.GeneralPositionProducts OMA.GeneralPositionPotential OMA.GeneralPositionHistory
open OMA.GeneralPositionLoss OMA.GeneralPositionCodegrees OMA.GeneralPositionCommonEdge
open scoped BigOperators Classical
variable {V : Type*} [DecidableEq V]

noncomputable def edgeCost (s : HypergraphState V) (v : V) (σ lam L z : ℝ) (B : Finset V) :=
  z * (lam * edgeG s v σ B + edgePhi s v B / L)

omit [DecidableEq V] in
theorem pairSum_cap (A : Finset V) (z : V → ℝ) {τ : ℝ} (hz : ∀ u, 0 ≤ z u ∧ z u ≤ τ) :
    pairSum A z ≤ τ^2 * (A.powersetCard 2).card := by
  calc
    _ ≤ ∑ _P ∈ A.powersetCard 2, τ^2 := by
      refine sum_le_sum (fun P hP => ?_)
      have hc := (mem_powersetCard.mp hP).2
      calc
        ∏ u ∈ P, z u ≤ ∏ _u ∈ P, τ := prod_le_prod (fun u _ => (hz u).1) (fun u _ => (hz u).2)
        _ = _ := by simp [hc]
    _ = _ := by simp [mul_comm]

/-- Turn the exact two drift estimates into the coefficient of (2.5). -/
private theorem numerical {q τ σ L lam z G DG DP P card : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1/4) (hτ : 0 ≤ τ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hL : 1 ≤ L) (hlam : 0 ≤ lam) (hz : 0 ≤ z) (hzτ : z ≤ τ) (hG : lam*G ≤ 1)
    (hP : 0 ≤ P) (hPc : P ≤ τ^2 * card)
    (hg : DG ≤ 4*q*G/σ^2*P) (hp : DP ≤ (2*q/(1-q))*P) :
    z*(lam*DG + DP/L) ≤ (8*τ^3/σ^2)*q*card := by
  have hσ2 := sq_pos_of_pos hσ
  have hσ21 : σ^2 ≤ 1 := by nlinarith [mul_nonneg hσ.le (sub_nonneg.mpr hσ1)]
  have hq1 : 0 < 1-q := by linarith
  have hg' : lam*DG ≤ (4*q/σ^2)*P := calc
    _ ≤ lam*(4*q*G/σ^2*P) := mul_le_mul_of_nonneg_left hg hlam
    _ = (4*q/σ^2*P)*(lam*G) := by ring
    _ ≤ (4*q/σ^2*P)*1 := mul_le_mul_of_nonneg_left hG (by positivity)
    _ = _ := mul_one _
  have hfac : 2*q/(1-q) ≤ 4*q := (div_le_iff₀ hq1).mpr (by nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq)])
  have hfac' : 4*q ≤ 4*q/σ^2 := (le_div_iff₀ hσ2).mpr (mul_le_of_le_one_right (by positivity) hσ21)
  have hp' : DP/L ≤ (4*q/σ^2)*P := calc
    _ ≤ ((2*q/(1-q))*P)/L := div_le_div_of_nonneg_right hp (by linarith)
    _ ≤ (2*q/(1-q))*P := div_le_self (by positivity) hL
    _ ≤ _ := mul_le_mul_of_nonneg_right (hfac.trans hfac') hP
  calc
    _ ≤ z*((4*q/σ^2)*P+(4*q/σ^2)*P) := mul_le_mul_of_nonneg_left (add_le_add hg' hp') hz
    _ = (z*(8*q/σ^2))*P := by ring
    _ ≤ (τ*(8*q/σ^2))*(τ^2*card) := mul_le_mul (mul_le_mul_of_nonneg_right hzτ (by positivity)) hPc hP (by positivity)
    _ = _ := by ring

theorem mixed_cost {s Y N : HypergraphState V} {v x : V} {A B : Finset V}
    {τ σ L lam : ℝ} (hs : WeightsIn τ s) (hq : s.weight x ≤ 1/4) (hτ : 0 ≤ τ)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hL : 1 ≤ L) (hlam : 0 ≤ lam) (hG : lam * edgeG s v σ B ≤ 1)
    (hg : s.weight x * edgeG Y v σ B + (1-s.weight x) * edgeG N v σ B - edgeG s v σ B ≤
      4*s.weight x*edgeG s v σ B/σ^2 * pairSum A s.weight)
    (hp : s.weight x * edgePhi Y v B + (1-s.weight x) * edgePhi N v B - edgePhi s v B ≤
      2*s.weight x/(1-s.weight x) * pairSum A s.weight) :
    s.weight x * edgeCost Y v σ lam L (s.weight v) B +
      (1-s.weight x) * edgeCost N v σ lam L (s.weight v) B - edgeCost s v σ lam L (s.weight v) B ≤
      (8*τ^3/σ^2)*s.weight x*(A.powersetCard 2).card := by
  have hP : 0 ≤ pairSum A s.weight := sum_nonneg fun _ _ => prod_nonneg fun u _ => (hs u).1
  have hh := numerical (hs x).1 hq hτ hσ hσ1 hL hlam (hs v).1 (hs v).2 hG hP
    (pairSum_cap A s.weight hs) hg hp
  unfold edgeCost
  convert hh using 1; ring

theorem common_cost {s Y N : HypergraphState V} {x v : V} {B : Finset V} {σ lam L : ℝ}
    (hL : 0 ≤ L) (hlam : 0 ≤ lam) (hv : 0 ≤ s.weight v)
    (hg : s.weight x*edgeG Y v σ B + (1-s.weight x)*edgeG N v σ B ≤ edgeG s v σ B)
    (hp : s.weight x*edgePhi Y v B + (1-s.weight x)*edgePhi N v B ≤ edgePhi s v B) :
    s.weight x*edgeCost Y v σ lam L (s.weight v) B +
    (1-s.weight x)*edgeCost N v σ lam L (s.weight v) B - edgeCost s v σ lam L (s.weight v) B ≤ 0 := by
  have hh := mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hg hlam)
    (div_le_div_of_nonneg_right hp hL)) hv
  unfold edgeCost
  linarith only [show _ ≤ _ from hh, le_of_eq (by ring :
    s.weight x * (s.weight v * (lam*edgeG Y v σ B + edgePhi Y v B/L)) +
      (1-s.weight x) * (s.weight v * (lam*edgeG N v σ B + edgePhi N v B/L)) =
    s.weight v * (lam*(s.weight x*edgeG Y v σ B+(1-s.weight x)*edgeG N v σ B) +
      (s.weight x*edgePhi Y v B+(1-s.weight x)*edgePhi N v B)/L))]

end OMA.GeneralPositionUnaffected

namespace OMA.GeneralPositionUnaffected
open Finset OMA.OnlineSelection OMA.OnlineSelection.HypergraphState
open OMA.GeneralPositionProducts OMA.GeneralPositionPotential OMA.GeneralPositionHistory
open OMA.GeneralPositionLoss OMA.GeneralPositionCodegrees OMA.GeneralPositionCommonEdge
open scoped BigOperators Classical
variable {V : Type*} [DecidableEq V]

noncomputable def totalCost (E : Finset (Finset V)) (s : HypergraphState V) (v : V)
    (σ lam L z : ℝ) : ℝ :=
  ∑ B ∈ E.filter (v ∈ ·), edgeCost s v σ lam L z B

theorem totalCost_eq (E : Finset (Finset V)) (s : HypergraphState V) (v : V) (σ lam L z : ℝ) :
    totalCost E s v σ lam L z = z * (lam * sumG E s v σ + sumPhi E s v / L) := by
  simp only [totalCost,edgeCost,sumG,sumPhi,← mul_sum,sum_add_distrib,← sum_div]

theorem potential_raw_le (E : Finset (Finset V)) {s : HypergraphState V} {v : V}
    (hv : v ∈ s.remaining) (hz : 0 ≤ s.weight v) (a τ σ lam : ℝ) :
    s.weight v * (1 - Real.log (s.weight v/a)/Real.log (τ/a)) -
      totalCost E s v σ lam (Real.log (τ/a)) (s.weight v) ≤ potential true E s v a τ σ lam := by
  rw [potential,if_pos ⟨rfl,hv⟩,totalCost_eq]
  calc
    _ = s.weight v * (1 - lam*sumG E s v σ - (Real.log (s.weight v/a)+sumPhi E s v)/Real.log (τ/a)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) hz

theorem potential_raw_eq {E : Finset (Finset V)} {s : HypergraphState V} {v : V}
    (hv : v ∈ s.remaining) {a τ σ lam : ℝ} (hp : 0 < potential true E s v a τ σ lam) :
    potential true E s v a τ σ lam = s.weight v * (1-Real.log (s.weight v/a)/Real.log (τ/a)) -
      totalCost E s v σ lam (Real.log (τ/a)) (s.weight v) := by
  rw [potential, if_pos ⟨rfl,hv⟩] at hp ⊢
  rw [totalCost_eq]
  have hb : 0 < 1 - lam * sumG E s v σ - (Real.log (s.weight v / a) + sumPhi E s v) / Real.log (τ / a) := by
    by_contra! hn
    rw [max_eq_right hn,mul_zero] at hp
    exact hp.false
  rw [max_eq_left hb.le]
  ring

theorem from_cost {E : Finset (Finset V)} {s : HypergraphState V} {v x : V}
    {a τ σ lam loss : ℝ} (hv : v ∈ s.remaining.erase x) (hna : ¬Affected E s x v) (hs : WeightsIn τ s)
    (hq : s.weight x ≤ 1) (hp : 0 < potential true E s v a τ σ lam)
    (hd : s.weight x * totalCost E (advance E τ x true s) v σ lam (Real.log (τ/a)) (s.weight v) +
      (1-s.weight x)*totalCost E (advance E τ x false s) v σ lam (Real.log (τ/a)) (s.weight v) -
        totalCost E s v σ lam (Real.log (τ/a)) (s.weight v) ≤ loss) :
    potential true E s v a τ σ lam ≤
      s.weight x*potential true E (advance E τ x true s) v a τ σ lam +
      (1-s.weight x)*potential true E (advance E τ x false s) v a τ σ lam + loss := by
  have hw (b : Bool) : (advance E τ x b s).weight v = s.weight v := by simp [advance,updateWeight,hna]
  have h (b : Bool) := potential_raw_le E (s := advance E τ x b s) (v := v) hv
    ((hw b).symm ▸ (hs v).1) a τ σ lam
  have hy := h true
  have hn := h false
  rw [hw true] at hy
  rw [hw false] at hn
  have hs' := add_le_add (mul_le_mul_of_nonneg_left hy (hs x).1)
    (mul_le_mul_of_nonneg_left hn (sub_nonneg.mpr hq))
  rw [potential_raw_eq (mem_of_mem_erase hv) hp]
  linarith only [hs',hd]

theorem incidence_sum {E : Finset (Finset V)} {Q : Finset V} {s : HypergraphState V} {x v : V}
    {a : ℝ} {tail : List V} (h : Valid E a (x::tail) s)
    (hsize : ∀ B ∈ E, 3 ≤ (B ∩ Q).card) :
    ∑ B ∈ E.filter (v ∈ ·), (if x ∈ B then (0:ℝ) else ((activeSet E s x v B).powersetCard 2).card) =
      (incidences E Q s.selected tail.toFinset v x .twoNeighbors).card := by
  rw [card_incidences_eq_sum]
  push_cast
  simp only [active_eq_targets h, card_powersetCard, markCount,centerGate, and_true]
  simp_rw [← ite_not (x ∈ _)  _ _]
  rw [← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext B
  simp only [mem_filter]
  aesop

end OMA.GeneralPositionUnaffected

namespace OMA.GeneralPositionUnaffected
open Finset OMA.OnlineSelection OMA.OnlineSelection.HypergraphState
open OMA.GeneralPositionProducts OMA.GeneralPositionPotential OMA.GeneralPositionHistory
open OMA.GeneralPositionLoss OMA.GeneralPositionCodegrees OMA.GeneralPositionCommonEdge
open scoped BigOperators Classical
variable {V : Type*} [DecidableEq V]

/-- Equation (2.5) with the incidence loss on the actual retained hypergraph.
The stated bounds are the scalar hypotheses used by the paper in §2.3. -/
theorem localBound_false {E : Finset (Finset V)} (hE : Linear E) (Q : Finset V) (v : V)
    {a τ σ η lam : ℝ} (ha : 0 < a) (haτ : a < τ) (hτ4 : τ ≤ 1/4)
    (hτσ : τ ≤ σ) (hσ1 : σ ≤ 1)
    (hscale : 2*τ*η/σ ≤ Real.log 2) (hL : 1 ≤ Real.log (τ/a))
    (hlam : lam = Real.exp (-(η/(2*σ)))) :
    LocalBound false (retainedEdges E Q) v a τ σ lam (paperLoss (retainedEdges E Q) Q v τ σ) := by
  let F := retainedEdges E Q
  have hF : Linear F := OMA.GeneralPositionSelection.linear_trace hE Q
  have hsize (B : Finset V) (hB : B ∈ F) : 3 ≤ (B ∩ Q).card := by
    obtain ⟨⟨C,hC,rfl⟩,hc⟩ := OMA.GeneralPositionSelection.mem_trace.mp hB
    simpa only [inter_assoc,inter_self] using hc
  intro x tail s hs hvd hv hkind hp
  have hx : x ∈ s.remaining := by simp [hvd.remaining]
  have hv' : v ∈ s.remaining.erase x := by
    rw [hvd.remaining,List.toFinset_cons,erase_insert (by simpa using (List.nodup_cons.mp hvd.nodup).1)]
    exact List.mem_toFinset.mpr hv
  have hna : ¬ Affected F s x v := fun haff => Bool.noConfusion (hkind.mp haff)
  have hz := positive_consequences ha haτ hτσ hlam hs hvd.floor hp
  have hq := (hs x).2.trans hτ4
  have hτ := (ha.trans haτ).le
  have hσ := (ha.trans haτ).trans_le hτσ
  have hlam0 : 0 ≤ lam := hlam ▸ (Real.exp_pos _).le
  let Y := advance F τ x true s
  let N := advance F τ x false s
  let L := Real.log (τ/a)
  let T := F.filter (v ∈ ·)
  let c := 8*τ^3/σ^2*s.weight x
  let count (B : Finset V) : ℝ := if x ∈ B then 0 else ((activeSet F s x v B).powersetCard 2).card
  have hbound (B : Finset V) (hB : B ∈ T) :
      s.weight x * edgeCost Y v σ lam L (s.weight v) B +
      (1-s.weight x)*edgeCost N v σ lam L (s.weight v) B - edgeCost s v σ lam L (s.weight v) B ≤ c * count B := by
    obtain ⟨hBF,hvB⟩ := mem_filter.mp hB
    by_cases hxB : x ∈ B
    · obtain ⟨hg,hp'⟩ := common_drift hF hBF hvB hxB hx hv' hna hs hσ
      simpa only [count,if_pos hxB,mul_zero] using
        common_cost (L := L) (by dsimp [L]; linarith) hlam0 (hs v).1 hg hp'
    · obtain ⟨hm,hg⟩ := hz.2.2.2.2 B hBF hvB
      have hm' : 2*s.weight x*mass s v B/σ ≤ Real.log 2 := by
        apply le_trans _ hscale
        apply div_le_div_of_nonneg_right _ hσ.le
        exact mul_le_mul (by linarith [(hs x).2]) hm.le
          (sum_nonneg fun u _ => (hs u).1) (by positivity)
      obtain ⟨hG,hP⟩ := mixed_drift (E := F) hxB hs (by linarith) hσ hτ hm'
      simpa only [count,if_neg hxB,c] using mixed_cost hs hq hτ hσ hσ1 hL hlam0 hg.le hG hP
  have hsum := sum_le_sum hbound
  rw [sum_sub_distrib,sum_add_distrib,← mul_sum,← mul_sum,← mul_sum] at hsum
  have hcount : ∑ B ∈ T, count B = ((incidences F Q s.selected tail.toFinset v x .twoNeighbors).card : ℝ) :=
    incidence_sum hvd hsize
  rw [hcount] at hsum
  have hlocal : 0 ≤ localLoss F Q v .centerAndNeighbor (16*τ^2/σ) x tail s := by
    unfold localLoss
    have := (hs x).1
    positivity
  apply from_cost hv' hna hs (by linarith) hp
  exact hsum.trans (le_add_of_nonneg_right hlocal)

/-- Fixed-order integration interface. Only the affected one-step estimate is
left as a local premise. The two counted configurations use the original E. -/
theorem fixed_order_of_affected {E : Finset (Finset V)} (hE : Linear E) {Q : Finset V} {v : V}
    {a τ σ η lam : ℝ} (ha : 0 < a) (haτ : a < τ) (hτ4 : τ ≤ 1/4)
    (hτσ : τ ≤ σ) (hσ1 : σ ≤ 1)
    (hscale : 2*τ*η/σ ≤ Real.log 2) (hL : 1 ≤ Real.log (τ/a))
    (hlam : lam = Real.exp (-(η/(2*σ)))) (xs : List V) (hxs : xs.Nodup) (hQ : xs.toFinset = Q)
    (affected : LocalBound true (retainedEdges E Q) v a τ σ lam (paperLoss (retainedEdges E Q) Q v τ σ)) :
    potential true (retainedEdges E Q) (initial Q a) v a τ σ lam ≤
      (process (retainedEdges E Q) τ).joint xs (initial Q a) {v} +
      (8*τ^6/σ^2 * ((eligible E Q v .twoNeighbors).card : ℝ) +
       16*τ^5/σ * ((eligible E Q v .centerAndNeighbor).card : ℝ)) :=
  fixed_order_bound hE ha haτ (by linarith) ((ha.trans haτ).trans_le hτσ)
    (hlam ▸ (Real.exp_pos _).le) xs hxs hQ
    (localBound_false hE Q v ha haτ hτ4 hτσ hσ1 hscale hL hlam) affected

end OMA.GeneralPositionUnaffected

namespace OMA.GeneralPositionUnaffected
open Finset OMA.OnlineSelection OMA.OnlineSelection.HypergraphState
open OMA.GeneralPositionProducts OMA.GeneralPositionPotential OMA.GeneralPositionHistory
open OMA.GeneralPositionLoss OMA.GeneralPositionCodegrees OMA.GeneralPositionCommonEdge
open scoped BigOperators Classical
variable {V : Type*} [DecidableEq V]

/-- The state-level common-edge hypotheses needed to instantiate
GeneralPositionCommonEdge.common_case_two for the affected case. -/
theorem affected_common_edge {E : Finset (Finset V)} (hE : Linear E)
    {s : HypergraphState V} (hs : Safe E s) {v x : V}
    (haff : Affected E s x v) (hvz : 0 < s.weight v) :
    ∃ B ∈ E, x ∈ B ∧ v ∈ B ∧ (s.selected ∩ B).card = 1 ∧
      (∀ C ∈ E, x ∈ C → v ∈ C → C = B) ∧
      (∀ u ∈ (unprocessed s v B).erase x, Affected E s x u) := by
  obtain ⟨hv,y,hy,B,hB,hxB,hyB,hvB⟩ := haff
  have hcard := selected_card_le_one hs (mem_of_mem_erase hv) hvz hB hvB
  have hpos := card_pos.mpr (show (s.selected ∩ B).Nonempty from ⟨y,mem_inter.mpr ⟨hy,hyB⟩⟩)
  refine ⟨B,hB,hxB,hvB,by omega,?_,?_⟩
  · intro C hC hxC hvC
    exact hE.edge_eq_of_pair hC hB (mem_erase.mp hv).1 hvC hvB hxC hxB
  · intro u hu
    have hint := mem_inter.mp (mem_of_mem_erase (mem_of_mem_erase hu))
    exact ⟨mem_erase.mpr ⟨(mem_erase.mp hu).1,hint.1⟩,y,hy,B,hB,hxB,hyB,hint.2⟩

/-- The second case of the actual loss counts one affected later vertex per
non-common incident edge. This uses the real center gate in the incidence set. -/
theorem affected_incidence_sum {E : Finset (Finset V)} {Q : Finset V} {s : HypergraphState V} {x v : V}
    {a : ℝ} {tail : List V} (h : Valid E a (x::tail) s) (haff : Affected E s x v)
    (hsize : ∀ B ∈ E, 3 ≤ (B ∩ Q).card) :
    ∑ B ∈ E.filter (v ∈ ·), (if x ∈ B then (0:ℝ) else (activeSet E s x v B).card) =
      (incidences E Q s.selected tail.toFinset v x .centerAndNeighbor).card := by
  have hx : x ∈ s.remaining := by simp [h.remaining]
  have hg := ((affected_iff_hasWitness h.safe.disjoint hx).mp haff).2
  rw [card_incidences_eq_sum]
  push_cast
  simp only [active_eq_targets h, markCount,Nat.choose_one_right,centerGate,hg,and_true]
  simp_rw [← ite_not (x ∈ _) _ _]
  rw [← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext B
  simp only [mem_filter]
  aesop

end OMA.GeneralPositionUnaffected

/-! Deterministic restriction and degree trimming from §2.4 of Pham,
Le Quang-Ham and Xue, General-position sets and linear hypergraphs,
arXiv:2610.34254v1. -/

namespace OMA.GeneralPositionPretrim
open scoped Classical
variable {V : Type*} [DecidableEq V]

def contribution (x : V) (B : Finset V) : ℕ :=
  if x ∈ B then (B.card - 1).choose 2 else 0

def degree (E : Finset (Finset V)) (x : V) : ℕ := ∑ B ∈ E, contribution x B

def restrictEdges (E : Finset (Finset V)) (U : Finset V) : Finset (Finset V) :=
  (E.image (· ∩ U)).filter fun B => 3 ≤ B.card

theorem degree_sum {A : Finset V} {E : Finset (Finset V)} (hE : ∀ B ∈ E, B ⊆ A) :
    ∑ x ∈ A, degree E x = 3 * ∑ B ∈ E, B.card.choose 3 := by
  classical
  simp only [degree, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B hB
  have heq : A.filter (· ∈ B) = B := by
    ext x
    simpa using (show x ∈ B → x ∈ A from fun hx => hE B hB hx)
  simp only [contribution, ← Finset.sum_filter, heq, Finset.sum_const, nsmul_eq_mul]
  cases hn : B.card with
  | zero => simp
  | succ n => simpa [Nat.mul_comm] using Nat.add_one_mul_choose_eq n 2

theorem restricted_degree_le (E : Finset (Finset V)) (U : Finset V) (x : V) :
    degree (restrictEdges E U) x ≤ degree E x := by
  classical
  unfold degree restrictEdges
  calc
    _ ≤ ∑ B ∈ E.image (· ∩ U), contribution x B :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; omega)
    _ ≤ ∑ B ∈ E, contribution x (B ∩ U) :=
      Finset.sum_image_le_of_nonneg (by intros; omega)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro B _
      by_cases hx : x ∈ B ∩ U
      · simp only [contribution, if_pos hx, if_pos (Finset.mem_inter.mp hx).1]
        exact Nat.choose_le_choose 2 (Nat.sub_le_sub_right (Finset.card_le_card Finset.inter_subset_left) _)
      · simp [contribution, hx]

theorem restrict_linear {E : Finset (Finset V)} (U : Finset V)
    (lin : ∀ B ∈ E, ∀ C ∈ E, B ≠ C → (B ∩ C).card ≤ 1) :
    ∀ B ∈ restrictEdges E U, ∀ C ∈ restrictEdges E U, B ≠ C → (B ∩ C).card ≤ 1 := by
  intro _ hB _ hC hne
  obtain ⟨B, hb, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hB).1
  obtain ⟨C, hc, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hC).1
  refine (Finset.card_le_card (show (B ∩ U) ∩ (C ∩ U) ⊆ B ∩ C from ?_)).trans
    (lin B hb C hc (fun h => hne (congrArg (· ∩ U) h)))
  intro x hx
  obtain ⟨hb', hc'⟩ := Finset.mem_inter.mp hx
  exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hb').1, (Finset.mem_inter.mp hc').1⟩

theorem lift_independent {E : Finset (Finset V)} {I U : Finset V} (sub : I ⊆ U)
    (ind : ∀ B ∈ restrictEdges E U, (I ∩ B).card ≤ 2) :
    ∀ B ∈ E, (I ∩ B).card ≤ 2 := by
  intro B hb
  have eq : I ∩ B = I ∩ (B ∩ U) := by
    ext x
    simp only [Finset.mem_inter]
    exact ⟨fun h => ⟨h.1, h.2, sub h.1⟩, fun h => ⟨h.1, h.2.1⟩⟩
  rw [eq]
  by_cases h : 3 ≤ (B ∩ U).card
  · exact ind _ (Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hb, h⟩)
  · exact (Finset.card_le_card Finset.inter_subset_right).trans (by omega)

end OMA.GeneralPositionPretrim


namespace OMA.GeneralPositionPretrim
open scoped Classical
variable {V : Type*} [DecidableEq V]

theorem half_remains (A : Finset V) (d : V → ℕ) (t : ℝ) (ht : 0 < t)
    (hs : 2 * (∑ v ∈ A, (d v : ℝ)) ≤ A.card * t) :
    A.card ≤ 2 * (A.filter fun v => (d v : ℝ) ≤ t).card := by
  classical
  let U := A.filter fun v => (d v : ℝ) ≤ t
  change A.card ≤ 2 * U.card
  have hsub : U ⊆ A := Finset.filter_subset _ _
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  have hbad : ((A \ U).card : ℝ) * t ≤ ∑ v ∈ A, (d v : ℝ) := by
    calc
      _ = ∑ _v ∈ A \ U, t := by simp
      _ ≤ ∑ v ∈ A \ U, (d v : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        have h := Finset.mem_sdiff.mp hv
        exact le_of_not_ge (fun hle => h.2 (Finset.mem_filter.mpr ⟨h.1, hle⟩))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (by intros; positivity)
  have hmul : (2 * ((A \ U).card : ℝ)) * t ≤ (A.card : ℝ) * t := by linarith
  have hle : 2 * (A \ U).card ≤ A.card := by exact_mod_cast (le_of_mul_le_mul_right hmul ht)
  omega

end OMA.GeneralPositionPretrim


namespace OMA.GeneralPositionPretrim
open OMA.S_opg_general_position_subsets
open scoped Classical

/-- Lemma 9 at K = 12 × 73728, after summing marginal inclusion probabilities
and choosing a realization of at least the expected cardinality.
The triple degree uses the incident-edge sum, as in the local codegree lemmas. -/
def Lemma9Selection : Prop :=
  ∃ n₀ : ℕ, ∀ (n : ℝ) (U : Finset P) (F : Finset (Finset P)), (n₀ : ℝ) ≤ n →
    (∀ B ∈ F, B ⊆ U ∧ 3 ≤ B.card ∧ (B.card : ℝ) ≤ 884736 * n) →
    (∀ B ∈ F, ∀ D ∈ F, B ≠ D → (B ∩ D).card ≤ 1) →
    (∀ x ∈ U, ((∑ B ∈ F.filter (x ∈ ·), (B.card - 1).choose 2 : ℕ) : ℝ)
      ≤ 884736 * n ^ 2 * Real.log n) →
    ∃ I ⊆ U, (1 / (4000 * 884736) : ℝ) * U.card ≤ n * I.card ∧
      ∀ B ∈ F, (I ∩ B).card ≤ 2

theorem degree_eq_incident {V : Type*} [DecidableEq V] (E : Finset (Finset V)) (x : V) :
    degree E x = ∑ B ∈ E.filter (x ∈ ·), (B.card - 1).choose 2 := by
  classical
  simp [degree, contribution, Finset.sum_filter]

/-- Section 2.4, specializing the sufficiently-large-scale consequence of
Lemma 9 to the registered hypothesis with N vertices and n = √N. -/
theorem h1_of_lemma9 : Lemma9Selection → OMA.R_opg_general_position_subsets_R1.H1 := by
  classical
  rintro ⟨n₀, select⟩
  let g : ℝ := 1 / (4000 * 884736)
  have hg : 0 < g := by norm_num [g]
  refine ⟨g / 2, by positivity, max 2 (n₀^2), ?_⟩
  intro A E hN hE lin budget
  have htwo : 2 ≤ A.card := (le_max_left _ _).trans hN
  have hA : (1 : ℝ) < A.card := by exact_mod_cast (show 1 < A.card by omega)
  have hA₀ : (0 : ℝ) ≤ A.card := by positivity
  let n := Real.sqrt (A.card : ℝ)
  have hn : 0 < n := Real.sqrt_pos.2 (by linarith)
  have hn₂ : n^2 = (A.card : ℝ) := Real.sq_sqrt hA₀
  have hn₀ : (n₀ : ℝ) ≤ n := Real.le_sqrt_of_sq_le (by
    exact_mod_cast (le_max_right 2 (n₀^2)).trans hN)
  let t : ℝ := 442368 * (A.card : ℝ) * Real.log A.card
  have hlog : 0 < Real.log A.card := Real.log_pos hA
  have ht : 0 < t := by dsimp [t]; positivity
  let U := A.filter fun x => (degree E x : ℝ) ≤ t
  let F := restrictEdges E U
  have hsum : ∑ x ∈ A, (degree E x : ℝ) = 3 * ((∑ B ∈ E, B.card.choose 3 : ℕ) : ℝ) := by
    exact_mod_cast degree_sum (fun B hB => (hE B hB).1)
  have hhalf : A.card ≤ 2 * U.card := by
    apply half_remains A (degree E) t ht
    rw [hsum]
    dsimp [t]
    nlinarith [budget]
  have hcap : ((Nat.sqrt A.card : ℕ) : ℝ) ≤ n := Real.le_sqrt_of_sq_le (by
    exact_mod_cast Nat.sqrt_le' A.card)
  have hedge : ∀ B ∈ F, B ⊆ U ∧ 3 ≤ B.card ∧ (B.card : ℝ) ≤ 884736 * n := by
    intro B hB
    obtain ⟨hb, hc⟩ := Finset.mem_filter.mp hB
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hb
    refine ⟨Finset.inter_subset_right, hc, ?_⟩
    have hle : (C ∩ U).card ≤ Nat.sqrt A.card :=
      (Finset.card_le_card Finset.inter_subset_left).trans (hE C hC).2
    have hle' : ((C ∩ U).card : ℝ) ≤ n := (Nat.cast_le.mpr hle).trans hcap
    linarith
  have hdegree : ∀ x ∈ U, ((∑ B ∈ F.filter (x ∈ ·), (B.card - 1).choose 2 : ℕ) : ℝ)
      ≤ 884736 * n^2 * Real.log n := by
    intro x hx
    rw [← degree_eq_incident]
    have hx' : (degree E x : ℝ) ≤ t := (Finset.mem_filter.mp hx).2
    have hrestrict : (degree F x : ℝ) ≤ degree E x := by exact_mod_cast restricted_degree_le E U x
    calc
      _ ≤ t := hrestrict.trans hx'
      _ = _ := by rw [hn₂, Real.log_sqrt hA₀]; dsimp [t]; ring
  obtain ⟨I, hI, hsize, hind⟩ := select n U F hn₀ hedge (restrict_linear U lin) hdegree
  refine ⟨I, hI.trans (Finset.filter_subset _ _), ?_, lift_independent hI hind⟩
  change g * (U.card : ℝ) ≤ n * (I.card : ℝ) at hsize
  have hhalf' : (A.card : ℝ) ≤ 2 * (U.card : ℝ) := by exact_mod_cast hhalf
  have hm := mul_le_mul_of_nonneg_left hhalf' hg.le
  rw [← hn₂] at hm
  change g / 2 * n ≤ (I.card : ℝ)
  apply (mul_le_mul_iff_left₀ hn).mp
  calc
    _ = (g * n ^ 2) / 2 := by ring
    _ ≤ (g * (2 * (U.card : ℝ))) / 2 := div_le_div_of_nonneg_right hm (by norm_num)
    _ = g * (U.card : ℝ) := by ring
    _ ≤ n * I.card := hsize
    _ = _ := mul_comm _ _

end OMA.GeneralPositionPretrim


namespace OMA.GeneralPositionPretrim
open OMA.S_opg_general_position_subsets
open scoped Classical

/-- A finite law with prescribed lower marginals has a realization at least
as large as the sum of the marginal lower bounds. -/
theorem exists_large_of_marginals {V : Type*} [DecidableEq V] (U : Finset V)
    (S : Finset (Finset V)) (w : Finset V → ℝ) (q : ℝ)
    (hsub : ∀ I ∈ S, I ⊆ U) (hw : ∀ I ∈ S, 0 ≤ w I)
    (mass : ∑ I ∈ S, w I = 1)
    (hmarg : ∀ x ∈ U, q ≤ ∑ I ∈ S.filter (x ∈ ·), w I) :
    ∃ I ∈ S, q * U.card ≤ I.card := by
  classical
  have hne : S.Nonempty := by
    by_contra! h
    simp [h] at mass
  obtain ⟨J, hJ, hmax⟩ := S.exists_max_image Finset.card hne
  refine ⟨J, hJ, ?_⟩
  calc
    q * U.card = ∑ _x ∈ U, q := by simp [mul_comm]
    _ ≤ ∑ x ∈ U, ∑ I ∈ S.filter (x ∈ ·), w I := Finset.sum_le_sum hmarg
    _ = ∑ I ∈ S, (I.card : ℝ) * w I := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro I hI
      have heq : U.filter (· ∈ I) = I := by
        ext x
        simpa using (show x ∈ I → x ∈ U from fun hx => hsub I hI hx)
      rw [← Finset.sum_filter, heq]
      simp
    _ ≤ ∑ I ∈ S, (J.card : ℝ) * w I := by
      apply Finset.sum_le_sum
      intro I hI
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hmax I hI)) (hw I hI)
    _ = J.card := by rw [← Finset.mul_sum, mass, mul_one]

/-- Lemma 9, specialized to the single constant used in Section 2.4.
The law of the random independent set is represented on its finite support. -/
def Lemma9Marginals : Prop :=
  ∃ n₀ : ℕ, ∀ (n : ℝ) (U : Finset P) (F : Finset (Finset P)), (n₀ : ℝ) ≤ n →
    (∀ B ∈ F, B ⊆ U ∧ 3 ≤ B.card ∧ (B.card : ℝ) ≤ 884736 * n) →
    (∀ B ∈ F, ∀ D ∈ F, B ≠ D → (B ∩ D).card ≤ 1) →
    (∀ x ∈ U, ((∑ B ∈ F.filter (x ∈ ·), (B.card - 1).choose 2 : ℕ) : ℝ)
      ≤ 884736 * n ^ 2 * Real.log n) →
    ∃ (S : Finset (Finset P)) (w : Finset P → ℝ),
      (∀ I ∈ S, I ⊆ U ∧ ∀ B ∈ F, (I ∩ B).card ≤ 2) ∧
      (∀ I ∈ S, 0 ≤ w I) ∧ (∑ I ∈ S, w I) = 1 ∧
      ∀ x ∈ U, 1 / (4000 * 884736 * n) ≤ ∑ I ∈ S.filter (x ∈ ·), w I

theorem selection_of_marginals : Lemma9Marginals → Lemma9Selection := by
  rintro ⟨n₀, h⟩
  refine ⟨max 1 n₀, ?_⟩
  intro n U F hn hedge hlin hdeg
  have h₀ : (n₀ : ℝ) ≤ n := (Nat.cast_le.mpr (le_max_right 1 n₀)).trans hn
  have h₁ : (1 : ℝ) ≤ n := (by exact_mod_cast (le_max_left 1 n₀) : (1 : ℝ) ≤ (max 1 n₀ : ℕ)).trans hn
  have hpos : 0 < n := by linarith
  obtain ⟨S, w, hset, hw, hmass, hm⟩ := h n U F h₀ hedge hlin hdeg
  obtain ⟨I, hI, hcard⟩ := exists_large_of_marginals U S w _ (fun I hI => (hset I hI).1) hw hmass hm
  refine ⟨I, (hset I hI).1, ?_, (hset I hI).2⟩
  calc
    _ = n * (1 / (4000 * 884736 * n) * U.card) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hcard hpos.le

theorem h1_of_marginals : Lemma9Marginals → OMA.R_opg_general_position_subsets_R1.H1 :=
  h1_of_lemma9 ∘ selection_of_marginals

end OMA.GeneralPositionPretrim

namespace OMA.GeneralPositionOuter

open Filter Finset OMA.OnlineSelection OMA.OnlineSelection.HypergraphState
open OMA.GeneralPositionSelection OMA.GeneralPositionCodegrees OMA.GeneralPositionLoss
open OMA.GeneralPositionHistory OMA.GeneralPositionUnaffected OMA.GeneralPositionPretrim
open scoped BigOperators Classical

variable {V : Type*} [DecidableEq V]

/-- The remaining local inequality, with the scalar hypotheses used by
the capped process. -/
def AffectedEstimate (V : Type*) [DecidableEq V] : Prop :=
  ∀ {E : Finset (Finset V)} (_ : Linear E) (Q : Finset V) (v : V)
    {a τ σ lam : ℝ}, 0 < a → a < τ → τ ≤ 1/4 → τ ≤ σ → σ ≤ 1 →
    2*τ*(1/8)/σ ≤ Real.log 2 → 1 ≤ Real.log (τ/a) →
    lam = Real.exp (-((1/8)/(2*σ))) →
    LocalBound true (retainedEdges E Q) v a τ σ lam (paperLoss (retainedEdges E Q) Q v τ σ)

theorem select_at {U : Finset V} {E : Finset (Finset V)} (hE : Linear E)
    {K n : ℝ} (hK : 1 ≤ K) (affected : AffectedEstimate V)
    (H :
      1 < n ∧ 1 ≤ degreeLimit K n ∧
      0 < p n ∧ p n ≤ 1 ∧
      0 < a K n ∧ a K n < tau n ∧ tau n ≤ 1/4 ∧ tau n ≤ sigma n ∧ sigma n ≤ 1 ∧
      2*tau n*(1/8)/sigma n ≤ Real.log 2 ∧ 1 ≤ Real.log (tau n / a K n) ∧
      degreeLimit K n * Real.exp (-(K * n ^ (1/6 : ℝ))/2) ≤ 1/4 ∧
      a K n * (3*(K * n ^ (1/6 : ℝ))+1) ≤ (1/8)/4 ∧
      sampledDegree K n * Real.exp (-((1/8)/(4*sigma n))) +
        2*a K n^2*sampledDegree K n/Real.log (tau n/a K n) ≤ 1/4 ∧
      256 * p n^6 * degreeLimit K n^(7/3 : ℝ) *
        (tau n^6/sigma n^2 + tau n^5/sigma n) ≤ p n*a K n/16)
    (hedge : ∀ B ∈ E, B ⊆ U ∧ 3 ≤ B.card ∧ (B.card : ℝ) ≤ K*n)
    (hdegree : ∀ v ∈ U, (tripleDegree E v : ℝ) ≤ degreeLimit K n) :
    ∃ I ⊆ U, (1/(4000*K))*U.card ≤ n*I.card ∧ Independent E I := by
  obtain ⟨hn,hD,hp,hp1,ha,haτ,hτ4,hτσ,hσ1,hscale,hL,hsmall,hsize,hscalar,hloss⟩ := H
  have hn0 := zero_lt_one.trans hn
  let t := K * n ^ (1/6 : ℝ)
  let η : ℝ := 1/8
  let lam := Real.exp (-(η/(2*sigma n)))
  have hdeg (v : V) : (tripleDegree E v : ℝ) ≤ degreeLimit K n := by
    by_cases hv : v ∈ U
    · exact hdegree v hv
    · have hfilter : E.filter (v ∈ ·) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro B h
        exact hv ((hedge B (mem_filter.mp h).1).1 (mem_filter.mp h).2)
      rw [tripleDegree, incident, hfilter, sum_empty, Nat.cast_zero]
      linarith
  have hσ := (ha.trans haτ).trans_le hτσ
  have hτ := (ha.trans haτ).le
  have hτ1 : tau n < 1 := by linarith
  have heq : p n * n = n ^ (1/6 : ℝ) := by
    rw [p, ← Real.rpow_add_one hn0.ne', show (-5/6 : ℝ) + 1 = 1/6 by norm_num]
  have hsizeB (B : Finset V) (hB : B ∈ E) :
      B ⊆ U ∧ 3 ≤ B.card ∧ p n * B.card ≤ t := by
    obtain ⟨hb, hb3, hbK⟩ := hedge B hB
    refine ⟨hb, hb3, (mul_le_mul_of_nonneg_left hbK hp.le).trans ?_⟩
    rw [show p n * (K * n) = K * (p n * n) by ring, heq]
  have hj (v : V) (hv : v ∈ U) := sampled_joint_lower hE hv hD hp hp1 ha haτ hτ1 hσ
    (show lam = Real.exp (-(η/(2*sigma n))) from rfl)
    hsizeB hdeg hsmall hsize hscalar hloss
    (fun S _ => localBound_false hE _ v ha haτ hτ4 hτσ hσ1 hscale hL rfl)
    (fun S _ => affected hE _ v ha haτ hτ4 hτσ hσ1 hscale hL rfl)
  obtain ⟨I,hIU,hI,hInd⟩ := exists_large_from_joint hp.le hp1 hτ hτ1 ha.le haτ.le hj
  refine ⟨I,hIU,?_ ,hInd⟩
  calc
    _ = n * ((p n * a K n / 4) * U.card) := by
      rw [initial_scale hn0, gamma]
      field_simp [show K ≠ 0 by linarith]
      <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hI hn0.le

theorem lemma9_of_affected (h : AffectedEstimate OMA.S_opg_general_position_subsets.P) :
    Lemma9Selection := by
  classical
  obtain ⟨r, hr⟩ := eventually_atTop.mp
    (show ∀ᶠ n : ℝ in atTop, ∀ (U : Finset OMA.S_opg_general_position_subsets.P)
        (E : Finset (Finset OMA.S_opg_general_position_subsets.P)),
        Linear E →
        (∀ B ∈ E, B ⊆ U ∧ 3 ≤ B.card ∧ (B.card : ℝ) ≤ 884736*n) →
        (∀ v ∈ U, (tripleDegree E v : ℝ) ≤ degreeLimit 884736 n) →
        ∃ I ⊆ U, (1/(4000*884736))*U.card ≤ n*I.card ∧ Independent E I from by
      -- A single sufficient parameter threshold works for every finite hypergraph.
      filter_upwards [selection_parameters_eventually (K := 884736) (by norm_num)] with n hn
      intro U E hE hs hd
      exact select_at hE (by norm_num) h hn hs hd)
  obtain ⟨n₀, h₀⟩ := exists_nat_ge r
  refine ⟨n₀, ?_⟩
  intro n U E hn hs hlin hd
  exact hr n (h₀.trans hn) U E hlin hs hd

theorem registered_of_affected (h : AffectedEstimate OMA.S_opg_general_position_subsets.P) :
    OMA.R_opg_general_position_subsets_R1.H1 :=
  h1_of_lemma9 (lemma9_of_affected h)


end OMA.GeneralPositionOuter

/-! Separate rejection-branch bounds for the mixed edges in Lemma 9, §2.3. -/

namespace OMA.GeneralPositionSelection

open Finset OMA.GeneralPositionProducts OMA.GeneralPositionCommonEdge
open scoped Classical

variable {V : Type*} [DecidableEq V]

lemma exp_sub_one_le_twice {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ Real.log 2) :
    Real.exp t - 1 ≤ 2 * t := by
  have hexp := Real.exp_pos t
  have hexp' : Real.exp t ≤ 2 := (Real.exp_le_exp.mpr ht').trans_eq (Real.exp_log (by norm_num))
  have h := Real.add_one_le_exp (-t)
  rw [Real.exp_neg] at h
  have hb := (le_div_iff₀ hexp).mp (show -t + 1 ≤ 1 / Real.exp t by simpa only [one_div] using h)
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hexp')]

theorem reject_mixed_product {A U : Finset V} (hA : A ⊆ U)
    (z : V → ℝ) {q τ σ : ℝ} (hσ : 0 < σ) (hq : 0 ≤ q) (hq' : q ≤ 1/2)
    (hz : ∀ x ∈ U, 0 ≤ z x ∧ z x ≤ τ)
    (hsmall : 2*q*(∑ x ∈ U, z x)/σ ≤ Real.log 2) :
    edgeProduct U (onReject A z q τ) σ - edgeProduct U z σ ≤
      4*q*edgeProduct U z σ/σ * ∑ x ∈ A, z x := by
  have hs : 0 < 1-q := by linarith
  let w := onReject A z q τ
  have le_w (x : V) (hx : x ∈ U) : z x ≤ w x := by
    by_cases hax : x ∈ A
    · simp only [w, onReject, if_pos hax, le_min_iff]
      exact ⟨(le_div_iff₀ hs).mpr (by nlinarith [(hz x hx).1]), (hz x hx).2⟩
    · simp [w, onReject, hax]
  have hfac (x : V) (hx : x ∈ U) : 0 < 1 + z x/σ := by
    have := (hz x hx).1
    positivity
  have hfac' (x : V) (hx : x ∈ U) : 0 < 1 + w x/σ := by
    have := (hz x hx).1.trans (le_w x hx)
    positivity
  let G := edgeProduct U z σ
  let G' := edgeProduct U w σ
  have hG : 0 < G := prod_pos hfac
  have hG' : 0 < G' := prod_pos hfac'
  have hlog : Real.log (G'/G) ≤ 2*q*(∑ x ∈ A, z x)/σ := by
    rw [Real.log_div hG'.ne' hG.ne']
    unfold G G' edgeProduct
    rw [Real.log_prod (fun x hx => (hfac' x hx).ne'),
      Real.log_prod (fun x hx => (hfac x hx).ne'), ← sum_sub_distrib]
    rw [show 2*q*(∑ x ∈ A, z x)/σ = ∑ x ∈ A, 2*q*z x/σ by rw [mul_sum, sum_div]]
    have hf : U.filter (· ∈ A) = A := filter_mem_eq_inter.trans (inter_eq_right.mpr hA)
    rw [← hf, sum_filter]
    apply sum_le_sum
    intro x hx
    by_cases hxA : x ∈ A
    · rw [if_pos hxA, ← Real.log_div (hfac' x hx).ne' (hfac x hx).ne']
      apply (Real.log_le_sub_one_of_pos (div_pos (hfac' x hx) (hfac x hx))).trans
      have hz0 := (hz x hx).1
      have hw : w x ≤ z x/(1-q) := by simp only [w, onReject, if_pos hxA, min_le_left]
      have hwZ : w x - z x ≤ 2*q*z x := by
        calc
          _ ≤ z x/(1-q) - z x := sub_le_sub_right hw _
          _ ≤ 2*q*z x := by
            rw [sub_le_iff_le_add]
            apply (div_le_iff₀ hs).mpr
            nlinarith [mul_nonneg (mul_nonneg hq hz0) (show 0 ≤ 1-2*q by linarith)]
      have hr : (1+w x/σ)/(1+z x/σ) - 1 =
          ((w x-z x)/σ)/(1+z x/σ) := by
        field_simp
        <;> ring
      rw [hr]
      apply (div_le_iff₀ (hfac x hx)).mpr
      have hu := div_le_div_of_nonneg_right hwZ hσ.le
      have hp := mul_nonneg (show 0 ≤ 2*q*z x/σ by positivity) (div_nonneg hz0 hσ.le)
      linarith
    · simp [w, onReject, hxA]
  have hle : G ≤ G' := prod_le_prod (fun x hx => (hfac x hx).le)
    (fun x hx => add_le_add le_rfl (div_le_div_of_nonneg_right (le_w x hx) hσ.le))
  have hlog0 := Real.log_nonneg ((one_le_div hG).mpr hle)
  have hlog2 : Real.log (G'/G) ≤ Real.log 2 := hlog.trans (le_trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hA (fun x hx _ => (hz x hx).1)) (by positivity))
      hσ.le) hsmall)
  have hexp := exp_sub_one_le_twice hlog0 hlog2
  rw [Real.exp_log (div_pos hG' hG)] at hexp
  have hmul := mul_le_mul_of_nonneg_left (hexp.trans (mul_le_mul_of_nonneg_left hlog (by norm_num))) hG.le
  have hcancel : G * (G'/G - 1) = G' - G := by field_simp
  rw [hcancel] at hmul
  change G' - G ≤ 4*q*G/σ * ∑ x ∈ A, z x
  calc
    _ ≤ _ := hmul
    _ = _ := by ring

theorem pairSum_identity (U : Finset V) (z : V → ℝ) :
    2 * pairSum U z = (∑ x ∈ U, z x)^2 - ∑ x ∈ U, (z x)^2 := by
  classical
  induction U using Finset.induction_on with
  | empty =>
    have hE : (∅ : Finset V).powersetCard 2 = ∅ := by
      ext P
      simp only [mem_powersetCard, subset_empty, notMem_empty, iff_false]
      rintro ⟨rfl, h⟩
      norm_num at h
    simp [pairSum, hE]
  | @insert x U hx ih =>
    rw [pairSum_insert hx, sum_insert hx, sum_insert hx]
    linarith [sq_nonneg (z x), (show (z x+∑ y ∈ U, z y)^2 =
      (z x)^2 + (∑ y ∈ U, z y)^2 + 2*z x*(∑ y ∈ U, z y) by ring)]

theorem reject_mixed_phi {A U : Finset V} (hA : A ⊆ U) (z : V → ℝ)
    {q τ : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1/4)
    (hz : ∀ x ∈ U, 0 ≤ z x ∧ z x ≤ τ)
    (hmass : (∑ x ∈ U, z x) ≤ 1/8) :
    (2*∑ x ∈ U, onReject A z q τ x) - (2*∑ x ∈ U, z x) ≤ 10*q*∑ x ∈ A, z x ∧
    2*pairSum U (onReject A z q τ) - 2*pairSum U z ≤ 10*q*∑ x ∈ A, z x := by
  let w := onReject A z q τ
  let M := ∑ x ∈ U, z x
  let M' := ∑ x ∈ U, w x
  let MA := ∑ x ∈ A, z x
  have hs : 0 < 1-q := by linarith
  have hw (x : V) (hx : x ∈ U) : z x ≤ w x ∧ w x ≤ z x/(1-q) := by
    have hd : z x ≤ z x/(1-q) := (le_div_iff₀ hs).mpr (by nlinarith [(hz x hx).1])
    by_cases hxA : x ∈ A
    · simp only [w, onReject, if_pos hxA, le_min_iff]
      exact ⟨⟨hd, (hz x hx).2⟩, min_le_left _ _⟩
    · simpa [w, onReject, hxA] using hd
  have hM' : M' ≤ M/(1-q) := by
    dsimp [M', M]
    rw [sum_div]
    exact sum_le_sum fun x hx => (hw x hx).2
  have hdiff : M'-M ≤ 2*q*MA := by
    dsimp [M', M, MA]
    rw [← sum_sub_distrib, mul_sum]
    have hf : U.filter (· ∈ A) = A := filter_mem_eq_inter.trans (inter_eq_right.mpr hA)
    rw [← hf, sum_filter]
    apply sum_le_sum
    intro x hx
    by_cases hxA : x ∈ A
    · rw [if_pos hxA]
      apply (sub_le_sub_right (hw x hx).2 _).trans
      rw [sub_le_iff_le_add]
      apply (div_le_iff₀ hs).mpr
      nlinarith [mul_nonneg (mul_nonneg hq (hz x hx).1) (show 0 ≤ 1-2*q by linarith)]
    · simp [w, onReject, hxA]
  have hM0 : 0 ≤ M := sum_nonneg fun x hx => (hz x hx).1
  have hMle : M ≤ M' := sum_le_sum fun x hx => (hw x hx).1
  have hM'0 := hM0.trans hMle
  have hMA0 : 0 ≤ MA := sum_nonneg fun x hx => (hz x (hA hx)).1
  have hM'1 : M' ≤ 1/6 := hM'.trans ((div_le_iff₀ hs).mpr (by linarith))
  have hpair := sum_le_sum (s := U) fun x hx => pow_le_pow_left₀ (hz x hx).1 (hw x hx).1 2
  constructor
  · change 2*M'-2*M ≤ 10*q*MA
    nlinarith [mul_nonneg hq hMA0]
  · rw [pairSum_identity, pairSum_identity]
    change (M')^2 - (∑ x ∈ U, w x ^ 2) - (M^2 - ∑ x ∈ U, z x ^ 2) ≤ 10*q*MA
    have hsq : (M')^2-M^2 ≤ 2*q*MA := by
      calc
        _ = (M'-M)*(M'+M) := by ring
        _ ≤ (M'-M)*1 := mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hMle)
        _ ≤ _ := by simpa only [mul_one] using hdiff
    nlinarith [mul_nonneg hq hMA0]

end OMA.GeneralPositionSelection

/-! Pham, Le Quang-Ham and Xue, “General-position sets and linear
hypergraphs”, §2.3. The common edge on the rejection branch in (2.6). -/

namespace OMA.GeneralPositionAffected
open OMA.GeneralPositionUnaffected OMA.GeneralPositionSelection
open Finset OMA.OnlineSelection OMA.OnlineSelection.HypergraphState
open OMA.GeneralPositionProducts OMA.GeneralPositionPotential OMA.GeneralPositionHistory
open OMA.GeneralPositionLoss OMA.GeneralPositionCodegrees OMA.GeneralPositionCommonEdge
open scoped BigOperators Classical
variable {V : Type*} [DecidableEq V]

theorem common_rejection {E : Finset (Finset V)} {s : HypergraphState V} {x v : V} {B : Finset V}
    (hB : B ∈ E) (hxB : x ∈ B) (hvB : v ∈ B) (hx : x ∈ s.remaining) (haff : Affected E s x v)
    (hc : (s.selected ∩ B).card = 1) (hR : ∀ u ∈ (unprocessed s v B).erase x, Affected E s x u)
    {τ σ a lam : ℝ} (ha : 0 < a) (haτ : a < τ) (hτ4 : τ ≤ 1/4) (hτσ : τ ≤ σ)
    (hlam : 0 ≤ lam) (hs : WeightsIn τ s) (hvz : 0 < s.weight v)
    (hm : mass s v B < 1/8) (hp : 0 < potential true E s v a τ σ lam) :
    let q := s.weight x
    let N := advance E τ x false s
    N.weight v = s.weight v/(1-q) ∧ N.weight v < τ ∧ (1-q)*N.weight v = s.weight v ∧
      edgeG N v σ B ≤ edgeG s v σ B ∧
      Real.log (N.weight v/a) + edgePhi N v B ≤ Real.log (s.weight v/a) + edgePhi s v B := by
  let U := unprocessed s v B
  let R := U.erase x
  let N := advance E τ x false s
  let w := onReject R s.weight (s.weight x) τ
  have hxu : x ∈ U := mem_erase.mpr ⟨(mem_erase.mp haff.1).1.symm,mem_inter.mpr ⟨hx,hxB⟩⟩
  have hi : insert x R = U := insert_erase hxu
  have hnr : unprocessed N v B = R := unprocessed_advance _ _ _ _ _ _ _
  have hw (u : V) (hu : u ∈ R) : N.weight u = w u := by
    simp [N,w,advance,updateWeight,onReject,hu,hR u hu]
  have hz : N.weight v = min (s.weight v/(1-s.weight x)) τ := updateWeight_reject_of_affected haff
  have hphi : edgePhi s v B = 2 * ∑ u ∈ U, s.weight u := by
    simp only [edgePhi,hc,one_ne_zero,if_false,mass,U]
  have hphi' : edgePhi N v B = 2 * ∑ u ∈ R, w u := by
    have hc' : (N.selected ∩ B).card = 1 := hc
    simp only [edgePhi,hc',one_ne_zero,if_false,mass,hnr,sum_congr rfl hw]
  have hg' : edgeG N v σ B = edgeProduct R w σ := by
    unfold edgeG
    rw [hnr]
    exact edgeProduct_congr hw σ
  have hsum : edgePhi s v B ≤ sumPhi E s v :=
    single_le_sum (fun C _ => edgePhi_nonneg s v C (fun u => (hs u).1)) (mem_filter.mpr ⟨hB,hvB⟩)
  have hΦ : 2*(∑ u ∈ insert x R, s.weight u) ≤ sumPhi E s v := by rwa [hi,← hphi]
  have hG : 0 ≤ sumG E s v σ := sum_nonneg fun C _ =>
    (edgeG_pos s v C ((ha.trans haτ).trans_le hτσ) fun u => (hs u).1).le
  have hm' : s.weight x + ∑ u ∈ R, s.weight u < 1/8 := by
    change (∑ u ∈ U, s.weight u) < _ at hm
    rwa [← hi,sum_insert (notMem_erase x U)] at hm
  have hC := hp
  rw [potential,if_pos ⟨rfl,mem_of_mem_erase haff.1⟩] at hC
  obtain ⟨hprod,_,huncap,hlt,hcomp,hcombined⟩ := common_case_two (R := R) (x := x) (notMem_erase x U)
    s.weight rfl (fun u _ => (hs u).1) (hs x).1 ((hs x).2.trans hτ4)
    ((ha.trans haτ).trans_le hτσ) ((hs x).2.trans hτσ) (ha.trans haτ) ha hvz hm'
    (mul_nonneg hlam hG) hΦ (Real.log_pos ((one_lt_div ha).mpr haτ)) hC
  rw [hi] at hprod hcombined
  change N.weight v = _ ∧ N.weight v < _ ∧ _ * N.weight v = _ ∧ edgeG N v σ B ≤ _ ∧ _ + edgePhi N v B ≤ _
  rw [hz,hg',hphi',hphi]
  exact ⟨huncap,hlt,hcomp,hprod,hcombined⟩

end OMA.GeneralPositionAffected

namespace OMA.GeneralPositionAffected
open OMA.GeneralPositionUnaffected OMA.GeneralPositionSelection
open Finset OMA.OnlineSelection OMA.OnlineSelection.HypergraphState
open OMA.GeneralPositionProducts OMA.GeneralPositionPotential OMA.GeneralPositionHistory
open OMA.GeneralPositionLoss OMA.GeneralPositionCodegrees OMA.GeneralPositionCommonEdge
open scoped BigOperators Classical
variable {V : Type*} [DecidableEq V]

theorem mixed_rejection {E : Finset (Finset V)} {s : HypergraphState V} {x v : V} {B : Finset V}
    (hx : x ∉ B) {τ σ : ℝ} (hs : WeightsIn τ s) (hq : s.weight x ≤ 1/4)
    (hσ : 0 < σ) (hm : mass s v B ≤ 1/8) (hsmall : 2*s.weight x*mass s v B/σ ≤ Real.log 2) :
    let N := advance E τ x false s
    let q := s.weight x
    let W := ∑ u ∈ activeSet E s x v B, s.weight u
    (edgeG N v σ B - edgeG s v σ B ≤ 4*q*edgeG s v σ B/σ * W) ∧
    (edgePhi N v B - edgePhi s v B ≤ 10*q*W) := by
  let U := unprocessed s v B
  let A := activeSet E s x v B
  let N := advance E τ x false s
  let w := onReject A s.weight (s.weight x) τ
  have hn (u : V) (hu : u ∈ U) : N.weight u = w u := (weight_update_on E s x v B τ hu).2
  have hA : A ⊆ U := filter_subset _ _
  have hU : unprocessed N v B = U := by
    rw [unprocessed_advance,erase_eq_of_notMem]
    exact fun h => hx (mem_inter.mp (mem_of_mem_erase h)).2
  have hG : edgeG N v σ B = edgeProduct U w σ := by
    unfold edgeG
    rw [hU]
    exact edgeProduct_congr hn _
  have hz (u : V) (_ : u ∈ U) := hs u
  have hP := reject_mixed_phi hA s.weight (hs x).1 hq hz hm
  constructor
  · rw [hG]
    exact reject_mixed_product hA s.weight hσ (hs x).1 (by linarith) hz hsmall
  · change edgePhi N v B - edgePhi s v B ≤ _
    have he : N.selected = s.selected := rfl
    unfold edgePhi mass
    rw [hU,he]
    by_cases hc : (s.selected ∩ B).card = 0
    · simp only [hc,if_true]
      rw [pairSum_congr hn]
      exact hP.2
    · simp only [hc,if_false]
      rw [sum_congr rfl hn]
      exact hP.1

/-- Bound the rejection drift of an ordinary incident edge per affected vertex. -/
theorem mixed_rejection_cost {s N : HypergraphState V} {x v : V} {A B : Finset V}
    {τ σ lam L : ℝ} (hs : WeightsIn τ s) (hτ : 0 ≤ τ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hlam : 0 ≤ lam) (hL : 1 ≤ L) (hG : lam * edgeG s v σ B ≤ 1)
    (hg : edgeG N v σ B - edgeG s v σ B ≤ 4*s.weight x*edgeG s v σ B/σ * ∑ u ∈ A, s.weight u)
    (hp : edgePhi N v B - edgePhi s v B ≤ 10*s.weight x* ∑ u ∈ A, s.weight u) :
    edgeCost N v σ lam L (s.weight v) B - edgeCost s v σ lam L (s.weight v) B ≤
      (16*τ^2/σ)*s.weight x*A.card := by
  let q := s.weight x
  let W := ∑ u ∈ A, s.weight u
  have hW : 0 ≤ W := sum_nonneg fun u _ => (hs u).1
  have hq : 0 ≤ q := (hs x).1
  have hw : W ≤ τ*A.card := calc
    W ≤ ∑ _u ∈ A, τ := sum_le_sum fun u _ => (hs u).2
    _ = _ := by simp [mul_comm]
  have hg' : lam*(edgeG N v σ B-edgeG s v σ B) ≤ (4*q/σ)*W := calc
    _ ≤ lam*(4*q*edgeG s v σ B/σ*W) := mul_le_mul_of_nonneg_left hg hlam
    _ = (4*q/σ*W)*(lam*edgeG s v σ B) := by ring
    _ ≤ (4*q/σ*W)*1 := mul_le_mul_of_nonneg_left hG (by positivity)
    _ = _ := mul_one _
  have hp' : (edgePhi N v B-edgePhi s v B)/L ≤ (10*q/σ)*W := calc
    _ ≤ (10*q*W)/L := div_le_div_of_nonneg_right hp (by linarith)
    _ ≤ 10*q*W := div_le_self (by positivity) hL
    _ ≤ _ := mul_le_mul_of_nonneg_right ((le_div_iff₀ hσ).mpr
      (mul_le_of_le_one_right (by positivity) hσ1)) hW
  have hcoef : 4*q/σ + 10*q/σ ≤ 16*q/σ := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hσ.le
  unfold edgeCost
  calc
    _ = s.weight v*(lam*(edgeG N v σ B-edgeG s v σ B)+(edgePhi N v B-edgePhi s v B)/L) := by ring
    _ ≤ s.weight v*((4*q/σ)*W+(10*q/σ)*W) :=
      mul_le_mul_of_nonneg_left (add_le_add hg' hp') (hs v).1
    _ = s.weight v*((4*q/σ + 10*q/σ)*W) := by ring
    _ ≤ τ*((16*q/σ)*(τ*A.card)) := mul_le_mul (hs v).2
      (mul_le_mul hcoef hw hW (by positivity)) (by positivity) hτ
    _ = _ := by dsimp [q]; ring

end OMA.GeneralPositionAffected

namespace OMA.GeneralPositionAffected
open OMA.GeneralPositionUnaffected OMA.GeneralPositionSelection
open Finset OMA.OnlineSelection OMA.OnlineSelection.HypergraphState
open OMA.GeneralPositionProducts OMA.GeneralPositionPotential OMA.GeneralPositionHistory
open OMA.GeneralPositionLoss OMA.GeneralPositionCodegrees OMA.GeneralPositionCommonEdge
open scoped BigOperators Classical
variable {V : Type*} [DecidableEq V]

/-- The common-edge drop pays for the change in the tracked logarithm. -/
theorem common_rejection_cost {s N : HypergraphState V} {v : V} {B : Finset V} {a σ lam L : ℝ}
    (hz : 0 ≤ s.weight v) (hlam : 0 ≤ lam) (hL : 0 ≤ L)
    (hG : edgeG N v σ B ≤ edgeG s v σ B)
    (hp : Real.log (N.weight v/a) + edgePhi N v B ≤ Real.log (s.weight v/a) + edgePhi s v B) :
    edgeCost N v σ lam L (s.weight v) B - edgeCost s v σ lam L (s.weight v) B ≤
      -(s.weight v*((Real.log (N.weight v/a)-Real.log (s.weight v/a))/L)) := by
  have hh := mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hG hlam)
    (div_le_div_of_nonneg_right hp hL)) hz
  unfold edgeCost
  simp only [add_div,sub_div,mul_add,mul_sub] at hh ⊢
  linarith only [hh]

theorem accept_zero {E : Finset (Finset V)} {s : HypergraphState V} {x v : V}
    (h : Affected E s x v) (a τ σ lam : ℝ) :
    potential true E (advance E τ x true s) v a τ σ lam = 0 := by
  have hv : v ∈ (advance E τ x true s).remaining := h.1
  have hz : (advance E τ x true s).weight v = 0 := updateWeight_accept_of_affected h
  rw [potential,if_pos ⟨rfl,hv⟩,hz,zero_mul]

theorem from_rejection_cost {E : Finset (Finset V)} {s : HypergraphState V} {x v : V}
    {a τ σ lam loss : ℝ} (haff : Affected E s x v)
    (hq : s.weight x ≤ 1) (hp : 0 < potential true E s v a τ σ lam)
    (hn : 0 ≤ (advance E τ x false s).weight v)
    (hcomp : (1-s.weight x)*(advance E τ x false s).weight v = s.weight v)
    (hd : let N := advance E τ x false s
          let L := Real.log (τ/a)
          totalCost E N v σ lam L (s.weight v) - totalCost E s v σ lam L (s.weight v) ≤
            loss - s.weight v*((Real.log (N.weight v/a)-Real.log (s.weight v/a))/L)) :
    potential true E s v a τ σ lam ≤
      s.weight x*potential true E (advance E τ x true s) v a τ σ lam +
      (1-s.weight x)*potential true E (advance E τ x false s) v a τ σ lam + loss := by
  let N := advance E τ x false s
  let L := Real.log (τ/a)
  have hraw := potential_raw_le E (s := N) (v := v) haff.1 hn a τ σ lam
  have h := mul_le_mul_of_nonneg_left hraw (sub_nonneg.mpr hq)
  have hc : (1-s.weight x)*N.weight v = s.weight v := hcomp
  rw [potential_raw_eq (mem_of_mem_erase haff.1) hp,accept_zero haff,mul_zero,zero_add]
  dsimp only at hd
  rw [totalCost_eq,totalCost_eq] at hd
  rw [totalCost_eq] at h ⊢
  rw [mul_sub,← mul_assoc,hc,← mul_assoc,hc] at h
  dsimp only [N] at h
  simp only [sub_div,mul_sub] at h hd ⊢
  linarith only [h,hd]

end OMA.GeneralPositionAffected

namespace OMA.GeneralPositionAffected
open OMA.GeneralPositionUnaffected OMA.GeneralPositionSelection
open Finset OMA.OnlineSelection OMA.OnlineSelection.HypergraphState
open OMA.GeneralPositionProducts OMA.GeneralPositionPotential OMA.GeneralPositionHistory
open OMA.GeneralPositionLoss OMA.GeneralPositionCodegrees OMA.GeneralPositionCommonEdge
open scoped BigOperators Classical
variable {V : Type*} [DecidableEq V]

/-- The affected case (2.6) on the true retained traces with the registered
two-pattern step loss. The mass cutoff may be any η ≤ 1/8. -/
theorem localBound_true {E : Finset (Finset V)} (hE : Linear E) (Q : Finset V) (v : V)
    {a τ σ η lam : ℝ} (ha : 0 < a) (haτ : a < τ) (hτ4 : τ ≤ 1/4)
    (hτσ : τ ≤ σ) (hσ1 : σ ≤ 1) (hη : η ≤ 1/8)
    (hscale : 2*τ*η/σ ≤ Real.log 2) (hL : 1 ≤ Real.log (τ/a))
    (hlam : lam = Real.exp (-(η/(2*σ)))) :
    LocalBound true (retainedEdges E Q) v a τ σ lam (paperLoss (retainedEdges E Q) Q v τ σ) := by
  let F := retainedEdges E Q
  have hF : Linear F := linear_trace hE Q
  have hsize (B : Finset V) (hB : B ∈ F) : 3 ≤ (B ∩ Q).card := by
    obtain ⟨⟨C,hC,rfl⟩,hc⟩ := mem_trace.mp hB
    simpa only [inter_assoc,inter_self] using hc
  intro x tail s hs hvd _ hkind hp
  have hx : x ∈ s.remaining := by simp [hvd.remaining]
  have haff : Affected F s x v := hkind.mpr rfl
  have hz := positive_consequences ha haτ hτσ hlam hs hvd.floor hp
  have hq := (hs x).2.trans hτ4
  have hτ := (ha.trans haτ).le
  have hσ := (ha.trans haτ).trans_le hτσ
  have hlam0 : 0 ≤ lam := hlam ▸ (Real.exp_pos _).le
  let N := advance F τ x false s
  let L := Real.log (τ/a)
  let T := F.filter (v ∈ ·)
  let c := (16*τ^2/σ)*s.weight x
  let logChange := s.weight v*((Real.log (N.weight v/a)-Real.log (s.weight v/a))/L)
  let count (B : Finset V) : ℝ := if x ∈ B then 0 else (activeSet F s x v B).card
  obtain ⟨B₀,hB,hxB,hvB,hsel,huni,hR⟩ := affected_common_edge hF hvd.safe haff hz.2.2.1
  have hB₀ : B₀ ∈ T := mem_filter.mpr ⟨hB,hvB⟩
  obtain ⟨huncap,_,hcomp,hG,hcancel⟩ := common_rejection hB hxB hvB hx haff hsel hR
    ha haτ hτ4 hτσ hlam0 hs hz.2.2.1 ((hz.2.2.2.2 B₀ hB hvB).1.trans_le hη) hp
  have hn : 0 ≤ N.weight v := by
    change 0 ≤ (advance F τ x false s).weight v
    rw [huncap]
    exact div_nonneg (hs v).1 (by linarith)
  have hbound (B : Finset V) (hBT : B ∈ T) :
      edgeCost N v σ lam L (s.weight v) B - edgeCost s v σ lam L (s.weight v) B ≤
        c*count B - (if B = B₀ then logChange else 0) := by
    obtain ⟨hBF,hvB'⟩ := mem_filter.mp hBT
    by_cases h : B = B₀
    · subst B
      simpa only [count,if_pos hxB,if_true,mul_zero,zero_sub] using
        common_rejection_cost (L := L) (hs v).1 hlam0 (by dsimp [L]; linarith) hG hcancel
    · have hxB' : x ∉ B := fun hh => h (huni B hBF hh hvB')
      obtain ⟨hm,hg⟩ := hz.2.2.2.2 B hBF hvB'
      have hm' : 2*s.weight x*mass s v B/σ ≤ Real.log 2 := by
        apply le_trans _ hscale
        apply div_le_div_of_nonneg_right _ hσ.le
        exact mul_le_mul (by linarith [(hs x).2]) hm.le
          (sum_nonneg fun u _ => (hs u).1) (by positivity)
      obtain ⟨hG',hP'⟩ := mixed_rejection (E := F) hxB' hs hq hσ (hm.le.trans hη) hm'
      simpa only [count,if_neg hxB',if_neg h,sub_zero,c] using
        mixed_rejection_cost hs hτ hσ hσ1 hlam0 hL hg.le hG' hP'
  have hsum := sum_le_sum hbound
  rw [sum_sub_distrib,sum_sub_distrib,← mul_sum] at hsum
  have hcount : ∑ B ∈ T, count B = ((incidences F Q s.selected tail.toFinset v x .centerAndNeighbor).card : ℝ) :=
    affected_incidence_sum hvd haff hsize
  rw [hcount] at hsum
  simp only [sum_ite_eq',if_pos hB₀] at hsum
  have hadd : 0 ≤ localLoss F Q v .twoNeighbors (8*τ^3/σ^2) x tail s := by
    unfold localLoss
    have := (hs x).1
    positivity
  apply from_rejection_cost haff (by linarith) hp hn hcomp
  exact hsum.trans (sub_le_sub_right (le_add_of_nonneg_left hadd) logChange)

/-- Fixed-order terminal bound with both one-step cases discharged. -/
theorem fixed_order {E : Finset (Finset V)} (hE : Linear E) {Q : Finset V} {v : V}
    {a τ σ η lam : ℝ} (ha : 0 < a) (haτ : a < τ) (hτ4 : τ ≤ 1/4)
    (hτσ : τ ≤ σ) (hσ1 : σ ≤ 1) (hη : η ≤ 1/8)
    (hscale : 2*τ*η/σ ≤ Real.log 2) (hL : 1 ≤ Real.log (τ/a))
    (hlam : lam = Real.exp (-(η/(2*σ)))) (xs : List V) (hxs : xs.Nodup) (hQ : xs.toFinset = Q) :
    potential true (retainedEdges E Q) (initial Q a) v a τ σ lam ≤
      (process (retainedEdges E Q) τ).joint xs (initial Q a) {v} +
      (8*τ^6/σ^2 * ((eligible E Q v .twoNeighbors).card : ℝ) +
       16*τ^5/σ * ((eligible E Q v .centerAndNeighbor).card : ℝ)) :=
  fixed_order_of_affected hE ha haτ hτ4 hτσ hσ1 hscale hL hlam xs hxs hQ
    (localBound_true hE Q v ha haτ hτ4 hτσ hσ1 hη hscale hL hlam)

end OMA.GeneralPositionAffected

theorem OMA.GeneralPositionOuter.selection_proof : OMA.R_opg_general_position_subsets_R1.H1 :=
  OMA.GeneralPositionOuter.registered_of_affected (by
    intro E hE Q v a τ σ lam ha haτ hτ4 hτσ hσ1 hscale hL hlam
    exact OMA.GeneralPositionAffected.localBound_true hE Q v ha haτ hτ4 hτσ hσ1
      (show (1/8 : ℝ) ≤ 1/8 from le_rfl) hscale hL hlam)

theorem OMA.solution : OMA.R_opg_general_position_subsets_R1.H1 := by
  exact OMA.GeneralPositionOuter.selection_proof
