import OMAStatements.S_oeis_a223682

/-!
Proof of Barker's two conjectures for OEIS A223682, by an exact transfer-matrix count.

Each line condition (unimodal, nondecreasing) is recognised by a small automaton reading the line
from its first to its last entry. Adding a bottom row to an array extends every column, the
diagonals and antidiagonals ending in that row, and finalises nothing else, so the states of
the lines meeting the bottom row form a finite summary that is updated row by row. The number of
ways to complete a summary to an array with t more rows satisfies a linear recursion over the
294 reachable summaries; the kernel checks the explicit successor table, the count tables up
to t = 11, and the order-9 recurrence for every summary at t = 2, which then propagates
to all t by linearity. The generating function follows from the recurrence and the initial terms.
-/

namespace OMA.S_oeis_a223682

open PowerSeries Finset

abbrev Q : ℕ := 2
abbrev K : ℕ := 4
abbrev κr : ℕ := 0
abbrev κc : ℕ := 1
abbrev κd : ℕ := 0
abbrev κa : ℕ := 1

/-! ## Line automata -/

abbrev LS := Option (Fin Q × Bool)

/-- Kinds: 1 unimodal, 2 nondecreasing, anything else no condition. -/
def δ (κ : ℕ) (s : LS) (b : Fin Q) : Option LS :=
  match κ, s with
  | 1, none => some (some (b, false))
  | 1, some (h, false) => some (some (b, decide (b < h)))
  | 1, some (h, true) => if b ≤ h then some (some (b, true)) else none
  | 2, none => some (some (b, false))
  | 2, some (h, _) => if h ≤ b then some (some (b, false)) else none
  | _, _ => some none

def lrun (κ : ℕ) (l : List (Fin Q)) : Option LS :=
  l.foldl (fun o b => o.bind fun s => δ κ s b) (some none)

def LP (κ : ℕ) (l : List (Fin Q)) : Prop :=
  match κ with
  | 1 => Unimodal l
  | 2 => l.IsChain (· ≤ ·)
  | _ => True

theorem lrun_append (κ : ℕ) (l : List (Fin Q)) (b : Fin Q) :
    lrun κ (l ++ [b]) = (lrun κ l).bind fun s => δ κ s b := by
  simp [lrun, List.foldl_append]

theorem nd_append (l : List (Fin Q)) (b : Fin Q) :
    (l ++ [b]).IsChain (· ≤ ·) ↔ l.IsChain (· ≤ ·) ∧ ∀ h ∈ l.getLast?, h ≤ b := by
  rw [List.isChain_append]
  simp

theorem ni_append (l : List (Fin Q)) (b : Fin Q) :
    (l ++ [b]).IsChain (· ≥ ·) ↔ l.IsChain (· ≥ ·) ∧ ∀ h ∈ l.getLast?, b ≤ h := by
  rw [List.isChain_append]
  simp

theorem unimodal_iff (l : List (Fin Q)) :
    Unimodal l ↔ ∃ m ≤ l.length, (l.take m).IsChain (· ≤ ·) ∧ (l.drop m).IsChain (· ≥ ·) := by
  constructor
  · rintro ⟨m, h⟩
    exact ⟨m, by omega, h⟩
  · rintro ⟨m, hm, h⟩
    exact ⟨⟨m, by omega⟩, h⟩

theorem getLast?_drop' (l : List (Fin Q)) (m : ℕ) (hm : m < l.length) :
    (l.drop m).getLast? = l.getLast? := by
  rw [List.getLast?_drop]
  simp [show ¬ l.length ≤ m by omega]

theorem unimodal_append (l : List (Fin Q)) (b : Fin Q) :
    Unimodal (l ++ [b]) ↔ Unimodal l ∧ (l.IsChain (· ≤ ·) ∨ ∀ h ∈ l.getLast?, b ≤ h) := by
  rw [unimodal_iff, unimodal_iff]
  constructor
  · rintro ⟨m, hm, h1, h2⟩
    simp only [List.length_append, List.length_singleton] at hm
    rcases Nat.lt_or_ge l.length m with hlt | hle
    · have hm' : m = l.length + 1 := by omega
      subst hm'
      rw [List.take_of_length_le (by simp)] at h1
      have hl := ((nd_append l b).1 h1).1
      refine ⟨⟨l.length, le_rfl, by rw [List.take_of_length_le le_rfl]; exact hl, by simp⟩, Or.inl hl⟩
    · rw [List.take_append_of_le_length hle] at h1
      rw [List.drop_append_of_le_length hle] at h2
      have h2' := (ni_append _ b).1 h2
      refine ⟨⟨m, hle, h1, h2'.1⟩, ?_⟩
      rcases Nat.lt_or_ge m l.length with hlt2 | hge
      · right
        rw [← getLast?_drop' l m hlt2]
        exact h2'.2
      · left
        rw [List.take_of_length_le hge] at h1
        exact h1
  · rintro ⟨⟨m, hm, h1, h2⟩, hor⟩
    rcases hor with hnd | hb
    · refine ⟨l.length, by simp, ?_, ?_⟩
      · rw [List.take_append_of_le_length le_rfl, List.take_of_length_le le_rfl]
        exact hnd
      · rw [List.drop_append_of_le_length le_rfl]
        simp
    · refine ⟨m, by simp; omega, ?_, ?_⟩
      · rw [List.take_append_of_le_length hm]
        exact h1
      · rw [List.drop_append_of_le_length hm]
        refine (ni_append _ b).2 ⟨h2, ?_⟩
        intro h hh
        rcases Nat.lt_or_ge m l.length with hlt2 | hge
        · rw [getLast?_drop' l m hlt2] at hh
          exact hb h hh
        · simp [List.drop_of_length_le hge] at hh

theorem gl (l : List (Fin Q)) (h : Fin Q) : (l ++ [h]).getLast? = some h := by simp

theorem lrun1 (l : List (Fin Q)) :
    lrun 1 l = if Unimodal l then some (l.getLast?.map fun h => (h, !decide (l.IsChain (· ≤ ·)))) else none := by
  induction l using List.reverseRecOn with
  | nil => simp [lrun, Unimodal]
  | append_singleton l b ih =>
    rw [lrun_append, ih]
    by_cases hu : Unimodal l
    · rw [if_pos hu]
      simp only [Option.bind_some]
      rcases List.eq_nil_or_concat' l with hl | ⟨l', h, rfl⟩
      · subst hl
        simp [δ, Unimodal]
      · simp only [gl, Option.map_some]
        by_cases hnd : (l' ++ [h]).IsChain (· ≤ ·)
        · have hu2 : Unimodal (l' ++ [h] ++ [b]) := (unimodal_append _ b).2 ⟨hu, Or.inl hnd⟩
          rw [if_pos hu2]
          simp only [decide_eq_true hnd, Bool.not_true, δ, gl, Option.map_some]
          congr 3
          have e : (l' ++ [h] ++ [b]).IsChain (· ≤ ·) ↔ h ≤ b := by rw [nd_append]; simp [hnd]
          by_cases hhb : h ≤ b
          · simp [e.2 hhb, not_lt.2 hhb, hnd, hhb]
          · simp [mt e.1 hhb, lt_of_not_ge hhb]
        · have hnd2 : ¬ (l' ++ [h] ++ [b]).IsChain (· ≤ ·) := fun h2 => hnd ((nd_append _ b).1 h2).1
          simp only [decide_eq_false hnd, Bool.not_false, δ, decide_eq_false hnd2, gl, Option.map_some, Bool.not_false]
          by_cases hb : b ≤ h
          · rw [if_pos hb, if_pos ((unimodal_append _ b).2 ⟨hu, Or.inr (by simpa using hb)⟩)]
          · rw [if_neg hb, if_neg]
            intro h2
            rcases ((unimodal_append _ b).1 h2).2 with h3 | h3
            · exact hnd h3
            · exact hb (by simpa using h3)
    · rw [if_neg hu, if_neg (fun h2 => hu ((unimodal_append l b).1 h2).1)]
      rfl

theorem lrun2 (l : List (Fin Q)) :
    lrun 2 l = if l.IsChain (· ≤ ·) then some (l.getLast?.map fun h => (h, false)) else none := by
  induction l using List.reverseRecOn with
  | nil => simp [lrun]
  | append_singleton l b ih =>
    rw [lrun_append, ih]
    by_cases hu : l.IsChain (· ≤ ·)
    · rw [if_pos hu]
      simp only [Option.bind_some]
      rcases List.eq_nil_or_concat' l with hl | ⟨l', h, rfl⟩
      · subst hl
        simp [δ]
      · simp only [gl, Option.map_some, δ]
        by_cases hb : h ≤ b
        · rw [if_pos hb, if_pos ((nd_append _ b).2 ⟨hu, by simpa using hb⟩)]
        · rw [if_neg hb, if_neg]
          intro h2
          exact hb (by simpa using ((nd_append _ b).1 h2).2)
    · rw [if_neg hu, if_neg (fun h2 => hu ((nd_append l b).1 h2).1)]
      rfl

theorem lrun0 (κ : ℕ) (hκ : κ ≠ 1 ∧ κ ≠ 2) (l : List (Fin Q)) : lrun κ l = some none := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l b ih =>
    rw [lrun_append, ih]
    simp only [Option.bind_some]
    rcases hκ with ⟨h1, h2⟩
    unfold δ
    split <;> simp_all

theorem alive_iff (κ : ℕ) (l : List (Fin Q)) : (lrun κ l).isSome ↔ LP κ l := by
  by_cases h1 : κ = 1
  · subst h1; rw [lrun1]; split_ifs with h <;> simp [LP, h]
  by_cases h2 : κ = 2
  · subst h2; rw [lrun2]; split_ifs with h <;> simp [LP, h]
  rw [lrun0 κ ⟨h1, h2⟩]
  unfold LP
  split <;> simp_all



/-! ## Arrays built row by row -/

abbrev Row := Fin K → Fin Q
abbrev St := (Fin K → LS) × (Fin K → LS) × (Fin K → LS)

def colE {t : ℕ} (y : Fin t → Row) (j : Fin K) : List (Fin Q) := List.ofFn fun i => y i j

def dgE {t : ℕ} (y : Fin t → Row) (c : ℤ) : List (Fin Q) :=
  (List.finRange t).filterMap fun i : Fin t =>
    if h : 0 ≤ (i : ℤ) - c ∧ (i : ℤ) - c < K then some (y i ⟨((i : ℤ) - c).toNat, by omega⟩) else none

def adE {t : ℕ} (y : Fin t → Row) (c : ℤ) : List (Fin Q) :=
  (List.finRange t).filterMap fun i : Fin t =>
    if h : 0 ≤ c - (i : ℤ) ∧ c - (i : ℤ) < K then some (y i ⟨(c - (i : ℤ)).toNat, by omega⟩) else none

def rowOK (r : Row) : Bool := (lrun κr (List.ofFn r)).isSome

def G {t : ℕ} (y : Fin t → Row) : Prop :=
  (∀ i, rowOK (y i) = true) ∧ (∀ j, (lrun κc (colE y j)).isSome = true) ∧
    (∀ c, (lrun κd (dgE y c)).isSome = true) ∧ (∀ c, (lrun κa (adE y c)).isSome = true)

noncomputable instance {t : ℕ} : DecidablePred (@G t) := fun _ => Classical.dec _

def Sm {t : ℕ} (y : Fin t → Row) : St :=
  (fun j => (lrun κc (colE y j)).getD none,
   fun p => (lrun κd (dgE y ((t : ℤ) - 1 - (p : ℕ)))).getD none,
   fun p => (lrun κa (adE y ((t : ℤ) - 1 + (p : ℕ)))).getD none)

def optPi (f : Fin K → Option LS) : Option (Fin K → LS) :=
  if ∀ j, (f j).isSome = true then some (fun j => (f j).getD none) else none

def prevD (s : Fin K → LS) (p : Fin K) : LS := if h : (p : ℕ) = 0 then none else s ⟨(p : ℕ) - 1, by omega⟩

def prevA (s : Fin K → LS) (p : Fin K) : LS := if h : (p : ℕ) + 1 < K then s ⟨(p : ℕ) + 1, h⟩ else none

def step (s : St) (r : Row) : Option St :=
  if rowOK r = true then
    match optPi (fun j => δ κc (s.1 j) (r j)), optPi (fun p => δ κd (prevD s.2.1 p) (r p)),
      optPi (fun p => δ κa (prevA s.2.2 p) (r p)) with
    | some u, some v, some w => some (u, v, w)
    | _, _, _ => none
  else none

def init : St := (fun _ => none, fun _ => none, fun _ => none)

def RunO (o : Option St) (l : List Row) : Option St := l.foldl (fun o r => o.bind fun s => step s r) o

theorem RunO_none (l : List Row) : RunO none l = none := by
  induction l with
  | nil => rfl
  | cons r l ih => exact ih

theorem lrun_gen (κ : ℕ) (l m : List (Fin Q)) :
    lrun κ (l ++ m) = m.foldl (fun o b => o.bind fun s => δ κ s b) (lrun κ l) := by
  simp [lrun, List.foldl_append]

theorem foldl_none (κ : ℕ) (m : List (Fin Q)) :
    m.foldl (fun o b => o.bind fun s => δ κ s b) (none : Option LS) = none := by
  induction m with
  | nil => rfl
  | cons r l ih => exact ih

theorem alive_prefix (κ : ℕ) (l m : List (Fin Q)) (h : (lrun κ (l ++ m)).isSome = true) :
    (lrun κ l).isSome = true := by
  rw [lrun_gen] at h
  cases hl : lrun κ l with
  | none => rw [hl, foldl_none] at h; exact absurd h (by simp)
  | some s => rfl

theorem colE_snoc {t : ℕ} (y : Fin t → Row) (r : Row) (j : Fin K) :
    colE (Fin.snoc y r : Fin (t + 1) → Row) j = colE y j ++ [r j] := by
  unfold colE
  rw [List.ofFn_succ_last]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem dgE_snoc {t : ℕ} (y : Fin t → Row) (r : Row) (c : ℤ) :
    dgE (Fin.snoc y r : Fin (t + 1) → Row) c = dgE y c ++
      (if h : 0 ≤ (t : ℤ) - c ∧ (t : ℤ) - c < K then [r ⟨((t : ℤ) - c).toNat, by omega⟩] else []) := by
  unfold dgE
  rw [List.finRange_succ_last, List.filterMap_append, List.filterMap_map]
  congr 1
  · apply List.filterMap_congr
    intro i _
    simp only [Function.comp, Fin.coe_castSucc, Fin.snoc_castSucc]
  · simp only [List.filterMap_cons, List.filterMap_nil, Fin.val_last, Fin.snoc_last]
    split_ifs <;> rfl

theorem adE_snoc {t : ℕ} (y : Fin t → Row) (r : Row) (c : ℤ) :
    adE (Fin.snoc y r : Fin (t + 1) → Row) c = adE y c ++
      (if h : 0 ≤ c - (t : ℤ) ∧ c - (t : ℤ) < K then [r ⟨(c - (t : ℤ)).toNat, by omega⟩] else []) := by
  unfold adE
  rw [List.finRange_succ_last, List.filterMap_append, List.filterMap_map]
  congr 1
  · apply List.filterMap_congr
    intro i _
    simp only [Function.comp, Fin.coe_castSucc, Fin.snoc_castSucc]
  · simp only [List.filterMap_cons, List.filterMap_nil, Fin.val_last, Fin.snoc_last]
    split_ifs <;> rfl

theorem dgE_ge {t : ℕ} (y : Fin t → Row) (c : ℤ) (hc : (t : ℤ) ≤ c) : dgE y c = [] := by
  unfold dgE
  rw [List.filterMap_eq_nil_iff]
  intro i _
  rw [dif_neg]
  have := i.isLt
  omega

theorem adE_ge {t : ℕ} (y : Fin t → Row) (c : ℤ) (hc : (t : ℤ) - 1 + K ≤ c) : adE y c = [] := by
  unfold adE
  rw [List.filterMap_eq_nil_iff]
  intro i _
  rw [dif_neg]
  have := i.isLt
  omega

theorem dgE_at {t : ℕ} (y : Fin t → Row) (r : Row) (p : Fin K) :
    dgE (Fin.snoc y r : Fin (t + 1) → Row) ((t : ℤ) - (p : ℕ)) = dgE y ((t : ℤ) - (p : ℕ)) ++ [r p] := by
  rw [dgE_snoc, dif_pos (by have := p.isLt; omega)]
  congr 3
  ext
  simp

theorem adE_at {t : ℕ} (y : Fin t → Row) (r : Row) (p : Fin K) :
    adE (Fin.snoc y r : Fin (t + 1) → Row) ((t : ℤ) + (p : ℕ)) = adE y ((t : ℤ) + (p : ℕ)) ++ [r p] := by
  rw [adE_snoc, dif_pos (by have := p.isLt; omega)]
  congr 3
  ext
  simp

theorem getD_of_isSome {s : Option LS} (h : s.isSome = true) : s = some (s.getD none) := by
  cases s with
  | none => simp at h
  | some v => rfl

/-- Under G y, the previous diagonal state of position p of a new bottom row. -/
theorem hD {t : ℕ} (y : Fin t → Row) (hy : G y) (p : Fin K) :
    lrun κd (dgE y ((t : ℤ) - (p : ℕ))) = some (prevD (Sm y).2.1 p) := by
  unfold prevD
  split_ifs with h0
  · rw [dgE_ge y _ (by omega)]; rfl
  · have e : (t : ℤ) - (p : ℕ) = (t : ℤ) - 1 - ((⟨(p : ℕ) - 1, by omega⟩ : Fin K) : ℕ) := by
      simp only; omega
    rw [e]
    exact getD_of_isSome (hy.2.2.1 _)

theorem hA {t : ℕ} (y : Fin t → Row) (hy : G y) (p : Fin K) :
    lrun κa (adE y ((t : ℤ) + (p : ℕ))) = some (prevA (Sm y).2.2 p) := by
  unfold prevA
  split_ifs with h0
  · have e : (t : ℤ) + (p : ℕ) = (t : ℤ) - 1 + ((⟨(p : ℕ) + 1, h0⟩ : Fin K) : ℕ) := by
      simp only; omega
    rw [e]
    exact getD_of_isSome (hy.2.2.2 _)
  · rw [adE_ge y _ (by omega)]; rfl

theorem hC {t : ℕ} (y : Fin t → Row) (hy : G y) (j : Fin K) :
    lrun κc (colE y j) = some ((Sm y).1 j) := getD_of_isSome (hy.2.1 j)

theorem G_snoc_imp {t : ℕ} (y : Fin t → Row) (r : Row) (h : G (Fin.snoc y r : Fin (t + 1) → Row)) : G y := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun i => ?_, fun j => ?_, fun c => ?_, fun c => ?_⟩
  · have := h1 i.castSucc; rwa [Fin.snoc_castSucc] at this
  · have := h2 j; rw [colE_snoc] at this; exact alive_prefix _ _ _ this
  · have := h3 c; rw [dgE_snoc] at this; exact alive_prefix _ _ _ this
  · have := h4 c; rw [adE_snoc] at this; exact alive_prefix _ _ _ this

theorem optPi_eq (f : Fin K → Option LS) :
    optPi f = if ∀ j, (f j).isSome = true then some (fun j => (f j).getD none) else none := rfl

theorem G_snoc_iff {t : ℕ} (y : Fin t → Row) (r : Row) (hy : G y) :
    G (Fin.snoc y r : Fin (t + 1) → Row) ↔ rowOK r = true ∧
      (∀ j, (δ κc ((Sm y).1 j) (r j)).isSome = true) ∧
      (∀ p, (δ κd (prevD (Sm y).2.1 p) (r p)).isSome = true) ∧
      (∀ p, (δ κa (prevA (Sm y).2.2 p) (r p)).isSome = true) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, fun j => ?_, fun p => ?_, fun p => ?_⟩
    · have := h1 (Fin.last t); rwa [Fin.snoc_last] at this
    · have := h2 j; rwa [colE_snoc, lrun_append, hC y hy] at this
    · have := h3 ((t : ℤ) - (p : ℕ)); rwa [dgE_at, lrun_append, hD y hy] at this
    · have := h4 ((t : ℤ) + (p : ℕ)); rwa [adE_at, lrun_append, hA y hy] at this
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun i => ?_, fun j => ?_, fun c => ?_, fun c => ?_⟩
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [Fin.snoc_last]; exact h1
      · rw [Fin.snoc_castSucc]; exact hy.1 i
    · rw [colE_snoc, lrun_append, hC y hy]; exact h2 j
    · by_cases hc : 0 ≤ (t : ℤ) - c ∧ (t : ℤ) - c < K
      · obtain ⟨p, rfl⟩ : ∃ p : Fin K, c = (t : ℤ) - (p : ℕ) := ⟨⟨((t : ℤ) - c).toNat, by omega⟩, by simp only; omega⟩
        rw [dgE_at, lrun_append, hD y hy]; exact h3 p
      · rw [dgE_snoc, dif_neg hc, List.append_nil]; exact hy.2.2.1 c
    · by_cases hc : 0 ≤ c - (t : ℤ) ∧ c - (t : ℤ) < K
      · obtain ⟨p, rfl⟩ : ∃ p : Fin K, c = (t : ℤ) + (p : ℕ) := ⟨⟨(c - (t : ℤ)).toNat, by omega⟩, by simp only; omega⟩
        rw [adE_at, lrun_append, hA y hy]; exact h4 p
      · rw [adE_snoc, dif_neg hc, List.append_nil]; exact hy.2.2.2 c

theorem Sm_snoc {t : ℕ} (y : Fin t → Row) (r : Row) (hy : G y) :
    Sm (Fin.snoc y r : Fin (t + 1) → Row) =
      (fun j => (δ κc ((Sm y).1 j) (r j)).getD none,
       fun p => (δ κd (prevD (Sm y).2.1 p) (r p)).getD none,
       fun p => (δ κa (prevA (Sm y).2.2 p) (r p)).getD none) := by
  have e1 : ∀ p : Fin K, ((t + 1 : ℕ) : ℤ) - 1 - (p : ℕ) = (t : ℤ) - (p : ℕ) := fun p => by push_cast; ring
  have e2 : ∀ p : Fin K, ((t + 1 : ℕ) : ℤ) - 1 + (p : ℕ) = (t : ℤ) + (p : ℕ) := fun p => by push_cast; ring
  unfold Sm
  simp only [e1, e2]
  refine Prod.ext (funext fun j => ?_) (Prod.ext (funext fun p => ?_) (funext fun p => ?_))
  · simp only; rw [colE_snoc, lrun_append, hC y hy]; rfl
  · simp only; rw [dgE_at, lrun_append, hD y hy]; rfl
  · simp only; rw [adE_at, lrun_append, hA y hy]; rfl

theorem step_spec {t : ℕ} (y : Fin t → Row) (r : Row) (hy : G y) :
    step (Sm y) r = if G (Fin.snoc y r : Fin (t + 1) → Row) then some (Sm (Fin.snoc y r : Fin (t + 1) → Row)) else none := by
  rw [Sm_snoc y r hy]
  by_cases hg : G (Fin.snoc y r : Fin (t + 1) → Row)
  · rw [if_pos hg]
    obtain ⟨h1, h2, h3, h4⟩ := (G_snoc_iff y r hy).1 hg
    unfold step
    rw [if_pos h1, optPi_eq, optPi_eq, optPi_eq, if_pos h2, if_pos h3, if_pos h4]
  · rw [if_neg hg]
    unfold step
    split_ifs with h1
    · rw [optPi_eq, optPi_eq, optPi_eq]
      split_ifs with h2 h3 h4 <;> first | rfl | exact absurd ((G_snoc_iff y r hy).2 ⟨h1, h2, h3, h4⟩) hg
    · rfl

theorem ofFn_snoc {t : ℕ} (y : Fin t → Row) (r : Row) :
    List.ofFn (Fin.snoc y r : Fin (t + 1) → Row) = List.ofFn y ++ [r] := by
  rw [List.ofFn_succ_last]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem INV : ∀ (t : ℕ) (y : Fin t → Row), RunO (some init) (List.ofFn y) = if G y then some (Sm y) else none := by
  intro t
  induction t with
  | zero =>
    intro y
    have hg : G y := ⟨fun i => i.elim0, fun j => by simp [colE, lrun], fun c => by simp [dgE, lrun],
      fun c => by simp [adE, lrun]⟩
    rw [if_pos hg]
    have : Sm y = init := by
      unfold Sm init
      simp [colE, dgE, adE, lrun]
    rw [this]
    rfl
  | succ t ih =>
    intro y
    obtain ⟨y', r, rfl⟩ : ∃ (y' : Fin t → Row) (r : Row), y = (Fin.snoc y' r : Fin (t + 1) → Row) :=
      ⟨Fin.init y, y (Fin.last t), (Fin.snoc_init_self y).symm⟩
    rw [ofFn_snoc]
    unfold RunO
    rw [List.foldl_append]
    change ((RunO (some init) (List.ofFn y')).bind fun s => step s r) = _
    rw [ih y']
    by_cases hy : G y'
    · rw [if_pos hy, Option.bind_some, step_spec y' r hy]
    · rw [if_neg hy, if_neg (fun h => hy (G_snoc_imp y' r h))]
      rfl

/-! ## Counting continuations -/

def E (t : ℕ) (s : St) : ℕ := (univ.filter fun z : Fin t → Row => (RunO (some s) (List.ofFn z)).isSome = true).card

theorem E_zero (s : St) : E 0 s = 1 := by
  unfold E
  rw [Finset.filter_true_of_mem (fun z _ => by simp [RunO])]
  simp

theorem E_succ (t : ℕ) (s : St) :
    E (t + 1) s = ∑ r : Row, (match step s r with | none => 0 | some s' => E t s') := by
  unfold E
  rw [Finset.card_filter]
  rw [← (Fin.consEquiv fun _ => Row).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  simp only [show ∀ y : Fin t → Row, (Fin.consEquiv (fun _ => Row)) (r, y) = Fin.cons r y from fun _ => rfl,
    List.ofFn_cons]
  have hR : ∀ l : List Row, RunO (some s) (r :: l) = RunO (step s r) l := fun l => by
    simp [RunO, List.foldl_cons]
  simp only [hR]
  cases step s r with
  | none => simp [RunO_none]
  | some s' => exact (Finset.card_filter _ _).symm

theorem a_eq_E (n : ℕ) : (univ.filter fun y : Fin n → Row => G y).card = E n init := by
  unfold E
  refine congrArg Finset.card (Finset.filter_congr (fun y _ => ?_))
  rw [INV]
  split_ifs with h <;> simp [h]


theorem dg_cells {n : ℕ} (x : Fin n → Row) (P : List (Fin Q) → Prop) (h0 : P []) :
    (∀ c, P (dgE x c)) ↔ ∀ (i : Fin n) (j : Fin K), P (dgE x ((i : ℤ) - (j : ℕ))) := by
  refine ⟨fun h i j => h _, fun h c => ?_⟩
  by_cases hc : ∃ (i : Fin n) (j : Fin K), c = (i : ℤ) - (j : ℕ)
  · obtain ⟨i, j, rfl⟩ := hc; exact h i j
  · convert h0
    unfold dgE
    rw [List.filterMap_eq_nil_iff]
    intro i _
    rw [dif_neg]
    rintro ⟨h1, h2⟩
    exact hc ⟨i, ⟨((i : ℤ) - c).toNat, by omega⟩, by simp only; omega⟩

theorem ad_cells {n : ℕ} (x : Fin n → Row) (P : List (Fin Q) → Prop) (h0 : P []) :
    (∀ c, P (adE x c)) ↔ ∀ (i : Fin n) (j : Fin K), P (adE x ((i : ℤ) + (j : ℕ))) := by
  refine ⟨fun h i j => h _, fun h c => ?_⟩
  by_cases hc : ∃ (i : Fin n) (j : Fin K), c = (i : ℤ) + (j : ℕ)
  · obtain ⟨i, j, rfl⟩ := hc; exact h i j
  · convert h0
    unfold adE
    rw [List.filterMap_eq_nil_iff]
    intro i _
    rw [dif_neg]
    rintro ⟨h1, h2⟩
    exact hc ⟨i, ⟨(c - (i : ℤ)).toNat, by omega⟩, by simp only; omega⟩

theorem ad_cellsT {n : ℕ} (y : Fin n → Row) (P : List (Fin Q) → Prop) (h0 : P []) :
    (∀ c, P (adE y c)) ↔ ∀ (i : Fin K) (j : Fin n), P (adE y ((i : ℕ) + (j : ℤ))) := by
  rw [ad_cells y P h0]
  constructor
  · intro h i j; have := h j i; rwa [add_comm] at this
  · intro h i j; have := h j i; rwa [add_comm] at this

theorem LP_nil (κ : ℕ) : LP κ [] := by
  unfold LP
  split
  · exact ⟨0, by simp, by simp⟩
  · simp
  · trivial

theorem LP1 (l : List (Fin Q)) : LP 1 l ↔ Unimodal l := Iff.rfl
theorem LP2 (l : List (Fin Q)) : LP 2 l ↔ l.IsChain (· ≤ ·) := Iff.rfl
theorem LP0 (l : List (Fin Q)) : LP 0 l ↔ True := Iff.rfl

theorem good_iff {n : ℕ} (x : Fin K → Fin n → Fin Q) : good x ↔ G (fun j i => x i j) := by
  unfold good G rowOK
  simp only [alive_iff, κr, κc, κd, κa]
  rw [ad_cellsT _ _ (LP_nil _)]
  simp only [LP0, LP1, LP2, colE]
  simp only [show ∀ c, adE (fun j i => x i j) c = antidiag x c from fun _ => rfl]
  all_goals simp

theorem card_bridge (n : ℕ) : a n = (univ.filter fun y : Fin n → Row => G y).card := by
  unfold a
  refine Finset.card_bij (fun x _ => fun j i => x i j) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact (good_iff x).1 hx
  · intro x _ x' _ h
    funext i j
    exact congrFun (congrFun h j) i
  · intro y hy
    refine ⟨fun i j => y j i, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact (good_iff _).2 hy

/-! ## The explicit automaton, checked by the kernel -/

def lsD (v : ℕ) : LS :=
  if v = 0 then none else some (⟨(v - 1) / 2 % Q, Nat.mod_lt _ (by decide)⟩, decide ((v - 1) % 2 = 1))

def decS (code : ℕ) : St :=
  (fun j => lsD (code / (2 * Q + 1) ^ (j : ℕ) % (2 * Q + 1)),
   fun p => lsD (code / (2 * Q + 1) ^ (K + (p : ℕ)) % (2 * Q + 1)),
   fun p => lsD (code / (2 * Q + 1) ^ (2 * K + (p : ℕ)) % (2 * Q + 1)))

abbrev M : ℕ := 294
abbrev NR : ℕ := Q ^ K

/-- Codes of the reachable states, 28 bits each. -/
instance decFK : DecidableEq (Fin K → LS) := inferInstance
instance decSt : DecidableEq St := instDecidableEqProd

def RS : ℕ := 0x3a1d6543a1d6533a1d64f3adc2123a1d64e3a1d63b3a1d63a3dd710a3a1d6363adc1fe3e95ccd3dd71093adc1f93a1d635a2cbaac45a9c75a2cbaab45a9c743c5997c3c5997b3a7cc353adc2173a7cc343a7cc303a7cc2f3a7cc1c3a7cc1b4d1d23b3e366eb3a7cc174d1d23a3e366ea3a7cc16a08f784436d94da08f783436d94c973f48b3a1d5d7973f48a3a1d5d6a08f77f436d948973f4863a1d5d2a14e342a08f77e442c50b436d94797fe049973f4853adc1953a1d5d13c599953c59994a26c4d0454a699a26c4cf454a6983bfa3b93bfa3b83bfa3a03bfa39fa2cbab145a9c7aa32b093a2cbab0460925c45a9c79a26c4cb454a694a32b08ea26c4ca4609257454a6933e367043c5999a3e367033cb8f7c3c599993dd71233bfa3b43e95ce63dd71223cb8f773bfa3b33c599813cb8f633c599803bfa39b3cb8f5e3bfa39aa2cbac54ef9fa045a9c8ea2cbac44ef9f9f45a9c8da0eed6543ccf2ea14e347a0eed64442c51043ccf2da0eed6043ccf29a0eed5f43ccf28ac1bdd7997b7cc4ef9f233c59918ac1bdd6997b7cb4ef9f223c59917979ea6c3a7cbb897fe04e979ea6b3adc19a3a7cbb7979ea673a7cbb3979ea663a7cbb2a26c4e94e9a9c4454a6b2a26c4e84e9a9c3454a6b1a08f76b4cbdc5f436d934a08f76a4cbdc5e436d933abbc7fb991c1f04e9a9473bfa33cabbc7fa991c1ef4e9a9463bfa33ba9dfa96973f4724cbdbe23a1d5bea9dfa95973f4714cbdbe13a1d5bda4a8834a2cbaca4ef9fa547869fd45a9c93a4a8833a32b0aca2cbac94f595874ef9fa447869fc460927545a9c92a449253a26c4e44e9a9bf472741c454a6ada507e16a449252a32b0a7a26c4e34f595824e9a9be47e5fdf472741b4609270454a6aca4a881ba0eed4c50d6d0f4d1d24047869e443ccf15a4a881aa14e32ea0eed4b50d6d0e4d7c8224d1d23f47869e3442c4f743ccf14a44923aa08f766507772e4cbdc5a4727403436d92fa507dfda449239a14e329a08f76551362f1507772d4d7c81d4cbdc5947e5fc64727402442c4f2436d92eac1bddc9b5853b997b7d14ef9f283e366873c5991dac7b3beac1bddb9b5853a99dadb3997b7d04f5950a4ef9f273e366863cb8eff3c5991cabbc7f69af8f5a991c1eb4e9a9423dd70a63bfa337ac7b3b9abbc7f59bb7b1d9af8f5999dadae991c1ea4f595054e9a9413e95c693dd70a53cb8efa3bfa336adf8b46aa3f0779b58522979ea5350d6c924d1d1c33e3666e3a7cb9fadf8b45aa9e659aa3f0769b5852197fe035979ea5250d6c914d7c7a54d1d1c23e3666d3adc1813a7cb9ead99565a9dfa919af8f41973f46d50776b14cbdbdd3dd708d3a1d5b9ae58128ad99564aa9e654a9dfa909bb7b049af8f4097fe030973f46c513627450776b04d7c7a04cbdbdc3e95c503dd708c3adc17c3a1d5b80000000

/-- Successor table: entry i * NR + c is 0 (dead) or 1 + the index of the successor, 9 bits each. -/
def TRT : ℕ := 0x1260000000000000000000000000000000223250000000000000000000000000000035801240000000000000000000000000006a35a47240000000000000000000000000006a34e47220000000000000000000000000a100000012100000000000000000000000cc9e000023b20000000000000000000001b8006d00428010d0000000000000000000017c005e0047c011e00000000000000000000000cca1000023b210000000000000000002b9b8cc6d8e42a3b0d0000000000000000002b99ccc658e41e3b0c0000000000000000002b97caa5e8e47e351e0000000000000000002b958aa548e46e35190000000ba0000001180000000c90000001170000000000000000000000000c90000001140000000b60000001160000000c60000001150000000000000000000000000c6000000113000000000000000000001b8010b0042801090000000000000000000019c01080041c01060000000000000000000000000000000001260000000000000000000000000000000223260000000000000000000000000000000223250000000000000000000000000000035801240000000000000000000000000006a34e47220000000000000000000000000a100000012100000000000000000000000cc9e000023b200000000000000000000017c007d0035800d5000000000000000000001b8006d00428010d0000000000000000000017c005e0047c011e0000000000000000002b958ec756a34da4d10000000000000000002b99ccc658e41e3b0c0000000000000000002b958aa548e46e35190000000000000000a80000000000000000a60000000000000000000000000000000000eb000000000000010ca50000000000000102a300000000000000000000000000000001b0ea0000000000000001050000000000000001040000000000000001010000000000000001000000000000000185030000000000000181020000000000000160ff000000000000015cfe00000000000000007e00000000000000007b0000000000000000000000000000000000d5000000000001fc00fd000000000001f000fc000000000000f800fb000000000000ec00fa00000000000000f07e00000000000000e47b00000000000000f07700000000000000e47100000000000000000000000000000001a4d500000000000000000000000000000001a4d10000000003d1fdf2fd0000000003a1f1eefc0000000003d1e5f2f80000000003a1cdeef60000000001b8f9eafb000000000188ede6fa0000000001b8d9eaf4000000000188c1e6f20000000000000000000000000000036c010f00000000000000000000000000000364010e00000004f0000000e700000008a0000000e600000000000000000000000008a0000000d00000000480000000e40000000830000000e20000000000000000000000000830000000ce00000000000000000000000000000000011200000000000000000000000000000000011000000000000000000000000006d00000010d00000000000000000000000006500000010c00000004f0000000e700000008a0000000e600000000000000000000000008a0000000d000000004f0000000e700000008a0000000e60000000480000000e40000000830000000e200000000000000000000000008a0000000d00000000000000000000000000830000000ce0000000ba0000001180000000c90000001170000000000000000000000000c90000001140000000ba0000001180000000c90000001170000000b60000001160000000c60000001150000000000000000000000000c90000001140000000000000000000000000c60000001130000000000000000000000000000036c01120000000000000000000000000000000001120000000000000000000000000006a36623100000000000000000000000000000000001120000000000000000000000000000000001100000000000000000000000000000036c01120000000000000000000000000000036c010f0000000000000000000000000006a36e23120000000000000000000000000006a36623100000000000000000000000000000036c010f00000000000000000000000000000364010e00000000000000000000000006d00000010d00000000000000000000000006d00000010d00000000000000000000000006500000010c000000000000000000001b8010b004280109000000000000000000001b8010b0042801090000000000000000000019c01080041c01060000000000000000ca0000000000000000c8000000000000000000001b800c90036c00f10000000000000000000000000000000000f10000000000000000c70000000000000000c50000000000000000000019c00c60036400f00000000000000000000000000000000000f00000000000000000a80000000000000000a60000000000000000000000000000000000eb000000000000010ca80000000000000102a6000000000000010ca50000000000000102a300000000000000000000000000000001b0eb00000000000000000000000000000001b0ea00000000000000007e00000000000000007b0000000000000000000000000000000000d500000000000000f07700000000000000e47100000000000000000000000000000001a4d1000b400ba0023000ca001b800c90022400c80000000000023000be0000000000022400bd000b400ba0013800b9000a400b80012c00b70000000000013800ac0000000000012c00ab0009400b60021c00c70019c00c60020800c50000000000021c00bc0000000000020800bb0009400b60011c00b50007c00b40010800b30000000000011c00aa0000000000010800a9000000000000000105000000000000000104000000000000000101000000000000000100000000000000018505000000000000018104000000000000018503000000000000018102000000000000016101000000000000015d000000000000000160ff000000000000015cfe000000000001fc00fd000000000001f000fc000000000000f800fb000000000000ec00fa0000000003d1e5f2f80000000003a1cdeef60000000001b8d9eaf4000000000188c1e6f200000000000000008b00000000000000008800000000000000000000000008a0000000da0000000000000000000000000000000000da0000000000000000850000000000000000800000000000000000000000000830000000d70000000000000000000000000000000000d700000009c0000000ef0000000a70000000ee0000000000000000000000000a70000000eb0000000000000000000000000a70000000e900000929800001caed0000108a400001c6ec0000000000000000000000108a400001b0ea0000000000000000000000108a4000019ee800000004f00000008b00000008a0000000880000000000000000c40000000000000000c300000004f00000004d00000004c00000004a0000000000000000b20000000000000000b10000000480000000850000000830000000800000000000000000c10000000000000000bf0000000480000000450000000430000000400000000000000000af0000000000000000ad00000009c0000000a80000000a70000000a60000000940000000a20000000a10000000a000000009c00000009b00000009a000000099000000094000000093000000092000000091000009298000010ca50000108a40000102a300000489000000d29f00000cc9e00000c69d000009298000008c9700000889600000829500000489000000428f000003c8e00000368d00000000000000008b00000000000000008800000000000000008b00000000000000008800000000000000000000000008a0000000da0000000000000000000000000000000000da0000000000000000000000000000000000da000000000000010c8500000000000001028000000000000000008b00000000000000008800000000000000008500000000000000008000000000000000000000000008a0000000da0000000000000000000000000830000000d700000000000000000000000000000001b0d70000000000000000000000000000000000da0000000000000000000000000000000000d700000000000000008b0000000000000000880000000000000000ca0000000000000000c8000000000000000000001b800c90036c00f10000000000000000000000000000000000da0000000000000000000000000000000000f1000000000000010c8b000000000000010288000000000000010c850000000000000102800000000000000000ca0000000000000000c80000000000000000c70000000000000000c5000000000000000000001b800c90036c00f10000000000000000000019c00c60036400f000000000000000000000000000000001b0da00000000000000000000000000000001b0d70000000000000000000000000000000000f10000000000000000000000000000000000f000000004f0000000e700000008a0000000e600000009c0000000ef0000000a70000000ee000000000000000000001b8008a0036c00da0000000000000000000000000a70000000eb00000000000000000000000008a0000000d00000000000000000000000000a70000000e900000924800001cae400001088300001c6e200000929c00001caef0000108a700001c6ee00000929800001caed0000108a400001c6ec0000000000000000002b99d08836a365b0d70000000000000000000000108a700001b0eb0000000000000000000000108a400001b0ea000000000000000000000010883000019ece0000000000000000000000108a7000019ee90000000000000000000000108a4000019ee800000004f0000000e700000008a0000000e600000003f0000000e100000007d0000000e0000000000000000000001b8008a0036c00da0000000000000000000017c007d0035800d500000000000000000000000008a0000000d000000000000000000000000007d0000000cd00000924f00001cae700001088a00001c6e600000924800001cae400001088300001c6e200000723f00001bee100000ec7d00001bae000000723800001bede00000ec7500001badc0000000000000000002b9b9088a6a36db0da0000000000000000002b99d08836a365b0d70000000000000000002b97cec7d6a359a4d50000000000000000002b958ec756a34da4d100000000000000000000001088a000019ed0000000000000000000000010883000019ece00000000000000000000000ec7d0000198cd00000000000000000000000ec750000198cb00000004f00000008b00000008a0000000880000000000023000c40000000000022400c30000000000000000c40000000000000000c300000004f00000004d00000004c00000004a0000000000013800b20000000000012c00b10000000000000000b20000000000000000b100000004f00000008b00000008a0000000880000000480000000850000000830000000800000000003d21d84c10000000003a20980bf0000000000000000c40000000000000000c30000000000000000c10000000000000000bf00000004f00000004d00000004c00000004a0000000480000000450000000430000000400000000001b91d60af000000000189095cad0000000000000000b20000000000000000b10000000000000000af0000000000000000ad000b400ba0023000ca001b800c90022400c80000000000023000c40000000000022400c30000000000023000be0000000000022400bd000b400ba0013800b9000a400b80012c00b70000000000013800b20000000000012c00b10000000000013800ac0000000000012c00ab000b400ba0023000ca001b800c90022400c80009400b60021c00c70019c00c60020800c50000000003d23184c40000000003a22580c30000000003d21d84c10000000003a20980bf0000000000023000be0000000000022400bd0000000000021c00bc0000000000020800bb000b400ba0013800b9000a400b80012c00b70009400b60011c00b50007c00b40010800b30000000001b93960b20000000001892d5cb10000000001b91d60af000000000189095cad0000000000013800ac0000000000012c00ab0000000000011c00aa0000000000010800a9000b4004f00230008b001b8008a00224008800000009c0000000a80000000a70000000a6000b4002c001c0006f001b8006d001b0006b0000000940000000a20000000a10000000a0000b4004f00138004d000a4004c0012c004a00000009c00000009b00000009a000000099000b4002c000ac002a000a400280009c00260000000940000000930000000920000000910889492483d21d0c852b99d08833a209028000000929c000010ca80000108a70000102a6000009298000010ca50000108a40000102a30889448232d9a8d2682b99ccc6529990c66200000489400000d2a200000cca100000c6a000000489000000d29f00000cc9e00000c69d0889492481b91c8c450487c884318908824000000929c000008c9b00000889a000008299000009298000008c970000088960000082950889448230688842200487c3c1d02870361a000004894000004293000003c9200000369100000489000000428f000003c8e00000368d000b4004f00230008b001b8008a00224008800064003f001fc007e0017c007d001f0007b000b4002c001c0006f001b8006d001b0006b0006400180018400600017c005e00174005c000b4004f00138004d000a4004c0012c004a00064003f000f8003d00054003c000ec003a000b4002c000ac002a000a400280009c00260006400180005c00160005400140004c0012088b4924f3d2310c8b2b9b9088a3a22502880889492483d21d0c852b99d08833a209028008864723f3d1fcf07e2b97cec7d3a1f0e47b0884072383d1e4f0772b958ec753a1cce471088b4482c2d9c0d26f2b9b8cc6d299b0c66b0889448232d9a8d2682b99ccc6529990c662088641e182d984b2602b97caa5e29974a25c088401e0e2d968b2582b958aa5429948a250088b4924f1b9388c4d048a4884c1892c824a0889492481b91c8c450487c884318908824008864723f1b8f86a3d04854663c188ec5e3a0884072381b8d86a34048206632188c05e2e088b4482c068ac422a048a43c280289c36260889448230688842200487c3c1d02870361a088641e180685c1616048540e140284c0612088401e0e06830160a048200e06028100602088401e0e06830160a048200e06028100602

def dec (i : ℕ) : St := decS (RS / 2 ^ (28 * i) % 2 ^ 28)
def tr (i c : ℕ) : ℕ := TRT / 2 ^ (9 * (i * NR + c)) % 2 ^ 9
def rowOf (c : ℕ) : Row := fun j => ⟨c / Q ^ (j : ℕ) % Q, Nat.mod_lt _ (by decide)⟩

theorem chk0 : ∀ i < 200, ∀ c < NR, step (dec (0 + i)) (rowOf c) = (if tr (0 + i) c = 0 then none else some (dec (tr (0 + i) c - 1))) ∧
    tr (0 + i) c ≤ M := by
  decide +kernel

theorem chk1 : ∀ i < 94, ∀ c < NR, step (dec (200 + i)) (rowOf c) = (if tr (200 + i) c = 0 then none else some (dec (tr (200 + i) c - 1))) ∧
    tr (200 + i) c ≤ M := by
  decide +kernel

theorem chk : ∀ i < M, ∀ c < NR, step (dec i) (rowOf c) = (if tr i c = 0 then none else some (dec (tr i c - 1))) ∧
    tr i c ≤ M := by
  intro i hi
  have hi' : i < 294 := hi
  by_cases h0 : i < 200
  · have := chk0 (i - 0) (by omega); rwa [show 0 + (i - 0) = i by omega] at this
  have := chk1 (i - 200) (by omega); rwa [show 200 + (i - 200) = i by omega] at this

theorem dec0 : dec 0 = init := by decide +kernel

def sumN : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, g => sumN n g + g n

theorem sumN_eq (n : ℕ) (g : ℕ → ℕ) : sumN n g = ∑ c ∈ Finset.range n, g c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumN, ih, Finset.sum_range_succ]

def nxt (f : ℕ → ℕ) (i : ℕ) : ℕ := sumN NR fun c => if tr i c = 0 then 0 else f (tr i c - 1)

def E' : ℕ → ℕ → ℕ
  | 0, _ => 1
  | t + 1, i => nxt (E' t) i

theorem sum_row (g : Row → ℕ) : ∑ r : Row, g r = ∑ c ∈ Finset.range NR, g (rowOf c) := by
  rw [← Fin.sum_univ_eq_sum_range (fun c => g (rowOf c)) NR]
  rw [← (finFunctionFinEquiv (m := Q) (n := K)).symm.sum_comp g]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  congr 1
  all_goals funext j
  all_goals ext
  all_goals simp [rowOf, finFunctionFinEquiv_symm_apply_val]

theorem E_E' : ∀ t, ∀ i < M, E t (dec i) = E' t i := by
  intro t
  induction t with
  | zero => intro i _; rw [E_zero]; rfl
  | succ t ih =>
    intro i hi
    rw [E_succ, sum_row]
    show _ = sumN NR _
    rw [sumN_eq]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    obtain ⟨h1, h2⟩ := chk i hi c (Finset.mem_range.1 hc)
    rw [h1]
    split_ifs with h0
    · rfl
    · exact ih _ (by omega)

theorem nxt_congr (f g : ℕ → ℕ) (h : ∀ j < M, f j = g j) : ∀ i < M, nxt f i = nxt g i := by
  intro i hi
  unfold nxt
  rw [sumN_eq, sumN_eq]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  have := (chk i hi c (Finset.mem_range.1 hc)).2
  split_ifs with h0
  · rfl
  · exact h _ (by omega)

/-! ## Count tables -/


def TT : List ℕ := [0x80000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010000020000040000080000100000200000400000800001, 0x80000200000400001000002000002000008000010000020000040000100000200000400000800000800000800002000002000008000010000008000020000040000080000200000200000800001000002000004000010000020000040000020000020000100000100000200000400001000002000002000002000010000020000040000080000080000100000800001000002000004000002000004000010000010000040000040000040000080000200000400001000001000004000008000008000010000040000040000100000200000200000400000800000800004000002000004000010000020000080000100000100000200000400000800001000004000008000010000010000040000020000080000200000100000400000400002000004000004000008000010000010000080000080000400000400001000001000004000004000010000010000010000020000080000100000200000400000800001000004000008000004000008000008000020000040000040000200000200000400002000002000004000008000008000020000020000080000080000200000200000800001000002000004000010000020000040000080000040000080000100000100000200001000001000002000004000008000010000010000020000080000100000400000200000400002000004000004000008000020000040000040000080000080000100000800001000002000002000004000008000040000080000100000200000200000400000800001000002000004000008000010000020000020000040000200000400000800001000002000004000008000010000010000020000040000080000100000200000200000800001000001000004000008000020000010000020000080000100000400000200000400002000002000004000010000010000020000080000100000200000400000400000800002000004000008000010000010000020000080000080000200000200000800000800002000002000010000010000020000080000080000100000400000400000800002000002000004000008000010000020000040000080000100000200000400001000002000004000008000010000020000040000080000100000200000400000800001000002000004000008000010, 0x800004000008000030000080000040000200000300000800000c0000480000c000018000040000024000020000090000080000200000800000080000300000800001000008000004000020000030000060000100000480000c00002000000300000200001800001000003000008000030000080000030000040000180000800000600000c000010000020000120000300000c0000200000040000100000300000200000c000008000004000010000040000100000300000200000c000018000010000020000120000100000480000900000800001000000c0000080000c0000020000080000180000400001200003000002000008000008000010000040000100000200000800000180000c00000400000c00009000002000006000004000030000060000040000080000180000200000c0000100000f0000060000600000400001680000c000090000080000018000040000120000300000600001000000c0000400000c00004000000600000c00000800003000006000004000060000030000080000600000300000800001200000c0000600000400001200001800006000008000012000030000060000100000240000c00000c00004000000600000c000018000010000020000180000180000300000600000c0000100000100000200000c0000180000c0000020000080000300000600000600000c0000600001200000400000800001000002000018000030000048000030000080000100000c000018000030000078000030000060000100000200000400000c000024000024000060000040000100000600000c0000240000480000600000f00001e0000480000200000400001000002000002400003000003000018000030000020000090000120000600000180000600001800003000018000004000010000078000030000060000600000300000800001e00005a0000480000c0000060000180000c00002400002400006000004000010000018000012000078000060000240000180000c00000800004e0000240000480003c0000240000600001e00000c0000180001800000c00002000001800003c000078000120000240000600000c00002000003f00009c00012c0002d00005a0000f00001b0000480000600000f00001e00004800009000018000030000080000100, 0x80000700000e00007000018800007000050000070000188000190000d40002c80005d80013c0000880000700002c8000320000620002c80000080000400000e00001c000188000070000500000700000e0000310000ea0002c80009e0000040000020000200000180000400000e000040000188000050000080000240001400000a0000140000200000600001b0000480002800008c0000070000380000700000380001c0000160000040000200000700002c0000700000380001c00003800001c000058000440000380001100002c80001c0000640000100000080001c000002000010000020000070000200000700000380001c00000e00001c0000b0000310000620002c80000280001c000008000014000220000080000080000040000400000800000400000c000028000040000140000300002a0000090001640000a00005c00001200035e000280000020000070000180000400000e0000310000120000a0000120001180000080000100000080000400000a0000080000e00000400000e0000e0000048000120000200000100000e0000070000200000200001180001c0000200000700000e0000310000400001c00001f8001180000080000100000200000100000200002000002000004000008000014000018000010000040000100000280001c0000020000100000400000800000a0000140000e00004400000400000c000020000080000380000700000800000400000e00001c0001c000038000070000150000040000090000240000380000900001c0000880000400000e0000070000380000e00001c00008800013a0000d40002a00004d0000ea0000380000900003800009c00004000004000004000038000064000038000100000200000800000200000800003800008c000578000070000380001500000400000900016400006400014000054000170000060000100000090000240002c8000d780006400015e0000a0000500000350000200001340000e00006a0000380002ec000188000f3000040000080000b98000540000e00008880001c00003f00093e0002bc0008c0000350000a80001340003a80006a0001640002ec0009e0000a40001e6000388000a30000fc0002e60006240012900015b0004440007ac001740002c200093e0012d0003f80007f0, 0x80000b0000160000dc0003c80000b0000a40000dc0003c80002c0001ee0007dc0011000045e0001a0000134000c38000f60000f2000adc0000080000500001600002c0003c80000b0000a40000dc0001b8000790002700007dc0022f00000500000200002c000028000050000160000540003480000900000e0000380002900001200002c0000380001180002a00007a000624001a100000b00009a0000dc0000580003c0000360000040000380000b0000620000dc0000580003700007800002c0000d8000d000009a000340000c380004d0001ec0000140000080003700000200001c0000280000b0000320000dc0000580004d00001600002c000188000790000f2000adc0000480003700000e0000340006800001c00000a0000040000500000b0000040000140000480000700002c00008c0006180000e0003ee0001480012d800021000dfa00082c0000280000b00001e0000540001980006900001c0001480001e80034200000a000014000008000060000120000100001b8000050000160001cc000070000260000320000140001b80000b00003600002c0002b8000410000320000dc0001b8000790000680003840004700034200000a0000140000280000100000200002c0000280000600000a000024000028000010000080000140000480003700000200001c0000500000b0000120000340001b8000d00000040000140000380001c00006e0000dc0000c80000500001600002c0003980006e0000e600030c0000500000e00004c000058000130000370001a00000640001b80000b00009a0001b8000398001a00004ae00018c0006180009f0002700000580001300009a0002860000640000500000500006e0000b0000058000190000360000a80000280000b00006e00015c000da00000b00008200030c0000500000e0003ee0000b0000290000c30004b60000780001500000e0000420007dc0037e8000d00003680001480010580006300003200027c0001b8000f700006e0008800003c8002690000640000d0001c88000a50001c2001bb40003700008e00244c000750001a100006300018600027c0009c0000f70003ee0008800022f00015f0004d200087c001db80022c000722001118003a28003a9000dda0016a40055780093800244c004c940132f00265e, 0x8000100000200001800008000001000012c000180000800000460003e00012a80028c800c6900042e0002c0002d4000387000200002140000008000060000200000400008000001000012c000180000300001000005aa0012a80063480000600000200004000004000006000020000070000600000100000160000580004b0000200000720000580002c0000420000ea000cdc003ff0000100001600001800000800007b000074000004000058000100000c0000180000080000600000f60000400001d00021700016000085c002d40000b000070e0000180000080006000000200002c00003000010000048000180000080000b000002000004000030000100000200002140000080000600000160000a40010b80004d00000c000004000060000100000040000200000800000b000072000160000c600001600095400025800348000049002d7000157400003000010000024000070000290000c000002c0002580003a8007fe00000c0000180000080000a00002000001c0003000000600002000036c0000b00004a0000480000180003000001000005c0000400005f00007e000048000180000300001000000a400066c0008f0007fe00000c000018000030000010000020000400000300000a00000c0000400000400000100000e0000180000800006000000200002c000060000100000200000a4000300002170000040000200000580004d0000c0000180000120000060000200000400006d8000c00001b6000630000060000160000940000800002500006000042e000090000300000100001600003000006d80042e000f7e000298000c600011e0005aa0000800002500016000086e000090000060000060000c00001180000800002400005c0000e0000030000100000c00002f8001c60000100000fc000630000060000160009540001180004b00018c000d200000900001c0000160000920012a800b5c000176000718000258002ae8000a6000048000478000300001f00000c00014640008000055c000090000148003d30001200003360049200006000011e006eee001064003ff0000a60003180004780016a8001f000095400146400634800298000ab8001190004b4000424000f4c00284c009c60008460024900036e800fe400189e006eee00f0200455a808ab5, 0x80001600002c000268000f20000160001fc000268000f200006800070400272800558801e41000966000580008eb000a670003c80055d00000080000700002c000058000f20000160001fc0002680004d0001e4000bda00272800f208000070000020000600000600000700002c000098000a000001b0000200000880007f000036000122000080000600000660001da001844008a50000160002c00002680000b0000f30000e0000004000080000160001580002680000b00009a0001e6000058000380004b30002c00012cc008eb0001600014ce00001c0000080009a000002000040000038000160000620002680000b00016000002c000058000560001e40003c80055d00000d80009a0000200001d8002598000b000000e000004000070000180000040000300000d8000100001220003000016c0000220013940003f80080e8000a9007cac0030dc0000380001600002a0000980003d0001400000440003f80007680114a00000e00001c0000080001100003600002c0004d00000700002c0006340001100008600006200001c0004d00001600009e000060000bd0000dc0000620002680004d0001e4000100000b040010a00114a00000e00001c000038000010000020000600000380001100000e00006c0000600000100001600001c0000d80009a000002000040000070000180000360001d80004d0004b3000004000030000080000b00001340002680001880000700002c000058000c680013400031a000b600000700002200010c0000b00004300009a0009660000c40004d0000160002c00004d0000c6800966002d120004080016c0001d4000bda0000b0000430002c000178e0000c4000070000070001340001a00000b00003100009e000130000038000180001340005e80034f0000160001b8000b60000070000220013940001a00007f0002d800203a0000a80002600002200015200272801f2b000266000d3c0003f80061b8001020000620007500004d000382000134002ac4000f2000acc0000c4000200007760001ce00058200a7d00009a000214011f56002094008a50001020005b0000750002f6800382001394002ac400f2080047f0015980020ac00ab8000726001dd800546c017b70010940053e8007490028d8003892011f560278680cf05819e0b, 0x80001d00003a0003a0001a480001d00032c0003a0001a4800093000bc4004af000a290041d900130a0009f801886801a2700069200c3400000080000800003a000074001a480001d00032c0003a0000740003490016d0004af0020ec8000080000020000900000880000800003a0000d0000fa80002b00002c0000cc000cb0000560002a20000b0000bb0000990003b6002a740111400001d0004fc0003a00000e8001cd00018e0000040000b00001d0002400003a00000e8000e800039a000074000638009850004fc0026140188680027e00344e000020000008000e80000020000580000400001d0000800003a00000e80027e00003a0000740009000034900069200c340000158000e800002c000498004c280016000001000000400008000024000004000044000158000160002a20005d80026c000033002578000658011df000175012dfa0064840000400001d0000300000d0000560001f5000066000658000ed8022280000100000200000080001c0000560000400007400000800003a000ad4000198000e40000800000200007400001d00010c0000900015e8001660000800003a00007400034900018c001214001d2802228000010000020000040000010000020000900000400001c0000100000ac00008800001000020000020000158000e800000200005800008000024000056000498000740009850000040000440000b0001600001d00003a00002000000800003a0000740015a8001d000056a001360000080000330001c80000e8000720000e800130a0001000007400001d0004fc0007400015a80130a0075240005ec0026c0002cb0016d00000e8000720004fc00394a000100000080000080001d000024c0000e80004000010c0001a0000040000240001d0000af4005b780001d0002cc0013600000800003300257800024c000cb0004d800477c0000c0000340000330002ea004af004b7e8003b20016de00065800c9080017b000080000b2c000740005e20001d0005148001a480141f00010000031800d8e8002b800090a015bc8000e80003a5029494003b480111400017b0009b0000b2c005b40005e2002578005148020ec80074c00283e00381801676000b7c00363a00a1b803535001e6d00ade400e08405e310074a602949405bca021a9f84353f, 0x80002500004a000534002ac8000250004d8000534002ac8000c800129a008574011e980834f0023860010c403c3b803a55000ab20193540000080000900004a000094002ac8000250004d8000534000a6800559002906008574041a78000090000020000d40000b80000900004a00011c0017680004100003a0001280013600008200058e0000e80014d8000de00072000461001f79000025000862000534000128003450002960000040000e8000250003920005340001280014d00068a000094000a58011c300086200470c03c3b8004310074aa0000240000080014d000002000074000048000250000a20005340001280043100004a000094000e4800559000ab20193540002080014d00003a000a18008e180027e0000120000040000900003500000400005c0002080001d00058e000a6c003e280004a0042ba0009b00247a8002fc02987200bf680000480002500003600011c000748002ed0000940009b0001c8003ef20000120000240000080002c000082000058000a680000900004a001248000250001700000a2000024000a68000250001ba0000d4002668002290000a2000534000a680055900025c001cb00030d003ef2000012000024000048000010000020000d40000480002c0000120001040000b80000100002c0000240002080014d00000200007400009000035000082000a18000a68011c300000400005c0000e80027e00029a0005340002880000900004a0000940024900029a000924001f140000900004a0002e0000128000b800014d002386000144000a6800025000862000a6800249002386011474000854003e280040d002906000128000b8000862007d0c0001440000900000900029a000320000128000510001ba0002380000480003500029a00133400953000025000452001f140000900004a0042ba000320001360007c50091ea0000d80004700004a0005f80085740a61c80056e00254c0009b0017ed0002150000a2001034000a680094d00029a008f4c002ac8023330001440004b8017468003e7000e58029a740014d00061a056a8a0064cc01f79000215000f8a00103400a4180094d0042ba008f4c041a7800b3f004666005a7c02be7801178005d1a0120ac06fe1803435014d3a0191540c79880dd88056a8a0c1b9c4ee8389dd07, 0x80002e00005c0007300042200002e00072000073000422000108001c1000e05001dc300f436003e0c001a98086c20076980010880303d00000080000a00005c0000b80042200002e000720000730000e60008440045bc00e05007a1b00000a0000020001300000f00000a00005c0001800021c00005e00004a0001a0001c80000bc000ac40001280022b000138000cfc006e58036de00002e000d4c000730000170005ae0004140000040001280002e00056c000730000170001cc000b5c0000b800105001f06000d4c007c18086c20006a600ed30000028000008001cc0000020000940000500002e0000c8000730000170006a600005c0000b80015b0008440010880303d00002f0001cc00004a00141000f830004310000140000040000a00004c0000040000780002f000025000ac4001158005f0000068007028000e40045800005ae054a100156d80000500002e00003c000180000990004380000d0000e400033f006dbc000014000028000008000420000bc000074000e600000a00005c001de8000340002380000c8000028000e600002e0002c0000130004040003340000c8000730000e6000844000388002c48004ea006dbc00001400002800005000001000002000130000050000420000140001780000f00000100003a0000280002f0001cc0000020000940000a00004c0000bc001410000e6001f06000004000078000128004310003980007300003200000a00005c0000b8003bd000398000ef4002f800000a0000680004700001700011c0001cc003e0c000190000e600002e000d4c000e60003bd003e0c025914000b50005f00005a40045bc0001700011c000d4c00fa7c0001900000a00000a000398000420000170000640002c00003000000500004c00039800202000e8800002e000668002f800000a000068007028000420001c8000be00116000000f000060000068000b5c00e050152840007b0003a20000e4002adb0002d40000c8001690000e6000e0800039800ee1800422003a700001900007100262200056400162404afc0001cc0009d40a93a400a268036de0002d40017c00016900116f000e0800702800ee1807a1b0010a00074e0008ae0050ec00197400988801e6a80de6c0054ec0257e002a41018afc018a500a93a417b2c0aa4f31549e6, 0x8000380000700009a000620000038000a280009a0006200001540028c001679002f2301ad0e0066b00028401171100dffa001880056c200000080000b0000700000e000620000038000a280009a000134000c400071140167900d68700000b0000020001a80001300000b000070000200002f400008300005c0002380028a0001060013700001700036a0001aa00167c00a73805b620000380014200009a00001c000976000628000004000170000380007f00009a00001c0002680012ec0000e00018a00335800142000cd6011711000a1001bff400002c000008002680000020000b8000058000380000f20009a00001c000a100000700000e0001fc000c40001880056c200004180026800005c0024d4019ac0006a60000160000040000b00006a0000040000980004180002e001370001b50008b900008e00b3c800145007cfa800a220a1f3802482800005800038000042000200000c40005e800011c0014500059f00b6c400001600002c0000080005f0001060000940013400000b000070002f780004700034c0000f200002c0013400003800043a0001a8006740004980000f20009a000134000c4000052c0042b8007a800b6c400001600002c000058000010000020001a80000580005f00001600020c0001300000100004a00002c000418002680000020000b80000b00006a0001060024d400134003358000004000098000170006a60004d00009a00003c80000b0000700000e0005ef0004d00017bc0045c80000b00008e0006980001c0001a60002680066b00001e400134000038001420001340005ef0066b004c2f4000ef0008b900079a0071140001c0001a600142001d4140001e40000b00000b0004d00005500001c00007900043a0004000000580006a0004d00033a0015d20000380009300045c80000b00008e00b3c80005500028a00117201f3ea0001080008000008e001444016790287ce000a90005748001450049050003bc0000f2001e68001340014600004d001791800620005cda0001e4000a5803c0c00073800215c0803e000268000f5013791400fa7805b620003bc0022e4001e6801c4500146000b3c80179180d6870017bf00b9b400ccac08dd70023d200f030030e981a4ce0084400401f0043d202e2800299f41379142ba1d157b352af66a, 0x800043000086000c90008c4800043000e18000c90008c48001ad0039540229f8047c282ceea00a284003aa021db4818e600023120943b80000080000c00008600010c008c4800043000e18000c900019200118900b02e0229f81677500000c0000020002400001780000c0000860002a0004088000b10000700002f4003860001620021180001c00052400023700252c00f55809278000043001d50000c9000021800f2a0008f60000040001c000043000b44000c9000021800324001e5400010c0023d805142001d5001450821db4800ea8031cc0000030000008003240000020000e000006000043000120000c9000021800ea800008600010c002d10011890023120943b800058800324000070003f6c028a1000a100000180000040000c0000900000040000bc0005880003800211800292000c660000bd0114fc001c300d60200111c12606603ba98000060000430000480002a0000f600081100017a001c300094b0124f0000018000030000008000840001620000b80019200000c0000860049380005e8004be0001200000300019200004300064800024000a03800668000120000c900019200118900076800625800b958124f000001800003000006000001000002000240000060000840000180002c40001780000100005c000030000588003240000020000e00000c000090000162003f6c001920051420000040000bc0001c000a10000648000c900004800000c00008600010c0092700064800249c0063300000c0000bd00097c0002180025f00032400a28400024000192000043001d500019200092700a28409195600134400c660009f900b02e0002180025f001d50033a100002400000c00000c0006480006b4000218000900006480005400000600009000064800501c01fc3800043000cd00063300000c0000bd0114fc0006b4003860018cc035808000120000a80000bd0022380229f849819800e28007f0e001c30077530004d10001200027e400192001caa000648023e14008c4808e23000240000ed005b6380096c00312c0d21c80032400172b222252017484092780004d10031980027e402c0b801caa0114fc023e14167750020f4011c460123a80ee110030fc016d8e04b99c2f9c100c69f0690e406891c523fe0434e22222524c5cf28fdbd51fb7a]

def tb (t i : ℕ) : ℕ := TT.getD t 0 / 2 ^ (23 * i) % 2 ^ 23

theorem tb0 : ∀ i < M, tb 0 i = 1 := by decide +kernel

theorem tbs0 : ∀ i < M, nxt (tb 0) i = tb 1 i := by decide +kernel
theorem tbs1 : ∀ i < M, nxt (tb 1) i = tb 2 i := by decide +kernel
theorem tbs2 : ∀ i < M, nxt (tb 2) i = tb 3 i := by decide +kernel
theorem tbs3 : ∀ i < M, nxt (tb 3) i = tb 4 i := by decide +kernel
theorem tbs4 : ∀ i < M, nxt (tb 4) i = tb 5 i := by decide +kernel
theorem tbs5 : ∀ i < M, nxt (tb 5) i = tb 6 i := by decide +kernel
theorem tbs6 : ∀ i < M, nxt (tb 6) i = tb 7 i := by decide +kernel
theorem tbs7 : ∀ i < M, nxt (tb 7) i = tb 8 i := by decide +kernel
theorem tbs8 : ∀ i < M, nxt (tb 8) i = tb 9 i := by decide +kernel
theorem tbs9 : ∀ i < M, nxt (tb 9) i = tb 10 i := by decide +kernel
theorem tbs10 : ∀ i < M, nxt (tb 10) i = tb 11 i := by decide +kernel
theorem tbs : ∀ t < 11, ∀ i < M, nxt (tb t) i = tb (t + 1) i := by
  intro t ht
  interval_cases t
  · exact tbs0
  · exact tbs1
  · exact tbs2
  · exact tbs3
  · exact tbs4
  · exact tbs5
  · exact tbs6
  · exact tbs7
  · exact tbs8
  · exact tbs9
  · exact tbs10

theorem E'_tb : ∀ t ≤ 11, ∀ i < M, E' t i = tb t i := by
  intro t
  induction t with
  | zero => intro _ i hi; rw [tb0 i hi]; rfl
  | succ t ih =>
    intro ht i hi
    show nxt (E' t) i = _
    rw [nxt_congr _ _ (ih (by omega)) i hi, tbs t (by omega) i hi]

/-! ## The linear recurrence, state by state -/


def cf (l : ℕ) : ℤ := match l with | 0 => -1 | 1 => 9 | 2 => -36 | 3 => 84 | 4 => -126 | 5 => 126 | 6 => -84 | 7 => 36 | 8 => -9 | 9 => 1 | _ => 0

def V (t i : ℕ) : ℤ := ∑ l ∈ Finset.range (9 + 1), cf l * (E' (t + l) i : ℤ)

def Vtb (t i : ℕ) : ℤ := ∑ l ∈ Finset.range (9 + 1), cf l * (tb (t + l) i : ℤ)

theorem Vbase : ∀ i < M, Vtb 2 i = 0 := by decide +kernel

theorem V_succ (t i : ℕ) :
    V (t + 1) i = ∑ c ∈ Finset.range NR, if tr i c = 0 then 0 else V t (tr i c - 1) := by
  unfold V
  have e : ∀ l, E' (t + 1 + l) i = nxt (E' (t + l)) i := fun l => by
    rw [show t + 1 + l = (t + l) + 1 by omega]; rfl
  simp only [e, nxt, sumN_eq, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  by_cases h0 : tr i c = 0 <;> simp [h0]

theorem V_zero : ∀ t, 2 ≤ t → ∀ i < M, V t i = 0 := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    intro i hi
    rw [← Vbase i hi]
    unfold V Vtb
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [E'_tb _ (by have := Finset.mem_range.1 hl; omega) i hi]
  | succ t _ ih =>
    intro i hi
    rw [V_succ]
    refine Finset.sum_eq_zero (fun c hc => ?_)
    have := (chk i hi c (Finset.mem_range.1 hc)).2
    split_ifs with h0
    · rfl
    · exact ih _ (by omega)

theorem a_E' (n : ℕ) : a n = E' n 0 := by
  rw [← E_E' n 0 (by decide), dec0, ← a_eq_E]
  exact card_bridge n

theorem a_rec (n : ℕ) (hn : 2 + 9 ≤ n) : ∑ l ∈ Finset.range (9 + 1), cf l * (a (n - 9 + l) : ℤ) = 0 := by
  have := V_zero (n - 9) (by omega) 0 (by decide)
  unfold V at this
  simpa only [a_E'] using this

theorem a_tb (n : ℕ) (hn : n ≤ 11) : a n = tb n 0 := by
  rw [a_E', E'_tb n hn 0 (by decide)]


theorem rec_small : ∀ n < 11, 9 < n → (tb n 0 : ℤ) = 9 * (tb (n - 1) 0 : ℤ) - 36 * (tb (n - 2) 0 : ℤ) + 84 * (tb (n - 3) 0 : ℤ) - 126 * (tb (n - 4) 0 : ℤ) + 126 * (tb (n - 5) 0 : ℤ) - 84 * (tb (n - 6) 0 : ℤ) + 36 * (tb (n - 7) 0 : ℤ) - 9 * (tb (n - 8) 0 : ℤ) + (tb (n - 9) 0 : ℤ) := by
  decide +kernel

theorem recurrence (n : ℕ) (hn : 9 < n) : (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  rcases Nat.lt_or_ge n 11 with h | h
  · have := rec_small n (by omega) hn
    rw [a_tb n (by omega), a_tb (n - 1) (by omega), a_tb (n - 2) (by omega), a_tb (n - 3) (by omega), a_tb (n - 4) (by omega), a_tb (n - 5) (by omega), a_tb (n - 6) (by omega), a_tb (n - 7) (by omega), a_tb (n - 8) (by omega), a_tb (n - 9) (by omega)]
    exact this
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    have hr := a_rec (m + 9) (by omega)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, cf, Nat.add_sub_cancel, add_zero] at hr
    simp only [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega, show m + 9 - 3 = m + 6 by omega, show m + 9 - 4 = m + 5 by omega, show m + 9 - 5 = m + 4 by omega, show m + 9 - 6 = m + 3 by omega, show m + 9 - 7 = m + 2 by omega, show m + 9 - 8 = m + 1 by omega, show m + 9 - 9 = m by omega]
    linarith

theorem gf_of (f : ℕ → ℕ) (hr : ∀ n, 11 ≤ n → (f n : ℤ) = 9 * f (n - 1) - 36 * f (n - 2) + 84 * f (n - 3) - 126 * f (n - 4) + 126 * f (n - 5) - 84 * f (n - 6) + 36 * f (n - 7) - 9 * f (n - 8) + f (n - 9))
    (hv : ∀ n < 11, f n = tb n 0) :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (f n : ℚ)) * (1 - X) ^ 9 =
      X * (16 + 112 * X + 304 * X ^ 2 - 594 * X ^ 3 + 775 * X ^ 4 - 442 * X ^ 5 + 216 * X ^ 6 - 36 * X ^ 7 + 9 * X ^ 8) := by
  have v1 : (f 1 : ℚ) = 16 := by exact_mod_cast (hv 1 (by norm_num)).trans (by decide +kernel : tb 1 0 = 16)
  have v2 : (f 2 : ℚ) = 256 := by exact_mod_cast (hv 2 (by norm_num)).trans (by decide +kernel : tb 2 0 = 256)
  have v3 : (f 3 : ℚ) = 2032 := by exact_mod_cast (hv 3 (by norm_num)).trans (by decide +kernel : tb 3 0 = 2032)
  have v4 : (f 4 : ℚ) = 9822 := by exact_mod_cast (hv 4 (by norm_num)).trans (by decide +kernel : tb 4 0 = 9822)
  have v5 : (f 5 : ℚ) = 35509 := by exact_mod_cast (hv 5 (by norm_num)).trans (by decide +kernel : tb 5 0 = 35509)
  have v6 : (f 6 : ℚ) = 105995 := by exact_mod_cast (hv 6 (by norm_num)).trans (by decide +kernel : tb 6 0 = 105995)
  have v7 : (f 7 : ℚ) = 275775 := by exact_mod_cast (hv 7 (by norm_num)).trans (by decide +kernel : tb 7 0 = 275775)
  have v8 : (f 8 : ℚ) = 646407 := by exact_mod_cast (hv 8 (by norm_num)).trans (by decide +kernel : tb 8 0 = 646407)
  have v9 : (f 9 : ℚ) = 1395174 := by exact_mod_cast (hv 9 (by norm_num)).trans (by decide +kernel : tb 9 0 = 1395174)
  have v10 : (f 10 : ℚ) = 2815594 := by exact_mod_cast (hv 10 (by norm_num)).trans (by decide +kernel : tb 10 0 = 2815594)
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (f n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 9 = A - C 9 * (A * X ^ 1) + C 36 * (A * X ^ 2) - C 84 * (A * X ^ 3) + C 126 * (A * X ^ 4) - C 126 * (A * X ^ 5) + C 84 * (A * X ^ 6) - C 36 * (A * X ^ 7) + C 9 * (A * X ^ 8) - (A * X ^ 9) := by
    simp only [map_ofNat]; ring
  have e2 : (X * (16 + 112 * X + 304 * X ^ 2 - 594 * X ^ 3 + 775 * X ^ 4 - 442 * X ^ 5 + 216 * X ^ 6 - 36 * X ^ 7 + 9 * X ^ 8) : ℚ⟦X⟧) = X ^ 1 * C 16 + X ^ 2 * C 112 + X ^ 3 * C 304 - X ^ 4 * C 594 + X ^ 5 * C 775 - X ^ 6 * C 442 + X ^ 7 * C 216 - X ^ 8 * C 36 + X ^ 9 * C 9 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℚ) else (f k : ℚ) := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 11 with hn | hn
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
    have h := hr (m + 11) (by omega)
    simp only [show m + 11 - 1 = m + 10 by omega, show m + 11 - 2 = m + 9 by omega, show m + 11 - 3 = m + 8 by omega, show m + 11 - 4 = m + 7 by omega, show m + 11 - 5 = m + 6 by omega, show m + 11 - 6 = m + 5 by omega, show m + 11 - 7 = m + 4 by omega, show m + 11 - 8 = m + 3 by omega, show m + 11 - 9 = m + 2 by omega] at h ⊢
    simp only [show ¬ (m + 11 = 0) by omega, show 1 ≤ m + 11 by omega, show ¬ (m + 10 = 0) by omega, show 2 ≤ m + 11 by omega, show ¬ (m + 9 = 0) by omega, show 3 ≤ m + 11 by omega, show ¬ (m + 8 = 0) by omega, show 4 ≤ m + 11 by omega, show ¬ (m + 7 = 0) by omega, show 5 ≤ m + 11 by omega, show ¬ (m + 6 = 0) by omega, show 6 ≤ m + 11 by omega, show ¬ (m + 5 = 0) by omega, show 7 ≤ m + 11 by omega, show ¬ (m + 4 = 0) by omega, show 8 ≤ m + 11 by omega, show ¬ (m + 3 = 0) by omega, show 9 ≤ m + 11 by omega, show ¬ (m + 2 = 0) by omega, show ¬ (m + 11 = 1) by omega, show ¬ (m + 11 = 2) by omega, show ¬ (m + 11 = 3) by omega, show ¬ (m + 11 = 4) by omega, show ¬ (m + 11 = 5) by omega, show ¬ (m + 11 = 6) by omega, show ¬ (m + 11 = 7) by omega, show ¬ (m + 11 = 8) by omega, show ¬ (m + 11 = 9) by omega, ↓reduceIte, zero_mul, mul_zero, add_zero, sub_zero]
    have h' : ((f (m + 11) : ℤ) : ℚ) = (((9 * (f (m + 10) : ℤ) - 36 * (f (m + 9) : ℤ) + 84 * (f (m + 8) : ℤ) - 126 * (f (m + 7) : ℤ) + 126 * (f (m + 6) : ℤ) - 84 * (f (m + 5) : ℤ) + 36 * (f (m + 4) : ℤ) - 9 * (f (m + 3) : ℤ) + (f (m + 2) : ℤ) : ℤ)) : ℚ) := congrArg _ h
    push_cast at h'
    linarith

theorem solution_main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (16 + 112 * X + 304 * X ^ 2 - 594 * X ^ 3 + 775 * X ^ 4 - 442 * X ^ 5 + 216 * X ^ 6 - 36 * X ^ 7 + 9 * X ^ 8) ∧
    ∀ n : ℕ, 9 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) :=
  ⟨gf_of a (fun n hn => recurrence n (by omega)) (fun n hn => a_tb n (by omega)), recurrence⟩

end OMA.S_oeis_a223682

theorem OMA.solution : type_of% @OMA.S_oeis_a223682.main :=
  OMA.S_oeis_a223682.solution_main
