import OMAStatements.S_oeis_a223765

/-!
Proof of Barker's two conjectures for OEIS A223765, by an exact transfer-matrix count.

Each line condition (unimodal, nondecreasing) is recognised by a small automaton reading the line
from its first to its last entry. Adding a bottom row to an array extends every column, the
diagonals and antidiagonals ending in that row, and finalises nothing else, so the states of
the lines meeting the bottom row form a finite summary that is updated row by row. The number of
ways to complete a summary to an array with t more rows satisfies a linear recursion over the
41 reachable summaries; the kernel checks the explicit successor table, the count tables up
to t = 10, and the order-7 recurrence for every summary at t = 3, which then propagates
to all t by linearity. The generating function follows from the recurrence and the initial terms.
-/

namespace OMA.S_oeis_a223765

open PowerSeries Finset

abbrev Q : ℕ := 2
abbrev K : ℕ := 3
abbrev κr : ℕ := 1
abbrev κc : ℕ := 1
abbrev κd : ℕ := 2
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

theorem LP_nil (κ : ℕ) : LP κ [] := by
  unfold LP
  split
  · exact ⟨0, by simp, by simp⟩
  · simp
  · trivial

theorem LP1 (l : List (Fin Q)) : LP 1 l ↔ Unimodal l := Iff.rfl
theorem LP2 (l : List (Fin Q)) : LP 2 l ↔ l.IsChain (· ≤ ·) := Iff.rfl
theorem LP0 (l : List (Fin Q)) : LP 0 l ↔ True := Iff.rfl

theorem good_iff {n : ℕ} (x : Fin n → Row) : good x ↔ G x := by
  unfold good G rowOK
  simp only [alive_iff, κr, κc, κd, κa]
  rw [dg_cells _ _ (LP_nil _)]
  rw [ad_cells _ _ (LP_nil _)]
  simp only [LP0, LP1, LP2, colE]
  simp only [show ∀ c, dgE x c = diag x c from fun _ => rfl]
  simp only [show ∀ c, adE x c = antidiag x c from fun _ => rfl]
  all_goals simp

theorem card_bridge (n : ℕ) : a n = (univ.filter fun y : Fin n → Row => G y).card := by
  unfold a
  exact congrArg Finset.card (Finset.filter_congr (fun x _ => good_iff x))

/-! ## The explicit automaton, checked by the kernel -/

def lsD (v : ℕ) : LS :=
  if v = 0 then none else some (⟨(v - 1) / 2 % Q, Nat.mod_lt _ (by decide)⟩, decide ((v - 1) % 2 = 1))

def decS (code : ℕ) : St :=
  (fun j => lsD (code / (2 * Q + 1) ^ (j : ℕ) % (2 * Q + 1)),
   fun p => lsD (code / (2 * Q + 1) ^ (K + (p : ℕ)) % (2 * Q + 1)),
   fun p => lsD (code / (2 * Q + 1) ^ (2 * K + (p : ℕ)) % (2 * Q + 1)))

abbrev M : ℕ := 41
abbrev NR : ℕ := Q ^ K

/-- Codes of the reachable states, 21 bits each. -/
instance decFK : DecidableEq (Fin K → LS) := inferInstance
instance decSt : DecidableEq St := instDecidableEqProd

def RS : ℕ := 0x773784ed5c9fba14ee6ee7b0813f7401dcdc8f61008e1aea54752292951c35b4e5ed470d4285f0942f827b07ba5474a47ec9149494e5f39da635397ca951c8a55c64ed5c247eb51493f61c07b0e034ed316bbdfc9daa0b2d05d77bf66ef6ea55ad4ed4f9fb99cee6b200000

/-- Successor table: entry i * NR + c is 0 (dead) or 1 + the index of the successor, 6 bits each. -/
def TRT : ℕ := 0x290000000000000000000000000000000009e60000000000290000004680000000004509230000000009e600000000002500001500002100000000002500000000002200c01d01a01c00000001a01900000000000000000000000000000045092300001300001e00000000000000000000002200001500002100002000001f00001300001e00c01d01a01c00000000000000000000000000000001b00000000001a01900d01500000020c0130000000000180005d600d01500000000d01400000020d00000000020c0130000002070124503ce20d00000000020c00b00000020a0001490002070061440c22070061440c2

def dec (i : ℕ) : St := decS (RS / 2 ^ (21 * i) % 2 ^ 21)
def tr (i c : ℕ) : ℕ := TRT / 2 ^ (6 * (i * NR + c)) % 2 ^ 6
def rowOf (c : ℕ) : Row := fun j => ⟨c / Q ^ (j : ℕ) % Q, Nat.mod_lt _ (by decide)⟩

theorem chk : ∀ i < M, ∀ c < NR, step (dec i) (rowOf c) = (if tr i c = 0 then none else some (dec (tr i c - 1))) ∧
    tr i c ≤ M := by
  decide +kernel

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


def TT : List ℕ := [0x10008004002001000800400200100080040020010008004002001000800400200100080040020010008004002001000800400200100080040020010008004002001, 0x10000000004001001001000400100100040020040010000000004001000000200200100080080000000004004002001800c004002001000c00e002001801000e007, 0x100000000040010000018004001001800400400900200000000060018000004003001800c0120000000000008004003800c008004002001c018004004002003801c, 0x1000000000400100000180040010020004004014003000000000600280000040040020014028000000000000c007007001400e0070040038030008007004008e047, 0x100000000040010000018004001002800400402800300000000060038000004005002801c050000000000000c00b00d801c01600b007806c06000f00d807813609b, 0x1000000000400100000180040010030004004049003000000000600480000040060030024092000000000000c010018802402001000d00c40b001a01880d027a13d, 0x100000000040010000018004001003800400408000300000000060058000004007003802c100000000000000c01602a002c02c016015015013402a02a01504be25f, 0x10000000004001000001800400100400040040da0030000000006006800000400800400341b4000000000000c01d044803403a01d02002242080400448200892449, 0x100000000040010000018004001004800400416900300000000060078000004009004803c2d2000000000000c02506b003c04a02502e835835205d06b02e8ebe75f, 0x10000000004001000001800400100500040042450030000000006008800000400a005004448a000000000000c02e0a1004405c02e04105085440820a10411850c28, 0x100000000040010000018004001005800400438d0030000000006009800000400b005804c71a000000000000c0380ea804c070038058075481e0b00ea85826ad356]

def tb (t i : ℕ) : ℕ := TT.getD t 0 / 2 ^ (13 * i) % 2 ^ 13

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
theorem tbs : ∀ t < 10, ∀ i < M, nxt (tb t) i = tb (t + 1) i := by
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

theorem E'_tb : ∀ t ≤ 10, ∀ i < M, E' t i = tb t i := by
  intro t
  induction t with
  | zero => intro _ i hi; rw [tb0 i hi]; rfl
  | succ t ih =>
    intro ht i hi
    show nxt (E' t) i = _
    rw [nxt_congr _ _ (ih (by omega)) i hi, tbs t (by omega) i hi]

/-! ## The linear recurrence, state by state -/


def cf (l : ℕ) : ℤ := match l with | 0 => -1 | 1 => 7 | 2 => -21 | 3 => 35 | 4 => -35 | 5 => 21 | 6 => -7 | 7 => 1 | _ => 0

def V (t i : ℕ) : ℤ := ∑ l ∈ Finset.range (7 + 1), cf l * (E' (t + l) i : ℤ)

def Vtb (t i : ℕ) : ℤ := ∑ l ∈ Finset.range (7 + 1), cf l * (tb (t + l) i : ℤ)

theorem Vbase : ∀ i < M, Vtb 3 i = 0 := by decide +kernel

theorem V_succ (t i : ℕ) :
    V (t + 1) i = ∑ c ∈ Finset.range NR, if tr i c = 0 then 0 else V t (tr i c - 1) := by
  unfold V
  have e : ∀ l, E' (t + 1 + l) i = nxt (E' (t + l)) i := fun l => by
    rw [show t + 1 + l = (t + l) + 1 by omega]; rfl
  simp only [e, nxt, sumN_eq, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  by_cases h0 : tr i c = 0 <;> simp [h0]

theorem V_zero : ∀ t, 3 ≤ t → ∀ i < M, V t i = 0 := by
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

theorem a_rec (n : ℕ) (hn : 3 + 7 ≤ n) : ∑ l ∈ Finset.range (7 + 1), cf l * (a (n - 7 + l) : ℤ) = 0 := by
  have := V_zero (n - 7) (by omega) 0 (by decide)
  unfold V at this
  simpa only [a_E'] using this

theorem a_tb (n : ℕ) (hn : n ≤ 10) : a n = tb n 0 := by
  rw [a_E', E'_tb n hn 0 (by decide)]


theorem rec_small : ∀ n < 10, 9 < n → (tb n 0 : ℤ) = 7 * (tb (n - 1) 0 : ℤ) - 21 * (tb (n - 2) 0 : ℤ) + 35 * (tb (n - 3) 0 : ℤ) - 35 * (tb (n - 4) 0 : ℤ) + 21 * (tb (n - 5) 0 : ℤ) - 7 * (tb (n - 6) 0 : ℤ) + (tb (n - 7) 0 : ℤ) := by
  decide +kernel

theorem recurrence (n : ℕ) (hn : 9 < n) : (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  rcases Nat.lt_or_ge n 10 with h | h
  · have := rec_small n (by omega) hn
    rw [a_tb n (by omega), a_tb (n - 1) (by omega), a_tb (n - 2) (by omega), a_tb (n - 3) (by omega), a_tb (n - 4) (by omega), a_tb (n - 5) (by omega), a_tb (n - 6) (by omega), a_tb (n - 7) (by omega)]
    exact this
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    have hr := a_rec (m + 7) (by omega)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, cf, Nat.add_sub_cancel, add_zero] at hr
    simp only [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega, show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega, show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega, show m + 7 - 7 = m by omega]
    linarith

theorem gf_of (f : ℕ → ℕ) (hr : ∀ n, 10 ≤ n → (f n : ℤ) = 7 * f (n - 1) - 21 * f (n - 2) + 35 * f (n - 3) - 35 * f (n - 4) + 21 * f (n - 5) - 7 * f (n - 6) + f (n - 7))
    (hv : ∀ n < 10, f n = tb n 0) :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (f n : ℚ)) * (1 - X) ^ 7 =
      X * (7 - 21 * X + 22 * X ^ 2 + X ^ 3 - 12 * X ^ 4 - 9 * X ^ 5 + 26 * X ^ 6 - 17 * X ^ 7 + 4 * X ^ 8) := by
  have v1 : (f 1 : ℚ) = 7 := by exact_mod_cast (hv 1 (by norm_num)).trans (by decide +kernel : tb 1 0 = 7)
  have v2 : (f 2 : ℚ) = 28 := by exact_mod_cast (hv 2 (by norm_num)).trans (by decide +kernel : tb 2 0 = 28)
  have v3 : (f 3 : ℚ) = 71 := by exact_mod_cast (hv 3 (by norm_num)).trans (by decide +kernel : tb 3 0 = 71)
  have v4 : (f 4 : ℚ) = 155 := by exact_mod_cast (hv 4 (by norm_num)).trans (by decide +kernel : tb 4 0 = 155)
  have v5 : (f 5 : ℚ) = 317 := by exact_mod_cast (hv 5 (by norm_num)).trans (by decide +kernel : tb 5 0 = 317)
  have v6 : (f 6 : ℚ) = 607 := by exact_mod_cast (hv 6 (by norm_num)).trans (by decide +kernel : tb 6 0 = 607)
  have v7 : (f 7 : ℚ) = 1097 := by exact_mod_cast (hv 7 (by norm_num)).trans (by decide +kernel : tb 7 0 = 1097)
  have v8 : (f 8 : ℚ) = 1887 := by exact_mod_cast (hv 8 (by norm_num)).trans (by decide +kernel : tb 8 0 = 1887)
  have v9 : (f 9 : ℚ) = 3112 := by exact_mod_cast (hv 9 (by norm_num)).trans (by decide +kernel : tb 9 0 = 3112)
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (f n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 7 = A - C 7 * (A * X ^ 1) + C 21 * (A * X ^ 2) - C 35 * (A * X ^ 3) + C 35 * (A * X ^ 4) - C 21 * (A * X ^ 5) + C 7 * (A * X ^ 6) - (A * X ^ 7) := by
    simp only [map_ofNat]; ring
  have e2 : (X * (7 - 21 * X + 22 * X ^ 2 + X ^ 3 - 12 * X ^ 4 - 9 * X ^ 5 + 26 * X ^ 6 - 17 * X ^ 7 + 4 * X ^ 8) : ℚ⟦X⟧) = X ^ 1 * C 7 - X ^ 2 * C 21 + X ^ 3 * C 22 + X ^ 4 - X ^ 5 * C 12 - X ^ 6 * C 9 + X ^ 7 * C 26 - X ^ 8 * C 17 + X ^ 9 * C 4 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℚ) else (f k : ℚ) := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 10 with hn | hn
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    have h := hr (m + 10) (by omega)
    simp only [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega, show m + 10 - 3 = m + 7 by omega, show m + 10 - 4 = m + 6 by omega, show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega, show m + 10 - 7 = m + 3 by omega] at h ⊢
    simp only [show ¬ (m + 10 = 0) by omega, show 1 ≤ m + 10 by omega, show ¬ (m + 9 = 0) by omega, show 2 ≤ m + 10 by omega, show ¬ (m + 8 = 0) by omega, show 3 ≤ m + 10 by omega, show ¬ (m + 7 = 0) by omega, show 4 ≤ m + 10 by omega, show ¬ (m + 6 = 0) by omega, show 5 ≤ m + 10 by omega, show ¬ (m + 5 = 0) by omega, show 6 ≤ m + 10 by omega, show ¬ (m + 4 = 0) by omega, show 7 ≤ m + 10 by omega, show ¬ (m + 3 = 0) by omega, show ¬ (m + 10 = 1) by omega, show ¬ (m + 10 = 2) by omega, show ¬ (m + 10 = 3) by omega, show ¬ (m + 10 = 4) by omega, show ¬ (m + 10 = 5) by omega, show ¬ (m + 10 = 6) by omega, show ¬ (m + 10 = 7) by omega, show ¬ (m + 10 = 8) by omega, show ¬ (m + 10 = 9) by omega, ↓reduceIte, zero_mul, mul_zero, add_zero, sub_zero]
    have h' : ((f (m + 10) : ℤ) : ℚ) = (((7 * (f (m + 9) : ℤ) - 21 * (f (m + 8) : ℤ) + 35 * (f (m + 7) : ℤ) - 35 * (f (m + 6) : ℤ) + 21 * (f (m + 5) : ℤ) - 7 * (f (m + 4) : ℤ) + (f (m + 3) : ℤ) : ℤ)) : ℚ) := congrArg _ h
    push_cast at h'
    linarith

theorem solution_main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (7 - 21 * X + 22 * X ^ 2 + X ^ 3 - 12 * X ^ 4 - 9 * X ^ 5 + 26 * X ^ 6 - 17 * X ^ 7 + 4 * X ^ 8) ∧
    ∀ n : ℕ, 9 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) :=
  ⟨gf_of a (fun n hn => recurrence n (by omega)) (fun n hn => a_tb n (by omega)), recurrence⟩

end OMA.S_oeis_a223765

theorem OMA.solution : type_of% @OMA.S_oeis_a223765.main :=
  OMA.S_oeis_a223765.solution_main
