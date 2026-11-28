import OMAStatements.S_oeis_a223766

/-!
Proof of Barker's two conjectures for OEIS A223766, by an exact transfer-matrix count.

Each line condition (unimodal, nondecreasing) is recognised by a small automaton reading the line
from its first to its last entry. Adding a bottom row to an array extends every column, the
diagonals and antidiagonals ending in that row, and finalises nothing else, so the states of
the lines meeting the bottom row form a finite summary that is updated row by row. The number of
ways to complete a summary to an array with t more rows satisfies a linear recursion over the
107 reachable summaries; the kernel checks the explicit successor table, the count tables up
to t = 14, and the order-9 recurrence for every summary at t = 5, which then propagates
to all t by linearity. The generating function follows from the recurrence and the initial terms.
-/

namespace OMA.S_oeis_a223766

open PowerSeries Finset

abbrev Q : ℕ := 2
abbrev K : ℕ := 4
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

abbrev M : ℕ := 107
abbrev NR : ℕ := Q ^ K

/-- Codes of the reachable states, 28 bits each. -/
instance decFK : DecidableEq (Fin K → LS) := inferInstance
instance decSt : DecidableEq St := instDecidableEqProd

def RS : ℕ := 0x3a353303df06693af43d53a3532f3a9491150986863df06503eaf70e3df06683af43d03a3532a3a949103c71676456238e3c120954d3c92e4d3c92d3eaf6f53df064f3af43b73a353113e4fc4a3e4fc493a9490b3c716754621433456238d3cd113a3c1209445c196fa12cc9b43e4c0a3c71670a3099e145c19504f1968d3c7165750f7c673e4fc3150f7c664d3c9283e4fc303a948f2462142e45623883cd11353c1208f45c196ea12cc9a43e4c09a309a00a2aa41fac02143995a12645c1969a2aa4004621415456236f4f196924eba0ac3cd111c3c12076a3099ffac6171ea3099faa12cc95479ff4243e4c04a2aa41eac02142995a125ac61724aa849bf4d3c8b1a2aa419a0cd69b515772b50986854cdd34747ff9ee474094844446b0438560aac61723ac0213d995a120ae3fcf850f7beaae3fcf7aa849be50f7be94d3c8b0ade071750986093df05d3ae9f7bcade0716aa253d8977d3a251576ae50986084cdd2ca3eaf6783df05d23af433a3a352940000000

/-- Successor table: entry i * NR + c is 0 (dead) or 1 + the index of the successor, 7 bits each. -/
def TRT : ℕ := 0x6b0000000000000000000000000000000000000000000000000000000000000000000000000000000034e8000000000000000000000000006b000000000000000000000000000000000000000000011805c000000000000000000000000000000000000000000000000000000000000000000000000000000000000c9a8000000000000000000000000c98f16100000000000000000000000034e80000000000000000000000000067000000000000000000000000005f000000000000000000000000006700000000000000000000000000000000000000000000000000000000000000000000003f180000000000000000000000003f1005b0000000000000000000003f98000b594000000000000000003e7801db566c5700000000000000000000000000000000000000000000000000000000000000000000000000000c98f16100000000000000000000000000600000000000000000000000000000000000000000000000000000005300000000000000000000000000000000000000000000000000000060000000000000000000000000005f000000000000380000000000005e000000000000000000000000005d0000000000000000000000154054000002c000004a00000480000049000000000000000000048000004700000000000000000000000000000000000000000001100430108041000000000000000000000000000000000000000000011805c000000000000000000000000000000000000000000000000000000000000000000000000000003f1005b0000000000000000000003e7801db566c570000000000000000000000000000000000000000000000000000004b0000000000000000000000158000000000000000000000000015405400000000000000000000000000530000000000002700000000002951000000000000000000000000284f000000000000390000000000004e000000000000390000000000004e00000240000039000000000000000000000000004d0000000000004c000000000000000000000000004b000002c000004a000004800000490000000000000000000000000000000000000000000000048000004700000000000000000000000000000000000000000000000000000000000000000000000118000011400000000000000000011004301080410000000000002d0000000000003c004c02c000002b000000000000000000000000002b00000000000035000000000000210000000000203f00000000000000000000000000000000000000000000000000001f3d0000000000002d0000000000003c0000018000002d000000000000000000000000003b0000000000003a0000024000003900000000000000000003700000380000000000000000000370000036000000000000000000000000002b0000000000003500000170000034000003000019b200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000310000000000000000000000000000000000000000000000000000003000017ae0000018000002d00000000000000004c02c000002b000000000000000000000000002a000000000a402800540240000000000000000000000054024000000000000000000000184c0180000000000000000000000000026000002700000000000000184c01800000000000000000000000000260000025000000000000000054024000000000000000000000005402400000000000000000000000540230000000005002200000001854000000000000000000000000184c018000000000000000000000182c017000002100000000000000182c00a00000203e7801d386cd191854000000000000000000000000184c018000000000000000000000182c0170000016000000000000001854000000000010500000000000184c012000000010440100000000183c000000000010380000a34000182c00a0000009101c0060a10182182c00a0000009101c0060a10182

def dec (i : ℕ) : St := decS (RS / 2 ^ (28 * i) % 2 ^ 28)
def tr (i c : ℕ) : ℕ := TRT / 2 ^ (7 * (i * NR + c)) % 2 ^ 7
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


def TT : List ℕ := [0x4000200010000800040002000100008000400020001000080004000200010000800040002000100008000400020001000080004000200010000800040002000100008000400020001000080004000200010000800040002000100008000400020001000080004000200010000800040002000100008000400020001000080004000200010000800040002000100008000400020001000080004000200010000800040002000100008000400020001000080004000200010000800040002000100008000400020001000080004000200010000800040002000100008000400020001, 0x4000000000001000040000000200000000000040004000100004000200010000000000004000300020001c0000000000020000400000001000000004000200020000800080008000200000001000000002000000000000600070000000040002000200008000c00040002000100008000400010002000000004000000000000800080002000180008000600000001000080004000200010000800040002000280000000000000000000040000000300010000c0006000200010000c000400030001000080004000400010000c0008000b00010000c000800040003000180016000b, 0x400000000000100004000000000000000000000000600010000400020001000000000000000000002000400000000000030000800000001000000008000200030000800100012000400000002800000000000000000000000100000000080000000400008000c0002000300018001000060002000480000000800000000000080014000300040000c0006000000018000c00080005000200010000800030004800000000000000000000000000006000200020000a000400020001c000800070002000100008000800020001c0014001200020001c0016000800070004000700038, 0x40000000000010000400000000000000000000000060001000040002000100000000000000000000000050000000000003000080000000200000000800020004000080018002a000a0000000400000000000000000000000014000000010000000060001000100004000400020001c00080004000a800000014000000000000000200004000900014000a0000000200010000e000400038001c000e0005000a80000000000000000000000000000c000380048000c000800040003c000e000f0004800200010001000040003c002c002400040003c00300010000f000800136009b, 0x40000000000010000400000000000000000000000060001000040002000100000000000000000000000050000000000003000080000000200000000800020005000080018006200100000000500000000000000000000000014000000018000000060001000180004000500028002c000a00060018800000020000000000000000280006001300024001200000003000180016000600058002c0016000900188000000000000000000000000000100005800980012000f0007800780016001e00058003c001e001e000800078005c004e000800078005e0020001f0010002d20169, 0x4000000000001000040000000000000000000000006000100004000200010000000000000000000000005000000000000300008000000020000000080002000600008001800ce001400000005000000000000000000000000140000000180000000600010002000040006000300040000c0006003380000002800000000000000028000800268003c001e0000000300020002200080008000400020000f0033800000000000000000000000000014000880134001e001a000d000e40022003900088006800340034000f800e400ba009d000f800e400ba003e0039001f0061c030e, 0x400000000000100004000000000000000000000000600010000400020001000000000000000000000000500000000000030000800000002000000008000200070000800180190001400000005000000000000000000000000140000000180000000600010002800040007000380058000e0006006400000002800000000000000028000a004a80054002a00000003000280032000a000b00058002c00150064000000000000000000000000000014000c80254002a002a0015001a400320069000c800a800540054001c801a401680130001c801a4016800720069003900c820641, 0x4000000000001000040000000000000000000000006000100004000200010000000000000000000000005000000000000300008000000020000000080002000800008001802e20014000000050000000000000000000000001400000001800000006000100030000400080004000740010000600b880000002800000000000000028000c00898006c003600000003000300046000c000e80074003a001b00b880000000000000000000000000001400118044c003600400020002ec004600bb001180100008000800031802ec029802320031802ec029800c600bb00630188a0c45, 0x40000000000010000400000000000000000000000060001000040002000100000000000000000000000050000000000003000080000000200000000800020009000080018053000140000000500000000000000000000000014000000018000000060001000380004000900048009400120006014c00000002800000000000000028000e00f48008400420000000300038005e000e001280094004a0021014c0000000000000000000000000000140017807a40042005d002e80504005e014100178017400ba00ba005180504049803ef00518050404980146014100a302e261713, 0x4000000000001000040000000000000000000000006000100004000200010000000000000000000000005000000000000300008000000020000000080002000a000080018092a00140000000500000000000000000000000014000000018000000060001000400004000a0005000b800140006024a80000002800000000000000028001001a58009c004e0000000300040007a00100017000b8005c0027024a800000000000000000000000000014001e80d2c004e008200410084c007a0213001e802080104010400800084c07dc06dc00800084c07dc0200021301000536c29b6, 0x4000000000001000040000000000000000000000006000100004000200010000000000000000000000005000000000000300008000000020000000080002000b0000800180fe800140000000500000000000000000000000014000000018000000060001000480004000b0005800e00016000603fa00000002800000000000000028001202c2800b4005a0000000300048009a0012001c000e00070002d03fa000000000000000000000000000014002681614005a00b0005800d40009a03500026802c00160016000c100d400d0a0baa00c100d400d0a0304035001820917448ba, 0x4000000000001000040000000000000000000000006000100004000200010000000000000000000000005000000000000300008000000020000000080002000c0000800181b1a00140000000500000000000000000000000014000000018000000060001000500004000c00060010c0018000606c68000000280000000000000002800140481000cc0066000000030005000be001400218010c0086003306c6800000000000000000000000000014002f82408006600e800740147c00be051f002f803a001d001d001190147c1508135f01190147c15080464051f02320f57c7abe, 0x4000000000001000040000000000000000000000006000100004000200010000000000000000000000005000000000000300008000000020000000080002000d0000800182d4600140000000500000000000000000000000014000000018000000060001000580004000d00068013c001a00060b51800000028000000000000000280016072a000e40072000000030005800e6001600278013c009e00390b518000000000000000000000000000140039839500072012b009581ec000e607b00039804ac02560256018d01ec0210c1f76018d01ec0210c063407b0031a19262c931, 0x4000000000001000040000000000000000000000006000100004000200010000000000000000000000005000000000000300008000000020000000080002000e0000800184a1600140000000500000000000000000000000014000000018000000060001000600004000e000700170001c000612858000000280000000000000002800180b1e800fc007e000000030006001120018002e0017000b8003f12858000000000000000000000000000140044858f4007e017a00bd02cf401120b3d0044805e802f402f4022282cf432ae3207022282cf432ae088a0b3d0445282874143, 0x4000000000001000040000000000000000000000006000100004000200010000000000000000000000005000000000000300008000000020000000080002000f00008001876b800140000000500000000000000000000000014000000018000000060001000680004000f0007801a8001e00061dae00000002800000000000000028001a10dc80114008a00000003000680142001a0035001a800d400451dae0000000000000000000000000000140050886e4008a01d600eb0402c0142100b00508075803ac03ac02df8402c4bfc4df802df8402c4bfc0b7e100b05bf3ea29f514]

def tb (t i : ℕ) : ℕ := TT.getD t 0 / 2 ^ (17 * i) % 2 ^ 17

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
theorem tbs11 : ∀ i < M, nxt (tb 11) i = tb 12 i := by decide +kernel
theorem tbs12 : ∀ i < M, nxt (tb 12) i = tb 13 i := by decide +kernel
theorem tbs13 : ∀ i < M, nxt (tb 13) i = tb 14 i := by decide +kernel
theorem tbs : ∀ t < 14, ∀ i < M, nxt (tb t) i = tb (t + 1) i := by
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
  · exact tbs11
  · exact tbs12
  · exact tbs13

theorem E'_tb : ∀ t ≤ 14, ∀ i < M, E' t i = tb t i := by
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

theorem Vbase : ∀ i < M, Vtb 5 i = 0 := by decide +kernel

theorem V_succ (t i : ℕ) :
    V (t + 1) i = ∑ c ∈ Finset.range NR, if tr i c = 0 then 0 else V t (tr i c - 1) := by
  unfold V
  have e : ∀ l, E' (t + 1 + l) i = nxt (E' (t + l)) i := fun l => by
    rw [show t + 1 + l = (t + l) + 1 by omega]; rfl
  simp only [e, nxt, sumN_eq, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  by_cases h0 : tr i c = 0 <;> simp [h0]

theorem V_zero : ∀ t, 5 ≤ t → ∀ i < M, V t i = 0 := by
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

theorem a_rec (n : ℕ) (hn : 5 + 9 ≤ n) : ∑ l ∈ Finset.range (9 + 1), cf l * (a (n - 9 + l) : ℤ) = 0 := by
  have := V_zero (n - 9) (by omega) 0 (by decide)
  unfold V at this
  simpa only [a_E'] using this

theorem a_tb (n : ℕ) (hn : n ≤ 14) : a n = tb n 0 := by
  rw [a_E', E'_tb n hn 0 (by decide)]


theorem rec_small : ∀ n < 14, 13 < n → (tb n 0 : ℤ) = 9 * (tb (n - 1) 0 : ℤ) - 36 * (tb (n - 2) 0 : ℤ) + 84 * (tb (n - 3) 0 : ℤ) - 126 * (tb (n - 4) 0 : ℤ) + 126 * (tb (n - 5) 0 : ℤ) - 84 * (tb (n - 6) 0 : ℤ) + 36 * (tb (n - 7) 0 : ℤ) - 9 * (tb (n - 8) 0 : ℤ) + (tb (n - 9) 0 : ℤ) := by
  decide +kernel

theorem recurrence (n : ℕ) (hn : 13 < n) : (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  rcases Nat.lt_or_ge n 14 with h | h
  · have := rec_small n (by omega) hn
    rw [a_tb n (by omega), a_tb (n - 1) (by omega), a_tb (n - 2) (by omega), a_tb (n - 3) (by omega), a_tb (n - 4) (by omega), a_tb (n - 5) (by omega), a_tb (n - 6) (by omega), a_tb (n - 7) (by omega), a_tb (n - 8) (by omega), a_tb (n - 9) (by omega)]
    exact this
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    have hr := a_rec (m + 9) (by omega)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, cf, Nat.add_sub_cancel, add_zero] at hr
    simp only [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega, show m + 9 - 3 = m + 6 by omega, show m + 9 - 4 = m + 5 by omega, show m + 9 - 5 = m + 4 by omega, show m + 9 - 6 = m + 3 by omega, show m + 9 - 7 = m + 2 by omega, show m + 9 - 8 = m + 1 by omega, show m + 9 - 9 = m by omega]
    linarith

theorem gf_of (f : ℕ → ℕ) (hr : ∀ n, 14 ≤ n → (f n : ℤ) = 9 * f (n - 1) - 36 * f (n - 2) + 84 * f (n - 3) - 126 * f (n - 4) + 126 * f (n - 5) - 84 * f (n - 6) + 36 * f (n - 7) - 9 * f (n - 8) + f (n - 9))
    (hv : ∀ n < 14, f n = tb n 0) :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (f n : ℚ)) * (1 - X) ^ 9 =
      X * (11 - 43 * X + 47 * X ^ 2 + 58 * X ^ 3 - 205 * X ^ 4 + 209 * X ^ 5 - 42 * X ^ 6 - 150 * X ^ 7 + 256 * X ^ 8 - 245 * X ^ 9 + 151 * X ^ 10 - 55 * X ^ 11 + 9 * X ^ 12) := by
  have v1 : (f 1 : ℚ) = 11 := by exact_mod_cast (hv 1 (by norm_num)).trans (by decide +kernel : tb 1 0 = 11)
  have v2 : (f 2 : ℚ) = 56 := by exact_mod_cast (hv 2 (by norm_num)).trans (by decide +kernel : tb 2 0 = 56)
  have v3 : (f 3 : ℚ) = 155 := by exact_mod_cast (hv 3 (by norm_num)).trans (by decide +kernel : tb 3 0 = 155)
  have v4 : (f 4 : ℚ) = 361 := by exact_mod_cast (hv 4 (by norm_num)).trans (by decide +kernel : tb 4 0 = 361)
  have v5 : (f 5 : ℚ) = 782 := by exact_mod_cast (hv 5 (by norm_num)).trans (by decide +kernel : tb 5 0 = 782)
  have v6 : (f 6 : ℚ) = 1601 := by exact_mod_cast (hv 6 (by norm_num)).trans (by decide +kernel : tb 6 0 = 1601)
  have v7 : (f 7 : ℚ) = 3141 := by exact_mod_cast (hv 7 (by norm_num)).trans (by decide +kernel : tb 7 0 = 3141)
  have v8 : (f 8 : ℚ) = 5907 := by exact_mod_cast (hv 8 (by norm_num)).trans (by decide +kernel : tb 8 0 = 5907)
  have v9 : (f 9 : ℚ) = 10678 := by exact_mod_cast (hv 9 (by norm_num)).trans (by decide +kernel : tb 9 0 = 10678)
  have v10 : (f 10 : ℚ) = 18618 := by exact_mod_cast (hv 10 (by norm_num)).trans (by decide +kernel : tb 10 0 = 18618)
  have v11 : (f 11 : ℚ) = 31422 := by exact_mod_cast (hv 11 (by norm_num)).trans (by decide +kernel : tb 11 0 = 31422)
  have v12 : (f 12 : ℚ) = 51505 := by exact_mod_cast (hv 12 (by norm_num)).trans (by decide +kernel : tb 12 0 = 51505)
  have v13 : (f 13 : ℚ) = 82243 := by exact_mod_cast (hv 13 (by norm_num)).trans (by decide +kernel : tb 13 0 = 82243)
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (f n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 9 = A - C 9 * (A * X ^ 1) + C 36 * (A * X ^ 2) - C 84 * (A * X ^ 3) + C 126 * (A * X ^ 4) - C 126 * (A * X ^ 5) + C 84 * (A * X ^ 6) - C 36 * (A * X ^ 7) + C 9 * (A * X ^ 8) - (A * X ^ 9) := by
    simp only [map_ofNat]; ring
  have e2 : (X * (11 - 43 * X + 47 * X ^ 2 + 58 * X ^ 3 - 205 * X ^ 4 + 209 * X ^ 5 - 42 * X ^ 6 - 150 * X ^ 7 + 256 * X ^ 8 - 245 * X ^ 9 + 151 * X ^ 10 - 55 * X ^ 11 + 9 * X ^ 12) : ℚ⟦X⟧) = X ^ 1 * C 11 - X ^ 2 * C 43 + X ^ 3 * C 47 + X ^ 4 * C 58 - X ^ 5 * C 205 + X ^ 6 * C 209 - X ^ 7 * C 42 - X ^ 8 * C 150 + X ^ 9 * C 256 - X ^ 10 * C 245 + X ^ 11 * C 151 - X ^ 12 * C 55 + X ^ 13 * C 9 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℚ) else (f k : ℚ) := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 14 with hn | hn
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 14 := ⟨n - 14, by omega⟩
    have h := hr (m + 14) (by omega)
    simp only [show m + 14 - 1 = m + 13 by omega, show m + 14 - 2 = m + 12 by omega, show m + 14 - 3 = m + 11 by omega, show m + 14 - 4 = m + 10 by omega, show m + 14 - 5 = m + 9 by omega, show m + 14 - 6 = m + 8 by omega, show m + 14 - 7 = m + 7 by omega, show m + 14 - 8 = m + 6 by omega, show m + 14 - 9 = m + 5 by omega] at h ⊢
    simp only [show ¬ (m + 14 = 0) by omega, show 1 ≤ m + 14 by omega, show ¬ (m + 13 = 0) by omega, show 2 ≤ m + 14 by omega, show ¬ (m + 12 = 0) by omega, show 3 ≤ m + 14 by omega, show ¬ (m + 11 = 0) by omega, show 4 ≤ m + 14 by omega, show ¬ (m + 10 = 0) by omega, show 5 ≤ m + 14 by omega, show ¬ (m + 9 = 0) by omega, show 6 ≤ m + 14 by omega, show ¬ (m + 8 = 0) by omega, show 7 ≤ m + 14 by omega, show ¬ (m + 7 = 0) by omega, show 8 ≤ m + 14 by omega, show ¬ (m + 6 = 0) by omega, show 9 ≤ m + 14 by omega, show ¬ (m + 5 = 0) by omega, show ¬ (m + 14 = 1) by omega, show ¬ (m + 14 = 2) by omega, show ¬ (m + 14 = 3) by omega, show ¬ (m + 14 = 4) by omega, show ¬ (m + 14 = 5) by omega, show ¬ (m + 14 = 6) by omega, show ¬ (m + 14 = 7) by omega, show ¬ (m + 14 = 8) by omega, show ¬ (m + 14 = 9) by omega, show ¬ (m + 14 = 10) by omega, show ¬ (m + 14 = 11) by omega, show ¬ (m + 14 = 12) by omega, show ¬ (m + 14 = 13) by omega, ↓reduceIte, zero_mul, mul_zero, add_zero, sub_zero]
    have h' : ((f (m + 14) : ℤ) : ℚ) = (((9 * (f (m + 13) : ℤ) - 36 * (f (m + 12) : ℤ) + 84 * (f (m + 11) : ℤ) - 126 * (f (m + 10) : ℤ) + 126 * (f (m + 9) : ℤ) - 84 * (f (m + 8) : ℤ) + 36 * (f (m + 7) : ℤ) - 9 * (f (m + 6) : ℤ) + (f (m + 5) : ℤ) : ℤ)) : ℚ) := congrArg _ h
    push_cast at h'
    linarith

theorem solution_main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (11 - 43 * X + 47 * X ^ 2 + 58 * X ^ 3 - 205 * X ^ 4 + 209 * X ^ 5 - 42 * X ^ 6 - 150 * X ^ 7 + 256 * X ^ 8 - 245 * X ^ 9 + 151 * X ^ 10 - 55 * X ^ 11 + 9 * X ^ 12) ∧
    ∀ n : ℕ, 13 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) :=
  ⟨gf_of a (fun n hn => recurrence n (by omega)) (fun n hn => a_tb n (by omega)), recurrence⟩

end OMA.S_oeis_a223766

theorem OMA.solution : type_of% @OMA.S_oeis_a223766.main :=
  OMA.S_oeis_a223766.solution_main
