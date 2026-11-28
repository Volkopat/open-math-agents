import OMAStatements.S_oeis_a223640

/-!
Proof of Barker's two conjectures for OEIS A223640, by an exact transfer-matrix count.

Each line condition (unimodal, nondecreasing) is recognised by a small automaton reading the line
from its first to its last entry. Adding a bottom row to an array extends every column, the
diagonals and antidiagonals ending in that row, and finalises nothing else, so the states of
the lines meeting the bottom row form a finite summary that is updated row by row. The number of
ways to complete a summary to an array with t more rows satisfies a linear recursion over the
607 reachable summaries; the kernel checks the explicit successor table, the count tables up
to t = 14, and the order-9 recurrence for every summary at t = 5, which then propagates
to all t by linearity. The generating function follows from the recurrence and the initial terms.
-/

namespace OMA.S_oeis_a223640

open PowerSeries Finset

abbrev Q : ℕ := 2
abbrev K : ℕ := 4
abbrev κr : ℕ := 1
abbrev κc : ℕ := 1
abbrev κd : ℕ := 1
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

abbrev M : ℕ := 607
abbrev NR : ℕ := Q ^ K

/-- Codes of the reachable states, 28 bits each. -/
instance decFK : DecidableEq (Fin K → LS) := inferInstance
instance decSt : DecidableEq St := instDecidableEqProd

def RS : ℕ := 0x3b0be3b3a4cd963b0be223a4cd7da3099e745c1956a3099e245c19513af8d0e3a39c693a39c553a4cd823af8cf53a39c503a4c161439c45a3b0bdbe3a4cd193a4c0e43c7165da3099e645c19553c722923c7165ca2aa4064562375456238945c196aa2aa40145623703a39c6e3af500a3a35f653af50053a35f604cddf823af4ff13a35f4c3b0be273ec652b3e66a663b0b1f23aab72d4cf10af3b0811e3a490793b074e93a484433af8cfa4cddf7d3af4fec3a35f473a9924a9781cfa3af8c913a39bec45754a2a2aa405462141a45623743df06693a3532b3a353173df06503a35312a0cd6b547409624385624456238ea0cd6ba4385629a0cd6a14cdd34d4385610a3099fba12cc96479ff4343e4c05ac6171f99b97024f2c73e3c8472197dc99d3a9488fa2aa41aa0cd69c50986864cdd3484740949438560b3a353303a484583a4845d3a390393af43d53a3532f3a4cd9b3a4c1663b081373a490923b075023a4845c3df43723a390343eaf70e3df06683af43d03a3532a3a4c14d3a484443c28ecb3a390203af43bc3a353163aa7a393e074863a4c1483e66a673e0377d3a4843f3e0749f3c28ec63df43593a3901b3eb33fe3e539393af80c53a986003eaf6f53df064f3af43b73a353113cd1d6f3c12cca9781cff3a39bf1977dff63af4f8d3a35ee845754b643987564753a8f43987513a483db3cd1d6a3c12cc5977dff13af4f883a35ee34d3c92e3a948f83a955463a992363a986014d3d5633a9552d4d3c92d3a948f74621433456238da0d13c34389332a0cd6b944446ce4385628a0d13aa4389319a0cd6a04cdd34c44446b5438560f3a949113c716713a9490c4f1968e3c716584d4fa5b3aa7a254f2c7bb3e62d774d3c9293a948f33c12095977d3c13a352b33c7537f3c12090977d3bc3df05ec3a352ae45c196f3c716764eba0b23c1207ca12cc9b43e4c0a97dc9a23a94894aa253de977d3a84cdd2d03a3529a3e037963c251bd4f196933c753664eba0ad3c12077ac0213e995a1214ecd15d3e037193c25140aa253d9977d3a34cdd2cb3a352953aa7a3e3a9861a3a949103a98615a3099e145c19504f1a2c33c7228d4f1968d3c716573aab7473b0be403aac37c3b0b20b3aab7463aa86733aa7a3d3e539533af8d133a9924f3eb34173e539523af80de3a986193e4fc4a3a955413e4fc493a9490b3aac3633aab72e4d506903aa865a4d4fa5a3aa7a243c884a73a992313e5393a3a985fc50f7c674d3d55e3e4fc313a9552850f7c664d3c9283e4fc303a948f23c251c23a483e03cd113a3c1209497810ca3a38fbc977d3c03af43583a352b2462142e45623883cd11353c1208f439c45f3a4cd1e3a4c0e944577fb43987553b080ba3a490153b074853a483dfa0d13be474466b438932d97e06ab3a9859d97810c53df42f53a38fb7a0cd6b447ffa07474096144446c94385623977d3bb3eaf6913df05eb3af43533a352ad3c251a945c196e3c722ab3c716753ce42673c251c14ebace73cd1d563c12cb14eba0b13cd11213c1207ba12cc9a43e4c0997dd5d73a954c997dc9a13a948939781ce63a39bd897810b13a38fa3aa26013977dfdd4cddf053af4f743a35ecfaa253dd977d3a74cdd2cf3af433f3a352993c847a345d4a973c8479e457549d3c884934ecd1da3c251a4a309a0045d4a9c43f7d3799b97073c847263aa79c147b307043f7d323e62cfa3aa79bca2aa41f4ecd1df45754bb4cf047a439873dac02143995a1264ecd1623c251454cf03fd3a483c7475777f439c4413b0bda53a4cd003e074093a4c0cb50ab7b34cf04754753a76439873850ab7364cf03f83e037003a483c23c884ac3c853d83c847a245c19693e62d763c8479d3cd5a783c75fb43cd4e433c7537e3c722a63c71670a2aa4004621415456236f3e66a803ce8ba53c890e13ec65443e66a7f3ce7f703c884ab3ec283b3e037953ce42623c251bc4f1a2c83cd5a5f3c75f9b4f196923cd4e2a3c753654ebace23cd1d513c12cac4eba0ac3cd111c3c1207643fba403aab6caa3099ff45d4a9b43f7d3699b97063c847253b0bdc33aac2ff3b0b18e3aab6c93aa85f63aa79c0a3099fa4f2c7ba47b306f45d4a96a12cc95479ff4243e4c04ac6171e99b97014f2c73d3e62cf93c8472097e12e03e538d63af8c963a991d297e06aa3eb339a3e538d53af80613a9859c97dd5d23e4fbcd3a954c497dc99c3e4fbcc3a9488ea2ae12845791c4439c446995de2f3c28e4e4d4f9de3aab6b13a4cd053a4c0d0a2aa41e4ecd1de463456045754ba4cf047944577e2439873cac02142995a1254ecd1613ce41ea3c251444d506133e669ea3b0bdaa3aac2e64d4f9dd3ec64ae3e669e93b0b1753aab6b04cf10323b080a13a48ffc4cf03fc3b0746c3a483c6a30d7094f2c7c045d87a5a2ae123475779845791bfa0d13a547446524389314ac6172499bd4104f2c7433c8842f995de2a3e074223c28e49aa849bf97e06924d3c8b13a985849781ce13af8c783a39bd397810ac3df42dc3a38f9ea30e33e510ad944f2d3f547b6d794638e9e45d93daa30d708510ad934f2c7bf481683d47b6d78463826945d87a4a2aa419516a85850ab7b24ecd1d94812b344753a8e463455b45754b5a0cd69b515772b50986854cdd34747ff9ee474094844446b0438560aac6235999be045510ad174f2d3783e66a033ce8b283c89064ac6172399bd40f510ad164f2c7423ec64c73e66a023ce7ef33c8842eac0213d995a120516a7db50ab7354ecd15c3ec27be3e037183ce41e53c2513fae3fcf8aa855f497e12c750f7bea4d3d4e63e538bd3af8c7d3a991b9ae3fcf7aa849be97e069150f7be94d3c8b03eb33813e538bc3af80483a98583ade0717aa2600e977dfd850986094cddf003df05d33af4f6f3a35ecaae9f7bcade0716aa253d8977d3a251576ae50986084cdd2ca3eaf6783df05d23af433a3a352940000000

/-- Successor table: entry i * NR + c is 0 (dead) or 1 + the index of the successor, 10 bits each. -/
def TRT : ℕ := 0x351e797e5e000000000000000000000000000000001e7002510000000000000000000000000000008e1ec9765c000000000000000000000000000000001ec001eb000000006b000000025b0000000193000000025a000000000000000000000000000193000000024c0000000211000000025900000001b100000002580000000000000000000000000001b100000001b0000000000000000000000000000000351e797e5e000000000000000000000000000000001e70025100000000000000000000000000000000000001f300000000000000000000000000000000000001f30000000000000000000000000000008e1ec9765c000000000000000000000000000000001ec001eb000000000000000000000000000000001950020400000000000000000000000000000000000001940000000000000000000000000000000c86693e4e000000000000000000000000000000000660024d0000000000000000000000000000000018c001d00000000000000000000000000001ca00000001c90000000036000000024b00000000c9000000024a0000000000000000000000000000c9000000024800000000000000000000000000000000000001c60000000000000000000000000001c300000001c2000000006b000000025b0000000193000000025a000000000000000000000000000193000000024c00000000000000000000000000000000000001b300000000000000000000000000000000000001b30000000211000000025900000001b100000002580000000000000000000000000001b100000001b000000000000000000000000000000000000001fe000000000000000000000000000000000005d24100000000000000000000000000000000000002020000000000000000000000000000005c9f995e56000000000000000000000000000000001f9001f800000000000000000000000000000000000001f1000000000000000000000000000000000008be5500000000000000000000000000000000000001f0000000000000000000000000000000000008e6540000000000000000000013059001688e1ea8e56a0000000000000000000013053001668e2378da35000000000000000000000000000234000008ce3200000000000000000000000000008b000008c63000000000000000000000000000000000000001f1000000000000000000000000000000000008be5500000000000000000000000000000000000001f000000000000000000000000000023c000008ee3a0000000000000000000000000001b7000007bdee000000000000000000000000000000000008e654000000000000000000000000000000001e7001e600000000000000000000000000000078de594e52000000000000000000000000000000001e5001e4000000000000000000000000000000001e70025100000000000000000000000000000000070002500000000000000000000000000000000c86693e4e000000000000000000000000000000000660024d000000000000000000000000000193000000024c0000000036000000024b00000000c9000000024a0000000000000000000000000000cc00000002490000000000000000000000000000c900000002480000000000000000000000000000000017500185000000000000000000000000000000002230022200000000000000000000000000021700000002210000000000000000000000160001ca00162001c6000000000000000000000020900208002200021f0000000000000000020b0000000000000000024500000000000000000000000000000000000001a600000000000000000000000000000000000001a500000000000000000000000000000000000001a0000000000000000000ff0000000000000000021b00000000000000000000000000000000000001a900000000fa0000000247000000019f00000002460000000000000000000000000000fe000000015800000000000000000000000000019f000000019e00000000000000000215000000000000000002440000000000000000020b0000000000000000024500000000000000000000000000000000000001a600000000000000000000000000000000000001a50002500211000000021500059001ad001030010f0000000000000000021400000000000021300212000250021100000002100003b0020f001010020e0000000000000000020d00000000000009d0020c0000000000000000021e00000000000021d0021c000000000000000001a40000000000001a3001a20000000000000000021500000000000000000244000000018f000000024300000001910000000242000000000000000000000005900073000d7000e600000000000000000000000ee0010b0019500194000000000000000000000000000193000000019200000000000000000000000000019100000001900000000000000000000000000000000000000205000000000000000000000000000000002230022200000000000000000000000000000000000002050000000000000000000000000000000000000203000000000000000000000000000000000009023f000000000000000000000000000000000008060000000000000000000000000000000000000001fe0000000000000000000000000000000000000203000000000000000000000000000000000005d2410000000000000000000000000000000000000202000000000000000000000000000000000009023f0000000000000000000000000000000000080600000000000000000000000000000000000d70017c00000000000000000000000000000000195002040000000000000000000000000000005c9755d1730000000000000000000000000000005c9715c16f0000000000000000000000000000007de238fa3d0000000000000000000000000000007ddf67d5f40000000000000000000000000000fc00000001f2000000000000000000000000000217000000022100000000000000000000000000000000000001860000000000000000000000000000fc00000001f200000000000000000000000000023c000008ee3a0000000000000000000000000001b7000007bdee00000000000000000000000000000000223002220000000000000000000000059001af001ea0016900000000000000000000000ee000ed001e9001e80000000000000000000000059001af001ea001690000000000000000000000160001ca00162001c6000000000000000000000020900208002200021f000000000000000000000000000000000d70017c000000000000000000000000000000001ac001ed0000000000000000000000059001af001ea0016900000000000000000000000ee000ed001e9001e80000000000000000000013059001688e1ea8e56a0000000000000000000013053001668e2378da35000000000000000000000000000234000008ce3200000000000000000000000000008b000008c6300000000000000000000011160001c578d628bdc7000000000000000000001115c001c378de2785e000000000000000000000112090022e77e208b62c00000000000000000000110430004277dde775dc00000000000000000000000000000000000001730000000000000000000000000000000000000185000000000000000000000000000000000000014b0000000000000000000000000000000000000149000000000000000001bf000000000000000001be000000000000000001d9000000000000000295d8000000000000000001540000000000000000015300000000000000000000000000000000000001b300000000000000000000000000000000000001a900000000000000000000000000000000000001a600000000000000000000000000000000000001a5000000000000000001a40000000000001a3001a2000000000000000000000000000000001750022b000000000000000000000000000000001750018300000000000000000142000000000000141001400000000000000000022a00000000002893c8a6280000000000000000013d00000000000013c0013b0000000000000000000000000000fe00000001580000000000000000000000000002170000000221000000000000000000000000000000000000020200000000000000000000000000000000000001f30000000000000000000000000000fc00000001f200000000000000000000000000000000000001f100000000000000000000000000000000000001f000000000000000000000000000008e000004b12b0000000000000000000000000001b7000007bdee000000000000000000000000000000000000012e000000000000000000000000000000000000012d00000000000000000000000000000000000000fd00000000000000000000000000000000000001580000000000000000008f000000000000000705c00000000000000000000000000000000000076dda00000000000000000000000000000000000559550000000000000000000000000000fe00000002270000000000000000000000000000fe0000000130000000008800000002260000000127000008962400000000000000000000000000008e000004b12b00000000000000000000000000012a000004a528000000000000000000000000000127000004992500000000000000000000000000000000000002050000000000000000000000000000000016e001b200000000000000000000000000000000223002220000000000000000000000059001ad001ac0010e0000000000000000000000160001ab0015e001aa0000000000000000000000000000fe000000015800000000000000000000000000021700000002210000000000000000000000059001ad001ac0010e000000000000000000000000000000001750018500000000000000000000000ee0010b0019500194000000000000000000000020900208002200021f00000000000000000000000000000000000001b40000000000000000021a00000000000000000219000000000000000001a8000000000000000001a700000000000000000000000000000000000001860000000000000000000000000000000016e001b20000000000000000021e00000000000021d0021c0000000000000000013f0000000000000a60013e000000000000000001a40000000000001a3001a200000000000000000000000000000000000001a000000000000000000000000000000000000001b400000000000000000000000000007300000001100000000000000000000000000001ca00000001c9000000000000000000ff0000000000000000021b00000000000000000000000000000000000001a90000000000000000021a00000000000000000219000000000000000001a8000000000000000001a700000000fa00000000ff00000000fe00000000fd000000019900000002180000000217000000021600000000fa00000000f900000000f800000000f7000000019900000001980000000197000000019600000000000000000000000000000000175001850000000000000000000000000000000016e001b200000000000000000000000000007300000001100000000000000000000000000001af00000001ae0000000000000000000000059001ad001ac0010e0000000000000000000000160001ab0015e001aa0002500211000000021500059001ad001030010f0000000000000000021400000000000021300212000250021100000002100003b0020f001010020e0000000000000000013f0000000000000a60013e0000000000000000020d00000000000009d0020c000140018f000000020b000ee0010b001d2001d4000140018a000000020a00209002080020700206000140018f000000018e000ea0018d0018c0018b000140018a000000018900011001880000f00187000000000000000000000000000000000000020500000000000000000000000000000000000002030000000000000000000000000000000000080600000000000000000000000000000000001950020400000000ac0000000182000000017e000000018100000000000000000000000000017e000000017d000000000000000000000000000000000d70016400000000000000000000000000000000162001610000000000000000000000053000b2000e2000e1000000000000000000000015c0015b0015a001590000000000000000000000000000000000000203000000000000000000000000000000000005edff00000000000000000000000000000000000001fe000000000000000000000000000000000007f5fc000000000000000000000000000000000007edfa00000000000000000000000000000000000002020000000000000000000000000000000000080600000000000000000000000000000000000d70017c000000000000000000000000000000000005edff00000000000000000000000000000000000001fe000000000000000000000000000000350d75ed7a000000000000000000000000000000350d35e578000000000000000000000000000000000007f5fc000000000000000000000000000000000007edfa0000000000000000000000000000000017500185000000000000000000000000000000001f9001f80000000000000000000000000000005c9715c16f0000000000000000000000000000007ddf67d5f400000000000000000000000000000000000001f30000000000000000000000000000fc00000001f200000000000000000000000000000000000001f100000000000000000000000000000000000001f000000000000000000000000000008e000004b12b0000000000000000000000000001b7000007bdee000000000000000000000000000000001ac001ed000000000000000000000000000000001ec001eb0000000000000000000000059001af001ea0016900000000000000000000000ee000ed001e9001e8000000000000000000000005900073000d7000e6000000000000000000000000000000001e7001e60000000000000000000000160001ca00162001c6000000000000000000000000000000001e5001e4000000000000000000001305300052350d3348d1000000000000000000001304b0004a340cf338cd000000000000000000001115c001c378de2785e000000000000000000000110430004277dde775dc00000000000000000000000000000000000001b4000000000000000001a8000000000000000001a700000000000000000000000000000000000001c8000000000000000000000000000000000000018400000000000000000000000000000000000001d30000000000000000000000000000000000000157000000000000000001bd0000000000000006f1bb000000000000000001d7000000000000000759d5000000000000000001520000000000000005455000000000000000000000000000000000000000dc00000000000000000000000000000000000000db0000000000000000000000000000000016e0016d0000000000000000000000000000000016c0016b0000000000000000000000000000000000000158000000000000000000000000000000000000014900000000000000000000000000000000000001570000000000000000000000000000000000076dda0000000000000000000000000000000000055955000000000000000001d9000000000000000295d80000000000000000015400000000000000000153000000000000000001d7000000000000000759d5000000000000000001520000000000000005455000000000000000000000000000000000000001d400000000000000000000000000000000000000e6000000000000000000000000000000000000019400000000000000000000000000000000000001d30000000000000000000000000000000000000157000000000000000000000000000000001d2001d100000000000000000000000000000000039000bf0000000000000000000000000000000018c001d00000000000000000004d00000000000000053d4e00000000000000000000000000000000000380df00000000000000000000000000000000000378dd0000000000000000000000000000000000073dce000000000000000000000000000000000005354c0000000000000000013a00000000004e5384dd36000000000000000000a70000000000288a6294a4000000000000000000a30000000000288a12809f000000000000000001cd00000000004d1a3731cb0000000000000000013500000000004d1334c9310000000000000000000000000001ca00000001c9000000000000000000000000000000000000012d0000000000000000000000000000000000000185000000000000000000000000000000000000018400000000000000000000000000000000000001c8000000000000000000000000000000000000018400000000000000000000000000000000000000e600000000000000000000000000000000000001c700000000000000000000000000000000000001c600000000000000000000000000005200000000e40000000000000000000000000001c500000001c40000000000000000000000000001c300000001c20000000000000000008f000000000000000705c00000000000000000000000000000000000055955000000000000000001bf000000000000000001be0000000000000000015400000000000000000153000000000000000001bd0000000000000006f1bb0000000000000000015200000000000000054550000000000000000000000000000000000000009600000000000000000000000000000000000000900000000000000000000000000000fc00000000fb0000000000000000000000000000f600000000f50000000000000000009800000000000000000097000000000000000001ba000000000000000001b900000000000000000095000000000000000000940000000000000000011e00000000000000007d1d0000000000000000011c0000000000000000011b0000000088000000008f000000008e000002348c000000011500000001b800000001b7000006d9b50000000088000000008700000000860000021484000000011a000000011900000001180000045d16000000011500000001140000000113000004491100000000000000000000000000000000000001b400000000000000000000000000000000000001b30000000000000000000000000000000016e001b20000000000000000000000000001b100000001b00000000000000000000000000001af00000001ae0000000000000000000000059001ad001ac0010e0000000000000000000000160001ab0015e001aa00000000000000000109000000000000000001a100000000000000000000000000000000000001a000000000000000000000000000000000000001a90000000000000000019d0000000000000000019c0000000000000000019b0000000000000000019a000000000000000001a8000000000000000001a700000000000000000000000000000000000001a600000000000000000000000000000000000001a50000000000000000013f0000000000000a60013e000000000000000001a40000000000001a3001a200000000000000000109000000000000000001a1000000000000000000000000000073000000011000000000000000000000000000000000000001a00000000000000000000000000000fe000000015800000000000000000000000000019f000000019e000000006b0000000109000000007300000001080000000000000000019d0000000000000000019c000000006b0000000106000000006900000001050000000000000000019b0000000000000000019a00000000fa00000000f900000000f800000000f70000000199000000019800000001970000000196000000000000000000000000000073000000010c00000000000000000000000000010b000000010a0000000000000000000000000000001f8f03c8f1000000000000000000000000000000000f0000ef000000000000000000000003b00093000820009200000000000000000000000ea000e9000e8000e7000000000000000000000005900073000d7000e600000000000000000000000ee0010b001950019400000000000000000000000000019300000001920000000000000000000000000001910000000190000250006b000000006a0003b000690003900068000140018f000000018e000ea0018d0018c0018b0002500064000000006300022000620002000061000140018a000000018900011001880000f0018700000000000000000000000000000000000001860000000000000000000000000000000000000185000000000000000000000000000000000000018400000000000000000000000000000000000000db0000000000000000000000000000005c9715c16f0000000000000000000000000000000016c0016b000000000000000000000000000000000000017a000000000000000000000000000000000000017c0000000000000000000000000000000000000177000000000000000000000000000000000000017600000000000000000000000000000000175001830000000000000000000000000000000016c0016b00000000ac0000000182000000017e0000000181000000000000000000000000000180000000017f00000000000000000000000000017e000000017d000000000000000000000000000000000d70017c000000000000000000000000000000000000017a000000000000000000000000000000000000017c000000000000000000000000000000350d75ed7a000000000000000000000000000000350d35e578000000000000000000000000000000000000017700000000000000000000000000000000000001760000000000000000000000000000005c9755d1730000000000000000000000000000005c9715c16f0000000000000000000000000000000016e0016d0000000000000000000000000000000016c0016b00000000000000000000000000000000000000e6000000000000000000000000000000000000016a000000000000000000000000000000000000016900000000000000000000000000005200000000e400000000000000000000000000016800000001670000000000000000000000000001660000000165000000000000000000000000000000000d700164000000000000000000000000000000001620016300000000000000000000000000000000162001610000000000000000000000053000b2000e2000e100000000000000000000001600015f0015e0015d000000000000000000000015c0015b0015a0015900000000000000000000000000000000000001580000000000000000000000000000000000000157000000000000000000be0000000000000000012f000000000000000000000000000000000000012d00000000000000000000000000000000000559550000000000000000012400000000000000000123000000000000000001200000000000000000011f000000000000000000000000000000000002e54a00000000000000000000000000000000000001490000000000000000000000000000000000051945000000000000000000000000000000000005114300000000000000000154000000000000000001530000000000000000015200000000000000054550000000000000000000b3000000000000000000e30000000000000000000000053000b2000e2000e100000000000000000000000000000000000378dd00000000000000000000000000000000000000db0000000000000000004d00000000000000053d4e00000000000000000000000000000000000378dd000000000000000000000000000000000005354c0001d000ac00000000b300053000b2000b1000b0000000000000000000af0000000000000ae000ad0001d000ac00000000ab00034000aa000a9000a8000000000000000000a30000000000288a12809f0000000000000000009b00000000000009a00099000000000000000000000000000000000000014b00000000000000000000000000000000039000bf000000000000000000000000000000000002e54a000000000000000000000000000000000000014900000000000000000000000000000000000521470000000000000000000000000000000c8392e4b80000000000000000000000000000000c8312dcb60000000000000000000000000000000000051945000000000000000000000000000000000005114300000000000000000142000000000000141001400000000000000000013f0000000000000a60013e0000000000000000013d00000000000013c0013b0000000000000000013a00000000004e5384dd36000000000000000000a30000000000288a12809f0000000000000000013500000000004d1334c931000000000000000000000000000000000000010800000000000000000000000000000000000001100000000000000000000000000000fe00000001300000000000000000000000000000000000000107000000000000000000000000000000000000010400000000fa00000000f900000000f800000000f70000000000000000000000000000f600000000f500000000000000000000000000000000000000900000000000000000000000000000f600000000f5000000000000000000be0000000000000000012f00000000000000000000000000005200000000e4000000000000000000000000000000000000012e000000000000000000000000000000000000012d00000000000000000000000000008e000004b12b00000000000000000000000000012a000004a5280000000000000000000000000001270000049925000000003600000000be000000005200000000bd0000000000000000012400000000000000000123000000003600000000bb000000003300000000ba0000000000000000012200000000000000000121000000000000000001200000000000000000011f0000000000000000009500000000000000000094000000000000000000000003b000930008200092000000000000000000000000000000000002049100000000000000000000000000000000000000900000000088000000008700000000860000021484000000000000000000000b03b000831f88220480000000000000000000000b0340007f1f87d1f07b00000000000000000000000000007a000001e478000000000000000000000000000077000001d87500000000000000000095000000000000000000940000000000000000011e00000000000000007d1d0000000000000000011c0000000000000000011b0000000088000000008700000000860000021484000000011a000000011900000001180000045d160000000115000000011400000001130000044911000000000000000000000000000000000000010800000000000000000000000000007300000001100000000000000000000000000000000000000110000000000000000000000000000000000000010f00000000000000000000000000000000000000e6000000000000000000000000000000000000010e00000000000000000000000000010b000000010d000000000000000000000000000073000000010c00000000000000000000000000010b000000010a000000006b0000000109000000007300000001080000000000000000000000000000000000000107000000006b0000000106000000006900000001050000000000000000000000000000000000000104000000000000000000000000000000001030010200000000000000000000000000000000039000bf000000000000000000000000000000001010010000000000fa00000000ff00000000fe00000000fd0000000000000000000000000000fc00000000fb00000000fa00000000f900000000f800000000f70000000000000000000000000000f600000000f5000000000000000000000000000000000f4000f30000000000000000000000000000001f8f03c8f1000000000000000000000000000000000f0000ef00000000000000000000000ee000ed000ec000eb000000000000000000000003b00093000820009200000000000000000000000ea000e9000e8000e70000000000000000000000000000000000000072000000000000000000000005900073000d7000e600000000000000000000000000000000000000e600000000000000000000000000000000000000e600000000000000000000000000000000000000d500000000000000000000000000000000000000e600000000000000000000000000000000000000bd000000000000000000001305300052350d3348d100000000000000000000000000005200000000e400000000000000000000000000000000000358d500000000000000000000000000000000000348d100000000000000000000000000000000000000e500000000000000000000000000000000000000e4000000000000000000b3000000000000000000e3000000000000000000001305900058350d7358d5000000000000000000001305300052350d3348d10000000000000000000000053000b2000e2000e100000000000000000000000000000000000380df00000000000000000000000000000000000378dd00000000000000000000000000000000000000dc00000000000000000000000000000000000000db000000002e00000000da00000000c300000364d8000000000000000000001305900058350d7358d5000000000000000000001305300052350d3348d1000000000000000000001304b0004a340cf338cd0000000000000000000000000000cc0000032cca0000000000000000000000000000c900000320c70000000000000000000000000000c600000314c40000000000000000000000000000c300000308c1000000000000000000740000000000000000007200000000000000000000000000000000000000c0000250006b000000006a0003b0006900039000680000000000000000006a0000000000000000006800000000000000000000000000000000039000bf00000000000000000000000000000000000000b800000000000000000000000000000000000000bf000000003600000000be000000005200000000bd00000000000000000000000000000000000000bc0301d0003600000000350b034000330c8310c02f000000003600000000bb000000003300000000ba0000000000000000000000000000000c8392e4b80000000000000000000000000000000c8312dcb600000000000000000000000000000000000000b500000000000000000000000000000000000000b40001d000ac00000000b300053000b2000b1000b0000000000000000000af0000000000000ae000ad030250003d000000003c0b03b0003a0c8390e0370301d0003600000000350b034000330c8310c02f0001d000ac00000000ab00034000aa000a9000a8000000000000000000a70000000000288a6294a4000000000000000000a30000000000288a12809f0000000000000000009e00000000000009d0009c0000000000000000009b00000000000009a00099000250006b00000000740005900073000570007200000000000000000098000000000000000000970000000000000000000000000000000000000096000250006b000000006a0003b0006900039000680000000000000000009500000000000000000094000000000000000000000003b000930008200092000000000000000000000000000000000002049100000000000000000000000000000000000000900301d00036000000005413053000521445013c4e0000000088000000008f000000008e000002348c00000000000000000000000000008b00000228890301d0003600000000350b034000330c8310c02f0000000088000000008700000000860000021484000000000000000000000b03b000831f88220480000000000000000000000b0340007f1f87d1f07b00000000000000000000000000007a000001e478000000000000000000000000000077000001d875000250006b000000007400059000730005700072000000000000000000710000000000000700006f0000000000000000006e00000000000006d0006c000250006b000000006a0003b000690003900068000000000000000000670000000000000660006500025000640000000063000220006200020000610000000000000000006000000000000605c17c5e0000000000000000005d00000000000005c0005b030250003d000000005a130590005814457158550301d00036000000005413053000521445013c4e0300b0002e000000004d1304b0004a1244811c460300b0000a00000000451104300042104400fc3e030250003d000000003c0b03b0003a0c8390e0370301d0003600000000350b034000330c8310c02f0300b0002e000000002d0b02b0002a0a42809c260302500024000000002302022000210602007c1e0301d0001c000000001b0201a0001906017058150301400013000000001202011000100140f0380d0300b0000a000000000902007000060140400c020300b0000a000000000902007000060140400c02

def dec (i : ℕ) : St := decS (RS / 2 ^ (28 * i) % 2 ^ 28)
def tr (i c : ℕ) : ℕ := TRT / 2 ^ (10 * (i * NR + c)) % 2 ^ 10
def rowOf (c : ℕ) : Row := fun j => ⟨c / Q ^ (j : ℕ) % Q, Nat.mod_lt _ (by decide)⟩

theorem chk0 : ∀ i < 200, ∀ c < NR, step (dec (0 + i)) (rowOf c) = (if tr (0 + i) c = 0 then none else some (dec (tr (0 + i) c - 1))) ∧
    tr (0 + i) c ≤ M := by
  decide +kernel

theorem chk1 : ∀ i < 200, ∀ c < NR, step (dec (200 + i)) (rowOf c) = (if tr (200 + i) c = 0 then none else some (dec (tr (200 + i) c - 1))) ∧
    tr (200 + i) c ≤ M := by
  decide +kernel

theorem chk2 : ∀ i < 200, ∀ c < NR, step (dec (400 + i)) (rowOf c) = (if tr (400 + i) c = 0 then none else some (dec (tr (400 + i) c - 1))) ∧
    tr (400 + i) c ≤ M := by
  decide +kernel

theorem chk3 : ∀ i < 7, ∀ c < NR, step (dec (600 + i)) (rowOf c) = (if tr (600 + i) c = 0 then none else some (dec (tr (600 + i) c - 1))) ∧
    tr (600 + i) c ≤ M := by
  decide +kernel

theorem chk : ∀ i < M, ∀ c < NR, step (dec i) (rowOf c) = (if tr i c = 0 then none else some (dec (tr i c - 1))) ∧
    tr i c ≤ M := by
  intro i hi
  have hi' : i < 607 := hi
  by_cases h0 : i < 200
  · have := chk0 (i - 0) (by omega); rwa [show 0 + (i - 0) = i by omega] at this
  by_cases h1 : i < 400
  · have := chk1 (i - 200) (by omega); rwa [show 200 + (i - 200) = i by omega] at this
  by_cases h2 : i < 600
  · have := chk2 (i - 400) (by omega); rwa [show 400 + (i - 400) = i by omega] at this
  have := chk3 (i - 600) (by omega); rwa [show 600 + (i - 600) = i by omega] at this

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


def TT : List ℕ := [0x1000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001000001, 0x400000200000400000200000400000200000400000200000400000200000100000100000400000200000200000100000400000200000200000200000400000200000100000200000400000200000100000100000400000200000100000200000100000400000200000100000200000100000200000700000700000300000300000100000200000100000300000300000200000200000400000200000200000200000400000200000200000400000200000200000200000200000200000400000400000200000100000100000100000200000100000400000200000200000200000200000100000100000700000300000700000300000300000300000200000400000400000400000200000200000100000200000100000100000200000200000100000100000200000100000200000200000200000200000400000400000400000400000200000200000100000200000300000300000200000400000400000400000400000400000200000200000400000400000700000700000300000300000700000700000700000700000100000100000100000100000200000300000200000100000100000100000100000300000200000200000300000500000300000200000200000100000100000200000100000100000300000300000100000100000100000100000300000200000200000200000200000500000300000300000300000100000200000200000400000400000200000200000400000200000400000400000100000200000200000100000200000300000300000300000100000100000200000200000200000100000200000200000400000400000400000400000200000200000200000200000400000400000700000300000700000300000300000700000700000700000700000100000100000200000200000400000200000200000200000400000400000100000200000100000200000200000100000200000200000200000100000400000400000200000200000200000200000400000400000100000200000100000100000300000300000200000200000400000400000400000200000400000200000700000700000700000700000100000200000100000100000100000100000300000300000300000100000100000200000200000100000100000100000200000200000300000200000300000300000100000100000100000100000100000200000200000200000300000200000200000200000200000500000500000500000500000500000200000100000100000100000100000100000100000100000100000200000200000200000300000200000200000200000300000300000100000100000200000200000200000200000200000300000200000500000500000500000500000500000100000100000200000200000200000400000400000200000100000100000200000200000200000100000100000300000300000200000200000100000200000200000400000200000400000200000400000400000200000200000400000200000400000400000400000400000200000200000700000700000700000700000100000100000100000100000400000200000100000100000100000100000200000200000400000200000200000200000100000100000400000400000100000100000400000400000200000200000100000100000100000200000200000200000200000200000200000400000400000400000100000100000200000100000200000200000200000200000100000200000200000200000300000200000400000200000100000300000200000200000700000300000700000500000300000100000200000200000100000200000400000400000200000200000300000300000300000500000500000500000100000100000200000100000100000400000200000100000200000200000200000100000100000300000300000300000400000200000400000200000200000200000400000200000100000500000700000700000300000300000200000300000200000500000500000500000100000200000100000100000100000100000200000200000200000400000100000400000100000200000200000200000400000200000400000200000200000400000200000400000400000400000100000400000100000100000100000100000100000700000200000200000200000100000100000200000700000700000400000200000200000100000100000500000700000700000700000300000300000300000300000200000100000700000200000200000100000100000400000100000b00000400000400000400000100000100000700000300000b00000b00000700000500000500000300000300000700000200000100000700000200000400000200000100000b00000500000300000b00000500000700000700000300000300000700000300000300000700000300000700000500000300000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b, 0xc00000400001100000800000c00000400001100000800000c00000400000200000200001100000800000400000200000c00000400000600000400000c00000400000200000600000c00000400000200000200001100000800000100000300000100000c00000400000100000300000200000300001a00002500000400000900000100000300000200000400000900000300000400001100000800000400000200000c00000400000400000c00000200000400000300000400000400000c00001000000300000100000200000100000300000100000c00000300000400000300000300000100000200001a00000400002500000900000400000900000300001100000900000c00000400000800000100000400000100000100000300000400000100000100000300000100000300000400000300000400000900000c00000c00001000000400000400000100000400000400000900000400000c00001000000c00000c00001000000300000400000c00001000001a00002500000400000900001a00002500001e00003100000100000100000100000100000200000400000200000200000100000100000200000900000400000400000300000e00000600000300000400000100000200000400000100000200000400000900000100000100000100000100000400000200000200000400000400000e00000400000300000600000100000400000400000c00001000000300000400000c00000300000c00001000000100000300000400000100000400000400000400000900000100000100000300000400000300000100000300000400000900000c00000c00001000000300000400000300000400000c00001000001a00000400002500000400000900001a00001e00002500003100000100000100000400000400001100000800000400000800001100001c00000100000300000100000300000400000100000400000300000300000100000900000c00000300000400000300000400000c00001000000200000400000100000200000400000900000400000800000c00001000000900000400000c00000800001a00001e00002500003100000100000400000100000200000100000200000700000700000900000200000200000400000800000100000100000200000200000200000400000200000700000900000100000100000200000100000200000200000300000600000400000200000200000400000400000b00000a00000e00001300001900000400000100000100000200000100000200000100000100000200000300000200000600000400000200000200000200000700000900000200000200000400000800000200000400000200000400000400000a00001300000e00000b00001900000100000200000400000800000400000c00001000000300000100000100000300000400000400000100000200000400000900000300000300000100000300000400000900000300000c00000400000c00001000000400000800001100000800001100001c00000900000c00000400000800001a00002500001e00003100000100000100000200000200000c00000800000100000100000100000200000400000800001100000400000800000300000100000100000900000c00000100000200000900000c00000400000800000100000100000200000300000200000600000400000600000800001100000c00001c00000100000200000300000100000200000500000600000300000100000500000600000200000900000300001100000200000200000400000200000400002200000700002f00000e00000f00000100000300000300000100000400000900000c00000500000600000300000400000600000b00000e00001900000100000100000400000100000200000c00000800000200000800000300000300000100000100000400000300000600000900000500000c00000400000600000200001100000300000200000e00002200002f00000700000f00000200000400000400000e00000b00001900000100000300000100000100000100000200000600000400000800000900000100000c00000200000200000300000600000900000400000c00000800000400001100000800000c00001100001c00000100000900000100000100000100000100000100001a00000300000200000200000100000100000300001400001a00001100000200000200000200000200001300001400001a00001e00000300000600000600000c00000200000100001a00000200000300000100000100000900000200003f00000c00000900000c00000200000300002200000700003100003f00002f00000a00000e00000900000f00001400000200000200001a00000200001100000300000200003100000a00000900003f00000e00002200002f00000700000f00001400000300000600001a00000600001e00001300000c00002600003100003700004700003100003f00004d00003700004d000047000079000079, 0x1c00000700003f00001c00001c00000700003f00001c00001c00000700000400000400003f00001c00000700000400001c00000900000d00000700001c00000900000400000d00001c00000700000400000400003f00001c00000100000400000100001c00000700000100000500000400000500004900007e00000600001100000100000500000400000600001100000500000700003f00001c00000700000300001c00000900000700001c00000300000900000400000700000700001c00003100000500000100000400000100000400000100001c00000400000700000500000500000100000400004900000600007e00001100000600001100000500003f00001000001c00000700001c00000100000700000100000100000400000700000100000100000400000100000400000700000400000700001000001c00001c00003100000700000700000100000700000600001100000700001c00003100001c00001c00003100000400000700001c00003100004900007e00000600001100004900007e0000600000da00000100000100000100000200000200000500000300000400000100000100000400001100000700000700000400001e00000b00000400000700000100000400000700000100000400000600001100000100000200000100000100000500000200000300000700000700001e00000600000400000b00000100000700000700001c00003100000400000700001c00000400001c00003100000100000400000700000100000700000600000600001100000100000100000400000700000400000100000400000700001000001c00001c00003100000400000700000400000700001c00003100004900000600007e00000600001100004900006000007e0000da00000100000100000700000700004c00002d00000700001c00003f00008e00000100000400000100000400000700000100000700000400000400000100001000001c00000400000700000400000700001c00003100000400000700000100000400000600001100000700001c00001c00003100001000000700001c00001c00004900006000007e0000da00000100000700000100000400000100000400000800000800001700000400000800000700001c00000100000200000400000200000300000500000300000800001700000200000100000400000100000400000300000500000d00000700000200000300000800000c00001000001100002400002500004f00000700000200000100000400000100000400000100000200000400000500000300000d00000500000300000200000300000800001700000400000800000700001c00000200000800000300000700000c00001100002500002400001000004f00000100000400000700001c00000700001c00003100000400000100000100000400000700000700000100000400000600001100000400000400000100000400000700001000000400001c00000700001c00003100000700001c00004c00002d00003f00008e00001000001c00000700001c00004900007e0000600000da00000100000100000400000800001c00001c00000100000100000100000400000700001c00004c00000c00002d00000400000100000100001000001c00000100000400001000001c00000700001c00000100000200000400000500000300000d00000700001400001c00003f00002100008e00000100000400000400000200000300000600001000000400000200000600001000000300001700000500003f00000300000800000700000300000c00008500000a0000e500002400003200000100000500000400000200000400001000002000000600001000000400000600000b00001000002400004f00000100000100000700000100000400001c00001c00000800001c00000400000500000100000200000600000400000b00001000000600002000000400001000000300003f0000050000080000240000850000e500000a00003200000300000700000c00002400001000004f00000100000400000100000200000100000400001400000700001c00001000000100001c00000400000300000500000d00001000000700001c00001c00000c00004c00002d00002100003f00008e00000100001000000100000100000100000100000100004900000500000200000300000100000200000500002c00004900003f00000200000300000400000800005000002c00004900006000000400000b0000120000390000020000010000490000030000050000010000020000100000020000f800002000001000002000000200000900008500000a0000980000f80000e500001100002400000d00003200002c00000200000400004900000300003f00000500000800009800001100000d0000f80000240000850000e500000a00003200002c00000400001200004900000b0000600000500000390000600000980000c30001080000980000f800014f0000c300014f0001080002d60002d6, 0x3700000b0000c000004d00003700000b0000c000004d00003700000b0000070000070000c000004d00000b00000700003a00001200001700000b00003a00001200000700001700003700000b0000070000070000c000004d00000100000500000100003700000b0000010000090000070000090000ab00015900000a00001d00000100000900000700000a00001d00000900000b0000c000004d00000b00000500003a00001200000b00003a00000500001200000500000b00000b00003700007900000900000100000700000100000500000100003700000500000b0000090000090000010000070000ab00000a00015900001d00000a00001d0000090000c000001900003700000b00004d00000100000b00000100000100000500000b00000100000100000500000100000500000b00000500000b00001900003700003700007900000b00000b00000100000b00000a00001d00000b00003700007900003700003700007900000500000b0000370000790000ab00015900000a00001d0000ab0001590001030002d600000100000100000100000400000200000700000500000700000100000100000700001d00000b00000b00000700003d00001500000500000b00000100000700000b00000100000700000a00001d00000100000400000100000100000700000200000500000b00000b00003d00000a00000700001500000100000b00000b00003700007900000500000b00003700000500003700007900000100000500000b00000100000b00000a00000a00001d00000100000100000500000b00000500000100000500000b00001900003700003700007900000500000b00000500000b0000370000790000ab00000a00015900000a00001d0000ab0001030001590002d600000100000100000b00000b00013d0000cd00000b00004d0000c000020100000100000500000100000500000b00000100000b00000500000500000100001900003700000500000b00000500000b00003700007900000700000b00000100000700000a00001d00000b00004d00003700007900001900000b00003700004d0000ab0001030001590002d600000100000b00000100000700000100000700000a00000a00002700000700001c00000b00004d00000100000400000700000200000500000700000500000a00002700000400000100000700000100000700000500000900001700001100000200000500000e00002300002000001c00004a0000440000b900000b00000400000100000700000100000700000100000400000700000900000500001700000700000500000200000500000a00002700000700001c00000b00004d00000200000e00000500001100002300001c00004400004a0000200000b900000100000700000b00004d00000b00003700007900000500000100000100000500000b00000b00000100000700000a00001d00000500000500000100000500000b00001900000500003700000b00003700007900000b00004d00013d0000cd0000c000020100001900003700000b00004d0000ab0001590001030002d600000100000100000700001c00003700004d00000100000100000100000700000b00004d00013d0000230000cd00000500000100000100001900003700000100000700001900003700000b00004d00000100000400000700000900000500001700000b00003800004d0000c000004f00020100000100000700000600000400000500000800001f00000600000400000800001f00000500002700000d0000c000000500001c0000110000050000230001b500001600035a00004a00008300000100000900000600000400000500001b00004600000800001f00000700000a00001500002000004a0000b900000100000100000b00000100000700003700004d00001c00004d00000600000900000100000400000a00000700001500001b00000800004600000500001f0000050000c000000d00001c00004a0001b500035a00001600008300000500001100002300004a0000200000b900000100000500000100000400000100000700003800000b00004d00001900000100003700000700000500000900001700001900000b00003700004d00002300013d0000cd00004f0000c00002010000010000190000010000010000010000010000020000ab00000900000200000500000100000400000d0000530000ab0000c000000200000500000700001c0001490000530000ab0001030000070000150000370000ee0000020000010000ab00000500000900000200000400001b0000030002f500004600001b0000460000030000170001b500001600018b0002f500035a00001c00004a0000150000830000530000020000070000ab0000050000c000000d00001c00018b00001c0000150002f500004a0001b500035a0000160000830000530000070000370000ab0000150001030001490000ee0000d100018b00024700033a00018b0002f500047000024700047000033a000b92000b92, 0x600000100001ef0000b00000600000100001ef0000b000006000001000000b00000b0001ef0000b000001000000b00007000002000002700001000007000002000000b00002700006000001000000b00000b0001ef0000b000000100000600000100006000001000000100001000000b00001000015f00033300001100003100000100001000000b0000110000310000100000100001ef0000b000001000000800007000002000001000007000000800002000000600001000001000006000010000001000000100000b00000100000600000100006000000600001000001000001000000100000b00015f0000110003330000310000110000310000100001ef0000240000600000100000b000000100001000000100000100000600001000000100000100000600000100000600001000000600001000002400006000006000010000001000001000000100001000001100003100001000006000010000006000006000010000000600001000006000010000015f00033300001100003100015f0003330002660007de00000100000100000100000700000200000b00000800000b00000100000100000b00003100001000001000000c00007500002500000600001000000100000b00001000000100000b00001100003100000100000700000100000100000b00000200000800001000001000007500001100000c00002500000100001000001000006000010000000600001000006000000600006000010000000100000600001000000100001000001100001100003100000100000100000600001000000600000100000600001000002400006000006000010000000600001000000600001000006000010000015f00001100033300001100003100015f0002660003330007de00000100000100001000001000047f0002c10000100000b00001ef0005dd00000100000600000100000600001000000100001000000600000600000100002400006000000600001000000600001000006000010000000b00001000000100000b0000110000310000100000b00000600001000000240000100000600000b000015f0002660003330007de00000100001000000100000b00000100000b00000e00000e00003b00000b00004d0000100000b000000100000700000b00000200000800000b00000800000e00003b00000700000100000b00000100000b00000800001000002700003000000200000800001600005800004900002f00008d00007f00018300001000000700000100000b00000100000b00000100000700000b00001000000800002700000b00000800000200000800000e00003b00000b00004d0000100000b000000200001600000800003000005800002f00007f00008d00004900018300000100000b0000100000b000001000006000010000000600000100000100000600001000001000000100000b0000110000310000060000060000010000060000100000240000060000600000100000600001000000100000b000047f0002c10001ef0005dd0000240000600000100000b000015f0003330002660007de00000100000100000b00004d0000600000b000000100000100000100000b0000100000b000047f0000580002c100000600000100000100002400006000000100000b0000240000600000100000b000000100000700000b0000100000080000270000100000840000b00001ef0000a80005dd00000100000b00000a00000700000800000c00003100000a00000700000c00003100000800003b0000290001ef00000800004d0000300000080000580004d9000039000a7200008d00012300000100001000000a00000700000700002e00008800000c00003100000c00001100002500004900008d00018300000100000100001000000100000b0000600000b000004d0000b000000a00001000000100000700001100000c00002500002e00000c0000880000070000310000080001ef00002900004d00008d0004d9000a7200003900012300000800003000005800008d00004900018300000100000600000100000700000100000b0000840000100000b000002400000100006000000b0000080000100000270000240000100000600000b000005800047f0002c10000a80001ef0005dd00000100002400000100000100000100000100000400015f00001000000200000800000100000700002900008d00015f0001ef00000200000800000b00004d0004a200008d00015f00026600000c00002500009000031000000200000100015f00000800001000000400000700002e0000050007bb00008800002e0000880000050000270004d900003900038c0007bb000a7200002f00008d00002600012300008d00000200000b00015f0000080001ef00002900004d00038c00002f0000260007bb00008d0004d9000a7200003900012300008d00000c00009000015f0000250002660004a200031000019900038c00060600092e00038c0007bb000cff000606000cff00092e002650002650, 0x9a00001600045e00016000009a00001600045e00016000009a00001600001000001000045e0001600000160000100000ce0000370000420000160000ce00003700001000004200009a00001600001000001000045e00016000000100000700000100009a00001600000100001b00001000001b00028c0006d100001c00005300000100001b00001000001c00005300001b00001600045e00016000001600000c0000ce0000370000160000ce00000c00003700000700001600001600009a0001e400001b00000100001000000100000700000100009a00000700001600001b00001b00000100001000028c00001c0006d100005300001c00005300001b00045e00003100009a00001600016000000100001600000100000100000700001600000100000100000700000100000700001600000700001600003100009a00009a0001e400001600001600000100001600001c00005300001600009a0001e400009a00009a0001e400000700001600009a0001e400028c0006d100001c00005300028c0006d100051f00132800000100000100000100000b00000200001200000c0000100000010000010000100000530000160000160000130000d600003f00000700001600000100001000001600000100001000001c00005300000100000b00000100000100001200000200000c0000160000160000d600001c00001300003f00000100001600001600009a0001e400000700001600009a00000700009a0001e400000100000700001600000100001600001c00001c00005300000100000100000700001600000700000100000700001600003100009a00009a0001e400000700001600000700001600009a0001e400028c00001c0006d100001c00005300028c00051f0006d1001328000001000001000016000016000e080007cc00001600016000045e000ed600000100000700000100000700001600000100001600000700000700000100003100009a00000700001600000700001600009a0001e400001000001600000100001000001c00005300001600016000009a0001e400003100001600009a00016000028c00051f0006d10013280000010000160000010000100000010000100000150000150000570000100000b000001600016000000100000b00001000000200000c00001200000c00001500005700000b00000100001000000100001000000c00001b00004200008100000200000c0000200000c00000a80000500000fa0000e600030700001600000b00000100001000000100001000000100000b00001000001b00000c00004200001200000c00000200000c0000150000570000100000b000001600016000000200002000000c0000810000c00000500000e60000fa0000a800030700000100001000001600016000001600009a0001e400000700000100000100000700001600001600000100001000001c00005300000700000700000100000700001600003100000700009a00001600009a0001e4000016000160000e080007cc00045e000ed600003100009a00001600016000028c0006d100051f0013280000010000010000100000b000009a000160000001000001000001000010000016000160000e080000c00007cc00000700000100000100003100009a00000100001000003100009a00001600016000000100000b00001000001b00000c00004200001600011000016000045e000144000ed600000100001000001100000b00000c00001300004900001100000b00001300004900000c00005700007600045e00000c0000b000008100000c0000c0000c31000090001c7b0000fa00025900000100001b00001100000b00000a00004f0000f300001300004900001300001c00003f0000a80000fa00030700000100000100001600000100001000009a0001600000b000016000001100001b00000100000b00001c00001300003f00004f0000130000f300000a00004900000c00045e0000760000b00000fa000c31001c7b00009000025900000c0000810000c00000fa0000a800030700000100000700000100000b00000100001000011000001600016000003100000100009a00001000000c00001b00004200003100001600009a0001600000c0000e080007cc00014400045e000ed600000100003100000100000100000100000100000700028c00001b00000200000c00000100000b0000760000de00028c00045e00000200000c0000100000b0000e600000de00028c00051f00001300003f00014400087400000200000100028c00000c00001b00000700000b00004f0000080012090000f300004f0000f300000800003b000c31000090000765001209001c7b0000500000fa0000420002590000de00000200001000028c00000c00045e0000760000b00007650000500000420012090000fa000c31001c7b0000900002590000de00001300014400028c00003f00051f000e600008740002e0000765000e640017f00007650012090021f5000e640021f50017f0006f22006f22, 0xe800001d0008e400027e0000e800001d0008e400027e0000e800001d0000160000160008e400027e00001d00001600016f00005d00006f00001d00016f00005d00001600006f0000e800001d0000160000160008e400027e0000010000080000010000e800001d00000100002b00001600002b000461000d5200002c00008b00000100002b00001600002c00008b00002b00001d0008e400027e00001d00001100016f00005d00001d00016f00001100005d00000800001d00001d0000e800034900002b0000010000160000010000080000010000e800000800001d00002b00002b00000100001600046100002c000d5200008b00002c00008b00002b0008e40000400000e800001d00027e00000100001d00000100000100000800001d00000100000100000800000100000800001d00000800001d0000400000e80000e800034900001d00001d00000100001d00002c00008b00001d0000e80003490000e80000e800034900000800001d0000e8000349000461000d5200002c00008b000461000d52000a09002a2d00000100000100000100001000000200001d00001100001600000100000100001600008b00001d00001d00001c00017b00006900000800001d00000100001600001d00000100001600002c00008b00000100001000000100000100001d00000200001100001d00001d00017b00002c00001c00006900000100001d00001d0000e800034900000800001d0000e80000080000e800034900000100000800001d00000100001d00002c00002c00008b00000100000100000800001d00000800000100000800001d0000400000e80000e800034900000800001d00000800001d0000e800034900046100002c000d5200002c00008b000461000a09000d52002a2d00000100000100001d00001d00266300133400001d00027e0008e40021a400000100000800000100000800001d00000100001d0000080000080000010000400000e800000800001d00000800001d0000e800034900001600001d00000100001600002c00008b00001d00027e0000e800034900004000001d0000e800027e000461000a09000d52002a2d00000100001d00000100001600000100001600002000002000008100001600016000001d00027e00000100001000001600000200001100001d00001100002000008100001000000100001600000100001600001100002b00006f00013600000200001100002c00017600016f0000870001a80001940005df00001d00001000000100001600000100001600000100001000001600002b00001100006f00001d00001100000200001100002000008100001600016000001d00027e00000200002c0000110001360001760000870001940001a800016f0005df00000100001600001d00027e00001d0000e800034900000800000100000100000800001d00001d00000100001600002c00008b00000800000800000100000800001d0000400000080000e800001d0000e800034900001d00027e0026630013340008e40021a40000400000e800001d00027e000461000d52000a09002a2d0000010000010000160001600000e800027e00000100000100000100001600001d00027e0026630001760013340000080000010000010000400000e80000010000160000400000e800001d00027e00000100001000001600002b00001100006f00001d0001fa00027e0008e40002410021a400000100001600001c00001000001100001e00006c00001c00001000001e00006c0000110000810001260008e4000011000160000136000011000176001bb200014d0045fd0001a80004a900000100002b00001c00001000000e00008600019e00001e00006c00001c00002c00006900016f0001a80005df00000100000100001d0000010000160000e800027e00016000027e00001c00002b00000100001000002c00001c00006900008600001e00019e00000e00006c0000110008e40001260001600001a8001bb20045fd00014d0004a90000110001360001760001a800016f0005df0000010000080000010000100000010000160001fa00001d00027e0000400000010000e800001600001100002b00006f00004000001d0000e800027e0001760026630013340002410008e40021a400000100004000000100000100000100000100000b00046100002b00000200001100000100001000012600014a0004610008e400000200001100001600016000272300014a000461000a0900001c00006900028600147800000200000100046100001100002b00000b00001000008600000c00268200019e00008600019e00000c000057001bb200014d000e3a0026820045fd0000870001a800006e0004a900014a0000020000160004610000110008e4000126000160000e3a00008700006e0026820001a8001bb20045fd00014d0004a900014a00001c000286000461000069000a090027230014780004d6000e3a001f8200399c000e3a0026820050d4001f820050d400399c012367012367, 0x14d0000250010ab00043100014d0000250010ab00043100014d00002500001d00001d0010ab00043100002500001d00027d00009a0000b700002500027d00009a00001d0000b700014d00002500001d00001d0010ab00043100000100000900000100014d00002500000100004100001d0000410007150018410000420000e300000100004100001d0000420000e30000410000250010ab00043100002500001700027d00009a00002500027d00001700009a00000900002500002500014d00055900004100000100001d00000100000900000100014d00000900002500004100004100000100001d0007150000420018410000e30000420000e30000410010ab00005100014d00002500043100000100002500000100000100000900002500000100000100000900000100000900002500000900002500005100014d00014d0005590000250000250000010000250000420000e300002500014d00055900014d00014d00055900000900002500014d0005590007150018410000420000e300071500184100125200559d00000100000100000100001600000200002d00001700001d00000100000100001d0000e300002500002500002700028e0000ab00000900002500000100001d00002500000100001d0000420000e300000100001600000100000100002d00000200001700002500002500028e0000420000270000ab00000100002500002500014d00055900000900002500014d00000900014d0005590000010000090000250000010000250000420000420000e300000100000100000900002500000900000100000900002500005100014d00014d00055900000900002500000900002500014d0005590007150000420018410000420000e300071500125200184100559d000001000001000025000025005e2d002a880000250004310010ab0045e900000100000900000100000900002500000100002500000900000900000100005100014d00000900002500000900002500014d00055900001d00002500000100001d0000420000e300002500043100014d00055900005100002500014d00043100071500125200184100559d00000100002500000100001d00000100001d0000300000300000c100001d00027e00002500043100000100001600001d00000200001700002d0000170000300000c100001600000100001d00000100001d0000170000410000b700029c00000200001700003a00029b0002eb0000de0002bc0002b3000b1100002500001600000100001d00000100001d00000100001600001d0000410000170000b700002d0000170000020000170000300000c100001d00027e00002500043100000200003a00001700029c00029b0000de0002b30002bc0002eb000b1100000100001d00002500043100002500014d00055900000900000100000100000900002500002500000100001d0000420000e300000900000900000100000900002500005100000900014d00002500014d000559000025000431005e2d002a880010ab0045e900005100014d00002500043100071500184100125200559d00000100000100001d00027e00014d00043100000100000100000100001d000025000431005e2d00029b002a8800000900000100000100005100014d00000100001d00005100014d00002500043100000100001600001d0000410000170000b70000250003660004310010ab0003c30045e900000100001d00002c00001600001700002e0000a100002c00001600002e0000a10000170000c10002860010ab00001700027e00029c00001700029b0039c80002bd009e090002bc0008f600000100004100002c0000160000130000dd0002ae00002e0000a10000270000420000ab0002eb0002bc000b1100000100000100002500000100001d00014d00043100027e00043100002c0000410000010000160000420000270000ab0000dd00002e0002ae0000130000a10000170010ab00028600027e0002bc0039c8009e090002bd0008f600001700029c00029b0002bc0002eb000b1100000100000900000100001600000100001d00036600002500043100005100000100014d00001d0000170000410000b700005100002500014d00043100029b005e2d002a880003c30010ab0045e90000010000510000010000010000010000010000100007150000410000020000170000010000160002860001d50007150010ab00000200001700001d00027e005fa30001d50007150012520000270000ab000495002cc90000020000010007150000170000410000100000160000dd000011004c830002ae0000dd0002ae0000110000810039c80002bd00199b004c83009e090000de0002bc0000b10008f60001d500000200001d0007150000170010ab00028600027e00199b0000de0000b1004c830002bc0039c8009e090002bd0008f60001d50000270004950007150000ab001252005fa3002cc90007b300199b0040000080ec00199b004c8300b20e00400000b20e0080ec02bf1702bf17, 0x1cc00002e001d3e0006a60001cc00002e001d3e0006a60001cc00002e000025000025001d3e0006a600002e0000250004350000f800012500002e0004350000f80000250001250001cc00002e000025000025001d3e0006a600000100000a0000010001cc00002e00000100005e00002500005e000ae70029a700005f00016700000100005e00002500005f00016700005e00002e001d3e0006a600002e00001e0004350000f800002e00043500001e0000f800000a00002e00002e0001cc00084400005e00000100002500000100000a0000010001cc00000a00002e00005e00005e000001000025000ae700005f0029a700016700005f00016700005e001d3e0000640001cc00002e0006a600000100002e00000100000100000a00002e00000100000100000a00000100000a00002e00000a00002e0000640001cc0001cc00084400002e00002e00000100002e00005f00016700002e0001cc0008440001cc0001cc00084400000a00002e0001cc000844000ae70029a700005f000167000ae70029a7001f8900a28100000100000100000100001d00000200004300001e00002500000100000100002500016700002e00002e00003400044c00010f00000a00002e00000100002500002e00000100002500005f00016700000100001d00000100000100004300000200001e00002e00002e00044c00005f00003400010f00000100002e00002e0001cc00084400000a00002e0001cc00000a0001cc00084400000100000a00002e00000100002e00005f00005f00016700000100000100000a00002e00000a00000100000a00002e0000640001cc0001cc00084400000a00002e00000a00002e0001cc000844000ae700005f0029a700005f000167000ae7001f890029a700a28100000100000100002e00002e00d32800569400002e0006a6001d3e00874500000100000a00000100000a00002e00000100002e00000a00000a0000010000640001cc00000a00002e00000a00002e0001cc00084400002500002e00000100002500005f00016700002e0006a60001cc00084400006400002e0001cc0006a6000ae7001f890029a700a28100000100002e00000100002500000100002500004600004600012100002500043100002e0006a600000100001d00002500000200001e00004300001e00004600012100001d00000100002500000100002500001e00005e00012500052100000200001e00004a00045600058a00016100046d00048000144900002e00001d00000100002500000100002500000100001d00002500005e00001e00012500004300001e00000200001e00004600012100002500043100002e0006a600000200004a00001e00052100045600016100048000046d00058a00144900000100002500002e0006a600002e0001cc00084400000a00000100000100000a00002e00002e00000100002500005f00016700000a00000a00000100000a00002e00006400000a0001cc00002e0001cc00084400002e0006a600d328005694001d3e0087450000640001cc00002e0006a6000ae70029a7001f8900a2810000010000010000250004310001cc0006a600000100000100000100002500002e0006a600d32800045600569400000a0000010000010000640001cc0000010000250000640001cc00002e0006a600000100001d00002500005e00001e00012500002e00057e0006a6001d3e0005f400874500000100002500004200001d00001e0000440000f100004200001d0000440000f100001e000121000504001d3e00001e00043100052100001e00045600703e00054e014c5e00046d0010b800000100005e00004200001d00001900016000045a0000440000f100003400005f00010f00058a00046d00144900000100000100002e0000010000250001cc0006a60004310006a600004200005e00000100001d00005f00003400010f00016000004400045a0000190000f100001e001d3e00050400043100046d00703e014c5e00054e0010b800001e00052100045600046d00058a00144900000100000a00000100001d00000100002500057e00002e0006a60000640000010001cc00002500001e00005e00012500006400002e0001cc0006a600045600d3280056940005f4001d3e008745000001000064000001000001000001000001000016000ae700005e00000200001e00000100001d000504000283000ae7001d3e00000200001e00002500043100d5c3000283000ae7001f8900003400010f0007bc005a57000002000001000ae700001e00005e00001600001d000160000017008f2500045a00016000045a0000170000c100703e00054e002b96008f25014c5e00016100046d0001140010b8000283000002000025000ae700001e001d3e000504000431002b96000161000114008f2500046d00703e014c5e00054e0010b80002830000340007bc000ae700010f001f8900d5c3005a57000bb7002b960079e5010e5d002b96008f25016f3b0079e5016f3b010e5d062c77062c77, 0x268000038003097000a10000268000038003097000a1000026800003800002e00002e003097000a1000003800002e0006eb0001830001c60000380006eb00018300002e0001c600026800003800002e00002e003097000a1000000100000b00000100026800003800000100008300002e00008300101e00441d00008400022500000100008300002e000084000225000083000038003097000a100000380000260006eb0001830000380006eb00002600018300000b000038000038000268000c4000008300000100002e00000100000b00000100026800000b00003800008300008300000100002e00101e00008400441d000225000084000225000083003097000079000268000038000a1000000100003800000100000100000b00003800000100000100000b00000100000b00003800000b000038000079000268000268000c40000038000038000001000038000084000225000038000268000c40000268000268000c4000000b000038000268000c4000101e00441d00008400022500101e00441d0033ac01238b00000100000100000100002500000200006000002600002e00000100000100002e0002250000380000380000430007090001a100000b00003800000100002e00003800000100002e0000840002250000010000250000010000010000600000020000260000380000380007090000840000430001a1000001000038000038000268000c4000000b00003800026800000b000268000c4000000100000b00003800000100003800008400008400022500000100000100000b00003800000b00000100000b000038000079000268000268000c4000000b00003800000b000038000268000c4000101e00008400441d00008400022500101e0033ac00441d01238b00000100000100003800003801b73800a483000038000a1000309700f69800000100000b00000100000b00003800000100003800000b00000b00000100007900026800000b00003800000b000038000268000c4000002e00003800000100002e000084000225000038000a10000268000c40000079000038000268000a1000101e0033ac00441d01238b00000100003800000100002e00000100002e0000630000630001ad00002e0006a6000038000a1000000100002500002e0000020000260000600000260000630001ad00002500000100002e00000100002e0000260000830001c600095a00000200002600005c0006d40009e100021e00070800074f00242100003800002500000100002e00000100002e00000100002500002e0000830000260001c60000600000260000020000260000630001ad00002e0006a6000038000a1000000200005c00002600095a0006d400021e00074f0007080009e100242100000100002e000038000a10000038000268000c4000000b00000100000100000b00003800003800000100002e00008400022500000b00000b00000100000b00003800007900000b000268000038000268000c40000038000a1001b73800a48300309700f698000079000268000038000a1000101e00441d0033ac01238b00000100000100002e0006a6000268000a1000000100000100000100002e000038000a1001b7380006d400a48300000b00000100000100007900026800000100002e000079000268000038000a1000000100002500002e0000830000260001c6000038000872000a1000309700090400f69800000100002e00005f00002500002600006100016700005f0000250000610001670000260001ad0009350030970000260006a600095a0000260006d400cd4c0009950291ca000708001e4000000100008300005f00002500002000021d0006ef0000610001670000430000840001a10009e100070800242100000100000100003800000100002e000268000a100006a6000a1000005f0000830000010000250000840000430001a100021d0000610006ef0000200001670000260030970009350006a600070800cd4c0291ca000995001e4000002600095a0006d40007080009e100242100000100000b00000100002500000100002e000872000038000a1000007900000100026800002e0000260000830001c6000079000038000268000a100006d401b73800a48300090400309700f69800000100007900000100000100000100000100001d00101e00008300000200002600000100002500093500035800101e00309700000200002600002e0006a601bb8e00035800101e0033ac0000430001a1000c5200aa7700000200000100101e00002600008300001d00002500021d00001e00fe6b0006ef00021d0006ef00001e00012100cd4c0009950046c900fe6b0291ca00021e0007080001a2001e4000035800000200002e00101e0000260030970009350006a60046c900021e0001a200fe6b00070800cd4c0291ca000995001e40000358000043000c5200101e0001a10033ac01bb8e00aa7700112a0046c900dbad02173e0046c900fe6b02cb8c00dbad02cb8c02173e0d0d790d0d79, 0x324000043004d2d000ea8000324000043004d2d000ea8000324000043000038000038004d2d000ea8000043000038000b0e0002490002a9000043000b0e0002490000380002a9000324000043000038000038004d2d000ea800000100000c0000010003240000430000010000b10000380000b1001709006ade0000b200032d0000010000b10000380000b200032d0000b1000043004d2d000ea800004300002f000b0e000249000043000b0e00002f00024900000c0000430000430003240011890000b100000100003800000100000c00000100032400000c0000430000b10000b10000010000380017090000b2006ade00032d0000b200032d0000b1004d2d000090000324000043000ea800000100004300000100000100000c00004300000100000100000c00000100000c00004300000c0000430000900003240003240011890000430000430000010000430000b200032d00004300032400118900032400032400118900000c000043000324001189001709006ade0000b200032d001709006ade00513601f29400000100000100000100002e00000200008500002f00003800000100000100003800032d000043000043000054000b3400026f00000c0000430000010000380000430000010000380000b200032d00000100002e00000100000100008500000200002f000043000043000b340000b200005400026f00000100004300004300032400118900000c00004300032400000c00032400118900000100000c0000430000010000430000b20000b200032d00000100000100000c00004300000c00000100000c00004300009000032400032400118900000c00004300000c0000430003240011890017090000b2006ade0000b200032d001709005136006ade01f29400000100000100004300004303599e01272f000043000ea8004d2d01ab7200000100000c00000100000c00004300000100004300000c00000c00000100009000032400000c00004300000c0000430003240011890000380000430000010000380000b200032d000043000ea8000324001189000090000043000324000ea8001709005136006ade01f294000001000043000001000038000001000038000088000088000273000038000a10000043000ea800000100002e00003800000200002f00008500002f00008800027300002e00000100003800000100003800002f0000b10002a900100900000200002f000070000a480010b2000325000af4000b8f003e7700004300002e00000100003800000100003800000100002e0000380000b100002f0002a900008500002f00000200002f000088000273000038000a10000043000ea800000200007000002f001009000a48000325000b8f000af40010b2003e77000001000038000043000ea800004300032400118900000c00000100000100000c0000430000430000010000380000b200032d00000c00000c00000100000c00004300009000000c000324000043000324001189000043000ea803599e01272f004d2d01ab72000090000324000043000ea8001709006ade00513601f294000001000001000038000a10000324000ea8000001000001000001000038000043000ea803599e000a4801272f00000c000001000001000090000324000001000038000090000324000043000ea800000100002e0000380000b100002f0002a9000043000c78000ea8004d2d000d2901ab7200000100003800008400002e00002f00008600021000008400002e00008600021000002f000273000fdb004d2d00002f000a1000100900002f000a480164cb00105404d327000af400350a0000010000b100008400002e000028000324000ad40000860002100000540000b200026f0010b2000af4003e77000001000001000043000001000038000324000ea8000a10000ea80000840000b100000100002e0000b200005400026f000324000086000ad400002800021000002f004d2d000fdb000a10000af40164cb04d32700105400350a00002f001009000a48000af40010b2003e7700000100000c00000100002e000001000038000c78000043000ea800009000000100032400003800002f0000b10002a9000090000043000324000ea8000a4803599e01272f000d29004d2d01ab720000010000900000010000010000010000010000250017090000b100000200002f00000100002e000fdb000458001709004d2d00000200002f000038000a1003607200045800170900513600005400026f0012ba01303300000200000100170900002f0000b100002500002e00032400002601b09c000ad4000324000ad40000260001ad0164cb001054006e7401b09c04d327000325000af400026800350a00045800000200003800170900002f004d2d000fdb000a10006e7400032500026801b09c000af40164cb04d32700105400350a0004580000540012ba00170900026f00513603607201303300185c006e7401797d03eefd006e7401b09c052eda01797d052eda03eefd1a278e1a278e, 0x40300004f0076020014ad00040300004f0076020014ad00040300004f0000430000430076020014ad00004f00004300112c00035a0003df00004f00112c00035a0000430003df00040300004f0000430000430076020014ad00000100000d00000100040300004f0000010000e90000430000e9001fff00a1d90000ea0004910000010000e90000430000ea0004910000e900004f0076020014ad00004f00003900112c00035a00004f00112c00003900035a00000d00004f00004f0004030018610000e900000100004300000100000d00000100040300000d00004f0000e90000e9000001000043001fff0000ea00a1d90004910000ea0004910000e90076020000a900040300004f0014ad00000100004f00000100000100000d00004f00000100000100000d00000100000d00004f00000d00004f0000a900040300040300186100004f00004f00000100004f0000ea00049100004f00040300186100040300040300186100000d00004f000403001861001fff00a1d90000ea000491001fff00a1d9007b2d0332480000010000010000010000380000020000b300003900004300000100000100004300049100004f00004f00006700115b00038900000d00004f00000100004300004f0000010000430000ea0004910000010000380000010000010000b300000200003900004f00004f00115b0000ea00006700038900000100004f00004f00040300186100000d00004f00040300000d00040300186100000100000d00004f00000100004f0000ea0000ea00049100000100000100000d00004f00000d00000100000d00004f0000a900040300040300186100000d00004f00000d00004f000403001861001fff0000ea00a1d90000ea000491001fff007b2d00a1d903324800000100000100004f00004f0632c501f89f00004f0014ad00760202c5b100000100000d00000100000d00004f00000100004f00000d00000d0000010000a900040300000d00004f00000d00004f00040300186100004300004f0000010000430000ea00049100004f0014ad0004030018610000a900004f0004030014ad001fff007b2d00a1d903324800000100004f0000010000430000010000430000b60000b6000383000043000ea800004f0014ad0000010000380000430000020000390000b30000390000b60003830000380000010000430000010000430000390000e90003df001a23000002000039000086000eeb001af20004880010b60011ce0068d100004f0000380000010000430000010000430000010000380000430000e90000390003df0000b30000390000020000390000b6000383000043000ea800004f0014ad000002000086000039001a23000eeb0004880011ce0010b6001af20068d100000100004300004f0014ad00004f00040300186100000d00000100000100000d00004f00004f0000010000430000ea00049100000d00000d00000100000d00004f0000a900000d00040300004f00040300186100004f0014ad0632c501f89f00760202c5b10000a900040300004f0014ad001fff00a1d9007b2d033248000001000001000043000ea80004030014ad00000100000100000100004300004f0014ad0632c5000eeb01f89f00000d0000010000010000a90004030000010000430000a900040300004f0014ad0000010000380000430000e90000390003df00004f0011cc0014ad00760200129f02c5b10000010000430000b20000380000390000b40002fb0000b20000380000b40002fb0000390003830019eb007602000039000ea8001a23000039000eeb02518f001a8008a7540010b6005a1d0000010000e90000b200003800003100048700108e0000b40002fb0000670000ea000389001af20010b60068d100000100000100004f0000010000430004030014ad000ea80014ad0000b20000e90000010000380000ea0000670003890004870000b400108e0000310002fb0000390076020019eb000ea80010b602518f08a754001a80005a1d000039001a23000eeb0010b6001af20068d100000100000d0000010000380000010000430011cc00004f0014ad0000a90000010004030000430000390000e90003df0000a900004f0004030014ad000eeb0632c501f89f00129f00760202c5b10000010000a900000100000100000100000100002e001fff0000e90000020000390000010000380019eb000587001fff007602000002000039000043000ea8063d0d000587001fff007b2d000067000389001b630205c8000002000001001fff0000390000e900002e00003800048700002f02c3c900108e00048700108e00002f00027302518f001a8000a68b02c3c908a7540004880010b6000375005a1d000587000002000043001fff0000390076020019eb000ea800a68b00048800037502c3c90010b602518f08a754001a80005a1d000587000067001b63001fff000389007b2d063d0d0205c80021a500a68b026e7d07130600a68b02c3c90933b1026e7d0933b107130631fc1631fc16, 0x50800005c00aeb1001c6400050800005c00aeb1001c6400050800005c00004f00004f00aeb1001c6400005c00004f0019f60004c800057b00005c0019f60004c800004f00057b00050800005c00004f00004f00aeb1001c6400000100000e00000100050800005c00000100012c00004f00012c002b5f00edc300012d00066500000100012c00004f00012d00066500012c00005c00aeb1001c6400005c0000440019f60004c800005c0019f60000440004c800000e00005c00005c00050800211000012c00000100004f00000100000e00000100050800000e00005c00012c00012c00000100004f002b5f00012d00edc300066500012d00066500012c00aeb10000c400050800005c001c6400000100005c00000100000100000e00005c00000100000100000e00000100000e00005c00000e00005c0000c400050800050800211000005c00005c00000100005c00012d00066500005c00050800211000050800050800211000000e00005c000508002110002b5f00edc300012d000665002b5f00edc300b5300510000000010000010000010000430000020000eb00004400004f00000100000100004f00066500005c00005c00007c001a2f00050100000e00005c00000100004f00005c00000100004f00012d0006650000010000430000010000010000eb00000200004400005c00005c001a2f00012d00007c00050100000100005c00005c00050800211000000e00005c00050800000e00050800211000000100000e00005c00000100005c00012d00012d00066500000100000100000e00005c00000e00000100000e00005c0000c400050800050800211000000e00005c00000e00005c000508002110002b5f00012d00edc300012d000665002b5f00b53000edc305100000000100000100005c00005c0af2f5033bb300005c001c6400aeb1046f4d00000100000e00000100000e00005c00000100005c00000e00000e0000010000c400050800000e00005c00000e00005c00050800211000004f00005c00000100004f00012d00066500005c001c640005080021100000c400005c000508001c64002b5f00b53000edc305100000000100005c00000100004f00000100004f0000ee0000ee0004ef00004f0014ad00005c001c6400000100004300004f0000020000440000eb0000440000ee0004ef00004300000100004f00000100004f00004400012c00057b0028d600000200004400009e0014fc0029cf00065b0018f5001abd00aacf00005c00004300000100004f00000100004f00000100004300004f00012c00004400057b0000eb0000440000020000440000ee0004ef00004f0014ad00005c001c6400000200009e0000440028d60014fc00065b001abd0018f50029cf00aacf00000100004f00005c001c6400005c00050800211000000e00000100000100000e00005c00005c00000100004f00012d00066500000e00000e00000100000e00005c0000c400000e00050800005c00050800211000005c001c640af2f5033bb300aeb1046f4d0000c400050800005c001c64002b5f00edc300b53005100000000100000100004f0014ad000508001c6400000100000100000100004f00005c001c640af2f50014fc033bb300000e0000010000010000c400050800000100004f0000c400050800005c001c6400000100004300004f00012c00004400057b00005c0018b0001c6400aeb10019a8046f4d00000100004f0000ea0000430000440000ec0004390000ea0000430000ec0004390000440004ef00289300aeb10000440014ad0028d60000440014fc03b6e70029470ee88a0018f500947900000100012c0000ea00004300003b00065a0018c40000ec00043900007c00012d0005010029cf0018f500aacf00000100000100005c00000100004f000508001c640014ad001c640000ea00012c00000100004300012d00007c00050100065a0000ec0018c400003b00043900004400aeb10028930014ad0018f503b6e70ee88a0029470094790000440028d60014fc0018f50029cf00aacf00000100000e00000100004300000100004f0018b000005c001c640000c400000100050800004f00004400012c00057b0000c400005c000508001c640014fc0af2f5033bb30019a800aeb1046f4d0000010000c4000001000001000001000001000038002b5f00012c0000020000440000010000430028930006e9002b5f00aeb100000200004400004f0014ad0b01e00006e9002b5f00b53000007c0005010026c8034e52000002000001002b5f00004400012c00003800004300065a000039045f7f0018c400065a0018c400003900038303b6e700294700f3c8045f7f0ee88a00065b0018f50004da0094790006e900000200004f002b5f00004400aeb10028930014ad00f3c800065b0004da045f7f0018f503b6e70ee88a0029470094790006e900007c0026c8002b5f00050100b5300b01e0034e52002d6500f3c803de580c398800f3c8045f7f0fb8b703de580fb8b70c39885b99025b9902, 0x63600006a00fb7c00261800063600006a00fb7c00261800063600006a00005c00005c00fb7c00261800006a00005c0026440006a700079200006a0026440006a700005c00079200063600006a00005c00005c00fb7c00261800000100000f00000100063600006a00000100017b00005c00017b00399001542900017c0008bf00000100017b00005c00017c0008bf00017b00006a00fb7c00261800006a0000500026440006a700006a0026440000500006a700000f00006a00006a000636002be400017b00000100005c00000100000f00000100063600000f00006a00017b00017b00000100005c00399000017c0154290008bf00017c0008bf00017b00fb7c0000e100063600006a00261800000100006a00000100000100000f00006a00000100000100000f00000100000f00006a00000f00006a0000e1000636000636002be400006a00006a00000100006a00017c0008bf00006a000636002be4000636000636002be400000f00006a000636002be400399001542900017c0008bf00399001542901038507c5ca00000100000100000100004f00000200012e00005000005c00000100000100005c0008bf00006a00006a0000930026880006eb00000f00006a00000100005c00006a00000100005c00017c0008bf00000100004f00000100000100012e00000200005000006a00006a00268800017c0000930006eb00000100006a00006a000636002be400000f00006a00063600000f000636002be400000100000f00006a00000100006a00017c00017c0008bf00000100000100000f00006a00000f00000100000f00006a0000e1000636000636002be400000f00006a00000f00006a000636002be400399000017c01542900017c0008bf00399001038501542907c5ca00000100000100006a00006a129440051dfe00006a00261800fb7c06de5200000100000f00000100000f00006a00000100006a00000f00000f0000010000e100063600000f00006a00000f00006a000636002be400005c00006a00000100005c00017c0008bf00006a002618000636002be40000e100006a00063600261800399001038501542907c5ca00000100006a00000100005c00000100005c0001310001310006cb00005c001c6400006a00261800000100004f00005c00000200005000012e0000500001310006cb00004f00000100005c00000100005c00005000017b000792003d8f0000020000500000b8001cc0003eb60008b400247e002734010eab00006a00004f00000100005c00000100005c00000100004f00005c00017b00005000079200012e0000500000020000500001310006cb00005c001c6400006a0026180000020000b8000050003d8f001cc00008b400273400247e003eb6010eab00000100005c00006a00261800006a000636002be400000f00000100000100000f00006a00006a00000100005c00017c0008bf00000f00000f00000100000f00006a0000e100000f00063600006a000636002be400006a002618129440051dfe00fb7c06de520000e100063600006a00261800399001542901038507c5ca00000100000100005c001c6400063600261800000100000100000100005c00006a002618129440001cc0051dfe00000f0000010000010000e100063600000100005c0000e100063600006a00261800000100004f00005c00017b00005000079200006a00216c00261800fb7c00228c06de5200000100005c00012d00004f00005000012f0005dd00012d00004f00012f0005dd0000500006cb003d4000fb7c000050001c64003d8f000050001cc005c243003e1618c96d00247e00ed9300000100017b00012d00004f0000460008b300244300012f0005dd00009300017c0006eb003eb600247e010eab00000100000100006a00000100005c000636002618001c6400261800012d00017b00000100004f00017c0000930006eb0008b300012f0024430000460005dd00005000fb7c003d40001c6400247e05c24318c96d003e1600ed93000050003d8f001cc000247e003eb6010eab00000100000f00000100004f00000100005c00216c00006a0026180000e100000100063600005c00005000017b0007920000e100006a000636002618001cc0129440051dfe00228c00fb7c06de520000010000e100000100000100000100000100004300399000017b00000200005000000100004f003d4000088200399000fb7c00000200005000005c001c6412a93c0008820039900103850000930006eb0035700537a600000200000100399000005000017b00004300004f0008b300004406b6a50024430008b30024430000440004ef05c243003e16015bbd06b6a518c96d0008b400247e0006aa00ed9300088200000200005c00399000005000fb7c003d40001c64015bbd0008b40006aa06b6a500247e05c24318c96d003e1600ed930008820000930035700039900006eb01038512a93c0537a6003c04015bbd05f6e2146374015bbd06b6a519f5cf05f6e219f5cf146374a1aea4a1aea4]

def tb (t i : ℕ) : ℕ := TT.getD t 0 / 2 ^ (24 * i) % 2 ^ 24

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
      X * (11 + 22 * X + 33 * X ^ 2 - 140 * X ^ 3 + 508 * X ^ 4 - 314 * X ^ 5 - 17 * X ^ 6 + 432 * X ^ 7 - 233 * X ^ 8 + 28 * X ^ 9 + 56 * X ^ 10 - 28 * X ^ 11 + 2 * X ^ 12) := by
  have v1 : (f 1 : ℚ) = 11 := by exact_mod_cast (hv 1 (by norm_num)).trans (by decide +kernel : tb 1 0 = 11)
  have v2 : (f 2 : ℚ) = 121 := by exact_mod_cast (hv 2 (by norm_num)).trans (by decide +kernel : tb 2 0 = 121)
  have v3 : (f 3 : ℚ) = 726 := by exact_mod_cast (hv 3 (by norm_num)).trans (by decide +kernel : tb 3 0 = 726)
  have v4 : (f 4 : ℚ) = 2962 := by exact_mod_cast (hv 4 (by norm_num)).trans (by decide +kernel : tb 4 0 = 2962)
  have v5 : (f 5 : ℚ) = 9808 := by exact_mod_cast (hv 5 (by norm_num)).trans (by decide +kernel : tb 5 0 = 9808)
  have v6 : (f 6 : ℚ) = 28450 := by exact_mod_cast (hv 6 (by norm_num)).trans (by decide +kernel : tb 6 0 = 28450)
  have v7 : (f 7 : ℚ) = 74599 := by exact_mod_cast (hv 7 (by norm_num)).trans (by decide +kernel : tb 7 0 = 74599)
  have v8 : (f 8 : ℚ) = 179991 := by exact_mod_cast (hv 8 (by norm_num)).trans (by decide +kernel : tb 8 0 = 179991)
  have v9 : (f 9 : ℚ) = 404599 := by exact_mod_cast (hv 9 (by norm_num)).trans (by decide +kernel : tb 9 0 = 404599)
  have v10 : (f 10 : ℚ) = 855417 := by exact_mod_cast (hv 10 (by norm_num)).trans (by decide +kernel : tb 10 0 = 855417)
  have v11 : (f 11 : ℚ) = 1714062 := by exact_mod_cast (hv 11 (by norm_num)).trans (by decide +kernel : tb 11 0 = 1714062)
  have v12 : (f 12 : ℚ) = 3275798 := by exact_mod_cast (hv 12 (by norm_num)).trans (by decide +kernel : tb 12 0 = 3275798)
  have v13 : (f 13 : ℚ) = 6002946 := by exact_mod_cast (hv 13 (by norm_num)).trans (by decide +kernel : tb 13 0 = 6002946)
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (f n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 9 = A - C 9 * (A * X ^ 1) + C 36 * (A * X ^ 2) - C 84 * (A * X ^ 3) + C 126 * (A * X ^ 4) - C 126 * (A * X ^ 5) + C 84 * (A * X ^ 6) - C 36 * (A * X ^ 7) + C 9 * (A * X ^ 8) - (A * X ^ 9) := by
    simp only [map_ofNat]; ring
  have e2 : (X * (11 + 22 * X + 33 * X ^ 2 - 140 * X ^ 3 + 508 * X ^ 4 - 314 * X ^ 5 - 17 * X ^ 6 + 432 * X ^ 7 - 233 * X ^ 8 + 28 * X ^ 9 + 56 * X ^ 10 - 28 * X ^ 11 + 2 * X ^ 12) : ℚ⟦X⟧) = X ^ 1 * C 11 + X ^ 2 * C 22 + X ^ 3 * C 33 - X ^ 4 * C 140 + X ^ 5 * C 508 - X ^ 6 * C 314 - X ^ 7 * C 17 + X ^ 8 * C 432 - X ^ 9 * C 233 + X ^ 10 * C 28 + X ^ 11 * C 56 - X ^ 12 * C 28 + X ^ 13 * C 2 := by
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
      X * (11 + 22 * X + 33 * X ^ 2 - 140 * X ^ 3 + 508 * X ^ 4 - 314 * X ^ 5 - 17 * X ^ 6 + 432 * X ^ 7 - 233 * X ^ 8 + 28 * X ^ 9 + 56 * X ^ 10 - 28 * X ^ 11 + 2 * X ^ 12) ∧
    ∀ n : ℕ, 13 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) :=
  ⟨gf_of a (fun n hn => recurrence n (by omega)) (fun n hn => a_tb n (by omega)), recurrence⟩

end OMA.S_oeis_a223640

theorem OMA.solution : type_of% @OMA.S_oeis_a223640.main :=
  OMA.S_oeis_a223640.solution_main
