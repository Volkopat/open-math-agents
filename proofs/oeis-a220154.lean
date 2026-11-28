import OMAStatements.S_oeis_a220154
import Mathlib

/-!
Proof of Barker's conjectures for OEIS A220154.

Reading the source array row by row as a word of letters (rows of the long direction), the
derived array is a sliding-window map of radius one, and the sorted words form a regular
language: adjacent letters are lexicographically ordered, and each pair of adjacent tracks
carries a three-valued lexicographic comparison status. The library below proves, for any such
window map, that the set of configurations (guessed next letter, last letter, statuses) realised
by an output prefix evolves by an explicit successor relation, and that an output word is a
derived word exactly when a configuration with no next letter is realised. A subset automaton
over configuration codes (`stT`, `nxT`, checked by `decide +kernel`) then turns the number of
derived words into a sum of state counts, which obey a linear recursion. The 3-th difference of
the count vector of every live state vanishes from length 5 on (checked on the table `vecT`
and propagated by linearity), which gives Barker's recurrence; the g.f. follows from the
recurrence and the first terms.
-/


namespace MinNbLib
open Finset

/-! ## Lexicographic order lemmas -/

theorem concat_lt {α : Type*} [LinearOrder α] (a b : α) :
    ∀ (l₁ l₂ : List α), l₁.length = l₂.length →
      (l₁ ++ [a] < l₂ ++ [b] ↔ l₁ < l₂ ∨ (l₁ = l₂ ∧ a < b))
  | [], [], _ => by simp [List.cons_lt_cons_iff]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: l₁, y :: l₂, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.cons_append, List.cons_lt_cons_iff, concat_lt a b l₁ l₂ h, List.cons.injEq]
    constructor
    · rintro (h1 | ⟨rfl, h2 | ⟨rfl, h3⟩⟩) <;> tauto
    · rintro ((h1 | ⟨rfl, h2⟩) | ⟨⟨rfl, rfl⟩, h3⟩) <;> tauto

/-- Three-valued comparison: 0 for less, 1 for equal, 2 for greater. -/
def cmp3 {α : Type*} [LinearOrder α] (a b : α) : Fin 3 :=
  if a < b then 0 else if a = b then 1 else 2

theorem cmp3_concat {α : Type*} [LinearOrder α] (a b : α) (l₁ l₂ : List α)
    (h : l₁.length = l₂.length) :
    cmp3 (l₁ ++ [a]) (l₂ ++ [b]) = if cmp3 l₁ l₂ = 1 then cmp3 a b else cmp3 l₁ l₂ := by
  have he : l₁ ++ [a] = l₂ ++ [b] ↔ l₁ = l₂ ∧ a = b := by
    constructor
    · intro h'; exact ⟨(List.append_inj h' h).1, by simpa using (List.append_inj h' h).2⟩
    · rintro ⟨rfl, rfl⟩; rfl
  unfold cmp3
  simp only [concat_lt a b l₁ l₂ h, he]
  by_cases h1 : l₁ < l₂
  · have : l₁ ≠ l₂ := ne_of_lt h1
    simp [h1, this]
  · by_cases h2 : l₁ = l₂
    · subst h2; simp
    · simp [h1, h2]

theorem cmp3_ne_two {α : Type*} [LinearOrder α] (a b : α) : cmp3 a b ≠ 2 ↔ a ≤ b := by
  unfold cmp3
  rcases lt_trichotomy a b with h | h | h
  · simp [h, h.le]
  · subst h; simp
  · simp [not_lt.2 h.le, ne_of_gt h, not_le.2 h]

theorem cmp3_ne_zero {α : Type*} [LinearOrder α] (a b : α) : cmp3 a b ≠ 0 ↔ b ≤ a := by
  unfold cmp3
  rcases lt_trichotomy a b with h | h | h
  · simp [h, not_le.2 h]
  · subst h; simp
  · simp [not_lt.2 h.le, ne_of_gt h, h.le]

/-- `rel d x y` : `x ≤ y` when `d`, else `y ≤ x`. -/
def rel {α : Type*} [LinearOrder α] (d : Bool) (x y : α) : Prop := if d then x ≤ y else y ≤ x

instance {α : Type*} [LinearOrder α] (d : Bool) (x y : α) : Decidable (rel d x y) := by
  unfold rel; split <;> infer_instance

/-- monotone when `d`, antitone otherwise -/
def ordB {α : Type*} [Preorder α] {n : ℕ} (d : Bool) (f : Fin n → α) : Prop :=
  if d then Monotone f else Antitone f

theorem ordB_iff {α : Type*} [LinearOrder α] {n : ℕ} (d : Bool) (f : Fin n → α) :
    ordB d f ↔ ∀ (i : ℕ) (h : i + 1 < n), rel d (f ⟨i, by omega⟩) (f ⟨i + 1, h⟩) := by
  rcases n with _ | n
  · simp only [ordB]; split <;> simp [Monotone, Antitone]
  · cases d
    · simp only [ordB, rel, Bool.false_eq_true, ↓reduceIte, Fin.antitone_iff_succ_le]
      constructor
      · intro h i hi; exact h ⟨i, by omega⟩
      · intro h i; exact h i.1 (by omega)
    · simp only [ordB, rel, ↓reduceIte, Fin.monotone_iff_le_succ]
      constructor
      · intro h i hi; exact h ⟨i, by omega⟩
      · intro h i; exact h i.1 (by omega)


/-! ## Words of letters -/

abbrev Ltr (w m : ℕ) := Fin w → Fin (m + 1)

variable {w m : ℕ}

def track {n : ℕ} (W : Fin n → Ltr w m) (s : Fin w) : List (Fin (m + 1)) :=
  List.ofFn (fun t => W t s)

def sortedW (dL dT : Bool) {n : ℕ} (W : Fin n → Ltr w m) : Prop :=
  ordB dL (fun t => List.ofFn (W t)) ∧ ordB dT (fun s => track W s)

def stW {n : ℕ} (W : Fin n → Ltr w m) (s : Fin w) : Fin 3 :=
  if h : s.1 + 1 < w then cmp3 (track W s) (track W ⟨s.1 + 1, h⟩) else 1

def upd (st : Fin w → Fin 3) (x : Ltr w m) (s : Fin w) : Fin 3 :=
  if h : s.1 + 1 < w then (if st s = 1 then cmp3 (x s) (x ⟨s.1 + 1, h⟩) else st s) else 1

def bad (dT : Bool) : Fin 3 := if dT then 2 else 0

def okSt (dT : Bool) (st : Fin w → Fin 3) : Prop := ∀ s : Fin w, s.1 + 1 < w → st s ≠ bad dT

instance (dT : Bool) (st : Fin w → Fin 3) : Decidable (okSt dT st) := by
  unfold okSt; infer_instance

def lastOpt {n : ℕ} (W : Fin n → Ltr w m) : Option (Ltr w m) :=
  if h : 0 < n then some (W ⟨n - 1, by omega⟩) else none

theorem snoc_lt {n : ℕ} (W : Fin n → Ltr w m) (x : Ltr w m) (k : ℕ) (hk : k < n) :
    (Fin.snoc W x : Fin (n + 1) → Ltr w m) ⟨k, by omega⟩ = W ⟨k, hk⟩ := by
  simp [Fin.snoc, hk]

theorem snoc_eq {n : ℕ} (W : Fin n → Ltr w m) (x : Ltr w m) :
    (Fin.snoc W x : Fin (n + 1) → Ltr w m) ⟨n, by omega⟩ = x := by
  simp [Fin.snoc]

theorem track_snoc {n : ℕ} (W : Fin n → Ltr w m) (x : Ltr w m) (s : Fin w) :
    track (Fin.snoc W x : Fin (n + 1) → Ltr w m) s = track W s ++ [x s] := by
  simp only [track, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]

theorem stW_snoc {n : ℕ} (W : Fin n → Ltr w m) (x : Ltr w m) :
    stW (Fin.snoc W x : Fin (n + 1) → Ltr w m) = upd (stW W) x := by
  funext s
  unfold stW upd
  split
  · rename_i h
    rw [track_snoc, track_snoc, cmp3_concat _ _ _ _ (by simp [track])]
    simp only [dif_pos h]
  · rfl

theorem stW_zero (W : Fin 0 → Ltr w m) : stW W = fun _ => 1 := by
  funext s; unfold stW; split
  · simp [track, cmp3]
  · rfl

theorem lastOpt_snoc {n : ℕ} (W : Fin n → Ltr w m) (x : Ltr w m) :
    lastOpt (Fin.snoc W x : Fin (n + 1) → Ltr w m) = some x := by
  simp only [lastOpt, Nat.zero_lt_succ, ↓reduceDIte, Nat.add_sub_cancel]
  rw [snoc_eq]

theorem lastOpt_zero (W : Fin 0 → Ltr w m) : lastOpt W = none := by simp [lastOpt]

theorem ordB_track_iff (dT : Bool) {n : ℕ} (W : Fin n → Ltr w m) :
    ordB dT (fun s => track W s) ↔ okSt dT (stW W) := by
  rw [ordB_iff]
  constructor
  · intro h s hs
    unfold stW bad
    rw [dif_pos hs]
    · have := h s.1 hs
      cases dT
      · simp only [rel, Bool.false_eq_true, ↓reduceIte] at this ⊢
        exact (cmp3_ne_zero _ _).2 this
      · simp only [rel, ↓reduceIte] at this ⊢
        exact (cmp3_ne_two _ _).2 this
  · intro h i hi
    have := h ⟨i, by omega⟩ hi
    simp only [stW, bad, hi, ↓reduceDIte] at this
    cases dT
    · simp only [rel, Bool.false_eq_true, ↓reduceIte] at this ⊢
      exact (cmp3_ne_zero _ _).1 this
    · simp only [rel, ↓reduceIte] at this ⊢
      exact (cmp3_ne_two _ _).1 this

theorem okSt_of_upd (dT : Bool) (st : Fin w → Fin 3) (x : Ltr w m) :
    okSt dT (upd st x) → okSt dT st := by
  intro h s hs
  have := h s hs
  unfold upd at this
  rw [dif_pos hs] at this
  split at this
  · rename_i h1; rw [h1]; cases dT <;> decide
  · exact this


theorem sortedW_snoc (dL dT : Bool) {n : ℕ} (W : Fin n → Ltr w m) (x : Ltr w m) :
    sortedW dL dT (Fin.snoc W x : Fin (n + 1) → Ltr w m) ↔
      sortedW dL dT W ∧ (∀ y, lastOpt W = some y → rel dL (List.ofFn y) (List.ofFn x)) ∧
        okSt dT (upd (stW W) x) := by
  unfold sortedW
  rw [ordB_track_iff, ordB_track_iff, stW_snoc, ordB_iff, ordB_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun i hi => ?_, okSt_of_upd _ _ _ h2⟩, fun y hy => ?_, h2⟩
    · have := h1 i (by omega)
      rwa [snoc_lt W x i (by omega), snoc_lt W x (i + 1) hi] at this
    · simp only [lastOpt] at hy
      split at hy
      · rename_i hn
        cases hy
        have := h1 (n - 1) (by omega)
        rw [snoc_lt W x (n - 1) (by omega)] at this
        have e : n - 1 + 1 = n := by omega
        simp only [e] at this
        rwa [snoc_eq] at this
      · cases hy
  · rintro ⟨⟨h1, _⟩, h3, h4⟩
    refine ⟨fun i hi => ?_, h4⟩
    by_cases hin : i + 1 < n
    · rw [snoc_lt W x i (by omega), snoc_lt W x (i + 1) hin]
      exact h1 i hin
    · have e : i + 1 = n := by omega
      subst e
      rw [snoc_lt W x i (by omega), snoc_eq]
      apply h3
      simp [lastOpt]

instance (dL dT : Bool) {n : ℕ} (W : Fin n → Ltr w m) : Decidable (sortedW dL dT W) := by
  unfold sortedW ordB; split <;> split <;> infer_instance

/-! ## Window outputs -/

def val (o : Option (Ltr w m)) (s : Fin w) : Fin (m + 1) :=
  match o with
  | none => ⊤
  | some y => y s

def pick (dd : Fin 3) (l : Option (Ltr w m)) (x : Ltr w m) (q : Option (Ltr w m)) :
    Option (Ltr w m) :=
  if dd.1 = 0 then l else if dd.1 = 1 then some x else q

section Window
variable (nbL : ℕ → ℕ → ℕ → ℕ → Prop) [∀ a b c d, Decidable (nbL a b c d)]

/-- Output letter at a position whose left, own and right letters are `l`, `x`, `q`. -/
def out (l : Option (Ltr w m)) (x : Ltr w m) (q : Option (Ltr w m)) : Ltr w m := fun s =>
  ((univ : Finset (Fin 3 × Fin w)).filter (fun p => nbL 1 s p.1 p.2)).inf
    (fun p => val (pick p.1 l x q) p.2)

def prevOf {n : ℕ} (W : Fin n → Ltr w m) (t : Fin n) : Option (Ltr w m) :=
  if h : t.1 = 0 then none else some (W ⟨t.1 - 1, by omega⟩)

def nextOf {n : ℕ} (q : Option (Ltr w m)) (W : Fin n → Ltr w m) (t : Fin n) :
    Option (Ltr w m) :=
  if h : t.1 + 1 < n then some (W ⟨t.1 + 1, h⟩) else q

/-- Window outputs of `W`, the letter after the end being `q`. -/
def Fs {n : ℕ} (q : Option (Ltr w m)) (W : Fin n → Ltr w m) : Fin n → Ltr w m :=
  fun t => out nbL (prevOf W t) (W t) (nextOf q W t)

/-- The neighbourhood minimum of `W` itself. -/
def Fmin {n : ℕ} (W : Fin n → Ltr w m) : Fin n → Ltr w m := fun t s =>
  ((univ : Finset (Fin n × Fin w)).filter (fun p => nbL t s p.1 p.2)).inf (fun p => W p.1 p.2)

theorem Fmin_eq (hnb : ∀ t s t' s', nbL t s t' s' ↔ (t' + 1 = t ∧ nbL 1 s 0 s') ∨
      (t' = t ∧ nbL 1 s 1 s') ∨ (t' = t + 1 ∧ nbL 1 s 2 s'))
    {n : ℕ} (W : Fin n → Ltr w m) : Fmin nbL W = Fs nbL none W := by
  funext t s
  simp only [Fmin, Fs, out]
  apply le_antisymm
  · apply Finset.le_inf
    rintro ⟨dd, s'⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [pick]
    fin_cases dd
    · simp only [Fin.zero_eta, Fin.isValue, Fin.val_zero, ↓reduceIte, prevOf]
      split
      · exact le_top
      · rename_i ht
        simp only [val]
        apply Finset.inf_le (b := ((⟨t.1 - 1, by omega⟩ : Fin n), s'))
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hnb]; left; exact ⟨by omega, hp⟩
    · simp only [Fin.mk_one, Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceIte, val]
      apply Finset.inf_le (b := (t, s'))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hnb]; right; left; exact ⟨rfl, hp⟩
    · simp only [Fin.reduceFinMk, Fin.isValue, Fin.val_two, OfNat.ofNat_ne_zero, ↓reduceIte,
        OfNat.ofNat_ne_one, nextOf]
      split
      · rename_i ht
        simp only [val]
        apply Finset.inf_le (b := ((⟨t.1 + 1, ht⟩ : Fin n), s'))
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hnb]; right; right; exact ⟨rfl, hp⟩
      · exact le_top
  · apply Finset.le_inf
    rintro ⟨t', s'⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [hnb] at hp
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := Finset.inf_le (f := fun p : Fin 3 × Fin w => val (pick p.1 (prevOf W t) (W t)
        (nextOf none W t)) p.2) (s := (univ.filter (fun p : Fin 3 × Fin w => nbL 1 s p.1 p.2)))
        (b := (0, s')) (by simp [h2])
      refine le_trans this (le_of_eq ?_)
      simp only [pick, Fin.isValue, Fin.val_zero, ↓reduceIte, prevOf]
      rw [dif_neg (by omega)]
      simp only [val]
      have e : (⟨t.1 - 1, by omega⟩ : Fin n) = t' := Fin.ext (by simp; omega)
      rw [e]
    · have := Finset.inf_le (f := fun p : Fin 3 × Fin w => val (pick p.1 (prevOf W t) (W t)
        (nextOf none W t)) p.2) (s := (univ.filter (fun p : Fin 3 × Fin w => nbL 1 s p.1 p.2)))
        (b := (1, s')) (by simp [h2])
      refine le_trans this (le_of_eq ?_)
      simp only [pick, Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceIte, val]
      have e : t = t' := Fin.ext h1.symm
      rw [e]
    · have := Finset.inf_le (f := fun p : Fin 3 × Fin w => val (pick p.1 (prevOf W t) (W t)
        (nextOf none W t)) p.2) (s := (univ.filter (fun p : Fin 3 × Fin w => nbL 1 s p.1 p.2)))
        (b := (2, s')) (by simp [h2])
      refine le_trans this (le_of_eq ?_)
      simp only [pick, Fin.isValue, Fin.val_two, OfNat.ofNat_ne_zero, ↓reduceIte,
        OfNat.ofNat_ne_one, nextOf]
      rw [dif_pos (by omega)]
      simp only [val]
      have e : (⟨t.1 + 1, by omega⟩ : Fin n) = t' := Fin.ext (by simp; omega)
      rw [e]

theorem Fs_snoc {n : ℕ} (q : Option (Ltr w m)) (W : Fin n → Ltr w m) (x : Ltr w m) :
    Fs nbL q (Fin.snoc W x : Fin (n + 1) → Ltr w m) =
      Fin.snoc (Fs nbL (some x) W) (out nbL (lastOpt W) x q) := by
  funext t
  refine Fin.lastCases ?_ (fun i => ?_) t
  · rw [Fin.snoc_last]
    simp only [Fs, Fin.snoc_last]
    congr 1
    · simp only [prevOf, Fin.val_last, lastOpt]
      by_cases hn : n = 0
      · subst hn; simp
      · rw [dif_neg hn, dif_pos (by omega), snoc_lt W x (n - 1) (by omega)]
    · simp [nextOf]
  · rw [Fin.snoc_castSucc]
    simp only [Fs, Fin.snoc_castSucc]
    congr 1
    · simp only [prevOf, Fin.val_castSucc]
      split
      · rfl
      · rw [snoc_lt W x (i.1 - 1) (by omega)]
    · simp only [nextOf, Fin.val_castSucc]
      by_cases hi : i.1 + 1 < n
      · rw [dif_pos (by omega), dif_pos hi, snoc_lt W x (i.1 + 1) hi]
      · rw [dif_pos (by omega), dif_neg hi]
        have e : i.1 + 1 = n := by omega
        simp only [e]; rw [snoc_eq]


/-! ## Configurations -/

/-- (guessed next letter, last letter, track statuses) -/
abbrev Cfg (w m : ℕ) := Option (Ltr w m) × Option (Ltr w m) × (Fin w → Fin 3)

variable (dL dT : Bool)

def sortedSO {n : ℕ} (W : Fin n → Ltr w m) (q : Option (Ltr w m)) : Prop :=
  sortedW dL dT W ∧ ∀ x, q = some x → sortedW dL dT (Fin.snoc W x : Fin (n + 1) → Ltr w m)

/-- `c` is realized by the output prefix `B`. -/
def Rz {n : ℕ} (B : Fin n → Ltr w m) (c : Cfg w m) : Prop :=
  ∃ W : Fin n → Ltr w m, sortedSO dL dT W c.1 ∧ stW W = c.2.2 ∧ lastOpt W = c.2.1 ∧
    Fs nbL c.1 W = B

def guard (x : Ltr w m) (st' : Fin w → Fin 3) (q' : Option (Ltr w m)) : Prop :=
  ∀ y, q' = some y → rel dL (List.ofFn x) (List.ofFn y) ∧ okSt dT (upd st' y)

def stepRel (c : Cfg w m) (b : Ltr w m) (c' : Cfg w m) : Prop :=
  ∃ x, c.1 = some x ∧ c'.2.1 = some x ∧ c'.2.2 = upd c.2.2 x ∧ out nbL c.2.1 x c'.1 = b ∧
    guard dL dT x c'.2.2 c'.1

theorem snoc_inj {n : ℕ} {B B' : Fin n → Ltr w m} {b b' : Ltr w m}
    (h : (Fin.snoc B b : Fin (n + 1) → Ltr w m) = Fin.snoc B' b') : B = B' ∧ b = b' := by
  constructor
  · have := congrArg Fin.init h; simpa only [Fin.init_snoc] using this
  · have := congrFun h (Fin.last n); simpa only [Fin.snoc_last] using this

theorem Rz_snoc {n : ℕ} (B : Fin n → Ltr w m) (b : Ltr w m) (c' : Cfg w m) :
    Rz nbL dL dT (Fin.snoc B b : Fin (n + 1) → Ltr w m) c' ↔
      ∃ c, Rz nbL dL dT B c ∧ stepRel nbL dL dT c b c' := by
  constructor
  · rintro ⟨W'', ⟨hs1, hs2⟩, hst, hl, hF⟩
    rw [← Fin.snoc_init_self W''] at hs1 hs2 hst hl hF
    set W := Fin.init W''
    set x := W'' (Fin.last n)
    rw [Fs_snoc] at hF
    obtain ⟨hB, hb⟩ := snoc_inj hF
    obtain ⟨hW, _, _⟩ := (sortedW_snoc dL dT W x).1 hs1
    refine ⟨(some x, lastOpt W, stW W), ⟨W, ⟨hW, ?_⟩, rfl, rfl, hB⟩, x, rfl, ?_, ?_, hb, ?_⟩
    · rintro x' ⟨⟩; exact hs1
    · rw [← hl, lastOpt_snoc]
    · rw [← hst, stW_snoc]
    · intro y hy
      obtain ⟨_, h2, h3⟩ := (sortedW_snoc dL dT _ y).1 (hs2 y hy)
      refine ⟨h2 x (lastOpt_snoc W x), ?_⟩
      rw [← hst]; exact h3
  · rintro ⟨c, ⟨W, ⟨hs1, hs2⟩, hst, hl, hF⟩, x, hx, h1, h2, h3, h4⟩
    refine ⟨Fin.snoc W x, ⟨hs2 x hx, fun y hy => ?_⟩, ?_, ?_, ?_⟩
    · rw [sortedW_snoc]
      obtain ⟨g1, g2⟩ := h4 y hy
      refine ⟨hs2 x hx, ?_, ?_⟩
      · intro y' hy'; rw [lastOpt_snoc] at hy'; cases hy'; exact g1
      · rw [stW_snoc, hst, ← h2]; exact g2
    · rw [stW_snoc, hst, h2]
    · rw [lastOpt_snoc, h1]
    · rw [Fs_snoc, ← hx, hF, hl, h3]

def guard0 (q : Option (Ltr w m)) : Prop := ∀ y, q = some y → okSt dT (upd (fun _ => 1) y)

theorem sortedW_zero (W : Fin 0 → Ltr w m) : sortedW dL dT W := by
  refine ⟨?_, ?_⟩
  · rw [ordB_iff]; intro i hi; omega
  · rw [ordB_track_iff, stW_zero]; intro s _; cases dT <;> simp [bad]

theorem Rz_zero (B : Fin 0 → Ltr w m) (c : Cfg w m) :
    Rz nbL dL dT B c ↔ c.2.1 = none ∧ c.2.2 = (fun _ => 1) ∧ guard0 dT c.1 := by
  constructor
  · rintro ⟨W, ⟨_, hs2⟩, hst, hl, _⟩
    refine ⟨by rw [← hl, lastOpt_zero], by rw [← hst, stW_zero], fun y hy => ?_⟩
    have := (sortedW_snoc dL dT W y).1 (hs2 y hy)
    rw [stW_zero] at this; exact this.2.2
  · rintro ⟨h1, h2, h3⟩
    refine ⟨B, ⟨sortedW_zero dL dT B, fun y hy => ?_⟩, by rw [stW_zero, h2], by rw [lastOpt_zero, h1],
      funext (fun i => i.elim0)⟩
    rw [sortedW_snoc]
    refine ⟨sortedW_zero dL dT B, ⟨(fun y' hy' => by rw [lastOpt_zero] at hy'; cases hy'), ?_⟩⟩
    rw [stW_zero]; exact h3 y hy

theorem image_iff (hnb : ∀ t s t' s', nbL t s t' s' ↔ (t' + 1 = t ∧ nbL 1 s 0 s') ∨
      (t' = t ∧ nbL 1 s 1 s') ∨ (t' = t + 1 ∧ nbL 1 s 2 s'))
    {n : ℕ} (B : Fin n → Ltr w m) :
    (∃ W, sortedW dL dT W ∧ Fmin nbL W = B) ↔ ∃ c, Rz nbL dL dT B c ∧ c.1 = none := by
  constructor
  · rintro ⟨W, hW, hF⟩
    refine ⟨(none, lastOpt W, stW W), ⟨W, ⟨hW, fun x hx => by cases hx⟩, rfl, rfl, ?_⟩, rfl⟩
    rw [← hF, Fmin_eq nbL hnb]
  · rintro ⟨c, ⟨W, ⟨hW, _⟩, _, _, hF⟩, hc⟩
    refine ⟨W, hW, ?_⟩
    rw [Fmin_eq nbL hnb, ← hc, hF]


end Window

/-! ## Codes -/

def dec (x : ℕ) : Ltr w m := fun s => ⟨x / (m + 1) ^ s.1 % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩

def enc (f : Ltr w m) : ℕ := ∑ i, (f i : ℕ) * (m + 1) ^ (i : ℕ)

theorem enc_eq (f : Ltr w m) : enc f = (finFunctionFinEquiv f : ℕ) := by
  rw [finFunctionFinEquiv_apply]; rfl

theorem dec_enc (f : Ltr w m) : dec (enc f) = f := by
  funext s
  apply Fin.ext
  have := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv f) s
  rw [Equiv.symm_apply_apply] at this
  simp only [dec, enc_eq]
  exact this.symm

theorem enc_lt (f : Ltr w m) : enc f < (m + 1) ^ w := by
  rw [enc_eq]; exact (finFunctionFinEquiv f).2

theorem enc_dec (x : ℕ) (hx : x < (m + 1) ^ w) : enc (dec x : Ltr w m) = x := by
  have h1 : (dec x : Ltr w m) = finFunctionFinEquiv.symm ⟨x, hx⟩ := by
    funext s; apply Fin.ext; rw [finFunctionFinEquiv_symm_apply_val]; rfl
  rw [h1, enc_eq, Equiv.apply_symm_apply]

def decS (z : ℕ) : Fin w → Fin 3 := fun s => ⟨z / 3 ^ s.1 % 3, Nat.mod_lt _ (by norm_num)⟩

def encS (st : Fin w → Fin 3) : ℕ := ∑ i, (st i : ℕ) * 3 ^ (i : ℕ)

theorem decS_encS (st : Fin w → Fin 3) : decS (encS st) = st := by
  funext s
  apply Fin.ext
  have := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv st) s
  rw [Equiv.symm_apply_apply] at this
  simp only [decS, encS]
  rw [this, finFunctionFinEquiv_apply]

def decO (x : ℕ) : Option (Ltr w m) := if x = 0 then none else some (dec (x - 1))

def encO : Option (Ltr w m) → ℕ
  | none => 0
  | some f => enc f + 1

theorem decO_encO (o : Option (Ltr w m)) : decO (encO o) = o := by
  cases o <;> simp [decO, encO, dec_enc]

theorem encO_lt (o : Option (Ltr w m)) : encO o < (m + 1) ^ w + 1 := by
  cases o <;> simp [encO, enc_lt]

variable (w m) in
abbrev KO : ℕ := (m + 1) ^ w + 1

def decC (c : ℕ) : Cfg w m :=
  (decO (c % KO w m), decO (c / KO w m % KO w m), decS (c / KO w m / KO w m))

variable (w m) in
def mkC (q l z : ℕ) : ℕ := q + KO w m * (l + KO w m * z)

theorem decC_mkC (q l z : ℕ) (hq : q < KO w m) (hl : l < KO w m) :
    (decC (mkC w m q l z) : Cfg w m) = (decO q, decO l, decS z) := by
  have hK : 0 < KO w m := by positivity
  simp only [decC, mkC]
  have e1 : (q + KO w m * (l + KO w m * z)) % KO w m = q := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq]
  have e2 : (q + KO w m * (l + KO w m * z)) / KO w m = l + KO w m * z := by
    rw [Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hq, zero_add]
  rw [e1, e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl, Nat.add_mul_div_left _ _ hK,
    Nat.div_eq_of_lt hl, zero_add]

theorem decO_ne_none {q : ℕ} : (decO q : Option (Ltr w m)) = none ↔ q = 0 := by
  unfold decO; split <;> simp_all

section CodeStep
variable (nbL : ℕ → ℕ → ℕ → ℕ → Prop) [∀ a b c d, Decidable (nbL a b c d)] (dL dT : Bool)

def guardB (x : Ltr w m) (st' : Fin w → Fin 3) (q' : ℕ) : Bool :=
  q' == 0 || (decide (rel dL (List.ofFn x) (List.ofFn (dec (q' - 1) : Ltr w m))) &&
    decide (okSt dT (upd st' (dec (q' - 1) : Ltr w m))))

theorem guardB_iff (x : Ltr w m) (st' : Fin w → Fin 3) (q' : ℕ) :
    guardB dL dT x st' q' = true ↔ guard dL dT x st' (decO q') := by
  unfold guardB guard decO
  by_cases h : q' = 0
  · simp [h]
  · simp [h]

variable (w m) in
/-- Code successors of configuration code `c` on output letter code `b`. -/
def succC (c b : ℕ) : List ℕ :=
  if c % KO w m = 0 then [] else
    ((List.range (KO w m)).filter (fun q' =>
      enc (out nbL (decO (c / KO w m % KO w m)) (dec (c % KO w m - 1) : Ltr w m) (decO q')) == b &&
      guardB dL dT (dec (c % KO w m - 1) : Ltr w m)
        (upd (decS (c / KO w m / KO w m)) (dec (c % KO w m - 1) : Ltr w m)) q')).map
      (fun q' => mkC w m q' (c % KO w m)
        (encS (upd (decS (c / KO w m / KO w m)) (dec (c % KO w m - 1) : Ltr w m))))

open Classical in
noncomputable def δ (b : Ltr w m) (S : Finset (Cfg w m)) : Finset (Cfg w m) :=
  univ.filter (fun c' => ∃ c ∈ S, stepRel nbL dL dT c b c')

theorem succC_spec (c b : ℕ) (hb : b < (m + 1) ^ w) (c' : Cfg w m) :
    stepRel nbL dL dT (decC c) (dec b) c' ↔ ∃ c₂ ∈ succC w m nbL dL dT c b, decC c₂ = c' := by
  obtain ⟨q', l', st'⟩ := c'
  have hq : c % KO w m < KO w m := Nat.mod_lt _ (by positivity)
  simp only [stepRel, decC, succC]
  by_cases h0 : c % KO w m = 0
  · simp [h0, decO]
  · simp only [h0, ↓reduceIte, List.mem_map, List.mem_filter, List.mem_range, Bool.and_eq_true,
      beq_iff_eq, guardB_iff]
    have hd : (decO (c % KO w m) : Option (Ltr w m)) = some (dec (c % KO w m - 1)) := by
      simp [decO, h0]
    rw [hd]
    constructor
    · rintro ⟨x, ⟨⟩, rfl, rfl, h3, h4⟩
      refine ⟨mkC w m (encO q') (c % KO w m) (encS (upd (decS (c / KO w m / KO w m))
        (dec (c % KO w m - 1)))), ⟨encO q', ⟨encO_lt q', ?_, ?_⟩, rfl⟩, ?_⟩
      · rw [decO_encO, h3, enc_dec b hb]
      · rw [decO_encO]; exact h4
      · rw [← decC, decC_mkC _ _ _ (encO_lt q') hq, decO_encO, hd, decS_encS]
    · rintro ⟨c₂, ⟨q₂, ⟨hq₂, h3, h4⟩, rfl⟩, he⟩
      rw [← decC, decC_mkC _ _ _ hq₂ hq, hd, decS_encS] at he
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      refine ⟨_, rfl, rfl, rfl, ?_, h4⟩
      rw [← h3, dec_enc]

theorem δ_code (L : List ℕ) (b : ℕ) (hb : b < (m + 1) ^ w) :
    δ nbL dL dT (dec b) ((L.map (fun c => (decC c : Cfg w m))).toFinset) =
      ((L.flatMap (fun c => succC w m nbL dL dT c b)).map (fun c => (decC c : Cfg w m))).toFinset := by
  ext c'
  simp only [δ, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset, List.mem_map,
    List.mem_flatMap]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, hs⟩
    obtain ⟨c₂, h1, h2⟩ := (succC_spec nbL dL dT c b hb c').1 hs
    exact ⟨c₂, ⟨c, hc, h1⟩, h2⟩
  · rintro ⟨c₂, ⟨c, hc, h1⟩, h2⟩
    exact ⟨decC c, ⟨c, hc, rfl⟩, (succC_spec nbL dL dT c b hb c').2 ⟨c₂, h1, h2⟩⟩


end CodeStep

/-! ## Bit masks -/

def maskOf (L : List ℕ) : ℕ := L.foldr (fun c acc => acc ||| (1 <<< c)) 0

theorem testBit_maskOf (L : List ℕ) (j : ℕ) : (maskOf L).testBit j = true ↔ j ∈ L := by
  induction L with
  | nil => simp [maskOf]
  | cons c L ih =>
    simp only [maskOf, List.foldr_cons] at ih ⊢
    rw [Nat.testBit_or, Bool.or_eq_true, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
    simp only [decide_eq_true_eq, List.mem_cons]
    tauto

theorem mem_iff_of_mask {L₁ L₂ : List ℕ} (h : maskOf L₁ = maskOf L₂) (j : ℕ) :
    j ∈ L₁ ↔ j ∈ L₂ := by
  rw [← testBit_maskOf, ← testBit_maskOf, h]

theorem toFinset_map_of_mask {α : Type*} [DecidableEq α] (f : ℕ → α) {L₁ L₂ : List ℕ}
    (h : maskOf L₁ = maskOf L₂) : (L₁.map f).toFinset = (L₂.map f).toFinset := by
  ext a; simp only [List.mem_toFinset, List.mem_map, mem_iff_of_mask h]

/-! ## The automaton tables -/

section DFA
variable (nbL : ℕ → ℕ → ℕ → ℕ → Prop) [∀ a b c d, Decidable (nbL a b c d)] (dL dT : Bool)
variable (stT nxT : List (List ℕ)) (D : ℕ)

variable (w m) in
def SD (d : ℕ) : Finset (Cfg w m) := ((stT.getD d []).map (fun c => (decC c : Cfg w m))).toFinset

def nextD (d b : ℕ) : ℕ := (nxT.getD d []).getD b 0

variable (w m) in
def initC : List ℕ :=
  ((List.range (KO w m)).filter (fun q => q == 0 ||
    decide (okSt dT (upd (fun _ => 1) (dec (q - 1) : Ltr w m))))).map
    (fun q => mkC w m q 0 (encS (fun _ : Fin w => (1 : Fin 3))))

variable (w m) in
def rowOK (d : ℕ) : Bool :=
  (List.range ((m + 1) ^ w)).all (fun b =>
    decide (nextD nxT d b < D) &&
    maskOf ((stT.getD d []).flatMap (fun c => succC w m nbL dL dT c b)) ==
      maskOf (stT.getD (nextD nxT d b) []))

variable (w m) in
def checkT : Bool :=
  maskOf (initC w m dT) == maskOf (stT.getD 0 []) && decide (0 < D) &&
  (List.range D).all (fun d => rowOK w m nbL dL dT stT nxT D d)

variable (w m) in
def rowsOK (lo len : ℕ) : Bool :=
  (List.range' lo len).all (fun d => rowOK w m nbL dL dT stT nxT D d)

variable {nbL dL dT stT nxT D} in
theorem rowsOK_spec {lo len : ℕ} (h : rowsOK w m nbL dL dT stT nxT D lo len = true) (d : ℕ)
    (h1 : lo ≤ d) (h2 : d < lo + len) : rowOK w m nbL dL dT stT nxT D d = true := by
  simp only [rowsOK, List.all_eq_true, List.mem_range'] at h
  exact h d ⟨d - lo, by omega, by omega⟩

theorem all_range'_spec {p : ℕ → Bool} {lo len : ℕ} (h : (List.range' lo len).all p = true)
    (d : ℕ) (h1 : lo ≤ d) (h2 : d < lo + len) : p d = true := by
  simp only [List.all_eq_true, List.mem_range'] at h
  exact h d ⟨d - lo, by omega, by omega⟩

variable {nbL dL dT stT nxT D} in
theorem checkT_of
    (h0 : (maskOf (initC w m dT) == maskOf (stT.getD 0 []) && decide (0 < D)) = true)
    (hr : ∀ d < D, rowOK w m nbL dL dT stT nxT D d = true) :
    checkT w m nbL dL dT stT nxT D = true := by
  simp only [checkT, h0, Bool.true_and, List.all_eq_true, List.mem_range]
  exact hr

variable (w m) in
def run : {n : ℕ} → (Fin n → Ltr w m) → ℕ
  | 0, _ => 0
  | n + 1, B => nextD nxT (run (Fin.init B)) (enc (B (Fin.last n)))

theorem run_snoc {n : ℕ} (B : Fin n → Ltr w m) (x : Ltr w m) :
    run w m nxT (Fin.snoc B x : Fin (n + 1) → Ltr w m) = nextD nxT (run w m nxT B) (enc x) := by
  simp only [run, Fin.init_snoc, Fin.snoc_last]

variable {nbL dL dT stT nxT D}

theorem checkT_spec (hT : checkT w m nbL dL dT stT nxT D = true) :
    maskOf (initC w m dT) = maskOf (stT.getD 0 []) ∧ 0 < D ∧
    ∀ d < D, ∀ b < (m + 1) ^ w, nextD nxT d b < D ∧
      maskOf ((stT.getD d []).flatMap (fun c => succC w m nbL dL dT c b)) =
        maskOf (stT.getD (nextD nxT d b) []) := by
  simp only [checkT, rowOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hT
  obtain ⟨⟨h1, h2⟩, h3⟩ := hT
  exact ⟨h1, h2, fun d hd b hb => h3 d hd b hb⟩

open Classical in
theorem real_run (hT : checkT w m nbL dL dT stT nxT D = true) :
    ∀ {n : ℕ} (B : Fin n → Ltr w m),
      run w m nxT B < D ∧ univ.filter (Rz nbL dL dT B) = SD w m stT (run w m nxT B)
  | 0, B => by
    obtain ⟨h1, h2, _⟩ := checkT_spec hT
    refine ⟨h2, ?_⟩
    simp only [run, SD]
    rw [← toFinset_map_of_mask _ h1]
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Rz_zero, List.mem_toFinset,
      List.mem_map, initC, List.mem_filter, List.mem_range, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq]
    obtain ⟨q, l, st⟩ := c
    constructor
    · rintro ⟨rfl, rfl, hg⟩
      refine ⟨mkC w m (encO q) 0 (encS (fun _ : Fin w => (1 : Fin 3))),
        ⟨encO q, ⟨encO_lt q, ?_⟩, rfl⟩, ?_⟩
      · cases q with
        | none => left; rfl
        | some y =>
          right
          simp only [encO, Nat.add_sub_cancel, dec_enc]
          exact hg y rfl
      · rw [decC_mkC _ _ _ (encO_lt q) (by positivity), decO_encO, decS_encS]; rfl
    · rintro ⟨c₂, ⟨q₂, ⟨hq, hg⟩, rfl⟩, he⟩
      rw [decC_mkC _ _ _ hq (by positivity), decS_encS] at he
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      refine ⟨by simp [decO], rfl, fun y hy => ?_⟩
      rcases hg with hg | hg
      · subst hg; simp [decO] at hy
      · have hq0 : q₂ ≠ 0 := by rintro rfl; simp [decO] at hy
        simp only [decO, hq0, ↓reduceIte, Option.some.injEq] at hy
        rw [← hy]; exact hg
  | n + 1, B => by
    obtain ⟨_, _, h3⟩ := checkT_spec hT
    obtain ⟨ih1, ih2⟩ := real_run hT (Fin.init B)
    have hB : B = Fin.snoc (Fin.init B) (B (Fin.last n)) := (Fin.snoc_init_self B).symm
    have hb := enc_lt (B (Fin.last n))
    obtain ⟨g1, g2⟩ := h3 _ ih1 _ hb
    have hrun : run w m nxT B = nextD nxT (run w m nxT (Fin.init B)) (enc (B (Fin.last n))) := rfl
    refine ⟨by rw [hrun]; exact g1, ?_⟩
    rw [hrun, SD, ← toFinset_map_of_mask _ g2, ← δ_code nbL dL dT _ _ hb, dec_enc, ← SD, ← ih2]
    ext c'
    conv_lhs => rw [hB]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Rz_snoc, δ]


variable (w m stT) in
def accB (d : ℕ) : Bool := (stT.getD d []).any (fun c => c % KO w m == 0)

variable (w m nxT) in
/-- Number of output words of length `n` whose run ends in state `d`. -/
def NC (n d : ℕ) : ℕ := (univ.filter (fun B : Fin n → Ltr w m => run w m nxT B = d)).card

variable (w m nbL dL dT) in
/-- Number of distinct neighbourhood-minimum words of sorted words of length `n`. -/
def AC (n : ℕ) : ℕ := ((univ.filter (fun W : Fin n → Ltr w m => sortedW dL dT W)).image
  (Fmin nbL)).card

open Classical in
theorem AC_eq (hnb : ∀ t s t' s', nbL t s t' s' ↔ (t' + 1 = t ∧ nbL 1 s 0 s') ∨
      (t' = t ∧ nbL 1 s 1 s') ∨ (t' = t + 1 ∧ nbL 1 s 2 s'))
    (hT : checkT w m nbL dL dT stT nxT D = true) (n : ℕ) :
    AC w m nbL dL dT n = ∑ d ∈ range D, if accB w m stT d then NC w m nxT n d else 0 := by
  have himg : (univ.filter (fun W : Fin n → Ltr w m => sortedW dL dT W)).image (Fmin nbL) =
      univ.filter (fun B : Fin n → Ltr w m => accB w m stT (run w m nxT B) = true) := by
    ext B
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [image_iff nbL dL dT hnb B]
    obtain ⟨_, h2⟩ := real_run hT B
    constructor
    · rintro ⟨c, hc, hc1⟩
      have : c ∈ univ.filter (Rz nbL dL dT B) := by simp [hc]
      rw [h2, SD] at this
      simp only [List.mem_toFinset, List.mem_map] at this
      obtain ⟨c₀, hc₀, rfl⟩ := this
      simp only [accB, List.any_eq_true, beq_iff_eq]
      refine ⟨c₀, hc₀, ?_⟩
      simp only [decC] at hc1
      exact decO_ne_none.1 hc1
    · intro h
      simp only [accB, List.any_eq_true, beq_iff_eq] at h
      obtain ⟨c₀, hc₀, h0⟩ := h
      have : (decC c₀ : Cfg w m) ∈ univ.filter (Rz nbL dL dT B) := by
        rw [h2, SD]; simp only [List.mem_toFinset, List.mem_map]; exact ⟨c₀, hc₀, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact ⟨_, this, by simp [decC, h0, decO]⟩
  unfold AC
  rw [himg, Finset.card_eq_sum_card_fiberwise (f := fun B => run w m nxT B) (t := range D)]
  · apply Finset.sum_congr rfl
    intro d _
    unfold NC
    split
    · congr 1; ext B
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨by rw [h]; assumption, h⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro B hB h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB
      rw [h] at hB; simp_all
  · intro B _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact (real_run hT B).1

theorem sum_enc (g : ℕ → ℕ) :
    ∑ x : Ltr w m, g (enc x) = ∑ b ∈ range ((m + 1) ^ w), g b := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [enc_eq]
  exact Fintype.sum_equiv finFunctionFinEquiv _ _ (fun _ => rfl)

theorem NC_zero (d : ℕ) : NC w m nxT 0 d = if d = 0 then 1 else 0 := by
  unfold NC
  split
  · rename_i h; subst h
    rw [Finset.filter_true_of_mem]
    · simp
    · intro B _; rfl
  · rename_i h
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro B _; exact fun h' => h h'.symm

theorem NC_succ (hT : checkT w m nbL dL dT stT nxT D = true) (n d' : ℕ) :
    NC w m nxT (n + 1) d' = ∑ d ∈ range D, ∑ b ∈ range ((m + 1) ^ w),
      if nextD nxT d b = d' then NC w m nxT n d else 0 := by
  unfold NC
  rw [Finset.card_filter, ← (Fin.snocEquiv (fun _ => Ltr w m)).sum_comp, Fintype.sum_prod_type]
  have hs : ∀ x (y : Fin n → Ltr w m),
      (Fin.snocEquiv (fun _ => Ltr w m)) (x, y) = Fin.snoc y x := fun _ _ => rfl
  simp only [hs, run_snoc]
  have key : ∀ b, ∑ y : Fin n → Ltr w m, (if nextD nxT (run w m nxT y) b = d' then 1 else 0) =
      ∑ d ∈ range D, if nextD nxT d b = d' then
        (univ.filter (fun B : Fin n → Ltr w m => run w m nxT B = d)).card else 0 := by
    intro b
    rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := range D)
      (g := fun y => run w m nxT y) (fun y _ => by simpa using (real_run hT y).1)]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_congr rfl (g := fun _ => if nextD nxT d b = d' then 1 else 0)
      (fun y hy => by simp only [Finset.mem_filter] at hy; rw [hy.2])]
    rw [Finset.sum_const, smul_eq_mul]
    split <;> simp
  rw [Finset.sum_congr rfl (fun x _ => key (enc x)), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  exact sum_enc (fun b => if nextD nxT d b = d' then
    (univ.filter (fun B : Fin n → Ltr w m => run w m nxT B = d)).card else 0)


/-! ## Count vectors and the annihilation certificate -/

variable (w m nxT D) in
def stepV (v : List ℕ) : List ℕ :=
  (List.range D).map (fun d' => ∑ d ∈ range D, ∑ b ∈ range ((m + 1) ^ w),
    if nextD nxT d b = d' then v.getD d 0 else 0)

variable (w m nxT D) in
def stepOK (vecT : List (List ℕ)) (k : ℕ) : Bool :=
  vecT.getD (k + 1) [] == stepV w m nxT D (vecT.getD k [])

variable (w m nxT D) in
def checkV (vecT : List (List ℕ)) : Bool :=
  vecT.getD 0 [] == (List.range D).map (fun d => if d = 0 then 1 else 0) &&
  (List.range (vecT.length - 1)).all (fun k => stepOK w m nxT D vecT k)

theorem checkV_of (vecT : List (List ℕ))
    (h0 : (vecT.getD 0 [] == (List.range D).map (fun d => if d = 0 then 1 else 0)) = true)
    (hs : ∀ k < vecT.length - 1, stepOK w m nxT D vecT k = true) :
    checkV w m nxT D vecT = true := by
  simp only [checkV, h0, Bool.true_and, List.all_eq_true, List.mem_range]
  exact hs

theorem getD_map_range (f : ℕ → ℕ) (D d : ℕ) (hd : d < D) :
    ((List.range D).map f).getD d 0 = f d := by
  rw [List.getD_eq_getElem _ _ (by simpa using hd)]
  simp

theorem vec_spec (hT : checkT w m nbL dL dT stT nxT D = true) (vecT : List (List ℕ))
    (hV : checkV w m nxT D vecT = true) :
    ∀ k < vecT.length, ∀ d < D, (vecT.getD k []).getD d 0 = NC w m nxT k d := by
  simp only [checkV, stepOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hV
  obtain ⟨h0, hs⟩ := hV
  intro k
  induction k with
  | zero =>
    intro _ d hd
    rw [h0, getD_map_range _ _ _ hd, NC_zero]
  | succ k ih =>
    intro hk d' hd'
    rw [hs k (by omega), stepV, getD_map_range _ _ _ hd', NC_succ hT]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro b _
    rw [ih (by omega) d (by simpa using hd)]

variable (stT) in
def liveB (d : ℕ) : Bool := !(stT.getD d []).isEmpty

variable (w m stT nxT D) in
def checkLive : Bool :=
  (List.range D).all (fun d => (List.range ((m + 1) ^ w)).all (fun b =>
    liveB stT d || !liveB stT (nextD nxT d b)))

variable (w m nxT) in
/-- `e`-th difference of the state counts. -/
def UC (e n d : ℕ) : ℤ :=
  ∑ i ∈ range (e + 1), (-1) ^ i * (e.choose i : ℤ) * (NC w m nxT (n + e - i) d : ℤ)

theorem UC_succ (hT : checkT w m nbL dL dT stT nxT D = true) (e n d' : ℕ) :
    UC w m nxT e (n + 1) d' = ∑ d ∈ range D, ∑ b ∈ range ((m + 1) ^ w),
      if nextD nxT d b = d' then UC w m nxT e n d else 0 := by
  unfold UC
  have : ∀ i ∈ range (e + 1), (-1) ^ i * (e.choose i : ℤ) * (NC w m nxT (n + 1 + e - i) d' : ℤ) =
      ∑ d ∈ range D, ∑ b ∈ range ((m + 1) ^ w), if nextD nxT d b = d' then
        (-1) ^ i * (e.choose i : ℤ) * (NC w m nxT (n + e - i) d : ℤ) else 0 := by
    intro i hi
    simp only [Finset.mem_range] at hi
    have e1 : n + 1 + e - i = (n + e - i) + 1 := by omega
    rw [e1, NC_succ hT]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b _
    split <;> simp
  rw [Finset.sum_congr rfl this, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  split <;> simp

theorem UC_zero (hT : checkT w m nbL dL dT stT nxT D = true)
    (hL : checkLive w m stT nxT D = true) (e n₁ : ℕ)
    (h₁ : ∀ d < D, liveB stT d = true → UC w m nxT e n₁ d = 0) :
    ∀ n, n₁ ≤ n → ∀ d < D, liveB stT d = true → UC w m nxT e n d = 0 := by
  simp only [checkLive, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at hL
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact h₁
  | succ n _ ih =>
    intro d' _ hd'
    rw [UC_succ hT]
    apply Finset.sum_eq_zero; intro d hd
    apply Finset.sum_eq_zero; intro b hb
    simp only [Finset.mem_range] at hd hb
    split
    · rename_i hn
      rcases hL d hd b hb with h | h
      · exact ih d hd h
      · rw [hn] at h; simp [h] at hd'
    · rfl

theorem AC_rec (hnb : ∀ t s t' s', nbL t s t' s' ↔ (t' + 1 = t ∧ nbL 1 s 0 s') ∨
      (t' = t ∧ nbL 1 s 1 s') ∨ (t' = t + 1 ∧ nbL 1 s 2 s'))
    (hT : checkT w m nbL dL dT stT nxT D = true)
    (hL : checkLive w m stT nxT D = true) (e n₁ : ℕ)
    (h₁ : ∀ d < D, liveB stT d = true → UC w m nxT e n₁ d = 0) (n : ℕ) (hn : n₁ ≤ n) :
    ∑ i ∈ range (e + 1), (-1) ^ i * (e.choose i : ℤ) * (AC w m nbL dL dT (n + e - i) : ℤ) = 0 := by
  have : ∀ i ∈ range (e + 1), (-1) ^ i * (e.choose i : ℤ) * (AC w m nbL dL dT (n + e - i) : ℤ) =
      ∑ d ∈ range D, if accB w m stT d then
        (-1) ^ i * (e.choose i : ℤ) * (NC w m nxT (n + e - i) d : ℤ) else 0 := by
    intro i _
    rw [AC_eq hnb hT]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d _
    split <;> simp
  rw [Finset.sum_congr rfl this, Finset.sum_comm]
  apply Finset.sum_eq_zero; intro d hd
  simp only [Finset.mem_range] at hd
  split
  · rename_i ha
    have hl : liveB stT d = true := by
      simp only [accB, List.any_eq_true] at ha
      obtain ⟨c, hc, _⟩ := ha
      simp only [liveB, Bool.not_eq_true', List.isEmpty_eq_false_iff]
      rintro h; rw [h] at hc; simp at hc
    have := UC_zero hT hL e n₁ h₁ n hn d hd hl
    unfold UC at this
    exact this
  · simp


variable (w m stT D) in
def valsOf (vecT : List (List ℕ)) (k : ℕ) : ℕ :=
  ∑ d ∈ range D, if accB w m stT d then (vecT.getD k []).getD d 0 else 0

theorem AC_vals (hnb : ∀ t s t' s', nbL t s t' s' ↔ (t' + 1 = t ∧ nbL 1 s 0 s') ∨
      (t' = t ∧ nbL 1 s 1 s') ∨ (t' = t + 1 ∧ nbL 1 s 2 s'))
    (hT : checkT w m nbL dL dT stT nxT D = true) (vecT : List (List ℕ))
    (hV : checkV w m nxT D vecT = true) (k : ℕ) (hk : k < vecT.length) :
    AC w m nbL dL dT k = valsOf w m stT D vecT k := by
  rw [AC_eq hnb hT, valsOf]
  apply Finset.sum_congr rfl; intro d hd
  rw [vec_spec hT vecT hV k hk d (by simpa using hd)]

variable (stT D) in
def checkU (vecT : List (List ℕ)) (e n₁ : ℕ) : Bool :=
  decide (n₁ + e < vecT.length) &&
  (List.range D).all (fun d => !liveB stT d || decide ((∑ i ∈ range (e + 1),
    (-1) ^ i * (e.choose i : ℤ) * ((vecT.getD (n₁ + e - i) []).getD d 0 : ℤ)) = 0))

theorem rec_tables (hnb : ∀ t s t' s', nbL t s t' s' ↔ (t' + 1 = t ∧ nbL 1 s 0 s') ∨
      (t' = t ∧ nbL 1 s 1 s') ∨ (t' = t + 1 ∧ nbL 1 s 2 s'))
    (hT : checkT w m nbL dL dT stT nxT D = true)
    (hL : checkLive w m stT nxT D = true) (vecT : List (List ℕ))
    (hV : checkV w m nxT D vecT = true) (e n₁ : ℕ) (hU : checkU stT D vecT e n₁ = true)
    (n : ℕ) (hn : n₁ ≤ n) :
    ∑ i ∈ range (e + 1), (-1) ^ i * (e.choose i : ℤ) * (AC w m nbL dL dT (n + e - i) : ℤ) = 0 := by
  simp only [checkU, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true'] at hU
  obtain ⟨hlen, hU⟩ := hU
  refine AC_rec hnb hT hL e n₁ (fun d hd hl => ?_) n hn
  rcases hU d hd with h | h
  · rw [h] at hl; cases hl
  · rw [← h]; unfold UC
    apply Finset.sum_congr rfl; intro i hi
    simp only [Finset.mem_range] at hi
    rw [vec_spec hT vecT hV _ (by omega) d hd]

end DFA

/-! ## Generating functions -/

section GF
open PowerSeries

theorem coeff_mk_mul_one_sub_X_pow (c : ℕ → ℚ) (e k : ℕ) :
    coeff k (mk c * (1 - X) ^ e) = ∑ i ∈ range (e + 1),
      if i ≤ k then (-1) ^ i * (e.choose i : ℚ) * c (k - i) else 0 := by
  have h1 : (1 - X : PowerSeries ℚ) ^ e = ∑ i ∈ range (e + 1), C ((-1) ^ i * (e.choose i : ℚ)) * X ^ i := by
    rw [show (1 - X : PowerSeries ℚ) = -X + 1 by ring, add_pow]
    apply Finset.sum_congr rfl; intro i _
    simp only [one_pow, mul_one, map_mul, map_pow, map_neg, map_one, map_natCast]
    rw [neg_pow]; ring
  rw [h1, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [mul_comm (C _), ← mul_assoc, coeff_mul_C, coeff_mul_X_pow', coeff_mk]
  split <;> ring

theorem coeff_poly (P : List ℚ) (k : ℕ) :
    coeff k (∑ j ∈ range P.length, C (P.getD j 0) * X ^ j) = P.getD k 0 := by
  rw [map_sum]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split
  · rfl
  · rename_i h; simp only [Finset.mem_range, not_lt] at h
    rw [List.getD_eq_default _ _ h]

theorem gf_main (a : ℕ → ℕ) (e n₁ K₁ : ℕ) (P : List ℤ)
    (hrec : ∀ n, n₁ ≤ n → ∑ i ∈ range (e + 1), (-1) ^ i * (e.choose i : ℤ) * (a (n + e - i) : ℤ) = 0)
    (hK : n₁ + e ≤ K₁) (hK' : e + 1 ≤ K₁) (hP : P.length ≤ K₁)
    (hsmall : ∀ k < K₁, (∑ i ∈ range (e + 1), if i ≤ k then (-1) ^ i * (e.choose i : ℤ) *
      (if k - i = 0 then 0 else (a (k - i) : ℤ)) else 0) = P.getD k 0) :
    mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ e =
      ∑ j ∈ range P.length, C ((P.getD j 0 : ℤ) : ℚ) * X ^ j := by
  have hP' : ∀ j, (((P.map (Int.cast : ℤ → ℚ)).getD j 0) : ℚ) = ((P.getD j 0 : ℤ) : ℚ) := by
    intro j
    by_cases hj : j < P.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj]; simp
    · simp only [not_lt] at hj
      rw [List.getD_eq_default _ _ (by simpa using hj), List.getD_eq_default _ _ hj]; simp
  have e1 : ∑ j ∈ range P.length, C ((P.getD j 0 : ℤ) : ℚ) * X ^ j =
      ∑ j ∈ range (P.map (Int.cast : ℤ → ℚ)).length,
        C ((P.map (Int.cast : ℤ → ℚ)).getD j 0) * X ^ j := by
    rw [List.length_map]; apply Finset.sum_congr rfl; intro j _; rw [hP']
  rw [e1]
  ext k
  rw [coeff_mk_mul_one_sub_X_pow, coeff_poly, hP']
  by_cases hk : k < K₁
  · rw [← hsmall k hk]; push_cast
    apply Finset.sum_congr rfl; intro i _
    by_cases h1 : i ≤ k
    · by_cases h2 : k - i = 0
      · simp [h1, h2]
      · simp [h1, h2]
    · simp [h1]
  · simp only [not_lt] at hk
    rw [List.getD_eq_default _ _ (by omega)]
    have := hrec (k - e) (by omega)
    have e2 : k - e + e = k := by omega
    rw [e2] at this
    have e3 : ((0 : ℤ) : ℚ) = ((∑ i ∈ range (e + 1), (-1) ^ i * (e.choose i : ℤ) *
        (a (k - i) : ℤ) : ℤ) : ℚ) := by rw [this]
    rw [e3]; push_cast
    apply Finset.sum_congr rfl; intro i hi
    simp only [Finset.mem_range] at hi
    rw [if_pos (by omega), if_neg (by omega)]

end GF

/-! ## Arrays read column by column -/

section Transpose
variable (nb : ℕ → ℕ → ℕ → ℕ → Prop) [∀ a b c d, Decidable (nb a b c d)]

def nbT (t s t' s' : ℕ) : Prop := nb s t s' t'

instance (t s t' s' : ℕ) : Decidable (nbT nb t s t' s') := by unfold nbT; infer_instance

def sortedT (dL : Bool) {n : ℕ} (A : Fin w → Fin n → Fin (m + 1)) : Prop :=
  Monotone (fun i => List.ofFn (A i)) ∧ ordB dL (fun j => List.ofFn (fun i => A i j))

instance (dL : Bool) {n : ℕ} (A : Fin w → Fin n → Fin (m + 1)) : Decidable (sortedT dL A) := by
  unfold sortedT ordB; split <;> infer_instance

def minT {n : ℕ} (A : Fin w → Fin n → Fin (m + 1)) : Fin w → Fin n → Fin (m + 1) := fun i j =>
  ((univ : Finset (Fin w × Fin n)).filter (fun p => nb i j p.1 p.2)).inf (fun p => A p.1 p.2)

variable (w m) in
def ACT (dL : Bool) (n : ℕ) : ℕ :=
  ((univ.filter (fun A : Fin w → Fin n → Fin (m + 1) => sortedT dL A)).image (minT nb)).card

def tau {n : ℕ} (A : Fin w → Fin n → Fin (m + 1)) : Fin n → Ltr w m := fun t s => A s t

theorem tau_inj {n : ℕ} : Function.Injective (tau (w := w) (m := m) (n := n)) := by
  intro A B h; funext s t; exact congrFun (congrFun h t) s

theorem Fmin_tau {n : ℕ} (A : Fin w → Fin n → Fin (m + 1)) :
    Fmin (nbT nb) (tau A) = tau (minT nb A) := by
  funext t s
  simp only [Fmin, tau, minT, nbT]
  apply le_antisymm
  · apply Finset.le_inf; rintro ⟨i, j⟩ hp
    exact Finset.inf_le (b := (j, i)) (Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hp).2⟩)
  · apply Finset.le_inf; rintro ⟨j, i⟩ hp
    exact Finset.inf_le (b := (i, j)) (Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hp).2⟩)

theorem ACT_eq (dL : Bool) (n : ℕ) : ACT w m nb dL n = AC w m (nbT nb) dL true n := by
  unfold ACT AC
  rw [← Finset.card_image_of_injective _ tau_inj, Finset.image_image]
  have h1 : (tau ∘ minT nb : (Fin w → Fin n → Fin (m + 1)) → Fin n → Ltr w m) =
      Fmin (nbT nb) ∘ tau := by funext A; exact (Fmin_tau nb A).symm
  rw [h1, ← Finset.image_image]
  congr 2
  ext W
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨A, ⟨h1, h2⟩, rfl⟩
    exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun s t => W t s, ⟨h2, h1⟩, rfl⟩

end Transpose

end MinNbLib


namespace OMA.P_oeis_a220154

open OMA.S_oeis_a220154 MinNbLib Finset PowerSeries

theorem a_eq (n : ℕ) : a n = AC 2 2 (nbT nb) false true n := by
  rw [← ACT_eq]
  unfold a ACT IsSorted minNb sortedT minT
  rfl

theorem hnb : ∀ t s t' s', (nbT nb) t s t' s' ↔ (t' + 1 = t ∧ (nbT nb) 1 s 0 s') ∨
    (t' = t ∧ (nbT nb) 1 s 1 s') ∨ (t' = t + 1 ∧ (nbT nb) 1 s 2 s') := by
  intro t s t' s'
  unfold nbT nb
  have e1 : ∀ x : ℕ, (x = x + 1 + 1) = False := fun x => by simp; omega
  have e2 : ∀ x : ℕ, (x + 1 + 1 = x) = False := fun x => by simp; omega
  rcases (by omega : t' + 1 = t ∨ t' = t ∨ t' = t + 1 ∨ (t' ≠ t ∧ t' + 1 ≠ t ∧ t' ≠ t + 1)) with
    h | h | h | ⟨h1, h2, h3⟩
  · subst h; simp [e1, e2]; try tauto
  · subst h; simp [e1, e2]; try tauto
  · subst h; simp [e1, e2]; try tauto
  · simp [h1, h2, h3]

/-- Configuration codes of the automaton states. -/
def stT : List (List ℕ) := [[400, 401, 404, 405, 407, 408, 409], [341, 371, 381, 382, 410, 411, 451, 491], [], [340, 344, 374, 384, 454, 457, 494], [385, 450, 455, 495], [370, 377, 387, 497], [380, 388, 498], [490, 499], [310, 311, 321, 322, 324, 327, 410, 411], [320], [340, 341, 344, 371], [340, 344, 370, 374, 377], [351, 352, 451], [354, 357, 454, 457], [350, 355, 450, 455], [370, 371, 374, 377], [370, 374, 377], [370, 377], [381, 382], [384, 387], [380, 385, 388], [387], [380, 388], [491], [494], [495], [497], [498], [310, 311, 321, 322, 324, 327, 340, 341, 344, 370, 371, 374, 377, 410, 411], [310, 311, 340, 341, 344], [340, 341, 344, 370, 371, 374, 377], [341, 371], [310, 311, 340, 341, 344, 370, 371, 374, 377], [310, 311, 321, 322, 324, 327], [351, 352, 381, 382], [354, 357, 384, 387], [350, 355, 380, 385, 388], [371], [410, 411], [341], [340, 344], [451], [454, 457], [450, 455], [374], [384], [385], [310, 311], [310, 311, 321, 322, 324, 327, 340, 341, 344, 370, 371, 374, 377], [340, 341, 344], [351, 352], [354, 357], [350, 355]]

/-- Transitions of the automaton, indexed by output letter code. -/
def nxT : List (List ℕ) := [[1, 2, 2, 3, 4, 2, 5, 6, 7], [8, 9, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2], [10, 2, 2, 11, 2, 2, 2, 2, 2], [12, 2, 2, 13, 14, 2, 2, 2, 2], [15, 2, 2, 16, 2, 2, 17, 2, 2], [18, 2, 2, 19, 20, 2, 21, 22, 2], [23, 2, 2, 24, 25, 2, 26, 27, 7], [28, 9, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2], [29, 2, 2, 2, 2, 2, 2, 2, 2], [30, 2, 2, 2, 2, 2, 2, 2, 2], [8, 9, 2, 2, 2, 2, 2, 2, 2], [31, 2, 2, 11, 2, 2, 2, 2, 2], [12, 2, 2, 13, 14, 2, 2, 2, 2], [32, 2, 2, 2, 2, 2, 2, 2, 2], [30, 2, 2, 2, 2, 2, 2, 2, 2], [15, 2, 2, 2, 2, 2, 2, 2, 2], [33, 9, 2, 2, 2, 2, 2, 2, 2], [31, 2, 2, 11, 2, 2, 2, 2, 2], [34, 2, 2, 35, 36, 2, 2, 2, 2], [37, 2, 2, 16, 2, 2, 2, 2, 2], [18, 2, 2, 19, 20, 2, 2, 2, 2], [38, 2, 2, 2, 2, 2, 2, 2, 2], [39, 2, 2, 40, 2, 2, 2, 2, 2], [41, 2, 2, 42, 43, 2, 2, 2, 2], [37, 2, 2, 44, 2, 2, 17, 2, 2], [18, 2, 2, 45, 46, 2, 21, 22, 2], [28, 9, 2, 2, 2, 2, 2, 2, 2], [29, 2, 2, 2, 2, 2, 2, 2, 2], [32, 2, 2, 2, 2, 2, 2, 2, 2], [47, 2, 2, 2, 2, 2, 2, 2, 2], [32, 2, 2, 2, 2, 2, 2, 2, 2], [48, 9, 2, 2, 2, 2, 2, 2, 2], [33, 9, 2, 2, 2, 2, 2, 2, 2], [31, 2, 2, 11, 2, 2, 2, 2, 2], [34, 2, 2, 35, 36, 2, 2, 2, 2], [47, 2, 2, 2, 2, 2, 2, 2, 2], [38, 2, 2, 2, 2, 2, 2, 2, 2], [47, 2, 2, 2, 2, 2, 2, 2, 2], [49, 2, 2, 2, 2, 2, 2, 2, 2], [38, 2, 2, 2, 2, 2, 2, 2, 2], [31, 2, 2, 11, 2, 2, 2, 2, 2], [41, 2, 2, 42, 43, 2, 2, 2, 2], [49, 2, 2, 2, 2, 2, 2, 2, 2], [39, 2, 2, 40, 2, 2, 2, 2, 2], [50, 2, 2, 51, 52, 2, 2, 2, 2], [47, 2, 2, 2, 2, 2, 2, 2, 2], [48, 9, 2, 2, 2, 2, 2, 2, 2], [29, 2, 2, 2, 2, 2, 2, 2, 2], [33, 9, 2, 2, 2, 2, 2, 2, 2], [31, 2, 2, 11, 2, 2, 2, 2, 2], [50, 2, 2, 51, 52, 2, 2, 2, 2]]

/-- State count vectors for lengths 0 to 9. -/
def vecT : List (List ℕ) := [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 3, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 60, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 683, 0, 0, 0, 0, 1, 1, 3, 0, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0], [0, 0, 6479, 0, 0, 0, 0, 1, 1, 7, 0, 4, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 3, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1], [0, 0, 58920, 0, 0, 0, 0, 1, 1, 13, 0, 7, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 7, 8, 5, 3, 3, 3, 2, 6, 2, 2, 3, 3, 3, 1, 1, 1, 13, 4, 3, 2, 2, 2], [0, 0, 531254, 0, 0, 0, 0, 1, 1, 21, 0, 10, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 8, 10, 14, 7, 4, 4, 4, 2, 10, 2, 2, 4, 4, 4, 1, 1, 1, 24, 9, 3, 3, 3, 3], [0, 0, 4782713, 0, 0, 0, 0, 1, 1, 31, 0, 13, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 9, 11, 13, 23, 9, 5, 5, 5, 2, 15, 2, 2, 5, 5, 5, 1, 1, 1, 38, 16, 3, 4, 4, 4], [0, 0, 43046385, 0, 0, 0, 0, 1, 1, 43, 0, 16, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 12, 14, 16, 35, 11, 6, 6, 6, 2, 21, 2, 2, 6, 6, 6, 1, 1, 1, 55, 25, 3, 5, 5, 5], [0, 0, 387420062, 0, 0, 0, 0, 1, 1, 57, 0, 19, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 15, 17, 19, 50, 13, 7, 7, 7, 2, 28, 2, 2, 7, 7, 7, 1, 1, 1, 75, 36, 3, 6, 6, 6]]

theorem hT0 : (maskOf (initC 2 2 true) == maskOf (stT.getD 0 []) && decide (0 < 53)) = true := by
  decide +kernel

theorem hR0 : rowsOK 2 2 (nbT nb) false true stT nxT 53 0 53 = true := by decide +kernel

theorem hT : checkT 2 2 (nbT nb) false true stT nxT 53 = true :=
  checkT_of hT0 (fun d hd =>
    rowsOK_spec hR0 d (by omega) (by omega))

theorem hL : checkLive 2 2 stT nxT 53 = true := by decide +kernel

theorem hV0 : (vecT.getD 0 [] == (List.range 53).map (fun d => if d = 0 then 1 else 0)) = true := by
  decide +kernel

theorem hS0 : (List.range' 0 9).all (stepOK 2 2 nxT 53 vecT) = true := by
  decide +kernel

theorem hV : checkV 2 2 nxT 53 vecT = true :=
  checkV_of vecT hV0 (fun d hd =>
    all_range'_spec hS0 d (by omega) (Nat.lt_of_lt_of_le hd (by decide +kernel)))

theorem hU : checkU stT 53 vecT 3 5 = true := by decide +kernel

theorem v0 : a 0 = 1 := by rw [a_eq, AC_vals hnb hT vecT hV 0 (by decide)]; decide +kernel
theorem v1 : a 1 = 6 := by rw [a_eq, AC_vals hnb hT vecT hV 1 (by decide)]; decide +kernel
theorem v2 : a 2 = 11 := by rw [a_eq, AC_vals hnb hT vecT hV 2 (by decide)]; decide +kernel
theorem v3 : a 3 = 23 := by rw [a_eq, AC_vals hnb hT vecT hV 3 (by decide)]; decide +kernel
theorem v4 : a 4 = 50 := by rw [a_eq, AC_vals hnb hT vecT hV 4 (by decide)]; decide +kernel
theorem v5 : a 5 = 88 := by rw [a_eq, AC_vals hnb hT vecT hV 5 (by decide)]; decide +kernel
theorem v6 : a 6 = 137 := by rw [a_eq, AC_vals hnb hT vecT hV 6 (by decide)]; decide +kernel
theorem v7 : a 7 = 197 := by rw [a_eq, AC_vals hnb hT vecT hV 7 (by decide)]; decide +kernel
theorem v8 : a 8 = 268 := by rw [a_eq, AC_vals hnb hT vecT hV 8 (by decide)]; decide +kernel
theorem v9 : a 9 = 350 := by rw [a_eq, AC_vals hnb hT vecT hV 9 (by decide)]; decide +kernel

theorem hrec (n : ℕ) (hn : 5 ≤ n) :
    ∑ i ∈ range (3 + 1), (-1) ^ i * ((3 : ℕ).choose i : ℤ) * (a (n + 3 - i) : ℤ) = 0 := by
  have := rec_tables hnb hT hL vecT hV 3 5 hU n hn
  simpa only [a_eq] using this

theorem hsmall : ∀ k < 8, (∑ i ∈ range (3 + 1), if i ≤ k then (-1) ^ i * ((3 : ℕ).choose i : ℤ) *
    (if k - i = 0 then 0 else (a (k - i) : ℤ)) else 0) = ([0, 6, -7, 8, 8, -4] : List ℤ).getD k 0 := by
  intro k hk
  interval_cases k <;> norm_num [Finset.sum_range_succ, Nat.choose, v1, v2, v3, v4, v5, v6, v7]

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 3 =
    X * (6 - 7 * X + 8 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4) := by
  rw [gf_main a 3 5 8 [0, 6, -7, 8, 8, -4] hrec (by norm_num) (by norm_num) (by norm_num) hsmall]
  simp [Finset.sum_range_succ]
  ring

theorem rec (n : ℕ) (hn : 5 < n) : (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  by_cases h : 8 ≤ n
  · have := hrec (n - 3) (by omega)
    have e0 : n - 3 + 3 = n := by omega
    simp only [e0] at this
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
    norm_num [Nat.choose] at this
    linarith
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9]

end OMA.P_oeis_a220154

theorem OMA.solution : type_of% @OMA.S_oeis_a220154.main :=
  ⟨OMA.P_oeis_a220154.gf, OMA.P_oeis_a220154.rec⟩
