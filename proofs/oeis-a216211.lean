import OMAStatements.S_oeis_a216211

-- Credit: @DavidHallgren
namespace FourColumn

/-- A run through a list of labelled transitions. -/
def Run {E S : Type*} (src dst : E → S) : S → List E → S → Prop
  | s, [], t => s = t
  | s, e :: w, t => s = src e ∧ Run src dst (dst e) w t

/-- Internal port or a labelled crossing of the seam. -/
inductive Port (A C : Type*) where
  | inner (a : A)
  | seam (c : C)
deriving DecidableEq, Repr

namespace Port

def collapse {A C : Type*} : Port A C → Option A
  | .inner a => some a
  | .seam _ => none

def label {A C : Type*} : Port A C → List C
  | .inner _ => []
  | .seam c => [c]

end Port

inductive Control (A B C : Type*) where
  | left (a : A)
  | right (b : B)
  | enterLeft (c : C)
  | enterRight (c : C)
deriving DecidableEq, Repr

namespace Glue

variable {A B C L R : Type}
variable (li lo : L → Port A C) (ri ro : R → Port B C)

def input : L ⊕ R → Control A B C
  | .inl e => match li e with | .inner a => .left a | .seam c => .enterLeft c
  | .inr e => match ri e with | .inner b => .right b | .seam c => .enterRight c

def output : L ⊕ R → Control A B C
  | .inl e => match lo e with | .inner a => .left a | .seam c => .enterRight c
  | .inr e => match ro e with | .inner b => .right b | .seam c => .enterLeft c

def history {E S : Type} (i o : E → Port S C) (w : List E) : List C :=
  w.flatMap (fun e => (i e).label ++ (o e).label)

def lefts (w : List (L ⊕ R)) : List L := w.filterMap Sum.getLeft?
def rights (w : List (L ⊕ R)) : List R := w.filterMap Sum.getRight?

def leftPos : Control A B C → Option A
  | .left a => some a
  | _ => none

def rightPos : Control A B C → Option B
  | .right b => some b
  | _ => none

def sync (s : Control A B C) (u v : List C) : Prop :=
  match s with
  | .enterLeft c => u = c :: v
  | .enterRight c => c :: u = v
  | _ => u = v

def ready (s : Control A B C) (u : List L) (v : List R) (b : B) : Prop :=
  Run (Port.collapse ∘ li) (Port.collapse ∘ lo) (leftPos s) u none ∧
  Run (Port.collapse ∘ ri) (Port.collapse ∘ ro) (rightPos s) v (some b) ∧
  sync s (history li lo u) (history ri ro v)

theorem ready_left (e : L) (u : List L) (v : List R) (b : B)
    (s : Control A B C) (h : (∃ a, s = .left a) ∨ (∃ c, s = .enterLeft c)) :
    ready li lo ri ro s (e :: u) v b ↔
      s = input li ri (.inl e) ∧ ready li lo ri ro (output lo ro (.inl e)) u v b := by
  rcases h with ⟨a, rfl⟩ | ⟨c, rfl⟩ <;> cases hi : li e <;> cases ho : lo e <;>
    simp [ready, Run, leftPos, rightPos, input, output, sync, history, hi, ho,
      Port.collapse, Port.label, and_assoc, and_left_comm] <;> grind

theorem ready_right (e : R) (u : List L) (v : List R) (b : B)
    (s : Control A B C) (h : (∃ a, s = .right a) ∨ (∃ c, s = .enterRight c)) :
    ready li lo ri ro s u (e :: v) b ↔
      s = input li ri (.inr e) ∧ ready li lo ri ro (output lo ro (.inr e)) u v b := by
  rcases h with ⟨a, rfl⟩ | ⟨c, rfl⟩ <;> cases hi : ri e <;> cases ho : ro e <;>
    simp [ready, Run, leftPos, rightPos, input, output, sync, history, hi, ho,
      Port.collapse, Port.label, and_assoc, and_left_comm, and_comm]

def onLeft : Control A B C → Bool
  | .left _ | .enterLeft _ => true
  | _ => false

theorem onLeft_yes (s : Control A B C) (h : onLeft s = true) :
    (∃ a, s = .left a) ∨ (∃ c, s = .enterLeft c) := by
  cases s <;> simp_all [onLeft]

theorem onLeft_no (s : Control A B C) (h : ¬ onLeft s = true) :
    (∃ a, s = .right a) ∨ (∃ c, s = .enterRight c) := by
  cases s <;> simp_all [onLeft]

def weave : ℕ → Control A B C → List L → List R → List (L ⊕ R)
  | 0, _, _, _ => []
  | k+1, s, u, v =>
    if onLeft s then
      match u with
      | [] => []
      | e::es => .inl e :: weave k (output lo ro (.inl e)) es v
    else
      match v with
      | [] => []
      | e::es => .inr e :: weave k (output lo ro (.inr e)) u es

theorem proj_run {s : Control A B C} {w : List (L ⊕ R)} {b : B}
    (h : Run (input li ri) (output lo ro) s w (.right b)) :
    ready li lo ri ro s (lefts w) (rights w) b ∧
    ∀ fuel ≥ w.length, weave lo ro fuel s (lefts w) (rights w) = w := by
  induction w generalizing s with
  | nil =>
    subst s
    refine ⟨by simp [ready, Run, lefts, rights, leftPos, rightPos, sync, history], ?_⟩
    intro fuel _
    cases fuel <;> rfl
  | cons e w ih =>
    obtain ⟨rfl, ht⟩ := h
    obtain ⟨hr, hw⟩ := ih ht
    cases e with
    | inl e =>
      have side : onLeft (input li ri (.inl e)) = true := by cases he : li e <;> simp [input, he, onLeft]
      refine ⟨(ready_left li lo ri ro _ _ _ _ _ (onLeft_yes _ side)).2 ⟨rfl, hr⟩, ?_⟩
      intro fuel hf
      cases fuel with
      | zero => simp at hf
      | succ k => simp [lefts, rights, weave, side] at *; exact hw k (by omega)
    | inr e =>
      have side : onLeft (input li ri (.inr e)) = false := by cases he : ri e <;> simp [input, he, onLeft]
      refine ⟨(ready_right li lo ri ro _ _ _ _ _ (onLeft_no _ (by simp [side]))).2 ⟨rfl, hr⟩, ?_⟩
      intro fuel hf
      cases fuel with
      | zero => simp at hf
      | succ k => simp [lefts, rights, weave, side] at *; exact hw k (by omega)

theorem finish_ready {s : Control A B C} {u : List L} {v : List R} {b : B}
    (h : ready li lo ri ro s u v b) (hempty : if onLeft s then u = [] else v = []) :
    u = [] ∧ v = [] ∧ s = .right b := by
  cases s with
  | left a => simp [onLeft] at hempty; subst u; simp [ready, leftPos, Run] at h
  | enterLeft c => simp [onLeft] at hempty; subst u; simp [ready, history, sync] at h
  | enterRight c => simp [onLeft] at hempty; subst v; simp [ready, rightPos, Run] at h
  | right a =>
    simp [onLeft] at hempty; subst v
    cases u with
    | nil => simpa [ready, Run, leftPos, rightPos, sync, history] using h
    | cons e es =>
      cases he : li e <;> cases ho : lo e <;>
        simp [ready, Run, leftPos, rightPos, sync, history, he, ho, Port.label, Port.collapse] at h

theorem weave_ready (fuel : ℕ) (s : Control A B C) (u : List L) (v : List R) (b : B)
    (hf : u.length + v.length ≤ fuel) (h : ready li lo ri ro s u v b) :
    let w := weave lo ro fuel s u v
    Run (input li ri) (output lo ro) s w (.right b) ∧ lefts w = u ∧ rights w = v := by
  induction fuel generalizing s u v with
  | zero =>
    have hu : u = [] := List.length_eq_zero_iff.mp (by omega)
    have hv : v = [] := List.length_eq_zero_iff.mp (by omega)
    subst u; subst v
    obtain ⟨_, _, rfl⟩ := finish_ready li lo ri ro h (by simp)
    exact ⟨rfl,rfl,rfl⟩
  | succ k ih =>
    by_cases side : onLeft s = true
    · cases u with
      | nil =>
        obtain ⟨_, rfl, rfl⟩ := finish_ready li lo ri ro h (by simp [side])
        simp [onLeft] at side
      | cons e es =>
        obtain ⟨hs, ht⟩ := (ready_left li lo ri ro _ _ _ _ _ (onLeft_yes _ side)).1 h
        obtain ⟨hw, hu, hv⟩ := ih (output lo ro (.inl e)) es v (by simp at hf; omega) ht
        simp [weave, side, Run, lefts, rights] at * <;> exact ⟨⟨hs,hw⟩,hu,hv⟩
    · cases v with
      | nil =>
        obtain ⟨rfl, _, rfl⟩ := finish_ready li lo ri ro h (by simp [side])
        exact ⟨rfl,rfl,rfl⟩
      | cons e es =>
        obtain ⟨hs, ht⟩ := (ready_right li lo ri ro _ _ _ _ _ (onLeft_no _ side)).1 h
        obtain ⟨hw, hu, hv⟩ := ih (output lo ro (.inr e)) u es (by simp at hf; omega) ht
        simp [weave, side, Run, lefts, rights] at * <;> exact ⟨⟨hs,hw⟩,hu,hv⟩

end Glue
@[simp] theorem mem_lefts {L R : Type} (e : L) (w : List (L ⊕ R)) :
    e ∈ Glue.lefts w ↔ Sum.inl e ∈ w := by
  simp [Glue.lefts, List.mem_filterMap]
@[simp] theorem mem_rights {L R : Type} (e : R) (w : List (L ⊕ R)) :
    e ∈ Glue.rights w ↔ Sum.inr e ∈ w := by
  simp [Glue.rights, List.mem_filterMap]

theorem run_map {E F S T : Type} (i o : E → S) (j p : F → T)
    (f : E → F) (g : S → T) (hg : Function.Injective g)
    (hi : ∀ e, j (f e) = g (i e)) (ho : ∀ e, p (f e) = g (o e))
    (w : List E) (s t : S) :
    Run j p (g s) (w.map f) (g t) ↔ Run i o s w t := by
  induction w generalizing s with
  | nil => exact hg.eq_iff
  | cons e es ih => simp [Run, hi, ho, hg.eq_iff, ih]

inductive Dir | north | south | west | east
  deriving DecidableEq, Repr

structure Tile where
  col : Fin 4
  prev : Dir
  next : Dir
  deriving DecidableEq, Repr

abbrev Ev := ℕ × Tile

inductive Key
  | top | bot
  | horiz (row cut : ℕ) (forward : Bool)
  | vert (cut : ℕ) (col : Fin 4) (forward : Bool)
  deriving DecidableEq, Repr

def key (h r : ℕ) (c : Fin 4) (incoming : Bool) : Dir → Key
  | .north => if r = 0 then .top else .vert r c incoming
  | .south => if r+1 = h then .bot else .vert (r+1) c (!incoming)
  | .west => .horiz r c.val incoming
  | .east => .horiz r (c.val+1) (!incoming)

def src (h : ℕ) (e : Ev) := key h e.1 e.2.col true e.2.prev
def dst (h : ℕ) (e : Ev) := key h e.1 e.2.col false e.2.next

def sideLabels (p : Dir) (t : Tile) : List (Fin 4) :=
  (if t.prev = p then [t.col] else []) ++ (if t.next = p then [t.col] else [])

def upper (w : List Ev) := w.flatMap fun e => if e.1 = 0 then sideLabels .north e.2 else []
def lower (h : ℕ) (w : List Ev) := w.flatMap fun e => if e.1+1 = h then sideLabels .south e.2 else []

def distinctSites (w : List Ev) : Prop :=
  w.Pairwise (fun e f => e.1 ≠ f.1 ∨ e.2.col ≠ f.2.col)

def Fits (h : ℕ) (w : List Ev) : Prop :=
  distinctSites w ∧ ∀ e ∈ w, e.1 < h ∧ e.2.prev ≠ e.2.next

def Board (h : ℕ) (p q : List (Fin 4)) := {w : List Ev //
  Fits h w ∧ Run (src h) (dst h) .top w .bot ∧ upper w = p ∧ lower h w = q}

def untag : Tile ⊕ Ev → Ev
  | .inl t => (0,t)
  | .inr (r,t) => (r+1,t)

def tag : Ev → Tile ⊕ Ev
  | (0,t) => .inl t
  | (r+1,t) => .inr (r,t)

@[simp] theorem untag_tag (e : Ev) : untag (tag e) = e := by
  rcases e with ⟨r,t⟩; cases r <;> rfl
@[simp] theorem tag_untag (x : Tile ⊕ Ev) : tag (untag x) = x := by
  rcases x with t | ⟨r,t⟩ <;> rfl

def splitKey : Key → Control Key Key (Fin 4)
  | .top => .left .top
  | .bot => .right .bot
  | .horiz 0 c b => .left (.horiz 0 c b)
  | .horiz (r+1) c b => .right (.horiz r c b)
  | .vert 0 c b => .left (.vert 0 c b)
  | .vert 1 c true => .enterRight c
  | .vert 1 c false => .enterLeft c
  | .vert (r+2) c b => .right (.vert (r+1) c b)

def unsplitKey : Control Key Key (Fin 4) → Key
  | .left k => k
  | .right (.horiz r c b) => .horiz (r+1) c b
  | .right (.vert r c b) => .vert (r+1) c b
  | .right k => k
  | .enterRight c => .vert 1 c true
  | .enterLeft c => .vert 1 c false

theorem splitKey_inj : Function.Injective splitKey := by
  apply Function.LeftInverse.injective (g := unsplitKey)
  intro k
  cases k with
  | top | bot => rfl
  | horiz r c b => cases r <;> rfl
  | vert r c b => rcases r with _ | _ | r <;> cases b <;> rfl

def portL (t : Tile) (b : Bool) (d : Dir) : Port Key (Fin 4) :=
  if d = .south then .seam t.col else .inner (key 1 0 t.col b d)

def portR (h : ℕ) (e : Ev) (b : Bool) (d : Dir) : Port Key (Fin 4) :=
  if e.1 = 0 ∧ d = .north then .seam e.2.col else .inner (key h e.1 e.2.col b d)

def li (t : Tile) := portL t true t.prev
def lo (t : Tile) := portL t false t.next
def ri (h : ℕ) (e : Ev) := portR h e true e.2.prev
def ro (h : ℕ) (e : Ev) := portR h e false e.2.next

theorem split_src (n : ℕ) (e : Tile ⊕ Ev) :
    splitKey (src (n+2) (untag e)) = Glue.input li (ri (n+1)) e := by
  rcases e with ⟨c,d,f⟩ | ⟨r,c,d,f⟩
  · cases d <;> simp [untag, src, key, splitKey, Glue.input, li, portL]
  · by_cases h : r+1 = n+1
    · have := Nat.succ.inj h; subst n
      cases d <;> cases r <;> simp [untag, src, key, splitKey, Glue.input, ri, portR]
    · cases d <;> cases r <;> simp_all [untag, src, key, splitKey, Glue.input, ri, portR]

theorem split_dst (n : ℕ) (e : Tile ⊕ Ev) :
    splitKey (dst (n+2) (untag e)) = Glue.output lo (ro (n+1)) e := by
  rcases e with ⟨c,d,f⟩ | ⟨r,c,d,f⟩
  · cases f <;> simp [untag, dst, key, splitKey, Glue.output, lo, portL]
  · by_cases h : r+1 = n+1
    · have := Nat.succ.inj h; subst n
      cases f <;> cases r <;> simp [untag, dst, key, splitKey, Glue.output, ro, portR]
    · cases f <;> cases r <;> simp_all [untag, dst, key, splitKey, Glue.output, ro, portR]

def dropTop (k : Key) : Option Key := if k = .top then none else some k
def dropBot (k : Key) : Option Key := if k = .bot then none else some k

theorem dropTop_inj : Function.Injective dropTop := by
  intro a b; cases a <;> cases b <;> simp [dropTop]
theorem dropBot_inj : Function.Injective dropBot := by
  intro a b; cases a <;> cases b <;> simp [dropBot]

lemma collapseR (n : ℕ) (e : Ev) (b : Bool) (d : Dir) :
    (portR (n+1) e b d).collapse = dropTop (key (n+1) e.1 e.2.col b d) := by
  rcases e with ⟨r,t⟩
  cases d <;> cases r <;> simp [portR, key, Port.collapse, dropTop] <;> split <;> simp_all

lemma labelR (h : ℕ) (e : Ev) (b : Bool) (d : Dir) :
    (portR h e b d).label = (if e.1 = 0 ∧ d = .north then [e.2.col] else []) := by
  unfold portR; split <;> simp_all [Port.label]

lemma histR (h : ℕ) (w : List Ev) : Glue.history (ri h) (ro h) w = upper w := by
  unfold Glue.history upper
  apply List.flatMap_congr
  intro e _
  by_cases h0 : e.1 = 0 <;> simp [ri, ro, labelR, h0, sideLabels]

def rowUpper (w : List Tile) := w.flatMap (sideLabels .north)
def rowLower (w : List Tile) := w.flatMap (sideLabels .south)

lemma histL (w : List Tile) : Glue.history li lo w = rowLower w := by
  unfold Glue.history rowLower
  apply List.flatMap_congr
  rintro ⟨c,d,f⟩ _
  cases d <;> cases f <;> rfl

def RowFits (w : List Tile) : Prop :=
  (w.map Tile.col).Nodup ∧ ∀ t ∈ w, t.prev ≠ t.next

def RowRun (w : List Tile) :=
  Run (Port.collapse ∘ li) (Port.collapse ∘ lo) (some .top) w none

@[simp] lemma split_l_cons (t : Tile) (w : List (Tile ⊕ Ev)) :
    Glue.lefts (.inl t :: w) = t :: Glue.lefts w := rfl
@[simp] lemma split_l_skip (e : Ev) (w : List (Tile ⊕ Ev)) :
    Glue.lefts (.inr e :: w) = Glue.lefts w := rfl
@[simp] lemma split_r_cons (e : Ev) (w : List (Tile ⊕ Ev)) :
    Glue.rights (.inr e :: w) = e :: Glue.rights w := rfl
@[simp] lemma split_r_skip (t : Tile) (w : List (Tile ⊕ Ev)) :
    Glue.rights (.inl t :: w) = Glue.rights w := rfl

lemma all_split {P : Tile ⊕ Ev → Prop} {w : List (Tile ⊕ Ev)} :
    (∀ e ∈ w, P e) ↔ (∀ t ∈ Glue.lefts w, P (.inl t)) ∧ (∀ t ∈ Glue.rights w, P (.inr t)) := by
  simp only [mem_lefts, mem_rights]
  constructor
  · intro h; exact ⟨fun t => h _, fun t => h _⟩
  · rintro ⟨h₁,h₂⟩ (t | t); exact h₁ t; exact h₂ t

lemma distinct_cons (e : Ev) (w : List Ev) : distinctSites (e::w) ↔
    (∀ f ∈ w, e.1 ≠ f.1 ∨ e.2.col ≠ f.2.col) ∧ distinctSites w := List.pairwise_cons

lemma disjoint_split (w : List (Tile ⊕ Ev)) :
    distinctSites (w.map untag) ↔ (w |> Glue.lefts |>.map Tile.col).Nodup ∧ distinctSites (Glue.rights w) := by
  induction w with
  | nil => simp [distinctSites, Glue.lefts, Glue.rights]
  | cons e w ih =>
    rcases e with t | ⟨r,t⟩
    · simp only [List.map_cons, split_l_cons, split_r_skip, List.nodup_cons, distinct_cons]
      change ((∀ f ∈ w.map untag, (0 : ℕ) ≠ f.1 ∨ t.col ≠ f.2.col) ∧ distinctSites (w.map untag)) ↔ _
      rw [List.forall_mem_map, all_split, ih]
      simp [untag, List.mem_map, eq_comm, and_assoc]
    · simp only [List.map_cons, split_l_skip, split_r_cons, distinct_cons]
      change ((∀ f ∈ w.map untag, r+1 ≠ f.1 ∨ t.col ≠ f.2.col) ∧ distinctSites (w.map untag)) ↔
        _ ∧ ((∀ f ∈ Glue.rights w, r ≠ f.1 ∨ t.col ≠ f.2.col) ∧ distinctSites (Glue.rights w))
      rw [List.forall_mem_map, all_split, ih]
      simp [untag, and_left_comm]

lemma bounds_split (n : ℕ) (w : List (Tile ⊕ Ev)) :
    Fits (n+2) (w.map untag) ↔ RowFits (Glue.lefts w) ∧ Fits (n+1) (Glue.rights w) := by
  simp only [Fits, RowFits, disjoint_split, List.forall_mem_map, all_split, untag,
    Nat.zero_lt_succ, true_and, Nat.succ_lt_succ_iff]
  tauto

lemma histories_split (n : ℕ) (w : List (Tile ⊕ Ev)) :
    upper (w.map untag) = rowUpper (Glue.lefts w) ∧
    lower (n+2) (w.map untag) = lower (n+1) (Glue.rights w) := by
  induction w with
  | nil => exact ⟨rfl,rfl⟩
  | cons e w ih =>
    rcases e with t | ⟨r,t⟩ <;> simp only [List.map_cons, split_l_cons, split_r_skip, split_l_skip, split_r_cons]
    all_goals simp [upper, lower, untag, rowUpper] at * <;> simp_all

lemma run_split (n : ℕ) (w : List (Tile ⊕ Ev)) (s t : Key) :
    Run (Glue.input li (ri (n+1))) (Glue.output lo (ro (n+1))) (splitKey s) w (splitKey t) ↔
    Run (src (n+2)) (dst (n+2)) s (w.map untag) t := by
  induction w generalizing s with
  | nil => exact splitKey_inj.eq_iff
  | cons e es ih =>
    simp only [List.map_cons, Run, ← split_src, ← split_dst, splitKey_inj.eq_iff, ih]

lemma run_lo (n : ℕ) (w : List Ev) (s t : Key) :
    Run (Port.collapse ∘ ri (n+1)) (Port.collapse ∘ ro (n+1)) (dropTop s) w (dropTop t) ↔
    Run (src (n+1)) (dst (n+1)) s w t := by
  induction w generalizing s with
  | nil => exact dropTop_inj.eq_iff
  | cons e es ih =>
    simp only [Run, Function.comp_apply, ri, ro, collapseR, dropTop_inj.eq_iff, src, dst] at *
    exact and_congr_right (fun _ => ih _)

lemma ready_grid (n : ℕ) (u : List Tile) (v : List Ev) :
    Glue.ready li lo (ri (n+1)) (ro (n+1)) (.left .top) u v .bot ↔
      RowRun u ∧ Run (src (n+1)) (dst (n+1)) .top v .bot ∧ rowLower u = upper v := by
  change RowRun u ∧ Run _ _ (dropTop .top) v (dropTop .bot) ∧ _ ↔ _
  change _ ∧ _ ∧ Glue.history li lo u = Glue.history (ri (n+1)) (ro (n+1)) v ↔ _
  rw [run_lo, histL, histR]

@[simp] lemma proj_untag (w : List (Tile ⊕ Ev)) : (w.map untag).map tag = w := by
  simp [List.map_map, Function.comp_def]
@[simp] lemma proj_tag (w : List Ev) : (w.map tag).map untag = w := by
  simp [List.map_map, Function.comp_def]

lemma lengths (w : List (Tile ⊕ Ev)) : (Glue.lefts w).length + (Glue.rights w).length = w.length := by
  induction w with
  | nil => rfl
  | cons e w ih => cases e <;> simp only [split_l_cons, split_l_skip, split_r_cons, split_r_skip, List.length_cons] <;> omega

def Row (p : List (Fin 4)) := {w : List Tile // RowFits w ∧ RowRun w ∧ rowUpper w = p}

def cut {n : ℕ} {p q : List (Fin 4)} (x : Board (n+2) p q) :
    (t : Row p) × Board (n+1) (rowLower t.val) q := by
  let w := x.val.map tag
  have hback : w.map untag = x.val := proj_tag _
  refine ⟨⟨Glue.lefts w, ?_⟩, ⟨Glue.rights w, ?_⟩⟩ <;>
   (obtain ⟨fit, hw, hp, hq⟩ := x.property
    rw [← hback] at fit hw hp hq
    obtain ⟨hf, hg⟩ := (bounds_split n w).1 fit
    have hr := (Glue.proj_run li lo (ri (n+1)) (ro (n+1))
      ((run_split n w .top .bot).2 hw)).1
    obtain ⟨ha, hb, hc⟩ := (ready_grid n _ _).1 hr
    obtain ⟨ht,hd⟩ := histories_split n w
    first | exact ⟨hf, ha, ht.symm.trans hp⟩ | exact ⟨hg, hb, hc.symm, hd.symm.trans hq⟩)

def paste {n : ℕ} {p q : List (Fin 4)} (x : (t : Row p) × Board (n+1) (rowLower t.val) q) :
    Board (n+2) p q := by
  let u := x.1.val
  let v := x.2.val
  let w := Glue.weave lo (ro (n+1)) (u.length + v.length) (.left .top) u v
  refine ⟨w.map untag, ?_⟩
  obtain ⟨hu,hr,hp⟩ := x.1.property
  obtain ⟨hv,hs,ht,hq⟩ := x.2.property
  obtain ⟨hw, h₁, h₂⟩ := Glue.weave_ready li lo (ri (n+1)) (ro (n+1))
    (u.length+v.length) (.left .top) u v .bot (by rfl)
    ((ready_grid n u v).2 ⟨hr,hs,ht.symm⟩)
  change Glue.lefts w = u at h₁
  change Glue.rights w = v at h₂
  refine ⟨(bounds_split n w).2 ?_, (run_split n w .top .bot).1 hw, ?_, ?_⟩
  · simpa [h₁,h₂] using And.intro hu hv
  · rw [(histories_split n w).1, h₁, hp]
  · rw [(histories_split n w).2, h₂, hq]

def cutEquiv (n : ℕ) (p q : List (Fin 4)) :
    Board (n+2) p q ≃ ((t : Row p) × Board (n+1) (rowLower t.val) q) where
  toFun := cut
  invFun := paste
  left_inv x := by
    apply Subtype.ext
    let w := x.val.map tag
    have hback : w.map untag = x.val := proj_tag _
    have hr := x.property.2.1
    rw [← hback] at hr
    have h := (Glue.proj_run li lo (ri (n+1)) (ro (n+1))
      ((run_split n w .top .bot).2 hr)).2 ((Glue.lefts w).length + (Glue.rights w).length) (by rw [lengths])
    change (Glue.weave lo (ro (n+1)) _ _ _ _).map untag = _
    exact (congrArg (List.map untag) h).trans hback
  right_inv x := by
    obtain ⟨⟨u,hu,hr,hp⟩, ⟨v,hv,hs,ht,hq⟩⟩ := x
    let w := Glue.weave lo (ro (n+1)) (u.length + v.length) (.left .top) u v
    obtain ⟨_, h₁, h₂⟩ := Glue.weave_ready li lo (ri (n+1)) (ro (n+1))
      (u.length+v.length) (.left .top) u v .bot (by rfl)
      ((ready_grid n u v).2 ⟨hr,hs,ht.symm⟩)
    change Glue.lefts w = u at h₁
    change Glue.rights w = v at h₂
    have htop : (cut (paste (n := n) (q := q) ⟨⟨u,hu,hr,hp⟩,⟨v,hv,hs,ht,hq⟩⟩)).1 = (⟨u,hu,hr,hp⟩ : Row p) := by
      apply Subtype.ext
      change Glue.lefts ((w.map untag).map tag) = u
      rw [proj_untag, h₁]
    apply Sigma.ext htop
    apply (Subtype.heq_iff_coe_eq (fun w => by rw [congrArg (fun z : Row p => rowLower z.val) htop])).2
    change Glue.rights ((w.map untag).map tag) = v
    rw [proj_untag, h₂]

def dirs : List Dir := [.north,.south,.west,.east]

def tiles : List Tile :=
  (List.finRange 4).flatMap fun c => dirs.flatMap fun d => dirs.map fun f => ⟨c,d,f⟩

@[simp] lemma mem_tiles (t : Tile) : t ∈ tiles := by
  rcases t with ⟨c,d,f⟩
  simp only [tiles, List.mem_flatMap, List.mem_map]
  refine ⟨c, by simp, d, ?_, f, ?_, rfl⟩
  · cases d <;> decide
  · cases f <;> decide

def outWords (s : Option Key) : List (List Tile) := if s = none then [[]] else []

def enumerate : ℕ → Option Key → List (Fin 4) → List (List Tile)
  | 0, s, _ => outWords s
  | k+1, s, used => outWords s ++ tiles.flatMap fun t =>
      if t.col ∉ used ∧ t.prev ≠ t.next ∧ s = (li t).collapse then
        (enumerate k (lo t).collapse (t.col::used)).map (t::·)
      else []

lemma mem_enum (k : ℕ) (s : Option Key) (used : List (Fin 4)) (w : List Tile) :
    w ∈ enumerate k s used ↔ w.length ≤ k ∧ RowFits w ∧
    (∀ t ∈ w, t.col ∉ used) ∧ Run (Port.collapse ∘ li) (Port.collapse ∘ lo) s w none := by
  induction k generalizing s used w with
  | zero => cases w <;> cases s <;> simp [enumerate, outWords, RowFits, Run]
  | succ k ih =>
    cases w with
    | nil =>
      simp only [enumerate, List.mem_append, List.mem_flatMap]
      have hem (t : Tile) : [] ∉ (if t.col ∉ used ∧ t.prev ≠ t.next ∧ s = (li t).collapse then
          (enumerate k (lo t).collapse (t.col::used)).map (t::·) else []) := by split <;> simp
      cases s <;> simp [hem, outWords, RowFits, Run]
    | cons e es =>
      have he : e::es ∉ outWords s := by cases s <;> simp [outWords]
      simp only [enumerate, List.mem_append, he, false_or, List.mem_flatMap, mem_tiles,
        true_and]
      have hm (t : Tile) :
          e::es ∈ (if t.col ∉ used ∧ t.prev ≠ t.next ∧ s = (li t).collapse then
            (enumerate k (lo t).collapse (t.col::used)).map (t::·) else []) ↔
          t = e ∧ (t.col ∉ used ∧ t.prev ≠ t.next ∧ s = (li t).collapse) ∧
            es ∈ enumerate k (lo t).collapse (t.col::used) := by
        split <;> rename_i htest <;> simp only [List.mem_map, List.cons.injEq, List.not_mem_nil] <;> grind
      simp only [hm, ih, RowFits, List.map_cons, List.nodup_cons,
        List.mem_cons, not_or, List.mem_map, not_exists,
        List.length_cons, Nat.succ_le_succ_iff, Run, Function.comp_apply]
      grind

def rowSet (p : List (Fin 4)) : Finset (List Tile) :=
  ((enumerate 4 (some .top) []).filter (fun w => rowUpper w == p)).toFinset

@[simp] lemma mem_rowSet (p : List (Fin 4)) (w : List Tile) :
    w ∈ rowSet p ↔ RowFits w ∧ RowRun w ∧ rowUpper w = p := by
  simp only [rowSet, List.mem_toFinset, List.mem_filter, beq_iff_eq, mem_enum,
    List.not_mem_nil, not_false_eq_true, implies_true, true_and, RowRun]
  have h (hf : RowFits w) : w.length ≤ 4 := by simpa using hf.1.length_le_card
  tauto

def rowEquiv (p : List (Fin 4)) : Row p ≃ ↥(rowSet p) :=
  Equiv.subtypeEquivRight fun w => (mem_rowSet p w).symm

instance (p : List (Fin 4)) : Finite (Row p) := Finite.of_equiv _ (rowEquiv p).symm

def firstRow (t : Tile) : Ev := (0,t)

lemma collapseL (t : Tile) (b : Bool) (d : Dir) :
    (portL t b d).collapse = dropBot (key 1 0 t.col b d) := by cases d <;> rfl

lemma oneRun (u : List Tile) (s t : Key) :
    Run (src 1) (dst 1) s (u.map firstRow) t ↔
      Run (Port.collapse ∘ li) (Port.collapse ∘ lo) (dropBot s) u (dropBot t) := by
  induction u generalizing s with
  | nil => exact dropBot_inj.eq_iff.symm
  | cons e es ih =>
    simp only [List.map_cons, Run, firstRow, Function.comp_apply, li, lo, collapseL,
      src, dst, ih, dropBot_inj.eq_iff]

lemma oneFits (u : List Tile) : Fits 1 (u.map firstRow) ↔ RowFits u := by
  simp only [Fits, distinctSites, List.pairwise_map, firstRow, ne_self_iff_false, false_or,
    List.forall_mem_map, Nat.zero_lt_one, true_and, RowFits, List.nodup_iff_pairwise_ne]

lemma oneHist (u : List Tile) :
    upper (u.map firstRow) = rowUpper u ∧ lower 1 (u.map firstRow) = rowLower u := by
  simp [upper, lower, firstRow, rowUpper, rowLower, List.flatMap_map]

lemma oneBack {w : List Ev} (h : Fits 1 w) : (w.map Prod.snd).map firstRow = w := by
  rw [List.map_map]
  calc
   _ = w.map id := ?_
   _ = w := List.map_id w
  apply List.map_congr_left
  rintro ⟨r,t⟩ ht
  have hr := (h.2 (r,t) ht).1
  have : r = 0 := by omega
  subst r; rfl

def oneEquiv (p q : List (Fin 4)) :
    Board 1 p q ≃ {t : Row p // rowLower t.val = q} where
  toFun x := by
    let u := x.val.map Prod.snd
    have hb : u.map firstRow = x.val := oneBack x.property.1
    refine ⟨⟨u, ?_⟩, ?_⟩
    · exact ⟨(oneFits u).1 (hb ▸ x.property.1), (oneRun u .top .bot).1 (hb ▸ x.property.2.1),
        (oneHist u).1.symm.trans (hb ▸ x.property.2.2.1)⟩
    · exact (oneHist u).2.symm.trans (hb ▸ x.property.2.2.2)
  invFun x := by
    let u := x.val.val
    refine ⟨u.map firstRow, (oneFits u).2 x.val.property.1,
      (oneRun u .top .bot).2 x.val.property.2.1, ?_, ?_⟩
    · exact (oneHist u).1.trans x.val.property.2.2
    · exact (oneHist u).2.trans x.property
  left_inv x := by apply Subtype.ext; exact oneBack x.property.1
  right_inv x := by
    apply Subtype.ext; apply Subtype.ext
    change (x.val.val.map firstRow).map Prod.snd = x.val.val
    simp [List.map_map, firstRow, Function.comp_def]

instance boardFinite (n : ℕ) (p q : List (Fin 4)) : Finite (Board (n+1) p q) := by
  induction n generalizing p with
  | zero => exact Finite.of_equiv _ (oneEquiv p q).symm
  | succ n ih =>
    let (t : Row p) : Finite (Board (n+1) (rowLower t.val) q) := ih _
    exact Finite.of_equiv _ (cutEquiv n p q).symm

/-- An ordered list records the columns crossed at the boundary between rows.
Of the twenty profiles reached from the northwest corner, twelve can return to
the southwest corner. Reflecting the columns pairs those twelve profiles. The
symmetric and antisymmetric transition matrices each have size six, accounting
for the two factors in the denominator. -/
def profile : Fin 20 → List (Fin 4) :=
  ![[0],[0,1,2],[0,1,3],[0,2,1],[0,2,3],[0,3,1],[0,3,2],[1],[1,2,3],[1,3,2],[2],[3],[2,0,1],[2,1,0],[3,0,1],[3,1,0],[3,0,2],[3,1,2],[3,2,0],[3,2,1]]

def edges : Fin 20 → List (Fin 20) :=
  ![[0,1,2,3,4,6,5,7,8,9,10,11],[1,2,10,11],[2,1,4,11,10],[3,5],[2,4,8,11],[3,5,6],[6,5,9],[7,8,9,0,4,6,10,11],[8,4,11],[9,6],[10,12,13,7,0,11,14,15],[11,14,16,15,17,19,18,10,12,13,7,0],[12,14],[13,0,15],[14,16,12],[15,18,13,0],[16,14,17],[16,17],[15,18,19,0,7],[19,18,7,0]]

def rows (i : Fin 20) := (enumerate 4 (some .top) []).filter fun w => rowUpper w == profile i

lemma rows_mem (i : Fin 20) (w : List Tile) :
    w ∈ rows i ↔ RowFits w ∧ RowRun w ∧ rowUpper w = profile i := by
  rw [← mem_rowSet]
  simp [rows, rowSet]

set_option maxRecDepth 15000 in
set_option maxHeartbeats 8000000 in
lemma rowTable : ∀ i : Fin 20, (rows i).Nodup ∧
    (rows i).map rowLower = (edges i).map profile := by decide

lemma edgeLength (i : Fin 20) : (edges i).length = (rows i).length := by
  simpa using congrArg List.length (rowTable i).2.symm

def ithRow (i : Fin 20) : Fin (edges i).length ≃ Row (profile i) :=
  ((finCongr (edgeLength i)).trans ((rowTable i).1.getEquiv _)).trans
    (Equiv.subtypeEquivRight fun w => rows_mem i w)

lemma ithLower (i : Fin 20) (k : Fin (edges i).length) :
    rowLower ((ithRow i k).val) = profile ((edges i).get k) := by
  have a := congrArg (fun l : List (List (Fin 4)) => l[k.val]?) (rowTable i).2
  have h₁ : k.val < (rows i).length := by rw [← edgeLength]; exact k.isLt
  change rowLower ((rows i)[k.val]) = profile ((edges i)[k.val])
  simpa [List.getElem?_map, List.getElem?_eq_getElem h₁,
    List.getElem?_eq_getElem k.isLt] using a

def AtHeight : ℕ → List (Fin 4) → Type
  | 0, p => PLift (p = [0])
  | n+1, p => Board (n+1) p [0]

instance (n : ℕ) (p : List (Fin 4)) : Finite (AtHeight n p) := by
  cases n with
  | zero => change Finite (PLift _); infer_instance
  | succ n => exact boardFinite _ _ _

def peel (n : ℕ) (p : List (Fin 4)) :
    AtHeight (n+1) p ≃ ((t : Row p) × AtHeight n (rowLower t.val)) := by
  cases n with
  | zero =>
    refine (oneEquiv p [0]).trans ?_
    exact { toFun := fun t => ⟨t.val, ⟨t.property⟩⟩
            invFun := fun t => ⟨t.1, t.2.down⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  | succ n => exact cutEquiv n p [0]

def nextEquiv (n : ℕ) (i : Fin 20) : AtHeight (n+1) (profile i) ≃
    ((k : Fin (edges i).length) × AtHeight n (profile ((edges i).get k))) :=
  (peel n (profile i)).trans (((Equiv.sigmaCongrLeft (ithRow i)).symm).trans
    (Equiv.sigmaCongrRight fun k => Equiv.cast (congrArg (AtHeight n) (ithLower i k))))

abbrev Vec := Fin 20 → ℤ

def advance (v : Vec) (i : Fin 20) : ℤ := ∑ k : Fin (edges i).length, v ((edges i).get k)

noncomputable def total (n : ℕ) (i : Fin 20) : ℤ := Nat.card (AtHeight n (profile i))

lemma total_succ (n : ℕ) : total (n+1) = advance (total n) := by
  funext i
  simp only [total, advance, Nat.card_congr (nextEquiv n i), Nat.card_sigma, Nat.cast_sum]

def act : Vec →ₗ[ℤ] Vec where
  toFun := advance
  map_add' u v := by funext i; simp [advance, Finset.sum_add_distrib]
  map_smul' a v := by funext i; exact (Finset.mul_sum _ _ _).symm

/-- Periodic checkpoints keep the kernel computation of the transfer recurrence small. -/
def checkpoint : Fin 5 → Vec :=
  ![![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![28,18,19,0,12,0,0,24,10,0,29,38,0,11,0,16,0,0,21,17],
    ![5493,2935,3374,0,2367,0,0,4314,1738,0,4276,5382,0,1732,0,2323,0,0,3317,2902],
    ![895519,480598,551019,0,386425,0,0,707538,286004,0,707963,896476,0,286290,0,386979,0,0,551567,480926],
    ![147666219,79232389,90856957,0,63731851,0,0,116641175,47159367,0,116638419,147657866,0,47156755,0,63726656,0,0,90849836,79226622]]

def sample (k : Fin 13) : Vec :=
  advance^[k.val % 3] (checkpoint ⟨k.val / 3, by omega⟩)

lemma total_zero : total 0 = sample 0 := by
  have h : ∀ i : Fin 20, (if profile i = [0] then (1 : ℤ) else 0) = sample 0 i := by decide
  funext i
  rw [← h i]
  change (Nat.card (PLift (profile i = [0])) : ℤ) = _
  split <;> rename_i he
  · letI : Nonempty (PLift (profile i = [0])) := ⟨⟨he⟩⟩
    rw [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩]
    rfl
  · letI : IsEmpty (PLift (profile i = [0])) := ⟨fun x => he x.down⟩
    simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
lemma sample_step : ∀ k : Fin 12, ∀ i : Fin 20,
    advance (sample k.castSucc) i = sample k.succ i := by decide

lemma sample_total (k : Fin 13) : total k.val = sample k := by
  obtain ⟨k,hk⟩ := k
  induction k with
  | zero => exact total_zero
  | succ k ih =>
    have ht : k < 12 := by omega
    rw [total_succ, ih (by omega)]
    exact funext (sample_step ⟨k,ht⟩)

def mix (f : ℕ → Vec) (n : ℕ) : Vec :=
  -(f (n+0)) - 4 • (f (n+1)) + 12 • (f (n+2)) + 40 • (f (n+3)) - 69 • (f (n+4)) - 94 • (f (n+5)) + 175 • (f (n+6)) - 16 • (f (n+7)) - 133 • (f (n+8)) + 124 • (f (n+9)) - 54 • (f (n+10)) + 12 • (f (n+11))

lemma base_relation : total 12 = mix total 0 := by
  have h (k : ℕ) (hk : k < 13) : total k = sample ⟨k,hk⟩ := sample_total ⟨k,hk⟩
  simp (disch := decide) only [mix, Nat.zero_add, h]
  funext i
  revert i
  decide

lemma all_relation (n : ℕ) : total (n+12) = mix total n := by
  induction n with
  | zero => exact base_relation
  | succ n ih =>
    have h := congrArg act ih
    change act (total (n+12)) = act (mix total n) at h
    simp only [mix, map_add, map_sub, map_neg, map_nsmul] at h
    simp only [show ∀ v, act v = advance v from fun _ => rfl, ← total_succ] at h
    simpa only [mix, Nat.succ_add] using h


def calls {E : Type} (f : E → Key) (k : Key) (w : List E) := (w.filter (fun e => f e == k)).length

lemma calls_cons {E : Type} (f : E → Key) (k : Key) (e : E) (w : List E) :
    calls f k (e::w) = (if f e = k then 1 else 0) + calls f k w := by
  by_cases h : f e = k <;> simp [calls, h, Nat.add_comm]

lemma flow {E : Type} {i o : E → Key} {s t : Key} {w : List E} (h : Run i o s w t) (k : Key) :
    calls i k w + (if t = k then 1 else 0) = calls o k w + (if s = k then 1 else 0) := by
  induction w generalizing s with
  | nil => subst s; rfl
  | cons e es ih =>
    obtain ⟨rfl,hr⟩ := h
    have a := ih hr
    simp only [calls_cons]
    omega

def boundary (k : Key) (h : ℕ) (w : List Ev) := w.flatMap fun e =>
  (if src h e = k then [e.2.col] else []) ++ (if dst h e = k then [e.2.col] else [])

lemma topKey (n : ℕ) (e : Ev) (b : Bool) (d : Dir) :
    key (n+1) e.1 e.2.col b d = .top ↔ e.1 = 0 ∧ d = .north := by
  cases d <;> simp [key] <;> split <;> simp_all
lemma botKey (n : ℕ) (e : Ev) (b : Bool) (d : Dir) :
    key (n+1) e.1 e.2.col b d = .bot ↔ e.1+1=n+1 ∧ d = .south := by
  cases d <;> simp [key] <;> split <;> simp_all

lemma bound_top (n : ℕ) (w : List Ev) : boundary .top (n+1) w = upper w := by
  apply List.flatMap_congr
  intro e _
  simp only [src, dst, topKey n e]
  by_cases h : e.1 = 0 <;> simp [h, sideLabels]
lemma bound_bot (n : ℕ) (w : List Ev) : boundary .bot (n+1) w = lower (n+1) w := by
  apply List.flatMap_congr
  intro e _
  simp only [src, dst, botKey n e, Nat.add_right_cancel_iff]
  by_cases h : e.1=n <;> simp [h, sideLabels]

lemma boundary_length (k : Key) (h : ℕ) (w : List Ev) :
    (boundary k h w).length = calls (src h) k w + calls (dst h) k w := by
  induction w with
  | nil => rfl
  | cons e w ih =>
    by_cases hi : src h e = k <;> by_cases ho : dst h e = k <;>
      simp [boundary, calls_cons, hi, ho] at * <;> omega

lemma col_mem {h : ℕ} {w : List Ev} {k : Key} {e : Ev} (he : e ∈ w)
    (hc : src h e = k ∨ dst h e = k) : e.2.col ∈ boundary k h w := by
  apply List.mem_flatMap.mpr
  refine ⟨e,he,?_⟩
  rcases hc with h | h <;> simp [h]

lemma calls_zero {E : Type} {f : E → Key} {k : Key} {w : List E} (h : calls f k w = 0) :
    ∀ e ∈ w, f e ≠ k := by
  simpa [calls, List.filter_eq_nil_iff] using h

lemma noOuter {n : ℕ} {w : List Ev} (hr : Run (src (n+1)) (dst (n+1)) .top w .bot)
    (hu : upper w = [0]) (hl : lower (n+1) w = [0]) :
    ∀ e ∈ w, dst (n+1) e ≠ .top ∧ src (n+1) e ≠ .bot ∧
      (src (n+1) e = .top → e.2.col = 0) ∧ (dst (n+1) e = .bot → e.2.col = 0) := by
  rw [← bound_top n] at hu
  rw [← bound_bot n] at hl
  have a := boundary_length .top (n+1) w
  have b := boundary_length .bot (n+1) w
  rw [hu] at a
  rw [hl] at b
  have c := flow hr .top
  have d := flow hr .bot
  simp only [List.length_singleton, reduceCtorEq, ↓reduceIte, Nat.add_zero] at a b c d
  intro e he
  refine ⟨calls_zero (by omega : calls (dst (n+1)) .top w = 0) e he,
    calls_zero (by omega : calls (src (n+1)) .bot w = 0) e he, ?_, ?_⟩
  · intro ht; simpa [hu] using col_mem he (Or.inl ht)
  · intro ht; simpa [hl] using col_mem he (Or.inr ht)

abbrev Pos := ℤ × ℤ

def center (e : Ev) : Pos := (e.1, (e.2.col.val : ℤ))
def move (p : Pos) : Dir → Pos
  | .north => (p.1-1,p.2)
  | .south => (p.1+1,p.2)
  | .west => (p.1,p.2-1)
  | .east => (p.1,p.2+1)

def enter (e : Ev) : Pos × Pos := (move (center e) e.2.prev, center e)
def leave (e : Ev) : Pos × Pos := (center e, move (center e) e.2.next)

def startPair : Pos × Pos := ((-1,0),(0,0))
def endPair (n : ℕ) : Pos × Pos := ((n,0),((n:ℤ)+1,0))

def vertPair (r : ℕ) (c : Fin 4) (b : Bool) : Pos × Pos :=
  let u : Pos := ((r:ℤ)-1,(c.val:ℤ))
  let v : Pos := (r,(c.val:ℤ))
  if b then (u,v) else (v,u)

def horizPair (r c : ℕ) (b : Bool) : Pos × Pos :=
  let u : Pos := (r,(c:ℤ)-1)
  let v : Pos := (r,c)
  if b then (u,v) else (v,u)

def realize (n : ℕ) : Key → Pos × Pos
  | .top => startPair
  | .bot => endPair n
  | .vert r c b => vertPair r c b
  | .horiz r c b => horizPair r c b

lemma realize_src (n : ℕ) (e : Ev) (hb : src (n+1) e ≠ .bot)
    (ht : src (n+1) e = .top → e.2.col = 0) :
    realize n (src (n+1) e) = enter e := by
  rcases e with ⟨r,c,d,f⟩
  by_cases h : r = 0 <;> by_cases hh : r = n <;> cases d <;>
    simp_all [src, key, realize, enter, center, move, vertPair, horizPair, startPair]

lemma realize_dst (n : ℕ) (e : Ev) (ht : dst (n+1) e ≠ .top)
    (hb : dst (n+1) e = .bot → e.2.col = 0) :
    realize n (dst (n+1) e) = leave e := by
  rcases e with ⟨r,c,d,f⟩
  by_cases h : r = 0 <;> by_cases hh : r = n <;> have hrev : n = r ↔ r = n := eq_comm <;> cases f <;>
    simp_all [dst, key, realize, leave, center, move, vertPair, horizPair, endPair]

lemma push_run {E S T : Type} {i o : E → S} {j p : E → T} (f : S → T)
    {s t : S} {w : List E} (hr : Run i o s w t)
    (hi : ∀ e ∈ w, f (i e) = j e) (ho : ∀ e ∈ w, f (o e) = p e) :
    Run j p (f s) w (f t) := by
  induction w generalizing s with
  | nil => exact congrArg f hr
  | cons e w ih =>
    obtain ⟨rfl,hs⟩ := hr
    simp only [List.forall_mem_cons] at hi ho
    exact ⟨hi.1, ho.1 ▸ ih hs hi.2 ho.2⟩

lemma raw_of_board {n : ℕ} (x : Board (n+1) [0] [0]) :
    Run enter leave startPair x.val (endPair n) := by
  obtain ⟨_,hs,ht,hb⟩ := x.property
  have h := noOuter hs ht hb
  exact push_run (realize n) hs (fun e he => realize_src n e (h e he).2.1 (h e he).2.2.1)
    (fun e he => realize_dst n e (h e he).1 (h e he).2.2.2)

def column (p : Pos) : Fin 4 := Fin.ofNat 4 p.2.toNat

def classify (n : ℕ) (x : Pos × Pos) : Key :=
  if x.1.1 = x.2.1 then
    .horiz x.1.1.toNat (max x.1.2 x.2.2).toNat (decide (x.1.2 < x.2.2))
  else
    let cut := (max x.1.1 x.2.1).toNat
    if cut = 0 then .top else if cut = n+1 then .bot
    else .vert cut (column x.1) (decide (x.1.1 < x.2.1))

lemma classify_enter (n : ℕ) (e : Ev) (hr : e.1 < n+1) : classify n (enter e) = src (n+1) e := by
  rcases e with ⟨r,c,d,f⟩
  change r < n+1 at hr
  have hne : r ≠ n+1 := by omega
  cases d <;> simp [classify, enter, src, key, move, center, column, hne, Fin.ofNat_eq_cast]

lemma classify_leave (n : ℕ) (e : Ev) (hr : e.1 < n+1) : classify n (leave e) = dst (n+1) e := by
  rcases e with ⟨r,c,d,f⟩
  change r < n+1 at hr
  have hne : r ≠ n+1 := by omega
  have h₁ : ¬ (r:ℤ) = (r:ℤ)-1 := by omega
  have h₂ : ¬ (r:ℤ) < (r:ℤ)-1 := by omega
  have h₃ : ¬ (c.val:ℤ) < (c.val:ℤ)-1 := by omega
  cases f <;> simp [h₁,h₂,h₃,classify, leave, dst, key, move, center, column, hne, Fin.ofNat_eq_cast]

def marked (out : Pos → Prop) [DecidablePred out] (w : List Ev) := w.flatMap fun e =>
  (if out (enter e).1 then [column (center e)] else []) ++
  (if out (leave e).2 then [column (center e)] else [])

lemma marked_run (out : Pos → Prop) [DecidablePred out] (e : Ev) (w : List Ev)
    (s t : Pos × Pos) (hr : Run enter leave s (e::w) t)
    (h : ∀ f ∈ e::w, ¬out (center f)) :
    marked out (e::w) =
      (if out s.1 then [column s.2] else []) ++ (if out t.2 then [column t.1] else []) := by
  induction w generalizing e s with
  | nil =>
    obtain ⟨rfl,ht⟩ := hr
    change leave e = t at ht
    subst t
    simp [marked, enter, leave]
  | cons f w ih =>
    obtain ⟨rfl,hs⟩ := hr
    have heq := hs.1
    have ho : ¬out (leave e).2 := by
      rw [heq]; exact h f (by simp)
    have hi : ¬out (leave e).1 := h e (by simp)
    have hx := ih f (leave e) hs (fun g hg => h g (by simp [hg]))
    change ((_ ++ _) ++ marked out (f::w)) = _
    rw [hx]
    simp [ho,hi,enter]

lemma upper_mark (w : List Ev) : upper w = marked (fun p => p.1 < 0) w := by
  apply List.flatMap_congr
  rintro ⟨r,c,d,f⟩ _
  cases r <;> cases d <;> cases f <;>
    simp [sideLabels, enter, leave, center, move, column, Fin.ofNat_eq_cast] <;> omega

lemma lower_mark (n : ℕ) (w : List Ev) (hr : ∀ e ∈ w, e.1 < n+1) :
    lower (n+1) w = marked (fun p => (n:ℤ) < p.1) w := by
  apply List.flatMap_congr
  rintro ⟨r,c,d,f⟩ he
  have h := hr _ he
  change r < n+1 at h
  by_cases hh : r = n
  · subst r; cases d <;> cases f <;> simp [sideLabels, enter, leave, center, move, column, Fin.ofNat_eq_cast]
  · have h₁ : ¬(n:ℤ) < r := by omega
    have h₂ : ¬(n:ℤ) < (r:ℤ)+1 := by omega
    have h₃ : ¬(n:ℤ) < (r:ℤ)-1 := by omega
    cases d <;> cases f <;> simp [enter, leave, center, move, hh, h₁,h₂,h₃]

lemma board_of_raw {n : ℕ} {w : List Ev} (hf : Fits (n+1) w)
    (hr : Run enter leave startPair w (endPair n)) :
    Run (src (n+1)) (dst (n+1)) .top w .bot ∧ upper w = [0] ∧ lower (n+1) w = [0] := by
  have h₀ : classify n startPair = .top := by simp [classify, startPair]
  have h₁ : classify n (endPair n) = .bot := by simp [classify, endPair]
  refine ⟨h₀ ▸ h₁ ▸ push_run (classify n) hr (fun e he => classify_enter n e (hf.2 _ he).1)
    (fun e he => classify_leave n e (hf.2 _ he).1), ?_⟩
  cases w with
  | nil =>
    change startPair = endPair n at hr
    have := congrArg (fun p : Pos × Pos => p.1.1) hr
    simp [startPair,endPair] at this
  | cons e es =>
    rw [upper_mark, lower_mark n _ (fun f h => (hf.2 f h).1)]
    rw [marked_run _ e es _ _ hr (by intro f _; simp [center])]
    rw [marked_run _ e es _ _ hr (by intro f hh; have hb := (hf.2 f hh).1; change ¬(n:ℤ) < (f.1:ℤ); omega)]
    simp [startPair, endPair, column] <;> omega

open OMA.S_oeis_a216211

def site (e : Ev) : Site := (e.1,e.2.col.val)
def loc (a : Site) : Pos := (a.1,a.2)

lemma lift_site (e : Ev) : loc (site e) = center e := rfl

lemma loc_inj : Function.Injective loc := by
  rintro ⟨r,c⟩ ⟨t,d⟩ h; simpa [loc] using h

def AdjPos (p q : Pos) : Prop := ∃ d, move p d = q

lemma adj_loc (u v : Site) : adjacent u v ↔ AdjPos (loc u) (loc v) := by
  rcases u with ⟨r,c⟩; rcases v with ⟨t,d⟩
  unfold adjacent AdjPos
  constructor
  · simp only [Nat.dist]
    intro h
    by_cases a : r=t
    · subst t
      by_cases b : c<d
      · exact ⟨.east, by simp [move,loc]; omega⟩
      · exact ⟨.west, by simp [move,loc]; omega⟩
    · by_cases b : r<t
      · exact ⟨.south, by simp [move,loc]; constructor <;> omega⟩
      · exact ⟨.north, by simp [move,loc]; constructor <;> omega⟩
  · rintro ⟨f,h⟩
    cases f <;> simp [move,loc] at h <;> simp [Nat.dist] <;> omega

def choose (p q : Pos) : Dir :=
  if q.1<p.1 then .north else if p.1<q.1 then .south else if q.2<p.2 then .west else .east

@[simp] lemma choose_move (p : Pos) (d : Dir) : choose p (move p d) = d := by
  cases d <;> simp [choose, move]

lemma move_choose {p q : Pos} (h : AdjPos p q) : move p (choose p q) = q := by
  obtain ⟨d,rfl⟩ := h
  rw [choose_move]

lemma adj_rev {p q : Pos} (h : AdjPos p q) : AdjPos q p := by
  obtain ⟨d,rfl⟩ := h
  cases d with
  | north => exact ⟨.south, by cases p; simp [move]⟩
  | south => exact ⟨.north, by cases p; simp [move]⟩
  | east => exact ⟨.west, by cases p; simp [move]⟩
  | west => exact ⟨.east, by cases p; simp [move]⟩

def Match (p q : Pos) : List Ev → Prop
  | [] => True
  | e::w => move (center e) e.2.prev = p ∧
    move (center e) e.2.next = (w.map center).headD q ∧ Match (center e) q w

lemma raw_match (p c l q : Pos) (w : List Ev) :
    Run enter leave (p,c) w (l,q) ↔
      c = (w.map center).headD q ∧ l = (w.map center).getLastD p ∧ Match p q w := by
  induction w generalizing p c with
  | nil => simp [Run, Match, eq_comm, and_comm]
  | cons e es ih =>
    change ((_ = enter e) ∧ Run enter leave (center e, move (center e) e.2.next) es (l,q)) ↔ _
    rw [ih]
    cases es <;> simp [enter, Match, List.getLast?_cons, eq_comm, and_assoc, and_left_comm, and_comm]

def shape (a : Site) (p q : Pos) : Ev :=
  (a.1,⟨Fin.ofNat 4 a.2, choose (loc a) p, choose (loc a) q⟩)

def paint (p q : Pos) : List Site → List Ev
  | [] => []
  | a::w => shape a p ((w.map loc).headD q) :: paint (loc a) q w

lemma site_shape (a : Site) (p q : Pos) (hc : a.2 < 4) : site (shape a p q) = a := by
  rcases a with ⟨r,c⟩; simp [site,shape,Fin.ofNat, Nat.mod_eq_of_lt hc]

lemma paint_sites (p q : Pos) (w : List Site) (hb : ∀ a ∈ w, a.2 < 4) :
    (paint p q w).map site = w := by
  induction w generalizing p with
  | nil => rfl
  | cons a w ih => simp only [List.forall_mem_cons] at hb; simp [paint, site_shape _ _ _ hb.1, ih _ hb.2]

lemma paint_centers (p q : Pos) (w : List Site) (hb : ∀ a ∈ w, a.2 < 4) :
    (paint p q w).map center = w.map loc := by
  calc
    _ = ((paint p q w).map site).map loc := by rw [List.map_map]; rfl
    _ = w.map loc := by rw [paint_sites _ _ _ hb]

lemma paint_back (p q : Pos) (w : List Ev) (hm : Match p q w) :
    paint p q (w.map site) = w := by
  induction w generalizing p with
  | nil => rfl
  | cons e w ih =>
    obtain ⟨h₁,h₂,h₃⟩ := hm
    simp only [List.map_cons, paint, List.map_map]
    change shape (site e) p ((w.map center).headD q) :: paint (center e) q (w.map site) = _
    rw [ih _ h₃, ← h₁, ← h₂]
    rcases e with ⟨r,c,d,f⟩
    simp [shape, site, loc, center, Fin.ofNat_eq_cast, choose_move]

lemma sites_distinct (w : List Ev) : distinctSites w ↔ (w.map site).Nodup := by
  simp only [distinctSites, List.nodup_iff_pairwise_ne, List.pairwise_map]
  constructor <;> intro h <;> apply h.imp <;> rintro a b hh <;> simp_all [site, Prod.ext_iff] <;> grind

lemma paint_valid (p q : Pos) (w : List Site) (hb : ∀ a ∈ w, a.2 < 4)
    (hc : (p :: (w.map loc ++ [q])).IsChain AdjPos) (hn : (p :: (w.map loc ++ [q])).Nodup) :
    Match p q (paint p q w) ∧ ∀ e ∈ paint p q w, e.2.prev ≠ e.2.next := by
  induction w generalizing p with
  | nil => simp [Match, paint]
  | cons a w ih =>
    simp only [List.map_cons, List.cons_append, List.isChain_cons_cons] at hc
    simp only [List.map_cons, List.cons_append, List.nodup_cons] at hn
    simp only [List.forall_mem_cons] at hb
    let z := (w.map loc).headD q
    have hz : z ∈ w.map loc ++ [q] := by cases w <;> simp [z]
    have hstep : AdjPos (loc a) z := by cases w <;> simpa [z, List.isChain_cons_cons] using hc.2.rel_head? (by simp)
    have hpz : p ≠ z := by intro h; exact hn.1 (by simp [h,hz])
    have htail := ih (loc a) hb.2 hc.2 (List.nodup_cons.mpr hn.2)
    have cen : center (shape a p z) = loc a := by
      rw [← lift_site, site_shape _ _ _ hb.1]
    have h₁ := move_choose (adj_rev hc.1)
    have h₂ := move_choose hstep
    have hnturn : choose (loc a) p ≠ choose (loc a) z := by
      intro h; exact hpz (h₁.symm.trans ((congrArg (move (loc a)) h).trans h₂))
    change Match p q (shape a p z :: paint (loc a) q w) ∧ _
    refine ⟨⟨?_, ?_, cen ▸ htail.1⟩, ?_⟩
    · change move (center (shape a p z)) (choose (loc a) p) = p
      rw [cen]; exact h₁
    · change move (center (shape a p z)) (choose (loc a) z) = _
      rw [cen, paint_centers _ _ _ hb.2]; exact h₂
    · exact List.forall_mem_cons.mpr ⟨hnturn,htail.2⟩

lemma match_chain (p q : Pos) (w : List Ev) (hm : Match p q w) : (w.map site).IsChain adjacent := by
  induction w generalizing p with
  | nil => exact .nil
  | cons e es ih =>
    cases es with
    | nil => exact .singleton _
    | cons f fs =>
      apply List.isChain_cons_cons.mpr
      exact ⟨(adj_loc _ _).2 ⟨e.2.next, hm.2.1⟩, ih _ hm.2.2⟩

lemma padded_walk {n : ℕ} {w : List Site} (hw : isWalk (n+1) 4 (0,0) (n,0) w) :
    (startPair.1 :: (w.map loc ++ [(endPair n).2])).IsChain AdjPos ∧
    (startPair.1 :: (w.map loc ++ [(endPair n).2])).Nodup := by
  obtain ⟨hh,hl,hn,hc,hb⟩ := hw
  have hn₁ : (w.map loc).Nodup := hn.map loc_inj
  have hc₁ : (w.map loc).IsChain AdjPos :=
    (List.isChain_map loc).mpr ((List.IsChain.iff adj_loc).mp hc)
  have hfirst : (w.map loc).head? = some (0,0) := by simp [hh,loc]
  have hlast : (w.map loc).getLast? = some ((n:ℤ),0) := by simp [hl,loc]
  have hg : (w.map loc ++ [(endPair n).2]).head? = some (0,0) := by simp [List.head?_append,hfirst]
  refine ⟨List.isChain_cons.mpr ⟨?_, List.isChain_append.mpr ⟨hc₁,.singleton _,?_⟩⟩,?_⟩
  · simpa [hg] using (show AdjPos startPair.1 (0,0) from ⟨.south, by decide⟩)
  · simp only [hlast, List.head?_cons, Option.mem_some_iff]
    rintro x rfl y rfl
    exact ⟨.south,rfl⟩
  · simp only [List.nodup_cons, List.mem_append, List.mem_singleton, List.mem_map,
      not_or, not_exists, List.nodup_append, hn₁, true_and]
    simp [startPair, endPair, loc] at *
    grind

def Walks (n : ℕ) := {w : List Site // isWalk (n+1) 4 (0,0) (n,0) w}

def ofWalk (n : ℕ) (x : Walks n) : Board (n+1) [0] [0] := by
  let w := paint startPair.1 (endPair n).2 x.val
  refine ⟨w, ?_⟩
  obtain ⟨hp,ht,hn,_,hb⟩ := x.property
  have hc : ∀ a ∈ x.val, a.2 < 4 := fun a ha => (hb a ha).2
  have hcent : w.map center = x.val.map loc := paint_centers _ _ _ hc
  have hsite : w.map site = x.val := paint_sites _ _ _ hc
  obtain ⟨hchain,hnod⟩ := padded_walk x.property
  obtain ⟨hm,hnturn⟩ := paint_valid _ _ _ hc hchain hnod
  have hfit : Fits (n+1) w := by
    refine ⟨(sites_distinct w).2 (hsite ▸ hn), fun e he => ⟨?_,hnturn e he⟩⟩
    exact (hb (site e) (hsite ▸ List.mem_map_of_mem he)).1
  have hraw : Run enter leave startPair w (endPair n) := by
    apply (raw_match _ _ _ _ _).2
    refine ⟨?_,?_,hm⟩
    · simp [hcent,hp,startPair,loc]
    · simp [hcent, ht,loc]
  exact ⟨hfit, board_of_raw hfit hraw⟩

def toWalk (n : ℕ) (x : Board (n+1) [0] [0]) : Walks n := by
  refine ⟨x.val.map site, ?_⟩
  have hraw := raw_of_board x
  obtain ⟨hh,hl,hm⟩ := (raw_match _ _ _ _ _).1 hraw
  have hne : x.val ≠ [] := by
    intro he
    rw [he] at hraw
    change startPair = endPair n at hraw
    have := congrArg (fun x : Pos × Pos => x.1.1) hraw
    simp [startPair, endPair] at this
  have hhead := List.head?_eq_some_head hne
  have hlast := List.getLast?_eq_some_getLast hne
  refine ⟨?_,?_, (sites_distinct _).1 x.property.1.1, match_chain _ _ _ hm,?_⟩
  · simp [hhead] at hh
    simp [hhead]
    apply loc_inj
    exact hh.symm
  · simp [hlast] at hl
    simp [hlast]
    apply loc_inj
    exact hl.symm
  · simp only [List.forall_mem_map]
    intro e he; exact ⟨(x.property.1.2 e he).1, e.2.col.isLt⟩

def walksEquiv (n : ℕ) : Walks n ≃ Board (n+1) [0] [0] where
  toFun := ofWalk n
  invFun := toWalk n
  left_inv x := Subtype.ext (paint_sites _ _ x.val (fun a h => (x.property.2.2.2.2 a h).2))
  right_inv x := Subtype.ext (paint_back _ _ x.val ((raw_match _ _ _ _ _).1 (raw_of_board x)).2.2)

lemma count_total (n : ℕ) : count (n+1) = total (n+1) 0 := by
  change (Nat.card (Walks n) : ℤ) = (Nat.card (Board (n+1) [0] [0]) : ℤ)
  rw [Nat.card_congr (walksEquiv n)]

lemma count_none : count 0 = 0 := by
  let : IsEmpty {w : List Site // isWalk 0 4 (0,0) (0-1,0) w} :=
    ⟨fun x => Nat.not_lt_zero _ (x.property.2.2.2.2 _ (List.mem_of_head? x.property.1)).1⟩
  simp [count]

lemma recurrence (n : ℕ) : count (n+13) =
    12*count (n+12) - 54*count (n+11) + 124*count (n+10) - 133*count (n+9) -
    16*count (n+8) + 175*count (n+7) - 94*count (n+6) - 69*count (n+5) +
    40*count (n+4) + 12*count (n+3) - 4*count (n+2) - count (n+1) := by
  have h := congrFun (all_relation (n+1)) 0
  simp only [mix, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, nsmul_eq_mul,
    Nat.cast_ofNat] at h
  simp only [Nat.add_assoc, Nat.reduceAdd, Pi.mul_apply, Pi.ofNat_apply] at h
  simp only [count_total, Nat.add_assoc, Nat.reduceAdd]
  linarith only [h]


lemma initials (k : Fin 13) : count k.val = (if k.val = 0 then 0 else sample k 0) := by
  rcases k with ⟨j,hj⟩
  cases j with
  | zero => exact count_none
  | succ j =>
    rw [count_total]
    exact congrFun (sample_total ⟨j+1,hj⟩) 0

set_option maxHeartbeats 4000000 in
lemma initialColumn : ∀ k : Fin 13, sample k 0 =
    ![1,1,4,28,178,1008,5493,29879,163357,895519,4911542,26932856,147666219] k := by decide

open PowerSeries

noncomputable def series := PowerSeries.mk count

lemma generating :
    (let x : PowerSeries ℤ := X
     series * ((1-8*x+15*x^2-5*x^3-9*x^4+2*x^5+x^6) *
        (1-4*x+7*x^2-3*x^3-7*x^4+2*x^5+x^6)) =
       x*(1-8*x+34*x^2-66*x^3+21*x^4+85*x^5-64*x^6-45*x^7+26*x^8+11*x^9-3*x^10-x^11)) := by
  let x : PowerSeries ℤ := X
  have hD : series * ((1-8*x+15*x^2-5*x^3-9*x^4+2*x^5+x^6) *
      (1-4*x+7*x^2-3*x^3-7*x^4+2*x^5+x^6)) =
      (1 : ℤ) • (series * x^0) +
      (-12 : ℤ) • (series * x^1) +
      (54 : ℤ) • (series * x^2) +
      (-124 : ℤ) • (series * x^3) +
      (133 : ℤ) • (series * x^4) +
      (16 : ℤ) • (series * x^5) +
      (-175 : ℤ) • (series * x^6) +
      (94 : ℤ) • (series * x^7) +
      (69 : ℤ) • (series * x^8) +
      (-40 : ℤ) • (series * x^9) +
      (-12 : ℤ) • (series * x^10) +
      (4 : ℤ) • (series * x^11) +
      (1 : ℤ) • (series * x^12) := by simp only [zsmul_eq_mul]; push_cast; ring
  have hN : x*(1-8*x+34*x^2-66*x^3+21*x^4+85*x^5-64*x^6-45*x^7+26*x^8+11*x^9-3*x^10-x^11) =
      (1 : ℤ) • (x^1) +
      (-8 : ℤ) • (x^2) +
      (34 : ℤ) • (x^3) +
      (-66 : ℤ) • (x^4) +
      (21 : ℤ) • (x^5) +
      (85 : ℤ) • (x^6) +
      (-64 : ℤ) • (x^7) +
      (-45 : ℤ) • (x^8) +
      (26 : ℤ) • (x^9) +
      (11 : ℤ) • (x^10) +
      (-3 : ℤ) • (x^11) +
      (-1 : ℤ) • (x^12) := by simp only [zsmul_eq_mul]; push_cast; ring
  refine hD.trans (Eq.trans ?_ hN.symm)
  ext k
  simp only [map_add, map_zsmul, x, coeff_mul_X_pow', coeff_X_pow, series, coeff_mk]
  simp only [zsmul_eq_mul, Int.cast_id]
  by_cases hk : k < 13
  · have init (j : ℕ) (hj : j < 13) : count j = (if j = 0 then 0 else sample ⟨j,hj⟩ 0) := initials ⟨j,hj⟩
    interval_cases k <;> norm_num [init, initialColumn]
  · obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le (by omega : 13 ≤ k)
    have hr := recurrence m
    simp (disch := omega) only [if_pos, if_neg]
    simp (disch := decide) only [Nat.add_comm 13 m, Nat.add_sub_assoc, Nat.reduceSub]
    linarith only [hr]

end FourColumn

theorem OMA.solution : type_of% @OMA.S_oeis_a216211.main :=
  ⟨FourColumn.generating, FourColumn.recurrence⟩
