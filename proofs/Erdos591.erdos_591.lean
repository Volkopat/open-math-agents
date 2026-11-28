import FormalConjectures.ErdosProblems.«591»
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.SetTheory.Ordinal.Principal

/-!
# Erdős 591

The height-two game records a cut at each marked leaf. The theorem
`spacedFamilies` constructs a full-order family whose pairs give spaced games.
The theorem `ramseyOfPositiveOpening` reduces the Ramsey statement to
simultaneous triangle realization for winning strategies with a positive
opening. The zero-mark opening and an inside single-cut case give triangles.
-/

-- Credit: @aliuyar1234

namespace Erdos591Proof

open Set Filter

-- A position has a countable set of possible moves. Every play terminates,
-- although the lengths of the plays need not have a finite upper bound.
inductive PairGame where
  | terminal (win : Prop)
  | architect (children : ℕ → PairGame)
  | builder (children : ℕ → PairGame)

namespace PairGame

def value : PairGame → Prop
  | terminal p => p
  | architect t => ∃ n, (t n).value
  | builder t => ∀ᶠ n in hyperfilter ℕ, (t n).value

def child : PairGame → ℕ → PairGame
  | terminal p, _ => terminal p
  | architect t, n => t n
  | builder t, n => t n

def position (g : PairGame) : List ℕ → PairGame
  | [] => g
  | n :: ns => (g.child n).position ns

def allowed : PairGame → Set ℕ
  | builder t => {n | (t n).value ↔ (builder t).value}
  | _ => univ

theorem allowed_mem (g : PairGame) : g.allowed ∈ hyperfilter ℕ := by
  cases g with
  | terminal | architect => exact univ_mem
  | builder t =>
    by_cases h : (builder t).value
    · simp only [allowed, h, iff_true]
      exact h
    · change {n | (t n).value ↔ (builder t).value} ∈ hyperfilter ℕ
      simp only [h, iff_false]
      exact
        (Ultrafilter.compl_mem_iff_notMem.mpr h :
          {n | (t n).value}ᶜ ∈ hyperfilter ℕ)

-- Diagonalize the constraints at all positions in one game. At position p
-- every move from a sufficiently late place in f preserves its value.
theorem thin (g : PairGame) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ∀ p : List ℕ, ∀ᶠ k in atTop, f k ∈ (g.position p).allowed := by
  classical
  let idx := Encodable.encode (α := List ℕ)
  let A (i : ℕ) := (g.position ((Encodable.decode (α := List ℕ) i).getD [])).allowed
  have pick (n b : ℕ) : ∃ x : ℕ, b < x ∧ ∀ i ≤ n, x ∈ A i := by
    have hbig : ∀ᶠ x : ℕ in hyperfilter ℕ, b < x :=
      Nat.hyperfilter_le_atTop (eventually_gt_atTop b)
    have hA : ∀ᶠ x : ℕ in hyperfilter ℕ, ∀ i ∈ Finset.range (n+1), x ∈ A i :=
      (Finset.eventually_all _).mpr fun i _ => allowed_mem _
    obtain ⟨x, hx, hxA⟩ := (hbig.and hA).exists
    exact ⟨x, hx, fun i hi => hxA i (Finset.mem_range.mpr (by omega))⟩
  choose next hn hA using pick
  let f : ℕ → ℕ := Nat.rec (next 0 0) fun k last => next (k+1) last
  refine ⟨f, strictMono_nat_of_lt_succ (fun k => hn (k+1) (f k)), ?_⟩
  intro p
  filter_upwards [eventually_ge_atTop (idx p + 1)] with k hk
  cases k with
  | zero => omega
  | succ j =>
    have h := hA (j+1) (f j) (idx p) (by omega)
    simpa [f, A, idx] using h

-- In the winning case the architect chooses an action. In the losing case
-- every architect action loses. At a builder node either conclusion holds
-- for all sufficiently late choices from the same sequence.
def outcome (f : ℕ → ℕ) (winning : Bool) : PairGame → Prop
  | terminal p => if winning then p else ¬ p
  | architect t =>
      if winning then ∃ n, (t n).outcome f winning
      else ∀ n, (t n).outcome f winning
  | builder t => ∀ᶠ k in atTop, (t (f k)).outcome f winning

theorem realize (g : PairGame) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ (g.value → g.outcome f true) ∧ (¬ g.value → g.outcome f false) := by
  obtain ⟨f, hf, hall⟩ := g.thin
  have aux (t : PairGame)
      (ht : ∀ p : List ℕ, ∀ᶠ k in atTop, f k ∈ (t.position p).allowed) :
      (t.value → t.outcome f true) ∧ (¬ t.value → t.outcome f false) := by
    induction t with
    | terminal p => simp [value, outcome]
    | architect c ih =>
      have hc (n : ℕ) := ih n (fun p => ht (n :: p))
      exact ⟨fun ⟨n, hn⟩ => ⟨n, (hc n).1 hn⟩,
        fun h n => (hc n).2 (fun hn => h ⟨n, hn⟩)⟩
    | builder c ih =>
      have hc (n : ℕ) := ih n (fun p => ht (n :: p))
      have hgood := ht []
      constructor
      · intro h
        exact hgood.mono fun k hk => (hc (f k)).1 (hk.mpr h)
      · intro h
        exact hgood.mono fun k hk => (hc (f k)).2 (fun v => h (hk.mp v))
  exact ⟨f, hf, aux g hall⟩

theorem dichotomy (g : PairGame) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ (g.outcome f true ∨ g.outcome f false) := by
  obtain ⟨f,hf,hwin,hlose⟩ := g.realize
  exact ⟨f,hf,(Classical.em g.value).imp hwin hlose⟩

end PairGame
-- Keep the terminal object so that the same tree of moves can be evaluated
-- with several payoffs (for example, the two possible endpoint orders).
inductive LabelledGame (L : Type) where
  | terminal (label : L)
  | architect (children : ℕ → LabelledGame L)
  | builder (children : ℕ → LabelledGame L)

namespace LabelledGame
variable {L C : Type}

def score (p : L → Prop) : LabelledGame L → PairGame
  | terminal l => .terminal (p l)
  | architect t => .architect fun n => (t n).score p
  | builder t => .builder fun n => (t n).score p

theorem valueFiniteUnion [Finite C] (p : C → L → Prop) (t : LabelledGame L) :
    (t.score (fun l => ∃ c, p c l)).value ↔ ∃ c, (t.score (p c)).value := by
  induction t with
  | terminal => rfl
  | architect t ih =>
    change (∃ n, ((t n).score _).value) ↔ ∃ c n, ((t n).score (p c)).value
    simp_rw [ih]
    exact exists_comm
  | builder t ih =>
    change (∀ᶠ n in hyperfilter ℕ, ((t n).score _).value) ↔
      ∃ c, ∀ᶠ n in hyperfilter ℕ, ((t n).score (p c)).value
    simp_rw [ih]
    exact Ultrafilter.eventually_exists_iff

theorem finiteDichotomy [Finite C] (p : C → L → Prop) (t : LabelledGame L) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ((∃ c, (t.score (p c)).outcome f true) ∨
        (t.score (fun l => ∃ c, p c l)).outcome f false) := by
  by_cases h : (t.score (fun l => ∃ c, p c l)).value
  · obtain ⟨c,hc⟩ := (valueFiniteUnion p t).mp h
    obtain ⟨f,hf,win,_⟩ := (t.score (p c)).realize
    exact ⟨f,hf,Or.inl ⟨c,win hc⟩⟩
  · obtain ⟨f,hf,_,lose⟩ := (t.score (fun l => ∃ c, p c l)).realize
    exact ⟨f,hf,Or.inr (lose h)⟩

def reindex (h : ℕ → ℕ) : LabelledGame L → LabelledGame L
  | terminal l => terminal l
  | architect t => architect fun n => (t n).reindex h
  | builder t => builder fun n => (t (h n)).reindex h

private theorem outcome_reindex (t : LabelledGame L) (p : L → Prop) (h f : ℕ → ℕ)
    (b : Bool) :
    ((t.reindex h).score p).outcome f b ↔ (t.score p).outcome (h ∘ f) b := by
  induction t with
  | terminal => rfl
  | architect t ih => cases b <;> simp only [reindex, score, PairGame.outcome] <;> simp_rw [ih]
  | builder t ih =>
    change (∀ᶠ n in atTop, (((t (h (f n))).reindex h).score p).outcome f b) ↔ _
    simp_rw [ih]
    rfl

theorem finiteDichotomyWithin [Finite C] (p : C → L → Prop) (t : LabelledGame L)
    (H : Set ℕ) (hH : H.Infinite) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ Set.range f ⊆ H ∧
      ((∃ c, (t.score (p c)).outcome f true) ∨
        (t.score (fun l => ∃ c, p c l)).outcome f false) := by
  let h := Nat.nth (· ∈ H)
  have hh : StrictMono h := Nat.nth_strictMono hH
  obtain ⟨f,hf,hom⟩ := finiteDichotomy p (t.reindex h)
  refine ⟨h ∘ f,hh.comp hf,?_,?_⟩
  · rintro _ ⟨k,rfl⟩
    exact Nat.nth_mem_of_infinite hH (f k)
  · rcases hom with ⟨c,hc⟩ | hn
    · exact Or.inl ⟨c,(outcome_reindex t (p c) h f true).mp hc⟩
    · exact Or.inr ((outcome_reindex t _ h f false).mp hn)

end LabelledGame
end Erdos591Proof

/- Vertex partitions of ordinal powers and independent sets in countable products. -/

namespace Erdos591Proof

open Ordinal Set
open scoped Classical

private theorem lexProductType {X Y : Type} [LinearOrder X] [WellFoundedLT X]
    [LinearOrder Y] [WellFoundedLT Y] : typeLT (X ×ₗ Y) = (typeLT Y) * (typeLT X) := by
  let e : ((· < ·) : (X ×ₗ Y) → _ → Prop) ≃r Prod.Lex ((· < ·) : X → _ → Prop)
      ((· < ·) : Y → _ → Prop) := ⟨ofLex, Iff.rfl⟩
  rw [e.ordinalType_congr, type_prod_lex]

private theorem fit {X Y : Type} [LinearOrder X] [WellFoundedLT X]
    [LinearOrder Y] [WellFoundedLT Y] (h : typeLT X ≤ typeLT Y) :
    ∃ f : X → Y, StrictMono f := by
  obtain ⟨f⟩ := type_le_iff'.mp h
  exact ⟨f, fun _ _ => f.map_rel_iff.mpr⟩

private theorem monoBound {X Y : Type} [LinearOrder X] [WellFoundedLT X]
    [LinearOrder Y] [WellFoundedLT Y] {f : X → Y} (hf : StrictMono f) :
    typeLT X ≤ typeLT Y :=
  type_le_iff'.mpr ⟨⟨⟨f, hf.injective⟩, hf.lt_iff_lt⟩⟩

-- Indivisibility for a partition of the vertices of any ordinal power of omega.
theorem vertexPartition (a : Ordinal.{0}) {X : Type}
    [LinearOrder X] [WellFoundedLT X] (color : X → Bool)
    (h : ω ^ a ≤ typeLT X) : ∃ b, ω ^ a ≤ typeLT {x : X // color x = b} := by
  induction a using limitRecOn generalizing X with
  | zero =>
    have hx : Nonempty X := by
      apply (type_ne_zero_iff_nonempty (r := LT.lt)).mp
      intro he
      simp [he] at h
    obtain ⟨x⟩ := hx
    refine ⟨color x, ?_⟩
    rw [opow_zero, Order.one_le_iff_ne_zero, type_ne_zero_iff_nonempty]
    exact ⟨⟨x, rfl⟩⟩
  | add_one a ih =>
    let B := ((ω : Ordinal.{0}) ^ a).ToType
    have hB : typeLT B = ω ^ a := type_toType _
    have hprod : typeLT (ℕ ×ₗ B) = ω ^ (a + 1) := by
      rw [lexProductType, hB, type_nat_lt, opow_add_one]
    obtain ⟨e, he⟩ := fit (hprod.le.trans h)
    let col (n : ℕ) (x : B) := color (e (toLex (n,x)))
    have row (n : ℕ) : ∃ b, ∃ f : B → {x : B // col n x = b}, StrictMono f := by
      obtain ⟨b, hb⟩ := ih (col n) hB.ge
      exact ⟨b, fit (hB.le.trans hb)⟩
    choose b rowEmbed hr using row
    obtain ⟨c, hcinf⟩ := Finite.exists_infinite_fiber b
    have hc : ({n | b n = c} : Set ℕ).Infinite := Set.infinite_coe_iff.mp hcinf
    let idx := Nat.nth (fun n => b n = c)
    have hi : StrictMono idx := Nat.nth_strictMono hc
    have hc' (n : ℕ) : b (idx n) = c := Nat.nth_mem_of_infinite hc n
    let f (p : ℕ ×ₗ B) : {x : X // color x = c} :=
      ⟨e (toLex (idx (ofLex p).1, (rowEmbed (idx (ofLex p).1) (ofLex p).2).val)),
        ((rowEmbed _ _).property).trans (hc' _)⟩
    refine ⟨c, hprod.ge.trans (monoBound (f := f) ?_)⟩
    intro x y hxy
    apply he
    rw [Prod.Lex.lt_iff] at hxy ⊢
    rcases hxy with hlt | ⟨heq, hlt⟩
    · exact Or.inl (hi hlt)
    · apply Or.inr
      refine ⟨congrArg idx heq, ?_⟩
      rw [heq]
      exact hr _ hlt
  | limit a ha ih =>
    let size (b : Bool) := typeLT {x : X // color x = b}
    by_contra! bad
    have hb : ∀ b, size b < ω ^ a := bad
    have hm := max_lt (hb false) (hb true)
    have norm := (isNormal_opow (a := (ω : Ordinal.{0})) one_lt_omega0).le_iff_forall_le (b := max (size false) (size true)) ha
    have small : ∃ d < a, max (size false) (size true) < ω ^ d := by
      by_contra! hn
      exact (not_le_of_gt hm) (norm.mpr hn)
    obtain ⟨d, hd, hs⟩ := small
    have hda : (ω : Ordinal.{0}) ^ d ≤ ω ^ a :=
      ((opow_lt_opow_iff_right one_lt_omega0).mpr hd).le
    obtain ⟨c, hc⟩ := ih d hd color (hda.trans h)
    have hc' : size c ≤ max (size false) (size true) := by cases c <;> simp
    exact (not_le_of_gt hs) (hc.trans hc')

private theorem avoidOne {a : Ordinal.{0}} {X Y : Type} [LinearOrder X] [WellFoundedLT X]
    [LinearOrder Y] [WellFoundedLT Y] (e : X → Y) (he : StrictMono e)
    (hX : typeLT X = ω ^ a) (s : Set Y) (hs : typeLT s < ω ^ a) :
    ∃ f : X → X, StrictMono f ∧ ∀ x, e (f x) ∉ s := by
  classical
  let col (x : X) : Bool := decide (e x ∈ s)
  obtain ⟨b, hb⟩ := vertexPartition a col hX.ge
  obtain ⟨f, hf⟩ := fit (hX.le.trans hb)
  cases b with
  | false =>
    refine ⟨fun x => (f x).val, fun _ _ h => hf h, fun x => ?_⟩
    simpa [col] using (f x).property
  | true =>
    let g (x : X) : s := ⟨e (f x).val, by simpa [col] using (f x).property⟩
    have hg : StrictMono g := fun _ _ h => he (hf h)
    exact ((not_le_of_gt hs) (hX.ge.trans (monoBound hg))).elim

theorem avoidFinite {a : Ordinal.{0}} {X Y I : Type} [LinearOrder X] [WellFoundedLT X]
    [LinearOrder Y] [WellFoundedLT Y] (e : X → Y) (he : StrictMono e)
    (hX : typeLT X = ω ^ a) (s : I → Set Y) (hs : ∀ i, typeLT (s i) < ω ^ a)
    (t : Finset I) : ∃ f : X → X, StrictMono f ∧ ∀ x i, i ∈ t → e (f x) ∉ s i := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨id, strictMono_id, by simp⟩
  | insert i t hi ih =>
    obtain ⟨f, hf, hft⟩ := ih
    obtain ⟨g, hg, hgi⟩ := avoidOne (e ∘ f) (he.comp hf) hX (s i) (hs i)
    refine ⟨f ∘ g, hf.comp hg, fun x j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | h
    · exact hgi x
    · exact hft _ _ h

-- Pick one vertex from each row. Enumerating the rows by natural numbers
-- ensures that each decision has only finitely many earlier vertices to avoid.
theorem independentRows {a : Ordinal.{0}} {X I Y : Type} [LinearOrder X] [WellFoundedLT X]
    [LinearOrder I] [Countable I] [Nonempty I] [LinearOrder Y] [WellFoundedLT Y]
    (row : I ×ₗ X → Y) (hrow : StrictMono row) (hX : typeLT X = ω ^ a)
    (G : SimpleGraph Y) (small : ∀ y, typeLT (G.neighborSet y) < ω ^ a) :
    ∃ f : I → Y, StrictMono f ∧ ∀ i j, ¬ G.Adj (f i) (f j) := by
  classical
  let := Encodable.ofCountable I
  let atRow (n : ℕ) := (Encodable.decode (α := I) n).getD (Classical.choice ‹Nonempty I›)
  have hx : Nonempty X := (type_ne_zero_iff_nonempty (r := LT.lt)).mp (by rw [hX]; exact opow_ne_zero _ omega0_ne_zero)
  let point (n : ℕ) (x : X) := row (toLex (atRow n,x))
  have step (n : ℕ) (past : ∀ k : ℕ, k < n → X) :
      ∃ x : X, ∀ k (hk : k < n), ¬ G.Adj (point k (past k hk)) (point n x) := by
    let N (k : Fin n) := G.neighborSet (point k.val (past k.val k.isLt))
    have hmono : StrictMono (point n) := fun _ _ h =>
      hrow (Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, h⟩))
    obtain ⟨f, _, hf⟩ := avoidFinite (point n) hmono hX N (fun _ => small _) Finset.univ
    exact ⟨f (Classical.choice hx), fun k hk => hf _ ⟨k,hk⟩ (Finset.mem_univ _)⟩
  choose choosePoint good using step
  let pts : ℕ → X := Nat.lt_wfRel.wf.fix choosePoint
  have good' (k n : ℕ) (hk : k < n) : ¬ G.Adj (point k (pts k)) (point n (pts n)) := by
    have eqn : pts n = choosePoint n (fun j _ => pts j) := WellFounded.fix_eq _ _ n
    rw [eqn]
    exact good n (fun j _ => pts j) k hk
  let f (i : I) := row (toLex (i, pts (Encodable.encode i)))
  have hf (i : I) : f i = point (Encodable.encode i) (pts (Encodable.encode i)) := by
    simp [f, point, atRow]
  refine ⟨f, fun _ _ h => hrow (Prod.Lex.lt_iff.mpr (Or.inl h)), ?_⟩
  intro i j hij
  rw [hf i, hf j] at hij
  rcases lt_trichotomy (Encodable.encode i) (Encodable.encode j) with h | h | h
  · exact good' _ _ h hij
  · rw [h] at hij
    exact G.loopless.irrefl _ hij
  · exact good' _ _ h hij.symm

end Erdos591Proof

/- The length-then-lexicographic model of the ordinal for Erdős 591. -/

namespace Erdos591Proof
open Ordinal

abbrev Tuple (X : Type) : ℕ → Type
  | 0 => PUnit
  | n + 1 => X ×ₗ Tuple X n

instance tupleOrder (X : Type) [LinearOrder X] : ∀ n, LinearOrder (Tuple X n)
  | 0 => inferInstanceAs (LinearOrder PUnit)
  | n + 1 =>
    letI := tupleOrder X n
    inferInstanceAs (LinearOrder (X ×ₗ Tuple X n))

private theorem tupleWF' (X : Type) [LinearOrder X] [WellFoundedLT X] : ∀ n, WellFoundedLT (Tuple X n)
  | 0 => inferInstanceAs (WellFoundedLT PUnit)
  | n + 1 =>
    letI := tupleWF' X n
    inferInstanceAs (WellFoundedLT (X ×ₗ Tuple X n))

instance tupleWF (X : Type) [LinearOrder X] [WellFoundedLT X] (n : ℕ) : WellFoundedLT (Tuple X n) :=
  tupleWF' X n

theorem tupleType (X : Type) [LinearOrder X] [WellFoundedLT X] (n : ℕ) :
    typeLT (Tuple X n) = (typeLT X) ^ n := by
  induction n with
  | zero => exact (type_eq_one_of_unique (α := PUnit.{1}) (· < ·)).trans (pow_zero _).symm
  | succ n ih =>
    let e : ((· < ·) : (X ×ₗ Tuple X n) → _ → Prop) ≃r
        Prod.Lex ((· < ·) : X → _ → Prop) ((· < ·) : Tuple X n → _ → Prop) := ⟨ofLex, Iff.rfl⟩
    change typeLT (X ×ₗ Tuple X n) = _
    rw [e.ordinalType_congr, type_prod_lex]
    change (typeLT (Tuple X n)) * (typeLT X) = _
    rw [ih, pow_succ]

structure Word (X : Type) where
  len : ℕ
  letters : Tuple X len

namespace Word
variable {X : Type} [LinearOrder X] [WellFoundedLT X]

-- The extra leading digit 1 separates words of different lengths.
noncomputable def rank (w : Word X) : Ordinal.{0} :=
  (typeLT X) ^ w.len + typein (α := Tuple X w.len) LT.lt w.letters

private theorem belowNext (hb : 2 ≤ typeLT X) (w : Word X) :
    w.rank < (typeLT X) ^ (w.len+1) := by
  have h := typein_lt_type (α := Tuple X w.len) LT.lt w.letters
  change _ < typeLT (Tuple X w.len) at h
  rw [tupleType] at h
  calc w.rank < (typeLT X) ^ w.len + (typeLT X) ^ w.len := add_lt_add_right h _
    _ = (typeLT X) ^ w.len * 2 := by rw [show (2 : Ordinal) = 1 + 1 by norm_num, mul_add_one, mul_one]
    _ ≤ (typeLT X) ^ (w.len+1) := by rw [pow_succ]; exact mul_le_mul_right hb _

private theorem lenRank (hb : 2 ≤ typeLT X) {u v : Word X} (h : u.len < v.len) :
    u.rank < v.rank := by
  refine (belowNext hb u).trans_le ((?_: (typeLT X) ^ (u.len+1) ≤ (typeLT X) ^ v.len).trans le_self_add)
  rw [← opow_natCast, ← opow_natCast]
  exact opow_le_opow_right (zero_lt_two.trans_le hb) (Nat.cast_le.mpr h)

private theorem rankInj (hb : 2 ≤ typeLT X) : Function.Injective (rank (X := X)) := by
  rintro ⟨n,x⟩ ⟨m,y⟩ h
  obtain hlt | rfl | hgt := lt_trichotomy n m
  · exact ((lenRank hb (u := ⟨n,x⟩) (v := ⟨m,y⟩) hlt).ne h).elim
  · unfold rank at h
    have hi : x = y := (typein_inj (α := Tuple X n) LT.lt).mp (add_left_cancel h)
    cases hi
    rfl
  · exact ((lenRank hb (u := ⟨m,y⟩) (v := ⟨n,x⟩) hgt).ne h.symm).elim

noncomputable instance wordOrder [Fact (2 ≤ typeLT X)] : LinearOrder (Word X) :=
  LinearOrder.lift' rank (rankInj Fact.out)

instance wordWF [Fact (2 ≤ typeLT X)] : WellFoundedLT (Word X) :=
  ⟨InvImage.wf rank wellFounded_lt⟩

theorem lt_iff [Fact (2 ≤ typeLT X)] (u v : Word X) :
    u < v ↔ u.len < v.len ∨ ∃ h : u.len = v.len, h ▸ u.letters < v.letters := by
  rcases u with ⟨n,x⟩
  rcases v with ⟨m,y⟩
  obtain h | rfl | h := lt_trichotomy n m
  · exact iff_of_true (lenRank Fact.out h) (Or.inl h)
  · change (typeLT X) ^ n + typein (α := Tuple X n) LT.lt x < (typeLT X) ^ n + typein (α := Tuple X n) LT.lt y ↔ _
    rw [add_lt_add_iff_left, typein_lt_typein]
    constructor
    · exact fun h => Or.inr ⟨rfl,h⟩
    · rintro (h | ⟨_,h⟩)
      · exact (lt_irrefl n h).elim
      · exact h
  · exact iff_of_false (not_lt_of_ge (lenRank Fact.out (u := ⟨m,y⟩) (v := ⟨n,x⟩) h).le)
      (by rintro (hl | ⟨he, _⟩); exact h.not_gt hl; exact h.ne he.symm)

theorem orderType [Fact (2 ≤ typeLT X)] : typeLT (Word X) = (typeLT X) ^ (ω : Ordinal) := by
  have hb : 1 < typeLT X := one_lt_two.trans_le Fact.out
  apply le_antisymm
  · let f (w : Word X) : ((typeLT X) ^ (ω : Ordinal)).ToType :=
      ToType.mk ⟨w.rank, (belowNext Fact.out w).trans (by
        rw [← opow_natCast]
        exact (opow_lt_opow_iff_right hb).mpr (natCast_lt_omega0 _))⟩
    have hf : StrictMono f := fun _ _ h => ToType.mk.strictMono h
    have hle := (RelEmbedding.ofMonotone f hf).ordinal_type_le
    simpa only [type_toType] using hle
  -- Every level embeds back, and their order types converge to the upper bound.
  · rw [(isNormal_opow hb).le_iff_forall_le isSuccLimit_omega0]
    intro d hd
    obtain ⟨n,rfl⟩ := lt_omega0.mp hd
    let f (x : Tuple X n) : Word X := ⟨n,x⟩
    have hf : StrictMono f := fun _ _ h => (lt_iff _ _).mpr (Or.inr ⟨rfl,h⟩)
    rw [opow_natCast, ← tupleType]
    exact (RelEmbedding.ofMonotone f hf).ordinal_type_le

end Word

instance : Fact (2 ≤ typeLT ℕ) := ⟨by rw [type_nat_lt]; exact (natCast_lt_omega0 2).le⟩

instance : Fact (2 ≤ typeLT (Word ℕ)) := ⟨by
  rw [Word.orderType, type_nat_lt]
  exact (natCast_lt_omega0 2).le.trans (by
    calc ω = (ω : Ordinal.{0}) ^ (1 : Ordinal) := (opow_one _).symm
         _ ≤ ω ^ (ω : Ordinal) := opow_le_opow_right omega0_pos one_lt_omega0.le)⟩

theorem heightTwoOrderType : typeLT (Word (Word ℕ)) = (ω : Ordinal.{0}) ^ ω ^ 2 := by
  rw [Word.orderType, Word.orderType, type_nat_lt, ← opow_mul, sq]

end Erdos591Proof
namespace Erdos591Proof
open Ordinal

-- For a countable power B of omega, any triangle-free graph on B times B
-- contains an independent copy of B. The two alternatives use a single
-- neighborhood or a transversal of the rows, respectively.
theorem squareIndependent {X Y : Type} [LinearOrder X] [WellFoundedLT X]
    [Countable X] [Nonempty X] [LinearOrder Y] [WellFoundedLT Y] {a : Ordinal.{0}}
    (hX : typeLT X = ω ^ a) (space : (typeLT X) * (typeLT X) ≤ typeLT Y)
    (G : SimpleGraph Y) (hG : G.CliqueFree 3) :
    ∃ f : X → Y, StrictMono f ∧ ∀ x y, ¬ G.Adj (f x) (f y) := by
  classical
  by_cases small : ∀ y, typeLT (G.neighborSet y) < ω ^ a
  · obtain ⟨e, he⟩ := fit ((lexProductType (X := X) (Y := X)).le.trans space)
    exact independentRows e he hX G small
  · push Not at small
    obtain ⟨v, hv⟩ := small
    obtain ⟨f, hf⟩ := fit (hX.le.trans hv)
    refine ⟨fun x => (f x).val, fun _ _ h => hf h, fun x y hxy => ?_⟩
    exact G.isIndepSet_neighborSet_of_triangleFree hG v (f x).property (f y).property
      (G.ne_of_adj hxy) hxy

private theorem tupleCountable (X : Type) [Countable X] : ∀ n, Countable (Tuple X n)
  | 0 => inferInstanceAs (Countable PUnit)
  | n + 1 =>
    let := tupleCountable X n
    inferInstanceAs (Countable (X × Tuple X n))

private theorem tupleNonempty (X : Type) [Nonempty X] : ∀ n, Nonempty (Tuple X n)
  | 0 => ⟨PUnit.unit⟩
  | n + 1 => ⟨toLex (Classical.choice ‹Nonempty X›, Classical.choice (tupleNonempty X n))⟩

instance {X : Type} [Countable X] : Countable (Word X) := by
  let := tupleCountable X
  exact Function.Injective.countable (f := fun w : Word X => (⟨w.len,w.letters⟩ : Σ n, Tuple X n))
    (by rintro ⟨n,x⟩ ⟨m,y⟩ h; cases h; rfl)

instance {X : Type} : Nonempty (Word X) := ⟨⟨0,PUnit.unit⟩⟩

-- All pairs from the same outer length can simultaneously be made independent.
theorem homogeneousLevels (G : SimpleGraph (Word (Word ℕ))) (hG : G.CliqueFree 3) :
    ∃ f : Word (Word ℕ) → Word (Word ℕ), StrictMono f ∧
      ∀ u v, u.len = v.len → ¬ G.Adj (f u) (f v) := by
  classical
  let X := Word ℕ
  have hX : typeLT X = (ω : Ordinal.{0}) ^ (ω : Ordinal) := by
    rw [Word.orderType, type_nat_lt]
  have layer (n : ℕ) :
      ∃ f : Tuple X n → Tuple X (n+n), StrictMono f ∧ ∀ u v,
        ¬ G.Adj ⟨n+n, f u⟩ ⟨n+n, f v⟩ := by
    let := tupleCountable X n
    let := tupleNonempty X n
    let e (u : Tuple X (n+n)) : Word X := ⟨n+n,u⟩
    have free : (G.comap e).CliqueFree 3 := by
      intro t ht
      obtain ⟨i,j,k,hij,hik,hjk,_⟩ := SimpleGraph.is3Clique_iff.mp ht
      exact hG {e i,e j,e k} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hij,hik,hjk⟩)
    apply squareIndependent (a := (ω : Ordinal.{0}) * (n : Ordinal)) _ _ (G.comap e) free
    · rw [tupleType, hX, opow_mul, opow_natCast]
    · rw [tupleType, tupleType, pow_add]
  choose block hblock ind using layer
  let f (w : Word X) : Word X := ⟨w.len+w.len, block w.len w.letters⟩
  refine ⟨f, ?_, ?_⟩
  · rintro ⟨n,u⟩ ⟨m,v⟩ h
    rcases (Word.lt_iff _ _).mp h with h | ⟨he,h⟩
    · exact (Word.lt_iff _ _).mpr (Or.inl (Nat.add_lt_add h h))
    · change n = m at he
      subst m
      exact (Word.lt_iff _ _).mpr (Or.inr ⟨rfl,hblock n h⟩)
  · rintro ⟨n,u⟩ ⟨m,v⟩ h
    change n = m at h
    subst m
    exact ind _ _ _

end Erdos591Proof

namespace Erdos591Proof
open Ordinal

-- A common proper bound on all the neighborhoods gives an independent
-- copy of the whole ordinal, even without the triangle-free assumption.
theorem boundedNeighborhoods (G : SimpleGraph (Word (Word ℕ))) {b : Ordinal.{0}}
    (hb : b < typeLT (Word (Word ℕ))) (bound : ∀ x, typeLT (G.neighborSet x) ≤ b) :
    ∃ f : Word (Word ℕ) → Word (Word ℕ), StrictMono f ∧ ∀ i j, ¬ G.Adj (f i) (f j) := by
  rw [heightTwoOrderType, sq, opow_mul] at hb
  have hg : 1 < (ω : Ordinal.{0}) ^ (ω : Ordinal) :=
    one_lt_opow.mpr ⟨one_lt_omega0, omega0_ne_zero⟩
  have ex : ∃ d < (ω : Ordinal.{0}), b < (ω ^ (ω : Ordinal)) ^ d := by
    by_contra! all
    exact hb.not_ge (((isNormal_opow hg).le_iff_forall_le isSuccLimit_omega0).mpr all)
  obtain ⟨d, hd, hb'⟩ := ex
  let a : Ordinal.{0} := ω * d
  have ha : a < (ω : Ordinal.{0}) ^ (2 : ℕ) := by
    rw [sq]
    exact mul_lt_mul_of_pos_left hd omega0_pos
  have hadd : a + (ω : Ordinal.{0}) ^ (2 : ℕ) = ω ^ (2 : ℕ) := by
    rw [← opow_natCast] at ha ⊢
    exact add_omega0_opow ha
  let B := ((ω : Ordinal.{0}) ^ a).ToType
  have hB : typeLT B = ω ^ a := type_toType _
  have room : typeLT (Word (Word ℕ) ×ₗ B) = typeLT (Word (Word ℕ)) := by
    rw [lexProductType, hB, heightTwoOrderType, ← opow_add, hadd]
  obtain ⟨e,he⟩ := fit room.le
  apply independentRows e he hB G
  intro x
  change typeLT (G.neighborSet x) < ω ^ (ω * d)
  rw [opow_mul]
  exact (bound x).trans_lt hb'

end Erdos591Proof

namespace Erdos591Proof
open Ordinal
universe u

private theorem liftNatPower (b : Ordinal.{0}) (n : ℕ) :
    lift.{u} (b ^ n) = (lift.{u} b) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,pow_succ,lift_mul,ih]

private theorem leOmegaPower {b x : Ordinal.{u}} (hb : 1 < b) :
    b ^ (ω : Ordinal) ≤ x ↔ ∀ n : ℕ, b ^ n ≤ x := by
  rw [(isNormal_opow hb).le_iff_forall_le isSuccLimit_omega0]
  constructor
  · intro h n
    simpa only [opow_natCast] using h n (natCast_lt_omega0 n)
  · intro h d hd
    obtain ⟨n,rfl⟩ := lt_omega0.mp hd
    simpa only [opow_natCast] using h n

private theorem liftOmegaPower {b : Ordinal.{0}} (hb : 1 < b) :
    lift.{u} (b ^ (ω : Ordinal)) = (lift.{u} b) ^ (ω : Ordinal) := by
  have hb' : 1 < lift.{u} b := by simpa only [lift_one] using lift_lt.{u,0}.mpr hb
  apply le_antisymm
  · by_contra! h
    obtain ⟨c,hc,he⟩ := lt_lift_iff.mp h
    have hnc : ∃ n : ℕ, c < b ^ n := by
      by_contra! hn
      exact hc.not_ge ((leOmegaPower hb).mpr hn)
    obtain ⟨n,hn⟩ := hnc
    have h' := lift_lt.{u,0}.mpr hn
    rw [he,liftNatPower] at h'
    exact h'.not_ge ((leOmegaPower hb').mp le_rfl n)
  · apply (leOmegaPower hb').mpr
    intro n
    rw [← liftNatPower, lift_le]
    exact (leOmegaPower hb).mp le_rfl n

theorem liftedHeightTwoOrderType :
    typeLT (ULift.{u,0} (Word (Word ℕ))) = (ω : Ordinal.{u}) ^ ω ^ 2 := by
  rw [type_lt_ulift,heightTwoOrderType,sq,opow_mul,
    liftOmegaPower (one_lt_opow.mpr ⟨one_lt_omega0,omega0_ne_zero⟩),
    liftOmegaPower one_lt_omega0,lift_omega0,← opow_mul,sq]

end Erdos591Proof

namespace Erdos591Proof
open Ordinal

theorem unionLarge {X : Type} [LinearOrder X] [WellFoundedLT X]
    (a : Ordinal.{0}) (A B : Set X) (h : ω ^ a ≤ typeLT (A ∪ B : Set X)) :
    ω ^ a ≤ typeLT A ∨ ω ^ a ≤ typeLT B := by
  classical
  let U := A ∪ B
  let color (x : U) : Bool := decide (x.val ∈ A)
  obtain ⟨b,hb⟩ := vertexPartition a color h
  cases b with
  | true =>
    let f (x : {x : U // color x = true}) : A := ⟨x.val.val, by simpa [color] using x.property⟩
    exact Or.inl (hb.trans (monoBound (f := f) (fun _ _ hx => hx)))
  | false =>
    let f (x : {x : U // color x = false}) : B := ⟨x.val.val, by
      have hn : x.val.val ∉ A := by simpa [color] using x.property
      exact x.val.property.resolve_left hn⟩
    exact Or.inr (hb.trans (monoBound (f := f) (fun _ _ hx => hx)))

-- Vertices whose neighborhoods belong to the same ultrafilter are independent:
-- any two of their neighborhoods intersect, and an edge would close a triangle.
open Filter
theorem commonFilterIndependent {X : Type*} (G : SimpleGraph X) (hG : G.CliqueFree 3)
    (U : Ultrafilter X) : G.IsIndepSet {x | G.neighborSet x ∈ U} := by
  intro x hx y hy hne hxy
  have hx' : ∀ᶠ z in U, G.Adj x z := hx
  have hy' : ∀ᶠ z in U, G.Adj y z := hy
  obtain ⟨z,hxz,hyz⟩ := (hx'.and hy').exists
  exact G.isIndepSet_neighborSet_of_triangleFree hG z hxz.symm hyz.symm hne hxy

end Erdos591Proof

namespace Erdos591Proof
open Ordinal Cardinal
universe v

-- Transport the concrete level construction to the universe of the upstream
-- graph, and distinguish the blue triangle from the equal-length red pairs.
theorem homogeneousOrdinalLevels
    (red blue : SimpleGraph ((ω : Ordinal.{v}) ^ ω ^ 2).ToType) (comp : IsCompl red blue) :
    (∃ s, blue.IsClique s ∧ #s = 3) ∨
      ∃ f : Word (Word ℕ) → ((ω : Ordinal.{v}) ^ ω ^ 2).ToType, StrictMono f ∧
        ∀ u v, u ≠ v → u.len = v.len → red.Adj (f u) (f v) := by
  classical
  obtain ⟨iso⟩ := type_eq.mp (liftedHeightTwoOrderType.{v}.trans (type_toType _).symm)
  let e (w : Word (Word ℕ)) := iso (ULift.up w)
  have he : StrictMono e := fun _ _ h => iso.map_rel_iff.mpr h
  by_cases free : blue.CliqueFree 3
  · right
    have free' : (blue.comap e).CliqueFree 3 := by
      intro s hs
      obtain ⟨x,y,z,hxy,hxz,hyz,_⟩ := SimpleGraph.is3Clique_iff.mp hs
      exact free {e x,e y,e z} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy,hxz,hyz⟩)
    obtain ⟨g,hg,hlev⟩ := homogeneousLevels _ free'
    refine ⟨e ∘ g,he.comp hg, fun u v huv hl => ?_⟩
    have hc : (red ⊔ blue).Adj (e (g u)) (e (g v)) := by
      rw [comp.codisjoint.eq_top]
      exact (he.comp hg).injective.ne huv
    exact hc.resolve_right (hlev u v hl)
  · left
    change ¬ ∀ s, ¬ blue.IsNClique 3 s at free
    push Not at free
    obtain ⟨s,hs⟩ := free
    refine ⟨(s : Set _), hs.1, ?_⟩
    simp [hs.2]

end Erdos591Proof

-- Nash-Williams on thin families, from the finite-cardinal Erdős 590 proof.
namespace Erdos591Proof.ThinFamilies
open Cardinal Ordinal Filter Set
open scoped Classical

def StrictSorted (l : List ℕ) : Prop := l.Pairwise (· < ·)

def ListAllIn (s : List ℕ) (B : Set ℕ) : Prop := ∀ x ∈ s, x ∈ B

private lemma mem_le_list_sum : ∀ {s : List ℕ} {a : ℕ}, a ∈ s → a ≤ s.sum
  | [], _, h => by simp at h
  | x :: xs, a, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · simp
    · have := mem_le_list_sum h'; simp; omega

private lemma infinite_gt_nat {B : Set ℕ} (hB : B.Infinite) (x : ℕ) :
    { b ∈ B | x < b }.Infinite :=
  (hB.sdiff (Set.finite_le_nat x)).mono (fun _ h => ⟨h.1, not_le.mp h.2⟩)

private lemma infinite_gt_list {B : Set ℕ} (hB : B.Infinite) (s : List ℕ) :
    { b ∈ B | ∀ a ∈ s, a < b }.Infinite :=
  (infinite_gt_nat hB s.sum).mono fun _ h =>
    ⟨h.1, fun _ ha => lt_of_le_of_lt (mem_le_list_sum ha) h.2⟩

private def Accepts (F : Set (List ℕ)) (B : Set ℕ) (s : List ℕ) : Prop :=
  ∃ t ∈ F, t <+: s ∨ ∃ u, t = s ++ u ∧ ListAllIn u B

private def StronglyAccepts (F : Set (List ℕ)) (B : Set ℕ) (s : List ℕ) : Prop :=
  ∀ C, C ⊆ B → C.Infinite → Accepts F C s

private def Rejects (F : Set (List ℕ)) (B : Set ℕ) (s : List ℕ) : Prop :=
  ¬ Accepts F B s

private def Decides (F : Set (List ℕ)) (B : Set ℕ) (s : List ℕ) : Prop :=
  StronglyAccepts F B s ∨ Rejects F B s

private lemma accepts_mono {F : Set (List ℕ)} {B C : Set ℕ} {s : List ℕ}
    (hCB : C ⊆ B) (h : Accepts F C s) : Accepts F B s := by
  rcases h with ⟨t, htF, hpre | ⟨u, rfl, hu⟩⟩
  · exact ⟨t, htF, Or.inl hpre⟩
  · exact ⟨s ++ u, htF, Or.inr ⟨u, rfl, fun x hx => hCB (hu x hx)⟩⟩

private lemma decides_mono {F : Set (List ℕ)} {B C : Set ℕ} {s : List ℕ}
    (hCB : C ⊆ B) (h : Decides F B s) : Decides F C s := by
  rcases h with hsa | hrej
  · exact Or.inl fun D hDC hDinf => hsa D (hDC.trans hCB) hDinf
  · exact Or.inr fun hacc => hrej (accepts_mono hCB hacc)

private lemma exists_decides {F : Set (List ℕ)} {B : Set ℕ} (hB : B.Infinite) (s : List ℕ) :
    ∃ C, C ⊆ B ∧ C.Infinite ∧ Decides F C s := by
  by_cases hsa : StronglyAccepts F B s
  · exact ⟨B, Subset.rfl, hB, Or.inl hsa⟩
  · unfold StronglyAccepts at hsa
    push Not at hsa
    obtain ⟨C, hCB, hCinf, hrej⟩ := hsa
    exact ⟨C, hCB, hCinf, Or.inr hrej⟩

private lemma exists_decides_list {F : Set (List ℕ)} :
    ∀ (L : List (List ℕ)) {B : Set ℕ}, B.Infinite →
      ∃ C, C ⊆ B ∧ C.Infinite ∧ ∀ s ∈ L, Decides F C s
  | [], B, hB => ⟨B, Subset.rfl, hB, fun _ h => by simp at h⟩
  | s :: L, B, hB => by
    obtain ⟨C₁, hC₁B, hC₁inf, hdec⟩ := exists_decides (F := F) hB s
    obtain ⟨C₂, hC₂C₁, hC₂inf, hL⟩ := exists_decides_list L hC₁inf
    refine ⟨C₂, hC₂C₁.trans hC₁B, hC₂inf, fun t ht => ?_⟩
    rcases List.mem_cons.mp ht with rfl | htL
    · exact decides_mono hC₂C₁ hdec
    · exact hL t htL

private lemma accepts_iff_tail {F : Set (List ℕ)} (hF : ∀ t ∈ F, StrictSorted t)
    {B : Set ℕ} {s : List ℕ} :
    Accepts F B s ↔ Accepts F { b ∈ B | ∀ a ∈ s, a < b } s := by
  constructor
  · rintro ⟨t, htF, hpre | ⟨u, rfl, hu⟩⟩
    · exact ⟨t, htF, Or.inl hpre⟩
    · refine ⟨s ++ u, htF, Or.inr ⟨u, rfl, fun x hx => ⟨hu x hx, fun a ha => ?_⟩⟩⟩
      exact (List.pairwise_append.mp (hF (s ++ u) htF)).2.2 a ha x hx
  · exact accepts_mono (fun _ h => h.1)

private lemma decides_of_tail {F : Set (List ℕ)} (hF : ∀ t ∈ F, StrictSorted t)
    {B C : Set ℕ} {s : List ℕ}
    (hsub : { b ∈ B | ∀ a ∈ s, a < b } ⊆ C) (hdec : Decides F C s) :
    Decides F B s := by
  rcases hdec with hsa | hrej
  · left
    intro D hDB hDinf
    have hDtail : { b ∈ D | ∀ a ∈ s, a < b }.Infinite := infinite_gt_list hDinf s
    have hacc := hsa { b ∈ D | ∀ a ∈ s, a < b }
      (fun x hx => hsub ⟨hDB hx.1, hx.2⟩) hDtail
    exact (accepts_iff_tail hF).mpr hacc
  · right
    intro hacc
    exact hrej (accepts_mono hsub ((accepts_iff_tail hF).mp hacc))

private lemma sublist_of_strictSorted_mem {s t : List ℕ}
    (hs : StrictSorted s) (ht : StrictSorted t) (hsub : ∀ x ∈ s, x ∈ t) :
    List.Sublist s t := by
  induction t generalizing s with
  | nil =>
    cases s with
    | nil => exact List.Sublist.slnil
    | cons a _ => exact absurd (hsub a (by simp)) (by simp)
  | cons b t' ih =>
    have hb_lt : ∀ y ∈ t', b < y := (List.pairwise_cons.mp ht).1
    have ht' : StrictSorted t' := (List.pairwise_cons.mp ht).2
    cases s with
    | nil => exact List.nil_sublist _
    | cons a s' =>
      have ha_lt : ∀ y ∈ s', a < y := (List.pairwise_cons.mp hs).1
      have hs' : StrictSorted s' := (List.pairwise_cons.mp hs).2
      have ha_mem : a = b ∨ a ∈ t' := by simpa using hsub a (by simp)
      rcases ha_mem with rfl | ha_t'
      · refine List.Sublist.cons_cons a (ih hs' ht' ?_)
        intro y hy
        have hy_mem : y = a ∨ y ∈ t' := by simpa using hsub y (by simp [hy])
        rcases hy_mem with rfl | hy'
        · exact absurd (ha_lt y hy) (lt_irrefl _)
        · exact hy'
      · refine List.Sublist.cons b (ih hs ht' ?_)
        intro y hy
        have hy_mem : y = b ∨ y ∈ t' := by simpa using hsub y hy
        rcases hy_mem with hyb | hy'
        · have hba : b < a := hb_lt a ha_t'
          rw [hyb] at hy
          rcases List.mem_cons.mp hy with h | hys'
          · exact absurd (h ▸ hba) (lt_irrefl _)
          · exact absurd (ha_lt b hys') (by omega)
        · exact hy'

private lemma nash_williams_diag {F : Set (List ℕ)} (hF : ∀ t ∈ F, StrictSorted t)
    {A : Set ℕ} (hA : A.Infinite) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧ ∀ s, StrictSorted s → ListAllIn s B → Decides F B s := by
  obtain ⟨A₀, hA₀A, hA₀inf, hA₀dec⟩ := exists_decides (F := F) hA []
  let step : { p : List ℕ × Set ℕ //
      StrictSorted p.1 ∧ ListAllIn p.1 A ∧ p.2 ⊆ A ∧ p.2.Infinite ∧
      (∀ a ∈ p.1, ∀ b ∈ p.2, a < b) ∧ (∀ s ∈ p.1.sublists, Decides F p.2 s) } →
      { p : List ℕ × Set ℕ //
      StrictSorted p.1 ∧ ListAllIn p.1 A ∧ p.2 ⊆ A ∧ p.2.Infinite ∧
      (∀ a ∈ p.1, ∀ b ∈ p.2, a < b) ∧ (∀ s ∈ p.1.sublists, Decides F p.2 s) } := fun cur =>
    let x := Nat.nth (· ∈ cur.1.2) 0
    have hx_mem : x ∈ cur.1.2 := Nat.nth_mem_of_infinite cur.2.2.2.2.1 0
    let s' := cur.1.1 ++ [x]
    have htail_inf : { b ∈ cur.1.2 | x < b }.Infinite :=
      infinite_gt_nat cur.2.2.2.2.1 x
    let ex := exists_decides_list (F := F) s'.sublists htail_inf
    let C := Classical.choose ex
    let hC := Classical.choose_spec ex
    ⟨(s', C),
      by
        refine List.pairwise_append.mpr ⟨cur.2.1, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        exact cur.2.2.2.2.2.1 a ha x hx_mem,
      fun y hy => by
        rcases List.mem_append.mp hy with h1 | h2
        · exact cur.2.2.1 y h1
        · simp only [List.mem_singleton] at h2; subst h2; exact cur.2.2.2.1 hx_mem,
      fun y hy => cur.2.2.2.1 (hC.1 hy).1,
      hC.2.1,
      fun a ha b hb => by
        rcases List.mem_append.mp ha with h1 | h2
        · exact lt_trans (cur.2.2.2.2.2.1 a h1 x hx_mem) (hC.1 hb).2
        · simp only [List.mem_singleton] at h2; subst h2; exact (hC.1 hb).2,
      hC.2.2⟩
  let seq : ℕ → { p : List ℕ × Set ℕ //
      StrictSorted p.1 ∧ ListAllIn p.1 A ∧ p.2 ⊆ A ∧ p.2.Infinite ∧
      (∀ a ∈ p.1, ∀ b ∈ p.2, a < b) ∧ (∀ s ∈ p.1.sublists, Decides F p.2 s) } :=
    Nat.rec ⟨([], A₀), List.Pairwise.nil, fun _ h => by simp at h, hA₀A, hA₀inf,
      fun _ h => by simp at h, fun s hs => by
        have : s = [] := by simpa using hs
        subst this; exact hA₀dec⟩ (fun _ cur => step cur)
  have hlen : ∀ n, (seq n).1.1.length = n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      show ((seq n).1.1 ++ [_]).length = n + 1
      simp [ih]
  have hpref : ∀ n, (seq n).1.1 <+: (seq (n + 1)).1.1 := fun n => ⟨[_], rfl⟩
  have hpref_le : ∀ {m n}, m ≤ n → (seq m).1.1 <+: (seq n).1.1 := by
    intro m n h
    induction n, h using Nat.le_induction with
    | base => exact List.prefix_refl _
    | succ n _ ih => exact ih.trans (hpref n)
  have hA_anti : ∀ n, (seq (n + 1)).1.2 ⊆ (seq n).1.2 := by
    intro n y hy
    let cur := seq n
    let x := Nat.nth (· ∈ cur.1.2) 0
    have htail_inf : { b ∈ cur.1.2 | x < b }.Infinite :=
      infinite_gt_nat cur.2.2.2.2.1 x
    have hC := Classical.choose_spec
      (exists_decides_list (F := F) (cur.1.1 ++ [x]).sublists htail_inf)
    exact (hC.1 hy).1
  have hA_anti_le : ∀ {m n}, m ≤ n → (seq n).1.2 ⊆ (seq m).1.2 := by
    intro m n h
    induction n, h using Nat.le_induction with
    | base => exact Subset.rfl
    | succ n _ ih => exact (hA_anti n).trans ih
  let xseq : ℕ → ℕ := fun n => Nat.nth (· ∈ (seq n).1.2) 0
  have hx_in_next : ∀ n, (seq (n + 1)).1.1 = (seq n).1.1 ++ [xseq n] := fun _ => rfl
  have hx_mem_A : ∀ n, xseq n ∈ (seq n).1.2 := fun n =>
    Nat.nth_mem_of_infinite (seq n).2.2.2.2.1 0
  have hx_mono : StrictMono xseq := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    have h1 : xseq n ∈ (seq (n + 1)).1.1 := by rw [hx_in_next]; simp
    exact (seq (n + 1)).2.2.2.2.2.1 (xseq n) h1 (xseq (n + 1)) (hx_mem_A (n + 1))
  have hseq_mem_iff : ∀ n y, y ∈ (seq n).1.1 ↔ ∃ k < n, xseq k = y := by
    intro n
    induction n with
    | zero => intro y; simp [seq]
    | succ n ih =>
      intro y
      rw [hx_in_next, List.mem_append, List.mem_singleton, ih]
      constructor
      · rintro (⟨k, hk, rfl⟩ | rfl)
        · exact ⟨k, by omega, rfl⟩
        · exact ⟨n, by omega, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        by_cases hkn : k < n
        · exact Or.inl ⟨k, hkn, rfl⟩
        · have : k = n := by omega
          subst this; exact Or.inr rfl
  let B : Set ℕ := Set.range xseq
  have hB_sub_A : B ⊆ A := by
    rintro _ ⟨n, rfl⟩
    exact (seq n).2.2.2.1 (hx_mem_A n)
  have hB_inf : B.Infinite := Set.infinite_range_of_injective hx_mono.injective
  refine ⟨B, hB_sub_A, hB_inf, fun s hs_sort hs_B => ?_⟩
  by_cases hs_nil : s = []
  · subst hs_nil
    refine decides_of_tail hF (C := (seq 0).1.2) ?_ ((seq 0).2.2.2.2.2.2 [] (by simp))
    rintro _ ⟨⟨k, rfl⟩, _⟩
    exact hA_anti_le (Nat.zero_le k) (hx_mem_A k)
  · have hlast_mem : s.getLast hs_nil ∈ s := List.getLast_mem hs_nil
    obtain ⟨m, hm⟩ := hs_B _ hlast_mem
    have hs_in_seq : ∀ y ∈ s, y ∈ (seq (m + 1)).1.1 := by
      intro y hy
      obtain ⟨k, rfl⟩ := hs_B y hy
      have hkle : k ≤ m := by
        have hle_last : xseq k ≤ s.getLast hs_nil := by
          have : ∀ {L : List ℕ} (hne : L ≠ []), StrictSorted L → ∀ a ∈ L, a ≤ L.getLast hne := by
            intro L
            induction L with
            | nil => intro hne; exact absurd rfl hne
            | cons a t ihL =>
              intro _ hst x hx
              cases t with
              | nil =>
                simp only [List.mem_singleton] at hx
                simp [hx]
              | cons b t' =>
                have hab : a < b := (List.pairwise_cons.mp hst).1 b (by simp)
                have hst' : StrictSorted (b :: t') := (List.pairwise_cons.mp hst).2
                have hgl : (a :: b :: t').getLast (List.cons_ne_nil _ _) =
                    (b :: t').getLast (List.cons_ne_nil _ _) := rfl
                rw [hgl]
                rcases List.mem_cons.mp hx with rfl | hxt
                · exact le_trans (le_of_lt hab) (ihL _ hst' b (by simp))
                · exact ihL _ hst' x hxt
          exact this hs_nil hs_sort (xseq k) hy
        rw [← hm] at hle_last
        exact hx_mono.le_iff_le.mp hle_last
      exact (hseq_mem_iff (m + 1) (xseq k)).mpr ⟨k, by omega, rfl⟩
    have hsublist : s ∈ (seq (m + 1)).1.1.sublists :=
      List.mem_sublists.mpr (sublist_of_strictSorted_mem hs_sort (seq (m + 1)).2.1 hs_in_seq)
    refine decides_of_tail hF (C := (seq (m + 1)).1.2) ?_
      ((seq (m + 1)).2.2.2.2.2.2 s hsublist)
    rintro _ ⟨⟨k, rfl⟩, hgt⟩
    have hmk : m + 1 ≤ k := by
      have hlt : xseq m < xseq k := hm ▸ hgt _ hlast_mem
      have := hx_mono.lt_iff_lt.mp hlt
      omega
    exact hA_anti_le hmk (hx_mem_A k)

private lemma nash_williams_finite_bad {F : Set (List ℕ)} {B : Set ℕ} {s : List ℕ}
    (hsa : StronglyAccepts F B s) :
    { n ∈ B | (∀ a ∈ s, a < n) ∧ Rejects F B (s ++ [n]) }.Finite := by
  by_contra hinf
  let C := { n ∈ B | (∀ a ∈ s, a < n) ∧ Rejects F B (s ++ [n]) }
  have hCinf : C.Infinite := hinf
  have hCB : C ⊆ B := fun _ h => h.1
  obtain ⟨t, htF, hpre | ⟨u, rfl, hu⟩⟩ := hsa C hCB hCinf
  · obtain ⟨n, hn⟩ := hCinf.nonempty
    exact hn.2.2 ⟨t, htF, Or.inl (hpre.trans ⟨[n], rfl⟩)⟩
  · cases u with
    | nil =>
      obtain ⟨n, hn⟩ := hCinf.nonempty
      simp only [List.append_nil] at htF
      exact hn.2.2 ⟨s, htF, Or.inl ⟨[n], rfl⟩⟩
    | cons n u' =>
      have hnC : n ∈ C := hu n (by simp)
      refine hnC.2.2 ⟨s ++ n :: u', htF, Or.inr ⟨u', by simp, fun x hx => hCB (hu x (by simp [hx]))⟩⟩

theorem nash_williams (F : Set (List ℕ)) (hF_sort : ∀ s ∈ F, StrictSorted s)
    (hF_thin : ∀ s ∈ F, ∀ t ∈ F, s <+: t → s = t)
    (c : List ℕ → Bool) (A : Set ℕ) (hA : A.Infinite) :
    ∃ (b : Bool) (B : Set ℕ), B ⊆ A ∧ B.Infinite ∧
      ∀ s ∈ F, ListAllIn s B → c s = b := by
  let F₀ : Set (List ℕ) := { s ∈ F | c s = false }
  have hF₀_sort : ∀ s ∈ F₀, StrictSorted s := fun s hs => hF_sort s hs.1
  obtain ⟨B, hBA, hBinf, hBdec⟩ := nash_williams_diag hF₀_sort hA
  rcases hBdec [] List.Pairwise.nil (fun _ h => by simp at h) with hsa0 | hrej0
  · -- Strongly accepts `[]`: build infinite `H ⊆ B` where every strictly sorted `s ⊆ H` is strongly accepted
    let step : { L : List ℕ // StrictSorted L ∧ ListAllIn L B ∧
        ∀ s ∈ L.sublists, StronglyAccepts F₀ B s } →
        { L : List ℕ // StrictSorted L ∧ ListAllIn L B ∧
        ∀ s ∈ L.sublists, StronglyAccepts F₀ B s } := fun cur =>
      let bad : Set ℕ :=
        { n : ℕ | ¬ ∀ a ∈ cur.1, a < n } ∪
        ⋃ s ∈ cur.1.sublists, { n ∈ B | (∀ a ∈ s, a < n) ∧ Rejects F₀ B (s ++ [n]) }
      have hbad_fin : bad.Finite := by
        refine Set.Finite.union ?_ ?_
        · refine (Set.finite_le_nat cur.1.sum).subset fun n hn => ?_
          push Not at hn
          obtain ⟨a, ha, han⟩ := hn
          have ham := mem_le_list_sum ha
          show n ≤ cur.1.sum
          omega
        · refine (cur.1.sublists.finite_toSet).biUnion fun s hs =>
            nash_williams_finite_bad (cur.2.2.2 s hs)
      have hgood : (B \ bad).Nonempty := (hBinf.sdiff hbad_fin).nonempty
      let x := Classical.choose hgood
      have hx : x ∈ B ∧ x ∉ bad := Classical.choose_spec hgood
      have hx_gt : ∀ a ∈ cur.1, a < x := by
        by_contra h
        exact hx.2 (Or.inl h)
      ⟨cur.1 ++ [x],
        List.pairwise_append.mpr ⟨cur.2.1, List.pairwise_singleton _ _, fun a ha b hb => by
          simp only [List.mem_singleton] at hb; subst hb; exact hx_gt a ha⟩,
        fun y hy => by
          rcases List.mem_append.mp hy with h1 | h2
          · exact cur.2.2.1 y h1
          · simp only [List.mem_singleton] at h2; subst h2; exact hx.1,
        fun s hs => by
          have hsub : List.Sublist s (cur.1 ++ [x]) := List.mem_sublists.mp hs
          by_cases hx_in : x ∈ s
          · -- `x` is the last element of `s`, so `s = s' ++ [x]` with `s' <+ cur.1`
            have hs_sort : StrictSorted s :=
              (List.pairwise_append.mpr ⟨cur.2.1, List.pairwise_singleton _ _, fun a ha b hb => by
                simp only [List.mem_singleton] at hb; subst hb; exact hx_gt a ha⟩).sublist hsub
            have hs_ne : s ≠ [] := List.ne_nil_of_mem hx_in
            have hlast : s.getLast hs_ne = x := by
              have hle1 : x ≤ s.getLast hs_ne := by
                have hgl_mem : s.getLast hs_ne ∈ s := List.getLast_mem hs_ne
                have : ∀ {L : List ℕ} (hne : L ≠ []), StrictSorted L → ∀ a ∈ L, a ≤ L.getLast hne := by
                  intro L
                  induction L with
                  | nil => intro hne; exact absurd rfl hne
                  | cons a t ihL =>
                    intro _ hst u hu
                    cases t with
                    | nil => simp only [List.mem_singleton] at hu; simp [hu]
                    | cons b t' =>
                      have hab : a < b := (List.pairwise_cons.mp hst).1 b (by simp)
                      have hst' : StrictSorted (b :: t') := (List.pairwise_cons.mp hst).2
                      have hgl : (a :: b :: t').getLast (List.cons_ne_nil _ _) =
                          (b :: t').getLast (List.cons_ne_nil _ _) := rfl
                      rw [hgl]
                      rcases List.mem_cons.mp hu with rfl | hut
                      · exact le_trans (le_of_lt hab) (ihL _ hst' b (by simp))
                      · exact ihL _ hst' u hut
                exact this hs_ne hs_sort x hx_in
              have hle2 : s.getLast hs_ne ≤ x := by
                have hmem := hsub.subset (List.getLast_mem hs_ne)
                rcases List.mem_append.mp hmem with h1 | h2
                · exact le_of_lt (hx_gt _ h1)
                · simp only [List.mem_singleton] at h2; omega
              omega
            let s' := s.dropLast
            have hs_eq : s = s' ++ [x] := by
              rw [← hlast]
              exact (List.dropLast_append_getLast hs_ne).symm
            have hs'_lt : ∀ a ∈ s', a < x := by
              intro a ha
              have hp := List.pairwise_append.mp (hs_eq ▸ hs_sort)
              exact hp.2.2 a ha x (by simp)
            have hs'_sub : List.Sublist s' cur.1 := by
              refine sublist_of_strictSorted_mem (List.pairwise_append.mp (hs_eq ▸ hs_sort)).1 cur.2.1 ?_
              intro a ha
              have hmem := hsub.subset (hs_eq ▸ List.mem_append_left [x] ha)
              rcases List.mem_append.mp hmem with h1 | h2
              · exact h1
              · simp only [List.mem_singleton] at h2
                exact absurd (h2 ▸ hs'_lt a ha) (lt_irrefl _)
            have hs'_mem_sub : s' ∈ cur.1.sublists := List.mem_sublists.mpr hs'_sub
            have hdec_s := hBdec s hs_sort (fun y hy => by
              rcases List.mem_append.mp (hsub.subset hy) with h1 | h2
              · exact cur.2.2.1 y h1
              · simp only [List.mem_singleton] at h2; subst h2; exact hx.1)
            rcases hdec_s with hsa_s | hrej_s
            · exact hsa_s
            · exfalso
              apply hx.2
              right
              exact Set.mem_iUnion₂.mpr ⟨s', hs'_mem_sub, hx.1, hs'_lt, hs_eq ▸ hrej_s⟩
          · have hs_sub : List.Sublist s cur.1 := by
              have hs_sort : StrictSorted s :=
                (List.pairwise_append.mpr ⟨cur.2.1, List.pairwise_singleton _ _, fun a ha b hb => by
                  simp only [List.mem_singleton] at hb; subst hb; exact hx_gt a ha⟩).sublist hsub
              refine sublist_of_strictSorted_mem hs_sort cur.2.1 ?_
              intro a ha
              rcases List.mem_append.mp (hsub.subset ha) with h1 | h2
              · exact h1
              · simp only [List.mem_singleton] at h2
                exact absurd (h2 ▸ ha) hx_in
            exact cur.2.2.2 s (List.mem_sublists.mpr hs_sub)⟩
    let chain : ℕ → { L : List ℕ // StrictSorted L ∧ ListAllIn L B ∧
        ∀ s ∈ L.sublists, StronglyAccepts F₀ B s } :=
      Nat.rec ⟨[], List.Pairwise.nil, fun _ h => by simp at h, fun s hs => by
        have : s = [] := by simpa using hs
        subst this; exact hsa0⟩ (fun _ cur => step cur)
    have hlen : ∀ n, (chain n).1.length = n := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        show ((chain n).1 ++ [_]).length = n + 1
        simp [ih]
    let H : Set ℕ := ⋃ n, { x | x ∈ (chain n).1 }
    have hH_sub_B : H ⊆ B := by
      intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨n, hxn⟩
      exact (chain n).2.2.1 x hxn
    have hH_inf : H.Infinite := by
      intro hfin
      have hcard : ∀ n, n ≤ hfin.toFinset.card := by
        intro n
        have hsub : (chain n).1.toFinset ⊆ hfin.toFinset := by
          intro x hx
          rw [Set.Finite.mem_toFinset]
          exact Set.mem_iUnion.mpr ⟨n, List.mem_toFinset.mp hx⟩
        have hnodup : (chain n).1.Nodup := (chain n).2.1.imp ne_of_lt
        calc n = (chain n).1.length := (hlen n).symm
          _ = (chain n).1.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
          _ ≤ hfin.toFinset.card := Finset.card_le_card hsub
      exact absurd (hcard (hfin.toFinset.card + 1)) (by omega)
    have hchain_mono : ∀ {m n}, m ≤ n → ∀ x ∈ (chain m).1, x ∈ (chain n).1 := by
      intro m n h
      induction n, h using Nat.le_induction with
      | base => intro _ hx; exact hx
      | succ n _ ih =>
        intro x hx
        show x ∈ (chain n).1 ++ [_]
        exact List.mem_append_left _ (ih x hx)
    refine ⟨false, H, hH_sub_B.trans hBA, hH_inf, fun s hsF hsH => ?_⟩
    -- Find `N` containing all elements of `s`
    have hexN : ∀ {L : List ℕ}, ListAllIn L H → ∃ N, ∀ x ∈ L, x ∈ (chain N).1 := by
      intro L
      induction L with
      | nil => intro _; exact ⟨0, fun _ h => by simp at h⟩
      | cons a t ihL =>
        intro hL
        obtain ⟨n₁, hn₁⟩ := Set.mem_iUnion.mp (hL a (by simp))
        obtain ⟨n₂, hn₂⟩ := ihL (fun x hx => hL x (by simp [hx]))
        refine ⟨max n₁ n₂, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hxt
        · exact hchain_mono (le_max_left n₁ n₂) _ hn₁
        · exact hchain_mono (le_max_right n₁ n₂) _ (hn₂ x hxt)
    obtain ⟨N, hN⟩ := hexN hsH
    have hs_sub : s ∈ (chain N).1.sublists :=
      List.mem_sublists.mpr (sublist_of_strictSorted_mem (hF_sort s hsF) (chain N).2.1 hN)
    have hsa_s := (chain N).2.2.2 s hs_sub
    obtain ⟨t, htF₀, hpre | ⟨u, rfl, _⟩⟩ := hsa_s B Subset.rfl hBinf
    · have hts : t = s := hF_thin t htF₀.1 s hsF hpre
      rw [← hts]
      exact htF₀.2
    · have hst : s = s ++ u := hF_thin s hsF (s ++ u) htF₀.1 ⟨u, rfl⟩
      rw [hst]
      exact htF₀.2
  · refine ⟨true, B, hBA, hBinf, fun s hsF hsB => ?_⟩
    by_contra hne
    have hfalse : c s = false := by cases h : c s <;> simp_all
    exact hrej0 ⟨s, ⟨hsF, hfalse⟩, Or.inr ⟨s, by simp, hsB⟩⟩

-- Each finite pattern has its own threshold in a single increasing sequence.
theorem simultaneous (F : ℕ → Set (List ℕ)) (color : ℕ → List ℕ → Bool)
    (sorted : ∀ n s, s ∈ F n → StrictSorted s)
    (thin : ∀ n s, s ∈ F n → ∀ t ∈ F n, s <+: t → s = t)
    (A : Set ℕ) (hA : A.Infinite) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ Set.range f ⊆ A ∧ ∃ b : ℕ → Bool,
      ∀ n s, s ∈ F n → ListAllIn s (f '' Set.Ici n) → color n s = b n := by
  let Domain := {s : Set ℕ // s.Infinite}
  have step (n : ℕ) (S : Domain) :
      ∃ (T : Domain) (b : Bool), T.val ⊆ S.val ∧
        ∀ s ∈ F n, ListAllIn s T.val → color n s = b := by
    obtain ⟨b,T,hT,hTi,hom⟩ := nash_williams (F n) (sorted n) (thin n) (color n) S.val S.property
    exact ⟨⟨T,hTi⟩,b,hT,hom⟩
  choose next colorOf subset hom using step
  let chain : ℕ → Domain := Nat.rec ⟨A,hA⟩ next
  have nested : Antitone (fun n => (chain n).val) :=
    antitone_nat_of_succ_le fun n => subset n (chain n)
  have chooseLarge (n lower : ℕ) : ∃ k, k ∈ (chain (n+1)).val ∧ lower < k :=
    (chain (n+1)).property.exists_gt lower
  choose large memLarge gtLarge using chooseLarge
  let f : ℕ → ℕ := Nat.rec (large 0 0) fun n k => large (n+1) k
  have mem (n : ℕ) : f n ∈ (chain (n+1)).val := by
    cases n with
    | zero => exact memLarge 0 0
    | succ n => exact memLarge (n+1) (f n)
  refine ⟨f,strictMono_nat_of_lt_succ (fun n => gtLarge (n+1) (f n)),?_,
    fun n => colorOf n (chain n),?_⟩
  · rintro _ ⟨k,rfl⟩
    exact nested (Nat.zero_le (k+1)) (mem k)
  · intro n s hs hin
    apply hom n (chain n) s hs
    intro i hi
    obtain ⟨k,hk,rfl⟩ := hin i hi
    exact nested (Nat.succ_le_succ hk) (mem k)

end Erdos591Proof.ThinFamilies

namespace Erdos591Proof
open Set

def tupleMap {X Y : Type} (f : X → Y) : (n : ℕ) → Tuple X n → Tuple Y n
  | 0, _ => PUnit.unit
  | n+1, x => toLex (f (ofLex x).1, tupleMap f n (ofLex x).2)

def Word.map {X Y : Type} (f : X → Y) (w : Word X) : Word Y :=
  ⟨w.len, tupleMap f w.len w.letters⟩

structure PairPattern where
  arity : ℕ
  left : Word (Word (Fin arity))
  right : Word (Word (Fin arity))

private instance : Countable PairPattern :=
  Function.Injective.countable
    (f := fun p : PairPattern => (⟨p.arity,(p.left,p.right)⟩ :
      Σ k, Word (Word (Fin k)) × Word (Word (Fin k))))
    (by rintro ⟨k,x,y⟩ ⟨j,u,v⟩ h; cases h; rfl)

def PairPattern.edge (p : PairPattern) (G : SimpleGraph (Word (Word ℕ)))
    (labels : List ℕ) (hlen : labels.length = p.arity) : Prop :=
  let f (i : Fin p.arity) := labels[i.val]'(hlen.symm ▸ i.isLt)
  G.Adj (p.left.map (Word.map f)) (p.right.map (Word.map f))

-- Simultaneously stabilize every way of interleaving two words with a fixed
-- shape. The threshold can depend on both shapes and on the interleaving.
theorem canonicalPairs (G : SimpleGraph (Word (Word ℕ))) (A : Set ℕ) (hA : A.Infinite) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ range f ⊆ A ∧ ∀ p : PairPattern,
      ∃ (threshold : ℕ) (blue : Prop), ∀ (l : List ℕ) (hl : l.length = p.arity),
        l.Pairwise (· < ·) → (∀ x ∈ l, x ∈ f '' Ici threshold) → (p.edge G l hl ↔ blue) := by
  classical
  let := Encodable.ofCountable PairPattern
  let empty : Word (Word (Fin 0)) := ⟨0,PUnit.unit⟩
  let pat (i : ℕ) := (Encodable.decode (α := PairPattern) i).getD ⟨0,empty,empty⟩
  let F (i : ℕ) := {l : List ℕ | l.Pairwise (· < ·) ∧ l.length = (pat i).arity}
  let col (i : ℕ) (l : List ℕ) :=
    if h : l.length = (pat i).arity then decide ((pat i).edge G l h) else false
  have hthin (i : ℕ) (s : List ℕ) (hs : s ∈ F i) (t : List ℕ) (ht : t ∈ F i)
      (hp : s <+: t) : s = t := by
    obtain ⟨tail,rfl⟩ := hp
    have hh := hs.2.trans ht.2.symm
    simp only [List.length_append] at hh
    have hz : tail.length = 0 := by omega
    simp [List.length_eq_zero_iff.mp hz]
  obtain ⟨f,hf,hfA,b,hom⟩ := ThinFamilies.simultaneous F col (fun _ _ h => h.1) hthin A hA
  refine ⟨f,hf,hfA,fun p => ?_⟩
  let i := Encodable.encode p
  have hi : pat i = p := by simp [pat,i]
  refine ⟨i,b i = true,fun l hl hsort hin => ?_⟩
  have hmem : l ∈ F i := ⟨hsort,hl.trans (congrArg PairPattern.arity hi).symm⟩
  have heq := hom i l hmem hin
  simp [col,hi,hl] at heq
  rw [← heq]
  simp

end Erdos591Proof

namespace Erdos591Proof
open Set

-- A finite diagram of colored edges using the same k labels is realized by
-- one assignment of those labels. The cutoff is the largest of the finitely
-- many individual cutoffs.
theorem finiteDiagrams (G : SimpleGraph (Word (Word ℕ))) (A : Set ℕ) (hA : A.Infinite) :
    ∃ color : PairPattern → Prop, ∀ (k : ℕ) (D : Finset PairPattern)
      (arity : ∀ p ∈ D, p.arity = k), ∃ l : List ℕ, ∃ hl : l.length = k,
      l.Pairwise (· < ·) ∧ (∀ x ∈ l, x ∈ A) ∧
      ∀ p (hp : p ∈ D), p.edge G l (hl.trans (arity p hp).symm) ↔ color p := by
  classical
  obtain ⟨f,hf,hA',patterns⟩ := canonicalPairs G A hA
  choose cutoff color hom using patterns
  refine ⟨color,fun k D hD => ?_⟩
  let N := D.sup cutoff
  let l := (List.range k).map fun n => f (N + n)
  have hlen : l.length = k := by simp [l]
  have hs : l.Pairwise (· < ·) := by
    dsimp only [l]
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp fun h => hf (by omega)
  refine ⟨l,hlen,hs,?_,?_⟩
  · intro x hx
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
    exact hA' ⟨_,rfl⟩
  · intro p hp
    apply hom p l _ hs
    intro x hx
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
    exact ⟨N+j,(Finset.le_sup hp : cutoff p ≤ N).trans (Nat.le_add_right N j),rfl⟩

theorem canonicalTriangleFree (G : SimpleGraph (Word (Word ℕ))) (hG : G.CliqueFree 3) :
    ∃ color : PairPattern → Prop,
      (∀ (k : ℕ) (D : Finset PairPattern) (arity : ∀ p ∈ D, p.arity = k),
        ∃ l : List ℕ, ∃ hl : l.length = k, l.Pairwise (· < ·) ∧
          ∀ p (hp : p ∈ D), p.edge G l (hl.trans (arity p hp).symm) ↔ color p) ∧
      ∀ (k : ℕ) (x y z : Word (Word (Fin k))),
        ¬ (color ⟨k,x,y⟩ ∧ color ⟨k,x,z⟩ ∧ color ⟨k,y,z⟩) := by
  classical
  obtain ⟨c,realize⟩ := finiteDiagrams G univ infinite_univ
  refine ⟨c,?_,?_⟩
  · intro k D arity
    obtain ⟨l,hl,hs,_,hom⟩ := realize k D arity
    exact ⟨l,hl,hs,hom⟩
  · intro k x y z ⟨hxy,hxz,hyz⟩
    let a : PairPattern := ⟨k,x,y⟩
    let b : PairPattern := ⟨k,x,z⟩
    let c' : PairPattern := ⟨k,y,z⟩
    let D : Finset PairPattern := {a,b,c'}
    have ha : a ∈ D := by simp [D]
    have hb : b ∈ D := by simp [D]
    have hc : c' ∈ D := by simp [D]
    have arity (p : PairPattern) (hp : p ∈ D) : p.arity = k := by
      simp only [D, Finset.mem_insert,Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> rfl
    obtain ⟨l,hl,_,_,hom⟩ := realize k D arity
    let g (i : Fin k) := l[i.val]'(hl.symm ▸ i.isLt)
    let v (t : Word (Word (Fin k))) := t.map (Word.map g)
    exact hG {v x,v y,v z} (SimpleGraph.is3Clique_triple_iff.mpr
      ⟨(hom a ha).mpr hxy,(hom b hb).mpr hxz,(hom c' hc).mpr hyz⟩)

end Erdos591Proof

namespace Erdos591Proof
open Ordinal

-- If a full independent copy is absent, arbitrarily high neighborhood ranks
-- occur on full copies themselves. This applies again inside each full copy.
theorem highNeighborhoods (G : SimpleGraph (Word (Word ℕ)))
    (noCopy : ¬ ∃ f : Word (Word ℕ) → Word (Word ℕ),
      StrictMono f ∧ ∀ x y, ¬ G.Adj (f x) (f y))
    {b : Ordinal.{0}} (hb : b < typeLT (Word (Word ℕ))) :
    typeLT (Word (Word ℕ)) ≤ typeLT {x // b < typeLT (G.neighborSet x)} := by
  classical
  let X := Word (Word ℕ)
  let col (x : X) := decide (b < typeLT (G.neighborSet x))
  have hrank : typeLT X = (ω : Ordinal.{0}) ^ ω ^ 2 := heightTwoOrderType
  obtain ⟨d,hd⟩ := vertexPartition ((ω : Ordinal.{0}) ^ (2 : ℕ)) col hrank.ge
  obtain ⟨e,he⟩ := fit (hrank.le.trans hd)
  cases d with
  | true =>
    let f (x : X) : {x // b < typeLT (G.neighborSet x)} :=
      ⟨(e x).val, by simpa [col] using (e x).property⟩
    exact monoBound (f := f) (fun _ _ h => he h)
  | false =>
    let f (x : X) : X := (e x).val
    have hf : StrictMono f := fun _ _ h => he h
    have hs (x : X) : typeLT ((G.comap f).neighborSet x) ≤ b := by
      let g (y : (G.comap f).neighborSet x) : G.neighborSet (f x) := ⟨f y.val,y.property⟩
      have hg : StrictMono g := fun _ _ h => hf h
      apply (monoBound hg).trans
      simpa [col,f] using (e x).property
    obtain ⟨g,hg,ind⟩ := boundedNeighborhoods (G.comap f) hb hs
    exact (noCopy ⟨f ∘ g,hf.comp hg,ind⟩).elim

end Erdos591Proof

namespace Erdos591Proof

open Ordinal Set

-- A completion has b unopened blocks left after the l outstanding leaves of
-- its current block. Opening a new block can give arbitrarily many leaves.
-- Choosing a leaf gives infinitely many ordered, disjoint sets of completions.
def FreeCompletions {X : Type} [LinearOrder X] : ℕ → ℕ → Set X → Prop
  | 0, 0, s => s.Nonempty
  | b+1, 0, s => ∀ k, ∃ m ≥ k, ∃ t ⊆ s, FreeCompletions b m t
  | b, l+1, s => ∃ t : ℕ → Set X, (∀ i, t i ⊆ s) ∧
      (∀ i j, i < j → ∀ x ∈ t i, ∀ y ∈ t j, x < y) ∧
      ∀ i, FreeCompletions b l (t i)
termination_by b l _ => (b,l)

private theorem orderedBranches {X : Type} [LinearOrder X] [WellFoundedLT X]
    {s : Set X} {t : ℕ → Set X} {a : Ordinal.{0}}
    (sub : ∀ i, t i ⊆ s) (sep : ∀ i j, i < j → ∀ x ∈ t i, ∀ y ∈ t j, x < y)
    (large : ∀ i, a ≤ typeLT (t i)) : a * ω ≤ typeLT s := by
  have emb (i : ℕ) := fit ((type_toType a).le.trans (large i))
  choose f hf using emb
  let g (z : ℕ ×ₗ a.ToType) : s :=
    ⟨(f (ofLex z).1 (ofLex z).2).val, sub _ (f _ _).property⟩
  have hg : StrictMono g := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    rcases Prod.Lex.lt_iff.mp h with hij | ⟨rfl,hxy⟩
    · exact sep _ _ hij _ (f i x).property _ (f j y).property
    · exact hf i hxy
  simpa only [lexProductType, type_nat_lt, type_toType] using monoBound hg

private theorem leafBound {X : Type} [LinearOrder X] [WellFoundedLT X] (b : ℕ)
    (a : Ordinal.{0}) (base : ∀ s : Set X, FreeCompletions b 0 s → a ≤ typeLT s)
    (l : ℕ) (s : Set X) (h : FreeCompletions b l s) : a * ω ^ l ≤ typeLT s := by
  induction l generalizing s with
  | zero => simpa using base s h
  | succ l ih =>
    rw [FreeCompletions] at h
    obtain ⟨t,sub,sep,ht⟩ := h
    rw [pow_succ, ← mul_assoc]
    exact orderedBranches sub sep (fun i => ih _ (ht i))

theorem freeCompletionsBound {X : Type} [LinearOrder X] [WellFoundedLT X] (b l : ℕ)
    (s : Set X) (h : FreeCompletions b l s) :
    ((ω : Ordinal.{0}) ^ (ω : Ordinal)) ^ b * ω ^ l ≤ typeLT s := by
  induction b generalizing l s with
  | zero =>
    apply leafBound 0 _ _ l s h
    intro t ht
    rw [FreeCompletions] at ht
    rw [pow_zero, Order.one_le_iff_ne_zero, type_ne_zero_iff_nonempty]
    exact ht.to_subtype
  | succ b ih =>
    apply leafBound (b+1) _ _ l s h
    intro t ht
    rw [FreeCompletions] at ht
    rw [pow_succ]
    apply (((isNormal_mul_right (pow_pos (opow_pos _ omega0_pos) b)).comp
      (isNormal_opow one_lt_omega0)).le_iff_forall_le isSuccLimit_omega0).mpr
    intro d hd
    obtain ⟨k,rfl⟩ := lt_omega0.mp hd
    obtain ⟨m,hm,u,hu,hfree⟩ := ht k
    change _ * ω ^ (k : Ordinal) ≤ _
    apply le_trans _ ((ih m u hfree).trans
      (monoBound (f := Set.inclusion hu) (fun _ _ hxy => hxy)))
    simpa only [opow_natCast] using
      (isNormal_mul_right (pow_pos (opow_pos (ω : Ordinal.{0}) omega0_pos) b)).monotone
        (opow_le_opow_right omega0_pos (Nat.cast_le.mpr hm))

-- The root needs only cofinally many branching sizes. Bounds at the completed
-- root therefore give the full height-two ordinal, including for sparse sizes.
theorem freeHeightTwoBound {X : Type} [LinearOrder X] [WellFoundedLT X] (s : Set X)
    (h : ∀ k, ∃ b ≥ k, FreeCompletions b 0 s) :
    (ω : Ordinal.{0}) ^ ω ^ 2 ≤ typeLT s := by
  rw [sq, opow_mul]
  apply (leOmegaPower (one_lt_opow.mpr ⟨one_lt_omega0,omega0_ne_zero⟩)).mpr
  intro k
  obtain ⟨b,hb,ht⟩ := h k
  have bound := freeCompletionsBound b 0 s ht
  simp only [pow_zero, mul_one] at bound
  refine le_trans ?_ bound
  rw [← opow_natCast, ← opow_natCast]
  exact opow_le_opow_right (opow_pos _ omega0_pos) (Nat.cast_le.mpr hb)

end Erdos591Proof

namespace Erdos591Proof.HeightTwoGame

-- One tree is built in preorder. A marked leaf gives the other tree a turn.
inductive Script (A : Type) where
  | done (result : A)
  | architect (next : ℕ → Script A)
  | builder (next : ℕ → Script A)
  | cut (next : Script A)

namespace Script

def bind {A B : Type} (p : Script A) (k : A → Script B) : Script B :=
  match p with
  | .done x => k x
  | .architect f => .architect fun n => (f n).bind k
  | .builder f => .builder fun n => (f n).bind k
  | .cut q => .cut (q.bind k)

-- One-based indices ensure that a marked successor precedes the final one:
-- its index was drawn strictly before the move specifying the total arity.
def indices : ℕ → Script (List ℕ)
  | 0 => .done []
  | n+1 => .builder fun i => (indices n).bind fun rest => .done (i :: rest)

def children {A : Type} (child : ℕ → Script A) : (n start : ℕ) → Script (Tuple A n)
  | 0, _ => .done PUnit.unit
  | n+1, start => (child start).bind fun x =>
      (children child n (start+1)).bind fun xs => .done (toLex (x,xs))

def node {A : Type} (markedCount : ℕ) (child : Bool → Script A) : Script (Word A) :=
  (indices markedCount).bind fun marked => .builder fun total =>
    (children (fun i => child (decide (i ∈ marked))) total 1).bind fun xs =>
      .done ⟨total,xs⟩

def leaf (marked : Bool) : Script ℕ :=
  .builder fun n => if marked then .cut (.done n) else .done n

def block (marked : Bool) : Script (Word ℕ) :=
  if marked then .architect fun n => node (n+1) leaf else node 0 leaf

def tree : Script (Word (Word ℕ)) := .architect fun n => node n block

-- Once the other tree has ended there can be no further oscillation cuts.
def finish {A L : Type} (p : Script A) (k : A → L) (bad : L) : LabelledGame L :=
  match p with
  | .done x => .terminal (k x)
  | .architect f => .architect fun n => (f n).finish k bad
  | .builder f => .builder fun n => (f n).finish k bad
  | .cut _ => .terminal bad

def untilCut {A L : Type} (p : Script A) (stop : A → LabelledGame L)
    (resume : Script A → LabelledGame L) : LabelledGame L :=
  match p with
  | .done x => stop x
  | .architect f => .architect fun n => (f n).untilCut stop resume
  | .builder f => .builder fun n => (f n).untilCut stop resume
  | .cut q => resume q

-- The Boolean is true exactly when the first tree supplies the last cell.
def interleave {A B : Type} (p : Script A) (q : Script B) :
    LabelledGame (Option (A × B × Bool)) :=
  match p with
  | .done x => q.finish (fun y => some (x,y,false)) none
  | .architect f => .architect fun n => (f n).interleave q
  | .builder f => .builder fun n => (f n).interleave q
  | .cut rest => q.untilCut
      (fun y => rest.finish (fun x => some (x,y,true)) none)
      (fun next => rest.interleave next)

end Script

-- The single clock controls all Builder moves across both trees, including
-- choices of arities and indices. Zero is excluded at the initial position.
def increasing {A : Type} (p : LabelledGame (Option A)) (last : ℕ) :
    LabelledGame (Option A) :=
  match p with
  | .terminal x => .terminal x
  | .architect f => .architect fun n => increasing (f n) last
  | .builder f => .builder fun n => if last < n then increasing (f n) n else .terminal none

abbrev Tree := Word (Word ℕ)

def game := increasing (Script.tree.interleave Script.tree) 0

def wins (G : SimpleGraph Tree) (inside : Bool) : Option (Tree × Tree × Bool) → Prop
  | none => False
  | some (x,y,b) => G.Adj x y ∧ b = inside

theorem dichotomy (G : SimpleGraph Tree) (H : Set ℕ) (hH : H.Infinite) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ Set.range f ⊆ H ∧
      ((∃ inside, (game.score (wins G inside)).outcome f true) ∨
        (game.score (fun l => ∃ b, wins G b l)).outcome f false) :=
  LabelledGame.finiteDichotomyWithin (wins G) game H hH

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

def Reaches {A : Type} : LabelledGame A → A → Prop
  | .terminal y, x => y = x
  | .builder f, x | .architect f, x => ∃ i, Reaches (f i) x

-- Count the marked leaves on one play through one tree.
def Cuts {A : Type} : Script A → A → ℕ → Prop
  | .done y, x, n => y = x ∧ n = 0
  | .architect f, x, n | .builder f, x, n => ∃ i, Cuts (f i) x n
  | .cut _, _, 0 => False
  | .cut p, x, n+1 => Cuts p x n

private theorem reachesFinish {A L : Type} (p : Script A) (k : A → L)
    (bad l : L) (hne : bad ≠ l) :
    Reaches (p.finish k bad) l ↔ ∃ x, Cuts p x 0 ∧ k x = l := by
  induction p with
  | done x => simp [finish, Reaches, Cuts]
  | cut => simp [finish, Reaches, Cuts, hne]
  | architect f ih | builder f ih =>
    simp only [finish, Reaches, Cuts, ih]
    constructor
    · rintro ⟨i,x,hx,he⟩
      exact ⟨x,⟨i,hx⟩,he⟩
    · rintro ⟨x,⟨i,hx⟩,he⟩
      exact ⟨i,x,hx,he⟩

private theorem moveExists {P : ℕ → ℕ → Prop} {Q : ℕ → Prop} :
    (∃ i j, P i j ∧ Q j) ↔ ∃ j, (∃ i, P i j) ∧ Q j := by
  constructor
  · rintro ⟨i,j,hp,hq⟩
    exact ⟨j,⟨i,hp⟩,hq⟩
  · rintro ⟨j,⟨i,hp⟩,hq⟩
    exact ⟨i,j,hp,hq⟩

private theorem moveExistsRight {P : ℕ → ℕ → Prop} {Q : ℕ → Prop} :
    (∃ i j, Q j ∧ P i j) ↔ ∃ j, Q j ∧ ∃ i, P i j := by
  constructor
  · rintro ⟨i,j,hq,hp⟩
    exact ⟨j,hq,i,hp⟩
  · rintro ⟨j,hq,i,hp⟩
    exact ⟨i,j,hq,hp⟩

-- Ignoring the clock, two prescribed one-tree outcomes can be interleaved
-- exactly when their cut counts agree (outside), or the first has one extra
-- cut (inside). In particular an unmatched cut after the end is rejected.
theorem interleaveCuts {A B : Type} (p : Script A) (q : Script B)
    (x : A) (y : B) (b : Bool) :
    Reaches (p.interleave q) (some (x,y,b)) ↔
      ∃ j, Cuts p x (j + b.toNat) ∧ Cuts q y j := by
  induction p generalizing q with
  | done z =>
    rw [interleave, reachesFinish _ _ _ _ (by simp)]
    cases b <;> simp [Cuts, Bool.toNat, eq_comm, and_comm]
  | architect f ih | builder f ih =>
    simp only [interleave, Reaches, Cuts, ih]
    exact moveExists
  | cut rest ih =>
    rw [interleave]
    induction q with
    | done z =>
      rw [untilCut, reachesFinish _ _ _ _ (by simp)]
      cases b <;> simp [Cuts, Bool.toNat, eq_comm, and_comm]
    | architect f hq | builder f hq =>
      simp only [untilCut, Reaches, Cuts, hq]
      exact moveExistsRight
    | cut next =>
      rw [untilCut, ih]
      constructor
      · rintro ⟨j,hx,hy⟩
        exact ⟨j+1,by simpa only [Nat.succ_add, Cuts] using hx,hy⟩
      · rintro ⟨j,hx,hy⟩
        cases j with
        | zero => exact False.elim hy
        | succ j => exact ⟨j,by simpa only [Nat.succ_add, Cuts] using hx,hy⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

open Set Ordinal

-- A transcript lists the root arity, then each block arity followed by its
-- leaves. Histories are stored in reverse order for constant-time extension.
def tokens {A : Type} (emit : A → List ℕ) : (l : ℕ) → Tuple A l → List ℕ
  | 0, _ => []
  | l+1, t => emit (ofLex t).1 ++ tokens emit l (ofLex t).2

def blockTokens (w : Word ℕ) := w.len :: tokens (fun x => [x]) w.len w.letters

def transcript (w : Tree) := w.len :: tokens blockTokens w.len w.letters

def Admissible (menu : List ℕ → ℕ → ℕ) (hist : List ℕ) : List ℕ → Prop
  | [] => True
  | n :: ns => n ∈ range (menu hist) ∧ Admissible menu (n :: hist) ns

private abbrev Rest (b l : ℕ) := Tuple ℕ l ×ₗ Tuple (Word ℕ) b

private def restTokens {b l : ℕ} (z : Rest b l) : List ℕ :=
  tokens (fun x => [x]) l (ofLex z).1 ++ tokens blockTokens b (ofLex z).2

private def prependLeaf {b l : ℕ} (v : ℕ) (z : Rest b l) : Rest b (l+1) :=
  toLex (toLex (v,(ofLex z).1),(ofLex z).2)

private theorem prependLeafMono {b l : ℕ} (v : ℕ) : StrictMono (@prependLeaf b l v) := by
  rintro ⟨a,x⟩ ⟨c,y⟩ h
  rcases Prod.Lex.lt_iff.mp h with h | ⟨rfl,h⟩
  · exact Prod.Lex.left _ _ (Prod.Lex.right _ h)
  · exact Prod.Lex.right _ h

private def openBlock {b : ℕ} (m : ℕ) (z : Rest b m) : Rest (b+1) 0 :=
  toLex (PUnit.unit,toLex (⟨m,(ofLex z).1⟩,(ofLex z).2))

private theorem openBlockMono {b : ℕ} (m : ℕ) : StrictMono (@openBlock b m) := by
  rintro ⟨a,x⟩ ⟨c,y⟩ h
  apply Prod.Lex.right
  rcases Prod.Lex.lt_iff.mp h with h | ⟨rfl,h⟩
  · exact Prod.Lex.left _ _ ((Word.lt_iff _ _).mpr (Or.inr ⟨rfl,h⟩))
  · exact Prod.Lex.right _ h

private theorem admissibleFree {X : Type} [LinearOrder X]
    (menu : List ℕ → ℕ → ℕ) (hm : ∀ p, StrictMono (menu p))
    (b l : ℕ) (hist : List ℕ) (s : Set X) (f : Rest b l → X) (hf : StrictMono f)
    (ok : ∀ z, Admissible menu hist (restTokens z) → f z ∈ s) :
    FreeCompletions b l s := by
  induction b generalizing l hist s with
  | zero =>
    induction l generalizing hist s with
    | zero =>
      rw [FreeCompletions]
      exact ⟨_, ok (toLex (PUnit.unit,PUnit.unit)) trivial⟩
    | succ l ih =>
      rw [FreeCompletions]
      let child (i : ℕ) (z : Rest 0 l) := f (prependLeaf (menu hist i) z)
      refine ⟨fun i => s ∩ range (child i), fun _ => inter_subset_left, ?_, ?_⟩
      · rintro i j hij _ ⟨_,a,rfl⟩ _ ⟨_,c,rfl⟩
        exact hf (Prod.Lex.left _ _ (Prod.Lex.left _ _ (hm hist hij)))
      · intro i
        apply ih (menu hist i :: hist) _ (child i) (hf.comp (prependLeafMono _))
        exact fun z hz => ⟨ok _ ⟨⟨i,rfl⟩,hz⟩,z,rfl⟩
  | succ b ib =>
    induction l generalizing hist s with
    | zero =>
      rw [FreeCompletions]
      intro k
      let m := menu hist k
      refine ⟨m,(hm hist).id_le k,s,Subset.rfl,?_⟩
      apply ib m (m :: hist) s (f ∘ openBlock m) (hf.comp (openBlockMono m))
      intro z hz
      apply ok
      change m ∈ range (menu hist) ∧ Admissible menu (m :: hist) _
      exact ⟨⟨k,rfl⟩, by simpa [restTokens, openBlock, tokens, blockTokens] using hz⟩
    | succ l ih =>
      rw [FreeCompletions]
      let child (i : ℕ) (z : Rest (b+1) l) := f (prependLeaf (menu hist i) z)
      refine ⟨fun i => s ∩ range (child i), fun _ => inter_subset_left, ?_, ?_⟩
      · rintro i j hij _ ⟨_,a,rfl⟩ _ ⟨_,c,rfl⟩
        exact hf (Prod.Lex.left _ _ (Prod.Lex.left _ _ (hm hist hij)))
      · intro i
        apply ih (menu hist i :: hist) _ (child i) (hf.comp (prependLeafMono _))
        exact fun z hz => ⟨ok _ ⟨⟨i,rfl⟩,hz⟩,z,rfl⟩

-- All branching sizes and leaf labels can be thinned simultaneously, even
-- when the allowed infinite sequence depends on every preceding choice.
theorem admissibleOrderType (menu : List ℕ → ℕ → ℕ) (hm : ∀ p, StrictMono (menu p)) :
    typeLT {w : Tree // Admissible menu [] (transcript w)} = (ω : Ordinal.{0}) ^ ω ^ 2 := by
  let s := {w : Tree | Admissible menu [] (transcript w)}
  change typeLT s = _
  apply le_antisymm
  · rw [← heightTwoOrderType]
    exact monoBound (f := (Subtype.val : s → Tree)) (fun _ _ h => h)
  · apply freeHeightTwoBound
    intro k
    let b := menu [] k
    refine ⟨b,(hm []).id_le k,?_⟩
    let f (z : Rest b 0) : Tree := ⟨b,(ofLex z).2⟩
    have hf : StrictMono f := by
      rintro ⟨a,x⟩ ⟨c,y⟩ h
      rcases Prod.Lex.lt_iff.mp h with h | ⟨_,h⟩
      · exact False.elim (lt_irrefl (PUnit.unit : PUnit.{1}) h)
      · exact (Word.lt_iff _ _).mpr (Or.inr ⟨rfl,h⟩)
    apply admissibleFree menu hm b 0 [b] s f hf
    exact fun z hz => ⟨⟨k,rfl⟩,hz⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Filter Set Ordinal Script

-- Forget the opponent, retaining the eventual quantifier on each Builder move.
def Force {A : Type} (f : ℕ → ℕ) (P : A → Prop) : Script A → Prop
  | .done x => P x
  | .architect t => ∃ n, Force f P (t n)
  | .builder t => ∀ᶠ k in atTop, Force f P (t (f k))
  | .cut p => Force f P p

private theorem forceBind {A B : Type} (f : ℕ → ℕ) (P : B → Prop) (p : Script A)
    (g : A → Script B) :
    Force f P (p.bind g) ↔ Force f (fun x => Force f P (g x)) p := by
  induction p with
  | done => rfl
  | cut p ih => exact ih
  | architect t ih | builder t ih => simp only [Script.bind, Force, ih]

private theorem forceConst {A : Type} (f : ℕ → ℕ) (p : Script A) (P : Prop) :
    Force f (fun _ => P) p ↔ P := by
  induction p with
  | done => rfl
  | cut p ih => exact ih
  | architect t ih => simp [Force, ih]
  | builder t ih => simp only [Force, ih, eventually_const]

def tupleQuantifier {A : Type} (Q : (A → Prop) → Prop) : (n : ℕ) → (Tuple A n → Prop) → Prop
  | 0, P => P PUnit.unit
  | n+1, P => Q fun x => tupleQuantifier Q n (fun xs => P (toLex (x,xs)))

def wordQuantifier {A : Type} (f : ℕ → ℕ) (Q : (A → Prop) → Prop) (P : Word A → Prop) :=
  ∀ᶠ i in atTop, tupleQuantifier Q (f i) (fun t => P ⟨f i,t⟩)

private theorem childrenForce {A : Type} (f : ℕ → ℕ) (child : ℕ → Script A)
    (Q : (A → Prop) → Prop) (hc : ∀ i P, Force f P (child i) ↔ Q P)
    (n start : ℕ) (P : Tuple A n → Prop) :
    Force f P (children child n start) ↔ tupleQuantifier Q n P := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [children, forceBind, Force, ih, hc, tupleQuantifier]

private theorem nodeForce {A : Type} (f : ℕ → ℕ) (child : Bool → Script A)
    (Q : (A → Prop) → Prop) (hc : ∀ b P, Force f P (child b) ↔ Q P)
    (d : ℕ) (P : Word A → Prop) :
    Force f P (node d child) ↔ wordQuantifier f Q P := by
  unfold node
  rw [forceBind]
  simp only [Force, forceBind, childrenForce f _ Q (fun i => hc _), forceConst,
    wordQuantifier]

def leafQuantifier (f : ℕ → ℕ) (P : ℕ → Prop) := ∀ᶠ i in atTop, P (f i)

theorem treeForce (f : ℕ → ℕ) (P : Tree → Prop) :
    Force f P tree ↔ wordQuantifier f (wordQuantifier f (leafQuantifier f)) P := by
  have hLeaf (b : Bool) (Q : ℕ → Prop) : Force f Q (leaf b) ↔ leafQuantifier f Q := by
    cases b <;> rfl
  have hBlock (b : Bool) (Q : Word ℕ → Prop) :
      Force f Q (block b) ↔ wordQuantifier f (leafQuantifier f) Q := by
    cases b <;> simp [block, Force, nodeForce f leaf _ hLeaf]
  simp [tree, Force, nodeForce f block _ hBlock]

private theorem tupleQuantifierBound {A : Type} [LinearOrder A] [WellFoundedLT A]
    (Q : (A → Prop) → Prop) (a : Ordinal.{0})
    (hq : ∀ P, Q P → a ≤ typeLT {x : A // P x}) (n : ℕ) (P : Tuple A n → Prop)
    (hP : tupleQuantifier Q n P) : a ^ n ≤ typeLT {x // P x} := by
  induction n with
  | zero =>
    rw [pow_zero, Order.one_le_iff_ne_zero, type_ne_zero_iff_nonempty]
    exact ⟨⟨PUnit.unit,hP⟩⟩
  | succ n ih =>
    let row (x : A) (y : Tuple A n) := P (toLex (x,y))
    let I := {x : A // tupleQuantifier Q n (row x)}
    have hi : a ≤ typeLT I := hq _ hP
    obtain ⟨g,hg⟩ := fit ((type_toType a).le.trans hi)
    have emb (i : a.ToType) := fit ((type_toType (a^n)).le.trans (ih (row (g i).val) (g i).property))
    choose e he using emb
    let z (p : a.ToType ×ₗ (a^n).ToType) : {x // P x} :=
      ⟨toLex ((g (ofLex p).1).val,(e (ofLex p).1 (ofLex p).2).val),(e _ _).property⟩
    have hz : StrictMono z := by
      rintro ⟨i,x⟩ ⟨j,y⟩ h
      rcases Prod.Lex.lt_iff.mp h with hl | ⟨rfl,hr⟩
      · exact Prod.Lex.left _ _ (hg hl)
      · exact Prod.Lex.right _ (he i hr)
    simpa only [lexProductType,type_toType,pow_succ] using monoBound hz

private theorem wordQuantifierBound {A : Type} [LinearOrder A] [WellFoundedLT A]
    [Fact (2 ≤ typeLT A)] (f : ℕ → ℕ) (hf : StrictMono f)
    (Q : (A → Prop) → Prop) (a : Ordinal.{0}) (ha : 1 < a)
    (hq : ∀ P, Q P → a ≤ typeLT {x : A // P x}) (P : Word A → Prop)
    (hP : wordQuantifier f Q P) : a ^ (ω : Ordinal) ≤ typeLT {x // P x} := by
  apply (leOmegaPower ha).mpr
  intro n
  obtain ⟨i,hi,hbig⟩ := (hP.and (eventually_ge_atTop n)).exists
  let g (x : {x : Tuple A (f i) // P ⟨f i,x⟩}) : {x // P x} := ⟨⟨f i,x.val⟩,x.property⟩
  have hg : StrictMono g := fun _ _ h => (Word.lt_iff _ _).mpr (Or.inr ⟨rfl,h⟩)
  have ht := (tupleQuantifierBound Q a hq (f i) _ hi).trans (monoBound hg)
  apply le_trans _ ht
  rw [← opow_natCast, ← opow_natCast]
  exact opow_le_opow_right ha.pos (Nat.cast_le.mpr (hbig.trans (hf.id_le i)))

theorem treeForceOrderType (f : ℕ → ℕ) (hf : StrictMono f) (P : Tree → Prop)
    (hP : Force f P tree) : typeLT {x // P x} = (ω : Ordinal.{0}) ^ ω ^ 2 := by
  apply le_antisymm
  · rw [← heightTwoOrderType]
    exact monoBound (f := (Subtype.val : {x // P x} → Tree)) (fun _ _ h => h)
  · rw [sq, opow_mul]
    apply wordQuantifierBound f hf _ _ (one_lt_opow.mpr ⟨one_lt_omega0,omega0_ne_zero⟩) _
      P ((treeForce f P).mp hP)
    apply wordQuantifierBound f hf _ _ one_lt_omega0
    intro R hR
    obtain ⟨k,hk⟩ := eventually_atTop.mp hR
    let g (i : ℕ) : {x // R x} := ⟨f (k+i), hk _ (Nat.le_add_right k i)⟩
    have hg : StrictMono g := fun _ _ h => hf (Nat.add_lt_add_left h k)
    simpa only [type_nat_lt] using monoBound hg

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Filter Script Set Ordinal

private theorem finishForce {A L : Type} (p : Script A) (k : A → Option L)
    (P : Option L → Prop) (hb : ¬ P none) (f : ℕ → ℕ) (last : ℕ)
    (h : ((increasing (p.finish k none) last).score P).outcome f true) :
    Force f (fun x => P (k x)) p := by
  induction p generalizing last with
  | done => exact h
  | cut => exact False.elim (hb h)
  | architect t ih =>
    obtain ⟨i,hi⟩ := h
    exact ⟨i,ih i last hi⟩
  | builder t ih =>
    change ∀ᶠ i in atTop, ((if last < f i then increasing ((t (f i)).finish k none) (f i)
      else LabelledGame.terminal none).score P).outcome f true at h
    filter_upwards [h] with i hi
    split at hi
    · exact ih _ _ hi
    · exact False.elim (hb hi)

private def NoCuts {A : Type} : Script A → Prop
  | .done _ => True
  | .cut _ => False
  | .builder t | .architect t => ∀ i, NoCuts (t i)

private theorem noCutsBind {A B : Type} (p : Script A) (k : A → Script B)
    (hp : NoCuts p) (hk : ∀ x, NoCuts (k x)) : NoCuts (p.bind k) := by
  induction p with
  | done x => exact hk x
  | cut => exact hp.elim
  | architect t ih | builder t ih => exact fun i => ih i (hp i)

private theorem noCutsChildren {A : Type} (child : ℕ → Script A)
    (h : ∀ i, NoCuts (child i)) (n start : ℕ) : NoCuts (children child n start) := by
  induction n generalizing start with
  | zero => trivial
  | succ n ih =>
    exact noCutsBind _ _ (h start) fun _ => noCutsBind _ _ (ih _) fun _ => trivial

private theorem noCutsNode {A : Type} (child : Bool → Script A) (hc : NoCuts (child false)) :
    NoCuts (node 0 child) := by
  intro total
  apply noCutsBind
  · apply noCutsChildren
    intro i
    simpa using hc
  · intro x
    trivial

private theorem noCutsFirst {A B : Type} (p : Script A) (q : Script B)
    (hp : NoCuts p) (P : Option (A × B × Bool) → Prop) (hb : ¬ P none)
    (f : ℕ → ℕ) (last : ℕ) (h : ((increasing (p.interleave q) last).score P).outcome f true) :
    Force f (fun x => Force f (fun y => P (some (x,y,false))) q) p := by
  induction p generalizing last with
  | done x => exact finishForce q _ P hb f last h
  | cut => exact hp.elim
  | architect t ih =>
    obtain ⟨i,hi⟩ := h
    exact ⟨i,ih i (hp i) last hi⟩
  | builder t ih =>
    change ∀ᶠ i in atTop, ((if last < f i then increasing ((t (f i)).interleave q) (f i)
      else LabelledGame.terminal none).score P).outcome f true at h
    filter_upwards [h] with i hi
    split at hi
    · exact ih _ (hp _) _ hi
    · exact False.elim (hb hi)

private theorem forceWitness {A : Type} (f : ℕ → ℕ) (P : A → Prop) (p : Script A)
    (h : Force f P p) : ∃ x, P x := by
  induction p with
  | done x => exact ⟨x,h⟩
  | cut p ih => exact ih h
  | architect t ih =>
    obtain ⟨i,hi⟩ := h
    exact ih i hi
  | builder t ih =>
    obtain ⟨i,hi⟩ := h.exists
    exact ih _ hi

private def Compatible {A : Type} (Q : (A → Prop) → Prop) :=
  ∀ P R, Q P → Q R → ∃ x, P x ∧ R x

private theorem tupleCompatible {A : Type} (Q : (A → Prop) → Prop) (hq : Compatible Q)
    (n : ℕ) : Compatible (tupleQuantifier Q n) := by
  intro P R hP hR
  induction n with
  | zero => exact ⟨PUnit.unit,hP,hR⟩
  | succ n ih =>
    obtain ⟨x,hx,kx⟩ := hq _ _ hP hR
    obtain ⟨xs,hs,ks⟩ := ih _ _ hx kx
    exact ⟨toLex (x,xs),hs,ks⟩

private theorem wordCompatible {A : Type} (f : ℕ → ℕ) (Q : (A → Prop) → Prop)
    (hq : Compatible Q) : Compatible (wordQuantifier f Q) := by
  intro P R hP hR
  obtain ⟨i,hi,ki⟩ := (hP.and hR).exists
  obtain ⟨t,ht,kt⟩ := tupleCompatible Q hq (f i) _ _ hi ki
  exact ⟨⟨f i,t⟩,ht,kt⟩

private theorem treeCompatible (f : ℕ → ℕ) : Compatible (fun P => Force f P tree) := by
  intro P R hP hR
  apply wordCompatible f _ (wordCompatible f _ ?_) _ _ ((treeForce f P).mp hP)
    ((treeForce f R).mp hR)
  intro S T hS hT
  obtain ⟨i,hi,ki⟩ := (hS.and hT).exists
  exact ⟨f i,hi,ki⟩

theorem zeroOpeningTriangle (G : SimpleGraph Tree) (f : ℕ → ℕ) (inside : Bool)
    (h : ((increasing ((node 0 block).interleave tree) 0).score (wins G inside)).outcome f true) :
    ∃ x y z, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z := by
  let N (x y : Tree) := wins G inside (some (x,y,false))
  let good (x : Tree) := Force f (N x) tree
  have hp : NoCuts (node 0 block) := noCutsNode _ (noCutsNode leaf (fun _ => trivial))
  have hall : Force f good tree := ⟨0,noCutsFirst _ _ hp _ id f 0 h⟩
  obtain ⟨x,hx⟩ := forceWitness f good tree hall
  obtain ⟨y,hy,hxy⟩ := treeCompatible f good (N x) hall hx
  obtain ⟨z,hxz,hyz⟩ := treeCompatible f (N x) (N y) hx hy
  exact ⟨x,y,z,hxy.1,hxz.1,hyz.1⟩

-- If a winning Architect opens without a marked block, the whole first tree
-- is built in a single turn. Its neighborhood already has the target type.
theorem zeroOpeningNeighborhood (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (inside : Bool)
    (h : ((increasing ((node 0 block).interleave tree) 0).score (wins G inside)).outcome f true) :
    ∃ x, typeLT (G.neighborSet x) = (ω : Ordinal.{0}) ^ ω ^ 2 := by
  have hp : NoCuts (node 0 block) := noCutsNode _ (noCutsNode leaf (fun _ => trivial))
  obtain ⟨x,hh⟩ := forceWitness _ _ _ (noCutsFirst _ _ hp _ id f 0 h)
  have bound := treeForceOrderType f hf _ hh
  refine ⟨x,le_antisymm ?_ ?_⟩
  · rw [← heightTwoOrderType]
    exact monoBound (f := (Subtype.val : G.neighborSet x → Tree)) (fun _ _ hxy => hxy)
  · rw [← bound]
    exact monoBound (f := fun y => (⟨y.val,y.property.1⟩ : G.neighborSet x))
      (fun _ _ hxy => hxy)

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Ordinal Cardinal Set Script

def IndependentCopy (G : SimpleGraph Tree) :=
  ∃ e : Tree → Tree, StrictMono e ∧ ∀ x y, ¬ G.Adj (e x) (e y)

private theorem copyOfNeighborhood (G : SimpleGraph Tree) (hg : G.CliqueFree 3) {v : Tree}
    (h : typeLT (G.neighborSet v) = (ω : Ordinal.{0}) ^ ω ^ 2) : IndependentCopy G := by
  obtain ⟨f,hf⟩ := fit (heightTwoOrderType.trans h.symm).le
  refine ⟨fun x => (f x).val,fun _ _ hxy => hf hxy,?_⟩
  intro x y hxy
  exact G.isIndepSet_neighborSet_of_triangleFree hg v (f x).property (f y).property
    (G.ne_of_adj hxy) hxy

-- After the opening dichotomy only an opening with at least one cut and the
-- all-Builder case require joint constructions on more than one tree.
theorem openingCases (G : SimpleGraph Tree) (hg : G.CliqueFree 3) :
    IndependentCopy G ∨ ∃ f : ℕ → ℕ, StrictMono f ∧
      ((∃ d inside, ((increasing ((node (d+1) block).interleave tree) 0).score
          (wins G inside)).outcome f true) ∨
       (game.score (fun l => ∃ b, wins G b l)).outcome f false) := by
  obtain ⟨f,hf,_,h⟩ := dichotomy G univ Set.infinite_univ
  rcases h with ⟨inside,hw⟩ | h
  · obtain ⟨d,hd⟩ := hw
    cases d with
    | zero =>
      obtain ⟨x,hx⟩ := zeroOpeningNeighborhood G f hf inside hd
      exact Or.inl (copyOfNeighborhood G hg hx)
    | succ d => exact Or.inr ⟨f,hf,Or.inl ⟨d,inside,hd⟩⟩
  · exact Or.inr ⟨f,hf,Or.inr h⟩

universe u

theorem ordinalRamseyOfLevelGraphs
    (ind : ∀ G : SimpleGraph Tree, G.CliqueFree 3 →
      (∀ x y : Tree, x.len = y.len → ¬ G.Adj x y) → IndependentCopy G) :
    OrdinalCardinalRamsey ((ω : Ordinal.{u}) ^ ω ^ 2) (ω ^ ω ^ 2) 3 := by
  intro red blue comp
  obtain hb | ⟨e,he,hsame⟩ := homogeneousOrdinalLevels red blue comp
  · exact Or.inr hb
  classical
  by_cases hfree : blue.CliqueFree 3
  · let G := blue.comap e
    have free : G.CliqueFree 3 := by
      intro s hs
      obtain ⟨x,y,z,hxy,hxz,hyz,_⟩ := SimpleGraph.is3Clique_iff.mp hs
      exact hfree {e x,e y,e z} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy,hxz,hyz⟩)
    have lev (x y : Tree) (h : x.len = y.len) (hadj : G.Adj x y) : False := by
      have hr := hsame x y (G.ne_of_adj hadj) h
      have hb : (red ⊓ blue).Adj (e x) (e y) := ⟨hr,hadj⟩
      rw [comp.disjoint.eq_bot] at hb
      exact hb
    obtain ⟨g,hg,hi⟩ := ind G free lev
    let f (z : ULift.{u} Tree) := e (g z.down)
    have hf : StrictMono f := fun _ _ h => he (hg h)
    refine Or.inl ⟨range f,?_,?_⟩
    · rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ hxy
      have ht : (red ⊔ blue).Adj (f x) (f y) := by
        rw [comp.codisjoint.eq_top]
        exact hxy
      exact ht.resolve_right (hi x.down y.down)
    · let iso : ULift.{u} Tree ≃o range f :=
        { toEquiv := Equiv.ofBijective (fun z => ⟨f z,z,rfl⟩)
            ⟨fun _ _ h => hf.injective (congrArg Subtype.val h),
             fun ⟨_,z,h⟩ => ⟨z,Subtype.ext h⟩⟩
          map_rel_iff' := fun {_ _} => hf.le_iff_le }
      exact iso.symm.ordinalType_congr.trans liftedHeightTwoOrderType
  · change ¬ ∀ s, ¬ blue.IsNClique 3 s at hfree
    push Not at hfree
    obtain ⟨s,hs⟩ := hfree
    exact Or.inr ⟨(s : Set _),hs.1,by simp [hs.2]⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.PairGame
open Filter

-- The Architect uses a witness at winning positions. The Builder can be given
-- an explicit cutoff at every history, shared by any construction revisiting
-- that history. Histories list actual moves in chronological order.
structure Policy where
  action : List ℕ → ℕ
  cutoff : List ℕ → ℕ

def Plays (g : PairGame) (f : ℕ → ℕ) (win : Bool) (policy : Policy) :
    List ℕ → List ℕ → Prop
  | _, [] => True
  | past, n :: ns =>
    (match g.position past with
      | .terminal _ => False
      | .architect _ => win = true → n = policy.action past
      | .builder _ => ∃ k ≥ policy.cutoff past, f k = n) ∧
    Plays g f win policy (past ++ [n]) ns

private theorem position_append (g : PairGame) (p s : List ℕ) :
    g.position (p ++ s) = (g.position p).position s := by
  induction p generalizing g with
  | nil => rfl
  | cons n p ih => exact ih (g.child n)

theorem policyOfOutcome (g : PairGame) (f : ℕ → ℕ) (win : Bool)
    (h : g.outcome f win) :
    ∃ policy, ∀ moves, Plays g f win policy [] moves →
      (g.position moves).outcome f win := by
  classical
  let pick (p : List ℕ) (n : ℕ) :=
    ((g.position p).child n).outcome f true
  let action (p : List ℕ) := if hp : ∃ n, pick p n then hp.choose else 0
  let safe (p : List ℕ) (k : ℕ) :=
    ∀ i ≥ k, ((g.position p).child (f i)).outcome f win
  let cutoff (p : List ℕ) := if hp : ∃ k, safe p k then hp.choose else 0
  let policy : Policy := ⟨action,cutoff⟩
  have step (past : List ℕ) (n : ℕ) (hv : (g.position past).outcome f win)
      (hm : match g.position past with
        | .terminal _ => False
        | .architect _ => win = true → n = policy.action past
        | .builder _ => ∃ k ≥ policy.cutoff past, f k = n) :
      (g.position (past ++ [n])).outcome f win := by
    rw [position_append]
    change ((g.position past).child n).outcome f win
    cases he : g.position past with
    | terminal q => simp [he] at hm
    | architect t =>
      rw [he] at hv hm
      cases win with
      | false => exact hv n
      | true =>
        have hex : ∃ j, pick past j := by simpa [pick, he, child, outcome] using hv
        have hw := hex.choose_spec
        have ha : policy.action past = hex.choose := dif_pos hex
        rw [hm rfl,ha]
        simpa only [pick,he,child] using hw
    | builder t =>
      rw [he] at hv hm
      obtain ⟨k,hk,rfl⟩ := hm
      have hex : ∃ j, safe past j := by
        simpa only [safe, he, child] using eventually_atTop.mp hv
      have hc : policy.cutoff past = hex.choose := dif_pos hex
      rw [hc] at hk
      simpa only [safe,he,child] using hex.choose_spec k hk
  have loop (s p : List ℕ) (hp : (g.position p).outcome f win)
      (hs : Plays g f win policy p s) : (g.position (p ++ s)).outcome f win := by
    induction s generalizing p with
    | nil => simpa using hp
    | cons n ns ih =>
      obtain ⟨hm,hr⟩ := hs
      simpa [List.append_assoc] using ih (p ++ [n]) (step p n hp hm) hr
  exact ⟨policy,fun s hs => loop s [] h hs⟩

end Erdos591Proof.PairGame

namespace Erdos591Proof.HeightTwoGame
open Set

-- A schedule says which simultaneous games read each number. This permits
-- common maxima and overlapping sets of marked indices, with different
-- history-dependent thresholds for every game.
def projection {I : Type} [DecidableEq I] (i : I) :
    List (Finset I × ℕ) → List ℕ
  | [] => []
  | (js,k) :: rest =>
    if i ∈ js then k :: projection i rest else projection i rest

def Above (cutoff : List ℕ → ℕ) (history : List ℕ) : List ℕ → Prop
  | [] => True
  | k :: ks => cutoff history ≤ k ∧ Above cutoff (history ++ [k]) ks

theorem realizeSchedule {I : Type} [DecidableEq I] (cutoff : I → List ℕ → ℕ)
    (schedule : List (Finset I)) (hist : I → List ℕ) (lo : ℕ) :
    ∃ trace : List (Finset I × ℕ), trace.map Prod.fst = schedule ∧
      (lo :: trace.map Prod.snd).Pairwise (· < ·) ∧
      ∀ i, Above (cutoff i) (hist i) (projection i trace) := by
  induction schedule generalizing hist lo with
  | nil => exact ⟨[],rfl,by simp,fun _ => trivial⟩
  | cons js todo ih =>
    let k := max (lo+1) (js.sup fun i => cutoff i (hist i))
    let next (i : I) := if i ∈ js then hist i ++ [k] else hist i
    obtain ⟨rest,hr,hs,ha⟩ := ih next k
    have hl : lo < k := lt_of_lt_of_le (Nat.lt_succ_self lo) (le_max_left _ _)
    refine ⟨(js,k) :: rest,by simp [hr],?_,?_⟩
    · apply List.pairwise_cons.mpr
      refine ⟨?_,hs⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hl
      · exact hl.trans ((List.pairwise_cons.mp hs).1 v hv)
    · intro i
      by_cases hi : i ∈ js
      · simp only [projection,if_pos hi,Above]
        exact ⟨(Finset.le_sup (f := fun j => cutoff j (hist j)) hi).trans (le_max_right _ _),
          by simpa [next,hi] using ha i⟩
      · simpa [projection,next,hi] using ha i

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Set Ordinal

private theorem admissibleTail (menu : List ℕ → ℕ → ℕ) (pool : Set ℕ)
    (inPool : ∀ p k, menu p k ∈ pool)
    (above : ∀ p v, v ∈ p → ∀ k, v < menu p k) (xs hist : List ℕ)
    (h : Admissible menu hist xs) :
    xs.Pairwise (· < ·) ∧ (∀ x ∈ xs, x ∈ pool) ∧ ∀ y ∈ hist, ∀ x ∈ xs, y < x := by
  induction xs generalizing hist with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨⟨k,hk⟩,ht⟩ := h
    subst x
    obtain ⟨hs,hi,hb⟩ := ih _ ht
    refine ⟨List.pairwise_cons.mpr ⟨hb _ (List.mem_cons_self),hs⟩,?_,?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact inPool _ _
      · exact hi x hx
    · intro y hy x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact above _ y hy k
      · exact hb y (List.mem_cons_of_mem _ hy) x hx

-- Trees at different root arities have disjoint numerical alphabets. Their
-- first leaves occur in root order, before the later tree's root arity. The
-- family still has the entire target order type.
theorem separatedHeightTwoFamily (H : Set ℕ) (hH : H.Infinite) :
    ∃ s : Set Tree, typeLT s = (ω : Ordinal.{0}) ^ ω ^ 2 ∧
      (∀ w ∈ s, (transcript w).Pairwise (· < ·) ∧ ∀ x ∈ transcript w, x ∈ H) ∧
      ∀ w ∈ s, ∀ z ∈ s, w.len < z.len →
        (∀ x ∈ transcript w, x ∉ transcript z) ∧
        ∃ a, (transcript w)[2]? = some a ∧ a < z.len := by
  classical
  let h := Nat.nth (· ∈ H)
  have hh : StrictMono h := Nat.nth_strictMono hH
  let pool (n k : ℕ) := h (Nat.pair n k)
  have mon (n : ℕ) : StrictMono (pool n) := fun _ _ hlt => hh (Nat.pair_lt_pair_right n hlt)
  let start : ℕ → ℕ := Nat.rec 1 (fun n k => pool n (k+2) + 1)
  let root (n : ℕ) := pool n (start n)
  let arity (n : ℕ) := pool n (start n+1)
  let leaf₀ (n : ℕ) := pool n (start n+2)
  have h₁ (n : ℕ) : root n < arity n := mon n (Nat.lt_succ_self _)
  have h₂ (n : ℕ) : arity n < leaf₀ n := mon n (Nat.lt_succ_self _)
  have h₃ (n : ℕ) : leaf₀ n < root (n+1) :=
    lt_of_lt_of_le (Nat.lt_succ_self _) ((mon (n+1)).id_le (start (n+1)))
  have hr : StrictMono root := strictMono_nat_of_lt_succ fun n => ((h₁ n).trans (h₂ n)).trans (h₃ n)
  have hrpos (n : ℕ) : 0 < root n := by
    apply lt_of_lt_of_le _ ((mon n).id_le (start n))
    cases n <;> simp [start]
  let menu (n : ℕ) (p : List ℕ) (i : ℕ) := pool n (p.sum + 1 + i)
  have hm (n : ℕ) (p : List ℕ) : StrictMono (menu n p) := fun _ _ hij =>
    mon n (Nat.add_lt_add_left hij _)
  let s := {w : Tree | ∃ n xs, transcript w = root n :: arity n :: leaf₀ n :: xs ∧
    Admissible (menu n) [leaf₀ n] xs}
  have tailFacts (n : ℕ) (xs : List ℕ) (hx : Admissible (menu n) [leaf₀ n] xs) :=
    admissibleTail (menu n) (range (pool n)) (fun p k => ⟨p.sum+1+k,rfl⟩)
      (fun p v hv k => lt_of_lt_of_le
        (by have := ThinFamilies.mem_le_list_sum hv; omega :
          v < p.sum+1+k) ((mon n).id_le _)) xs _ hx
  have allPool (n : ℕ) (xs : List ℕ) (hx : Admissible (menu n) [leaf₀ n] xs) :
      ∀ x ∈ root n :: arity n :: leaf₀ n :: xs, x ∈ range (pool n) := by
    intro x hx'
    simp only [List.mem_cons] at hx'
    rcases hx' with rfl | rfl | rfl | hx'
    · exact ⟨_,rfl⟩
    · exact ⟨_,rfl⟩
    · exact ⟨_,rfl⟩
    · exact (tailFacts n xs hx).2.1 _ hx'
  refine ⟨s,le_antisymm ?_ ?_,?_,?_⟩
  · rw [← heightTwoOrderType]
    exact monoBound (f := (Subtype.val : s → Tree)) (fun _ _ hxy => hxy)
  · rw [sq, opow_mul]
    apply (leOmegaPower (one_lt_opow.mpr ⟨one_lt_omega0,omega0_ne_zero⟩)).mpr
    intro k
    let n := k+1
    let b := root n - 1
    let l := arity n - 1
    have hroot : b+1 = root n := Nat.sub_add_cancel (hrpos n)
    have harity : l+1 = arity n := Nat.sub_add_cancel ((hrpos n).trans (h₁ n))
    let pack (z : Rest b l) : Tree :=
      ⟨b+1,toLex (⟨l+1,toLex (leaf₀ n,(ofLex z).1)⟩,(ofLex z).2)⟩
    have hp : StrictMono pack := by
      rintro ⟨a,x⟩ ⟨c,y⟩ hlt
      apply (Word.lt_iff _ _).mpr
      right
      refine ⟨rfl,?_⟩
      rcases Prod.Lex.lt_iff.mp hlt with hlt | ⟨rfl,hlt⟩
      · exact Prod.Lex.left _ _ ((Word.lt_iff _ _).mpr (Or.inr ⟨rfl,Prod.Lex.right _ hlt⟩))
      · exact Prod.Lex.right _ hlt
    have ht := admissibleFree (menu n) (hm n) b l [leaf₀ n] s pack hp
      (fun z hz => ⟨n,restTokens z,by
        change (b+1) :: (l+1) :: leaf₀ n :: restTokens z = _
        rw [hroot,harity],hz⟩)
    have bound := freeCompletionsBound b l s ht
    have hkb : k ≤ b := by have hhkn : k+1 ≤ root n := hr.id_le n; dsimp only [b]; omega
    apply le_trans _ bound
    calc ((ω : Ordinal.{0}) ^ (ω : Ordinal)) ^ k ≤ (ω ^ (ω : Ordinal)) ^ b := by
            rw [← opow_natCast, ← opow_natCast]
            exact opow_le_opow_right (opow_pos _ omega0_pos) (Nat.cast_le.mpr hkb)
      _ ≤ _ := by
        conv_lhs => rw [← mul_one ((ω ^ (ω : Ordinal)) ^ b)]
        exact (isNormal_mul_right (pow_pos (opow_pos _ omega0_pos) b)).monotone
          (Order.one_le_iff_pos.mpr (pow_pos omega0_pos l))
  · rintro w ⟨n,xs,he,hx⟩
    rw [he]
    obtain ⟨hs,_,hb⟩ := tailFacts n xs hx
    have hl := hb (leaf₀ n) (List.mem_singleton_self _)
    constructor
    · simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp]
      exact ⟨⟨h₁ n,(h₁ n).trans (h₂ n),fun x hx => ((h₁ n).trans (h₂ n)).trans (hl x hx)⟩,
        ⟨h₂ n,fun x hx => (h₂ n).trans (hl x hx)⟩,hl,hs⟩
    · intro x hx'
      obtain ⟨i,rfl⟩ := allPool n xs hx x hx'
      exact Nat.nth_mem_of_infinite hH _
  · rintro w ⟨n,xs,hw,hx⟩ z ⟨m,ys,hz,hy⟩ hlt
    have hrootW : w.len = root n := List.cons.inj hw |>.1
    have hrootZ : z.len = root m := List.cons.inj hz |>.1
    rw [hrootW,hrootZ] at hlt
    have hnm := hr.lt_iff_lt.mp hlt
    rw [hw,hz,hrootZ]
    refine ⟨?_,leaf₀ n,rfl,(h₃ n).trans_le (hr.monotone hnm)⟩
    intro x hxx hyy
    obtain ⟨i,hi⟩ := allPool n xs hx x hxx
    obtain ⟨j,hj⟩ := allPool m ys hy x hyy
    exact hnm.ne (Nat.pair_eq_pair.mp (hh.injective (hi.trans hj.symm))).1

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Filter Script

-- Membership in a large one-tree set can be maintained against every
-- Architect choice while interleaving the construction with another tree.
def Keep {A : Type} (f : ℕ → ℕ) (P : A → Prop) : Script A → Prop
  | .done x => P x
  | .architect t => ∀ n, Keep f P (t n)
  | .builder t => ∀ᶠ k in atTop, Keep f P (t (f k))
  | .cut p => Keep f P p

private theorem keepBind {A B : Type} (f : ℕ → ℕ) (P : B → Prop) (p : Script A)
    (g : A → Script B) :
    Keep f P (p.bind g) ↔ Keep f (fun x => Keep f P (g x)) p := by
  induction p with
  | done => rfl
  | cut p ih => exact ih
  | architect t ih | builder t ih => simp only [Script.bind, Keep, ih]

private theorem keepConst {A : Type} (f : ℕ → ℕ) (p : Script A) (P : Prop) :
    Keep f (fun _ => P) p ↔ P := by
  induction p with
  | done => rfl
  | cut p ih => exact ih
  | architect t ih => simp [Keep, ih]
  | builder t ih => simp only [Keep, ih, eventually_const]

private theorem childrenKeep {A : Type} (f : ℕ → ℕ) (child : ℕ → Script A)
    (Q : (A → Prop) → Prop) (hc : ∀ i P, Keep f P (child i) ↔ Q P)
    (n start : ℕ) (P : Tuple A n → Prop) :
    Keep f P (children child n start) ↔ tupleQuantifier Q n P := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp only [children, keepBind, Keep, ih, hc, tupleQuantifier]

private theorem nodeKeep {A : Type} (f : ℕ → ℕ) (child : Bool → Script A)
    (Q : (A → Prop) → Prop) (hc : ∀ b P, Keep f P (child b) ↔ Q P)
    (d : ℕ) (P : Word A → Prop) :
    Keep f P (node d child) ↔ wordQuantifier f Q P := by
  unfold node
  rw [keepBind]
  simp only [Keep, keepBind, childrenKeep f _ Q (fun i => hc _), keepConst,
    wordQuantifier]

theorem treeKeep (f : ℕ → ℕ) (P : Tree → Prop) : Keep f P tree ↔ Force f P tree := by
  have hLeaf (b : Bool) (Q : ℕ → Prop) : Keep f Q (leaf b) ↔ leafQuantifier f Q := by
    cases b <;> rfl
  have hBlock (b : Bool) (Q : Word ℕ → Prop) :
      Keep f Q (block b) ↔ wordQuantifier f (leafQuantifier f) Q := by
    cases b <;> simp [block, Keep, nodeKeep f leaf _ hLeaf]
  rw [treeForce]
  simp [tree, Keep, nodeKeep f block _ hBlock]

private def Keeps {A : Type} (f : ℕ → ℕ) (P : A → Prop) : LabelledGame A → Prop
  | .terminal x => P x
  | .architect t => ∀ n, Keeps f P (t n)
  | .builder t => ∀ᶠ k in atTop, Keeps f P (t (f k))

private theorem keepsFinish {A B : Type} (f : ℕ → ℕ) (P : A → Prop) (Q : B → Prop)
    (p : Script A) (k : A → B) (bad : B) (hb : Q bad) (h : Keep f P p)
    (hk : ∀ x, P x → Q (k x)) : Keeps f Q (p.finish k bad) := by
  induction p with
  | done x => exact hk x h
  | cut => exact hb
  | architect t ih => exact fun n => ih n (h n)
  | builder t ih => exact h.mono fun n hn => ih _ hn

private theorem keepsUntil {A B : Type} (f : ℕ → ℕ) (P : A → Prop) (Q : B → Prop)
    (q : Script A) (stop : A → LabelledGame B) (resume : Script A → LabelledGame B)
    (hs : ∀ x, P x → Keeps f Q (stop x))
    (hr : ∀ t, Keep f P t → Keeps f Q (resume t)) (h : Keep f P q) :
    Keeps f Q (q.untilCut stop resume) := by
  induction q with
  | done x => exact hs x h
  | cut t => exact hr t h
  | architect t ih => exact fun n => ih n (h n)
  | builder t ih => exact h.mono fun n hn => ih _ hn

private def pairProperty {A B : Type} (P : A → Prop) (Q : B → Prop) :
    Option (A × B × Bool) → Prop
  | none => True
  | some (x,y,_) => P x ∧ Q y

private theorem keepsInterleave {A B : Type} (f : ℕ → ℕ) (P : A → Prop) (Q : B → Prop)
    (p : Script A) (q : Script B) (hp : Keep f P p) (hq : Keep f Q q) :
    Keeps f (pairProperty P Q) (p.interleave q) := by
  induction p generalizing q with
  | done x => exact keepsFinish _ _ _ _ _ _ trivial hq fun _ hy => ⟨hp,hy⟩
  | architect t ih => exact fun n => ih n q (hp n) hq
  | builder t ih => exact hp.mono fun n hn => ih _ q hn hq
  | cut t ih =>
    apply keepsUntil f Q _ q _ _ _ _ hq
    · intro y hy
      exact keepsFinish _ _ _ _ _ _ trivial hp fun _ hx => ⟨hx,hy⟩
    · exact fun r hr => ih r hp hr

private theorem keepsIncreasing {A : Type} (f : ℕ → ℕ) (P : Option A → Prop)
    (hb : P none) (t : LabelledGame (Option A)) (last : ℕ) (h : Keeps f P t) :
    Keeps f P (increasing t last) := by
  induction t generalizing last with
  | terminal => exact h
  | architect t ih => exact fun n => ih n last (h n)
  | builder t ih =>
    apply h.mono
    intro i hi
    change Keeps f P (if last < f i then _ else _)
    split
    · exact ih _ _ hi
    · exact hb

private theorem winningWitness {A : Type} (t : LabelledGame A) (f : ℕ → ℕ) (P Q : A → Prop)
    (h : (t.score P).outcome f true) (hq : Keeps f Q t) : ∃ a, P a ∧ Q a := by
  induction t with
  | terminal a => exact ⟨a,h,hq⟩
  | architect t ih =>
    obtain ⟨i,hi⟩ := h
    exact ih _ hi (hq i)
  | builder t ih =>
    obtain ⟨i,hi,qi⟩ := (h.and hq).exists
    exact ih _ hi qi

-- Every winning strategy gives a blue edge even if separate large
-- restrictions are imposed on its two endpoints.
theorem winningEdgeWithin (G : SimpleGraph Tree) (f : ℕ → ℕ) (inside : Bool)
    (win : (game.score (wins G inside)).outcome f true) (P Q : Tree → Prop)
    (hp : Force f P tree) (hq : Force f Q tree) :
    ∃ x y, P x ∧ Q y ∧ G.Adj x y := by
  have keep := keepsInterleave f P Q tree tree ((treeKeep _ _).mpr hp) ((treeKeep _ _).mpr hq)
  obtain ⟨r,hr,hs⟩ := winningWitness game f _ _ win
    (keepsIncreasing f _ trivial _ 0 keep)
  obtain _ | ⟨x,y,b⟩ := r
  · exact hr.elim
  · exact ⟨x,y,hs.1,hs.2,hr.1⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Filter Script

-- After its last marked leaf, a tree has only ordinary Builder labels left.
def Plain {A : Type} : Script A → Prop
  | .done _ => True
  | .builder t => ∀ n, Plain (t n)
  | .architect _ | .cut _ => False

private theorem plainNoCuts {A : Type} (p : Script A) (h : Plain p) : NoCuts p := by
  induction p with
  | done => trivial
  | cut | architect => exact h.elim
  | builder t ih => exact fun n => ih n (h n)

private theorem plainCompatible {A : Type} (p : Script A) (h : Plain p) (f : ℕ → ℕ) :
    Compatible (fun P => Force f P p) := by
  intro P R hp hr
  induction p with
  | done x => exact ⟨x,hp,hr⟩
  | cut | architect => exact h.elim
  | builder t ih =>
    obtain ⟨i,hi,ki⟩ := (hp.and hr).exists
    exact ih _ (h _) hi ki

-- In an inside game the second tree must finish first. If it asks to switch
-- while the first tree has no cuts left, all completions are outside.
private theorem insideReturn (G : SimpleGraph Tree) (p q : Script Tree) (hp : NoCuts p)
    (f : ℕ → ℕ) (last : ℕ)
    (h : ((increasing ((Script.cut p).interleave q) last).score (wins G true)).outcome f true) :
    Force f (fun y => Force f (fun x => G.Adj x y) p) q := by
  induction q generalizing last with
  | done y =>
    have ht := finishForce p _ (wins G true) (fun hn => hn) f last h
    have mono (s : Script Tree) (hs : Force f (fun x => wins G true (some (x,y,true))) s) :
        Force f (fun x => G.Adj x y) s := by
      induction s with
      | done => exact hs.1
      | cut s ih => exact ih hs
      | architect t ih =>
        obtain ⟨i,hi⟩ := hs
        exact ⟨i,ih i hi⟩
      | builder t ih => exact hs.mono fun i hi => ih _ hi
    exact mono p ht
  | cut q =>
    have bad := noCutsFirst p q hp (wins G true) (fun hn => hn) f last h
    obtain ⟨x,hx⟩ := forceWitness _ _ _ bad
    obtain ⟨y,hy⟩ := forceWitness _ _ _ hx
    exact Bool.noConfusion hy.2
  | architect t ih =>
    obtain ⟨i,hi⟩ := h
    exact ⟨i,ih _ _ hi⟩
  | builder t ih =>
    change ∀ᶠ i in atTop, ((if last < f i then increasing ((Script.cut p).interleave (t (f i))) (f i)
      else LabelledGame.terminal none).score (wins G true)).outcome f true at h
    filter_upwards [h] with i hi
    split at hi
    · exact ih _ _ hi
    · exact False.elim hi

-- This covers the inside configuration where the first cut of the first
-- tree leaves only an unmarked suffix, before the second tree has started.
theorem insideSingleCutTriangle (G : SimpleGraph Tree) (f : ℕ → ℕ)
    (win : (game.score (wins G true)).outcome f true) (p : Script Tree)
    (hp : Plain p) (last : ℕ)
    (h : ((increasing ((Script.cut p).interleave tree) last).score (wins G true)).outcome f true) :
    ∃ x y z, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z := by
  let good (y : Tree) := Force f (fun x => G.Adj x y) p
  have hg := insideReturn G p tree (plainNoCuts p hp) f last h
  obtain ⟨y,z,hy,hz,hyz⟩ := winningEdgeWithin G f true win good good hg hg
  obtain ⟨x,hxy,hxz⟩ := plainCompatible p hp f _ _ hy hz
  exact ⟨x,y,z,hxy,hxz,hyz⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

-- A concrete one-tree play records both branching decisions and the exact
-- Builder integers. This distinguishes two decorations of the same tree.
inductive Event
  | architect (n : ℕ)
  | builder (n : ℕ)
  | cut
deriving DecidableEq

inductive Reads {A : Type} : Script A → List Event → A → Prop
  | done (x : A) : Reads (.done x) [] x
  | architect {t : ℕ → Script A} {n s x} :
      Reads (t n) s x → Reads (.architect t) (.architect n :: s) x
  | builder {t : ℕ → Script A} {n s x} :
      Reads (t n) s x → Reads (.builder t) (.builder n :: s) x
  | cut {t : Script A} {s x} : Reads t s x → Reads (.cut t) (.cut :: s) x

private theorem readsBind {A B : Type} {p : Script A} {k : A → Script B} {s t x y}
    (hs : Reads p s x) (ht : Reads (k x) t y) : Reads (p.bind k) (s ++ t) y := by
  induction hs with
  | done => exact ht
  | architect _ ih => exact .architect (ih ht)
  | builder _ ih => exact .builder (ih ht)
  | cut _ ih => exact .cut (ih ht)

private theorem readsIndices (m : List ℕ) : Reads (Script.indices m.length)
    (m.map Event.builder) m := by
  induction m with
  | nil => exact .done []
  | cons i m ih =>
    apply Reads.builder
    simpa using readsBind (k := fun rest => Script.done (i :: rest)) ih (.done _)

private def makeTuple {A B : Type} (g : A → B) : (xs : List A) → Tuple B xs.length
  | [] => PUnit.unit
  | x :: xs => toLex (g x, makeTuple g xs)

private def indexedMoves {A : Type} (g : ℕ → A → List Event) :
    ℕ → List A → List Event
  | _, [] => []
  | i, x :: xs => g i x ++ indexedMoves g (i+1) xs

private def IndexedAll {A : Type} (P : ℕ → A → Prop) : ℕ → List A → Prop
  | _, [] => True
  | i, x :: xs => P i x ∧ IndexedAll P (i+1) xs

private theorem readsChildren {A B : Type} (child : ℕ → Script B) (g : A → B)
    (ev : ℕ → A → List Event) (xs : List A) (start : ℕ)
    (h : IndexedAll (fun i x => Reads (child i) (ev i x) (g x)) start xs) :
    Reads (Script.children child xs.length start) (indexedMoves ev start xs) (makeTuple g xs) := by
  induction xs generalizing start with
  | nil => exact .done _
  | cons x xs ih =>
    apply readsBind h.1
    have hr := readsBind (B := Tuple B (xs.length+1))
      (k := fun ys : Tuple B xs.length => Script.done (toLex (g x,ys)))
      (ih _ h.2) (.done _)
    rw [List.append_nil] at hr
    exact hr

structure MarkedBlock where
  leaves : List ℕ
  marked : List ℕ

def MarkedBlock.word (b : MarkedBlock) : Word ℕ := ⟨b.leaves.length, makeTuple id b.leaves⟩

private def leafMoves (marked : List ℕ) (i x : ℕ) : List Event :=
  .builder x :: (if i ∈ marked then [.cut] else [])

private theorem readsLeaf (marked : List ℕ) (i x : ℕ) :
    Reads (Script.leaf (decide (i ∈ marked))) (leafMoves marked i x) x := by
  by_cases hi : i ∈ marked
  · simpa [Script.leaf,leafMoves,hi] using
      (Reads.builder (Reads.cut (Reads.done x)) :
        Reads (.builder fun n => .cut (.done n)) [.builder x,.cut] x)
  · simpa [Script.leaf,leafMoves,hi] using
      (Reads.builder (Reads.done x) : Reads (.builder Script.done) [.builder x] x)

private def nodeMoves (m : List ℕ) (size : ℕ) (body : List Event) :=
  m.map Event.builder ++ .builder size :: body

private theorem readsNode {A B : Type} (child : Bool → Script B) (m : List ℕ)
    (g : A → B) (ev : ℕ → A → List Event) (xs : List A)
    (h : IndexedAll (fun i x => Reads (child (decide (i ∈ m))) (ev i x) (g x)) 1 xs) :
    Reads (Script.node m.length child) (nodeMoves m xs.length (indexedMoves ev 1 xs))
      ⟨xs.length,makeTuple g xs⟩ := by
  apply readsBind (readsIndices m)
  apply Reads.builder
  simpa using readsBind (k := fun t => Script.done (Word.mk xs.length t))
    (readsChildren _ g ev xs 1 h) (.done _)

private theorem indexedAllOfForall {A : Type} {P : ℕ → A → Prop} (h : ∀ i x, P i x)
    (xs : List A) (start : ℕ) : IndexedAll P start xs := by
  induction xs generalizing start with
  | nil => trivial
  | cons x xs ih => exact ⟨h _ _,ih _⟩

def MarkedBlock.moves (b : MarkedBlock) : List Event :=
  let body := nodeMoves b.marked b.leaves.length (indexedMoves (leafMoves b.marked) 1 b.leaves)
  if b.marked = [] then body else .architect (b.marked.length - 1) :: body

theorem MarkedBlock.reads (b : MarkedBlock) :
    Reads (Script.block (decide (b.marked ≠ []))) b.moves b.word := by
  have hb := readsNode Script.leaf b.marked id (leafMoves b.marked) b.leaves
    (indexedAllOfForall (readsLeaf b.marked) _ _)
  cases h : b.marked with
  | nil => simpa [Script.block, MarkedBlock.moves, MarkedBlock.word, h] using hb
  | cons i m =>
    simp only [h, List.cons_ne_nil, ne_eq, not_false_eq_true, decide_true, Script.block,
      if_true, MarkedBlock.moves, if_false, List.length_cons, Nat.add_one_sub_one]
    apply Reads.architect
    simpa [h,MarkedBlock.word] using hb

structure MarkedTree where
  blocks : List MarkedBlock
  marked : List ℕ

def MarkedTree.word (t : MarkedTree) : Tree := ⟨t.blocks.length,makeTuple MarkedBlock.word t.blocks⟩

def MarkedTree.moves (t : MarkedTree) : List Event :=
  .architect t.marked.length :: nodeMoves t.marked t.blocks.length
    (indexedMoves (fun _ b => b.moves) 1 t.blocks)

-- The projection of marked leaves to their block indices determines exactly
-- which blocks receive a branching move from the Architect.
def MarkedTree.consistent (t : MarkedTree) :=
  IndexedAll (fun i (b : MarkedBlock) => i ∈ t.marked ↔ b.marked ≠ []) 1 t.blocks

theorem MarkedTree.reads (t : MarkedTree) (h : t.consistent) :
    Reads Script.tree t.moves t.word := by
  apply Reads.architect
  apply readsNode
  have aux (xs : List MarkedBlock) (start : ℕ)
      (ht : IndexedAll (fun i (b : MarkedBlock) => i ∈ t.marked ↔ b.marked ≠ []) start xs) :
      IndexedAll (fun i (b : MarkedBlock) =>
        Reads (Script.block (decide (i ∈ t.marked))) b.moves b.word) start xs := by
    induction xs generalizing start with
    | nil => trivial
    | cons b xs ih =>
      refine ⟨?_,ih _ ht.2⟩
      simpa only [propext ht.1] using b.reads
  exact aux _ _ h

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

def Event.number : Event → Option ℕ
  | .builder n => some n
  | _ => none

private theorem numbersNode (m : List ℕ) (n : ℕ) (s : List Event) :
    (nodeMoves m n s).filterMap Event.number = m ++ n :: s.filterMap Event.number := by
  simp [nodeMoves, List.filterMap_map, Function.comp_def, Event.number]

private theorem numbersLeaves (m : List ℕ) (xs : List ℕ) (i : ℕ) :
    (indexedMoves (leafMoves m) i xs).filterMap Event.number = xs := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    by_cases hi : i ∈ m <;> simp [indexedMoves,leafMoves,hi,List.filterMap_cons,Event.number,ih]

def MarkedBlock.numbers (b : MarkedBlock) : List ℕ := b.marked ++ b.leaves.length :: b.leaves

theorem MarkedBlock.builderMoves (b : MarkedBlock) :
    b.moves.filterMap Event.number = b.numbers := by
  by_cases h : b.marked = [] <;>
    simp [MarkedBlock.moves, h, List.filterMap_cons, Event.number, MarkedBlock.numbers, numbersNode,numbersLeaves]

private theorem numbersBlocks (xs : List MarkedBlock) (i : ℕ) :
    (indexedMoves (fun _ b => b.moves) i xs).filterMap Event.number =
      xs.flatMap MarkedBlock.numbers := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => simp [indexedMoves,MarkedBlock.builderMoves,ih]

def MarkedTree.numbers (t : MarkedTree) :=
  t.marked ++ t.blocks.length :: t.blocks.flatMap MarkedBlock.numbers

theorem MarkedTree.builderMoves (t : MarkedTree) :
    t.moves.filterMap Event.number = t.numbers := by
  simp [MarkedTree.moves,List.filterMap_cons,Event.number,MarkedTree.numbers,numbersNode,numbersBlocks]

def activeBlocks : ℕ → List MarkedBlock → List ℕ
  | _, [] => []
  | i, b :: bs =>
    if b.marked = [] then activeBlocks (i+1) bs else i :: activeBlocks (i+1) bs

private theorem activeLower (i : ℕ) (bs : List MarkedBlock) :
    ∀ j ∈ activeBlocks i bs, i ≤ j := by
  induction bs generalizing i with
  | nil => simp [activeBlocks]
  | cons b bs ih =>
    intro j hj
    rw [activeBlocks] at hj
    split at hj
    · exact (Nat.le_succ _).trans (ih _ _ hj)
    · rcases List.mem_cons.mp hj with rfl | hj
      · rfl
      · exact (Nat.le_succ _).trans (ih _ _ hj)

private theorem indexedChange {A : Type} {P Q : ℕ → A → Prop} (xs : List A) (i : ℕ)
    (h : IndexedAll P i xs) (f : ∀ j ≥ i, ∀ x, P j x → Q j x) : IndexedAll Q i xs := by
  induction xs generalizing i with
  | nil => trivial
  | cons x xs ih =>
    exact ⟨f i le_rfl x h.1, ih _ h.2 fun j hij => f j ((Nat.le_succ i).trans hij)⟩

private theorem consistentActive (i : ℕ) (bs : List MarkedBlock) :
    IndexedAll (fun j (b : MarkedBlock) => j ∈ activeBlocks i bs ↔ b.marked ≠ []) i bs := by
  induction bs generalizing i with
  | nil => trivial
  | cons b bs ih =>
    have hn : i ∉ activeBlocks (i+1) bs := fun h => (Nat.not_succ_le_self i) (activeLower _ _ _ h)
    by_cases he : b.marked = []
    · simp only [activeBlocks, if_pos he, IndexedAll]
      exact ⟨by simp [hn,he],ih _⟩
    · simp only [activeBlocks, if_neg he, IndexedAll]
      refine ⟨by simp [he],indexedChange _ _ (ih _) ?_⟩
      intro j hj x hx
      simpa [Nat.ne_of_gt hj] using hx

def decorate (bs : List MarkedBlock) : MarkedTree := ⟨bs,activeBlocks 1 bs⟩

theorem readsDecoration (bs : List MarkedBlock) :
    Reads Script.tree (decorate bs).moves (decorate bs).word :=
  (decorate bs).reads (consistentActive 1 bs)

def pruneBlocks (keep : ℕ → ℕ → Bool) : ℕ → List MarkedBlock → List MarkedBlock
  | _, [] => []
  | i, b :: bs => {b with marked := b.marked.filter (keep i)} :: pruneBlocks keep (i+1) bs

private theorem pruneActive (keep : ℕ → ℕ → Bool) (i : ℕ) (bs : List MarkedBlock) :
    (activeBlocks i (pruneBlocks keep i bs)).Sublist (activeBlocks i bs) := by
  induction bs generalizing i with
  | nil => exact .refl _
  | cons b bs ih =>
    simp only [pruneBlocks, activeBlocks]
    by_cases he : b.marked = []
    · simpa [he] using ih (i+1)
    · rw [if_neg he]
      split
      · exact (ih _).cons _
      · exact (ih _).cons_cons _

private theorem pruneBlockNumbers (keep : ℕ → ℕ → Bool) (i : ℕ) (bs : List MarkedBlock) :
    ((pruneBlocks keep i bs).flatMap MarkedBlock.numbers).Sublist
      (bs.flatMap MarkedBlock.numbers) := by
  induction bs generalizing i with
  | nil => exact .refl _
  | cons b bs ih =>
    exact ((List.filter_sublist (p := keep i) (l := b.marked)).append_right _).append (ih _)

private theorem pruneLength (keep : ℕ → ℕ → Bool) (i : ℕ) (bs : List MarkedBlock) :
    (pruneBlocks keep i bs).length = bs.length := by
  induction bs generalizing i with
  | nil => rfl
  | cons b bs ih => simp [pruneBlocks, ih]

private theorem pruneWord (keep : ℕ → ℕ → Bool) (i : ℕ) (bs : List MarkedBlock) :
    (decorate (pruneBlocks keep i bs)).word = (decorate bs).word := by
  induction bs generalizing i with
  | nil => rfl
  | cons b bs ih =>
    let add (w : Tree) : Tree := ⟨w.len+1,toLex (b.word,w.letters)⟩
    exact congrArg add (ih (i+1))

-- Dropping any collection of marked leaves deletes Builder moves and keeps
-- the completed tree. Each surviving marked block still has a legal positive
-- branching move, even when pruning has removed every mark in other blocks.
theorem coarsenDecoration (bs : List MarkedBlock) (keep : ℕ → ℕ → Bool) :
    let coarse := decorate (pruneBlocks keep 1 bs)
    let full := decorate bs
    Reads Script.tree coarse.moves full.word ∧
      (coarse.moves.filterMap Event.number).Sublist (full.moves.filterMap Event.number) := by
  dsimp only
  constructor
  · rw [← pruneWord keep 1 bs]
    exact readsDecoration _
  · rw [MarkedTree.builderMoves,MarkedTree.builderMoves]
    simp only [MarkedTree.numbers,decorate,pruneLength]
    exact (pruneActive _ _ _).append ((pruneBlockNumbers _ _ _).cons_cons _)

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

-- The Boolean at the left of Weave is the currently active tree (true for
-- the first). Its final Boolean gives the inside/outside classification.
inductive Weave : Bool → List Event → List Event → List Event → Bool → Prop
  | finishLeft {s} : Event.cut ∉ s → Weave true [] s s false
  | finishRight {s} : Event.cut ∉ s → Weave false s [] s true
  | leftMove {e s t u b} : e ≠ .cut → Weave true s t u b →
      Weave true (e :: s) t (e :: u) b
  | rightMove {e s t u b} : e ≠ .cut → Weave false s t u b →
      Weave false s (e :: t) (e :: u) b
  | leftCut {s t u b} : Weave false s t u b → Weave true (.cut :: s) t u b
  | rightCut {s t u b} : Weave true s t u b → Weave false s (.cut :: t) u b

inductive Follows {A : Type} : LabelledGame A → List Event → A → Prop
  | done (a : A) : Follows (.terminal a) [] a
  | architect {t : ℕ → LabelledGame A} {n s a} :
      Follows (t n) s a → Follows (.architect t) (.architect n :: s) a
  | builder {t : ℕ → LabelledGame A} {n s a} :
      Follows (t n) s a → Follows (.builder t) (.builder n :: s) a

private theorem followsFinish {A B : Type} {p : Script A} {s x} (h : Reads p s x)
    (k : A → B) (bad : B) (hn : Event.cut ∉ s) : Follows (p.finish k bad) s (k x) := by
  induction h with
  | done => exact .done _
  | architect h ih => exact .architect (ih (fun hm => hn (List.mem_cons_of_mem _ hm)))
  | builder h ih => exact .builder (ih (fun hm => hn (List.mem_cons_of_mem _ hm)))
  | cut => exact (hn List.mem_cons_self).elim

private def turn {A B : Type} (first : Bool) (p : Script A) (q : Script B) :=
  if first then p.interleave q else
    q.untilCut (fun y => p.finish (fun x => some (x,y,true)) none)
      (fun next => p.interleave next)

private theorem followsWeave {A B : Type} {first b : Bool} {s t u : List Event}
    (hw : Weave first s t u b) {p : Script A} {q : Script B} {x y}
    (hp : Reads p s x) (hq : Reads q t y) :
    Follows (turn first p q) u (some (x,y,b)) := by
  induction hw generalizing p q with
  | finishLeft hn => cases hp; exact followsFinish hq _ _ hn
  | finishRight hn => cases hq; exact followsFinish hp _ _ hn
  | leftMove he _ ih =>
    cases hp with
    | architect ht => exact .architect (ih ht hq)
    | builder ht => exact .builder (ih ht hq)
    | cut => exact (he rfl).elim
  | rightMove he _ ih =>
    cases hq with
    | architect ht => exact .architect (ih hp ht)
    | builder ht => exact .builder (ih hp ht)
    | cut => exact (he rfl).elim
  | leftCut _ ih => cases hp with | cut ht => exact ih ht hq
  | rightCut _ ih => cases hq with | cut ht => exact ih hp ht

private theorem followsIncreasing {A : Type} {p : LabelledGame (Option A)} {s a}
    (h : Follows p s a) (last : ℕ) (hs : (last :: s.filterMap Event.number).Pairwise (· < ·)) :
    Follows (increasing p last) s a := by
  induction h generalizing last with
  | done => exact .done _
  | architect ht ih => exact .architect (ih last hs)
  | @builder t n s a ht ih =>
    have hp : (last :: n :: s.filterMap Event.number).Pairwise (· < ·) := hs
    have hl := (List.pairwise_cons.mp hp).1 n List.mem_cons_self
    apply Follows.builder
    simpa [hl] using ih n (List.pairwise_cons.mp hp).2

-- These conditions suffice for a pair of decorated trees to be an actual
-- legal play, with exactly the specified sequence of Architect and Builder moves.
theorem followsGame (t u : MarkedTree) (ht : t.consistent) (hu : u.consistent)
    (s : List Event) (b : Bool) (hw : Weave true t.moves u.moves s b)
    (hs : (0 :: s.filterMap Event.number).Pairwise (· < ·)) :
    Follows game s (some (t.word,u.word,b)) :=
  followsIncreasing (followsWeave hw (t.reads ht) (u.reads hu)) 0 hs

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

private def Event.value : Event → ℕ
  | .architect n | .builder n => n
  | .cut => 0

-- The cutoff is indexed by the moves in the actual two-tree play. A
-- coarsening changes this history, so timeliness is checked after weaving.
def Timely (f : ℕ → ℕ) (cutoff : List ℕ → ℕ) (past : List ℕ) : List Event → Prop
  | [] => True
  | .architect n :: s => Timely f cutoff (past ++ [n]) s
  | .builder n :: s =>
      (∃ k ≥ cutoff past, f k = n) ∧ Timely f cutoff (past ++ [n]) s
  | .cut :: _ => False

def Prescribed (action : List ℕ → ℕ) (past : List ℕ) : List Event → Prop
  | [] => True
  | .architect n :: s => n = action past ∧ Prescribed action (past ++ [n]) s
  | .builder n :: s => Prescribed action (past ++ [n]) s
  | .cut :: _ => False

private theorem timelyPlay {A : Type} (P : A → Prop) (root : PairGame)
    (f : ℕ → ℕ) (win : Bool) (policy : PairGame.Policy) {p : LabelledGame A} {s a}
    (w : Follows p s a) (past : List ℕ) (ht : Timely f policy.cutoff past s)
    (ha : win = true → Prescribed policy.action past s)
    (he : root.position past = p.score P) :
    root.Plays f win policy past (s.map Event.value) ∧
      root.position (past ++ s.map Event.value) = .terminal (P a) := by
  induction w generalizing past with
  | done => exact ⟨trivial,by simpa [LabelledGame.score] using he⟩
  | @architect t n s a hw ih =>
    have hn : root.position (past ++ [n]) = (t n).score P := by
      rw [PairGame.position_append,he]
      rfl
    obtain ⟨hm,he'⟩ := ih _ ht (fun hw => (ha hw).2) hn
    refine ⟨⟨?_,hm⟩,?_⟩
    · rw [he]
      exact fun hw => (ha hw).1
    · simpa [Event.value] using he'
  | @builder t n s a hw ih =>
    have hn : root.position (past ++ [n]) = (t n).score P := by
      rw [PairGame.position_append,he]
      rfl
    obtain ⟨hm,he'⟩ := ih _ ht.2 ha hn
    refine ⟨⟨?_,hm⟩,?_⟩
    · rw [he]
      exact ht.1
    · simpa [Event.value] using he'

theorem builderNonedges (G : SimpleGraph Tree) (f : ℕ → ℕ)
    (lose : (game.score (fun x => ∃ b, wins G b x)).outcome f false) :
    ∃ cutoff : List ℕ → ℕ, ∀ (t u : MarkedTree) (s : List Event) (b : Bool),
      t.consistent → u.consistent → Weave true t.moves u.moves s b →
      (0 :: s.filterMap Event.number).Pairwise (· < ·) →
      Timely f cutoff [] s → ¬ G.Adj t.word u.word := by
  let P (x : Option (Tree × Tree × Bool)) := ∃ b, wins G b x
  let root := game.score P
  obtain ⟨policy,hp⟩ := PairGame.policyOfOutcome root f false lose
  refine ⟨policy.cutoff,?_⟩
  intro t u s b ht hu hw hs htime edge
  have h := followsGame t u ht hu s b hw hs
  obtain ⟨legal,terminal⟩ := timelyPlay P root f false policy h [] htime
    (fun hw => Bool.noConfusion hw) rfl
  have hv := hp _ legal
  simp only [List.nil_append] at terminal
  rw [terminal] at hv
  exact hv ⟨b,edge,rfl⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

private def histories (cap : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | l+1 => insert [] (((Finset.range (cap+1)) ×ˢ histories cap l).image fun p => p.1 :: p.2)

private theorem historyMem (cap l : ℕ) (p : List ℕ) (hl : p.length ≤ l)
    (hb : ∀ x ∈ p, x ≤ cap) : p ∈ histories cap l := by
  induction l generalizing p with
  | zero =>
    have he : p = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
    simp [he,histories]
  | succ l ih =>
    cases p with
    | nil => simp [histories]
    | cons x xs =>
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨(x,xs),Finset.mem_product.mpr ⟨?_,?_⟩,rfl⟩
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hb x List.mem_cons_self))
      · exact ih _ (Nat.le_of_succ_le_succ hl) (fun j hj => hb j (List.mem_cons_of_mem _ hj))

-- Sufficiently late is uniform over all subplays of bounded length using
-- bounded moves. Both bounds include the Architect's branching choices.
theorem thinCutoffs (cutoff : List ℕ → ℕ) :
    ∃ h : ℕ → ℕ, StrictMono h ∧ ∀ k (p : List ℕ), p.length ≤ k →
      (∀ x ∈ p, x ≤ k) → cutoff p ≤ h k := by
  let M (k : ℕ) := (histories k k).sup cutoff
  let h : ℕ → ℕ := Nat.rec (M 0) fun k v => max (v+1) (M (k+1))
  have hm (k : ℕ) : M k ≤ h k := by
    cases k with
    | zero => exact le_rfl
    | succ k => exact le_max_right _ _
  refine ⟨h,strictMono_nat_of_lt_succ (fun k => (Nat.lt_succ_self _).trans_le (le_max_left _ _)),?_⟩
  intro k p hl hb
  exact (Finset.le_sup (historyMem k k p hl hb)).trans (hm k)

def Spaced (g : ℕ → ℕ) (past : List ℕ) : List Event → Prop
  | [] => True
  | .architect n :: s => Spaced g (past ++ [n]) s
  | .builder n :: s =>
      (∃ k, past.length ≤ k ∧ (∀ x ∈ past, x ≤ k) ∧ g k = n) ∧
        Spaced g (past ++ [n]) s
  | .cut :: _ => False

private theorem spacedTimely {h : ℕ → ℕ} {cutoff : List ℕ → ℕ}
    (hc : ∀ k (p : List ℕ), p.length ≤ k → (∀ x ∈ p, x ≤ k) → cutoff p ≤ h k)
    (f : ℕ → ℕ) (s : List Event) (p : List ℕ) (hs : Spaced (f ∘ h) p s) :
    Timely f cutoff p s := by
  induction s generalizing p with
  | nil => trivial
  | cons e s ih =>
    cases e with
    | cut => exact hs
    | architect n => exact ih _ hs
    | builder n =>
      obtain ⟨⟨k,hl,hb,he⟩,hr⟩ := hs
      exact ⟨⟨h k,hc k p hl hb,he⟩,ih _ hr⟩

theorem spacedBuilderNonedges (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (lose : (game.score (fun x => ∃ b, wins G b x)).outcome f false) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ Set.range g ⊆ Set.range f ∧
      ∀ (t u : MarkedTree) (s : List Event) (b : Bool),
        t.consistent → u.consistent → Weave true t.moves u.moves s b →
        (0 :: s.filterMap Event.number).Pairwise (· < ·) →
        Spaced g [] s → ¬ G.Adj t.word u.word := by
  obtain ⟨c,hc⟩ := builderNonedges G f lose
  obtain ⟨h,hh,hbound⟩ := thinCutoffs c
  refine ⟨f ∘ h,hf.comp hh,?_,?_⟩
  · rintro _ ⟨i,rfl⟩
    exact ⟨h i,rfl⟩
  · intro t u s b ht hu hw hs hspace
    exact hc t u s b ht hu hw hs (spacedTimely hbound f s [] hspace)

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Ordinal Set Script

-- A property of the numerical tree construction alone: after projection to
-- any two unequal levels, their retained decorations describe a spaced play.
def SpacedFamily (g : ℕ → ℕ) :=
  ∃ X : Set Tree, typeLT X = (ω : Ordinal.{0}) ^ ω ^ 2 ∧
    ∀ x ∈ X, ∀ y ∈ X, x.len < y.len →
      ∃ (t u : MarkedTree) (s : List Event) (b : Bool),
        t.word = x ∧ u.word = y ∧ t.consistent ∧ u.consistent ∧
        Weave true t.moves u.moves s b ∧ (0 :: s.filterMap Event.number).Pairwise (· < ·) ∧
        Spaced g [] s

theorem builderCopyOfSpacedFamily (G : SimpleGraph Tree)
    (lev : ∀ x y : Tree, x.len = y.len → ¬ G.Adj x y)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (lose : (game.score (fun x => ∃ b, wins G b x)).outcome f false)
    (families : ∀ g : ℕ → ℕ, StrictMono g → SpacedFamily g) : IndependentCopy G := by
  obtain ⟨g,hg,_,hn⟩ := spacedBuilderNonedges G f hf lose
  obtain ⟨X,hX,hpair⟩ := families g hg
  have ordered (x y : X) (hlt : x.val.len < y.val.len) : ¬ G.Adj x.val y.val := by
    obtain ⟨t,u,s,b,hx,hy,ht,hu,hw,hs,hspace⟩ := hpair _ x.property _ y.property hlt
    rw [← hx,← hy]
    exact hn _ _ _ _ ht hu hw hs hspace
  obtain ⟨e,he⟩ := fit (heightTwoOrderType.trans hX.symm).le
  refine ⟨fun x => (e x).val,fun _ _ h => he h,?_⟩
  intro x y
  rcases lt_trichotomy (e x).val.len (e y).val.len with hl | hl | hl
  · exact ordered _ _ hl
  · exact lev _ _ hl
  · exact fun edge => ordered _ _ hl edge.symm

universe v

theorem ramseyOfConstructions
    (families : ∀ g : ℕ → ℕ, StrictMono g → SpacedFamily g)
    (triangle : ∀ (G : SimpleGraph Tree) (f : ℕ → ℕ), StrictMono f →
      ∀ (d : ℕ) (b : Bool),
      ((increasing ((node (d+1) block).interleave tree) 0).score (wins G b)).outcome f true →
        ∃ x y z, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z) :
    OrdinalCardinalRamsey ((ω : Ordinal.{v}) ^ ω ^ 2) (ω ^ ω ^ 2) 3 := by
  apply ordinalRamseyOfLevelGraphs
  intro G hg lev
  obtain h | ⟨f,hf,hw⟩ := openingCases G hg
  · exact h
  rcases hw with ⟨d,b,hd⟩ | h
  · obtain ⟨x,y,z,hxy,hxz,hyz⟩ := triangle G f hf d b hd
    exact (hg {x,y,z} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy,hxz,hyz⟩)).elim
  · exact builderCopyOfSpacedFamily G lev f hf h families

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

-- One bound controls both the number of moves played and their maximum.
-- Cuts are bookkeeping events and do not consume an integer.
def advance (bound n : ℕ) := max (bound+1) n

def Room (g : ℕ → ℕ) (bound : ℕ) : List Event → Prop
  | [] => True
  | .cut :: s => Room g bound s
  | .architect n :: s => Room g (advance bound n) s
  | .builder n :: s => (∃ k ≥ bound, g k = n) ∧ Room g (advance bound n) s

private theorem roomMono {g : ℕ → ℕ} (s : List Event) {a b : ℕ} (hab : a ≤ b)
    (h : Room g b s) : Room g a s := by
  induction s generalizing a b with
  | nil => trivial
  | cons e s ih =>
    cases e with
    | cut => exact ih hab h
    | architect n => exact ih (max_le_max (Nat.succ_le_succ hab) le_rfl) h
    | builder n =>
      obtain ⟨⟨k,hk,he⟩,hr⟩ := h
      exact ⟨⟨k,hab.trans hk,he⟩,ih (max_le_max (Nat.succ_le_succ hab) le_rfl) hr⟩

inductive Shrinks : List Event → List Event → Prop
  | nil : Shrinks [] []
  | skip {s t} (e) : Shrinks s t → Shrinks s (e :: t)
  | cut {s t} : Shrinks s t → Shrinks (.cut :: s) (.cut :: t)
  | builder {s t} (n) : Shrinks s t → Shrinks (.builder n :: s) (.builder n :: t)
  | architect {s t a b} : a ≤ b → Shrinks s t →
      Shrinks (.architect a :: s) (.architect b :: t)

theorem Shrinks.room {g : ℕ → ℕ} {s t : List Event} (h : Shrinks s t) (n : ℕ)
    (ht : Room g n t) : Room g n s := by
  induction h generalizing n with
  | nil => trivial
  | skip e _ ih =>
    cases e with
    | cut => exact ih n ht
    | architect k => exact roomMono _ ((Nat.le_succ _).trans (le_max_left _ _)) (ih _ ht)
    | builder k => exact roomMono _ ((Nat.le_succ _).trans (le_max_left _ _)) (ih _ ht.2)
  | cut _ ih => exact ih n ht
  | builder k _ ih => exact ⟨ht.1,ih _ ht.2⟩
  | @architect s t a b hab _ ih =>
    change Room g (advance n a) s
    exact roomMono s (max_le_max (le_refl (n+1)) hab) (ih (advance n b) ht)

theorem spacedOfRoom {g : ℕ → ℕ} (s : List Event) (p : List ℕ) (n : ℕ)
    (hr : Room g n s) (hn : Event.cut ∉ s) (hl : p.length ≤ n) (hb : ∀ j ∈ p, j ≤ n) :
    Spaced g p s := by
  induction s generalizing p n with
  | nil => trivial
  | cons e s ih =>
    have tail := fun (h : Event.cut ∈ s) => hn (List.mem_cons_of_mem e h)
    have next (v : ℕ) : (p ++ [v]).length ≤ advance n v ∧
        ∀ j ∈ p ++ [v], j ≤ advance n v := by
      refine ⟨by simpa only [List.length_append,List.length_singleton,advance] using
        (Nat.succ_le_succ hl).trans (le_max_left (n+1) v),?_⟩
      intro j hj
      rcases List.mem_append.mp hj with hj | hj
      · exact (hb j hj).trans ((Nat.le_succ _).trans (le_max_left _ _))
      · rw [List.mem_singleton.mp hj]
        exact le_max_right _ _
    cases e with
    | cut => exact (hn List.mem_cons_self).elim
    | architect v => exact ih _ _ hr tail (next v).1 (next v).2
    | builder v =>
      obtain ⟨⟨k,hk,he⟩,ht⟩ := hr
      exact ⟨⟨k,hl.trans hk,fun j hj => (hb j hj).trans hk,he⟩,
        ih _ _ ht tail (next v).1 (next v).2⟩

-- Construct a single cell of a partial tree. Branching choices are assigned
-- the requested stage rank. A new Builder integer is drawn above every
-- preceding move and above the rank, including at unmarked filler nodes.
structure Batch (A : Type) where
  events : List Event
  bound : ℕ
  result : Sum A (Script A)

def nextBatch {A : Type} (g : ℕ → ℕ) (rank : ℕ) (p : Script A) (n : ℕ) : Batch A :=
  match p with
  | .done x => ⟨[],n,.inl x⟩
  | .cut t => ⟨[.cut],n,.inr t⟩
  | .architect t =>
    let b := nextBatch g rank (t rank) (advance n rank)
    {b with events := .architect rank :: b.events}
  | .builder t =>
    let v := g (n+1)
    let b := nextBatch g rank (t v) (advance n v)
    {b with events := .builder v :: b.events}

theorem nextBatchRoom {A : Type} (g : ℕ → ℕ) (rank : ℕ) (p : Script A) (n : ℕ)
    (s : List Event) (hr : Room g (nextBatch g rank p n).bound s) :
    Room g n ((nextBatch g rank p n).events ++ s) := by
  induction p generalizing n with
  | done | cut => exact hr
  | architect t ih => exact ih _ _ hr
  | builder t ih => exact ⟨⟨n+1,Nat.le_succ _,rfl⟩,ih _ _ hr⟩

theorem nextBatchReads {A : Type} (g : ℕ → ℕ) (rank : ℕ) (p : Script A) (n : ℕ)
    (s : List Event) (x : A)
    (h : match (nextBatch g rank p n).result with
      | .inl y => s = [] ∧ y = x
      | .inr t => Reads t s x) :
    Reads p ((nextBatch g rank p n).events ++ s) x := by
  induction p generalizing n with
  | done y =>
    obtain ⟨rfl,rfl⟩ := h
    exact .done _
  | cut t => exact .cut h
  | architect t ih => exact .architect (ih _ _ h)
  | builder t ih => exact .builder (ih _ _ h)

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

private theorem Shrinks.refl (s : List Event) : Shrinks s s := by
  induction s with
  | nil => exact .nil
  | cons e s ih =>
    cases e with
    | architect n => exact .architect le_rfl ih
    | builder n => exact .builder n ih
    | cut => exact .cut ih

private theorem Shrinks.append {s t u v : List Event} (h : Shrinks s t) (k : Shrinks u v) :
    Shrinks (s ++ u) (t ++ v) := by
  induction h with
  | nil => exact k
  | skip e _ ih => exact .skip e ih
  | cut _ ih => exact .cut ih
  | builder n _ ih => exact .builder n ih
  | architect hab _ ih => exact .architect hab ih

private theorem shrinksIndices {m n : List ℕ} (h : m.Sublist n) :
    Shrinks (m.map Event.builder) (n.map Event.builder) := by
  induction h with
  | slnil => exact .nil
  | cons i _ ih => exact .skip (.builder i) ih
  | cons_cons i _ ih => exact .builder i ih

private theorem shrinksNode {m n : List ℕ} (h : m.Sublist n) (len : ℕ)
    {xs ys : List Event} (hs : Shrinks xs ys) :
    Shrinks (nodeMoves m len xs) (nodeMoves n len ys) :=
  (shrinksIndices h).append (.builder len hs)

private theorem shrinksLeaves {m n : List ℕ} (h : m.Sublist n) (start : ℕ) (xs : List ℕ) :
    Shrinks (indexedMoves (leafMoves m) start xs) (indexedMoves (leafMoves n) start xs) := by
  induction xs generalizing start with
  | nil => exact .nil
  | cons x xs ih =>
    apply Shrinks.append _ (ih _)
    by_cases hm : start ∈ m
    · simp only [leafMoves,if_pos hm,if_pos (h.subset hm)]
      exact .refl _
    · by_cases hn : start ∈ n
      · simp only [leafMoves,if_neg hm,if_pos hn]
        exact .builder _ (.skip .cut .nil)
      · simp only [leafMoves,if_neg hm,if_neg hn]
        exact .refl _

private theorem shrinksBlock (b : MarkedBlock) (f : ℕ → Bool) :
    Shrinks ({b with marked := b.marked.filter f} : MarkedBlock).moves b.moves := by
  have hf : (b.marked.filter f).Sublist b.marked := List.filter_sublist
  have hs := shrinksNode hf b.leaves.length (shrinksLeaves hf 1 b.leaves)
  by_cases he : b.marked = []
  · simp [MarkedBlock.moves,he] at hs ⊢
    exact hs
  · by_cases hc : b.marked.filter f = []
    · simp only [MarkedBlock.moves,if_pos hc,if_neg he]
      exact .skip _ hs
    · simp only [MarkedBlock.moves,if_neg hc,if_neg he]
      exact .architect (Nat.sub_le_sub_right hf.length_le _) hs

private theorem shrinksBlocks (keep : ℕ → ℕ → Bool) (i j : ℕ) (bs : List MarkedBlock) :
    Shrinks (indexedMoves (fun _ b => b.moves) j (pruneBlocks keep i bs))
      (indexedMoves (fun _ b => b.moves) j bs) := by
  induction bs generalizing i j with
  | nil => exact .nil
  | cons b bs ih => exact (shrinksBlock b (keep i)).append (ih _ _)

theorem coarsenMoves (bs : List MarkedBlock) (keep : ℕ → ℕ → Bool) :
    Shrinks (decorate (pruneBlocks keep 1 bs)).moves (decorate bs).moves := by
  have hm := pruneActive keep 1 bs
  simp only [MarkedTree.moves,decorate,pruneLength]
  exact .architect hm.length_le (shrinksNode hm _ (shrinksBlocks keep 1 1 bs))

theorem coarsenRoom {g : ℕ → ℕ} (bs : List MarkedBlock) (keep : ℕ → ℕ → Bool)
    (n : ℕ) (h : Room g n (decorate bs).moves) :
    Room g n (decorate (pruneBlocks keep 1 bs)).moves :=
  (coarsenMoves bs keep).room n h

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

-- Slot zero is the root. At time t the table creates slot t+1, extending
-- the slot with index (Nat.unpair t).1. Old slots stay available for reuse.
structure StageTable (A : Type) where
  slot : ℕ → Sum A (Script A)
  bound : ℕ

def StageTable.batch {A : Type} (g : ℕ → ℕ) (T : StageTable A) (t : ℕ) : Batch A :=
  match T.slot (Nat.unpair t).1 with
  | .inl x => ⟨[], T.bound + 1, .inl x⟩
  | .inr p => nextBatch g (T.bound + 1) p (T.bound + 1)

def stageTable {A : Type} (g : ℕ → ℕ) (root : Script A) : ℕ → StageTable A
  | 0 => ⟨fun _ => .inr root, 0⟩
  | t+1 =>
    let T := stageTable g root t
    let b := T.batch g t
    ⟨Function.update T.slot (t+1) b.result, b.bound⟩

def stageBatch {A : Type} (g : ℕ → ℕ) (root : Script A) (t : ℕ) :=
  (stageTable g root t).batch g t

private theorem stableSlot {A : Type} (g : ℕ → ℕ) (root : Script A) {i t : ℕ} (h : i ≤ t) :
    (stageTable g root t).slot i = (stageTable g root i).slot i := by
  induction h with
  | refl => rfl
  | step h ih =>
    simpa only [stageTable, Function.update_of_ne (Nat.ne_of_lt (Nat.lt_succ_of_le h))] using ih

private theorem newSlot {A : Type} (g : ℕ → ℕ) (root : Script A) (t : ℕ) :
    (stageTable g root (t+1)).slot (t+1) = (stageBatch g root t).result := by
  simp [stageTable, stageBatch]

theorem stageBatchAtPair {A : Type} (g : ℕ → ℕ) (root : Script A) (i k : ℕ)
    (p : Script A) (hp : (stageTable g root i).slot i = .inr p) :
    let t := Nat.pair i k
    let rank := (stageTable g root t).bound + 1
    stageBatch g root t = nextBatch g rank p rank := by
  simp [stageBatch, StageTable.batch, stableSlot g root (Nat.left_le_pair i k), hp]

private theorem nextBound {A : Type} (g : ℕ → ℕ) (r : ℕ) (p : Script A) (n : ℕ) :
    n ≤ (nextBatch g r p n).bound := by
  induction p generalizing n with
  | done | cut => exact le_rfl
  | architect t ih => exact ((Nat.le_succ n).trans (le_max_left _ _)).trans (ih _ _)
  | builder t ih => exact ((Nat.le_succ n).trans (le_max_left _ _)).trans (ih _ _)

theorem stageBoundMono {A : Type} (g : ℕ → ℕ) (root : Script A) :
    StrictMono (fun t => (stageTable g root t).bound) := by
  apply strictMono_nat_of_lt_succ
  intro t
  change (stageTable g root t).bound < ((stageTable g root t).batch g t).bound
  unfold StageTable.batch
  split
  · exact Nat.lt_succ_self _
  · exact nextBound _ _ _ _

theorem arbitrarilyLateChild {A : Type} (g : ℕ → ℕ) (root : Script A) (i k : ℕ)
    (p : Script A) (hp : (stageTable g root i).slot i = .inr p) :
    ∃ t ≥ k, (Nat.unpair t).1 = i ∧ k < (stageTable g root t).bound + 1 ∧
      stageBatch g root t = nextBatch g ((stageTable g root t).bound + 1) p
        ((stageTable g root t).bound + 1) := by
  let t := Nat.pair i k
  have h : k ≤ t := by simpa [t] using Nat.unpair_right_le (Nat.pair i k)
  exact ⟨t, h, by simp [t], Nat.lt_succ_of_le (h.trans ((stageBoundMono g root).id_le t)),
    stageBatchAtPair g root i k p hp⟩

-- A stage interval controls the whole play, including moves of the other
-- tree between two visits to this one.
private theorem batchIncreasing {A : Type} (g : ℕ → ℕ) (hg : StrictMono g)
    (r : ℕ) (p : Script A) (n : ℕ) (tail : List ℕ)
    (ht : ((nextBatch g r p n).bound :: tail).Pairwise (· < ·)) :
    (n :: ((nextBatch g r p n).events.filterMap Event.number ++ tail)).Pairwise (· < ·) := by
  have weaken {a b : ℕ} {l : List ℕ} (hab : a ≤ b)
      (hl : (b :: l).Pairwise (· < ·)) : (a :: l).Pairwise (· < ·) :=
    List.pairwise_cons.mpr ⟨fun x hx => hab.trans_lt ((List.pairwise_cons.mp hl).1 x hx),
      (List.pairwise_cons.mp hl).2⟩
  induction p generalizing n with
  | done | cut => exact ht
  | architect t ih =>
    exact weaken ((Nat.le_succ n).trans (le_max_left _ _)) (ih _ _ ht)
  | builder t ih =>
    let x := g (n+1)
    have hx : n < x := hg.id_le (n+1)
    have hl := weaken (le_max_right (n+1) x) (ih x (advance n x) ht)
    exact List.pairwise_cons.mpr ⟨fun j hj => by
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hx
      · exact hx.trans ((List.pairwise_cons.mp hl).1 j hj), hl⟩

def stageTrace {A : Type} (g : ℕ → ℕ) (root : Script A) : ℕ → List Event
  | 0 => []
  | t+1 => stageTrace g root t ++ (stageBatch g root t).events

theorem stageTraceRoom {A : Type} (g : ℕ → ℕ) (root : Script A) (t : ℕ)
    (s : List Event) (h : Room g (stageTable g root t).bound s) :
    Room g 0 (stageTrace g root t ++ s) := by
  induction t generalizing s with
  | zero => exact h
  | succ t ih =>
    rw [stageTrace,List.append_assoc]
    apply ih
    change Room g (stageTable g root t).bound (((stageTable g root t).batch g t).events ++ s)
    change Room g ((stageTable g root t).batch g t).bound s at h
    unfold StageTable.batch at *
    split at h <;> rename_i he
    · exact roomMono _ (Nat.le_succ _) h
    · exact roomMono _ (Nat.le_succ _) (nextBatchRoom _ _ _ _ _ h)

theorem stageTraceIncreasing {A : Type} (g : ℕ → ℕ) (hg : StrictMono g)
    (root : Script A) (t : ℕ) (s : List ℕ)
    (h : ((stageTable g root t).bound :: s).Pairwise (· < ·)) :
    (0 :: ((stageTrace g root t).filterMap Event.number ++ s)).Pairwise (· < ·) := by
  induction t generalizing s with
  | zero => exact h
  | succ t ih =>
    rw [stageTrace,List.filterMap_append,List.append_assoc]
    apply ih
    have weaken {n : ℕ} {l : List ℕ} (h : ((n+1) :: l).Pairwise (· < ·)) :
        (n :: l).Pairwise (· < ·) :=
      List.pairwise_cons.mpr ⟨fun _ hx => (Nat.le_succ _).trans_lt
        ((List.pairwise_cons.mp h).1 _ hx), (List.pairwise_cons.mp h).2⟩
    apply weaken
    change (((stageTable g root t).bound + 1) ::
      (((stageTable g root t).batch g t).events.filterMap Event.number ++ s)).Pairwise (· < ·)
    change (((stageTable g root t).batch g t).bound :: s).Pairwise (· < ·) at h
    unfold StageTable.batch at *
    split at h <;> rename_i he
    · exact h
    · exact batchIncreasing g hg _ _ _ _ h

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

def branchTrace {A : Type} (g : ℕ → ℕ) (root : Script A) : ℕ → List Event
  | 0 => []
  | t+1 => branchTrace g root (Nat.unpair t).1 ++ (stageBatch g root t).events
termination_by t => t
decreasing_by exact Nat.lt_succ_of_le (Nat.unpair_left_le _)

private theorem stageTraceExtends {A : Type} (g : ℕ → ℕ) (root : Script A) {i t : ℕ}
    (hit : i ≤ t) : (stageTrace g root i).Sublist (stageTrace g root t) := by
  induction hit with
  | refl => exact List.Sublist.refl _
  | step h ih => exact ih.trans (List.sublist_append_left _ _)

theorem branchTraceSublist {A : Type} (g : ℕ → ℕ) (root : Script A) (i : ℕ) :
    (branchTrace g root i).Sublist (stageTrace g root i) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero => simp [branchTrace,stageTrace]
    | succ t =>
      rw [branchTrace,stageTrace]
      exact ((ih _ (Nat.lt_succ_of_le (Nat.unpair_left_le t))).trans
        (stageTraceExtends g root (Nat.unpair_left_le t))).append (List.Sublist.refl _)

private theorem shrinksOfSublist {s t : List Event} (h : s.Sublist t) : Shrinks s t := by
  induction h with
  | slnil => exact .nil
  | cons e _ ih => exact .skip e ih
  | cons_cons e _ ih =>
    cases e with
    | cut => exact .cut ih
    | architect a => exact .architect le_rfl ih
    | builder n => exact .builder n ih

def ResidualReads {A : Type} (r : Sum A (Script A)) (s : List Event) (x : A) :=
  match r with
  | .inl y => s = [] ∧ y = x
  | .inr p => Reads p s x

theorem branchTraceReads {A : Type} (g : ℕ → ℕ) (root : Script A) (i : ℕ)
    (s : List Event) (x : A) (h : ResidualReads ((stageTable g root i).slot i) s x) :
    Reads root (branchTrace g root i ++ s) x := by
  induction i using Nat.strong_induction_on generalizing s with
  | h i ih =>
    cases i with
    | zero => simpa [branchTrace,stageTable,ResidualReads] using h
    | succ t =>
      rw [newSlot] at h
      rw [branchTrace,List.append_assoc]
      apply ih _ (Nat.lt_succ_of_le (Nat.unpair_left_le t))
      let j := (Nat.unpair t).1
      have he := stableSlot g root (Nat.unpair_left_le t)
      cases hp : (stageTable g root j).slot j with
      | inl y =>
        have hb : stageBatch g root t = ⟨[],(stageTable g root t).bound + 1,.inl y⟩ := by
          simp [stageBatch, StageTable.batch, he.trans hp]
        rw [hb] at h ⊢
        exact h
      | inr p =>
        have hb : stageBatch g root t =
            nextBatch g ((stageTable g root t).bound+1) p ((stageTable g root t).bound+1) := by
          simp [stageBatch, StageTable.batch, he.trans hp]
        rw [hb] at h ⊢
        exact nextBatchReads _ _ _ _ _ _ h

theorem finalStageReads {A : Type} (g : ℕ → ℕ) (root : Script A) (i : ℕ)
    (x : A) (h : (stageTable g root i).slot i = .inl x) :
    Reads root (branchTrace g root i) x ∧ Room g 0 (branchTrace g root i) := by
  have hr : ResidualReads ((stageTable g root i).slot i) [] x := by
    rw [h]
    exact ⟨rfl,rfl⟩
  exact ⟨by simpa using branchTraceReads g root i [] x hr,
    (shrinksOfSublist (branchTraceSublist g root i)).room 0
      (by simpa using stageTraceRoom g root i [] trivial)⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

-- The suffix after a cut is a strict descendant in the inductive script.
-- This proves termination even when branching sizes have no finite bound.
theorem batchInduction {A : Type} (g : ℕ → ℕ) (P : Script A → Prop)
    (step : ∀ p, (∀ r n q, (nextBatch g r p n).result = .inr q → P q) → P p)
    (p : Script A) : P p := by
  suffices P p ∧ ∀ r n q, (nextBatch g r p n).result = .inr q → P q from this.1
  induction p with
  | done x =>
    have h (r n : ℕ) (q : Script A) (e : (nextBatch g r (.done x) n).result = .inr q) :
        P q := by cases e
    exact ⟨step _ h,h⟩
  | cut p ih =>
    have h (r n : ℕ) (q : Script A) (e : (nextBatch g r (.cut p) n).result = .inr q) :
        P q := (Sum.inr.inj e) ▸ ih.1
    exact ⟨step _ h,h⟩
  | architect t ih =>
    have h (r n : ℕ) (q : Script A) (e : (nextBatch g r (.architect t) n).result = .inr q) :
        P q := (ih r).2 r (advance n r) q e
    exact ⟨step _ h,h⟩
  | builder t ih =>
    have h (r n : ℕ) (q : Script A) (e : (nextBatch g r (.builder t) n).result = .inr q) :
        P q := (ih (g (n+1))).2 r (advance n (g (n+1))) q e
    exact ⟨step _ h,h⟩

def SlotChild (i j : ℕ) := ∃ t, j = t+1 ∧ (Nat.unpair t).1 = i

theorem finalDescendant {A : Type} (g : ℕ → ℕ) (root p : Script A) (i : ℕ)
    (hi : (stageTable g root i).slot i = .inr p) :
    ∃ j x, Relation.TransGen SlotChild i j ∧ (stageTable g root j).slot j = .inl x := by
  induction p using batchInduction g generalizing i with
  | step p ih =>
    let t := Nat.pair i 0
    have hc : SlotChild i (t+1) := ⟨t,rfl,by simp [t]⟩
    have hr := stageBatchAtPair g root i 0 p hi
    have hslot := newSlot g root t
    rw [show stageBatch g root t = _ from hr] at hslot
    cases he : (nextBatch g ((stageTable g root t).bound+1) p
        ((stageTable g root t).bound+1)).result with
    | inl x => exact ⟨t+1,x,.single hc,hslot.trans he⟩
    | inr q =>
      obtain ⟨j,x,hj,hx⟩ := ih _ _ q he _ (hslot.trans he)
      exact ⟨j,x,hj.head hc,hx⟩

private theorem shrinksNumbers {s t : List Event} (h : Shrinks s t) :
    (s.filterMap Event.number).Sublist (t.filterMap Event.number) := by
  induction h with
  | nil => exact List.Sublist.slnil
  | skip e _ ih =>
    cases e with
    | cut | architect => exact ih
    | builder n => exact .cons n ih
  | cut | architect => assumption
  | builder n _ ih => exact .cons_cons n ih

private theorem weaveCutFree {c b : Bool} {l r s : List Event} (h : Weave c l r s b) :
    Event.cut ∉ s := by
  induction h with
  | finishLeft h | finishRight h => exact h
  | leftMove he _ ih | rightMove he _ ih =>
    exact fun hm => (List.mem_cons.mp hm).elim (fun e => he e.symm) ih
  | leftCut | rightCut => assumption

-- Once a woven trace is identified inside the chronological record, both
-- numerical side conditions hold for that same interleaving.
theorem spacedStageWeave {A : Type} (g : ℕ → ℕ) (hg : StrictMono g) (root : Script A)
    (i : ℕ) {l r s : List Event} {b : Bool} (hw : Weave true l r s b)
    (hs : Shrinks s (stageTrace g root i)) :
    (0 :: s.filterMap Event.number).Pairwise (· < ·) ∧ Spaced g [] s := by
  have hn : (0 :: (stageTrace g root i).filterMap Event.number).Pairwise (· < ·) := by
    simpa using stageTraceIncreasing g hg root i [] (by simp)
  exact ⟨hn.sublist ((shrinksNumbers hs).cons_cons 0),
    spacedOfRoom s [] 0 (hs.room 0 (by simpa using stageTraceRoom g root i [] trivial))
      (weaveCutFree hw) (by simp) (by simp)⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

private theorem splitRead {A B : Type} (p : Script A) (k : A → Script B)
    {s : List Event} {y : B} (h : Reads (p.bind k) s y) :
    ∃ x u v, Reads p u x ∧ Reads (k x) v y ∧ s = u ++ v := by
  induction p generalizing s with
  | done x => exact ⟨x,[],s,.done x,h,rfl⟩
  | architect t ih =>
    cases h with
    | architect h =>
      obtain ⟨x,u,v,hu,hv,rfl⟩ := ih _ h
      exact ⟨x,_,v,.architect hu,hv,rfl⟩
  | builder t ih =>
    cases h with
    | builder h =>
      obtain ⟨x,u,v,hu,hv,rfl⟩ := ih _ h
      exact ⟨x,_,v,.builder hu,hv,rfl⟩
  | cut p ih =>
    cases h with
    | cut h =>
      obtain ⟨x,u,v,hu,hv,rfl⟩ := ih h
      exact ⟨x,_,v,.cut hu,hv,rfl⟩

private theorem indicesOfRead (n : ℕ) {s : List Event} {m : List ℕ}
    (h : Reads (indices n) s m) : m.length = n ∧ s = m.map Event.builder := by
  induction n generalizing s m with
  | zero => cases h; exact ⟨rfl,rfl⟩
  | succ n ih =>
    cases h with
    | builder h =>
      obtain ⟨m,u,v,hu,hv,rfl⟩ := splitRead (indices n) _ h
      cases hv
      obtain ⟨hk,rfl⟩ := ih hu
      simp [hk]

private theorem childrenOfRead {A B : Type} (child : ℕ → Script B) (val : A → B)
    (ev : ℕ → A → List Event) (P : ℕ → A → Prop)
    (decode : ∀ i s x, Reads (child i) s x → ∃ a, P i a ∧ s = ev i a ∧ x = val a)
    (n i : ℕ) {s : List Event} {x : Tuple B n} (h : Reads (children child n i) s x) :
    ∃ bs : List A, IndexedAll P i bs ∧ s = indexedMoves ev i bs ∧
      (Word.mk n x) = ⟨bs.length,makeTuple val bs⟩ := by
  induction n generalizing i s with
  | zero => cases h; exact ⟨[],trivial,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨y,u,v,hu,hv,rfl⟩ := splitRead (child i) _ h
    obtain ⟨a,ha,rfl,rfl⟩ := decode i _ y hu
    obtain ⟨xs,w,z,hw,hz,rfl⟩ := splitRead (children child n (i+1)) _ hv
    cases hz
    obtain ⟨bs,hbs,rfl,he⟩ := ih (i+1) hw
    let prepend (w : Word B) : Word B := ⟨w.len+1,toLex (val a,w.letters)⟩
    exact ⟨a::bs,⟨ha,hbs⟩,by simp [indexedMoves],congrArg prepend he⟩

private theorem nodeOfRead {A B : Type} (child : Bool → Script B) (val : A → B)
    (ev : List ℕ → ℕ → A → List Event) (P : List ℕ → ℕ → A → Prop)
    (decode : ∀ m i s x, Reads (child (decide (i ∈ m))) s x →
      ∃ a, P m i a ∧ s = ev m i a ∧ x = val a)
    (n : ℕ) {s : List Event} {x : Word B} (h : Reads (node n child) s x) :
    ∃ m : List ℕ, ∃ bs : List A, m.length = n ∧ IndexedAll (P m) 1 bs ∧
      s = nodeMoves m bs.length (indexedMoves (ev m) 1 bs) ∧ x = ⟨bs.length,makeTuple val bs⟩ := by
  obtain ⟨m,u,v,hu,hv,rfl⟩ := splitRead (indices n) _ h
  obtain ⟨hn,rfl⟩ := indicesOfRead n hu
  cases hv with
  | @builder _ total _ _ hv =>
    obtain ⟨ys,w,z,hw,hz,rfl⟩ := splitRead (children _ total 1) _ hv
    cases hz
    obtain ⟨bs,hbs,rfl,he⟩ := childrenOfRead _ val (ev m) (P m) (decode m) total 1 hw
    have hl := congrArg Word.len he
    refine ⟨m,bs,hn,hbs,?_,he⟩
    simpa only [nodeMoves,List.append_nil] using congrArg
      (fun a => m.map Event.builder ++ Event.builder a :: indexedMoves (ev m) 1 bs) hl

private theorem leafOfRead (m : List ℕ) (i : ℕ) (s : List Event) (x : ℕ)
    (h : Reads (leaf (decide (i ∈ m))) s x) :
    ∃ a : ℕ, True ∧ s = leafMoves m i a ∧ x = id a := by
  cases h with
  | builder h =>
    by_cases hm : i ∈ m
    · simp only [hm,decide_true,if_true] at h
      cases h with | cut h => cases h; exact ⟨_,trivial,by simp [leafMoves,hm],rfl⟩
    · simp only [hm,decide_false] at h
      cases h
      exact ⟨_,trivial,by simp [leafMoves,hm],rfl⟩

private theorem blockOfRead (m : List ℕ) (i : ℕ) (s : List Event) (x : Word ℕ)
    (h : Reads (block (decide (i ∈ m))) s x) :
    ∃ b : MarkedBlock, (i ∈ m ↔ b.marked ≠ []) ∧ s = b.moves ∧ x = b.word := by
  by_cases hm : i ∈ m
  · simp only [hm,decide_true,block,if_true] at h
    cases h with
    | @architect _ n _ _ h =>
      obtain ⟨marks,bs,hn,_,rfl,he⟩ := nodeOfRead leaf id leafMoves
        (fun _ _ _ => True) leafOfRead (n+1) h
      have hpos : marks ≠ [] := by rintro rfl; simp at hn
      exact ⟨⟨bs,marks⟩,by simp [hm,hpos],by simp [MarkedBlock.moves,hpos,hn],he⟩
  · simp only [hm,decide_false,block] at h
    obtain ⟨marks,bs,hn,_,rfl,he⟩ := nodeOfRead leaf id leafMoves
      (fun _ _ _ => True) leafOfRead 0 h
    obtain rfl := List.length_eq_zero_iff.mp hn
    exact ⟨⟨bs,[]⟩,by simp [hm],rfl,he⟩

theorem decorationOfRead {s : List Event} {x : Tree} (h : Reads tree s x) :
    ∃ t : MarkedTree, t.consistent ∧ s = t.moves ∧ t.word = x := by
  cases h with
  | @architect _ n _ _ h =>
    obtain ⟨m,bs,hn,hbs,rfl,he⟩ := nodeOfRead block MarkedBlock.word
      (fun _ _ b => b.moves) (fun m i b => i ∈ m ↔ b.marked ≠ []) blockOfRead n h
    exact ⟨⟨bs,m⟩,hbs,by simp [MarkedTree.moves,hn],he.symm⟩

theorem finalStageDecoration (g : ℕ → ℕ) (i : ℕ) (x : Tree)
    (h : (stageTable g tree i).slot i = .inl x) :
    ∃ t : MarkedTree, t.word = x ∧ t.consistent ∧ t.moves = branchTrace g tree i ∧
      Room g 0 t.moves := by
  obtain ⟨hr,hs⟩ := finalStageReads g tree i x h
  obtain ⟨t,hc,he,hx⟩ := decorationOfRead hr
  exact ⟨t,hx,hc,he.symm,he ▸ hs⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

-- Each run is a maximal group of consecutive cells of one tree, after
-- ignoring stages belonging to neither tree. It ends in a switch exactly
-- when the tree has a later run of its own.
def runProjection : List (List Event) → List Event
  | [] => []
  | [a] => a
  | [a,_] => a
  | a :: _ :: c :: rs => a ++ .cut :: runProjection (c :: rs)

private theorem movesBeforeWeave {l r s : List Event} {b : Bool} (p : List Event)
    (hn : Event.cut ∉ p) :
    (Weave true l r s b → Weave true (p ++ l) r (p ++ s) b) ∧
    (Weave false l r s b → Weave false l (p ++ r) (p ++ s) b) := by
  induction p with
  | nil => exact ⟨id,id⟩
  | cons e p ih =>
    have he : e ≠ .cut := by rintro rfl; exact hn List.mem_cons_self
    have h := ih (fun hm => hn (List.mem_cons_of_mem _ hm))
    exact ⟨fun hw => .leftMove he (h.1 hw),fun hw => .rightMove he (h.2 hw)⟩

theorem weaveRuns (runs : List (List Event)) (hc : ∀ p ∈ runs, Event.cut ∉ p) :
    ∃ b, Weave true (runProjection runs) (runProjection runs.tail) runs.flatten b ∧
      Weave false (runProjection runs.tail) (runProjection runs) runs.flatten (!b) := by
  induction runs with
  | nil => exact ⟨false,.finishLeft (by simp [runProjection]),.finishRight (by simp [runProjection])⟩
  | cons p rs ih =>
    have hp := hc p List.mem_cons_self
    have hrest := fun q hq => hc q (List.mem_cons_of_mem p hq)
    obtain _ | ⟨q,rs⟩ := rs
    · exact ⟨false,by simpa [runProjection] using
        (movesBeforeWeave p hp).1 (Weave.finishLeft (by simp) : Weave true [] [] [] false),
        by simpa [runProjection] using
        (movesBeforeWeave p hp).2 (Weave.finishRight (by simp) : Weave false [] [] [] true)⟩
    · obtain _ | ⟨r,rs⟩ := rs
      · have hq := hrest q List.mem_cons_self
        exact ⟨false,by simpa [runProjection] using (movesBeforeWeave p hp).1 (.finishLeft hq),
          by simpa [runProjection] using (movesBeforeWeave p hp).2 (.finishRight hq)⟩
      · obtain ⟨b,hl,hr⟩ := ih hrest
        refine ⟨!b,?_,?_⟩
        · exact (movesBeforeWeave p hp).1 (.leftCut hr)
        · rw [Bool.not_not]
          exact (movesBeforeWeave p hp).2 (.rightCut hl)

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Ordinal

-- A difference in the encoded word is witnessed before either suffix
-- begins. In particular unrelated later choices cannot reverse its order.
private def OrderedCode {A : Type} [LT A] (code : A → List ℕ) :=
  ∀ x y, x < y → ∀ u v : List ℕ,
    List.Lex (· < ·) (code x ++ u) (code y ++ v)

private theorem tupleCode {A : Type} [LinearOrder A] (code : A → List ℕ)
    (hcode : OrderedCode code) (n : ℕ) : OrderedCode (tokens code n) := by
  induction n with
  | zero =>
    intro x y h
    exact (lt_irrefl _ (Subsingleton.elim x y ▸ h)).elim
  | succ n ih =>
    rintro ⟨a,x⟩ ⟨b,y⟩ h u v
    rcases Prod.Lex.lt_iff.mp h with hab | ⟨rfl,hxy⟩
    · change List.Lex _ ((code a ++ tokens code n x) ++ u) ((code b ++ tokens code n y) ++ v)
      simpa only [List.append_assoc] using
        hcode a b hab (tokens code n x ++ u) (tokens code n y ++ v)
    · change List.Lex _ ((code a ++ tokens code n x) ++ u) ((code a ++ tokens code n y) ++ v)
      simpa only [List.append_assoc] using
        List.Lex.append_left (· < ·) (ih x y hxy u v) (code a)

private theorem wordCode {A : Type} [LinearOrder A] [WellFoundedLT A] [Fact (2 ≤ typeLT A)]
    (code : A → List ℕ) (hc : OrderedCode code) :
    OrderedCode (fun x : Word A => x.len :: tokens code x.len x.letters) := by
  intro x y h u v
  rcases (Word.lt_iff x y).mp h with hl | ⟨he,hl⟩
  · exact .rel hl
  · rcases x with ⟨n,x⟩
    rcases y with ⟨m,y⟩
    cases he
    exact .cons (tupleCode code hc n x y hl u v)

theorem transcriptStrictMono : StrictMono transcript := by
  have hleaf : OrderedCode (fun x : ℕ => [x]) := fun _ _ h _ _ => .rel h
  have hc := wordCode blockTokens (wordCode _ hleaf)
  intro x y hxy
  change List.Lex (· < ·) (transcript x) (transcript y)
  simpa only [List.append_nil,transcript] using hc x y hxy [] []

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

private theorem activeSorted (i : ℕ) (bs : List MarkedBlock) :
    (activeBlocks i bs).Pairwise (· < ·) := by
  induction bs generalizing i with
  | nil => exact .nil
  | cons b bs ih =>
    rw [activeBlocks]
    split
    · exact ih _
    · exact List.pairwise_cons.mpr ⟨activeLower _ _,ih _⟩

private theorem activeMem (m : List ℕ) (i j : ℕ) (bs : List MarkedBlock)
    (hc : IndexedAll (fun k (b : MarkedBlock) => k ∈ m ↔ b.marked ≠ []) i bs) :
    j ∈ activeBlocks i bs ↔ i ≤ j ∧ j < i + bs.length ∧ j ∈ m := by
  induction bs generalizing i with
  | nil => simp [activeBlocks]; omega
  | cons b bs ih =>
    obtain ⟨hi,ht⟩ := hc
    rw [activeBlocks]
    by_cases he : b.marked = []
    · rw [if_pos he,ih _ ht,List.length_cons]
      have hni : i ∉ m := fun h => (hi.mp h) he
      by_cases hj : j = i
      · subst j
        simp [hni]
      · by_cases hmj : j ∈ m <;> (simp [hmj]; all_goals omega)
    · rw [if_neg he,List.mem_cons,ih _ ht,List.length_cons]
      have hmi : i ∈ m := hi.mpr he
      by_cases hj : j = i
      · subst j
        simp [hmi]
      · by_cases hmj : j ∈ m <;> (simp [hmj,hj]; all_goals omega)

theorem markedTreeCanonical (t : MarkedTree) (hc : t.consistent)
    (hs : (0 :: t.moves.filterMap Event.number).Pairwise (· < ·)) :
    decorate t.blocks = t := by
  rw [MarkedTree.builderMoves] at hs
  obtain ⟨hpos,hrest⟩ := List.pairwise_cons.mp hs
  obtain ⟨hm,_,hcross⟩ := List.pairwise_append.mp hrest
  have he : activeBlocks 1 t.blocks = t.marked := by
    apply (activeSorted _ _).eq_of_mem_iff hm
    intro j
    rw [activeMem t.marked 1 j t.blocks hc]
    refine ⟨fun h => h.2.2,fun hj => ⟨?_,?_,hj⟩⟩
    · exact hpos _ (List.mem_append_left _ hj)
    · have hlt := hcross j hj t.blocks.length List.mem_cons_self
      omega
  cases t
  exact congrArg _ he

theorem finalCanonicalDecoration (g : ℕ → ℕ) (hg : StrictMono g) (i : ℕ) (x : Tree)
    (h : (stageTable g Script.tree i).slot i = .inl x) :
    ∃ bs : List MarkedBlock, (decorate bs).word = x ∧
      (decorate bs).moves = branchTrace g Script.tree i ∧ Room g 0 (decorate bs).moves := by
  obtain ⟨t,hx,hc,he,hr⟩ := finalStageDecoration g i x h
  have hs := stageTraceIncreasing g hg Script.tree i [] (by simp)
  rw [List.append_nil] at hs
  have ht := hs.sublist ((shrinksNumbers (shrinksOfSublist
    (branchTraceSublist g Script.tree i))).cons_cons 0)
  rw [← he] at ht
  exact ⟨t.blocks,by rwa [markedTreeCanonical t hc ht],
    by rwa [markedTreeCanonical t hc ht],by rwa [markedTreeCanonical t hc ht]⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

-- A switch is named by the Builder value of the leaf immediately before
-- it. Suppressing a switch preserves the leaf, including its value.
inductive LeafMask (keep : ℕ → Bool) : List Event → List Event → Prop
  | nil : LeafMask keep [] []
  | dropBuilder {s t} (x : ℕ) : LeafMask keep s t → LeafMask keep s (.builder x :: t)
  | dropArchitect {s t} (n : ℕ) : LeafMask keep s t → LeafMask keep s (.architect n :: t)
  | builder {s t} (x : ℕ) : LeafMask keep s t →
      LeafMask keep (.builder x :: s) (.builder x :: t)
  | architect {s t a b} : a ≤ b → LeafMask keep s t →
      LeafMask keep (.architect a :: s) (.architect b :: t)
  | leaf {s t} (x : ℕ) : LeafMask keep s t →
      LeafMask keep (.builder x :: (if keep x then [.cut] else []) ++ s)
        (.builder x :: .cut :: t)

private theorem LeafMask.append {k : ℕ → Bool} {s t u v : List Event}
    (h : LeafMask k s t) (hr : LeafMask k u v) : LeafMask k (s ++ u) (t ++ v) := by
  induction h with
  | nil => exact hr
  | dropBuilder x _ ih => exact .dropBuilder x ih
  | dropArchitect n _ ih => exact .dropArchitect n ih
  | builder x _ ih => exact .builder x ih
  | architect hab _ ih => exact .architect hab ih
  | leaf x _ ih => simpa only [List.cons_append,List.append_assoc] using LeafMask.leaf x ih

theorem LeafMask.shrinks {k : ℕ → Bool} {s t : List Event} (h : LeafMask k s t) :
    Shrinks s t := by
  induction h with
  | nil => exact .nil
  | dropBuilder x _ ih => exact .skip (.builder x) ih
  | dropArchitect n _ ih => exact .skip (.architect n) ih
  | builder x _ ih => exact .builder x ih
  | architect hab _ ih => exact .architect hab ih
  | leaf x _ ih =>
    cases hk : k x
    · exact .builder x (.skip .cut ih)
    · exact .builder x (.cut ih)

private theorem maskIndices (k : ℕ → Bool) {m n : List ℕ} (h : m.Sublist n) :
    LeafMask k (m.map Event.builder) (n.map Event.builder) := by
  induction h with
  | slnil => exact .nil
  | cons x _ ih => exact .dropBuilder x ih
  | cons_cons x _ ih => exact .builder x ih

private theorem maskLeaves (k f : ℕ → Bool) (m : List ℕ) (i : ℕ) (xs : List ℕ)
    (hf : IndexedAll (fun j x => f j = k x) i xs) :
    LeafMask k (indexedMoves (leafMoves (m.filter f)) i xs) (indexedMoves (leafMoves m) i xs) := by
  induction xs generalizing i with
  | nil => exact .nil
  | cons x xs ih =>
    obtain ⟨he,ht⟩ := hf
    apply LeafMask.append _ (ih _ ht)
    by_cases hm : i ∈ m
    · simpa [leafMoves,hm,he] using (LeafMask.leaf x (LeafMask.nil (keep := k)))
    · simpa [leafMoves,hm] using (LeafMask.builder x (LeafMask.nil (keep := k)))

private theorem maskBlock (k f : ℕ → Bool) (b : MarkedBlock)
    (hf : IndexedAll (fun j x => f j = k x) 1 b.leaves) :
    LeafMask k ({b with marked := b.marked.filter f} : MarkedBlock).moves b.moves := by
  have hm : (b.marked.filter f).Sublist b.marked := List.filter_sublist
  have hs := (maskIndices k hm).append
    (LeafMask.builder b.leaves.length (maskLeaves k f b.marked 1 b.leaves hf))
  by_cases he : b.marked = []
  · simpa [MarkedBlock.moves,nodeMoves,he] using hs
  · by_cases hc : b.marked.filter f = []
    · simp only [MarkedBlock.moves,if_pos hc,if_neg he]
      exact .dropArchitect _ hs
    · simp only [MarkedBlock.moves,if_neg hc,if_neg he]
      exact .architect (Nat.sub_le_sub_right hm.length_le _) hs

private theorem maskBlocks (k : ℕ → Bool) (fs : ℕ → ℕ → Bool) (i j : ℕ)
    (bs : List MarkedBlock)
    (hf : IndexedAll (fun a (b : MarkedBlock) =>
      IndexedAll (fun v x => fs a v = k x) 1 b.leaves) i bs) :
    LeafMask k (indexedMoves (fun _ b => b.moves) j (pruneBlocks fs i bs))
      (indexedMoves (fun _ b => b.moves) j bs) := by
  induction bs generalizing i j with
  | nil => exact .nil
  | cons b bs ih => exact (maskBlock k (fs i) b hf.1).append (ih _ _ hf.2)

private theorem indexedLookup {A : Type} (a : A) (i : ℕ) (xs : List A) :
    IndexedAll (fun j x => xs[j-i]?.getD a = x) i xs := by
  induction xs generalizing i with
  | nil => trivial
  | cons x xs ih =>
    refine ⟨by simp,?_⟩
    apply indexedChange _ _ (ih (i+1))
    intro j hj y hy
    simpa [show j-i = (j-(i+1))+1 by omega] using hy

theorem coarsenByLeafValue (k : ℕ → Bool) (bs : List MarkedBlock) :
    ∃ t : MarkedTree, t.word = (decorate bs).word ∧ t.consistent ∧
      LeafMask k t.moves (decorate bs).moves := by
  let bsAt (i : ℕ) := bs[i-1]?.getD ⟨[],[]⟩
  let fs (i j : ℕ) := k ((bsAt i).leaves[j-1]?.getD 0)
  have hf : IndexedAll (fun a (b : MarkedBlock) =>
      IndexedAll (fun v x => fs a v = k x) 1 b.leaves) 1 bs := by
    apply indexedChange _ _ (indexedLookup ⟨[],[]⟩ 1 bs)
    intro i _ b hb
    apply indexedChange _ _ (indexedLookup 0 1 b.leaves)
    intro j _ x hx
    change k ((bsAt i).leaves[j-1]?.getD 0) = k x
    change bsAt i = b at hb
    rw [hb,hx]
  refine ⟨decorate (pruneBlocks fs 1 bs),pruneWord _ _ _,consistentActive _ _,?_⟩
  have hm := pruneActive fs 1 bs
  simp only [MarkedTree.moves,decorate,pruneLength]
  exact .architect hm.length_le ((maskIndices k hm).append
    (.builder _ (maskBlocks k fs 1 1 bs hf)))

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

theorem branchExtends {A : Type} (g : ℕ → ℕ) (root : Script A) {i j : ℕ}
    (h : Relation.TransGen SlotChild i j) :
    ∃ u, branchTrace g root j = branchTrace g root i ++ u := by
  have one {a b : ℕ} (hc : SlotChild a b) :
      ∃ u, branchTrace g root b = branchTrace g root a ++ u := by
    obtain ⟨t,rfl,rfl⟩ := hc
    exact ⟨_,by rw [branchTrace]⟩
  induction h with
  | single h => exact one h
  | tail _ h ih =>
    obtain ⟨u,hu⟩ := ih
    obtain ⟨v,hv⟩ := one h
    exact ⟨u ++ v,by rw [hv,hu,List.append_assoc]⟩

theorem finalExtension {A : Type} (g : ℕ → ℕ) (root : Script A) (i : ℕ) :
    ∃ j x u, (stageTable g root j).slot j = .inl x ∧
      branchTrace g root j = branchTrace g root i ++ u := by
  cases hp : (stageTable g root i).slot i with
  | inl x => exact ⟨i,x,[],hp,by simp⟩
  | inr p =>
    obtain ⟨j,x,hj,he⟩ := finalDescendant g root p i hp
    obtain ⟨u,hu⟩ := branchExtends g root hj
    exact ⟨j,x,u,he,hu⟩

private theorem activeLength (i : ℕ) (bs : List MarkedBlock) :
    (activeBlocks i bs).length ≤ bs.length := by
  induction bs generalizing i with
  | nil => rfl
  | cons b bs ih =>
    rw [activeBlocks]
    split
    · exact (ih _).trans (Nat.le_succ _)
    · exact Nat.succ_le_succ (ih _)

def stagedWords (g : ℕ → ℕ) : Set Tree :=
  {x | ∃ j, (stageTable g Script.tree j).slot j = .inl x}

theorem unboundedStagedWords (g : ℕ → ℕ) (hg : StrictMono g) (k : ℕ) :
    ∃ x ∈ stagedWords g, k < x.len := by
  obtain ⟨t,_,hparent,hrank,hbatch⟩ := arbitrarilyLateChild g Script.tree 0 k Script.tree rfl
  obtain ⟨j,x,u,hj,hu⟩ := finalExtension g Script.tree (t+1)
  obtain ⟨bs,hword,htrace,_⟩ := finalCanonicalDecoration g hg j x hj
  rw [branchTrace,hparent,branchTrace,List.nil_append,hbatch] at hu
  let rank := (stageTable g Script.tree t).bound+1
  have he : Event.architect (activeBlocks 1 bs).length = .architect rank :=
    List.cons.inj (htrace.trans hu) |>.1
  have hlen := Event.architect.inj he
  refine ⟨x,⟨j,hj⟩,?_⟩
  rw [← hword]
  change k < bs.length
  exact (hrank.trans_le (hlen.ge.trans (activeLength 1 bs)))

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

-- The three projected histories may use different actions at the same
-- vertex. Each history is checked from just after its fixed opening move.
theorem positiveOpeningEdges (G : SimpleGraph Tree) (f : ℕ → ℕ) (d : ℕ) (b : Bool)
    (h : ((increasing ((node (d+1) block).interleave tree) 0).score (wins G b)).outcome f true) :
    ∃ policy : PairGame.Policy, ∀ (t u : MarkedTree) (s : List Event) (c : Bool),
      t.consistent → u.consistent →
      Weave true t.moves u.moves (.architect (d+1) :: s) c →
      (0 :: s.filterMap Event.number).Pairwise (· < ·) →
      Timely f policy.cutoff [] s → Prescribed policy.action [] s →
      G.Adj t.word u.word ∧ c = b := by
  let game' := increasing ((node (d+1) block).interleave tree) 0
  let root := game'.score (wins G b)
  obtain ⟨policy,hp⟩ := PairGame.policyOfOutcome root f true h
  refine ⟨policy,?_⟩
  intro t u s c ht hu hw hs htime ha
  have hw' := followsGame t u ht hu _ c hw hs
  have follow : Follows game' s (some (t.word,u.word,c)) := by
    cases hw' with | architect h => exact h
  obtain ⟨legal,terminal⟩ := timelyPlay _ root f true policy follow [] htime (fun _ => ha) rfl
  have hv := hp _ legal
  rw [List.nil_append] at terminal
  rw [terminal] at hv
  exact hv

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

-- Erase the numerical labels to read the remaining marked-block and
-- marked-leaf counts directly from a completed branch.
private def control : Event → Bool
  | .builder _ => false
  | _ => true

private theorem controlNode (m : List ℕ) (n : ℕ) (body : List Event) :
    (nodeMoves m n body).filter control = body.filter control := by
  induction m with
  | nil => simp [nodeMoves,control]
  | cons x xs ih => exact ih

private theorem controlLeaves (m : List ℕ) (i : ℕ) (xs : List ℕ) :
    (indexedMoves (leafMoves m) i xs).filter control = List.replicate
      (((List.range' i xs.length).filter (fun j => decide (j ∈ m))).length) .cut := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : i ∈ m <;> simp [indexedMoves,leafMoves,h,control,List.filter_cons,List.range'_succ,ih,List.replicate_succ]

private theorem controlBlock (b : MarkedBlock)
    (h : (0 :: b.numbers).Pairwise (· < ·)) :
    b.moves.filter control = if b.marked = [] then [] else
      .architect (b.marked.length-1) :: List.replicate b.marked.length .cut := by
  obtain ⟨hpos,hrest⟩ := List.pairwise_cons.mp h
  obtain ⟨hs,_,hcross⟩ := List.pairwise_append.mp hrest
  let ms := (List.range' 1 b.leaves.length).filter (fun j => decide (j ∈ b.marked))
  have eq : ms = b.marked := by
    have hms : ms.Pairwise (· < ·) := (List.pairwise_lt_range' _ (by decide : 0 < 1)).sublist List.filter_sublist
    apply hms.eq_of_mem_iff hs
    intro j
    simp only [ms,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    intro hj
    have hpos' := hpos j (List.mem_append_left _ hj)
    have hlt := hcross j hj b.leaves.length List.mem_cons_self
    exact List.mem_range'.mpr ⟨j-1,by omega,by simp; omega⟩
  have hl := controlLeaves b.marked 1 b.leaves
  change _ = List.replicate ms.length Event.cut at hl
  rw [eq] at hl
  by_cases he : b.marked = []
  · simpa only [MarkedBlock.moves,if_pos he,controlNode,he,ite_true,List.length_nil,List.replicate_zero]
      using hl
  · simp [MarkedBlock.moves,he,List.filter_cons,control,controlNode,hl]

private def degrees : List MarkedBlock → List ℕ
  | [] => []
  | b :: bs => if b.marked = [] then degrees bs else b.marked.length :: degrees bs

private theorem degreesLength (i : ℕ) (bs : List MarkedBlock) :
    (degrees bs).length = (activeBlocks i bs).length := by
  induction bs generalizing i with
  | nil => rfl
  | cons b bs ih =>
    by_cases he : b.marked = [] <;> simpa [degrees,activeBlocks,he] using ih (i+1)

private theorem positiveDegrees (bs : List MarkedBlock) :
    ∀ d ∈ degrees bs, 0 < d := by
  induction bs with
  | nil => simp [degrees]
  | cons b bs ih =>
    by_cases he : b.marked = []
    · simpa [degrees,he] using ih
    · simpa [degrees,he,List.length_pos_iff] using And.intro
        (List.length_pos_iff.mpr he) ih

private theorem controlBlocks (bs : List MarkedBlock) (i : ℕ)
    (h : (0 :: bs.flatMap MarkedBlock.numbers).Pairwise (· < ·)) :
    (indexedMoves (fun _ b => b.moves) i bs).filter control =
      (degrees bs).flatMap (fun n => .architect (n-1) :: List.replicate n .cut) := by
  induction bs generalizing i with
  | nil => rfl
  | cons b bs ih =>
    have h₁ : (0 :: b.numbers).Pairwise (· < ·) :=
      h.sublist ((List.sublist_append_left _ _).cons_cons 0)
    have h₂ : (0 :: bs.flatMap MarkedBlock.numbers).Pairwise (· < ·) :=
      h.sublist ((List.sublist_append_right _ _).cons_cons 0)
    by_cases he : b.marked = [] <;>
      simp [indexedMoves,List.filter_append,controlBlock b h₁,he,degrees,ih _ h₂]

theorem finalStageShape (g : ℕ → ℕ) (hg : StrictMono g) (j : ℕ) (x : Tree)
    (h : (stageTable g Script.tree j).slot j = .inl x) :
    ∃ ds : List ℕ, (∀ n ∈ ds, 0 < n) ∧ ds.length ≤ x.len ∧
      (branchTrace g Script.tree j).filter (fun e => e.number.isNone) =
        .architect ds.length :: ds.flatMap (fun n => .architect (n-1) :: List.replicate n .cut) := by
  obtain ⟨bs,hx,he,_⟩ := finalCanonicalDecoration g hg j x h
  have hn := stageTraceIncreasing g hg Script.tree j [] (by simp)
  rw [List.append_nil] at hn
  have ht := hn.sublist ((shrinksNumbers (shrinksOfSublist (branchTraceSublist g Script.tree j))).cons_cons 0)
  rw [← he,MarkedTree.builderMoves] at ht
  have hbs : (0 :: bs.flatMap MarkedBlock.numbers).Pairwise (· < ·) :=
    ht.sublist (((List.Sublist.refl _).cons bs.length).trans
      (List.sublist_append_right _ _) |>.cons_cons 0)
  refine ⟨degrees bs,positiveDegrees bs,?_,?_⟩
  · rw [← hx,degreesLength 1 bs]
    exact activeLength 1 bs
  · have hcontrol : (fun e : Event => e.number.isNone) = control := by funext e; cases e <;> rfl
    rw [← he,hcontrol,degreesLength 1 bs]
    simp [MarkedTree.moves,decorate,List.filter_cons,control,controlNode,controlBlocks bs 1 hbs]

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

-- The indices announced before an arity describe a decoration. Erasing
-- them recovers the root arity, block arities and actual leaf values.
private def readWordLabels (root : Bool) (skip : ℕ) : List Event → List ℕ
  | [] => []
  | .cut :: s => readWordLabels false 0 s
  | .architect n :: s => readWordLabels false (if root then n else n+1) s
  | .builder n :: s =>
    match skip with
    | 0 => n :: readWordLabels false 0 s
    | k+1 => readWordLabels false k s

private theorem readIndexLabels (m : List ℕ) (s : List Event) :
    readWordLabels false m.length (m.map Event.builder ++ s) = readWordLabels false 0 s := by
  induction m with
  | nil => rfl
  | cons x xs ih => exact ih

private theorem readLeafLabels (m : List ℕ) (i : ℕ) (xs : List ℕ) (s : List Event) :
    readWordLabels false 0 (indexedMoves (leafMoves m) i xs ++ s) =
      tokens (fun x => [x]) xs.length (makeTuple id xs) ++ readWordLabels false 0 s := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    by_cases hm : i ∈ m <;> simpa [indexedMoves,leafMoves,hm,readWordLabels,tokens,makeTuple]
      using congrArg (List.cons x) (ih (i+1))

private theorem readBlockLabels (b : MarkedBlock) (s : List Event) :
    readWordLabels false 0 (b.moves ++ s) = blockTokens b.word ++ readWordLabels false 0 s := by
  have body : readWordLabels false b.marked.length
      (nodeMoves b.marked b.leaves.length (indexedMoves (leafMoves b.marked) 1 b.leaves) ++ s) =
      blockTokens b.word ++ readWordLabels false 0 s := by
    simp only [nodeMoves,List.append_assoc,readIndexLabels,List.cons_append,readWordLabels,
      blockTokens,MarkedBlock.word,readLeafLabels]
  by_cases hm : b.marked = []
  · simpa [MarkedBlock.moves,hm] using body
  · have hl : b.marked.length-1+1 = b.marked.length := Nat.sub_add_cancel (List.length_pos_iff.mpr hm)
    simpa [MarkedBlock.moves,hm,readWordLabels,hl] using body

private theorem readBlocksLabels (bs : List MarkedBlock) (i : ℕ) (s : List Event) :
    readWordLabels false 0 (indexedMoves (fun _ b => b.moves) i bs ++ s) =
      tokens blockTokens bs.length (makeTuple MarkedBlock.word bs) ++ readWordLabels false 0 s := by
  induction bs generalizing i with
  | nil => rfl
  | cons b bs ih => simp [indexedMoves,List.append_assoc,readBlockLabels,ih,tokens,makeTuple]

theorem readTranscript {s : List Event} {x : Tree} (h : Reads Script.tree s x) :
    readWordLabels true 0 s = transcript x := by
  obtain ⟨t,_,rfl,rfl⟩ := decorationOfRead h
  have ht := readBlocksLabels t.blocks 1 []
  simp only [List.append_nil,readWordLabels] at ht
  simp [MarkedTree.moves,MarkedTree.word,readWordLabels,nodeMoves,readIndexLabels,ht,transcript]

private theorem decodeAcrossCut (p s : List Event) (root : Bool) (skip : ℕ) :
    readWordLabels root skip (p ++ .cut :: s) =
      readWordLabels root skip (p ++ [.cut]) ++ readWordLabels false 0 s := by
  induction p generalizing root skip with
  | nil => rfl
  | cons e p ih =>
    cases e with
    | cut | architect => exact ih _ _
    | builder n =>
      cases skip with
      | zero => exact congrArg (List.cons n) (ih false 0)
      | succ => exact ih _ _

theorem orderAfterCut {x y : Tree} {p s t : List Event} {a b : ℕ} (hab : a < b)
    (hx : Reads Script.tree (p ++ .cut :: .builder a :: s) x)
    (hy : Reads Script.tree (p ++ .cut :: .builder b :: t) y) : x < y := by
  apply transcriptStrictMono.lt_iff_lt.mp
  rw [← readTranscript hx,← readTranscript hy,decodeAcrossCut p (.builder a :: s),decodeAcrossCut p (.builder b :: t)]
  exact List.Lex.append_left _ (List.Lex.rel hab) _

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

private def ProperSwitches : List Event → Prop
  | [] => True
  | .cut :: s => (∃ n u, s = .builder n :: u) ∧ ProperSwitches s
  | _ :: s => ProperSwitches s

private theorem switchesAppend (s t : List Event) (hs : ProperSwitches s) (ht : ProperSwitches t) :
    ProperSwitches (s ++ t) := by
  induction s with
  | nil => exact ht
  | cons e s ih =>
    cases e with
    | builder | architect => exact ih hs
    | cut =>
      obtain ⟨⟨n,u,hu⟩,hr⟩ := hs
      exact ⟨⟨n,u++t,by rw [hu]; rfl⟩,ih hr⟩

private theorem switchesNode (m : List ℕ) (n : ℕ) (s : List Event) (hs : ProperSwitches s) :
    ProperSwitches (nodeMoves m n s) := by
  induction m with
  | nil => exact hs
  | cons _ _ ih => exact ih

private theorem switchesLeaves (m : List ℕ) (i : ℕ) (xs : List ℕ)
    (h : ∀ j ∈ m, j+1 < i+xs.length) : ProperSwitches (indexedMoves (leafMoves m) i xs) := by
  induction xs generalizing i with
  | nil => trivial
  | cons x xs ih =>
    have ht := ih (i+1) (fun j hj => by have := h j hj; simp only [List.length_cons] at this; omega)
    by_cases hm : i ∈ m
    · have hn : xs ≠ [] := by rintro rfl; have := h i hm; simp at this
      obtain ⟨y,ys,rfl⟩ := List.exists_cons_of_ne_nil hn
      simp only [indexedMoves,leafMoves,if_pos hm,List.cons_append,List.nil_append,ProperSwitches]
      exact ⟨⟨y,_,rfl⟩,ht⟩
    · simpa only [indexedMoves,leafMoves,if_neg hm,List.cons_append,List.nil_append,
        ProperSwitches] using ht

private theorem switchesBlock (b : MarkedBlock) (hs : b.numbers.Pairwise (· < ·)) :
    ProperSwitches b.moves := by
  have hp := (List.pairwise_append.mp hs).2.2
  have hu (j : ℕ) (hj : j ∈ b.marked) : j + 1 < 1+b.leaves.length := by
    have := hp j hj b.leaves.length List.mem_cons_self
    omega
  have hn := switchesNode b.marked b.leaves.length _ (switchesLeaves b.marked 1 b.leaves hu)
  dsimp only [MarkedBlock.moves]
  split <;> exact hn

private theorem switchesBlocks (bs : List MarkedBlock) (i : ℕ)
    (hs : (bs.flatMap MarkedBlock.numbers).Pairwise (· < ·)) :
    ProperSwitches (indexedMoves (fun _ b => b.moves) i bs) := by
  induction bs generalizing i with
  | nil => trivial
  | cons b bs ih =>
    obtain ⟨hb,hbs,_⟩ := List.pairwise_append.mp hs
    exact switchesAppend _ _ (switchesBlock b hb) (ih _ hbs)

theorem nextLeafAfterSwitch {t : MarkedTree} {p s : List Event}
    (he : t.moves = p ++ .cut :: s) (hs : t.numbers.Pairwise (· < ·)) :
    ∃ n u, s = .builder n :: u := by
  have hb := ((List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).2)
  have h : ProperSwitches t.moves :=
    switchesNode t.marked t.blocks.length _ (switchesBlocks _ 1 hb)
  rw [he] at h
  clear he
  induction p with
  | nil => exact h.1
  | cons e p ih =>
    cases e with
    | cut => exact ih h.2
    | builder | architect => exact ih h

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

private theorem batchInterval {A : Type} (g : ℕ → ℕ) (hg : StrictMono g)
    (r : ℕ) (p : Script A) (n : ℕ) (v : ℕ)
    (hv : v ∈ (nextBatch g r p n).events.filterMap Event.number) :
    n < v ∧ v ≤ (nextBatch g r p n).bound := by
  induction p generalizing n with
  | done => cases hv
  | cut p ih => cases hv
  | architect t ih =>
    obtain ⟨hl,hu⟩ := ih r (advance n r) hv
    exact ⟨((Nat.le_succ n).trans (le_max_left _ _)).trans_lt hl,hu⟩
  | builder t ih =>
    let a := g (n+1)
    change v ∈ a :: (nextBatch g r (t a) (advance n a)).events.filterMap Event.number at hv
    rcases List.mem_cons.mp hv with h | h
    · subst v
      exact ⟨hg.id_le _,(le_max_right _ _).trans (nextBound g r (t a) _)⟩
    · obtain ⟨hl,hu⟩ := ih a (advance n a) h
      exact ⟨((Nat.le_succ n).trans (le_max_left _ _)).trans_lt hl,hu⟩

theorem stageInterval {A : Type} (g : ℕ → ℕ) (hg : StrictMono g) (root : Script A)
    {v t : ℕ} (hv : v ∈ (stageBatch g root t).events.filterMap Event.number) :
    (stageTable g root t).bound < v ∧ v ≤ (stageTable g root (t+1)).bound := by
  change _ ∧ v ≤ ((stageTable g root t).batch g t).bound
  change v ∈ ((stageTable g root t).batch g t).events.filterMap Event.number at hv
  unfold StageTable.batch at *
  split at hv
  · cases hv
  · obtain ⟨hl,hu⟩ := batchInterval g hg _ _ _ _ hv
    exact ⟨(Nat.le_succ _).trans_lt hl,hu⟩

private theorem batchEnd {A : Type} (g : ℕ → ℕ) (r : ℕ) (p : Script A) (n : ℕ) :
    match (nextBatch g r p n).result with
    | .inl _ => Event.cut ∉ (nextBatch g r p n).events
    | .inr _ => ∃ u, (nextBatch g r p n).events = u ++ [.cut] ∧ Event.cut ∉ u := by
  induction p generalizing n with
  | done => exact List.not_mem_nil
  | cut => exact ⟨[],rfl,List.not_mem_nil⟩
  | architect t ih =>
    specialize ih r (advance n r)
    dsimp only [nextBatch]
    split at *
    · simpa using ih
    · obtain ⟨u,hu,hn⟩ := ih
      exact ⟨.architect r :: u,congrArg _ hu,by simpa using hn⟩
  | builder t ih =>
    specialize ih (g (n+1)) (advance n (g (n+1)))
    dsimp only [nextBatch]
    split at *
    · simpa using ih
    · obtain ⟨u,hu,hn⟩ := ih
      exact ⟨.builder _ :: u,congrArg _ hu,by simpa using hn⟩

private theorem stageBatchEnd {A : Type} (g : ℕ → ℕ) (root : Script A) (t : ℕ) :
    match (stageBatch g root t).result with
    | .inl _ => Event.cut ∉ (stageBatch g root t).events
    | .inr _ => ∃ u, (stageBatch g root t).events = u ++ [.cut] ∧ Event.cut ∉ u := by
  unfold stageBatch StageTable.batch
  cases (stageTable g root t).slot (Nat.unpair t).1 with
  | inl x => exact List.not_mem_nil
  | inr p => exact batchEnd .. 

private theorem emptyBatch {A : Type} (g : ℕ → ℕ) (rank : ℕ) (p : Script A) (bound : ℕ)
    (he : (nextBatch g rank p bound).events = []) :
    ∃ x, (nextBatch g rank p bound).result = .inl x := by
  cases p with
  | done x => exact ⟨x,rfl⟩
  | builder | architect | cut => cases he

private theorem finalPrefix {A : Type} (g : ℕ → ℕ) (root : Script A) {i j : ℕ}
    (h : Relation.ReflTransGen SlotChild i j) :
    ∃ u, branchTrace g root j = branchTrace g root i ++ u := by
  rcases h.cases_tail with rfl | ⟨a,ha,hab⟩
  · exact ⟨[],by simp⟩
  · exact branchExtends g root (Relation.TransGen.tail' ha hab)

def stageCone (g : ℕ → ℕ) (i : ℕ) : Set Tree :=
  {x | ∃ j, Relation.ReflTransGen SlotChild i j ∧ (stageTable g Script.tree j).slot j = .inl x}

theorem orderedStageChildren (g : ℕ → ℕ) (hg : StrictMono g) (i : ℕ) (u : List Event)
    (hu : branchTrace g Script.tree i = u ++ [.cut]) {t v : ℕ} (htv : t < v)
    (ht : (Nat.unpair t).1 = i) (hv : (Nat.unpair v).1 = i)
    {x y : Tree} (hx : x ∈ stageCone g (t+1)) (hy : y ∈ stageCone g (v+1)) : x < y := by
  have first (a : ℕ) (ha : (Nat.unpair a).1 = i) (z : Tree) (hz : z ∈ stageCone g (a+1)) :
      ∃ n s, n ∈ (stageBatch g Script.tree a).events.filterMap Event.number ∧
        Reads Script.tree (u ++ .cut :: .builder n :: s) z := by
    obtain ⟨j,hd,hj⟩ := hz
    obtain ⟨w,hw⟩ := finalPrefix g Script.tree hd
    rw [branchTrace,ha,hu,List.append_assoc,List.append_assoc] at hw
    obtain ⟨bs,hword,htrace,_⟩ := finalCanonicalDecoration g hg j z hj
    have hsort := stageTraceIncreasing g hg Script.tree j [] (by simp)
    rw [List.append_nil] at hsort
    have hnums := (List.pairwise_cons.mp (hsort.sublist ((shrinksNumbers
      (shrinksOfSublist (branchTraceSublist g Script.tree j))).cons_cons 0))).2
    rw [← htrace,MarkedTree.builderMoves] at hnums
    obtain ⟨n,s,he⟩ := nextLeafAfterSwitch (htrace.trans hw) hnums
    have hne : (stageBatch g Script.tree a).events ≠ [] := by
      intro hnil
      have hz' : ∃ q, (stageBatch g Script.tree a).result = .inl q := by
        unfold stageBatch StageTable.batch at hnil ⊢
        split at hnil
        · exact ⟨_,rfl⟩
        · exact emptyBatch _ _ _ _ hnil
      obtain ⟨q,hq⟩ := hz'
      obtain ⟨bs',_,he',_⟩ := finalCanonicalDecoration g hg (a+1) q ((newSlot ..).trans hq)
      have hqsort := stageTraceIncreasing g hg Script.tree (a+1) [] (by simp)
      rw [List.append_nil] at hqsort
      have hn := (List.pairwise_cons.mp (hqsort.sublist ((shrinksNumbers (shrinksOfSublist
        (branchTraceSublist g Script.tree (a+1)))).cons_cons 0))).2
      rw [← he',MarkedTree.builderMoves] at hn
      rw [branchTrace,ha,hu,hnil,List.append_nil] at he'
      obtain ⟨_,_,hf⟩ := nextLeafAfterSwitch (s := []) he' hn
      cases hf
    obtain ⟨e,es,hee⟩ := List.exists_cons_of_ne_nil hne
    rw [hee] at he
    have hhead := (List.cons.inj he).1
    have hread := (finalStageReads g Script.tree j z hj).1
    rw [hw] at hread
    refine ⟨n,s,?_,?_⟩
    · simp [hee,hhead,Event.number]
    · have htail : es ++ w = s := (List.cons.inj he).2
      change Reads Script.tree (u ++ .cut :: ((stageBatch g Script.tree a).events ++ w)) z at hread
      rw [hee,List.cons_append,hhead,htail] at hread
      exact hread
  obtain ⟨a,s,hnum,hr⟩ := first t ht x hx
  obtain ⟨b,w,hnum',hr'⟩ := first v hv y hy
  have h₁ := (stageInterval g hg Script.tree hnum).2
  have h₂ := (stageInterval g hg Script.tree hnum').1
  exact orderAfterCut ((h₁.trans ((stageBoundMono g Script.tree).monotone htv)).trans_lt h₂) hr hr'

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

private def endSignal {A : Type} : Sum A (Script A) → List Event
  | .inl _ => []
  | .inr _ => [.cut]

private theorem batchControl {A : Type} (g : ℕ → ℕ) (r : ℕ) (p : Script A) (n : ℕ) :
    ∃ k, (nextBatch g r p n).events.filter control =
      List.replicate k (.architect r) ++ endSignal (nextBatch g r p n).result := by
  induction p generalizing n with
  | done | cut => exact ⟨0,rfl⟩
  | architect t ih =>
    obtain ⟨k,he⟩ := ih r (advance n r)
    exact ⟨k+1,by simpa only [nextBatch,List.filter_cons,control,if_true,List.replicate_succ,
      List.cons_append] using congrArg (List.cons (.architect r)) he⟩
  | builder t ih =>
    obtain ⟨k,he⟩ := ih (g (n+1)) (advance n (g (n+1)))
    exact ⟨k,he⟩

private theorem stageControl (g : ℕ → ℕ) (t : ℕ) :
    ∃ k, (stageBatch g Script.tree t).events.filter control =
      List.replicate k (.architect ((stageTable g Script.tree t).bound+1)) ++
        endSignal (stageBatch g Script.tree t).result := by
  unfold stageBatch StageTable.batch
  split
  · exact ⟨0,rfl⟩
  · exact batchControl .. 

private def degreeSignals (ds : List ℕ) : List Event :=
  ds.flatMap (fun n => .architect (n-1) :: List.replicate n .cut)

private def Remaining (b l : ℕ) (s : List Event) :=
  ∃ ds : List ℕ, ds.length = b ∧ (∀ n ∈ ds, 0 < n) ∧
    s = List.replicate l .cut ++ degreeSignals ds

private theorem leafStep {b l k r : ℕ} {s : List Event}
    (h : Remaining b (l+1) (List.replicate k (.architect r) ++ .cut :: s)) :
    Remaining b l s := by
  obtain ⟨ds,hd,hp,he⟩ := h
  cases k with
  | zero => exact ⟨ds,hd,hp,List.cons.inj he |>.2⟩
  | succ => cases he

private theorem blockStep {b k r : ℕ} {s : List Event}
    (h : Remaining (b+1) 0 (List.replicate k (.architect r) ++ .cut :: s)) :
    Remaining b r s := by
  obtain ⟨ds,hd,hp,he⟩ := h
  cases ds with
  | nil => cases hd
  | cons d ds =>
    cases d with
    | zero => exact (Nat.lt_irrefl 0 (hp _ List.mem_cons_self)).elim
    | succ d =>
      cases k with
      | zero => cases he
      | succ k =>
        obtain ⟨ha,he'⟩ := List.cons.inj he
        have had : r = d := Event.architect.inj ha
        subst r
        cases k with
        | zero =>
          exact ⟨ds,Nat.succ.inj hd,fun n hn => hp _ (List.mem_cons_of_mem _ hn),
            List.cons.inj he' |>.2⟩
        | succ => cases he'

private theorem hasRemainingCut {b l : ℕ} {s : List Event} (h : Remaining b l s)
    (hn : 0 < b+l) : Event.cut ∈ s := by
  obtain ⟨ds,hd,hp,rfl⟩ := h
  cases l with
  | succ l => exact List.mem_append_left _ List.mem_cons_self
  | zero =>
    cases ds with
    | nil => simp_all
    | cons d ds =>
      have hpos := hp d List.mem_cons_self
      cases d with
      | zero => cases hpos
      | succ d => exact List.mem_cons_of_mem _ (List.mem_append_left _ List.mem_cons_self)

private theorem coneNonempty (g : ℕ → ℕ) (i : ℕ) : (stageCone g i).Nonempty := by
  cases he : (stageTable g Script.tree i).slot i with
  | inl x => exact ⟨x,i,.refl,he⟩
  | inr p =>
    obtain ⟨j,x,hj,hx⟩ := finalDescendant g Script.tree p i he
    exact ⟨x,j,hj.to_reflTransGen,hx⟩

private def SlotBudget (g : ℕ → ℕ) (i b l : ℕ) :=
  ∀ j x, Relation.ReflTransGen SlotChild i j →
    (stageTable g Script.tree j).slot j = .inl x →
    ∀ tail, branchTrace g Script.tree j = branchTrace g Script.tree i ++ tail →
      Remaining b l (tail.filter control)

private theorem childBudgetStep (g : ℕ → ℕ) {i b l : ℕ} (hc : SlotBudget g i b l)
    (hn : 0 < b+l) (t : ℕ) (hi : (Nat.unpair t).1 = i) :
    (∃ u, branchTrace g Script.tree (t+1) = u ++ [.cut]) ∧
    ∃ k, ∀ j x, Relation.ReflTransGen SlotChild (t+1) j →
      (stageTable g Script.tree j).slot j = .inl x →
      ∀ tail, branchTrace g Script.tree j = branchTrace g Script.tree (t+1) ++ tail →
        Remaining b l (List.replicate k (.architect ((stageTable g Script.tree t).bound+1)) ++
          .cut :: tail.filter control) := by
  have edge : SlotChild i (t+1) := ⟨t,rfl,hi⟩
  have ht : branchTrace g Script.tree (t+1) =
      branchTrace g Script.tree i ++ (stageBatch g Script.tree t).events := by rw [branchTrace,hi]
  obtain ⟨k,hk⟩ := stageControl g t
  have hend := stageBatchEnd g Script.tree t
  cases he : (stageBatch g Script.tree t).result with
  | inl x =>
    have hh := hasRemainingCut (hc _ x (.single edge) ((newSlot ..).trans he) _ ht) hn
    rw [hk,he] at hh
    simp [endSignal] at hh
  | inr p =>
    rw [he] at hend hk
    obtain ⟨u,hu,_⟩ := hend
    refine ⟨⟨branchTrace g Script.tree i ++ u,by rw [ht,hu,List.append_assoc]⟩,k,?_⟩
    intro j x hj hx tail htail
    rw [ht,List.append_assoc] at htail
    have hb := hc j x (hj.head edge) hx _ htail
    simpa only [List.filter_append,hk,endSignal,List.append_assoc,List.singleton_append] using hb

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Ordinal

private theorem coneChild (g : ℕ → ℕ) {i t : ℕ} (hp : (Nat.unpair t).1 = i) :
    stageCone g (t+1) ⊆ stageCone g i := by
  rintro x ⟨j,hj,he⟩
  exact ⟨j,hj.head ⟨t,rfl,hp⟩,he⟩

private theorem freeStageCone (g : ℕ → ℕ) (hg : StrictMono g) :
    ∀ (b l i : ℕ), (∃ u, branchTrace g Script.tree i = u ++ [.cut]) → SlotBudget g i b l →
      FreeCompletions b l (stageCone g i)
  | 0, 0, i, _, _ => by rw [FreeCompletions]; exact coneNonempty g i
  | b+1, 0, i, _, hc => by
    rw [FreeCompletions]
    intro k
    let t := Nat.pair i k
    have hp : (Nat.unpair t).1 = i := by simp [t]
    have hle : k ≤ t := by simpa [t] using Nat.unpair_right_le (Nat.pair i k)
    obtain ⟨endCut,_,hb⟩ := childBudgetStep g hc (by omega) t hp
    let r := (stageTable g Script.tree t).bound + 1
    refine ⟨r,hle.trans ((stageBoundMono g Script.tree).id_le t) |>.trans (Nat.le_succ _),
      stageCone g (t+1),coneChild g hp,freeStageCone g hg b r _ endCut ?_⟩
    exact fun j x hj hx tail ht => blockStep (hb j x hj hx tail ht)
  | b, l+1, i, ⟨u,hu⟩, hc => by
    rw [FreeCompletions]
    let t (n : ℕ) := Nat.pair i n
    have hp (n : ℕ) : (Nat.unpair (t n)).1 = i := by simp [t]
    refine ⟨fun n => stageCone g (t n+1),fun n => coneChild g (hp n),?_,?_⟩
    · intro n m hnm x hx y hy
      exact orderedStageChildren g hg i u hu (Nat.pair_lt_pair_right i hnm) (hp n) (hp m) hx hy
    · intro n
      obtain ⟨endCut,_,hb⟩ := childBudgetStep g hc (by omega) (t n) (hp n)
      exact freeStageCone g hg b l _ endCut (fun j x hj hx tail ht => leafStep (hb j x hj hx tail ht))
termination_by b l _ _ _ => (b,l)

private theorem initialStageBudget (g : ℕ → ℕ) (hg : StrictMono g) (k : ℕ) :
    let t := Nat.pair 0 k
    let b := (stageTable g Script.tree t).bound
    (∃ u, branchTrace g Script.tree (t+1) = u ++ [.cut]) ∧ SlotBudget g (t+1) b (b+1) := by
  let t := Nat.pair 0 k
  let b := (stageTable g Script.tree t).bound
  let r := b+1
  have hp : (Nat.unpair t).1 = 0 := by simp [t]
  have hbatch : stageBatch g Script.tree t = nextBatch g r Script.tree r :=
    stageBatchAtPair g Script.tree 0 k Script.tree rfl
  have hbranch : branchTrace g Script.tree (t+1) = (stageBatch g Script.tree t).events := by
    rw [branchTrace,hp,branchTrace,List.nil_append]
  obtain ⟨a,ha⟩ := batchControl g r (Script.node r Script.block) (advance r r)
  have batchSig : (stageBatch g Script.tree t).events.filter control =
      .architect r :: (List.replicate a (.architect r) ++ endSignal (stageBatch g Script.tree t).result) := by
    rw [hbatch]
    exact congrArg (List.cons (.architect r)) ha
  have afterRoot (j : ℕ) (x : Tree) (hx : (stageTable g Script.tree j).slot j = .inl x)
      (tail : List Event) (ht : branchTrace g Script.tree j = branchTrace g Script.tree (t+1) ++ tail) :
      Remaining r 0 ((List.replicate a (.architect r) ++ endSignal (stageBatch g Script.tree t).result) ++
        tail.filter control) := by
    obtain ⟨ds,hpos,_,he⟩ := finalStageShape g hg j x hx
    have hcontrol : (fun e : Event => e.number.isNone) = control := by funext e; cases e <;> rfl
    rw [hcontrol,ht,hbranch,List.filter_append,batchSig,List.cons_append] at he
    obtain ⟨hr,hs⟩ := List.cons.inj he
    exact ⟨ds,(Event.architect.inj hr).symm,hpos,hs⟩
  have hend := stageBatchEnd g Script.tree t
  cases he : (stageBatch g Script.tree t).result with
  | inl x =>
    have hh := hasRemainingCut (afterRoot (t+1) x ((newSlot ..).trans he) [] (by simp))
      (Nat.zero_lt_succ b)
    simp [he,endSignal] at hh
  | inr p =>
    rw [he] at hend
    obtain ⟨u,hu,_⟩ := hend
    refine ⟨⟨u,hbranch.trans hu⟩,?_⟩
    intro j x _ hx tail ht
    have hs := afterRoot j x hx tail ht
    rw [he] at hs
    apply blockStep (k := a)
    simpa only [endSignal,List.append_assoc,List.singleton_append] using hs

theorem stagedWordsOrderType (g : ℕ → ℕ) (hg : StrictMono g) :
    typeLT (stagedWords g) = (ω : Ordinal.{0}) ^ ω ^ 2 := by
  apply le_antisymm ((monoBound (f := (Subtype.val : stagedWords g → Tree)) (fun _ _ h => h)).trans
    heightTwoOrderType.le)
  rw [sq,opow_mul]
  apply (leOmegaPower (one_lt_opow.mpr ⟨one_lt_omega0,omega0_ne_zero⟩)).mpr
  intro k
  let t := Nat.pair 0 k
  let b := (stageTable g Script.tree t).bound
  have hle : k ≤ t := by simpa [t] using Nat.unpair_right_le (Nat.pair 0 k)
  have hb : k ≤ b := hle.trans ((stageBoundMono g Script.tree).id_le t)
  obtain ⟨hend,hbudget⟩ := initialStageBudget g hg k
  have hfree := freeStageCone g hg b (b+1) (t+1) hend hbudget
  have hbound := freeCompletionsBound b (b+1) _ hfree
  have hsub : stageCone g (t+1) ⊆ stagedWords g := by
    rintro x ⟨j,_,hj⟩
    exact ⟨j,hj⟩
  refine le_trans ?_ (hbound.trans (monoBound (f := Set.inclusion hsub) (fun _ _ h => h)))
  calc ((ω : Ordinal.{0}) ^ (ω : Ordinal)) ^ k ≤ (ω ^ (ω : Ordinal)) ^ b := by
         rw [← opow_natCast,← opow_natCast]
         exact opow_le_opow_right (opow_pos _ omega0_pos) (Nat.cast_le.mpr hb)
       _ ≤ _ := by
         conv_lhs => rw [← mul_one ((ω ^ (ω : Ordinal)) ^ b)]
         exact (isNormal_mul_right (pow_pos (opow_pos _ omega0_pos) b)).monotone
           (Order.one_le_iff_pos.mpr (pow_pos omega0_pos (b+1)))

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

-- Splitting before an ordinary event never separates a marked leaf from
-- its switch. This permits coarsening each chronological run separately.
theorem LeafMask.splitAt {k : ℕ → Bool} {s t : List Event} (h : LeafMask k s t)
    (p q : List Event) (ht : t = p ++ q) (hq : ∀ u, q ≠ .cut :: u) :
    ∃ a b, s = a ++ b ∧ LeafMask k a p ∧ LeafMask k b q := by
  induction h generalizing p with
  | nil =>
    obtain ⟨rfl,rfl⟩ := List.append_eq_nil_iff.mp ht.symm
    exact ⟨[],[],rfl,.nil,.nil⟩
  | dropBuilder x h ih =>
    cases p with
    | nil =>
      simp only [List.nil_append] at ht
      subst q
      exact ⟨[],_,rfl,.nil,LeafMask.dropBuilder x h⟩
    | cons e p =>
      obtain ⟨rfl,htail⟩ := List.cons.inj ht
      obtain ⟨a,b,rfl,ha,hb⟩ := ih p htail
      exact ⟨a,b,rfl,.dropBuilder x ha,hb⟩
  | dropArchitect x h ih =>
    cases p with
    | nil =>
      simp only [List.nil_append] at ht
      subst q
      exact ⟨[],_,rfl,.nil,LeafMask.dropArchitect x h⟩
    | cons e p =>
      obtain ⟨rfl,htail⟩ := List.cons.inj ht
      obtain ⟨a,b,rfl,ha,hb⟩ := ih p htail
      exact ⟨a,b,rfl,.dropArchitect x ha,hb⟩
  | builder x h ih =>
    cases p with
    | nil =>
      simp only [List.nil_append] at ht
      subst q
      exact ⟨[],_,rfl,.nil,LeafMask.builder x h⟩
    | cons e p =>
      obtain ⟨rfl,htail⟩ := List.cons.inj ht
      obtain ⟨a,b,rfl,ha,hb⟩ := ih p htail
      exact ⟨.builder x :: a,b,rfl,.builder x ha,hb⟩
  | architect hab h ih =>
    cases p with
    | nil =>
      simp only [List.nil_append] at ht
      subst q
      exact ⟨[],_,rfl,.nil,LeafMask.architect hab h⟩
    | cons e p =>
      obtain ⟨rfl,htail⟩ := List.cons.inj ht
      obtain ⟨a,b,rfl,ha,hb⟩ := ih p htail
      exact ⟨.architect _ :: a,b,rfl,.architect hab ha,hb⟩
  | leaf x h ih =>
    cases p with
    | nil =>
      simp only [List.nil_append] at ht
      subst q
      exact ⟨[],_,rfl,.nil,LeafMask.leaf x h⟩
    | cons e p =>
      obtain ⟨rfl,htail⟩ := List.cons.inj ht
      cases p with
      | nil => exact (hq _ htail.symm).elim
      | cons e p =>
        obtain ⟨rfl,htail'⟩ := List.cons.inj htail
        obtain ⟨a,b,rfl,ha,hb⟩ := ih p htail'
        exact ⟨.builder x :: (if k x then [.cut] else []) ++ a,b,by simp [List.append_assoc],
          .leaf x ha,hb⟩

theorem LeafMask.noSwitch {k : ℕ → Bool} {s t : List Event} (h : LeafMask k s t)
    (hn : ∀ n ∈ t.filterMap Event.number, k n = false) : Event.cut ∉ s := by
  induction h with
  | nil => exact List.not_mem_nil
  | dropArchitect n _ ih => exact ih hn
  | dropBuilder x _ ih => exact ih (fun n hm => hn _ (List.mem_cons_of_mem x hm))
  | architect hab _ ih => simpa using ih hn
  | builder x _ ih => simpa using ih (fun n hm => hn _ (List.mem_cons_of_mem x hm))
  | leaf x _ ih =>
    have hx := hn x List.mem_cons_self
    simpa [hx] using ih (fun n hm => hn _ (List.mem_cons_of_mem x hm))

private theorem LeafMask.markOnly {k : ℕ → Bool} {s : List Event} {x : ℕ}
    (h : LeafMask k s [.builder x,.cut]) (hx : k x = true) : s = [.builder x,.cut] := by
  cases h with
  | dropBuilder _ h => cases h
  | builder _ h => cases h
  | leaf _ h => cases h; simp [hx]

theorem LeafMask.lastSwitch {k : ℕ → Bool} {s p : List Event} {x : ℕ}
    (h : LeafMask k s (p ++ [.builder x,.cut])) (hx : k x = true)
    (hn : ∀ n ∈ p.filterMap Event.number, k n = false) :
    ∃ a, s = a ++ [.cut] ∧ Event.cut ∉ a ∧ Shrinks a (p ++ [.builder x,.cut]) := by
  obtain ⟨a,b,rfl,ha,hb⟩ := h.splitAt p [.builder x,.cut] rfl (by simp)
  obtain rfl := hb.markOnly hx
  refine ⟨a ++ [.builder x],by simp,by simp [ha.noSwitch hn],?_⟩
  exact ha.shrinks.append (.builder x (.skip .cut .nil))

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

private theorem Weave.flip {c b : Bool} {l r s : List Event} (h : Weave c l r s b) :
    Weave (!c) r l s (!b) := by
  induction h with
  | finishLeft h => exact .finishRight h
  | finishRight h => exact .finishLeft h
  | leftMove he _ ih => exact .rightMove he ih
  | rightMove he _ ih => exact .leftMove he ih
  | leftCut _ ih => exact .rightCut ih
  | rightCut _ ih => exact .leftCut ih

private def sideRuns : List (List Event) → List Event
  | [] => []
  | [p] => p
  | p :: _ :: rs => p ++ sideRuns rs

private def StartsClean (p : List Event) := ∀ u, p ≠ .cut :: u

private theorem startsAppend {a b : List Event} (ha : StartsClean a) (hb : StartsClean b) :
    StartsClean (a ++ b) := by
  cases a with
  | nil => exact hb
  | cons e es =>
    intro u he
    have hh := (List.cons.inj he).1
    exact ha es (hh ▸ rfl)

private theorem startsSide : ∀ (rs : List (List Event)), (∀ p ∈ rs, StartsClean p) →
    StartsClean (sideRuns rs)
  | [], _ => by intro _ h; cases h
  | [p], h => h _ List.mem_cons_self
  | p :: q :: rs, h => startsAppend (h _ List.mem_cons_self) (startsSide rs
      (fun x hx => h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))))

private def RunChoice (k : ℕ → Bool) : List (List Event) → Prop
  | [] => True
  | [p] => ∀ n ∈ p.filterMap Event.number, k n = false
  | [p,q] => (∀ n ∈ p.filterMap Event.number, k n = false) ∧
      ∀ n ∈ q.filterMap Event.number, k n = false
  | p :: q :: r :: rs =>
    (∃ pre x, p = pre ++ [.builder x,.cut] ∧ k x = true ∧
      ∀ n ∈ pre.filterMap Event.number, k n = false) ∧ RunChoice k (q :: r :: rs)

private theorem maskNil {k : ℕ → Bool} {s : List Event} (h : LeafMask k s []) : s = [] := by
  cases h; rfl

private theorem weaveRunChoice (k : ℕ → Bool) (rs : List (List Event)) {l r : List Event}
    (hc : RunChoice k rs) (heads : ∀ p ∈ rs, StartsClean p)
    (hl : LeafMask k l (sideRuns rs)) (hr : LeafMask k r (sideRuns rs.tail)) :
    ∃ s b, Weave true l r s b ∧ Shrinks s rs.flatten := by
  induction rs generalizing l r with
  | nil =>
    obtain rfl := maskNil hl
    obtain rfl := maskNil hr
    exact ⟨[],false,.finishLeft (by simp),.nil⟩
  | cons p rs ih =>
    cases rs with
    | nil =>
      obtain rfl := maskNil hr
      refine ⟨l,false,?_,?_⟩
      · simpa using (movesBeforeWeave l (hl.noSwitch hc)).1
          (.finishLeft List.not_mem_nil : Weave true [] [] [] false)
      · simpa [sideRuns] using hl.shrinks
    | cons q rest =>
      cases rest with
      | nil =>
        change LeafMask k l (p ++ []) at hl
        rw [List.append_nil] at hl
        change LeafMask k r q at hr
        refine ⟨l++r,false,?_,by simpa using hl.shrinks.append hr.shrinks⟩
        simpa using (movesBeforeWeave l (hl.noSwitch hc.1)).1 (.finishLeft (hr.noSwitch hc.2))
      | cons z rs =>
        have htail := fun x hx => heads x (List.mem_cons_of_mem p hx)
        have hhead := startsSide (z :: rs) (fun x hx => htail x (List.mem_cons_of_mem q hx))
        obtain ⟨a,b,rfl,ha,hb⟩ := hl.splitAt p (sideRuns (z::rs)) rfl hhead
        obtain ⟨⟨pre,x,rfl,hx,hn⟩,hrest⟩ := hc
        obtain ⟨a',rfl,hac,hsh⟩ := ha.lastSwitch hx hn
        obtain ⟨s,c,hw,hshr⟩ := ih hrest htail hr hb
        refine ⟨a'++s,!c,?_,hsh.append hshr⟩
        simpa only [List.append_assoc,List.singleton_append] using
          (movesBeforeWeave a' hac).1 (.leftCut hw.flip)

private def HasRunEnds : List (List Event) → Prop
  | p :: q :: r :: rs => (∃ pre, ∃ x : ℕ, p = pre ++ [.builder x,.cut]) ∧ HasRunEnds (q :: r :: rs)
  | _ => True

private theorem runChoiceCongr {k f : ℕ → Bool} (rs : List (List Event)) (h : RunChoice k rs)
    (he : ∀ n ∈ rs.flatten.filterMap Event.number, f n = k n) : RunChoice f rs := by
  induction rs with
  | nil => trivial
  | cons p rs ih =>
    have hp (n : ℕ) (hn : n ∈ p.filterMap Event.number) := he n (by rw [List.flatten_cons,List.filterMap_append]; exact List.mem_append_left _ hn)
    have hr (n : ℕ) (hn : n ∈ rs.flatten.filterMap Event.number) := he n (by rw [List.flatten_cons,List.filterMap_append]; exact List.mem_append_right _ hn)
    cases rs with
    | nil => exact fun n hn => (hp n hn).trans (h n hn)
    | cons q rs =>
      cases rs with
      | nil =>
        refine ⟨fun n hn => (hp n hn).trans (h.1 n hn),fun n hn => ?_⟩
        exact (hr n (by simpa using hn)).trans (h.2 n hn)
      | cons z rs =>
        obtain ⟨⟨pre,x,rfl,hx,hn⟩,hc⟩ := h
        refine ⟨⟨pre,x,rfl,(hp x (by simp [Event.number])).trans hx,?_⟩,ih hc hr⟩
        intro n hm
        exact (hp n (by simp [hm])).trans (hn n hm)

private theorem chooseRunCuts (rs : List (List Event)) (good : HasRunEnds rs)
    (sorted : (rs.flatten.filterMap Event.number).Pairwise (· < ·)) : ∃ k, RunChoice k rs := by
  induction rs with
  | nil => exact ⟨fun _ => false,trivial⟩
  | cons p rs ih =>
    cases rs with
    | nil => exact ⟨fun _ => false,fun _ _ => rfl⟩
    | cons q rs =>
      cases rs with
      | nil => exact ⟨fun _ => false,fun _ _ => rfl,fun _ _ => rfl⟩
      | cons z rs =>
        obtain ⟨⟨pre,x,rfl⟩,hrest⟩ := good
        let r := q :: z :: rs
        have hs : ((pre.filterMap Event.number ++ [x]) ++ r.flatten.filterMap Event.number).Pairwise (· < ·) := by
          simpa only [r,List.flatten_cons,List.filterMap_append,List.filterMap_cons,Event.number,List.filterMap_nil] using sorted
        obtain ⟨hp,ht,hcross⟩ := List.pairwise_append.mp hs
        obtain ⟨k,hk⟩ := ih hrest ht
        let f (n : ℕ) := if n ≤ x then decide (n = x) else k n
        refine ⟨f,⟨pre,x,rfl,by simp [f],?_⟩,runChoiceCongr r hk ?_⟩
        · intro n hn
          have hl := (List.pairwise_append.mp hp).2.2 n hn x (by simp)
          simp [f,hl.le,hl.ne]
        · intro n hn
          have hl := hcross x (by simp) n hn
          simp [f,hl.not_ge]

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

private def CellEnds (s : List Event) := ∃ pre, ∃ x : ℕ, s = pre ++ [.builder x,.cut]

private theorem prefixEnd {s : List Event} (h : CellEnds s) (p : List Event) : CellEnds (p ++ s) := by
  obtain ⟨pre,x,rfl⟩ := h
  exact ⟨p++pre,x,(List.append_assoc ..).symm⟩

private theorem prefixRunEnds (p q r : List Event) (rs : List (List Event))
    (h : HasRunEnds (q :: r :: rs)) : HasRunEnds ((p++q) :: r :: rs) := by
  cases rs with
  | nil => trivial
  | cons z zs => exact ⟨prefixEnd h.1 p,h.2⟩

private structure CellChain (ev : ℕ → List Event) (ts : List ℕ) : Prop where
  sorted : ts.Pairwise (· < ·)
  start : ∀ i ∈ ts, StartsClean (ev i)
  ends : ∀ i ∈ ts, ∀ j ∈ ts, i < j → CellEnds (ev i)

private theorem CellChain.tail {ev : ℕ → List Event} {i : ℕ} {ts : List ℕ}
    (h : CellChain ev (i::ts)) : CellChain ev ts :=
  ⟨(List.pairwise_cons.mp h.sorted).2,fun j hj => h.start j (List.mem_cons_of_mem _ hj),
    fun j hj k hk => h.ends j (List.mem_cons_of_mem _ hj) k (List.mem_cons_of_mem _ hk)⟩

private theorem startsChain {ev : ℕ → List Event} {ts : List ℕ} (h : CellChain ev ts) :
    StartsClean (ts.flatMap ev) := by
  induction ts with
  | nil => intro u e; cases e
  | cons i ts ih => exact startsAppend (h.start i List.mem_cons_self) (ih h.tail)

private structure RunMerge (ev : ℕ → List Event) (l r : List ℕ) where
  first : List Event
  second : List Event
  rest : List (List Event)
  times : List ℕ
  ordered : times.Pairwise (· < ·)
  member : ∀ i ∈ times, i ∈ l ∨ i ∈ r
  left : sideRuns (first::second::rest) = l.flatMap ev
  right : sideRuns (second::rest) = r.flatMap ev
  trace : (first::second::rest).flatten = times.flatMap ev
  starts : ∀ p ∈ first::second::rest, StartsClean p
  ends : HasRunEnds (first::second::rest)

private theorem beforeTimes {ev : ℕ → List Event} {i j : ℕ} {l r : List ℕ}
    (hl : CellChain ev (i::l)) (hr : CellChain ev (j::r)) (hij : i < j)
    {n : ℕ} (hn : n ∈ l ∨ n ∈ j::r) : i < n := by
  rcases hn with h | h
  · exact (List.pairwise_cons.mp hl.sorted).1 n h
  · rcases List.mem_cons.mp h with rfl | h
    · exact hij
    · exact hij.trans ((List.pairwise_cons.mp hr.sorted).1 _ h)

private theorem mergeStages (ev : ℕ → List Event) (i j : ℕ) (l r : List ℕ)
    (hl : CellChain ev (i::l)) (hr : CellChain ev (j::r))
    (apart : ∀ n ∈ i::l, n ∉ j::r) (hij : i < j) :
    Nonempty (RunMerge ev (i::l) (j::r)) := by
  have hi := hl.start i List.mem_cons_self
  cases hls : l with
  | nil =>
    refine ⟨⟨ev i,(j::r).flatMap ev,[],i::j::r,
      List.pairwise_cons.mpr ⟨fun n hn => beforeTimes hl hr hij (.inr hn),hr.sorted⟩,
      ?_,by simp [sideRuns],rfl,by simp,?_,trivial⟩⟩
    · intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact .inl List.mem_cons_self
      · exact .inr hn
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hi
      · exact List.mem_singleton.mp hp ▸ startsChain hr
  | cons k ks =>
    rw [hls] at hl apart
    have hik := (List.pairwise_cons.mp hl.sorted).1 k List.mem_cons_self
    have dis (n : ℕ) (hn : n ∈ k::ks) := apart n (List.mem_cons_of_mem i hn)
    rcases lt_trichotomy k j with hkj | rfl | hjk
    · obtain ⟨M⟩ := mergeStages ev k j ks r hl.tail hr dis hkj
      refine ⟨⟨ev i ++ M.first,M.second,M.rest,i::M.times,
        List.pairwise_cons.mpr ⟨fun n hn => beforeTimes hl hr hij (M.member n hn),M.ordered⟩,
        ?_,?_,M.right,?_,?_,prefixRunEnds _ _ _ _ M.ends⟩⟩
      · intro n hn
        rcases List.mem_cons.mp hn with rfl | hn
        · exact .inl List.mem_cons_self
        · exact (M.member n hn).imp (List.mem_cons_of_mem _) id
      · change (ev i ++ M.first) ++ sideRuns M.rest = ev i ++ _
        rw [List.append_assoc]
        exact congrArg (ev i ++ ·) M.left
      · change (ev i ++ M.first) ++ (M.second :: M.rest).flatten = ev i ++ _
        rw [List.append_assoc]
        exact congrArg (ev i ++ ·) M.trace
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact startsAppend hi (M.starts _ List.mem_cons_self)
        · exact M.starts _ (List.mem_cons_of_mem _ hp)
    · exact (dis _ List.mem_cons_self List.mem_cons_self).elim
    · obtain ⟨M⟩ := mergeStages ev j k r ks hr hl.tail (fun n hn hn' => dis n hn' hn) hjk
      refine ⟨⟨ev i,M.first,M.second::M.rest,i::M.times,
        List.pairwise_cons.mpr ⟨fun n hn => beforeTimes hl hr hij (M.member n hn).symm,M.ordered⟩,
        ?_,?_,M.left,congrArg (ev i ++ ·) M.trace,?_,
        ⟨hl.ends _ List.mem_cons_self _ (List.mem_cons_of_mem _ List.mem_cons_self) hik,M.ends⟩⟩⟩
      · intro n hn
        rcases List.mem_cons.mp hn with rfl | hn
        · exact .inl List.mem_cons_self
        · exact (M.member n hn).symm.imp (List.mem_cons_of_mem _) id
      · exact congrArg (ev i ++ ·) M.right
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hi
        · exact M.starts _ hp
termination_by l.length + r.length
decreasing_by all_goals simp only [hls,List.length_cons]; omega

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

private def slotTimes : ℕ → List ℕ
  | 0 => []
  | t+1 => slotTimes (Nat.unpair t).1 ++ [t]
termination_by t => t
decreasing_by exact Nat.lt_succ_of_le (Nat.unpair_left_le _)

private theorem memSlotTimes {i t : ℕ} (h : t ∈ slotTimes i) :
    t < i ∧ Relation.ReflTransGen SlotChild (t+1) i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero => simp [slotTimes] at h
    | succ k =>
      rw [slotTimes,List.mem_append] at h
      obtain h | h := h
      · obtain ⟨hlt,ha⟩ := ih _ (Nat.lt_succ_of_le (Nat.unpair_left_le k)) h
        exact ⟨hlt.trans (Nat.lt_succ_of_le (Nat.unpair_left_le k)),ha.tail ⟨k,rfl,rfl⟩⟩
      · obtain rfl := List.mem_singleton.mp h
        exact ⟨Nat.lt_succ_self _,.refl⟩

private theorem timesSorted (i : ℕ) : (slotTimes i).Pairwise (· < ·) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero => simp [slotTimes]
    | succ t =>
      rw [slotTimes,List.pairwise_append]
      exact ⟨ih _ (Nat.lt_succ_of_le (Nat.unpair_left_le t)),by simp,fun j hj k hk =>
        List.mem_singleton.mp hk ▸ (memSlotTimes hj).1.trans_le (Nat.unpair_left_le t)⟩

private def firstStage : ℕ → ℕ
  | 0 => 0
  | t+1 => if (Nat.unpair t).1 = 0 then t else firstStage (Nat.unpair t).1
termination_by t => t
decreasing_by exact Nat.lt_succ_of_le (Nat.unpair_left_le _)

private theorem firstStageSpec {i : ℕ} (hi : i ≠ 0) :
    (Nat.unpair (firstStage i)).1 = 0 ∧ ∃ rest, slotTimes i = firstStage i :: rest := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero => contradiction
    | succ t =>
      rw [firstStage,slotTimes]
      split
      next he => exact ⟨he,[],by rw [he,slotTimes]; rfl⟩
      next he =>
        obtain ⟨hp,rs,hr⟩ := ih _ (Nat.lt_succ_of_le (Nat.unpair_left_le t)) he
        exact ⟨hp,rs++[t],by rw [hr]; rfl⟩

private theorem sameFirstStage {i t : ℕ} (h : t ∈ slotTimes i) : firstStage (t+1) = firstStage i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero => simp [slotTimes] at h
    | succ k =>
      rw [slotTimes,List.mem_append] at h
      obtain h | h := h
      · have hp : (Nat.unpair k).1 ≠ 0 := by rintro e; simp [e,slotTimes] at h
        conv_rhs => rw [firstStage,if_neg hp]
        exact ih _ (Nat.lt_succ_of_le (Nat.unpair_left_le k)) h
      · rw [List.mem_singleton.mp h]

private theorem branchFromTimes (g : ℕ → ℕ) (i : ℕ) :
    branchTrace g Script.tree i = (slotTimes i).flatMap (fun t => (stageBatch g Script.tree t).events) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero => simp [branchTrace,slotTimes]
    | succ t =>
      rw [slotTimes,branchTrace,ih _ (Nat.lt_succ_of_le (Nat.unpair_left_le t))]
      simp

private theorem stageFromRange (g : ℕ → ℕ) (i : ℕ) :
    stageTrace g Script.tree i = (List.range i).flatMap (fun t => (stageBatch g Script.tree t).events) := by
  induction i with
  | zero => rfl
  | succ t ih => simp [stageTrace,ih,List.range_succ]

private theorem inheritFinal {A : Type} (g : ℕ → ℕ) (root : Script A) {i j : ℕ} {x : A}
    (h : Relation.ReflTransGen SlotChild i j) (hx : (stageTable g root i).slot i = .inl x) :
    (stageTable g root j).slot j = .inl x := by
  induction h with
  | refl => exact hx
  | tail h hc ih =>
    obtain ⟨t,rfl,rfl⟩ := hc
    rw [newSlot]
    simp only [stageBatch,StageTable.batch,(stableSlot g root (Nat.unpair_left_le t)).trans ih]

private def afterBuilder (prev : Bool) : List Event → Prop
  | [] => True
  | .builder _ :: s => afterBuilder true s
  | .architect _ :: s => afterBuilder false s
  | .cut :: s => prev = true ∧ afterBuilder false s

private theorem maskAfterBuilder {k : ℕ → Bool} {s t : List Event} (h : LeafMask k s t) (p : Bool) :
    afterBuilder p t := by
  induction h generalizing p with
  | nil => trivial
  | builder _ _ ih | dropBuilder _ _ ih => exact ih true
  | architect _ _ ih | dropArchitect _ _ ih => exact ih false
  | leaf _ _ ih => exact ⟨rfl,ih false⟩

private theorem afterBuilderPrefix (p s : List Event) (b : Bool) (h : afterBuilder b (p++s)) :
    afterBuilder b p := by
  induction p generalizing b with
  | nil => trivial
  | cons e p ih =>
    cases e with
    | cut => exact ⟨h.1,ih _ h.2⟩
    | builder | architect => exact ih _ h

private theorem afterCutTail (p s : List Event) (b : Bool) (h : afterBuilder b (p ++ .cut :: s)) :
    afterBuilder false s := by
  induction p generalizing b with
  | nil => exact h.2
  | cons e p ih =>
    cases e with
    | cut => exact ih _ h.2
    | builder | architect => exact ih _ h

private theorem endAfterBuilder (p : List Event) (h : afterBuilder false (p ++ [.cut])) :
    CellEnds (p ++ [.cut]) := by
  cases p using List.reverseRecOn with
  | nil => exact Bool.noConfusion h.1
  | append_singleton pre e =>
    have aux (l : List Event) (b : Bool) (h : afterBuilder b (l ++ [e,.cut])) :
        ∃ n, e = .builder n := by
      induction l generalizing b with
      | nil =>
        cases e with
        | builder n => exact ⟨n,rfl⟩
        | architect => exact Bool.noConfusion h.1
        | cut => exact Bool.noConfusion h.2.1
      | cons a l ih =>
        cases a with
        | cut => exact ih _ h.2
        | builder | architect => exact ih _ h
    obtain ⟨x,rfl⟩ := aux pre false (by simpa only [List.append_assoc,List.singleton_append] using h)
    exact ⟨pre,x,List.append_assoc ..⟩

private theorem minimalCellChain (g : ℕ → ℕ) (hg : StrictMono g) (j : ℕ) (x : Tree)
    (hj : (stageTable g Script.tree j).slot j = .inl x)
    (minj : ∀ k < j, (stageTable g Script.tree k).slot k ≠ .inl x) :
    CellChain (fun t => (stageBatch g Script.tree t).events) (slotTimes j) := by
  have pending {i : ℕ} (hi : i < j) (ha : Relation.ReflTransGen SlotChild i j) :
      ∃ p, (stageTable g Script.tree i).slot i = .inr p := by
    cases he : (stageTable g Script.tree i).slot i with
    | inr p => exact ⟨p,rfl⟩
    | inl y =>
      have hy := Sum.inl.inj ((inheritFinal g Script.tree ha he).symm.trans hj)
      subst y
      exact (minj i hi he).elim
  have proper (t : ℕ) (ht : t ∈ slotTimes j) :
      afterBuilder false (stageBatch g Script.tree t).events := by
    obtain ⟨bs,_,hb,_⟩ := finalCanonicalDecoration g hg j x hj
    obtain ⟨_,_,_,hm⟩ := coarsenByLeafValue (fun _ => true) bs
    have hall := maskAfterBuilder hm false
    rw [hb] at hall
    obtain ⟨w,hw⟩ := finalPrefix g Script.tree (memSlotTimes ht).2
    rw [hw,branchTrace,List.append_assoc] at hall
    apply afterBuilderPrefix _ w false
    let i := (Nat.unpair t).1
    by_cases hi : i = 0
    · simpa only [show (Nat.unpair t).1 = 0 from hi,branchTrace,List.nil_append] using hall
    · obtain ⟨u,hu⟩ := Nat.exists_eq_succ_of_ne_zero hi
      have hle : i ≤ t := Nat.unpair_left_le t
      have ha : SlotChild i (t+1) := ⟨t,rfl,rfl⟩
      obtain ⟨p,hp⟩ := pending (hle.trans_lt (memSlotTimes ht).1) ((memSlotTimes ht).2.head ha)
      rw [hu,newSlot] at hp
      have he := stageBatchEnd g Script.tree u
      rw [hp] at he
      obtain ⟨earlierMoves,he,_⟩ := he
      change afterBuilder false (branchTrace g Script.tree i ++ _) at hall
      rw [hu,branchTrace,he,List.append_assoc,List.append_assoc] at hall
      apply afterCutTail (branchTrace g Script.tree (Nat.unpair u).1 ++ earlierMoves) _ false
      simpa only [List.append_assoc,List.singleton_append] using hall
  refine ⟨timesSorted _,?_,?_⟩
  · intro t ht u he
    have hp := proper t ht
    rw [he] at hp
    exact Bool.noConfusion hp.1
  · intro t ht v hv htv
    have hlt : t+1 < j := (Nat.succ_le_of_lt htv).trans_lt (memSlotTimes hv).1
    obtain ⟨p,hp⟩ := pending hlt (memSlotTimes ht).2
    rw [newSlot] at hp
    have he := stageBatchEnd g Script.tree t
    rw [hp] at he
    obtain ⟨u,hu,_⟩ := he
    have h := proper t ht
    rw [hu] at h ⊢
    exact endAfterBuilder u h

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

private theorem firstStageArity (g : ℕ → ℕ) (hg : StrictMono g) (j : ℕ) (x : Tree)
    (hj : (stageTable g Script.tree j).slot j = .inl x) :
    let ev := (stageBatch g Script.tree (firstStage j)).events
    (readWordLabels true 0 ev).head? = some x.len ∧ x.len ∈ ev.filterMap Event.number := by
  have hne : j ≠ 0 := by rintro rfl; cases hj
  let t := firstStage j
  obtain ⟨hp,rs,hrs⟩ := firstStageSpec hne
  have heq : Nat.pair 0 (Nat.unpair t).2 = t := by simpa only [t,hp] using Nat.pair_unpair t
  obtain ⟨⟨u,hu⟩,_⟩ := initialStageBudget g hg (Nat.unpair t).2
  rw [heq,branchTrace,show (Nat.unpair t).1 = 0 from hp,branchTrace,List.nil_append] at hu
  let chunk := (stageBatch g Script.tree t).events
  have hcut : Event.cut ∈ chunk := by change _ ∈ (stageBatch g Script.tree t).events; rw [hu]; simp
  have hc : List.IsPrefix chunk (branchTrace g Script.tree j) := by
    rw [branchFromTimes,hrs]
    exact List.prefix_append _ _
  obtain ⟨bs,hx,hb,_⟩ := finalCanonicalDecoration g hg j x hj
  let m := activeBlocks 1 bs
  let header : List Event := .architect m.length :: m.map Event.builder ++ [.builder bs.length]
  have hhead : List.IsPrefix header (branchTrace g Script.tree j) := by
    rw [← hb]
    refine ⟨indexedMoves (fun _ b => b.moves) 1 bs,?_⟩
    simp [header,m,MarkedTree.moves,decorate,nodeMoves,List.append_assoc]
  have hnc : Event.cut ∉ header := by simp [header]
  obtain hh | hh := List.prefix_or_prefix_of_prefix hhead hc
  · obtain ⟨v,hv⟩ := hh
    change (readWordLabels true 0 chunk).head? = some x.len ∧ x.len ∈ chunk.filterMap Event.number
    rw [← hv,← hx]
    simp only [header,List.cons_append,List.append_assoc,readWordLabels,
      if_true,readIndexLabels,List.head?_cons,MarkedTree.word,decorate]
    simp [Event.number]
    exact ⟨.builder bs.length,Or.inr (Or.inl rfl),rfl⟩
  · exact (hnc (hh.sublist.subset hcut)).elim

private theorem orderedRoots (g : ℕ → ℕ) (hg : StrictMono g) {i j : ℕ} {x y : Tree}
    (hx : (stageTable g Script.tree i).slot i = .inl x)
    (hy : (stageTable g Script.tree j).slot j = .inl y) (hxy : x.len < y.len) :
    firstStage i < firstStage j := by
  obtain ⟨ha,hm⟩ := firstStageArity g hg i x hx
  obtain ⟨hb,hn⟩ := firstStageArity g hg j y hy
  rcases lt_trichotomy (firstStage i) (firstStage j) with h | h | h
  · exact h
  · rw [h] at ha
    exact (hxy.ne (Option.some.inj (ha.symm.trans hb))).elim
  · have hs := (stageInterval g hg Script.tree hn).2
    have ht := (stageInterval g hg Script.tree hm).1
    exact (hxy.asymm ((hs.trans ((stageBoundMono g Script.tree).monotone h)).trans_lt ht)).elim

private theorem Shrinks.ofRightSublist {s u v : List Event} (h : Shrinks s u) (hu : u.Sublist v) :
    Shrinks s v := by
  induction hu generalizing s with
  | slnil => exact h
  | cons e _ ih => exact .skip e (ih h)
  | cons_cons e _ ih =>
    cases h with
    | skip e h => exact .skip e (ih h)
    | cut h => exact .cut (ih h)
    | builder x h => exact .builder x (ih h)
    | architect hab h => exact .architect hab (ih h)

private theorem stagePair (g : ℕ → ℕ) (hg : StrictMono g) {x y : Tree}
    (hx : x ∈ stagedWords g) (hy : y ∈ stagedWords g) (hxy : x.len < y.len) :
    ∃ (t u : MarkedTree) (s : List Event) (b : Bool), t.word = x ∧ u.word = y ∧
      t.consistent ∧ u.consistent ∧ Weave true t.moves u.moves s b ∧
      (0 :: s.filterMap Event.number).Pairwise (· < ·) ∧ Spaced g [] s := by
  classical
  let i := Nat.find hx
  let j := Nat.find hy
  have hi : (stageTable g Script.tree i).slot i = .inl x := Nat.find_spec hx
  have hj : (stageTable g Script.tree j).slot j = .inl y := Nat.find_spec hy
  have hl := minimalCellChain g hg i x hi (fun k hk => Nat.find_min hx hk)
  have hr := minimalCellChain g hg j y hj (fun k hk => Nat.find_min hy hk)
  have hab := orderedRoots g hg hi hj hxy
  have dis (n : ℕ) (hn : n ∈ slotTimes i) (hm : n ∈ slotTimes j) :=
    hab.ne ((sameFirstStage hn).symm.trans (sameFirstStage hm))
  obtain ⟨_,l,he⟩ := firstStageSpec (i := i) (by rintro e; rw [e] at hi; cases hi)
  obtain ⟨_,r,hf⟩ := firstStageSpec (i := j) (by rintro e; rw [e] at hj; cases hj)
  rw [he] at hl dis
  rw [hf] at hr dis
  let ev (t : ℕ) := (stageBatch g Script.tree t).events
  obtain ⟨M⟩ := mergeStages ev _ _ l r hl hr dis hab
  let rs := M.first :: M.second :: M.rest
  let cap := max i j
  have htime : M.times.Sublist (List.range cap) := by
    apply List.sublist_of_subperm_of_pairwise _ M.ordered List.pairwise_lt_range
    apply List.subperm_of_subset M.ordered.nodup
    intro n hn
    have ht := M.member n hn
    rw [← he,← hf] at ht
    exact List.mem_range.mpr (ht.elim (fun h => (memSlotTimes h).1.trans_le (le_max_left _ _))
      (fun h => (memSlotTimes h).1.trans_le (le_max_right _ _)))
  have htrace : rs.flatten.Sublist (stageTrace g Script.tree cap) := by
    rw [stageFromRange]
    change (M.first :: M.second :: M.rest).flatten.Sublist _
    rw [M.trace]
    exact htime.flatMap ev
  have sorted := stageTraceIncreasing g hg Script.tree cap [] (by simp)
  rw [List.append_nil] at sorted
  obtain ⟨keep,hkeep⟩ := chooseRunCuts rs M.ends
    ((List.pairwise_cons.mp sorted).2.sublist (shrinksNumbers (shrinksOfSublist htrace)))
  obtain ⟨bs,bx,bt,_⟩ := finalCanonicalDecoration g hg i x hi
  obtain ⟨cs,cy,ct,_⟩ := finalCanonicalDecoration g hg j y hj
  obtain ⟨t,tx,tc,tm⟩ := coarsenByLeafValue keep bs
  obtain ⟨u,uy,uc,um⟩ := coarsenByLeafValue keep cs
  rw [bt,branchFromTimes,he] at tm
  rw [ct,branchFromTimes,hf] at um
  have left : LeafMask keep t.moves (sideRuns rs) := by rw [show sideRuns rs = _ from M.left]; exact tm
  have right : LeafMask keep u.moves (sideRuns rs.tail) := by rw [show sideRuns rs.tail = _ from M.right]; exact um
  obtain ⟨s,b,hw,hs⟩ := weaveRunChoice keep rs hkeep M.starts left right
  have hwhole := hs.ofRightSublist htrace
  exact ⟨t,u,s,b,tx.trans bx,uy.trans cy,tc,uc,hw,spacedStageWeave g hg Script.tree cap hw hwhole⟩

theorem spacedFamilies (g : ℕ → ℕ) (hg : StrictMono g) : SpacedFamily g :=
  ⟨stagedWords g,stagedWordsOrderType g hg,fun _ hx _ hy h => stagePair g hg hx hy h⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Ordinal Script

universe w

theorem ramseyOfPositiveOpening
    (triangle : ∀ (G : SimpleGraph Tree) (f : ℕ → ℕ), StrictMono f →
      ∀ (d : ℕ) (b : Bool),
      ((increasing ((node (d+1) block).interleave tree) 0).score (wins G b)).outcome f true →
        ∃ x y z, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z) :
    OrdinalCardinalRamsey ((ω : Ordinal.{w}) ^ ω ^ 2) (ω ^ ω ^ 2) 3 :=
  ramseyOfConstructions spacedFamilies triangle

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Filter Script

-- Fix the decorations in the local script of each vertex. Cut positions
-- may still depend on earlier Builder values. In an outside play, three
-- such scripts can share their Builder moves one round at a time.
def BuilderScript {A : Type} : Script A → Prop
  | .done _ => True
  | .builder t => ∀ n, BuilderScript (t n)
  | .cut p => BuilderScript p
  | .architect _ => False

private theorem forgetClock {A : Type} (t : LabelledGame (Option A)) (P : Option A → Prop)
    (hbad : ¬ P none) (f : ℕ → ℕ) (n : ℕ) (h : ((increasing t n).score P).outcome f true) :
    (t.score P).outcome f true := by
  induction t generalizing n with
  | terminal => exact h
  | architect t ih =>
    obtain ⟨k,hk⟩ := h
    exact ⟨k,ih _ _ hk⟩
  | builder t ih =>
    change ∀ᶠ k in atTop, ((if n < f k then increasing (t (f k)) (f k) else
      .terminal none).score P).outcome f true at h
    apply h.mono
    intro k hk
    split at hk
    · exact ih _ _ hk
    · exact (hbad hk).elim

private theorem finishKeepsOutside (G : SimpleGraph Tree) (f : ℕ → ℕ) (x : Tree)
    (p : Script Tree) (hp : BuilderScript p)
    (h : ((p.finish (fun y => some (x,y,false)) none).score (wins G false)).outcome f true) :
    Keep f (G.Adj x) p := by
  induction p with
  | done y => exact h.1
  | architect => exact hp.elim
  | cut => exact False.elim h
  | builder t ih => exact h.mono fun k hk => ih _ (hp _) hk

private theorem cannotFinishInside (G : SimpleGraph Tree) (f : ℕ → ℕ) (y : Tree)
    (p : Script Tree) :
    ¬ ((p.finish (fun x => some (x,y,true)) none).score (wins G false)).outcome f true := by
  induction p with
  | done => exact fun h => Bool.noConfusion h.2
  | cut => exact id
  | architect t ih => rintro ⟨k,h⟩; exact ih k h
  | builder t ih => intro h; obtain ⟨k,hk⟩ := h.exists; exact ih _ hk

private abbrev OutsideRun (G : SimpleGraph Tree) (f : ℕ → ℕ) (p q : Script Tree) :=
  ((p.interleave q).score (wins G false)).outcome f true

private theorem outsideShared (G : SimpleGraph Tree) (f : ℕ → ℕ) (p q r : Script Tree)
    (hp : BuilderScript p) (hq : BuilderScript q) (hr : BuilderScript r)
    (hpq : OutsideRun G f p q) (hpr : OutsideRun G f p r) (hqr : OutsideRun G f q r) :
    ∃ x y z, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z := by
  induction p generalizing q r with
  | architect => exact hp.elim
  | done x =>
    have hy := finishKeepsOutside G f x q hq hpq
    have hz := finishKeepsOutside G f x r hr hpr
    have h := keepsInterleave f _ _ q r hy hz
    obtain ⟨v,hw,ht⟩ := winningWitness (q.interleave r) f (wins G false) _ hqr h
    obtain _ | ⟨y,z,b⟩ := v
    · exact hw.elim
    · exact ⟨x,y,z,ht.1,ht.2,hw.1⟩
  | builder t ih =>
    obtain ⟨k,hk,hk'⟩ := (Filter.Eventually.and hpq hpr).exists
    exact ih _ _ _ (hp _) hq hr hk hk' hqr
  | cut p ih =>
    induction q generalizing r with
    | architect => exact hq.elim
    | done y => exact (cannotFinishInside G f y p hpq).elim
    | builder t ihq =>
      obtain ⟨k,hk,hk'⟩ := (Filter.Eventually.and hpq hqr).exists
      exact ihq _ _ (hq _) hr hk hpr hk'
    | cut q =>
      induction r with
      | architect => exact hr.elim
      | done z => exact (cannotFinishInside G f z p hpr).elim
      | builder t ihr =>
        obtain ⟨k,hk,hk'⟩ := (Filter.Eventually.and hpr hqr).exists
        exact ihr _ (hr _) hk hk'
      | cut r => exact ih q r hp hq hr hpq hpr hqr

theorem outsideBuilderScriptTriangle (G : SimpleGraph Tree) (f : ℕ → ℕ) (p : Script Tree)
    (hp : BuilderScript p)
    (h : ((increasing (p.interleave p) 0).score (wins G false)).outcome f true) :
    ∃ x y z, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z := by
  have hw := forgetClock _ (wins G false) id f 0 h
  exact outsideShared G f p p p hp hp hp hw hw hw

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.PairGame
open Filter

theorem outcomeSubsequence (p : PairGame) (f h : ℕ → ℕ) (hh : StrictMono h)
    (b : Bool) (hp : p.outcome f b) : p.outcome (f ∘ h) b := by
  induction p with
  | terminal => exact hp
  | architect t ih =>
    cases b with
    | true => obtain ⟨i,hi⟩ := hp; exact ⟨i,ih _ hi⟩
    | false => exact fun i => ih i (hp i)
  | builder t ih =>
    obtain ⟨n,hn⟩ := eventually_atTop.mp hp
    exact eventually_atTop.mpr ⟨n,fun j hj => ih _ (hn _ (hj.trans (hh.id_le j)))⟩

private theorem valueOfIdentityWin (p : PairGame) (h : p.outcome id true) : p.value := by
  induction p with
  | terminal => exact h
  | architect t ih =>
    obtain ⟨i,hi⟩ := h
    exact ⟨i,ih _ hi⟩
  | builder t ih => exact Nat.hyperfilter_le_atTop (h.mono fun n hn => ih _ hn)

end Erdos591Proof.PairGame

namespace Erdos591Proof.LabelledGame

def recordHistory {A : Type} (t : LabelledGame A) (past : List ℕ) :
    LabelledGame (List ℕ × A) :=
  match t with
  | .terminal a => .terminal (past,a)
  | .builder q => .builder fun n => recordHistory (q n) (past ++ [n])
  | .architect q => .architect fun n => recordHistory (q n) (past ++ [n])

private theorem scoreRecord {A : Type} (t : LabelledGame A) (past : List ℕ) (P : A → Prop) :
    ((recordHistory t past).score (fun z => P z.2)) = t.score P := by
  induction t generalizing past with
  | terminal => rfl
  | architect t ih => exact congrArg PairGame.architect (funext fun n => ih n _)
  | builder t ih => exact congrArg PairGame.builder (funext fun n => ih n _)

-- A bounded statistic of the full history can be fixed before the next
-- Builder move. Other simultaneous winning games survive this thinning.
theorem predictFiniteHistory {A C : Type} [Finite C] (t : LabelledGame A)
    (P : A → Prop) (color : List ℕ → A → C) (f : ℕ → ℕ) (h : (t.score P).outcome f true) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∃ c, ((recordHistory t []).score
      (fun z => P z.2 ∧ color z.1 z.2 = c)).outcome (f ∘ g) true := by
  let q := recordHistory t []
  let cond (c : C) (z : List ℕ × A) := P z.2 ∧ color z.1 z.2 = c
  have he : (fun z => ∃ c, cond c z) = fun z : List ℕ × A => P z.2 := by
    funext z
    exact propext ⟨fun ⟨_,hp,_⟩ => hp,fun hp => ⟨_,hp,rfl⟩⟩
  have hw : ((q.reindex f).score (fun z => ∃ c, cond c z)).outcome id true := by
    apply (outcome_reindex q (fun z => ∃ c, cond c z) f id true).mpr
    rw [he,show q = recordHistory t [] from rfl,scoreRecord]
    exact h
  obtain ⟨c,hc⟩ := (valueFiniteUnion cond (q.reindex f)).mp (PairGame.valueOfIdentityWin _ hw)
  obtain ⟨g,hg,win,_⟩ := ((q.reindex f).score (cond c)).realize
  exact ⟨g,hg,c,(outcome_reindex q (cond c) f g true).mp (win hc)⟩

end Erdos591Proof.LabelledGame

namespace Erdos591Proof.LabelledGame

def mapLabel {A B : Type} (f : A → B) : LabelledGame A → LabelledGame B
  | .terminal a => .terminal (f a)
  | .architect t => .architect fun n => (t n).mapLabel f
  | .builder t => .builder fun n => (t n).mapLabel f

theorem scoreMapLabel {A B : Type} (t : LabelledGame A) (f : A → B) (P : B → Prop) :
    (t.mapLabel f).score P = t.score (P ∘ f) := by
  induction t with
  | terminal => rfl
  | architect t ih => exact congrArg PairGame.architect (funext ih)
  | builder t ih => exact congrArg PairGame.builder (funext ih)

theorem predictFiniteLabel {A C : Type} [Finite C] (t : LabelledGame A)
    (P : A → Prop) (color : A → C) (f : ℕ → ℕ) (h : (t.score P).outcome f true) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∃ c, (t.score (fun z => P z ∧ color z = c)).outcome (f ∘ g) true := by
  obtain ⟨g,hg,c,hc⟩ := predictFiniteHistory t P (fun _ z => color z) f h
  exact ⟨g,hg,c,by rwa [scoreRecord t [] (fun z => P z ∧ color z = c)] at hc⟩

end Erdos591Proof.LabelledGame

namespace Erdos591Proof.HeightTwoGame
open Script

-- Each endpoint keeps its own chronological Architect moves. For a full
-- tree these are precisely its root count and the leaf count minus one at
-- each marked block.
def markCounts {A : Type} (p : Script A) (past : List ℕ) : Script (List ℕ × A) :=
  match p with
  | .done x => .done (past,x)
  | .architect t => .architect fun n => markCounts (t n) (past ++ [n])
  | .builder t => .builder fun n => markCounts (t n) past
  | .cut t => .cut (markCounts t past)

private theorem mapFinishCounts {A B C : Type} (p : Script A) (past : List ℕ)
    (k : List ℕ × A → B) (g : B → C) (f : A → C) (bad : B)
    (he : ∀ ns x, g (k (ns,x)) = f x) :
    ((markCounts p past).finish k bad).mapLabel g = p.finish f (g bad) := by
  induction p generalizing past with
  | done x => exact congrArg LabelledGame.terminal (he past x)
  | cut => rfl
  | architect t ih => exact congrArg LabelledGame.architect (funext fun n => ih n _)
  | builder t ih => exact congrArg LabelledGame.builder (funext fun n => ih n _)

private def forgetCounts {A B : Type} : Option ((List ℕ × A) × (List ℕ × B) × Bool) →
    Option (A × B × Bool)
  | none => none
  | some (x,y,b) => some (x.2,y.2,b)

theorem interleaveCounts {A B : Type} (p : Script A) (q : Script B) (s t : List ℕ) :
    ((markCounts p s).interleave (markCounts q t)).mapLabel forgetCounts = p.interleave q := by
  induction p generalizing q s t with
  | done x =>
    exact mapFinishCounts q t _ _ _ _ (fun _ _ => rfl)
  | architect p ih => exact congrArg LabelledGame.architect (funext fun n => ih n _ _ _)
  | builder p ih => exact congrArg LabelledGame.builder (funext fun n => ih n _ _ _)
  | cut p ih =>
    induction q generalizing t with
    | done y => exact mapFinishCounts p s _ _ _ _ (fun _ _ => rfl)
    | cut q => exact ih q s t
    | architect q hq => exact congrArg LabelledGame.architect (funext fun n => hq n _)
    | builder q hq => exact congrArg LabelledGame.builder (funext fun n => hq n _)

private theorem mapIncreasing {A B : Type} (f : Option A → Option B) (hf : f none = none)
    (p : LabelledGame (Option A)) (last : ℕ) :
    (increasing p last).mapLabel f = increasing (p.mapLabel f) last := by
  induction p generalizing last with
  | terminal => rfl
  | architect t ih => exact congrArg LabelledGame.architect (funext fun n => ih n last)
  | builder t ih =>
    apply congrArg LabelledGame.builder
    funext n
    change (if last < n then increasing (t n) n else LabelledGame.terminal none).mapLabel f = _
    by_cases hn : last < n
    · simpa [hn,increasing,LabelledGame.mapLabel] using ih n n
    · simp [hn,LabelledGame.mapLabel,hf]

-- The statistic can be chosen after fixing the first tree's initial leaf
-- count, even while the second tree has not made a single move.
theorem predictOpponentCounts {A B C : Type} [Finite C]
    (p : Script A) (q : Script B) (s t : List ℕ) (last : ℕ)
    (P : Option (A × B × Bool) → Prop)
    (stat : Option ((List ℕ × A) × (List ℕ × B) × Bool) → C) (f : ℕ → ℕ)
    (win : ((increasing (p.interleave q) last).score P).outcome f true) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∃ c,
      ((increasing ((markCounts p s).interleave (markCounts q t)) last).score
        (fun z => P (forgetCounts z) ∧ stat z = c)).outcome (f ∘ g) true := by
  let raw := (markCounts p s).interleave (markCounts q t)
  apply LabelledGame.predictFiniteLabel (increasing raw last) (P ∘ forgetCounts) stat f
  rw [← LabelledGame.scoreMapLabel,mapIncreasing forgetCounts rfl,show raw = _ from rfl,
    interleaveCounts]
  exact win

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame

-- The zero-based cut k occurs after s cuts in j earlier marked blocks.
-- Each entry n in this list represents n+1 leaves, as in Script.block.
def cutPivot (k : ℕ) (ds : List ℕ) : ℕ × ℕ :=
  match ds with
  | [] => (0,0)
  | d :: rest =>
    if k ≤ d then (0,0) else
      let (j,s) := cutPivot (k-(d+1)) rest
      (j+1,s+(d+1))

private theorem pivotBounds (k : ℕ) (ds : List ℕ) :
    (cutPivot k ds).1 ≤ (cutPivot k ds).2 ∧ (cutPivot k ds).2 ≤ k := by
  induction ds generalizing k with
  | nil => exact ⟨le_rfl,Nat.zero_le _⟩
  | cons d ds ih =>
    by_cases h : k ≤ d
    · simp [cutPivot,h]
    · obtain ⟨hj,hs⟩ := ih (k-(d+1))
      simp only [cutPivot,if_neg h]
      omega

theorem cutPivotSpec (ds : List ℕ) (k : ℕ) (hk : k < (ds.map (· + 1)).sum) :
    ∃ pre d tail, ds = pre ++ d :: tail ∧ cutPivot k ds = (pre.length,(pre.map (· + 1)).sum) ∧
      (pre.map (· + 1)).sum ≤ k ∧ k < (pre.map (· + 1)).sum + (d+1) := by
  induction ds generalizing k with
  | nil => simp at hk
  | cons d ds ih =>
    by_cases h : k ≤ d
    · exact ⟨[],d,ds,rfl,by simp [cutPivot,h],Nat.zero_le _,by simpa using Nat.lt_succ_of_le h⟩
    · simp only [List.map_cons,List.sum_cons] at hk
      obtain ⟨pre,e,tail,he,hp,hl,hu⟩ := ih (k-(d+1)) (by omega)
      refine ⟨d::pre,e,tail,congrArg (List.cons d) he,?_,?_,?_⟩
      · simp [cutPivot,h,hp,Nat.add_comm]
      · simp only [List.map_cons,List.sum_cons]
        omega
      · simp only [List.map_cons,List.sum_cons]
        omega

def opponentPivot {A : Type} (k : ℕ) (z : Option ((List ℕ × A) × (List ℕ × Tree) × Bool)) :
    Fin (k+1) × Fin (k+1) :=
  let ds := (z.map (fun w => w.2.1.1.tail)).getD []
  let p := cutPivot k ds
  let h := pivotBounds k ds
  (⟨p.1,Nat.lt_succ_of_le (h.1.trans h.2)⟩,⟨p.2,Nat.lt_succ_of_le h.2⟩)

theorem predictInsidePivot (G : SimpleGraph Tree) (f : ℕ → ℕ) (p : Script Tree)
    (last k : ℕ)
    (h : ((increasing (p.interleave Script.tree) last).score (wins G true)).outcome f true) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∃ pivot,
      ((increasing ((markCounts p []).interleave (markCounts Script.tree [])) last).score
        (fun z => wins G true (forgetCounts z) ∧ opponentPivot k z = pivot)).outcome (f ∘ g) true :=
  predictOpponentCounts p Script.tree [] [] last (wins G true) (opponentPivot k) f h

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Filter Script

-- The one-tree quantifier is independent of the arity chosen at each
-- Architect turn. This must hold at residual positions as well as the root.
private def Neutral {A : Type} (f : ℕ → ℕ) : Script A → Prop
  | .done _ => True
  | .builder t => ∀ n, Neutral f (t n)
  | .cut p => Neutral f p
  | .architect t => (∀ n, Neutral f (t n)) ∧
      ∀ n P, Force f P (t n) ↔ Force f P (t 0)

private theorem neutralBind {A B : Type} (f : ℕ → ℕ) (p : Script A) (k : A → Script B)
    (hp : Neutral f p) (hk : ∀ x, Neutral f (k x)) : Neutral f (p.bind k) := by
  induction p with
  | done x => exact hk x
  | cut p ih => exact ih hp
  | builder t ih => exact fun n => ih n (hp n)
  | architect t ih =>
    refine ⟨fun n => ih n (hp.1 n),fun n P => ?_⟩
    change Force f P ((t n).bind k) ↔ Force f P ((t 0).bind k)
    rw [forceBind, forceBind]
    exact hp.2 n _

private theorem neutralChildren {A : Type} (f : ℕ → ℕ) (t : ℕ → Script A)
    (ht : ∀ i, Neutral f (t i)) (n i : ℕ) : Neutral f (children t n i) := by
  induction n generalizing i with
  | zero => trivial
  | succ n ih =>
    exact neutralBind _ _ _ (ht i) fun _ => neutralBind _ _ _ (ih _) fun _ => trivial

private theorem neutralIndices (f : ℕ → ℕ) (n : ℕ) : Neutral f (indices n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact fun _ => neutralBind _ _ _ ih fun _ => trivial

private theorem neutralNode {A : Type} (f : ℕ → ℕ) (t : Bool → Script A)
    (ht : ∀ b, Neutral f (t b)) (n : ℕ) : Neutral f (node n t) := by
  apply neutralBind _ _ _ (neutralIndices f n)
  intro m total
  exact neutralBind _ _ _ (neutralChildren _ _ (fun _ => ht _) _ _) fun _ => trivial

private theorem neutralBlock (f : ℕ → ℕ) (b : Bool) : Neutral f (block b) := by
  have hl (c : Bool) : Neutral f (leaf c) := by cases c <;> exact fun _ => trivial
  have hq (c : Bool) (P : ℕ → Prop) : Force f P (leaf c) ↔ leafQuantifier f P := by
    cases c <;> rfl
  cases b with
  | false => exact neutralNode _ _ hl 0
  | true =>
    refine ⟨fun n => neutralNode _ _ hl _, fun n P => ?_⟩
    exact (nodeForce f leaf _ hq _ P).trans (nodeForce f leaf _ hq _ P).symm

private theorem neutralCompatible {A : Type} (p : Script A) (f : ℕ → ℕ)
    (h : Neutral f p) : Compatible (fun P => Force f P p) := by
  intro P Q hP hQ
  induction p with
  | done x => exact ⟨x,hP,hQ⟩
  | cut p ih => exact ih h hP hQ
  | builder t ih =>
    obtain ⟨k,hk,hk'⟩ := (hP.and hQ).exists
    exact ih _ (h _) hk hk'
  | architect t ih =>
    obtain ⟨n,hn⟩ := hP
    obtain ⟨m,hm⟩ := hQ
    exact ih 0 (h.1 _) ((h.2 n P).mp hn) ((h.2 m Q).mp hm)

private theorem noCutsRight {A B : Type} (p : Script A) (q : Script B)
    (hq : NoCuts q) (P : Option (A × B × Bool) → Prop) (hb : ¬ P none)
    (f : ℕ → ℕ) (last : ℕ)
    (win : ((increasing ((cut p).interleave q) last).score P).outcome f true) :
    Force f (fun y => Force f (fun x => P (some (x,y,true))) p) q := by
  induction q generalizing last with
  | done y => exact finishForce _ _ _ hb _ _ win
  | cut => exact hq.elim
  | architect t ih =>
    obtain ⟨i,hi⟩ := win
    exact ⟨i,ih i (hq i) _ hi⟩
  | builder t ih =>
    change ∀ᶠ k in atTop, ((if last < f k then increasing ((cut p).interleave
      (t (f k))) (f k) else LabelledGame.terminal none).score P).outcome f true at win
    apply win.mono
    intro k hk
    split at hk
    · exact ih _ (hq _) _ hk
    · exact (hb hk).elim

-- Under triangle-freeness Architect can be required to mark at least one
-- block of the second tree, even when the choice depends on the first tree.
def positiveTree : Script Tree := .architect fun r => node (r+1) block

theorem positiveReplyOrTriangle (G : SimpleGraph Tree) (f : ℕ → ℕ) (d : ℕ) (b : Bool)
    (h : ((increasing ((node d block).interleave tree) 0).score (wins G b)).outcome f true) :
    (∃ x y z, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z) ∨
    ((increasing ((node d block).interleave positiveTree) 0).score (wins G b)).outcome f true := by
  by_cases tri : ∃ x y z, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z
  · exact Or.inl tri
  right
  have win : (game.score (wins G b)).outcome f true := ⟨d,h⟩
  suffices aux : ∀ (p : Script Tree) (last : ℕ), Neutral f p →
      ((increasing (p.interleave tree) last).score (wins G b)).outcome f true →
      ((increasing (p.interleave positiveTree) last).score (wins G b)).outcome f true from
    aux _ _ (neutralNode _ _ (neutralBlock _) _) h
  intro p
  induction p with
  | done x =>
    intro last _ ⟨r,hr⟩
    cases r with
    | succ r => exact ⟨r,hr⟩
    | zero =>
      let good (y : Tree) := wins G b (some (x,y,false))
      have hg : Force f good tree := ⟨0,finishForce _ _ (wins G b) id f last hr⟩
      obtain ⟨y,z,hy,hz,hyz⟩ := winningEdgeWithin G f b win good good hg hg
      exact (tri ⟨x,y,z,hy.1,hz.1,hyz⟩).elim
  | architect t ih =>
    intro last hp ⟨n,hn⟩
    exact ⟨n,ih n last (hp.1 n) hn⟩
  | builder t ih =>
    intro last hp hw
    change ∀ᶠ k in atTop, ((if last < f k then increasing ((t (f k)).interleave tree) (f k)
      else LabelledGame.terminal none).score (wins G b)).outcome f true at hw
    change ∀ᶠ k in atTop, ((if last < f k then increasing ((t (f k)).interleave positiveTree) (f k)
      else LabelledGame.terminal none).score (wins G b)).outcome f true
    filter_upwards [hw] with k hk
    by_cases hl : last < f k
    · rw [if_pos hl] at hk ⊢
      exact ih _ _ (hp _) hk
    · simpa only [if_neg hl] using hk
  | cut p =>
    intro last hp ⟨r,hr⟩
    cases r with
    | succ r => exact ⟨r,hr⟩
    | zero =>
      let good (y : Tree) := Force f (fun x => wins G b (some (x,y,true))) p
      have hg : Force f good tree := ⟨0,noCutsRight p (node 0 block)
        (noCutsNode _ (noCutsNode leaf (fun _ => trivial))) (wins G b) id f last hr⟩
      obtain ⟨y,z,hy,hz,hyz⟩ := winningEdgeWithin G f b win good good hg hg
      obtain ⟨x,hxy,hxz⟩ := neutralCompatible p f hp _ _ hy hz
      exact (tri ⟨x,y,z,hxy.1,hxz.1,hyz⟩).elim

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Filter Script

private theorem bindAssocScript {A B C : Type} (p : Script A) (k : A → Script B)
    (h : B → Script C) : (p.bind k).bind h = p.bind (fun x => (k x).bind h) := by
  induction p with
  | done => rfl
  | cut p ih => exact congrArg cut ih
  | builder p ih => exact congrArg builder (funext ih)
  | architect p ih => exact congrArg architect (funext ih)

private def Allocate (f : ℕ → ℕ) : ℕ → (List ℕ → ℕ → Prop) → Prop
  | 0, K => ∀ᶠ i in atTop, K [] (f i)
  | n+1, K => ∀ᶠ i in atTop, Allocate f n (fun ms => K (f i :: ms))

-- This applies on either side of a hand-off. The continuation can include
-- all other positions in play and the clock of the game reading this header.
private theorem allocateIndices {A : Type} (f : ℕ → ℕ) (live : Script A → ℕ → Prop)
    (step : ∀ t last, live (.builder t) last → ∀ᶠ i in atTop, live (t (f i)) (f i))
    (n : ℕ) (k : List ℕ → ℕ → Script A) (last : ℕ)
    (h : live ((indices n).bind (fun ms => .builder (k ms))) last) :
    Allocate f n (fun ms total => live (k ms total) total) := by
  induction n generalizing k last with
  | zero => exact step _ _ h
  | succ n ih =>
    apply (step _ _ h).mono
    intro i hi
    apply ih (fun ms => k (f i :: ms)) (f i)
    simpa only [bindAssocScript, Script.bind] using hi

inductive HeaderReader where
  | first | second | both

def HeaderReader.reads : HeaderReader → Bool → Bool
  | .first, b => !b
  | .second, b => b
  | .both, _ => true

def headerCount (b : Bool) (plan : List HeaderReader) : ℕ :=
  (plan.filter (fun r => r.reads b)).length

def headerIndices (b : Bool) (xs : List (HeaderReader × ℕ)) : List ℕ :=
  (xs.filter (fun p => p.1.reads b)).map Prod.snd

private theorem mergeAllocations (f : ℕ → ℕ) (hf : StrictMono f) (plan : List HeaderReader)
    (P Q : List ℕ → ℕ → Prop) (hp : Allocate f (headerCount false plan) P)
    (hq : Allocate f (headerCount true plan) Q) (floor : ℕ) :
    ∃ (xs : List (HeaderReader × ℕ)) (total : ℕ), xs.map Prod.fst = plan ∧
      (floor :: (xs.map Prod.snd ++ [total])).Pairwise (· < ·) ∧
      P (headerIndices false xs) total ∧ Q (headerIndices true xs) total := by
  have fresh (a : ℕ) : ∀ᶠ i in atTop, a < f i :=
    (eventually_gt_atTop a).mono fun i h => h.trans_le (hf.id_le i)
  induction plan generalizing P Q floor with
  | nil =>
    obtain ⟨i,hi,hi',hfresh⟩ := (hp.and (hq.and (fresh floor))).exists
    exact ⟨[],f i,rfl,by simpa using hfresh,hi,hi'⟩
  | cons r rs ih =>
    have consStep (v : ℕ) (hv : floor < v) (xs : List (HeaderReader × ℕ)) (t : ℕ)
        (h : (v :: (xs.map Prod.snd ++ [t])).Pairwise (· < ·)) :
        (floor :: (((r,v)::xs).map Prod.snd ++ [t])).Pairwise (· < ·) := by
      refine List.pairwise_cons.mpr ⟨?_,h⟩
      intro x hx
      change x ∈ v :: (xs.map Prod.snd ++ [t]) at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hv
      · exact hv.trans ((List.pairwise_cons.mp h).1 x hx)
    cases r with
    | first =>
      change ∀ᶠ i in atTop, Allocate f (headerCount false rs) (fun m => P (f i :: m)) at hp
      obtain ⟨i,hi,hl⟩ := (hp.and (fresh floor)).exists
      obtain ⟨xs,t,hxs,hs,hp',hq'⟩ := ih _ _ hi hq (f i)
      exact ⟨(.first,f i)::xs,t,congrArg _ hxs,consStep _ hl _ _ hs,hp',hq'⟩
    | second =>
      change ∀ᶠ i in atTop, Allocate f (headerCount true rs) (fun m => Q (f i :: m)) at hq
      obtain ⟨i,hi,hl⟩ := (hq.and (fresh floor)).exists
      obtain ⟨xs,t,hxs,hs,hp',hq'⟩ := ih _ _ hp hi (f i)
      exact ⟨(.second,f i)::xs,t,congrArg _ hxs,consStep _ hl _ _ hs,hp',hq'⟩
    | both =>
      change ∀ᶠ i in atTop, Allocate f (headerCount false rs) (fun m => P (f i :: m)) at hp
      change ∀ᶠ i in atTop, Allocate f (headerCount true rs) (fun m => Q (f i :: m)) at hq
      obtain ⟨i,hi,hi',hl⟩ := (hp.and (hq.and (fresh floor))).exists
      obtain ⟨xs,t,hxs,hs,hp',hq'⟩ := ih _ _ hi hi' (f i)
      exact ⟨(.both,f i)::xs,t,congrArg _ hxs,consStep _ hl _ _ hs,hp',hq'⟩

def nodeBody {A : Type} (child : Bool → Script A) (ms : List ℕ) (total : ℕ) :
    Script (Word A) :=
  (children (fun i => child (decide (i ∈ ms))) total 1).bind fun xs => .done ⟨total,xs⟩

-- A plan can separate the two sets of indices, share just one of them,
-- or interleave them. Both residual games contain the same physical arity.
theorem synchronizeNodes {A : Type} (f : ℕ → ℕ) (hf : StrictMono f)
    (plan : List HeaderReader) (t u : Bool → Script A)
    (L R : Script (Word A) → ℕ → Prop)
    (stepL : ∀ t last, L (.builder t) last → ∀ᶠ i in atTop, L (t (f i)) (f i))
    (stepR : ∀ t last, R (.builder t) last → ∀ᶠ i in atTop, R (t (f i)) (f i))
    (a b floor : ℕ) (hl : L (node (headerCount false plan) t) a)
    (hr : R (node (headerCount true plan) u) b) :
    ∃ (xs : List (HeaderReader × ℕ)) (total : ℕ), xs.map Prod.fst = plan ∧
      (floor :: (xs.map Prod.snd ++ [total])).Pairwise (· < ·) ∧
      L (nodeBody t (headerIndices false xs) total) total ∧
      R (nodeBody u (headerIndices true xs) total) total := by
  exact mergeAllocations _ hf _ _ _ (allocateIndices _ L stepL _ (nodeBody t) a hl)
    (allocateIndices _ R stepR _ (nodeBody u) b hr) floor

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Filter Script

-- While a common unmarked portion of a tree is being filled, the two
-- continuations can impose entirely different lower bounds at each move.
theorem synchronizePlain {A B C : Type} (f : ℕ → ℕ) (hf : StrictMono f)
    (p : Script A) (hp : Plain p) (k : A → Script B) (l : A → Script C)
    (L : Script B → ℕ → Prop) (R : Script C → ℕ → Prop)
    (stepL : ∀ t last, L (.builder t) last → ∀ᶠ i in atTop, L (t (f i)) (f i))
    (stepR : ∀ t last, R (.builder t) last → ∀ᶠ i in atTop, R (t (f i)) (f i))
    (a b floor : ℕ) (hl : L (p.bind k) a) (hr : R (p.bind l) b) :
    ∃ (x : A) (last : Option ℕ), (∀ v ∈ last, floor < v) ∧
      L (k x) (last.getD a) ∧ R (l x) (last.getD b) := by
  induction p generalizing a b floor with
  | done x => exact ⟨x,none,by simp,hl,hr⟩
  | architect | cut => exact hp.elim
  | builder t ih =>
    have fresh : ∀ᶠ i in atTop, floor < f i :=
      (eventually_gt_atTop floor).mono fun i hi => hi.trans_le (hf.id_le i)
    obtain ⟨i,hi,hi',hv⟩ := ((stepL _ a hl).and ((stepR _ b hr).and fresh)).exists
    obtain ⟨x,opt,hs,hx,hx'⟩ := ih (f i) (hp _) (f i) (f i) (f i) hi hi'
    cases opt with
    | none => exact ⟨x,some (f i),by simpa using hv,hx,hx'⟩
    | some v =>
      have bound := hv.trans (hs v rfl)
      exact ⟨x,some v,by simpa using bound,hx,hx'⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

private def OneCut {A : Type} : Script A → Prop
  | .done _ => True
  | .cut p => Plain p
  | .builder t | .architect t => ∀ n, OneCut (t n)

private theorem plainBind {A B : Type} (p : Script A) (k : A → Script B)
    (hp : Plain p) (hk : ∀ x, Plain (k x)) : Plain (p.bind k) := by
  induction p with
  | done x => exact hk x
  | builder t ih => exact fun n => ih n (hp n)
  | cut | architect => exact hp.elim

private theorem plainChildren {A : Type} (c : ℕ → Script A) (n i : ℕ)
    (h : ∀ j ≥ i, Plain (c j)) : Plain (children c n i) := by
  induction n generalizing i with
  | zero => trivial
  | succ n ih =>
    exact plainBind _ _ (h i le_rfl) fun _ =>
      plainBind _ _ (ih _ (fun _ hj => h _ (by omega))) fun _ => trivial

private theorem plainBeforeOne {A B : Type} (p : Script A) (k : A → Script B)
    (hp : Plain p) (hk : ∀ x, OneCut (k x)) : OneCut (p.bind k) := by
  induction p with
  | done x => exact hk x
  | builder t ih => exact fun n => ih n (hp n)
  | cut | architect => exact hp.elim

private theorem oneOfPlain {A : Type} (p : Script A) (hp : Plain p) : OneCut p := by
  induction p with
  | done => trivial
  | cut | architect => exact hp.elim
  | builder t ih => exact fun n => ih n (hp n)

private theorem oneBeforePlain {A B : Type} (p : Script A) (k : A → Script B)
    (hp : OneCut p) (hk : ∀ x, Plain (k x)) : OneCut (p.bind k) := by
  induction p with
  | done x => exact oneOfPlain _ (hk x)
  | cut p => exact plainBind _ _ hp hk
  | builder t ih | architect t ih => exact fun n => ih n (hp n)

private theorem plainZeroNode {A : Type} (t : Bool → Script A) (h : Plain (t false)) :
    Plain (node 0 t) := by
  intro total
  exact plainBind _ _ (plainChildren _ _ _ (fun _ _ => h)) fun _ => trivial

private theorem oneMarkedNode {A : Type} (t : Bool → Script A)
    (h0 : Plain (t false)) (h1 : OneCut (t true)) : OneCut (node 1 t) := by
  intro mark total
  refine oneBeforePlain _ (fun xs : Tuple A total => done (⟨total,xs⟩ : Word A)) ?_ (fun _ => trivial)
  suffices aux : ∀ n i, OneCut (children (fun j => t (decide (j ∈ [mark]))) n i) from aux _ _
  intro n
  induction n with
  | zero => exact fun _ => trivial
  | succ n ih =>
    intro i
    by_cases he : i = mark
    · subst i
      apply oneBeforePlain
      · simpa using h1
      · intro x
        apply plainBind
        · apply plainChildren
          intro j hj
          simpa [show j ≠ mark by omega] using h0
        · intro xs
          trivial
    · apply plainBeforeOne
      · simpa [he] using h0
      · intro x
        exact oneBeforePlain _ _ (ih _) fun _ => trivial


private theorem oneCutWinsTriangle (G : SimpleGraph Tree) (f : ℕ → ℕ)
    (win : (game.score (wins G true)).outcome f true) (p : Script Tree) (last : ℕ)
    (hp : OneCut p) (h : ((increasing (p.interleave tree) last).score (wins G true)).outcome f true) :
    ∃ x y z, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z := by
  induction p generalizing last with
  | done x =>
    obtain ⟨_,hx⟩ := forceWitness _ _ _ (finishForce tree _ (wins G true) id f last h)
    exact (Bool.noConfusion hx.2 : False).elim
  | cut p => exact insideSingleCutTriangle G f win p hp last h
  | architect t ih =>
    obtain ⟨n,hn⟩ := h
    exact ih _ _ (hp _) hn
  | builder t ih =>
    obtain ⟨k,hk⟩ := h.exists
    change ((if last < f k then increasing ((t (f k)).interleave tree) (f k)
      else LabelledGame.terminal none).score (wins G true)).outcome f true at hk
    split at hk
    · exact ih _ _ (hp _) hk
    · exact False.elim hk

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Filter Script

def openingLayout (d : ℕ) : Bool → List HeaderReader
  | false => List.replicate (d+1) .first ++ List.replicate (d+1) .second
  | true => .both :: (List.replicate d .second ++ List.replicate d .first)

private abbrev LeftWin (f : ℕ → ℕ) (G : SimpleGraph Tree) (b : Bool)
    (p : Script Tree) (last : ℕ) :=
  ((increasing (p.interleave tree) last).score (wins G b)).outcome f true

private theorem leftWinStep (f : ℕ → ℕ) (G : SimpleGraph Tree) (b : Bool)
    (t : ℕ → Script Tree) (last : ℕ) (h : LeftWin f G b (.builder t) last) :
    ∀ᶠ i in atTop, LeftWin f G b (t (f i)) (f i) := by
  apply h.mono
  intro i hi
  change ((if last < f i then increasing ((t (f i)).interleave tree) (f i)
    else LabelledGame.terminal none).score (wins G b)).outcome f true at hi
  split at hi
  · exact hi
  · exact False.elim hi

theorem synchronizeOpeningRoots (f : ℕ → ℕ) (hf : StrictMono f)
    (G : SimpleGraph Tree) (d : ℕ) (b : Bool) (h : LeftWin f G b (node (d+1) block) 0) :
    ∃ (xs : List (HeaderReader × ℕ)) (total : ℕ), xs.map Prod.fst = openingLayout d b ∧
      (0 :: (xs.map Prod.snd ++ [total])).Pairwise (· < ·) ∧
      LeftWin f G b (nodeBody block (headerIndices false xs) total) total ∧
      LeftWin f G b (nodeBody block (headerIndices true xs) total) total := by
  have counts (c : Bool) : headerCount c (openingLayout d b) = d+1 := by
    cases b <;> cases c <;> simp [headerCount,openingLayout,HeaderReader.reads]
  apply synchronizeNodes _ hf _ _ _ _ _ (leftWinStep f G b) (leftWinStep f G b) 0 0
  · rwa [counts]
  · rwa [counts]

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

private def blockAt (ms : List ℕ) (i : ℕ) := block (decide (i ∈ ms))

def remainingBlocks (ms : List ℕ) (i n : ℕ) (k : Tuple (Word ℕ) (n+1) → Tree)
    (x : Word ℕ) : Script Tree :=
  (children (blockAt ms) n (i+1)).bind (fun xs => .done (k (toLex (x,xs))))

private theorem readFirstBlock (ms : List ℕ) (i n : ℕ) (k : Tuple (Word ℕ) (n+1) → Tree) :
    (children (blockAt ms) (n+1) i).bind (fun xs => .done (k xs)) =
      (blockAt ms i).bind (remainingBlocks ms i n k) := by
  simp only [children,bindAssocScript,Script.bind]
  rfl

-- Both games start the first marked block after reading identical words
-- at all lower positions. The function k retains their common root prefix.
theorem enterSharedFirstBlock (f : ℕ → ℕ) (hf : StrictMono f) (G : SimpleGraph Tree)
    (ms ts : List ℕ) (mark : ℕ) (hm : mark ∈ ms) (ht : mark ∈ ts)
    (minM : ∀ j ∈ ms, mark ≤ j) (minT : ∀ j ∈ ts, mark ≤ j)
    (start len : ℕ) (lo : start ≤ mark) (hi : mark < start + len)
    (k : Tuple (Word ℕ) len → Tree) (a b : ℕ)
    (h₁ : LeftWin f G true ((children (blockAt ms) len start).bind (fun xs => .done (k xs))) a)
    (h₂ : LeftWin f G true ((children (blockAt ts) len start).bind (fun xs => .done (k xs))) b) :
    ∃ (n : ℕ) (assemble : Tuple (Word ℕ) (n+1) → Tree) (m r a' b' : ℕ),
      mark + n + 1 = start + len ∧
      LeftWin f G true ((node (m+1) leaf).bind (remainingBlocks ms mark n assemble)) a' ∧
      LeftWin f G true ((node (r+1) leaf).bind (remainingBlocks ts mark n assemble)) b' := by
  induction len generalizing start a b with
  | zero => omega
  | succ n ih =>
    rw [readFirstBlock] at h₁ h₂
    by_cases he : start = mark
    · subst start
      simp only [blockAt, hm, ht, decide_true] at h₁ h₂
      obtain ⟨m,hm'⟩ := h₁
      obtain ⟨r,hr'⟩ := h₂
      exact ⟨n,k,m,r,a,b,by omega,hm',hr'⟩
    · have hm' : start ∉ ms := fun hj => he (Nat.le_antisymm lo (minM _ hj))
      have ht' : start ∉ ts := fun hj => he (Nat.le_antisymm lo (minT _ hj))
      simp only [blockAt,hm',ht',decide_false] at h₁ h₂
      have hp : Plain (block false) := plainZeroNode _ (fun _ => trivial)
      obtain ⟨x,opt,_,hL,hR⟩ := synchronizePlain _ hf (block false) hp
        (remainingBlocks ms start n k) (remainingBlocks ts start n k)
        (LeftWin f G true) (LeftWin f G true) (leftWinStep _ _ _) (leftWinStep _ _ _)
        a b (max a b) h₁ h₂
      obtain ⟨v,p,m,r,a',b',hv,hl,hr⟩ := ih (start+1) (by omega) (by omega)
        (fun xs => k (toLex (x,xs))) (opt.getD a) (opt.getD b) hL hR
      exact ⟨v,p,m,r,a',b',by omega,hl,hr⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script


-- The first block count is learned after the root prefix. Only at that
-- position do we thin the sequence to predict the opponent's pivot.
theorem prepareInsideOpening (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f) (d : ℕ)
    (h : LeftWin f G true (node (d+1) block) 0) :
    (∃ x y z, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z) ∨
    ∃ (mark : ℕ) (rest : List (HeaderReader × ℕ)) (total n : ℕ)
      (assemble : Tuple (Word ℕ) (n+1) → Tree) (m r a b k : ℕ) (g : ℕ → ℕ)
      (pivot : Fin (k+1) × Fin (k+1)),
      let xs := (HeaderReader.both,mark) :: rest
      let p := (node (m+1) leaf).bind (remainingBlocks (headerIndices false xs) mark n assemble)
      let q := (node (r+1) leaf).bind (remainingBlocks (headerIndices true xs) mark n assemble)
      xs.map Prod.fst = openingLayout d true ∧
      (0 :: (xs.map Prod.snd ++ [total])).Pairwise (· < ·) ∧ mark + n = total ∧
      k + 1 = m+1 - (if d = 0 then 1 else 0) ∧ StrictMono g ∧
      ((increasing ((markCounts p []).interleave (markCounts tree [])) a).score
        (fun z => wins G true (forgetCounts z) ∧ opponentPivot k z = pivot)).outcome (f ∘ g) true ∧
      LeftWin (f ∘ g) G true q b ∧ LeftWin (f ∘ g) G true (node (d+1) block) 0 := by
  obtain ⟨xs,total,layout,sorted,h₁,h₂⟩ := synchronizeOpeningRoots _ hf G d true h
  cases xs with
  | nil => cases layout
  | cons pair rest =>
    obtain ⟨reader,mark⟩ := pair
    have hreader : reader = .both := (List.cons.inj layout).1
    subst reader
    let xs := (HeaderReader.both,mark) :: rest
    have pos : 0 < mark := (List.pairwise_cons.mp sorted).1 _ List.mem_cons_self
    have higher := (List.pairwise_cons.mp (List.pairwise_cons.mp sorted).2).1
    have bound : mark < total := higher _ (List.mem_append_right _ List.mem_cons_self)
    have mem (b : Bool) : mark ∈ headerIndices b xs := List.mem_cons_self
    have low (b : Bool) : ∀ j ∈ headerIndices b xs, mark ≤ j := by
      intro j hj
      change j ∈ mark :: headerIndices b rest at hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact le_rfl
      · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hj
        exact (higher _ (List.mem_append_left _ (List.mem_map.mpr
          ⟨v,(List.mem_filter.mp hv).1,rfl⟩))).le
    obtain ⟨n,assemble,m,r,a,b,hn,hL,hR⟩ := enterSharedFirstBlock _ hf G
      _ _ _ (mem false) (mem true) (low false) (low true) 1 total pos (by omega)
      (fun xs => ⟨total,xs⟩) total total h₁ h₂
    let c := m+1 - (if d = 0 then 1 else 0)
    by_cases hc : c = 0
    · left
      have hd : d = 0 := by by_contra hd; simp [c,hd] at hc
      subst d
      have hm : m = 0 := by simpa [c] using hc
      subst m
      have hem : rest = [] := by simpa [openingLayout] using (List.cons.inj layout).2
      subst rest
      refine oneCutWinsTriangle G f (show (game.score (wins G true)).outcome f true from ⟨1,h⟩) _ a ?_ hL
      apply oneBeforePlain _ _ (oneMarkedNode leaf (fun _ => trivial) (fun _ => trivial))
      intro x
      apply plainBind
      swap
      · exact fun _ => trivial
      apply plainChildren
      intro j hj
      have hne : j ≠ mark := by omega
      change Plain (block (decide (j ∈ [mark])))
      simp only [List.mem_singleton,hne,decide_false]
      exact plainZeroNode leaf (fun _ => trivial)
    · right
      obtain ⟨g,hg,pivot,hw⟩ := predictInsidePivot G f _ a (c-1) hL
      exact ⟨mark,rest,total,n,assemble,m,r,a,b,c-1,g,pivot,layout,sorted,by omega,by change c-1+1=c; omega,
        hg,hw,PairGame.outcomeSubsequence _ _ _ hg true hR,PairGame.outcomeSubsequence _ _ _ hg true h⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Filter Script


def insideLeafLayout (s c m r : ℕ) : List HeaderReader :=
  List.replicate s .first ++ [.both] ++ List.replicate (c-s-1) .first ++
    List.replicate r .second ++ List.replicate (m+1-c) .first

-- The layout uses the fixed pivot before any leaf index of either game
-- is drawn. The saved histories and both continuations are still live.
theorem prepareSharedLeafArity (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (m r k : ℕ) (pivot : Fin (k+1) × Fin (k+1)) (hk : k ≤ m)
    (u v : Word ℕ → Script Tree) (a b floor : ℕ)
    (h₁ : ((increasing ((markCounts ((node (m+1) leaf).bind u) []).interleave
      (markCounts tree [])) a).score
      (fun z => wins G true (forgetCounts z) ∧ opponentPivot k z = pivot)).outcome f true)
    (h₂ : LeftWin f G true ((node (r+1) leaf).bind v) b) :
    ∃ (xs : List (HeaderReader × ℕ)) (total : ℕ),
      xs.map Prod.fst = insideLeafLayout pivot.2.val (k+1) m r ∧
      (floor :: (xs.map Prod.snd ++ [total])).Pairwise (· < ·) ∧
      ((increasing ((markCounts ((nodeBody leaf (headerIndices false xs) total).bind u) []).interleave
        (markCounts tree [])) total).score
        (fun z => wins G true (forgetCounts z) ∧ opponentPivot k z = pivot)).outcome f true ∧
      LeftWin f G true ((nodeBody leaf (headerIndices true xs) total).bind v) total := by
  let L (p : Script (Word ℕ)) (last : ℕ) := ((increasing ((markCounts (p.bind u) []).interleave
    (markCounts tree [])) last).score
    (fun z => wins G true (forgetCounts z) ∧ opponentPivot k z = pivot)).outcome f true
  let R (p : Script (Word ℕ)) (last : ℕ) := LeftWin f G true (p.bind v) last
  have leftCount : headerCount false (insideLeafLayout pivot.2.val (k+1) m r) = m+1 := by
    have hs := pivot.2.isLt
    simp [headerCount,insideLeafLayout,HeaderReader.reads]
    omega
  have rightCount : headerCount true (insideLeafLayout pivot.2.val (k+1) m r) = r+1 := by
    simp [headerCount,insideLeafLayout,HeaderReader.reads]
  refine synchronizeNodes f hf _ leaf leaf L R ?_ ?_ a b floor ?_ ?_
  · intro t last h
    apply h.mono
    intro i hi
    change ((if last < f i then increasing ((markCounts ((t (f i)).bind u) []).interleave
      (markCounts tree [])) (f i) else LabelledGame.terminal none).score _).outcome f true at hi
    split at hi
    · exact hi
    · exact hi.1.elim
  · intro t last h
    exact leftWinStep f G true (fun n => (t n).bind v) last h
  · rwa [leftCount]
  · rwa [rightCount]

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

private theorem clockedWitness {A : Type} (f : ℕ → ℕ) (P : Option A → Prop) (hb : ¬ P none)
    (t : LabelledGame (Option A)) (last : ℕ)
    (h : ((increasing t last).score P).outcome f true) :
    ∃ a s, P (some a) ∧ Follows t s (some a) ∧ (last :: s.filterMap Event.number).Pairwise (· < ·) := by
  induction t generalizing last with
  | terminal a =>
    cases a with
    | none => exact (hb h).elim
    | some a => exact ⟨a,[],h,.done _,by simp⟩
  | architect t ih =>
    obtain ⟨i,hi⟩ := h
    obtain ⟨a,s,ha,hs,hl⟩ := ih i last hi
    exact ⟨a,.architect i :: s,ha,.architect hs,hl⟩
  | builder t ih =>
    obtain ⟨i,hi⟩ := h.exists
    change ((if last < f i then increasing (t (f i)) (f i) else LabelledGame.terminal none).score
      P).outcome f true at hi
    split at hi
    next lt =>
      obtain ⟨a,s,ha,hs,hl⟩ := ih _ _ hi
      refine ⟨a,.builder (f i) :: s,ha,.builder hs,List.pairwise_cons.mpr ⟨?_,hl⟩⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact lt
      · exact lt.trans ((List.pairwise_cons.mp hl).1 _ hv)
    next => exact (hb hi).elim

private theorem readFinish {A B : Type} (p : Script A) (k : A → B)
    {s : List Event} {v : B} (h : Follows (p.finish (some ∘ k) none) s (some v)) :
    ∃ a, Reads p s a ∧ k a = v ∧ Event.cut ∉ s := by
  induction p generalizing s with
  | done x => cases h; exact ⟨_,.done _,rfl,by simp⟩
  | cut => cases h
  | architect t ih =>
    cases h with
    | architect h =>
      obtain ⟨a,ha,hv,hs⟩ := ih _ h
      exact ⟨a,.architect ha,hv,by simpa using hs⟩
  | builder t ih =>
    cases h with
    | builder h =>
      obtain ⟨a,ha,hv,hs⟩ := ih _ h
      exact ⟨a,.builder ha,hv,by simpa using hs⟩

private theorem readInterleave {A B : Type} (p : Script A) (q : Script B)
    {s : List Event} {x : A} {y : B} {b : Bool} (h : Follows (p.interleave q) s (some (x,y,b))) :
    ∃ l r, Reads p l x ∧ Reads q r y ∧ Weave true l r s b := by
  induction p generalizing q s with
  | done a =>
    obtain ⟨z,hz,he,hs⟩ := readFinish q (fun z => (a,z,false)) h
    cases he
    exact ⟨[],_,.done _,hz,.finishLeft hs⟩
  | architect t ih =>
    cases h with
    | architect h =>
      obtain ⟨l,r,hl,hr,hw⟩ := ih _ q h
      exact ⟨_,_,.architect hl,hr,.leftMove (by simp) hw⟩
  | builder t ih =>
    cases h with
    | builder h =>
      obtain ⟨l,r,hl,hr,hw⟩ := ih _ q h
      exact ⟨_,_,.builder hl,hr,.leftMove (by simp) hw⟩
  | cut p ih =>
    suffices aux : ∃ l r, Reads p l x ∧ Reads q r y ∧ Weave false l r s b by
      obtain ⟨l,r,hl,hr,hw⟩ := aux
      exact ⟨_,r,.cut hl,hr,.leftCut hw⟩
    induction q generalizing s with
    | done a =>
      obtain ⟨z,hz,he,hs⟩ := readFinish p (fun z => (z,a,true)) h
      cases he
      exact ⟨_,[],hz,.done _,.finishRight hs⟩
    | cut q =>
      obtain ⟨l,r,hl,hr,hw⟩ := ih q h
      exact ⟨l,_,hl,.cut hr,.rightCut hw⟩
    | architect t iq =>
      cases h with
      | architect h =>
        obtain ⟨l,r,hl,hr,hw⟩ := iq _ h
        exact ⟨l,_,hl,.architect hr,.rightMove (by simp) hw⟩
    | builder t iq =>
      cases h with
      | builder h =>
        obtain ⟨l,r,hl,hr,hw⟩ := iq _ h
        exact ⟨l,_,hl,.builder hr,.rightMove (by simp) hw⟩

-- An isolated completion of any live pair position exposes the actual
-- two scripts, their interleaving, and the increasing numerical history.
theorem completePairPosition {A B : Type} (f : ℕ → ℕ) (P : Option (A × B × Bool) → Prop)
    (hb : ¬ P none) (p : Script A) (q : Script B) (last : ℕ)
    (h : ((increasing (p.interleave q) last).score P).outcome f true) :
    ∃ x y b l r s, P (some (x,y,b)) ∧ Reads p l x ∧ Reads q r y ∧ Weave true l r s b ∧
      (last :: s.filterMap Event.number).Pairwise (· < ·) := by
  obtain ⟨⟨x,y,b⟩,s,hv,hs,ht⟩ := clockedWitness f P hb _ last h
  obtain ⟨l,r,hl,hr,hw⟩ := readInterleave p q hs
  exact ⟨x,y,b,l,r,s,hv,hl,hr,hw,ht⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

def Event.architectNumber : Event → Option ℕ
  | .architect n => some n
  | _ => none

theorem readCountHistory {A : Type} (p : Script A) (past : List ℕ)
    {s ns x} (h : Reads (markCounts p past) s (ns,x)) :
    Reads p s x ∧ ns = past ++ s.filterMap Event.architectNumber := by
  induction p generalizing past s with
  | done a =>
    cases h
    exact ⟨.done _,by simp⟩
  | cut p ih =>
    cases h with
    | cut h =>
      obtain ⟨hp,he⟩ := ih past h
      exact ⟨.cut hp,he⟩
  | architect t ih =>
    cases h with
    | architect h =>
      obtain ⟨hp,he⟩ := ih _ _ h
      exact ⟨.architect hp,by simpa [Event.architectNumber,List.append_assoc] using he⟩
  | builder t ih =>
    cases h with
    | builder h =>
      obtain ⟨hp,he⟩ := ih _ _ h
      exact ⟨.builder hp,he⟩

theorem Weave.localNumbers {c b : Bool} {l r s : List Event} (h : Weave c l r s b) :
    (l.filterMap Event.number).Sublist (s.filterMap Event.number) ∧
    (r.filterMap Event.number).Sublist (s.filterMap Event.number) := by
  induction h with
  | finishLeft => exact ⟨List.nil_sublist _,List.Sublist.refl _⟩
  | finishRight => exact ⟨List.Sublist.refl _,List.nil_sublist _⟩
  | @leftMove e _ _ _ _ _ _ ih =>
    cases e with
    | builder n => exact ⟨ih.1.cons_cons n,ih.2.cons n⟩
    | cut | architect => exact ih
  | @rightMove e _ _ _ _ _ _ ih =>
    cases e with
    | builder n => exact ⟨ih.1.cons n,ih.2.cons_cons n⟩
    | cut | architect => exact ih
  | leftCut _ ih | rightCut _ ih => exact ih


-- A completed increasing play has exactly one positive group of leaf
-- cuts per marked block. Its first Architect choice is their group count.

theorem treeControlShape {s : List Event} {x : Tree} (h : Reads tree s x)
    (hs : (0 :: s.filterMap Event.number).Pairwise (· < ·)) :
    ∃ ds : List ℕ, (∀ n ∈ ds, 0 < n) ∧
      s.filter control = .architect ds.length ::
        ds.flatMap (fun n => .architect (n-1) :: List.replicate n .cut) := by
  obtain ⟨t,hc,rfl,_⟩ := decorationOfRead h
  have he := markedTreeCanonical t hc hs
  let bs := t.blocks
  rw [MarkedTree.builderMoves] at hs
  have hb : (0 :: bs.flatMap MarkedBlock.numbers).Pairwise (· < ·) :=
    hs.sublist (((List.Sublist.refl _).cons bs.length).trans
      (List.sublist_append_right _ _) |>.cons_cons 0)
  refine ⟨degrees bs,positiveDegrees bs,?_⟩
  calc
    _ = (decorate bs).moves.filter control := congrArg (fun w : MarkedTree => w.moves.filter control) he.symm
    _ = _ := by
      have ha (v : ℕ) : (control : Event → Bool) (.architect v) = true := rfl
      simp [MarkedTree.moves,decorate,ha,controlNode,controlBlocks bs 1 hb,degreesLength 1 bs]

private theorem shapeNumbers (s : List Event) :
    (s.filter control).filterMap Event.architectNumber = s.filterMap Event.architectNumber ∧
      (s.filter control).count .cut = s.count .cut := by
  induction s with
  | nil => exact ⟨rfl,rfl⟩
  | cons e s ih =>
    have ha (v : ℕ) : (control : Event → Bool) (.architect v) = true := rfl
    have hb (v : ℕ) : (control : Event → Bool) (.builder v) = false := rfl
    have hc : (control : Event → Bool) .cut = true := rfl
    cases e <;> simp [ha,hb,hc,Event.architectNumber,List.filterMap_cons,ih.1,ih.2]

private theorem shapeGroups (ds : List ℕ) :
    let groups := ds.flatMap (fun n => Event.architect (n-1) :: List.replicate n .cut)
    groups.filterMap Event.architectNumber = ds.map (·-1) ∧ groups.count .cut = ds.sum := by
  induction ds with
  | nil => exact ⟨rfl,rfl⟩
  | cons n ds ih =>
    simpa [List.flatMap_cons,List.filterMap_append,Event.architectNumber,List.count_cons,
      List.filterMap_replicate,List.count_replicate,List.count_append,Nat.add_comm] using ih

theorem recordedTreeCuts {s : List Event} {x : Tree} {ns : List ℕ}
    (h : Reads (markCounts tree []) s (ns,x)) (hs : (0 :: s.filterMap Event.number).Pairwise (· < ·)) :
    ∃ ds : List ℕ, ns = ds.length :: ds ∧ s.count .cut = (ds.map (·+1)).sum := by
  obtain ⟨hr,hn⟩ := readCountHistory tree [] h
  obtain ⟨ds,hpos,hd⟩ := treeControlShape hr hs
  obtain ⟨ha,hc⟩ := shapeNumbers s
  rw [hd] at ha hc
  obtain ⟨hs₁,hs₂⟩ := shapeGroups ds
  have he : (ds.map (·-1)).map (·+1) = ds := by
    rw [List.map_map]
    calc
      _ = ds.map id := by
        apply List.map_congr_left
        intro x hx
        have := hpos x hx
        change x-1+1 = x
        omega
      _ = ds := List.map_id _
  refine ⟨ds.map (·-1),?_,?_⟩
  · simpa [hn,Event.architectNumber,hs₁] using ha.symm
  · simpa [he,hs₂,List.count_cons] using hc.symm

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

theorem readFirstLeafCount (m : ℕ) {s : List Event} {x : Word ℕ}
    (h : Reads (node (m+1) leaf) s x) (hs : (0 :: s.filterMap Event.number).Pairwise (· < ·)) :
    s.count .cut = m+1 := by
  have hr : Reads (block (decide (0 ∈ [0]))) (.architect m :: s) x := .architect h
  obtain ⟨b,hb,he,_⟩ := blockOfRead [0] 0 _ _ hr
  have ne := hb.mp List.mem_cons_self
  have sorted : (0 :: b.numbers).Pairwise (· < ·) := by
    rw [← b.builderMoves,← he]
    exact hs
  have ht := controlBlock b sorted
  rw [if_neg ne,← he] at ht
  have ha : (control : Event → Bool) (.architect m) = true := rfl
  simp only [List.filter_cons,ha,ite_true] at ht
  have eq := Event.architect.inj (List.cons.inj ht).1
  have count := congrArg (List.count Event.cut) (List.cons.inj ht).2
  rw [(shapeNumbers s).2,List.count_replicate_self] at count
  have := List.length_pos_iff.mpr ne
  omega

private theorem separateSorted (u v : List Event)
    (h : (0 :: (u++v).filterMap Event.number).Pairwise (· < ·)) :
    (0 :: u.filterMap Event.number).Pairwise (· < ·) ∧
    (0 :: v.filterMap Event.number).Pairwise (· < ·) := by
  rw [List.filterMap_append] at h
  exact ⟨h.sublist ((List.sublist_append_left _ _).cons_cons 0),
    h.sublist ((List.sublist_append_right _ _).cons_cons 0)⟩

private theorem laterBlockCut (ms : List ℕ) (j : ℕ) (hj : j ∈ ms) (n i : ℕ)
    (lo : i ≤ j) (hi : j < i+n) {s x}
    (h : Reads (children (blockAt ms) n i) s x)
    (hs : (0 :: s.filterMap Event.number).Pairwise (· < ·)) : 0 < s.count Event.cut := by
  induction n generalizing i s with
  | zero => omega
  | succ n ih =>
    obtain ⟨b,u,v,hu,hv,rfl⟩ := splitRead (blockAt ms i) _ h
    obtain ⟨su,sv⟩ := separateSorted _ _ hs
    rw [List.count_append]
    by_cases he : i = j
    · subst i
      change Reads (block (decide (j ∈ ms))) u b at hu
      simp only [hj,decide_true,block,if_true] at hu
      cases hu with
      | @architect _ m w _ hw =>
        have ct := readFirstLeafCount m hw su
        have hcount : (Event.architect m :: w).count .cut = w.count .cut := by simp
        omega
    · obtain ⟨xs,w,z,hw,hz,rfl⟩ := splitRead (children (blockAt ms) n (i+1)) _ hv
      cases hz
      obtain ⟨sw,_⟩ := separateSorted _ _ sv
      have := ih (i+1) (by omega) (by omega) hw sw
      simp only [List.append_nil]
      omega

theorem Weave.cutBalance {first b : Bool} {l r s : List Event} (w : Weave first l r s b) :
    l.count .cut + (!first).toNat = r.count .cut + b.toNat := by
  induction w with
  | finishLeft h | finishRight h => simp [List.count_eq_zero_of_not_mem h]
  | leftMove h _ ih | rightMove h _ ih => simpa [List.count_cons,h] using ih
  | leftCut _ ih | rightCut _ ih => simp_all [Bool.toNat] <;> omega

-- The checked count lower bound turns the bounded prediction into the
-- index of an actual marked block in every permissible right completion.
theorem predictedBlockExists {s : List Event} {y : Tree} {ns : List ℕ} {k : ℕ}
    (h : Reads (markCounts tree []) s (ns,y)) (hs : (0 :: s.filterMap Event.number).Pairwise (· < ·))
    (hk : k < s.count .cut) :
    ∃ n pre m tail, ns = n :: (pre ++ m :: tail) ∧
      cutPivot k ns.tail = (pre.length,(pre.map (·+1)).sum) ∧ pre.length < n ∧
      (pre.map (·+1)).sum ≤ k ∧ k < (pre.map (·+1)).sum + (m+1) := by
  obtain ⟨ds,rfl,he⟩ := recordedTreeCuts h hs
  obtain ⟨pre,m,tail,hds,hp,hl,hu⟩ := cutPivotSpec ds k (he ▸ hk)
  exact ⟨ds.length,pre,m,tail,by rw [← hds],hp,by simp [hds],hl,hu⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

private theorem firstResidualCuts (m : ℕ) (ms : List ℕ) (mark n : ℕ)
    (k : Tuple (Word ℕ) (n+1) → Tree) {s x}
    (h : Reads ((node (m+1) leaf).bind (remainingBlocks ms mark n k)) s x)
    (hs : (0 :: s.filterMap Event.number).Pairwise (· < ·)) :
    m+1 ≤ s.count Event.cut ∧
    ((∃ j ∈ ms, mark < j ∧ j ≤ mark+n) → m+2 ≤ s.count Event.cut) := by
  obtain ⟨b,u,v,hu,hv,rfl⟩ := splitRead (node (m+1) leaf) _ h
  obtain ⟨su,sv⟩ := separateSorted _ _ hs
  have ct := readFirstLeafCount m hu su
  rw [List.count_append,ct]
  refine ⟨by omega,?_⟩
  rintro ⟨j,hj,lo,hi⟩
  obtain ⟨tail,w,z,hw,hz,rfl⟩ := splitRead (children (blockAt ms) n (mark+1)) _ hv
  cases hz
  have := laterBlockCut _ _ hj _ _ (by omega) (by omega) hw (separateSorted _ _ sv).1
  simp only [List.append_nil]
  omega

private theorem headerIndicesLength (b : Bool) (xs : List (HeaderReader × ℕ)) :
    (headerIndices b xs).length = headerCount b (xs.map Prod.fst) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases he : x.1.reads b <;> simpa [headerIndices,headerCount,he] using ih

-- For the root layout actually allocated in the inside opening, every
-- increasing completion puts the predicted cut inside the stated block.
theorem insidePivotInReply (d mark n m k : ℕ) (rest : List (HeaderReader × ℕ))
    (assemble : Tuple (Word ℕ) (n+1) → Tree)
    (layout : ((HeaderReader.both,mark) :: rest).map Prod.fst = openingLayout d true)
    (ordered : (0 :: (mark :: (rest.map Prod.snd ++ [mark+n]))).Pairwise (· < ·))
    (hk : k+1 = m+1 - (if d=0 then 1 else 0))
    {l r s : List Event} {ns ds : List ℕ} {x y : Tree} {last : ℕ}
    (hl : Reads (markCounts ((node (m+1) leaf).bind (remainingBlocks
      (headerIndices false ((HeaderReader.both,mark)::rest)) mark n assemble)) []) l (ns,x))
    (hr : Reads (markCounts tree []) r (ds,y))
    (hw : Weave true l r s true) (hs : (last :: s.filterMap Event.number).Pairwise (· < ·)) :
    ∃ count pre e tail, ds = count :: (pre ++ e :: tail) ∧
      cutPivot k ds.tail = (pre.length,(pre.map (·+1)).sum) ∧ pre.length < count ∧
      (pre.map (·+1)).sum ≤ k ∧ k < (pre.map (·+1)).sum + (e+1) := by
  have hzero : (0 :: s.filterMap Event.number).Pairwise (· < ·) :=
    List.pairwise_cons.mpr ⟨fun j hj => (Nat.zero_le last).trans_lt ((List.pairwise_cons.mp hs).1 j hj),
      (List.pairwise_cons.mp hs).2⟩
  obtain ⟨hmin,hextra⟩ := firstResidualCuts _ _ _ _ _ (readCountHistory _ [] hl).1
    (hzero.sublist (hw.localNumbers.1.cons_cons 0))
  have hbal := hw.cutBalance
  change l.count .cut + 0 = r.count .cut + 1 at hbal
  apply predictedBlockExists hr (hzero.sublist (hw.localNumbers.2.cons_cons 0))
  by_cases hd : d=0
  · simp only [if_pos hd] at hk
    omega
  · simp only [if_neg hd,Nat.sub_zero] at hk
    have hlen := headerIndicesLength false ((HeaderReader.both,mark)::rest)
    rw [layout] at hlen
    change (mark :: headerIndices false rest).length = _ at hlen
    simp [headerCount,openingLayout,HeaderReader.reads] at hlen
    have hne : headerIndices false rest ≠ [] := by
      intro hem
      simp [hem] at hlen
      omega
    obtain ⟨j,hj⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hj
    have hm : v.2 ∈ rest.map Prod.snd := List.mem_map.mpr ⟨v,(List.mem_filter.mp hv).1,rfl⟩
    have lower := (List.pairwise_cons.mp (List.pairwise_cons.mp ordered).2).1 _ (List.mem_append_left _ hm)
    have upper := (List.pairwise_append.mp (List.pairwise_cons.mp (List.pairwise_cons.mp ordered).2).2).2.2
      _ hm _ List.mem_cons_self
    have := hextra ⟨v.2,List.mem_cons_of_mem _ hj,lower,upper.le⟩
    omega

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Filter Script

-- The same tuple constructor is carried through both games. Their outer
-- continuations may differ, even in the types of values they return.
def childRun {A V B : Type} (child : ℕ → Script A) (n i : ℕ)
    (assemble : Tuple A n → V) (resume : V → Script B) : Script B :=
  (children child n i).bind fun xs => resume (assemble xs)

private theorem childRunSucc {A V B : Type} (child : ℕ → Script A) (n i : ℕ)
    (assemble : Tuple A (n+1) → V) (resume : V → Script B) :
    childRun child (n+1) i assemble resume =
      (child i).bind fun x => childRun child n (i+1)
        (fun xs => assemble (toLex (x,xs))) resume := by
  simp only [childRun,children,bindAssocScript,Script.bind]

def BuilderStep {A : Type} (f : ℕ → ℕ) (L : Script A → ℕ → Prop) : Prop :=
  ∀ t last, L (.builder t) last → ∀ᶠ i in atTop, L (t (f i)) (f i)

-- Fill the actual children preceding the next mark, including any gaps
-- created by thinning f. Both residuals receive the very same prefix.
theorem playChildPrefix {A V B C : Type} (f : ℕ → ℕ) (hf : StrictMono f)
    (L : Script B → ℕ → Prop) (R : Script C → ℕ → Prop)
    (hL : BuilderStep f L) (hR : BuilderStep f R)
    (p q : ℕ → Script A) (n i mark : ℕ) (lo : i ≤ mark) (hi : mark ≤ i+n)
    (plain : ∀ j, i ≤ j → j < mark → Plain (p j) ∧ p j = q j)
    (assemble : Tuple A n → V) (u : V → Script B) (v : V → Script C)
    (a b floor : ℕ) (hl : L (childRun p n i assemble u) a)
    (hr : R (childRun q n i assemble v) b) :
    ∃ (m : ℕ) (put : Tuple A m → V) (last : Option ℕ),
      mark + m = i+n ∧ (∀ z ∈ last, floor < z) ∧
      L (childRun p m mark put u) (last.getD a) ∧
      R (childRun q m mark put v) (last.getD b) := by
  induction n generalizing i a b floor with
  | zero =>
    have he : mark = i := by omega
    subst mark
    exact ⟨0,assemble,none,rfl,by simp,hl,hr⟩
  | succ n ih =>
    by_cases he : i = mark
    · subst mark
      exact ⟨n+1,assemble,none,rfl,by simp,hl,hr⟩
    obtain ⟨hp,eq⟩ := plain i le_rfl (by omega)
    rw [childRunSucc] at hl hr
    rw [← eq] at hr
    obtain ⟨x,opt,hs,h₁,h₂⟩ := synchronizePlain f hf (p i) hp _ _ L R hL hR a b floor hl hr
    obtain ⟨m,put,next,hm,hs',h₃,h₄⟩ := ih (i+1) (by omega) (by omega)
      (fun j hj => plain j (by omega)) (fun xs => assemble (toLex (x,xs)))
      (opt.getD a) (opt.getD b) (opt.getD floor) h₁ h₂
    refine ⟨m,put,next.or opt,by omega,?_,?_,?_⟩
    · cases next with
      | none => exact hs
      | some z =>
        have H := hs' z rfl
        cases opt with
        | none => simpa using H
        | some t => simpa using Nat.lt_trans (hs t rfl) H
    · cases next <;> exact h₃
    · cases next <;> exact h₄

def leafRun (ms : List ℕ) (i : ℕ) := leaf (decide (i ∈ ms))

def cutIf {A : Type} (marked : Bool) (p : Script A) : Script A :=
  if marked then .cut p else p

-- At the selected leaf a common value is issued once. A reader that
-- marked this index sees a cut immediately; the other can stay in place.
theorem playSharedLeaf {V B C : Type} (f : ℕ → ℕ) (hf : StrictMono f)
    (L : Script B → ℕ → Prop) (R : Script C → ℕ → Prop)
    (hL : BuilderStep f L) (hR : BuilderStep f R)
    (ms ts : List ℕ) (i n : ℕ) (assemble : Tuple ℕ (n+1) → V)
    (u : V → Script B) (v : V → Script C) (a b floor : ℕ)
    (hl : L (childRun (leafRun ms) (n+1) i assemble u) a)
    (hr : R (childRun (leafRun ts) (n+1) i assemble v) b) :
    ∃ x, floor < x ∧
      L (cutIf (decide (i ∈ ms)) (childRun (leafRun ms) n (i+1)
        (fun xs => assemble (toLex (x,xs))) u)) x ∧
      R (cutIf (decide (i ∈ ts)) (childRun (leafRun ts) n (i+1)
        (fun xs => assemble (toLex (x,xs))) v)) x := by
  rw [childRunSucc] at hl hr
  have fresh : ∀ᶠ k in atTop, floor < f k :=
    (eventually_gt_atTop floor).mono fun k hk => hk.trans_le (hf.id_le k)
  obtain ⟨k,hk,hp,hq⟩ := (fresh.and ((hL _ _ hl).and (hR _ _ hr))).exists
  refine ⟨f k,hk,?_,?_⟩
  · by_cases h : i ∈ ms <;> simpa [leafRun,leaf,h,Script.bind,cutIf] using hp
  · by_cases h : i ∈ ts <;> simpa [leafRun,leaf,h,Script.bind,cutIf] using hq

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Filter Script

def ArchitectStep {A : Type} (L : Script A → ℕ → Prop) : Prop :=
  ∀ t last, L (.architect t) last → ∃ n, L (t n) last

private theorem chooseBlockCount {A : Type} (L : Script A → ℕ → Prop)
    (step : ArchitectStep L) (marked : Bool) (k : Word ℕ → Script A) (a : ℕ)
    (h : L ((block marked).bind k) a) :
    ∃ n, (0 < n ↔ marked = true) ∧ L ((node n leaf).bind k) a := by
  cases marked with
  | false => exact ⟨0,by simp,h⟩
  | true =>
    obtain ⟨n,hn⟩ := step _ _ h
    exact ⟨n+1,by simp,hn⟩

-- Both counts are chosen with the actual past in scope. Only after seeing
-- the counts do we select the order and overlap of the leaf marks.
theorem playSharedBlock {V B C : Type} (f : ℕ → ℕ) (hf : StrictMono f)
    (L : Script B → ℕ → Prop) (R : Script C → ℕ → Prop)
    (hL : BuilderStep f L) (hR : BuilderStep f R)
    (cL : ArchitectStep L) (cR : ArchitectStep R)
    (ms ts : List ℕ) (i n : ℕ) (assemble : Tuple (Word ℕ) (n+1) → V)
    (u : V → Script B) (v : V → Script C) (a b floor : ℕ)
    (hl : L (childRun (blockAt ms) (n+1) i assemble u) a)
    (hr : R (childRun (blockAt ts) (n+1) i assemble v) b) :
    ∃ m r, (0 < m ↔ i ∈ ms) ∧ (0 < r ↔ i ∈ ts) ∧
      ∀ plan, headerCount false plan = m → headerCount true plan = r →
        ∃ (xs : List (HeaderReader × ℕ)) (total : ℕ), xs.map Prod.fst = plan ∧
          (floor :: (xs.map Prod.snd ++ [total])).Pairwise (· < ·) ∧
          L ((nodeBody leaf (headerIndices false xs) total).bind fun x =>
            childRun (blockAt ms) n (i+1) (fun ys => assemble (toLex (x,ys))) u) total ∧
          R ((nodeBody leaf (headerIndices true xs) total).bind fun x =>
            childRun (blockAt ts) n (i+1) (fun ys => assemble (toLex (x,ys))) v) total := by
  rw [childRunSucc] at hl hr
  obtain ⟨m,hm,hp⟩ := chooseBlockCount L cL (decide (i ∈ ms)) _ a hl
  obtain ⟨r,ht,hq⟩ := chooseBlockCount R cR (decide (i ∈ ts)) _ b hr
  refine ⟨m,r,by simpa using hm,by simpa using ht,?_⟩
  intro plan h₁ h₂
  let k (x : Word ℕ) := childRun (blockAt ms) n (i+1) (fun ys => assemble (toLex (x,ys))) u
  let l (x : Word ℕ) := childRun (blockAt ts) n (i+1) (fun ys => assemble (toLex (x,ys))) v
  apply synchronizeNodes f hf plan leaf leaf
    (fun p t => L (p.bind k) t) (fun p t => R (p.bind l) t)
    (fun t last h => hL (fun j => (t j).bind k) last h)
    (fun t last h => hR (fun j => (t j).bind l) last h) a b floor
  · rwa [h₁]
  · rwa [h₂]

-- A one-cut game 13 can finish the argument on its own even when game
-- 12 has several cuts. In each case the unmarked root suffix is plain.
theorem insideOtherSingleCut (G : SimpleGraph Tree) (f : ℕ → ℕ)
    (win : (game.score (wins G true)).outcome f true)
    (mark n : ℕ) (assemble : Tuple (Word ℕ) (n+1) → Tree) (last : ℕ)
    (h : LeftWin f G true ((node 1 leaf).bind (remainingBlocks [mark] mark n assemble)) last) :
    ∃ x y z, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z := by
  refine oneCutWinsTriangle G f win _ last ?_ h
  apply oneBeforePlain _ _ (oneMarkedNode leaf (fun _ => trivial) (fun _ => trivial))
  intro x
  apply plainBind
  swap
  · exact fun _ => trivial
  apply plainChildren
  intro j hj
  have hne : j ≠ mark := by omega
  change Plain (block (decide (j ∈ [mark])))
  simp only [List.mem_singleton,hne,decide_false]
  exact plainZeroNode leaf (fun _ => trivial)

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Filter Script

-- This composite step advances through a whole unmarked gap and the
-- following leaf. The clock at that leaf dominates every move in the gap.
theorem playToNextLeaf {V B C : Type} (f : ℕ → ℕ) (hf : StrictMono f)
    (L : Script B → ℕ → Prop) (R : Script C → ℕ → Prop)
    (hL : BuilderStep f L) (hR : BuilderStep f R)
    (ms ts : List ℕ) (i len mark : ℕ) (lo : i ≤ mark) (hi : mark < i+len)
    (gap : ∀ j, i ≤ j → j < mark → j ∉ ms ∧ j ∉ ts)
    (assemble : Tuple ℕ len → V) (u : V → Script B) (v : V → Script C)
    (a b floor : ℕ)
    (hl : L (childRun (leafRun ms) len i assemble u) a)
    (hr : R (childRun (leafRun ts) len i assemble v) b) :
    ∃ (m : ℕ) (put : Tuple ℕ m → V) (last : ℕ),
      mark + m + 1 = i+len ∧ floor < last ∧
      L (cutIf (decide (mark ∈ ms)) (childRun (leafRun ms) m (mark+1) put u)) last ∧
      R (cutIf (decide (mark ∈ ts)) (childRun (leafRun ts) m (mark+1) put v)) last := by
  have plain (j : ℕ) (hj : i ≤ j) (he : j < mark) :
      Plain (leafRun ms j) ∧ leafRun ms j = leafRun ts j := by
    obtain ⟨hm,ht⟩ := gap j hj he
    simp [leafRun,hm,ht]
    exact fun _ => trivial
  obtain ⟨m,put,opt,hm,hs,hp,hq⟩ := playChildPrefix f hf L R hL hR _ _ len i mark
    lo hi.le plain assemble u v a b floor hl hr
  cases m with
  | zero => omega
  | succ m =>
    obtain ⟨x,hx,hp',hq'⟩ := playSharedLeaf f hf L R hL hR ms ts mark m put u v
      _ _ (opt.getD floor) hp hq
    refine ⟨m,(fun xs => put (toLex (x,xs))),x,by omega,?_,hp',hq'⟩
    cases opt with
    | none => exact hx
    | some z => exact (hs z rfl).trans hx

-- These two positions use a single convention for the player about to
-- move. A left cut changes to right play, and a right cut restores left play.
def PairTurn {A B : Type} (f : ℕ → ℕ) (P : Option (A × B × Bool) → Prop)
    (left : Bool) (p : Script A) (q : Script B) (last : ℕ) : Prop :=
  ((increasing ((if left then p else .cut p).interleave q) last).score P).outcome f true

theorem leftCutTurn {A B : Type} (f : ℕ → ℕ) (P : Option (A × B × Bool) → Prop)
    (p : Script A) (q : Script B) (a : ℕ) :
    PairTurn f P true (.cut p) q a ↔ PairTurn f P false p q a := Iff.rfl

theorem rightCutTurn {A B : Type} (f : ℕ → ℕ) (P : Option (A × B × Bool) → Prop)
    (p : Script A) (q : Script B) (a : ℕ) :
    PairTurn f P false p (.cut q) a ↔ PairTurn f P true p q a := Iff.rfl

private theorem clockBuilder {A : Type} (f : ℕ → ℕ) (P : Option A → Prop) (hb : ¬ P none)
    (t : ℕ → LabelledGame (Option A)) (a : ℕ)
    (h : ((increasing (.builder t) a).score P).outcome f true) :
    ∀ᶠ k in atTop, ((increasing (t (f k)) (f k)).score P).outcome f true := by
  apply h.mono
  intro i hi
  change ((if a < f i then increasing (t (f i)) (f i) else LabelledGame.terminal none).score P).outcome f true at hi
  split at hi
  · exact hi
  · exact (hb hi).elim

theorem leftTurnBuilder {A B : Type} (f : ℕ → ℕ) (P : Option (A × B × Bool) → Prop)
    (hb : ¬ P none) (q : Script B) :
    BuilderStep f (fun p => PairTurn f P true p q) := by
  intro t a h
  exact clockBuilder f P hb (fun j => (t j).interleave q) a h

theorem rightTurnBuilder {A B : Type} (f : ℕ → ℕ) (P : Option (A × B × Bool) → Prop)
    (hb : ¬ P none) (p : Script A) :
    BuilderStep f (PairTurn f P false p) := by
  intro t a h
  exact clockBuilder f P hb (fun j => (cut p).interleave (t j)) a h

theorem leftTurnArchitect {A B : Type} (f : ℕ → ℕ) (P : Option (A × B × Bool) → Prop)
    (q : Script B) : ArchitectStep (fun p => PairTurn f P true p q) :=
  fun _ _ h => h

theorem rightTurnArchitect {A B : Type} (f : ℕ → ℕ) (P : Option (A × B × Bool) → Prop)
    (p : Script A) : ArchitectStep (PairTurn f P false p) :=
  fun _ _ h => h

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Filter Script

-- Tree 2 can open as soon as the left player of 12 has switched to it.
-- The root mark common to 12 and 23 is last for 12 and first for 23.
def outsideMiddleLayout (r d : ℕ) : List HeaderReader :=
  List.replicate r .first ++ [.both] ++ List.replicate d .second

theorem openOutsideMiddle (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (p : Script Tree) (r d a b floor : ℕ)
    (h₁ : PairTurn f (wins G false) false p (node (r+1) block) a)
    (h₂ : LeftWin f G false (node (d+1) block) b) :
    ∃ (xs : List (HeaderReader × ℕ)) (total : ℕ), xs.map Prod.fst = outsideMiddleLayout r d ∧
      (floor :: (xs.map Prod.snd ++ [total])).Pairwise (· < ·) ∧
      PairTurn f (wins G false) false p (nodeBody block (headerIndices false xs) total) total ∧
      LeftWin f G false (nodeBody block (headerIndices true xs) total) total := by
  apply synchronizeNodes f hf _ block block _ _ (rightTurnBuilder f _ id p)
    (leftWinStep f G false) a b floor
  · simpa [headerCount,outsideMiddleLayout,HeaderReader.reads] using h₁
  · simpa [headerCount,outsideMiddleLayout,HeaderReader.reads,Nat.add_comm] using h₂

-- At Tree 3 both games are reading their right endpoint. The outside
-- layout puts all 13 blocks first; the inside layout shares the last 23
-- block with the first 13 block.
def thirdRootLayout (r t : ℕ) : Bool → List HeaderReader
  | false => List.replicate (r+1) .first ++ List.replicate (t+1) .second
  | true => List.replicate t .second ++ [.both] ++ List.replicate r .first

theorem openThirdRoot (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (inside : Bool) (p q : Script Tree) (r t a b floor : ℕ)
    (h₁ : PairTurn f (wins G inside) false p (node (r+1) block) a)
    (h₂ : PairTurn f (wins G inside) false q (node (t+1) block) b) :
    ∃ (xs : List (HeaderReader × ℕ)) (total : ℕ), xs.map Prod.fst = thirdRootLayout r t inside ∧
      (floor :: (xs.map Prod.snd ++ [total])).Pairwise (· < ·) ∧
      PairTurn f (wins G inside) false p (nodeBody block (headerIndices false xs) total) total ∧
      PairTurn f (wins G inside) false q (nodeBody block (headerIndices true xs) total) total := by
  apply synchronizeNodes f hf _ block block _ _ (rightTurnBuilder f _ id p)
    (rightTurnBuilder f _ id q) a b floor
  · cases inside <;> simpa [headerCount,thirdRootLayout,HeaderReader.reads,Nat.add_comm] using h₁
  · cases inside <;> simpa [headerCount,thirdRootLayout,HeaderReader.reads,Nat.add_comm] using h₂

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script Filter

-- Facts true of every increasing play can be stored in the winning
-- condition. They then survive every later choice of a common Builder value.
private theorem strengthenClocked {A : Type} (f : ℕ → ℕ) (P Q : Option A → Prop)
    (hb : ¬ P none) (t : LabelledGame (Option A)) (a : ℕ)
    (all : ∀ x s, P (some x) → Follows t s (some x) →
      (a :: s.filterMap Event.number).Pairwise (· < ·) → Q (some x))
    (h : ((increasing t a).score P).outcome f true) :
    ((increasing t a).score Q).outcome f true := by
  induction t generalizing a with
  | terminal x =>
    cases x with
    | none => exact (hb h).elim
    | some x => exact all x [] h (.done _) (by simp)
  | architect t ih =>
    obtain ⟨n,hn⟩ := h
    exact ⟨n,ih n a (fun x s hx hs ho => all x (.architect n :: s) hx (.architect hs) ho) hn⟩
  | builder t ih =>
    apply h.mono
    intro i hi
    change ((if a < f i then increasing (t (f i)) (f i) else LabelledGame.terminal none).score P).outcome f true at hi
    change ((if a < f i then increasing (t (f i)) (f i) else LabelledGame.terminal none).score Q).outcome f true
    by_cases ha : a < f i
    · rw [if_pos ha] at hi ⊢
      apply ih _ _ _ hi
      intro x s hx hs ho
      apply all x (.builder (f i) :: s) hx (.builder hs)
      apply List.pairwise_cons.mpr
      refine ⟨?_,ho⟩
      intro j hj
      change j ∈ f i :: s.filterMap Event.number at hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ha
      · exact ha.trans ((List.pairwise_cons.mp ho).1 _ hj)
    · rw [if_neg ha] at hi
      exact (hb hi).elim

def FitsPivot (k j s : ℕ) (ds : List ℕ) : Prop :=
  ∃ count pre e tail, ds = count :: (pre ++ e :: tail) ∧ j = pre.length ∧
    s = (pre.map (·+1)).sum ∧ j < count ∧ s ≤ k ∧ k < s+(e+1)

def pivotWins (G : SimpleGraph Tree) (k j s : ℕ) :
    Option ((List ℕ × Tree) × (List ℕ × Tree) × Bool) → Prop
  | none => False
  | some ((_,x),(ds,y),b) => G.Adj x y ∧ b = true ∧ FitsPivot k j s ds

theorem enforceInsidePivot (G : SimpleGraph Tree) (f : ℕ → ℕ)
    (d mark n m k : ℕ) (rest : List (HeaderReader × ℕ))
    (assemble : Tuple (Word ℕ) (n+1) → Tree)
    (layout : ((HeaderReader.both,mark) :: rest).map Prod.fst = openingLayout d true)
    (ordered : (0 :: (mark :: (rest.map Prod.snd ++ [mark+n]))).Pairwise (· < ·))
    (hk : k+1 = m+1 - (if d=0 then 1 else 0))
    (pivot : Fin (k+1) × Fin (k+1)) (a : ℕ) :
    let p := (node (m+1) leaf).bind (remainingBlocks
      (headerIndices false ((HeaderReader.both,mark)::rest)) mark n assemble)
    PairTurn f (fun z => wins G true (forgetCounts z) ∧ opponentPivot k z = pivot)
      true (markCounts p []) (markCounts tree []) a →
    PairTurn f (pivotWins G k pivot.1.val pivot.2.val) true
      (markCounts p []) (markCounts tree []) a := by
  intro p h
  refine strengthenClocked f _ _ (fun h => h.1.elim) _ a ?_ h
  rintro ⟨⟨ns,x⟩,⟨ds,y⟩,b⟩ ev ⟨hw,hp⟩ he hs
  change G.Adj x y ∧ b = true at hw
  obtain ⟨hxy,rfl⟩ := hw
  obtain ⟨l,r,hl,hr,hw⟩ := readInterleave (markCounts p []) (markCounts tree []) he
  obtain ⟨count,pre,e,tail,hd,he,hj,hlo,hhi⟩ :=
    insidePivotInReply d mark n m k rest assemble layout ordered hk hl hr hw hs
  have hp' := congrArg (fun v : Fin (k+1) × Fin (k+1) => (v.1.val,v.2.val)) hp
  change ((cutPivot k ds.tail).1,(cutPivot k ds.tail).2) =
    (pivot.1.val,pivot.2.val) at hp'
  rw [he] at hp'
  obtain ⟨hp₁,hp₂⟩ := Prod.mk.inj hp'
  exact ⟨hxy,rfl,count,pre,e,tail,hd,hp₁.symm,hp₂.symm,hp₁ ▸ hj,hp₂ ▸ hlo,hp₂ ▸ hhi⟩

-- At the moment Tree 2 chooses its root count, the strengthened payoff
-- already implies that the pivot block is among those selected.
theorem pivotBeforeRootAllocation (G : SimpleGraph Tree) (f : ℕ → ℕ)
    (k j s a count : ℕ) (p : Script (List ℕ × Tree))
    (h : PairTurn f (pivotWins G k j s) false p (markCounts (node count block) [count]) a) :
    j < count := by
  obtain ⟨_,⟨ds,y⟩,_,_,_,_,hw,_,hr,_,_⟩ := completePairPosition f _ (fun h => h)
    (cut p) (markCounts (node count block) [count]) a h
  rcases hw.2.2 with ⟨c,pre,e,tail,hd,_,_,hj,_,_⟩
  have hist := (readCountHistory _ [count] hr).2
  rw [hd] at hist
  exact (List.cons.inj hist).1 ▸ hj

def insideMiddleLayout (count d j : ℕ) : List HeaderReader :=
  List.replicate j .first ++ List.replicate d .second ++ [.both] ++
    List.replicate (count-(j+1)) .first

theorem openInsideMiddle (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (k j s a b floor d : ℕ) (opponent : Script Tree) (p : Script (List ℕ × Tree))
    (h₁ : PairTurn f (pivotWins G k j s) false p (markCounts tree []) a)
    (h₂ : PairTurn f (wins G true) true (node (d+1) block) opponent b) :
    ∃ count, j < count ∧ ∃ (xs : List (HeaderReader × ℕ)) (total : ℕ),
      xs.map Prod.fst = insideMiddleLayout count d j ∧
      (floor :: (xs.map Prod.snd ++ [total])).Pairwise (· < ·) ∧
      PairTurn f (pivotWins G k j s) false p
        (markCounts (nodeBody block (headerIndices false xs) total) [count]) total ∧
      PairTurn f (wins G true) true (nodeBody block (headerIndices true xs) total) opponent total := by
  obtain ⟨count,hc⟩ := h₁
  have hj := pivotBeforeRootAllocation G f k j s a count p hc
  refine ⟨count,hj,?_⟩
  let L (q : Script Tree) := PairTurn f (pivotWins G k j s) false p (markCounts q [count])
  have step : BuilderStep f L := fun t last h =>
    rightTurnBuilder f (pivotWins G k j s) id p (fun v => markCounts (t v) [count]) last h
  apply synchronizeNodes f hf _ block block L (fun t => PairTurn f (wins G true) true t opponent) step
    (leftTurnBuilder f _ id opponent) a b floor
  · have he : headerCount false (insideMiddleLayout count d j) = count := by
      simp [headerCount,insideMiddleLayout,HeaderReader.reads]
      omega
    rwa [he]
  · simpa [headerCount,insideMiddleLayout,HeaderReader.reads,Nat.add_comm] using h₂

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script Filter

private theorem headerMemValues (b : Bool) (xs : List (HeaderReader × ℕ)) :
    ∀ j ∈ headerIndices b xs, j ∈ xs.map Prod.snd := by
  intro j hj
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
  exact List.mem_map.mpr ⟨p,(List.mem_filter.mp hp).1,rfl⟩

-- This is the first physical hand-off of both schedules. The same leaf
-- value updates both games, including the game whose reader skips the cut.
theorem firstLeafHandoff {B C : Type} (f : ℕ → ℕ) (hf : StrictMono f)
    (L : Script B → ℕ → Prop) (R : Script C → ℕ → Prop)
    (hL : BuilderStep f L) (hR : BuilderStep f R) (reader : HeaderReader)
    (hfirst : reader.reads false = true) (mark total a b floor : ℕ)
    (rest : List (HeaderReader × ℕ))
    (sorted : (0 :: mark :: (rest.map Prod.snd ++ [total])).Pairwise (· < ·))
    (u : Word ℕ → Script B) (v : Word ℕ → Script C) :
    let xs := (reader,mark)::rest
    L ((nodeBody leaf (headerIndices false xs) total).bind u) a →
    R ((nodeBody leaf (headerIndices true xs) total).bind v) b →
    ∃ (n last : ℕ) (put : Tuple ℕ n → Word ℕ), mark+n = total ∧ floor < last ∧
      L (.cut (childRun (leafRun (headerIndices false xs)) n (mark+1) put u)) last ∧
      R (cutIf (reader.reads true) (childRun (leafRun (headerIndices true xs)) n
        (mark+1) put v)) last := by
  intro xs hl hr
  simp only [nodeBody,bindAssocScript,Script.bind] at hl hr
  have lo := (List.pairwise_cons.mp sorted).1 mark List.mem_cons_self
  have lower := (List.pairwise_cons.mp (List.pairwise_cons.mp sorted).2).1
  have hi := lower total (List.mem_append_right _ List.mem_cons_self)
  have gap (c : Bool) (j : ℕ) (hj : j < mark) : j ∉ headerIndices c xs := by
    intro mem
    have hv := headerMemValues c xs j mem
    rcases List.mem_cons.mp hv with e | hh
    · omega
    · exact hj.asymm (lower j (List.mem_append_left _ hh))
  obtain ⟨n,put,last,hn,hclock,hp,hq⟩ := playToNextLeaf f hf L R hL hR _ _ 1 total mark lo
    (by omega) (fun z _ hz => ⟨gap false z hz,gap true z hz⟩) _ u v a b floor hl hr
  have nr (c : Bool) : mark ∉ headerIndices c rest := fun h =>
    lt_irrefl mark (lower mark (List.mem_append_left _ (headerMemValues c rest mark h)))
  have test (c : Bool) : decide (mark ∈ headerIndices c xs) = reader.reads c := by
    cases e : reader.reads c with
    | false =>
      have he : headerIndices c xs = headerIndices c rest := by
        simp [xs,headerIndices,e]
      simp [he,nr c]
    | true =>
      have he : headerIndices c xs = mark :: headerIndices c rest := by
        simp [xs,headerIndices,e]
      simp [he]
  rw [test false,hfirst] at hp
  rw [test true] at hq
  exact ⟨n,last,put,by omega,hclock,hp,hq⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Filter Script

theorem openOutsideMiddleFromCut (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (p : Script Tree) (d a b floor : ℕ)
    (h₁ : PairTurn f (wins G false) false p tree a)
    (h₂ : LeftWin f G false (node (d+1) block) b) :
    ∃ (r : ℕ) (xs : List (HeaderReader × ℕ)) (total : ℕ), xs.map Prod.fst = outsideMiddleLayout r d ∧
      (floor :: (xs.map Prod.snd ++ [total])).Pairwise (· < ·) ∧
      PairTurn f (wins G false) false p (nodeBody block (headerIndices false xs) total) total ∧
      LeftWin f G false (nodeBody block (headerIndices true xs) total) total := by
  obtain ⟨r,hr⟩ := h₁
  cases r with
  | zero =>
    have h := noCutsRight p (node 0 block) (noCutsNode _ (noCutsNode leaf (fun _ => trivial)))
      (wins G false) id f a hr
    obtain ⟨_,hx⟩ := forceWitness _ _ _ h
    obtain ⟨_,hb⟩ := forceWitness _ _ _ hx
    exact Bool.noConfusion hb.2
  | succ r => exact ⟨r,openOutsideMiddle G f hf p r d a b floor hr h₂⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Filter Script

-- A completed edge only imposes a one-tree restriction on its unfinished
-- endpoint. Transfer that restriction to the other decoration of the same
-- physical suffix, even if it still has many switches to make.
def Transfers {A : Type} (f : ℕ → ℕ) (p q : Script A) : Prop :=
  ∀ P, Force f P p → Keep f P q

private theorem keepMono {A : Type} (f : ℕ → ℕ) (p : Script A) (P Q : A → Prop)
    (implies : ∀ x, P x → Q x) (h : Keep f P p) : Keep f Q p := by
  induction p with
  | done => exact implies _ h
  | cut p ih => exact ih h
  | architect t ih => exact fun i => ih i (h i)
  | builder t ih => exact h.mono fun i hi => ih _ hi

theorem Transfers.bind {A B : Type} {f : ℕ → ℕ} {p q : Script A}
    {k l : A → Script B} (hp : Transfers f p q) (hkl : ∀ x, Transfers f (k x) (l x)) :
    Transfers f (p.bind k) (q.bind l) := by
  intro P h
  apply (keepBind ..).mpr
  exact keepMono f q _ _ (fun x => hkl x P) (hp _ ((forceBind ..).mp h))

theorem Transfers.children {A : Type} {f : ℕ → ℕ} {p q : ℕ → Script A}
    (n i : ℕ) (h : ∀ j, i ≤ j → Transfers f (p j) (q j)) :
    Transfers f (children p n i) (children q n i) := by
  induction n generalizing i with
  | zero => exact fun _ h => h
  | succ n ih =>
    apply (h i le_rfl).bind
    intro x
    exact (ih (i+1) (fun j hj => h j (by omega))).bind fun _ _ h => h

theorem transfersBlocks (f : ℕ → ℕ) (ms ts : List ℕ) (i : ℕ) :
    Transfers f (blockAt ms i) (blockAt ts i) := by
  intro P h
  have k (b : Bool) (Q : ℕ → Prop) : Keep f Q (leaf b) ↔ leafQuantifier f Q := by
    cases b <;> rfl
  have s (b : Bool) (Q : ℕ → Prop) : Force f Q (leaf b) ↔ leafQuantifier f Q := by
    cases b <;> rfl
  cases e : decide (i ∈ ms) <;> cases e' : decide (i ∈ ts) <;>
    simpa [blockAt,e,e',block,Keep,nodeKeep f leaf _ k] using
      (show wordQuantifier f (leafQuantifier f) P by
        simpa [blockAt,e,block,Force,nodeForce f leaf _ s] using h)

theorem transfersChildRun {A V B : Type} (f : ℕ → ℕ) (p q : ℕ → Script A)
    (n i : ℕ) (assemble : Tuple A n → V) (k l : V → Script B)
    (hc : ∀ j, i ≤ j → Transfers f (p j) (q j)) (hk : ∀ x, Transfers f (k x) (l x)) :
    Transfers f (childRun p n i assemble k) (childRun q n i assemble l) :=
  (Transfers.children n i hc).bind fun _ => hk _

private theorem winAndKeeps {A : Type} (f : ℕ → ℕ) (p : LabelledGame A) (P Q : A → Prop)
    (h : (p.score P).outcome f true) (hq : Keeps f Q p) :
    (p.score (fun x => P x ∧ Q x)).outcome f true := by
  induction p with
  | terminal => exact ⟨h,hq⟩
  | architect t ih =>
    obtain ⟨i,hi⟩ := h
    exact ⟨i,ih i hi (hq i)⟩
  | builder t ih => exact (h.and hq).mono fun _ hi => ih _ hi.1 hi.2

theorem retainEndpointRestrictions {A B : Type} (f : ℕ → ℕ) (p : Script A) (q : Script B)
    (left : Bool) (a : ℕ) (P : Option (A × B × Bool) → Prop) (U : A → Prop) (V : B → Prop)
    (hp : Keep f U p) (hq : Keep f V q) (win : PairTurn f P left p q a) :
    PairTurn f (fun z => P z ∧ pairProperty U V z) left p q a := by
  apply winAndKeeps _ _ _ _ win
  apply keepsIncreasing _ _ trivial
  apply keepsInterleave _ _ _ _ q _ hq
  cases left <;> exact hp

-- Once one vertex x is fixed, finish the remaining game with both
-- endpoint restrictions. The remaining game may be on either player's turn.
theorem closeRemainingPair (G : SimpleGraph Tree) (f : ℕ → ℕ) (x : Tree)
    (p q : Script Tree) (active inside : Bool) (last : ℕ)
    (hp : Keep f (G.Adj x) p) (hq : Keep f (G.Adj x) q)
    (h : PairTurn f (wins G inside) active p q last) :
    ∃ y z, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z := by
  have hw := retainEndpointRestrictions f p q active last _ _ _ hp hq h
  obtain ⟨⟨y,z,b⟩,_,hs,_,_⟩ := clockedWitness f _ (fun h => h.1.elim)
    ((if active then p else cut p).interleave q) last hw
  exact ⟨y,z,hs.2.1,hs.2.2,hs.1.1⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Filter Script

-- After fixing the pivot, the strengthened payoff must be kept during the
-- first block allocation. This version takes any payoff on the two recorded
-- scripts, including the one that enforces the pivot inequalities.
private theorem insideFirstLeaf (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (P : Option ((List ℕ × Tree) × (List ℕ × Tree) × Bool) → Prop) (hb : ¬ P none)
    (s k m r a b floor : ℕ) (hs : s ≤ k) (hk : k ≤ m)
    (u v : Word ℕ → Script Tree)
    (hl : PairTurn f P true (markCounts ((node (m+1) leaf).bind u) []) (markCounts tree []) a)
    (hr : LeftWin f G true ((node (r+1) leaf).bind v) b) :
    ∃ (marks : List (HeaderReader × ℕ)) (idx n last : ℕ) (put : Tuple ℕ n → Word ℕ),
      marks.map Prod.fst = insideLeafLayout s (k+1) m r ∧ (marks.map Prod.snd).head? = some idx ∧
      (0 :: (marks.map Prod.snd ++ [idx+n])).Pairwise (· < ·) ∧ idx+n < last ∧ floor < last ∧
      PairTurn f P false
        (markCounts (childRun (leafRun (headerIndices false marks)) n (idx+1) put u) [])
        (markCounts tree []) last ∧
      LeftWin f G true (cutIf (decide (s=0))
        (childRun (leafRun (headerIndices true marks)) n (idx+1) put v)) last := by
  let L (p : Script Tree) := PairTurn f P true (markCounts p []) (markCounts tree [])
  have step : BuilderStep f L := fun t a h =>
    leftTurnBuilder f P hb (markCounts tree []) (fun j => markCounts (t j) []) a h
  let plan := insideLeafLayout s (k+1) m r
  have cm : headerCount false plan = m+1 := by
    simp [plan,headerCount,insideLeafLayout,HeaderReader.reads]
    omega
  have cr : headerCount true plan = r+1 := by
    simp [plan,headerCount,insideLeafLayout,HeaderReader.reads]
  obtain ⟨xs,total,layout,sorted,hp,hq⟩ := synchronizeNodes f hf plan leaf leaf
    (fun p => L (p.bind u)) (fun p => LeftWin f G true (p.bind v))
    (fun t a h => step (fun j => (t j).bind u) a h)
    (fun t a h => leftWinStep f G true (fun j => (t j).bind v) a h) a b floor
    (cm ▸ hl) (cr ▸ hr)
  cases xs with
  | nil => cases s <;> simp [plan,insideLeafLayout,List.replicate_succ] at layout
  | cons x rest =>
    obtain ⟨rd,idx⟩ := x
    have read : rd.reads false = true ∧ rd.reads true = decide (s = 0) := by
      cases s with
      | zero =>
        have h : rd = .both := (List.cons.inj (by
          simpa only [plan,insideLeafLayout,List.replicate_zero,List.nil_append,List.cons_append,
            List.map_cons] using layout)).1
        subst rd
        decide
      | succ s =>
        have h : rd = .first := (List.cons.inj (by
          simpa only [plan,insideLeafLayout,List.replicate_succ,List.cons_append,List.map_cons] using layout)).1
        subst rd
        exact ⟨rfl,rfl⟩
    have sorted' : (0 :: idx :: (rest.map Prod.snd ++ [total])).Pairwise (· < ·) :=
      List.pairwise_cons.mpr ⟨fun j hj => (Nat.zero_le floor).trans_lt
        ((List.pairwise_cons.mp sorted).1 j hj),(List.pairwise_cons.mp sorted).2⟩
    obtain ⟨n,last,put,hn,ht,hL,hR⟩ := firstLeafHandoff f hf L (LeftWin f G true)
      step (leftWinStep f G true) rd read.1 idx total total total total rest sorted' u v hp hq
    rw [read.2] at hR
    exact ⟨_,idx,n,last,put,layout,rfl,by simpa only [hn,List.map_cons,List.cons_append] using sorted',by simpa only [hn] using ht,((List.pairwise_cons.mp sorted).1 total
      (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))).trans ht,hL,hR⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

structure InsideHandoff (G : SimpleGraph Tree) (f : ℕ → ℕ) (d : ℕ) where
  mark : ℕ
  rest : List (HeaderReader × ℕ)
  n : ℕ
  put : Tuple (Word ℕ) (n+1) → Tree
  m : ℕ
  r : ℕ
  k : ℕ
  j : ℕ
  s : ℕ
  rootOrder : ((HeaderReader.both,mark)::rest).map Prod.fst = openingLayout d true
  rootClock : (0 :: mark :: (rest.map Prod.snd ++ [mark+n])).Pairwise (· < ·)
  threshold : k+1 = m+1 - (if d=0 then 1 else 0)
  offsetBound : s ≤ k
  secondMulti : d ≠ 0 ∨ r ≠ 0
  leaves : List (HeaderReader × ℕ)
  leafOrder : leaves.map Prod.fst = insideLeafLayout s (k+1) m r
  idx : ℕ
  len : ℕ
  last : ℕ
  firstLeafIndex : (leaves.map Prod.snd).head? = some idx
  leafClock : (0 :: (leaves.map Prod.snd ++ [idx+len])).Pairwise (· < ·)
  afterLeaf : idx+len < last
  pack : Tuple ℕ len → Word ℕ
  count : ℕ
  pivotBound : j < count
  middle : List (HeaderReader × ℕ)
  size : ℕ
  middleOrder : middle.map Prod.fst = insideMiddleLayout count d j
  middleClock : (last :: (middle.map Prod.snd ++ [size])).Pairwise (· < ·)
  game12 : PairTurn f (pivotWins G k j s) false
    (markCounts (childRun (leafRun (headerIndices false leaves)) len (idx+1) pack
      (remainingBlocks (headerIndices false ((HeaderReader.both,mark)::rest)) mark n put)) [])
    (markCounts (nodeBody block (headerIndices false middle) size) [count]) size
  game13 : LeftWin f G true (cutIf (decide (s=0))
    (childRun (leafRun (headerIndices true leaves)) len (idx+1) pack
      (remainingBlocks (headerIndices true ((HeaderReader.both,mark)::rest)) mark n put))) last
  game23 : PairTurn f (wins G true) true (nodeBody block (headerIndices true middle) size) positiveTree size

theorem insideFirstHandoff (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (d : ℕ) (h : LeftWin f G true (node (d+1) block) 0) :
    (∃ x y z, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z) ∨
      ∃ g : ℕ → ℕ, StrictMono g ∧ Nonempty (InsideHandoff G (f ∘ g) d) := by
  obtain tri | ⟨mark,rest,total,n,put,m,r,a,b,k,g,pivot,ord,sorted,hn,hk,hg,hp,hq,h₂⟩ :=
    prepareInsideOpening G f hf d h
  · exact Or.inl tri
  subst total
  by_cases multi : d ≠ 0 ∨ r ≠ 0
  · obtain tri | hpos := positiveReplyOrTriangle G (f ∘ g) (d+1) true h₂
    · exact Or.inl tri
    right
    have pred := enforceInsidePivot G (f ∘ g) d mark n m k rest put ord sorted hk pivot a hp
    have km : k ≤ m := by split at hk <;> omega
    obtain ⟨leaves,idx,len,last,pack,hlo,hfirst,hleaf,hafter,_,h₁,h₃⟩ := insideFirstLeaf G (f ∘ g) (hf.comp hg)
      (pivotWins G k pivot.1.val pivot.2.val) id pivot.2.val k m r a b (max a b)
      (by have := pivot.2.isLt; omega) km _ _ pred hq
    obtain ⟨count,hcount,middle,size,hmo,hmclock,h₄,h₅⟩ :=
      openInsideMiddle G (f ∘ g) (hf.comp hg) _ _ _ last 0 last d positiveTree _ h₁ hpos
    exact ⟨g,hg,⟨⟨mark,rest,n,put,m,r,k,pivot.1.val,pivot.2.val,ord,sorted,hk,by have := pivot.2.isLt; omega,multi,
      leaves,hlo,idx,len,last,hfirst,hleaf,hafter,pack,count,hcount,middle,size,hmo,hmclock,h₄,h₃,h₅⟩⟩⟩
  · left
    push Not at multi
    obtain ⟨rfl,rfl⟩ := multi
    have empty : rest = [] := by simpa [openingLayout] using (List.cons.inj ord).2
    subst rest
    exact insideOtherSingleCut G (f ∘ g) ⟨1,h₂⟩ mark n put b hq

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

-- Once 12 has committed counts through the pivot block, its partial
-- history determines the offset and gives enough leaves for the shared cut.
theorem pivotAtBlockAllocation (G : SimpleGraph Tree) (f : ℕ → ℕ)
    (k j s last count e : ℕ) (pre : List ℕ) (here : pre.length = j)
    (p : Script (List ℕ × Tree)) (q : Script Tree) (left : Bool)
    (h : PairTurn f (pivotWins G k j s) left p (markCounts q (count :: (pre ++ [e]))) last) :
    s = (pre.map (·+1)).sum ∧ s ≤ k ∧ k-s < e+1 := by
  obtain ⟨_,⟨ds,y⟩,_,_,_,_,hw,_,hr,_,_⟩ := completePairPosition f _ (fun h => h)
    (if left then p else cut p) (markCounts q (count :: (pre ++ [e]))) last h
  obtain ⟨_,u,m,tail,hd,hj,hs,_,lo,hi⟩ := hw.2.2
  have hist := (readCountHistory _ _ hr).2
  rw [hd] at hist
  have eq := (List.cons.inj hist).2
  change u ++ m::tail = (pre ++ [e]) ++ _ at eq
  rw [List.append_assoc,List.singleton_append] at eq
  have len : u.length = pre.length := hj.symm.trans here.symm
  have hpre := congrArg (List.take pre.length) eq
  simp only [← len,List.take_left] at hpre
  have hup : u = pre := by
    simpa only [len,List.take_left] using hpre
  subst u
  have htail := List.append_cancel_left eq
  have he := (List.cons.inj htail).1
  exact ⟨hs,lo,by omega⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Filter Script

-- Only the unconsumed marks occur in the cursor. Thus reading a marked
-- child deletes exactly one reader tag, independent of the size of the gap.
structure NodeCursor (A V : Type) (plan : List HeaderReader) where
  start : ℕ
  len : ℕ
  put : Tuple A len → V
  marks : List (HeaderReader × ℕ)
  roles : marks.map Prod.fst = plan
  lower : ∀ j ∈ marks.map Prod.snd, start ≤ j
  ordered : (marks.map Prod.snd ++ [start+len]).Pairwise (· < ·)

def NodeCursor.run {A V B : Type} {plan : List HeaderReader} (c : NodeCursor A V plan)
    (side : Bool) (child : Bool → Script A) (k : V → Script B) : Script B :=
  childRun (fun j => child (decide (j ∈ headerIndices side c.marks))) c.len c.start c.put k

private theorem childrenCongrFrom {A : Type} (p q : ℕ → Script A)
    (n i : ℕ) (he : ∀ j, i ≤ j → p j = q j) : children p n i = children q n i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [children,he i le_rfl,ih (i+1) (fun j hj => he j (by omega))]

private theorem headerTailMem (head : HeaderReader) (idx j : ℕ) (xs : List (HeaderReader × ℕ))
    (b : Bool) (hne : j ≠ idx) :
    j ∈ headerIndices b ((head,idx)::xs) ↔ j ∈ headerIndices b xs := by
  cases h : head.reads b <;> simp [headerIndices,h,hne]

private theorem headerHeadTest (rd : HeaderReader) (idx : ℕ) (xs : List (HeaderReader × ℕ))
    (b : Bool) (h : idx ∉ xs.map Prod.snd) :
    decide (idx ∈ headerIndices b ((rd,idx)::xs)) = rd.reads b := by
  cases e : rd.reads b with
  | false =>
    have he : headerIndices b ((rd,idx)::xs) = headerIndices b xs := by simp [headerIndices,e]
    simp [he,show idx ∉ headerIndices b xs from fun ht => h (headerMemValues b xs idx ht)]
  | true =>
    have he : headerIndices b ((rd,idx)::xs) = idx :: headerIndices b xs := by simp [headerIndices,e]
    simp [he]

theorem NodeCursor.split {A V B C : Type} {rd : HeaderReader} {rest : List HeaderReader}
    (c : NodeCursor A V (rd::rest)) (child : Bool → Script A) (plain : Plain (child false))
    (f : ℕ → ℕ) (hf : StrictMono f) (L : Script B → ℕ → Prop) (R : Script C → ℕ → Prop)
    (stepL : BuilderStep f L) (stepR : BuilderStep f R) (u : V → Script B) (v : V → Script C)
    (a b floor : ℕ) (hl : L (c.run false child u) a) (hr : R (c.run true child v) b) :
    ∃ (tail : NodeCursor A (A → V) rest) (opt : Option ℕ), (∀ z ∈ opt, floor < z) ∧
      L ((child (rd.reads false)).bind (fun x => tail.run false child (fun g => u (g x)))) (opt.getD a) ∧
      R ((child (rd.reads true)).bind (fun x => tail.run true child (fun g => v (g x)))) (opt.getD b) := by
  obtain ⟨i,len,put,marks,roles,lower,ordered⟩ := c
  cases marks with
  | nil => cases roles
  | cons pair marks =>
    obtain ⟨rd',idx⟩ := pair
    obtain ⟨rfl,tailRoles⟩ := List.cons.inj roles
    let xs := (rd',idx)::marks
    let p (b : Bool) (j : ℕ) := child (decide (j ∈ headerIndices b xs))
    have lo := lower idx List.mem_cons_self
    have above := (List.pairwise_cons.mp ordered).1
    have hi := above (i+len) (List.mem_append_right _ List.mem_cons_self)
    have gap (b : Bool) (j : ℕ) (hj : j < idx) : j ∉ headerIndices b xs := by
      intro h
      rcases List.mem_cons.mp (headerMemValues b _ _ h) with h | h
      · omega
      · exact hj.asymm (above _ (List.mem_append_left _ h))
    have fine (j : ℕ) (_ : i ≤ j) (hj : j < idx) : Plain (p false j) ∧ p false j = p true j := by
      simpa [p,gap false j hj,gap true j hj] using plain
    obtain ⟨n,put',opt,hn,hclock,hp,hq⟩ := playChildPrefix f hf L R stepL stepR
      (p false) (p true) len i idx lo hi.le fine put u v a b floor hl hr
    cases n with
    | zero => omega
    | succ n =>
      let tail : NodeCursor A (A → V) rest :=
        ⟨idx+1,n,(fun ys x => put' (toLex (x,ys))),marks,tailRoles,
          (fun j hj => above _ (List.mem_append_left _ hj)),by
            rw [show idx+1+n = i+len by omega]
            exact (List.pairwise_cons.mp ordered).2⟩
      have hd (b : Bool) : p b idx = child (rd'.reads b) := congrArg child
        (headerHeadTest rd' idx marks b (fun h => lt_irrefl _ (above _ (List.mem_append_left _ h))))
      have rem (b : Bool) : children (p b) n (idx+1) =
          children (fun j => child (decide (j ∈ headerIndices b marks))) n (idx+1) := by
        apply childrenCongrFrom
        intro j hj
        simp only [p,xs,headerTailMem rd' idx j marks b (by omega)]
      rw [childRunSucc,hd] at hp hq
      simp only [childRun,rem] at hp hq
      exact ⟨tail,opt,hclock,hp,hq⟩

theorem NodeCursor.finish {A V B C : Type} (c : NodeCursor A V [])
    (child : Bool → Script A) (plain : Plain (child false))
    (f : ℕ → ℕ) (hf : StrictMono f) (L : Script B → ℕ → Prop) (R : Script C → ℕ → Prop)
    (stepL : BuilderStep f L) (stepR : BuilderStep f R) (u : V → Script B) (v : V → Script C)
    (a b floor : ℕ) (hl : L (c.run false child u) a) (hr : R (c.run true child v) b) :
    ∃ (x : V) (opt : Option ℕ), (∀ z ∈ opt, floor < z) ∧ L (u x) (opt.getD a) ∧ R (v x) (opt.getD b) := by
  obtain ⟨i,n,put,marks,roles,_,_⟩ := c
  have empty : marks = [] := by simpa using roles
  subst marks
  let p := (children (fun _ => child false) n i).bind fun xs => done (put xs)
  have hp : Plain p := plainBind _ _ (plainChildren _ _ _ (fun _ _ => plain)) fun _ => trivial
  apply synchronizePlain f hf p hp u v L R stepL stepR a b floor
  · simpa [p,bindAssocScript,Script.bind,NodeCursor.run,childRun,headerIndices] using hl
  · simpa [p,bindAssocScript,Script.bind,NodeCursor.run,childRun,headerIndices] using hr

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script Filter

def NodeCursor.map {A V W : Type} {plan : List HeaderReader}
    (c : NodeCursor A V plan) (g : V → W) : NodeCursor A W plan :=
  { c with put := g ∘ c.put }

private theorem NodeCursor.runMap {A V W B : Type} {rs : List HeaderReader}
    (c : NodeCursor A V rs) (g : V → W) (side : Bool) (child : Bool → Script A)
    (k : W → Script B) :
    (c.map g).run side child k = c.run side child (fun x => k (g x)) := rfl

-- Running this operation repeatedly follows exactly the tags in a leaf
-- header. Each step may use new game positions and a new global clock.
theorem NodeCursor.playLeaf {V B C : Type} {rd : HeaderReader} {rs : List HeaderReader}
    (c : NodeCursor ℕ V (rd::rs)) (f : ℕ → ℕ) (hf : StrictMono f)
    (L : Script B → ℕ → Prop) (R : Script C → ℕ → Prop)
    (stepL : BuilderStep f L) (stepR : BuilderStep f R) (u : V → Script B) (v : V → Script C)
    (a b floor : ℕ) (hl : L (c.run false leaf u) a) (hr : R (c.run true leaf v) b) :
    ∃ (tail : NodeCursor ℕ V rs) (last : ℕ), floor < last ∧
      L (cutIf (rd.reads false) (tail.run false leaf u)) last ∧
      R (cutIf (rd.reads true) (tail.run true leaf v)) last := by
  obtain ⟨tail,opt,hs,hp,hq⟩ := c.split leaf (fun _ => trivial) f hf L R stepL stepR
    u v a b floor hl hr
  have fresh : ∀ᶠ k in atTop, opt.getD floor < f k :=
    (eventually_gt_atTop _).mono fun k hk => hk.trans_le (hf.id_le k)
  obtain ⟨k,hk,hp',hq'⟩ := (fresh.and ((stepL _ _ hp).and (stepR _ _ hq))).exists
  refine ⟨tail.map (fun g => g (f k)),f k,?_,?_,?_⟩
  · cases opt with
    | none => exact hk
    | some t => exact (hs t rfl).trans hk
  · rw [NodeCursor.runMap]
    cases he : rd.reads false <;> simpa only [he,leaf,cutIf,Script.bind,Bool.false_eq_true,
      if_false,if_true] using hp'
  · rw [NodeCursor.runMap]
    cases he : rd.reads true <;> simpa only [he,leaf,cutIf,Script.bind,Bool.false_eq_true,
      if_false,if_true] using hq'

-- The initial cursor records all of the numbers allocated by the node
-- header; successful opening requires no assumption about their spacing.
def NodeCursor.ofHeader {A : Type} (xs : List (HeaderReader × ℕ)) (total floor : ℕ)
    (h : (floor :: (xs.map Prod.snd ++ [total])).Pairwise (· < ·)) :
    NodeCursor A (Word A) (xs.map Prod.fst) where
  start := 1
  len := total
  put := fun ys => ⟨total,ys⟩
  marks := xs
  roles := rfl
  lower := fun j hj => (Nat.zero_le floor).trans_lt
    ((List.pairwise_cons.mp h).1 j (List.mem_append_left _ hj))
  ordered := by
    obtain ⟨ha,_,hu⟩ := List.pairwise_append.mp (List.pairwise_cons.mp h).2
    apply List.pairwise_append.mpr
    refine ⟨ha,by simp,?_⟩
    intro i hi j hj
    obtain rfl := List.mem_singleton.mp hj
    have := hu i hi total List.mem_cons_self
    omega

theorem NodeCursor.runOfHeader {A B : Type} (xs : List (HeaderReader × ℕ)) (total floor : ℕ)
    (h : (floor :: (xs.map Prod.snd ++ [total])).Pairwise (· < ·)) (b : Bool)
    (child : Bool → Script A) (k : Word A → Script B) :
    (NodeCursor.ofHeader xs total floor h).run b child k =
      (nodeBody child (headerIndices b xs) total).bind k := by
  simp only [NodeCursor.ofHeader,NodeCursor.run,childRun,nodeBody,bindAssocScript,Script.bind]
  rfl

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

private theorem forcesMono {A : Type} (f : ℕ → ℕ) (p : Script A) (P Q : A → Prop)
    (imp : ∀ x, P x → Q x) (h : Force f P p) : Force f Q p := by
  induction p with
  | done => exact imp _ h
  | cut p ih => exact ih h
  | architect t ih =>
    obtain ⟨i,hi⟩ := h
    exact ⟨i,ih _ hi⟩
  | builder t ih => exact h.mono fun _ hi => ih _ hi

private theorem keepTrue {A : Type} (f : ℕ → ℕ) (p : Script A) : Keep f (fun _ => True) p := by
  induction p with
  | done => trivial
  | cut p ih => exact ih
  | architect t ih => exact ih
  | builder t ih => exact Filter.Eventually.of_forall fun i => ih _

-- After Tree 1 has made all its 12 cuts, its eventual choice of x
-- guarantees enough completions of Tree 2 adjacent to x. Store this
-- promise in game 13 while it continues building x with Tree 3.
def outsidePromise (G : SimpleGraph Tree) (f : ℕ → ℕ) (y : Script Tree)
    (z : Option (Tree × Tree × Bool)) : Prop :=
  wins G false z ∧ pairProperty (fun x => Force f (G.Adj x) y) (fun _ => True) z

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

theorem forgetPivotAfterHandoff (G : SimpleGraph Tree) (f : ℕ → ℕ)
    (k j s a : ℕ) (x y : Script Tree) (xs ys : List ℕ) (active : Bool)
    (h : PairTurn f (pivotWins G k j s) active (markCounts x xs) (markCounts y ys) a) :
    PairTurn f (wins G true) active x y a := by
  let p := if active then x else cut x
  let raw := (markCounts p xs).interleave (markCounts y ys)
  have he : (if active then markCounts x xs else cut (markCounts x xs)) = markCounts p xs := by
    cases active <;> rfl
  change ((increasing ((if active then markCounts x xs else cut (markCounts x xs)).interleave _) a).score
    _).outcome f true at h
  rw [he] at h
  have hw : ((increasing raw a).score (wins G true ∘ forgetCounts)).outcome f true := by
    apply strengthenClocked f (pivotWins G k j s) _ id raw a _ h
    rintro ⟨⟨_,v⟩,⟨_,w⟩,b⟩ _ hv _ _
    exact ⟨hv.1,hv.2.1⟩
  rw [← LabelledGame.scoreMapLabel,mapIncreasing forgetCounts rfl,show raw = _ from rfl,
    interleaveCounts] at hw
  exact hw

def insidePromise (G : SimpleGraph Tree) (f : ℕ → ℕ) (y : Script Tree)
    (z : Option (Tree × Tree × Bool)) : Prop :=
  wins G true z ∧ pairProperty (fun _ => True) (fun w => Force f (fun v => G.Adj v w) y) z

theorem absorbInside23 (G : SimpleGraph Tree) (f : ℕ → ℕ)
    (y z x z' : Script Tree) (active : Bool) (a b : ℕ)
    (hz : NoCuts z) (share : Transfers f z z')
    (h₂ : PairTurn f (wins G true) false y z a)
    (h₁ : PairTurn f (wins G true) active x z' b) :
    PairTurn f (insidePromise G f y) active x z' b := by
  have hw := noCutsRight y z hz (wins G true) id f a h₂
  have hz' : Keep f (fun w => Force f (fun v => G.Adj v w) y) z' :=
    share _ (forcesMono f z _ _ (fun w hw => forcesMono f y _ _ (fun _ h => h.1) hw) hw)
  exact retainEndpointRestrictions f x z' active b _ _ _ (keepTrue f x) hz' h₁

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

private theorem positiveCountAtCut (G : SimpleGraph Tree) (f : ℕ → ℕ) (inside : Bool)
    (win : (game.score (wins G inside)).outcome f true) (p : Script Tree) (last : ℕ)
    (hp : Neutral f p) (h : PairTurn f (wins G inside) false p tree last) :
    (∃ x y z, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z) ∨
      ∃ r, PairTurn f (wins G inside) false p (node (r+1) block) last := by
  obtain ⟨r,hr⟩ := h
  cases r with
  | succ r => exact Or.inr ⟨r,hr⟩
  | zero =>
    let good (v : Tree) := Force f (fun x => wins G inside (some (x,v,true))) p
    have hg : Force f good tree := ⟨0,noCutsRight p (node 0 block)
      (noCutsNode _ (noCutsNode leaf (fun _ => trivial))) (wins G inside) id f last hr⟩
    obtain ⟨y,z,hy,hz,hyz⟩ := winningEdgeWithin G f inside win good good hg hg
    obtain ⟨x,hxy,hxz⟩ := neutralCompatible p f hp _ _ hy hz
    exact Or.inl ⟨x,y,z,hxy.1,hxz.1,hyz⟩

theorem thirdRootFromCuts (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (inside : Bool) (win : (game.score (wins G inside)).outcome f true)
    (p q : Script Tree) (a b floor : ℕ) (hp : Neutral f p)
    (h₁ : PairTurn f (wins G inside) false p tree a)
    (h₂ : PairTurn f (wins G inside) false q positiveTree b) :
    (∃ x y z, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z) ∨
    ∃ (r t : ℕ) (xs : List (HeaderReader × ℕ)) (total : ℕ),
      xs.map Prod.fst = thirdRootLayout r t inside ∧
      (floor :: (xs.map Prod.snd ++ [total])).Pairwise (· < ·) ∧
      PairTurn f (wins G inside) false p (nodeBody block (headerIndices false xs) total) total ∧
      PairTurn f (wins G inside) false q (nodeBody block (headerIndices true xs) total) total := by
  obtain tri | ⟨r,hr⟩ := positiveCountAtCut G f inside win p a hp h₁
  · exact Or.inl tri
  obtain ⟨t,ht⟩ := h₂
  exact Or.inr ⟨r,t,openThirdRoot G f hf inside p q r t a b floor hr ht⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Filter Script

-- Open a singly marked block and advance immediately to its first leaf
-- switch. The inactive decoration reads that whole prefix without a cut.
theorem NodeCursor.firstExclusive {V B C : Type} {rd : HeaderReader} {rs : List HeaderReader}
    (c : NodeCursor (Word ℕ) V (rd :: rs)) (f : ℕ → ℕ) (hf : StrictMono f)
    (sole : rd = .first ∨ rd = .second)
    (L : Script B → ℕ → Prop) (R : Script C → ℕ → Prop)
    (stepL : BuilderStep f L) (stepR : BuilderStep f R)
    (archL : rd.reads false = true → ArchitectStep L) (archR : rd.reads true = true → ArchitectStep R)
    (u : V → Script B) (v : V → Script C) (a b floor : ℕ)
    (hl : L (c.run false block u) a) (hr : R (c.run true block v) b) :
    ∃ (remaining : ℕ) (root : NodeCursor (Word ℕ) (Word ℕ → V) rs)
      (inner : NodeCursor ℕ (Word ℕ) (List.replicate remaining rd)) (last : ℕ),
      floor < last ∧
      L (cutIf (rd.reads false) (inner.run false leaf
        (fun x => root.run false block (fun g => u (g x))))) last ∧
      R (cutIf (rd.reads true) (inner.run true leaf
        (fun x => root.run true block (fun g => v (g x))))) last := by
  obtain ⟨root,opt,hs,hp,hq⟩ := c.split block (plainZeroNode leaf (fun _ => trivial))
    f hf L R stepL stepR u v a b floor hl hr
  let k (w : Word ℕ) := root.run false block (fun g => u (g w))
  let l (w : Word ℕ) := root.run true block (fun g => v (g w))
  have choose {X : Type} (S : Script X → ℕ → Prop) (b : Bool) (arch : b = true → ArchitectStep S)
      (k' : Word ℕ → Script X) (clock : ℕ) (h : S ((block b).bind k') clock) :
      ∃ m, (0 < m ↔ b = true) ∧ S ((node m leaf).bind k') clock := by
    cases b with
    | true => exact chooseBlockCount S (arch rfl) true k' clock h
    | false => exact ⟨0,by simp,h⟩
  obtain ⟨m,hm,hp'⟩ := choose L _ archL k _ hp
  obtain ⟨r,hr',hq'⟩ := choose R _ archR l _ hq
  have counts : ∃ n, headerCount false (List.replicate (n+1) rd) = m ∧
      headerCount true (List.replicate (n+1) rd) = r := by
    rcases sole with rfl | rfl
    · simp [HeaderReader.reads] at hm hr'
      exact ⟨m-1,by simp [headerCount,HeaderReader.reads]; omega,
        by simp [headerCount,HeaderReader.reads,hr']⟩
    · simp [HeaderReader.reads] at hm hr'
      exact ⟨r-1,by simp [headerCount,HeaderReader.reads,hm],
        by simp [headerCount,HeaderReader.reads]; omega⟩
  obtain ⟨n,hm',hr''⟩ := counts
  let plan := List.replicate (n+1) rd
  obtain ⟨xs,total,layout,sorted,h₁,h₂⟩ := synchronizeNodes f hf plan leaf leaf
    (fun p => L (p.bind k)) (fun p => R (p.bind l))
    (fun t last h => stepL (fun z => (t z).bind k) last h)
    (fun t last h => stepR (fun z => (t z).bind l) last h) _ _ (opt.getD floor)
    (hm' ▸ hp') (hr'' ▸ hq')
  have liftC {ts : List HeaderReader} (c' : NodeCursor ℕ (Word ℕ) ts)
      (eq : ts = rd :: List.replicate n rd)
      (w₁ : L (c'.run false leaf k) total) (w₂ : R (c'.run true leaf l) total) :
      ∃ (inner : NodeCursor ℕ (Word ℕ) (List.replicate n rd)) (last : ℕ), total < last ∧
        L (cutIf (rd.reads false) (inner.run false leaf k)) last ∧
        R (cutIf (rd.reads true) (inner.run true leaf l)) last := by
    subst ts
    exact c'.playLeaf f hf L R stepL stepR k l total total total w₁ w₂
  obtain ⟨inner,last,ht,h₃,h₄⟩ := liftC (NodeCursor.ofHeader xs total _ sorted)
    (layout.trans (List.replicate_succ ..)) (by rwa [NodeCursor.runOfHeader])
    (by rwa [NodeCursor.runOfHeader])
  have hflo := (List.pairwise_cons.mp sorted).1 total (List.mem_append_right _ List.mem_cons_self)
  refine ⟨n,root,inner,last,?_,h₃,h₄⟩
  cases opt with
  | none => exact hflo.trans ht
  | some z => exact (hs z rfl).trans (hflo.trans ht)

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

def soleReader (side : Bool) : HeaderReader := if side then .second else .first

private theorem NodeCursor.soleLeaf {V B C : Type} (side : Bool) {rs : List HeaderReader}
    (c : NodeCursor ℕ V (soleReader side :: rs)) (f : ℕ → ℕ) (hf : StrictMono f)
    (L : Script B → ℕ → Prop) (R : Script C → ℕ → Prop)
    (stepL : BuilderStep f L) (stepR : BuilderStep f R) (u : V → Script B) (v : V → Script C)
    (a b floor : ℕ) (hl : L (c.run side leaf u) a) (hr : R (c.run (!side) leaf v) b) :
    ∃ (tail : NodeCursor ℕ V rs) (last : ℕ), floor < last ∧
      L (cut (tail.run side leaf u)) last ∧ R (tail.run (!side) leaf v) last := by
  cases side with
  | false => exact c.playLeaf f hf L R stepL stepR u v a b floor hl hr
  | true =>
    obtain ⟨t,z,ht,hR,hL⟩ := c.playLeaf f hf R L stepR stepL v u b a floor hr hl
    exact ⟨t,z,ht,hL,hR⟩

-- A phase with arbitrarily many alternating cuts in one main game.
-- Each spectator game reads its own endpoint as it is built, retaining
-- its own winning condition and clock while the other endpoint moves.
theorem playAlternatingLeaves {U V A B C D : Type} (f : ℕ → ℕ) (hf : StrictMono f)
    (P : Option (A × B × Bool) → Prop) (hb : ¬ P none)
    (S : Script C → ℕ → Prop) (T : Script D → ℕ → Prop)
    (stepS : BuilderStep f S) (stepT : BuilderStep f T)
    (sx sy : Bool) (n : ℕ) (xs ys : List HeaderReader)
    (kx : U → Script A) (ky : V → Script B) (ux : U → Script C) (uy : V → Script D)
    (x : NodeCursor ℕ U (List.replicate n (soleReader sx) ++ xs))
    (y : NodeCursor ℕ V (List.replicate n (soleReader sy) ++ ys))
    (a b c floor : ℕ)
    (h : PairTurn f P false (x.run sx leaf kx) (y.run sy leaf ky) a)
    (hS : S (x.run (!sx) leaf ux) b) (hT : T (y.run (!sy) leaf uy) c) :
    ∃ (x' : NodeCursor ℕ U xs) (y' : NodeCursor ℕ V ys) (last b' c' : ℕ),
      (0 < n → floor < last) ∧
      PairTurn f P false (x'.run sx leaf kx) (y'.run sy leaf ky) last ∧
      S (x'.run (!sx) leaf ux) b' ∧ T (y'.run (!sy) leaf uy) c' := by
  induction n generalizing a b c floor with
  | zero => exact ⟨x,y,a,b,c,by omega,h,hS,hT⟩
  | succ n ih =>
    obtain ⟨y',m,hm,h',ht⟩ := y.soleLeaf sy f hf (PairTurn f P false (x.run sx leaf kx))
      T (rightTurnBuilder f P hb _) stepT ky uy a c floor h hT
    obtain ⟨x',l,hl,h'',hs⟩ := x.soleLeaf sx f hf (fun p => PairTurn f P true p (y'.run sy leaf ky))
      S (leftTurnBuilder f P hb _) stepS kx ux m b m h' hS
    cases n with
    | zero => exact ⟨x',y',l,l,m,fun _ => hm.trans hl,h'',hs,ht⟩
    | succ n =>
      obtain ⟨v,w,z,bs,cs,hz,hp,hv,hw⟩ := ih x' y' l l m l h'' hs ht
      exact ⟨v,w,z,bs,cs,fun _ => (hm.trans hl).trans (hz (by omega)),hp,hv,hw⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

private theorem bindDone {A : Type} (p : Script A) : p.bind done = p := by
  induction p with
  | done => rfl
  | cut p ih => exact congrArg cut ih
  | builder t ih => exact congrArg builder (funext ih)
  | architect t ih => exact congrArg architect (funext ih)

def InsideHandoff.firstTree {G f d} (h : InsideHandoff G f d) (side : Bool) : Script Tree :=
  childRun (leafRun (headerIndices side h.leaves)) h.len (h.idx+1) h.pack
    (remainingBlocks (headerIndices side ((HeaderReader.both,h.mark)::h.rest)) h.mark h.n h.put)

private theorem InsideHandoff.blockLeOffset {G f d} (h : InsideHandoff G f d) : h.j ≤ h.s := by
  obtain ⟨_,⟨ds,_⟩,_,_,_,_,hw,_,_,_,_⟩ := completePairPosition f (pivotWins G h.k h.j h.s)
    id (cut (markCounts (h.firstTree false) [])) _ h.size h.game12
  obtain ⟨_,pre,_,_,_,hj,hs,_,_,_⟩ := hw.2.2
  have len (l : List ℕ) : l.length ≤ (l.map (·+1)).sum := by
    induction l with
    | nil => exact le_rfl
    | cons x t ih =>
      simp only [List.length_cons,List.map_cons,List.sum_cons]
      omega
  simpa only [hj,hs] using len pre

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

private theorem countsBuilderBind {A B : Type} (p : Script A) (hp : BuilderScript p)
    (k : A → Script B) (ns : List ℕ) :
    markCounts (p.bind k) ns = p.bind (fun x => markCounts (k x) ns) := by
  induction p with
  | done => rfl
  | architect => exact hp.elim
  | cut t ih => exact congrArg cut (ih hp)
  | builder t ih => exact congrArg builder (funext fun i => ih i (hp i))

private theorem buildersBind {A B : Type} (p : Script A) (hp : BuilderScript p)
    (k : A → Script B) (hk : ∀ x, BuilderScript (k x)) : BuilderScript (p.bind k) := by
  induction p with
  | done => exact hk _
  | cut t ih => exact ih hp
  | architect => exact hp.elim
  | builder t ih => exact fun i => ih i (hp i)

private theorem buildersLeaves (ms : List ℕ) (n i : ℕ) : BuilderScript (children (leafRun ms) n i) := by
  induction n generalizing i with
  | zero => trivial
  | succ n ih =>
    apply buildersBind
    · intro v
      by_cases h : i ∈ ms <;> simp [h,BuilderScript]
    · intro x
      exact buildersBind _ (ih _) _ fun _ => trivial

theorem NodeCursor.countsLeaves {V A : Type} {plan : List HeaderReader} (c : NodeCursor ℕ V plan)
    (b : Bool) (k : V → Script A) (ns : List ℕ) :
    markCounts (c.run b leaf k) ns = c.run b leaf (fun x => markCounts (k x) ns) :=
  countsBuilderBind _ (buildersLeaves _ _ _) _ ns

-- Each singly marked 12 block updates the Architect history exactly once,
-- before its leaf header is allocated. The unmarked 23 view keeps the same
-- arity and reads every physical leaf in the block.
theorem openRecordedMiddleBlock (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (P : Option ((List ℕ × Tree) × (List ℕ × Tree) × Bool) → Prop) (hb : ¬ P none)
    (rs : List HeaderReader) (root : NodeCursor (Word ℕ) Tree (.first :: rs))
    (p : Script (List ℕ × Tree)) (past : List ℕ) (opp : Script Tree) (a b floor : ℕ)
    (hl : PairTurn f P false p (markCounts (root.run false block done) past) a)
    (hr : PairTurn f (wins G true) true (root.run true block done) opp b) :
    ∃ (e : ℕ) (tail : NodeCursor (Word ℕ) (Word ℕ → Tree) rs)
      (c : NodeCursor ℕ (Word ℕ) (List.replicate (e+1) HeaderReader.first)) (last : ℕ),
      let y := fun side => c.run side leaf fun w => tail.run side block fun g => done (g w)
      floor < last ∧ PairTurn f P false p (markCounts (y false) (past ++ [e])) last ∧
      PairTurn f (wins G true) true (y true) opp last := by
  let L (hist : List ℕ) (q : Script Tree) := PairTurn f P false p (markCounts q hist)
  let R (q : Script Tree) := PairTurn f (wins G true) true q opp
  have step (hist) : BuilderStep f (L hist) := fun t last h =>
    rightTurnBuilder f P hb p (fun v => markCounts (t v) hist) last h
  have sr : BuilderStep f R := leftTurnBuilder f _ id opp
  obtain ⟨tail,opt,hs,hp,hq⟩ := root.split block (plainZeroNode leaf (fun _ => trivial))
    f hf (L past) R (step past) sr done done a b floor hl hr
  let k (b : Bool) (w : Word ℕ) := tail.run b block (fun g => done (g w))
  obtain ⟨e,he⟩ := hp
  let plan := List.replicate (e+1) HeaderReader.first
  have he' : L (past ++ [e]) ((node (e+1) leaf).bind (k false)) (opt.getD a) := he
  have hq' : R ((node 0 leaf).bind (k true)) (opt.getD b) := hq
  obtain ⟨xs,total,hplan,sorted,h₁,h₂⟩ := synchronizeNodes f hf plan leaf leaf
    (fun q => L (past ++ [e]) (q.bind (k false))) (fun q => R (q.bind (k true)))
    (fun t last h => step _ (fun v => (t v).bind (k false)) last h)
    (fun t last h => sr (fun v => (t v).bind (k true)) last h)
    (opt.getD a) (opt.getD b) (opt.getD floor)
    (by simpa [plan,headerCount,HeaderReader.reads] using he')
    (by simpa [plan,headerCount,HeaderReader.reads] using hq')
  let base : NodeCursor ℕ (Word ℕ) _ := NodeCursor.ofHeader xs total _ sorted
  let c : NodeCursor ℕ (Word ℕ) plan := {base with roles := hplan}
  have run (b : Bool) : c.run b leaf (k b) = (nodeBody leaf (headerIndices b xs) total).bind (k b) :=
    NodeCursor.runOfHeader xs total _ sorted b leaf (k b)
  have hl' : L (past ++ [e]) (c.run false leaf (k false)) total := by rwa [run]
  have hr' : R (c.run true leaf (k true)) total := by rwa [run]
  refine ⟨e,tail,c,total,?_,hl',hr'⟩
  have bound := (List.pairwise_cons.mp sorted).1 total (List.mem_append_right _ List.mem_cons_self)
  cases opt with
  | none => exact bound
  | some z => exact (hs z rfl).trans bound

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

def NodeCursor.replan {A V : Type} {p q : List HeaderReader} (c : NodeCursor A V p) (h : p=q) :
    NodeCursor A V q := {c with roles := c.roles.trans h}

theorem pivotPrefixBudget (G : SimpleGraph Tree) (f : ℕ → ℕ)
    (k j s last count : ℕ) (pre : List ℕ) (before : pre.length ≤ j)
    (p : Script (List ℕ × Tree)) (q : Script Tree)
    (h : PairTurn f (pivotWins G k j s) false p (markCounts q (count :: pre)) last) :
    ∃ missing : List ℕ, pre.length + missing.length = j ∧
      (pre.map (·+1)).sum + (missing.map (·+1)).sum = s := by
  obtain ⟨_,⟨ds,y⟩,_,_,_,_,hw,_,hr,_,_⟩ := completePairPosition f _ (fun h => h)
    (cut p) (markCounts q (count :: pre)) last h
  obtain ⟨_,u,m,tail,hd,hj,hs,_,_,_⟩ := hw.2.2
  have hist := (readCountHistory _ _ hr).2
  rw [hd] at hist
  have eq := (List.cons.inj hist).2
  change u ++ m::tail = pre ++ _ at eq
  have htake := congrArg (List.take pre.length) eq
  rw [List.take_append_of_le_length (before.trans_eq hj),List.take_left] at htake
  obtain ⟨rem,he⟩ : ∃ rem, pre ++ rem = u :=
    ⟨u.drop pre.length,by simpa only [htake] using List.take_append_drop pre.length u⟩
  subst u
  exact ⟨rem,by simpa using hj.symm,by simpa using hs.symm⟩

-- Finish the unmarked end of a middle block while preserving an arbitrary
-- previously chosen prefix of the recorded 12 history.
private theorem finishMiddleBlock (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (P : Option ((List ℕ × Tree) × (List ℕ × Tree) × Bool) → Prop) (hb : ¬ P none)
    (rs : List HeaderReader) (root : NodeCursor (Word ℕ) (Word ℕ → Tree) rs)
    (c : NodeCursor ℕ (Word ℕ) []) (p : Script (List ℕ × Tree)) (past : List ℕ)
    (opp : Script Tree) (a b floor : ℕ)
    (hl : PairTurn f P false p (c.run false leaf (fun w =>
      markCounts (root.run false block (fun g => done (g w))) past)) a)
    (hr : PairTurn f (wins G true) true (c.run true leaf (fun w =>
      root.run true block (fun g => done (g w)))) opp b) :
    ∃ (tail : NodeCursor (Word ℕ) Tree rs) (opt : Option ℕ), (∀ z ∈ opt, floor < z) ∧
      PairTurn f P false p (markCounts (tail.run false block done) past) (opt.getD a) ∧
      PairTurn f (wins G true) true (tail.run true block done) opp (opt.getD b) := by
  obtain ⟨w,opt,hs,hL,hR⟩ := c.finish leaf (fun _ => trivial) f hf (PairTurn f P false p)
    (fun q => PairTurn f (wins G true) true q opp) (rightTurnBuilder f _ hb p)
    (leftTurnBuilder f _ id opp) _ _ a b floor hl hr
  exact ⟨root.map (fun g => g w),opt,hs,hL,hR⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

-- Run every marked middle block preceding the pivot. The final return of
-- 12 is the first switch of 13. No future Architect count is fixed in
-- this argument: the recorded winning payoff bounds each new count.
theorem runInsideBeforePivot {V C : Type} (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (k j s count : ℕ) (xs rs : List HeaderReader) (kx : V → Script (List ℕ × Tree))
    (ux : V → Script C) (S : Script C → ℕ → Prop) (stepS : BuilderStep f S)
    (opp : Script Tree) (blocks rem : ℕ) (pre : List ℕ)
    (number : pre.length + (blocks+1) = j) (budget : (pre.map (·+1)).sum + (rem+1) = s)
    (x : NodeCursor ℕ V (List.replicate rem .first ++ .both :: xs))
    (y : NodeCursor (Word ℕ) Tree (List.replicate (blocks+1) .first ++ rs))
    (a b c floor : ℕ)
    (h : PairTurn f (pivotWins G k j s) false (x.run false leaf kx)
      (markCounts (y.run false block done) (count::pre)) a)
    (hx : S (x.run true leaf ux) b)
    (hy : PairTurn f (wins G true) true (y.run true block done) opp c) :
    ∃ (past : List ℕ) (v : NodeCursor ℕ V xs) (w : NodeCursor (Word ℕ) Tree rs)
      (a' b' c' : ℕ), past.length = j ∧ (past.map (·+1)).sum = s ∧ floor < a' ∧
      PairTurn f (pivotWins G k j s) false (v.run false leaf kx)
        (markCounts (w.run false block done) (count::past)) a' ∧
      S (cut (v.run true leaf ux)) b' ∧ PairTurn f (wins G true) true (w.run true block done) opp c' := by
  let P := pivotWins G k j s
  let T (q : Script Tree) := PairTurn f (wins G true) true q opp
  have st : BuilderStep f T := leftTurnBuilder f _ id opp
  induction blocks generalizing rem pre a b c floor
  all_goals
    obtain ⟨e,root,inner,last,hfresh,hw,hT⟩ := openRecordedMiddleBlock G f hf P id _ y
      (x.run false leaf kx) (count::pre) opp a c floor h hy
    let next := pre ++ [e]
    have nlen : next.length = pre.length+1 := by simp [next]
    have nsum : (next.map (·+1)).sum = (pre.map (·+1)).sum + (e+1) := by simp [next]
    let K (w : Word ℕ) := markCounts (root.run false block (fun g => done (g w))) (count::next)
    let U (w : Word ℕ) := root.run true block (fun g => done (g w))
    have live : PairTurn f P false (x.run false leaf kx) (inner.run false leaf K) last := by
      rwa [← NodeCursor.countsLeaves]
    obtain ⟨missing,mlen,msum⟩ := pivotPrefixBudget G f k j s last count next (by omega)
      (x.run false leaf kx) _ hw
  case zero =>
    have hnil : missing = [] := List.length_eq_zero_iff.mp (by omega)
    subst missing
    simp only [List.map_nil,List.sum_nil,Nat.add_zero] at msum mlen
    have er : e = rem := by omega
    subst rem
    let inner' := inner.replan (show List.replicate (e+1) HeaderReader.first =
        List.replicate e (soleReader false) ++ [.first] by simp [soleReader,List.replicate_succ'])
    obtain ⟨v,w,a₀,b₀,c₀,_,hp,hs,ht⟩ := playAlternatingLeaves f hf P id S T stepS st
      false false e (.both::xs) [.first] kx K ux U x inner' last b last last live hx hT
    obtain ⟨w',z,hz,hp',ht'⟩ := w.soleLeaf false f hf (PairTurn f P false (v.run false leaf kx))
      T (rightTurnBuilder f P id _) st K U a₀ c₀ (max last (max a₀ (max b₀ c₀))) hp ht
    obtain ⟨v',t,htz,hp'',hs'⟩ := v.playLeaf f hf
      (fun p => PairTurn f P true p (w'.run false leaf K)) S (leftTurnBuilder f P id _)
      stepS kx ux z b₀ z hp' hs
    obtain ⟨w'',opt,hopt,H₁,H₂⟩ := finishMiddleBlock G f hf P id rs root w' (v'.run false leaf kx)
      (count::next) opp t z t hp'' ht'
    refine ⟨next,v',w'',_,t,_,by omega,msum,?_,H₁,hs',H₂⟩
    have hft := ((hfresh.trans_le (le_max_left _ _)).trans hz).trans htz
    cases opt with
    | none => exact hft
    | some u => exact hft.trans (hopt u rfl)
  case succ blocks ih =>
    have pos : 0 < (missing.map (·+1)).sum := by
      cases missing with
      | nil => simp at mlen; omega
      | cons v vs => simp
    let r := rem-(e+1)
    have splitCount : rem = (e+1)+r := by dsimp [r]; omega
    let x' := x.replan (show List.replicate rem HeaderReader.first ++ .both :: xs =
        List.replicate (e+1) (soleReader false) ++ (List.replicate r .first ++ .both::xs) by
          conv_lhs => rw [splitCount,List.replicate_add,List.append_assoc]
          rfl)
    let w' := inner.replan (List.append_nil _).symm
    obtain ⟨v,w,a₀,b₀,c₀,hz,hp,hs,ht⟩ := playAlternatingLeaves f hf P id S T stepS st
      false false (e+1) _ [] kx K ux U x' w' last b last last live hx hT
    let now := max a₀ (max b₀ c₀)
    obtain ⟨w'',opt,hopt,H₁,H₂⟩ := finishMiddleBlock G f hf P id _ root w (v.run false leaf kx)
      (count::next) opp a₀ c₀ now hp ht
    let nextFloor := max now (opt.getD now)
    obtain ⟨past,xx,yy,a',b',c',hNum,hSum,hA,h₁,h₂,h₃⟩ :=
      ih r next (by omega) (by omega) v w'' _ b₀ _ nextFloor H₁ hs H₂
    have hfa := hfresh.trans (hz (by omega))
    exact ⟨past,xx,yy,a',b',c',hNum,hSum,((hfa.trans_le (le_max_left ..)).trans_le
      (le_max_left ..)).trans hA,h₁,h₂,h₃⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

-- Re-enter a block at the physical index immediately following the first
-- consumed mark. All future child scripts can forget that earlier index.
private theorem cursorAfterFirst {V : Type} (marks : List (HeaderReader × ℕ)) (rd : HeaderReader)
    (rs : List HeaderReader) (idx len : ℕ) (put : Tuple ℕ len → V)
    (roles : marks.map Prod.fst = rd::rs) (head : (marks.map Prod.snd).head? = some idx)
    (sorted : (0 :: (marks.map Prod.snd ++ [idx+len])).Pairwise (· < ·)) :
    ∃ c : NodeCursor ℕ V rs, ∀ {B : Type} (b : Bool) (k : V → Script B),
      c.run b leaf k = childRun (leafRun (headerIndices b marks)) len (idx+1) put k := by
  cases marks with
  | nil => cases roles
  | cons x marks =>
    obtain ⟨tag,m⟩ := x
    obtain ⟨rfl,hroles⟩ := List.cons.inj roles
    have he : m = idx := Option.some.inj head
    subst m
    obtain ⟨bound,ord⟩ := List.pairwise_cons.mp (List.pairwise_cons.mp sorted).2
    let c : NodeCursor ℕ V rs := ⟨idx+1,len,put,marks,hroles,
      fun j hj => bound j (List.mem_append_left _ hj),by
        obtain ⟨hm,_,hb⟩ := List.pairwise_append.mp ord
        apply List.pairwise_append.mpr
        refine ⟨hm,by simp,?_⟩
        intro j hj z hz
        obtain rfl := List.mem_singleton.mp hz
        have := hb j hj (idx+len) List.mem_cons_self
        omega⟩
    refine ⟨c,?_⟩
    intro B b k
    unfold NodeCursor.run childRun
    apply congrArg (fun p : Script (Tuple ℕ len) => p.bind (fun ys => k (put ys)))
    apply childrenCongrFrom
    intro j hj
    change idx+1 ≤ j at hj
    simp only [c,leafRun,headerTailMem tag idx j marks b (by omega)]

def afterInsideShared (k s m r : ℕ) : List HeaderReader :=
  List.replicate (k-s) .first ++ List.replicate r .second ++ List.replicate (m-k) .first

def middleFromPivot (count d j : ℕ) : List HeaderReader :=
  List.replicate d .second ++ [.both] ++ List.replicate (count-(j+1)) .first

private theorem insideLayoutParts (s k m r : ℕ) :
    insideLeafLayout s (k+1) m r =
      List.replicate s .first ++ .both :: afterInsideShared k s m r := by
  simp only [insideLeafLayout,afterInsideShared,List.append_assoc,List.cons_append,List.nil_append]
  rw [show k+1-s-1 = k-s by omega,show m+1-(k+1) = m-k by omega]

def InsideHandoff.resumeFirst {G f d} (h : InsideHandoff G f d) (side : Bool)
    (w : Word ℕ) : Script Tree :=
  remainingBlocks (headerIndices side ((HeaderReader.both,h.mark)::h.rest)) h.mark h.n h.put w

theorem InsideHandoff.reachSharedCut {G f d} (h : InsideHandoff G f d) (hf : StrictMono f) :
    ∃ (pre : List ℕ) (x : NodeCursor ℕ (Word ℕ) (afterInsideShared h.k h.s h.m h.r))
      (y : NodeCursor (Word ℕ) Tree (middleFromPivot h.count d h.j)) (a b c : ℕ),
      pre.length = h.j ∧ (pre.map (·+1)).sum = h.s ∧
      PairTurn f (pivotWins G h.k h.j h.s) false
        (markCounts (x.run false leaf (h.resumeFirst false)) []) (markCounts (y.run false block done) (h.count::pre)) a ∧
      PairTurn f (wins G true) false (x.run true leaf (h.resumeFirst true)) tree b ∧
      PairTurn f (wins G true) true (y.run true block done) positiveTree c := by
  let base : NodeCursor (Word ℕ) Tree _ := NodeCursor.ofHeader h.middle h.size h.last h.middleClock
  let tail := middleFromPivot h.count d h.j
  let finish := afterInsideShared h.k h.s h.m h.r
  have rootPlan : h.middle.map Prod.fst = List.replicate h.j .first ++ tail := by
    simpa [tail,middleFromPivot,insideMiddleLayout,List.append_assoc] using h.middleOrder
  let y : NodeCursor (Word ℕ) Tree (List.replicate h.j .first ++ tail) := base.replan rootPlan
  have yr (b : Bool) : y.run b block done = nodeBody block (headerIndices b h.middle) h.size := by
    change (NodeCursor.ofHeader h.middle h.size h.last h.middleClock).run b block done = _
    rw [NodeCursor.runOfHeader,bindDone]
  let K (w : Word ℕ) := markCounts (h.resumeFirst false w) []
  have hp := h.game12
  have hq := h.game13
  have hz := h.game23
  rw [← yr] at hp hz
  have layout : h.leaves.map Prod.fst = List.replicate h.s .first ++ .both::finish :=
    h.leafOrder.trans (insideLayoutParts ..)
  rcases Nat.eq_zero_or_pos h.s with he | hspos
  ·
    have hj : h.j = 0 := Nat.eq_zero_of_le_zero (he ▸ h.blockLeOffset)
    rw [he] at layout hq
    obtain ⟨v,hv⟩ := cursorAfterFirst h.leaves .both finish h.idx h.len h.pack layout h.firstLeafIndex h.leafClock
    let w : NodeCursor (Word ℕ) Tree tail := y.replan (by rw [hj]; rfl)
    refine ⟨[],v,w,h.size,h.last,h.size,by simp [hj],by simp [he],?_,?_,hz⟩
    · rw [hv]
      exact hp
    · rw [hv]
      exact hq
  · let n := h.s-1
    have he : h.s = n+1 := by dsimp [n]; omega
    have hpos : 0 < h.j := by
      obtain ⟨missing,hn,hs⟩ := pivotPrefixBudget G f h.k h.j h.s h.size h.count [] (Nat.zero_le _)
        (markCounts (h.firstTree false) []) _ hp
      cases missing with
      | nil => simp at hs; omega
      | cons => simp at hn; omega
    let blocks := h.j-1
    have hnum : blocks+1 = h.j := by dsimp [blocks]; omega
    rw [he,List.replicate_succ,List.cons_append] at layout
    obtain ⟨v,hv⟩ := cursorAfterFirst h.leaves .first _ h.idx h.len h.pack layout h.firstLeafIndex h.leafClock
    let w := y.replan (show List.replicate h.j .first ++ tail =
      List.replicate (blocks+1) .first ++ tail by rw [hnum])
    let S := LeftWin f G true
    have h₁ : PairTurn f (pivotWins G h.k h.j h.s) false (v.run false leaf K)
        (markCounts (w.run false block done) (h.count::[])) h.size := by
      rw [show v.run false leaf K = markCounts (v.run false leaf (h.resumeFirst false)) [] from
        (v.countsLeaves false (h.resumeFirst false) []).symm,hv]
      exact hp
    have h₂ : S (v.run true leaf (h.resumeFirst true)) h.last := by
      rw [hv]
      simp only [he,Nat.succ_ne_zero,decide_false,cutIf,Bool.false_eq_true,if_false] at hq
      exact hq
    obtain ⟨pre,xx,yy,a,b,c,hl,hs,_,H₁,H₂,H₃⟩ := runInsideBeforePivot G f hf h.k h.j h.s h.count
      finish tail K (h.resumeFirst true) S (leftWinStep f G true) positiveTree blocks n []
      (by simpa using hnum) (by simp [he]) v w h.size h.last h.size h.size h₁ h₂ hz
    exact ⟨pre,xx,yy,a,b,c,hl,hs,by simpa only [NodeCursor.countsLeaves] using H₁,H₂,H₃⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script Filter

def middleLeafLayout (r e k s : ℕ) : List HeaderReader :=
  List.replicate r .second ++ List.replicate (k-s) .first ++ [.both] ++
    List.replicate (e-(k-s)) .first

-- At the pivot block the two new Architect counts are independent. The
-- stored 12 history determines precisely which of its leaves also ends 23.
theorem openInsidePivotBlock (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (k j s count : ℕ) (pre : List ℕ) (here : pre.length = j)
    (rs : List HeaderReader) (y : NodeCursor (Word ℕ) Tree (.both :: rs))
    (x : Script (List ℕ × Tree)) (z : Script Tree) (a b floor : ℕ)
    (h : PairTurn f (pivotWins G k j s) false x (markCounts (y.run false block done) (count::pre)) a)
    (h' : PairTurn f (wins G true) true (y.run true block done) z b) :
    ∃ (e r : ℕ) (root : NodeCursor (Word ℕ) (Word ℕ → Tree) rs)
      (inner : NodeCursor ℕ (Word ℕ) (middleLeafLayout r e k s)) (last : ℕ),
      let kY := fun side w => root.run side block fun g => done (g w)
      s = (pre.map (·+1)).sum ∧ s ≤ k ∧ k-s ≤ e ∧ floor < last ∧
      PairTurn f (pivotWins G k j s) false x
        (markCounts (inner.run false leaf (kY false)) (count :: (pre ++ [e]))) last ∧
      PairTurn f (wins G true) true (inner.run true leaf (kY true)) z last := by
  let P := pivotWins G k j s
  let L (hist : List ℕ) (q : Script Tree) := PairTurn f P false x (markCounts q hist)
  let R (p : Script Tree) := PairTurn f (wins G true) true p z
  have sl (hist) : BuilderStep f (L hist) := fun t last h =>
    rightTurnBuilder f P id x (fun v => markCounts (t v) hist) last h
  have sr : BuilderStep f R := leftTurnBuilder f _ id z
  obtain ⟨root,opt,hs,hl,hr⟩ := y.split block (plainZeroNode leaf (fun _ => trivial))
    f hf (L (count::pre)) R (sl _) sr done done a b floor h h'
  let ky (b : Bool) (w : Word ℕ) := root.run b block (fun g => done (g w))
  obtain ⟨e,he⟩ := hl
  obtain ⟨r,hw⟩ := hr
  have h₁ : L (count :: (pre ++ [e])) ((node (e+1) leaf).bind (ky false)) (opt.getD a) := he
  have h₂ : R ((node (r+1) leaf).bind (ky true)) (opt.getD b) := hw
  obtain ⟨hsum,hsk,hke⟩ := pivotAtBlockAllocation G f k j s (opt.getD a) count e pre here x _ false h₁
  let plan := middleLeafLayout r e k s
  have hfirst : headerCount false plan = e+1 := by
    simp [plan,middleLeafLayout,headerCount,HeaderReader.reads]
    omega
  have hsecond : headerCount true plan = r+1 := by simp [plan,middleLeafLayout,headerCount,HeaderReader.reads]
  obtain ⟨xs,total,hplan,sorted,H₁,H₂⟩ := synchronizeNodes f hf plan leaf leaf
    (fun p => L (count::(pre++[e])) (p.bind (ky false))) (fun p => R (p.bind (ky true)))
    (fun t last h => sl _ (fun v => (t v).bind (ky false)) last h)
    (fun t last h => sr (fun v => (t v).bind (ky true)) last h)
    _ _ (opt.getD floor) (hfirst ▸ h₁) (hsecond ▸ h₂)
  let base : NodeCursor ℕ (Word ℕ) _ := NodeCursor.ofHeader xs total _ sorted
  let inner := base.replan hplan
  have run (b : Bool) : inner.run b leaf (ky b) = (nodeBody leaf (headerIndices b xs) total).bind (ky b) :=
    NodeCursor.runOfHeader xs total _ sorted b leaf (ky b)
  refine ⟨e,r,root,inner,total,hsum,hsk,by omega,?_,?_,?_⟩
  · have hfloor := (List.pairwise_cons.mp sorted).1 total (List.mem_append_right _ List.mem_cons_self)
    cases opt with
    | none => exact hfloor
    | some t => exact (hs t rfl).trans hfloor
  · change L _ (inner.run false leaf (ky false)) total
    rwa [run]
  · change R (inner.run true leaf (ky true)) total
    rwa [run]

-- The last 23 mark can occur after several more 12 returns within the
-- pivot block. Run those returns and issue the final shared value once.
theorem handoffInsidePivot {U V : Type} (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (n : ℕ) (xs ys : List HeaderReader) (x : NodeCursor ℕ U (List.replicate n .first ++ xs))
    (y : NodeCursor ℕ V (List.replicate n .first ++ .both::ys))
    (kx ux : U → Script Tree) (ky uy : V → Script Tree) (z z' : Script Tree) (a b c floor : ℕ)
    (h₁ : PairTurn f (wins G true) false (x.run false leaf kx) (y.run false leaf ky) a)
    (h₂ : PairTurn f (wins G true) true (x.run true leaf ux) z b)
    (h₃ : PairTurn f (wins G true) true (y.run true leaf uy) z' c) :
    ∃ (v : NodeCursor ℕ U xs) (w : NodeCursor ℕ V ys) (b' last : ℕ), floor < last ∧
      PairTurn f (wins G true) true (v.run false leaf kx) (w.run false leaf ky) last ∧
      PairTurn f (wins G true) true (v.run true leaf ux) z b' ∧
      PairTurn f (wins G true) false (w.run true leaf uy) z' last := by
  let S (x : Script Tree) := PairTurn f (wins G true) true x z
  let T (y : Script Tree) := PairTurn f (wins G true) true y z'
  obtain ⟨v,w,a',b',c',_,h,hv,hw⟩ := playAlternatingLeaves f hf (wins G true) id S T
    (leftTurnBuilder f _ id z) (leftTurnBuilder f _ id z') false false n xs (.both::ys)
    kx ky ux uy x y a b c floor h₁ h₂ h₃
  let top := max floor (max a' (max b' c'))
  obtain ⟨w',last,hf',hl,hr⟩ := w.playLeaf f hf (PairTurn f (wins G true) false (v.run false leaf kx))
    T (rightTurnBuilder f _ id _) (leftTurnBuilder f _ id z') ky uy a' c' top h hw
  exact ⟨v,w',b',last,(le_max_left ..).trans_lt hf',hl,hv,hr⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

-- A prefix of blocks marked by just one game, possibly already inside
-- its first block. The remaining root tags describe the next phase.
inductive Exclusive (side : Bool) (rest : List HeaderReader) where
  | atRoot (n : ℕ) (root : NodeCursor (Word ℕ) Tree (List.replicate n (soleReader side) ++ rest))
  | inBlock (n m : ℕ) (root : NodeCursor (Word ℕ) (Word ℕ → Tree) (List.replicate n (soleReader side) ++ rest))
      (inner : NodeCursor ℕ (Word ℕ) (List.replicate m (soleReader side)))

def Exclusive.run {side rest} : Exclusive side rest → Bool → Script Tree
  | .atRoot _ root, b => root.run b block done
  | .inBlock _ _ root inner, b => inner.run b leaf (fun w => root.run b block (fun g => done (g w)))

def Exclusive.rank {side rest} : Exclusive side rest → ℕ × ℕ
  | .atRoot n _ => (n,0)
  | .inBlock n m _ _ => (n,m+1)

private theorem NodeCursor.firstSolo {rs : List HeaderReader} (side : Bool)
    (c : NodeCursor (Word ℕ) Tree (soleReader side :: rs)) (f : ℕ → ℕ) (hf : StrictMono f)
    (L R : Script Tree → ℕ → Prop) (stepL : BuilderStep f L) (stepR : BuilderStep f R)
    (arch : ArchitectStep L) (a b floor : ℕ)
    (hl : L (c.run side block done) a) (hr : R (c.run (!side) block done) b) :
    ∃ (m : ℕ) (root : NodeCursor (Word ℕ) (Word ℕ → Tree) rs)
      (inner : NodeCursor ℕ (Word ℕ) (List.replicate m (soleReader side))) (last : ℕ),
      let q := fun side => inner.run side leaf (fun w => root.run side block (fun g => done (g w)))
      floor < last ∧ L (cut (q side)) last ∧ R (q (!side)) last := by
  cases side with
  | false =>
    exact c.firstExclusive f hf (Or.inl rfl) L R stepL stepR (fun _ => arch)
      (fun h => Bool.noConfusion h) done done a b floor hl hr
  | true =>
    obtain ⟨m,u,v,last,hs,hR,hL⟩ := c.firstExclusive f hf (Or.inr rfl) R L stepR stepL
      (fun h => Bool.noConfusion h) (fun _ => arch) done done b a floor hr hl
    exact ⟨m,u,v,last,hs,hL,hR⟩

def Exclusive.Next {side rs} (q : Exclusive side rs) (L R : Script Tree → ℕ → Prop) (floor : ℕ) :=
  (∃ (root : NodeCursor (Word ℕ) Tree rs) (a b : ℕ), L (root.run side block done) a ∧
    R (root.run (!side) block done) b) ∨
  ∃ (next : Exclusive side rs) (last : ℕ),
    Prod.Lex (· < ·) (· < ·) next.rank q.rank ∧ floor < last ∧
    L (cut (next.run side)) last ∧ R (next.run (!side)) last

theorem Exclusive.advance {side rs} (q : Exclusive side rs) (f : ℕ → ℕ) (hf : StrictMono f)
    (L R : Script Tree → ℕ → Prop) (stepL : BuilderStep f L) (stepR : BuilderStep f R)
    (arch : ArchitectStep L) (a b floor : ℕ) (hl : L (q.run side) a) (hr : R (q.run (!side)) b) :
    q.Next L R floor := by
  have rootStep (n : ℕ) (root : NodeCursor (Word ℕ) Tree (List.replicate (n+1) (soleReader side) ++ rs))
      (a b floor : ℕ) (h₁ : L (root.run side block done) a) (h₂ : R (root.run (!side) block done) b) :
      ∃ (next : Exclusive side rs) (last : ℕ), next.rank.1 = n ∧ floor < last ∧
        L (cut (next.run side)) last ∧ R (next.run (!side)) last := by
    obtain ⟨m,tail,inner,last,hs,hL,hR⟩ := root.firstSolo side f hf L R stepL stepR arch a b floor h₁ h₂
    exact ⟨.inBlock n m tail inner,last,rfl,hs,hL,hR⟩
  cases q with
  | atRoot n c =>
    cases n with
    | zero => exact Or.inl ⟨c,a,b,hl,hr⟩
    | succ n =>
      obtain ⟨next,last,he,hs,hL,hR⟩ := rootStep n c a b floor hl hr
      exact Or.inr ⟨next,last,Prod.Lex.left _ _ (by change next.rank.1 < n+1; omega),hs,hL,hR⟩
  | inBlock n m root inner =>
    cases m with
    | succ m =>
      obtain ⟨tail,last,hs,hL,hR⟩ := inner.soleLeaf side f hf L R stepL stepR _ _ a b floor hl hr
      exact Or.inr ⟨.inBlock n m root tail,last,Prod.Lex.right _ (Nat.lt_succ_self _),hs,hL,hR⟩
    | zero =>
      obtain ⟨w,opt,hs,hL,hR⟩ := inner.finish leaf (fun _ => trivial) f hf
        (if side then R else L) (if side then L else R)
        (by cases side <;> first | exact stepL | exact stepR)
        (by cases side <;> first | exact stepL | exact stepR)
        (fun w => root.run false block (fun g => done (g w)))
        (fun w => root.run true block (fun g => done (g w)))
        (if side then b else a) (if side then a else b) floor
        (by cases side <;> first | exact hl | exact hr) (by cases side <;> first | exact hl | exact hr)
      let tail := root.map (fun g => g w)
      have ha : L (tail.run side block done) (opt.getD a) := by cases side <;> first | exact hL | exact hR
      have hb : R (tail.run (!side) block done) (opt.getD b) := by cases side <;> first | exact hR | exact hL
      cases n with
      | zero => exact Or.inl ⟨tail,_,_,ha,hb⟩
      | succ n =>
        obtain ⟨next,last,he,hz,h₁,h₂⟩ := rootStep n tail _ _ (max floor (opt.getD floor)) ha hb
        exact Or.inr ⟨next,last,Prod.Lex.left _ _ (by change next.rank.1 < n+1; omega),
          (le_max_left ..).trans_lt hz,h₁,h₂⟩

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

private def Mandatory {A : Type} (p : Script A) :=
  ∀ {s x}, Reads p s x → (0 :: s.filterMap Event.number).Pairwise (· < ·) → 0 < s.count .cut

private theorem mandatoryAfter {A B : Type} (p : Script A) (k : A → Script B)
    (h : ∀ x, Mandatory (k x)) : Mandatory (p.bind k) := by
  intro s x hr hs
  obtain ⟨v,_,_,hl,htail,rfl⟩ := splitRead p k hr
  have ht := h v htail (separateSorted _ _ hs).2
  rw [List.count_append]
  omega

private theorem laterLeafCut (ms : List ℕ) (j : ℕ) (hj : j ∈ ms) (n i : ℕ)
    (lo : i ≤ j) (hi : j < i+n) {s x} (hr : Reads (children (leafRun ms) n i) s x)
    (hs : (0 :: s.filterMap Event.number).Pairwise (· < ·)) : 0 < s.count .cut := by
  induction n generalizing i s with
  | zero => omega
  | succ n ih =>
    obtain ⟨v,u,w,hu,hw,rfl⟩ := splitRead (leafRun ms i) _ hr
    by_cases e : i=j
    · subst i
      simp only [leafRun,hj,decide_true,leaf,if_true] at hu
      cases hu with
      | builder hval => cases hval with | cut hval => cases hval; simp
    · obtain ⟨z,w₁,w₂,hz,_,rfl⟩ := splitRead (children (leafRun ms) n (i+1)) _ hw
      have := ih (i+1) (by omega) (by omega) hz (separateSorted _ _ (separateSorted _ _ hs).2).1
      simp only [List.count_append]
      omega

private theorem NodeCursor.mandatory {A V B : Type} {rs : List HeaderReader} (c : NodeCursor A V rs)
    (side : Bool) (child : Bool → Script A) (k : V → Script B)
    (marked : 0 < headerCount side rs)
    (hit : ∀ (ms : List ℕ) (j : ℕ), j ∈ ms → ∀ n i, i ≤ j → j < i+n →
      Mandatory (children (fun l => child (decide (l ∈ ms))) n i)) :
    Mandatory (c.run side child k) := by
  have length := headerIndicesLength side c.marks
  rw [c.roles] at length
  obtain ⟨j,hj⟩ := List.exists_mem_of_ne_nil (l := headerIndices side c.marks)
    (by intro h; rw [h] at length; simp at length; omega)
  have mem := headerMemValues side c.marks j hj
  have lo := c.lower _ mem
  have hi := (List.pairwise_append.mp c.ordered).2.2 j mem _ List.mem_cons_self
  intro s x hr hs
  obtain ⟨_,u,w,hu,_,rfl⟩ := splitRead (children _ c.len c.start) _ hr
  have := hit _ _ hj _ _ lo hi hu (separateSorted _ _ hs).1
  rw [List.count_append]
  omega

private theorem NodeCursor.plain {A V B : Type} {rs : List HeaderReader} (c : NodeCursor A V rs)
    (side : Bool) (child : Bool → Script A) (h : Plain (child false)) (k : V → Script B)
    (hk : ∀ v, Plain (k v)) (hem : headerCount side rs = 0) : Plain (c.run side child k) := by
  have len := headerIndicesLength side c.marks
  rw [c.roles,hem] at len
  have hn := List.length_eq_zero_iff.mp len
  apply plainBind
  · apply plainChildren
    intro j _
    simpa [hn] using h
  · exact fun _ => hk _

private theorem noCutsRead {A : Type} (p : Script A) (hp : NoCuts p)
    {s : List Event} {v : A} (hr : Reads p s v) : s.count .cut = 0 := by
  induction hr with
  | done => rfl
  | cut => exact hp.elim
  | builder hr ih | architect hr ih => simpa using ih (hp _)

private theorem outsideNeedsReturn (G : SimpleGraph Tree) (f : ℕ → ℕ) (p q : Script Tree)
    (a : ℕ) (hp : Plain p) (hq : Mandatory q) (h : PairTurn f (wins G false) true p q a) : False := by
  obtain ⟨_,_,_,l,r,s,hw,hl,hr,weave,hs⟩ := completePairPosition f _ id p q a h
  obtain ⟨_,rfl⟩ := hw
  have bal := weave.cutBalance
  have hc := noCutsRead p (plainNoCuts _ hp) hl
  have sorted : (0 :: s.filterMap Event.number).Pairwise (· < ·) := List.pairwise_cons.mpr
    ⟨fun j hj => (Nat.zero_le a).trans_lt ((List.pairwise_cons.mp hs).1 j hj),(List.pairwise_cons.mp hs).2⟩
  have ht := hq hr (sorted.sublist (weave.localNumbers.2.cons_cons 0))
  change l.count .cut + 0 = r.count .cut + 0 at bal
  omega

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

private theorem NodeCursor.transferRun {A V B : Type} {rs : List HeaderReader} (c : NodeCursor A V rs)
    (f : ℕ → ℕ) (p q : Bool) (child : Bool → Script A)
    (base : ∀ b t, Transfers f (child b) (child t)) (k l : V → Script B)
    (hk : ∀ v, Transfers f (k v) (l v)) :
    Transfers f (c.run p child k) (c.run q child l) :=
  transfersChildRun f _ _ _ _ _ _ _ (fun _ _ => base _ _) hk

private theorem transfersBlockTags (f : ℕ → ℕ) (p q : Bool) : Transfers f (block p) (block q) := by
  cases p <;> cases q
  · exact transfersBlocks f [] [] 0
  · exact transfersBlocks f [] [0] 0
  · exact transfersBlocks f [0] [] 0
  · exact transfersBlocks f [0] [0] 0

private theorem transfersLeafTags (f : ℕ → ℕ) (p q : Bool) : Transfers f (leaf p) (leaf q) := by
  cases p <;> cases q <;> exact fun _ h => h

private theorem Exclusive.transfer {side rs} (q : Exclusive side rs) (f : ℕ → ℕ) (b c : Bool) :
    Transfers f (q.run b) (q.run c) := by
  cases q with
  | atRoot n root => exact root.transferRun f _ _ block (transfersBlockTags f) _ _ fun _ _ h => h
  | inBlock n m root inner =>
    exact inner.transferRun f _ _ leaf (transfersLeafTags f) _ _
      (fun w => root.transferRun f _ _ block (transfersBlockTags f) _ _ fun _ _ h => h)

private theorem outsideRightExhausted (G : SimpleGraph Tree) (f : ℕ → ℕ) (p q : Script Tree)
    (Q : Tree → Tree → Prop) (last : ℕ) (hq : NoCuts q)
    (h : PairTurn f (fun z => wins G false z ∧ (∀ w, z = some w → Q w.1 w.2.1)) true p q last) :
    Force f (fun x => Force f (fun y => G.Adj x y ∧ Q x y) q) p := by
  let P (z : Option (Tree × Tree × Bool)) := wins G false z ∧ (∀ w, z = some w → Q w.1 w.2.1)
  induction p generalizing last with
  | done x =>
    exact forcesMono f q (fun y => P (some (x,y,false))) _ (fun y h => ⟨h.1.1,h.2 _ rfl⟩)
      (finishForce q _ P (fun h => h.1.elim) f last h)
  | architect t ih =>
    obtain ⟨n,hn⟩ := h
    exact ⟨n,ih n last hn⟩
  | builder t ih => exact ((leftTurnBuilder f P (fun h => h.1.elim) q) t last h).mono fun _ hi => ih _ _ hi
  | cut t ih =>
    have hw := noCutsRight t q hq P (fun h => h.1.elim) f last h
    obtain ⟨y,hy⟩ := forceWitness _ _ _ hw
    obtain ⟨x,hx⟩ := forceWitness _ _ _ hy
    exact Bool.noConfusion hx.1.2

private theorem absorbOutsideRight (G : SimpleGraph Tree) (f : ℕ → ℕ)
    (x y x' z : Script Tree) (a b : ℕ) (hy : NoCuts y) (share : Transfers f x x')
    (h₁ : PairTurn f (wins G false) true x y a) (h₂ : PairTurn f (wins G false) true x' z b) :
    PairTurn f (outsidePromise G f y) true x' z b := by
  have hw : PairTurn f (fun v => wins G false v ∧ (∀ w, v = some w → True)) true x y a := by
    apply strengthenClocked f _ _ id _ a _ h₁
    exact fun _ _ h _ _ => ⟨h,by simp⟩
  have H := outsideRightExhausted G f x y (fun _ _ => True) a hy hw
  have hx := share _ (forcesMono f x _ _ (fun u hu => forcesMono f y _ _ (fun _ h => h.1) hu) H)
  exact retainEndpointRestrictions f x' z true b _ _ _ hx (keepTrue f z) h₂

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

private abbrev HasTriangle (G : SimpleGraph Tree) := ∃ x y z, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z

private theorem walkLeft {P : Option (Tree × Tree × Bool) → Prop} (f : ℕ → ℕ) (hb : ¬ P none)
    (q : Script Tree) (A : Prop)
    (doneCase : ∀ x a, PairTurn f P true (done x) q a → A)
    (cutCase : ∀ p a, PairTurn f P false p q a → A) (p : Script Tree) (a : ℕ)
    (h : PairTurn f P true p q a) : A := by
  induction p generalizing a with
  | done x => exact doneCase x a h
  | cut p => exact cutCase p a h
  | architect t ih =>
    obtain ⟨i,hi⟩ := h
    exact ih i _ hi
  | builder t ih =>
    obtain ⟨i,hi⟩ := (leftTurnBuilder f P hb q t a h).exists
    exact ih _ _ hi

private theorem outsideLeftDone (G : SimpleGraph Tree) (f : ℕ → ℕ) (x : Tree)
    (y z y' z' : Script Tree) (a b : ℕ) (hy : Transfers f y y') (hz : Transfers f z z')
    (h : PairTurn f (outsidePromise G f y) true (done x) z a)
    (h' : PairTurn f (wins G false) false y' z' b) : HasTriangle G := by
  have hx := finishForce z (fun w => some (x,w,false)) (outsidePromise G f y) (fun h => h.1.elim) f a h
  obtain ⟨w,hw⟩ := forceWitness _ _ _ hx
  have hv := hz _ (forcesMono f z _ _ (fun w h => h.1.1) hx)
  exact ⟨x,closeRemainingPair G f x y' z' false false b (hy _ hw.2.1) hv h'⟩

private theorem completeOutside13 (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (y y' : Script Tree) (hy : Transfers f y y') (t : ℕ) (z : Exclusive false (List.replicate t .second))
    (x : Script Tree) (a b : ℕ)
    (h₁ : PairTurn f (outsidePromise G f y) false x (z.run false) a)
    (h₂ : PairTurn f (wins G false) false y' (z.run true) b) : HasTriangle G := by
  let P := outsidePromise G f y
  let L := PairTurn f P false x
  let R := PairTurn f (wins G false) false y'
  obtain stop | more := z.advance f hf L R (rightTurnBuilder f P (fun h => h.1.elim) x)
    (rightTurnBuilder f _ id y') (rightTurnArchitect f P x) a b (max a b) h₁ h₂
  · obtain ⟨root,aa,_,hl,_⟩ := stop
    have plain := root.plain false block (plainZeroNode leaf (fun _ => trivial)) done
      (fun _ => trivial) (by simp [headerCount,HeaderReader.reads])
    have bad := noCutsRight x _ (plainNoCuts _ plain) P (fun h => h.1.elim) f aa hl
    obtain ⟨_,hb⟩ := forceWitness _ _ _ bad
    obtain ⟨_,hv⟩ := forceWitness _ _ _ hb
    exact Bool.noConfusion hv.1.2
  · obtain ⟨next,last,dec,_,hl,hr⟩ := more
    apply walkLeft f (P := P) (fun h => h.1.elim) (next.run false) _ _ _ x last hl
    · intro u aa hu
      exact outsideLeftDone G f u y _ y' _ aa last hy (next.transfer f false true) hu hr
    · intro p aa hp
      exact completeOutside13 G f hf y y' hy t next p aa last hp hr
termination_by z.rank
decreasing_by exact dec

-- Starting from Tree 2's shared 12/23 leaf, complete the whole outside
-- schedule. Tree 3's two root counts are chosen independently at its turn.
theorem fromOutsideSharedCut (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (x y x' y' : Script Tree) (a b c : ℕ) (hy : Plain y)
    (sx : Transfers f x x') (sy : Transfers f y y')
    (h₁ : PairTurn f (wins G false) true x y a) (h₂ : LeftWin f G false x' b)
    (h₃ : PairTurn f (wins G false) false y' tree c) : HasTriangle G := by
  let P := outsidePromise G f y
  have live := absorbOutsideRight G f x y x' tree a b (plainNoCuts _ hy) sx h₁ h₂
  apply walkLeft f (P := P) (fun h => h.1.elim) tree _ _ _ x' b live
  · intro u aa hu
    exact outsideLeftDone G f u y tree y' tree aa c sy (fun Q => (treeKeep f Q).mpr) hu h₃
  · intro p aa hp
    obtain ⟨r,hr⟩ := hp
    obtain ⟨t,ht⟩ := h₃
    let plan := List.replicate r HeaderReader.first ++ List.replicate t .second
    have hL : headerCount false plan = r := by simp [plan,headerCount,HeaderReader.reads]
    have hR : headerCount true plan = t := by simp [plan,headerCount,HeaderReader.reads]
    obtain ⟨zs,total,hs,sorted,h₄,h₅⟩ := synchronizeNodes f hf plan block block
      (PairTurn f P false p) (PairTurn f (wins G false) false y')
      (rightTurnBuilder f P (fun h => h.1.elim) _) (rightTurnBuilder f _ id _)
      aa c (max aa c) (hL ▸ hr) (hR ▸ ht)
    let base : NodeCursor (Word ℕ) Tree _ := NodeCursor.ofHeader zs total _ sorted
    let z := Exclusive.atRoot (side := false) (rest := List.replicate t .second) r (base.replan hs)
    have run (b : Bool) : z.run b = nodeBody block (headerIndices b zs) total := by
      change (NodeCursor.ofHeader zs total _ sorted).run b block done = _
      rw [NodeCursor.runOfHeader,bindDone]
    exact completeOutside13 G f hf y y' sy t z p total total (by rwa [run]) (by rwa [run])

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

private theorem outsideFirstReturn (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (d : ℕ) (x : Exclusive false (List.replicate d .second)) (y : Script Tree) (hm : Mandatory y)
    (a b floor : ℕ) (hl : PairTurn f (wins G false) true (x.run false) y a)
    (hr : LeftWin f G false (x.run true) b) :
    ∃ (v : Exclusive false (List.replicate d .second)) (last : ℕ), floor < last ∧
      PairTurn f (wins G false) false (v.run false) y last ∧ LeftWin f G false (v.run true) last := by
  let L (p : Script Tree) := PairTurn f (wins G false) true p y
  obtain stop | more := x.advance f hf L (LeftWin f G false) (leftTurnBuilder f _ id y)
    (leftWinStep f G false) (leftTurnArchitect f _ y) a b floor hl hr
  · obtain ⟨root,aa,_,h₁,_⟩ := stop
    have plain := root.plain false block (plainZeroNode leaf (fun _ => trivial)) done (fun _ => trivial)
      (by simp [headerCount,HeaderReader.reads])
    exact (outsideNeedsReturn G f _ y aa plain hm h₁).elim
  · obtain ⟨v,last,_,hs,hL,hR⟩ := more
    exact ⟨v,last,hs,hL,hR⟩

private theorem middleMustSwitch (d : ℕ) (y : Exclusive false (.both :: List.replicate d .second)) :
    Mandatory (y.run false) := by
  have rootHit {V : Type} (n : ℕ)
      (root : NodeCursor (Word ℕ) V (List.replicate n (soleReader false) ++ .both :: List.replicate d .second))
      (k : V → Script Tree) : Mandatory (root.run false block k) :=
    root.mandatory false block k (by simp [headerCount,soleReader,HeaderReader.reads])
      (fun ms j hm n i lo hi _ _ h hs => laterBlockCut ms j hm n i lo hi h hs)
  cases y with
  | atRoot n root => exact fun _ _ h hs => rootHit n root done h hs
  | inBlock n m root inner =>
    apply mandatoryAfter
    exact fun ys _ _ h hs => rootHit n root (fun g => done (g (inner.put ys))) h hs

private theorem outsidePivotLeaves (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (d t : ℕ) (root : NodeCursor (Word ℕ) (Word ℕ → Tree) (List.replicate d .second))
    (r n : ℕ) (leafs : NodeCursor ℕ (Word ℕ) (List.replicate n .first ++ .both :: List.replicate r .second))
    (x : Exclusive false (List.replicate t .second)) (a b c : ℕ)
    (h₁ : PairTurn f (wins G false) false (x.run false)
      (leafs.run false leaf (fun w => root.run false block (fun g => done (g w)))) a)
    (h₂ : LeftWin f G false (x.run true) b)
    (h₃ : LeftWin f G false (leafs.run true leaf (fun w => root.run true block (fun g => done (g w)))) c) :
    HasTriangle G := by
  let ky (side : Bool) (w : Word ℕ) := root.run side block fun g => done (g w)
  let R := LeftWin f G false
  induction n generalizing x a b c with
  | zero =>
    obtain ⟨tail,last,_,hl,hr⟩ := leafs.playLeaf f hf (PairTurn f (wins G false) false (x.run false))
      R (rightTurnBuilder f _ id _) (leftWinStep f G false) (ky false) (ky true) a c (max a (max b c)) h₁ h₃
    have emp : ∀ k, headerCount false (List.replicate k .second) = 0 := by
      intro k; simp [headerCount,HeaderReader.reads]
    have plain := tail.plain false leaf (fun _ => trivial) (ky false)
      (fun _ => root.plain false block (plainZeroNode leaf (fun _ => trivial)) _
        (fun _ => trivial) (emp d)) (emp r)
    have transfer := tail.transferRun f false true leaf (transfersLeafTags f) (ky false) (ky true)
      (fun _ => root.transferRun f false true block (transfersBlockTags f) _ _ (fun _ _ h => h))
    exact fromOutsideSharedCut G f hf _ _ _ _ last b last plain (x.transfer f false true) transfer hl h₂ hr
  | succ n ih =>
    obtain ⟨tail,last,_,hl,hr⟩ := leafs.soleLeaf false f hf (PairTurn f (wins G false) false (x.run false))
      R (rightTurnBuilder f _ id _) (leftWinStep f G false) (ky false) (ky true) a c (max a (max b c)) h₁ h₃
    have hit : Mandatory (tail.run false leaf (ky false)) := tail.mandatory false leaf (ky false) (by simp [headerCount,HeaderReader.reads])
      (fun ms j hj n i lo hi _ _ h hs => laterLeafCut ms j hj n i lo hi h hs)
    obtain ⟨v,next,_,h₁',h₂'⟩ := outsideFirstReturn G f hf t x _ hit last b last hl h₂
    exact ih tail v next next last h₁' h₂' hr

private theorem outsidePivotBlock (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (d t : ℕ) (y : NodeCursor (Word ℕ) Tree (.both :: List.replicate d .second))
    (x : Exclusive false (List.replicate t .second)) (a b c : ℕ)
    (h₁ : PairTurn f (wins G false) false (x.run false) (y.run false block done) a)
    (h₂ : LeftWin f G false (x.run true) b) (h₃ : LeftWin f G false (y.run true block done) c) :
    HasTriangle G := by
  let L := PairTurn f (wins G false) false (x.run false)
  let R := LeftWin f G false
  have sl : BuilderStep f L := rightTurnBuilder f _ id _
  have sr : BuilderStep f R := leftWinStep f G false
  obtain ⟨root,opt,_,hl,hr⟩ := y.split block (plainZeroNode leaf (fun _ => trivial)) f hf L R sl sr
    done done a c (max a (max b c)) h₁ h₃
  let k (side : Bool) (w : Word ℕ) := root.run side block fun g => done (g w)
  obtain ⟨n,hn⟩ := hl
  obtain ⟨r,ht⟩ := hr
  have hn' : L ((node (n+1) leaf).bind (k false)) (opt.getD a) := hn
  have ht' : R ((node (r+1) leaf).bind (k true)) (opt.getD c) := ht
  let plan := List.replicate n HeaderReader.first ++ .both :: List.replicate r .second
  have cm : headerCount false plan = n+1 := by simp [plan,headerCount,HeaderReader.reads]
  have cr : headerCount true plan = r+1 := by simp [plan,headerCount,HeaderReader.reads]
  obtain ⟨marks,total,hm,sorted,hL,hR⟩ := synchronizeNodes f hf plan leaf leaf
    (fun s => L (s.bind (k false))) (fun s => R (s.bind (k true)))
    (fun q last h => sl (fun j => (q j).bind (k false)) last h)
    (fun q last h => sr (fun j => (q j).bind (k true)) last h)
    _ _ (max b (opt.getD (max a c))) (cm ▸ hn') (cr ▸ ht')
  let base : NodeCursor ℕ (Word ℕ) _ := NodeCursor.ofHeader marks total _ sorted
  let leafs := base.replan hm
  have run (side : Bool) : leafs.run side leaf (k side) =
      (nodeBody leaf (headerIndices side marks) total).bind (k side) :=
    NodeCursor.runOfHeader marks total _ sorted side leaf (k side)
  exact outsidePivotLeaves G f hf d t root r n leafs x total b total
    (by change L (leafs.run false leaf (k false)) total; rwa [run]) h₂
    (by change R (leafs.run true leaf (k true)) total; rwa [run])

private theorem completeOutside12 (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (d t : ℕ) (y : Exclusive false (.both :: List.replicate d .second))
    (x : Exclusive false (List.replicate t .second)) (a b c : ℕ)
    (h₁ : PairTurn f (wins G false) false (x.run false) (y.run false) a)
    (h₂ : LeftWin f G false (x.run true) b) (h₃ : LeftWin f G false (y.run true) c) : HasTriangle G := by
  let L := PairTurn f (wins G false) false (x.run false)
  let R := LeftWin f G false
  obtain stop | more := y.advance f hf L R (rightTurnBuilder f _ id _) (leftWinStep f G false)
    (rightTurnArchitect f _ _) a c (max a (max b c)) h₁ h₃
  · obtain ⟨root,aa,cc,hl,hr⟩ := stop
    exact outsidePivotBlock G f hf d t root x aa b cc hl h₂ hr
  · obtain ⟨next,last,dec,_,hl,hr⟩ := more
    obtain ⟨v,z,_,hL,hR⟩ := outsideFirstReturn G f hf t x _ (middleMustSwitch d next) last b last hl h₂
    exact completeOutside12 G f hf d t next v z z last hL hR hr
termination_by y.rank
decreasing_by exact dec

theorem outsideTriangle (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f) (d : ℕ)
    (h : LeftWin f G false (node (d+1) block) 0) : HasTriangle G := by
  obtain ⟨xs,size,horder,hclock,hL,hR⟩ := synchronizeOpeningRoots f hf G d false h
  let base : NodeCursor (Word ℕ) Tree _ := NodeCursor.ofHeader xs size 0 hclock
  let first : NodeCursor (Word ℕ) Tree (soleReader false :: (List.replicate d .first ++ List.replicate (d+1) .second)) :=
    base.replan (horder.trans (by rw [openingLayout,List.replicate_succ]; rfl))
  have run (b : Bool) : first.run b block done = nodeBody block (headerIndices b xs) size := by
    change base.run b block done = _
    rw [show base = _ from rfl,NodeCursor.runOfHeader,bindDone]
  obtain ⟨m,root,leafs,last,_,hp,hq⟩ := first.firstSolo false f hf (LeftWin f G false)
    (LeftWin f G false) (leftWinStep f G false) (leftWinStep f G false) (fun _ _ h => h)
    size size size (by rwa [run]) (by rwa [run])
  let x : Exclusive false (List.replicate (d+1) .second) := .inBlock d m root leafs
  obtain ⟨r,ys,total,ho,hs,h₁,h₂⟩ := openOutsideMiddleFromCut G f hf (x.run false) d last 0 last hp h
  let mid : NodeCursor (Word ℕ) Tree _ := NodeCursor.ofHeader ys total last hs
  let y : Exclusive false (.both :: List.replicate d .second) := .atRoot r (mid.replan
    (by simpa [outsideMiddleLayout,List.append_assoc,soleReader] using ho))
  have midRun (b : Bool) : y.run b = nodeBody block (headerIndices b ys) total := by
    change mid.run b block done = _
    rw [show mid = _ from rfl,NodeCursor.runOfHeader,bindDone]
  exact completeOutside12 G f hf d (d+1) y x total last total (by rwa [midRun]) hq (by rwa [midRun])

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

private theorem walkRight {P : Option (Tree × Tree × Bool) → Prop} (f : ℕ → ℕ) (hb : ¬ P none)
    (p : Script Tree) (A : Prop)
    (doneCase : ∀ z a, PairTurn f P false p (done z) a → A)
    (cutCase : ∀ q a, PairTurn f P true p q a → A) (q : Script Tree) (a : ℕ)
    (h : PairTurn f P false p q a) : A := by
  induction q generalizing a with
  | done z => exact doneCase z a h
  | cut q => exact cutCase q a h
  | architect t ih =>
    obtain ⟨n,hn⟩ := h
    exact ih n _ hn
  | builder t ih =>
    obtain ⟨n,hn⟩ := (rightTurnBuilder f P hb p t a h).exists
    exact ih _ _ hn

private theorem insideRightDone (G : SimpleGraph Tree) (f : ℕ → ℕ) (z : Tree)
    (y x y' x' : Script Tree) (a b : ℕ) (hy : Transfers f y y') (hx : Transfers f x x')
    (h : PairTurn f (insidePromise G f y) false x (done z) a)
    (h' : PairTurn f (wins G true) true x' y' b) : HasTriangle G := by
  have hz := finishForce x (fun w => some (w,z,true)) (insidePromise G f y) (fun h => h.1.elim) f a h
  obtain ⟨_,hw⟩ := forceWitness _ _ _ hz
  have hX := hx _ (forcesMono f x _ _ (fun _ h => h.1.1.symm) hz)
  have hY := hy _ (forcesMono f y _ _ (fun _ h => h.symm) hw.2.2)
  exact ⟨z,closeRemainingPair G f z x' y' true true b hX hY h'⟩

private theorem insideWithoutLeftCuts (G : SimpleGraph Tree) (f : ℕ → ℕ) (y x z : Script Tree) (a : ℕ)
    (hx : Plain x) (h : PairTurn f (insidePromise G f y) true x z a) : False := by
  have hp := noCutsFirst x z (plainNoCuts _ hx) (insidePromise G f y) (fun h => h.1.elim) f a h
  obtain ⟨_,hz⟩ := forceWitness _ _ _ hp
  obtain ⟨_,hw⟩ := forceWitness _ _ _ hz
  exact Bool.noConfusion hw.1.2

private theorem completeInside13 (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (y y' : Script Tree) (hy : Transfers f y y') (t : ℕ) (x : Exclusive true (List.replicate t .first))
    (z : Script Tree) (a b : ℕ)
    (h₁ : PairTurn f (insidePromise G f y) true (x.run true) z a)
    (h₂ : PairTurn f (wins G true) true (x.run false) y' b) : HasTriangle G := by
  let P := insidePromise G f y
  let L (p : Script Tree) := PairTurn f P true p z
  let R (p : Script Tree) := PairTurn f (wins G true) true p y'
  obtain stop | more := x.advance f hf L R (leftTurnBuilder f P (fun h => h.1.elim) z)
    (leftTurnBuilder f _ id _) (leftTurnArchitect f P z) a b (max a b) h₁ h₂
  · obtain ⟨root,aa,_,hl,_⟩ := stop
    have plain := root.plain true block (plainZeroNode leaf (fun _ => trivial)) done
      (fun _ => trivial) (by simp [headerCount,HeaderReader.reads])
    exact (insideWithoutLeftCuts G f y _ z aa plain hl).elim
  · obtain ⟨next,last,dec,_,hl,hr⟩ := more
    apply walkRight f (P := P) (fun h => h.1.elim) (next.run true) _ _ _ z last hl
    · intro w aa hw
      exact insideRightDone G f w y _ y' _ aa last hy (next.transfer f true false) hw hr
    · intro q aa hq
      exact completeInside13 G f hf y y' hy t next q aa last hq hr
termination_by x.rank
decreasing_by exact dec

private theorem insideFinalLeaves (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (y y' : Script Tree) (hy : Transfers f y y') (n m : ℕ) (x : NodeCursor ℕ (Word ℕ)
      (List.replicate n .second ++ List.replicate m .first))
    (u v : Word ℕ → Script Tree) (share : ∀ w, Transfers f (v w) (u w))
    (plain : ∀ w, Plain (v w)) (z : Script Tree) (a b : ℕ)
    (h₁ : PairTurn f (insidePromise G f y) true (x.run true leaf v) z a)
    (h₂ : PairTurn f (wins G true) true (x.run false leaf u) y' b) : HasTriangle G := by
  let P := insidePromise G f y
  induction n generalizing z a b with
  | zero =>
    have hpl := x.plain true leaf (fun _ => trivial) v plain (by simp [headerCount,HeaderReader.reads])
    exact (insideWithoutLeftCuts G f y _ _ a hpl h₁).elim
  | succ n ih =>
    obtain ⟨tail,last,_,hl,hr⟩ := x.soleLeaf true f hf (fun p => PairTurn f P true p z)
      (fun p => PairTurn f (wins G true) true p y') (leftTurnBuilder f P (fun h => h.1.elim) z)
      (leftTurnBuilder f _ id y') v u a b (max a b) h₁ h₂
    apply walkRight f (P := P) (fun h => h.1.elim) _ _ _ _ z last hl
    · intro w aa hw
      exact insideRightDone G f w y _ y' _ aa last hy
        (tail.transferRun f true false leaf (transfersLeafTags f) v u share) hw hr
    · intro q aa hw
      exact ih tail q aa last hw hr

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

private def InsideHandoff.rootTail {G f d} (h : InsideHandoff G f d) :
    NodeCursor (Word ℕ) (Word ℕ → Tree) (List.replicate d .second ++ List.replicate d .first) where
  start := h.mark+1
  len := h.n
  put := fun ys w => h.put (toLex (w,ys))
  marks := h.rest
  roles := (List.cons.inj h.rootOrder).2
  lower := fun j hj => (List.pairwise_cons.mp (List.pairwise_cons.mp h.rootClock).2).1 j
    (List.mem_append_left _ hj)
  ordered := by
    obtain ⟨ord,_,lt⟩ := List.pairwise_append.mp (List.pairwise_cons.mp (List.pairwise_cons.mp h.rootClock).2).2
    apply List.pairwise_append.mpr
    refine ⟨ord,by simp,?_⟩
    intro j hj z hz
    obtain rfl := List.mem_singleton.mp hz
    have := lt j hj (h.mark+h.n) List.mem_cons_self
    omega

private theorem InsideHandoff.rootTailRun {G f d} (h : InsideHandoff G f d) (b : Bool) (w : Word ℕ) :
    h.rootTail.run b block (fun g => done (g w)) = h.resumeFirst b w := by
  unfold NodeCursor.run childRun InsideHandoff.resumeFirst remainingBlocks
  apply congrArg (fun p : Script (Tuple (Word ℕ) h.n) => p.bind (fun ys => done (h.put (toLex (w,ys)))))
  apply childrenCongrFrom
  intro j hj
  change h.mark+1 ≤ j at hj
  simp only [InsideHandoff.rootTail,blockAt,headerTailMem HeaderReader.both h.mark j h.rest b (by omega)]
  rfl

-- From the last 23 switch of Tree 3, finish the diversion through the
-- middle pivot and then the whole inside schedule, including both possible
-- placements of Tree 1's final 12 mark.
private theorem finishInsidePivot {G f d} (h : InsideHandoff G f d) (hf : StrictMono f)
    (x : NodeCursor ℕ (Word ℕ) (afterInsideShared h.k h.s h.m h.r))
    (q t : ℕ) (root : NodeCursor (Word ℕ) (Word ℕ → Tree) (List.replicate q .first))
    (inner : NodeCursor ℕ (Word ℕ) (List.replicate (h.k-h.s) .first ++ .both :: List.replicate t .first))
    (z z' : Script Tree) (plain : Plain z') (share : Transfers f z' z) (a b c : ℕ)
    (h₁ : PairTurn f (wins G true) false (x.run false leaf (h.resumeFirst false))
      (inner.run false leaf (fun w => root.run false block fun g => done (g w))) a)
    (h₂ : PairTurn f (wins G true) true (x.run true leaf (h.resumeFirst true)) z b)
    (h₃ : PairTurn f (wins G true) true
      (inner.run true leaf (fun w => root.run true block fun g => done (g w))) z' c) : HasTriangle G := by
  let ky (side : Bool) (w : Word ℕ) := root.run side block fun g => done (g w)
  let tail := List.replicate h.r HeaderReader.second ++ List.replicate (h.m-h.k) .first
  let xx := x.replan (show afterInsideShared h.k h.s h.m h.r = List.replicate (h.k-h.s) .first ++ tail by
    simp [afterInsideShared,tail,List.append_assoc])
  obtain ⟨v,w,b',last,_,h₄,h₅,h₆⟩ := handoffInsidePivot G f hf (h.k-h.s) tail (List.replicate t .first)
    xx inner (h.resumeFirst false) (h.resumeFirst true) (ky false) (ky true) z z' a b c
    (max a (max b c)) h₁ h₂ h₃
  let y (side : Bool) := w.run side leaf (ky side)
  have hy : Transfers f (y true) (y false) := w.transferRun f true false leaf (transfersLeafTags f) _ _
    (fun _ => root.transferRun f true false block (transfersBlockTags f) _ _ (fun _ _ h => h))
  have hp := absorbInside23 G f (y true) z' (v.run true leaf (h.resumeFirst true)) z true last b'
    (plainNoCuts _ plain) share h₆ h₅
  by_cases hd : d=0
  · apply insideFinalLeaves G f hf (y true) (y false) hy h.r (h.m-h.k) v (h.resumeFirst false)
      (h.resumeFirst true) _ _ z b' last hp h₄
    · intro u
      rw [← h.rootTailRun true u,← h.rootTailRun false u]
      exact h.rootTail.transferRun f true false block (transfersBlockTags f) _ _ (fun _ _ hx => hx)
    · intro u
      rw [← h.rootTailRun true u]
      apply h.rootTail.plain true block (plainZeroNode leaf (fun _ => trivial)) (fun g => done (g u)) (fun _ => trivial)
      simp [hd,headerCount]
  · have ht := h.threshold
    rw [if_neg hd,Nat.sub_zero] at ht
    have hk : h.m-h.k=0 := by omega
    let cur := v.replan (show tail = List.replicate h.r (soleReader true) by simp [tail,hk,soleReader])
    let vertex : Exclusive true (List.replicate d .first) := .inBlock d h.r h.rootTail cur
    have run (b : Bool) : vertex.run b = v.run b leaf (h.resumeFirst b) := by
      change v.run b leaf (fun w => h.rootTail.run b block (fun g => done (g w))) = _
      simp only [h.rootTailRun]
    exact completeInside13 G f hf (y true) (y false) hy d vertex z b' last (by rwa [run]) (by rwa [run])

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

private theorem zeroSorted {a : ℕ} {s : List Event} (h : (a :: s.filterMap Event.number).Pairwise (· < ·)) :
    (0 :: s.filterMap Event.number).Pairwise (· < ·) := List.pairwise_cons.mpr
    ⟨fun j hj => (Nat.zero_le a).trans_lt ((List.pairwise_cons.mp h).1 j hj),(List.pairwise_cons.mp h).2⟩

private theorem positiveTreeMandatory : Mandatory positiveTree := by
  intro s x h hs
  cases h with
  | @architect _ m u _ hu =>
    have hr : Reads tree (.architect (m+1)::u) x := .architect hu
    obtain ⟨ds,hd,he⟩ := treeControlShape hr hs
    have ha (v : ℕ) : control (.architect v) = true := rfl
    simp only [List.filter_cons,ha,if_true] at he
    have len := Event.architect.inj (List.cons.inj he).1
    have cnt := (shapeNumbers u).2
    rw [(List.cons.inj he).2,(shapeGroups ds).2] at cnt
    cases ds with
    | nil => simp at len
    | cons n ns =>
      have hh := hd n List.mem_cons_self
      simp only [List.sum_cons] at cnt
      simp only [List.count_cons]
      omega

private theorem oneMarkedChildren (j n i : ℕ) : OneCut (children (leafRun [j]) n i) := by
  induction n generalizing i with
  | zero => trivial
  | succ n ih =>
    by_cases he : i=j
    · subst i
      apply oneBeforePlain
      · simp [leafRun,leaf,OneCut,Plain]
      · intro x
        apply plainBind
        · apply plainChildren
          intro l hl
          have ne : l ≠ j := by omega
          simp [leafRun,ne,leaf,Plain]
        · exact fun _ => trivial
    · apply plainBeforeOne
      · simp [leafRun,he,leaf,Plain]
      · exact fun _ => oneBeforePlain _ _ (ih _) (fun _ => trivial)

private theorem NodeCursor.oneLeaf {V B : Type} {rs : List HeaderReader} (c : NodeCursor ℕ V rs)
    (b : Bool) (k : V → Script B) (hk : ∀ v, Plain (k v)) (num : headerCount b rs = 1) :
    OneCut (c.run b leaf k) := by
  have len := headerIndicesLength b c.marks
  rw [c.roles,num] at len
  obtain ⟨j,hj⟩ := List.length_eq_one_iff.mp len
  apply oneBeforePlain
  · change OneCut (children (leafRun (headerIndices b c.marks)) c.len c.start)
    rw [hj]
    exact oneMarkedChildren _ _ _
  · exact fun _ => hk _

private theorem oneRead {A : Type} (p : Script A) (hp : OneCut p) {s x}
    (h : Reads p s x) : s.count .cut ≤ 1 := by
  induction h with
  | done => simp
  | cut h ih => simp [noCutsRead _ (plainNoCuts _ hp) h]
  | builder h ih | architect h ih => simpa using ih (hp _)

private theorem insideNeedsTwo (G : SimpleGraph Tree) (f : ℕ → ℕ) (p q : Script Tree)
    (a : ℕ) (one : OneCut p) (need : Mandatory q) (h : PairTurn f (wins G true) true p q a) : False := by
  obtain ⟨_,_,_,l,r,s,hw,hl,hr,weave,hs⟩ := completePairPosition f _ id p q a h
  obtain ⟨_,rfl⟩ := hw
  have bal := weave.cutBalance
  have lc := oneRead p one hl
  have rc := need hr ((zeroSorted hs).sublist (weave.localNumbers.2.cons_cons 0))
  change l.count .cut + 0 = r.count .cut + 1 at bal
  omega

private theorem insideNeedsLast (G : SimpleGraph Tree) (f : ℕ → ℕ) (p q : Script Tree)
    (a : ℕ) (need : Mandatory p) (plain : Plain q) (h : PairTurn f (wins G true) false p q a) : False := by
  obtain ⟨_,_,_,_,r,s,hw,hl,hr,weave,hs⟩ := completePairPosition f _ id (cut p) q a h
  obtain ⟨_,rfl⟩ := hw
  cases hl with
  | @cut _ l _ hp =>
    have lc := need hp ((zeroSorted hs).sublist (weave.localNumbers.1.cons_cons 0))
    have rc := noCutsRead _ (plainNoCuts _ plain) hr
    have bal := weave.cutBalance
    change (Event.cut :: l).count .cut + 0 = r.count .cut + 1 at bal
    simp at bal
    omega

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

private abbrev pivotRemainder (k s e : ℕ) :=
  List.replicate (k-s) HeaderReader.first ++ .both :: List.replicate (e-(k-s)) .first

private inductive MiddleProgress (k s t : ℕ) where
  | earlier (y : Exclusive true (.both :: List.replicate t .first))
  | pivot (e n : ℕ) (root : NodeCursor (Word ℕ) (Word ℕ → Tree) (List.replicate t .first))
      (inner : NodeCursor ℕ (Word ℕ) (List.replicate n .second ++ pivotRemainder k s e))

private def MiddleProgress.run {k s t} : MiddleProgress k s t → Bool → Script Tree
  | .earlier y,b => y.run b
  | .pivot _ _ root inner,b => inner.run b leaf (fun w => root.run b block (fun g => done (g w)))

private def MiddleProgress.history {k s t} : MiddleProgress k s t → ℕ → List ℕ → List ℕ
  | .earlier _, count, pre => count::pre
  | .pivot e _ _ _, count, pre => count::(pre++[e])

private theorem mandatoryExclusiveBoth (b : Bool) (tail : List HeaderReader) (y : Exclusive b (.both::tail)) :
    Mandatory (y.run b) := by
  have rootHit {V : Type} (n : ℕ) (root : NodeCursor (Word ℕ) V (List.replicate n (soleReader b) ++ .both::tail))
      (k : V → Script Tree) : Mandatory (root.run b block k) :=
    root.mandatory b block k (by cases b <;> simp [headerCount,soleReader,HeaderReader.reads])
      (fun ms j hm n i lo hi _ _ h hs => laterBlockCut ms j hm n i lo hi h hs)
  cases y with
  | atRoot n root => exact fun _ _ h hs => rootHit n root done h hs
  | inBlock n m root inner =>
    apply mandatoryAfter
    exact fun ys _ _ h hs => rootHit n root (fun g => done (g (inner.put ys))) h hs

private theorem MiddleProgress.pending {k s t} (y : MiddleProgress k s t) : Mandatory (y.run true) := by
  cases y with
  | earlier y => exact fun h hs => mandatoryExclusiveBoth true _ y h hs
  | pivot e n root inner =>
    apply inner.mandatory true leaf _
    · simp [headerCount,pivotRemainder,HeaderReader.reads]
    · exact fun ms j hm n i lo hi _ _ h hs => laterLeafCut ms j hm n i lo hi h hs

private theorem readyOneCut (k s t e : ℕ) (root : NodeCursor (Word ℕ) (Word ℕ → Tree) (List.replicate t .first))
    (inner : NodeCursor ℕ (Word ℕ) (pivotRemainder k s e)) :
    OneCut (inner.run true leaf (fun w => root.run true block (fun g => done (g w)))) := by
  apply inner.oneLeaf
  · exact fun _ => root.plain true block (plainZeroNode leaf (fun _ => trivial)) _ (fun _ => trivial)
      (by simp [headerCount,HeaderReader.reads])
  · simp [pivotRemainder,headerCount,HeaderReader.reads]

private theorem stepMiddle23 (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f)
    (k j s count t : ℕ) (pre : List ℕ) (here : pre.length=j)
    (x : Script (List ℕ × Tree)) (z : Script Tree) (A : Prop)
    (onCut : ∀ (y : MiddleProgress k s t) a b,
      PairTurn f (pivotWins G k j s) false x (markCounts (y.run false) (y.history count pre)) a →
      PairTurn f (wins G true) false (y.run true) z b → A)
    (onPivot : ∀ (e : ℕ) (root : NodeCursor (Word ℕ) (Word ℕ → Tree) (List.replicate t .first))
      (inner : NodeCursor ℕ (Word ℕ) (pivotRemainder k s e)) a b,
      let y := fun side => inner.run side leaf (fun w => root.run side block (fun g => done (g w)))
      PairTurn f (pivotWins G k j s) false x (markCounts (y false) (count::(pre++[e]))) a →
      PairTurn f (wins G true) true (y true) z b → A)
    (y : MiddleProgress k s t) (a b : ℕ)
    (h₁ : PairTurn f (pivotWins G k j s) false x (markCounts (y.run false) (y.history count pre)) a)
    (h₂ : PairTurn f (wins G true) true (y.run true) z b) : A := by
  let L (v : Script Tree) := PairTurn f (wins G true) true v z
  let R (hist : List ℕ) (v : Script Tree) := PairTurn f (pivotWins G k j s) false x (markCounts v hist)
  have sr (hist) : BuilderStep f (R hist) := fun q last h =>
    rightTurnBuilder f (pivotWins G k j s) id x (fun v => markCounts (q v) hist) last h
  have pivotStep (e n : ℕ) (root : NodeCursor (Word ℕ) (Word ℕ → Tree) (List.replicate t .first))
      (inner : NodeCursor ℕ (Word ℕ) (List.replicate n .second ++ pivotRemainder k s e)) (aa bb : ℕ)
      (h₃ : R (count::(pre++[e])) (inner.run false leaf (fun w => root.run false block fun g => done (g w))) aa)
      (h₄ : L (inner.run true leaf (fun w => root.run true block fun g => done (g w))) bb) : A := by
    cases n with
    | zero => exact onPivot e root inner aa bb h₃ h₄
    | succ n =>
      obtain ⟨next,last,_,hl,hr⟩ := inner.soleLeaf true f hf L (R (count::(pre++[e])))
        (leftTurnBuilder f _ id z) (sr _) _ _ bb aa (max aa bb) h₄ h₃
      exact onCut (.pivot e n root next) last last hr hl
  cases y with
  | pivot e n root inner => exact pivotStep e n root inner a b h₁ h₂
  | earlier v =>
    obtain stop | more := v.advance f hf L (R (count::pre)) (leftTurnBuilder f _ id z) (sr _)
      (leftTurnArchitect f _ z) b a (max a b) h₂ h₁
    · obtain ⟨root,bb,aa,hl,hr⟩ := stop
      obtain ⟨e,r,tail,inner,last,_,_,_,_,hw,hv⟩ := openInsidePivotBlock G f hf k j s count pre here _ root
        x z aa bb (max aa bb) hr hl
      let c := inner.replan (show middleLeafLayout r e k s = List.replicate r .second ++ pivotRemainder k s e by
        simp [middleLeafLayout,pivotRemainder,List.append_assoc])
      exact pivotStep e r tail c last last hw hv
    · obtain ⟨next,last,_,_,hl,hr⟩ := more
      exact onCut (.earlier next) last last hr hl

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

private abbrev FirstPivotCursor {G f d} (h : InsideHandoff G f d) :=
  NodeCursor ℕ (Word ℕ) (afterInsideShared h.k h.s h.m h.r)

private abbrev firstRecorded {G f d} (h : InsideHandoff G f d) (x : FirstPivotCursor h) :=
  markCounts (x.run false leaf (h.resumeFirst false)) []

private abbrev firstOther {G f d} (h : InsideHandoff G f d) (x : FirstPivotCursor h) :=
  x.run true leaf (h.resumeFirst true)

private theorem nextMiddleAgainstPending {G f d} (h : InsideHandoff G f d) (hf : StrictMono f)
    (x : FirstPivotCursor h) (t : ℕ) (pre : List ℕ) (here : pre.length=h.j)
    (y : MiddleProgress h.k h.s t) (z : Script Tree) (need : Mandatory z) (a b : ℕ)
    (h₁ : PairTurn f (pivotWins G h.k h.j h.s) false (firstRecorded h x)
      (markCounts (y.run false) (y.history h.count pre)) a)
    (h₂ : PairTurn f (wins G true) true (y.run true) z b) :
    ∃ (y' : MiddleProgress h.k h.s t) (aa bb : ℕ),
      PairTurn f (pivotWins G h.k h.j h.s) false (firstRecorded h x)
        (markCounts (y'.run false) (y'.history h.count pre)) aa ∧
      PairTurn f (wins G true) false (y'.run true) z bb := by
  apply stepMiddle23 G f hf h.k h.j h.s h.count t pre here (firstRecorded h x) z _ _ _ y a b h₁ h₂
  · exact fun v aa bb hl hr => ⟨v,aa,bb,hl,hr⟩
  · intro e root inner aa bb _ _ hr
    exact (insideNeedsTwo G f _ z bb (readyOneCut _ _ _ _ root inner) need hr).elim

private theorem afterThirdShared {G f d} (h : InsideHandoff G f d) (hf : StrictMono f)
    (x : FirstPivotCursor h) (t : ℕ) (pre : List ℕ) (here : pre.length=h.j)
    (y : MiddleProgress h.k h.s t) (z z' : Script Tree) (plain : Plain z') (share : Transfers f z' z)
    (a b c : ℕ)
    (h₁ : PairTurn f (pivotWins G h.k h.j h.s) false (firstRecorded h x)
      (markCounts (y.run false) (y.history h.count pre)) a)
    (h₂ : PairTurn f (wins G true) true (firstOther h x) z b)
    (h₃ : PairTurn f (wins G true) true (y.run true) z' c) : HasTriangle G := by
  apply stepMiddle23 G f hf h.k h.j h.s h.count t pre here _ z' _ _ _ y a c h₁ h₃
  · intro v aa bb _ hr
    exact (insideNeedsLast G f _ z' bb (fun hr hs => v.pending hr hs) plain hr).elim
  · intro e root inner aa bb _ hl hr
    have live := forgetPivotAfterHandoff G f h.k h.j h.s aa _ _ [] (h.count::(pre++[e])) false hl
    exact finishInsidePivot h hf x t (e-(h.k-h.s)) root inner z z' plain share aa b bb live h₂ hr

private theorem runThirdPivotLeaves {G f d} (h : InsideHandoff G f d) (hf : StrictMono f)
    (x : FirstPivotCursor h) (t : ℕ) (pre : List ℕ) (here : pre.length=h.j)
    (q r n : ℕ) (root : NodeCursor (Word ℕ) (Word ℕ → Tree) (List.replicate q .first))
    (inner : NodeCursor ℕ (Word ℕ) (List.replicate n .second ++ .both :: List.replicate r .first))
    (y : MiddleProgress h.k h.s t) (a b c : ℕ)
    (h₁ : PairTurn f (pivotWins G h.k h.j h.s) false (firstRecorded h x)
      (markCounts (y.run false) (y.history h.count pre)) a)
    (h₂ : PairTurn f (wins G true) false (firstOther h x)
      (inner.run false leaf (fun w => root.run false block (fun g => done (g w)))) b)
    (h₃ : PairTurn f (wins G true) false (y.run true)
      (inner.run true leaf (fun w => root.run true block (fun g => done (g w)))) c) : HasTriangle G := by
  let kz (side : Bool) (w : Word ℕ) := root.run side block fun g => done (g w)
  let L := PairTurn f (wins G true) false (firstOther h x)
  induction n generalizing y a b c with
  | zero =>
    obtain ⟨tail,last,_,hL,hR⟩ := inner.playLeaf f hf L (PairTurn f (wins G true) false (y.run true))
      (rightTurnBuilder f _ id _) (rightTurnBuilder f _ id _) (kz false) (kz true) b c (max a (max b c)) h₂ h₃
    have zero (n : ℕ) : headerCount true (List.replicate n .first) = 0 := by simp [headerCount,HeaderReader.reads]
    have plain := tail.plain true leaf (fun _ => trivial) (kz true) (fun _ =>
      root.plain true block (plainZeroNode leaf (fun _ => trivial)) _ (fun _ => trivial) (zero q)) (zero r)
    have share := tail.transferRun f true false leaf (transfersLeafTags f) (kz true) (kz false)
      (fun _ => root.transferRun f true false block (transfersBlockTags f) _ _ (fun _ _ hg => hg))
    exact afterThirdShared h hf x t pre here y _ _ plain share a last last h₁ hL hR
  | succ n ih =>
    obtain ⟨tail,last,_,hr,hl⟩ := inner.soleLeaf true f hf (PairTurn f (wins G true) false (y.run true)) L
      (rightTurnBuilder f _ id _) (rightTurnBuilder f _ id _) (kz true) (kz false) c b (max a (max b c)) h₃ h₂
    have need : Mandatory (tail.run true leaf (kz true)) := tail.mandatory true leaf (kz true)
      (by simp [headerCount,HeaderReader.reads]) (fun ms j hm n i lo hi _ _ h hs => laterLeafCut ms j hm n i lo hi h hs)
    obtain ⟨v,aa,cc,hv,hz⟩ := nextMiddleAgainstPending h hf x t pre here y _ need a last h₁ hr
    exact ih tail v aa last cc hv hl hz

private theorem runThirdPivotBlock {G f d} (h : InsideHandoff G f d) (hf : StrictMono f)
    (x : FirstPivotCursor h) (t : ℕ) (pre : List ℕ) (here : pre.length=h.j)
    (q : ℕ) (z : NodeCursor (Word ℕ) Tree (.both :: List.replicate q .first))
    (y : MiddleProgress h.k h.s t) (a b c : ℕ)
    (h₁ : PairTurn f (pivotWins G h.k h.j h.s) false (firstRecorded h x)
      (markCounts (y.run false) (y.history h.count pre)) a)
    (h₂ : PairTurn f (wins G true) false (firstOther h x) (z.run false block done) b)
    (h₃ : PairTurn f (wins G true) false (y.run true) (z.run true block done) c) : HasTriangle G := by
  let L := PairTurn f (wins G true) false (firstOther h x)
  let R := PairTurn f (wins G true) false (y.run true)
  have sl : BuilderStep f L := rightTurnBuilder f _ id _
  have sr : BuilderStep f R := rightTurnBuilder f _ id _
  obtain ⟨root,opt,_,hl,hr⟩ := z.split block (plainZeroNode leaf (fun _ => trivial)) f hf L R sl sr
    done done b c (max a (max b c)) h₂ h₃
  let kz (side : Bool) (w : Word ℕ) := root.run side block fun g => done (g w)
  obtain ⟨r,hm⟩ := hl
  obtain ⟨n,hn⟩ := hr
  have hm' : L ((node (r+1) leaf).bind (kz false)) (opt.getD b) := hm
  have hn' : R ((node (n+1) leaf).bind (kz true)) (opt.getD c) := hn
  let plan := List.replicate n HeaderReader.second ++ .both :: List.replicate r .first
  have cm : headerCount false plan = r+1 := by simp [plan,headerCount,HeaderReader.reads]
  have cn : headerCount true plan = n+1 := by simp [plan,headerCount,HeaderReader.reads]
  obtain ⟨marks,last,ms,sorted,H₁,H₂⟩ := synchronizeNodes f hf plan leaf leaf
    (fun s => L (s.bind (kz false))) (fun s => R (s.bind (kz true)))
    (fun lt aa H => sl (fun v => (lt v).bind (kz false)) aa H)
    (fun lt aa H => sr (fun v => (lt v).bind (kz true)) aa H)
    _ _ (max a (opt.getD (max b c))) (cm ▸ hm') (cn ▸ hn')
  let base : NodeCursor ℕ (Word ℕ) _ := NodeCursor.ofHeader marks last _ sorted
  let inner := base.replan ms
  have run (side : Bool) : inner.run side leaf (kz side) = (nodeBody leaf (headerIndices side marks) last).bind (kz side) :=
    NodeCursor.runOfHeader marks last _ sorted side leaf (kz side)
  exact runThirdPivotLeaves h hf x t pre here q r n root inner y a last last h₁
    (by change L (inner.run false leaf (kz false)) last; rwa [run])
    (by change R (inner.run true leaf (kz true)) last; rwa [run])

private theorem runThirdPrefix {G f d} (h : InsideHandoff G f d) (hf : StrictMono f)
    (x : FirstPivotCursor h) (t : ℕ) (pre : List ℕ) (here : pre.length=h.j)
    (q : ℕ) (z : Exclusive true (.both :: List.replicate q .first))
    (y : MiddleProgress h.k h.s t) (a b c : ℕ)
    (h₁ : PairTurn f (pivotWins G h.k h.j h.s) false (firstRecorded h x)
      (markCounts (y.run false) (y.history h.count pre)) a)
    (h₂ : PairTurn f (wins G true) false (firstOther h x) (z.run false) b)
    (h₃ : PairTurn f (wins G true) false (y.run true) (z.run true) c) : HasTriangle G := by
  let L := PairTurn f (wins G true) false (firstOther h x)
  let R := PairTurn f (wins G true) false (y.run true)
  obtain stop | more := z.advance f hf R L (rightTurnBuilder f _ id _) (rightTurnBuilder f _ id _)
    (rightTurnArchitect f _ _) c b (max a (max b c)) h₃ h₂
  · obtain ⟨root,cc,bb,hr,hl⟩ := stop
    exact runThirdPivotBlock h hf x t pre here q root y a bb cc h₁ hl hr
  · obtain ⟨next,last,dec,_,hr,hl⟩ := more
    obtain ⟨v,aa,cc,hv,hz⟩ := nextMiddleAgainstPending h hf x t pre here y _
      (fun h hs => mandatoryExclusiveBoth true _ next h hs) a last h₁ hr
    exact runThirdPrefix h hf x t pre here q next v aa last cc hv hl hz
termination_by z.rank
decreasing_by exact dec

end Erdos591Proof.HeightTwoGame

namespace Erdos591Proof.HeightTwoGame
open Script

private theorem realizeInsideHandoff {G f d} (h : InsideHandoff G f d) (hf : StrictMono f)
    (win : (game.score (wins G true)).outcome f true) : HasTriangle G := by
  obtain ⟨pre,x,y,a,b,c,here,_,h₁,h₂,h₃⟩ := h.reachSharedCut hf
  let t := h.count-(h.j+1)
  let start : MiddleProgress h.k h.s t := .earlier (.atRoot d (y.replan
    (by simp [middleFromPivot,soleReader,t,List.append_assoc])))
  obtain ⟨v,aa,cc,hv,hw⟩ := nextMiddleAgainstPending h hf x t pre here start positiveTree
    (fun h hs => positiveTreeMandatory h hs) a c h₁ h₃
  have neutral : Neutral f (firstOther h x) := by
    apply neutralBind
    · apply neutralChildren
      intro i
      cases decide (i ∈ headerIndices true x.marks) <;> exact fun _ => trivial
    · intro _
      exact neutralBind _ _ _ (neutralChildren f _ (fun _ => neutralBlock f _) _ _) fun _ => trivial
  obtain tri | ⟨r,n,zs,total,hplan,sorted,hx,hy⟩ := thirdRootFromCuts G f hf true win
    (firstOther h x) (v.run true) b cc (max aa (max b cc)) neutral h₂ hw
  · exact tri
  let base : NodeCursor (Word ℕ) Tree _ := NodeCursor.ofHeader zs total _ sorted
  let z : Exclusive true (.both :: List.replicate r .first) := .atRoot n (base.replan
    (by simpa [thirdRootLayout,soleReader,List.append_assoc] using hplan))
  have run (p : Bool) : z.run p = nodeBody block (headerIndices p zs) total := by
    change (NodeCursor.ofHeader zs total _ sorted).run p block done = _
    rw [NodeCursor.runOfHeader,bindDone]
  exact runThirdPrefix h hf x t pre here r z v aa total total hv (by rwa [run]) (by rwa [run])

theorem insideTriangle (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f) (d : ℕ)
    (h : LeftWin f G true (node (d+1) block) 0) : HasTriangle G := by
  obtain tri | ⟨g,hg,⟨stage⟩⟩ := insideFirstHandoff G f hf d h
  · exact tri
  have win : (game.score (wins G true)).outcome f true := ⟨d+1,h⟩
  exact realizeInsideHandoff stage (hf.comp hg) (PairGame.outcomeSubsequence _ _ _ hg true win)

theorem triangle (G : SimpleGraph Tree) (f : ℕ → ℕ) (hf : StrictMono f) (d : ℕ) (b : Bool)
    (h : ((increasing ((node (d+1) block).interleave tree) 0).score (wins G b)).outcome f true) :
    ∃ x y z, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z := by
  cases b with
  | false => exact outsideTriangle G f hf d h
  | true => exact insideTriangle G f hf d h

end Erdos591Proof.HeightTwoGame

theorem OMA.solution : type_of% @Erdos591.erdos_591 := by
  exact Erdos591Proof.HeightTwoGame.ramseyOfPositiveOpening Erdos591Proof.HeightTwoGame.triangle
