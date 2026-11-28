import FormalConjectures.ErdosProblems.«118»
import Mathlib.SetTheory.Ordinal.CantorNormalForm
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Data.Sigma.Order
import Mathlib.Data.Prod.Lex
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Logic.Equiv.List
import Mathlib.Data.Set.Constructions
import Mathlib.Logic.Encodable.Basic

/-!
# Larson’s ordinal partition theorem

The pair-game construction proves the Larson variant of Erdős problem 118 and its parent theorem.
-/

open Ordinal
open scoped Cardinal
universe u v

namespace Larson

private theorem imageClique {A : Type u} {B : Type v}
    [LinearOrder A] [WellFoundedLT A] [LinearOrder B] [WellFoundedLT B]
    (e : ((· < ·) : A → A → Prop) ≃r ((· < ·) : B → B → Prop))
    (G : SimpleGraph B) {a : Ordinal.{u}} {b : Ordinal.{v}}
    (hab : lift.{v} a = lift.{u} b)
    (h : ∃ s, (G.comap e).IsClique s ∧ typeLT s = a) :
    ∃ t, G.IsClique t ∧ typeLT t = b := by
  obtain ⟨s, hs, hsa⟩ := h
  let t := e '' s
  refine ⟨t, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
    exact hs hx hy (fun he => hne (congrArg e he))
  · let f : ((· < ·) : s → s → Prop) ≃r ((· < ·) : t → t → Prop) :=
      { toEquiv := e.toEquiv.image s
        map_rel_iff' := e.map_rel_iff }
    apply lift_inj.{u}.mp
    exact f.ordinal_lift_type_eq.symm.trans ((congrArg lift hsa).trans hab)

private theorem ramseyTransport {a b c : Ordinal.{u}} {d p q : Ordinal.{v}}
    (ha : lift.{v} a = lift.{u} d) (hb : lift.{v} b = lift.{u} p)
    (hc : lift.{v} c = lift.{u} q) (h : Erdos118.OrdinalRamsey a b c) :
    Erdos118.OrdinalRamsey d p q := by
  have he : Nonempty (((· < ·) : a.ToType → a.ToType → Prop) ≃r
      ((· < ·) : d.ToType → d.ToType → Prop)) :=
    lift_type_eq.{u,v,0}.mp (by simpa only [type_toType] using ha)
  obtain ⟨e⟩ := he
  intro R B hRB
  have hcomp : IsCompl (R.comap e) (B.comap e) := by
    rw [hRB.eq_compl]
    suffices Bᶜ.comap e = (B.comap e)ᶜ by rw [this]; exact isCompl_compl.symm
    ext x y
    simp [SimpleGraph.compl_adj, SimpleGraph.comap, e.injective.eq_iff]
  rcases h _ _ hcomp with hr | hblue
  · exact Or.inl (imageClique e R hb hr)
  · exact Or.inr (imageClique e B hc hblue)

theorem ramseyLift (a b c : Ordinal.{0}) :
    Erdos118.OrdinalRamsey (lift.{u} a) (lift.{u} b) (lift.{u} c) ↔
      Erdos118.OrdinalRamsey a b c := by
  constructor <;> apply ramseyTransport <;> simp only [lift_uzero]

private theorem liftSequenceSup (f : ℕ → Ordinal.{0}) :
    lift.{u} (⨆ n, f n) = ⨆ n, lift.{u} (f n) := by
  apply le_antisymm
  · by_contra! h
    obtain ⟨b, hb, he⟩ := lt_lift_iff.mp h
    obtain ⟨n, hn⟩ := Ordinal.lt_iSup_iff.mp hb
    have hlt := lift_lt.{u}.mpr hn
    rw [he] at hlt
    exact (Ordinal.le_iSup (fun k => lift.{u} (f k)) n).not_gt hlt
  · exact Ordinal.iSup_le fun n => lift_le.mpr (Ordinal.le_iSup f n)

private theorem liftNatPower (a : Ordinal.{0}) (n : ℕ) :
    lift.{u} (a ^ n) = lift.{u} a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ, lift_mul, ih]

private theorem liftOmegaPower (a : Ordinal.{0}) (ha : 0 < a) :
    lift.{u} (a ^ ω) = lift.{u} a ^ ω := by
  have ha' : 0 < lift.{u} a := by simpa only [lift_zero] using (lift_lt.{u}.mpr ha)
  rw [← iSup_pow_natCast ha, liftSequenceSup, ← iSup_pow_natCast ha']
  simp only [liftNatPower]

private theorem iteratedOmega :
    (ω : Ordinal.{v}) ^ (ω ^ (2 : Ordinal)) = (ω ^ ω) ^ (ω : Ordinal) := by
  have he : (ω : Ordinal.{v}) ^ (2 : Ordinal) = ω * ω :=
    (opow_natCast ω 2).trans (pow_two ω)
  rw [he, opow_mul]

theorem liftLarsonOrdinal :
    lift.{u} ((ω : Ordinal.{0}) ^ (ω ^ (2 : Ordinal))) =
      (ω : Ordinal.{u}) ^ (ω ^ (2 : Ordinal)) := by
  rw [iteratedOmega.{0}, iteratedOmega.{u}, liftOmegaPower _ (opow_pos _ omega0_pos),
    liftOmegaPower _ omega0_pos, lift_omega0]

theorem concreteRamseyLift (n : ℕ) :
    Erdos118.OrdinalRamsey ((ω : Ordinal.{u}) ^ (ω ^ (2 : Ordinal)))
      (ω ^ (ω ^ (2 : Ordinal))) n ↔
    Erdos118.OrdinalRamsey ((ω : Ordinal.{0}) ^ (ω ^ (2 : Ordinal)))
      (ω ^ (ω ^ (2 : Ordinal))) n := by
  simpa only [liftLarsonOrdinal, lift_natCast] using
    (ramseyLift.{u} (ω ^ (ω ^ (2 : Ordinal))) (ω ^ (ω ^ (2 : Ordinal))) n)

end Larson

open Ordinal

namespace Larson.Branching

noncomputable section

abbrev power (n : ℕ) : Ordinal.{0} := ω ^ (n : Ordinal)

def sumTo (f : ℕ → Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => 0
  | n+1 => sumTo f n + f n

def children (f : ℕ → Ordinal.{0}) := ⨆ n, sumTo f n

private theorem sumTo_split (f : ℕ → Ordinal.{0}) (a b : ℕ) :
    sumTo f (a+b) = sumTo f a + sumTo (fun j => f (a+j)) b := by
  induction b with
  | zero => simp [sumTo]
  | succ b ih =>
    change sumTo f (a+b) + f (a+b) = sumTo f a + (sumTo (fun j => f (a+j)) b + f (a+b))
    rw [ih, add_assoc]

private theorem sumTo_mono (f : ℕ → Ordinal.{0}) : Monotone (sumTo f) :=
  monotone_nat_of_le_succ fun _ => le_self_add

def mass (leaf : List ℕ → Prop) [DecidablePred leaf] (p : List ℕ) : ℕ → Ordinal.{0}
  | 0 => if leaf p then 1 else 0
  | h+1 => children fun i => mass leaf (p ++ [i]) h

theorem blockBound (n d h : ℕ) :
    (((ω : Ordinal.{0}) ^ ω) ^ n * (ω ^ ω)) * power ((d+2)*h) <
      ((ω : Ordinal.{0}) ^ ω) ^ (n+2) := by
  let a : Ordinal.{0} := ω ^ ω
  have hpos : 0 < a ^ (n+1) := pow_pos (opow_pos _ omega0_pos) _
  have hfin : power ((d+2)*h) < a :=
    (opow_lt_opow_iff_right one_lt_omega0).mpr (natCast_lt_omega0 _)
  change (a ^ n * a) * power ((d+2)*h) < a^(n+2)
  rw [← pow_succ, pow_succ a (n+1)]
  exact mul_lt_mul_of_pos_left hfin hpos

open Order

section Bounds
variable {A : Type} [LinearOrder A] [WellFoundedLT A]

private noncomputable def cut (s : Set A) (x : A) : Ordinal.{0} :=
  ⨆ z : s, if (z : A) < x then typein ((· < ·) : s → s → Prop) z + 1 else 0

private theorem cut_le (s : Set A) (x : A) : cut s x ≤ typeLT s := by
  apply Ordinal.iSup_le
  intro z
  split
  · exact add_one_le_iff.mpr (typein_lt_type _ _)
  · exact bot_le

private theorem cut_mono (s : Set A) : Monotone (cut s) := by
  intro x y h
  apply Ordinal.iSup_le
  intro z
  apply le_trans _ (Ordinal.le_iSup _ z)
  split_ifs with hx hy hy
  · rfl
  · exact (hy (hx.trans_le h)).elim
  all_goals exact bot_le

private theorem cut_lt {s : Set A} {x y : A} (hs : x ∈ s) (h : x < y) :
    cut s x < cut s y := by
  let v : s := ⟨x, hs⟩
  have hle : cut s x ≤ typein ((· < ·) : s → s → Prop) v := by
    apply Ordinal.iSup_le
    intro z
    split
    · exact add_one_le_iff.mpr ((typein_lt_typein _).mpr (by assumption))
    · exact bot_le
  have hge := Ordinal.le_iSup (fun z : s =>
    if (z : A) < y then typein ((· < ·) : s → s → Prop) z + 1 else 0) v
  rw [if_pos (show (v : A) < y from h)] at hge
  exact (hle.trans_lt (lt_add_one _)).trans_le hge

end Bounds

private theorem rankBound {X : Type} [LinearOrder X] [WellFoundedLT X]
    (r : X → Ordinal.{0}) (hr : StrictMono r) (B : Ordinal.{0}) (hb : ∀ x, r x < B) :
    typeLT X ≤ B := by
  let f (x : X) := ToType.mk (o := B) ⟨r x,hb x⟩
  have hm : StrictMono f := fun _ _ h => ToType.mk.strictMono (hr h)
  let e : ((· < ·) : X → X → Prop) ↪r ((· < ·) : B.ToType → B.ToType → Prop) :=
    ⟨⟨f,hm.injective⟩,hm.lt_iff_lt⟩
  exact (type_le_iff'.mpr ⟨e⟩).trans_eq (type_toType B)

private noncomputable def fiberRank {X I : Type} [LinearOrder X] [WellFoundedLT X]
    (f : X → I) (x : X) : Ordinal.{0} :=
  typein ((· < ·) : {y // f y = f x} → _ → Prop) ⟨x,rfl⟩

private theorem fiberStrict {X I : Type} [LinearOrder X] [WellFoundedLT X]
    (f : X → I) {x y : X} (he : f x = f y) (h : x < y) :
    fiberRank f x < fiberRank f y := by
  have aux (a b : I) (hx : f x = a) (hy : f y = b) (hab : a = b) :
      typein ((· < ·) : {z // f z = a} → _ → Prop) ⟨x,hx⟩ <
      typein ((· < ·) : {z // f z = b} → _ → Prop) ⟨y,hy⟩ := by
    cases hab
    exact (typein_lt_typein ((· < ·) : {z // f z = a} → _ → Prop)).mpr
      (show (⟨x,hx⟩ : {z // f z = a}) < ⟨y,hy⟩ from h)
  exact aux _ _ rfl rfl he

private theorem mulMono {a b : Ordinal.{0}} (h : a ≤ b) (c : Ordinal.{0}) : c*a ≤ c*b := by
  grw [h]

theorem gapBound {X I : Type} [LinearOrder X] [WellFoundedLT X]
    [LinearOrder I] [WellFoundedLT I] (key : X → I) (hm : Monotone key)
    (T H : Ordinal.{0}) (large : Set I)
    (hs : ∀ i ∉ large, typeLT {x // key x = i} ≤ T)
    (hl : ∀ i ∈ large, typeLT {x // key x = i} ≤ H) :
    typeLT X ≤ (T * typeLT I + H) * (typeLT large + 1) := by
  classical
  let A := typeLT I
  let B := T*A + H
  let start (i : I) := T * typein ((· < ·) : I → I → Prop) i
  let offset (x : X) := (if key x ∈ large then T*A else start (key x)) + fiberRank key x
  let r (x : X) := B * cut large (key x) + offset x
  have hR (x : X) : fiberRank key x < typeLT {y // key y = key x} :=
    typein_lt_type _ _
  have small (x : X) (hx : key x ∉ large) :
      offset x < T * (typein ((· < ·) : I → I → Prop) (key x) + 1) := by
    change (if key x ∈ large then T*A else start (key x)) + _ < _
    rw [if_neg hx, mul_add_one]
    exact (add_lt_add_iff_left _).mpr ((hR x).trans_le (hs _ hx))
  have ho (x : X) : offset x < B := by
    by_cases hx : key x ∈ large
    · dsimp only [offset,B]
      rw [if_pos hx]
      exact (add_lt_add_iff_left _).mpr ((hR x).trans_le (hl _ hx))
    · exact (small x hx).trans_le ((mulMono (add_one_le_iff.mpr
        (typein_lt_type ((· < ·) : I → I → Prop) (key x))) T).trans le_self_add)
  have room (x : X) : r x < B * (cut large (key x) + 1) := by
    rw [mul_add_one]
    exact (add_lt_add_iff_left _).mpr (ho x)
  apply rankBound r _ _ (fun x => (room x).trans_le (by grw [cut_le large (key x)]))
  intro x y hxy
  have hkey := hm hxy.le
  rcases hkey.eq_or_lt with he | hlt
  · have h : offset x < offset y := by
      dsimp only [offset]
      rw [he]
      exact (add_lt_add_iff_left _).mpr (fiberStrict key he hxy)
    dsimp only [r]
    rw [he]
    exact (add_lt_add_iff_left _).mpr h
  · by_cases hx : key x ∈ large
    · exact (room x).trans_le ((mulMono (add_one_le_iff.mpr
        (cut_lt hx hlt)) B).trans le_self_add)
    · have hs' := small x hx
      have ho' : offset x < offset y := by
        by_cases hy : key y ∈ large
        · change offset x < (if key y ∈ large then T*A else start (key y)) + _
          rw [if_pos hy]
          exact hs'.trans_le ((mulMono (add_one_le_iff.mpr
            (typein_lt_type ((· < ·) : I → I → Prop) (key x))) T).trans le_self_add)
        · change offset x < (if key y ∈ large then T*A else start (key y)) + _
          rw [if_neg hy]
          exact hs'.trans_le ((mulMono (add_one_le_iff.mpr
            ((typein_lt_typein ((· < ·) : I → I → Prop)).mpr hlt)) T).trans le_self_add)
      exact ((add_lt_add_iff_left (B * cut large (key x))).mpr ho').trans_le
        (by dsimp only [r]; grw [(cut_mono large) hkey])

theorem countableFibers {X : Type} [LinearOrder X] [WellFoundedLT X]
    (key : X → ℕ) (hm : Monotone key) (g : ℕ → Ordinal.{0})
    (hg : ∀ i, typeLT {x // key x = i} ≤ g i) : typeLT X ≤ children g := by
  let r (x : X) := sumTo g (key x) + fiberRank key x
  have room (x : X) : r x < sumTo g (key x + 1) :=
    (add_lt_add_iff_left _).mpr ((typein_lt_type _ _).trans_le (hg _))
  apply rankBound r _ _ (fun x => (room x).trans_le (Ordinal.le_iSup _ _))
  intro x y h
  rcases (hm h.le).eq_or_lt with he | hlt
  · dsimp only [r]
    rw [he]
    exact (add_lt_add_iff_left _).mpr (fiberStrict key he h)
  · exact (room x).trans_le (((sumTo_mono g) hlt).trans le_self_add)

theorem unboundedSections {X : Type} [LinearOrder X] [WellFoundedLT X]
    (key : X → ℕ) (hm : Monotone key) (a b : Ordinal.{0}) (hab : a < b)
    (hX : ω ^ b ≤ typeLT X) (hf : ∀ i, typeLT {x // key x = i} < ω ^ b) :
    ∀ m, ∃ i ≥ m, ω ^ a ≤ typeLT {x // key x = i} := by
  let g (i : ℕ) := typeLT {x // key x = i}
  have bound (f : ℕ → Ordinal.{0}) (c : Ordinal.{0}) (h : ∀ i, f i < ω ^ c) (m : ℕ) :
      sumTo f m < ω ^ c := by
    induction m with
    | zero => exact opow_pos _ omega0_pos
    | succ m ih => exact isPrincipal_add_omega0_opow _ ih (h m)
  intro m
  by_contra! ht
  have hr : ω ^ a < ω ^ b := (opow_lt_opow_iff_right one_lt_omega0).mpr hab
  have hs : children g ≤ sumTo g m + ω ^ a := by
    apply Ordinal.iSup_le
    intro n
    by_cases hn : n ≤ m
    · exact ((sumTo_mono g) hn).trans le_self_add
    · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le (by omega : m ≤ n)
      rw [sumTo_split]
      exact (add_le_add_iff_left _).mpr (bound _ a (fun i => ht (m+i) (by omega)) d).le
  exact (hX.trans ((countableFibers key hm g (fun _ => le_rfl)).trans hs)).not_gt
    (isPrincipal_add_omega0_opow _ (bound g b hf m) hr)

def capped (I : Type) [LinearOrder I] [WellFoundedLT I] (T D : Ordinal.{0}) :
    ℕ → (X : Type) → [LinearOrder X] → [WellFoundedLT X] → Prop
  | 0, X, _, _ => typeLT X ≤ 1
  | h+1, X, _, _ => ∃ key : X → I, Monotone key ∧
      typeLT {i : I // T ≤ typeLT {x // key x = i}} ≤ D ∧
      ∀ i, capped I T D h {x // key x = i}

private theorem twoFactor (d : ℕ) : 2 * (power d + 1) ≤ power (d+2) := by
  have h₁ : (2 : Ordinal.{0}) ≤ ω := (natCast_lt_omega0 2).le
  have h₂ : power d + 1 ≤ power (d+1) := add_one_le_iff.mpr
    ((opow_lt_opow_iff_right one_lt_omega0).mpr (by exact_mod_cast Nat.lt_succ_self d))
  calc
    _ ≤ ω * power (d+1) := by grw [h₁,h₂]
    _ = power (d+2) := by
      change ω * ω ^ ((d+1 : ℕ) : Ordinal) = ω ^ ((d+2 : ℕ) : Ordinal)
      rw [← opow_one_add]
      congr 1
      exact_mod_cast (show 1+(d+1)=d+2 by omega)

theorem cappedBound (I : Type) [LinearOrder I] [WellFoundedLT I] (T : Ordinal.{0})
    (hT : 1 ≤ T * typeLT I) (d h : ℕ) (X : Type) [LinearOrder X] [WellFoundedLT X]
    (hc : capped I T (power d) h X) :
    typeLT X ≤ (T * typeLT I) * power ((d+2)*h) := by
  induction h generalizing X with
  | zero => simpa [power] using (show typeLT X ≤ T * typeLT I from hc.trans hT)
  | succ h ih =>
    obtain ⟨key,hm,hn,hs⟩ := hc
    let B := T * typeLT I
    let H := B * power ((d+2)*h)
    let big : Set I := {i | T ≤ typeLT {x // key x = i}}
    have hlarge : ∀ i ∈ big, typeLT {x // key x = i} ≤ H := fun i _ => ih _ (hs i)
    have hsmall : ∀ i ∉ big, typeLT {x // key x = i} ≤ T := fun i hi => (lt_of_not_ge hi).le
    have hall := gapBound key hm T H big hsmall hlarge
    have hBH : B ≤ H := by
      have ho : (1 : Ordinal.{0}) ≤ power ((d+2)*h) := one_le_iff_pos.mpr (opow_pos _ omega0_pos)
      simpa only [mul_one] using mulMono ho B
    have hn' : typeLT big ≤ power d := hn
    calc
      _ ≤ (B+H) * (typeLT big + 1) := hall
      _ ≤ (H+H) * (power d + 1) := by grw [hBH,hn']
      _ = H * (2 * (power d + 1)) := by
        rw [← mul_assoc, Ordinal.mul_two]
      _ ≤ H * power (d+2) := mulMono (twoFactor d) H
      _ = B * power ((d+2)*(h+1)) := by
        dsimp only [H, power]
        simp only [mul_assoc, ← opow_add, Nat.mul_succ, Nat.cast_add, Nat.cast_ofNat]

theorem largeBlockRequired (I : Type) [LinearOrder I] [WellFoundedLT I]
    (hI : typeLT I = ω ^ (ω : Ordinal.{0})) (n d h : ℕ)
    (X : Type) [LinearOrder X] [WellFoundedLT X]
    (hX : ((ω : Ordinal.{0}) ^ ω) ^ (n+2) ≤ typeLT X) :
    ¬ capped I (((ω : Ordinal.{0}) ^ ω)^n) (power d) h X := by
  intro hc
  have pos : 0 < (typeLT I) := hI ▸ opow_pos _ omega0_pos
  have hb := cappedBound I _ (one_le_iff_pos.mpr (mul_pos (pow_pos (opow_pos _ omega0_pos) n) pos)) d h X hc
  rw [hI] at hb
  exact (hX.trans hb).not_gt (blockBound n d h)

end
end Larson.Branching

open Ordinal Order
namespace Larson.Words
noncomputable section

def Tuple (I : Type) : ℕ → Type
  | 0 => Unit
  | h+1 => I ×ₗ Tuple I h

instance tupleOrder (I : Type) [LinearOrder I] (h : ℕ) : LinearOrder (Tuple I h) :=
  Nat.rec (motive := fun k => LinearOrder (Tuple I k)) (inferInstanceAs (LinearOrder Unit))
    (fun n ih => @Prod.Lex.instLinearOrder I (Tuple I n) _ ih) h

instance tupleWF (I : Type) [LinearOrder I] [WellFoundedLT I] (h : ℕ) : WellFoundedLT (Tuple I h) :=
  Nat.rec (motive := fun k => WellFoundedLT (Tuple I k)) (inferInstanceAs (WellFoundedLT Unit))
    (fun n ih => by exact inferInstanceAs (WellFoundedLT (I ×ₗ Tuple I n))) h

theorem tupleType (I : Type) [LinearOrder I] [WellFoundedLT I] (h : ℕ) :
    typeLT (Tuple I h) = (typeLT I)^h := by
  induction h with
  | zero =>
    change type ((· < ·) : Unit → Unit → Prop) = _
    rw [type_fintype]
    simp
  | succ h ih =>
    change type (Prod.Lex ((· < ·) : I → I → Prop) ((· < ·) : Tuple I h → _ → Prop)) = _
    rw [type_prod_lex, pow_succ]
    exact congrArg (· * typeLT I) ih

abbrev Tower (I : Type) := Σₗ h : ℕ, Tuple I h

instance towerWF (I : Type) [LinearOrder I] [WellFoundedLT I] : WellFoundedLT (Tower I) := by
  let f (x : Tower I) : ℕ ×ₗ Ordinal.{0} := toLex (x.1,typein ((· < ·) : Tuple I x.1 → _ → Prop) x.2)
  constructor
  apply Subrelation.wf (r := InvImage (· < ·) f) _ (InvImage.wf _ wellFounded_lt)
  intro x y h
  cases h with
  | left a b hab => exact Prod.Lex.left _ _ hab
  | right a b hab => exact Prod.Lex.right _ ((typein_lt_typein _).mpr hab)

theorem towerType (I : Type) [LinearOrder I] [WellFoundedLT I] (hI : 2 ≤ typeLT I) :
    typeLT (Tower I) = (typeLT I) ^ (ω : Ordinal.{0}) := by
  let A := typeLT I
  have ha : 0 < A := lt_of_lt_of_le (by exact_mod_cast (show (0 : ℕ) < 2 by decide)) hI
  rw [← iSup_pow_natCast ha]
  apply le_antisymm
  · let r (x : Tower I) := A^x.1 + typein ((· < ·) : Tuple I x.1 → _ → Prop) x.2
    have room (x : Tower I) : r x < A^(x.1+1) := by
      have h := (typein_lt_type ((· < ·) : Tuple I x.1 → _ → Prop) x.2).trans_eq (tupleType I x.1)
      calc
        _ < A^x.1 + A^x.1 := (add_lt_add_iff_left _).mpr h
        _ = A^x.1 * 2 := (Ordinal.mul_two _).symm
        _ ≤ A^(x.1+1) := by rw [pow_succ]; exact (isNormal_mul_right (pow_pos ha _)).monotone hI
    have hm : StrictMono r := by
      intro x y h
      cases h with
      | left a b hab =>
        apply (room _).trans_le
        apply le_trans _ le_self_add
        exact pow_le_pow_right₀ (one_le_iff_pos.mpr ha) hab
      | right a b hab => exact (add_lt_add_iff_left _).mpr ((typein_lt_typein _).mpr hab)
    let B := ⨆ n : ℕ, A^n
    let f (x : Tower I) : B.ToType := ToType.mk ⟨r x,(room x).trans_le (Ordinal.le_iSup _ _)⟩
    have hf : StrictMono f := fun _ _ h => ToType.mk.strictMono (hm h)
    let e : ((· < ·) : Tower I → Tower I → Prop) ↪r ((· < ·) : B.ToType → _ → Prop) :=
      ⟨⟨f,hf.injective⟩,hf.lt_iff_lt⟩
    exact (type_le_iff'.mpr ⟨e⟩).trans_eq (type_toType _)
  · apply Ordinal.iSup_le
    intro n
    rw [← tupleType I n]
    let f (x : Tuple I n) : Tower I := ⟨n,x⟩
    have hf : StrictMono f := fun x y h => Sigma.Lex.right x y h
    exact type_le_iff'.mpr ⟨⟨⟨f,hf.injective⟩,hf.lt_iff_lt⟩⟩

abbrev Block := Tower ℕ
abbrev Word := Tower Block

theorem wordType : typeLT Word = ω ^ (ω ^ (2 : Ordinal.{0})) := by
  have hn : typeLT ℕ = ω := type_nat_lt
  have hB : typeLT Block = ω ^ ω := by
    rw [towerType ℕ (by rw [hn]; exact (natCast_lt_omega0 2).le), hn]
  have hb : 2 ≤ typeLT Block := by
    rw [hB]
    apply (natCast_lt_omega0 2).le.trans
    simpa only [opow_one] using (opow_le_opow_right omega0_pos (one_le_iff_pos.mpr omega0_pos))
  have he : (ω : Ordinal.{0}) ^ (2 : Ordinal) = ω * ω := (opow_natCast ω 2).trans (pow_two ω)
  rw [towerType Block hb, hB, ← opow_mul, he]

end
end Larson.Words

open Ordinal Order
namespace Larson.Words
open Ordinal Order Larson.Branching
noncomputable section

def Located (I : Type) [LinearOrder I] [WellFoundedLT I] (test : (I → Ordinal.{0}) → Prop) :
    (h : ℕ) → (X : Type) → [LinearOrder X] → [WellFoundedLT X] → (X → Tuple I h) → Prop
  | 0, _, _, _, _ => False
  | h+1, X, _, _, f =>
    let key (x : X) := (ofLex (f x)).1
    test (fun i => typeLT {x // key x = i}) ∨
      ∃ i, Located I test h {x // key x = i} (fun x => (ofLex (f x.val)).2)

abbrev hasSplit (I : Type) [LinearOrder I] [WellFoundedLT I] (T D : Ordinal.{0}) :=
  Located I (fun g => D < typeLT {i : I // T ≤ g i})

private theorem capOfNoSplit (I : Type) [LinearOrder I] [WellFoundedLT I]
    (T D : Ordinal.{0}) (h : ℕ) (X : Type) [LinearOrder X] [WellFoundedLT X]
    (f : X → Tuple I h) (hf : StrictMono f) (hn : ¬ hasSplit I T D h X f) :
    capped I T D h X := by
  induction h generalizing X with
  | zero =>
    have e : ((· < ·) : X → X → Prop) ↪r ((· < ·) : Tuple I 0 → _ → Prop) :=
      ⟨⟨f,hf.injective⟩,hf.lt_iff_lt⟩
    have hb := (type_le_iff'.mpr ⟨e⟩).trans_eq (tupleType I 0)
    change typeLT X ≤ 1
    simpa only [pow_zero] using hb
  | succ h ih =>
    let key (x : X) := (ofLex (f x)).1
    have hm : Monotone key := fun _ _ he => Prod.Lex.monotone_fst _ _ (hf.monotone he)
    have hno := not_or.mp hn
    refine ⟨key,hm,le_of_not_gt hno.1,fun i => ?_⟩
    let tail (x : {x // key x = i}) := (ofLex (f x.val)).2
    have htail : StrictMono tail := by
      intro x y hxy
      rcases Prod.Lex.lt_iff.mp (hf (show x.val < y.val from hxy)) with h | ⟨_,h⟩
      · change key x < key y at h
        rw [show key x = i from x.property,show key y = i from y.property] at h
        exact (lt_irrefl i h).elim
      · exact h
    exact ih _ tail htail (fun he => hno.2 ⟨i,he⟩)

end
noncomputable section

abbrev canDelay (T : Ordinal.{0}) :=
  Located ℕ (fun g => ∀ m, ∃ i ≥ m, T ≤ g i)

theorem delayInTuple (r h : ℕ) (X : Type) [LinearOrder X] [WellFoundedLT X]
    (f : X → Tuple ℕ h) (hf : StrictMono f) (hr : power (r+1) ≤ typeLT X) :
    canDelay (power r) h X f := by
  induction h generalizing X with
  | zero =>
    have e : ((· < ·) : X → X → Prop) ↪r ((· < ·) : Tuple ℕ 0 → _ → Prop) :=
      ⟨⟨f,hf.injective⟩,hf.lt_iff_lt⟩
    have hx := hr.trans ((type_le_iff'.mpr ⟨e⟩).trans_eq (tupleType ℕ 0))
    rw [pow_zero] at hx
    exact ((one_lt_opow.mpr ⟨one_lt_omega0, by exact_mod_cast (Nat.succ_ne_zero r)⟩).not_ge hx).elim
  | succ h ih =>
    let key (x : X) := (ofLex (f x)).1
    have hm : Monotone key := fun _ _ he => Prod.Lex.monotone_fst _ _ (hf.monotone he)
    by_cases hb : ∃ i, power (r+1) ≤ typeLT {x // key x = i}
    · obtain ⟨i,hi⟩ := hb
      apply Or.inr
      refine ⟨i,ih _ _ ?_ hi⟩
      intro x y hxy
      rcases Prod.Lex.lt_iff.mp (hf (show x.val < y.val from hxy)) with h | ⟨_,h⟩
      · change key x < key y at h
        rw [show key x = i from x.property,show key y = i from y.property] at h
        exact (lt_irrefl i h).elim
      · exact h
    · push Not at hb
      exact Or.inl (unboundedSections key hm _ _ (by exact_mod_cast Nat.lt_succ_self r) hr hb)

theorem chooseHeader (w : Set Block) (r : ℕ) (hw : power (r+1) ≤ typeLT w) :
    ∃ i, power r ≤ typeLT {b : w // b.val.1 = i} := by
  let key (b : w) := b.val.1
  have hm : Monotone key := by
    intro x y h
    rcases Sigma.Lex.le_def.mp (show x.val ≤ y.val from h) with h | ⟨h,_⟩
    · exact h.le
    · exact h.le
  by_contra! hn
  have hlt : (r : Ordinal.{0}) < ((r+1 : ℕ) : Ordinal) := by exact_mod_cast Nat.lt_succ_self r
  have hsmall (i : ℕ) : typeLT {b : w // key b = i} < power (r+1) :=
    (hn i).trans ((opow_lt_opow_iff_right one_lt_omega0).mpr hlt)
  obtain ⟨i,_,hi⟩ := unboundedSections key hm _ _ hlt hw hsmall 0
  exact (hn i).not_ge hi

end
def sliceTuple {I : Type} {w : Set (Tower I)} {m : ℕ}
    (x : {x : w // x.val.1 = m}) : Tuple I m := x.property ▸ x.val.val.2

theorem strictSlice {I : Type} [LinearOrder I] {w : Set (Tower I)} {m : ℕ} :
    StrictMono (sliceTuple (w := w) (m := m)) := by
  intro x y hh
  have h : x.val.val < y.val.val := hh
  obtain ⟨⟨⟨i,a⟩,ha⟩,hi⟩ := x
  obtain ⟨⟨⟨j,b⟩,hb⟩,hj⟩ := y
  change i = m at hi
  change j = m at hj
  subst i
  subst j
  have hl : Sigma.Lex (· < ·) (fun n => ((· < ·) : Tuple I n → _ → Prop))
      ⟨m,a⟩ ⟨m,b⟩ := h
  exact (Sigma.lex_iff.mp hl).elim (fun he => (lt_irrefl _ he).elim) (fun ⟨_,he⟩ => he)

theorem chooseRoot (w : Set Word) (N : ℕ) (hw : typeLT w = typeLT Word) :
    ∀ b, ∃ m ≥ b, ((ω : Ordinal.{0}) ^ ω)^N ≤ typeLT {x : w // x.val.1 = m} := by
  let key (x : w) := x.val.1
  have hm : Monotone key := by
    intro x y h
    rcases Sigma.Lex.le_def.mp (show x.val ≤ y.val from h) with h | ⟨h,_⟩
    · exact h.le
    · exact h.le
  have hB : typeLT Block = ω ^ (ω : Ordinal.{0}) := by
    rw [towerType ℕ (by rw [type_nat_lt]; exact (natCast_lt_omega0 2).le),type_nat_lt]
  have hfin (n : ℕ) : (ω : Ordinal.{0}) * n < ω ^ (2 : Ordinal) := by
    have he : (ω : Ordinal.{0}) ^ (2 : Ordinal) = ω*ω := (opow_natCast ω 2).trans (pow_two ω)
    rw [he]
    exact mul_lt_mul_of_pos_left (natCast_lt_omega0 n) omega0_pos
  have hn (n : ℕ) : ((ω : Ordinal.{0}) ^ ω)^n = ω ^ (ω * (n : Ordinal)) := by
    rw [opow_mul, opow_natCast]
  have hs (m : ℕ) : typeLT {x : w // key x = m} < ω ^ (ω ^ (2 : Ordinal)) := by
    let f := sliceTuple (w := w) (m := m)
    have hf : StrictMono f := strictSlice
    let e : ((· < ·) : {x : w // key x = m} → _ → Prop) ↪r
        ((· < ·) : Tuple Block m → _ → Prop) := ⟨⟨f,hf.injective⟩,hf.lt_iff_lt⟩
    have hu := (type_le_iff'.mpr ⟨e⟩).trans_eq (tupleType Block m)
    rw [hB,hn] at hu
    exact hu.trans_lt ((opow_lt_opow_iff_right one_lt_omega0).mpr (hfin m))
  rw [hn]
  exact unboundedSections key hm _ _ (hfin N) (hw.trans wordType).ge hs

noncomputable section

def tupleList {I : Type} : (h : ℕ) → Tuple I h → List I
  | 0, _ => []
  | n+1, t => (ofLex t).1 :: tupleList n (ofLex t).2

structure Domain where
  carrier : Type
  linear : LinearOrder carrier
  well : letI := linear; WellFoundedLT carrier

instance (d : Domain) : LinearOrder d.carrier := d.linear
instance (d : Domain) : WellFoundedLT d.carrier := d.well

structure Remainder (I X : Type) [LinearOrder I] where
  domain : Domain
  back : domain.carrier → X
  depth : ℕ
  digits : domain.carrier → Tuple I depth
  mono : StrictMono digits

theorem exposeNode {I X : Type} [LinearOrder I] [WellFoundedLT I]
    [LinearOrder X] [WellFoundedLT X] {h : ℕ} (f : X → Tuple I h)
    (hf : StrictMono f) (test : (I → Ordinal.{0}) → Prop) (hw : Located I test h X f) :
    ∃ pre : List I, ∃ g : I → Ordinal.{0}, test g ∧ ∀ i, ∃ r : Remainder I X,
      g i = typeLT r.domain.carrier ∧ ∀ y,
        tupleList h (f (r.back y)) = pre ++ i :: tupleList r.depth (r.digits y) := by
  induction h generalizing X with
  | zero => exact hw.elim
  | succ h ih =>
    let key (x : X) := (ofLex (f x)).1
    let tail (i : I) (x : {x // key x = i}) := (ofLex (f x.val)).2
    have hm (i : I) : StrictMono (tail i) := by
      intro x y hxy
      rcases Prod.Lex.lt_iff.mp (hf (show x.val < y.val from hxy)) with he | ⟨_,he⟩
      · change key x < key y at he
        rw [x.property,y.property] at he
        exact (lt_irrefl i he).elim
      · exact he
    rcases hw with good | ⟨i,sub⟩
    · refine ⟨[],_,good,fun i => ?_⟩
      let d : Domain := ⟨{x // key x = i}, inferInstance, inferInstance⟩
      refine ⟨⟨d,Subtype.val,h,tail i,hm i⟩,rfl,fun y => ?_⟩
      exact congrArg (· :: tupleList h (tail i y)) y.property
    · obtain ⟨pre,g,hg,hr⟩ := ih (tail i) (hm i) sub
      refine ⟨i :: pre,g,hg,fun j => ?_⟩
      obtain ⟨r,he,hr⟩ := hr j
      refine ⟨{ r with back := fun y => (r.back y).val },he,fun y => ?_⟩
      change key (r.back y) :: tupleList h (tail i (r.back y)) = i :: _
      rw [(r.back y).property,hr y]
      rfl

end
noncomputable section

abbrev Token := ℕ × Bool
abbrev Language := List Token → Prop

def shift (L : Language) (s : List Token) : Language := fun t => L (s ++ t)
private theorem shiftAppend (L : Language) (a b : List Token) :
    shift (shift L a) b = shift L (a ++ b) := by ext s; simp [shift,List.append_assoc]

def blanks (v : List ℕ) : List Token := v.map fun n => (n,false)
def marked (s : List Token) := s.any Prod.snd

private theorem marksBlanks (v : List ℕ) : marked (blanks v) = false := by
  induction v with
  | nil => rfl
  | cons n v _ => simp [marked,blanks]

def Ready : List Bool → Language → Prop
  | [], L => L []
  | b :: bs, L => ∀ bound : ℕ, ∃ i ≥ bound, ∃ m : Bool, ∃ s : List Token,
      (bs.isEmpty || marked ((i,m)::s)) = b ∧ Ready bs (shift L ((i,m)::s))

def script : ℕ → List Bool → List Bool
  | 0, bs => true :: bs
  | k+1, bs => false :: script k bs

private theorem nonemptyScript (k : ℕ) (bs : List Bool) : (script k bs).isEmpty = false := by
  cases k <;> rfl

def EndPlan (bs : List Bool) (L : Language) : Prop :=
  ∃ s : List Token, (bs.isEmpty || marked s) = true ∧ Ready bs (shift L s)

theorem leafPlan (k h : ℕ) (X : Type) [LinearOrder X] [WellFoundedLT X]
    (f : X → Tuple ℕ h) (hf : StrictMono f) (hr : power (k+1) ≤ typeLT X)
    (L : Language) (bs : List Bool)
    (cont : ∀ x, EndPlan bs (shift L (blanks (tupleList h (f x))))) :
    ∃ pre : List ℕ, Ready (script k bs) (shift L (blanks pre)) := by
  induction k generalizing X h L with
  | zero =>
    obtain ⟨pre,g,hg,hrg⟩ := exposeNode f hf _ (delayInTuple 0 h X f hf hr)
    refine ⟨pre,fun b => ?_⟩
    obtain ⟨i,hbi,hi⟩ := hg b
    obtain ⟨r,he,hr⟩ := hrg i
    rw [he] at hi
    have hn : Nonempty r.domain.carrier := type_ne_zero_iff_nonempty.mp
      ((opow_pos _ omega0_pos).trans_le hi).ne'
    obtain ⟨y⟩ := hn
    obtain ⟨s,hs,hc⟩ := cont (r.back y)
    rw [hr y] at hc
    let v := tupleList r.depth (r.digits y)
    refine ⟨i,hbi,false,blanks v ++ s,?_,?_⟩
    · simpa only [marked, List.any_cons, Bool.false_or, List.any_append,
        show (blanks v).any Prod.snd = false from marksBlanks v] using hs
    · simpa [shiftAppend,blanks,List.append_assoc,v] using hc
  | succ k ih =>
    obtain ⟨pre,g,hg,hrg⟩ := exposeNode f hf _ (delayInTuple (k+1) h X f hf hr)
    refine ⟨pre,fun b => ?_⟩
    obtain ⟨i,hbi,hi⟩ := hg b
    obtain ⟨r,he,hj⟩ := hrg i
    let base := blanks pre ++ [(i,false)]
    have hc (y : r.domain.carrier) :
        EndPlan bs (shift (shift L base) (blanks (tupleList r.depth (r.digits y)))) := by
      have hc' := cont (r.back y)
      rw [hj y] at hc'
      simpa [base,shiftAppend,blanks,List.append_assoc] using hc'
    obtain ⟨v,hv⟩ := ih _ _ r.digits r.mono (hi.trans_eq he) (shift L base) hc
    refine ⟨i,hbi,false,blanks v,?_,?_⟩
    · simp only [nonemptyScript,Bool.false_or,marked,List.any_cons]
      exact marksBlanks v
    · simpa [base,shiftAppend,List.append_assoc] using hv

end
noncomputable section

def blockTokens (b : Block) : List Token :=
  (b.1,true) :: blanks (tupleList b.1 b.2)

def spell (s : List Block) : List Token := s.flatMap blockTokens

def wordTokens (w : Word) : List Token := (w.1,true) :: spell (tupleList w.1 w.2)

private theorem headerTokens {v : Set Block} {j : ℕ} (x : {x : v // x.val.1 = j}) :
    blockTokens x.val.val = (j,true) :: blanks (tupleList j (sliceTuple x)) := by
  obtain ⟨⟨⟨b,a⟩,ha⟩,hb⟩ := x
  change b = j at hb
  subst j
  rfl

theorem buildBlocks (counts : List ℕ) (h : ℕ) (X : Type) [LinearOrder X] [WellFoundedLT X]
    (f : X → Tuple Block h) (hf : StrictMono f) (L : Language)
    (hr : ((ω : Ordinal.{0}) ^ ω)^(2*counts.length+1) ≤ typeLT X)
    (hw : ∀ x, L (spell (tupleList h (f x)))) :
    EndPlan (counts.foldr script []) L := by
  induction counts generalizing X h L with
  | nil =>
    obtain ⟨x⟩ : Nonempty X := type_ne_zero_iff_nonempty.mp
      ((pow_pos (opow_pos _ omega0_pos) _).trans_le hr).ne'
    exact ⟨_,rfl,by simpa [Ready,shift] using hw x⟩
  | cons k ks ih =>
    let n := 2*ks.length+1
    let T := ((ω : Ordinal.{0}) ^ ω)^n
    let after := ks.foldr script []
    have hB : typeLT Block = ω ^ (ω : Ordinal.{0}) := by
      rw [towerType ℕ (by rw [type_nat_lt]; exact (natCast_lt_omega0 2).le),type_nat_lt]
    have hsplit : hasSplit Block T (power (k+2)) h X f := by
      by_contra hn
      have eqn : n+2 = 2*(k::ks).length+1 := by simp [n]; omega
      apply largeBlockRequired Block hB n (k+2) h X (by rwa [eqn])
      exact capOfNoSplit Block _ _ h X f hf hn
    obtain ⟨pre,g,hg,hrg⟩ := exposeNode f hf _ hsplit
    let v : Set Block := {i | T ≤ g i}
    obtain ⟨j,hj⟩ := chooseHeader v (k+1) (le_of_lt hg)
    let Y := {y : v // y.val.1 = j}
    let start := spell pre ++ [(j,true)]
    have cont (y : Y) : EndPlan after
        (shift (shift L start) (blanks (tupleList j (sliceTuple y)))) := by
      obtain ⟨r,he,hr⟩ := hrg y.val.val
      apply ih r.depth r.domain.carrier r.digits r.mono _ (y.val.property.trans_eq he)
      intro z
      have hc := hw (r.back z)
      rw [hr z] at hc
      simp only [spell, List.flatMap_append,List.flatMap_cons,headerTokens y] at hc
      simpa [shift,start,spell,List.append_assoc] using hc
    obtain ⟨early,good⟩ := leafPlan k j Y sliceTuple strictSlice hj (shift L start) after cont
    refine ⟨start ++ blanks early,?_,?_⟩
    · simp [marked,start]
    · simpa [shiftAppend] using good

theorem rootPlan (w : Set Word) (hw : typeLT w = typeLT Word) (counts : List ℕ) :
    Ready (true :: counts.foldr script []) (fun s => ∃ x ∈ w, wordTokens x = s) := by
  intro b
  obtain ⟨m,hbm,hm⟩ := chooseRoot w (2*counts.length+1) hw b
  let X := {x : w // x.val.1 = m}
  let L : Language := fun s => ∃ x ∈ w, wordTokens x = (m,true) :: s
  have hc (x : X) : L (spell (tupleList m (sliceTuple x))) := by
    refine ⟨x.val.val,x.val.property,?_⟩
    obtain ⟨⟨⟨j,a⟩,ha⟩,hj⟩ := x
    change j = m at hj
    subst m
    rfl
  obtain ⟨s,_,hit⟩ := buildBlocks counts m X sliceTuple strictSlice L hm hc
  exact ⟨m,hbm,true,s,by simp [marked],hit⟩

end
end Larson.Words

namespace Larson.Pattern

abbrev Event := ℕ × Bool
abbrev PairState := ℕ × ℕ × ℕ

def heavy (r : ℕ) : Bool := r == 0 || r == 1 || r == 4 || r == 6 || r == 9 || r == 10

def consume (s : ℕ) (right mark : Bool) : ℕ :=
  if s = 31 then 31
  else if s = 0 then if right then 31 else 1 + mark.toNat
  else
    let r := (s - 1) / 2
    let b := (s - 1) % 2
    if r % 2 == right.toNat then
      if mark && !heavy r then 31 else 1 + 2*r + max b mark.toNat
    else if b != (heavy r).toNat || r == 10 || (mark && !heavy (r+1)) then 31
    else 1 + 2*(r+1) + mark.toNat

def advance (i j s : ℕ) (a : Event) : ℕ :=
  if a.1 = i then consume s false a.2 else if a.1 = j then consume s true a.2 else s

def accepts (i j : ℕ) : List Event → ℕ → Bool
  | [], s => s == 22
  | a :: w, s => accepts i j w (advance i j s a)

private theorem sink (w : List Event) (i j : ℕ) : accepts i j w 31 = false := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa [accepts, advance, consume, ite_self] using ih

def meets (c : List PairState) (f : ℕ → ℕ) (w : List Event) : Prop :=
  ∀ p ∈ c, accepts (f p.1) (f p.2.1) w p.2.2 = true

def update (a : Event) (p : PairState) : PairState :=
  (p.1, p.2.1, advance p.1 p.2.1 p.2.2 a)

def relabel (f : ℕ → ℕ) (p : PairState) : PairState := (f p.1, f p.2.1, p.2.2)

private theorem stepMeets {c f a w} (h : meets c f (a :: w)) {b : Event}
    (hb : a.2 = b.2)
    (hs : ∀ p ∈ c, (a.1 = f p.1 ↔ b.1 = p.1) ∧ (a.1 = f p.2.1 ↔ b.1 = p.2.1)) :
    meets (c.map (update b)) f w := by
  rintro _ hp
  obtain ⟨p,hpc,rfl⟩ := List.mem_map.mp hp
  simpa only [accepts, update, advance, hb, (hs p hpc).1, (hs p hpc).2] using h p hpc

private theorem subsetMeets {c d f w} (h : meets c f w) (g : ℕ → ℕ)
    (hs : ∀ p ∈ d, relabel g p ∈ c) : meets d (f ∘ g) w :=
  fun p hp => h _ (hs p hp)

structure Entry where
  clause : List PairState
  hint : ℕ → ℕ

def embed (mask i : ℕ) : ℕ :=
  ((List.range 5).filter (fun k => mask.testBit k))[i]?.getD (i + 5)

def decodeMap (h i : ℕ) := if h % 32 = 31 then i else embed (h % 32) i

def checkMove (db : ℕ → Entry) (e : Entry) (a : Event) : Bool :=
  let c := e.clause.map (update a)
  let h := e.hint (2*a.1 + a.2.toNat)
  if h = 0 then (c == e.clause) || c.any (fun p => p.2.2 == 31)
  else ((db (h / 32)).clause).all fun p => c.contains (relabel (decodeMap h) p)

def checkRow (db : ℕ → Entry) (i : ℕ) : Bool :=
  let e := db i
  e.clause.all (fun p => p.1 < 5 && p.2.1 < 5) &&
  e.clause.any (fun p => p.2.2 != 22) &&
  (List.range 5).all (fun k => checkMove db e (k,false) && checkMove db e (k,true))

private theorem embed_inj (mask : ℕ) : Function.Injective (embed mask) := by
  let l := (List.range 5).filter (fun k => mask.testBit k)
  have hn : l.Nodup := List.nodup_range.filter _
  have hl (i : ℕ) (hi : i < l.length) : l[i] < 5 :=
    List.mem_range.mp (List.mem_filter.mp (List.getElem_mem hi)).1
  intro i j h
  change l[i]?.getD (i+5) = l[j]?.getD (j+5) at h
  by_cases hi : i < l.length <;> by_cases hj : j < l.length
  · simp only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.getD_some] at h
    exact (List.Nodup.getElem_inj_iff hn).mp h
  · simp only [List.getElem?_eq_getElem hi, List.getElem?_eq_none (by omega : l.length ≤ j),
      Option.getD_some, Option.getD_none] at h
    have := hl i hi
    omega
  · simp only [List.getElem?_eq_getElem hj, List.getElem?_eq_none (by omega : l.length ≤ i),
      Option.getD_some, Option.getD_none] at h
    have := hl j hj
    omega
  · simp [List.getElem?_eq_none (by omega : l.length ≤ i), List.getElem?_eq_none (by omega : l.length ≤ j)] at h
    exact h

private theorem decode_inj (h : ℕ) : Function.Injective (decodeMap h) := by
  intro i j hij
  by_cases he : h % 32 = 31
  · simpa [decodeMap, he] using hij
  · exact embed_inj _ (by simpa [decodeMap, he] using hij)

theorem checkedRejects (db : ℕ → Entry) (ok : ∀ i, checkRow db i)
    (w : List Event) (i : ℕ) (f : ℕ → ℕ) (hf : Function.Injective f) :
    ¬ meets (db i).clause f w := by
  induction w generalizing i f with
  | nil =>
    intro h
    have hbad := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (ok i)).1).2
    obtain ⟨p,hp,hs⟩ := List.any_eq_true.mp hbad
    exact (bne_iff_ne.mp hs) (beq_iff_eq.mp (h p hp))
  | cons a w ih =>
    intro h
    obtain ⟨⟨hr,_⟩,hm⟩ := (Bool.and_eq_true_iff.mp (ok i)).imp_left Bool.and_eq_true_iff.mp
    have hr' := List.all_eq_true.mp hr
    by_cases ha : ∃ k < 5, a.1 = f k
    · obtain ⟨k,hk,he⟩ := ha
      let b : Event := (k,a.2)
      have hu := stepMeets h (b := b) rfl (fun p _ => by
        simp only [he, b, hf.eq_iff, and_self])
      have hm' := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hm k (List.mem_range.mpr hk))
      have hc : checkMove db (db i) b := by cases hz : a.2 <;> simp [b, hz, hm'.1, hm'.2]
      unfold checkMove at hc
      dsimp only at hc
      split at hc
      · rcases Bool.or_eq_true_iff.mp hc with hc | hc
        · rw [beq_iff_eq.mp hc] at hu
          exact ih i f hf hu
        obtain ⟨p,hp,hp'⟩ := List.any_eq_true.mp hc
        have hh := hu p hp
        rw [beq_iff_eq.mp hp', sink] at hh
        contradiction
      · apply ih _ _ (hf.comp (decode_inj _))
        apply subsetMeets hu
        intro p hp
        exact List.contains_iff_mem.mp (List.all_eq_true.mp hc p hp)
    · apply ih i f hf
      intro p hp
      have hh := h p hp
      obtain ⟨hi,hj⟩ := Bool.and_eq_true_iff.mp (hr' p hp)
      simpa only [accepts, advance, if_neg (fun he => ha ⟨_, of_decide_eq_true hi, he⟩),
        if_neg (fun he => ha ⟨_, of_decide_eq_true hj, he⟩)] using hh

private def part0 (i : ℕ) : ℕ :=
  if i < 64 then
    if i < 32 then
      if i < 16 then
        (0x21f0048fb0000000000000ff820475800000000000077c02236c000000003be037e01917600000000000019f0408ab0000000000000bf80444d8000000005fc057c0321ec00000000000027e0810b600000000000011f00484b00000000000007f84031d8000000003fc037c3010ac00005be057e017e19085537f035f00bf009f0cc42a000067f866f803f870214f67c35fc01fc017c3c10a2000217e213e007e18884f >>> (85*(i % 16))) % 2^85
      else
        (0x83e011d3583e07fe019cf500007be0814b59fe077e08949473e05fe02909400006fe100c7400002fe0111352fe067e0190f5000063e0810b500005fe00909500005be100c7500000000012d6000053e0112b653e04fe01929600004be1012764be047e181236 >>> (52*(i % 16))) % 2^52
    else
      if i < 48 then
        (0xc3e082d5600000000bfe012d350000bfe0bbe01acf500000000b7e0828b50000dbe0b3e08a894000000000000024b50000afe0abe04a494000000007be081cb5afe0a7e0a3e069c9400000000000001e76000000009be081e360000000097e009df60000000093e081dd6000000008fe011db600008fe08be019d760000000087e081d56 >>> (68*(i % 16))) % 2^68
      else
        (0x107e103e01bd7600000000ffe083d5600000000fbe013d350000fbe0f7e01bcf500000000f3e0838b5000117e0efe08b894000000000000034b50000ebe0e7e04b49400000000b7e082cb5ebe0e3e0dfe06ac9400000000000002e7600000000d7e082e3600000000d3e00adf600000000cfe082dd600000000cbe012db60000cbe0c7e01ad76 >>> (68*(i % 16))) % 2^68
  else
    if i < 96 then
      if i < 80 then
        (0xa1f0066fb000000004ff82137580000000277c029b6c00013be137e01cd760000000099f0426ab000000004bf80534d400025fc257c0399ea0000000127e0844b5aff0abf091f0c624a000000003cf820f2d400023fc237c05792800000000000003e760000000089f041f1b0000000043f802f7d80000000217c107bac0000000107e013db6 >>> (69*(i % 16))) % 2^69
      else
        (0xc1f0068fb000000005ff821475800000002f7c02a36c00017be177e01d17600000000b9f0428ab000000005bf80544d40002dfc2d7c03a1ea0000000167e0850b5c9f0c5f0b1f03684a0000000049f82132d40002bfc2b7c219928000000000000052d600000000a9f00a95b000054f853f8074a580000000297c209cec00014be147e184e36 >>> (69*(i % 16))) % 2^69
    else
      if i < 112 then
        (0x71f870f81873cc0001bfe0814b380f86ef82842c5a3e1b7e02909100006cf84031c40000afe0424932bf86af818724c0001a7e081493000068f808424c00019fe100c73000000000162d4000197e00d894000000000152d593e18fe04d494000052f84149d94be187e185236 >>> (54*(i % 16))) % 2^54
      else
        (0x97f095f00e67a0000000000004cf8211558000000000003f7c028a6a0001ffe1fbe1f7e09c4f40000f9f07df07bf01de7a0000000000003ff820e558000000000003d7c02726a0001efe1ebe1e7e09b8f4000000000000000001aab00000000000077f804d4d40003c7c3bfc3b7c0b69e9e3e1d7e0bfe0bbe07acf400000000000061f0414ab00000000000073f804a4d40003a7c39fc397c1351e8000000000001c7e0424f3 >>> (85*(i % 16))) % 2^85

private def part8 (i : ℕ) : ℕ :=
  if i < 192 then
    if i < 160 then
      if i < 144 then
        (0x74f82cf822a2d0000000023fe0424b388f88ff88ef83872c4000243e237e029c8f000073f872f806a4d0000000022fe04253300008bf88af81874c5c7e1c3e227e069cf1000088f86ef82852c4000233e21fe08948f000086f86df80a423c0000000217e100c6f000000006ff82053cc000000000000015330000000082f80844c400020fe207e0290f1 >>> (70*(i % 16))) % 2^70
      else
        (0x32f8a0f806b5d400027fe1cfe092955a1f873f89ef826a5500000000277e04255300009df89cf8189544000000026fe00a54f000000009af80895380000000267e01254d000099f898f806952c0002bfe25fe0a1d4a0000000096f80474a400025be257e019ce90000000094f82052a400035fe24fe0894a700008ff88ef81892c40000000247e00a48f >>> (70*(i % 16))) % 2^70
    else
      if i < 176 then
        (0xd6f8b1f8b0f80e75a80000000000013be014db5000000004ef8aef80735d00000000000013fe0845d6000000000000acf80516d40002b7e2b3e2afe09c57400000000000041f804f6d40002abe107e2a7e03bd7400000000000042f820e7580000000000029fe0139b50000a8f8a7f8a6f826e5d00000000000000000035d6000000000000a4f804d6d4000297e293e28fe05b574a5f8a2f832f8a0f81eb5d0000000000000cbe012db5 >>> (86*(i % 16))) % 2^86
      else
        (0xc1f8c0f812d7d307e2ffe2f3e06adf400000000000000b9d400000002f7e082e3500000000bcf802b7d400000000cfe0829d60000bbf8baf824a756fbe2ebe2e7e09a9d400000000b8f810974c0002e3e2dfe0625d100000000b6f802973c00000002d7e0225ce00000000b4f80497340002d3e2cfe01a5cb0000cdf8b2f8287728000353e2c7e031daa >>> (70*(i % 16))) % 2^70
  else
    if i < 224 then
      if i < 208 then
        (0xd0f80298af47e33fe0a1e2ad3f8cef80a77ab27e323e184e350000ccf80337d0000153e0152b554f8caf8074a54000327e104e75c9f8c8f86118d72fe31fe08c5f40000c3f820f8d71be317e02bdf40000000000f9d400030fe083a35c4f8c2f822e7d00000000003635 >>> (54*(i % 16))) % 2^54
      else
        (0xe0f893f822521c00022fe22be06253100000000def80293bc000377e227e029cef0000dcf887f82252bc000000025fe02254a00000000daf80494a400036be367e01a4e7d8f896f895f80e739c0002d3e357e01a56b00000000b4f80496b40002d3e357e01a5ab00000000d0f80297ac0000000000000266b00000000d2f80879a80000000000000262d >>> (70*(i % 16))) % 2^70
    else
      if i < 240 then
        (0xf0f8ecf80a75bc0002ebe3abe01a9b400000000eef81096cc0003bbe3b7e061db1e9f8e8f8ecf81a75c400000002ebe0129b5a1f8baf8eaf826a5d000000003a7e0425730000e9f8e8f81875cc000000039fe0815530000ebf8e6f82855440003bfe397e08954f0000000000000092a4000000038fe00a4870000000094f82072a400038be387e029c87 >>> (70*(i % 16))) % 2^70
      else
        (0x100f8fdf8225a3c000000000000016b300000000fef8085ac400000003f7e0096af000000000000005b4c00000003efe0216d100000000faf8025b3c00000003e7e0212ce0000fcf8f8f80c4abbffe3e3e3dfe03928e0000000000000099bc00000003d7e021e6f00000000f4f82059bc0003dbe3cfe12126e0000eef8edf81896c400000003c7e00a56f >>> (70*(i % 16))) % 2^70

private def part16 (i : ℕ) : ℕ :=
  if i < 320 then
    if i < 288 then
      if i < 272 then
        (0x95fc887c0523d4dcf90df82253bc000105f010a988000437e00952f77fc84fc112ade000000000056cc000215f010ad88000427e0095af81fc817c0c4d62000107f8029a3c000000000156b0000417e012ab582fc827c035568000103f8109ace07f205f030f58c1be407e029e8f >>> (55*(i % 16))) % 2^55
      else
        (0x907c8e7c8f7c132d16000000011cf8045ab4000239f23df00cb55800000003e7e0216ce000000008e7c022d9a00011cf91bf8065b2c0000000235f0109650000477e467e0312aa8ffc8cfc8c7c0725140000000114f82059ac00022ff22df0909350000000034be021e6b000000000000003cda0000000113f82058b4000229f225f044b15c5fe457e447e1a122a >>> (71*(i % 16))) % 2^71
    else
      if i < 304 then
        (0x98fc987c0c3be6000000012ff820574c0000000227f040f16800034fe4b7e029deb0000967c897c112bd60000000123f8089b380000000255f00935680004abe4a7e01a68b0000000082fc0255aa000105f927f806ab50000000024df021369800049be497e0626d100000000927c014d9e0000000123f8087b380000000245f008f56ca3e48be487e039e8b >>> (71*(i % 16))) % 2^71
      else
        (0xa1fca07c21990800013df80892940001c7f005253ce7e4f7e0a1ca56d7c6cfc034a4e00013bf8087495b1f275f014e72ce7e24be0a14a500004cfc024a5a99f937f80693ac000000000125680004d7e00a48b000078fc014b5e0000bdf820a8d57df265f0454fa00004c7e0425f3 >>> (55*(i % 16))) % 2^55
  else
    if i < 352 then
      if i < 336 then
        (0xa87c01aa9e000000014ff8095538000000029df00aaa6800053be537e01d54b00000000a67c04aa94000000014bf80554a4000297f295f00ea9380000000527e0251250000aafca47c05a1ca0000000000000152a4000000028df006a53800051fe517e0a50a5ac7cab7ca27c0da1080000000000000134940000000285f00667280000000507e084ca5 >>> (71*(i % 16))) % 2^71
      else
        (0xc1fcb07c11514f87f95ff828a29400025bf004ef680003d7e021e6e0000000000b15200015bf803629c0002b5f012c528000567e00d8840000a2fc04a94b58f957f813521297f295f00ea73800000000059560000aa7c02b2ab54f953f80765500002a5f022aa9d4be547e065551 >>> (55*(i % 16))) % 2^55
    else
      if i < 368 then
        (0xbcfcb87c145b94000180f96ff80cb6ab05f2dff2ddf01d6b50000107e2a7e01bd750000b67c3d7c1272aaa8f87af96bf826e55000000002d5f021aa980005abe5a7e06355100000000b47c016a9e0000000167f808d53800000002cdf009aa6800059be597e01b54b0000b6fcb27c145a940000000163f804b4a40002c7f2c5f00d67480000000587e0828a9 >>> (71*(i % 16))) % 2^71
      else
        (0x17cf802d7ac0000000000000366b000000017ef808b9a80000000000000362d000000017cf802d8ac0005f7e5efe0a2e2a00017ff97af80ab7a80000000317e00bdf5000178f8a7f824e75713e29fe5dfe09b9d40000000176f810d74c0005dbe5d7e0635d10000000174f802d73c00000005cfe0235ce0000000172f804d7340005cbe5c7e01b5cb >>> (70*(i % 16))) % 2^70

private def part24 (i : ℕ) : ℕ :=
  if i < 448 then
    if i < 416 then
      if i < 400 then
        (0xc97cc87c148aa2000194f98ff823153c0000000317f011a528000000000000034a900000000c67c01694e000187f98bf828b29400030df30bf00da9380000000627e022d250000c27cc47c0559ca0000000164f808d528000000030df009a94800061be617e01b4e7c27cb1fcb17c0759ce000172f981f806d5ac00000002e5f009ad680005cbe607e01b5ab >>> (71*(i % 16))) % 2^71
      else
        (0xd6fcd67c002cd07cc6108e26bb65f363f000b341f33ff31c423896e0000da7cd9fccf7c002cd4108a253800038df38bf379f33bf348422894de77ce6fce57ccefcce7cd3108a252c0003d7f3d5f15e7337f350422894a00000001057d04fccd7cc2108a24a400041ff41df335f333f30c42289270000000108fd087ccc7cc41088249400043bf439f433f32ff31442208e500010ffd0f7ccb7c491cd410882294000000000000000000064fe00cd6f0000000000000000000000000136c4000000000000000000064fe00cd710000000000000000000000000135cc0000000000000000000647e084553 >>> (118*(i % 16))) % 2^118
    else
      if i < 432 then
        (0x872cd37cd87c07210e76b8000000035ff1b6b11084395ae00000000432cd77c05210e46b80000000000035bf2006338dae7b3479346fb85a9cd4210f17380001bee16a7357f054843bdce0000d57c6fb85a9c54210ee7380001bee210b353f058843b5ce6fb885acd4fcd47c17210eb73800034ff1bee1c8b150843a9ce00006fb8862cd37c16210e9739bee21cb34df34bf05c8439dce0000d27c6fb86dac54210e57380001bee10cb347f05484391ce000000000000d17c8018ce373b45f343f000d000b35042389ce >>> (102*(i % 16))) % 2^102
      else
        (0xe07c01210e46b40000000000037ff2006338dad0000dffcdf7cd07cc2108e26b789f387f341f37bf30c423896d000087b46fb8721c54210ae5380001bee210b377f058842b54e6fb885acddfcdd7c17210ab538000373f1bee1c8b150842a94e00006fb8862cdc7c16210a9539bee21cb371f36ff05c8429d4e0000db7c6fb86dac54210a55380001bee10cb36bf054842914e000000000000da7c8018ca35380001bee10cb35df054843916e000000000000d97c8018ce35b80000000218b34df018843a5ae >>> (102*(i % 16))) % 2^102
  else
    if i < 480 then
      if i < 464 then
        (0xf2fc4938e87c51214a452c00000001bee39ff38ff054842914b0000000000000000e77c8018ca352c00000001bee1ac7381f054843916b0000000000000000e67c8018ce35af99f397f1ac7341f37bf31c423896b0000000000006fb8dc7c12210a953400000001bee371f393f04c8429d4d000000000000e47c6fb850210a5534000000000001bee38ff044842914d0000000000000000e37c8018ca3534000000000001bee381f044843916d0000000000000000e27c8018ce35b400000000000000034df008843a5ad000000000000d37ce17c03210e76b4000000000000000383f10084395ad >>> (118*(i % 16))) % 2^118
      else
        (0x99acee7cf07c0729ced5b80001aee25cd16ab150a73ba2e00006bb85aacef7c4529cee7b80001aee3bbf16ab150a73b9ce00006bb85aacee7c4629cee6b9aee16ab3b9f3b7f11ca73b96e000087b4ed7c5aac5421cae5380003bff266b3b3f058872b54ef0fc782cecfcec7c1721cab5380001aee1c8d134b150a73a9ce00006bb84d2ceb7c4629cea6b9aee134b3adf3abf11ca73a96e0000ebfcea7c4d2c5421caa53800000003c5f3a7f048872a54d0000f27ce9fce97c1321ca753400000003a3f124e140852954d >>> (102*(i % 16))) % 2^102
    else
      if i < 496 then
        (0x6bb89b2ceb7cf1fc4729ce75afdff26cb3a7f3a5f05c8729d4b0000f77c4938e87c51214a552c0003e1f1bee3dbf150842954a00006fb8e7fcf67c15210a4528000000000003d7f2006328d4a00006bb89a2cf47c4529ce45ac000000000001aee100a7395ad000000006bb8f47c4129ce55b400000003a3f3cff140872954d0000f4fc9a2cf37c1521ca452c0001aee3adf3c7f10ca739d6d000000000000eb7c0229ce96b400000003adf3c7f00ca73a56d6bb8782cee7cf07c4729ceb5b80000000266b3b9f018a73b5ae >>> (102*(i % 16))) % 2^102
      else
        (0x87b46fb9007c54210ae5280001bee407f3fff058842b54a6fb902fcfffcff7c17210ab529aee1acb3b9f3f3f11ca73ad6bfe7c6b2cecfcfbfc1721cab52c0001aee3b9f3f3f10ca73ad6d000000000000ee7c0229ced6b400000003b9f3f3f00ca73b56d00000000fc7cecfc1221cad5340003f5f3b3f3eff04c872ad4d0000ebfc4938722c54214aa5380003edf124e3ebf148852a94dfdfc4938fafcfa7c53214aa52c0003fbf1bee3e7f150842a94a00006fb9037cf97c16210a9529bee411f3e5f3e3f05c8429d4a >>> (102*(i % 16))) % 2^102

private def part32 (i : ℕ) : ℕ :=
  if i < 576 then
    if i < 544 then
      if i < 528 then
        (0x6fad05fc05210a449c0000000000041ff2006328d27000000000000f97c02210a94a400000003e5f41bf00c8429d29000000000001067c40210a54a400000000000417f0048429129000000000001057c8018ca34a7ddf124e3ebf40ff14c8529d4b000000004938fafc12214a9534000124e3ebf40ff04c852a54bfdfc4939017d027c53214ab52c0000000124e405f048852b54d00004939017d027c13214ad52c00021ed124e1c87150852b94e000087b44939017c52214ae5361ed124e405f403f14c852b94b >>> (102*(i % 16))) % 2^102
      else
        (0x37da37d6883e0a9084214a00000000000000010ffc8018c8329400000000df68df5a12f82a4210872800000000000000043bf2006320ce50000000037dc37d682fe0a908521ce00000000000000010dfc8018ca339e1bfa1af8d7399af999f9a62114473800000001aeb42ff42df10c8529d27000000002bd6249c7cfe2a10a5529400000000000000010bfc02214a94a400000000000217fa16f8064295293800000000000000042bf0108422525000000000000863e853e0290843a4a00000000000109fc492c4421085494000000000000df5a12f80a42108928000000000000000423f2006320d25 >>> (119*(i % 16))) % 2^119
    else
      if i < 560 then
        (0x3c1c8c7e8c3e4f1a0e9d6e2108000117fc72389c34512a9c4210000237fa2ef93868925534842473f45df45bf270d134aa5908400002bdc8b3e4e1a28954a21080000000115fc9c34092a52421000022bfa2af938681a549c84200000000453f27cb044892908400008ebe8a3e4f160a90e52108000113fc49389c2c51214a42100000d769387224f88a5210e72800000000000270e010a422525000000004e1c893e02948449ca0000000111fc491c1421089294000225f8923a22f82a4210e528000443f124d124b15084214a5 >>> (103*(i % 16))) % 2^103
      else
        (0x1207c9e391f7c153908f7b9e4b1ec71e47278e1d0e42462e98b498349e391f7c353908f8b800047bf25cd270e150a423a2e00011ffc9c391e7c452908e7b9aee457f455f270d134a7390846b3918fd1c7c9e341d3ad642100000000463f278d024ed69084000118fd1c7c9e340d3ada4210000000046bf27cd0152f790840000a19c9f9c9f34314c624210000000046bf27cd01531790840000ae391a7c9e34513c5c421000046df467f278d054ef710840001197c5ab89e34513b9c4210000266e463f278d064ed71084 >>> (102*(i % 16))) % 2^102
  else
    if i < 608 then
      if i < 592 then
        (0x250f8b5693c70a87211ce7000099b49e3927fc163908d73bc1a4f1c93fe93be0b9c845b9c00049bf134d278e150e4229ce000000013c724cf80c72112d700009e39267d25fc07390876b8000000092be4e1c2214842b5c0004a7f270e493f114a42116e00023ff9387246f88a5211ef70000792c791c9c3854290918b80003d1a4e1c91be2294848bdc0001e4d124e25c7150852c5d10000f268927244f8a242962e7fb34793522fd21fcd4210917380003d8e3c8e4f9c1a24848c5c000000027ce483f0152423dee >>> (101*(i % 16))) % 2^101
      else
        (0x937e391a4e1c2a1484539c0001307c9c392ffc462908a6ba62f938725ffa5ef88e52114b700004c7f4bbf1c8b150842294e00009b3e4316973e0b10844a9d377c872d2e7d2dfc172108753936693c724cfa4bf82e7210eb700004b3f270e493f114a42156e000096be963e36d62a10842a9c0001247c432d2bfc152108453800000000000256f90031906a700000000495f278e110e4215ae00004d1a4f1c953e0a9c8422dc000000009f3920fc05490917b800015c6a52f93c70a872122e70000481f278e4a3f054e423dce >>> (103*(i % 16))) % 2^103
    else
      if i < 624 then
        (0x9c3e400c641a5d2cfc9c392ffd36fc47290875b80000000138725ff80c52112d70000270e4bff4dbf01ca42256e98be4e1c9a3e9abe2394845adc000000009c39347c062908d6b80001387268fa6af80e5211ab700004a1f477f270e150a4239ce0000575a4e1c9a3e231484735c96349c39347d33fc472908e5b800010f6a66f8e438a84211ca700004d3f210b4cbf058842354e9afe42d6997e993e0b90845a9c6b349e3927fd30fc173908b5b8000000013c724ff80c7211ad70000278e49ff4c3f01ce422dae >>> (103*(i % 16))) % 2^103
      else
        (0x2aefaa2fa80f82af2108426bb49c393efd3e7c47290873b80002bda977e4e1c2a1484529c0000000270e4fbf018a42252e000138727dfa7cf80e5211277000000013dfc862c14210892b80009fbe43969ebe0a9084395c0004f3f124d1b6b15084214ae0000df68865a78f82a42108570000000000013bfc8018c832b800037da21969c7e0a908421dc000000000004ebf2006320cee000000010c5a5cf80c42112970000872d2e7d39fc07210874b800000009cbe36d62210842a5c000000010cb4e3f014842112e >>> (101*(i % 16))) % 2^101

private def part40 (i : ℕ) : ℕ :=
  if i < 704 then
    if i < 672 then
      if i < 656 then
        (0xa43e639a39162a44a7539c00014afc722d47fc46894ea6ba97f8e45a8ffa8ef88f129d4b70000282e51bf1c8b152252a94e0000505ca63ea33e2944a5529aa0b94efd467d45fc53894aa52c00014170af3a8af8a912954a5000000000000513f00a252a52900000000a27ea23e01c4a54a4e00000000000143fc0489089494000000029ffa86f80b12112728000000050bf1247051e4224a50000a83e248ea13e0abc84394a000000009fb8492c448908549400013f70925a82f88b1210a728000507f503f124b151e4214a5 >>> (103*(i % 16))) % 2^103
      else
        (0x35cea27ea23e09c4a549ce00006b2d497d4dfc0799ceb5ae9ef8d63a8ffa99f88f129d4b580000000525f537f00e673ad6d000000000000a4be014ce76b5a00000001497d4dfc0399ceb6b4000000029afa8ff885129d4d68000539f51ff533f10e253a96d00003c16a4bea5be03cce75adc0000000099ad497c0699ced6b80000f05a92fa96f80f339d6d7000000002b8b16a7112673c5ce000000002d4ea53e02cce77b9c0000000149fc5aac4499cee73800000001335a92f80d339dae700001e0b525f523f01e673adce >>> (103*(i % 16))) % 2^103
    else
      if i < 688 then
        (0x9fb940fc492c548908529686e27ee561f55ff31624210849fb554fd547c9e2c4d89ce421000027ed31ce2bcb1462a7108400009fb5567caf2c498a9a42127ed559f557f2bcb1362a5908400009fb5557caf2c518a9442100000000553f27cb0262949084000154fd547c9f2c0d8a4e4210000000054ff27cb045e929084000156fd537c9e2c1579ca4210000000027ed270b106254908400009fb5527c9c2c45894e421000054bf547f270b145e529084a0b86b9d44fd447c53894a739c00027ee543f50df1162421ce5 >>> (102*(i % 16))) % 2^102
      else
        (0x6bb53efd5f7c43290873b400000004fbf008a42252d00013efd5f7c03290893b4000000057bf04084224ad00015ffd5e7c11210872b4000577f124d14084214ad00006fb55d7c11210842b40000000573f2006320cad00006fb559fc11210843b4000000056ff2006320ced000000012e7c02210894b40004b9f56bf00c8421d2d000000015a7c40210854b40000000567f004842112d00000001597c8018c834b682e547f270b1462529084 >>> (86*(i % 16))) % 2^86
  else
    if i < 736 then
      if i < 720 then
        (0xb43e009087225a00000000000167fc8018ce34b400010f68df709a38a8421dca700001bee210b59bf058843b54e37dc42d6b37eb33e0b90875a9c000165fc6fb8722c54210ea5380000df710c5acaf82c421d2a71bee21cb595f593f05c8439d4e0000b23e37dc36d62a10872a9c00006fb8432d63fc15210e4538000000000002c6f900319c6a758df58bf33df000b350423894e0000b3feb3beb13e610847125b6a7d69fd627d61fcc3108e23b40002d6fad5fac2f9a02114456dc9f5c7f5b5f583f344422888b >>> (103*(i % 16))) % 2^103
      else
        (0x37dcb83e089087395a000000016ffc6fb850210e52b400000000df72def822421c8568000000000005bbf2006338cad0000b77eb73eb0be680847115b717d70fc9a1d6dfcc5108e222c000000000000df70204215256800000001bee5b3f0448429cad00000000b63e37dc281085295a000000006fb96bfc11210a42b4000000000002d6f9003194656800000001bee5a1f04484390ed000000000000b53e400c6719da000000000001657c02210e94b400000002cafad2f806421ce968000000000005a3f100843952d >>> (103*(i % 16))) % 2^103
    else
      if i < 752 then
        (0x35dc4d164e1a2294e72116000173fc49345021ca52b6eff9345aeef82a43948459aee5d7f5d5f10ca739ced35dc753e26962a14e7529c0000000175fc0229ce94b40002ebfaeaf806539d276800000005d3f040872a4ad0000bb3eba3e0890e5395a000173fc493850214a52b6edf89272e6f8a242948459bee5cbf5aff054842908b00000000b93e400c6519166fb89a1d6f7c15210e422c00000002e2f900319c645800000001bee040843a4ad >>> (87*(i % 16))) % 2^87
      else
        (0x36dcc03e0890ae494e0000000043397ffc14211c92940000867301fafef82a4238e5280005fbf10ce124b15084714a50000219c37d6bf3e0a908e214a0000000000017dfc8018dc329400008670df5af5f82a42388538000000000005f3f2006370ca7000000000000219c08108e49520000000043397bfc11211c72a400000002f6f88670a04238a548000000010ce5ebf04484710a9000000000000bd3e400c6e195200017a7d79fc0038d0109c22a6f9faf8f80072f2f9a22138453df7f5f5f000e5e3f35042708a5 >>> (103*(i % 16))) % 2^103

private def part48 (i : ℕ) : ℕ :=
  if i < 832 then
    if i < 800 then
      if i < 784 then
        (0x9fb9887c722c548908a5380000000218b61ff01a242252e0000862d87fd877c07890893b8000000061bf218b051e4224ae000189fc872d867c15790872b8000000027ee1b6b112242152e00009fb86dad857c45890853b8000617f613f1b6b151e4214ae00018a7c432d847c157908423800046df60bf278d054ef790849faca19c9f9c9e34713c62421262e260e60bf278d0d4ef890840001827c97389c34512ba2421000060df607f270d114ae7908400006bac6db9807c51215c729c000000000001b6e04085724a9 >>> (102*(i % 16))) % 2^102
      else
        (0x1917d907c9c2c512154421000062df63ff2bc705484510840000000000018f7c8018d432100000000631f278d104e56908400009a398e7c9e34153916421000045ff134e278d144ea71084000000018d7c9e34093a5a4210000635f633f278d034e769084000000018c7c9c3441295a4210000637f62ff270d114a45908400009fb984fc6dac54890852ba86e27ee10cb62bf316242108e9fb8872d87fd877c47890873b800027ee31cd1c8b15224229ce00009fb8722d897c468908a6ba7ee1c8b625f623f11e242296e >>> (102*(i % 16))) % 2^102
    else
      if i < 816 then
        (0x8bbe4e1a04952d21080001177d97fc9c340d2a56421239fb2afb2cf938689a55ac84200000000655f270d024ad690840000cabecb3e4e1a0695ab21080001197d817c9c34512b9c421000015d732af93868925734842258e655f653f270d134ae59084000043dcca3e578e2891ca2108000195fd93fcc6ac19235442132dfb27fb26f98a583a45a8842000064bf459f2bcb1448a510840000cbbec93e4f960c912a2109987d927d91fc9e2c1d21d4421136731afb19f93c683a73ac8420000643f62ff270d114a559084 >>> (103*(i % 16))) % 2^103
      else
        (0xd03e083c84495a00000001a17d9ffc11790872b40000000000013f70811210a968000000027ee67bf10624214ed00000000cfbecf3e283c84295a00000001a1fd9dfc11790842340000df7226f938382a4214842000000000000673f2006328c84000037dcccfe4f0e0a908721080000000000019bfc8018ce32100000000324f93e581244a48420000649f66bf278b034874908400000000cd3e4e162090a921080000000199fc9f1c052112421000000000000332f90031a4642643f45df65ff270d134a759084 >>> (103*(i % 16))) % 2^103
  else
    if i < 864 then
      if i < 848 then
        (0xd43e2d56224ce7729c000099ada7fc0699ced538f05b4ffb4ef80f339d6a7000069bf134b112673a94e00000000d33e014ce74a5a0001a67da5fc0399ce74b4000000034af881129ca9680006a5f693f10625394ed0000d4fed23e283ca5295baf7dae7da3fc51794a422f64fb46fb3bf82af210845800027ee679f14224214ad50dc4fdcd13e60c484211a9fb987fda0fc43890873b4000000030ff8051211296800061ff683f00e24224ed >>> (87*(i % 16))) % 2^87
      else
        (0xd4fed83e283ce5295a0001b17c9a2daffc1579ca422c00000001416b48f8a1129ca56800027ed26876bbf116253908b0000d4bed5fed5be21c4e739da0001487cc7344d2c5489cea738000295f89a5b5af88d139d4d752ff134b6b5f6b3f11e273a96e0000d37ed63e26962a44e7529c000000000001abfc0289ce94b40000000357fb56f807139d2768000000000006abf041e72a4ad00000000d6fed53e08bce5395a00000001a67da5fc0399ce73b4000000015c589a3889339e2a70000000013476a3f016673bd4e >>> (103*(i % 16))) % 2^103
    else
      if i < 880 then
        (0xdc3e37d6a03e0abc84210a000000006fb49a2d777c1521ca42ac000000036ef89272e6f8a24294855800000001bee6dbf5aff05484290ab0000000000000000db3e400c651956000000006fb89b1d687c15210e43ac00000000000000036af900319c675ed5f6d3f26c7589f587f31c42388eb0000db3edafeda3eb07e6888451156000000000000a0b9a47c50894a52b40000000141735cfb66f8a312948458000286e27ee6cbf689f316242108b000000000000505ad83e2844e7295a000000009fb49a2db1fc4589ce422c00000000000000034af881139ca968000000000006a5f6c3f10627394ed >>> (119*(i % 16))) % 2^119
      else
        (0x1bc7c9e3844390856a8000268d278e6fff054e42116a000087ac5ab49e38543908e728000266d278e6fbf058e4235ca78349e39befdbe7c173908b7280006f7f134d278e150e4229ca000000009e39bd7c06390896a8000278e6f5f6f3f01ce421daa00000001bc7c9c3844290856a80006fdf270e6eff114a42116a00009fb8859dba7c458908f5b8000286e27ee210731224245aea1b89fb8859dba7cc5890915b80001e4b6e7f1c87151e42454e0001bafc721db97c157908f53a86e27ee1beb55ff3162421085 >>> (102*(i % 16))) % 2^102

private def part56 (i : ℕ) : ℕ :=
  if i < 960 then
    if i < 928 then
      if i < 912 then
        (0xe53e80fee43e0b10846a95cb7d02fdc87dc7fc172108b528d6693c737dfb8cf82e72116b500000000278e6fbf018e4235aa00004f1cdf7ee33e039c845b540001bdfc72349c38542908a72800038bf938738af88c52114d571bf270e715f713f11ca42296a0000e3bee23e7cfe2a108452940001cbfd037dc3fc162108952b99fa08fb87fb86f82e4210ea526cd278e6f5f6f3f05ce421d6a0000e13e4e1cddfe2294842ad40001c2fdc1fcf6fc5421085528000376f9cffb82f82a42108a5000000000000703f2006320d4a >>> (103*(i % 16))) % 2^103
      else
        (0x6e3ee83e0190853a5a000000000001cffc40210a54b40000000000039ef802421489680000000000073bf2006328d2d0000e77ee73e677e610845125bd17dd0fccefdcdfcc3108a24af84f938738afb98f88e5210eb500000000270e715f018a4225aa00004e1ce2bee63e0394844ad5c6fc9c39c9fdcafc472908b5a800000001387393f80c5211ad50000270e727f72bf01ca42356a000043d643ce4e1c2a148473940000aeb49c39c9fc462908e6a92c69387393fb92f88e5211cb5000021ed723f401f150842394a >>> (103*(i % 16))) % 2^103
    else
      if i < 944 then
        (0xec3ee1fe0310844a55d97dc3fdd7fc07210874a93659d3fba6f80e4394e95800075bf749f104852952b0000ebbeeb3e2210842a540001d1fdd5fc05210844a800000003aaf90031906950000000074bf100872952d00004d16ea3e0290e5225600000000e9fc0221ca94b40001d3fba6f8064394e968000000074bf100852952d0000e9fee93e2090a522560001d1fdcf7c05210a44ac00000003a2f900319469580000000371f008842a52d >>> (87*(i % 16))) % 2^87
      else
        (0x35dc4d96bafebabe2394e739d600000001dffc9b2d747c1521ca72ac00000003bef89272e6f8a24294a5580000000781f124d77bf15084214aa0000000037dadb7eef3e0a908421540000000000000001ddfc8018c832a800000000df6bb6fbabf82a42108750000000000000000773f2006320cea0000000037da4d16ea3e0a90e521d600000001dbfc4939d27c51214a43ac00000000df73b6fb9ef82a4214875800000000000000076bf2006328cebed7eed3eda3e677ee6fe69884511d600000001d6fcfafdd8fc43214a74ac0000000000000001f5f80442952968000000000003ebf763f00c852a52b >>> (119*(i % 16))) % 2^119
  else
    if i < 992 then
      if i < 976 then
        (0xf37e4d96d5fed5be23c4e739d60001e7fc9b2daa7c1579ca72ac0001365b4cfb4bf80f339ce75800079bf26c7693f11625394eb0000f3bef33ed1fe28bca529560001eafde87de5fc54790852a80003f0fb46fbcaf82af2108451aed270e78df78bf11ca421cea0000efbe249cf0fe2890a53956000057b5c47c9c38542908a528000000013873c6f80c52112950000270e78df78bf01ca4224ea000000000000249c0810a5495a000000004939e1fc11214a92ac00000003c4fbc2f82842112550000791f78ff783f0548421caa >>> (103*(i % 16))) % 2^103
      else
        (0x4fdcf83ea2be2a448452940001f4fdeffc06890894abebfbdffbdef80f121127526c77b7f7b5f01e253a4ebd37ea37e39162a44a7529c00000001edfc02894e94b40003dbfbdaf807129d276800000007b3f041e52a4ad0000f73ef63e08bca549560001eefdebfc14790892abeefbecfbd6f82af210e55282e799f7a7f14625294eb00000000505c2044a52a5a0000a0b9e9fc41894a54ac00013f73d2f8891210a9527ee7a9f7a3f11624214ea >>> (87*(i % 16))) % 2^87
    else
      if i < 1008 then
        (0x505cfb7ea33efabe29c4a539d69fb9f7fdeffdef7c47890873abcdf9363bdbfbdaf88f129ce75800079df7dbf7b1f145e529cab0000f73ea33efabe09c4a549d6000000000001467c02894a94b4000000028cfbeaf8071295295a82e53bf7cbf7cff14e252a96b00000000505cf97e2144a5535a0000a0b9f2fdf3fc43894aa6ac000141718e68e458a912954e70000282e31cd7cbf14a252a9cd505c639af97ef93e29c4a5539600009fb8c735f1fc548908a72800013f73e6fbe2f88d12114d527ee7d1f7c5f7c3f11e242296a >>> (103*(i % 16))) % 2^103
      else
        (0x1e37e007c03290893a4000000000007fff04084224a90000000200fdff7c11210872a400000007fbf124d14084214a9000000006fb5fe7c11210842a4000000000007f7f2006320ca9000000006fb5fafc11210843a4000000000007f3f2006320ce9000000000001c3fc02210894a4000000070ff7eff00c8421d29000000000001fb7c40210854a4000000000007ebf0048421129000000000001fa7c8018c834a4000282e799f6cdf14625294ab00009fb9e87df97c54890852aa86e27ee6cbf7e3f316242108a >>> (102*(i % 16))) % 2^102

private def part64 (i : ℕ) : ℕ :=
  if i < 1088 then
    if i < 1056 then
      if i < 1040 then
        (0x208fe087c03000000000000286e27ee1beb819f31624210870002077c6fae01fc157908421c000000027ee809f14224214a90000a1b89fba067cc18908422400027ee7bff813f10e2421ce9000000000001effc02890894a400000007bff813f00e24224e9000000000002047c10790892a40000000815f80ff045e421ca90000000000009fb840890854a4000000027ee80bf10624214e900000002037e027c50790852a40000000817f807f045e42108900006bb5e37e007c43290873a40000000000078df008a422529 >>> (102*(i % 16))) % 2^102
      else
        (0x9c1e9bde0027083e63004210882125d3abd3a3c004e107e0ffcc700842110423b80002777a767c1ef80099a801084220845700008cff8cdf001383bf31402108441088e0000000000000001073e1000211086210dc000000020e7e0dfc004c340000210842138000000048cfc8bfc1af864000042108426800096df96bf835f833f0cc00008421084b00000001377f373f063e1a000010842109400000002effeef7e0bfc320000210842124000609fe08fc17fc16f86600004210842380000000c61fc5ff82bf0d00000842108450000000195ff95bf053e188000108421088000000000000000209fc08000010844210c00000000000413fc12f8180000000084210000000000000000823f008000000008421 >>> (139*(i % 16))) % 2^139
    else
      if i < 1072 then
        (0x861f1b7944de441e55084210842b9ce0000000010d944de441e85ff1548421084239ce0000000000000000000085df8006320c841b9ce000085df85bf0019001532bed504220884139ce0000871f86ff001532be859fc584220884135ce87bf879f001532be859f857fc5c422088412dce00004add4abd855f001532bed504220884129ce00004e1d4dfd001532be853fc584220884125ce4ebd4e9d001532be853f851fc5c422088411dce00004efd4edd84ff001532bed504220884115ce000087ff87df001532be84dfc544220884111ce0000000000000000000084bf200221886410dce0000000084bf849f001500133500210844109ce00000000897f895f0013847f3180210844109ae00008b9f8b7f0013847f845f31c02108441096e000000004acf4aaf843f001335002108441094e >>> (156*(i % 16))) % 2^156
      else
        (0x2207d137910793c7455210842108473800000000000000087ff8006320c84191ce000124751379107a1cfc55210842108b73800000000000000087bf8006320c841adce000000011379107a197c16210842112d73800044de441e865f877f05c84210843b5ce000000021d7d137910791421084210ad738000000044de441e873f0548421084235ce00000000000000021c7e0018c832106d73800048fd44de441e485d15484210847b9ce00021b7d1df5137910795421084211ce738000211944de441e86bf15884210846b9ce85e51379107a1afe1a7c57210842116e738000867f1c9944de441e5508421084539ce000086651379107a197c56210842112e73a1d944de441e865f863f15c84210843b9ce >>> (138*(i % 16))) % 2^138
  else
    if i < 1120 then
      if i < 1104 then
        (0x8a1f8006320c84191ae0000565d563d32be853fc184220884125ae56fd56dd32be853f89dfc1c422088411dae0000573d571d89bf32bed104220884115ae00008a1f89ff32be899fc144220884111ae0000000000000000897f200221886410dae000000004ffe1b751b73451c4210842a5ce00004ffe1b751b73893f455c42108429dce00004ffe891f1b751b73551c421084295ce00004ffe10d510d388ff455c421084211ce000088df31bc31ba31b9255a421084211ce88df88bf315c315a31593556421084211ce0000889f2bdc2bda2bd94554421084211ce0000887f27dc27da27d92552421084211ce887f885f279c279a2799354e421084211ce0000883f271c271a2719454a421084211ce >>> (140*(i % 16))) % 2^140
      else
        (0x8c1f271c271a2719454a4210842116e00008bff44de441e575d15484210842116e00000000000000008bdf8006320c841916e8bdf8bbf581d32be899fc5442208841116e00000000000000008b9f200221886410d6e0000000000004ffe1b73411c4210842a5ae000000004ffe1b738b5f415c42108429dae000000004ffe8b3f1b73511c421084295ae000000004ffe10d38b1f415c421084211ae000000008aff31ba31b9215a421084211ae00008aff8adf315a31593156421084211ae000000008abf2bda2bd94154421084211ae000000008a9f27da27d92152421084211ae00008a9f8a7f279a2799314e421084211ae000000008a5f271a2719414a421084211ae000000008a3f441e575d1148421084211ae >>> (140*(i % 16))) % 2^140
    else
      if i < 1136 then
        (0x8e1f8006370c841908e00008e1f8dff001c5e1e5e1dd1442708841108e00008f3f8f1f8ddf31ae31adc9442688841108e8fdf8fbf8ddf8dbf314e314dcd442588841108e000063de63be8d9f2bce2bcdd1442508841108e0000665e663e8d7f27ce27cdc9442488841108e66fe66de8d7f8d5f278e278dcd442388841108e0000673e671e8d3f270e270dd1442288841108e0000901f8fff8d1f32be32bdc5442208841108e000000000000000000008cff200221886410c8e000000004ffe491710d38b1f455c4210842116e000000008cbf31bc31ba31b9255a4210842116e00008cbf8c9f315c315a315935564210842116e000000008c7f2bdc2bda2bd945544210842116e000000008c5f27dc27da27d925524210842116e00008c5f8c3f279c279a2799354e4210842116e >>> (156*(i % 16))) % 2^156
      else
        (0x2407e0018c832106423800062de8f5f314e314d15484590842108e00000000000000023f7e0018d632106423800000008e9f27d627d509489690842108e00023a7e3e7c9e589e543521da42108423800000008f7f2716271541485690842108e000000023d7cc6b8c6b415211a4210842380000000000000008f3f8006368c841908e000183dd8178434d3c6d45239c421084238000211c8eff31b631b51948d710842108e85f23bfe3b7cc558c5547522dc4210842380008ebf1c9c2bd62bd55148a710842108e000086723a7c9f589f5465225c42108423a1dc8e9f8e7f279627951d487710842108e0002397c6df09c589c5545215c42108423800010dc8e3f5f9e5f9d15484710842108e >>> (138*(i % 16))) % 2^138

private def part72 (i : ℕ) : ℕ :=
  if i < 1216 then
    if i < 1184 then
      if i < 1168 then
        (0x564f562f841f30802108441092d000056ef56cf841f91ff30c0210844108ed00000000572f570f91df3400210844108ad00000000923f921f91bf30402108441088d0000000000000000919f08001088431086d0000000060fb27162715415c5490842108e000060fb915f27162715455c5390842108e000054be913f27162715515c5290842108e00004ffe911f10d34f17455c4210842108e000090ff31bc31ba31b9255a4210842108e90ff90df315c315a315935564210842108e000090bf2bdc2bda2bd945544210842108e0000909f27dc27da27d925524210842108e909f907f279c279a2799354e4210842108e0000905f271c271a2719454a4210842108e0000903f44de441e441d15484210842108e >>> (140*(i % 16))) % 2^140
      else
        (0x217c943f941f31551c48b710842108d0000000093ff1c9c2bd55048a710842108d00000000219c93df27d518489710842108d000021dc93df93bf27951c487710842108d00000000939f1b7c271550485710842108d0000000010dc937f5f9d14484710842108d0000000000000000935f8006370c841908d0000935f933f001c5e1dd0442708841108d0000947f945f931f31adc8442688841108d951f94ff931f92ff314dcc442588841108d000063de63be92df2bcdd0442508841108d0000665e663e92bf27cdc8442488841108d66fe66de92bf929f278dcc442388841108d0000673e671e927f270dd0442288841108d0000955f953f925f32bdc4442208841108d0000000000000000923f200221886410c8d >>> (140*(i % 16))) % 2^140
    else
      if i < 1200 then
        (0x963f961f315c315934564210842108d000095ff2bdc2bd944544210842108d000095df27dc27d924524210842108d95df95bf279c2799344e4210842108d0000959f271c2719444a4210842108d0000957f44de441d14484210842108d000000000000955f8006320c841908d000062de949f314d14484590842108d000000000000951f8006358c841908d0000000093df27d508489690842108d000093df94df27950c487690842108d0000000094bf271540485690842108d00000000949f31ad04484690842108d000000000000947f8006368c841908d00006757605e575b5048e710842108d0000211c943f31b51848d710842108d >>> (124*(i % 16))) % 2^124
      else
        (0x983f981f001c5e1e5e1dd1442708841108b0000995f993f97ff31ae31adc9442688841108b99ff99df97ff97df314e314dcd442588841108b000063de63be97bf2bce2bcdd1442508841108b0000665e663e979f27ce27cdc9442488841108b66fe66de979f977f278e278dcd442388841108b0000673e671e975f270e270dd1442288841108b00009a3f9a1f973f32be32bdc5442208841108b00000000000000000000971f200221886410c8b00000000971f96ff581791bf31402108441088b0000000000000000000096df08001088431086b0000000000000000675b2715405c5490842108d000000000000675b969f2715445c5390842108d00000000000054be967f2715505c5290842108d0000000000004ffe965f5757445c4210842108d000000000000963f31bc31b9245a4210842108d >>> (156*(i % 16))) % 2^156
  else
    if i < 1248 then
      if i < 1232 then
        (0x18b7a65fcc538c53455211642108422c00000000000000099ff8006358c841908b0000000262fc9f589f5425225a42108422c00098bf99bf279627950d487690842108b00000002667c9c589c5505215a42108422c0000000997f31ae31ad05484690842108b0000000000000002657e0018da32106422c00068b7605e5cbb575b5148e710842108b00008472647cc6d8c6d465235c42108422e17c991f98ff315631551d48b710842108b0002637c7270af58af5545229c42108422c000219c98bf27d627d519489710842108b877262fe627c9e589e547521dc42108422c000987f1b7c2716271551485710842108b00004372617d7e797e7455211c42108422c000000000000000983f8006370c841908b >>> (138*(i % 16))) % 2^138
      else
        (0x772f770f76779c3f9c1f31c0210844108ea0000776f774f9bff6cf73500210844108aa0000b75fb73f58179bdf31402108441088a00000000000000009bbf08001088431086a0000000068bb27162715415c5490842108b000068bb9b7f27162715455c5390842108b000054be9b5f27162715515c5290842108b00004ffe9b3f5cb75757455c4210842108b00009b1f31bc31ba31b9255a4210842108b9b1f9aff315c315a315935564210842108b00009adf2bdc2bda2bd945544210842108b00009abf27dc27da27d925524210842108b9abf9a9f279c279a2799354e4210842108b00009a7f271c271a2719454a4210842108b00009a5f44de441e441d15484210842108b00000000000000009a3f8006320c841908b >>> (140*(i % 16))) % 2^140
    else
      if i < 1264 then
        (0x9f9f9f7f1bee32be9e1fc584220885135cea03fa01f1bee32be9e1f9dffc5c422088512dce00004add4abd9ddf1bee32bed504220885129ce00004e1d4dfd1bee32be9dbfc584220885125ce4ebd4e9d1bee32be9dbf9d9fc5c422088511dce00004efd4edd9d7f1bee32bed504220885115ce0000a07fa05f1bee32be9d5fc544220885111ce000000000000000000009d3f200221886510dce000000009d3f9d1f001500133500210845109ce00000000a1ffa1df00159cff3480210845109cd0000a41fa3ff00159cff9cdf34c0210845109cb00000000a71fa6ff00159cbf3500210844109ca00000000b15fb13fac5f9c9f3180210844109aa0000b5ffb5dfb41f9c9f9c7f31c02108441096a00000000702f700f9c5f337735002108441094a00000000754f752f73579c3f31802108441092a >>> (156*(i % 16))) % 2^156
      else
        (0x1bf6441e9edf05884210854b5ce00001bf6441e9edf9fff05c84210853b5ce000000009fdf1bf6441e45084210852b5ce000000001bf6441e9fbf0548421085235ce00000000000000009f9f8006320c851b5ce000048fd1bf6441e485d15484210857b9ce00009f5f477d1bf6441e5508421085739ce000021191bf6441e9f3f15884210856b9ce21791bf6441e9f3f9f1f15c84210855b9ce00009eff1c991bf6441e5508421085539ce000021991bf6441e9edf15884210854b9ce21d91bf6441e9edf9ebf15c84210853b9ce00009e9f1b791bf6441e55084210852b9ce000010d91bf6441e9e7f1548421085239ce00000000000000009e5f8006320c851b9ce9e5f9e3f00191bee32bed504220885139ce >>> (140*(i % 16))) % 2^140

private def part80 (i : ℕ) : ℕ :=
  if i < 1344 then
    if i < 1312 then
      if i < 1296 then
        (0xa29fa27f1beea21fc444220885111cd0000000000000000a1ff200221886510dcd000000006dfe1bf61b73451c4210852a5ce00006dfe1bf61b73a1bf455c42108529dce00006dfea19f1bf61b73551c421085295ce00006dfe1bf610d3a17f455c421085211ce0000a15f31bc31ba31b9255a421085211cea15fa13f315c315a31593556421085211ce0000a11f2bdc2bda2bd94554421085211ce0000a0ff27dc27da27d92552421085211cea0ffa0df279c279a2799354e421085211ce0000a0bf271c271a2719454a421085211ce0000a09f1bf6441e4f1d1548421085211ce0000000000000000a07f8006320c85191ce0000491d1bf6441e9fbf154842108522dce0000000000000000a03f8006320c851adce >>> (140*(i % 16))) % 2^140
      else
        (0x1483e40044310ca21b96000000000001b7f86fd91071084214a9734000000036ff0dfb51efa22e21084294ee6800000006dfea3bf1bf6541c421085295cd00000000dbfc37ed473e88b884210a4239a000000028dfcc6f0c6e491690842148473400051bfd1af98ae18ac9a2b210842908e680000000a33f2bdc2bd94454421085211cd00000001463e4fb84fb248a484210a4239a00028c7e8bfc9e709e64d139084214847340000000516f938e138ca225210842908e680000000a2bf1bf64f1d1448421085211cd0000000000000001453f000c64190a3239a0001387537f46fba76ff12108822144973675ea74e8df74edfd12fe26211044288ee680004efd4edda23f1beed404220885115cd >>> (139*(i % 16))) % 2^139
    else
      if i < 1328 then
        (0x2195a61f049e421ce54a5cd0000000021d5a61fa5ff04de421ce53a5cd000000000000a5df1256441c4214e52a5cd00000000a69f1256a5bf445c4214e529dcd00000000507ea59f1256541c4214a5295cd0000507ea6bf1256a57f545c4214a5211cb00006dfe1bf6a55fa39f455c421085211cb0000a53f31bc31ba31b9255a421085211cba53fa51f315c315a31593556421085211cb0000a4ff2bdc2bda2bd94554421085211cb0000a4df27dc27da27d92552421085211cba4dfa4bf279c279a2799354e421085211cb0000a49f271c271a2719454a421085211cb0000a47f1bf6441e4f1d1548421085211cb0000000000000000a45f8006320c85191cba45fa43f1bee32bea21fc544220885111cb >>> (140*(i % 16))) % 2^140
      else
        (0xa83fa81f0019001532bed504220884139ca0000a95fa93f001532bea7ffc584220884135caa9ffa9df001532bea7ffa7dfc5c422088412dca00004add4abda7bf001532bed504220884129ca00004e1d4dfd001532bea79fc584220884125ca4ebd4e9d001532bea79fa77fc5c422088411dca00004efd4edda75f001532bed504220884115ca0000aa3faa1f001532bea73fc544220884111ca00000000000000000000a71f200221886410dca000000000000617da59f1256541c4214e5295cd0000000060fd1256268ba6df455c4214e5211cb00000000541e21d5a61fa5ff14de421ce539dcd000000006e3d541e1c8d16b3551e421ce5729ce00000000541e21152673a67f159e421ce56a9ce0000541e21751e13a67fa65f15de421ce55a9ce00000000a63f541e1c951353551e421ce5529ce >>> (156*(i % 16))) % 2^156
  else
    if i < 1376 then
      if i < 1360 then
        (0x124751379107aa5fc55210842108b728000000000000000a9ff8006320c841adca000000011379107aa2fc16210842112d72800044de441ea8bfa9bf05c84210843b5ca00000002a67d137910791421084210ad728000000044de441ea97f0548421084235ca0000000000000002a57e0018c832106d72800021f3477d44de441e5508421084739ca000084651379107aa47c5621084211ae72a17944de441ea91fa8ff15c84210845b9ca0002a37c72651379107954210842114e728000219944de441ea8bf15884210844b9ca87651379107aa2fea27c5721084210ee728000a87f1b7944de441e55084210842b9ca000043651379107aa17c55210842108e728000000000000000a83f8006320c841b9ca >>> (138*(i % 16))) % 2^138
      else
        (0x507e1256ac1f445c4214a52a5cb000000004ffe1b75abff451c4210842a5ca00004ffe1b75ac3fabdf455c42108429dca541e21d526d3a61fa5ff15de421ce539dcb0000ab9f125626cba5bf455c4214e529dcb0000507eab7f1256a57f545c4214a5295cb00004ffeabbf1b75ab5f551c421084295ca00004ffe10d5a55fab3f455c421084211ca0000ab1f31bc31ba31b9255a421084211caab1faaff315c315a31593556421084211ca0000aadf2bdc2bda2bd94554421084211ca0000aabf27dc27da27d92552421084211caaabfaa9f279c279a2799354e421084211ca0000aa7f271c271a2719454a421084211ca0000aa5f44de441e4f1d1548421084211ca0000000000000000aa3f8006320c84191ca >>> (140*(i % 16))) % 2^140
    else
      if i < 1392 then
        (0xae3fae1f31593056421085211ad00000000adff2bd94054421085211ad00000000addf27d92052421085211ad0000addfadbf2799304e421085211ad00000000ad9f2719404a421085211ad00000000ad7f575d1048421085211ad000000000000ad5f8006320c85191ad0000565d563d9dbfc084220885125ad56fd56dd9dbfad1fc0c422088511dad0000573d571dacffd004220885115ad0000ad5fad3facdfc044220885111ad000000000000acbf200221886510dad0000acbfac9f9cff3080210845109adaedfaebf9cffac7f30c0210845109ab507eab7f1256ac1f545c4214a529dcb00000000507e1256441c4214a52a5cd >>> (124*(i % 16))) % 2^124
      else
        (0x6dfeb01fae5f415c421085211ab0000afff31ba31b9215a421085211abafffafdf315a31593156421085211ab0000afbf2bda2bd94154421085211ab0000af9f27da27d92152421085211abaf9faf7f279a2799314e421085211ab0000af5f271a2719414a421085211ab0000af3f441e575d1148421085211ab000000000000af1f8006320c85191abaf1faeff32beacdfc144220885111ab000000000000aedf200221886510dab0000000000006dfe401c4210852a5ad000000006dfeae9f405c42108529dad000000006dfeae7f501c421085295ad000000006dfeae5f405c421085211ad00000000ae3f31b9205a421085211ad >>> (124*(i % 16))) % 2^124

private def part88 (i : ℕ) : ℕ :=
  if i < 1472 then
    if i < 1440 then
      if i < 1424 then
        (0x1643e883caeba2290842108423540000000000000002c7fe0018c83210646a80002b2eab1e995f53cfe0c2110442092d556fd56dd32bea79fb1bfc1c422088411daa0000ae7aae3b633e657da20844110822b540002c7fec77ccafac5ff0510882210446a800000000000000058af900110c432086d500000000000067ddb05f501c4214e5295ad00000000ceba4d17623e82b88429ca4235600000001507a987ec2fc4379087394e76b4000000000000000530f804f210e72a52d6800000000000a61fb0bf00de421ce53a5ad0000000000000001613e80388429ca54b5a000000000002c37ec1fd0171085394a76b400000000000283f582fa80e210a5294ad680000000507eb0ffb03f505c4214a5211ab >>> (139*(i % 16))) % 2^139
      else
        (0x507eb33fb3df505c4214a529dab000000000000507e401c4214a52a5ad00000000507eb3df405c4214a52a5ab000000004ffeb3bf411c4210842a5aa00004ffeb3ffb39f415c42108429daa541e26d3a61fb0bf11de421ce539dab0000b35f26cbb07f415c4214e529dab0000507eb33fb03f505c4214a5295ab00004ffeb37fb31f511c421084295aa00004ffeb01fb2ff415c421084211aa0000b2df31ba31b9215a421084211aab2dfb2bf315a31593156421084211aa0000b29f2bda2bd94154421084211aa0000b27f27da27d92152421084211aab27fb25f279a2799314e421084211aa0000b23f271a2719414a421084211aa >>> (124*(i % 16))) % 2^124
    else
      if i < 1456 then
        (0xb63fb61f581d32beb17fc5442208841116a0000000000000000b5ff200221886410d6a000068bd1256268bb11f455c4214e52116b0000507eb5bf1256b03f545c4214a52116b00006dfe1bf6b59fae5f455c4210852116b0000b57f31bc31ba31b9255a4210852116bb57fb55f315c315a315935564210852116b0000b53f2bdc2bda2bd945544210852116b0000b51f27dc27da27d925524210852116bb51fb4ff279c279a2799354e4210852116b0000b4df271c271a2719454a4210852116b0000b4bf1bf6441e575d15484210852116b0000000000000000b49f8006320c851916bb49fb47f1bee32beacdfc5442208851116b0000000000000000b45f200221886510d6bb45fb43f39579cffac7f34c02108451096b >>> (140*(i % 16))) % 2^140
      else
        (0xba3fba1fb83fb81f314e314dcd442588841108a000063de63beb7ff2bce2bcdd1442508841108a0000665e663eb7df27ce27cdc9442488841108a66fe66deb7dfb7bf278e278dcd442388841108a0000673e671eb79f270e270dd1442288841108a0000ba7fba5fb77f32be32bdc5442208841108a00000000000000000000b75f200221886410c8a000000004ffe6ed7b59fb2ff455c4210842116a00000000b71f31bc31ba31b9255a4210842116a0000b71fb6ff315c315a315935564210842116a00000000b6df2bdc2bda2bd945544210842116a00000000b6bf27dc27da27d925524210842116a0000b6bfb69f279c279a2799354e4210842116a00000000b67f271c271a2719454a4210842116a00000000b65f44de441e575d15484210842116a00000000000000000000b63f8006320c841916a >>> (156*(i % 16))) % 2^156
  else
    if i < 1504 then
      if i < 1488 then
        (0xb8ff27d627d509489690842108a0000b8ffb9ff279627950d487690842108a00000000b9df2716271541485690842108a00000000b9bf31ae31ad05484690842108a0000000000000000b99f8006368c841908a00007937605e5cbb779b5148e710842108a0000211cb95f31b631b51948d710842108a217cb95fb93f315631551d48b710842108a0000b91f1c9c2bd62bd55148a710842108a0000219cb8ff27d627d519489710842108a21dcb8ffb8df279627951d487710842108a0000b8bf1b7c2716271551485710842108a000010dcb89f5f9e5f9d15484710842108a0000000000000000b87f8006370c841908ab87fb85f001c5e1e5e1dd1442708841108ab99fb97fb83f31ae31adc9442688841108a >>> (140*(i % 16))) % 2^140
      else
        (0xbc9fbc7fbc1f3040210844108890000000000000000bbff08001088431086900000000793b27162715415c5490842108a0000793bbbbf27162715455c5390842108a000054bebb9f27162715515c5290842108a00004ffebb7f5cb77797455c4210842108a0000bb5f31bc31ba31b9255a4210842108abb5fbb3f315c315a315935564210842108a0000bb1f2bdc2bda2bd945544210842108a0000baff27dc27da27d925524210842108abaffbadf279c279a2799354e4210842108a0000babf271c271a2719454a4210842108a0000ba9f44de441e441d15484210842108a0000000000000000ba7f8006320c841908a000062deb9bf314e314d15484590842108a0000000000000000ba3f8006358c841908a >>> (140*(i % 16))) % 2^140
    else
      if i < 1520 then
        (0x21dcbe3fbe1f27951c487710842108900000000bdff1b7c27155048571084210890000000010dcbddf5f9d1448471084210890000000000000000bdbf8006370c84190890000bdbfbd9f001c5e1dd044270884110890000bedfbebfbd7f31adc84426888411089bf7fbf5fbd7fbd5f314dcc4425888411089000063de63bebd3f2bcdd044250884110890000665e663ebd1f27cdc8442488841108966fe66debd1fbcff278dcc44238884110890000673e671ebcdf270dd044228884110890000bfbfbf9fbcbf32bdc444220884110890000000000000000bc9f200221886410c89000000007e8f7e6f9c3f30802108441092900007f2f7f0f9c3fbc5f30c0210844108e9000000007f6f7f4fbc3f3400210844108a9 >>> (140*(i % 16))) % 2^140
      else
        (0xc03fc01f279c2799344e421084210890000bfff271c2719444a421084210890000bfdf44de441d144842108421089000000000000bfbf8006320c8419089000062debeff314d144845908421089000000000000bf7f8006358c841908900000000be3f27d50848969084210890000be3fbf3f27950c487690842108900000000bf1f271540485690842108900000000beff31ad044846908421089000000000000bedf8006368c841908900008057605e7f9b5048e71084210890000211cbe9f31b51848d7108421089217cbe9fbe7f31551c48b71084210890000be5f1c9c2bd55048a71084210890000219cbe3f27d5184897108421089 >>> (124*(i % 16))) % 2^124

private def part96 (i : ℕ) : ℕ :=
  if i < 1600 then
    if i < 1568 then
      if i < 1552 then
        (0xc7bcc77d843e579c579ba2884a11082210e0001997998fb07fc9f389f3725109222104421f37f336f60ffe0ef93c713c6e6a211c442088438000673e671ec1bf270e270dd144228884110870001893f88ff833e657c657b8a884411082210e0000000000000000000305fc80088621904321c000000060bfe0af8df3de0f98a01084220844380000000000000000000c13f080010884310867000000000000000100b64e2a80b8a9210842112000000000002016f03fc9c5511714e421084224000000000002a5f606f938aa82e294842108448000000000004ffec0bf7f97445c42108421089000000000001813e6378637248b48421084211200000003027f01fcc570c564d1590842108422400000000000602f95ee15eca22a21084210844800000000000c03f27dc27d9245242108421089 >>> (155*(i % 16))) % 2^155
      else
        (0xc31fc41f279627950d4876908421087000000000000c3ff27162715414856908421087000000000000c3df31ae31ad05484690842108700000000000000000000c3bf8006368c84190870000000081b7605e1bf37f9b5148e710842108700000000211cc37f31b631b51948d71084210870000217cc37fc35f315631551d48b710842108700000000c33f1c9c2bd62bd55148a710842108700000000219cc31f27d627d5194897108421087000021dcc31fc2ff279627951d487710842108700000000c2df1b7c271627155148571084210870000000010dcc2bf5f9e5f9d15484710842108700000000000000000000c29f8006370c84190870000c29fc27f001c5e1e5e1dd144270884110870000c3bfc39fc25f31ae31adc94426888411087c45fc43fc25fc23f314e314dcd4425888411087 >>> (156*(i % 16))) % 2^156
    else
      if i < 1584 then
        (0xc61f0800108843108650000000081bb27162715415c54908421087000081bbc5df27162715455c53908421087000054bec5bf27162715515c5290842108700004ffec59f1bf37f97455c421084210870000c57f31bc31ba31b9255a42108421087c57fc55f315c315a31593556421084210870000c53f2bdc2bda2bd94554421084210870000c51f27dc27da27d9255242108421087c51fc4ff279c279a2799354e421084210870000c4df271c271a2719454a421084210870000c4bf44de441e441d1548421084210870000000000000000c49f8006320c8419087000062dec3df314e314d1548459084210870000000000000000c45f8006358c841908700000000c31f27d627d5094896908421087 >>> (140*(i % 16))) % 2^140
      else
        (0xc81f1c9c2bd62bd55148a710842108500000000219cc7ff27d627d5194897108421085000021dcc7ffc7df279627951d487710842108500000000c7bf1b7c271627155148571084210850000000010dcc79f5f9e5f9d15484710842108500000000000000000000c77f8006370c84190850000c77fc75f001c5e1e5e1dd144270884110850000c89fc87fc73f31ae31adc94426888411085c93fc91fc73fc71f314e314dcd4425888411085000063de63bec6ff2bce2bcdd144250884110850000665e663ec6df27ce27cdc9442488841108566fe66dec6dfc6bf278e278dcd44238884110850000673e671ec69f270e270dd144228884110850000c97fc95fc67f32be32bdc5442208841108500000000000000000000c65f200221886410c8500000000c65fc63f1be732b7314021084410885 >>> (156*(i % 16))) % 2^156
  else
    if i < 1632 then
      if i < 1616 then
        (0xca1f2bdc2bda2bd94554421084210850000c9ff27dc27da27d9255242108421085c9ffc9df279c279a2799354e421084210850000c9bf271c271a2719454a421084210850000c99f44de441e441d1548421084210850000000000000000c97f8006320c8419085000062dec8bf314e314d1548459084210850000000000000000c93f8006358c841908500000000c7ff27d627d50948969084210850000c7ffc8ff279627950d487690842108500000000c8df2716271541485690842108500000000c8bf31ae31ad0548469084210850000000000000000c89f8006368c841908500006df7605e1bf3441b5148e71084210850000211cc85f31b631b51948d7108421085217cc85fc83f315631551d48b7108421085 >>> (140*(i % 16))) % 2^140
      else
        (0xcc1f200221886e10c840000cc1fcbff00165e17344021084e108840000d0dfd0bfcbdf31a7324021084d10884d2ffd2dfcbdfcbbf3147334021084b10884000063cf63afcb9f2bc7344021084a108840000664f662fcb7f27c732402108491088466ef66cfcb7fcb5f27873340210847108840000672f670fcb3f27073440210845108840000d45fd43fcb1f32b73140210844108840000000000000000caff080010884310864000000006dfb27162715415c5490842108500006dfbcabf27162715455c53908421085000054beca9f27162715515c5290842108500004ffeca7f1bf34417455c421084210850000ca5f31bc31ba31b9255a42108421085ca5fca3f315c315a3159355642108421085 >>> (140*(i % 16))) % 2^140
    else
      if i < 1648 then
        (0x211a2116ce1f441d16484235ce210840000217a2176ce1fcdff441d1748422dce2108400000000cddf1c9a1c96441d54484229ce2108400000000219a2196cdbf441d16484225ce21084000021da21d6cdbfcd9f441d1748421dce2108400000000cd7f1b7a1b76441d54484215ce210840000000010da10d6cd5f441d15484211ce2108400000000000000000000cd3f8006320dce190840000cd3fcd1f001a001632bdd4442209ce110840000ce7fce5f0016ccff32bdc6442209ae11084cf1fceff0016ccffccdf32bdc74422096e1108400004ade4abeccbf001632bdd44422094e1108400004e1e4dfe0016cc9f32bdc64422092e110844ebe4e9e0016cc9fcc7f32bdc7442208ee1108400004efe4edecc5f001632bdd4442208ae110840000cf5fcf3f0016cc3f32bdc54422088e11084 >>> (156*(i % 16))) % 2^156
      else
        (0xd03fd01f315c315a3159355642108e210840000cfff2bdc2bda2bd9455442108e210840000cfdf27dc27da27d9255242108e21084cfdfcfbf279c279a2799354e42108e210840000cf9f271c271a2719454a42108e210840000cf7f10d64f1e441d154842108e210840000000000000000cf5f8006320c8e190840000491e10d6ce9f441d154842116e210840000000000000000cf1f8006320d6e19084000000002196cdbf441d06484225ae21084000021d6cdbfcedf441d0748421dae2108400000000cebf1b76441d44484215ae210840000000010d6ce9f441d05484211ae210840000000000000000ce7f8006320dae19084000048fe44dd485e441d1548423dce210840000ce3f477e44dd441d54484239ce21084 >>> (140*(i % 16))) % 2^140

private def part104 (i : ℕ) : ℕ :=
  if i < 1696 then
    if i < 1680 then
      (0x1a43e57b457b282a884211a421080000000347fc9f689f6485490842348421000068ffe8ef93cd13cc98a72108469084200000000d1bf271a2719414a42108d2108400000001a33eaebc883a229084211a42108000000000000000345fe0018c83234642100002b2f2b1f664f995ee1221104968884256fe56decc9fd13f32bdc3442208ed110840000ae7cae3da23e657ba08844115a22108000345ff457f43fccaf7051088223444210000000000000000686f900110c43688642000000004ffd1b762713445c42152e2108400009ffa36eda13e4e268ab88429dc42108000185fb41fc6dd89c4d51710852b884210000307f086b682fafcba2ae210847108420000d03f31bc31ba31b9255a42108e21084 >>> (139*(i % 16))) % 2^139
    else
      (0xd41f31bc31ba31b9255a42108b21084d41fd3ff315c315a3159355642108b210840000d3df2bdc2bda2bd9455442108b210840000d3bf27dc27da27d9255242108b21084d3bfd39f279c279a2799354e42108b210840000d37f271c271a2719454a42108b210840000d35f5cbe575e441d154842108b210840000000000000000d33f8006320c8b19084d33fd31f581ed0ff32bdc54422088b110840000000000000000d2ff200221886b10c840000000000004ffd2713405c42152d21084000000004ffdd2bf2713415c4214ed210840000000067ded29f2713505c4214ad2108400000000675ed27f31a7415c42108d2108400000000d25f31ba31b9215a42108d210840000d25fd23f315a3159315642108d21084 >>> (140*(i % 16))) % 2^140
  else
    if i < 1712 then
      (0xd61f1c9c2bd62bd55148a710842108400000000219cd5ff27d627d5194897108421084000021dcd5ffd5df279627951d487710842108400000000d5bf1b7c271627155148571084210840000000010dcd59f5f9e5f9d15484710842108400000000000000000000d57f8006370c84190840000d57fd55f001c5e1e5e1dd144270884110840000d69fd67fd53f31ae31adc94426888411084d73fd71fd53fd51f314e314dcd4425888411084000063de63bed4ff2bce2bcdd144250884110840000665e663ed4df27ce27cdc9442488841108466fe66ded4dfd4bf278e278dcd44238884110840000673e671ed49f270e270dd144228884110840000d77fd75fd47f32be32bdc5442208841108400000000000000000000d45f200221886410c840000000068be62d7d27f3147455c42108b21084 >>> (156*(i % 16))) % 2^156
    else
      if i < 1728 then
        (0xd81f2bdc2bda2bd94554421084210840000d7ff27dc27da27d9255242108421084d7ffd7df279c279a2799354e421084210840000d7bf271c271a2719454a421084210840000d79f44de441e441d1548421084210840000000000000000d77f8006320c8419084000062ded6bf314e314d1548459084210840000000000000000d73f8006358c841908400000000d5ff27d627d50948969084210840000d5ffd6ff279627950d487690842108400000000d6df2716271541485690842108400000000d6bf31ae31ad0548469084210840000000000000000d69f8006368c841908400004ff7605e44db441b5148e71084210840000211cd65f31b631b51948d7108421084217cd65fd63f315631551d48b7108421084 >>> (140*(i % 16))) % 2^140
      else
        (0x4ffb27162715415c5490842108400004ffbd8bf27162715455c53908421084000054bed89f27162715515c5290842108400004ffed87f44d74417455c421084210840000d85f31bc31ba31b9255a42108421084d85fd83f315c315a3159355642108421084 >>> (140*(i % 16))) % 2^140

private def record (i : ℕ) : ℕ :=
  if i < 128 then part0 i else
  if i < 256 then part8 i else
  if i < 384 then part16 i else
  if i < 512 then part24 i else
  if i < 640 then part32 i else
  if i < 768 then part40 i else
  if i < 896 then part48 i else
  if i < 1024 then part56 i else
  if i < 1152 then part64 i else
  if i < 1280 then part72 i else
  if i < 1408 then part80 i else
  if i < 1536 then part88 i else
  if i < 1664 then part96 i else
  part104 i

private def entry (i : ℕ) : Entry :=
  let k := if i < 405 then 3 else if i < 1039 then 4 else 5
  let pairs : List (ℕ × ℕ) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
  let pairs := pairs.filter (fun p => p.2 < k)
  let v := record i
  let tail := v >>> (5*pairs.length)
  let mask := tail % 1024
  ⟨pairs.zipIdx.map (fun (p,n) => (p.1,p.2,(v >>> (5*n)) % 32)), fun a =>
    if mask.testBit a then
      let offset := ((List.range a).filter (fun j => mask.testBit j)).length
      (tail >>> (10 + 16*offset)) % 65536 else 0⟩

private def database (i : ℕ) := entry (i % 1734)

private def Checked (lo hi : ℕ) := ∀ i, lo ≤ i → i < hi → checkRow database i = true

private theorem combine {lo mid hi : ℕ} (a : Checked lo mid) (b : Checked mid hi) :
    Checked lo hi := fun i h₁ h₂ => if h : i < mid then a i h₁ h else b i (by omega) h₂

private theorem interval (lo n : ℕ)
    (h : (List.range n).all (fun j => checkRow database (lo+j)) = true) :
    Checked lo (lo+n) := by
  intro i h₁ h₂
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h₁
  exact List.all_eq_true.mp h d (List.mem_range.mpr (by omega))

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 8192 in
private theorem rowsChecked : Checked 0 1734 := by
  have ok0 := interval 0 16 (by decide +kernel)
  have ok16 := interval 16 16 (by decide +kernel)
  have ok32 := interval 32 16 (by decide +kernel)
  have ok48 := interval 48 16 (by decide +kernel)
  have ok64 := interval 64 16 (by decide +kernel)
  have ok80 := interval 80 16 (by decide +kernel)
  have ok96 := interval 96 16 (by decide +kernel)
  have ok112 := interval 112 16 (by decide +kernel)
  have ok128 := interval 128 16 (by decide +kernel)
  have ok144 := interval 144 16 (by decide +kernel)
  have ok160 := interval 160 16 (by decide +kernel)
  have ok176 := interval 176 16 (by decide +kernel)
  have ok192 := interval 192 16 (by decide +kernel)
  have ok208 := interval 208 16 (by decide +kernel)
  have ok224 := interval 224 16 (by decide +kernel)
  have ok240 := interval 240 16 (by decide +kernel)
  have ok256 := interval 256 16 (by decide +kernel)
  have ok272 := interval 272 16 (by decide +kernel)
  have ok288 := interval 288 16 (by decide +kernel)
  have ok304 := interval 304 16 (by decide +kernel)
  have ok320 := interval 320 16 (by decide +kernel)
  have ok336 := interval 336 16 (by decide +kernel)
  have ok352 := interval 352 16 (by decide +kernel)
  have ok368 := interval 368 16 (by decide +kernel)
  have ok384 := interval 384 16 (by decide +kernel)
  have ok400 := interval 400 16 (by decide +kernel)
  have ok416 := interval 416 16 (by decide +kernel)
  have ok432 := interval 432 16 (by decide +kernel)
  have ok448 := interval 448 16 (by decide +kernel)
  have ok464 := interval 464 16 (by decide +kernel)
  have ok480 := interval 480 16 (by decide +kernel)
  have ok496 := interval 496 16 (by decide +kernel)
  have ok512 := interval 512 16 (by decide +kernel)
  have ok528 := interval 528 16 (by decide +kernel)
  have ok544 := interval 544 16 (by decide +kernel)
  have ok560 := interval 560 16 (by decide +kernel)
  have ok576 := interval 576 16 (by decide +kernel)
  have ok592 := interval 592 16 (by decide +kernel)
  have ok608 := interval 608 16 (by decide +kernel)
  have ok624 := interval 624 16 (by decide +kernel)
  have ok640 := interval 640 16 (by decide +kernel)
  have ok656 := interval 656 16 (by decide +kernel)
  have ok672 := interval 672 16 (by decide +kernel)
  have ok688 := interval 688 16 (by decide +kernel)
  have ok704 := interval 704 16 (by decide +kernel)
  have ok720 := interval 720 16 (by decide +kernel)
  have ok736 := interval 736 16 (by decide +kernel)
  have ok752 := interval 752 16 (by decide +kernel)
  have ok768 := interval 768 16 (by decide +kernel)
  have ok784 := interval 784 16 (by decide +kernel)
  have ok800 := interval 800 16 (by decide +kernel)
  have ok816 := interval 816 16 (by decide +kernel)
  have ok832 := interval 832 16 (by decide +kernel)
  have ok848 := interval 848 16 (by decide +kernel)
  have ok864 := interval 864 16 (by decide +kernel)
  have ok880 := interval 880 16 (by decide +kernel)
  have ok896 := interval 896 16 (by decide +kernel)
  have ok912 := interval 912 16 (by decide +kernel)
  have ok928 := interval 928 16 (by decide +kernel)
  have ok944 := interval 944 16 (by decide +kernel)
  have ok960 := interval 960 16 (by decide +kernel)
  have ok976 := interval 976 16 (by decide +kernel)
  have ok992 := interval 992 16 (by decide +kernel)
  have ok1008 := interval 1008 16 (by decide +kernel)
  have ok1024 := interval 1024 16 (by decide +kernel)
  have ok1040 := interval 1040 16 (by decide +kernel)
  have ok1056 := interval 1056 16 (by decide +kernel)
  have ok1072 := interval 1072 16 (by decide +kernel)
  have ok1088 := interval 1088 16 (by decide +kernel)
  have ok1104 := interval 1104 16 (by decide +kernel)
  have ok1120 := interval 1120 16 (by decide +kernel)
  have ok1136 := interval 1136 16 (by decide +kernel)
  have ok1152 := interval 1152 16 (by decide +kernel)
  have ok1168 := interval 1168 16 (by decide +kernel)
  have ok1184 := interval 1184 16 (by decide +kernel)
  have ok1200 := interval 1200 16 (by decide +kernel)
  have ok1216 := interval 1216 16 (by decide +kernel)
  have ok1232 := interval 1232 16 (by decide +kernel)
  have ok1248 := interval 1248 16 (by decide +kernel)
  have ok1264 := interval 1264 16 (by decide +kernel)
  have ok1280 := interval 1280 16 (by decide +kernel)
  have ok1296 := interval 1296 16 (by decide +kernel)
  have ok1312 := interval 1312 16 (by decide +kernel)
  have ok1328 := interval 1328 16 (by decide +kernel)
  have ok1344 := interval 1344 16 (by decide +kernel)
  have ok1360 := interval 1360 16 (by decide +kernel)
  have ok1376 := interval 1376 16 (by decide +kernel)
  have ok1392 := interval 1392 16 (by decide +kernel)
  have ok1408 := interval 1408 16 (by decide +kernel)
  have ok1424 := interval 1424 16 (by decide +kernel)
  have ok1440 := interval 1440 16 (by decide +kernel)
  have ok1456 := interval 1456 16 (by decide +kernel)
  have ok1472 := interval 1472 16 (by decide +kernel)
  have ok1488 := interval 1488 16 (by decide +kernel)
  have ok1504 := interval 1504 16 (by decide +kernel)
  have ok1520 := interval 1520 16 (by decide +kernel)
  have ok1536 := interval 1536 16 (by decide +kernel)
  have ok1552 := interval 1552 16 (by decide +kernel)
  have ok1568 := interval 1568 16 (by decide +kernel)
  have ok1584 := interval 1584 16 (by decide +kernel)
  have ok1600 := interval 1600 16 (by decide +kernel)
  have ok1616 := interval 1616 16 (by decide +kernel)
  have ok1632 := interval 1632 16 (by decide +kernel)
  have ok1648 := interval 1648 16 (by decide +kernel)
  have ok1664 := interval 1664 16 (by decide +kernel)
  have ok1680 := interval 1680 16 (by decide +kernel)
  have ok1696 := interval 1696 16 (by decide +kernel)
  have ok1712 := interval 1712 16 (by decide +kernel)
  have ok1728 := interval 1728 6 (by decide +kernel)
  exact (@combine 0 864 1734 (@combine 0 432 864 (@combine 0 208 432 (@combine 0 96 208 (@combine 0 48 96 (@combine 0 16 48 ok0 (@combine 16 32 48 ok16 ok32)) (@combine 48 64 96 ok48 (@combine 64 80 96 ok64 ok80))) (@combine 96 144 208 (@combine 96 112 144 ok96 (@combine 112 128 144 ok112 ok128)) (@combine 144 176 208 (@combine 144 160 176 ok144 ok160) (@combine 176 192 208 ok176 ok192)))) (@combine 208 320 432 (@combine 208 256 320 (@combine 208 224 256 ok208 (@combine 224 240 256 ok224 ok240)) (@combine 256 288 320 (@combine 256 272 288 ok256 ok272) (@combine 288 304 320 ok288 ok304))) (@combine 320 368 432 (@combine 320 336 368 ok320 (@combine 336 352 368 ok336 ok352)) (@combine 368 400 432 (@combine 368 384 400 ok368 ok384) (@combine 400 416 432 ok400 ok416))))) (@combine 432 640 864 (@combine 432 528 640 (@combine 432 480 528 (@combine 432 448 480 ok432 (@combine 448 464 480 ok448 ok464)) (@combine 480 496 528 ok480 (@combine 496 512 528 ok496 ok512))) (@combine 528 576 640 (@combine 528 544 576 ok528 (@combine 544 560 576 ok544 ok560)) (@combine 576 608 640 (@combine 576 592 608 ok576 ok592) (@combine 608 624 640 ok608 ok624)))) (@combine 640 752 864 (@combine 640 688 752 (@combine 640 656 688 ok640 (@combine 656 672 688 ok656 ok672)) (@combine 688 720 752 (@combine 688 704 720 ok688 ok704) (@combine 720 736 752 ok720 ok736))) (@combine 752 800 864 (@combine 752 768 800 ok752 (@combine 768 784 800 ok768 ok784)) (@combine 800 832 864 (@combine 800 816 832 ok800 ok816) (@combine 832 848 864 ok832 ok848)))))) (@combine 864 1296 1734 (@combine 864 1072 1296 (@combine 864 960 1072 (@combine 864 912 960 (@combine 864 880 912 ok864 (@combine 880 896 912 ok880 ok896)) (@combine 912 928 960 ok912 (@combine 928 944 960 ok928 ok944))) (@combine 960 1008 1072 (@combine 960 976 1008 ok960 (@combine 976 992 1008 ok976 ok992)) (@combine 1008 1040 1072 (@combine 1008 1024 1040 ok1008 ok1024) (@combine 1040 1056 1072 ok1040 ok1056)))) (@combine 1072 1184 1296 (@combine 1072 1120 1184 (@combine 1072 1088 1120 ok1072 (@combine 1088 1104 1120 ok1088 ok1104)) (@combine 1120 1152 1184 (@combine 1120 1136 1152 ok1120 ok1136) (@combine 1152 1168 1184 ok1152 ok1168))) (@combine 1184 1232 1296 (@combine 1184 1200 1232 ok1184 (@combine 1200 1216 1232 ok1200 ok1216)) (@combine 1232 1264 1296 (@combine 1232 1248 1264 ok1232 ok1248) (@combine 1264 1280 1296 ok1264 ok1280))))) (@combine 1296 1520 1734 (@combine 1296 1408 1520 (@combine 1296 1344 1408 (@combine 1296 1312 1344 ok1296 (@combine 1312 1328 1344 ok1312 ok1328)) (@combine 1344 1376 1408 (@combine 1344 1360 1376 ok1344 ok1360) (@combine 1376 1392 1408 ok1376 ok1392))) (@combine 1408 1456 1520 (@combine 1408 1424 1456 ok1408 (@combine 1424 1440 1456 ok1424 ok1440)) (@combine 1456 1488 1520 (@combine 1456 1472 1488 ok1456 ok1472) (@combine 1488 1504 1520 ok1488 ok1504)))) (@combine 1520 1632 1734 (@combine 1520 1568 1632 (@combine 1520 1536 1568 ok1520 (@combine 1536 1552 1568 ok1536 ok1552)) (@combine 1568 1600 1632 (@combine 1568 1584 1600 ok1568 ok1584) (@combine 1600 1616 1632 ok1600 ok1616))) (@combine 1632 1680 1734 (@combine 1632 1648 1680 ok1632 (@combine 1648 1664 1680 ok1648 ok1664)) (@combine 1680 1712 1734 (@combine 1680 1696 1712 ok1680 ok1696) (@combine 1712 1728 1734 ok1712 ok1728)))))))

private theorem certificateValid (i : ℕ) : checkRow database i := by
  have h := rowsChecked (i % 1734) (Nat.zero_le _) (Nat.mod_lt _ (by decide))
  have he : database (i % 1734) = database i := by simp [database]
  unfold checkRow at h ⊢
  rwa [he] at h

theorem fiveImpossible (w : List Event) :
    ¬ ∀ i j : Fin 5, i < j → accepts i.val j.val w 0 = true := by
  intro hh
  apply checkedRejects database certificateValid w 1039 id Function.injective_id
  have hc : (database 1039).clause.all (fun p => p.1 < p.2.1 && p.2.1 < 5 && p.2.2 == 0) := by
    decide +kernel
  intro p hp
  obtain ⟨hs, hz⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hc p hp)
  obtain ⟨hi,hj⟩ := Bool.and_eq_true_iff.mp hs
  have hi' := of_decide_eq_true hi
  have hj' := of_decide_eq_true hj
  rw [beq_iff_eq.mp hz]
  exact hh ⟨_,hi'.trans hj'⟩ ⟨_,hj'⟩ hi'

structure MarkedWord where
  coords : Finset ℕ
  mark : ℕ → Bool

def scan (x y : MarkedWord) : List ℕ → ℕ → Bool
  | [], s => s == 22
  | t :: ts, s => scan x y ts (if t ∈ x.coords then consume s false (x.mark t)
      else if t ∈ y.coords then consume s true (y.mark t) else s)

def Matches (x y : MarkedWord) : Prop :=
  Disjoint x.coords y.coords ∧ ∃ b : ℕ, ∀ m ≥ b, scan x y (List.range m) 0 = true

def blueGraph {α : Type*} [LinearOrder α] (word : α → MarkedWord) : SimpleGraph α where
  Adj x y := (x < y ∧ Matches (word x) (word y)) ∨ (y < x ∧ Matches (word y) (word x))
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun x h => by rcases h with h | h <;> exact (lt_irrefl x) h.1⟩

private theorem readTrace (x y : MarkedWord) (i j : ℕ) (tag : ℕ → Event)
    (hx : ∀ t, (tag t).1 = i ↔ t ∈ x.coords)
    (hy : ∀ t, (tag t).1 = j ↔ t ∈ y.coords)
    (mx : ∀ t ∈ x.coords, (tag t).2 = x.mark t)
    (my : ∀ t ∈ y.coords, (tag t).2 = y.mark t)
    (ts : List ℕ) (s : ℕ) : accepts i j (ts.map tag) s = scan x y ts s := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, accepts, ih, scan, advance, hx, hy]
    by_cases h : t ∈ x.coords
    · simp [h, mx t h]
    · by_cases h' : t ∈ y.coords
      · simp [h,h',my t h']
      · simp [h,h']

private noncomputable def tag (v : Fin 5 → MarkedWord) (t : ℕ) : Event :=
  if h : ∃ i, t ∈ (v i).coords then (h.choose.val, (v h.choose).mark t) else (5,false)

private theorem tagSpec (v : Fin 5 → MarkedWord)
    (hd : ∀ i j, i ≠ j → Disjoint (v i).coords (v j).coords) (i : Fin 5) (t : ℕ) :
    ((tag v t).1 = i.val ↔ t ∈ (v i).coords) ∧
      (t ∈ (v i).coords → (tag v t).2 = (v i).mark t) := by
  classical
  unfold tag
  split
  next h =>
    have uniq (hm : t ∈ (v i).coords) : h.choose = i := by
      by_contra hn
      exact Finset.disjoint_left.mp (hd _ _ hn) h.choose_spec hm
    constructor
    · constructor
      · intro he
        exact (Fin.ext he : h.choose = i) ▸ h.choose_spec
      · intro hm
        exact congrArg Fin.val (uniq hm)
    · intro hm
      exact congrArg (fun j => (v j).mark t) (uniq hm)
  next h =>
    have hn : t ∉ (v i).coords := fun ht => h ⟨i,ht⟩
    have hi := i.isLt
    simp [hn, show 5 ≠ i.val by omega]

theorem blueGraph_cliqueFree {α : Type*} [LinearOrder α] (word : α → MarkedWord) :
    (blueGraph word).CliqueFree 5 := by
  classical
  intro s hs
  let u := s.orderEmbOfFin hs.2
  let v : Fin 5 → MarkedWord := fun i => word (u i)
  have hp (i j : Fin 5) (hij : i < j) : Matches (v i) (v j) := by
    have lt' := u.strictMono hij
    have hh := hs.1 (s.orderEmbOfFin_mem hs.2 i) (s.orderEmbOfFin_mem hs.2 j) lt'.ne
    exact hh.elim And.right (fun h => (lt_asymm lt' h.1).elim)
  have hd (i j : Fin 5) (hne : i ≠ j) : Disjoint (v i).coords (v j).coords := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hp i j h).1
    · exact (hp j i h).1.symm
  have hb (p : Fin 5 × Fin 5) : ∃ b : ℕ, ∀ m ≥ b, p.1 < p.2 →
      scan (v p.1) (v p.2) (List.range m) 0 = true := by
    by_cases hij : p.1 < p.2
    · obtain ⟨b,h⟩ := (hp _ _ hij).2
      exact ⟨b,fun m hm _ => h m hm⟩
    · exact ⟨0,fun _ _ h => (hij h).elim⟩
  choose b hb using hb
  let m := Finset.univ.sup b
  apply fiveImpossible ((List.range m).map (tag v))
  intro i j hij
  rw [readTrace (v i) (v j) _ _ _ (fun t => (tagSpec v hd i t).1)
    (fun t => (tagSpec v hd j t).1) (fun t => (tagSpec v hd i t).2)
    (fun t => (tagSpec v hd j t).2)]
  exact hb (i,j) m (Finset.le_sup (f := b) (Finset.mem_univ _)) hij

end Larson.Pattern

namespace Larson.Words

def ExactReady : List Bool → Language → Prop
  | [], L => L []
  | b :: bs, L => ∀ bound : ℕ, ∃ i ≥ bound, ∃ m : Bool, ∃ s : List Token,
      marked ((i,m)::s) = b ∧ ExactReady bs (shift L ((i,m)::s))

private theorem exactMono (bs : List Bool) {L R : Language} (h : ∀ s, L s → R s)
    (w : ExactReady bs L) : ExactReady bs R := by
  induction bs generalizing L R with
  | nil => exact h [] w
  | cons b bs ih =>
    intro n
    obtain ⟨i,hi,m,s,hb,hw⟩ := w n
    exact ⟨i,hi,m,s,hb,ih (fun _ => h _) hw⟩

def closedLang (L : Language) : Language := fun s => ∃ raw, L raw ∧ s = raw ++ [(0,true)]

theorem closeReady (bs : List Bool) (L : Language) (hne : bs ≠ []) (h : Ready bs L) :
    ExactReady bs (closedLang L) := by
  induction bs generalizing L with
  | nil => contradiction
  | cons b bs ih =>
    intro cut
    obtain ⟨i,hi,m,s,hb,hw⟩ := h cut
    cases bs with
    | nil =>
      have he : true = b := hb
      refine ⟨i,hi,m,s ++ [(0,true)],by simp [marked,← he],?_⟩
      refine ⟨(i,m)::s,by simpa [Ready,shift] using hw,by simp⟩
    | cons b' tail =>
      exact ⟨i,hi,m,s,hb,exactMono _ (fun t ⟨u,hu,ht⟩ =>
        ⟨((i,m)::s) ++ u,hu,by simp [ht,List.append_assoc]⟩)
        (ih _ (by simp) hw)⟩

abbrev Tape := List (Option Bool)
abbrev Timeline := List (Option (Bool × Bool))

def tape : List Token → Tape
  | [] => []
  | (d,m)::s => List.replicate d none ++ some m :: tape s

private theorem tapeAppend (s t : List Token) : tape (s++t) = tape s ++ tape t := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [tape,ih,List.append_assoc]

private theorem tapeHits (s : List Token) : (tape s).filterMap id = s.map Prod.snd := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [tape]; exact ih

def see (side : Bool) (v : Option (Bool × Bool)) : Option Bool :=
  v.bind fun p => if p.1 = side then some p.2 else none

def paint (side : Bool) (r : Tape) : Timeline := r.map (Option.map (Prod.mk side))

private theorem seePaint (s t : Bool) (r : Tape) :
    (paint s r).map (see t) = if s = t then r else List.replicate r.length none := by
  induction r with
  | nil => simp [paint]
  | cons a r ih =>
    by_cases eq : s = t <;> cases a <;> simp [paint,see,eq,List.replicate_succ] at ih ⊢ <;> exact ih

inductive Runs : List (Bool × Bool) → Timeline → Prop
  | nil : Runs [] []
  | cons {side b as z} (r : Tape) (nonempty : r.filterMap id ≠ [])
      (bit : (r.filterMap id).any id = b) (tail : Runs as z) :
      Runs ((side,b)::as) (paint side r ++ z)

def sideMoves (s : Bool) (a : List (Bool × Bool)) :=
  a.filterMap fun p => if p.1 = s then some p.2 else none

theorem playSchedule (actions : List (Bool × Bool)) (L : Bool → Language) (idle : Bool → ℕ)
    (h : ∀ s, ExactReady (sideMoves s actions) (L s)) :
    ∃ z, Runs actions z ∧ ∀ s, ∃ raw extra, L s raw ∧
      List.replicate (idle s) none ++ z.map (see s) = tape raw ++ List.replicate extra none := by
  induction actions generalizing L idle with
  | nil => exact ⟨[],.nil,fun s => ⟨[],idle s,h s,by simp [tape]⟩⟩
  | cons a acts ih =>
    obtain ⟨s,b⟩ := a
    have hs := h s
    simp only [sideMoves,List.filterMap_cons,if_true] at hs
    obtain ⟨d,hd,m,rest,bit,ready⟩ := hs (idle s)
    let seg : List Token := (d,m)::rest
    let r : Tape := List.replicate (d-idle s) none ++ some m :: tape rest
    let L' (j : Bool) := if j = s then shift (L j) seg else L j
    let idle' (j : Bool) := if j = s then 0 else idle j + r.length
    have nextReady (j : Bool) : ExactReady (sideMoves j acts) (L' j) := by
      by_cases hj : j = s
      · subst j
        simpa only [L',if_true,seg,sideMoves] using ready
      · simpa [L',hj,sideMoves,Ne.symm hj] using h j
    obtain ⟨z,hz,ends⟩ := ih L' idle' nextReady
    have hits : r.filterMap id = m :: rest.map Prod.snd := by simp [r]; exact tapeHits rest
    refine ⟨paint s r ++ z,.cons r (by rw [hits]; simp) ?_ hz,?_⟩
    · rw [hits]
      simpa [marked,List.any_map,Function.comp_def] using bit
    · intro j
      obtain ⟨raw,extra,hl,he⟩ := ends j
      by_cases hj : j = s
      · subst j
        refine ⟨seg++raw,extra,by simpa [L',shift] using hl,?_⟩
        have he' : z.map (see s) = tape raw ++ List.replicate extra none := by simpa [idle'] using he
        have before : List.replicate (idle s) none ++ r = tape seg := by
          dsimp only [r,seg,tape]
          rw [← List.append_assoc,List.replicate_append_replicate,Nat.add_sub_of_le hd]
        rw [List.map_append,seePaint,if_pos rfl,← List.append_assoc,before,he',tapeAppend,List.append_assoc]
      · refine ⟨raw,extra,by simpa [L',hj] using hl,?_⟩
        rw [List.map_append,seePaint,if_neg (Ne.symm hj),← List.append_assoc,List.replicate_append_replicate]
        simpa [idle',hj] using he

end Larson.Words

namespace Larson.Words
open Larson.Pattern

def observed (z : Timeline) : List Event :=
  z.filterMap (Option.map fun p => (p.1.toNat,p.2))

private theorem consumeBound (s : ℕ) (hs : s ≤ 31) (side a : Bool) :
    consume s side a ≤ 31 := by
  have finite : ∀ i : Fin 32, ∀ b m : Bool, consume i.val b m ≤ 31 := by decide +kernel
  exact finite ⟨s,by omega⟩ side a

private theorem collapse (s : ℕ) (hs : s ≤ 31) (side a b : Bool) :
    consume (consume s side a) side b = consume s side (a || b) := by
  have finite : ∀ i : Fin 32, ∀ d x y : Bool,
      consume (consume i.val d x) d y = consume i.val d (x || y) := by decide +kernel
  exact finite ⟨s,by omega⟩ side a b

private theorem owned (s : ℕ) (side m : Bool) :
    advance 0 1 s (side.toNat,m) = consume s side m := by cases side <;> rfl

private theorem readSame (side : Bool) (marks : List Bool) (a : Bool) (tail : List Event)
    (s : ℕ) (hs : s ≤ 31) :
    accepts 0 1 (((a::marks).map (fun m => (side.toNat,m))) ++ tail) s =
      accepts 0 1 tail (consume s side ((a::marks).any id)) := by
  induction marks generalizing a s with
  | nil => simp [accepts,owned]
  | cons b rest ih =>
    change accepts 0 1 (((b::rest).map _) ++ tail) (advance 0 1 s (side.toNat,a)) = _
    rw [owned, ih _ _ (consumeBound _ hs _ _), collapse _ hs]
    rfl

private theorem observedPaint (side : Bool) (r : Tape) :
    observed (paint side r) = (r.filterMap id).map (fun m => (side.toNat,m)) := by
  induction r with
  | nil => rfl
  | cons m r ih =>
    cases m <;> simp [observed,paint] at ih ⊢ <;> exact ih

theorem runsRead {actions z} (h : Runs actions z) (s : ℕ) (hs : s ≤ 31) :
    accepts 0 1 (observed z) s =
      accepts 0 1 (actions.map (fun p => (p.1.toNat,p.2))) s := by
  induction h generalizing s with
  | nil => rfl
  | @cons side b as z r hn hb _ ih =>
    have he : observed (paint side r ++ z) = observed (paint side r) ++ observed z :=
      List.filterMap_append ..
    rw [he, observedPaint]
    cases hm : r.filterMap id with
    | nil => exact (hn hm).elim
    | cons m ms =>
      rw [hm] at hb
      rw [readSame _ _ _ _ _ hs,hb,ih _ (consumeBound _ hs _ _)]
      simp [accepts,owned]

def atTick {α : Type} (x : List (Option α)) (i : ℕ) := x[i]?.join

private theorem atPad {α : Type} (x : List (Option α)) (b i : ℕ) :
    atTick (x ++ List.replicate b none) i = atTick x i := by
  by_cases h : i < x.length
  · simp [atTick,List.getElem?_append_left h]
  · simp only [atTick,List.getElem?_append_right (Nat.le_of_not_gt h),List.getElem?_replicate,
      List.getElem?_eq_none (Nat.le_of_not_gt h)]
    split <;> rfl

private theorem seeAt (s : Bool) (z : Timeline) (i : ℕ) :
    atTick (z.map (see s)) i = see s (atTick z i) := by
  simp only [atTick,List.getElem?_map]
  cases h : z[i]? <;> rfl

def fromTape (x : Tape) : MarkedWord :=
  ⟨(Finset.range x.length).filter (fun i => (atTick x i).isSome), fun i => (atTick x i).getD false⟩

private theorem memTape (x : Tape) (i : ℕ) :
    i ∈ (fromTape x).coords ↔ (atTick x i).isSome = true := by
  simp only [fromTape,Finset.mem_filter,Finset.mem_range,and_iff_right_iff_imp]
  contrapose!
  intro h
  simp [atTick,List.getElem?_eq_none h]

private theorem tickRange (z : Timeline) (m : ℕ) (hm : z.length ≤ m) :
    (List.range m).map (atTick z) = z ++ List.replicate (m-z.length) none := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    by_cases h : i < z.length
    · simp [atTick,h,List.getElem_append_left h]
    · simp [atTick,List.getElem?_eq_none (by omega : z.length ≤ i),List.getElem_append_right (by omega : z.length ≤ i)]

theorem matchesOfTape (x y : Tape) (z : Timeline) (nx ny : ℕ)
    (hx : z.map (see false) = x ++ List.replicate nx none)
    (hy : z.map (see true) = y ++ List.replicate ny none)
    (hblue : accepts 0 1 (observed z) 0 = true) :
    Matches (fromTape x) (fromTape y) := by
  have xx (i : ℕ) : atTick x i = see false (atTick z i) := by rw [← seeAt, hx,atPad]
  have yy (i : ℕ) : atTick y i = see true (atTick z i) := by rw [← seeAt, hy,atPad]
  have hscan (l : List ℕ) (s : ℕ) : scan (fromTape x) (fromTape y) l s =
      accepts 0 1 (observed (l.map (atTick z))) s := by
    induction l generalizing s with
    | nil => rfl
    | cons i is ih =>
      simp only [scan, ih, memTape, show (fromTape x).mark i = (atTick x i).getD false from rfl,
        show (fromTape y).mark i = (atTick y i).getD false from rfl,xx,yy,List.map_cons]
      cases he : atTick z i with
      | none => rfl
      | some p => obtain ⟨b,m⟩ := p; cases b <;> rfl
  constructor
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    rw [memTape,xx] at hi
    rw [memTape,yy] at hj
    cases he : atTick z i with
    | none => simp [he,see] at hi
    | some p => obtain ⟨s,m⟩ := p; cases s <;> simp [he,see] at hi hj
  · refine ⟨z.length,fun m hm => ?_⟩
    rw [hscan,tickRange z m hm]
    simpa [observed] using hblue

end Larson.Words

namespace Larson.Words
open Ordinal Order Larson.Pattern

def actions : List (Bool × Bool) :=
  [(false,true),(true,true),(false,false),(true,false),(false,true),(true,false),
   (false,true),(true,false),(false,false),(true,true),(false,true)]

def wholeTape (x : Word) := tape (wordTokens x ++ [(0,true)])

private theorem tapeRoot (x : Word) (i : ℕ) (hi : i ≤ x.1) :
    atTick (wholeTape x) i = if i = x.1 then some true else none := by
  change atTick (List.replicate x.1 none ++ some true :: _) i = _
  rcases hi.eq_or_lt with h | h
  · subst i
    simp [atTick]
  · simp [atTick,List.getElem?_append,h,h.ne]

private theorem rootOrder {z : Timeline} (run : Runs actions z) (x y : Word) (nx ny : ℕ)
    (hx : z.map (see false) = wholeTape x ++ List.replicate nx none)
    (hy : z.map (see true) = wholeTape y ++ List.replicate ny none) : x.1 < y.1 := by
  cases run with
  | cons r hn _ _ =>
    simp [seePaint] at hx hy
    obtain ⟨m,hm⟩ := List.exists_mem_of_ne_nil _ hn
    obtain ⟨val,hval,he⟩ := List.mem_filterMap.mp hm
    obtain ⟨i,hi,hev⟩ := List.getElem_of_mem hval
    have ht : atTick r i = some m := by simp only [atTick,List.getElem?_eq_getElem hi,Option.join_some,hev]; exact he
    have hx' : atTick (wholeTape x) i = some m := by
      rw [← atPad _ nx,← hx]
      simpa only [atTick,List.getElem?_append_left hi] using ht
    have hl : x.1 ≤ i := by
      by_contra! h
      rw [tapeRoot _ _ h.le,if_neg h.ne] at hx'
      contradiction
    have hr : r.length ≤ y.1 := by
      by_contra! h
      have ht' := tapeRoot y y.1 le_rfl
      rw [← atPad _ ny,← hy] at ht'
      simp [atTick,List.getElem?_append,h] at ht'
    exact hl.trans_lt (hi.trans_le hr)

theorem forcedPair (w : Set Word) (hw : typeLT w = typeLT Word) :
    ∃ x ∈ w, ∃ y ∈ w, (blueGraph (fun u : Word => fromTape (wholeTape u))).Adj x y := by
  let L : Language := fun s => ∃ x ∈ w, wordTokens x = s
  have hx : Ready (sideMoves false actions) L := rootPlan w hw [1,0,1]
  have hy : Ready (sideMoves true actions) L := rootPlan w hw [3]
  have h (b : Bool) : ExactReady (sideMoves b actions) (closedLang L) := by
    cases b
    · exact closeReady _ _ (by decide) hx
    · exact closeReady _ _ (by decide) hy
  obtain ⟨z,hz,hends⟩ := playSchedule actions (fun _ => closedLang L) (fun _ => 0) h
  obtain ⟨_,nx,⟨_,⟨x,hx,rfl⟩,rfl⟩,hxx⟩ := hends false
  obtain ⟨_,ny,⟨_,⟨y,hy,rfl⟩,rfl⟩,hyy⟩ := hends true
  have ht := rootOrder hz x y nx ny hxx hyy
  have hblue : accepts 0 1 (observed z) 0 = true := by rw [runsRead hz 0 (by decide)]; decide +kernel
  exact ⟨x,hx,y,hy,Or.inl ⟨Sigma.Lex.left _ _ ht, matchesOfTape _ _ z nx ny hxx hyy hblue⟩⟩

end Larson.Words

open Ordinal
namespace Larson

theorem counterexampleOfGraph {X : Type} [LinearOrder X] [WellFoundedLT X] (a : Ordinal.{0})
    (ha : typeLT X = a) (G : SimpleGraph X) (hG : G.CliqueFree 5)
    (pair : ∀ w : Set X, typeLT w = typeLT X → ∃ x ∈ w, ∃ y ∈ w, G.Adj x y) :
    ¬ Erdos118.OrdinalRamsey a a 5 := by
  classical
  obtain ⟨e⟩ : Nonempty (((· < ·) : a.ToType → a.ToType → Prop) ≃r
      ((· < ·) : X → X → Prop)) := type_eq.mp ((type_toType a).trans ha.symm)
  let B := G.comap e
  have transfer (s : Set a.ToType) : typeLT (e '' s) = typeLT s := by
    let f : ((· < ·) : s → s → Prop) ≃r ((· < ·) : (e '' s) → (e '' s) → Prop) :=
      { toEquiv := e.toEquiv.image s
        map_rel_iff' := e.map_rel_iff }
    exact f.ordinalType_congr.symm
  intro h
  obtain ⟨s,hs,ht⟩ | ⟨s,hs,ht⟩ := h Bᶜ B isCompl_compl.symm
  · obtain ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,hxy⟩ :=
      pair (e '' s) ((transfer s).trans (ht.trans ha.symm))
    have hne : x ≠ y := fun he => hxy.ne (congrArg e he)
    exact (hs hx hy hne).2 hxy
  · let w := e '' s
    have hcl : G.IsClique w := by
      rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ hne
      exact hs hx hy (fun he => hne (congrArg e he))
    have hc := (card_eq_nat (n := 5)).mpr ((transfer s).trans ht)
    rw [card_type] at hc
    obtain ⟨F,hF,hn⟩ := Cardinal.mk_set_eq_nat_iff_finset.mp hc
    exact hG F ⟨hF ▸ hcl,hn⟩

theorem negative : ¬ Erdos118.OrdinalRamsey ((ω : Ordinal.{u}) ^ (ω ^ (2 : Ordinal)))
    (ω ^ (ω ^ (2 : Ordinal))) 5 := by
  intro h
  exact counterexampleOfGraph _ Words.wordType
    (Pattern.blueGraph (fun x : Words.Word => Words.fromTape (Words.wholeTape x)))
    (Pattern.blueGraph_cliqueFree _) Words.forcedPair ((concreteRamseyLift.{u} 5).mp h)

end Larson

open Filter
namespace Larson.Game

inductive Front where
  | leaf : Bool → Front
  | fork : (ℕ → Front) → Front

def Front.next : Front → ℕ → Front
  | .leaf c, _ => .leaf c
  | .fork f, i => f i

noncomputable def Front.color : Front → Bool
  | .leaf c => c
  | .fork f => by
    classical
    exact decide (∀ᶠ i in hyperfilter ℕ, (f i).color = true)

private theorem keepColor (t : Front) :
    ∀ᶠ i in hyperfilter ℕ, (t.next i).color = t.color := by
  cases t with
  | leaf c => exact Eventually.of_forall fun _ => rfl
  | fork f =>
    classical
    rcases (hyperfilter ℕ).eventually_or.mp
        (Eventually.of_forall (fun i => Bool.eq_false_or_eq_true (f i).color)) with h | h
    · simpa only [Front.next, Front.color, decide_eq_true h] using h
    · have hn : ¬ ∀ᶠ i in hyperfilter ℕ, (f i).color = true := by
        intro hh
        obtain ⟨i,hi,hi'⟩ := (h.and hh).exists
        simp [hi] at hi'
      simpa only [Front.next, Front.color, decide_eq_false hn] using h

private theorem chooseMove (s : Finset Front) (b : ℕ) :
    ∃ n > b, ∀ t ∈ s, (t.next n).color = t.color := by
  have ha := (eventually_all_finset s).mpr fun t _ => keepColor t
  have hb : ∀ᶠ n in hyperfilter ℕ, b < n :=
    (eventually_gt_atTop b).filter_mono Nat.hyperfilter_le_atTop
  exact (hb.and ha).exists

private noncomputable def step (p : ℕ × Finset Front) : ℕ × Finset Front := by
  classical
  let n := (chooseMove p.2 p.1).choose
  exact (n,p.2 ∪ p.2.image (fun t => t.next n))

private noncomputable def stage (t : Front) : ℕ → ℕ × Finset Front
  | 0 => (0,{t})
  | n+1 => step (stage t n)

inductive PlayTree where
  | done : Bool → PlayTree
  | architect : (ℕ → PlayTree) → PlayTree
  | builder : (ℕ → PlayTree) → PlayTree

def PlayTree.move : PlayTree → ℕ → PlayTree
  | .done c, _ => .done c
  | .architect f, i | .builder f, i => f i

noncomputable def PlayTree.value : PlayTree → Bool
  | .done b => b
  | .architect f => by classical exact decide (∃ n, (f n).value = true)
  | .builder f => by classical exact decide (∀ᶠ n in hyperfilter ℕ, (f n).value = true)

def PlayTree.position (t : PlayTree) (p : List ℕ) := p.foldl PlayTree.move t

def stableMove (q : PlayTree) (n : ℕ) : Prop :=
  match q with
  | .builder f => (f n).value = q.value
  | _ => True

private theorem stableOften (q : PlayTree) : ∀ᶠ n in hyperfilter ℕ, stableMove q n := by
  cases q with
  | done _ | architect _ => exact Eventually.of_forall fun _ => trivial
  | builder f =>
    classical
    by_cases h : ∀ᶠ n in hyperfilter ℕ, (f n).value = true
    · simpa only [stableMove, PlayTree.value, decide_eq_true h] using h
    · have hh := (hyperfilter ℕ).em (fun n => (f n).value = true)
      simpa [stableMove, PlayTree.value, h] using hh.resolve_left h

private theorem diagonal {P : ℕ → ℕ → Prop} (h : ∀ i, ∀ᶠ n in hyperfilter ℕ, P i n) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∀ i j, i ≤ j → P i (g j) := by
  have pick (j b : ℕ) : ∃ n > b, ∀ i ∈ Finset.range (j+1), P i n := by
    have ha := (eventually_all_finset (Finset.range (j+1))).mpr (fun i _ => h i)
    have hb := (eventually_gt_atTop b).filter_mono Nat.hyperfilter_le_atTop
    exact (hb.and ha).exists
  let v : ℕ → ℕ := Nat.rec 0 (fun j b => (pick j b).choose)
  exact ⟨fun j => v (j+1),strictMono_nat_of_lt_succ (fun j => (pick (j+1) _).choose_spec.1),
    fun i j hij => (pick j _).choose_spec.2 i (Finset.mem_range.mpr (by omega))⟩

theorem gameThinning (t : PlayTree) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∀ p : List ℕ, ∃ b : ℕ,
      ∀ j ≥ b, stableMove (t.position p) (g j) := by
  let hist (i : ℕ) := (Encodable.decode (α := List ℕ) i).getD []
  obtain ⟨g,hg,h⟩ := diagonal (fun i => stableOften (t.position (hist i)))
  exact ⟨g,hg,fun p => ⟨Encodable.encode p,fun j hj => by
    simpa only [hist, Encodable.encodek, Option.getD_some] using h _ j hj⟩⟩

theorem architectChoice (f : ℕ → PlayTree) :
    (PlayTree.architect f).value = true ↔ ∃ n, (f n).value = true := by
  classical
  simp [PlayTree.value]

def legalStep (q : PlayTree) (g : ℕ → ℕ) (b : ℕ) (plan : Option ℕ) (n : ℕ) : Prop :=
  match q with
  | .done _ => False
  | .builder _ => ∃ j ≥ b, n = g j
  | .architect _ => ∀ a ∈ plan, n = a

inductive Allowed (t : PlayTree) (g : ℕ → ℕ) (b : List ℕ → ℕ)
    (plan : List ℕ → Option ℕ) : List ℕ → Prop
  | start : Allowed t g b plan []
  | extend {p n} : Allowed t g b plan p →
      legalStep (t.position p) g (b p) (plan p) n → Allowed t g b plan (p ++ [n])

private theorem positionAppend (t : PlayTree) (p : List ℕ) (n : ℕ) :
    t.position (p ++ [n]) = (t.position p).move n := by simp [PlayTree.position]

private noncomputable def preferred (f : ℕ → PlayTree) : ℕ := by
  classical
  exact if h : ∃ n, (f n).value = true then h.choose else 0

private noncomputable def advice : PlayTree → Option ℕ
  | .architect f => some (preferred f)
  | _ => none

theorem gameDichotomy (t : PlayTree) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∃ b : List ℕ → ℕ,
      (∃ plan : List ℕ → ℕ, ∀ p, Allowed t g b (fun p => some (plan p)) p →
        t.position p ≠ PlayTree.done false) ∨
      (∀ p, Allowed t g b (fun _ => none) p → t.position p ≠ PlayTree.done true) := by
  classical
  obtain ⟨g,hg,h⟩ := gameThinning t
  choose b hb using h
  refine ⟨g,hg,b,?_⟩
  by_cases root : t.value = true
  · let plan (p : List ℕ) := (advice (t.position p)).getD 0
    refine Or.inl ⟨plan,fun p hp ht => ?_⟩
    have inv {p} (hp : Allowed t g b (fun p => some (plan p)) p) :
        (t.position p).value = true := by
      induction hp with
      | start => exact root
      | @extend p n _ legal ih =>
        rw [positionAppend]
        cases he : t.position p with
        | done c => simp [he,legalStep] at legal
        | architect f =>
          have hval : (PlayTree.architect f).value = true := he ▸ ih
          have ex := (architectChoice f).mp hval
          have hn : n = preferred f := by simpa [legalStep,he,plan,advice] using legal
          simpa only [PlayTree.move, hn, preferred, dif_pos ex] using ex.choose_spec
        | builder f =>
          obtain ⟨j,hj,rfl⟩ := (show ∃ j ≥ b p, n = g j by simpa [he, legalStep] using legal)
          have hs := hb p j hj
          rw [he] at hs ih
          exact (show (f (g j)).value = (PlayTree.builder f).value from hs).trans ih
    have hi := inv hp
    rw [ht] at hi
    contradiction
  · apply Or.inr
    intro p hp ht
    have inv {p} (hp : Allowed t g b (fun _ => none) p) : (t.position p).value ≠ true := by
      induction hp with
      | start => exact root
      | @extend p n _ legal ih =>
        rw [positionAppend]
        cases he : t.position p with
        | done c => simp [legalStep,he] at legal
        | architect f =>
          intro hn
          exact ih (he ▸ (architectChoice f).mpr ⟨n,hn⟩)
        | builder f =>
          obtain ⟨j,hj,rfl⟩ := (show ∃ j ≥ b p, n = g j by simpa [he,legalStep] using legal)
          have hs := hb p j hj
          rw [he] at hs ih
          exact fun hh => ih ((show (f (g j)).value = (PlayTree.builder f).value from hs).symm.trans hh)
    exact inv hp (ht ▸ rfl)

end Larson.Game

open Ordinal
open Order

namespace Larson

variable {A : Type u} [LinearOrder A] [WellFoundedLT A]

private noncomputable def cut (s : Set A) (x : A) : Ordinal.{u} :=
  ⨆ z : s, if (z : A) < x then typein ((· < ·) : s → s → Prop) z + 1 else 0

private theorem cut_le (s : Set A) (x : A) : cut s x ≤ typeLT s := by
  apply Ordinal.iSup_le
  intro z
  split
  · exact add_one_le_iff.mpr (typein_lt_type _ _)
  · exact bot_le

private theorem cut_mono (s : Set A) : Monotone (cut s) := by
  intro x y h
  apply Ordinal.iSup_le
  intro z
  apply le_trans _ (Ordinal.le_iSup _ z)
  split_ifs with hx hy hy
  · rfl
  · exact (hy (hx.trans_le h)).elim
  all_goals exact bot_le

private theorem cut_lt {s : Set A} {x y : A} (hs : x ∈ s) (h : x < y) :
    cut s x < cut s y := by
  let v : s := ⟨x, hs⟩
  have hle : cut s x ≤ typein ((· < ·) : s → s → Prop) v := by
    apply Ordinal.iSup_le
    intro z
    split
    · exact add_one_le_iff.mpr ((typein_lt_typein _).mpr (by assumption))
    · exact bot_le
  have hge := Ordinal.le_iSup (fun z : s =>
    if (z : A) < y then typein ((· < ·) : s → s → Prop) z + 1 else 0) v
  rw [if_pos (show (v : A) < y from h)] at hge
  exact (hle.trans_lt (lt_add_one _)).trans_le hge

theorem unionProductBound (s t : Set A) :
    typeLT (s ∪ t : Set A) ≤ (typeLT t + 1) * (typeLT s + 1) := by
  let b := typeLT t + 1
  let rank (x : A) := b * cut s x + cut t x
  have room (x : A) : rank x < b * (cut s x + 1) := by
    rw [mul_add_one]
    exact (add_lt_add_iff_left _).mpr ((cut_le t x).trans_lt (lt_add_one _))
  let target := b * (typeLT s + 1)
  let f (x : (s ∪ t : Set A)) : target.ToType := ToType.mk
    ⟨rank x, (room x).trans_le (by grw [cut_le s x])⟩
  have hm : StrictMono f := by
    intro x y h
    apply ToType.mk.strictMono
    change rank x < rank y
    rcases x.property with hx | hx
    · calc
        rank x < b * (cut s x + 1) := room x
        _ ≤ b * cut s y := by grw [add_one_le_iff.mpr (cut_lt hx h)]
        _ ≤ rank y := le_self_add
    · have hc := (cut_mono s) (show (x : A) ≤ y from h.le)
      calc
        rank x < b * cut s x + cut t y := (add_lt_add_iff_left _).mpr (cut_lt hx h)
        _ ≤ rank y := by dsimp [rank]; grw [hc]
  let he : ((· < ·) : (s ∪ t : Set A) → (s ∪ t : Set A) → Prop) ↪r
      ((· < ·) : target.ToType → target.ToType → Prop) :=
    ⟨⟨f, hm.injective⟩, hm.lt_iff_lt⟩
  exact (type_le_iff'.mpr ⟨he⟩).trans_eq (type_toType target)

theorem unionSmall (s t : Set A) {α : Ordinal.{u}}
    (hs : typeLT s < ω ^ ω ^ α) (ht : typeLT t < ω ^ ω ^ α) :
    typeLT (s ∪ t : Set A) < ω ^ ω ^ α := by
  have one : (1 : Ordinal.{u}) < ω ^ ω ^ α := by
    exact one_lt_opow.mpr ⟨one_lt_omega0, opow_ne_zero _ omega0_ne_zero⟩
  apply (unionProductBound s t).trans_lt
  apply isPrincipal_mul_omega0_opow_opow
  · exact isPrincipal_add_omega0_opow _ ht one
  · exact isPrincipal_add_omega0_opow _ hs one

theorem finiteUnionSmall {ι : Type*} (F : Finset ι) (s : ι → Set A) {α : Ordinal.{u}}
    (hs : ∀ i ∈ F, typeLT (s i) < ω ^ ω ^ α) :
    typeLT (⋃ i ∈ F, s i) < ω ^ ω ^ α := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    rw [Set.biUnion_empty_finset]
    have h : typeLT (∅ : Set A) = 0 := type_eq_zero_iff_isEmpty.mpr inferInstance
    exact h.trans_lt (opow_pos _ omega0_pos)
  | insert i F hi ih =>
    rw [Finset.set_biUnion_insert]
    exact unionSmall _ _ (hs i (Finset.mem_insert_self ..))
      (ih fun j hj => hs j (Finset.mem_insert_of_mem hj))

end Larson

namespace Larson.Local

open Ordinal Order

def Indivisible (I : Type) [LinearOrder I] : Prop :=
  ∀ (K : Type) [Fintype K] (c : I → K), ∃ (v : K) (f : I → I), StrictMono f ∧ ∀ i, c (f i) = v

theorem indivisibleProduct (I J : Type) [LinearOrder I] [LinearOrder J]
    (hi : Indivisible I) (hj : Indivisible J) : Indivisible (I ×ₗ J) := by
  intro K _ c
  choose v f hf hc using fun i : I => hj K (fun j => c (toLex (i,j)))
  obtain ⟨v₀,g,hg,hv⟩ := hi K v
  refine ⟨v₀,fun x => toLex (g (ofLex x).1, f (g (ofLex x).1) (ofLex x).2),?_,?_⟩
  · intro x y h
    cases h with
    | left _ _ h => exact Prod.Lex.left _ _ (hg h)
    | right _ h => exact Prod.Lex.right _ (hf _ h)
  · intro x
    exact (hc _ _).trans (hv _)

theorem indivisibleTransport {I J : Type} [LinearOrder I] [LinearOrder J]
    (e : ((· < ·) : I → I → Prop) ≃r ((· < ·) : J → J → Prop))
    (hi : Indivisible I) : Indivisible J := by
  intro K _ c
  obtain ⟨v,f,hf,hh⟩ := hi K (c ∘ e)
  exact ⟨v,fun j => e (f (e.symm j)), fun _ _ h => e.map_rel_iff.mpr (hf (e.symm.map_rel_iff.mpr h)),
    fun j => hh _⟩

theorem indivisibleBlock {I : Type} [LinearOrder I] [WellFoundedLT I] (ht : typeLT I = ω ^ (ω : Ordinal.{0})) :
    Indivisible I := by
  classical
  intro K _ c
  let parts (i : K) : Set I := {x | c x = i}
  have full : ∃ i, typeLT I ≤ typeLT (parts i) := by
    by_contra! h
    have hull := Larson.finiteUnionSmall (α := 1) Finset.univ parts (fun i _ => by simpa [ht] using h i)
    have cover : (⋃ i ∈ (Finset.univ : Finset K), parts i) = Set.univ := by ext x; simp [parts]
    rw [cover,opow_one] at hull
    have hU : typeLT (Set.univ : Set I) = typeLT I := OrderIso.Set.univ.toRelIsoLT.ordinalType_congr
    exact (hU.trans ht).not_lt hull
  obtain ⟨i,hi⟩ := full
  obtain ⟨f⟩ := type_le_iff'.mp hi
  exact ⟨i, fun x => (f x).val, fun _ _ h => f.map_rel_iff.mpr h, fun x => (f x).property⟩

theorem indivisiblePower (n : ℕ) (I : Type) [LinearOrder I] [WellFoundedLT I]
    (ht : typeLT I = ((ω : Ordinal.{0}) ^ ω)^n) : Indivisible I := by
  induction n generalizing I with
  | zero =>
    rw [pow_zero] at ht
    obtain ⟨hn,hu⟩ := type_eq_one_iff_unique.mp ht
    intro K _ c
    obtain ⟨x⟩ := hn
    exact ⟨c x,id,strictMono_id,fun y => congrArg c ((hu y).trans (hu x).symm)⟩
  | succ n ih =>
    let A := (ω : Ordinal.{0}) ^ ω
    let B := A^n
    let P := A.ToType ×ₗ B.ToType
    have hP : typeLT P = B*A := by
      change type (Prod.Lex ((· < ·) : A.ToType → _ → Prop) ((· < ·) : B.ToType → _ → Prop)) = _
      rw [type_prod_lex,type_toType,type_toType]
    obtain ⟨e⟩ : Nonempty (((· < ·) : P → P → Prop) ≃r ((· < ·) : I → I → Prop)) :=
      type_eq.mp (hP.trans ((pow_succ A n).symm.trans ht.symm))
    exact indivisibleTransport e (indivisibleProduct _ _ (indivisibleBlock (type_toType A)) (ih _ (type_toType B)))

def RedCopy {X : Type} [LinearOrder X] (I : Type) [LinearOrder I] (R : SimpleGraph X) :=
  ∃ f : I → X, StrictMono f ∧ ∀ i j, i ≠ j → R.Adj (f i) (f j)

theorem redRows {I X : Type} [LinearOrder I] [LinearOrder X] [Countable I] [Nonempty I]
    (rows : I ×ₗ I → X) (ord : StrictMono rows) (hi : Indivisible I)
    (R B : SimpleGraph X) (hRB : IsCompl R B) (hB : B.CliqueFree 3) :
    RedCopy I R := by
  classical
  by_contra hn
  let atRow (i j : I) := rows (toLex (i,j))
  have cell (i : I) (F : Finset (I × I)) :
      ∃ j, ∀ p ∈ F, p.1 ≠ i → R.Adj (atRow i j) (atRow p.1 p.2) := by
    by_contra! bad
    choose c hc hne hx using bad
    let label (j : I) : F := ⟨c j,hc j⟩
    obtain ⟨p,f,hf,hcst⟩ := hi F label
    have allB (j : I) : atRow i (f j) ∈ B.neighborSet (atRow p.val.1 p.val.2) := by
      have he : c (f j) = p.val := congrArg Subtype.val (hcst j)
      have hnr := hx (f j)
      rw [he,hRB.eq_compl,SimpleGraph.compl_adj] at hnr
      have neq : atRow i (f j) ≠ atRow p.val.1 p.val.2 := by
        intro hh
        have : i = p.val.1 := congrArg (fun z : I ×ₗ I => (ofLex z).1) (ord.injective hh)
        exact hne (f j) (he ▸ this.symm)
      exact (show B.Adj _ _ from by_contra fun hh => hnr ⟨neq,hh⟩).symm
    have hs : R.IsClique (B.neighborSet (atRow p.val.1 p.val.2)) := by
      rw [hRB.eq_compl,SimpleGraph.isClique_compl]
      exact B.isIndepSet_neighborSet_of_triangleFree hB _
    have hmono : StrictMono (fun j => atRow i (f j)) := fun _ _ hj => ord (Prod.Lex.right _ (hf hj))
    exact hn ⟨_,hmono,fun j k hjk => hs (allB j) (allB k) (hmono.injective.ne hjk)⟩
  let : Encodable I := Encodable.ofCountable I
  let idx (n : ℕ) := (Encodable.decode (α := I) n).getD (Classical.arbitrary I)
  let pick (i : I) (F : Finset (I × I)) := (cell i F).choose
  let acc : ℕ → Finset (I × I) := Nat.rec ∅ fun n F => insert (idx n,pick (idx n) F) F
  let point (n : ℕ) := (idx n,pick (idx n) (acc n))
  have hm : Monotone acc := monotone_nat_of_le_succ fun _ => Finset.subset_insert ..
  have old (n m : ℕ) (h : n < m) : point n ∈ acc m :=
    hm h (Finset.mem_insert_self .. : point n ∈ acc (n+1))
  have adj (n m : ℕ) (h : n < m) (diff : idx n ≠ idx m) :
      R.Adj (atRow (idx m) (point m).2) (atRow (idx n) (point n).2) :=
    (cell (idx m) _).choose_spec (point n) (old n m h) diff
  let code := @Encodable.encode I _
  have hc (i : I) : idx (code i) = i := by simp [idx,code]
  refine hn ⟨fun i => atRow i (point (code i)).2, fun _ _ hij => ord (Prod.Lex.left _ _ hij),?_⟩
  intro i j hij
  have hd : code i ≠ code j := fun h => hij ((hc i).symm.trans ((congrArg idx h).trans (hc j)))
  rcases lt_or_gt_of_ne hd with h | h
  · simpa only [hc] using (adj _ _ h (by simpa only [hc] using hij)).symm
  · simpa only [hc] using adj _ _ h (by simpa only [hc] using hij.symm)

theorem redFinitePower (n : ℕ) (I X : Type) [LinearOrder I] [WellFoundedLT I]
    [LinearOrder X] [WellFoundedLT X] [Countable I] [Nonempty I]
    (hi : typeLT I = ((ω : Ordinal.{0}) ^ ω)^n)
    (hx : ((ω : Ordinal.{0}) ^ ω)^(2*n) ≤ typeLT X)
    (R B : SimpleGraph X) (hc : IsCompl R B) (hb : B.CliqueFree 3) : RedCopy I R := by
  have bound : typeLT (I ×ₗ I) ≤ typeLT X := by
    change type (Prod.Lex ((· < ·) : I → _ → Prop) ((· < ·) : I → _ → Prop)) ≤ _
    rw [type_prod_lex]
    rw [two_mul,pow_add] at hx
    simpa only [hi] using hx
  obtain ⟨e⟩ := type_le_iff'.mp bound
  exact redRows e (fun _ _ h => e.map_rel_iff.mpr h) (indivisiblePower n I hi) R B hc hb

end Larson.Local

namespace Larson.Words
open Ordinal Order Larson.Local

instance tupleCountable (I : Type) [Countable I] (n : ℕ) : Countable (Tuple I n) :=
  Nat.rec (motive := fun j => Countable (Tuple I j)) (inferInstanceAs (Countable Unit))
    (fun i _ => inferInstanceAs (Countable (I × Tuple I i))) n

instance tupleNonempty (I : Type) [Nonempty I] (n : ℕ) : Nonempty (Tuple I n) :=
  Nat.rec (motive := fun j => Nonempty (Tuple I j)) (inferInstanceAs (Nonempty Unit))
    (fun i _ => inferInstanceAs (Nonempty (I × Tuple I i))) n

private def level (m : ℕ) : Tuple Block m ↪ Word :=
  let f (x : Tuple Block m) : Word := ⟨m,x⟩
  let h : StrictMono f := fun x y hij => Sigma.Lex.right x y hij
  ⟨f,h.injective⟩

theorem redWithinBlocks (R B : SimpleGraph Word) (hc : IsCompl R B) (hb : B.CliqueFree 3) :
    ∃ f : Word → Word, StrictMono f ∧ ∀ x y, x.1 = y.1 → x ≠ y → R.Adj (f x) (f y) := by
  classical
  have : Countable Block := inferInstanceAs (Countable ((i : ℕ) × Tuple ℕ i))
  have : Nonempty Block := ⟨⟨0,()⟩⟩
  have hB : typeLT Block = ω ^ (ω : Ordinal.{0}) := by
    rw [towerType ℕ (by rw [type_nat_lt]; exact (natCast_lt_omega0 2).le),type_nat_lt]
  have localCopy (n : ℕ) : RedCopy (Tuple Block n) (R.comap (level (2*n))) := by
    let e := level (2*n)
    have hcomp : IsCompl (R.comap e) (B.comap e) := by
      rw [hc.eq_compl]
      suffices Bᶜ.comap e = (B.comap e)ᶜ by rw [this]; exact isCompl_compl.symm
      ext x y
      simp [SimpleGraph.compl_adj, SimpleGraph.comap, e.injective.eq_iff]
    apply redFinitePower n _ _ _ _ _ _ hcomp (SimpleGraph.CliqueFree.comap (SimpleGraph.Embedding.comap e B).isContained hb)
    · rw [tupleType,hB]
    · rw [tupleType,hB]
  choose f hf hr using localCopy
  let F (x : Word) : Word := level (2*x.1) (f x.1 x.2)
  refine ⟨F,?_,?_⟩
  · intro x y h
    cases h with
    | left a b hab => exact Sigma.Lex.left _ _ (Nat.mul_lt_mul_of_pos_left hab (by decide : 0 < 2))
    | right a b hab => exact Sigma.Lex.right _ _ (hf _ hab)
  · rintro ⟨n,a⟩ ⟨m,b⟩ he hn
    change n = m at he
    subst m
    exact hr n a b (fun h => hn (h ▸ rfl))

end Larson.Words

namespace Larson.Words
open Ordinal Order

def CrossBlock : Prop :=
  ∀ R B : SimpleGraph Word, IsCompl R B → B.CliqueFree 3 →
    ∃ s : Set Word, typeLT s = typeLT Word ∧
      ∀ x ∈ s, ∀ y ∈ s, x.1 ≠ y.1 → R.Adj x y

private theorem comapCompl {X Y : Type} (f : X ↪ Y) (R B : SimpleGraph Y)
    (hc : IsCompl R B) : IsCompl (R.comap f) (B.comap f) := by
  rw [hc.eq_compl]
  suffices Bᶜ.comap f = (B.comap f)ᶜ by rw [this]; exact isCompl_compl.symm
  ext x y
  simp [SimpleGraph.compl_adj,SimpleGraph.comap,f.injective.eq_iff]

theorem positiveOfCrossBlock (hAcross : CrossBlock) :
    Erdos118.OrdinalRamsey ((ω : Ordinal.{u}) ^ (ω ^ (2 : Ordinal)))
      (ω ^ (ω ^ (2 : Ordinal))) 3 := by
  apply (Larson.concreteRamseyLift.{u} 3).mpr
  let A := (ω : Ordinal.{0}) ^ (ω ^ (2 : Ordinal))
  intro R B hc
  by_cases ht : ∃ s, B.IsClique s ∧ typeLT s = 3
  · exact Or.inr ht
  apply Or.inl
  have hb : B.CliqueFree 3 := by
    intro s hs
    apply ht
    refine ⟨(s : Set A.ToType),hs.1,?_⟩
    change type ((· < ·) : s → _ → Prop) = _
    rw [type_fintype,Fintype.card_coe,hs.2]
    rfl
  obtain ⟨e⟩ : Nonempty (((· < ·) : Word → Word → Prop) ≃r ((· < ·) : A.ToType → _ → Prop)) :=
    type_eq.mp (wordType.trans (type_toType A).symm)
  let e₀ := e.toEquiv.toEmbedding
  let R₀ := R.comap e₀
  let B₀ := B.comap e₀
  have hc₀ := comapCompl e₀ R B hc
  have hb₀ := SimpleGraph.CliqueFree.comap (SimpleGraph.Embedding.comap e₀ B).isContained hb
  obtain ⟨f,hf,hr⟩ := redWithinBlocks R₀ B₀ hc₀ hb₀
  let fe : Word ↪ Word := ⟨f,hf.injective⟩
  obtain ⟨s,hs,ha⟩ := hAcross _ _ (comapCompl fe R₀ B₀ hc₀)
    (SimpleGraph.CliqueFree.comap (SimpleGraph.Embedding.comap fe B₀).isContained hb₀)
  let g (x : Word) := e (f x)
  have hg : StrictMono g := fun _ _ h => e.map_rel_iff.mpr (hf h)
  refine ⟨g '' s,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ hne
    by_cases eq : x.1 = y.1
    · exact hr x y eq (fun hh => hne (congrArg g hh))
    · exact ha x hx y hy eq
  · let iso : ((· < ·) : s → s → Prop) ≃r ((· < ·) : (g '' s) → _ → Prop) :=
      { toEquiv := Equiv.Set.image g s hg.injective
        map_rel_iff' := hg.lt_iff_lt }
    exact iso.ordinalType_congr.symm.trans (hs.trans wordType)

end Larson.Words

theorem Larson.fromCrossBlock (h : Larson.Words.CrossBlock) : type_of% @Erdos118.erdos_118.variants.larson := ⟨Larson.Words.positiveOfCrossBlock h, Larson.negative⟩

namespace Larson.PairGame
open Larson.Words Larson.Game

inductive Thread (α : Type) where
  | result : α → Thread α
  | pause : Thread α → Thread α
  | plan : (ℕ → Thread α) → Thread α
  | draw : (ℕ → Thread α) → Thread α

def Thread.bind {α β : Type} (t : Thread α) (k : α → Thread β) : Thread β :=
  match t with
  | .result x => k x
  | .pause t => .pause (t.bind k)
  | .plan f => .plan fun i => (f i).bind k
  | .draw f => .draw fun i => (f i).bind k

def indices : ℕ → Thread (List ℕ × ℕ)
  | 0 => .draw fun n => .result ([],n)
  | k+1 => .draw fun i => (indices k).bind fun p => .result (i :: p.1,p.2)

def visit {I : Type} (child : ℕ → Thread I) (start : ℕ) : (h : ℕ) → Thread (Tuple I h)
  | 0 => .result ()
  | h+1 => (child start).bind fun i =>
    (visit child (start+1) h).bind fun s => .result (toLex (i,s))

def drawBlock (cuts : ℕ) : Thread Block :=
  (indices cuts).bind fun ⟨marks,n⟩ =>
    let child j := Thread.draw fun i =>
      if j ∈ marks then Thread.pause (.result i) else .result i
    (visit child 0 n).bind fun s => .result ⟨n,s⟩

def drawWord : Thread Word :=
  .plan fun k => (indices k).bind fun ⟨marks,n⟩ =>
    let child j := if j ∈ marks then Thread.plan fun d => drawBlock (d+1) else drawBlock 0
    (visit child 0 n).bind fun s => .result ⟨n,s⟩

inductive OutcomeTree (α : Type) where
  | leaf : Option α → OutcomeTree α
  | plan : (ℕ → OutcomeTree α) → OutcomeTree α
  | draw : (ℕ → OutcomeTree α) → OutcomeTree α

def finish {α β : Type} (k : α → β) : Thread α → OutcomeTree β
  | .result x => .leaf (some (k x))
  | .pause _ => .leaf none
  | .plan f => .plan fun i => finish k (f i)
  | .draw f => .draw fun i => finish k (f i)

private def runRight {α β : Type} (left : Thread β → OutcomeTree (α × β))
    (atEnd : β → OutcomeTree (α × β)) : Thread β → OutcomeTree (α × β)
  | .result b => atEnd b
  | .pause y => left y
  | .plan f => .plan fun i => runRight left atEnd (f i)
  | .draw f => .draw fun i => runRight left atEnd (f i)

def interleave {α β : Type} : Thread α → Thread β → OutcomeTree (α × β)
  | .result a, y => finish (a,·) y
  | .pause x, y => runRight (interleave x) (fun b => finish (·,b) x) y
  | .plan f, y => .plan fun i => interleave (f i) y
  | .draw f, y => .draw fun i => interleave (f i) y

def OutcomeTree.move {α : Type} : OutcomeTree α → ℕ → OutcomeTree α
  | .leaf r, _ => .leaf r
  | .plan f, i | .draw f, i => f i

def OutcomeTree.score {α : Type} (c : α → Bool) : OutcomeTree α → PlayTree
  | .leaf r => .done (r.elim false c)
  | .plan f => .architect fun i => (f i).score c
  | .draw f => .builder fun i => (f i).score c

theorem scorePosition {α : Type} (t : OutcomeTree α) (c : α → Bool) (p : List ℕ) :
    (t.score c).position p = (p.foldl OutcomeTree.move t).score c := by
  induction p generalizing t with
  | nil => rfl
  | cons n p ih =>
    change ((t.score c).move n).position p = _
    have hm : (t.score c).move n = (t.move n).score c := by cases t <;> rfl
    exact (congrArg (fun q : PlayTree => q.position p) hm).trans (ih _)

def pairs := interleave drawWord drawWord

theorem wordDichotomy (c : Word × Word → Bool) :
    let t := pairs.score c
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∃ b : List ℕ → ℕ,
      (∃ plan : List ℕ → ℕ, ∀ p r, Allowed t g b (fun q => some (plan q)) p →
        p.foldl OutcomeTree.move pairs = .leaf r → ∃ w, r = some w ∧ c w = true) ∨
      (∀ p w, Allowed t g b (fun _ => none) p →
        p.foldl OutcomeTree.move pairs = .leaf (some w) → c w = false) := by
  obtain ⟨g,hg,b,h | h⟩ := gameDichotomy (pairs.score c)
  · obtain ⟨plan,h⟩ := h
    refine ⟨g,hg,b,Or.inl ⟨plan,?_⟩⟩
    intro p r hp he
    have hh := h p hp
    rw [scorePosition,he] at hh
    cases r with
    | none => exact (hh rfl).elim
    | some w =>
      exact ⟨w,rfl,Bool.eq_true_of_not_eq_false (fun h => hh (by simp [OutcomeTree.score,h]))⟩
  · refine ⟨g,hg,b,Or.inr ?_⟩
    intro p w hp he
    have hh := h p hp
    rw [scorePosition,he] at hh
    exact Bool.eq_false_of_not_eq_true (fun h => hh (by simp [OutcomeTree.score,h]))

end Larson.PairGame

namespace Larson.Words
open Ordinal Order

inductive FreeSection {X : Type} [LinearOrder X] : ℕ → ℕ → Set X → Prop where
  | terminal {s} : s.Nonempty → FreeSection 0 0 s
  | leaf {r k s} (t : ℕ → Set X) (sub : ∀ i, t i ⊆ s)
      (ordered : ∀ i j, i < j → ∀ x ∈ t i, ∀ y ∈ t j, x < y)
      (next : ∀ i, FreeSection r k (t i)) : FreeSection r (k+1) s
  | block {r s} (t : ℕ → Set X) (width : ℕ → ℕ) (large : ∀ n, n ≤ width n)
      (sub : ∀ i, t i ⊆ s) (next : ∀ i, FreeSection r (width i) (t i)) :
      FreeSection (r+1) 0 s

private theorem nestedType {X : Type} [LinearOrder X] [WellFoundedLT X]
    {s t : Set X} (h : s ⊆ t) : typeLT s ≤ typeLT t :=
  type_le_iff'.mpr ⟨⟨⟨fun x => (⟨x.val,h x.property⟩ : t),fun _ _ he => Subtype.ext (congrArg (fun v : t => v.val) he)⟩,
    Iff.rfl⟩⟩

private theorem orderedSections {X : Type} [LinearOrder X] [WellFoundedLT X] {s : Set X}
    (t : ℕ → Set X) (sub : ∀ i, t i ⊆ s)
    (ordered : ∀ i j, i < j → ∀ x ∈ t i, ∀ y ∈ t j, x < y)
    (a : Ordinal.{0}) (ht : ∀ i, a ≤ typeLT (t i)) : a * ω ≤ typeLT s := by
  
  let f (i : ℕ) := Classical.choice (type_le_iff'.mp (show typeLT a.ToType ≤ typeLT (t i) by
    rw [type_toType]; exact ht i))
  let g (z : ℕ ×ₗ a.ToType) : s :=
    ⟨(f (ofLex z).1 (ofLex z).2).val,sub _ (f (ofLex z).1 (ofLex z).2).property⟩
  have hg : StrictMono g := by
    intro x y h
    cases h with
    | left x y h => exact ordered _ _ h _ (f _ x).property _ (f _ y).property
    | right i h => exact (f i).map_rel_iff.mpr h
  have le : typeLT (ℕ ×ₗ a.ToType) ≤ typeLT s := type_le_iff'.mpr ⟨⟨⟨g,hg.injective⟩,hg.lt_iff_lt⟩⟩
  change type (Prod.Lex ((· < ·) : ℕ → _ → Prop) ((· < ·) : a.ToType → _ → Prop)) ≤ _ at le
  simpa only [type_prod_lex,type_nat_lt,type_toType] using le

theorem freeSectionType {X : Type} [LinearOrder X] [WellFoundedLT X] {s : Set X} {r k : ℕ}
    (h : FreeSection r k s) : ((ω : Ordinal.{0}) ^ ω)^r * ω^k ≤ typeLT s := by
  let A := (ω : Ordinal.{0}) ^ ω
  induction h with
  | terminal hn =>
    obtain ⟨x,hx⟩ := hn
    simpa only [pow_zero,mul_one] using (one_le_iff_pos.mpr
      (pos_iff_ne_zero.mpr (type_ne_zero_iff_nonempty.mpr ⟨⟨x,hx⟩⟩)))
  | leaf t sub ord _ ih =>
    simpa only [pow_succ,mul_assoc] using orderedSections t sub ord _ ih
  | @block r s t width large sub _ ih =>
    have sup := apply_omega0_of_isNormal ((isNormal_mul_right (pow_pos (opow_pos ω omega0_pos) r)).comp
      (isNormal_opow one_lt_omega0))
    change A^(r+1) * ω^(0:ℕ) ≤ typeLT s
    rw [pow_zero,mul_one,pow_succ]
    change A^r * (ω ^ ω) ≤ _
    rw [← show (⨆ i : ℕ, A^r * ω^(i : Ordinal)) = A^r * (ω ^ ω) from sup]
    apply Ordinal.iSup_le
    intro n
    rw [opow_natCast]
    exact (show A^r * ω^n ≤ A^r * ω^(width n) from by
      grw [pow_le_pow_right₀ (one_le_iff_pos.mpr omega0_pos) (large n)]).trans
        ((ih n).trans (nestedType (sub n)))

theorem freeWordType {s : Set Word}
    (free : ∀ n : ℕ, ∃ r k : ℕ, n ≤ r ∧ FreeSection r k s) : typeLT s = typeLT Word := by
  apply le_antisymm (type_set_le _)
  have hB : typeLT Block = ω ^ (ω : Ordinal.{0}) := by
    rw [towerType ℕ (by rw [type_nat_lt]; exact (natCast_lt_omega0 2).le),type_nat_lt]
  have hb : 2 ≤ typeLT Block := by
    rw [hB]
    apply (natCast_lt_omega0 2).le.trans
    simpa only [opow_one] using (opow_le_opow_right omega0_pos (one_le_iff_pos.mpr omega0_pos))
  rw [towerType Block hb,hB,← iSup_pow_natCast (opow_pos _ omega0_pos)]
  apply Ordinal.iSup_le
  intro n
  obtain ⟨r,k,hn,h⟩ := free n
  have ho : 1 ≤ (ω : Ordinal.{0})^k := one_le_iff_pos.mpr (pow_pos omega0_pos k)
  calc
    _ ≤ ((ω : Ordinal.{0}) ^ ω)^r := pow_le_pow_right₀ (one_le_iff_pos.mpr (opow_pos _ omega0_pos)) hn
    _ = _ * 1 := (mul_one _).symm
    _ ≤ _ := by grw [ho]
    _ ≤ _ := freeSectionType h

end Larson.Words

namespace Larson.PairGame
open Filter Larson.Game

end Larson.PairGame

namespace Larson.PairGame
open Larson.Words

inductive Action where
  | plan (n : ℕ)
  | draw (n : ℕ)
  | pause

inductive Trace {α : Type} : Thread α → List Action → α → Prop where
  | result (a) : Trace (.result a) [] a
  | pause {t p a} : Trace t p a → Trace (.pause t) (.pause :: p) a
  | plan {f p a} (n) : Trace (f n) p a → Trace (.plan f) (.plan n :: p) a
  | draw {f p a} (n) : Trace (f n) p a → Trace (.draw f) (.draw n :: p) a

theorem Trace.bind {α β : Type} {t : Thread α} {p a} (h : Trace t p a)
    {k : α → Thread β} {q b} (h' : Trace (k a) q b) : Trace (t.bind k) (p ++ q) b := by
  induction h with
  | result => exact h'
  | pause _ ih => exact .pause (ih h')
  | plan n _ ih => exact .plan n (ih h')
  | draw n _ ih => exact .draw n (ih h')

private theorem indicesTrace (l : List ℕ) (n : ℕ) :
    Trace (indices l.length) (l.map Action.draw ++ [.draw n]) (l,n) := by
  induction l with
  | nil => exact .draw n (.result _)
  | cons i l ih =>
    apply Trace.draw i
    simpa using ih.bind (k := fun p => Thread.result (i :: p.1,p.2)) (.result _)

private def actionsOf {I : Type} (cell : ℕ → I → List Action) (start : ℕ) :
    (h : ℕ) → Tuple I h → List Action
  | 0, _ => []
  | h+1, z => cell start (ofLex z).1 ++ actionsOf cell (start+1) h (ofLex z).2

private theorem visitTrace {I : Type} {child : ℕ → Thread I}
    {cell : ℕ → I → List Action} (valid : ∀ j a, Trace (child j) (cell j a) a)
    (start h : ℕ) (w : Tuple I h) : Trace (visit child start h) (actionsOf cell start h w) w := by
  induction h generalizing start with
  | zero => cases w; exact .result _
  | succ h ih =>
    obtain ⟨a,b⟩ := w
    apply (valid start a).bind
    have ht := (ih (start+1) b).bind (k := fun s => Thread.result (toLex (a,s))) (.result _)
    rw [List.append_nil] at ht
    exact ht

private def leafActions (marks : List ℕ) (j a : ℕ) : List Action :=
  if j ∈ marks then [.draw a,.pause] else [.draw a]

private def blockActions (marks : List ℕ) (b : Block) : List Action :=
  (marks.map Action.draw ++ [.draw b.1]) ++ actionsOf (leafActions marks) 0 b.1 b.2

private theorem blockTrace (marks : List ℕ) (b : Block) :
    Trace (drawBlock marks.length) (blockActions marks b) b := by
  apply (indicesTrace marks b.1).bind
  have valid (j a : ℕ) :
      Trace (Thread.draw (fun i => if j ∈ marks then Thread.pause (.result i) else .result i))
        (leafActions marks j a) a := by
    by_cases h : j ∈ marks
    · simpa [leafActions,h] using (Trace.draw a (f := fun i => Thread.pause (.result i))
        (.pause (.result a)))
    · simpa [leafActions,h] using (Trace.draw a (f := fun i => Thread.result i) (.result a))
  have ht := (visitTrace valid 0 b.1 b.2).bind
    (k := fun s => Thread.result (⟨b.1,s⟩ : Block)) (.result _)
  rw [List.append_nil] at ht
  exact ht

structure Cuts where
  blocks : List ℕ
  first : ℕ → ℕ
  rest : ℕ → List ℕ

private def cellActions (c : Cuts) (j : ℕ) (b : Block) : List Action :=
  if j ∈ c.blocks then .plan (c.rest j).length :: blockActions (c.first j :: c.rest j) b
  else blockActions [] b

def wordActions (c : Cuts) (w : Word) : List Action :=
  .plan c.blocks.length :: ((c.blocks.map Action.draw ++ [.draw w.1]) ++
    actionsOf (cellActions c) 0 w.1 w.2)

theorem wordTrace (c : Cuts) (w : Word) : Trace drawWord (wordActions c w) w := by
  apply Trace.plan c.blocks.length
  apply (indicesTrace c.blocks w.1).bind
  have valid (j : ℕ) (b : Block) :
      Trace (if j ∈ c.blocks then Thread.plan fun d => drawBlock (d+1) else drawBlock 0)
        (cellActions c j b) b := by
    by_cases h : j ∈ c.blocks
    · simpa only [h,if_true,cellActions] using
        (Trace.plan (c.rest j).length (f := fun d => drawBlock (d+1)) (blockTrace (c.first j :: c.rest j) b))
    · simpa [h,cellActions] using blockTrace [] b
  have ht := (visitTrace valid 0 w.1 w.2).bind
    (k := fun s => Thread.result (⟨w.1,s⟩ : Word)) (.result _)
  rw [List.append_nil] at ht
  exact ht

end Larson.PairGame

namespace Larson.PairGame
open Larson.Game

inductive Terminal {α : Type} : OutcomeTree α → List Action → Option α → Prop where
  | leaf (a) : Terminal (.leaf a) [] a
  | plan {f p a} (i) : Terminal (f i) p a → Terminal (.plan f) (.plan i :: p) a
  | draw {f p a} (i) : Terminal (f i) p a → Terminal (.draw f) (.draw i :: p) a

def uninterrupted : List Action → Prop
  | [] => True
  | .pause :: _ => False
  | .draw _ :: p | .plan _ :: p => uninterrupted p

private theorem finishTrace {α β : Type} (k : α → β) {x : Thread α} {p a}
    (h : Trace x p a) (hp : uninterrupted p) : Terminal (finish k x) p (some (k a)) := by
  induction h with
  | result => exact .leaf _
  | pause => exact hp.elim
  | plan i _ ih => exact .plan i (ih hp)
  | draw i _ ih => exact .draw i (ih hp)

inductive Weave : Bool → List Action → List Action → List Action → Prop where
  | endLeft {y} : uninterrupted y → Weave true [] y y
  | endRight {x} : uninterrupted x → Weave false x [] x
  | switchLeft {x y q} : Weave false x y q → Weave true (.pause :: x) y q
  | switchRight {x y q} : Weave true x y q → Weave false x (.pause :: y) q
  | planLeft {x y q} (n) : Weave true x y q → Weave true (.plan n :: x) y (.plan n :: q)
  | planRight {x y q} (n) : Weave false x y q → Weave false x (.plan n :: y) (.plan n :: q)
  | drawLeft {x y q} (n) : Weave true x y q → Weave true (.draw n :: x) y (.draw n :: q)
  | drawRight {x y q} (n) : Weave false x y q → Weave false x (.draw n :: y) (.draw n :: q)

theorem weaveTrace {α β : Type} {i : Bool} {px py p : List Action} (w : Weave i px py p)
    {x : Thread α} {y : Thread β} {a b} (hx : Trace x px a) (hy : Trace y py b) :
    Terminal (if i then interleave x y else runRight (interleave x) (fun b => finish (·,b) x) y)
      p (some (a,b)) := by
  induction w generalizing x y with
  | endLeft hu => cases hx; exact finishTrace _ hy hu
  | endRight hu => cases hy; exact finishTrace _ hx hu
  | switchLeft _ ih => cases hx with | pause hx => exact ih hx hy
  | switchRight _ ih => cases hy with | pause hy => exact ih hx hy
  | planLeft n _ ih => cases hx with | plan _ hx => exact .plan n (ih hx hy)
  | planRight n _ ih => cases hy with | plan _ hy => exact .plan n (ih hx hy)
  | drawLeft n _ ih => cases hx with | draw _ hx => exact .draw n (ih hx hy)
  | drawRight n _ ih => cases hy with | draw _ hy => exact .draw n (ih hx hy)

theorem pairReplay (c d : Cuts) (x y : Larson.Words.Word) {p : List Action}
    (w : Weave true (wordActions c x) (wordActions d y) p) : Terminal pairs p (some (x,y)) :=
  weaveTrace w (wordTrace c x) (wordTrace d y)

def moves : List Action → List ℕ
  | [] => []
  | .pause :: q => moves q
  | .draw n :: q | .plan n :: q => n :: moves q

def Within (g : ℕ → ℕ) (bound : List ℕ → ℕ) (plan : List ℕ → Option ℕ) :
    List ℕ → List Action → Prop
  | _, [] => True
  | _, .pause :: _ => False
  | p, .draw n :: q => (∃ j ≥ bound p, n = g j) ∧ Within g bound plan (p ++ [n]) q
  | p, .plan n :: q => (∀ a ∈ plan p, n = a) ∧ Within g bound plan (p ++ [n]) q

theorem terminalAllowed {α : Type} {t q : OutcomeTree α} {script : List Action} {r}
    (ht : Terminal q script r) (c : α → Bool) (g bound plan)
    {p : List ℕ} (start : p.foldl OutcomeTree.move t = q)
    (hp : Allowed (t.score c) g bound plan p) (bounds : Within g bound plan p script) :
    Allowed (t.score c) g bound plan (p ++ moves script) ∧
      (p ++ moves script).foldl OutcomeTree.move t = .leaf r := by
  induction ht generalizing p with
  | leaf => simpa [moves] using And.intro hp start
  | plan i _ ih =>
    have hpos := (scorePosition t c p).trans (congrArg (OutcomeTree.score c) start)
    have hs := Allowed.extend (n := i) hp (by simpa [hpos,legalStep,OutcomeTree.score] using bounds.1)
    have hh := ih (p := p ++ [i]) (by simp [List.foldl_append,start,OutcomeTree.move]) hs bounds.2
    simpa [moves,List.append_assoc] using hh
  | draw i _ ih =>
    have hpos := (scorePosition t c p).trans (congrArg (OutcomeTree.score c) start)
    have hs := Allowed.extend (n := i) hp (by simpa [hpos,legalStep,OutcomeTree.score] using bounds.1)
    have hh := ih (p := p ++ [i]) (by simp [List.foldl_append,start,OutcomeTree.move]) hs bounds.2
    simpa [moves,List.append_assoc] using hh

end Larson.PairGame

namespace Larson.PairGame
open Larson.Words Larson.Game Ordinal

def Realizes (g : ℕ → ℕ) (b : List ℕ → ℕ) (plan : List ℕ → Option ℕ) (x y : Word) : Prop :=
  ∃ c d script, Weave true (wordActions c x) (wordActions d y) script ∧ Within g b plan [] script

def EitherOrder (g : ℕ → ℕ) (b : List ℕ → ℕ) (plan : List ℕ → Option ℕ) (x y : Word) : Prop :=
  Realizes g b plan x y ∨ Realizes g b plan y x

private theorem realizedHistory {g b plan x y} (h : Realizes g b plan x y)
    (c : Word × Word → Bool) :
    ∃ p, Allowed (pairs.score c) g b plan p ∧ p.foldl OutcomeTree.move pairs = .leaf (some (x,y)) := by
  obtain ⟨d,e,s,hs,hw⟩ := h
  exact ⟨moves s, terminalAllowed (pairReplay _ _ _ _ hs) c g b plan (p := []) rfl .start hw⟩

def BuilderFamily : Prop :=
  ∀ (g : ℕ → ℕ), StrictMono g → ∀ b : List ℕ → ℕ, ∃ s : Set Word,
    (∀ n : ℕ, ∃ r k : ℕ, n ≤ r ∧ FreeSection r k s) ∧
    ∀ x ∈ s, ∀ y ∈ s, x.1 ≠ y.1 → EitherOrder g b (fun _ => none) x y

def ArchitectTriangle : Prop :=
  ∀ (g : ℕ → ℕ), StrictMono g → ∀ (b plan : List ℕ → ℕ),
    (∀ script, Terminal pairs script none → ¬ Within g b (fun p => some (plan p)) [] script) →
    ∃ x y z : Word, EitherOrder g b (fun p => some (plan p)) x y ∧
      EitherOrder g b (fun p => some (plan p)) x z ∧ EitherOrder g b (fun p => some (plan p)) y z

theorem crossBlockOfRealization (red : BuilderFamily) (triangle : ArchitectTriangle) : CrossBlock := by
  classical
  intro R B hc hb
  let c (xy : Word × Word) := decide (B.Adj xy.1 xy.2)
  obtain ⟨g,hg,b,left | right⟩ := wordDichotomy c
  · obtain ⟨plan,win⟩ := left
    let advice (p : List ℕ) := some (plan p)
    have valid (s) (ht : Terminal pairs s none) (hw : Within g b advice [] s) : False := by
      obtain ⟨ha,he⟩ := terminalAllowed ht c g b advice (p := []) rfl .start hw
      obtain ⟨_,h,_⟩ := win _ none ha he
      cases h
    obtain ⟨x,y,z,hxy,hxz,hyz⟩ := triangle g hg b plan valid
    have edge {x y : Word} (hr : Realizes g b advice x y) : B.Adj x y := by
      obtain ⟨p,ha,he⟩ := realizedHistory hr c
      obtain ⟨w,hw,hwc⟩ := win p _ ha he
      cases Option.some.inj hw
      exact of_decide_eq_true hwc
    have adj {x y : Word} (hr : EitherOrder g b advice x y) : B.Adj x y :=
      hr.elim edge (fun h => (edge h).symm)
    exact (hb {x,y,z} (SimpleGraph.is3Clique_triple_iff.mpr ⟨adj hxy,adj hxz,adj hyz⟩)).elim
  · obtain ⟨s,hs,hit⟩ := red g hg b
    refine ⟨s,freeWordType hs,?_⟩
    intro x hx y hy hne
    have noEdge {x y : Word} (hr : Realizes g b (fun _ => none) x y) : ¬ B.Adj x y := by
      obtain ⟨p,ha,he⟩ := realizedHistory hr c
      exact of_decide_eq_false (right p (x,y) ha he)
    rw [hc.eq_compl,SimpleGraph.compl_adj]
    exact ⟨fun h => hne (congrArg Sigma.fst h),
      (hit x hx y hy hne).elim noEdge (fun h adj => noEdge h adj.symm)⟩

end Larson.PairGame

namespace Larson.PairGame
open Larson.Words

private def plainCuts : Cuts := ⟨[], fun _ => 0, fun _ => []⟩

private theorem within_append {g b plan p} (a d : List Action) :
    Within g b plan p (a ++ d) ↔ Within g b plan p a ∧ Within g b plan (p ++ moves a) d := by
  induction a generalizing p with
  | nil => simp [Within,moves]
  | cons x a ih =>
    cases x <;> simp [Within,moves,ih,List.append_assoc,and_assoc]

private theorem uninterrupted_append (a d : List Action) :
    uninterrupted (a ++ d) ↔ uninterrupted a ∧ uninterrupted d := by
  induction a with
  | nil => simp [uninterrupted]
  | cons x a ih => cases x <;> simp [uninterrupted,ih]

private theorem weaveSerial {a : List Action} (ha : uninterrupted a) {d : List Action}
    (hd : uninterrupted d) : Weave true a d (a ++ d) := by
  induction a with
  | nil => exact .endLeft hd
  | cons x a ih =>
    cases x with
    | pause => exact ha.elim
    | draw n => exact .drawLeft n (ih ha)
    | plan n => exact .planLeft n (ih ha)

private def GoodFor (g : ℕ → ℕ) (b : List ℕ → ℕ) (P : List (List ℕ)) (a : List Action) :=
  uninterrupted a ∧ ∀ p ∈ P, Within g b (fun _ => none) p a

private def afterScript (P : List (List ℕ)) (a : List Action) :=
  P.map (fun p => p ++ moves a)

private theorem goodAppend {g b P a d} (ha : GoodFor g b P a)
    (hd : GoodFor g b (afterScript P a) d) : GoodFor g b P (a ++ d) := by
  refine ⟨(uninterrupted_append ..).2 ⟨ha.1,hd.1⟩,fun p hp => (within_append ..).2 ?_⟩
  exact ⟨ha.2 _ hp,hd.2 _ (List.mem_map.mpr ⟨p,hp,rfl⟩)⟩

private theorem goodDraw (g : ℕ → ℕ) (b : List ℕ → ℕ) (P : List (List ℕ)) :
    ∃ n, GoodFor g b P [.draw n] := by
  let j := P.toFinset.sup b
  refine ⟨g j,trivial,fun p hp => ⟨⟨j,?_,rfl⟩,trivial⟩⟩
  exact Finset.le_sup (List.mem_toFinset.mpr hp)

private theorem goodVisit {I : Type} {g b} (cell : ℕ → I → List Action)
    (hcell : ∀ j P, ∃ i, GoodFor g b P (cell j i))
    (start h : ℕ) (P) : ∃ t : Tuple I h, GoodFor g b P (actionsOf cell start h t) := by
  induction h generalizing start P with
  | zero => exact ⟨(),trivial,fun _ _ => trivial⟩
  | succ h ih =>
    obtain ⟨i,hi⟩ := hcell start P
    obtain ⟨s,hs⟩ := ih (start+1) (afterScript P (cell start i))
    exact ⟨toLex (i,s),goodAppend hi hs⟩

private theorem goodPlainBlock (g b P) : ∃ t : Block, GoodFor g b P (blockActions [] t) := by
  obtain ⟨h,hh⟩ := goodDraw g b P
  obtain ⟨s,hs⟩ := goodVisit (leafActions []) (g := g) (b := b)
    (fun j Q => by simpa [leafActions] using goodDraw g b Q) 0 h (afterScript P [.draw h])
  exact ⟨⟨h,s⟩,goodAppend hh hs⟩

private def plainBody (x : Word) := [.draw x.1] ++
  actionsOf (cellActions plainCuts) 0 x.1 x.2

private theorem plain_eq (x : Word) :
    wordActions plainCuts x = .plan 0 :: plainBody x := rfl

private theorem goodPlainBody (g b P) : ∃ x : Word, GoodFor g b P (plainBody x) := by
  obtain ⟨h,hh⟩ := goodDraw g b P
  obtain ⟨s,hs⟩ := goodVisit (cellActions plainCuts) (g := g) (b := b)
    (fun j Q => by simpa [cellActions,plainCuts] using goodPlainBlock g b Q)
    0 h (afterScript P [.draw h])
  exact ⟨⟨h,s⟩,goodAppend hh hs⟩

private theorem actionsOf_all {I : Type} {cell : ℕ → I → List Action} {Q : Action → Prop}
    (hc : ∀ j i a, a ∈ cell j i → Q a) (start h : ℕ) (w : Tuple I h) :
    ∀ a ∈ actionsOf cell start h w, Q a := by
  induction h generalizing start with
  | zero => simp [actionsOf]
  | succ h ih =>
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hc _ _ _ ha
    · exact ih _ _ _ ha

private theorem plainDraws (x : Word) : ∀ a ∈ plainBody x, ∃ n, a = .draw n := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact ⟨_,List.mem_singleton.mp ha⟩
  · apply actionsOf_all (Q := fun a => ∃ n, a = .draw n) _ _ _ _ _ ha
    intro j t a ht
    simp only [cellActions,plainCuts,List.not_mem_nil,if_false,blockActions,List.map_nil,
      List.nil_append] at ht
    rcases List.mem_append.mp ht with ht | ht
    · exact ⟨_,List.mem_singleton.mp ht⟩
    · exact actionsOf_all (Q := fun a => ∃ n, a = .draw n)
        (fun j i a ha => ⟨i,by simpa [leafActions] using ha⟩) _ _ _ a ht

private theorem withinDrawOnly {g b p a} {f : List ℕ → Option ℕ}
    (hd : ∀ t ∈ a, ∃ n, t = Action.draw n)
    (h : Within g b (fun _ => none) p a) : Within g b f p a := by
  induction a generalizing p with
  | nil => trivial
  | cons x a ih =>
    obtain ⟨n,rfl⟩ := hd x (by simp)
    exact ⟨h.1,ih (fun t ht => hd t (List.mem_cons_of_mem _ ht)) h.2⟩

private def PScript (x : Word) := wordActions plainCuts x

private theorem choosePlain (g b : _) (P : List (List ℕ)) (f : List ℕ → ℕ)
    (hz : ∀ p ∈ P, f p = 0) : ∃ x, uninterrupted (PScript x) ∧
    ∀ p ∈ P, Within g b (fun q => some (f q)) p (PScript x) := by
  obtain ⟨x,hx⟩ := goodPlainBody g b (P.map (· ++ [0]))
  refine ⟨x,?_,?_⟩
  · simpa only [PScript,plain_eq,uninterrupted] using hx.1
  · intro p hp
    rw [PScript,plain_eq]
    exact ⟨by simp [hz p hp],withinDrawOnly (plainDraws x) (hx.2 _ (List.mem_map.mpr ⟨p,hp,rfl⟩))⟩

private def reach {I : Type} (g : ℕ → ℕ) (Q : I → Prop) : Thread I → Prop
  | .result x => Q x
  | .pause _ => True
  | .plan f => ∀ i, reach g Q (f i)
  | .draw f => ∀ k, ∃ j ≥ k, reach g Q (f (g j))

private theorem reachBind {I J : Type} {g} (t : Thread I) (f : I → Thread J) (Q) :
    reach g Q (t.bind f) ↔ reach g (fun x => reach g Q (f x)) t := by
  induction t with
  | result => rfl
  | pause => exact Iff.rfl
  | plan _ ih => exact forall_congr' ih
  | draw _ ih =>
    exact forall_congr' (fun k => exists_congr (fun j => and_congr_right (fun _ => ih _)))

private theorem reachTotal {I : Type} (g) (t : Thread I) : reach g (fun _ => True) t := by
  induction t with
  | result | pause => trivial
  | plan _ ih => exact ih
  | draw _ ih => exact fun k => ⟨k,le_rfl,ih _⟩

private theorem reachMono {I : Type} {g} (t : Thread I) {P Q} (h : ∀ i, P i → Q i) :
    reach g P t → reach g Q t := by
  induction t with
  | result a => exact h a
  | pause => exact id
  | plan _ ih => exact fun hp i => ih i (hp i)
  | draw _ ih =>
    intro hp k
    obtain ⟨j,hj,hq⟩ := hp k
    exact ⟨j,hj,ih _ hq⟩

private theorem lateIndices {g : ℕ → ℕ} (hg : StrictMono g) (k lo : ℕ) :
    reach g (fun v => lo ≤ v.2) (indices k) := by
  induction k with
  | zero =>
    intro l
    exact ⟨max l lo,le_max_left ..,(le_max_right ..).trans (hg.id_le _)⟩
  | succ k ih =>
    intro l
    exact ⟨l,le_rfl,(reachBind ..).2 ih⟩

private theorem markedIndices {g : ℕ → ℕ} (hg : StrictMono g) (k : ℕ) :
    reach g (fun v => ∃ j ∈ v.1, j < v.2) (indices (k+1)) := by
  intro l
  refine ⟨l,le_rfl,(reachBind ..).2 ?_⟩
  exact reachMono (indices k) (fun v (hv : g l + 1 ≤ v.2) =>
    show ∃ j ∈ (g l :: v.1), j < v.2 from ⟨_,List.mem_cons_self,hv⟩) (lateIndices hg k _)

private theorem reachVisit {I : Type} {g : ℕ → ℕ} (f : ℕ → Thread I)
    (s h : ℕ) (Q : Tuple I h → Prop)
    (hit : ∃ j, s ≤ j ∧ j < s+h ∧ reach g (fun _ => False) (f j)) :
    reach g Q (visit f s h) := by
  induction h generalizing s with
  | zero =>
    obtain ⟨_,h1,h2,_⟩ := hit
    omega
  | succ h ih =>
    obtain ⟨j,h1,h2,hh⟩ := hit
    apply (reachBind ..).2
    by_cases he : s = j
    · subst j
      exact reachMono _ (fun _ hc => hc.elim) hh
    · apply reachMono _ _ (reachTotal g _)
      intro i _
      apply (reachBind ..).2
      exact ih (s+1) _ ⟨j,by omega,by omega,hh⟩

private theorem cutBlock {g : ℕ → ℕ} (hg : StrictMono g) (k : ℕ) :
    reach g (fun _ => False) (drawBlock (k+1)) := by
  apply (reachBind ..).2
  apply reachMono _ _ (markedIndices hg k)
  rintro ⟨m,n⟩ ⟨j,hj,hn⟩
  apply (reachBind ..).2
  apply reachVisit
  refine ⟨j,Nat.zero_le _,by simpa using hn,?_⟩
  intro l
  exact ⟨l,le_rfl,by simp [hj,reach]⟩

private theorem cutRoot {g : ℕ → ℕ} (hg : StrictMono g) (k : ℕ) :
    reach g (fun _ => False) ((fun | Thread.plan f => f (k+1) | t => t) drawWord) := by
  change reach g _ ((indices (k+1)).bind _)
  apply (reachBind ..).2
  apply reachMono _ _ (markedIndices hg k)
  rintro ⟨m,n⟩ ⟨j,hj,hn⟩
  apply (reachBind ..).2
  apply reachVisit
  refine ⟨j,Nat.zero_le _,by simpa using hn,?_⟩
  simpa [hj,reach] using (cutBlock hg)

private theorem failFinish {I J : Type} {g} (b plan : List ℕ → ℕ) (k : I → J)
    {t : Thread I} (h : reach g (fun _ => False) t) (p : List ℕ) :
    ∃ a, Terminal (finish k t) a none ∧ Within g b (fun q => some (plan q)) p a := by
  induction t generalizing p with
  | result => exact h.elim
  | pause => exact ⟨[],.leaf _,trivial⟩
  | plan f ih =>
    obtain ⟨a,ha,hw⟩ := ih (plan p) (h _) (p ++ [plan p])
    exact ⟨_ ,Terminal.plan _ ha,by exact ⟨by simp,hw⟩⟩
  | draw f ih =>
    obtain ⟨j,hj,hq⟩ := h (b p)
    obtain ⟨a,ha,hw⟩ := ih (g j) hq (p ++ [g j])
    exact ⟨_ ,Terminal.draw _ ha,by exact ⟨⟨j,hj,rfl⟩,hw⟩⟩

private theorem serialTerminal {I J : Type} {t : Thread I} {x a} (ht : Trace t a x)
    (hu : uninterrupted a) {y : Thread J} {q r} (hq : Terminal (finish (x,·) y) q r) :
    Terminal (interleave t y) (a ++ q) r := by
  induction ht with
  | result => exact hq
  | pause => exact hu.elim
  | plan n _ ih => exact .plan n (ih hu hq)
  | draw n _ ih => exact .draw n (ih hu hq)

private theorem zeroAfterPlain {g : ℕ → ℕ} (hg : StrictMono g) {b plan : List ℕ → ℕ}
    (valid : ∀ script, Terminal pairs script none → ¬ Within g b (fun p => some (plan p)) [] script)
    {x : Word} (hu : uninterrupted (PScript x))
    (hx : Within g b (fun p => some (plan p)) [] (PScript x)) :
    plan (moves (PScript x)) = 0 := by
  cases hp : plan (moves (PScript x)) with
  | zero => rfl
  | succ k =>
    obtain ⟨q,hq,hw⟩ := failFinish b plan (x,·) (cutRoot hg k) (moves (PScript x) ++ [k+1])
    have ht : Terminal (finish (x,·) drawWord) (.plan (k+1) :: q) none := Terminal.plan _ hq
    apply False.elim
    apply valid _ (serialTerminal (wordTrace plainCuts x) hu ht)
    apply (within_append ..).2
    refine ⟨hx,?_⟩
    change Within g b _ (moves (PScript x)) (.plan (k+1) :: q)
    exact ⟨by simp [hp],hw⟩

theorem architectTriangleZeroRoot {g : ℕ → ℕ} (hg : StrictMono g) {b plan : List ℕ → ℕ}
    (zero : plan [] = 0)
    (valid : ∀ script, Terminal pairs script none → ¬ Within g b (fun p => some (plan p)) [] script) :
    ∃ x y z : Word, EitherOrder g b (fun p => some (plan p)) x y ∧
      EitherOrder g b (fun p => some (plan p)) x z ∧ EitherOrder g b (fun p => some (plan p)) y z := by
  let H (x : Word) := moves (PScript x)
  let W := Within g b (fun p => some (plan p))
  have edge {x y} (ux : uninterrupted (PScript x)) (uy : uninterrupted (PScript y))
      (hx : W [] (PScript x)) (hy : W (H x) (PScript y)) :
      EitherOrder g b (fun p => some (plan p)) x y :=
    Or.inl ⟨plainCuts,plainCuts,_,weaveSerial ux uy,(within_append ..).2 ⟨hx,hy⟩⟩
  obtain ⟨x,ux,hx⟩ := choosePlain g b [[]] plan (by simpa using zero)
  have xx := hx [] (by simp)
  have zx := zeroAfterPlain hg valid ux xx
  obtain ⟨y,uy,hy⟩ := choosePlain g b [[],H x] plan (by simp [H,zero,zx])
  have yy := hy [] (by simp)
  have zy := zeroAfterPlain hg valid uy yy
  obtain ⟨z,uz,hz⟩ := choosePlain g b [H x,H y] plan (by simp [H,zx,zy])
  exact ⟨x,y,z,edge ux uy xx (hy _ (by simp)),edge ux uz xx (hz _ (by simp)),
    edge uy uz yy (hz _ (by simp))⟩

end Larson.PairGame

namespace Larson.Staged
abbrev Tuple := Larson.Words.Tuple
abbrev Word := Larson.Words.Tower
abbrev Tree := Larson.Words.Word
namespace Word
abbrev mk {A : Type} (n : ℕ) (t : Tuple A n) : Word A := ⟨n,t⟩
theorem lt_iff {A : Type} [LinearOrder A] (u v : Word A) :
    u < v ↔ u.1 < v.1 ∨ ∃ h : u.1 = v.1, h ▸ u.2 < v.2 := by
  cases u with | mk n x =>
    cases v with | mk m y =>
      constructor
      · intro h
        cases h with
        | left _ _ h => exact Or.inl h
        | right _ _ h => exact Or.inr ⟨rfl,h⟩
      · rintro (h | ⟨h,hy⟩)
        · exact Sigma.Lex.left _ _ h
        · change n = m at h
          subst m
          exact Sigma.Lex.right _ _ hy
end Word
def FreeCompletions {X : Type} [LinearOrder X] : ℕ → ℕ → Set X → Prop
  | 0, 0, s => s.Nonempty
  | b+1, 0, s => ∀ k, ∃ m ≥ k, ∃ t ⊆ s, FreeCompletions b m t
  | b, l+1, s => ∃ t : ℕ → Set X, (∀ i, t i ⊆ s) ∧
      (∀ i j, i < j → ∀ x ∈ t i, ∀ y ∈ t j, x < y) ∧
      ∀ i, FreeCompletions b l (t i)
termination_by b l _ => (b,l)
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

def indices : ℕ → Script (List ℕ)
  | 0 => .done []
  | n+1 => .builder fun i => (indices n).bind fun rest => .done (i :: rest)

def children {A : Type} (child : ℕ → Script A) : (n start : ℕ) → Script (Tuple A n)
  | 0, _ => .done ()
  | n+1, start => (child start).bind fun x =>
      (children child n (start+1)).bind fun xs => .done (toLex (x,xs))

def node {A : Type} (markedCount : ℕ) (child : Bool → Script A) : Script (Word A) :=
  (indices markedCount).bind fun marked => .builder fun total =>
    (children (fun i => child (decide (i ∈ marked))) total 0).bind fun xs =>
      .done ⟨total,xs⟩

def leaf (marked : Bool) : Script ℕ :=
  .builder fun n => if marked then .cut (.done n) else .done n

def block (marked : Bool) : Script (Word ℕ) :=
  if marked then .architect fun n => node (n+1) leaf else node 0 leaf

def tree : Script (Word (Word ℕ)) := .architect fun n => node n block
end Script
def tokens {A : Type} (emit : A → List ℕ) : (l : ℕ) → Tuple A l → List ℕ
  | 0, _ => []
  | l+1, t => emit (ofLex t).1 ++ tokens emit l (ofLex t).2

def blockTokens (w : Word ℕ) := w.1 :: tokens (fun x => [x]) w.1 w.2

def transcript (w : Tree) := w.1 :: tokens blockTokens w.1 w.2
end Larson.Staged
namespace Larson.Staged

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
  | [] => ()
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
    (h : IndexedAll (fun i x => Reads (child (decide (i ∈ m))) (ev i x) (g x)) 0 xs) :
    Reads (Script.node m.length child) (nodeMoves m xs.length (indexedMoves ev 0 xs))
      ⟨xs.length,makeTuple g xs⟩ := by
  apply readsBind (readsIndices m)
  apply Reads.builder
  simpa using readsBind (k := fun t => Script.done (Word.mk xs.length t))
    (readsChildren _ g ev xs 0 h) (.done _)

private theorem indexedAllOfForall {A : Type} {P : ℕ → A → Prop} (h : ∀ i x, P i x)
    (xs : List A) (start : ℕ) : IndexedAll P start xs := by
  induction xs generalizing start with
  | nil => trivial
  | cons x xs ih => exact ⟨h _ _,ih _⟩

def MarkedBlock.moves (b : MarkedBlock) : List Event :=
  let body := nodeMoves b.marked b.leaves.length (indexedMoves (leafMoves b.marked) 0 b.leaves)
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
    (indexedMoves (fun _ b => b.moves) 0 t.blocks)

def MarkedTree.consistent (t : MarkedTree) :=
  IndexedAll (fun i (b : MarkedBlock) => i ∈ t.marked ↔ b.marked ≠ []) 0 t.blocks

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

def decorate (bs : List MarkedBlock) : MarkedTree := ⟨bs,activeBlocks 0 bs⟩

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
    let add (w : Tree) : Tree := ⟨w.1+1,toLex (b.word,w.2)⟩
    exact congrArg add (ih (i+1))

inductive Weave : Bool → List Event → List Event → List Event → Bool → Prop
  | finishLeft {s} : Event.cut ∉ s → Weave true [] s s false
  | finishRight {s} : Event.cut ∉ s → Weave false s [] s true
  | leftMove {e s t u b} : e ≠ .cut → Weave true s t u b →
      Weave true (e :: s) t (e :: u) b
  | rightMove {e s t u b} : e ≠ .cut → Weave false s t u b →
      Weave false s (e :: t) (e :: u) b
  | leftCut {s t u b} : Weave false s t u b → Weave true (.cut :: s) t u b
  | rightCut {s t u b} : Weave true s t u b → Weave false s (.cut :: t) u b
end Larson.Staged
namespace Larson.Staged

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
end Larson.Staged
namespace Larson.Staged

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

theorem spacedStageWeave {A : Type} (g : ℕ → ℕ) (hg : StrictMono g) (root : Script A)
    (i : ℕ) {l r s : List Event} {b : Bool} (hw : Weave true l r s b)
    (hs : Shrinks s (stageTrace g root i)) :
    (0 :: s.filterMap Event.number).Pairwise (· < ·) ∧ Spaced g [] s := by
  have hn : (0 :: (stageTrace g root i).filterMap Event.number).Pairwise (· < ·) := by
    simpa using stageTraceIncreasing g hg root i [] (by simp)
  exact ⟨hn.sublist ((shrinksNumbers hs).cons_cons 0),
    spacedOfRoom s [] 0 (hs.room 0 (by simpa using stageTraceRoom g root i [] trivial))
      (weaveCutFree hw) (by simp) (by simp)⟩

end Larson.Staged

namespace Larson.Staged
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
    let prepend (w : Word B) : Word B := ⟨w.1+1,toLex (val a,w.2)⟩
    exact ⟨a::bs,⟨ha,hbs⟩,by simp [indexedMoves],congrArg prepend he⟩

private theorem nodeOfRead {A B : Type} (child : Bool → Script B) (val : A → B)
    (ev : List ℕ → ℕ → A → List Event) (P : List ℕ → ℕ → A → Prop)
    (decode : ∀ m i s x, Reads (child (decide (i ∈ m))) s x →
      ∃ a, P m i a ∧ s = ev m i a ∧ x = val a)
    (n : ℕ) {s : List Event} {x : Word B} (h : Reads (node n child) s x) :
    ∃ m : List ℕ, ∃ bs : List A, m.length = n ∧ IndexedAll (P m) 0 bs ∧
      s = nodeMoves m bs.length (indexedMoves (ev m) 0 bs) ∧ x = ⟨bs.length,makeTuple val bs⟩ := by
  obtain ⟨m,u,v,hu,hv,rfl⟩ := splitRead (indices n) _ h
  obtain ⟨hn,rfl⟩ := indicesOfRead n hu
  cases hv with
  | @builder _ total _ _ hv =>
    obtain ⟨ys,w,z,hw,hz,rfl⟩ := splitRead (children _ total 0) _ hv
    cases hz
    obtain ⟨bs,hbs,rfl,he⟩ := childrenOfRead _ val (ev m) (P m) (decode m) total 0 hw
    have hl := congrArg Sigma.fst he
    refine ⟨m,bs,hn,hbs,?_,he⟩
    simpa only [nodeMoves,List.append_nil] using congrArg
      (fun a => m.map Event.builder ++ Event.builder a :: indexedMoves (ev m) 0 bs) hl

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

end Larson.Staged

namespace Larson.Staged

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

end Larson.Staged

namespace Larson.Staged
open Ordinal

private def OrderedCode {A : Type} [LT A] (code : A → List ℕ) :=
  ∀ x y, x < y → ∀ u v : List ℕ,
    List.Lex (· < ·) (code x ++ u) (code y ++ v)

private theorem tupleCode {A : Type} [LinearOrder A] (code : A → List ℕ)
    (hcode : OrderedCode code) (n : ℕ) : OrderedCode (tokens code n) := by
  induction n with
  | zero =>
    intro x y h
    cases x; cases y; exact (lt_irrefl _ h).elim
  | succ n ih =>
    rintro ⟨a,x⟩ ⟨b,y⟩ h u v
    rcases Prod.Lex.lt_iff.mp h with hab | ⟨rfl,hxy⟩
    · change List.Lex _ ((code a ++ tokens code n x) ++ u) ((code b ++ tokens code n y) ++ v)
      simpa only [List.append_assoc] using
        hcode a b hab (tokens code n x ++ u) (tokens code n y ++ v)
    · change List.Lex _ ((code a ++ tokens code n x) ++ u) ((code a ++ tokens code n y) ++ v)
      simpa only [List.append_assoc] using
        List.Lex.append_left (· < ·) (ih x y hxy u v) (code a)

private theorem wordCode {A : Type} [LinearOrder A] [WellFoundedLT A]
    (code : A → List ℕ) (hc : OrderedCode code) :
    OrderedCode (fun x : Word A => x.1 :: tokens code x.1 x.2) := by
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

end Larson.Staged

namespace Larson.Staged

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
  have he : activeBlocks 0 t.blocks = t.marked := by
    apply (activeSorted _ _).eq_of_mem_iff hm
    intro j
    rw [activeMem t.marked 0 j t.blocks hc]
    refine ⟨fun h => h.2.2,fun hj => ⟨?_,?_,hj⟩⟩
    · exact Nat.zero_le _
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
    (hf : IndexedAll (fun j x => f j = k x) 0 b.leaves) :
    LeafMask k ({b with marked := b.marked.filter f} : MarkedBlock).moves b.moves := by
  have hm : (b.marked.filter f).Sublist b.marked := List.filter_sublist
  have hs := (maskIndices k hm).append
    (LeafMask.builder b.leaves.length (maskLeaves k f b.marked 0 b.leaves hf))
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
      IndexedAll (fun v x => fs a v = k x) 0 b.leaves) i bs) :
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
  let bsAt (i : ℕ) := bs[i-0]?.getD ⟨[],[]⟩
  let fs (i j : ℕ) := k ((bsAt i).leaves[j-0]?.getD 0)
  have hf : IndexedAll (fun a (b : MarkedBlock) =>
      IndexedAll (fun v x => fs a v = k x) 0 b.leaves) 0 bs := by
    apply indexedChange _ _ (indexedLookup ⟨[],[]⟩ 0 bs)
    intro i _ b hb
    apply indexedChange _ _ (indexedLookup 0 0 b.leaves)
    intro j _ x hx
    change k ((bsAt i).leaves[j-0]?.getD 0) = k x
    change bsAt i = b at hb
    rw [hb,hx]
  refine ⟨decorate (pruneBlocks fs 0 bs),pruneWord _ _ _,consistentActive _ _,?_⟩
  have hm := pruneActive fs 0 bs
  simp only [MarkedTree.moves,decorate,pruneLength]
  exact .architect hm.length_le ((maskIndices k hm).append
    (.builder _ (maskBlocks k fs 0 0 bs hf)))

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

end Larson.Staged
namespace Larson.Staged

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
  let ms := (List.range' 0 b.leaves.length).filter (fun j => decide (j ∈ b.marked))
  have eq : ms = b.marked := by
    have hms : ms.Pairwise (· < ·) := (List.pairwise_lt_range' _ (by decide : 0 < 1)).sublist List.filter_sublist
    apply hms.eq_of_mem_iff hs
    intro j
    simp only [ms,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    intro hj
    have hpos' := hpos j (List.mem_append_left _ hj)
    have hlt := hcross j hj b.leaves.length List.mem_cons_self
    exact List.mem_range'.mpr ⟨j,by omega,by simp⟩
  have hl := controlLeaves b.marked 0 b.leaves
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
    ∃ ds : List ℕ, (∀ n ∈ ds, 0 < n) ∧ ds.length ≤ x.1 ∧
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
  · rw [← hx,degreesLength 0 bs]
    exact activeLength 0 bs
  · have hcontrol : (fun e : Event => e.number.isNone) = control := by funext e; cases e <;> rfl
    rw [← he,hcontrol,degreesLength 0 bs]
    simp [MarkedTree.moves,decorate,List.filter_cons,control,controlNode,controlBlocks bs 0 hbs]

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
      (nodeMoves b.marked b.leaves.length (indexedMoves (leafMoves b.marked) 0 b.leaves) ++ s) =
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
  have ht := readBlocksLabels t.blocks 0 []
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

private theorem switchesBlock (b : MarkedBlock) (hs : b.numbers.Pairwise (fun a b => a+1 < b)) :
    ProperSwitches b.moves := by
  have hp := (List.pairwise_append.mp hs).2.2
  have hu (j : ℕ) (hj : j ∈ b.marked) : j + 1 < 0+b.leaves.length := by
    have := hp j hj b.leaves.length List.mem_cons_self
    omega
  have hn := switchesNode b.marked b.leaves.length _ (switchesLeaves b.marked 0 b.leaves hu)
  dsimp only [MarkedBlock.moves]
  split <;> exact hn

private theorem switchesBlocks (bs : List MarkedBlock) (i : ℕ)
    (hs : (bs.flatMap MarkedBlock.numbers).Pairwise (fun a b => a+1 < b)) :
    ProperSwitches (indexedMoves (fun _ b => b.moves) i bs) := by
  induction bs generalizing i with
  | nil => trivial
  | cons b bs ih =>
    obtain ⟨hb,hbs,_⟩ := List.pairwise_append.mp hs
    exact switchesAppend _ _ (switchesBlock b hb) (ih _ hbs)

theorem nextLeafAfterSwitch {t : MarkedTree} {p s : List Event}
    (he : t.moves = p ++ .cut :: s) (hs : t.numbers.Pairwise (fun a b => a+1 < b)) :
    ∃ n u, s = .builder n :: u := by
  have hb := ((List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).2)
  have h : ProperSwitches t.moves :=
    switchesNode t.marked t.blocks.length _ (switchesBlocks _ 0 hb)
  rw [he] at h
  clear he
  induction p with
  | nil => exact h.1
  | cons e p ih =>
    cases e with
    | cut => exact ih h.2
    | builder | architect => exact ih h

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

private theorem roomRange (g : ℕ → ℕ) (s : List Event) (n : ℕ) (h : Room g n s) :
    ∀ v ∈ s.filterMap Event.number, ∃ j, g j = v := by
  induction s generalizing n with
  | nil => simp
  | cons e l ih =>
    cases e with
    | cut => exact ih _ h
    | architect a => exact ih _ h
    | builder a =>
      obtain ⟨⟨j,_,he⟩,hr⟩ := h
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨j,he⟩
      · exact ih _ hr _ hv

private theorem gapNumbers {g : ℕ → ℕ} (hg : StrictMono g) (gap : ∀ i, g i + 1 < g (i+1))
    (t : MarkedTree) (h : Room g 0 t.moves) (hs : t.numbers.Pairwise (· < ·)) :
    t.numbers.Pairwise (fun a b => a+1 < b) := by
  have ran := roomRange g _ _ h
  rw [MarkedTree.builderMoves] at ran
  apply hs.imp_of_mem
  intro a b ha hb hab
  obtain ⟨i,rfl⟩ := ran a ha
  obtain ⟨j,rfl⟩ := ran b hb
  exact (gap i).trans_le (hg.monotone (Nat.succ_le_of_lt (hg.lt_iff_lt.mp hab)))

theorem orderedStageChildren (g : ℕ → ℕ) (hg : StrictMono g) (gap : ∀ i, g i + 1 < g (i+1)) (i : ℕ) (u : List Event)
    (hu : branchTrace g Script.tree i = u ++ [.cut]) {t v : ℕ} (htv : t < v)
    (ht : (Nat.unpair t).1 = i) (hv : (Nat.unpair v).1 = i)
    {x y : Tree} (hx : x ∈ stageCone g (t+1)) (hy : y ∈ stageCone g (v+1)) : x < y := by
  have first (a : ℕ) (ha : (Nat.unpair a).1 = i) (z : Tree) (hz : z ∈ stageCone g (a+1)) :
      ∃ n s, n ∈ (stageBatch g Script.tree a).events.filterMap Event.number ∧
        Reads Script.tree (u ++ .cut :: .builder n :: s) z := by
    obtain ⟨j,hd,hj⟩ := hz
    obtain ⟨w,hw⟩ := finalPrefix g Script.tree hd
    rw [branchTrace,ha,hu,List.append_assoc,List.append_assoc] at hw
    obtain ⟨bs,hword,htrace,hrm⟩ := finalCanonicalDecoration g hg j z hj
    have hsort := stageTraceIncreasing g hg Script.tree j [] (by simp)
    rw [List.append_nil] at hsort
    have hnums := (List.pairwise_cons.mp (hsort.sublist ((shrinksNumbers
      (shrinksOfSublist (branchTraceSublist g Script.tree j))).cons_cons 0))).2
    rw [← htrace,MarkedTree.builderMoves] at hnums
    obtain ⟨n,s,he⟩ := nextLeafAfterSwitch (htrace.trans hw) (gapNumbers hg gap _ hrm hnums)
    have hne : (stageBatch g Script.tree a).events ≠ [] := by
      intro hnil
      have hz' : ∃ q, (stageBatch g Script.tree a).result = .inl q := by
        unfold stageBatch StageTable.batch at hnil ⊢
        split at hnil
        · exact ⟨_,rfl⟩
        · exact emptyBatch _ _ _ _ hnil
      obtain ⟨q,hq⟩ := hz'
      obtain ⟨bs',_,he',hrm'⟩ := finalCanonicalDecoration g hg (a+1) q ((newSlot ..).trans hq)
      have hqsort := stageTraceIncreasing g hg Script.tree (a+1) [] (by simp)
      rw [List.append_nil] at hqsort
      have hn := (List.pairwise_cons.mp (hqsort.sublist ((shrinksNumbers (shrinksOfSublist
        (branchTraceSublist g Script.tree (a+1)))).cons_cons 0))).2
      rw [← he',MarkedTree.builderMoves] at hn
      rw [branchTrace,ha,hu,hnil,List.append_nil] at he'
      obtain ⟨_,_,hf⟩ := nextLeafAfterSwitch (s := []) he' (gapNumbers hg gap _ hrm' hn)
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

end Larson.Staged

namespace Larson.Staged
open Ordinal

private theorem coneChild (g : ℕ → ℕ) {i t : ℕ} (hp : (Nat.unpair t).1 = i) :
    stageCone g (t+1) ⊆ stageCone g i := by
  rintro x ⟨j,hj,he⟩
  exact ⟨j,hj.head ⟨t,rfl,hp⟩,he⟩

private theorem freeStageCone (g : ℕ → ℕ) (hg : StrictMono g) (gap : ∀ i, g i+1 < g (i+1)) :
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
      stageCone g (t+1),coneChild g hp,freeStageCone g hg gap b r _ endCut ?_⟩
    exact fun j x hj hx tail ht => blockStep (hb j x hj hx tail ht)
  | b, l+1, i, ⟨u,hu⟩, hc => by
    rw [FreeCompletions]
    let t (n : ℕ) := Nat.pair i n
    have hp (n : ℕ) : (Nat.unpair (t n)).1 = i := by simp [t]
    refine ⟨fun n => stageCone g (t n+1),fun n => coneChild g (hp n),?_,?_⟩
    · intro n m hnm x hx y hy
      exact orderedStageChildren g hg gap i u hu (Nat.pair_lt_pair_right i hnm) (hp n) (hp m) hx hy
    · intro n
      obtain ⟨endCut,_,hb⟩ := childBudgetStep g hc (by omega) (t n) (hp n)
      exact freeStageCone g hg gap b l _ endCut (fun j x hj hx tail ht => leafStep (hb j x hj hx tail ht))
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

end Larson.Staged

namespace Larson.Staged

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

private theorem firstStageArity (g : ℕ → ℕ) (hg : StrictMono g) (j : ℕ) (x : Tree)
    (hj : (stageTable g Script.tree j).slot j = .inl x) :
    let ev := (stageBatch g Script.tree (firstStage j)).events
    (readWordLabels true 0 ev).head? = some x.1 ∧ x.1 ∈ ev.filterMap Event.number := by
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
  let m := activeBlocks 0 bs
  let header : List Event := .architect m.length :: m.map Event.builder ++ [.builder bs.length]
  have hhead : List.IsPrefix header (branchTrace g Script.tree j) := by
    rw [← hb]
    refine ⟨indexedMoves (fun _ b => b.moves) 0 bs,?_⟩
    simp [header,m,MarkedTree.moves,decorate,nodeMoves,List.append_assoc]
  have hnc : Event.cut ∉ header := by simp [header]
  obtain hh | hh := List.prefix_or_prefix_of_prefix hhead hc
  · obtain ⟨v,hv⟩ := hh
    change (readWordLabels true 0 chunk).head? = some x.1 ∧ x.1 ∈ chunk.filterMap Event.number
    rw [← hv,← hx]
    simp only [header,List.cons_append,List.append_assoc,readWordLabels,
      if_true,readIndexLabels,List.head?_cons,MarkedTree.word,decorate]
    simp [Event.number]
    exact ⟨.builder bs.length,Or.inr (Or.inl rfl),rfl⟩
  · exact (hnc (hh.sublist.subset hcut)).elim

private theorem orderedRoots (g : ℕ → ℕ) (hg : StrictMono g) {i j : ℕ} {x y : Tree}
    (hx : (stageTable g Script.tree i).slot i = .inl x)
    (hy : (stageTable g Script.tree j).slot j = .inl y) (hxy : x.1 < y.1) :
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
    (hx : x ∈ stagedWords g) (hy : y ∈ stagedWords g) (hxy : x.1 < y.1) :
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

end Larson.Staged

namespace Larson.Staged
open Larson.PairGame

private def toAction : Event → Action
  | .cut => .pause
  | .architect n => .plan n
  | .builder n => .draw n

private theorem noPause {s : List Event} (h : Event.cut ∉ s) :
    uninterrupted (s.map toAction) := by
  induction s with
  | nil => trivial
  | cons e s ih =>
    have hn := ih (fun he => h (List.mem_cons_of_mem e he))
    cases e with
    | cut => exact (h List.mem_cons_self).elim
    | architect | builder => exact hn

private theorem mapWeave {c l r s d} (h : Weave c l r s d) :
    PairGame.Weave c (l.map toAction) (r.map toAction) (s.map toAction) := by
  induction h with
  | finishLeft h => exact .endLeft (noPause h)
  | finishRight h => exact .endRight (noPause h)
  | leftCut _ ih => exact .switchLeft ih
  | rightCut _ ih => exact .switchRight ih
  | @leftMove e _ _ _ _ he _ ih =>
    cases e with
    | cut => exact (he rfl).elim
    | architect => exact .planLeft _ ih
    | builder => exact .drawLeft _ ih
  | @rightMove e _ _ _ _ he _ ih =>
    cases e with
    | cut => exact (he rfl).elim
    | architect => exact .planRight _ ih
    | builder => exact .drawRight _ ih

private theorem mapTimely {g h : ℕ → ℕ} {b : List ℕ → ℕ}
    (hb : ∀ k p, p.length ≤ k → (∀ x ∈ p, x ≤ k) → b p ≤ h k)
    (p : List ℕ) (s : List Event) (hs : Spaced (g ∘ h) p s) :
    Within g b (fun _ => none) p (s.map toAction) := by
  induction s generalizing p with
  | nil => trivial
  | cons e s ih =>
    cases e with
    | cut => exact hs.elim
    | architect n => exact ⟨by simp,ih _ hs⟩
    | builder n =>
      obtain ⟨⟨k,hl,hm,he⟩,hr⟩ := hs
      exact ⟨⟨h k,hb k p hl hm,he.symm⟩,ih _ hr⟩

private theorem mapLeafLabels (m : List ℕ) (i : ℕ) (xs : List ℕ) :
    (indexedMoves (leafMoves m) i xs).map toAction =
      actionsOf (leafActions m) i xs.length (makeTuple id xs) := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : i ∈ m <;> simp [indexedMoves,leafMoves,leafActions,makeTuple,
      actionsOf,h,toAction,ih]

private theorem mapBlockBody (m leaves : List ℕ) :
    (nodeMoves m leaves.length (indexedMoves (leafMoves m) 0 leaves)).map toAction =
      blockActions m (⟨leaves.length,makeTuple id leaves⟩ : Words.Block) := by
  simp [nodeMoves,blockActions,mapLeafLabels,List.map_map,Function.comp_def,toAction]

private def rowMarks (t : MarkedTree) (j : ℕ) : List ℕ :=
  (t.blocks[j]?.map MarkedBlock.marked).getD []

private def cutsFor (t : MarkedTree) : Cuts :=
  ⟨t.marked,fun j => (rowMarks t j).headD 0,fun j => (rowMarks t j).tail⟩

private theorem markLookup {A : Type} (f : A → List ℕ) (xs : List A) (start : ℕ)
    (m : ℕ → List ℕ)
    (lookup : ∀ n : Fin xs.length, m (start + n.val) = f xs[n]) :
    IndexedAll (fun j a => m j = f a) start xs := by
  induction xs generalizing start with
  | nil => trivial
  | cons a xs ih =>
    refine ⟨by simpa using lookup ⟨0,by simp⟩,ih (start+1) ?_⟩
    intro n
    simpa [Nat.add_assoc,Nat.add_comm 1 n.val] using
      lookup ⟨n.val+1,Nat.succ_lt_succ n.isLt⟩

private theorem mapTreeMoves (t : MarkedTree) (ht : t.consistent) :
    t.moves.map toAction = wordActions (cutsFor t) t.word := by
  have align (j : ℕ) (b : MarkedBlock) (hm : rowMarks t j = b.marked)
      (hc : j ∈ t.marked ↔ b.marked ≠ []) :
      b.moves.map toAction = cellActions (cutsFor t) j b.word := by
    rcases b with ⟨leaves,marked⟩
    cases marked with
    | nil =>
      have hn : j ∉ t.marked := fun hh => hc.mp hh rfl
      simp [MarkedBlock.moves,MarkedBlock.word,cellActions,cutsFor,hn,mapBlockBody]
    | cons x xs =>
      have hy : j ∈ t.marked := hc.mpr (by simp)
      change rowMarks t j = x :: xs at hm
      simp [MarkedBlock.moves,MarkedBlock.word,cellActions,cutsFor,hy,hm,toAction,mapBlockBody]
  have body (xs : List MarkedBlock) (i : ℕ)
      (h1 : IndexedAll (fun j a => rowMarks t j = a.marked) i xs)
      (h2 : IndexedAll (fun j a => j ∈ t.marked ↔ a.marked ≠ []) i xs) :
      (indexedMoves (fun _ a => a.moves) i xs).map toAction =
        actionsOf (cellActions (cutsFor t)) i xs.length (makeTuple MarkedBlock.word xs) := by
    induction xs generalizing i with
    | nil => rfl
    | cons a l ih =>
      simp only [indexedMoves,List.map_append,makeTuple,List.length_cons,actionsOf,
        ofLex_toLex,align i a h1.1 h2.1,ih (i+1) h1.2 h2.2]
  have hrows := markLookup MarkedBlock.marked t.blocks 0 (rowMarks t) (by
    intro n
    simp [rowMarks])
  have hb := body t.blocks 0 hrows ht
  simpa only [MarkedTree.moves,MarkedTree.word,wordActions,nodeMoves,List.map_cons,List.map_append,
    List.map_map,toAction,List.singleton_append,List.append_assoc,cutsFor,Function.comp_def] using
    congrArg (fun z => Action.plan t.marked.length ::
      (t.marked.map Action.draw ++ Action.draw t.blocks.length :: z)) hb

private theorem sectionsOfCompletions {X : Type} [LinearOrder X] :
    ∀ r k (s : Set X), FreeCompletions r k s → Words.FreeSection r k s
  | 0,0,s,h => .terminal (by simpa [FreeCompletions] using h)
  | r+1,0,s,h => by
    rw [FreeCompletions] at h
    choose width large child sub next using h
    exact .block child width large sub (fun i => sectionsOfCompletions r _ _ (next i))
  | r,k+1,s,h => by
    rw [FreeCompletions] at h
    obtain ⟨child,sub,sep,next⟩ := h
    exact .leaf child sub sep (fun i => sectionsOfCompletions r k _ (next i))
termination_by r k _ _ => (r,k)

private theorem largerSection {X : Type} [LinearOrder X] {r k : ℕ} {s t : Set X}
    (h : Words.FreeSection r k s) (sub : s ⊆ t) : Words.FreeSection r k t := by
  cases h with
  | terminal hn => exact .terminal (hn.mono sub)
  | leaf f inc sep next => exact .leaf f (fun i => (inc i).trans sub) sep next
  | block f w hw inc next => exact .block f w hw (fun i => (inc i).trans sub) next

private theorem stageFree (g : ℕ → ℕ) (hg : StrictMono g) (gap : ∀ i, g i+1 < g (i+1)) (n : ℕ) :
    ∃ r k, n ≤ r ∧ Words.FreeSection r k (stagedWords g) := by
  let t := Nat.pair 0 n
  let r := (stageTable g Script.tree t).bound
  have hn : n ≤ t := by simpa [t] using Nat.unpair_right_le (Nat.pair 0 n)
  obtain ⟨hend,hbudget⟩ := initialStageBudget g hg n
  have free := sectionsOfCompletions _ _ _ (freeStageCone g hg gap r (r+1) (t+1) hend hbudget)
  have sub : stageCone g (t+1) ⊆ stagedWords g := by
    rintro x ⟨j,_,hj⟩
    exact ⟨j,hj⟩
  refine ⟨r,r+1,hn.trans ((stageBoundMono g Script.tree).id_le t),?_⟩
  exact largerSection free sub

theorem builderFamily : PairGame.BuilderFamily := by
  intro g hg b
  obtain ⟨h,hh,hb⟩ := thinCutoffs b
  let H (i : ℕ) := h (2*i)
  let f := g ∘ H
  have hH : StrictMono H := fun _ _ hlt => hh (by omega)
  have hf : StrictMono f := hg.comp hH
  have gap (i : ℕ) : f i + 1 < f (i+1) :=
    (Nat.succ_le_of_lt (hg (hh (Nat.lt_succ_self (2*i))))).trans_lt
      (hg (hh (show 2*i+1 < 2*(i+1) by omega)))
  have bound k p hl hm : b p ≤ H k := (hb k p hl hm).trans (hh.monotone (by omega))
  refine ⟨stagedWords f,stageFree f hf gap,?_⟩
  have pair {x y : Tree} (hx : x ∈ stagedWords f) (hy : y ∈ stagedWords f) (hl : x.1 < y.1) :
      Realizes g b (fun _ => none) x y := by
    obtain ⟨t,u,s,_,rfl,rfl,ht,hu,hw,_,hs⟩ := stagePair f hf hx hy hl
    refine ⟨cutsFor t,cutsFor u,s.map toAction,?_,mapTimely bound [] s hs⟩
    rw [← mapTreeMoves t ht,← mapTreeMoves u hu]
    exact mapWeave hw
  intro x hx y hy hn
  exact (lt_or_gt_of_ne hn).elim (fun hl => Or.inl (pair hx hy hl))
    (fun hl => Or.inr (pair hy hx hl))

end Larson.Staged

namespace Larson.PairGame
open Filter Larson.Words

private theorem finiteChoiceOften {V : Type} [Finite V] (f : ℕ → V) :
    ∃ v, ∀ᶠ i in hyperfilter ℕ, f i = v :=
  Ultrafilter.eventually_exists_iff.mp (Eventually.of_forall (fun i => ⟨f i,rfl⟩))

private noncomputable def forecast {A V : Type} [Finite V]
    (g : ℕ → ℕ) (plan : List ℕ → ℕ) (read : List ℕ → Option A → V) :
    OutcomeTree A → List ℕ → V
  | .leaf o, p => read p o
  | .plan f, p => forecast g plan read (f (plan p)) (p ++ [plan p])
  | .draw f, p => (finiteChoiceOften (fun i =>
      forecast g plan read (f (g i)) (p ++ [g i]))).choose

theorem predictAtPrefixes {A : Type} (root : OutcomeTree A) (g : ℕ → ℕ)
    (plan : List ℕ → ℕ) (V : List ℕ → Type) [∀ a, Finite (V a)]
    (read : (a : List ℕ) → List ℕ → Option A → V a) :
    ∃ h : ℕ → ℕ, StrictMono h ∧ ∃ cutoff : List ℕ → ℕ, ∃ predicted : (a : List ℕ) → V a,
      ∀ a s o, Terminal (a.foldl OutcomeTree.move root) s o →
        Within (g ∘ h) cutoff (fun p => some (plan p)) a s →
        read a (a ++ moves s) o = predicted a := by
  classical
  let pos (p : List ℕ) := p.foldl OutcomeTree.move root
  let F (a p : List ℕ) := forecast g plan (read a) (pos p) p
  let key (a p : List ℕ) := Encodable.encode (a,p)
  let hist (i : ℕ) := (Encodable.decode (α := List ℕ × List ℕ) i).getD ([],[])
  let stable (a p : List ℕ) (i : ℕ) := match pos p with
    | .draw f => forecast g plan (read a) (f (g i)) (p ++ [g i]) = F a p
    | _ => True
  have often (a p) : ∀ᶠ i in hyperfilter ℕ, stable a p i := by
    cases he : pos p with
    | leaf | plan => simp [stable,he]
    | draw f =>
      simpa only [stable,F,he,forecast] using (finiteChoiceOften (fun i =>
        forecast g plan (read a) (f (g i)) (p ++ [g i]))).choose_spec
  obtain ⟨h,hh,keep⟩ := Larson.Game.diagonal (P := fun i j => stable (hist i).1 (hist i).2 j)
    (fun i => often _ _)
  let cutoff (p : List ℕ) := (Finset.range (p.length+1)).sup (fun i => key (p.take i) p)
  have kept (a p : List ℕ) (ha : a <+: p) (j : ℕ) (hj : cutoff p ≤ j) : stable a p (h j) := by
    have he : key a p ≤ cutoff p := by
      have hi := Finset.le_sup (f := fun i => key (p.take i) p)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le ha.length_le))
      simpa only [← List.prefix_iff_eq_take.mp ha] using hi
    have unpack : hist (key a p) = (a,p) := congrArg
      (fun z : Option (List ℕ × List ℕ) => z.getD ([],[])) (Encodable.encodek (a,p))
    have found := keep (key a p) j (he.trans hj)
    rw [unpack] at found
    exact found
  have run (a p : List ℕ) (ha : a <+: p) {t s o} (he : pos p = t)
      (ht : Terminal t s o)
      (hs : Within (g ∘ h) cutoff (fun p => some (plan p)) p s) :
      read a (p ++ moves s) o = F a p := by
    induction ht generalizing p with
    | leaf o => simp [F,he,forecast,moves]
    | @plan f tail o i ht ih =>
      have hei : i = plan p := hs.1 _ rfl
      have hp : pos (p ++ [i]) = f i := by simp [pos,List.foldl_append,show p.foldl _ root = _ from he,OutcomeTree.move]
      have tailEq :=  ih _ (List.prefix_append_of_prefix ha) hp hs.2
      have step : F a (p ++ [i]) = F a p := by
        simp only [F,hp,he,forecast,← hei]
      simpa only [moves,List.append_assoc,List.singleton_append] using tailEq.trans step
    | @draw f tail o i ht ih =>
      obtain ⟨j,hj,hij⟩ := hs.1
      have hp : pos (p ++ [i]) = f i := by simp [pos,List.foldl_append,show p.foldl _ root = _ from he,OutcomeTree.move]
      have tailEq :=  ih _ (List.prefix_append_of_prefix ha) hp hs.2
      have step := kept a p ha j hj
      simp only [stable,he] at step
      have eq : F a (p ++ [i]) = F a p := by
        rw [show F a (p ++ [i]) = forecast g plan (read a) (f i) (p ++ [i]) by simp only [F,hp]]
        simpa only [← show i = g (h j) from hij] using step
      simpa only [moves,List.append_assoc,List.singleton_append] using tailEq.trans eq
  exact ⟨h,hh,cutoff,fun a => F a a,fun a _ _ ht hs => run a a (List.prefix_refl _) rfl ht hs⟩

private theorem withinThin {g h : ℕ → ℕ} {b c : List ℕ → ℕ} {plan}
    (hb : ∀ p j, c p ≤ j → b p ≤ h j) {p s} (hs : Within (g ∘ h) c plan p s) :
    Within g b plan p s := by
  induction s generalizing p with
  | nil => trivial
  | cons a s ih =>
    cases a with
    | pause => exact hs.elim
    | plan i => exact ⟨hs.1,ih hs.2⟩
    | draw i =>
      obtain ⟨j,hj,he⟩ := hs.1
      exact ⟨⟨h j,hb _ _ hj,he⟩,ih hs.2⟩

private theorem eitherThin {g h : ℕ → ℕ} {b c : List ℕ → ℕ} {plan}
    (hb : ∀ p j, c p ≤ j → b p ≤ h j) {x y} :
    EitherOrder (g ∘ h) c plan x y → EitherOrder g b plan x y := by
  have one {x y} (hxy : Realizes (g ∘ h) c plan x y) : Realizes g b plan x y := by
    obtain ⟨u,v,s,w,hs⟩ := hxy
    exact ⟨u,v,s,w,withinThin hb hs⟩
  exact Or.imp one one

abbrev MakesTriangle (g : ℕ → ℕ) (b plan : List ℕ → ℕ) :=
  ∃ x y z : Word, EitherOrder g b (fun p => some (plan p)) x y ∧
    EitherOrder g b (fun p => some (plan p)) x z ∧ EitherOrder g b (fun p => some (plan p)) y z

theorem crossBlockOfArchitect (tri : ArchitectTriangle) : Words.CrossBlock :=
  crossBlockOfRealization Larson.Staged.builderFamily tri

end Larson.PairGame

theorem Larson.larsonOfArchitect (tri : Larson.PairGame.ArchitectTriangle) :
    type_of% @Erdos118.erdos_118.variants.larson :=
  Larson.fromCrossBlock (Larson.PairGame.crossBlockOfArchitect tri)

theorem Larson.parentOfArchitect (tri : Larson.PairGame.ArchitectTriangle) :
    type_of% @Erdos118.erdos_118 := by
  let h := Larson.larsonOfArchitect.{0} tri
  intro claim
  exact h.2 (claim (ω ^ ω ^ (2 : Ordinal)) h.1 5 (by decide))

namespace Larson.PairGame
open Larson.Words

def planned : List Action → List ℕ
  | [] => []
  | .plan n :: s => n :: planned s
  | .draw _ :: s | .pause :: s => planned s

private def withPlans {A : Type} (t : Thread A) (ds : List ℕ) : Thread (A × List ℕ) :=
  match t with
  | .result x => .result (x,ds)
  | .pause q => .pause (withPlans q ds)
  | .draw f => .draw (fun j => withPlans (f j) ds)
  | .plan f => .plan (fun j => withPlans (f j) (ds ++ [j]))

private theorem traceWithPlans {A : Type} {t : Thread A} {a s} (ht : Trace t s a) (ds) :
    Trace (withPlans t ds) s (a,ds ++ planned s) := by
  induction ht generalizing ds with
  | result => simp [planned,withPlans,Trace.result]
  | pause _ ih => exact .pause (ih _)
  | draw n _ ih => exact .draw n (ih _)
  | plan n _ ih => exact .plan n (by simpa [planned,List.append_assoc] using ih (ds ++ [n]))

private theorem suffixTerminal {A : Type} {t : OutcomeTree A} {o s} (hs : Terminal t s o)
    {u v : List Action} (he : s = u ++ v) :
    Terminal ((moves u).foldl OutcomeTree.move t) v o := by
  induction u generalizing s t with
  | nil => simpa [he,moves] using hs
  | cons a u ih =>
    subst s
    cases hs with
    | plan n ht => exact ih ht rfl
    | draw n ht => exact ih ht rfl

def cutLocation (k : ℕ) : List ℕ → ℕ × ℕ
  | [] => (0,0)
  | d :: ds =>
    if k ≤ d then (0,0) else
      let v := cutLocation (k-(d+1)) ds
      (v.1+1,v.2+(d+1))

private theorem locationBound (k : ℕ) (ds : List ℕ) :
    (cutLocation k ds).1 ≤ (cutLocation k ds).2 ∧ (cutLocation k ds).2 ≤ k := by
  induction ds generalizing k with
  | nil => exact ⟨le_rfl,Nat.zero_le _⟩
  | cons d ds ih =>
    by_cases h : k ≤ d
    · simp [cutLocation,h]
    · obtain ⟨hj,hs⟩ := ih (k-(d+1))
      simp only [cutLocation,if_neg h]
      omega

theorem cutLocationSpec (ds : List ℕ) (k : ℕ) (hk : k < (ds.map (·+1)).sum) :
    ∃ before d after, ds = before ++ d :: after ∧
      cutLocation k ds = (before.length,(before.map (·+1)).sum) ∧
      (before.map (·+1)).sum ≤ k ∧ k < (before.map (·+1)).sum + (d+1) := by
  induction ds generalizing k with
  | nil => simp at hk
  | cons d ds ih =>
    by_cases h : k ≤ d
    · exact ⟨[],d,ds,rfl,by simp [cutLocation,h],Nat.zero_le _,by simpa using Nat.lt_succ_of_le h⟩
    · simp only [List.map_cons,List.sum_cons] at hk
      obtain ⟨pre,e,tail,he,hp,hl,hu⟩ := ih (k-(d+1)) (by omega)
      refine ⟨d::pre,e,tail,congrArg (List.cons d) he,?_,?_,?_⟩
      · simp [cutLocation,h,hp,Nat.add_comm]
      · simp only [List.map_cons,List.sum_cons]
        omega
      · simp only [List.map_cons,List.sum_cons]
        omega

theorem predictRightCut (g : ℕ → ℕ) (bound plan : List ℕ → ℕ) (query : List ℕ → ℕ) :
    ∃ h : ℕ → ℕ, StrictMono h ∧ ∃ cutoff : List ℕ → ℕ,
      (∀ p j, cutoff p ≤ j → bound p ≤ h j) ∧ ∃ predicted : List ℕ → ℕ × ℕ,
      ∀ (c d : Cuts) (x y : Word) (pre tail : List Action),
        Weave true (wordActions c x) (wordActions d y) (pre ++ tail) →
        Within (g ∘ h) cutoff (fun p => some (plan p)) [] (pre ++ tail) →
        cutLocation (query (moves pre)) (planned (wordActions d y)).tail = predicted (moves pre) := by
  let root := interleave (withPlans drawWord []) (withPlans drawWord [])
  let V (p : List ℕ) := Fin (query p+1) × Fin (query p+1)
  let stat (p : List ℕ) (_ : List ℕ) (r : Option ((Word × List ℕ) × Word × List ℕ)) : V p :=
    let ds := (r.map (fun xy => xy.2.2.tail)).getD []
    let v := cutLocation (query p) ds
    let hv := locationBound (query p) ds
    (⟨v.1,Nat.lt_succ_of_le (hv.1.trans hv.2)⟩,⟨v.2,Nat.lt_succ_of_le hv.2⟩)
  obtain ⟨h,hh,b,pred,hp⟩ := predictAtPrefixes root g plan V stat
  let cutoff (p : List ℕ) := max (bound p) (b p)
  refine ⟨h,hh,cutoff,fun p j hj => ((le_max_left ..).trans hj).trans (hh.id_le j),
    fun p => ((pred p).1.val,(pred p).2.val),?_⟩
  intro c d x y pre tail hw legal
  have trace := weaveTrace hw (traceWithPlans (wordTrace c x) []) (traceWithPlans (wordTrace d y) [])
  have terminal := suffixTerminal trace (u := pre) (v := tail) rfl
  have hs := (within_append pre tail).mp legal |>.2
  have within := withinThin (g := g ∘ h) (h := id) (b := b) (c := cutoff)
    (fun _ _ hj => (le_max_right ..).trans hj) hs
  have eq := hp (moves pre) tail _ terminal (by simpa using within)
  exact congrArg (fun v : V (moves pre) => (v.1.val,v.2.val)) eq

end Larson.PairGame

namespace Larson.PairGame

def pauseCount : List Action → ℕ
  | [] => 0
  | .pause :: s => pauseCount s + 1
  | .plan _ :: s | .draw _ :: s => pauseCount s

private theorem noPauses (s : List Action) : uninterrupted s ↔ pauseCount s = 0 := by
  induction s with
  | nil => simp [uninterrupted,pauseCount]
  | cons e s ih => cases e <;> simp [uninterrupted,pauseCount,ih]

def balanced (side : Bool) (l r : List Action) :=
  if side then pauseCount r ≤ pauseCount l ∧ pauseCount l ≤ pauseCount r + 1
  else pauseCount l ≤ pauseCount r ∧ pauseCount r ≤ pauseCount l + 1

private theorem weaveBalance {side l r s} (h : Weave side l r s) : balanced side l r := by
  induction h with
  | endLeft h | endRight h => simp [balanced,pauseCount,(noPauses _).mp h]
  | switchLeft _ ih | switchRight _ ih => simp [balanced,pauseCount] at *; omega
  | planLeft _ _ ih | planRight _ _ ih | drawLeft _ _ ih | drawRight _ _ ih => exact ih

end Larson.PairGame

namespace Larson.PairGame
open Larson.Words

private def countSwitches {A : Type} (t : Thread A) (m : ℕ) : Thread (A × ℕ) :=
  match t with
  | .result x => .result (x,m)
  | .pause q => .pause (countSwitches q (m+1))
  | .draw f => .draw (fun j => countSwitches (f j) m)
  | .plan f => .plan (fun j => countSwitches (f j) m)

private theorem traceCount {A : Type} {t : Thread A} {s x} (h : Trace t s x) (m : ℕ) :
    Trace (countSwitches t m) s (x,m + pauseCount s) := by
  induction h generalizing m with
  | result y => simpa [countSwitches,pauseCount] using Trace.result (y,m)
  | pause _ ih =>
    apply Trace.pause
    simpa only [pauseCount,Nat.add_assoc,Nat.add_comm 1] using ih (m+1)
  | draw n _ ih => exact .draw n (ih _)
  | plan n _ ih => exact .plan n (ih _)

def EndOrder (g : ℕ → ℕ) (b plan : List ℕ → ℕ) (inside : Bool) : Prop :=
  ∀ c d x y s, Weave true (wordActions c x) (wordActions d y) s →
    Within g b (fun p => some (plan p)) [] s →
    pauseCount (wordActions c x) = pauseCount (wordActions d y) + (if inside then 1 else 0)

theorem thinEndOrder (g : ℕ → ℕ) (b plan : List ℕ → ℕ) :
    ∃ h : ℕ → ℕ, StrictMono h ∧ ∃ c : List ℕ → ℕ,
      (∀ p j, c p ≤ j → b p ≤ h j) ∧ ∃ mode, EndOrder (g ∘ h) c plan mode := by
  let root := interleave (countSwitches drawWord 0) (countSwitches drawWord 0)
  let label (_ _ : List ℕ) (r : Option ((Word × ℕ) × Word × ℕ)) :=
    r.elim false (fun xy => decide (xy.2.2 < xy.1.2))
  obtain ⟨h,hh,b',pred,forced⟩ := predictAtPrefixes root g plan (fun _ => Bool) label
  let c (p : List ℕ) := max (b p) (b' p)
  refine ⟨h,hh,c,fun p j hj => ((le_max_left ..).trans hj).trans (hh.id_le j),pred [],?_⟩
  intro cut mark x y s weave legal
  have ht := weaveTrace weave (traceCount (wordTrace cut x) 0) (traceCount (wordTrace mark y) 0)
  have law := withinThin (g := g ∘ h) (h := id) (b := b') (c := c)
    (fun _ _ hj => (le_max_right ..).trans hj) legal
  have chosen := forced [] s _ ht law
  simp only [label,Option.elim_some,Nat.zero_add] at chosen
  have hb := weaveBalance weave
  simp only [balanced,if_true] at hb
  cases he : pred [] with
  | false =>
    rw [he] at chosen
    have := of_decide_eq_false chosen
    simp
    omega
  | true =>
    rw [he] at chosen
    have := of_decide_eq_true chosen
    simp
    omega

inductive Played {A : Type} : OutcomeTree A → List Action → OutcomeTree A → Prop where
  | nil (t) : Played t [] t
  | plan {f s t} (n) : Played (f n) s t → Played (.plan f) (.plan n :: s) t
  | draw {f s t} (n) : Played (f n) s t → Played (.draw f) (.draw n :: s) t

theorem Played.finishPlay {A : Type} {t u : OutcomeTree A} {s q o}
    (h : Played t s u) (k : Terminal u q o) : Terminal t (s ++ q) o := by
  induction h with
  | nil => exact k
  | plan n _ ih => exact .plan n (ih k)
  | draw n _ ih => exact .draw n (ih k)

private theorem legalCompletion {A : Type} (t : OutcomeTree A) (g : ℕ → ℕ) (b plan : List ℕ → ℕ) (p : List ℕ) :
    ∃ s o, Terminal t s o ∧ Within g b (fun q => some (plan q)) p s := by
  induction t generalizing p with
  | leaf o => exact ⟨[],o,.leaf _,trivial⟩
  | plan f ih =>
    obtain ⟨s,o,hs,hw⟩ := ih (plan p) (p ++ [plan p])
    exact ⟨_,o,.plan _ hs,(by exact ⟨fun _ h => Option.some.inj h,hw⟩)⟩
  | draw f ih =>
    obtain ⟨s,o,hs,hw⟩ := ih (g (b p)) (p ++ [g (b p)])
    exact ⟨_,o,.draw _ hs,(by exact ⟨⟨b p,le_rfl,rfl⟩,hw⟩)⟩

private theorem finishInv {A B : Type} (k : A → B) (x : Thread A) {s r}
    (ht : Terminal (finish k x) s (some r)) :
    ∃ a, Trace x s a ∧ uninterrupted s ∧ k a = r := by
  induction x generalizing s with
  | result a => cases ht; exact ⟨a,.result _,trivial,rfl⟩
  | pause => cases ht
  | plan f ih =>
    cases ht with | plan n h =>
      obtain ⟨a,h1,h2,h3⟩ := ih n h
      exact ⟨a,.plan _ h1,h2,h3⟩
  | draw f ih =>
    cases ht with | draw n h =>
      obtain ⟨a,h1,h2,h3⟩ := ih n h
      exact ⟨a,.draw _ h1,h2,h3⟩

theorem interleaveInv {A B : Type} (x : Thread A) (y : Thread B) {s a b}
    (h : Terminal (interleave x y) s (some (a,b))) :
    ∃ l r, Trace x l a ∧ Trace y r b ∧ Weave true l r s := by
  induction x generalizing y s with
  | result c =>
    obtain ⟨b',hr,hu,he⟩ := finishInv (c,·) y h
    cases he
    exact ⟨[],s,.result _,hr,.endLeft hu⟩
  | plan f ih =>
    cases h with | plan n ht =>
      obtain ⟨l,r,hl,hr,hw⟩ := ih n y ht
      exact ⟨_,r,.plan n hl,hr,.planLeft n hw⟩
  | draw f ih =>
    cases h with | draw n ht =>
      obtain ⟨l,r,hl,hr,hw⟩ := ih n y ht
      exact ⟨_,r,.draw n hl,hr,.drawLeft n hw⟩
  | pause x ih =>
    change Terminal (runRight (interleave x) (fun b => finish (·,b) x) y) _ _ at h
    suffices ∃ l r, Trace x l a ∧ Trace y r b ∧ Weave false l r s by
      obtain ⟨l,r,hl,hr,hw⟩ := this
      exact ⟨_,r,.pause hl,hr,.switchLeft hw⟩
    induction y generalizing s with
    | result c =>
      obtain ⟨a',hl,hu,he⟩ := finishInv (·,c) x h
      cases he
      exact ⟨s,[],hl,.result _,.endRight hu⟩
    | pause y _ =>
      obtain ⟨l,r,hl,hr,hw⟩ := ih y h
      exact ⟨l,_,hl,.pause hr,.switchRight hw⟩
    | plan f ihy =>
      cases h with | plan n ht =>
        obtain ⟨l,r,hl,hr,hw⟩ := ihy n ht
        exact ⟨l,_,hl,.plan n hr,.planRight n hw⟩
    | draw f ihy =>
      cases h with | draw n ht =>
        obtain ⟨l,r,hl,hr,hw⟩ := ihy n ht
        exact ⟨l,_,hl,.draw n hr,.drawRight n hw⟩

private theorem splitTrace {A B : Type} (t : Thread A) (k : A → Thread B) {s b}
    (h : Trace (t.bind k) s b) :
    ∃ l r a, Trace t l a ∧ Trace (k a) r b ∧ s = l ++ r := by
  induction t generalizing s with
  | result a => exact ⟨[],s,a,.result _,h,rfl⟩
  | pause q ih =>
    cases h with | pause ht =>
      obtain ⟨l,r,a,h1,h2,rfl⟩ := ih ht
      exact ⟨_,r,a,.pause h1,h2,rfl⟩
  | plan f ih =>
    cases h with | plan n ht =>
      obtain ⟨l,r,a,h1,h2,rfl⟩ := ih n ht
      exact ⟨_,r,a,.plan n h1,h2,rfl⟩
  | draw f ih =>
    cases h with | draw n ht =>
      obtain ⟨l,r,a,h1,h2,rfl⟩ := ih n ht
      exact ⟨_,r,a,.draw n h1,h2,rfl⟩

private theorem indicesInv (k : ℕ) {s p} (h : Trace (indices k) s p) :
    p.1.length = k ∧ s = p.1.map Action.draw ++ [.draw p.2] := by
  induction k generalizing s p with
  | zero => cases h with | draw n ht => cases ht; exact ⟨rfl,rfl⟩
  | succ k ih =>
    cases h with | draw n ht =>
      obtain ⟨l,r,q,h1,h2,rfl⟩ := splitTrace (indices k) _ ht
      cases h2
      obtain ⟨hlen,rfl⟩ := ih h1
      simp [hlen]

private theorem actionsOf_agree {I : Type} (f g : ℕ → I → List Action) (i h : ℕ) (w : Tuple I h)
    (he : ∀ j ≥ i, f j = g j) : actionsOf f i h w = actionsOf g i h w := by
  induction h generalizing i with
  | zero => rfl
  | succ h ih =>
    simp only [actionsOf,he i le_rfl]
    rw [ih (i+1) _ (fun j hj => he j (by omega))]

private theorem visitInv {I D : Type} [Inhabited D] (child : ℕ → Thread I)
    (cell : D → ℕ → I → List Action)
    (one : ∀ j a s, Trace (child j) s a → ∃ d, s = cell d j a)
    (i h : ℕ) {w : Tuple I h} {s} (tr : Trace (visit child i h) s w) :
    ∃ ds : ℕ → D, s = actionsOf (fun j => cell (ds j) j) i h w := by
  induction h generalizing i s with
  | zero => cases tr; exact ⟨fun _ => default,rfl⟩
  | succ h ih =>
    obtain ⟨l,r,a,ha,ht,rfl⟩ := splitTrace (child i) _ tr
    obtain ⟨l',r',tail,hr,hend,rfl⟩ := splitTrace (visit child (i+1) h) _ ht
    cases hend
    obtain ⟨d,rfl⟩ := one i a l ha
    obtain ⟨ds,rfl⟩ := ih (i+1) hr
    refine ⟨Function.update ds i d,?_⟩
    simp only [List.append_nil,actionsOf,ofLex_toLex,Function.update_self]
    congr 1
    apply actionsOf_agree
    intro j hj
    rw [Function.update_of_ne (by omega : j ≠ i)]

private theorem blockInv (k : ℕ) {s b} (h : Trace (drawBlock k) s b) :
    ∃ marks, marks.length = k ∧ s = blockActions marks b := by
  obtain ⟨_,_,⟨marks,n⟩,hi,ht,rfl⟩ := splitTrace (indices k) _ h
  obtain ⟨hk,rfl⟩ := indicesInv k hi
  let child j := Thread.draw fun a : ℕ =>
    if j ∈ marks then Thread.pause (.result a) else .result a
  obtain ⟨_,_,w,hr,he,rfl⟩ := splitTrace (visit child 0 n) _ ht
  cases he
  have one (j a : ℕ) (s) (hh : Trace (child j) s a) : ∃ _ : Unit, s = leafActions marks j a := by
    cases hh with | draw n ht =>
      by_cases hm : j ∈ marks
      · simp only [hm,if_true] at ht
        cases ht with | pause ht => cases ht; exact ⟨(),by simp [leafActions,hm]⟩
      · simp only [hm,if_false] at ht
        cases ht
        exact ⟨(),by simp [leafActions,hm]⟩
  obtain ⟨_,eq⟩ := visitInv child (fun _ : Unit => leafActions marks) one 0 n hr
  exact ⟨marks,hk,by simp [eq,blockActions]⟩

theorem wordTraceInv {s w} (h : Trace drawWord s w) : ∃ c, s = wordActions c w := by
  cases h with | plan k ht =>
    obtain ⟨_,_,⟨marks,n⟩,hi,childTrace,rfl⟩ := splitTrace (indices k) _ ht
    obtain ⟨hk,rfl⟩ := indicesInv k hi
    let child j := if j ∈ marks then Thread.plan (fun d => drawBlock (d+1)) else drawBlock 0
    let cell (d : ℕ × List ℕ) (j : ℕ) (b : Block) :=
      if j ∈ marks then Action.plan d.2.length :: blockActions (d.1 :: d.2) b else blockActions [] b
    obtain ⟨_,_,w,hr,he,rfl⟩ := splitTrace (visit child 0 n) _ childTrace
    cases he
    have one (j : ℕ) (b : Block) (s) (hh : Trace (child j) s b) : ∃ d, s = cell d j b := by
      by_cases hm : j ∈ marks
      · simp only [child,hm,if_true] at hh
        cases hh with | plan d hh =>
          obtain ⟨ms,hlen,rfl⟩ := blockInv _ hh
          cases ms with
          | nil => simp at hlen
          | cons a rest =>
            simp only [List.length_cons,Nat.succ.injEq] at hlen
            exact ⟨(a,rest),by simp [cell,hm,hlen]⟩
      · simp only [child,hm,if_false] at hh
        obtain ⟨ms,hlen,rfl⟩ := blockInv 0 hh
        obtain rfl := List.length_eq_zero_iff.mp hlen
        exact ⟨(0,[]),by simp [cell,hm]⟩
    obtain ⟨ds,rfl⟩ := visitInv child cell one 0 n hr
    exact ⟨⟨marks,fun j => (ds j).1,fun j => (ds j).2⟩,by simp [wordActions,hk]; rfl⟩

inductive Coupled {A B : Type} (R : A → B → Prop) : Thread A → Thread B → Type 1 where
  | result {a b} (h : R a b) : Coupled R (.result a) (.result b)
  | planL {f y} (next : ∀ n, Coupled R (f n) y) : Coupled R (.plan f) y
  | planR {x f} (next : ∀ n, Coupled R x (f n)) : Coupled R x (.plan f)
  | drawL {f y} (lo : ℕ) (next : ∀ n ≥ lo, Coupled R (f n) y) : Coupled R (.draw f) y
  | drawR {x f} (lo : ℕ) (next : ∀ n ≥ lo, Coupled R x (f n)) : Coupled R x (.draw f)
  | drawBoth {f h} (lo : ℕ) (next : ∀ n ≥ lo, Coupled R (f n) (h n)) : Coupled R (.draw f) (.draw h)
  | pauseL {x y} (next : Coupled R x y) : Coupled R (.pause x) y
  | pauseR {x y} (next : Coupled R x y) : Coupled R x (.pause y)
  | pauseBoth {x y} (next : Coupled R x y) : Coupled R (.pause x) (.pause y)
  | inspect {x y} (next : List ℕ → List ℕ → Coupled R x y) : Coupled R x y

def Coupled.bind {A B C D : Type} {R : A → B → Prop} {S : C → D → Prop}
    {x : Thread A} {y : Thread B} (p : Coupled R x y)
    (f : A → Thread C) (h : B → Thread D)
    (k : ∀ a b, R a b → Coupled S (f a) (h b)) :
    Coupled S (x.bind f) (y.bind h) :=
  match p with
  | .result r => k _ _ r
  | .planL next => .planL fun n => (next n).bind f h k
  | .planR next => .planR fun n => (next n).bind f h k
  | .drawL lo next => .drawL lo fun n hn => (next n hn).bind f h k
  | .drawR lo next => .drawR lo fun n hn => (next n hn).bind f h k
  | .drawBoth lo next => .drawBoth lo fun n hn => (next n hn).bind f h k
  | .pauseL next => .pauseL (next.bind f h k)
  | .pauseR next => .pauseR (next.bind f h k)
  | .pauseBoth next => .pauseBoth (next.bind f h k)
  | .inspect next => .inspect fun a b => (next a b).bind f h k

inductive ReadBy where | left | right | both deriving DecidableEq

def arities : List ReadBy → ℕ × ℕ
  | [] => (0,0)
  | .left :: ms => ((arities ms).1+1,(arities ms).2)
  | .right :: ms => ((arities ms).1,(arities ms).2+1)
  | .both :: ms => ((arities ms).1+1,(arities ms).2+1)

inductive Placed : ℕ → List ReadBy → (List ℕ × ℕ) → (List ℕ × ℕ) → Prop where
  | nil {lo n} (h : lo ≤ n) : Placed lo [] ([],n) ([],n)
  | left {lo n ms l r z} (h : lo ≤ n) (tail : Placed (n+1) ms l r) (hz : z = l.2) :
      Placed lo (.left :: ms) (n::l.1,z) r
  | right {lo n ms l r z} (h : lo ≤ n) (tail : Placed (n+1) ms l r) (hz : z = r.2) :
      Placed lo (.right :: ms) l (n::r.1,z)
  | both {lo n ms l r} (h : lo ≤ n) (tail : Placed (n+1) ms l r) :
      Placed lo (.both :: ms) (n::l.1,l.2) (n::r.1,r.2)

private theorem Placed.same {lo ms l r} (h : Placed lo ms l r) : l.2 = r.2 := by
  induction h <;> simp_all

private theorem bindReturn {A : Type} (p : Thread A) : p.bind Thread.result = p := by
  induction p with
  | result => rfl
  | pause _ ih => simp [Thread.bind,ih]
  | plan f ih => simp [Thread.bind,funext ih]
  | draw f ih => simp [Thread.bind,funext ih]

def coupledIndices (ms : List ReadBy) (lo : ℕ) :
    Coupled (Placed lo ms) (indices (arities ms).1) (indices (arities ms).2) :=
  match ms with
  | [] => .drawBoth lo fun n hn => .result (.nil hn)
  | .left :: ms => .drawL lo fun n hn => by
    change Coupled _ _ (indices (arities ms).2)
    rw [← bindReturn (indices (arities ms).2)]
    exact (coupledIndices ms (n+1)).bind _ Thread.result fun _ _ ht => .result (.left hn ht rfl)
  | .right :: ms => .drawR lo fun n hn => by
    change Coupled _ (indices (arities ms).1) _
    rw [← bindReturn (indices (arities ms).1)]
    exact (coupledIndices ms (n+1)).bind Thread.result _ fun _ _ ht => .result (.right hn ht rfl)
  | .both :: ms => .drawBoth lo fun n hn =>
    (coupledIndices ms (n+1)).bind _ _ fun _ _ ht => .result (.both hn ht)

private def coupledVisit {I : Type} (f h : ℕ → Thread I) (step : ∀ j, Coupled Eq (f j) (h j))
    (i : ℕ) : (n : ℕ) → Coupled Eq (visit f i n) (visit h i n)
  | 0 => .result rfl
  | n+1 => (step i).bind _ _ fun a b he => by
    subst b
    exact (coupledVisit f h step (i+1) n).bind _ _ fun _ _ eq => .result (congrArg (fun s => toLex (a,s)) eq)

private def leafProgram (m : List ℕ) (j : ℕ) : Thread ℕ :=
  .draw fun a => if j ∈ m then .pause (.result a) else .result a

private def coupledLeafEnd (P Q : Prop) (p : Decidable P) (q : Decidable Q) (n : ℕ) :
    Coupled Eq (@ite _ P p (Thread.pause (.result n)) (.result n))
      (@ite _ Q q (Thread.pause (.result n)) (.result n)) := by
  cases p <;> cases q
  · exact .result rfl
  · exact .pauseR (.result rfl)
  · exact .pauseL (.result rfl)
  · exact .pauseBoth (.result rfl)

private def coupledLeaf (m r : List ℕ) (j : ℕ) : Coupled Eq (leafProgram m j) (leafProgram r j) :=
  .drawBoth 0 fun a _ => coupledLeafEnd (j ∈ m) (j ∈ r) inferInstance inferInstance a

def coupledBlock (ms : List ReadBy) :
    Coupled Eq (drawBlock (arities ms).1) (drawBlock (arities ms).2) :=
  (coupledIndices ms 0).bind _ _ fun ⟨m,n⟩ ⟨r,t⟩ hp => by
    have he : n = t := hp.same
    subst t
    exact (coupledVisit (leafProgram m) (leafProgram r) (coupledLeaf m r) 0 n).bind _ _
      fun _ _ eq => .result (congrArg (fun s => (⟨n,s⟩ : Block)) eq)

abbrev Arrangement := (a b : ℕ) → List ℕ → List ℕ → {ms : List ReadBy // arities ms = (a,b)}

private def selectedBlock (a b : ℕ) (ms : List ReadBy) (hm : arities ms = (a,b)) :
    Coupled Eq (drawBlock a) (drawBlock b) := by
  obtain rfl : (arities ms).1 = a := congrArg Prod.fst hm
  obtain rfl : (arities ms).2 = b := congrArg Prod.snd hm
  exact coupledBlock ms

private def arrangedBlock (pick : Arrangement) (a b : ℕ) : Coupled Eq (drawBlock a) (drawBlock b) :=
  .inspect fun h k => selectedBlock a b (pick a b h k).1 (pick a b h k).2

private def cellProgram (P Q : Prop) (p : Decidable P) (q : Decidable Q) (pick : Arrangement) :
    Coupled Eq (@ite _ P p (Thread.plan fun d => drawBlock (d+1)) (drawBlock 0))
      (@ite _ Q q (Thread.plan fun d => drawBlock (d+1)) (drawBlock 0)) := by
  cases p <;> cases q
  · exact arrangedBlock pick 0 0
  · exact .planR fun b => arrangedBlock pick 0 (b+1)
  · exact .planL fun a => arrangedBlock pick (a+1) 0
  · exact .planL fun a => .planR fun b => arrangedBlock pick (a+1) (b+1)

private def coupledCell (m r : List ℕ) (j : ℕ) (pick : Arrangement) :
    Coupled Eq (if j ∈ m then Thread.plan fun d => drawBlock (d+1) else drawBlock 0)
      (if j ∈ r then Thread.plan fun d => drawBlock (d+1) else drawBlock 0) :=
  cellProgram (j ∈ m) (j ∈ r) inferInstance inferInstance pick

private def wordRows (p : List ℕ × ℕ) : Thread Word :=
  (visit (fun j => if j ∈ p.1 then Thread.plan (fun d => drawBlock (d+1)) else drawBlock 0) 0 p.2).bind
    (fun w => .result ⟨p.2,w⟩)

private def selectedWord (a b : ℕ) (ms : List ReadBy) (hm : arities ms = (a,b))
    (leaf : ℕ → Arrangement) :
    Coupled Eq ((indices a).bind wordRows) ((indices b).bind wordRows) := by
  obtain rfl : (arities ms).1 = a := congrArg Prod.fst hm
  obtain rfl : (arities ms).2 = b := congrArg Prod.snd hm
  apply (coupledIndices ms 0).bind
  intro ⟨m,n⟩ ⟨r,t⟩ hp
  have he : n = t := hp.same
  subst t
  exact (coupledVisit _ _ (fun j => coupledCell m r j (leaf j)) 0 n).bind _ _
    fun _ _ eq => .result (congrArg (fun s => (⟨n,s⟩ : Word)) eq)

def coupledWord (root : Arrangement) (leaf : ℕ → Arrangement) : Coupled Eq drawWord drawWord :=
  .planL fun a => .planR fun b => .inspect fun h k =>
    selectedWord a b (root a b h k).1 (root a b h k).2 leaf

end Larson.PairGame

namespace Larson.PairGame

inductive Fragment {A : Type} : Thread A → List Action → Thread A → Prop where
  | nil (x) : Fragment x [] x
  | plan {f s x} (n) : Fragment (f n) s x → Fragment (.plan f) (.plan n :: s) x
  | draw {f s x} (n) : Fragment (f n) s x → Fragment (.draw f) (.draw n :: s) x

inductive Handoff {A B : Type} (R : A → B → Prop) : Thread A → Thread B → Type 1 where
  | done {a b} (h : R a b) : Handoff R (.result a) (.result b)
  | left {x y} (next : Coupled R x y) : Handoff R (.pause x) y
  | right {x y} (next : Coupled R x y) : Handoff R x (.pause y)
  | both {x y} (next : Coupled R x y) : Handoff R (.pause x) (.pause y)

noncomputable def Coupled.height {A B : Type} {R : A → B → Prop} {x : Thread A} {y : Thread B}
    (p : Coupled R x y) : Ordinal.{0} :=
  match p with
  | .result _ => 1
  | .planL f => Order.succ (⨆ n, (f n).height)
  | .planR f => Order.succ (⨆ n, (f n).height)
  | .drawL lo f => Order.succ (⨆ n : {n : ℕ // lo ≤ n}, (f n.1 n.2).height)
  | .drawR lo f => Order.succ (⨆ n : {n : ℕ // lo ≤ n}, (f n.1 n.2).height)
  | .drawBoth lo f => Order.succ (⨆ n : {n : ℕ // lo ≤ n}, (f n.1 n.2).height)
  | .pauseL q => Order.succ q.height
  | .pauseR q => Order.succ q.height
  | .pauseBoth q => Order.succ q.height
  | .inspect f => Order.succ (⨆ h : List ℕ × List ℕ, (f h.1 h.2).height)

noncomputable def Handoff.height {A B : Type} {R : A → B → Prop} {x : Thread A} {y : Thread B}
    (s : Handoff R x y) : Ordinal.{0} :=
  match s with
  | .done _ => 0
  | .left q => q.height
  | .right q => q.height
  | .both q => q.height

private theorem branch_lt {I : Type} (f : I → Ordinal.{0}) (i : I) :
    f i < Order.succ (⨆ j, f j) := (Ordinal.le_iSup f i).trans_lt (Order.lt_succ _)

structure Batch {A B : Type} (R : A → B → Prop) (x : Thread A) (y : Thread B)
    (g : ℕ → ℕ) (b plan : List ℕ → ℕ) (p q : List ℕ) (budget : Ordinal.{0}) : Type 1 where
  l : List Action
  r : List Action
  left : Thread A
  right : Thread B
  leftTrace : Fragment x l left
  rightTrace : Fragment y r right
  leftLegal : Within g b (fun h => some (plan h)) p l
  rightLegal : Within g b (fun h => some (plan h)) q r
  stop : Handoff R left right
  decreases : stop.height < budget

noncomputable def Coupled.nextHandoff {A B : Type} {R : A → B → Prop} {x : Thread A} {y : Thread B}
    (program : Coupled R x y) (g : ℕ → ℕ) (hg : StrictMono g) (b plan : List ℕ → ℕ)
    (p q : List ℕ) : Batch R x y g b plan p q program.height := by
  have ge (n : ℕ) : n ≤ g n := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hg (Nat.lt_succ_self n)))
  induction program generalizing p q with
  | result h => exact ⟨[],[],_,_,.nil _,.nil _,trivial,trivial,.done h,zero_lt_one⟩
  | pauseL next _ => exact ⟨[],[],_,_,.nil _,.nil _,trivial,trivial,.left next,Order.lt_succ _⟩
  | pauseR next _ => exact ⟨[],[],_,_,.nil _,.nil _,trivial,trivial,.right next,Order.lt_succ _⟩
  | pauseBoth next _ => exact ⟨[],[],_,_,.nil _,.nil _,trivial,trivial,.both next,Order.lt_succ _⟩
  | inspect f ih =>
    let t := ih p q p q
    exact {t with decreases := t.decreases.trans (branch_lt (fun h : List ℕ × List ℕ => (f h.1 h.2).height) (p,q))}
  | planL next ih =>
    obtain ⟨l,r,x,y,h,k,hl,hr,stop,dec⟩ := ih (plan p) (p ++ [plan p]) q
    exact ⟨_,_,_,_,.plan _ h,k,⟨by simp,hl⟩,hr,stop,dec.trans (branch_lt (fun n => (next n).height) (plan p))⟩
  | planR next ih =>
    obtain ⟨l,r,x,y,h,k,hl,hr,stop,dec⟩ := ih (plan q) p (q ++ [plan q])
    exact ⟨_,_,_,_,h,.plan _ k,hl,⟨by simp,hr⟩,stop,dec.trans (branch_lt (fun n => (next n).height) (plan q))⟩
  | drawL lo next ih =>
    let j := max lo (b p)
    have lower : lo ≤ g j := (le_max_left ..).trans (ge j)
    obtain ⟨l,r,x,y,h,k,hl,hr,stop,dec⟩ := ih (g j) lower (p ++ [g j]) q
    exact ⟨_,_,_,_,.draw _ h,k,⟨⟨j,le_max_right ..,rfl⟩,hl⟩,hr,stop,dec.trans (branch_lt (fun n : {n : ℕ // lo ≤ n} => (next n.1 n.2).height) ⟨_,lower⟩)⟩
  | drawR lo next ih =>
    let j := max lo (b q)
    have lower : lo ≤ g j := (le_max_left ..).trans (ge j)
    obtain ⟨l,r,x,y,h,k,hl,hr,stop,dec⟩ := ih (g j) lower p (q ++ [g j])
    exact ⟨_,_,_,_,h,.draw _ k,hl,⟨⟨j,le_max_right ..,rfl⟩,hr⟩,stop,dec.trans (branch_lt (fun n : {n : ℕ // lo ≤ n} => (next n.1 n.2).height) ⟨_,lower⟩)⟩
  | drawBoth lo next ih =>
    let j := max lo (max (b p) (b q))
    have lower : lo ≤ g j := (le_max_left ..).trans (ge j)
    obtain ⟨l,r,x,y,h,k,hl,hr,stop,dec⟩ := ih (g j) lower (p ++ [g j]) (q ++ [g j])
    exact ⟨_,_,_,_,.draw _ h,.draw _ k,⟨⟨j,(le_max_left ..).trans (le_max_right ..),rfl⟩,hl⟩,
      ⟨⟨j,(le_max_right ..).trans (le_max_right ..),rfl⟩,hr⟩,stop,dec.trans (branch_lt (fun n : {n : ℕ // lo ≤ n} => (next n.1 n.2).height) ⟨_,lower⟩)⟩

end Larson.PairGame

namespace Larson.PairGame
open ReadBy

private theorem arities_append (m n : List ReadBy) : arities (m ++ n) =
    ((arities m).1 + (arities n).1,(arities m).2 + (arities n).2) := by
  induction m with
  | nil => simp [arities]
  | cons e m ih => cases e <;> simp [arities,ih,Nat.succ_add]

private theorem arities_copies (n : ℕ) :
    arities (List.replicate n left) = (n,0) ∧ arities (List.replicate n right) = (0,n) := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => simp [List.replicate_succ,arities,ih.1,ih.2]

def apart (backwards : Bool) (a b : ℕ) : {ms : List ReadBy // arities ms = (a,b)} := by
  let A := List.replicate a left
  let B := List.replicate b right
  cases backwards with
  | false => exact ⟨A++B,by simp [A,B,arities_append,(arities_copies _).1,(arities_copies _).2]⟩
  | true => exact ⟨B++A,by simp [A,B,arities_append,(arities_copies _).1,(arities_copies _).2]⟩

def overlap (backwards : Bool) (a b i j h : ℕ) : {ms : List ReadBy // arities ms = (a,b)} := by
  if ok : i+1+h ≤ a ∧ j < b then
    let pre := apart backwards i j
    let seq := pre.val ++ [both] ++ List.replicate h left ++
      List.replicate (b-j-1) right ++ List.replicate (a-(i+1+h)) left
    refine ⟨seq,?_⟩
    simp only [seq,arities_append,pre.property,(arities_copies _).1,(arities_copies _).2,
      arities,Prod.mk.injEq]
    omega
  else exact apart backwards a b

def outsideArrangement (atY atZ : Bool) : Arrangement :=
  fun a b _ _ => if atY then overlap false a b (a-1) 0 0 else apart atZ a b

def outsideLeafArrangement : Arrangement :=
  fun a b _ _ => overlap false a b (a-1) 0 0

def insideRootX : Arrangement := fun a b _ _ => overlap false a b 0 0 0
def insideRootY (target : ℕ) : Arrangement := fun a b _ _ => overlap false a b target (b-1) 0
def insideRootZ : Arrangement := fun a b _ _ => overlap false a b (a-1) 0 0

def insideLeafX (k : ℕ) (before : List ℕ → ℕ) : Arrangement := fun a b p _ =>
  let pivot := if k = 1 then 1 else a
  let n := if k = 1 then 0 else before p
  overlap false a b n 0 (pivot-n-1)

def insideLeafY (pivot preceding : ℕ) : Arrangement := fun a b _ _ =>
  overlap true a b (pivot-preceding-1) (b-1) 0

def insideLeafZ : Arrangement := fun a b _ _ => overlap false a b (a-1) 0 0

end Larson.PairGame

namespace Larson.PairGame

inductive PairState (A B : Type) where
  | left (x : Thread A) (y : Thread B)
  | right (x : Thread A) (y : Thread B)
  | onlyLeft (x : Thread A) (b : B)
  | onlyRight (a : A) (y : Thread B)
  | done (a : A) (b : B)

def PairState.tree {A B : Type} : PairState A B → OutcomeTree (A × B)
  | .left x y => interleave x y
  | .right x y => runRight (interleave x) (fun b => finish (·,b) x) y
  | .onlyLeft x b => finish (·,b) x
  | .onlyRight a y => finish (a,·) y
  | .done a b => .leaf (some (a,b))

def PairState.accepts {A B : Type} (t : PairState A B) (l r s : List Action) (a : A) (b : B) :=
  match t with
  | .left x y => Trace x l a ∧ Trace y r b ∧ Weave true l r s
  | .right x y => Trace x l a ∧ Trace y r b ∧ Weave false l r s
  | .onlyLeft x b' => Trace x l a ∧ b = b' ∧ r = [] ∧ uninterrupted l ∧ s = l
  | .onlyRight a' y => Trace y r b ∧ a = a' ∧ l = [] ∧ uninterrupted r ∧ s = r
  | .done a' b' => a = a' ∧ b = b' ∧ l = [] ∧ r = [] ∧ s = []

private theorem PairState.decode {A B : Type} (t : PairState A B) {s a b}
    (h : Terminal t.tree s (some (a,b))) : ∃ l r, t.accepts l r s a b := by
  cases t with
  | left x y => exact interleaveInv x y h
  | right x y =>
    obtain ⟨l,r,hl,hr,hw⟩ := interleaveInv (.pause x) y h
    cases hl with | pause hleft =>
      cases hw with | switchLeft step => exact ⟨_,r,hleft,hr,step⟩
  | onlyLeft x b' =>
    obtain ⟨a',h1,h2,he⟩ := finishInv (·,b') x h
    cases he
    exact ⟨s,[],h1,rfl,rfl,h2,rfl⟩
  | onlyRight a' y =>
    obtain ⟨b',h1,h2,he⟩ := finishInv (a',·) y h
    cases he
    exact ⟨[],s,h1,rfl,rfl,h2,rfl⟩
  | done a' b' => cases h; exact ⟨[],[],rfl,rfl,rfl,rfl,rfl⟩

inductive PairStep {A B : Type} :
    PairState A B → List Action → List Action → List Action → PairState A B → Prop where
  | pl {f y} (i) : PairStep (.left (.plan f) y) [.plan i] [] [.plan i] (.left (f i) y)
  | dl {f y} (i) : PairStep (.left (.draw f) y) [.draw i] [] [.draw i] (.left (f i) y)
  | sl {x y} : PairStep (.left (.pause x) y) [.pause] [] [] (.right x y)
  | el {a y} : PairStep (.left (.result a) y) [] [] [] (.onlyRight a y)
  | pr {x f} (i) : PairStep (.right x (.plan f)) [] [.plan i] [.plan i] (.right x (f i))
  | dr {x f} (i) : PairStep (.right x (.draw f)) [] [.draw i] [.draw i] (.right x (f i))
  | sr {x y} : PairStep (.right x (.pause y)) [] [.pause] [] (.left x y)
  | er {x b} : PairStep (.right x (.result b)) [] [] [] (.onlyLeft x b)
  | pal {f b} (i) : PairStep (.onlyLeft (.plan f) b) [.plan i] [] [.plan i] (.onlyLeft (f i) b)
  | dal {f b} (i) : PairStep (.onlyLeft (.draw f) b) [.draw i] [] [.draw i] (.onlyLeft (f i) b)
  | eal {a b} : PairStep (.onlyLeft (.result a) b) [] [] [] (.done a b)
  | par {a f} (i) : PairStep (.onlyRight a (.plan f)) [] [.plan i] [.plan i] (.onlyRight a (f i))
  | dar {a f} (i) : PairStep (.onlyRight a (.draw f)) [] [.draw i] [.draw i] (.onlyRight a (f i))
  | ear {a b} : PairStep (.onlyRight a (.result b)) [] [] [] (.done a b)

theorem PairStep.played {A B : Type} {t u : PairState A B} {l r s}
    (h : PairStep t l r s u) : Played t.tree s u.tree := by
  cases h <;> first | exact .nil _ | exact .plan _ (.nil _) | exact .draw _ (.nil _)

theorem PairStep.prepend {A B : Type} {t u : PairState A B} {l r s l' r' s' a b}
    (step : PairStep t l r s u) (h : u.accepts l' r' s' a b) :
    t.accepts (l++l') (r++r') (s++s') a b := by
  cases step with
  | pl n => exact ⟨.plan n h.1,h.2.1,.planLeft n h.2.2⟩
  | dl n => exact ⟨.draw n h.1,h.2.1,.drawLeft n h.2.2⟩
  | sl => exact ⟨.pause h.1,h.2.1,.switchLeft h.2.2⟩
  | el =>
    obtain ⟨hr,rfl,rfl,hu,rfl⟩ := h
    exact ⟨.result _,hr,.endLeft hu⟩
  | pr n => exact ⟨h.1,.plan n h.2.1,.planRight n h.2.2⟩
  | dr n => exact ⟨h.1,.draw n h.2.1,.drawRight n h.2.2⟩
  | sr => exact ⟨h.1,.pause h.2.1,.switchRight h.2.2⟩
  | er =>
    obtain ⟨hl,rfl,rfl,hu,rfl⟩ := h
    exact ⟨hl,.result _,.endRight hu⟩
  | pal n | dal n | par n | dar n =>
    obtain ⟨hr,rfl,rfl,hu,rfl⟩ := h
    first | exact ⟨.plan n hr,rfl,rfl,hu,rfl⟩ | exact ⟨.draw n hr,rfl,rfl,hu,rfl⟩
  | eal | ear =>
    obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := h
    exact ⟨.result _,rfl,rfl,trivial,rfl⟩

inductive PairPath {A B : Type} :
    PairState A B → List Action → List Action → List Action → PairState A B → Prop where
  | nil (t) : PairPath t [] [] [] t
  | cons {t v u x y z l r s} : PairStep t x y z v → PairPath v l r s u →
      PairPath t (x++l) (y++r) (z++s) u

theorem Played.append {A : Type} {t v u : OutcomeTree A} {p q}
    (h : Played t p v) (k : Played v q u) : Played t (p++q) u := by
  induction h with
  | nil => exact k
  | plan n _ ih => exact .plan n (ih k)
  | draw n _ ih => exact .draw n (ih k)

theorem PairPath.played {A B : Type} {t u : PairState A B} {x y z}
    (h : PairPath t x y z u) : Played t.tree z u.tree := by
  induction h with
  | nil => exact .nil _
  | cons step _ ih => exact step.played.append ih

theorem PairPath.prepend {A B : Type} {t u : PairState A B} {x y z l r s a b}
    (path : PairPath t x y z u) (h : u.accepts l r s a b) :
    t.accepts (x++l) (y++r) (z++s) a b := by
  induction path with
  | nil => exact h
  | cons step _ ih => simpa only [List.append_assoc] using step.prepend (ih h)

theorem extendLocalPrefixes (g : ℕ → ℕ) (b plan : List ℕ → ℕ)
    (valid : ∀ s, Terminal pairs s none → ¬ Within g b (fun p => some (plan p)) [] s)
    {lx ly pre t} (path : PairPath (.left drawWord drawWord) lx ly pre t)
    (hw : Within g b (fun p => some (plan p)) [] pre) :
    ∃ c d x y tx ty tail, wordActions c x = lx ++ tx ∧ wordActions d y = ly ++ ty ∧
      Weave true (lx++tx) (ly++ty) (pre++tail) ∧ Within g b (fun p => some (plan p)) [] (pre++tail) := by
  obtain ⟨tail,o,ht,hl⟩ := legalCompletion t.tree g b plan (moves pre)
  have legal := (within_append pre tail).mpr ⟨hw,hl⟩
  cases o with
  | none => exact (valid _ (path.played.finishPlay ht) legal).elim
  | some v =>
    obtain ⟨x,y⟩ := v
    obtain ⟨tx,ty,cont⟩ := t.decode ht
    obtain ⟨hx,hy,weave⟩ := path.prepend cont
    obtain ⟨c,hc⟩ := wordTraceInv hx
    obtain ⟨d,hd⟩ := wordTraceInv hy
    exact ⟨c,d,x,y,tx,ty,tail,hc.symm,hd.symm,weave,legal⟩

def readMask (l r : List ℕ) (i : ℕ) : Option ReadBy :=
  if i ∈ l then some (if i ∈ r then .both else .left)
  else if i ∈ r then some .right else none

private theorem Placed.bounds {lo ms l r} (h : Placed lo ms l r) :
    lo ≤ l.2 ∧ (∀ j ∈ l.1, lo ≤ j ∧ j < l.2) ∧ (∀ j ∈ r.1, lo ≤ j ∧ j < l.2) := by
  induction h with
  | nil h => simp [h]
  | left h t hz ih | right h t hz ih | both h t ih =>
    simp_all only [List.mem_cons, forall_eq_or_imp]
    grind [Placed.same]

private theorem maskCongr (f g : ℕ → Option ReadBy) (xs : List ℕ)
    (h : ∀ x ∈ xs, f x = g x) : xs.filterMap f = xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons,h x List.mem_cons_self,ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]

private theorem scanStep (s i n : ℕ) (hs : s ≤ i) (hn : i < n)
    (f g : ℕ → Option ReadBy) (m : ReadBy)
    (before : ∀ k, s ≤ k → k < i → f k = none) (here : f i = some m)
    (after : ∀ k, i < k → f k = g k) :
    (List.range' s (n-s)).filterMap f = m :: (List.range' (i+1) (n-(i+1))).filterMap g := by
  have split : List.range' s (n-s) =
      List.range' s (i-s) ++ i :: List.range' (i+1) (n-(i+1)) := by
    have E := List.range'_append_1 (s := s) (m := i-s) (n := (n-(i+1))+1)
    rw [show s+(i-s) = i by omega,show (i-s) + (n-(i+1)+1) = n-s by omega,
      List.range'_succ] at E
    exact E.symm
  have empty : (List.range' s (i-s)).filterMap f = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro k hk
    have h := List.mem_range'_1.mp hk
    exact before _ h.1 (by omega)
  rw [split,List.filterMap_append,empty,List.nil_append,List.filterMap_cons,here]
  apply congrArg (m :: ·)
  exact maskCongr _ _ _ (fun k hk => after k (List.mem_range'_1.mp hk).1)

theorem Placed.scan {lo ms l r} (h : Placed lo ms l r) :
    (List.range' lo (l.2-lo)).filterMap (readMask l.1 r.1) = ms := by
  induction h with
  | nil _ => simp [readMask]
  | @left s i ms l r z hs ht hz ih =>
    subst z
    obtain ⟨hn,hl,hr⟩ := ht.bounds
    rw [← ih]
    apply scanStep s i l.2 hs hn
    · intro k _ hki
      have nl : k ∉ l.1 := fun h => (by have := (hl k h).1; omega)
      have nr : k ∉ r.1 := fun h => (by have := (hr k h).1; omega)
      simp [readMask,nl,nr,ne_of_lt hki]
    · have nr : i ∉ r.1 := fun h => (by have := (hr i h).1; omega)
      simp [readMask,nr]
    · intro k hk; simp [readMask,ne_of_gt hk]
  | @right s i ms l r z hs ht hz ih =>
    subst z
    obtain ⟨hn,hl,hr⟩ := ht.bounds
    rw [← ih]
    apply scanStep s i l.2 hs hn
    · intro k _ hki
      have nl : k ∉ l.1 := fun h => (by have := (hl k h).1; omega)
      have nr : k ∉ r.1 := fun h => (by have := (hr k h).1; omega)
      simp [readMask,nl,nr,ne_of_lt hki]
    · have nl : i ∉ l.1 := fun h => (by have := (hl i h).1; omega)
      simp [readMask,nl]
    · intro k hk; simp [readMask,ne_of_gt hk]
  | @both s i ms l r hs ht ih =>
    obtain ⟨hn,hl,hr⟩ := ht.bounds
    rw [← ih]
    apply scanStep s i l.2 hs hn
    · intro k _ hki
      have nl : k ∉ l.1 := fun h => (by have := (hl k h).1; omega)
      have nr : k ∉ r.1 := fun h => (by have := (hr k h).1; omega)
      simp [readMask,nl,nr,ne_of_lt hki]
    · simp [readMask]
    · intro k hk; simp [readMask,ne_of_gt hk]

end Larson.PairGame

namespace Larson.PairGame
open Larson.Words

theorem PairPath.append {A B : Type} {s t u : PairState A B} {l r p l' r' p'}
    (h : PairPath s l r p t) (k : PairPath t l' r' p' u) :
    PairPath s (l++l') (r++r') (p++p') u := by
  induction h with
  | nil => exact k
  | cons step _ ih => simpa only [List.append_assoc] using PairPath.cons step (ih k)

private theorem singlePath {A B : Type} {t u : PairState A B} {l r s}
    (h : PairStep t l r s u) : PairPath t l r s u := by
  simpa only [List.append_nil] using PairPath.cons h (PairPath.nil _)

private theorem Fragment.onLeft {A B : Type} {x x' : Thread A} {l}
    (h : Fragment x l x') (y : Thread B) :
    PairPath (.left x y) l [] l (.left x' y) := by
  induction h with
  | nil => exact .nil _
  | plan n _ ih => exact .cons (.pl n) ih
  | draw n _ ih => exact .cons (.dl n) ih

private theorem Fragment.onRight {A B : Type} {y y' : Thread B} {r}
    (h : Fragment y r y') (x : Thread A) :
    PairPath (.right x y) [] r r (.right x y') := by
  induction h with
  | nil => exact .nil _
  | plan n _ ih => exact .cons (.pr n) ih
  | draw n _ ih => exact .cons (.dr n) ih

private theorem Fragment.aloneLeft {A B : Type} {x x' : Thread A} {l}
    (h : Fragment x l x') (b : B) :
    PairPath (.onlyLeft x b) l [] l (.onlyLeft x' b) := by
  induction h with
  | nil => exact .nil _
  | plan n _ ih => exact .cons (.pal n) ih
  | draw n _ ih => exact .cons (.dal n) ih

private theorem Fragment.aloneRight {A B : Type} {y y' : Thread B} {r}
    (h : Fragment y r y') (a : A) :
    PairPath (.onlyRight a y) [] r r (.onlyRight a y') := by
  induction h with
  | nil => exact .nil _
  | plan n _ ih => exact .cons (.par n) ih
  | draw n _ ih => exact .cons (.dar n) ih

inductive Focus {A B : Type} : Thread A → Thread B → Type where
  | left {x y} : Focus x y
  | right {x y} : Focus x y
  | onlyLeft {x b} : Focus x (.result b)
  | onlyRight {a y} : Focus (.result a) y
  | done {a b} : Focus (.result a) (.result b)

def Focus.state {A B : Type} {x : Thread A} {y : Thread B} : Focus x y → PairState A B
  | .left => .left x y
  | .right => .right x y
  | @Focus.onlyLeft _ _ _ b => .onlyLeft x b
  | @Focus.onlyRight _ _ a _ => .onlyRight a y
  | @Focus.done _ _ a b => .done a b

def Focus.active {A B : Type} {x : Thread A} {y : Thread B} : Focus x y → Bool → Bool
  | .left | .onlyLeft => id
  | .right | .onlyRight => (!·)
  | .done => fun _ => false

structure Strategy where
  g : ℕ → ℕ
  mono : StrictMono g
  bound : List ℕ → ℕ
  plan : List ℕ → ℕ
  valid : ∀ s, Terminal pairs s none → ¬ Within g bound (fun p => some (plan p)) [] s

abbrev Strategy.legal (S : Strategy) := Within S.g S.bound (fun p => some (S.plan p))

structure Link (S : Strategy) (x y : Thread Word) where
  focus : Focus x y
  l : List Action
  r : List Action
  p : List Action
  path : PairPath (.left drawWord drawWord) l r p focus.state
  legal : S.legal [] p

def Link.start (S : Strategy) : Link S drawWord drawWord :=
  ⟨.left,[],[],[],.nil _,trivial⟩

private def Link.extend {S x y x' y'} (e : Link S x y) (f : Focus x' y') {l r s}
    (step : PairPath e.focus.state l r s f.state) (law : S.legal (moves e.p) s) : Link S x' y' :=
  ⟨f,e.l++l,e.r++r,e.p++s,e.path.append step,(within_append ..).mpr ⟨e.legal,law⟩⟩

def Link.readLeft {S x y x' l} (e : Link S x y) (act : e.focus.active true = true)
    (h : Fragment x l x') (law : S.legal (moves e.p) l) :
    {e' : Link S x' y // e'.focus.active true ∧ e'.p = e.p++l} := by
  cases hf : e.focus with
  | left => exact ⟨e.extend .left (l := l) (r := []) (s := l) (by rw [hf]; exact h.onLeft y) law,rfl,rfl⟩
  | onlyLeft => exact ⟨e.extend .onlyLeft (l := l) (r := []) (s := l) (by rw [hf]; exact h.aloneLeft _) law,rfl,rfl⟩
  | right | onlyRight | done => simp [hf,Focus.active] at act

def Link.readRight {S x y y' r} (e : Link S x y) (act : e.focus.active false = true)
    (h : Fragment y r y') (law : S.legal (moves e.p) r) :
    {e' : Link S x y' // e'.focus.active false ∧ e'.p = e.p++r} := by
  cases hf : e.focus with
  | right => exact ⟨e.extend .right (l := []) (r := r) (s := r) (by rw [hf]; exact h.onRight x) law,rfl,rfl⟩
  | onlyRight => exact ⟨e.extend .onlyRight (l := []) (r := r) (s := r) (by rw [hf]; exact h.aloneRight _) law,rfl,rfl⟩
  | left | onlyLeft | done => simp [hf,Focus.active] at act

private theorem Link.noFailure {S x y} (e : Link S x y) (h : Terminal e.focus.state.tree [] none) :
    False := by
  apply S.valid e.p _ e.legal
  simpa only [List.append_nil,PairState.tree,pairs] using e.path.played.finishPlay h

def Link.switchLeft {S x y} (e : Link S (.pause x) y) (act : e.focus.active true = true) :
    Link S x y := by
  cases hf : e.focus with
  | left => exact e.extend .right (l := [.pause]) (r := []) (s := []) (by rw [hf]; exact singlePath .sl) trivial
  | onlyLeft => exact False.elim (e.noFailure (hf ▸ Terminal.leaf _))
  | right => simp [hf,Focus.active] at act

def Link.switchRight {S x y} (e : Link S x (.pause y)) (act : e.focus.active false = true) :
    Link S x y := by
  cases hf : e.focus with
  | right => exact e.extend .left (l := []) (r := [.pause]) (s := []) (by rw [hf]; exact singlePath .sr) trivial
  | onlyRight => exact False.elim (e.noFailure (hf ▸ Terminal.leaf _))
  | left => simp [hf,Focus.active] at act

def Link.endLeft {S a y} (e : Link S (.result a) y) (act : e.focus.active true = true) :
    Link S (.result a) y := by
  cases hf : e.focus with
  | left => exact e.extend .onlyRight (l := []) (r := []) (s := []) (by rw [hf]; exact singlePath .el) trivial
  | onlyLeft => exact e.extend .done (l := []) (r := []) (s := []) (by rw [hf]; exact singlePath .eal) trivial
  | right | onlyRight | done => simp [hf,Focus.active] at act

def Link.endRight {S x b} (e : Link S x (.result b)) (act : e.focus.active false = true) :
    Link S x (.result b) := by
  cases hf : e.focus with
  | right => exact e.extend .onlyLeft (l := []) (r := []) (s := []) (by rw [hf]; exact singlePath .er) trivial
  | onlyRight => exact e.extend .done (l := []) (r := []) (s := []) (by rw [hf]; exact singlePath .ear) trivial
  | left | onlyLeft | done => simp [hf,Focus.active] at act

theorem Link.success {S : Strategy} {x y : Word} (e : Link S (.result x) (.result y)) :
    Realizes S.g S.bound (fun p => some (S.plan p)) x y := by
  have terminal : e.focus.state.accepts [] [] [] x y := by
    cases e.focus with
    | left => exact ⟨.result _,.result _,.endLeft trivial⟩
    | right => exact ⟨.result _,.result _,.endRight trivial⟩
    | onlyLeft | onlyRight => exact ⟨.result _,rfl,rfl,trivial,rfl⟩
    | done => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨hx,hy,hw⟩ := e.path.prepend terminal
  obtain ⟨c,hc⟩ := wordTraceInv hx
  obtain ⟨d,hd⟩ := wordTraceInv hy
  exact ⟨c,d,e.p,by simpa only [← hc,← hd,List.append_nil] using hw,e.legal⟩

inductive Site where
  | live {x y : Thread Word} (program : Coupled Eq x y)
  | finished (w : Word)

def Site.first : Site → Thread Word
  | @Site.live x _ _ => x
  | .finished w => .result w

def Site.second : Site → Thread Word
  | @Site.live _ y _ => y
  | .finished w => .result w

def Site.pending : Site → Bool
  | .live _ => true
  | .finished _ => false

noncomputable def Site.height : Site → Ordinal.{0}
  | .live p => p.height
  | .finished _ => 0

structure Board (S : Strategy) where
  x : Site
  y : Site
  z : Site
  xy : Link S x.first y.first
  xz : Link S x.second z.second
  yz : Link S y.second z.first

def Board.opening (S : Strategy) (p q r : Coupled Eq drawWord drawWord) : Board S :=
  ⟨.live p,.live q,.live r,.start _,.start _,.start _⟩

def Board.canX {S} (w : Board S) := w.x.pending && w.xy.focus.active true && w.xz.focus.active true
def Board.canY {S} (w : Board S) := w.y.pending && w.xy.focus.active false && w.yz.focus.active true
def Board.canZ {S} (w : Board S) := w.z.pending && w.yz.focus.active false && w.xz.focus.active false

theorem Board.finishedTriangle {S} (w : Board S)
    (hx : w.x.pending = false) (hy : w.y.pending = false) (hz : w.z.pending = false) :
    MakesTriangle S.g S.bound S.plan := by
  obtain ⟨x,y,z,xy,xz,yz⟩ := w
  cases x with
  | live => contradiction
  | finished a =>
    cases y with
    | live => contradiction
    | finished b =>
      cases z with
      | live => contradiction
      | finished c => exact ⟨a,b,c,Or.inl xy.success,Or.inl xz.success,Or.inl yz.success⟩

private noncomputable def Board.budget {S} (w : Board S) : Ordinal ×ₗ Ordinal ×ₗ Ordinal :=
  toLex (w.x.height,toLex (w.y.height,w.z.height))

end Larson.PairGame

namespace Larson.PairGame

def pivotIndex (p : List ℕ) : ℕ := if p.head? = some 1 then 0 else p.getLastD 0

end Larson.PairGame

namespace Larson.PairGame
open Larson.Words

def builderNumber : Action → Option ℕ
  | .draw n => some n
  | _ => none

def signal : Action → Option (Option ℕ)
  | .plan n => some (some n)
  | .pause => some none
  | .draw _ => none

def blockSignals (ds : List ℕ) :=
  ds.flatMap fun d => some d :: List.replicate (d+1) none

private theorem labels_draws (ns : List ℕ) :
    (ns.map Action.draw).filterMap builderNumber = ns ∧
      (ns.map Action.draw).filterMap signal = [] := by
  induction ns <;> simp_all [builderNumber,signal]

private theorem sortedMarks {ms : List ℕ} {n : ℕ} {tail : List ℕ}
    (hs : (ms ++ n :: tail).Pairwise (· < ·)) :
    (List.range' 0 n).filter (· ∈ ms) = ms := by
  obtain ⟨sort,_,cross⟩ := List.pairwise_append.mp hs
  have order := (List.pairwise_lt_range' (s := 0) (n := n) 1 (by decide : 0 < 1)).sublist
    (List.filter_sublist (p := fun j => decide (j ∈ ms)))
  apply order.eq_of_mem_iff sort
  intro j
  simp only [List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
  exact fun h => List.mem_range'_1.mpr ⟨Nat.zero_le _,by simpa using cross j h n List.mem_cons_self⟩

private theorem signalsLeaves (ms : List ℕ) (i n : ℕ) (w : Tuple ℕ n) :
    (actionsOf (leafActions ms) i n w).filterMap signal =
      List.replicate (((List.range' i n).filter (· ∈ ms)).length) none := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    by_cases h : i ∈ ms <;> simp [actionsOf,List.filterMap_cons,leafActions,h,signal,
      List.range'_succ,ih,List.replicate_succ]

private theorem signalsBlock (ms : List ℕ) (b : Block)
    (hs : ((blockActions ms b).filterMap builderNumber).Pairwise (· < ·)) :
    (blockActions ms b).filterMap signal = List.replicate ms.length none := by
  simp only [blockActions,List.filterMap_append,(labels_draws ms).1,List.filterMap_cons,
    builderNumber,List.singleton_append,List.append_assoc] at hs
  have marked := sortedMarks hs
  simp [blockActions,(labels_draws ms).2,List.filterMap_cons,signal,signalsLeaves,marked]

def blockPlans (c : Cuts) (i h : ℕ) : List ℕ :=
  ((List.range' i h).filter (· ∈ c.blocks)).map (fun j => (c.rest j).length)

private theorem signalsCells (c : Cuts) (i n : ℕ) (w : Tuple Block n)
    (hs : ((actionsOf (cellActions c) i n w).filterMap builderNumber).Pairwise (· < ·)) :
    (actionsOf (cellActions c) i n w).filterMap signal = blockSignals (blockPlans c i n) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    rw [actionsOf,List.filterMap_append,List.pairwise_append] at hs
    obtain ⟨head,tail,_⟩ := hs
    rw [actionsOf,List.filterMap_append,ih (i+1) _ tail]
    by_cases h : i ∈ c.blocks
    · simp only [cellActions,h,if_true,List.filterMap_cons,builderNumber] at head
      simp [cellActions,h,signal,signalsBlock _ _ head,blockPlans,List.range'_succ,blockSignals]
    · simp only [cellActions,h,if_false] at head
      simp [cellActions,h,signalsBlock _ _ head,blockPlans,List.range'_succ]

theorem canonicalWordProfile (c : Cuts) (w : Word)
    (hs : ((wordActions c w).filterMap builderNumber).Pairwise (· < ·)) :
    ∃ ds : List ℕ, ds.length = c.blocks.length ∧
      (wordActions c w).filterMap signal = some c.blocks.length :: blockSignals ds := by
  simp only [wordActions,List.filterMap_cons,builderNumber,List.filterMap_append,(labels_draws _).1,
    List.append_assoc,List.singleton_append] at hs
  have marked := sortedMarks hs
  have tail := (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).2
  refine ⟨blockPlans c 0 w.1,by simp [blockPlans,marked],?_⟩
  simp [wordActions,(labels_draws _).2,List.filterMap_cons,signal,signalsCells c _ _ _ tail]

end Larson.PairGame

namespace Larson.PairGame

def Strategy.increasing (S : Strategy) : Prop :=
  ∀ (p : List ℕ) (n : ℕ), n ∈ p → n < S.bound p

private theorem withinLabels {S : Strategy} (inc : S.increasing) (p : List ℕ) (s : List Action)
    (h : S.legal p s) :
    (s.filterMap builderNumber).Pairwise (· < ·) ∧
      ∀ v ∈ p, ∀ n ∈ s.filterMap builderNumber, v < n := by
  induction s generalizing p with
  | nil => simp
  | cons a s ih =>
    cases a with
    | pause => exact h.elim
    | plan k =>
      obtain ⟨hs,hist⟩ := ih _ h.2
      exact ⟨hs,fun v hv => hist v (List.mem_append_left _ hv)⟩
    | draw k =>
      obtain ⟨j,hj,rfl⟩ := h.1
      obtain ⟨hs,hist⟩ := ih _ h.2
      have early v (hv : v ∈ p) : v < S.g j := ((inc p v hv).trans_le hj).trans_le (S.mono.id_le _)
      refine ⟨List.pairwise_cons.mpr ⟨hist _ (by simp),hs⟩,?_⟩
      intro v hv n hn
      rcases List.mem_cons.mp hn with rfl | ht
      · exact early v hv
      · exact hist v (List.mem_append_left _ hv) n ht

private theorem Weave.builderSublists {i l r s} (h : Weave i l r s) :
    (l.filterMap builderNumber).Sublist (s.filterMap builderNumber) ∧
    (r.filterMap builderNumber).Sublist (s.filterMap builderNumber) := by
  induction h with
  | endLeft => exact ⟨List.nil_sublist _,List.Sublist.refl _⟩
  | endRight => exact ⟨List.Sublist.refl _,List.nil_sublist _⟩
  | switchLeft _ ih | switchRight _ ih | planLeft _ _ ih | planRight _ _ ih => exact ih
  | drawLeft n _ ih => exact ⟨ih.1.cons_cons _,ih.2.cons _⟩
  | drawRight n _ ih => exact ⟨ih.1.cons _,ih.2.cons_cons _⟩

theorem Link.profiles {S x y} (e : Link S x y) (inc : S.increasing) :
    ∃ c d u v a b tx ty tail, wordActions c u = e.l ++ tx ∧ wordActions d v = e.r ++ ty ∧
      Weave true (wordActions c u) (wordActions d v) (e.p ++ tail) ∧ S.legal [] (e.p++tail) ∧
      a.length = c.blocks.length ∧ b.length = d.blocks.length ∧
      (wordActions c u).filterMap signal = some c.blocks.length :: blockSignals a ∧
      (wordActions d v).filterMap signal = some d.blocks.length :: blockSignals b := by
  obtain ⟨c,d,u,v,tx,ty,tail,hx,hy,w,legal⟩ :=
    extendLocalPrefixes S.g S.bound S.plan S.valid e.path e.legal
  rw [← hx,← hy] at w
  have ordered := (withinLabels inc _ _ legal).1
  obtain ⟨a,ha,hl⟩ := canonicalWordProfile c u (ordered.sublist w.builderSublists.1)
  obtain ⟨b,hb,hr⟩ := canonicalWordProfile d v (ordered.sublist w.builderSublists.2)
  exact ⟨c,d,u,v,a,b,tx,ty,tail,hx,hy,w,legal,ha,hb,hl,hr⟩

private theorem signalCounts (s : List Action) :
    (s.filterMap signal).filterMap id = planned s ∧
      (s.filterMap signal).count none = pauseCount s := by
  induction s with
  | nil => exact ⟨rfl,rfl⟩
  | cons a s ih =>
    cases a <;> simp [signal,List.filterMap_cons,planned,pauseCount,ih,Nat.add_comm] <;> exact ih.1

private theorem blockSignalCounts (ds : List ℕ) :
    (blockSignals ds).filterMap id = ds ∧
      (blockSignals ds).count none = (ds.map (·+1)).sum := by
  induction ds with
  | nil => exact ⟨rfl,rfl⟩
  | cons d ds ih =>
    simp only [blockSignals,List.flatMap_cons,List.cons_append] at *
    simp [List.count_append,ih,Nat.add_comm]
    exact ih.1

theorem Link.profileBalance {S x y} (e : Link S x y) (inc : S.increasing) (mode : Bool)
    (fixed : EndOrder S.g S.bound S.plan mode) :
    ∃ c d u v, ∃ a b : List ℕ, ∃ tx ty tail,
      wordActions c u = e.l ++ tx ∧ wordActions d v = e.r ++ ty ∧
      Weave true (wordActions c u) (wordActions d v) (e.p ++ tail) ∧ S.legal [] (e.p++tail) ∧
      a.length = c.blocks.length ∧ b.length = d.blocks.length ∧
      planned (wordActions c u) = a.length :: a ∧ planned (wordActions d v) = b.length :: b ∧
      (a.map (·+1)).sum = (b.map (·+1)).sum + (if mode then 1 else 0) := by
  obtain ⟨c,d,u,v,a,b,tx,ty,tail,hx,hy,w,legal,ha,hb,hl,hr⟩ := e.profiles inc
  have count {s ds n} (h : s.filterMap signal = some n :: blockSignals ds) :
      planned s = n :: ds ∧ pauseCount s = (ds.map (·+1)).sum := by
    obtain ⟨hp,hc⟩ := signalCounts s
    rw [h] at hp hc
    constructor
    · exact hp.symm.trans (congrArg (n :: ·) (blockSignalCounts ds).1)
    · simpa [List.count_cons,(blockSignalCounts ds).2] using hc.symm
  obtain ⟨al,ac⟩ := count hl
  obtain ⟨bl,bc⟩ := count hr
  exact ⟨c,d,u,v,a,b,tx,ty,tail,hx,hy,w,legal,ha,hb,ha ▸ al,hb ▸ bl,
    by simpa [ac,bc] using fixed _ _ _ _ _ w legal⟩

def Strategy.RightLocation (S : Strategy) (predict : List ℕ → ℕ × ℕ) : Prop :=
  ∀ c d x y pre tail, Weave true (wordActions c x) (wordActions d y) (pre ++ tail) →
    S.legal [] (pre ++ tail) →
    cutLocation (pivotIndex (moves pre)) (planned (wordActions d y)).tail = predict (moves pre)

inductive WordEvent where
  | planL (n : ℕ) | planR (n : ℕ)
  | drawL (n : ℕ) | drawR (n : ℕ) | drawBoth (n : ℕ)
  | pass (m : ReadBy)
  | inspect (p q : List ℕ)

def WordEvent.left : WordEvent → Option Action
  | .planL n => some (.plan n)
  | .drawL n | .drawBoth n => some (.draw n)
  | .pass .left | .pass .both => some .pause
  | _ => none

def WordEvent.right : WordEvent → Option Action
  | .planR n => some (.plan n)
  | .drawR n | .drawBoth n => some (.draw n)
  | .pass .right | .pass .both => some .pause
  | _ => none

def WordEvent.mask : WordEvent → Option ReadBy
  | .pass m => some m
  | _ => none

inductive WordRun {A B : Type} {R : A → B → Prop} : {x : Thread A} → {y : Thread B} →
    Coupled R x y → List WordEvent → A → B → Prop where
  | done {a b h} : WordRun (@Coupled.result _ _ R a b h) [] a b
  | pl {f y k s a b} (n) : WordRun (k n) s a b →
      WordRun (@Coupled.planL _ _ R f y k) (.planL n :: s) a b
  | pr {x f k s a b} (n) : WordRun (k n) s a b →
      WordRun (@Coupled.planR _ _ R x f k) (.planR n :: s) a b
  | dl {f y lo k s a b} (n hn) : WordRun (k n hn) s a b →
      WordRun (@Coupled.drawL _ _ R f y lo k) (.drawL n :: s) a b
  | dr {x f lo k s a b} (n hn) : WordRun (k n hn) s a b →
      WordRun (@Coupled.drawR _ _ R x f lo k) (.drawR n :: s) a b
  | dab {f h lo k s a b} (n hn) : WordRun (k n hn) s a b →
      WordRun (@Coupled.drawBoth _ _ R f h lo k) (.drawBoth n :: s) a b
  | sl {x y k s a b} : WordRun k s a b →
      WordRun (@Coupled.pauseL _ _ R x y k) (.pass .left :: s) a b
  | sr {x y k s a b} : WordRun k s a b →
      WordRun (@Coupled.pauseR _ _ R x y k) (.pass .right :: s) a b
  | sab {x y k s a b} : WordRun k s a b →
      WordRun (@Coupled.pauseBoth _ _ R x y k) (.pass .both :: s) a b
  | see {x y k s a b} (p q) : WordRun (k p q) s a b →
      WordRun (@Coupled.inspect _ _ R x y k) (.inspect p q :: s) a b

theorem WordRun.projections {A B : Type} {R : A → B → Prop} {x : Thread A} {y : Thread B}
    {p : Coupled R x y} {s a b} (run : WordRun p s a b) :
    Trace x (s.filterMap WordEvent.left) a ∧ Trace y (s.filterMap WordEvent.right) b ∧ R a b := by
  induction run with
  | done => exact ⟨.result _,.result _,by assumption⟩
  | pl n _ ih => exact ⟨.plan n ih.1,ih.2⟩
  | pr n _ ih => exact ⟨ih.1,.plan n ih.2.1,ih.2.2⟩
  | dl n _ _ ih => exact ⟨.draw n ih.1,ih.2⟩
  | dr n _ _ ih => exact ⟨ih.1,.draw n ih.2.1,ih.2.2⟩
  | dab n _ _ ih => exact ⟨.draw n ih.1,.draw n ih.2.1,ih.2.2⟩
  | sl _ ih => exact ⟨.pause ih.1,ih.2⟩
  | sr _ ih => exact ⟨ih.1,.pause ih.2.1,ih.2.2⟩
  | sab _ ih => exact ⟨.pause ih.1,.pause ih.2.1,ih.2.2⟩
  | see _ _ _ ih => exact ih

def Handoff.run {A B : Type} {R : A → B → Prop} {x : Thread A} {y : Thread B}
    (s : Handoff R x y) (t : List WordEvent) (a : A) (b : B) : Prop :=
  match s with
  | .done (a := u) (b := v) _ => a = u ∧ b = v ∧ t = []
  | .left q => ∃ tail, t = .pass .left :: tail ∧ WordRun q tail a b
  | .right q => ∃ tail, t = .pass .right :: tail ∧ WordRun q tail a b
  | .both q => ∃ tail, t = .pass .both :: tail ∧ WordRun q tail a b

theorem Coupled.fillPlans {A B : Type} {R : A → B → Prop} {x : Thread A} {y : Thread B}
    (program : Coupled R x y) (a b : ℕ → ℕ) (i j floor : ℕ)
    (observe : List ℕ × List ℕ) :
    ∃ t u v, WordRun program t u v ∧
      (∀ k (h : k < (planned (t.filterMap WordEvent.left)).length),
        (planned (t.filterMap WordEvent.left))[k] = a (i+k)) ∧
      (∀ k (h : k < (planned (t.filterMap WordEvent.right)).length),
        (planned (t.filterMap WordEvent.right))[k] = b (j+k)) ∧
      (floor :: ((t.filterMap WordEvent.left).filterMap builderNumber)).Pairwise (· < ·) ∧
      (floor :: ((t.filterMap WordEvent.right).filterMap builderNumber)).Pairwise (· < ·) := by
  have add {n} (f : ℕ → ℕ) {ns : List ℕ}
      (h : ∀ k (hk : k < ns.length), ns[k] = f (n+1+k)) :
      ∀ k (hk : k < (f n :: ns).length), (f n :: ns)[k] = f (n+k) := by
    intro k hk
    cases k with
    | zero => simp
    | succ k => simpa [Nat.add_assoc,Nat.add_comm 1] using h k (by simpa using hk)
  have lower {i n : ℕ} (hin : i < n) {l : List ℕ} (h : (n :: l).Pairwise (· < ·)) :
      (i :: l).Pairwise (· < ·) := List.pairwise_cons.mpr
        ⟨fun v hv => hin.trans ((List.pairwise_cons.mp h).1 v hv),(List.pairwise_cons.mp h).2⟩
  have push {i n : ℕ} (hin : i < n) {l : List ℕ} (h : (n :: l).Pairwise (· < ·)) :
      (i :: n :: l).Pairwise (· < ·) :=
    List.pairwise_cons.mpr ⟨fun v hv => (List.mem_cons.mp hv).elim (fun he => he ▸ hin)
      (fun hm => hin.trans ((List.pairwise_cons.mp h).1 v hm)),h⟩
  induction program generalizing i j floor with
  | result h => exact ⟨[],_,_,.done,(by simp [planned]),(by simp [planned]),by simp,by simp⟩
  | planL _ ih =>
    obtain ⟨t,u,v,hr,hl,hR,hx,hy⟩ := ih (a i) (i+1) j floor
    exact ⟨_,u,v,.pl _ hr,add a hl,hR,hx,hy⟩
  | planR _ ih =>
    obtain ⟨t,u,v,hr,hl,hR,hx,hy⟩ := ih (b j) i (j+1) floor
    exact ⟨_,u,v,.pr _ hr,hl,add b hR,hx,hy⟩
  | drawL lo _ ih =>
    let n := max (floor+1) lo
    have gt : floor < n := (Nat.lt_succ_self floor).trans_le (le_max_left ..) 
    obtain ⟨t,u,v,hr,hl,hR,hx,hy⟩ := ih n (le_max_right ..) i j n
    exact ⟨_,u,v,.dl _ _ hr,hl,hR,push gt hx,lower gt hy⟩
  | drawR lo _ ih =>
    let n := max (floor+1) lo
    have gt : floor < n := (Nat.lt_succ_self floor).trans_le (le_max_left ..)
    obtain ⟨t,u,v,hr,hl,hR,hx,hy⟩ := ih n (le_max_right ..) i j n
    exact ⟨_,u,v,.dr _ _ hr,hl,hR,lower gt hx,push gt hy⟩
  | drawBoth lo _ ih =>
    let n := max (floor+1) lo
    have gt : floor < n := (Nat.lt_succ_self floor).trans_le (le_max_left ..)
    obtain ⟨t,u,v,hr,hl,hR,hx,hy⟩ := ih n (le_max_right ..) i j n
    exact ⟨_,u,v,.dab _ _ hr,hl,hR,push gt hx,push gt hy⟩
  | pauseL _ ih | pauseR _ ih | pauseBoth _ ih =>
    obtain ⟨t,u,v,hr,hl,hR,hx,hy⟩ := ih i j floor
    first | exact ⟨_,u,v,.sl hr,hl,hR,hx,hy⟩ | exact ⟨_,u,v,.sr hr,hl,hR,hx,hy⟩ |
      exact ⟨_,u,v,.sab hr,hl,hR,hx,hy⟩
  | inspect _ ih =>
    obtain ⟨t,u,v,hr,hl,hR,hx,hy⟩ := ih observe.1 observe.2 i j floor
    exact ⟨_,u,v,.see _ _ hr,hl,hR,hx,hy⟩

theorem Coupled.nextHandoff_trace {A B : Type} {R : A → B → Prop} {x : Thread A} {y : Thread B}
    (prog : Coupled R x y) (g) (hg : StrictMono g) (b plan : List ℕ → ℕ) (p q : List ℕ) :
    let batch := prog.nextHandoff g hg b plan p q
    ∃ log : List WordEvent, log.filterMap WordEvent.left = batch.l ∧
      log.filterMap WordEvent.right = batch.r ∧ log.filterMap WordEvent.mask = [] ∧
      ∀ t u v, batch.stop.run t u v → WordRun prog (log++t) u v := by
  induction prog generalizing p q with
  | result h =>
    refine ⟨[],rfl,rfl,rfl,?_⟩
    intro t a b ht
    change a = _ ∧ b = _ ∧ t = [] at ht
    obtain ⟨rfl,rfl,rfl⟩ := ht
    exact .done
  | pauseL next _ =>
    refine ⟨[],rfl,rfl,rfl,?_⟩
    intro t a b ht
    change ∃ tail, t = .pass .left :: tail ∧ WordRun next tail a b at ht
    obtain ⟨tail,rfl,hr⟩ := ht
    exact .sl hr
  | pauseR next _ =>
    refine ⟨[],rfl,rfl,rfl,?_⟩
    intro t a b ht
    change ∃ tail, t = .pass .right :: tail ∧ WordRun next tail a b at ht
    obtain ⟨tail,rfl,hr⟩ := ht
    exact .sr hr
  | pauseBoth next _ =>
    refine ⟨[],rfl,rfl,rfl,?_⟩
    intro t a b ht
    change ∃ tail, t = .pass .both :: tail ∧ WordRun next tail a b at ht
    obtain ⟨tail,rfl,hr⟩ := ht
    exact .sab hr
  | inspect next ih =>
    obtain ⟨l,hl,hr,hm,ex⟩ := ih p q p q
    exact ⟨.inspect p q :: l,hl,hr,hm,fun t u v hh => .see p q (ex t u v hh)⟩
  | planL next ih =>
    obtain ⟨l,hl,hr,hm,ex⟩ := ih (plan p) (p++[plan p]) q
    exact ⟨.planL (plan p) :: l,congrArg (Action.plan (plan p) :: ·) hl,hr,hm,
      fun t u v hh => .pl _ (ex t u v hh)⟩
  | planR next ih =>
    obtain ⟨l,hl,hr,hm,ex⟩ := ih (plan q) p (q++[plan q])
    exact ⟨.planR (plan q) :: l,hl,congrArg (Action.plan (plan q) :: ·) hr,hm,
      fun t u v hh => .pr _ (ex t u v hh)⟩
  | drawL lo next ih =>
    let n := g (max lo (b p))
    have ge : lo ≤ n := (le_max_left ..).trans (hg.id_le _)
    obtain ⟨l,hl,hr,hm,ex⟩ := ih n ge (p++[n]) q
    exact ⟨.drawL n :: l,congrArg (Action.draw n :: ·) hl,hr,hm,
      fun t u v hh => .dl _ ge (ex t u v hh)⟩
  | drawR lo next ih =>
    let n := g (max lo (b q))
    have ge : lo ≤ n := (le_max_left ..).trans (hg.id_le _)
    obtain ⟨l,hl,hr,hm,ex⟩ := ih n ge p (q++[n])
    exact ⟨.drawR n :: l,hl,congrArg (Action.draw n :: ·) hr,hm,
      fun t u v hh => .dr _ ge (ex t u v hh)⟩
  | drawBoth lo next ih =>
    let n := g (max lo (max (b p) (b q)))
    have ge : lo ≤ n := (le_max_left ..).trans (hg.id_le _)
    obtain ⟨l,hl,hr,hm,ex⟩ := ih n ge (p++[n]) (q++[n])
    exact ⟨.drawBoth n :: l,congrArg (Action.draw n :: ·) hl,congrArg (Action.draw n :: ·) hr,
      hm,fun t u v hh => .dab _ ge (ex t u v hh)⟩

end Larson.PairGame

namespace Larson.PairGame
open Larson.Words

private theorem planned_append_eq (a b : List Action) : planned (a++b) = planned a ++ planned b := by
  induction a with
  | nil => rfl
  | cons e a ih => cases e <;> simp [planned,ih]

private def reports (expected xs : List ℕ) :=
  ∀ k (h : k < xs.length), xs[k] = expected[k]?.getD 0

private theorem reports_join {ds old new : List ℕ} (h : old <+: ds)
    (rest : ∀ k (hk : k < new.length), new[k] = ds[old.length+k]?.getD 0) :
    reports ds (old++new) := by
  intro k hk
  obtain ⟨ext,rfl⟩ := h
  by_cases hit : k < old.length
  · simp [List.getElem_append_left hit,List.getElem?_append_left hit,List.getElem?_eq_getElem hit]
  · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hit)
    simp only [List.getElem_append_right (by omega : old.length ≤ old.length+j),Nat.add_sub_cancel_left]
    exact rest j (by simp at hk; omega)

private theorem reports_eq {as ds : List ℕ}
    (h : reports (as.length :: as) (ds.length :: ds)) :
    ds.length :: ds = as.length :: as := by
  have hl : ds.length = as.length := h 0 (by simp)
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    simpa [List.getElem?_eq_getElem h2] using h i h1

private theorem canonicalPlanShape {s w} (h : Trace drawWord s w)
    (sorted : (s.filterMap builderNumber).Pairwise (· < ·)) :
    ∃ ds, planned s = ds.length :: ds := by
  obtain ⟨c,rfl⟩ := wordTraceInv h
  obtain ⟨ds,hlen,signals⟩ := canonicalWordProfile c w sorted
  have hp := (signalCounts (wordActions c w)).1
  rw [signals] at hp
  refine ⟨ds,?_⟩
  rw [hlen]
  exact hp.symm.trans (congrArg (_ :: ·) (blockSignalCounts ds).1)

theorem fillCompatiblePrefix {root : Coupled Eq drawWord drawWord} {x y : Thread Word}
    (current : Coupled Eq x y) (pre : List WordEvent)
    (extend : ∀ s a b, WordRun current s a b → WordRun root (pre++s) a b)
    (ds es : List ℕ) (observe : List ℕ × List ℕ)
    (left : planned (pre.filterMap WordEvent.left) <+: ds.length :: ds)
    (right : planned (pre.filterMap WordEvent.right) <+: es.length :: es)
    (sl : ((pre.filterMap WordEvent.left).filterMap builderNumber).Pairwise (· < ·))
    (sr : ((pre.filterMap WordEvent.right).filterMap builderNumber).Pairwise (· < ·)) :
    ∃ tail w, WordRun root (pre++tail) w w ∧ WordRun current tail w w ∧
      planned ((pre++tail).filterMap WordEvent.left) = ds.length :: ds ∧
      planned ((pre++tail).filterMap WordEvent.right) = es.length :: es := by
  let old (f : WordEvent → Option Action) := (pre.filterMap f).filterMap builderNumber
  let floor := ((old WordEvent.left ++ old WordEvent.right).toFinset).sup id
  obtain ⟨t,u,v,ht,hl,hr,dl,dr⟩ := current.fillPlans
    (fun n => (ds.length :: ds)[n]?.getD 0) (fun n => (es.length :: es)[n]?.getD 0)
    (planned (pre.filterMap WordEvent.left)).length (planned (pre.filterMap WordEvent.right)).length
    floor observe
  have run := extend t u v ht
  obtain ⟨rx,ry,rfl⟩ := run.projections
  have one (f : WordEvent → Option Action) (as : List ℕ) (tr : Trace drawWord ((pre++t).filterMap f) u)
      (hs : (old f).Pairwise (· < ·)) (bound : ∀ n ∈ old f, n ≤ floor)
      (late : (floor :: (t.filterMap f).filterMap builderNumber).Pairwise (· < ·))
      (reportsAll : reports (as.length :: as) (planned (pre.filterMap f) ++ planned (t.filterMap f))) :
      planned ((pre++t).filterMap f) = as.length :: as := by
    have sorted : (((pre++t).filterMap f).filterMap builderNumber).Pairwise (· < ·) := by
      simp only [List.filterMap_append,List.pairwise_append]
      exact ⟨hs,(List.pairwise_cons.mp late).2,fun n hn j hj =>
        (bound n hn).trans_lt ((List.pairwise_cons.mp late).1 j hj)⟩
    obtain ⟨cs,hcs⟩ := canonicalPlanShape tr sorted
    rw [← planned_append_eq,← List.filterMap_append] at reportsAll
    rw [hcs] at reportsAll ⊢
    exact reports_eq reportsAll
  refine ⟨t,u,run,ht,one _ _ rx sl ?_ dl (reports_join left hl),
    one _ _ ry sr ?_ dr (reports_join right hr)⟩
  · intro n hn
    exact Finset.le_sup (f := id) (List.mem_toFinset.mpr (List.mem_append_left _ hn))
  · intro n hn
    exact Finset.le_sup (f := id) (List.mem_toFinset.mpr (List.mem_append_right _ hn))

end Larson.PairGame

namespace Larson.PairGame

private theorem WordRun.inv_planL {A B : Type} {R : A → B → Prop} {f y k} {s u v}
    (run : WordRun (@Coupled.planL A B R f y k) s u v) :
    ∃ n t, s = .planL n :: t ∧ WordRun (k n) t u v := by
  cases run
  exact ⟨_, _,rfl,by assumption⟩

private theorem WordRun.inv_planR {A B : Type} {R : A → B → Prop} {x f k} {s u v}
    (run : WordRun (@Coupled.planR A B R x f k) s u v) :
    ∃ n t, s = .planR n :: t ∧ WordRun (k n) t u v := by
  cases run
  exact ⟨_, _,rfl,by assumption⟩

private theorem WordRun.inv_drawL {A B : Type} {R : A → B → Prop} {f y lo k} {s u v}
    (run : WordRun (@Coupled.drawL A B R f y lo k) s u v) :
    ∃ n hn t, s = .drawL n :: t ∧ WordRun (k n hn) t u v := by
  cases run
  exact ⟨_, _, _,rfl,by assumption⟩

private theorem WordRun.inv_drawR {A B : Type} {R : A → B → Prop} {x f lo k} {s u v}
    (run : WordRun (@Coupled.drawR A B R x f lo k) s u v) :
    ∃ n hn t, s = .drawR n :: t ∧ WordRun (k n hn) t u v := by
  cases run
  exact ⟨_, _, _,rfl,by assumption⟩

private theorem WordRun.inv_drawBoth {A B : Type} {R : A → B → Prop} {f h lo k} {s u v}
    (run : WordRun (@Coupled.drawBoth A B R f h lo k) s u v) :
    ∃ n hn t, s = .drawBoth n :: t ∧ WordRun (k n hn) t u v := by
  cases run
  exact ⟨_, _, _,rfl,by assumption⟩

private theorem WordRun.inv_pauseL {A B : Type} {R : A → B → Prop} {x y k} {s u v}
    (run : WordRun (@Coupled.pauseL A B R x y k) s u v) :
    ∃  t, s = .pass .left :: t ∧ WordRun k t u v := by
  cases run
  exact ⟨_,rfl,by assumption⟩

private theorem WordRun.inv_pauseR {A B : Type} {R : A → B → Prop} {x y k} {s u v}
    (run : WordRun (@Coupled.pauseR A B R x y k) s u v) :
    ∃  t, s = .pass .right :: t ∧ WordRun k t u v := by
  cases run
  exact ⟨_,rfl,by assumption⟩

private theorem WordRun.inv_pauseBoth {A B : Type} {R : A → B → Prop} {x y k} {s u v}
    (run : WordRun (@Coupled.pauseBoth A B R x y k) s u v) :
    ∃  t, s = .pass .both :: t ∧ WordRun k t u v := by
  cases run
  exact ⟨_,rfl,by assumption⟩

private theorem WordRun.inv_inspect {A B : Type} {R : A → B → Prop} {x y k} {s u v}
    (run : WordRun (@Coupled.inspect A B R x y k) s u v) :
    ∃ p q t, s = .inspect p q :: t ∧ WordRun (k p q) t u v := by
  cases run
  exact ⟨_, _, _,rfl,by assumption⟩

theorem WordRun.splitBind {A B C D : Type} {R : A → B → Prop} {S : C → D → Prop}
    {x : Thread A} {y : Thread B} (prog : Coupled R x y) (f : A → Thread C) (h : B → Thread D)
    (k : ∀ a b, R a b → Coupled S (f a) (h b)) {s u v} (tr : WordRun (prog.bind f h k) s u v) :
    ∃ p q a b, ∃ hr : R a b, WordRun prog p a b ∧ WordRun (k a b hr) q u v ∧ s = p++q := by
  induction prog generalizing s with
  | result hr => exact ⟨[],s,_,_,hr,.done,tr,rfl⟩
  | planL _ ih =>
    obtain ⟨n,_,rfl,ht⟩ := WordRun.inv_planL tr
    obtain ⟨l,r,a,b,hr,hl,hh,rfl⟩ := ih n ht
    exact ⟨_,r,a,b,hr,.pl n hl,hh,rfl⟩
  | planR _ ih =>
    obtain ⟨n,_,rfl,ht⟩ := WordRun.inv_planR tr
    obtain ⟨l,r,a,b,hr,hl,hh,rfl⟩ := ih n ht
    exact ⟨_,r,a,b,hr,.pr n hl,hh,rfl⟩
  | drawL _ _ ih =>
    obtain ⟨n,hn,_,rfl,ht⟩ := WordRun.inv_drawL tr
    obtain ⟨l,r,a,b,hr,hl,hh,rfl⟩ := ih n hn ht
    exact ⟨_,r,a,b,hr,.dl n hn hl,hh,rfl⟩
  | drawR _ _ ih =>
    obtain ⟨n,hn,_,rfl,ht⟩ := WordRun.inv_drawR tr
    obtain ⟨l,r,a,b,hr,hl,hh,rfl⟩ := ih n hn ht
    exact ⟨_,r,a,b,hr,.dr n hn hl,hh,rfl⟩
  | drawBoth _ _ ih =>
    obtain ⟨n,hn,_,rfl,ht⟩ := WordRun.inv_drawBoth tr
    obtain ⟨l,r,a,b,hr,hl,hh,rfl⟩ := ih n hn ht
    exact ⟨_,r,a,b,hr,.dab n hn hl,hh,rfl⟩
  | pauseL _ ih =>
    obtain ⟨_,rfl,ht⟩ := WordRun.inv_pauseL tr
    obtain ⟨l,r,a,b,hr,hl,hh,rfl⟩ := ih  ht
    exact ⟨_,r,a,b,hr,.sl hl,hh,rfl⟩
  | pauseR _ ih =>
    obtain ⟨_,rfl,ht⟩ := WordRun.inv_pauseR tr
    obtain ⟨l,r,a,b,hr,hl,hh,rfl⟩ := ih  ht
    exact ⟨_,r,a,b,hr,.sr hl,hh,rfl⟩
  | pauseBoth _ ih =>
    obtain ⟨_,rfl,ht⟩ := WordRun.inv_pauseBoth tr
    obtain ⟨l,r,a,b,hr,hl,hh,rfl⟩ := ih  ht
    exact ⟨_,r,a,b,hr,.sab hl,hh,rfl⟩
  | inspect _ ih =>
    obtain ⟨p,q,_,rfl,ht⟩ := WordRun.inv_inspect tr
    obtain ⟨l,r,a,b,hr,hl,hh,rfl⟩ := ih p q ht
    exact ⟨_,r,a,b,hr,.see p q hl,hh,rfl⟩

private theorem indicesNoMask {R : (List ℕ × ℕ) → (List ℕ × ℕ) → Prop} {i j}
    {p : Coupled R (indices i) (indices j)} {t a b} (h : WordRun p t a b) :
    t.filterMap WordEvent.mask = [] := by
  obtain ⟨hx,hy,_⟩ := h.projections
  obtain ⟨_,hl⟩ := indicesInv i hx
  obtain ⟨_,hr⟩ := indicesInv j hy
  have noPause (ds : List ℕ) (n : ℕ) : Action.pause ∉ ds.map Action.draw ++ [.draw n] := by simp
  apply List.filterMap_eq_nil_iff.mpr
  intro e he
  cases e with
  | pass m =>
    cases m with
    | left | both =>
      have hm := List.mem_filterMap.mpr ⟨_,he,(rfl : WordEvent.left _ = some Action.pause)⟩
      rw [hl] at hm
      exact (noPause _ _ hm).elim
    | right =>
      have hm := List.mem_filterMap.mpr ⟨_,he,(rfl : WordEvent.right _ = some Action.pause)⟩
      rw [hr] at hm
      exact (noPause _ _ hm).elim
  | _ => rfl

private theorem coupledVisitMasks {I : Type} (f h : ℕ → Thread I)
    (step : ∀ j, Coupled Eq (f j) (h j)) (mark : ℕ → Option ReadBy)
    (one : ∀ j t u v, WordRun (step j) t u v → t.filterMap WordEvent.mask = (mark j).toList)
    (i n : ℕ) {s u v} (tr : WordRun (coupledVisit f h step i n) s u v) :
    s.filterMap WordEvent.mask = (List.range' i n).filterMap mark := by
  induction n generalizing i s with
  | zero => cases tr; rfl
  | succ n ih =>
    obtain ⟨p,q,a,b,he,ha,ht,rfl⟩ := tr.splitBind (step i) _ _ _
    subst b
    obtain ⟨p',q',w,w',he,hw,hend,rfl⟩ := ht.splitBind (coupledVisit f h step (i+1) n) _ _ _
    cases hend
    simp only [List.append_nil,List.filterMap_append,one _ _ _ _ ha,ih _ hw,List.range'_succ,List.filterMap_cons]
    cases mark i <;> rfl

private theorem coupledLeafEndMask (P Q : Prop) (p : Decidable P) (q : Decidable Q)
    (n : ℕ) {s u v} (tr : WordRun (coupledLeafEnd P Q p q n) s u v) :
    s.filterMap WordEvent.mask = (@ite _ P p (some (@ite _ Q q ReadBy.both ReadBy.left))
      (@ite _ Q q (some ReadBy.right) none)).toList := by
  cases p <;> cases q
  · cases tr; rfl
  · obtain ⟨_,rfl,ht⟩ := WordRun.inv_pauseR tr
    cases ht; rfl
  · obtain ⟨_,rfl,ht⟩ := WordRun.inv_pauseL tr
    cases ht; rfl
  · obtain ⟨_,rfl,ht⟩ := WordRun.inv_pauseBoth tr
    cases ht; rfl

private theorem coupledLeafMask (m r : List ℕ) (j) {s u v}
    (tr : WordRun (coupledLeaf m r j) s u v) :
    s.filterMap WordEvent.mask = (readMask m r j).toList := by
  obtain ⟨n,_,t,rfl,hr⟩ := WordRun.inv_drawBoth tr
  exact coupledLeafEndMask (j ∈ m) (j ∈ r) inferInstance inferInstance n (s := t) hr

theorem coupledBlockMasks (ms : List ReadBy) {s u v} (tr : WordRun (coupledBlock ms) s u v) :
    s.filterMap WordEvent.mask = ms := by
  obtain ⟨p,q,⟨m,n⟩,⟨r,z⟩,hp,hi,ht,rfl⟩ := tr.splitBind (coupledIndices ms 0) _ _ _
  have hn : n = z := hp.same
  subst z
  let visit := coupledVisit (leafProgram m) (leafProgram r) (coupledLeaf m r) 0 n
  obtain ⟨l,tail,a,b,he,body,hend,rfl⟩ := ht.splitBind visit _ _ _
  cases hend
  rw [List.append_nil,List.filterMap_append,indicesNoMask hi,List.nil_append]
  have eq := coupledVisitMasks _ _ (coupledLeaf m r) (readMask m r)
    (fun j _ _ _ => coupledLeafMask m r j) 0 n body
  exact eq.trans (by simpa using hp.scan)

end Larson.PairGame

namespace Larson.PairGame
open Larson.Words

private theorem selectedBlockMasks {a b ms hm s u v}
    (hr : WordRun (selectedBlock a b ms hm) s u v) : s.filterMap WordEvent.mask = ms := by
  obtain rfl : (arities ms).1 = a := congrArg Prod.fst hm
  obtain rfl : (arities ms).2 = b := congrArg Prod.snd hm
  exact coupledBlockMasks ms hr

theorem arrangedBlockMasks (pick a b) {s u v} (h : WordRun (arrangedBlock pick a b) s u v) :
    ∃ p q t, s = .inspect p q :: t ∧ t.filterMap WordEvent.mask = (pick a b p q).1 := by
  obtain ⟨p,q,t,rfl,hr⟩ := WordRun.inv_inspect h
  exact ⟨p,q,t,rfl,selectedBlockMasks hr⟩

private def RowLogs {I : Type} {f h : ℕ → Thread I} (step : ∀ j, Coupled Eq (f j) (h j)) :
    ℕ → List (List WordEvent) → Prop
  | _, [] => True
  | i, s :: ss => (∃ a b, WordRun (step i) s a b) ∧ RowLogs step (i+1) ss

private theorem coupledVisitRows {I : Type} (f h : ℕ → Thread I)
    (step : ∀ j, Coupled Eq (f j) (h j)) (i n : ℕ) {s u v}
    (tr : WordRun (coupledVisit f h step i n) s u v) :
    ∃ rows : List (List WordEvent), rows.length = n ∧ s = rows.flatten ∧ RowLogs step i rows := by
  induction n generalizing i s with
  | zero => cases tr; exact ⟨[],rfl,rfl,trivial⟩
  | succ n ih =>
    obtain ⟨p,q,a,b,he,ha,ht,rfl⟩ := tr.splitBind (step i) _ _ _
    subst b
    obtain ⟨p',q',w,w',he,hw,hend,rfl⟩ := ht.splitBind (coupledVisit f h step (i+1) n) _ _ _
    cases hend
    obtain ⟨rows,hlen,rfl,hrows⟩ := ih _ hw
    exact ⟨p::rows,by simp [hlen],by simp,⟨a,a,ha⟩,hrows⟩

private theorem selectedWordRows (a b : ℕ) (ms : List ReadBy) (hm : arities ms = (a,b))
    (leaf : ℕ → Arrangement) {s u v} (h : WordRun (selectedWord a b ms hm leaf) s u v) :
    ∃ m r n hdr rows, Placed 0 ms (m,n) (r,n) ∧ rows.length = n ∧
      s = hdr ++ rows.flatten ∧ hdr.filterMap WordEvent.mask = [] ∧
      planned (hdr.filterMap WordEvent.left) = [] ∧ planned (hdr.filterMap WordEvent.right) = [] ∧
      RowLogs (fun j => coupledCell m r j (leaf j)) 0 rows := by
  obtain rfl : (arities ms).1 = a := congrArg Prod.fst hm
  obtain rfl : (arities ms).2 = b := congrArg Prod.snd hm
  obtain ⟨hdr,tail,⟨m,n⟩,⟨r,t⟩,hp,hi,ht,rfl⟩ := h.splitBind (coupledIndices ms 0) _ _ _
  obtain rfl : n = t := hp.same
  obtain ⟨body,fin,w,w',eq,hr,hend,rfl⟩ := ht.splitBind (coupledVisit _ _ (fun j => coupledCell m r j (leaf j)) 0 n) _ _ _
  cases hend
  obtain ⟨rows,hlen,rfl,hrows⟩ := coupledVisitRows _ _ _ _ _ hr
  have draws (q : List ℕ) : planned (q.map Action.draw) = [] := by induction q <;> simp_all [planned]
  obtain ⟨_,hl⟩ := indicesInv _ hi.projections.1
  obtain ⟨_,hy⟩ := indicesInv _ hi.projections.2.1
  exact ⟨m,r,n,hdr,rows,hp,hlen,by simp,indicesNoMask hi,by simp [hl,planned_append_eq,draws,planned],
    by simp [hy,planned_append_eq,draws,planned],hrows⟩

theorem coupledWordRows (root : Arrangement) (leaf : ℕ → Arrangement) {s u v}
    (h : WordRun (coupledWord root leaf) s u v) :
    ∃ a b ph qh m r n hdr rows, Placed 0 (root a b ph qh).1 (m,n) (r,n) ∧ rows.length = n ∧
      s = .planL a :: .planR b :: .inspect ph qh :: (hdr ++ rows.flatten) ∧
      hdr.filterMap WordEvent.mask = [] ∧ planned (hdr.filterMap WordEvent.left) = [] ∧
      planned (hdr.filterMap WordEvent.right) = [] ∧ RowLogs (fun j => coupledCell m r j (leaf j)) 0 rows := by
  obtain ⟨a,_,rfl,h1⟩ := WordRun.inv_planL h
  obtain ⟨b,_,rfl,h2⟩ := WordRun.inv_planR h1
  obtain ⟨ph,qh,_,rfl,h3⟩ := WordRun.inv_inspect h2
  obtain ⟨m,r,n,hdr,rows,placed,hlen,rfl,hmask,hl,hr,rowLogs⟩ := selectedWordRows _ _ _ _ _ h3
  exact ⟨a,b,ph,qh,m,r,n,hdr,rows,placed,hlen,rfl,hmask,hl,hr,rowLogs⟩

private theorem blockPlanFree {n s b} (h : Trace (drawBlock n) s b) : planned s = [] := by
  obtain ⟨ms,_,rfl⟩ := blockInv _ h
  have head (ds : List ℕ) : planned (ds.map Action.draw) = [] := by induction ds <;> simp_all [planned]
  have body (i n : ℕ) (w : Tuple ℕ n) : planned (actionsOf (leafActions ms) i n w) = [] := by
    induction n generalizing i with
    | zero => rfl
    | succ n ih => by_cases h : i ∈ ms <;> simp [actionsOf,leafActions,h,planned,ih]
  simp only [blockActions,planned_append_eq,head,planned,List.nil_append,body]

private theorem arrangedInfo (pick a b) {s u v} (h : WordRun (arrangedBlock pick a b) s u v) :
    ∃ p q, s.filterMap WordEvent.mask = (pick a b p q).1 ∧
      planned (s.filterMap WordEvent.left) = [] ∧ planned (s.filterMap WordEvent.right) = [] := by
  obtain ⟨p,q,t,he,hmask⟩ := arrangedBlockMasks pick a b h
  exact ⟨p,q,(by rw [he]; exact hmask),blockPlanFree h.projections.1,blockPlanFree h.projections.2.1⟩

private theorem cellProgramShape (P Q : Prop) (dP : Decidable P) (dQ : Decidable Q) (pick)
    {s u v} (run : WordRun (cellProgram P Q dP dQ pick) s u v) :
    ∃ a b : Option ℕ, ∃ p q, a.isSome = @decide P dP ∧ b.isSome = @decide Q dQ ∧
      planned (s.filterMap WordEvent.left) = a.toList ∧
      planned (s.filterMap WordEvent.right) = b.toList ∧
      s.filterMap WordEvent.mask =
        (pick (a.elim 0 (·+1)) (b.elim 0 (·+1)) p q).1 := by
  cases dP <;> cases dQ
  · obtain ⟨p,q,hm,hl,hr⟩ := arrangedInfo _ _ _ run
    exact ⟨none,none,p,q,rfl,rfl,hl,hr,hm⟩
  · obtain ⟨b,t,rfl,ht⟩ := WordRun.inv_planR run
    obtain ⟨p,q,hm,hl,hr⟩ := arrangedInfo _ _ _ ht
    exact ⟨none,some b,p,q,rfl,rfl,hl,congrArg (b :: ·) hr,hm⟩
  · obtain ⟨a,t,rfl,ht⟩ := WordRun.inv_planL run
    obtain ⟨p,q,hm,hl,hr⟩ := arrangedInfo _ _ _ ht
    exact ⟨some a,none,p,q,rfl,rfl,congrArg (a :: ·) hl,hr,hm⟩
  · obtain ⟨a,t,rfl,ht⟩ := WordRun.inv_planL run
    obtain ⟨b,t',rfl,ht'⟩ := WordRun.inv_planR ht
    obtain ⟨p,q,hm,hl,hr⟩ := arrangedInfo _ _ _ ht'
    exact ⟨some a,some b,p,q,rfl,rfl,congrArg (a :: ·) hl,congrArg (b :: ·) hr,hm⟩

private theorem oneSided (ms : List ReadBy) :
    ((arities ms).2 = 0 → ms = List.replicate (arities ms).1 .left) ∧
    ((arities ms).1 = 0 → ms = List.replicate (arities ms).2 .right) := by
  induction ms with
  | nil => simp [arities]
  | cons e ms ih =>
    cases e <;> simp [arities,List.replicate_succ] <;> first | exact ih.1 | exact ih.2

inductive MaskShape (pick : Arrangement) :
    List ReadBy → List ℕ → List ℕ → List ReadBy → Prop where
  | nil : MaskShape pick [] [] [] []
  | left {ms a b s} (d : ℕ) : MaskShape pick ms a b s →
      MaskShape pick (.left :: ms) (d :: a) b (List.replicate (d+1) .left ++ s)
  | right {ms a b s} (d : ℕ) : MaskShape pick ms a b s →
      MaskShape pick (.right :: ms) a (d :: b) (List.replicate (d+1) .right ++ s)
  | both {ms a b s} (d e : ℕ) (p q : List ℕ) : MaskShape pick ms a b s →
      MaskShape pick (.both :: ms) (d :: a) (e :: b) ((pick (d+1) (e+1) p q).1 ++ s)

private theorem rowMasks (m r : List ℕ) (pick : Arrangement) (i : ℕ) (rows : List (List WordEvent))
    (h : RowLogs (fun j => coupledCell m r j pick) i rows) :
    MaskShape pick ((List.range' i rows.length).filterMap (readMask m r))
      (planned (rows.flatten.filterMap WordEvent.left)) (planned (rows.flatten.filterMap WordEvent.right))
      (rows.flatten.filterMap WordEvent.mask) := by
  induction rows generalizing i with
  | nil => exact .nil
  | cons s rows ih =>
    obtain ⟨⟨u,v,hr⟩,hrest⟩ := h
    have tail := ih (i+1) hrest
    obtain ⟨a,b,p,q,ha,hb,hl,hr,hm⟩ := cellProgramShape _ _ _ _ _ hr
    simp only [List.length_cons,List.range'_succ,List.filterMap_cons,List.flatten_cons,List.filterMap_append,
      planned_append_eq,hl,hr,hm]
    cases a <;> cases b <;> simp only [Option.isSome_none,Option.isSome_some,Option.toList_none,
      Option.toList_some,List.nil_append,List.singleton_append,Option.elim_none,Option.elim_some,
      false_eq_decide_iff,true_eq_decide_iff] at ha hb ⊢
    case none.none =>
      have z := (oneSided (pick 0 0 p q).1).1 (congrArg Prod.snd (pick 0 0 p q).2)
      rw [congrArg Prod.fst (pick 0 0 p q).2] at z
      simpa [readMask,ha,hb,z] using tail
    case some.none d =>
      have z := (oneSided (pick (d+1) 0 p q).1).1 (congrArg Prod.snd (pick (d+1) 0 p q).2)
      rw [congrArg Prod.fst (pick (d+1) 0 p q).2] at z
      simpa [readMask,ha,hb,z] using MaskShape.left d tail
    case none.some e =>
      have z := (oneSided (pick 0 (e+1) p q).1).2 (congrArg Prod.fst (pick 0 (e+1) p q).2)
      rw [congrArg Prod.snd (pick 0 (e+1) p q).2] at z
      simpa [readMask,ha,hb,z] using MaskShape.right e tail
    case some.some d e =>
      simpa [readMask,ha,hb] using MaskShape.both d e p q tail

theorem coupledWordShape (root leaf : Arrangement) {s u v}
    (h : WordRun (coupledWord root (fun _ => leaf)) s u v) :
    ∃ a b ph qh ds es, planned (s.filterMap WordEvent.left) = a :: ds ∧
      planned (s.filterMap WordEvent.right) = b :: es ∧
      MaskShape leaf (root a b ph qh).1 ds es (s.filterMap WordEvent.mask) := by
  obtain ⟨a,b,ph,qh,m,r,n,hdr,rows,placed,hlen,rfl,hmask,hl,hr,hrows⟩ := coupledWordRows _ _ h
  have shape := rowMasks _ _ _ _ _ hrows
  rw [hlen] at shape
  have hs : (List.range' 0 n).filterMap (readMask m r) = (root a b ph qh).1 := by simpa using placed.scan
  rw [hs] at shape
  refine ⟨a,b,ph,qh,planned (rows.flatten.filterMap WordEvent.left),
    planned (rows.flatten.filterMap WordEvent.right),?_,?_,?_⟩
  all_goals simp [List.filterMap_cons,WordEvent.left,WordEvent.right,WordEvent.mask,planned,
    planned_append_eq,hl,hr,hmask]
  simpa using shape

end Larson.PairGame

namespace Larson.PairGame
open ReadBy

private abbrev weight (ds : List ℕ) := (ds.map (·+1)).sum

private theorem MaskShape.leftPrefix {pick} (k : ℕ) {ms ds es s}
    (h : MaskShape pick (List.replicate k .left ++ ms) ds es s) :
    ∃ pre post tail, ds = pre++post ∧ pre.length = k ∧
      s = List.replicate (weight pre) .left ++ tail ∧ MaskShape pick ms post es tail := by
  induction k generalizing ds s with
  | zero => exact ⟨[],ds,s,rfl,rfl,rfl,h⟩
  | succ k ih =>
    simp only [List.replicate_succ,List.cons_append] at h
    cases h with | left d ht =>
      obtain ⟨pre,post,tail,rfl,hlen,rfl,rest⟩ := ih ht
      exact ⟨d::pre,post,tail,rfl,by simp [hlen],
        by simp [-List.replicate_append_replicate,weight,List.replicate_add,List.append_assoc],rest⟩

private theorem MaskShape.rightPrefix {pick} (k : ℕ) {ms ds es s}
    (h : MaskShape pick (List.replicate k .right ++ ms) ds es s) :
    ∃ pre post tail, es = pre++post ∧ pre.length = k ∧
      s = List.replicate (weight pre) .right ++ tail ∧ MaskShape pick ms ds post tail := by
  induction k generalizing es s with
  | zero => exact ⟨[],es,s,rfl,rfl,rfl,h⟩
  | succ k ih =>
    simp only [List.replicate_succ,List.cons_append] at h
    cases h with | right d ht =>
      obtain ⟨pre,post,tail,rfl,hlen,rfl,rest⟩ := ih ht
      exact ⟨d::pre,post,tail,rfl,by simp [hlen],
        by simp [-List.replicate_append_replicate,weight,List.replicate_add,List.append_assoc],rest⟩

theorem MaskShape.separated {pick} (a b : ℕ) {ds es s}
    (h : MaskShape pick (apart false a b).1 ds es s) :
    s = List.replicate (weight ds) .left ++ List.replicate (weight es) .right := by
  obtain ⟨pre,post,tail,rfl,_,rfl,ht⟩ := h.leftPrefix a
  obtain ⟨pre',post',tail',rfl,_,rfl,hr⟩ := MaskShape.rightPrefix (ms := []) b (by simpa using ht)
  cases hr
  simp

theorem MaskShape.separatedRev {pick} (a b : ℕ) {ds es s}
    (h : MaskShape pick (apart true a b).1 ds es s) :
    s = List.replicate (weight es) .right ++ List.replicate (weight ds) .left := by
  obtain ⟨pre,post,tail,rfl,_,rfl,ht⟩ := h.rightPrefix b
  obtain ⟨pre',post',tail',rfl,_,rfl,hr⟩ := MaskShape.leftPrefix (ms := []) a (by simpa using ht)
  cases hr
  simp

private theorem overlapLastFirst (a b : ℕ) :
    (overlap false (a+1) (b+1) a 0 0).1 =
      List.replicate a .left ++ [.both] ++ List.replicate b .right := by
  simp [overlap,apart]

theorem MaskShape.lastFirst (a b : ℕ) {ds es s}
    (h : MaskShape outsideLeafArrangement (overlap false (a+1) (b+1) a 0 0).1 ds es s) :
    s = List.replicate (weight ds-1) .left ++ [.both] ++ List.replicate (weight es-1) .right := by
  rw [overlapLastFirst,List.append_assoc] at h
  obtain ⟨pre,post,tail,rfl,_,rfl,hr⟩ := h.leftPrefix a
  cases hr with | both d e p q htail =>
    obtain ⟨pre',post',tail',rfl,_,rfl,he⟩ :=
      MaskShape.rightPrefix (ms := []) b (by simpa using htail)
    cases he
    simp only [List.append_nil]
    have hl : weight (pre++[d])-1 = weight pre+d := by simp [weight]
    have hr : weight (e::pre')-1 = e+weight pre' := by simp [weight]
    rw [hl,hr]
    simp only [outsideLeafArrangement,Nat.add_sub_cancel,overlapLastFirst,List.replicate_add,
      List.append_assoc,List.cons_append]

end Larson.PairGame

namespace Larson.PairGame

private theorem pauseAppend (p q : List Action) : pauseCount (p++q) = pauseCount p + pauseCount q := by
  induction p with
  | nil => simp [pauseCount]
  | cons e p ih => cases e <;> simp [pauseCount,ih,Nat.add_comm,Nat.add_left_comm]

private def PairState.tally {A B : Type} (t : PairState A B) (l r : ℕ) : Prop :=
  match t with
  | .left _ _ | .onlyRight _ _ => l = r
  | .right _ _ | .onlyLeft _ _ => l = r+1
  | .done _ _ => l = r ∨ l = r+1

private theorem PairStep.tally {A B : Type} {t u : PairState A B} {l r s}
    (h : PairStep t l r s u) (x y : ℕ) (hc : t.tally x y) :
    u.tally (x+pauseCount l) (y+pauseCount r) := by
  cases h <;> simp_all [PairState.tally,pauseCount]

private theorem PairPath.tally {A B : Type} {t u : PairState A B} {l r s}
    (h : PairPath t l r s u) (x y : ℕ) (hc : t.tally x y) :
    u.tally (x+pauseCount l) (y+pauseCount r) := by
  induction h generalizing x y with
  | nil => simpa [pauseCount] using hc
  | cons step _ ih => simpa only [pauseAppend,← Nat.add_assoc] using ih _ _ (step.tally _ _ hc)

def Focus.leftEnded {A B : Type} {x : Thread A} {y : Thread B} : Focus x y → Bool
  | .onlyRight | .done => true
  | _ => false

def Focus.rightEnded {A B : Type} {x : Thread A} {y : Thread B} : Focus x y → Bool
  | .onlyLeft | .done => true
  | _ => false

def Link.rightTurn {S x y} (e : Link S x y) : Bool :=
  decide (pauseCount e.r + e.focus.rightEnded.toNat < pauseCount e.l + e.focus.leftEnded.toNat)

theorem Link.turnBalance {S x y} (e : Link S x y) :
    pauseCount e.l + e.focus.leftEnded.toNat =
      e.rightTurn.toNat + (pauseCount e.r + e.focus.rightEnded.toNat) := by
  have h := e.path.tally 0 0 rfl
  by_cases lt : pauseCount e.r + e.focus.rightEnded.toNat < pauseCount e.l + e.focus.leftEnded.toNat
  · simp only [rightTurn,lt,decide_true,Bool.toNat_true]
    cases hf : e.focus <;> simp_all [Focus.state,PairState.tally,Focus.leftEnded,Focus.rightEnded] <;> omega
  · simp only [rightTurn,lt,decide_false,Bool.toNat_false,Nat.zero_add]
    cases hf : e.focus <;> simp_all [Focus.state,PairState.tally,Focus.leftEnded,Focus.rightEnded]
    omega

theorem Link.leftOwns {S x y} (e : Link S x y) (live : e.focus.leftEnded = false)
    (turn : e.rightTurn = false) : e.focus.active true = true := by
  have balance := e.turnBalance
  have tally := e.path.tally 0 0 rfl
  cases hf : e.focus <;> simp_all [Focus.state,PairState.tally,Focus.active,Focus.leftEnded,Focus.rightEnded]

theorem Link.rightOwns {S x y} (e : Link S x y) (live : e.focus.rightEnded = false)
    (turn : e.rightTurn = true) : e.focus.active false = true := by
  have balance := e.turnBalance
  have tally := e.path.tally 0 0 rfl
  cases hf : e.focus <;> simp_all [Focus.state,PairState.tally,Focus.active,Focus.leftEnded,Focus.rightEnded]

end Larson.PairGame

namespace Larson.PairGame
open Larson.Words

def Site.accepts : Site → List WordEvent → Word → Prop
  | .live p,s,w => WordRun p s w w
  | .finished v,s,w => s = [] ∧ w = v

def Site.Recorded (p : Coupled Eq drawWord drawWord) (v : Site) (left right : List Action) : Prop :=
  ∃ pre : List WordEvent, pre.filterMap WordEvent.left = left ∧ pre.filterMap WordEvent.right = right ∧
    ∀ t w, v.accepts t w → WordRun p (pre++t) w w

private theorem recordStart (p : Coupled Eq drawWord drawWord) : Site.Recorded p (.live p) [] [] :=
  ⟨[],rfl,rfl,fun _ _ h => h⟩

def Handoff.site {x y : Thread Word} : Handoff Eq x y → Site
  | .done (a := a) _ => .finished a
  | .left q | .right q | .both q => .live q

def Handoff.give {x y : Thread Word} : Handoff Eq x y → List WordEvent
  | .done _ => []
  | .left _ => [.pass .left]
  | .right _ => [.pass .right]
  | .both _ => [.pass .both]

private theorem Handoff.splice {x y : Thread Word} (s : Handoff Eq x y) {t w}
    (h : s.site.accepts t w) : s.run (s.give++t) w w := by
  cases s with
  | done he => cases he; obtain ⟨rfl,rfl⟩ := h; exact ⟨rfl,rfl,rfl⟩
  | left | right | both => exact ⟨t,rfl,h⟩

private theorem advanceRecord {x y : Thread Word} {p : Coupled Eq x y} {orig l r}
    (rec : Site.Recorded orig (.live p) l r) (S : Strategy) (a b : List ℕ) :
    let out := p.nextHandoff S.g S.mono S.bound S.plan a b
    Site.Recorded orig out.stop.site (l++out.l++out.stop.give.filterMap WordEvent.left)
      (r++out.r++out.stop.give.filterMap WordEvent.right) := by
  obtain ⟨pre,hl,hr,ex⟩ := rec
  obtain ⟨log,hL,hR,_,cont⟩ := p.nextHandoff_trace S.g S.mono S.bound S.plan a b
  let out := p.nextHandoff S.g S.mono S.bound S.plan a b
  refine ⟨(pre++log)++out.stop.give,by simp [hl,hL,out],by simp [hr,hR,out],?_⟩
  intro t w h
  simpa only [List.append_assoc] using ex _ _ (cont _ _ _ (out.stop.splice h))

private theorem Link.readLeft_frame {S x y x' l} (e : Link S x y) (act : e.focus.active true = true)
    (h : Fragment x l x') (law : S.legal (moves e.p) l) :
    let v := (e.readLeft act h law).1
    v.l = e.l++l ∧ v.r = e.r ∧ v.focus.leftEnded = e.focus.leftEnded ∧
      v.focus.rightEnded = e.focus.rightEnded := by
  obtain ⟨f,el,er,p,path,legal⟩ := e
  cases f <;> first | exact ⟨rfl,List.append_nil _,rfl,rfl⟩ | contradiction

private theorem Link.readRight_frame {S x y y' r} (e : Link S x y) (act : e.focus.active false = true)
    (h : Fragment y r y') (law : S.legal (moves e.p) r) :
    let v := (e.readRight act h law).1
    v.r = e.r++r ∧ v.l = e.l ∧ v.focus.leftEnded = e.focus.leftEnded ∧
      v.focus.rightEnded = e.focus.rightEnded := by
  obtain ⟨f,el,er,p,path,legal⟩ := e
  cases f <;> first | exact ⟨rfl,List.append_nil _,rfl,rfl⟩ | contradiction

private theorem Link.switchLeft_frame {S x y} (e : Link S (.pause x) y) (act : e.focus.active true = true) :
    let v := e.switchLeft act
    v.l = e.l++[.pause] ∧ v.r = e.r ∧ v.focus.leftEnded = e.focus.leftEnded ∧
      v.focus.rightEnded = e.focus.rightEnded := by
  have fail := e.noFailure
  obtain ⟨f,el,er,p,path,legal⟩ := e
  cases f <;> first | exact ⟨rfl,List.append_nil _,rfl,rfl⟩ | contradiction | exact (fail (.leaf _)).elim

private theorem Link.switchRight_frame {S x y} (e : Link S x (.pause y)) (act : e.focus.active false = true) :
    let v := e.switchRight act
    v.r = e.r++[.pause] ∧ v.l = e.l ∧ v.focus.leftEnded = e.focus.leftEnded ∧
      v.focus.rightEnded = e.focus.rightEnded := by
  have fail := e.noFailure
  obtain ⟨f,el,er,p,path,legal⟩ := e
  cases f <;> first | exact ⟨rfl,List.append_nil _,rfl,rfl⟩ | contradiction | exact (fail (.leaf _)).elim

private theorem Link.endLeft_frame {S a y} (e : Link S (.result a) y) (act : e.focus.active true = true) :
    let v := e.endLeft act
    v.l = e.l ∧ v.r = e.r ∧ v.focus.leftEnded = true ∧ v.focus.rightEnded = e.focus.rightEnded := by
  obtain ⟨f,el,er,p,path,legal⟩ := e
  cases f <;> first | exact ⟨List.append_nil _,List.append_nil _,rfl,rfl⟩ | contradiction

private theorem Link.endRight_frame {S x b} (e : Link S x (.result b)) (act : e.focus.active false = true) :
    let v := e.endRight act
    v.r = e.r ∧ v.l = e.l ∧ v.focus.rightEnded = true ∧ v.focus.leftEnded = e.focus.leftEnded := by
  obtain ⟨f,el,er,p,path,legal⟩ := e
  cases f <;> first | exact ⟨List.append_nil _,List.append_nil _,rfl,rfl⟩ | contradiction

structure Board.Records {S} (w : Board S) (px py pz : Coupled Eq drawWord drawWord) : Prop where
  xLog : Site.Recorded px w.x w.xy.l w.xz.l
  yLog : Site.Recorded py w.y w.xy.r w.yz.l
  zLog : Site.Recorded pz w.z w.yz.r w.xz.r
  xDone : w.xy.focus.leftEnded = !w.x.pending ∧ w.xz.focus.leftEnded = !w.x.pending
  yDone : w.xy.focus.rightEnded = !w.y.pending ∧ w.yz.focus.leftEnded = !w.y.pending
  zDone : w.yz.focus.rightEnded = !w.z.pending ∧ w.xz.focus.rightEnded = !w.z.pending

private theorem Board.recordsStart (S px py pz) :
    (Board.opening S px py pz).Records px py pz :=
  ⟨recordStart _,recordStart _,recordStart _,⟨rfl,rfl⟩,⟨rfl,rfl⟩,⟨rfl,rfl⟩⟩

private theorem Site.Recorded.relabel {p v l r l' r'} (rec : Site.Recorded p v l r)
    (hl : l' = l) (hr : r' = r) : Site.Recorded p v l' r' := by subst l'; subst r'; exact rec

private theorem Board.stepXAnchor {S} (w : Board S) {px py pz} (records : w.Records px py pz)
    (ok : w.canX = true) : ∃ t : Board S, t.budget < w.budget ∧ t.Records px py pz ∧ w.xy.l <+: t.xy.l := by
  obtain ⟨x,y,z,xy,xz,yz⟩ := w
  cases x with
  | finished _ => simp [canX,Site.pending] at ok
  | live p =>
    obtain ⟨ha,hb⟩ : xy.focus.active true = true ∧ xz.focus.active true = true := by
      simpa [canX,Site.pending] using ok
    obtain ⟨rx,ry,rz,xd,yd,zd⟩ := records
    have adv := advanceRecord rx S (moves xy.p) (moves xz.p)
    dsimp only at adv xd yd zd rx ry rz
    generalize hreq : p.nextHandoff S.g S.mono S.bound S.plan (moves xy.p) (moves xz.p) = req at adv
    obtain ⟨l,r,x',y',hl,hr,wl,wr,stop,lower⟩ := req
    have fa := xy.readLeft_frame ha hl wl
    generalize haRead : xy.readLeft ha hl wl = aRead at fa
    obtain ⟨a,aa,_⟩ := aRead
    obtain ⟨a1,a2,a3,a4⟩ := fa
    have fb := xz.readLeft_frame hb hr wr
    generalize hbRead : xz.readLeft hb hr wr = bRead at fb
    obtain ⟨b,bb,_⟩ := bRead
    obtain ⟨b1,b2,b3,b4⟩ := fb
    cases stop with
    | done eq =>
      cases eq
      obtain ⟨af0,af1,af2,af3⟩ := a.endLeft_frame aa
      obtain ⟨bf0,bf1,bf2,bf3⟩ := b.endLeft_frame bb
      refine ⟨⟨.finished _,y,z,a.endLeft aa,b.endLeft bb,yz⟩,Prod.Lex.left _ _ lower,?_⟩
      simp only [Handoff.give,Handoff.site,List.filterMap_nil,WordEvent.left,WordEvent.right,List.append_nil] at adv
      refine ⟨?_, ⟨l,(af0.trans a1).symm⟩⟩
      exact ⟨adv.relabel (af0.trans a1) (bf0.trans b1),
        ry.relabel (af1.trans a2) rfl,
        rz.relabel rfl (bf1.trans b2),
        ⟨af2,bf2⟩,
        ⟨(af3.trans (a4.trans yd.1)),yd.2⟩,
        ⟨zd.1,(bf3.trans (b4.trans zd.2))⟩⟩
    | left q =>
      obtain ⟨af0,af1,af2,af3⟩ := a.switchLeft_frame aa
      refine ⟨⟨.live q,y,z,a.switchLeft aa,b,yz⟩,Prod.Lex.left _ _ lower,?_⟩
      simp only [Handoff.give,Handoff.site,List.filterMap_cons,List.filterMap_nil,WordEvent.left,WordEvent.right,List.append_nil] at adv
      refine ⟨?_, ⟨l++[.pause],by simpa only [List.append_assoc] using ((af0.trans (congrArg (· ++ [.pause]) a1))).symm⟩⟩
      exact ⟨adv.relabel (af0.trans (congrArg (· ++ [.pause]) a1)) b1,
        ry.relabel (af1.trans a2) rfl,
        rz.relabel rfl b2,
        ⟨(af2.trans (a3.trans xd.1)),(b3.trans xd.2)⟩,
        ⟨(af3.trans (a4.trans yd.1)),yd.2⟩,
        ⟨zd.1,(b4.trans zd.2)⟩⟩
    | right q =>
      obtain ⟨bf0,bf1,bf2,bf3⟩ := b.switchLeft_frame bb
      refine ⟨⟨.live q,y,z,a,b.switchLeft bb,yz⟩,Prod.Lex.left _ _ lower,?_⟩
      simp only [Handoff.give,Handoff.site,List.filterMap_cons,List.filterMap_nil,WordEvent.left,WordEvent.right,List.append_nil] at adv
      refine ⟨?_, ⟨l,a1.symm⟩⟩
      exact ⟨adv.relabel a1 (bf0.trans (congrArg (· ++ [.pause]) b1)),
        ry.relabel a2 rfl,
        rz.relabel rfl (bf1.trans b2),
        ⟨(a3.trans xd.1),(bf2.trans (b3.trans xd.2))⟩,
        ⟨(a4.trans yd.1),yd.2⟩,
        ⟨zd.1,(bf3.trans (b4.trans zd.2))⟩⟩
    | both q =>
      obtain ⟨af0,af1,af2,af3⟩ := a.switchLeft_frame aa
      obtain ⟨bf0,bf1,bf2,bf3⟩ := b.switchLeft_frame bb
      refine ⟨⟨.live q,y,z,a.switchLeft aa,b.switchLeft bb,yz⟩,Prod.Lex.left _ _ lower,?_⟩
      simp only [Handoff.give,Handoff.site,List.filterMap_cons,List.filterMap_nil,WordEvent.left,WordEvent.right] at adv
      refine ⟨?_, ⟨l++[.pause],by simpa only [List.append_assoc] using ((af0.trans (congrArg (· ++ [.pause]) a1))).symm⟩⟩
      exact ⟨adv.relabel (af0.trans (congrArg (· ++ [.pause]) a1)) (bf0.trans (congrArg (· ++ [.pause]) b1)),
        ry.relabel (af1.trans a2) rfl,
        rz.relabel rfl (bf1.trans b2),
        ⟨(af2.trans (a3.trans xd.1)),(bf2.trans (b3.trans xd.2))⟩,
        ⟨(af3.trans (a4.trans yd.1)),yd.2⟩,
        ⟨zd.1,(bf3.trans (b4.trans zd.2))⟩⟩

private theorem Board.stepYAnchor {S} (w : Board S) {px py pz} (records : w.Records px py pz)
    (ok : w.canY = true) : ∃ t : Board S, t.budget < w.budget ∧ t.Records px py pz ∧ w.xy.l <+: t.xy.l := by
  obtain ⟨x,y,z,xy,xz,yz⟩ := w
  cases y with
  | finished _ => simp [canY,Site.pending] at ok
  | live p =>
    obtain ⟨ha,hb⟩ : xy.focus.active false = true ∧ yz.focus.active true = true := by
      simpa [canY,Site.pending] using ok
    obtain ⟨rx,ry,rz,xd,yd,zd⟩ := records
    have adv := advanceRecord ry S (moves xy.p) (moves yz.p)
    dsimp only at adv xd yd zd rx ry rz
    generalize hreq : p.nextHandoff S.g S.mono S.bound S.plan (moves xy.p) (moves yz.p) = req at adv
    obtain ⟨l,r,x',y',hl,hr,wl,wr,stop,lower⟩ := req
    have fa := xy.readRight_frame ha hl wl
    generalize haRead : xy.readRight ha hl wl = aRead at fa
    obtain ⟨a,aa,_⟩ := aRead
    obtain ⟨a1,a2,a3,a4⟩ := fa
    have fb := yz.readLeft_frame hb hr wr
    generalize hbRead : yz.readLeft hb hr wr = bRead at fb
    obtain ⟨b,bb,_⟩ := bRead
    obtain ⟨b1,b2,b3,b4⟩ := fb
    cases stop with
    | done eq =>
      cases eq
      obtain ⟨af0,af1,af2,af3⟩ := a.endRight_frame aa
      obtain ⟨bf0,bf1,bf2,bf3⟩ := b.endLeft_frame bb
      refine ⟨⟨x,.finished _,z,a.endRight aa,xz,b.endLeft bb⟩,Prod.Lex.right _ (Prod.Lex.left _ _ lower),?_⟩
      simp only [Handoff.give,Handoff.site,List.filterMap_nil,WordEvent.left,WordEvent.right,List.append_nil] at adv
      refine ⟨?_, ⟨[],by simpa only [List.append_nil] using (af1.trans a2).symm⟩⟩
      exact ⟨rx.relabel (af1.trans a2) rfl,
        adv.relabel (af0.trans a1) (bf0.trans b1),
        rz.relabel (bf1.trans b2) rfl,
        ⟨(af3.trans (a3.trans xd.1)),xd.2⟩,
        ⟨af2,bf2⟩,
        ⟨(bf3.trans (b4.trans zd.1)),zd.2⟩⟩
    | left q =>
      obtain ⟨af0,af1,af2,af3⟩ := a.switchRight_frame aa
      refine ⟨⟨x,.live q,z,a.switchRight aa,xz,b⟩,Prod.Lex.right _ (Prod.Lex.left _ _ lower),?_⟩
      simp only [Handoff.give,Handoff.site,List.filterMap_cons,List.filterMap_nil,WordEvent.left,WordEvent.right,List.append_nil] at adv
      refine ⟨?_, ⟨[],by simpa only [List.append_nil] using (af1.trans a2).symm⟩⟩
      exact ⟨rx.relabel (af1.trans a2) rfl,
        adv.relabel (af0.trans (congrArg (· ++ [.pause]) a1)) b1,
        rz.relabel b2 rfl,
        ⟨(af2.trans (a3.trans xd.1)),xd.2⟩,
        ⟨(af3.trans (a4.trans yd.1)),(b3.trans yd.2)⟩,
        ⟨(b4.trans zd.1),zd.2⟩⟩
    | right q =>
      obtain ⟨bf0,bf1,bf2,bf3⟩ := b.switchLeft_frame bb
      refine ⟨⟨x,.live q,z,a,xz,b.switchLeft bb⟩,Prod.Lex.right _ (Prod.Lex.left _ _ lower),?_⟩
      simp only [Handoff.give,Handoff.site,List.filterMap_cons,List.filterMap_nil,WordEvent.left,WordEvent.right,List.append_nil] at adv
      refine ⟨?_, ⟨[],by simpa only [List.append_nil] using (a2).symm⟩⟩
      exact ⟨rx.relabel a2 rfl,
        adv.relabel a1 (bf0.trans (congrArg (· ++ [.pause]) b1)),
        rz.relabel (bf1.trans b2) rfl,
        ⟨(a3.trans xd.1),xd.2⟩,
        ⟨(a4.trans yd.1),(bf2.trans (b3.trans yd.2))⟩,
        ⟨(bf3.trans (b4.trans zd.1)),zd.2⟩⟩
    | both q =>
      obtain ⟨af0,af1,af2,af3⟩ := a.switchRight_frame aa
      obtain ⟨bf0,bf1,bf2,bf3⟩ := b.switchLeft_frame bb
      refine ⟨⟨x,.live q,z,a.switchRight aa,xz,b.switchLeft bb⟩,Prod.Lex.right _ (Prod.Lex.left _ _ lower),?_⟩
      simp only [Handoff.give,Handoff.site,List.filterMap_cons,List.filterMap_nil,WordEvent.left,WordEvent.right] at adv
      refine ⟨?_, ⟨[],by simpa only [List.append_nil] using (af1.trans a2).symm⟩⟩
      exact ⟨rx.relabel (af1.trans a2) rfl,
        adv.relabel (af0.trans (congrArg (· ++ [.pause]) a1)) (bf0.trans (congrArg (· ++ [.pause]) b1)),
        rz.relabel (bf1.trans b2) rfl,
        ⟨(af2.trans (a3.trans xd.1)),xd.2⟩,
        ⟨(af3.trans (a4.trans yd.1)),(bf2.trans (b3.trans yd.2))⟩,
        ⟨(bf3.trans (b4.trans zd.1)),zd.2⟩⟩

private theorem Board.stepZAnchor {S} (w : Board S) {px py pz} (records : w.Records px py pz)
    (ok : w.canZ = true) : ∃ t : Board S, t.budget < w.budget ∧ t.Records px py pz ∧ w.xy.l <+: t.xy.l := by
  obtain ⟨x,y,z,xy,xz,yz⟩ := w
  cases z with
  | finished _ => simp [canZ,Site.pending] at ok
  | live p =>
    obtain ⟨ha,hb⟩ : yz.focus.active false = true ∧ xz.focus.active false = true := by
      simpa [canZ,Site.pending] using ok
    obtain ⟨rx,ry,rz,xd,yd,zd⟩ := records
    have adv := advanceRecord rz S (moves yz.p) (moves xz.p)
    dsimp only at adv xd yd zd rx ry rz
    generalize hreq : p.nextHandoff S.g S.mono S.bound S.plan (moves yz.p) (moves xz.p) = req at adv
    obtain ⟨l,r,x',y',hl,hr,wl,wr,stop,lower⟩ := req
    have fa := yz.readRight_frame ha hl wl
    generalize haRead : yz.readRight ha hl wl = aRead at fa
    obtain ⟨a,aa,_⟩ := aRead
    obtain ⟨a1,a2,a3,a4⟩ := fa
    have fb := xz.readRight_frame hb hr wr
    generalize hbRead : xz.readRight hb hr wr = bRead at fb
    obtain ⟨b,bb,_⟩ := bRead
    obtain ⟨b1,b2,b3,b4⟩ := fb
    cases stop with
    | done eq =>
      cases eq
      obtain ⟨af0,af1,af2,af3⟩ := a.endRight_frame aa
      obtain ⟨bf0,bf1,bf2,bf3⟩ := b.endRight_frame bb
      refine ⟨⟨x,y,.finished _,xy,b.endRight bb,a.endRight aa⟩,Prod.Lex.right _ (Prod.Lex.right _ lower),?_⟩
      simp only [Handoff.give,Handoff.site,List.filterMap_nil,WordEvent.left,WordEvent.right,List.append_nil] at adv
      refine ⟨?_, List.prefix_refl _⟩
      exact ⟨rx.relabel rfl (bf1.trans b2),
        ry.relabel rfl (af1.trans a2),
        adv.relabel (af0.trans a1) (bf0.trans b1),
        ⟨xd.1,(bf3.trans (b3.trans xd.2))⟩,
        ⟨yd.1,(af3.trans (a3.trans yd.2))⟩,
        ⟨af2,bf2⟩⟩
    | left q =>
      obtain ⟨af0,af1,af2,af3⟩ := a.switchRight_frame aa
      refine ⟨⟨x,y,.live q,xy,b,a.switchRight aa⟩,Prod.Lex.right _ (Prod.Lex.right _ lower),?_⟩
      simp only [Handoff.give,Handoff.site,List.filterMap_cons,List.filterMap_nil,WordEvent.left,WordEvent.right,List.append_nil] at adv
      refine ⟨?_, List.prefix_refl _⟩
      exact ⟨rx.relabel rfl b2,
        ry.relabel rfl (af1.trans a2),
        adv.relabel (af0.trans (congrArg (· ++ [.pause]) a1)) b1,
        ⟨xd.1,(b3.trans xd.2)⟩,
        ⟨yd.1,(af2.trans (a3.trans yd.2))⟩,
        ⟨(af3.trans (a4.trans zd.1)),(b4.trans zd.2)⟩⟩
    | right q =>
      obtain ⟨bf0,bf1,bf2,bf3⟩ := b.switchRight_frame bb
      refine ⟨⟨x,y,.live q,xy,b.switchRight bb,a⟩,Prod.Lex.right _ (Prod.Lex.right _ lower),?_⟩
      simp only [Handoff.give,Handoff.site,List.filterMap_cons,List.filterMap_nil,WordEvent.left,WordEvent.right,List.append_nil] at adv
      refine ⟨?_, List.prefix_refl _⟩
      exact ⟨rx.relabel rfl (bf1.trans b2),
        ry.relabel rfl a2,
        adv.relabel a1 (bf0.trans (congrArg (· ++ [.pause]) b1)),
        ⟨xd.1,(bf2.trans (b3.trans xd.2))⟩,
        ⟨yd.1,(a3.trans yd.2)⟩,
        ⟨(a4.trans zd.1),(bf3.trans (b4.trans zd.2))⟩⟩
    | both q =>
      obtain ⟨af0,af1,af2,af3⟩ := a.switchRight_frame aa
      obtain ⟨bf0,bf1,bf2,bf3⟩ := b.switchRight_frame bb
      refine ⟨⟨x,y,.live q,xy,b.switchRight bb,a.switchRight aa⟩,Prod.Lex.right _ (Prod.Lex.right _ lower),?_⟩
      simp only [Handoff.give,Handoff.site,List.filterMap_cons,List.filterMap_nil,WordEvent.left,WordEvent.right] at adv
      refine ⟨?_, List.prefix_refl _⟩
      exact ⟨rx.relabel rfl (bf1.trans b2),
        ry.relabel rfl (af1.trans a2),
        adv.relabel (af0.trans (congrArg (· ++ [.pause]) a1)) (bf0.trans (congrArg (· ++ [.pause]) b1)),
        ⟨xd.1,(bf2.trans (b3.trans xd.2))⟩,
        ⟨yd.1,(af2.trans (a3.trans yd.2))⟩,
        ⟨(af3.trans (a4.trans zd.1)),(bf3.trans (b4.trans zd.2))⟩⟩

private theorem Board.stepXRecord {S} (w : Board S) {px py pz} (rec : w.Records px py pz)
    (ok : w.canX = true) : ∃ t : Board S, t.budget < w.budget ∧ t.Records px py pz := by
  obtain ⟨t,lt,r,_⟩ := w.stepXAnchor rec ok
  exact ⟨t,lt,r⟩

private theorem Board.stepYRecord {S} (w : Board S) {px py pz} (rec : w.Records px py pz)
    (ok : w.canY = true) : ∃ t : Board S, t.budget < w.budget ∧ t.Records px py pz := by
  obtain ⟨t,lt,r,_⟩ := w.stepYAnchor rec ok
  exact ⟨t,lt,r⟩

private theorem Board.stepZRecord {S} (w : Board S) {px py pz} (rec : w.Records px py pz)
    (ok : w.canZ = true) : ∃ t : Board S, t.budget < w.budget ∧ t.Records px py pz := by
  obtain ⟨t,lt,r,_⟩ := w.stepZAnchor rec ok
  exact ⟨t,lt,r⟩

structure LinkProfile {S x y} (e : Link S x y) (mode : Bool) where
  left : List ℕ
  right : List ℕ
  opening : left.length = S.plan []
  balance : weight left = weight right + (if mode then 1 else 0)
  leftPrefix : planned e.l <+: left.length :: left
  rightPrefix : planned e.r <+: right.length :: right
  leftSorted : (e.l.filterMap builderNumber).Pairwise (· < ·)
  rightSorted : (e.r.filterMap builderNumber).Pairwise (· < ·)
  witness : ∃ c d u v tail, right.length = d.blocks.length ∧ (e.l <+: wordActions c u) ∧
    Weave true (wordActions c u) (wordActions d v) (e.p++tail) ∧ S.legal [] (e.p++tail) ∧
    planned (wordActions c u) = left.length :: left ∧ planned (wordActions d v) = right.length :: right

theorem Link.hasProfile {S x y} (e : Link S x y) (inc : S.increasing) (mode)
    (fixed : EndOrder S.g S.bound S.plan mode) : Nonempty (LinkProfile e mode) := by
  obtain ⟨c,d,u,v,a,b,tx,ty,tail,hx,hy,w,legal,ha,hb,hl,hr,eq⟩ := e.profileBalance inc mode fixed
  have sorted := (withinLabels inc _ _ legal).1
  have lx := sorted.sublist w.builderSublists.1
  have ly := sorted.sublist w.builderSublists.2
  rw [hx,List.filterMap_append,List.pairwise_append] at lx
  rw [hy,List.filterMap_append,List.pairwise_append] at ly
  have op : c.blocks.length = S.plan [] := by
    generalize hist : e.p++tail = s at w legal
    unfold wordActions at w
    cases w with | planLeft n _ => exact legal.1 _ rfl
  have fullL := hl
  have fullR := hr
  rw [hx,planned_append_eq] at hl
  rw [hy,planned_append_eq] at hr
  exact ⟨⟨a,b,ha.trans op,eq,⟨_,hl⟩,⟨_,hr⟩,lx.1,ly.1,⟨c,d,u,v,tail,hb,⟨_,hx.symm⟩,w,legal,fullL,fullR⟩⟩⟩

def Site.program (s : Site) : Coupled Eq s.first s.second :=
  match s with
  | .live p => p
  | .finished _ => .result rfl

private theorem Site.acceptsProgram (s : Site) {t u v} (h : WordRun s.program t u v) :
    u = v ∧ s.accepts t u := by
  cases s with
  | live p => obtain rfl := h.projections.2.2; exact ⟨rfl,h⟩
  | finished w => cases h; exact ⟨rfl,rfl,rfl⟩

theorem Site.Recorded.fit {orig v l r} (h : Site.Recorded orig v l r) (ds es : List ℕ)
    (lp : planned l <+: ds.length :: ds) (rp : planned r <+: es.length :: es)
    (ls : (l.filterMap builderNumber).Pairwise (· < ·)) (rs : (r.filterMap builderNumber).Pairwise (· < ·))
    (obs : List ℕ × List ℕ) :
    ∃ pre tail w, pre.filterMap WordEvent.left = l ∧ pre.filterMap WordEvent.right = r ∧
      WordRun orig (pre++tail) w w ∧ (v.pending = false → tail = []) ∧
      planned ((pre++tail).filterMap WordEvent.left) = ds.length :: ds ∧
      planned ((pre++tail).filterMap WordEvent.right) = es.length :: es := by
  obtain ⟨pre,rfl,rfl,extend⟩ := h
  have ex t u v' (tape : WordRun v.program t u v') : WordRun orig (pre++t) u v' := by
    obtain ⟨rfl,ok⟩ := v.acceptsProgram tape
    exact extend t u ok
  obtain ⟨tail,w,full,res,hl,hr⟩ := fillCompatiblePrefix v.program pre ex ds es obs lp rp ls rs
  refine ⟨pre,tail,w,rfl,rfl,full,?_,hl,hr⟩
  intro done
  cases v with
  | live => contradiction
  | finished _ => cases res; rfl

end Larson.PairGame

namespace Larson.PairGame.Schedule

inductive Visit where
  | xA | xB | xAB
  | yA | yC | yAC
  | zB | zC | zBC
  deriving DecidableEq

open Visit

structure Turns where
  xy : Bool
  xz : Bool
  yz : Bool
  deriving DecidableEq

def initial : Turns := ⟨false, false, false⟩
def finalTurns : Turns := ⟨false, false, false⟩

def advance (s : Turns) : Visit → Option Turns
  | .xA  => if !s.xy && !s.xz then some ⟨true,false,s.yz⟩ else none
  | .xB  => if !s.xy && !s.xz then some ⟨false,true,s.yz⟩ else none
  | .xAB => if !s.xy && !s.xz then some ⟨true,true,s.yz⟩ else none
  | .yA  => if s.xy && !s.yz then some ⟨false,s.xz,false⟩ else none
  | .yC  => if s.xy && !s.yz then some ⟨true,s.xz,true⟩ else none
  | .yAC => if s.xy && !s.yz then some ⟨false,s.xz,true⟩ else none
  | .zB  => if s.xz && s.yz then some ⟨s.xy,false,true⟩ else none
  | .zC  => if s.xz && s.yz then some ⟨s.xy,true,false⟩ else none
  | .zBC => if s.xz && s.yz then some ⟨s.xy,false,false⟩ else none

def run (s : Turns) : List Visit → Option Turns
  | [] => some s
  | v :: vs => (advance s v).bind (fun t => run t vs)

private theorem run_append (s : Turns) (vs ws : List Visit) :
    run s (vs ++ ws) = (run s vs).bind (fun t => run t ws) := by
  induction vs generalizing s with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.cons_append, run]
    cases advance s v <;> simp [ih]

private def laps (vs : List Visit) (n : Nat) := (List.replicate n vs).flatten

private theorem repeat_cycle (s : Turns) (vs : List Visit) (n : Nat)
    (cycle : run s vs = some s) : run s (laps vs n) = some s := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [laps, List.replicate_succ, run_append, cycle] using ih

def outside (a b c : Nat) :=
  laps [xA,yA] a ++ [xA,yAC] ++ laps [xB,zB] b ++ [xAB] ++
  laps [zC,yC] c ++ [zC,yAC,zBC]

def inside (b t m n a : Nat) :=
  laps [xA,yA] b ++ [xAB] ++ laps [yC,zC] n ++ [yC,zBC] ++
  laps [yA,xA] t ++ [yAC] ++ laps [xB,zB] m ++ [xB,zBC] ++
  laps [xA,yA] a ++ [xA,yAC,xAB]

def insideEmptyYZ (m a : Nat) :=
  [xAB,yAC,zB] ++ laps [xB,zB] m ++ [xB,zBC] ++
  laps [xA,yA] a ++ [xA,yAC,xAB]

def insideEmptyXY (n : Nat) :=
  [xAB] ++ laps [yC,zC] n ++ [yC,zBC,yAC,xAB]

private theorem run_after {s t u : Turns} {vs ws : List Visit}
    (first : run s vs = some t) (second : run t ws = some u) :
    run s (vs ++ ws) = some u := by rw [run_append, first]; exact second

theorem outsideRuns (a b c : Nat) :
    run initial (outside a b c) = some finalTurns  := by
  simp only [outside, initial, finalTurns, List.append_assoc]
  repeat' first
    | exact rfl
    | refine run_after (repeat_cycle _ _ _ (by rfl)) ?_
    | refine run_after (by rfl) ?_

theorem insideRuns (b t m n a : Nat) :
    run initial (inside b t m n a) = some ⟨true,true,true⟩  := by
  simp only [inside, initial, List.append_assoc]
  repeat' first
    | exact rfl
    | refine run_after (repeat_cycle _ _ _ (by rfl)) ?_
    | refine run_after (by rfl) ?_

theorem insideEmptyXYRuns (n : Nat) :
    run initial (insideEmptyXY n) = some ⟨true,true,true⟩  := by
  simp only [insideEmptyXY, initial, List.append_assoc]
  repeat' first
    | exact rfl
    | refine run_after (repeat_cycle _ _ _ (by rfl)) ?_
    | refine run_after (by rfl) ?_

inductive Vertex where | x | y | z
  deriving DecidableEq

def owner : Visit → Vertex
  | xA | xB | xAB => .x
  | yA | yC | yAC => .y
  | zB | zC | zBC => .z

def localTape (v : Vertex) (schedule : List Visit) : List Visit :=
  schedule.filter (fun e => owner e == v)

private theorem local_append (v : Vertex) (l r : List Visit) :
    localTape v (l ++ r) = localTape v l ++ localTape v r := List.filter_append _ _

private theorem local_laps (v : Vertex) (l : List Visit) (n : Nat) :
    localTape v (laps l n) = laps (localTape v l) n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [laps, List.replicate_succ, List.flatten_cons, local_append] using (congrArg (localTape v l ++ ·) ih)

private theorem laps_one (e : Visit) (n : Nat) : laps [e] n = List.replicate n e := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [laps, List.replicate_succ, List.flatten_cons, List.singleton_append]
      using congrArg (e :: ·) ih

private theorem laps_nil (n : Nat) : laps [] n = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [laps, List.replicate_succ, List.flatten_cons, List.nil_append] using ih

private abbrev copies := @List.replicate Visit

theorem outsideTapes (a b c : Nat) :
    localTape .x (outside a b c) = copies a xA ++ [xA] ++ copies b xB ++ [xAB] ∧
    localTape .y (outside a b c) = copies a yA ++ [yAC] ++ copies c yC ++ [yAC] ∧
    localTape .z (outside a b c) = copies b zB ++ copies c zC ++ [zC,zBC] := by
  simp only [outside, local_append, local_laps]
  simp [localTape, owner, laps_one, laps_nil, copies, List.append_assoc]

theorem insideTapes (b t m n a : Nat) :
    localTape .x (inside b t m n a) =
      copies b xA ++ [xAB] ++ copies t xA ++ copies m xB ++ [xB] ++ copies a xA ++ [xA,xAB] ∧
    localTape .y (inside b t m n a) =
      copies b yA ++ copies n yC ++ [yC] ++ copies t yA ++ [yAC] ++ copies a yA ++ [yAC] ∧
    localTape .z (inside b t m n a) =
      copies n zC ++ [zBC] ++ copies m zB ++ [zBC] := by
  simp only [inside, local_append, local_laps]
  simp [localTape, owner, laps_one, laps_nil, copies, List.append_assoc]

theorem insideEmptyXYTapes (n : Nat) :
    localTape .x (insideEmptyXY n) = [xAB,xAB] ∧
    localTape .y (insideEmptyXY n) = copies n yC ++ [yC,yAC] ∧
    localTape .z (insideEmptyXY n) = copies n zC ++ [zBC] := by
  simp only [insideEmptyXY, local_append, local_laps]
  simp [localTape, owner, laps_one, laps_nil, copies]

private def owns (s : Turns) : Vertex → Bool
  | .x => !s.xy && !s.xz
  | .y => s.xy && !s.yz
  | .z => s.xz && s.yz

private theorem owned {s t : Turns} {e : Visit} (h : advance s e = some t) :
    owns s (owner e) = true := by
  cases e <;> simp only [advance] at h <;> split at h <;> simp_all [owns, owner]

private theorem run_head {s t : Turns} {e es} (h : run s (e::es) = some t) :
    ∃ u, advance s e = some u ∧ run u es = some t := by
  cases he : advance s e with
  | none => simp [run,he] at h
  | some u => exact ⟨u,rfl,by simpa [run,he] using h⟩

end Larson.PairGame.Schedule

namespace Larson.PairGame.Schedule
open Visit Vertex

def xyMark : Visit → Bool
  | xA | xAB | yA | yAC => true
  | _ => false

def xzMark : Visit → Bool
  | xB | xAB | zB | zBC => true
  | _ => false

def yzMark : Visit → Bool
  | yC | yAC | zC | zBC => true
  | _ => false

def Consistent (s t : Turns) (spent : Vertex → List Visit) : Prop :=
  s.xy.toNat + (spent x).countP xyMark = t.xy.toNat + (spent y).countP xyMark ∧
  s.xz.toNat + (spent x).countP xzMark = t.xz.toNat + (spent z).countP xzMark ∧
  s.yz.toNat + (spent y).countP yzMark = t.yz.toNat + (spent z).countP yzMark

private def prependAt (e : Visit) (l : Vertex → List Visit) (v : Vertex) :=
  if owner e = v then e :: l v else l v

private theorem spendStep {s s' : Turns} (t : Turns) (e : Visit) (l : Vertex → List Visit)
    (step : advance s e = some s') :
    Consistent s t (prependAt e l) ↔ Consistent s' t l := by
  obtain ⟨a,b,c⟩ := s
  cases e <;> cases a <;> cases b <;> cases c <;> simp [advance] at step
  all_goals subst s'
  all_goals
    simp [Consistent,prependAt,owner,xyMark,xzMark,yzMark,List.countP_cons]
    omega

private theorem emptyOwner {s t : Turns} {l : Vertex → List Visit} (hc : Consistent s t l)
    (v : Vertex) (he : l v = []) (active : owns s v = true) : owns t v = true := by
  obtain ⟨a,b,c⟩ := t
  cases v <;> cases a <;> cases b <;> cases c <;> simp_all [owns,Consistent]
  all_goals omega

theorem enabledOfTapes {s t u : Turns} (whole : List Visit) (spent : Vertex → List Visit)
    (hw : run s whole = some u) (hp : ∀ v, spent v <+: localTape v whole)
    (hc : Consistent s t spent) :
    (∀ v, spent v = localTape v whole) ∨
      ∃ v, owns t v = true ∧ spent v ≠ localTape v whole := by
  induction whole generalizing s spent with
  | nil =>
    left
    intro v
    simpa [localTape] using hp v
  | cons e w ih =>
    obtain ⟨s',hstep,hw⟩ := run_head hw
    cases hs : spent (owner e) with
    | nil =>
      right
      exact ⟨owner e,emptyOwner hc _ hs (owned hstep),by simp [hs,localTape]⟩
    | cons f fs =>
      have matched := hp (owner e)
      simp [hs,localTape] at matched
      obtain ⟨hef,hm⟩ := matched
      subst f
      let remaining v := if v = owner e then fs else spent v
      have early : spent = prependAt e remaining := by
        funext v
        by_cases hv : v = owner e
        · subst v; simp [prependAt,remaining,hs]
        · simp [prependAt,remaining,hv,Ne.symm hv]
      have prefixRest v : remaining v <+: localTape v w := by
        by_cases hv : v = owner e
        · subst v; simpa [remaining,localTape] using hm
        · have h := hp v
          simpa [localTape,remaining,hv,Ne.symm hv] using h
      have restore v : remaining v = localTape v w ↔ spent v = localTape v (e::w) := by
        by_cases hv : v = owner e
        · subst v; simp [remaining,hs,localTape]
        · simp [remaining,hv,Ne.symm hv,localTape]
      rw [early] at hc
      rcases ih remaining hw prefixRest ((spendStep t e remaining hstep).mp hc) with all | ⟨v,hv,hne⟩
      · exact Or.inl (fun v => (restore v).mp (all v))
      · exact Or.inr ⟨v,hv,fun h => hne ((restore v).mpr h)⟩

end Larson.PairGame.Schedule

namespace Larson.PairGame
open Schedule Larson.Words

def visitTag : Vertex → ReadBy → Visit
  | .x,.left => .xA | .x,.right => .xB | .x,.both => .xAB
  | .y,.left => .yA | .y,.right => .yC | .y,.both => .yAC
  | .z,.left => .zC | .z,.right => .zB | .z,.both => .zBC

def firstMark : Vertex → Visit → Bool
  | .x | .y => xyMark
  | .z => yzMark

def secondMark : Vertex → Visit → Bool
  | .x | .z => xzMark
  | .y => yzMark

private theorem countTagged (v : Vertex) (t : List WordEvent) :
    ((t.filterMap WordEvent.mask).map (visitTag v)).countP (firstMark v) = pauseCount (t.filterMap WordEvent.left) ∧
    ((t.filterMap WordEvent.mask).map (visitTag v)).countP (secondMark v) = pauseCount (t.filterMap WordEvent.right) := by
  induction t with
  | nil => exact ⟨rfl,rfl⟩
  | cons e t ih =>
    cases e with
    | pass m =>
      cases m <;> cases v <;> simp_all [WordEvent.mask,WordEvent.left,WordEvent.right,visitTag,
        firstMark,secondMark,xyMark,xzMark,yzMark,List.filterMap_cons,List.countP_cons,pauseCount]
    | _ => simpa [WordEvent.mask,WordEvent.left,WordEvent.right,List.filterMap_cons,pauseCount] using ih

structure LocalCut (v : Vertex) (site : Site) (left right : List Action) (tape : List Visit) where
  spent : List Visit
  initial : spent <+: tape
  finished : spent = tape ↔ site.pending = false
  fst : spent.countP (firstMark v) = pauseCount left + (!site.pending).toNat
  snd : spent.countP (secondMark v) = pauseCount right + (!site.pending).toNat

private theorem cutFromLog (v : Vertex) (site : Site) (pre tail : List WordEvent) (l r)
    (hl : pre.filterMap WordEvent.left = l) (hr : pre.filterMap WordEvent.right = r)
    (done : site.pending = false → tail = []) :
    Nonempty (LocalCut v site l r ((((pre++tail).filterMap WordEvent.mask).map (visitTag v)) ++ [visitTag v .both])) := by
  obtain ⟨x,y⟩ := countTagged v pre
  rw [hl] at x
  rw [hr] at y
  cases h : site.pending with
  | false =>
    obtain rfl := done h
    refine ⟨⟨_,List.prefix_refl _,by simp [h],?_,?_⟩⟩ <;>
      cases v <;> simp_all [visitTag,firstMark,secondMark,xyMark,xzMark,yzMark]
  | true =>
    let a := (pre.filterMap WordEvent.mask).map (visitTag v)
    let b := (tail.filterMap WordEvent.mask).map (visitTag v)
    change Nonempty (LocalCut v site l r _)
    have eq : (((pre++tail).filterMap WordEvent.mask).map (visitTag v)) ++ [visitTag v .both] =
        a ++ (b ++ [visitTag v .both]) := by simp [a,b,List.append_assoc]
    rw [eq]
    refine ⟨⟨a,⟨_,rfl⟩,?_,by simpa [h,a] using x,by simpa [h,a] using y⟩⟩
    simp [h]

theorem Board.activeFromCuts {S px py pz} (w : Board S) (rec : w.Records px py pz)
    (whole : List Visit) {u : Turns} (valid : run initial whole = some u)
    (x : LocalCut .x w.x w.xy.l w.xz.l (localTape .x whole))
    (y : LocalCut .y w.y w.xy.r w.yz.l (localTape .y whole))
    (z : LocalCut .z w.z w.yz.r w.xz.r (localTape .z whole)) :
    (w.x.pending = false ∧ w.y.pending = false ∧ w.z.pending = false) ∨
      w.canX = true ∨ w.canY = true ∨ w.canZ = true := by
  let turns : Turns := ⟨w.xy.rightTurn,w.xz.rightTurn,w.yz.rightTurn⟩
  let spent : Vertex → List Visit := fun | .x => x.spent | .y => y.spent | .z => z.spent
  have hpre v : spent v <+: localTape v whole := by cases v <;> first | exact x.initial | exact y.initial | exact z.initial
  have tally : Consistent initial turns spent := by
    change 0+x.spent.countP (firstMark .x) = _+y.spent.countP (firstMark .y) ∧
      0+x.spent.countP (secondMark .x) = _+z.spent.countP (secondMark .z) ∧
      0+y.spent.countP (secondMark .y) = _+z.spent.countP (firstMark .z)
    simp only [Nat.zero_add,x.fst,x.snd,y.fst,y.snd,z.fst,z.snd]
    exact ⟨by simpa only [rec.xDone.1,rec.yDone.1] using w.xy.turnBalance,
      by simpa only [rec.xDone.2,rec.zDone.2] using w.xz.turnBalance,
      by simpa only [rec.yDone.2,rec.zDone.1] using w.yz.turnBalance⟩
  rcases enabledOfTapes whole spent valid hpre tally with h | ⟨v,own,hne⟩
  · exact Or.inl ⟨x.finished.mp (h .x),y.finished.mp (h .y),z.finished.mp (h .z)⟩
  right
  cases v with
  | x =>
    have live : w.x.pending = true := Bool.eq_true_of_not_eq_false (fun h => hne (x.finished.mpr h))
    have h : w.xy.rightTurn = false ∧ w.xz.rightTurn = false := by simpa [turns,Schedule.owns] using own
    exact Or.inl (by simp [canX,live,w.xy.leftOwns (by simp [rec.xDone.1,live]) h.1,
      w.xz.leftOwns (by simp [rec.xDone.2,live]) h.2])
  | y =>
    have live : w.y.pending = true := Bool.eq_true_of_not_eq_false (fun h => hne (y.finished.mpr h))
    have h : w.xy.rightTurn = true ∧ w.yz.rightTurn = false := by simpa [turns,Schedule.owns] using own
    exact Or.inr (Or.inl (by simp [canY,live,w.xy.rightOwns (by simp [rec.yDone.1,live]) h.1,
      w.yz.leftOwns (by simp [rec.yDone.2,live]) h.2]))
  | z =>
    have live : w.z.pending = true := Bool.eq_true_of_not_eq_false (fun h => hne (z.finished.mpr h))
    have h : w.xz.rightTurn = true ∧ w.yz.rightTurn = true := by simpa [turns,Schedule.owns] using own
    exact Or.inr (Or.inr (by simp [canZ,live,w.yz.rightOwns (by simp [rec.zDone.1,live]) h.2,
      w.xz.rightOwns (by simp [rec.zDone.2,live]) h.1]))

end Larson.PairGame

namespace Larson.PairGame
open Larson.Words Schedule

private theorem Site.Recorded.cut {root leaf : Arrangement} {site l r} (v : Vertex)
    (h : Site.Recorded (coupledWord root (fun _ => leaf)) site l r) (ds es : List ℕ)
    (lp : planned l <+: ds.length :: ds) (rp : planned r <+: es.length :: es)
    (ls : (l.filterMap builderNumber).Pairwise (· < ·)) (rs : (r.filterMap builderNumber).Pairwise (· < ·))
    (tape : List Visit) (all : ∀ p q ms, MaskShape leaf (root ds.length es.length p q).1 ds es ms →
      ms.map (visitTag v) ++ [visitTag v .both] = tape) : Nonempty (LocalCut v site l r tape) := by
  obtain ⟨pre,tail,w,hl,hr,run,ended,al,ar⟩ := h.fit ds es lp rp ls rs ([],[])
  obtain ⟨a,b,ph,qh,ds',es',h1,h2,shape⟩ := coupledWordShape _ _ run
  rw [al] at h1
  rw [ar] at h2
  cases h1
  cases h2
  rw [← all ph qh _ shape]
  exact cutFromLog v site pre tail l r hl hr ended

private theorem weight_positive (ds : List ℕ) (h : 0 < ds.length) : 0 < weight ds := by
  cases ds with
  | nil => contradiction
  | cons n ns => simp [weight]

private theorem middleOutside {a b : ℕ} {ds es s p q} (pa : 0 < a) (pb : 0 < b)
    (mask : MaskShape outsideLeafArrangement (outsideArrangement true false a b p q).1 ds es s) :
    s = List.replicate (weight ds-1) .left ++ [.both] ++ List.replicate (weight es-1) .right := by
  cases a with
  | zero => contradiction
  | succ a =>
    cases b with
    | zero => contradiction
    | succ b => exact MaskShape.lastFirst a b mask

private theorem outsideActive (S : Strategy) (inc : S.increasing) (pos : 0 < S.plan [])
    (fixed : EndOrder S.g S.bound S.plan false) (w : Board S)
    (rec : w.Records
      (coupledWord (outsideArrangement false false) (fun _ => outsideLeafArrangement))
      (coupledWord (outsideArrangement true false) (fun _ => outsideLeafArrangement))
      (coupledWord (outsideArrangement false true) (fun _ => outsideLeafArrangement))) :
    (w.x.pending = false ∧ w.y.pending = false ∧ w.z.pending = false) ∨
      w.canX = true ∨ w.canY = true ∨ w.canZ = true := by
  obtain ⟨A⟩ := w.xy.hasProfile inc false fixed
  obtain ⟨B⟩ := w.xz.hasProfile inc false fixed
  obtain ⟨C⟩ := w.yz.hasProfile inc false fixed
  have ea : weight A.left = weight A.right := by simpa using A.balance
  have eb : weight B.left = weight B.right := by simpa using B.balance
  have ec : weight C.left = weight C.right := by simpa using C.balance
  have pa : 0 < weight A.left := weight_positive _ (A.opening ▸ pos)
  have pc : 0 < weight C.left := weight_positive _ (C.opening ▸ pos)
  obtain ⟨a,ha⟩ := Nat.exists_eq_succ_of_ne_zero pa.ne'
  obtain ⟨c,hc⟩ := Nat.exists_eq_succ_of_ne_zero pc.ne'
  have par : 0 < A.right.length := by
    by_contra! h
    have hz : A.right = [] := List.length_eq_zero_iff.mp (by omega)
    simp [ea,hz,weight] at pa
  let whole := outside a (weight B.left) c
  obtain ⟨tx,ty,tz⟩ := outsideTapes a (weight B.left) c
  obtain ⟨cx⟩ := rec.xLog.cut .x A.left B.left A.leftPrefix B.leftPrefix A.leftSorted B.leftSorted
    (localTape .x whole) (by
      intro p q ms mask
      have hx := mask.separated A.left.length B.left.length
      rw [hx,ha,tx]
      simp [visitTag,List.replicate_succ',List.append_assoc])
  obtain ⟨cy⟩ := rec.yLog.cut .y A.right C.left A.rightPrefix C.leftPrefix A.rightSorted C.leftSorted
    (localTape .y whole) (by
      intro p q ms mask
      have hy := middleOutside par (show 0 < C.left.length from C.opening ▸ pos) mask
      rw [hy,← ea,ha,hc,ty]
      simp [visitTag,List.append_assoc])
  obtain ⟨cz⟩ := rec.zLog.cut .z C.right B.right C.rightPrefix B.rightPrefix C.rightSorted B.rightSorted
    (localTape .z whole) (by
      intro p q ms mask
      have hz := mask.separatedRev C.right.length B.right.length
      rw [hz,← eb,← ec,hc,tz]
      simp [visitTag,List.replicate_succ',List.append_assoc])
  exact w.activeFromCuts rec whole (outsideRuns ..) cx cy cz

/-- Realize all three edges using the outside order of marked positions. -/
theorem outsideTriangle (S : Strategy) (inc : S.increasing) (pos : 0 < S.plan [])
    (fixed : EndOrder S.g S.bound S.plan false) : MakesTriangle S.g S.bound S.plan := by
  let make (m z : Bool) := coupledWord (outsideArrangement m z) (fun _ => outsideLeafArrangement)
  have run (w : Board S) (r : w.Records (make false false) (make true false) (make false true)) :
      MakesTriangle S.g S.bound S.plan := by
    induction w using (InvImage.wf Board.budget wellFounded_lt).induction with
    | h w next =>
      rcases outsideActive S inc pos fixed w r with done | x | y | z
      · exact w.finishedTriangle done.1 done.2.1 done.2.2
      · obtain ⟨t,lt,rt⟩ := w.stepXRecord r x; exact next _ lt rt
      · obtain ⟨t,lt,rt⟩ := w.stepYRecord r y; exact next _ lt rt
      · obtain ⟨t,lt,rt⟩ := w.stepZRecord r z; exact next _ lt rt
  exact run _ (Board.recordsStart S _ _ _)

end Larson.PairGame

namespace Larson.PairGame
open ReadBy

theorem MaskShape.oneMeeting {pick : Arrangement} (kl kr nl nr : ℕ) {ds es s}
    (h : MaskShape pick
      (List.replicate kl .left ++ (List.replicate kr .right ++
        (.both :: (List.replicate nr .right ++ List.replicate nl .left)))) ds es s) :
    ∃ ld d lt re e rt p q,
      ds = ld ++ d :: lt ∧ es = re ++ e :: rt ∧
      ld.length = kl ∧ re.length = kr ∧ lt.length = nl ∧ rt.length = nr ∧
      s = List.replicate (weight ld) .left ++ List.replicate (weight re) .right ++
        (pick (d+1) (e+1) p q).1 ++ List.replicate (weight rt) .right ++ List.replicate (weight lt) .left := by
  obtain ⟨ld,dl,_,rfl,hld,rfl,hr⟩ := h.leftPrefix kl
  obtain ⟨re,er,_,rfl,hre,rfl,hm⟩ := hr.rightPrefix kr
  cases hm with | both d e p q tail =>
    obtain ⟨rt,zr,_,rfl,hrt,rfl,hl⟩ := tail.rightPrefix nr
    obtain ⟨lt,zl,_,rfl,hlt,rfl,stop⟩ := MaskShape.leftPrefix (ms := []) nl (by simpa using hl)
    cases stop
    exact ⟨ld,d,lt,re,e,rt,p,q,by simp,by simp,hld,hre,hlt,hrt,by simp [List.append_assoc]⟩

end Larson.PairGame

namespace Larson.PairGame
open Larson.Words

def RightEmpty (g : ℕ → ℕ) (b plan : List ℕ → ℕ) (empty : Bool) : Prop :=
  ∀ c d x y s, Weave true (wordActions c x) (wordActions d y) s →
    Within g b (fun p => some (plan p)) [] s → d.blocks.isEmpty = empty

theorem thinRightEmpty (g : ℕ → ℕ) (bound plan : List ℕ → ℕ) :
    ∃ h : ℕ → ℕ, StrictMono h ∧ ∃ b : List ℕ → ℕ,
      (∀ p j, b p ≤ j → bound p ≤ h j) ∧ ∃ empty, RightEmpty (g ∘ h) b plan empty := by
  let tree := interleave (withPlans drawWord []) (withPlans drawWord [])
  let read (_ _ : List ℕ) (r : Option ((Word × List ℕ) × Word × List ℕ)) :=
    r.elim false (fun xy => xy.2.2.head? == some 0)
  obtain ⟨h,hh,b',pred,hp⟩ := predictAtPrefixes tree g plan (fun _ => Bool) read
  let b p := max (bound p) (b' p)
  refine ⟨h,hh,b,fun p j hj => ((le_max_left ..).trans hj).trans (hh.id_le j),pred [],?_⟩
  intro c d x y s w legal
  have trace := weaveTrace w (traceWithPlans (wordTrace c x) []) (traceWithPlans (wordTrace d y) [])
  have law := withinThin (g := g ∘ h) (h := id) (b := b') (c := b) (fun _ _ hj => (le_max_right ..).trans hj) legal
  have label := hp [] s _ trace law
  cases hd : d.blocks <;> simpa [read,Option.elim,wordActions,planned,hd] using label

end Larson.PairGame

namespace Larson.PairGame
open ReadBy

private theorem MaskShape.justLeft {pick k a b s} (h : MaskShape pick (List.replicate k .left) a b s) :
    b = [] ∧ s = List.replicate (weight a) .left := by
  obtain ⟨l,r,t,rfl,_,rfl,tail⟩ := MaskShape.leftPrefix (ms := []) k (by simpa using h)
  cases tail; simp

private theorem MaskShape.justRight {pick k a b s} (h : MaskShape pick (List.replicate k .right) a b s) :
    a = [] ∧ s = List.replicate (weight b) .right := by
  obtain ⟨l,r,t,rfl,_,rfl,tail⟩ := MaskShape.rightPrefix (ms := []) k (by simpa using h)
  cases tail; simp

private def leafOneX := insideLeafX 1 (fun _ => 0)

private theorem insideOneX {ds es s p q} (h : MaskShape leafOneX (insideRootX 1 1 p q).1 ds es s) :
    s = .both :: (List.replicate (weight es-1) .right ++ List.replicate (weight ds-1) .left) := by
  change MaskShape leafOneX [.both] ds es s at h
  cases h with | both d e p q tail =>
    cases tail
    simp [leafOneX,insideLeafX,overlap,apart,weight]

private theorem insideOneY {k ds es s p q} (h : MaskShape (insideLeafY 1 0) (insideRootY 0 (k+1) 1 p q).1 ds es s) :
    s = List.replicate (weight es-1) .right ++ .both :: List.replicate (weight ds-1) .left := by
  have root : (insideRootY 0 (k+1) 1 p q).1 = .both :: List.replicate k .left := by simp [insideRootY,overlap,apart]
  rw [root] at h
  cases h with | both d e p q tail =>
    obtain ⟨rfl,hs⟩ := tail.justLeft
    rw [hs]
    have leaf : (insideLeafY 1 0 (d+1) (e+1) p q).1 =
        List.replicate e .right ++ [.both] ++ List.replicate d .left := by simp [insideLeafY,overlap,apart]
    rw [leaf]
    simp only [weight,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_sub_cancel]
    have adjust (n : ℕ) : d+1+n-1 = d+n := by omega
    rw [adjust]
    simp only [List.replicate_add,List.append_assoc,List.cons_append,List.nil_append]

private theorem insidePositiveZ {kl kr ds es s p q} (h : MaskShape insideLeafZ
    (insideRootZ (kl+1) (kr+1) p q).1 ds es s) :
    s = List.replicate (weight ds-1) .left ++ [.both] ++ List.replicate (weight es-1) .right := by
  exact MaskShape.lastFirst kl kr h

end Larson.PairGame

namespace Larson.PairGame
open Larson.Words Schedule

private abbrev onePX := coupledWord insideRootX (fun _ => leafOneX)
private abbrev onePY := coupledWord (insideRootY 0) (fun _ => insideLeafY 1 0)
private abbrev onePZ := coupledWord insideRootZ (fun _ => insideLeafZ)

private theorem LinkProfile.rightEmpty {S x y e m} {link : Link S x y} (p : LinkProfile link m)
    (he : RightEmpty S.g S.bound S.plan e) : p.right.isEmpty = e := by
  obtain ⟨c,d,u,v,tail,hlen,_,w,legal,_,_⟩ := p.witness
  have hp := he _ _ _ _ _ w legal
  cases hr : p.right <;> cases hd : d.blocks <;> simp_all

private theorem rootChange {pick root : Arrangement} {p q a b a' b' ds es s}
    (h : MaskShape pick (root a b p q).1 ds es s) (ha : a = a') (hb : b = b') :
    MaskShape pick (root a' b' p q).1 ds es s := ha ▸ hb ▸ h

private theorem oneZeroActive {S : Strategy} (inc : S.increasing) (op : S.plan [] = 1)
    (fixed : EndOrder S.g S.bound S.plan true) (he : RightEmpty S.g S.bound S.plan true) (w : Board S)
    (rec : w.Records onePX onePY onePZ) :
    (w.x.pending = false ∧ w.y.pending = false ∧ w.z.pending = false) ∨
      w.canX = true ∨ w.canY = true ∨ w.canZ = true := by
  obtain ⟨A⟩ := w.xy.hasProfile inc true fixed
  obtain ⟨B⟩ := w.xz.hasProfile inc true fixed
  obtain ⟨C⟩ := w.yz.hasProfile inc true fixed
  have empty {x y} {e : Link S x y} (P : LinkProfile e true) : P.right = [] := by
    simpa using P.rightEmpty he
  have one {x y} {e : Link S x y} (P : LinkProfile e true) : weight P.left = 1 := by
    simpa [empty P,weight] using P.balance
  obtain ⟨tx,ty,tz⟩ := insideEmptyXYTapes 0
  obtain ⟨cx⟩ := rec.xLog.cut .x A.left B.left A.leftPrefix B.leftPrefix A.leftSorted B.leftSorted
    (localTape .x (insideEmptyXY 0)) (by
      intro p q ms h
      have masks := insideOneX (rootChange h (A.opening.trans op) (B.opening.trans op))
      simp [masks,one A,one B,tx,visitTag])
  obtain ⟨cy⟩ := rec.yLog.cut .y A.right C.left A.rightPrefix C.leftPrefix A.rightSorted C.leftSorted
    (localTape .y (insideEmptyXY 0)) (by
      intro p q ms h
      have hh := rootChange h (show A.right.length = 0 by simp [empty A]) (C.opening.trans op)
      change MaskShape _ (List.replicate 1 .right) _ _ _ at hh
      simp [hh.justRight.2,one C,ty,visitTag])
  obtain ⟨cz⟩ := rec.zLog.cut .z C.right B.right C.rightPrefix B.rightPrefix C.rightSorted B.rightSorted
    (localTape .z (insideEmptyXY 0)) (by
      intro p q ms h
      have hh := rootChange h (show C.right.length = 0 by simp [empty C]) (show B.right.length = 0 by simp [empty B])
      change MaskShape _ [] _ _ ms at hh
      have nilMasks {pick ds es s} (tr : MaskShape pick [] ds es s) : s = [] := by cases tr; rfl
      simp [nilMasks hh,tz,visitTag])
  exact w.activeFromCuts rec _ (insideEmptyXYRuns 0) cx cy cz

private theorem onePositiveActive {S : Strategy} (inc : S.increasing) (op : S.plan [] = 1)
    (fixed : EndOrder S.g S.bound S.plan true) (he : RightEmpty S.g S.bound S.plan false) (w : Board S)
    (rec : w.Records onePX onePY onePZ) :
    (w.x.pending = false ∧ w.y.pending = false ∧ w.z.pending = false) ∨
      w.canX = true ∨ w.canY = true ∨ w.canZ = true := by
  obtain ⟨A⟩ := w.xy.hasProfile inc true fixed
  obtain ⟨B⟩ := w.xz.hasProfile inc true fixed
  obtain ⟨C⟩ := w.yz.hasProfile inc true fixed
  have part {x y} {e : Link S x y} (P : LinkProfile e true) :
      ∃ k n, P.right.length = k+1 ∧ weight P.right = n+1 ∧ weight P.left = n+2 := by
    have nz : P.right ≠ [] := by simpa using P.rightEmpty he
    have pk := List.length_pos_iff.mpr nz
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero pk.ne'
    obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (weight_positive _ pk).ne'
    exact ⟨k,n,hk,hn,by simpa only [if_true,hn] using P.balance⟩
  obtain ⟨ka,a,hka,hra,hla⟩ := part A
  obtain ⟨kb,m,hkb,hrb,hlb⟩ := part B
  obtain ⟨kc,n,hkc,hrc,hlc⟩ := part C
  let whole := inside 0 0 m n a
  obtain ⟨tx,ty,tz⟩ := insideTapes 0 0 m n a
  obtain ⟨cx⟩ := rec.xLog.cut .x A.left B.left A.leftPrefix B.leftPrefix A.leftSorted B.leftSorted
    (localTape .x whole) (by
      intro p q ms h
      have masks := insideOneX (rootChange h (A.opening.trans op) (B.opening.trans op))
      rw [masks,tx,hla,hlb]
      simp [visitTag,List.replicate_succ',List.append_assoc])
  obtain ⟨cy⟩ := rec.yLog.cut .y A.right C.left A.rightPrefix C.leftPrefix A.rightSorted C.leftSorted
    (localTape .y whole) (by
      intro p q ms h
      have masks := insideOneY (rootChange h hka (C.opening.trans op))
      rw [masks,ty,hra,hlc]
      simp [visitTag,List.replicate_succ',List.append_assoc])
  obtain ⟨cz⟩ := rec.zLog.cut .z C.right B.right C.rightPrefix B.rightPrefix C.rightSorted B.rightSorted
    (localTape .z whole) (by
      intro p q ms h
      have masks := insidePositiveZ (rootChange h hkc hkb)
      rw [masks,tz,hrc,hrb]
      simp [visitTag,List.append_assoc])
  exact w.activeFromCuts rec whole (insideRuns ..) cx cy cz

theorem insideOneTriangle {S : Strategy} (inc : S.increasing) (op : S.plan [] = 1)
    (fixed : EndOrder S.g S.bound S.plan true) (e : Bool) (he : RightEmpty S.g S.bound S.plan e) :
    MakesTriangle S.g S.bound S.plan := by
  have run (w : Board S) (r : w.Records onePX onePY onePZ) : MakesTriangle S.g S.bound S.plan := by
    induction w using (InvImage.wf Board.budget wellFounded_lt).induction with
    | h w next =>
      have act : (w.x.pending = false ∧ w.y.pending = false ∧ w.z.pending = false) ∨
          w.canX = true ∨ w.canY = true ∨ w.canZ = true := by
        cases e with
        | true => exact oneZeroActive inc op fixed he w r
        | false => exact onePositiveActive inc op fixed he w r
      rcases act with done | x | y | z
      · exact w.finishedTriangle done.1 done.2.1 done.2.2
      · obtain ⟨t,lt,rt⟩ := w.stepXRecord r x; exact next _ lt rt
      · obtain ⟨t,lt,rt⟩ := w.stepYRecord r y; exact next _ lt rt
      · obtain ⟨t,lt,rt⟩ := w.stepZRecord r z; exact next _ lt rt
  exact run _ (Board.recordsStart S _ _ _)

end Larson.PairGame

namespace Larson.PairGame
open ReadBy

private def leafAt (B : ℕ) : Arrangement := fun a b _ _ =>
  if a = 0 ∨ b = 0 then apart false a b else overlap false a b B 0 (a-B-1)

private theorem leafAtMask {d e B} (hb : B ≤ d) (p q : List ℕ) :
    (leafAt B (d+1) (e+1) p q).1 =
      List.replicate B .left ++ [.both] ++ List.replicate (d-B) .left ++ List.replicate e .right := by
  have ht : d+1-B-1 = d-B := by omega
  have h : B+1+(d-B) = d+1 := by omega
  simp [leafAt,overlap,ht,h,apart,List.append_assoc]

private theorem manyXShape {k B d ds es s p q} (hb : B ≤ d)
    (h : MaskShape (leafAt B) (insideRootX (k+1) (k+1) p q).1 (d::ds) es s) :
    s = List.replicate B .left ++ [.both] ++ List.replicate (d-B) .left ++
      List.replicate (weight es-1) .right ++ List.replicate (weight ds) .left := by
  have root : (insideRootX (k+1) (k+1) p q).1 = .both :: (List.replicate k .right ++ List.replicate k .left) := by
    simp [insideRootX,overlap,apart]
  rw [root] at h
  cases h with | both d0 e ph qh tail =>
    obtain ⟨pre,post,t,rfl,_,rfl,hleft⟩ := tail.rightPrefix k
    obtain ⟨rfl,rfl⟩ := hleft.justLeft
    rw [leafAtMask hb ph qh]
    have add (n : ℕ) : e+1+n-1 = e+n := by omega
    simp only [List.append_nil,weight,List.map_cons,List.sum_cons,add,List.replicate_add,List.append_assoc]

private theorem manyYShape {ds es s p q} (prior : List ℕ) (d : ℕ) (later : List ℕ) (k c B : ℕ)
    (hl : ds = prior ++ d :: later) (hb : weight prior = B) (h1 : B < c) (h2 : c ≤ B+d+1)
    (h : MaskShape (insideLeafY c B) (insideRootY prior.length ds.length (k+1) p q).1 ds es s) :
    s = List.replicate B .left ++ List.replicate (weight es-1) .right ++
      List.replicate (c-B-1) .left ++ [.both] ++ List.replicate (weight ds-c) .left := by
  subst ds
  have root : (insideRootY prior.length (prior++d::later).length (k+1) p q).1 =
      List.replicate prior.length .left ++ (List.replicate k .right ++
      (.both :: (List.replicate 0 .right ++ List.replicate later.length .left))) := by
    simp [insideRootY,overlap,apart,List.append_assoc]
    omega
  rw [root] at h
  obtain ⟨ld,d',lt,re,e,rt,ph,qh,heL,rfl,nld,_,_,nrt,rfl⟩ := h.oneMeeting ..
  obtain rfl := List.append_inj_left heL nld.symm
  have he := List.append_inj_right heL rfl
  cases he
  obtain rfl := List.length_eq_zero_iff.mp nrt
  have hit : (c-B-1)+1+0 ≤ d+1 := by omega
  have adjust : d+1-((c-B-1)+1+0) = d+1-(c-B) := by omega
  have leaf : (insideLeafY c B (d+1) (e+1) ph qh).1 =
      List.replicate e .right ++ List.replicate (c-B-1) .left ++ [.both] ++ List.replicate (d+1-(c-B)) .left := by
    simp [insideLeafY,overlap,apart,hit,adjust,List.append_assoc]
  have wa : weight (prior++d::later)-c = (d+1-(c-B)) + weight later := by
    simp only [weight,List.map_append,List.sum_append,List.map_cons,List.sum_cons] at hb ⊢
    omega
  have wb : weight (re++[e])-1 = weight re+e := by simp [weight]
  rw [leaf,wa,wb,hb]
  simp only [weight,List.map_nil,List.sum_nil,List.replicate_zero,List.nil_append,List.append_nil,
    List.replicate_add,List.append_assoc,List.cons_append]

end Larson.PairGame

namespace Larson.PairGame
open Larson.Words

inductive WordPrefix {A B : Type} {R : A → B → Prop} :
    {x : Thread A} → {y : Thread B} → Coupled R x y → List WordEvent →
    {x' : Thread A} → {y' : Thread B} → Coupled R x' y' → Prop where
  | nil {x y} (p : Coupled R x y) : WordPrefix p [] p
  | pl {f y k s x' y' q} (n) : WordPrefix (k n) s q →
      WordPrefix (@Coupled.planL _ _ R f y k) (.planL n :: s) (q : Coupled R x' y')
  | pr {x f k s x' y' q} (n) : WordPrefix (k n) s q →
      WordPrefix (@Coupled.planR _ _ R x f k) (.planR n :: s) (q : Coupled R x' y')
  | dl {f y lo k s x' y' q} (n hn) : WordPrefix (k n hn) s q →
      WordPrefix (@Coupled.drawL _ _ R f y lo k) (.drawL n :: s) (q : Coupled R x' y')
  | dr {x f lo k s x' y' q} (n hn) : WordPrefix (k n hn) s q →
      WordPrefix (@Coupled.drawR _ _ R x f lo k) (.drawR n :: s) (q : Coupled R x' y')
  | dab {f h lo k s x' y' q} (n hn) : WordPrefix (k n hn) s q →
      WordPrefix (@Coupled.drawBoth _ _ R f h lo k) (.drawBoth n :: s) (q : Coupled R x' y')
  | see {x y k s x' y' q} (a b) : WordPrefix (k a b) s q →
      WordPrefix (@Coupled.inspect _ _ R x y k) (.inspect a b :: s) (q : Coupled R x' y')

theorem WordPrefix.append {A B : Type} {R : A → B → Prop} {x y x' y' x'' y''}
    {p : Coupled R x y} {q : Coupled R x' y'} {k : Coupled R x'' y''} {s t}
    (h : WordPrefix p s q) (g : WordPrefix q t k) : WordPrefix p (s++t) k := by
  induction h with
  | nil => exact g
  | pl n _ ih => exact .pl n (ih g)
  | pr n _ ih => exact .pr n (ih g)
  | dl n hn _ ih => exact .dl n hn (ih g)
  | dr n hn _ ih => exact .dr n hn (ih g)
  | dab n hn _ ih => exact .dab n hn (ih g)
  | see a b _ ih => exact .see a b (ih g)

theorem WordPrefix.sound {A B : Type} {R : A → B → Prop} {x y x' y'} {p : Coupled R x y}
    {q : Coupled R x' y'} {s} (h : WordPrefix p s q) :
    Fragment x (s.filterMap WordEvent.left) x' ∧ Fragment y (s.filterMap WordEvent.right) y' ∧
    ∀ t a b, WordRun q t a b → WordRun p (s++t) a b := by
  induction h with
  | nil => exact ⟨.nil _,.nil _,fun _ _ _ h => h⟩
  | pl n _ ih => exact ⟨.plan n ih.1,ih.2.1,fun _ _ _ h => .pl n (ih.2.2 _ _ _ h)⟩
  | pr n _ ih => exact ⟨ih.1,.plan n ih.2.1,fun _ _ _ h => .pr n (ih.2.2 _ _ _ h)⟩
  | dl n hn _ ih => exact ⟨.draw n ih.1,ih.2.1,fun _ _ _ h => .dl n hn (ih.2.2 _ _ _ h)⟩
  | dr n hn _ ih => exact ⟨ih.1,.draw n ih.2.1,fun _ _ _ h => .dr n hn (ih.2.2 _ _ _ h)⟩
  | dab n hn _ ih => exact ⟨.draw n ih.1,.draw n ih.2.1,fun _ _ _ h => .dab n hn (ih.2.2 _ _ _ h)⟩
  | see a b _ ih => exact ⟨ih.1,ih.2.1,fun _ _ _ h => .see a b (ih.2.2 _ _ _ h)⟩

theorem WordPrefix.inBind {A B C D : Type} {R : A → B → Prop} {S : C → D → Prop}
    {x y x' y'} {p : Coupled R x y} {q : Coupled R x' y'} {s} (piece : WordPrefix p s q)
    (f : A → Thread C) (h : B → Thread D) (k : ∀ a b, R a b → Coupled S (f a) (h b)) :
    WordPrefix (p.bind f h k) s (q.bind f h k) := by
  induction piece with
  | nil => exact .nil _
  | pl n _ ih => exact .pl n ih
  | pr n _ ih => exact .pr n ih
  | dl n hn _ ih => exact .dl n hn ih
  | dr n hn _ ih => exact .dr n hn ih
  | dab n hn _ ih => exact .dab n hn ih
  | see a b _ ih => exact .see a b ih

theorem WordRun.finishBind {A B C D : Type} {R : A → B → Prop} {S : C → D → Prop}
    {x y} {p : Coupled R x y} {s a b} (run : WordRun p s a b)
    (clean : s.filterMap WordEvent.mask = []) (f : A → Thread C) (h : B → Thread D)
    (k : ∀ a b, R a b → Coupled S (f a) (h b)) :
    WordPrefix (p.bind f h k) s (k a b run.projections.2.2) := by
  induction run with
  | done => exact .nil _
  | pl n _ ih => exact .pl n (ih clean)
  | pr n _ ih => exact .pr n (ih clean)
  | dl n hn _ ih => exact .dl n hn (ih clean)
  | dr n hn _ ih => exact .dr n hn (ih clean)
  | dab n hn _ ih => exact .dab n hn (ih clean)
  | see a b _ ih => exact .see a b (ih clean)
  | sl | sr | sab => simp [WordEvent.mask] at clean

def GoodLog (S : Strategy) (p q : List ℕ) (log : List WordEvent) :=
  S.legal p (log.filterMap WordEvent.left) ∧ S.legal q (log.filterMap WordEvent.right)

private theorem GoodLog.append {S p q s t} (h : GoodLog S p q s)
    (g : GoodLog S (p++moves (s.filterMap WordEvent.left)) (q++moves (s.filterMap WordEvent.right)) t) :
    GoodLog S p q (s++t) := by
  simpa only [GoodLog,List.filterMap_append,within_append] using And.intro ⟨h.1,g.1⟩ ⟨h.2,g.2⟩

private theorem Handoff.quiet {A B : Type} {R : A → B → Prop} {x y}
    (stop : Handoff R x y) (quiet : ∀ t u v, stop.run t u v → t.filterMap WordEvent.mask = []) :
    ∃ u v, stop.run [] u v := by
  cases stop with
  | done h => exact ⟨_,_,rfl,rfl,rfl⟩
  | left next | right next | both next =>
    obtain ⟨tail,a,b,ht,_⟩ := next.fillPlans (fun _ => 0) (fun _ => 0) 0 0 0 ([],[])
    have hh := quiet _ a b ⟨tail,rfl,ht⟩
    simp [WordEvent.mask] at hh

private theorem Coupled.drain {A B : Type} {R : A → B → Prop} {x y} (p : Coupled R x y)
    (clean : ∀ s a b, WordRun p s a b → s.filterMap WordEvent.mask = [])
    (S : Strategy) (l r : List ℕ) :
    ∃ log u v, WordRun p log u v ∧ GoodLog S l r log := by
  let batch := p.nextHandoff S.g S.mono S.bound S.plan l r
  obtain ⟨log,hl,hr,hm,cont⟩ := p.nextHandoff_trace S.g S.mono S.bound S.plan l r
  change ∀ t u v, batch.stop.run t u v → WordRun p (log++t) u v at cont
  have hw : GoodLog S l r log := ⟨hl ▸ batch.leftLegal,hr ▸ batch.rightLegal⟩
  obtain ⟨u,v,ok⟩ := batch.stop.quiet (fun t u v h => by
    have hh := clean _ _ _ (cont _ _ _ h)
    simpa [hm] using hh)
  exact ⟨log,u,v,by simpa using cont _ _ _ ok,hw⟩

private theorem unmarkedFamily (P Q : Prop) (p : Decidable P) (q : Decidable Q)
    (hp : ¬P) (hq : ¬Q) (B : ℕ) :
    cellProgram P Q p q (leafAt B) = cellProgram P Q p q (leafAt 0) := by
  cases p <;> cases q <;> first | contradiction | rfl

private theorem unmarkedClean (m r : List ℕ) (j : ℕ) (hm : j ∉ m) (hr : j ∉ r)
    {s u v} (run : WordRun (coupledCell m r j (leafAt 0)) s u v) :
    s.filterMap WordEvent.mask = [] ∧ planned (s.filterMap WordEvent.left) = [] ∧
      planned (s.filterMap WordEvent.right) = [] := by
  obtain ⟨a,b,p,q,ha,hb,hl,hR,hmask⟩ := cellProgramShape _ _ _ _ _ run
  cases a <;> cases b <;> simp_all [leafAt,apart]

private theorem openSharedCell (P Q : Prop) (p : Decidable P) (q : Decidable Q)
    (hp : P) (hq : Q) (B d e : ℕ) :
    ∃ x y, ∃ next : Coupled Eq x y,
      WordPrefix (cellProgram P Q p q (leafAt B)) [.planL d,.planR e] next := by
  cases p <;> cases q <;> first | contradiction | exact ⟨_,_,_,.pl _ (.pr _ (.nil _))⟩

private def Prepared {I : Type} {x y : Thread I} (F : ℕ → Coupled Eq x y) (s : List WordEvent) : Prop :=
  ∀ B, ∃ a b, ∃ next : Coupled Eq a b, WordPrefix (F B) s next

private theorem prepareRows (S : Strategy) (m r : List ℕ) (j : ℕ)
    (hm : j ∈ m) (hr : j ∈ r) (empty : ∀ i < j, i ∉ m ∧ i ∉ r)
    (i n : ℕ) (ij : i ≤ j) (jn : j < i+n) (l h : List ℕ) :
    ∃ log d, GoodLog S l h log ∧ planned (log.filterMap WordEvent.left) = [d] ∧
      (∃ before, log.filterMap WordEvent.left = before ++ [.plan d]) ∧
      Prepared (fun B => coupledVisit _ _ (fun row => coupledCell m r row (leafAt B)) i n) log := by
  induction n generalizing i l h with
  | zero => omega
  | succ n ih =>
    by_cases hit : i = j
    · subst j
      let d := S.plan l
      let e := S.plan h
      refine ⟨[.planL d,.planR e],d,⟨⟨by simp [d],trivial⟩,⟨by simp [e],trivial⟩⟩,
        rfl,⟨[],rfl⟩,?_⟩
      intro B
      obtain ⟨x,y,next,piece⟩ := openSharedCell (i ∈ m) (i ∈ r) inferInstance inferInstance hm hr B d e
      exact ⟨_,_,_,piece.inBind _ _ _⟩
    · obtain ⟨em,er⟩ := empty i (by omega)
      let step := coupledCell m r i (leafAt 0)
      obtain ⟨head,u,v,run,legal⟩ := step.drain (fun s _ _ hh => (unmarkedClean m r i em er hh).1) S l h
      have clean := unmarkedClean m r i em er run
      obtain rfl := run.projections.2.2
      obtain ⟨tail,d,ht,hp,⟨before,hb⟩,prepared⟩ := ih (i+1) (by omega) (by omega)
        (l++moves (head.filterMap WordEvent.left)) (h++moves (head.filterMap WordEvent.right))
      refine ⟨head++tail,d,legal.append ht,by simp [planned_append_eq,clean.2.1,hp],
        ⟨head.filterMap WordEvent.left ++ before,by simp [hb,List.append_assoc]⟩,?_⟩
      intro B
      have header : WordRun (coupledCell m r i (leafAt B)) head u u := by
        change WordRun (cellProgram _ _ _ _ _) _ _ _
        rw [unmarkedFamily _ _ _ _ em er B]
        exact run
      obtain ⟨x,y,next,reach⟩ := prepared B
      exact ⟨_,_,_,WordPrefix.append (header.finishBind clean.1 _ _ _) (reach.inBind _ _ _)⟩

private theorem firstShared {ms lo m r} (h : Placed lo (.both :: ms) m r) :
    ∃ j < m.2, j ∈ m.1 ∧ j ∈ r.1 ∧ ∀ i < j, i ∉ m.1 ∧ i ∉ r.1 := by
  cases h with
  | @both s j _ l r hs tail =>
    obtain ⟨hb,hl,hr⟩ := tail.bounds
    refine ⟨j,hb,List.mem_cons_self,List.mem_cons_self,?_⟩
    intro i hi
    constructor <;> intro hm <;> rcases List.mem_cons.mp hm with rfl | h
    · omega
    · have := (hl _ h).1; omega
    · omega
    · have := (hr _ h).1; omega

private theorem prepareBody (S : Strategy) (a b : ℕ) (rest : List ReadBy)
    (arity : arities (.both :: rest) = (a,b)) (p q : List ℕ) :
    ∃ log d, GoodLog S p q log ∧ planned (log.filterMap WordEvent.left) = [d] ∧
      (∃ pre, log.filterMap WordEvent.left = pre ++ [.plan d]) ∧
      Prepared (fun B => selectedWord a b (.both::rest) arity (fun _ => leafAt B)) log := by
  obtain rfl : (arities (.both::rest)).1 = a := congrArg Prod.fst arity
  obtain rfl : (arities (.both::rest)).2 = b := congrArg Prod.snd arity
  obtain ⟨hdr,⟨m,n⟩,⟨r,z⟩,run,law⟩ :=
    (coupledIndices (.both :: rest) 0).drain (fun _ _ _ h => indicesNoMask h) S p q
  have placed := run.projections.2.2
  obtain rfl : n = z := placed.same
  obtain ⟨j,hj,hm,hr,empty⟩ := firstShared placed
  obtain ⟨body,d,wb,pb,⟨pre,hpre⟩,reach⟩ := prepareRows S m r j hm hr empty 0 n (Nat.zero_le _)
    (by simpa using hj) (p++moves (hdr.filterMap WordEvent.left)) (q++moves (hdr.filterMap WordEvent.right))
  have hh := (indicesInv _ run.projections.1).2
  have allDraws (l : List ℕ) : planned (l.map Action.draw) = [] := by induction l <;> simp_all [planned]
  have noPlans : planned (hdr.filterMap WordEvent.left) = [] := by simp [hh,planned_append_eq,allDraws,planned]
  refine ⟨hdr++body,d,law.append wb,by simp [planned_append_eq,noPlans,pb],
    ⟨hdr.filterMap WordEvent.left ++ pre,by simp [hpre,List.append_assoc]⟩,?_⟩
  intro B
  obtain ⟨x,y,next,rows⟩ := reach B
  exact ⟨_,_,_,WordPrefix.append (run.finishBind (indicesNoMask run) _ _ _) (rows.inBind _ _ _)⟩

private theorem warmStart (S : Strategy) (k : ℕ) (op : S.plan [] = k+1) :
    ∃ log d, GoodLog S [] [] log ∧ planned (log.filterMap WordEvent.left) = [k+1,d] ∧
      (∃ pre, log.filterMap WordEvent.left = .plan (k+1) :: (pre++[.plan d])) ∧
      Prepared (fun B => coupledWord insideRootX (fun _ => leafAt B)) log := by
  let p := [k+1]
  let root := insideRootX (k+1) (k+1) p p
  let rest := List.replicate k ReadBy.right ++ List.replicate k ReadBy.left
  have layout : root.val = .both :: rest := by simp [root,p,rest,insideRootX,overlap,apart]
  have ha : arities (.both :: rest) = (k+1,k+1) := layout ▸ root.property
  obtain ⟨log,d,hw,hp,⟨pre,he⟩,ready⟩ := prepareBody S (k+1) (k+1) rest ha p p
  let head : List WordEvent := [.planL (k+1),.planR (k+1),.inspect p p]
  have hlegal : GoodLog S [] [] head :=
    ⟨⟨fun _ h => op ▸ Option.some.inj h,trivial⟩,⟨fun _ h => op ▸ Option.some.inj h,trivial⟩⟩
  refine ⟨head++log,d,hlegal.append hw,?_,⟨pre,?_⟩,?_⟩
  · simp [head,List.filterMap_cons,WordEvent.left,planned,hp]
  · simp [head,List.filterMap_cons,WordEvent.left,he]
  · intro B
    obtain ⟨x,y,next,hr⟩ := ready B
    refine ⟨x,y,next,.pl _ (.pr _ (.see p p ?_))⟩
    change WordPrefix (selectedWord (k+1) (k+1) root.val root.property (fun _ => leafAt B)) log next
    have eq : root = (⟨.both :: rest,ha⟩ :
        {ms : List ReadBy // arities ms = (k+1,k+1)}) := Subtype.ext layout
    have same := congrArg
      (fun sh : {ms : List ReadBy // arities ms = (k+1,k+1)} =>
        selectedWord (k+1) (k+1) sh.1 sh.2 (fun _ => leafAt B)) eq
    rw [same]
    exact hr

private theorem moves_append_eq (a b : List Action) : moves (a++b) = moves a ++ moves b := by
  induction a with
  | nil => rfl
  | cons x a ih => cases x <;> simp [moves,ih]

private theorem weaveHead {l r s} (w : Weave true l r s) (pre : List Action)
    (hp : pre <+: l) (clean : uninterrupted pre) : pre <+: s := by
  induction pre generalizing l r s with
  | nil => exact List.nil_prefix
  | cons e pre ih =>
    obtain ⟨tail,rfl⟩ := hp
    have rest : pre <+: pre++tail := ⟨tail,rfl⟩
    cases e with
    | pause => exact clean.elim
    | plan n => cases w with | planLeft _ w => exact List.cons_prefix_cons.mpr ⟨rfl,ih w rest clean⟩
    | draw n => cases w with | drawLeft _ w => exact List.cons_prefix_cons.mpr ⟨rfl,ih w rest clean⟩

private theorem Fragment.clean {A : Type} {x y : Thread A} {s} (h : Fragment x s y) : uninterrupted s := by
  induction h with
  | nil => trivial
  | plan _ _ ih | draw _ _ ih => exact ih

end Larson.PairGame

namespace Larson.PairGame
open Larson.Words Schedule

private theorem weightGe (ds : List ℕ) : ds.length ≤ weight ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [weight,List.length_cons,List.map_cons,List.sum_cons] at *; omega

private abbrev manyPX (B : ℕ) := coupledWord insideRootX (fun _ => leafAt B)
private abbrev manyPY (j c B : ℕ) := coupledWord (insideRootY j) (fun _ => insideLeafY c B)

private theorem insideManyActive {S : Strategy} (k : ℕ) (op : S.plan [] = k+2) (inc : S.increasing)
    (fixed : EndOrder S.g S.bound S.plan true) (pred : List ℕ → ℕ × ℕ)
    (location : S.RightLocation pred) (pre : List Action) (d : ℕ)
    (plans : planned pre = [k+2,d]) (clean : uninterrupted pre) (idx : pivotIndex (moves pre) = d)
    (w : Board S) (guarded : pre <+: w.xy.l)
    (rec : w.Records (manyPX (pred (moves pre)).2)
      (manyPY (pred (moves pre)).1 (d+1) (pred (moves pre)).2) onePZ) :
    (w.x.pending = false ∧ w.y.pending = false ∧ w.z.pending = false) ∨
      w.canX = true ∨ w.canY = true ∨ w.canZ = true := by
  obtain ⟨A⟩ := w.xy.hasProfile inc true fixed
  obtain ⟨B⟩ := w.xz.hasProfile inc true fixed
  obtain ⟨C⟩ := w.yz.hasProfile inc true fixed
  obtain ⟨ac,ad,u,v,tail,_,preL,weave,law,_,rightPlans⟩ := A.witness
  obtain ⟨q,hq⟩ := weaveHead weave pre (guarded.trans preL) clean
  rw [← hq] at weave law
  have forecast := location _ _ _ _ pre q weave law
  simp only [idx,rightPlans,List.tail_cons] at forecast
  have hPrefix : [k+2,d] <+: A.left.length :: A.left := by
    refine List.IsPrefix.trans ?_ A.leftPrefix
    obtain ⟨t,ht⟩ := guarded
    refine ⟨planned t,?_⟩
    rw [← plans,← planned_append_eq,ht]
  have hasHead : ∃ rest, A.left = d :: rest := by
    cases hh : A.left with
    | nil => simp [hh] at hPrefix
    | cons a rest =>
      simp only [hh,List.cons_prefix_cons] at hPrefix
      exact ⟨rest,by simp [hPrefix.2.1]⟩
  obtain ⟨ds,hds⟩ := hasHead
  have hk : A.left.length = k+2 := A.opening.trans op
  have positive : 0 < weight ds := weight_positive _ (by rw [hds] at hk; simp at hk; omega)
  have total := A.balance
  simp only [hds,weight,List.map_cons,List.sum_cons,if_true] at total
  have inRange : d < weight A.right := by change 0 < (ds.map (·+1)).sum at positive; unfold weight; omega
  obtain ⟨before,e,after,rightShape,hLoc,lower,upper⟩ := cutLocationSpec A.right d inRange
  have key := forecast.symm.trans hLoc
  have key1 := congrArg Prod.fst key
  have key2 := congrArg Prod.snd key
  dsimp only at key1 key2
  let b := weight before
  let a := weight A.right - (d+1)
  have tailWeight : weight ds = a+1 := by
    dsimp only [a,weight]
    change 0 < (ds.map (·+1)).sum at positive
    omega
  have other {x y} {link : Link S x y} (P : LinkProfile link true) :
      ∃ m kr, weight P.left = m+2 ∧ weight P.right = m+1 ∧ P.right.length = kr+1 := by
    have hl := P.opening.trans op
    have hge := weightGe P.left
    have bal : weight P.left = weight P.right+1 := P.balance
    have nz : P.right ≠ [] := by rintro hz; rw [hz] at bal; change weight P.left = 1 at bal; omega
    obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (weight_positive _ (List.length_pos_iff.mpr nz)).ne'
    obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (List.length_pos_iff.mpr nz).ne'
    exact ⟨m,n,by omega,hm,hn⟩
  obtain ⟨m,kr,hlB,hrB,hkr⟩ := other B
  obtain ⟨n,ks,hlC,hrC,hks⟩ := other C
  let whole := inside b (d-b) m n a
  obtain ⟨tx,ty,tz⟩ := insideTapes b (d-b) m n a
  obtain ⟨cx⟩ := rec.xLog.cut .x A.left B.left A.leftPrefix B.leftPrefix A.leftSorted B.leftSorted
    (localTape .x whole) (by
      intro p q ms mask
      have h := rootChange mask hk (B.opening.trans op)
      rw [hds,key2] at h
      have mx := manyXShape (B := b) lower h
      rw [mx,hlB,tailWeight,tx]
      simp [visitTag,List.replicate_succ',List.append_assoc])
  obtain ⟨cy⟩ := rec.yLog.cut .y A.right C.left A.rightPrefix C.leftPrefix A.rightSorted C.leftSorted
    (localTape .y whole) (by
      intro p q ms mask
      have h := rootChange mask (a' := A.right.length) rfl (C.opening.trans op)
      rw [key1,key2] at h
      have my := manyYShape before e after (k+1) (d+1) b rightShape rfl (by dsimp [b,weight]; omega)
        (by dsimp [b,weight]; omega) h
      rw [my,hlC,ty]
      have sub : d+1-b-1 = d-b := by omega
      simp [visitTag,sub,List.replicate_succ',List.append_assoc,a])
  obtain ⟨cz⟩ := rec.zLog.cut .z C.right B.right C.rightPrefix B.rightPrefix C.rightSorted B.rightSorted
    (localTape .z whole) (by
      intro p q ms mask
      have mz := insidePositiveZ (rootChange mask hks hkr)
      rw [mz,hrC,hrB,tz]
      simp [visitTag,List.append_assoc])
  exact w.activeFromCuts rec whole (insideRuns ..) cx cy cz

end Larson.PairGame

namespace Larson.PairGame
open Larson.Words

/-- Read the two opening block plans before fixing the shared cut. -/
theorem insideManyTriangle (S : Strategy) (k : ℕ) (op : S.plan [] = k+2) (inc : S.increasing)
    (fixed : EndOrder S.g S.bound S.plan true) (pred : List ℕ → ℕ × ℕ)
    (location : S.RightLocation pred) : MakesTriangle S.g S.bound S.plan := by
  obtain ⟨log,d,law,plans,⟨pre,he⟩,ready⟩ := warmStart S (k+1) op
  let lx := log.filterMap WordEvent.left
  let target := pred (moves lx)
  obtain ⟨x,y,start,hp⟩ := ready target.2
  have frag := hp.sound
  have clean := frag.1.clean
  have index : pivotIndex (moves lx) = d := by
    simp [lx,he,pivotIndex,moves,moves_append_eq]
    change (((k+1+1) :: moves pre) ++ [d]).getLast?.getD 0 = d
    exact congrArg (fun o : Option ℕ => o.getD 0)
      (List.getLast?_concat (l := (k+1+1) :: moves pre) (a := d))
  let px := manyPX target.2
  let py := manyPY target.1 (d+1) target.2
  let pz := onePZ
  have run (w : Board S) (r : w.Records px py pz) (saved : lx <+: w.xy.l) : MakesTriangle S.g S.bound S.plan := by
    induction w using (InvImage.wf Board.budget wellFounded_lt).induction with
    | h w next =>
      rcases insideManyActive k op inc fixed pred location lx d plans clean index w saved r with done | xx | yy | zz
      · exact w.finishedTriangle done.1 done.2.1 done.2.2
      · obtain ⟨t,lt,rt,mono⟩ := w.stepXAnchor r xx; exact next _ lt rt (saved.trans mono)
      · obtain ⟨t,lt,rt,mono⟩ := w.stepYAnchor r yy; exact next _ lt rt (saved.trans mono)
      · obtain ⟨t,lt,rt,mono⟩ := w.stepZAnchor r zz; exact next _ lt rt (saved.trans mono)
  let A := (Link.start S).readLeft rfl frag.1 law.1
  let B := (Link.start S).readLeft rfl frag.2.1 law.2
  let w : Board S := ⟨.live start,.live py,.live pz,A.1,B.1,.start S⟩
  obtain ⟨a1,a2,a3,a4⟩ := (Link.start S).readLeft_frame rfl frag.1 law.1
  obtain ⟨b1,b2,b3,b4⟩ := (Link.start S).readLeft_frame rfl frag.2.1 law.2
  have rx : Site.Recorded px (.live start) lx (log.filterMap WordEvent.right) :=
    ⟨log,rfl,rfl,fun t v hv => frag.2.2 t v v hv⟩
  have records : w.Records px py pz :=
    ⟨rx.relabel a1 b1,(recordStart py).relabel a2 rfl,(recordStart pz).relabel rfl b2,
      ⟨a3,b3⟩,⟨a4,rfl⟩,⟨rfl,b4⟩⟩
  apply run w records
  change lx <+: ((Link.start S).readLeft rfl frag.1 law.1).1.l
  rw [a1]
  change lx <+: [] ++ lx
  simp

end Larson.PairGame

namespace Larson.PairGame

/-- Thin to a fixed end order and predicted cut, then realize a triangle there. -/
theorem architectTriangle : ArchitectTriangle := by
  intro g hg bound plan valid
  rcases Nat.eq_zero_or_pos (plan []) with zero | pos
  · exact architectTriangleZeroRoot hg zero valid
  obtain ⟨f,hf,b,hb,mode,endLaw⟩ := thinEndOrder g bound plan
  obtain ⟨h,hh,c,hc,empty,rightLaw⟩ := thinRightEmpty (g ∘ f) b plan
  obtain ⟨r,hr,d,hd,pred,location⟩ := predictRightCut ((g ∘ f) ∘ h) c plan pivotIndex
  let draws := ((g ∘ f) ∘ h) ∘ r
  let D (p : List ℕ) := max (d p) (p.toFinset.sup id + 1)
  have weaken (p : List ℕ) (j : ℕ) (hj : D p ≤ j) : d p ≤ id j := (le_max_left ..).trans hj
  have law {p s} (hw : Within draws D (fun t => some (plan t)) p s) :
      Within draws d (fun t => some (plan t)) p s := withinThin (g := draws) (h := id) weaken hw
  let S : Strategy := ⟨draws,((hg.comp hf).comp hh).comp hr,D,plan,
    fun s ht hw => valid s ht (withinThin hb (withinThin hc (withinThin hd (law hw))))⟩
  have inc : S.increasing := by
    intro p n hn
    exact (Nat.lt_succ_of_le (Finset.le_sup (f := id) (List.mem_toFinset.mpr hn))).trans_le (le_max_right ..)
  have fixed : EndOrder S.g S.bound S.plan mode :=
    fun a b x y s w hw => endLaw a b x y s w (withinThin hc (withinThin hd (law hw)))
  have fixedRoot : RightEmpty S.g S.bound S.plan empty :=
    fun a b x y s w hw => rightLaw a b x y s w (withinThin hd (law hw))
  have loc : S.RightLocation pred := fun a b x y pre tail w hw => location a b x y pre tail w (law hw)
  have triangle : MakesTriangle S.g S.bound S.plan := by
    cases mode with
    | false => exact outsideTriangle S inc pos fixed
    | true =>
      cases k : plan [] with
      | zero => omega
      | succ n =>
        cases n with
        | zero => exact insideOneTriangle inc k fixed empty fixedRoot
        | succ n => exact insideManyTriangle S n k inc fixed pred loc
  have lift {x y} (hxy : EitherOrder S.g S.bound (fun p => some (plan p)) x y) :
      EitherOrder g bound (fun p => some (plan p)) x y :=
    eitherThin hb (eitherThin hc (eitherThin hd (eitherThin (g := draws) (h := id) weaken hxy)))
  obtain ⟨x,y,z,xy,xz,yz⟩ := triangle
  exact ⟨x,y,z,lift xy,lift xz,lift yz⟩

end Larson.PairGame

theorem OMA.solution : type_of% @Erdos118.erdos_118.variants.larson :=
  Larson.larsonOfArchitect Larson.PairGame.architectTriangle
