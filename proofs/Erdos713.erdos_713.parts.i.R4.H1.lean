import OMAReductions.R_Erdos713_erdos_713_parts_i_R4
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds

-- Credit: @grp06
-- The anchored repetition approach was identified in zarnab222-dev's work on
-- https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2828.
-- This proof constructs the anchor sets by successively collecting obstruction sets.
-- The extremal graph bounds used below are from reduction R4 by @mucoucah.

open Filter SimpleGraph Finset
open scoped Classical Topology Sym2 BigOperators

namespace Erdos713Anchor

open OMA.R_Erdos713_erdos_713_parts_i_R4
noncomputable section

private abbrev Pattern (q : ℕ) {W : Type} (A : Finset W) :=
  Finset (Fin q) × (Fin q → Option (↥A))

/-- An extension of a partial assignment, with its unanchored images avoiding B. -/
private def Fits {q : ℕ} {W : Type} (H : SimpleGraph (Fin q)) (X : SimpleGraph W)
    {A : Finset W} (p : Pattern q A) (B : Finset W) (g : Fin q → W) : Prop :=
  Set.InjOn g (↑p.1 : Set (Fin q)) ∧
  (∀ v ∈ p.1, ∀ w ∈ p.1, H.Adj v w → X.Adj (g v) (g w)) ∧
  ∀ v ∈ p.1, match p.2 v with
    | some a => g v = a.val
    | none => g v ∉ A ∧ g v ∉ B

private def Abundant {q : ℕ} {W : Type} (H : SimpleGraph (Fin q))
    (X : SimpleGraph W) {A : Finset W} (p : Pattern q A) : Prop :=
  ∀ B : Finset W, B.card ≤ q → ∃ g, Fits H X p B g

private def obstruction {q : ℕ} {W : Type} (H : SimpleGraph (Fin q))
    (X : SimpleGraph W) {A : Finset W} (p : Pattern q A) : Finset W :=
  if h : ∃ B : Finset W, B.card ≤ q ∧ ¬ ∃ g, Fits H X p B g then h.choose else ∅

private theorem obstruction_card {q : ℕ} {W : Type} (H : SimpleGraph (Fin q))
    (X : SimpleGraph W) {A : Finset W} (p : Pattern q A) :
    (obstruction H X p).card ≤ q := by
  unfold obstruction
  split
  · rename_i h
    exact h.choose_spec.1
  · simp

private def grow {q : ℕ} {W : Type} (H : SimpleGraph (Fin q))
    (X : SimpleGraph W) (A : Finset W) : Finset W :=
  A ∪ (univ : Finset (Pattern q A)).biUnion (obstruction H X)

private def shell {q : ℕ} {W : Type} (H : SimpleGraph (Fin q))
    (X : SimpleGraph W) (A : Finset W) : Finset W :=
  grow H X A \ A

private theorem subset_grow {q : ℕ} {W : Type} (H : SimpleGraph (Fin q))
    (X : SimpleGraph W) (A : Finset W) : A ⊆ grow H X A :=
  Finset.subset_union_left

private theorem abundant_of_clean {q : ℕ} {W : Type} (H : SimpleGraph (Fin q))
    (X : SimpleGraph W) {A : Finset W} (p : Pattern q A) {g : Fin q → W}
    (hg : Fits H X p (shell H X A) g) : Abundant H X p := by
  intro B hB
  by_contra h
  have hex : ∃ B : Finset W, B.card ≤ q ∧ ¬ ∃ g, Fits H X p B g := ⟨B, hB, h⟩
  apply hex.choose_spec.2
  refine ⟨g, hg.1, hg.2.1, ?_⟩
  intro v hv
  have hfit := hg.2.2 v hv
  cases hp : p.2 v with
  | some a => simpa only [hp] using hfit
  | none =>
    simp only [hp] at hfit ⊢
    refine ⟨hfit.1, ?_⟩
    intro hvB
    apply hfit.2
    unfold shell
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p, mem_univ _, ?_⟩), hfit.1⟩
    simpa only [obstruction, dif_pos hex] using hvB

private def budget (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => budget q i + (2 ^ q * (budget q i + 1) ^ q) * q

private def layers {q : ℕ} {W : Type} (H : SimpleGraph (Fin q))
    (X : SimpleGraph W) : ℕ → Finset W
  | 0 => ∅
  | i + 1 => grow H X (layers H X i)

private theorem layers_card {q : ℕ} {W : Type} (H : SimpleGraph (Fin q))
    (X : SimpleGraph W) (i : ℕ) : (layers H X i).card ≤ budget q i := by
  induction i with
  | zero => simp [layers, budget]
  | succ i ih =>
    let A := layers H X i
    have hA : A.card ≤ budget q i := ih
    have hOb :
        ((univ : Finset (Pattern q A)).biUnion (obstruction H X)).card
          ≤ (2 ^ q * (A.card + 1) ^ q) * q := by
      calc
        _ ≤ ∑ p : Pattern q A, (obstruction H X p).card := Finset.card_biUnion_le
        _ ≤ ∑ _p : Pattern q A, q :=
          Finset.sum_le_sum (fun p _ => obstruction_card H X p)
        _ = _ := by
          rw [Finset.sum_const_nat (m := q) (fun _ _ => rfl)]
          simp only [Finset.card_univ, Pattern, Fintype.card_prod, Fintype.card_finset,
            Fintype.card_fun, Fintype.card_option, Fintype.card_coe, Fintype.card_fin]
    change (grow H X A).card ≤ budget q i + (2 ^ q * (budget q i + 1) ^ q) * q
    calc
      _ ≤ A.card + ((univ : Finset (Pattern q A)).biUnion (obstruction H X)).card :=
        Finset.card_union_le _ _
      _ ≤ A.card + (2 ^ q * (A.card + 1) ^ q) * q := Nat.add_le_add_left hOb _
      _ ≤ _ := add_le_add hA (Nat.mul_le_mul_right q (Nat.mul_le_mul_left (2 ^ q)
        (Nat.pow_le_pow_left (Nat.add_le_add_right hA 1) q)))

private theorem choose_layer {q : ℕ} {W : Type} [Fintype W]
    (H : SimpleGraph (Fin q)) (X : SimpleGraph W) [DecidableRel X.Adj] {L : ℕ}
    (hL : 0 < L) :
    ∃ A : Finset W, A.card ≤ budget q L ∧
      L * (∑ w ∈ shell H X A, X.degree w) ≤ 2 * X.edgeFinset.card := by
  let A := layers H X
  let weight (S : Finset W) := ∑ w ∈ S, X.degree w
  let E := X.edgeFinset.card
  have hw (S : Finset W) : weight S ≤ 2 * E := by
    change (∑ w ∈ S, X.degree w) ≤ 2 * X.edgeFinset.card
    rw [← X.sum_degrees_eq_twice_card_edges]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  have hstep (i : ℕ) : weight (A (i+1) \ A i) + weight (A i) = weight (A (i+1)) :=
    Finset.sum_sdiff (subset_grow H X (A i))
  have hex : ∃ i < L, L * weight (A (i+1) \ A i) ≤ 2 * E := by
    by_contra! h
    have bound (i : ℕ) (hi : i ≤ L) :
        i * (2 * E + 1) ≤ L * weight (A i) := by
      induction i with
      | zero => simp
      | succ i ih =>
        have hlow := ih (by omega)
        have hbig := h i (by omega)
        have heq := congrArg (L * ·) (hstep i)
        rw [Nat.mul_add] at heq
        rw [Nat.succ_mul]
        omega
    have hb := bound L le_rfl
    have := Nat.le_of_mul_le_mul_left hb hL
    have := hw (A L)
    omega
  obtain ⟨i, hi, hsmall⟩ := hex
  have hmono : Monotone (budget q) :=
    monotone_nat_of_le_succ (fun j => Nat.le_add_right _ _)
  exact ⟨A i, (layers_card H X i).trans (hmono hi.le), hsmall⟩

/-- Remove edges incident to the shell and edges internal to the anchors. -/
private def prune {W : Type} (X : SimpleGraph W) (A S : Finset W) : SimpleGraph W :=
  ⟨fun x y => X.Adj x y ∧ x ∉ S ∧ y ∉ S ∧ ¬ (x ∈ A ∧ y ∈ A),
    ⟨fun _ _ h => ⟨h.1.symm, h.2.2.1, h.2.1, fun h' => h.2.2.2 ⟨h'.2, h'.1⟩⟩⟩,
    ⟨fun _ h => X.irrefl h.1⟩⟩

private theorem prune_bound {W : Type} [Fintype W] (X : SimpleGraph W)
    [DecidableRel X.Adj] (A S : Finset W) :
    X.edgeFinset.card ≤ (prune X A S).edgeFinset.card +
      (∑ w ∈ S, X.degree w) + A.card ^ 2 := by
  let Y : SimpleGraph W :=
    ⟨fun x y => X.Adj x y ∧ x ∉ (↑S : Set W) ∧ y ∉ (↑S : Set W),
      ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩, ⟨fun _ h => X.irrefl h.1⟩⟩
  let e : ↥A ↪ W := ⟨Subtype.val, Subtype.val_injective⟩
  let Z : SimpleGraph W := ((⊤ : SimpleGraph (↥A)).map e)
  have hYZ : Y ≤ prune X A S ⊔ Z := by
    intro x y hxy
    change X.Adj x y ∧ x ∉ (↑S : Set W) ∧ y ∉ (↑S : Set W) at hxy
    change (prune X A S).Adj x y ∨ Z.Adj x y
    by_cases hA : x ∈ A ∧ y ∈ A
    · right
      exact (map_adj e _ _ _).mpr
        ⟨⟨x, hA.1⟩, ⟨y, hA.2⟩,
          (top_adj _ _).mpr (fun he => hxy.1.ne (congrArg Subtype.val he)), rfl, rfl⟩
    · exact Or.inl ⟨hxy.1, hxy.2.1, hxy.2.2, hA⟩
  have hcard : Z.edgeFinset.card ≤ A.card ^ 2 := by
    have hmap : Z.edgeFinset.card = (⊤ : SimpleGraph (↥A)).edgeFinset.card :=
      card_edgeFinset_map e _
    rw [hmap, card_edgeFinset_top_eq_card_choose_two, Fintype.card_coe]
    exact Nat.choose_le_pow _ _
  have hY : Y.edgeFinset.card ≤ (prune X A S).edgeFinset.card + Z.edgeFinset.card := by
    calc
      _ ≤ (prune X A S ⊔ Z).edgeFinset.card := Finset.card_le_card (edgeFinset_mono hYZ)
      _ ≤ _ := by rw [edgeFinset_sup]; exact Finset.card_union_le _ _
  have hX : X.edgeFinset.card ≤ Y.edgeFinset.card + ∑ w ∈ S, X.degree w := by
    convert card_edges_eraseVertices_le_degree_sum X S
  omega

private abbrev Replica {W : Type} (A : Finset W) (k : ℕ) := (↥A) ⊕ (Fin k × W)

private def base {W : Type} {A : Finset W} {k : ℕ} : Replica A k → W
  | .inl a => a.val
  | .inr (_, w) => w

private def anchor {W : Type} {A : Finset W} {k : ℕ} : Replica A k → Option (↥A)
  | .inl a => some a
  | .inr _ => none

private def slot {W : Type} {A : Finset W} {k : ℕ} : Replica A k → Option (Fin k)
  | .inl _ => none
  | .inr (i, _) => some i

private def lift {W : Type} {A : Finset W} {k : ℕ} (i : Fin k) (w : W) : Replica A k :=
  if h : w ∈ A then .inl ⟨w, h⟩ else .inr (i, w)

private theorem base_lift {W : Type} {A : Finset W} {k : ℕ} (i : Fin k) (w : W) :
    base (lift (A := A) i w) = w := by
  by_cases h : w ∈ A <;> simp [lift, h, base]

private theorem slot_lift {W : Type} {A : Finset W} {k : ℕ} (i : Fin k) (w : W) :
    slot (lift (A := A) i w) = (if w ∈ A then none else some i) := by
  by_cases h : w ∈ A <;> simp [lift, h, slot]

private def repeatGraph {W : Type} (A : Finset W) (Y : SimpleGraph W) (k : ℕ) :
    SimpleGraph (Replica A k) :=
  ⟨fun x y => ∃ i : Fin k, Y.Adj (base x) (base y) ∧
      lift i (base x) = x ∧ lift i (base y) = y,
    ⟨fun _ _ ⟨i, hadj, hx, hy⟩ => ⟨i, hadj.symm, hy, hx⟩⟩,
    ⟨fun _ ⟨_, hadj, _, _⟩ => Y.irrefl hadj⟩⟩

private theorem repeatGraph_lift_adj {W : Type} {A : Finset W} {Y : SimpleGraph W}
    {k : ℕ} (i : Fin k) {x y : W} (h : Y.Adj x y) :
    (repeatGraph A Y k).Adj (lift i x) (lift i y) := by
  refine ⟨i, ?_⟩
  simpa only [base_lift, and_true] using h

private theorem repeatGraph_card {W : Type} [Fintype W] (A : Finset W)
    (Y : SimpleGraph W) (outside : ∀ {x y}, Y.Adj x y → ¬ (x ∈ A ∧ y ∈ A)) (k : ℕ) :
    k * Y.edgeFinset.card ≤ (repeatGraph A Y k).edgeFinset.card := by
  let emb (i : Fin k) (e : ↥Y.edgeFinset) : ↥(repeatGraph A Y k).edgeFinset :=
    ⟨Sym2.map (lift i) e.val, by
      obtain ⟨e, he⟩ := e
      induction e using Sym2.inductionOn with
      | _ x y =>
        rw [Sym2.map_mk, mem_edgeFinset, mem_edgeSet]
        exact repeatGraph_lift_adj i (by rwa [mem_edgeFinset, mem_edgeSet] at he)⟩
  let F (p : Fin k × ↥Y.edgeFinset) := emb p.1 p.2
  have hlift {i j : Fin k} {x y : W}
      (h : lift (A := A) i x = lift j y) : x = y ∧ (x ∉ A → i = j) := by
    have hxy : x = y := by simpa only [base_lift] using congrArg base h
    subst y
    exact ⟨rfl, fun hx => by simpa [slot_lift, hx] using congrArg slot h⟩
  have hinj : Function.Injective F := by
    rintro ⟨i, ⟨e, he⟩⟩ ⟨j, ⟨e', he'⟩⟩ hij
    induction e using Sym2.inductionOn with
    | _ x y =>
      induction e' using Sym2.inductionOn with
      | _ z w =>
        have hh : s(lift (A := A) i x, lift i y) = s(lift j z, lift j w) :=
          congrArg Subtype.val hij
        have hxy : Y.Adj x y := by rwa [mem_edgeFinset, mem_edgeSet] at he
        have hn : x ∉ A ∨ y ∉ A := not_and_or.mp (outside hxy)
        rcases Sym2.eq_iff.mp hh with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact Prod.ext (hn.elim (hlift hx).2 (hlift hy).2)
            (Subtype.ext (Sym2.eq_iff.mpr (Or.inl ⟨(hlift hx).1, (hlift hy).1⟩)))
        · exact Prod.ext (hn.elim (hlift hx).2 (hlift hy).2)
            (Subtype.ext (Sym2.eq_iff.mpr (Or.inr ⟨(hlift hx).1, (hlift hy).1⟩)))
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] using
    Fintype.card_le_of_injective F hinj

set_option maxHeartbeats 1000000 in
/-- A copy assembled from replicas could already be assembled in the original graph. -/
private theorem repeatGraph_free {q : ℕ} {W : Type} (H : SimpleGraph (Fin q))
    (X : SimpleGraph W) (active : ∀ v, ∃ w, H.Adj v w) (free : H.Free X)
    (A : Finset W) (k : ℕ) :
    H.Free (repeatGraph A (prune X A (shell H X A)) k) := by
  rintro ⟨f⟩
  let S := shell H X A
  let pos (v : Fin q) := slot (f v)
  let lab (v : Fin q) := anchor (f v)
  let proj (v : Fin q) := base (f v)
  have hEdge {v w} (h : H.Adj v w) :
      ∃ i : Fin k, (prune X A S).Adj (proj v) (proj w) ∧
        lift (A := A) i (proj v) = f v ∧ lift i (proj w) = f w :=
    f.toHom.map_adj h
  have root {v : Fin q} (hv : pos v = none) : ∃ a : ↥A, f v = Sum.inl a := by
    cases h : f v with
    | inl a => exact ⟨a, rfl⟩
    | inr p => simp [pos, h, slot] at hv
  have clean (v : Fin q) : ∃ i : Fin k, lift (A := A) i (proj v) = f v ∧ proj v ∉ S := by
    obtain ⟨w, hw⟩ := active v
    obtain ⟨i, hi, hv, _⟩ := hEdge hw
    exact ⟨i, hv, hi.2.1⟩
  have unroot {v : Fin q} {i : Fin k} (hv : pos v = some i) :
      lab v = none ∧ proj v ∉ A ∧ lift (A := A) i (proj v) = f v := by
    obtain ⟨j, hj, _⟩ := clean v
    have heq : (if proj v ∈ A then none else some j) = pos v := by
      simpa only [slot_lift] using congrArg slot hj
    rw [hv] at heq
    have hn : proj v ∉ A := by
      intro ha
      simp [ha] at heq
    have hji : j = i := by simpa [hn] using heq
    subst j
    have hl : lab v = none := by
      cases h : f v with
      | inl a => simp [pos, h, slot] at hv
      | inr p => simp [lab, h, anchor]
    exact ⟨hl, hn, hj⟩
  have edgeSlots {v w : Fin q} (h : H.Adj v w) :
      ∃ i : Fin k, (pos v = none ∨ pos v = some i) ∧
        (pos w = none ∨ pos w = some i) ∧ ¬ (pos v = none ∧ pos w = none) := by
    obtain ⟨i, hi, hv, hw⟩ := hEdge h
    have slotOf (u : Fin q) (hu : lift (A := A) i (proj u) = f u) :
        pos u = none ∨ pos u = some i := by
      have heq : (if proj u ∈ A then none else some i) = pos u := by
        simpa only [slot_lift] using congrArg slot hu
      by_cases ha : proj u ∈ A
      · exact Or.inl (by simpa [ha] using heq.symm)
      · exact Or.inr (by simpa [ha] using heq.symm)
    refine ⟨i, slotOf v hv, slotOf w hw, ?_⟩
    rintro ⟨hv', hw'⟩
    obtain ⟨a, ha⟩ := root hv'
    obtain ⟨b, hb⟩ := root hw'
    exact hi.2.2.2 ⟨by simpa [proj, ha, base] using a.property,
      by simpa [proj, hb, base] using b.property⟩
  have neighborSlot {v w : Fin q} {i : Fin k} (hv : pos v = some i) (h : H.Adj v w) :
      pos w = none ∨ pos w = some i := by
    obtain ⟨j, hj, hw, _⟩ := edgeSlots h
    rw [hv] at hj
    have hij : i = j := by simpa using hj
    simpa [hij] using hw
  let D (I : Finset (Fin k)) : Finset (Fin q) :=
    univ.filter (fun v => pos v = none ∨ ∃ i ∈ I, pos v = some i)
  have memD (I : Finset (Fin k)) (v : Fin q) :
      v ∈ D I ↔ pos v = none ∨ ∃ i ∈ I, pos v = some i := by simp [D]
  have memOne (i : Fin k) (v : Fin q) :
      v ∈ D {i} ↔ pos v = none ∨ pos v = some i := by simp [memD]
  have abundant (i : Fin k) : Abundant H X (A := A) (D {i}, lab) := by
    apply abundant_of_clean H X (g := proj)
    have lifted {v : Fin q} (hv : v ∈ D {i}) : lift (A := A) i (proj v) = f v := by
      rcases (memOne i v).mp hv with hv | hv
      · obtain ⟨a, ha⟩ := root hv
        simp [proj, ha, base, lift, a.property]
      · exact (unroot hv).2.2
    refine ⟨?_, ?_, ?_⟩
    · intro v hv w hw he
      apply f.injective
      change f v = f w
      rw [← lifted hv, ← lifted hw, he]
    · intro v _ w _ h
      obtain ⟨j, hj, _, _⟩ := hEdge h
      exact hj.1
    · intro v hv
      change match lab v with
        | some a => proj v = a.val
        | none => proj v ∉ A ∧ proj v ∉ S
      rcases (memOne i v).mp hv with hv | hv
      · obtain ⟨a, ha⟩ := root hv
        simp [lab, proj, ha, anchor, base]
      · rw [(unroot hv).1]
        exact ⟨(unroot hv).2.1, (clean v).choose_spec.2⟩
  have assemble (I : Finset (Fin k)) : ∃ g : Fin q → W,
      Set.InjOn g (↑(D I) : Set (Fin q)) ∧
      (∀ v ∈ D I, ∀ w ∈ D I, H.Adj v w → X.Adj (g v) (g w)) ∧
      (∀ v, pos v = none → g v = proj v) := by
    induction I using Finset.induction_on with
    | empty =>
      refine ⟨proj, ?_, ?_, fun _ _ => rfl⟩
      · intro v hv w hw he
        obtain ⟨a, ha⟩ := root (by simpa [memD] using hv)
        obtain ⟨b, hb⟩ := root (by simpa [memD] using hw)
        have hab : a = b := Subtype.ext (by simpa [proj, ha, hb, base] using he)
        apply f.injective
        change f v = f w
        rw [ha, hb, hab]
      · intro v hv w hw h
        obtain ⟨i, _, _, hn⟩ := edgeSlots h
        exact (hn ⟨by simpa [memD] using hv, by simpa [memD] using hw⟩).elim
    | @insert i I hi ih =>
      obtain ⟨g, hginj, hgadj, hgroot⟩ := ih
      let B := (D I).image g
      have hD : (D I).card ≤ q := by
        simpa only [Fintype.card_fin] using (D I).card_le_univ
      have hB : B.card ≤ q := Finset.card_image_le.trans hD
      obtain ⟨h, hhinj, hhadj, hhpos⟩ := abundant i B hB
      let m (v : Fin q) := if pos v = some i then h v else g v
      have oldMem {v : Fin q} (hv : v ∈ D (insert i I)) (hn : pos v ≠ some i) :
          v ∈ D I := by
        apply (memD _ _).mpr
        rcases (memD _ _).mp hv with hvroot | ⟨j, hj, hvslot⟩
        · exact Or.inl hvroot
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact (hn hvslot).elim
        · exact Or.inr ⟨j, hj, hvslot⟩
      have newMem {v : Fin q} (hv : pos v = some i) : v ∈ D {i} :=
        (memOne i v).mpr (Or.inr hv)
      have avoid {v : Fin q} (hv : pos v = some i) : h v ∉ B := by
        have hh := hhpos v (newMem hv)
        change (match lab v with | some a => h v = a.val | none => h v ∉ A ∧ h v ∉ B) at hh
        rw [(unroot hv).1] at hh
        exact hh.2
      have localAgree {v : Fin q} (hv : v ∈ D {i}) : m v = h v := by
        rcases (memOne i v).mp hv with hn | hs
        · obtain ⟨a, ha⟩ := root hn
          have hh := hhpos v hv
          change (match lab v with | some a => h v = a.val | none => h v ∉ A ∧ h v ∉ B) at hh
          rw [show lab v = some a by simp [lab, ha, anchor]] at hh
          simpa [m, hn, hgroot v hn, proj, ha, base] using hh.symm
        · simp [m, hs]
      have newAdj {v w : Fin q} (hv : pos v = some i) (hadj : H.Adj v w) :
          X.Adj (m v) (m w) := by
        have hv' := newMem hv
        have hw' := (memOne i w).mpr (neighborSlot hv hadj)
        rw [localAgree hv', localAgree hw']
        exact hhadj v hv' w hw' hadj
      refine ⟨m, ?_, ?_, ?_⟩
      · intro v hv w hw he
        change v ∈ D (insert i I) at hv
        change w ∈ D (insert i I) at hw
        by_cases hv' : pos v = some i <;> by_cases hw' : pos w = some i
        · exact hhinj (newMem hv') (newMem hw') (by simpa [m, hv', hw'] using he)
        · have he' : h v = g w := by simpa [m, hv', hw'] using he
          exact (avoid hv' (Finset.mem_image.mpr ⟨w, oldMem hw hw', he'.symm⟩)).elim
        · have he' : g v = h w := by simpa [m, hv', hw'] using he
          exact (avoid hw' (Finset.mem_image.mpr ⟨v, oldMem hv hv', he'⟩)).elim
        · exact hginj (oldMem hv hv') (oldMem hw hw') (by simpa [m, hv', hw'] using he)
      · intro v hv w hw hadj
        by_cases hv' : pos v = some i
        · exact newAdj hv' hadj
        by_cases hw' : pos w = some i
        · exact (newAdj hw' hadj.symm).symm
        simpa [m, hv', hw'] using hgadj v (oldMem hv hv') w (oldMem hw hw') hadj
      · intro v hv
        simpa [m, hv] using hgroot v hv
  obtain ⟨g, hinj, hadj, _⟩ := assemble univ
  have allMem (v : Fin q) : v ∈ D univ := by
    apply (memD _ _).mpr
    cases h : pos v with
    | none => exact Or.inl (by simp [h])
    | some i => exact Or.inr ⟨i, mem_univ _, by simp [h]⟩
  exact free ⟨⟨⟨g, fun {v w} h => hadj v (allMem v) w (allMem w) h⟩,
    fun v w e => hinj (allMem v) (allMem w) e⟩⟩

private def density {q : ℕ} (H : SimpleGraph (Fin q)) (n : ℕ) : ℝ :=
  (extremalNumber n H : ℝ) / n

set_option maxHeartbeats 1000000 in
/-- Recurring densities above b imply a permanent lower bound at every smaller positive slope. -/
private theorem sustained {q : ℕ} (H : SimpleGraph (Fin q))
    (hH : H ≠ ⊥) (active : ∀ v, ∃ w, H.Adj v w)
    (cap : ∀ n, extremalNumber n H ≤ q * n) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (freq : ∃ᶠ n in atTop, b < density H n) :
    ∀ᶠ n in atTop, a ≤ density H n := by
  let ε : ℝ := (b - a) / 4
  let t : ℝ := (a + b) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hat : a < t := by dsimp [t]; linarith
  have ht : 0 ≤ t := ha.trans hat.le
  obtain ⟨L, hL⟩ := exists_nat_gt (2 * (q : ℝ) / ε)
  have hLr : 0 < (L : ℝ) := lt_of_le_of_lt (by positivity) hL
  have hcoef : 2 * (q : ℝ) ≤ (L : ℝ) * ε := ((div_lt_iff₀ hε).mp hL).le
  let K := budget q L
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((K : ℝ)^2 / ε)
  obtain ⟨n, hn, hd⟩ := frequently_atTop.mp freq (max 1 N₀)
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left 1 N₀).trans hn)
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hK : (K : ℝ)^2 ≤ ε * (n : ℝ) := by
    have hn₀ : (N₀ : ℝ) ≤ n := Nat.cast_le.mpr ((le_max_right 1 N₀).trans hn)
    have h : (K : ℝ)^2 < (N₀ : ℝ) * ε := (div_lt_iff₀ hε).mp hN₀
    calc
      _ ≤ (N₀ : ℝ) * ε := h.le
      _ ≤ (n : ℝ) * ε := mul_le_mul_of_nonneg_right hn₀ hε.le
      _ = _ := mul_comm _ _
  obtain ⟨X, hXd, hX⟩ := exists_isExtremal_free (V := Fin n) hH
  letI := hXd
  have hcard : X.edgeFinset.card = extremalNumber n H := by
    simpa only [Fintype.card_fin] using card_edgeFinset_of_isExtremal_free hX
  have high : b * (n : ℝ) < X.edgeFinset.card := by
    rw [hcard]
    exact (lt_div_iff₀ hnR).mp hd
  have upper : (X.edgeFinset.card : ℝ) ≤ (q : ℝ) * (n : ℝ) := by
    exact_mod_cast (hcard.le.trans (cap n))
  obtain ⟨A, hA, hloss⟩ := choose_layer H X (Nat.cast_pos.mp hLr)
  let S := shell H X A
  let Y := prune X A S
  change L * (∑ w ∈ S, X.degree w) ≤ 2 * X.edgeFinset.card at hloss
  have shellLoss : (∑ w ∈ S, (X.degree w : ℝ)) ≤ ε * (n : ℝ) := by
    have h : (L : ℝ) * (∑ w ∈ S, (X.degree w : ℝ)) ≤ 2 * (X.edgeFinset.card : ℝ) := by
      exact_mod_cast hloss
    apply le_of_mul_le_mul_left _ hLr
    calc
      _ ≤ 2 * (X.edgeFinset.card : ℝ) := h
      _ ≤ 2 * ((q : ℝ) * (n : ℝ)) := mul_le_mul_of_nonneg_left upper (by norm_num)
      _ = (2 * (q : ℝ)) * (n : ℝ) := by ring
      _ ≤ ((L : ℝ) * ε) * (n : ℝ) := mul_le_mul_of_nonneg_right hcoef hnR.le
      _ = _ := by ring
  have anchorLoss : (A.card : ℝ)^2 ≤ ε * (n : ℝ) := by
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr hA) 2).trans hK
  have hY : t * (n : ℝ) ≤ Y.edgeFinset.card := by
    have hl : (X.edgeFinset.card : ℝ) ≤ (Y.edgeFinset.card : ℝ) +
        (∑ w ∈ S, (X.degree w : ℝ)) + (A.card : ℝ)^2 := by
      exact_mod_cast prune_bound X A S
    have heq : b * (n : ℝ) = t * (n : ℝ) + ε * (n : ℝ) + ε * (n : ℝ) := by
      dsimp [t, ε]
      ring
    linarith
  have repeat_bound (k N : ℕ) (hN : A.card + k * n ≤ N) :
      k * Y.edgeFinset.card ≤ extremalNumber N H := by
    have hCard : Fintype.card (Replica A k) ≤ N := by
      simpa only [Replica, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
        using hN
    have hFree : H.Free (repeatGraph A Y k) := by
      simpa only [Y, S] using repeatGraph_free H X active hX.prop A k
    exact (repeatGraph_card A Y (fun h => h.2.2.2) k).trans
      (card_edgeFinset_le_extremal_of_card_le (X := repeatGraph A Y k) active hFree hCard)
  obtain ⟨M, hM⟩ := exists_nat_gt (t * ((A.card : ℝ) + n) / (t - a))
  filter_upwards [eventually_ge_atTop (max (max A.card 1) M)] with N hN
  have hNA : A.card ≤ N := (le_max_left A.card 1).trans ((le_max_left _ M).trans hN)
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr
    (Nat.zero_lt_one.trans_le ((le_max_right A.card 1).trans ((le_max_left _ M).trans hN)))
  have hMN : (M : ℝ) ≤ N := Nat.cast_le.mpr ((le_max_right _ M).trans hN)
  have hta : 0 < t - a := sub_pos.mpr hat
  have herr : t * ((A.card : ℝ) + n) ≤ (N : ℝ) * (t - a) :=
    ((div_lt_iff₀ hta).mp hM).le.trans (mul_le_mul_of_nonneg_right hMN hta.le)
  let k := (N - A.card) / n
  have hdiv : (N - A.card) % n + n * k = N - A.card := Nat.mod_add_div _ _
  have hrem : (N - A.card) % n < n := Nat.mod_lt _ hn0
  have hfit : A.card + k * n ≤ N := by rw [Nat.mul_comm k n]; omega
  have hclose : (N : ℝ) ≤ (A.card : ℝ) + (k : ℝ) * (n : ℝ) + (n : ℝ) := by
    have hclose' : N ≤ A.card + k * n + n := by rw [Nat.mul_comm k n]; omega
    exact_mod_cast hclose'
  have hx : (k : ℝ) * (Y.edgeFinset.card : ℝ) ≤ extremalNumber N H := by
    exact_mod_cast repeat_bound k N hfit
  have hty : (k : ℝ) * (t * (n : ℝ)) ≤ (k : ℝ) * (Y.edgeFinset.card : ℝ) :=
    mul_le_mul_of_nonneg_left hY (Nat.cast_nonneg _)
  have htn := mul_le_mul_of_nonneg_left hclose ht
  apply (le_div_iff₀ hN0).mpr
  nlinarith only [herr, hx, hty, htn]

theorem positive_limit {q : ℕ} (H : SimpleGraph (Fin q))
    (active : ∀ v, ∃ w, H.Adj v w) (edges : 2 ≤ H.edgeFinset.card)
    (cap : ∀ n, extremalNumber n H ≤ q * n) :
    ∃ c : ℝ, 0 < c ∧ Tendsto (density H) atTop (𝓝 c) := by
  have hH : H ≠ ⊥ := by
    intro he
    rw [edgeFinset_eq_empty.mpr he] at edges
    simp at edges
  let u := density H
  have hup : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) u := by
    apply Filter.isBoundedUnder_of
    refine ⟨(q : ℝ), ?_⟩
    intro n
    by_cases hn : n = 0
    · simp [u, density, hn]
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    apply (div_le_iff₀ hn').mpr
    exact_mod_cast cap n
  have hlower : ∀ᶠ n in atTop, (1 / 3 : ℝ) ≤ u n := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hn' : 0 < n := by omega
    have hm : n / 2 ≤ extremalNumber n H := extremal_linear_lower H edges hn'
    have hb : n ≤ 3 * extremalNumber n H := by omega
    have hb' : (n : ℝ) ≤ 3 * (extremalNumber n H : ℝ) := by exact_mod_cast hb
    apply (le_div_iff₀ (Nat.cast_pos.mpr hn' : (0 : ℝ) < n)).mpr
    linarith
  have hlo : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) u :=
    Filter.isBoundedUnder_of_eventually_ge hlower
  have hpos : (1 / 3 : ℝ) ≤ liminf u atTop :=
    le_liminf_of_le hup.isCoboundedUnder_ge hlower
  have hlim : limsup u atTop ≤ liminf u atTop := by
    by_contra! h
    obtain ⟨a, hia, has⟩ := exists_between h
    obtain ⟨b, hab, hbs⟩ := exists_between has
    have hfreq : ∃ᶠ n in atTop, b < density H n :=
      frequently_lt_of_lt_limsup hlo.isCoboundedUnder_le hbs
    have ha : (0 : ℝ) ≤ a := (by norm_num : (0 : ℝ) ≤ 1 / 3).trans (hpos.trans hia.le)
    have hstay := sustained H hH active cap ha hab hfreq
    exact hia.not_ge (le_liminf_of_le hup.isCoboundedUnder_ge hstay)
  refine ⟨liminf u atTop, lt_of_lt_of_le (by norm_num) hpos, ?_⟩
  exact tendsto_of_le_liminf_of_limsup_le le_rfl hlim hup hlo

end
end Erdos713Anchor

theorem OMA.solution : OMA.R_Erdos713_erdos_713_parts_i_R4.H1 := by
  intro q H _ active edges cap
  exact Erdos713Anchor.positive_limit H active edges cap
