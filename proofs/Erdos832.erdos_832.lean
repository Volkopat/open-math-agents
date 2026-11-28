import FormalConjectures.ErdosProblems.«832»
import Mathlib.Algebra.Ring.BooleanRing

/-!
# The counterexample to Erdős Problem 832

Copyright (c) 2026. All rights reserved.
Released under Apache 2.0. Authors of the source formalization: Aristotle,
OpenAI Codex and GPT-5.6 Sol. Adapted from plby/lean-proofs, file
src/latest/ErdosProblems/Erdos832.lean, revision 8822f7ddef30fadbd92e1c6ab4ed897af356af5e.
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos832.lean

Noga Alon disproved the proposed hypergraph bound. This formalization uses
a Giraud-type construction on two copies of a binary vector space. The
coordinate construction and edge counts below are adapted from the cited
source. We relabel the vertices and use the minimum number of colors of
the construction itself to obtain the formulation in formal-conjectures.
-/

namespace Erdos832.BinaryConstruction

open Finset
open scoped BigOperators

abbrev Code (d : ℕ) := Fin d → Bool

def dot {d : ℕ} (x y : Code d) : Bool := ∑ i, x i * y i

def toggle {d : ℕ} (i : Fin d) (y : Code d) : Code d :=
  fun j => if j = i then !y j else y j

lemma toggle_toggle {d : ℕ} (i : Fin d) (y : Code d) :
    toggle i (toggle i y) = y := by
  funext j
  by_cases h : j = i <;> simp [toggle, h]

lemma dot_toggle {d : ℕ} (x y : Code d) (i : Fin d) :
    dot x (toggle i y) = dot x y + x i := by
  have hb (b : Bool) : (!b : Bool) = b + true := by cases b <;> decide
  calc
    dot x (toggle i y) = ∑ j, (x j * y j + if j = i then x i else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hji : j = i
      · subst j
        simp only [toggle, if_pos, hb]
        rw [mul_add]
        change x i * y i + x i * 1 = x i * y i + x i
        ring
      · simp [toggle, hji]
    _ = (∑ j, x j * y j) + ∑ j, (if j = i then x i else false) :=
      Finset.sum_add_distrib
    _ = dot x y + x i := by
      have hz : (false : Bool) = 0 := by decide
      simp only [hz]
      have hs : (∑ j : Fin d, if j = i then x i else 0) = x i := by
        simp
      rw [hs]
      change dot x y + x i = dot x y + x i
      rfl

def pairs (d : ℕ) : Finset (Finset (Code d)) :=
  (Finset.univ : Finset (Code d)).powersetCard 2

def pairLabel {d : ℕ} (p : Finset (Code d)) (y : Code d) : Bool :=
  ∑ x ∈ p, dot x y

lemma pairLabel_toggle {d : ℕ} {p : Finset (Code d)} (hp : p ∈ pairs d) :
    ∃ i : Fin d, ∀ y, pairLabel p (toggle i y) = !pairLabel p y := by
  have hpcard : p.card = 2 := (Finset.mem_powersetCard.mp hp).2
  obtain ⟨x, x', hxx', rfl⟩ := Finset.card_eq_two.mp hpcard
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ x' i := by
    simpa [Function.ne_iff] using hxx'
  refine ⟨i, fun y ↦ ?_⟩
  simp only [pairLabel, Finset.sum_pair hxx', dot_toggle]
  have diff_add_true (a b : Bool) (h : a ≠ b) : a + b = true := by
    cases a <;> cases b
    · exact (h rfl).elim
    · decide
    · decide
    · exact (h rfl).elim
  have hbits : x i + x' i = true := diff_add_true _ _ hi
  have hnot (b : Bool) : (!b : Bool) = b + true := by cases b <;> decide
  rw [hnot, ← hbits]
  ring

def fiber {d : ℕ} (p : Finset (Code d)) (b : Bool) : Finset (Code d) :=
  Finset.univ.filter fun y ↦ pairLabel p y = b

lemma fiber_toggle_mem {d : ℕ} {p : Finset (Code d)} (_hp : p ∈ pairs d)
    {i : Fin d} (hi : ∀ y, pairLabel p (toggle i y) = !pairLabel p y)
    {b : Bool} {y : Code d} : y ∈ fiber p b → toggle i y ∈ fiber p (!b) := by
  intro hy
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  rw [hi, hy]

lemma fiber_card_eq {d : ℕ} {p : Finset (Code d)} (hp : p ∈ pairs d) :
    (fiber p false).card = (fiber p true).card := by
  obtain ⟨i, hi⟩ := pairLabel_toggle hp
  apply Finset.card_bij (fun y _ ↦ toggle i y)
  · intro y hy
    simpa using fiber_toggle_mem hp hi hy
  · intro a ha b hb hab
    have := congrArg (toggle i) hab
    simpa only [toggle_toggle] using this
  · intro y hy
    refine ⟨toggle i y, ?_, ?_⟩
    · have hmem : toggle i y ∈ fiber p (!true) := fiber_toggle_mem hp hi hy
      simpa using hmem
    · exact toggle_toggle i y

lemma bool_add_eq_false_iff (a b : Bool) : a + b = false ↔ a = b := by
  cases a <;> cases b <;> decide

def evenColumns {d : ℕ} (p : Finset (Code d)) : Finset (Finset (Code d)) :=
  (pairs d).filter fun cp ↦ (∑ y ∈ cp, pairLabel p y) = false

lemma evenColumns_eq {d : ℕ} {p : Finset (Code d)} :
    evenColumns p =
      (fiber p false).powersetCard 2 ∪ (fiber p true).powersetCard 2 := by
  ext cp
  simp only [evenColumns, Finset.mem_filter, pairs, Finset.mem_powersetCard,
    Finset.mem_union]
  constructor
  · rintro ⟨⟨hsub, hcard⟩, hsum⟩
    obtain ⟨y, z, hyz, rfl⟩ := Finset.card_eq_two.mp hcard
    simp only [Finset.sum_pair hyz] at hsum
    have heq : pairLabel p y = pairLabel p z :=
      (bool_add_eq_false_iff _ _).mp hsum
    cases hb : pairLabel p y
    · left
      refine ⟨?_, Finset.card_pair hyz⟩
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · simp [fiber, hb]
      · simp [fiber, ← heq, hb]
    · right
      refine ⟨?_, Finset.card_pair hyz⟩
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · simp [fiber, hb]
      · simp [fiber, ← heq, hb]
  · rintro (hfalse | htrue)
    · obtain ⟨hsub, hcard⟩ := hfalse
      refine ⟨⟨hsub.trans (Finset.filter_subset _ _), hcard⟩, ?_⟩
      obtain ⟨y, z, hyz, rfl⟩ := Finset.card_eq_two.mp hcard
      have hy : pairLabel p y = false := (Finset.mem_filter.mp (hsub (by simp))).2
      have hz : pairLabel p z = false := (Finset.mem_filter.mp (hsub (by simp))).2
      rw [Finset.sum_pair hyz, hy, hz]
      decide
    · obtain ⟨hsub, hcard⟩ := htrue
      refine ⟨⟨hsub.trans (Finset.filter_subset _ _), hcard⟩, ?_⟩
      obtain ⟨y, z, hyz, rfl⟩ := Finset.card_eq_two.mp hcard
      have hy : pairLabel p y = true := (Finset.mem_filter.mp (hsub (by simp))).2
      have hz : pairLabel p z = true := (Finset.mem_filter.mp (hsub (by simp))).2
      rw [Finset.sum_pair hyz, hy, hz]
      decide

lemma two_mul_choose_two (a : ℕ) : 2 * a.choose 2 = a * (a - 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose a 2
  norm_num [Nat.descFactorial, Nat.factorial] at h
  calc
    2 * a.choose 2 = (a - 1) * a := h.symm
    _ = a * (a - 1) := Nat.mul_comm _ _

lemma card_evenColumns_bound {d : ℕ} {p : Finset (Code d)} (hp : p ∈ pairs d) :
    4 * (evenColumns p).card ≤ (Fintype.card (Code d)) ^ 2 := by
  rw [evenColumns_eq]
  calc
    4 * ((fiber p false).powersetCard 2 ∪
        (fiber p true).powersetCard 2).card
        ≤ 4 * ((fiber p false).powersetCard 2).card +
          4 * ((fiber p true).powersetCard 2).card := by
            have h := Finset.card_union_le ((fiber p false).powersetCard 2)
              ((fiber p true).powersetCard 2)
            omega
    _ = 8 * (fiber p false).card.choose 2 := by
      simp only [Finset.card_powersetCard, fiber_card_eq hp]
      omega
    _ ≤ (Fintype.card (Code d)) ^ 2 := by
      have hpartition := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Code d)))
        (fun y : Code d ↦ pairLabel p y = false)
      have htrue : (Finset.univ.filter fun y : Code d ↦ ¬pairLabel p y = false) =
          fiber p true := by
        ext y
        simp [fiber]
      have hsum : (fiber p false).card + (fiber p true).card =
          Fintype.card (Code d) := by
        simpa [fiber, htrue] using hpartition
      have hbal := fiber_card_eq hp
      rw [← hsum, ← hbal]
      let t := (fiber p false).card
      have hchoose := two_mul_choose_two t
      have hle := Nat.mul_le_mul_left t (Nat.sub_le t 1)
      change 8 * t.choose 2 ≤ (t + t) ^ 2
      nlinarith only [hchoose, hle]

def evenRectParams (d : ℕ) : Finset (Sigma fun _ : Finset (Code d) ↦ Finset (Code d)) :=
  (pairs d).sigma fun p ↦ evenColumns p

lemma card_pairs (d : ℕ) :
    (pairs d).card = (Fintype.card (Code d)).choose 2 := by
  simp [pairs]

lemma twentyFour_mul_choose_four (a : ℕ) :
    24 * a.choose 4 = a * (a - 1) * (a - 2) * (a - 3) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose a 4
  norm_num [Nat.descFactorial, Nat.factorial] at h
  calc
    24 * a.choose 4 = (a - 3) * ((a - 2) * ((a - 1) * a)) := h.symm
    _ = a * (a - 1) * (a - 2) * (a - 3) := by ac_rfl

lemma choose_four_bound (a : ℕ) : 24 * a.choose 4 ≤ a ^ 4 := by
  rw [twentyFour_mul_choose_four]
  have h1 : a - 1 ≤ a := Nat.sub_le _ _
  have h2 : a - 2 ≤ a := Nat.sub_le _ _
  have h3 : a - 3 ≤ a := Nat.sub_le _ _
  calc
    a * (a - 1) * (a - 2) * (a - 3) ≤ a * a * a * a := by
      gcongr
    _ = a ^ 4 := by ring

lemma card_evenRectParams_bound (d : ℕ) :
    8 * (evenRectParams d).card ≤ (Fintype.card (Code d)) ^ 4 := by
  let q := Fintype.card (Code d)
  have hsum : 4 * (evenRectParams d).card ≤ (pairs d).card * q ^ 2 := by
    rw [evenRectParams, Finset.card_sigma]
    calc
      4 * ∑ p ∈ pairs d, (evenColumns p).card =
          ∑ p ∈ pairs d, 4 * (evenColumns p).card := by
            simp [Finset.mul_sum]
      _ ≤ ∑ _p ∈ pairs d, q ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        exact card_evenColumns_bound hp
      _ = (pairs d).card * q ^ 2 := by simp
  have hpairs : 2 * (pairs d).card ≤ q ^ 2 := by
    rw [card_pairs, two_mul_choose_two]
    exact calc
      q * (q - 1) ≤ q * q := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = q ^ 2 := by ring
  calc
    8 * (evenRectParams d).card = 2 * (4 * (evenRectParams d).card) := by ring
    _ ≤ 2 * ((pairs d).card * q ^ 2) := Nat.mul_le_mul_left _ hsum
    _ = (2 * (pairs d).card) * q ^ 2 := by ring
    _ ≤ q ^ 2 * q ^ 2 := Nat.mul_le_mul_right _ hpairs
    _ = q ^ 4 := by ring

abbrev Vertex (d : ℕ) := Bool × Code d

def fours (d : ℕ) : Finset (Finset (Code d)) :=
  (Finset.univ : Finset (Code d)).powersetCard 4

def sideSet {d : ℕ} (b : Bool) (s : Finset (Code d)) : Finset (Vertex d) :=
  s.image fun x ↦ (b, x)

lemma sideSet_card {d : ℕ} (b : Bool) (s : Finset (Code d)) :
    (sideSet b s).card = s.card := by
  exact Finset.card_image_of_injective s fun _ _ h ↦ congrArg Prod.snd h

lemma sideSet_disjoint {d : ℕ} (s t : Finset (Code d)) :
    Disjoint (sideSet false s) (sideSet true t) := by
  rw [Finset.disjoint_left]
  intro v hvf hvt
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hvf
  obtain ⟨y, hy, hEq⟩ := Finset.mem_image.mp hvt
  exact Bool.false_ne_true (congrArg Prod.fst hEq.symm)

def rectSet {d : ℕ}
    (z : Sigma fun _ : Finset (Code d) ↦ Finset (Code d)) : Finset (Vertex d) :=
  sideSet false z.1 ∪ sideSet true z.2

lemma rectSet_card {d : ℕ}
    {z : Sigma fun _ : Finset (Code d) ↦ Finset (Code d)}
    (hz : z ∈ evenRectParams d) : (rectSet z).card = 4 := by
  have hz' := Finset.mem_sigma.mp hz
  have hp : z.1.card = 2 := (Finset.mem_powersetCard.mp hz'.1).2
  have hcpairs : z.2 ∈ pairs d := (Finset.mem_filter.mp hz'.2).1
  have hq : z.2.card = 2 := (Finset.mem_powersetCard.mp hcpairs).2
  rw [rectSet, Finset.card_union_of_disjoint (sideSet_disjoint _ _),
    sideSet_card, sideSet_card, hp, hq]

def constructionEdges (d : ℕ) : Finset (Finset (Vertex d)) :=
  ((fours d).image (sideSet false) ∪ (fours d).image (sideSet true)) ∪
    (evenRectParams d).image rectSet

lemma construction_uniform (d : ℕ) :
    ∀ e ∈ constructionEdges d, e.card = 4 := by
  intro e he
  simp only [constructionEdges, Finset.mem_union, Finset.mem_image] at he
  rcases he with ((⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨z, hz, rfl⟩)
  · rw [sideSet_card]
    exact (Finset.mem_powersetCard.mp hs).2
  · rw [sideSet_card]
    exact (Finset.mem_powersetCard.mp hs).2
  · exact rectSet_card hz

lemma card_fours (d : ℕ) :
    (fours d).card = (Fintype.card (Code d)).choose 4 := by
  simp [fours]

lemma construction_card_aux (d : ℕ) :
    (constructionEdges d).card ≤ 2 * (fours d).card + (evenRectParams d).card := by
  unfold constructionEdges
  calc
    (((fours d).image (sideSet false) ∪ (fours d).image (sideSet true)) ∪
      (evenRectParams d).image rectSet).card ≤
        ((fours d).image (sideSet false) ∪ (fours d).image (sideSet true)).card +
          ((evenRectParams d).image rectSet).card := Finset.card_union_le _ _
    _ ≤ ((fours d).image (sideSet false)).card +
          ((fours d).image (sideSet true)).card +
          ((evenRectParams d).image rectSet).card := by
      have h := Finset.card_union_le ((fours d).image (sideSet false))
        ((fours d).image (sideSet true))
      omega
    _ ≤ 2 * (fours d).card + (evenRectParams d).card := by
      have hrow := Finset.card_image_le (s := fours d) (f := sideSet false)
      have hcol := Finset.card_image_le (s := fours d) (f := sideSet true)
      have hrect := Finset.card_image_le (s := evenRectParams d) (f := rectSet)
      omega

lemma construction_card_bound (d : ℕ) :
    24 * (constructionEdges d).card ≤ 5 * (Fintype.card (Code d)) ^ 4 := by
  let q := Fintype.card (Code d)
  have hedge := construction_card_aux d
  have hfour : 24 * (fours d).card ≤ q ^ 4 := by
    rw [card_fours]
    exact choose_four_bound q
  have hrect := card_evenRectParams_bound d
  have hmul : 24 * (constructionEdges d).card ≤
      48 * (fours d).card + 24 * (evenRectParams d).card := by omega
  calc
    24 * (constructionEdges d).card ≤
        48 * (fours d).card + 24 * (evenRectParams d).card := hmul
    _ = 2 * (24 * (fours d).card) + 3 * (8 * (evenRectParams d).card) := by ring
    _ ≤ 2 * q ^ 4 + 3 * q ^ 4 := by gcongr
    _ = 5 * q ^ 4 := by ring

/- Every five vertices contain an edge. -/

lemma three_points_same_bool {α : Type} [Fintype α]
    (hcard : Fintype.card α = 3) (f : α → Bool) :
    ∃ x y : α, x ≠ y ∧ f x = f y := by
  by_contra h
  have hinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    exact h ⟨x, y, hne, hxy⟩
  have hle := Fintype.card_le_of_injective f hinj
  rw [hcard, Fintype.card_bool] at hle
  omega

lemma pair_in_three_same_bool {α : Type}
    {s : Finset α} (hcard : s.card = 3) (f : α → Bool) :
    ∃ p ∈ s.powersetCard 2, (∑ x ∈ p, f x) = false := by
  classical
  let g : ↥s → Bool := fun x ↦ f x
  have hsubcard : Fintype.card ↥s = 3 := by simpa using hcard
  obtain ⟨x, y, hxy, heq⟩ := three_points_same_bool hsubcard g
  refine ⟨{x.1, y.1}, ?_, ?_⟩
  · apply Finset.mem_powersetCard.mpr
    refine ⟨?_, Finset.card_pair (fun h ↦ hxy (Subtype.ext h))⟩
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact x.2
    · exact y.2
  · rw [Finset.sum_pair (fun h ↦ hxy (Subtype.ext h))]
    have heq' : f x.1 = f y.1 := heq
    rw [bool_add_eq_false_iff]
    exact heq'

def codesOn {d : ℕ} (b : Bool) (S : Finset (Vertex d)) : Finset (Code d) :=
  (S.filter fun v ↦ v.1 = b).image Prod.snd

lemma mem_codesOn {d : ℕ} {b : Bool} {S : Finset (Vertex d)} {x : Code d} :
    x ∈ codesOn b S ↔ (b, x) ∈ S := by
  constructor
  · intro hx
    obtain ⟨v, hv, hsecond⟩ := Finset.mem_image.mp hx
    have hv' := Finset.mem_filter.mp hv
    have hfirst : v.1 = b := hv'.2
    have : v = (b, x) := by
      apply Prod.ext
      · exact hfirst
      · exact hsecond
    simpa [this] using hv'.1
  · intro hx
    exact Finset.mem_image.mpr ⟨(b, x), Finset.mem_filter.mpr ⟨hx, rfl⟩, rfl⟩

lemma sideSet_codesOn_subset {d : ℕ} (b : Bool) (S : Finset (Vertex d)) :
    sideSet b (codesOn b S) ⊆ S := by
  intro v hv
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
  exact mem_codesOn.mp hx

lemma card_codesOn {d : ℕ} (b : Bool) (S : Finset (Vertex d)) :
    (codesOn b S).card = (S.filter fun v ↦ v.1 = b).card := by
  apply Finset.card_image_iff.mpr
  intro v hv w hw hsecond
  have hvb := (Finset.mem_filter.mp hv).2
  have hwb := (Finset.mem_filter.mp hw).2
  apply Prod.ext
  · exact hvb.trans hwb.symm
  · exact hsecond

lemma card_codesOn_add {d : ℕ} (S : Finset (Vertex d)) :
    (codesOn false S).card + (codesOn true S).card = S.card := by
  rw [card_codesOn, card_codesOn]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := S) (fun v : Vertex d ↦ v.1 = false)
  have htrue : (S.filter fun v : Vertex d ↦ ¬v.1 = false) =
      S.filter fun v ↦ v.1 = true := by
    ext v
    simp
  simpa [htrue] using hpartition

lemma side_edge_of_four {d : ℕ} {b : Bool} {S : Finset (Vertex d)}
    (hfour : 4 ≤ (codesOn b S).card) :
    ∃ e ∈ constructionEdges d, e ⊆ S := by
  obtain ⟨s, hsub, hcard⟩ := Finset.exists_subset_card_eq hfour
  refine ⟨sideSet b s, ?_, ?_⟩
  · have hs : s ∈ fours d := Finset.mem_powersetCard.mpr
      ⟨hsub.trans (by simp [codesOn]), hcard⟩
    cases b
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact mem_codesOn.mp (hsub hx)

lemma rect_param_mem {d : ℕ} {rp cp : Finset (Code d)}
    (hrp : rp ∈ pairs d) (hcp : cp ∈ pairs d)
    (heven : (∑ y ∈ cp, pairLabel rp y) = false) :
    (Sigma.mk rp cp) ∈ evenRectParams d := by
  exact Finset.mem_sigma.mpr ⟨hrp, Finset.mem_filter.mpr ⟨hcp, heven⟩⟩

lemma rectSet_subset_of_codesOn {d : ℕ} {S : Finset (Vertex d)}
    {rp cp : Finset (Code d)} (hr : rp ⊆ codesOn false S)
    (hc : cp ⊆ codesOn true S) : rectSet (Sigma.mk rp cp) ⊆ S := by
  intro v hv
  simp only [rectSet, Finset.mem_union] at hv
  rcases hv with hv | hv
  · exact sideSet_codesOn_subset false S (Finset.mem_image.mpr <|
      let ⟨x, hx, hEq⟩ := Finset.mem_image.mp hv
      ⟨x, hr hx, hEq⟩)
  · exact sideSet_codesOn_subset true S (Finset.mem_image.mpr <|
      let ⟨x, hx, hEq⟩ := Finset.mem_image.mp hv
      ⟨x, hc hx, hEq⟩)

lemma rect_is_edge {d : ℕ} {z : Sigma fun _ : Finset (Code d) ↦ Finset (Code d)}
    (hz : z ∈ evenRectParams d) : rectSet z ∈ constructionEdges d := by
  apply Finset.mem_union.mpr
  right
  exact Finset.mem_image.mpr ⟨z, hz, rfl⟩

lemma mixed_edge_row_three {d : ℕ} {S : Finset (Vertex d)}
    (hr : (codesOn false S).card = 3) (hc : (codesOn true S).card = 2) :
    ∃ e ∈ constructionEdges d, e ⊆ S := by
  let R := codesOn false S
  let C := codesOn true S
  let f : Code d → Bool := fun x ↦ ∑ y ∈ C, dot x y
  obtain ⟨rp, hrpR, hsum⟩ := pair_in_three_same_bool hr f
  have hrpData := Finset.mem_powersetCard.mp hrpR
  have hrp : rp ∈ pairs d := Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _, hrpData.2⟩
  have hcp : C ∈ pairs d := Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _, hc⟩
  have heven : (∑ y ∈ C, pairLabel rp y) = false := by
    calc
      (∑ y ∈ C, pairLabel rp y) = ∑ x ∈ rp, ∑ y ∈ C, dot x y := by
        simp only [pairLabel]
        rw [Finset.sum_comm]
      _ = false := hsum
  have hz := rect_param_mem hrp hcp heven
  refine ⟨rectSet (Sigma.mk rp C), rect_is_edge hz, ?_⟩
  exact rectSet_subset_of_codesOn hrpData.1 (by rfl)

lemma mixed_edge_col_three {d : ℕ} {S : Finset (Vertex d)}
    (hr : (codesOn false S).card = 2) (hc : (codesOn true S).card = 3) :
    ∃ e ∈ constructionEdges d, e ⊆ S := by
  let R := codesOn false S
  let C := codesOn true S
  obtain ⟨cp, hcpC, heven⟩ :=
    pair_in_three_same_bool hc (pairLabel R)
  have hcpData := Finset.mem_powersetCard.mp hcpC
  have hrp : R ∈ pairs d := Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _, hr⟩
  have hcp : cp ∈ pairs d := Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _, hcpData.2⟩
  have hz := rect_param_mem hrp hcp heven
  refine ⟨rectSet (Sigma.mk R cp), rect_is_edge hz, ?_⟩
  exact rectSet_subset_of_codesOn (by rfl) hcpData.1

lemma construction_covers_five {d : ℕ} {S : Finset (Vertex d)}
    (hS : S.card = 5) : ∃ e ∈ constructionEdges d, e ⊆ S := by
  have hsum := card_codesOn_add S
  rw [hS] at hsum
  by_cases hr4 : 4 ≤ (codesOn false S).card
  · exact side_edge_of_four hr4
  by_cases hc4 : 4 ≤ (codesOn true S).card
  · exact side_edge_of_four hc4
  have hrle : (codesOn false S).card ≤ 3 := by omega
  have hcle : (codesOn true S).card ≤ 3 := by omega
  by_cases hr3 : (codesOn false S).card = 3
  · apply mixed_edge_row_three hr3
    omega
  · apply mixed_edge_col_three
    · omega
    · omega

/- The chromatic number and the edge bound. -/

lemma card_code (d : ℕ) : Fintype.card (Code d) = 2 ^ d := by
  simp [Code]

lemma card_vertex (d : ℕ) : Fintype.card (Vertex d) = 2 * 2 ^ d := by
  simp [Vertex, Code, Fintype.card_prod]

lemma construction_monochromatic_edge (n : ℕ)
    (c : Vertex (n + 1) → Fin (2 ^ n - 1)) :
    ∃ e ∈ constructionEdges (n + 1), ∃ a, ∀ x ∈ e, c x = a := by
  have hcard : Fintype.card (Fin (2 ^ n - 1)) * 4 <
      Fintype.card (Vertex (n + 1)) := by
    rw [Fintype.card_fin, card_vertex]
    rw [pow_succ]
    have hk : 2 ^ n - 1 < 2 ^ n :=
      Nat.sub_lt (pow_pos (by decide : (0 : ℕ) < 2) n) (by decide)
    calc
      (2 ^ n - 1) * 4 < 2 ^ n * 4 :=
        (Nat.mul_lt_mul_right (a := 4) (by decide)).2 hk
      _ = 2 * (2 ^ n * 2) := by ring
  obtain ⟨a, ha⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card (f := c) hcard
  let fiberA := Finset.univ.filter fun x ↦ c x = a
  have hfive : 5 ≤ fiberA.card := by
    change 5 ≤ (Finset.univ.filter fun x ↦ c x = a).card
    omega
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hfive
  obtain ⟨e, he, hesub⟩ := construction_covers_five hScard
  refine ⟨e, he, a, ?_⟩
  intro x hx
  exact (Finset.mem_filter.mp (hSsub (hesub hx))).2


lemma benchmark_choose_scaled (k : ℕ) (hk : 512 ≤ k) :
    80 * k ^ 4 < 24 * (3 * (k - 1) + 1).choose 4 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [twentyFour_mul_choose_four]
  simp only [show 512 + t - 1 = 511 + t by omega, Nat.mul_add]
  rw [show 3 * 511 + 3 * t + 1 - 1 = 1533 + 3*t by omega,
      show 3 * 511 + 3 * t + 1 - 2 = 1532 + 3*t by omega,
      show 3 * 511 + 3 * t + 1 - 3 = 1531 + 3*t by omega]
  ring_nf
  omega

lemma construction_strict_bound (n : ℕ) (hn : 9 ≤ n) :
    (constructionEdges (n + 1)).card < (3 * (2 ^ n - 1) + 1).choose 4 := by
  let k := 2 ^ n
  have hk : 512 ≤ k := by
    change 2 ^ 9 ≤ 2 ^ n
    exact Nat.pow_le_pow_right (by decide) hn
  have hedge := construction_card_bound (n + 1)
  have hedge' : 24 * (constructionEdges (n + 1)).card ≤ 80 * k ^ 4 := by
    calc
      24 * (constructionEdges (n + 1)).card ≤
          5 * Fintype.card (Code (n + 1)) ^ 4 := hedge
      _ = 80 * k ^ 4 := by
        rw [card_code, pow_succ]
        dsimp [k]
        ring
  have hbenchmark := benchmark_choose_scaled k hk
  have hscaled : 24 * (constructionEdges (n + 1)).card <
      24 * (3 * (k - 1) + 1).choose 4 := hedge'.trans_lt hbenchmark
  exact (Nat.mul_lt_mul_left (a := 24) (by decide)).1 hscaled


end Erdos832.BinaryConstruction

open Erdos832.BinaryConstruction

theorem OMA.solution : type_of% @Erdos832.erdos_832 := by
  classical
  intro h
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 (h 4 (by decide))
  let n := K + 9
  let ι := Fintype.equivFin (Vertex (n + 1))
  let edges := constructionEdges (n + 1)
  let H := edges.map ι.finsetCongr.toEmbedding
  have hunif : H.IsUniform 4 := by
    intro e he
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.1 he
    change (s.map ι.toEmbedding).card = 4
    simpa using construction_uniform (n + 1) s hs
  have hex : ∃ j, H.HypergraphColorable j := by
    refine ⟨_, id, fun e he ↦ Finset.one_lt_card.1 ?_⟩
    rw [hunif e he]
    decide
  let k := Nat.find hex
  have hchi : H.HasHypergraphChromaticNumber k :=
    ⟨Nat.find_spec hex, fun j hj ↦ Nat.find_min hex hj⟩
  have hlarge : 2 ^ n ≤ k := by
    by_contra! hlt
    obtain ⟨c, hc⟩ := hchi.1
    have hj : k ≤ 2 ^ n - 1 := by omega
    obtain ⟨s, hs, a, ha⟩ := construction_monochromatic_edge n
      (fun v ↦ Fin.castLE hj (c (ι v)))
    have hm : s.map ι.toEmbedding ∈ H := Finset.mem_map.2 ⟨s, hs, rfl⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hc _ hm
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 hy
    exact hxy (Fin.castLE_injective hj ((ha v hv).trans (ha w hw).symm))
  have hKpow : K ≤ 2 ^ n := by
    have hpow := Nat.mul_le_pow (a := 2) (by decide) K
    exact (show K ≤ 2 ^ K by omega).trans (Nat.pow_le_pow_right (by decide) (by dsimp [n]; omega))
  have hlower := (hK k (hKpow.trans hlarge) _ H hunif hchi).1
  have hstrict := construction_strict_bound n (by dsimp [n]; omega)
  have hcard : H.card = (constructionEdges (n + 1)).card := Finset.card_map _
  have hmono : (3 * (2 ^ n - 1) + 1).choose 4 ≤ (3 * (k - 1) + 1).choose 4 :=
    Nat.choose_le_choose 4 (by omega)
  rw [hcard] at hlower
  exact (Nat.not_le_of_lt hstrict) (hmono.trans hlower)
