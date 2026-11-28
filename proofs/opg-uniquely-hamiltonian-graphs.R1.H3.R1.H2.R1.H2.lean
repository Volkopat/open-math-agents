import OMAReductions.R_opg_uniquely_hamiltonian_graphs_R1_H3_R1_H2_R1
import Mathlib.Data.Fintype.List

/-!
# A second Hamilton cycle in a cubic graph

Formalizes the parity argument of Thomason, *Hamiltonian cycles and uniquely
edge colourable graphs*, Ann. Discrete Math. 3 (1978), 259–268.
https://www.dpmms.cam.ac.uk/~agt2/HC.pdf

Fix the first oriented edge of a Hamilton path. The endpoint has two
neighbors besides its predecessor. The nonclosing choices pair off by
reversing a suffix, so any closing choice has a distinct companion.
-/

namespace OMA.HamiltonThomason

open Finset
open scoped BigOperators

private theorem even_card_closed_finset {α : Type*} [DecidableEq α] (f : α → α)
    (hf : Function.Involutive f) (hne : ∀ a, f a ≠ a) (s : Finset α)
    (hStable : ∀ a ∈ s, f a ∈ s) : Even s.card := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨a, ha⟩ := hs
      have hfa : f a ∈ s.erase a := mem_erase.mpr ⟨hne a, hStable a ha⟩
      let t := (s.erase a).erase (f a)
      have hts : t ⊂ s := lt_of_le_of_lt (erase_subset _ _) (erase_ssubset ha)
      have htStable (x : α) (hx : x ∈ t) : f x ∈ t := by
        have hxfa : x ≠ f a := (mem_erase.mp hx).1
        obtain ⟨hxa, hxs⟩ := mem_erase.mp (mem_erase.mp hx).2
        refine mem_erase.mpr ⟨fun h => hxa (hf.injective h), mem_erase.mpr ⟨?_, hStable x hxs⟩⟩
        intro h
        exact hxfa ((hf x).symm.trans (congrArg f h))
      obtain ⟨k, hk⟩ := ih t hts htStable
      have hcard : t.card + 2 = s.card := by
        have h := card_pos.mpr (show (s.erase a).Nonempty from ⟨f a, hfa⟩)
        dsimp only [t]
        rw [card_erase_of_mem hfa, card_erase_of_mem ha]
        rw [card_erase_of_mem ha] at h
        omega
      exact ⟨k + 1, by omega⟩
    · simp [not_nonempty_iff_eq_empty.mp hs]

/-- An involution without fixed points partitions a finite type into pairs. -/
theorem even_card_of_free_involution {α : Type*} [Finite α] (f : α → α)
    (hf : Function.Involutive f) (hne : ∀ a, f a ≠ a) : Even (Nat.card α) := by
  classical
  let := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, ← card_univ]
  exact even_card_closed_finset f hf hne univ (fun _ _ => mem_univ _)

/-- Two ports per path give an even total number of ports. -/
theorem even_card_two_ports {P : Type*} [Finite P] (ports : P → Type*)
    [∀ p, Finite (ports p)] (hPorts : ∀ p, Nat.card (ports p) = 2) :
    Even (Nat.card (Σ p, ports p)) := by
  classical
  let := Fintype.ofFinite P
  let (p : P) := Fintype.ofFinite (ports p)
  have h (p : P) : Fintype.card (ports p) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hPorts p
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [h, sum_const, card_univ, Nat.nsmul_eq_mul]
  exact ⟨Fintype.card P, Nat.mul_two _⟩

theorem even_card_closing {Ω : Type*} [Finite Ω] (closing : Ω → Prop)
    (hTotal : Even (Nat.card Ω)) (internal : {x // ¬ closing x} → {x // ¬ closing x})
    (hInv : Function.Involutive internal) (hFree : ∀ x, internal x ≠ x) :
    Even (Nat.card {x // closing x}) := by
  classical
  have hSplit : Nat.card Ω = Nat.card {x // closing x} + Nat.card {x // ¬ closing x} := by
    let := Fintype.ofFinite Ω
    let := Fintype.ofFinite {x // closing x}
    let := Fintype.ofFinite {x // ¬ closing x}
    simp only [Nat.card_eq_fintype_card]
    rw [← Fintype.card_congr (Equiv.sumCompl closing), Fintype.card_sum]
  obtain ⟨k, hk⟩ := hTotal
  obtain ⟨j, hj⟩ := even_card_of_free_involution internal hInv hFree
  exact ⟨k - j, by omega⟩

/-- If the internal ports pair up, one closing port forces another. -/
theorem exists_other_closing {Ω : Type*} [Finite Ω] (closing : Ω → Prop)
    (hTotal : Even (Nat.card Ω)) (internal : {x // ¬ closing x} → {x // ¬ closing x})
    (hInv : Function.Involutive internal) (hFree : ∀ x, internal x ≠ x) (x : Ω)
    (hx : closing x) : ∃ y : Ω, y ≠ x ∧ closing y := by
  classical
  by_contra hn
  have hOnly : ∀ y : {z // closing z}, y = ⟨x, hx⟩ := by
    intro y
    apply Subtype.ext
    by_contra hne
    exact hn ⟨y.val, hne, y.property⟩
  have hOne : Nat.card {z // closing z} = 1 := Nat.card_eq_one_iff_unique.mpr
    ⟨⟨fun y z => (hOnly y).trans (hOnly z).symm⟩, ⟨⟨x, hx⟩⟩⟩
  obtain ⟨j, hj⟩ := even_card_closing closing hTotal internal hInv hFree
  omega

end OMA.HamiltonThomason

namespace OMA.HamiltonThomason

open SimpleGraph

def IsPathOrder {V : Type*} (G : SimpleGraph V) (a b : V) (l : List V) : Prop :=
  (∃ t, l = a :: b :: t) ∧ l.Nodup ∧ (∀ x, x ∈ l) ∧ l.IsChain G.Adj

def IsClosing {V : Type*} (G : SimpleGraph V) (a : V) (l : List V) : Prop :=
  ∃ z, l.getLast? = some z ∧ G.Adj z a

def IsPort {V : Type*} (G : SimpleGraph V) (l : List V) (y : V) : Prop :=
  ∃ x p, l.getLast? = some x ∧ l.dropLast.getLast? = some p ∧ G.Adj x y ∧ y ≠ p

abbrev PathOrders {V : Type*} (G : SimpleGraph V) (a b : V) :=
  {l : List V // IsPathOrder G a b l}

abbrev Ports {V : Type*} (G : SimpleGraph V) (a b : V) :=
  Σ l : PathOrders G a b, {y : V // IsPort G l.val y}

abbrev InternalPorts {V : Type*} (G : SimpleGraph V) (a b : V) :=
  {p : Ports G a b // p.2.val ≠ a}

noncomputable instance pathOrderFintype {V : Type*} [Fintype V] (G : SimpleGraph V) (a b : V) :
    Fintype (PathOrders G a b) :=
  Fintype.ofInjective
    (fun l => (⟨l.val, l.prop.2.1⟩ : {l : List V // l.Nodup}))
    (fun _ _ h => Subtype.ext (congrArg (fun v : {l : List V // l.Nodup} => v.val) h))

private theorem exists_last_two {V : Type*} (l : List V) (hl : 2 ≤ l.length) :
    ∃ t p x, l = t ++ [p, x] := by
  cases hrev : l.reverse with
  | nil =>
    have hlen := congrArg List.length hrev
    simp only [List.length_reverse, List.length_nil] at hlen
    omega
  | cons x rest =>
    cases rest with
    | nil =>
      have hlen := congrArg List.length hrev
      simp only [List.length_reverse, List.length_cons, List.length_nil] at hlen
      omega
    | cons p t =>
      refine ⟨t.reverse, p, x, ?_⟩
      simpa [List.reverse_cons, List.append_assoc] using congrArg List.reverse hrev

private theorem last_two_iff {V : Type*} {G : SimpleGraph V} {l : List V} {p x y : V}
    (hx : l.getLast? = some x) (hp : l.dropLast.getLast? = some p) :
    IsPort G l y ↔ G.Adj x y ∧ y ≠ p := by
  constructor
  · rintro ⟨x', p', hx', hp', hadj, hne⟩
    rw [hx, Option.some_inj] at hx'
    rw [hp, Option.some_inj] at hp'
    subst x' p'
    exact ⟨hadj, hne⟩
  · exact fun ⟨hadj, hne⟩ => ⟨x, p, hx, hp, hadj, hne⟩

theorem port_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsRegularOfDegree 3)
    {a b : V} (l : PathOrders G a b) [Fintype {y : V // IsPort G l.val y}] :
    Fintype.card {y : V // IsPort G l.val y} = 2 := by
  have hl : 2 ≤ l.val.length := by obtain ⟨t, ht⟩ := l.prop.1; simp [ht]
  obtain ⟨t, p, x, h⟩ := exists_last_two l.val hl
  have hx : l.val.getLast? = some x := by rw [h]; simp
  have hp : l.val.dropLast.getLast? = some p := by rw [h]; simp
  have hc := l.prop.2.2.2
  rw [h] at hc
  have hpMem : p ∈ G.neighborFinset x :=
    G.mem_neighborFinset x p |>.mpr (hc.right_of_append.rel.symm)
  rw [Fintype.card_of_subtype ((G.neighborFinset x).erase p)
    (fun y => by rw [last_two_iff hx hp, Finset.mem_erase, G.mem_neighborFinset, and_comm])]
  rw [Finset.card_erase_of_mem hpMem, G.card_neighborFinset_eq_degree, hG.degree_eq]

theorem closing_iff_port {V : Type*} {G : SimpleGraph V} {a b : V} {l : List V}
    (hl : IsPathOrder G a b l) (hmin : 3 ≤ l.length) :
    IsClosing G a l ↔ IsPort G l a := by
  obtain ⟨t, p, x, h⟩ := exists_last_two l (by omega)
  have hx : l.getLast? = some x := by rw [h]; simp
  have hp : l.dropLast.getLast? = some p := by rw [h]; simp
  have hne : a ≠ p := by
    cases t with
    | nil => simp [h] at hmin
    | cons z t =>
      have hza : z = a := by
        obtain ⟨u, hu⟩ := hl.1
        rw [h] at hu
        exact (List.cons.inj hu).1
      have hn := hl.2.1
      rw [h, List.cons_append, List.nodup_cons] at hn
      subst z
      exact fun hap => hn.1 (by rw [hap]; simp)
  simp [IsClosing, hx, last_two_iff hx hp, hne]

theorem path_length_ge_three {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsRegularOfDegree 3)
    {a b : V} {l : List V} (hl : IsPathOrder G a b l) : 3 ≤ l.length := by
  have hu : l.toFinset = Finset.univ := by
    ext x
    simp [hl.2.2.1 x]
  have hcard : Fintype.card V = l.length := by
    rw [← Finset.card_univ, ← hu, List.card_toFinset, List.dedup_eq_self.mpr hl.2.1]
  have hdegree := G.degree_lt_card_verts a
  rw [hG.degree_eq, hcard] at hdegree
  omega

private def rotateList {V : Type*} [DecidableEq V] (l : List V) (y : V) : List V :=
  l.takeWhile (fun z => decide (z ≠ y)) ++ y ::
    (l.dropWhile (fun z => decide (z ≠ y))).tail.reverse

private theorem rotateList_of_split {V : Type*} [DecidableEq V] (t s : List V) (y : V)
    (hy : y ∉ t) :
    rotateList (t ++ y :: s) y = t ++ y :: s.reverse := by
  have hfilter : ∀ z ∈ t, decide (z ≠ y) = true := by
    intro z hz
    exact decide_eq_true (fun h => hy (h ▸ hz))
  unfold rotateList
  rw [List.takeWhile_append_of_pos hfilter, List.dropWhile_append_of_pos hfilter]
  simp

private theorem rotate_path_order {V : Type*} {G : SimpleGraph V}
    {a b y : V} {t s : List V} (hne : y ≠ a) (hs : 2 ≤ s.length)
    (horder : IsPathOrder G a b (t ++ y :: s))
    (hport : IsPort G (t ++ y :: s) y) :
    IsPathOrder G a b (t ++ y :: s.reverse) ∧ IsPort G (t ++ y :: s.reverse) y := by
  have hsne : s ≠ [] := by
    intro h
    simp [h] at hs
  obtain ⟨x, p, hx, _hp, hxy, _hyp⟩ := hport
  have hsplit : (t ++ [y]) ++ s = t ++ y :: s := by simp
  have hxS : s.getLast? = some x := by
    rw [← hsplit, List.getLast?_append_of_ne_nil _ hsne] at hx
    exact hx
  have hchain := horder.2.2.2
  have hsufChain : (y :: s).IsChain G.Adj := hchain.right_of_append
  have hreversedChain : (s.reverse).IsChain G.Adj :=
    List.isChain_reverse.mpr (hsufChain.tail.imp (fun _ _ h => h.symm))
  have hchain' : (t ++ y :: s.reverse).IsChain G.Adj := by
    apply (List.isChain_append).mpr
    refine ⟨hchain.left_of_append, hreversedChain.cons (fun z hz => ?_), ?_⟩
    · rw [List.head?_reverse, hxS] at hz
      have hzx : z = x := Option.some.inj (Option.mem_def.mp hz).symm
      simpa only [hzx] using hxy.symm
    · simpa using (List.isChain_append.mp hchain).2.2
  have hperm : (t ++ y :: s.reverse).Perm (t ++ y :: s) :=
    (List.reverse_perm s).cons y |>.append_left t
  have hstart : ∃ u, t ++ y :: s.reverse = a :: b :: u := by
    obtain ⟨u, hu⟩ := horder.1
    cases t with
    | nil => exact (hne (List.cons.inj hu).1).elim
    | cons z t =>
      cases t with
      | nil =>
        obtain ⟨hza, hyb⟩ := List.cons.inj hu
        refine ⟨s.reverse, ?_⟩
        simp [hza, (List.cons.inj hyb).1]
      | cons q t =>
        obtain ⟨hza, htail⟩ := List.cons.inj hu
        exact ⟨t ++ y :: s.reverse, by simp [hza, (List.cons.inj htail).1]⟩
  refine ⟨⟨hstart, hperm.nodup_iff.mpr horder.2.1,
    fun w => hperm.mem_iff.mpr (horder.2.2.1 w), hchain'⟩, ?_⟩
  obtain ⟨u, q, z, hr⟩ := exists_last_two s.reverse (by simpa using hs)
  have he : (t ++ y :: s.reverse) = (t ++ y :: u) ++ [q,z] := by
    rw [hr, List.append_assoc, List.cons_append]
  have hzinhead : z ∈ s.head? := by
    rw [← List.getLast?_reverse, hr]
    simp
  have hyq : y ≠ q := by
    have hnot := (List.nodup_cons.mp (List.nodup_append'.mp horder.2.1).2.1).1
    have hq : q ∈ s := by rw [← List.mem_reverse, hr]; simp
    exact fun h => hnot (h ▸ hq)
  refine ⟨z, q, ?_, ?_, (hsufChain.rel_head? hzinhead).symm, hyq⟩
  · rw [he, List.getLast?_append_of_ne_nil _ (by simp : [q, z] ≠ [])]
    rfl
  · rw [he, List.dropLast_append_cons]
    change ((t ++ y :: u) ++ [q]).getLast? = some q
    rw [List.getLast?_append_of_ne_nil _ (by simp : [q] ≠ [])]
    rfl

private theorem split_internal_port {V : Type*} {G : SimpleGraph V} {a b : V}
    (l : InternalPorts G a b) :
    ∃ t s, l.val.1.val = t ++ l.val.2.val :: s ∧ l.val.2.val ∉ t ∧ 2 ≤ s.length := by
  let raw := l.val.1.val
  let y := l.val.2.val
  obtain ⟨t, s, h, hyt⟩ := List.eq_append_cons_of_mem (l.val.1.prop.2.2.1 y)
  refine ⟨t, s, h, hyt, ?_⟩
  obtain ⟨x, p, hx, hp, hxy, hyp⟩ := l.val.2.prop
  change raw.getLast? = some x at hx
  change raw.dropLast.getLast? = some p at hp
  change raw = t ++ y :: s at h
  rw [h] at hx hp
  cases s with
  | nil =>
    have hxe : y = x := by simpa using hx
    exact (hxy.ne hxe.symm).elim
  | cons z s =>
    cases s with
    | nil =>
      have hpe : y = p := by simpa using hp
      exact (hyp hpe).elim
    | cons q s => simp

private theorem rotateList_valid {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b : V}
    (l : InternalPorts G a b) :
    IsPathOrder G a b (rotateList l.val.1.val l.val.2.val) ∧
      IsPort G (rotateList l.val.1.val l.val.2.val) l.val.2.val := by
  let raw := l.val.1.val
  let y := l.val.2.val
  change IsPathOrder G a b (rotateList raw y) ∧ IsPort G (rotateList raw y) y
  obtain ⟨t, s, h, hyt, hs⟩ := split_internal_port l
  change raw = t ++ y :: s at h
  have hraw : IsPathOrder G a b raw := l.val.1.prop
  have hptr : IsPort G raw y := l.val.2.prop
  rw [h, rotateList_of_split t s y hyt]
  rw [h] at hraw hptr
  exact rotate_path_order l.prop hs hraw hptr

def rotatePort {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b : V}
    (l : InternalPorts G a b) : InternalPorts G a b :=
  ⟨⟨⟨_, (rotateList_valid l).1⟩, ⟨l.val.2.val, (rotateList_valid l).2⟩⟩, l.prop⟩

@[simp]
theorem rotatePort_order {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b : V}
    (l : InternalPorts G a b) :
    (rotatePort l).val.1.val = rotateList l.val.1.val l.val.2.val := rfl

@[simp]
theorem rotatePort_pivot {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b : V}
    (l : InternalPorts G a b) :
    (rotatePort l).val.2.val = l.val.2.val := rfl

theorem ports_ext {V : Type*} {G : SimpleGraph V} {a b : V}
    {x y : Ports G a b} (hL : x.1.val = y.1.val) (hP : x.2.val = y.2.val) : x = y := by
  rcases x with ⟨xL, xP⟩
  rcases y with ⟨yL, yP⟩
  have : xL = yL := Subtype.ext hL
  subst yL
  congr 1
  exact Subtype.ext hP

theorem rotatePort_involutive {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b : V} :
    Function.Involutive (rotatePort (G := G) (a := a) (b := b)) := by
  intro l
  apply Subtype.ext
  apply ports_ext
  · simp only [rotatePort_order, rotatePort_pivot]
    let raw := l.val.1.val
    let y := l.val.2.val
    change rotateList (rotateList raw y) y = raw
    obtain ⟨t, s, ht, hn, _hs⟩ := split_internal_port l
    change raw = t ++ y :: s at ht
    rw [ht, rotateList_of_split t s y hn, rotateList_of_split t s.reverse y hn,
      List.reverse_reverse]
  · simp

theorem rotatePort_ne_self {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b : V}
    (l : InternalPorts G a b) : rotatePort l ≠ l := by
  intro h
  let raw := l.val.1.val
  let y := l.val.2.val
  have heq : rotateList raw y = raw := congrArg (fun p : InternalPorts G a b => p.val.1.val) h
  obtain ⟨t, s, ht, hyt, hs⟩ := split_internal_port l
  change raw = t ++ y :: s at ht
  rw [ht, rotateList_of_split t s y hyt] at heq
  have hrev : s.reverse = s := (List.cons.inj (List.append_cancel_left heq)).2
  have hn := l.val.1.prop.2.1
  change raw.Nodup at hn
  rw [ht] at hn
  have hns : s.Nodup := (List.nodup_append'.mp hn).2.1.of_cons
  have hsne : s ≠ [] := by intro he; simp [he] at hs
  have hend : s.head? = s.getLast? := by rw [← List.getLast?_reverse, hrev]
  have he : s.head hsne = s.getLast hsne := by
    simpa only [List.head?_eq_some_head hsne, List.getLast?_eq_some_getLast hsne,
      Option.some_inj] using hend
  obtain ⟨x, hx⟩ := (List.Nodup.head_eq_getLast_iff hsne hns).mp he
  simp [hx] at hs

end OMA.HamiltonThomason

namespace OMA.HamiltonThomason

open SimpleGraph

theorem exists_other_closing_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsRegularOfDegree 3)
    {a b : V} {l : List V} (hl : IsPathOrder G a b l) (hc : IsClosing G a l) :
    ∃ l', l' ≠ l ∧ IsPathOrder G a b l' ∧ IsClosing G a l' := by
  classical
  let port : Ports G a b :=
    ⟨⟨l, hl⟩, ⟨a, (closing_iff_port hl (path_length_ge_three G hG hl)).mp hc⟩⟩
  have heven : Even (Nat.card (Ports G a b)) :=
    even_card_two_ports (fun p : PathOrders G a b => {y : V // IsPort G p.val y})
      (fun p => Nat.card_eq_fintype_card.trans (port_card G hG p))
  obtain ⟨other, hne, hlast⟩ := exists_other_closing
    (fun p : Ports G a b => p.2.val = a)
    heven rotatePort rotatePort_involutive rotatePort_ne_self port rfl
  refine ⟨other.1.val, ?_, other.1.prop,
    (closing_iff_port other.1.prop (path_length_ge_three G hG other.1.prop)).mpr ?_⟩
  · exact fun h => hne (ports_ext h hlast)
  · simpa only [← hlast] using other.2.prop

end OMA.HamiltonThomason

namespace OMA.HamiltonThomason

open SimpleGraph

variable {V : Type*}

private theorem exists_support_prefix {G : SimpleGraph V} {a z : V} (p : G.Walk a z)
    (hp : ¬ p.Nil) : ∃ t, p.support = a :: p.snd :: t := by
  cases p with
  | nil => exact (hp Walk.Nil.nil).elim
  | cons h p =>
      exact ⟨p.support.tail, by rw [Walk.support_cons, Walk.snd_cons, p.cons_tail_support]⟩

theorem exists_order_of_cycle {G : SimpleGraph V} {a : V} (c : G.Walk a a)
    (hc : c.IsCycle) (hspan : ∀ x : V, x ∈ c.support) :
    IsPathOrder G a c.snd c.support.dropLast ∧ IsClosing G a c.support.dropLast := by
  have hlength := hc.three_le_length
  have hne : ¬ c.dropLast.Nil := Walk.not_nil_iff_lt_length.mpr (by
    rw [Walk.length_dropLast]
    omega)
  have hsnd : c.dropLast.snd = c.snd := Walk.getVert_dropLast (by omega)
  have hdrop := c.support_dropLast hc.not_nil
  refine ⟨⟨?_, hc.nodup_dropLast_support, ?_, ?_⟩, ?_⟩
  · rw [← hdrop, ← hsnd]
    exact exists_support_prefix c.dropLast hne
  · intro x
    rw [← hdrop]
    by_cases h : x = a
    · subst x
      exact c.dropLast.start_mem_support
    · have hx := hspan x
      rw [← c.support_dropLast_concat hc.not_nil, List.mem_append, List.mem_singleton] at hx
      exact hx.resolve_right h
  · rw [← hdrop]
    exact c.dropLast.isChain_adj_support
  · refine ⟨c.penultimate, ?_, c.adj_penultimate hc.not_nil⟩
    rw [← hdrop, List.getLast?_eq_some_getLast c.dropLast.support_ne_nil, Walk.getLast_support]

theorem exists_cycle_of_order {G : SimpleGraph V} {a b : V} {l : List V}
    (hl : IsPathOrder G a b l) (hclose : IsClosing G a l) (hlen : 3 ≤ l.length) :
    ∃ d : G.Walk a a, d.IsCycle ∧ (∀ x, x ∈ d.support) ∧
      d.support = l ++ [a] ∧ d.snd = b := by
  obtain ⟨⟨t, rfl⟩, hn, hspan, hchain⟩ := hl
  obtain ⟨z, hz, hza⟩ := hclose
  let l := a :: b :: t
  have hlane : l ++ [a] ≠ [] := by simp
  have hall : (l ++ [a]).IsChain G.Adj := by
    apply hchain.append (.singleton _)
    intro x hx y hy
    change x ∈ (a :: b :: t).getLast? at hx
    rw [hz] at hx
    have hzx : z = x := by simpa using hx
    have hay : a = y := by simpa using hy
    simpa only [hzx, hay] using hza
  have hfirst : (l ++ [a]).head hlane = a := by simp [l]
  have hend : (l ++ [a]).getLast hlane = a := by simp
  let q := Walk.ofSupport (l ++ [a]) hlane hall
  let d : G.Walk a a := q.copy hfirst hend
  have hsupp : d.support = l ++ [a] :=
    (q.support_copy hfirst hend).trans (Walk.support_ofSupport hlane hall)
  have hdlength : 3 ≤ d.length := by
    have he := d.length_support
    rw [hsupp, List.length_append, List.length_singleton] at he
    change 3 ≤ l.length at hlen
    omega
  have hdn : ¬ d.Nil := Walk.not_nil_iff_lt_length.mpr (by omega)
  refine ⟨d, Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, hdlength⟩,
    fun x => hsupp ▸ List.mem_append_left [a] (hspan x), hsupp, ?_⟩
  · apply Walk.IsPath.mk'
    rw [d.support_tail_of_not_nil hdn, hsupp]
    have ha : a ∉ b :: t := (List.nodup_cons.mp hn).1
    have ht : (b :: t).Nodup := (List.nodup_cons.mp hn).2
    change ((b :: t) ++ [a]).Nodup
    refine List.nodup_append'.mpr ⟨ht, by simp, ?_⟩
    intro x hx hxa
    exact ha (List.mem_singleton.mp hxa ▸ hx)
  · rw [d.snd_eq_support_getElem_one hdn]
    simp [hsupp, l]

theorem cycle_eq_of_first_edge_and_edge_finset [DecidableEq V]
    {G : SimpleGraph V} {a : V} (c d : G.Walk a a)
    (hc : c.IsCycle) (hd : d.IsCycle) (hfirst : c.snd = d.snd)
    (he : c.edges.toFinset = d.edges.toFinset) : c = d := by
  have hlength : c.length = d.length := by
    calc
      c.length = c.edges.toFinset.card := by simp [List.toFinset_card_of_nodup hc.isTrail.edges_nodup]
      _ = d.edges.toFinset.card := congrArg Finset.card he
      _ = d.length := by simp [List.toFinset_card_of_nodup hd.isTrail.edges_nodup]
  have hadj {x y : V} : c.toSubgraph.Adj x y ↔ d.toSubgraph.Adj x y := by
    rw [Walk.adj_toSubgraph_iff_mem_edges, Walk.adj_toSubgraph_iff_mem_edges]
    simpa only [List.mem_toFinset] using
      (show s(x, y) ∈ c.edges.toFinset ↔ s(x, y) ∈ d.edges.toFinset by rw [he])
  have h₂ (i : ℕ) :
      (i ≤ c.length → c.getVert i = d.getVert i) ∧
      (i + 1 ≤ c.length → c.getVert (i + 1) = d.getVert (i + 1)) := by
    induction i with
    | zero => exact ⟨fun _ => by simp, fun _ => hfirst⟩
    | succ i ih =>
        refine ⟨ih.2, ?_⟩
        intro hi
        have hprev := ih.1 (by omega)
        have hhere := ih.2 (by omega)
        have hp : c.toSubgraph.spanningCoe.Adj (c.getVert (i+1)) (c.getVert i) :=
          (c.toSubgraph_adj_getVert (i := i) (by omega)).symm
        obtain ⟨w, _, huniq⟩ := hc.isCycles_spanningCoe_toSubgraph.existsUnique_ne_adj hp
        have hc₁ : c.getVert i ≠ c.getVert (i+2) := by
          simpa [Nat.add_assoc] using hc.getVert_sub_one_ne_getVert_add_one (i := i+1) (by omega)
        have hd₁ : d.getVert i ≠ d.getVert (i+2) := by
          simpa [Nat.add_assoc] using hd.getVert_sub_one_ne_getVert_add_one (i := i+1) (by omega)
        have hc₂ : c.toSubgraph.spanningCoe.Adj (c.getVert (i+1)) (c.getVert (i+2)) :=
          c.toSubgraph_adj_getVert (by omega)
        have hd₂ : c.toSubgraph.spanningCoe.Adj (d.getVert (i+1)) (d.getVert (i+2)) :=
          hadj.mpr (d.toSubgraph_adj_getVert (by omega))
        exact (huniq _ ⟨hc₁, hc₂⟩).trans (huniq _ ⟨hprev ▸ hd₁, hhere ▸ hd₂⟩).symm
  exact Walk.ext_getVert_le_length hlength fun n hn => (h₂ n).1 hn

end OMA.HamiltonThomason

theorem OMA.solution : OMA.R_opg_uniquely_hamiltonian_graphs_R1_H3_R1_H2_R1.H2 := by
  intro V _ _ G _ hG v c hc
  open OMA.HamiltonThomason in
  obtain ⟨hl, hclose⟩ := exists_order_of_cycle c hc.1 hc.2
  open OMA.HamiltonThomason in
  obtain ⟨l, hne, horder, hclosing⟩ := exists_other_closing_order G hG hl hclose
  open OMA.HamiltonThomason in
  obtain ⟨d, hd, hspan, hsupp, hfirst⟩ :=
    exists_cycle_of_order horder hclosing (path_length_ge_three G hG horder)
  refine ⟨v, d, ⟨hd, hspan⟩, ?_⟩
  intro he
  have hcd := OMA.HamiltonThomason.cycle_eq_of_first_edge_and_edge_finset
    c d hc.1 hd hfirst.symm he.symm
  have hs : c.support = d.support := congrArg SimpleGraph.Walk.support hcd
  rw [hsupp] at hs
  exact hne (by simpa using congrArg List.dropLast hs.symm)
