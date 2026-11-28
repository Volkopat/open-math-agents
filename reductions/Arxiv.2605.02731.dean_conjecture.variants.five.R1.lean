import FormalConjectures.Arxiv.«2605.02731».DeanCycles
import Mathlib

-- Credit: @MrSeizy

/-!
Connectivity reduction for the modulus-five case of Dean's conjecture.
The induced two-connected core and path-gluing helpers are adapted from the
catalog's general Dean reduction (open-math-agents PR #9511, commit 91a8666a).
The three-cut argument uses the rooted-path method of Kamil Sieniawski,
with two sides partitioning the entire deletion and the retained separator
vertex allowed to attach through either of the two roots. The no-degree-bound
connectivity conclusion also applies when the exceptional vertex is arbitrary.
Reference: https://github.com/pkchv/dean-conjecture/blob/main/paper/Dean_conjecture_k5.md
-/

namespace OMA.R_Arxiv_2605_02731_dean_conjecture_variants_five_R1

open SimpleGraph

private def inComponent {V : Type} (G : SimpleGraph V) {S : Set V} (r : S) : Set V :=
  {v | ∃ hv : v ∈ S, (G.induce S).Reachable r ⟨v, hv⟩}

private lemma mem_comp {V : Type} (G : SimpleGraph V) {S : Set V} (r v : S) :
    v.val ∈ inComponent G r ↔ (G.induce S).Reachable r v :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨v.property, h⟩⟩

private lemma comp_subset {V : Type} (G : SimpleGraph V) {S : Set V} (r : S) :
    inComponent G r ⊆ S :=
  fun _ ⟨h, _⟩ => h

private lemma comp_closed {V : Type} {G : SimpleGraph V} {S : Set V} {r : S}
    {u v : V} (hu : u ∈ inComponent G r) (hv : v ∈ S) (ha : G.Adj u v) :
    v ∈ inComponent G r := by
  obtain ⟨huS, hru⟩ := hu
  have h : (G.induce S).Adj ⟨u, huS⟩ ⟨v, hv⟩ := ha
  exact ⟨hv, hru.trans h.reachable⟩

private lemma comp_conn {V : Type} {G : SimpleGraph V} {S : Set V} (r : S) :
    (G.induce (inComponent G r)).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨r.val, ⟨r.property, .rfl⟩⟩, ?_⟩
  rintro ⟨v, hv, hrv⟩
  obtain ⟨p⟩ := hrv
  classical
  have all (w : S) (hw : w ∈ p.support) : w.val ∈ inComponent G r :=
    ⟨w.property, (p.takeUntil w hw).reachable⟩
  let f := SimpleGraph.Embedding.induce S (G := G)
  have hsub : ∀ w ∈ (p.map f.toHom).support, w ∈ inComponent G r := by
    simp only [Walk.support_map, List.mem_map]
    rintro _ ⟨w, hw, rfl⟩
    exact all w hw
  exact ⟨(p.map f.toHom).induce _ hsub⟩

private def twoConn {V : Type} (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∀ v : V, (G.induce {w | w ≠ v}).Connected

private lemma induce_compl_conn {V : Type} {G : SimpleGraph V} {S : Set V} {c : S}
    (h : ¬ (G.induce S |>.induce {w : S | w ≠ c}).Connected)
    (hne : ∃ v ∈ S, v ≠ c.val) :
    ∃ r t : {v : V | v ∈ S ∧ v ≠ c.val},
      ¬ (G.induce {v : V | v ∈ S ∧ v ≠ c.val}).Reachable r t := by
  let T := {v : V | v ∈ S ∧ v ≠ c.val}
  by_contra hn
  push Not at hn
  have hconn : (G.induce T).Connected := by
    obtain ⟨v, hv, hvc⟩ := hne
    let _ : Nonempty T := ⟨⟨v, hv, hvc⟩⟩
    exact Connected.mk hn
  apply h
  let f : G.induce T →g (G.induce S).induce {w : S | w ≠ c} :=
    ⟨fun v => ⟨⟨v, v.property.1⟩, fun he => v.property.2 (congrArg Subtype.val he)⟩,
     fun ha => ha⟩
  exact hconn.map f (by
    rintro ⟨⟨v, hv⟩, hvc⟩
    exact ⟨⟨v, hv, fun h => hvc (Subtype.ext h)⟩, rfl⟩)

private noncomputable def boundary {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (B S : Finset V) : Finset V := by
  classical
  exact S.filter fun v => v ∈ B ∨ ∃ w ∉ S, G.Adj v w

private lemma mem_boundary {V : Type} [DecidableEq V] {G : SimpleGraph V}
    {B S : Finset V} {v : V} :
    v ∈ boundary G B S ↔ v ∈ S ∧ (v ∈ B ∨ ∃ w ∉ S, G.Adj v w) := by
  classical
  simp [boundary]

private lemma card_le_of_good {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {B S : Finset V} {v : V} {k : ℕ}
    (hdeg : ∀ w ∉ B, k ≤ (G.neighborSet w).ncard) (hv : v ∈ S) (hb : v ∉ boundary G B S) :
    k < S.card := by
  have hvB : v ∉ B := fun h => hb (mem_boundary.mpr ⟨hv, Or.inl h⟩)
  have hsub : G.neighborSet v ⊆ (S : Set V) := by
    intro w hw
    by_contra hs
    exact hb (mem_boundary.mpr ⟨hv, Or.inr ⟨w, hs, hw⟩⟩)
  let f (w : G.neighborSet v) : ↥(S.erase v) :=
    ⟨w, Finset.mem_erase.mpr ⟨(G.ne_of_adj w.property).symm, hsub w.property⟩⟩
  have hn := Fintype.card_le_of_injective f
    (fun _ _ e => Subtype.ext (congrArg (fun w : ↥(S.erase v) => w.val) e))
  rw [Set.fintypeCard_eq_ncard, Fintype.card_coe, Finset.card_erase_of_mem hv] at hn
  exact ((hdeg v hvB).trans hn).trans_lt
    (Nat.sub_lt (Finset.card_pos.mpr ⟨v, hv⟩) (by decide))

private theorem exists_twoConn_core {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (B : Finset V) (k q : ℕ)
    (hq : 1 ≤ q) (hqk : q < k) (hB : B.card ≤ q)
    (hdeg : ∀ w ∉ B, k ≤ (G.neighborSet w).ncard) (hgood : ∃ v, v ∉ B) :
    ∃ S : Finset V, twoConn (G.induce (S : Set V)) ∧
      (boundary G B S).card ≤ q ∧ ∃ v ∈ S, v ∉ boundary G B S := by
  classical
  let P (S : Finset V) : Prop :=
    (boundary G B S).card ≤ q ∧ ∃ v ∈ S, v ∉ boundary G B S
  have hP : ∃ S, P S := by
    obtain ⟨v, hv⟩ := hgood
    have heq : boundary G B Finset.univ = B := by
      ext w
      simp [mem_boundary]
    exact ⟨Finset.univ, by rwa [heq], v, Finset.mem_univ _, by rwa [heq]⟩
  obtain ⟨S, hS, hmin⟩ := exists_minimalFor_of_wellFoundedLT P Finset.card hP
  obtain ⟨hbS, v, hv, hvb⟩ := hS
  have hlarge := card_le_of_good hdeg hv hvb
  have hconn : (G.induce (S : Set V)).Connected := by
    let r : (S : Set V) := ⟨v, hv⟩
    let T := inComponent G r
    let F := T.toFinset
    have hFT : (F : Set V) = T := Set.coe_toFinset T
    have hFsub : F ⊆ S := by
      intro w hw
      exact comp_subset G r ((Set.mem_toFinset).mp hw)
    have hvT : v ∈ F := Set.mem_toFinset.mpr ⟨hv, .rfl⟩
    have hbsub : boundary G B F ⊆ boundary G B S := by
      intro w hw
      rw [mem_boundary] at hw ⊢
      refine ⟨hFsub hw.1, hw.2.imp_right ?_⟩
      rintro ⟨u, hu, hwu⟩
      refine ⟨u, fun huS => hu ?_, hwu⟩
      exact Set.mem_toFinset.mpr (comp_closed (Set.mem_toFinset.mp hw.1) huS hwu)
    have hPF : P F := ⟨(Finset.card_le_card hbsub).trans hbS, v, hvT, fun h => hvb (hbsub h)⟩
    have heq : F = S := by
      apply Finset.eq_of_subset_of_card_le hFsub
      exact hmin hPF (Finset.card_le_card hFsub)
    have hc := comp_conn (G := G) r
    change (G.induce T).Connected at hc
    rwa [← hFT, heq] at hc
  refine ⟨S, ⟨hconn, ?_⟩, hbS, v, hv, hvb⟩
  intro c
  by_contra hcut
  have hex : ∃ t ∈ S, t ≠ c.val := by
    have : 1 < S.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp this
    by_cases h : a = c.val
    · exact ⟨b, hb, fun he => hab (h.trans he.symm)⟩
    · exact ⟨a, ha, h⟩
  let D := {w : V | w ∈ S ∧ w ≠ c.val}
  obtain ⟨r, t, hrt⟩ := induce_compl_conn hcut hex
  have hgoodD : ∃ u : D, u.val ∉ boundary G B S := by
    have hcsmall : (insert c.val (boundary G B S)).card ≤ q + 1 :=
      (Finset.card_insert_le _ _).trans (by omega)
    have hns : ¬ S ⊆ insert c.val (boundary G B S) :=
      fun h => by have := Finset.card_le_card h; omega
    obtain ⟨u, hu, hbad⟩ := Finset.not_subset.mp hns
    rw [Finset.mem_insert, not_or] at hbad
    exact ⟨⟨u, hu, hbad.1⟩, hbad.2⟩
  obtain ⟨u, hu⟩ := hgoodD
  have hpick : ∃ a b : D, a.val ∉ boundary G B S ∧
      ¬ (G.induce D).Reachable a b ∧
      ((boundary G B S).card < q ∨
        ∃ z ∈ boundary G B S, z ∉ inComponent G a) := by
    have hout : ∃ b : D, ¬ (G.induce D).Reachable u b := by
      by_cases h : (G.induce D).Reachable u r
      · exact ⟨t, fun ht => hrt (h.symm.trans ht)⟩
      · exact ⟨r, h⟩
    obtain ⟨b, hb⟩ := hout
    by_cases hsmall : (boundary G B S).card < q
    · exact ⟨u, b, hu, hb, Or.inl hsmall⟩
    by_cases hbad : ∃ z ∈ boundary G B S, z ∉ inComponent G u
    · exact ⟨u, b, hu, hb, Or.inr hbad⟩
    have hh : ∀ z ∈ boundary G B S, z ∈ inComponent G u := by
      push Not at hbad
      exact hbad
    have hb' : b.val ∉ boundary G B S := fun h =>
      hb ((mem_comp G u b).mp (hh b.val h))
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < (boundary G B S).card)
    refine ⟨b, u, hb', fun h => hb h.symm, Or.inr ⟨z, hz, ?_⟩⟩
    intro hzb
    obtain ⟨hzD, huz⟩ := hh z hz
    obtain ⟨_, hbz⟩ := hzb
    exact hb (huz.trans hbz.symm)
  obtain ⟨a, b, ha, hab, hlimit⟩ := hpick
  let T := inComponent G a
  let F := insert c.val T.toFinset
  have hsub : F ⊆ S := by
    intro w hw
    rw [Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · exact c.property
    · exact (comp_subset G a (Set.mem_toFinset.mp hw)).1
  have hbF : b.val ∉ F := by
    rw [Finset.mem_insert, not_or, Set.mem_toFinset]
    exact ⟨b.property.2, fun h => hab ((mem_comp G a b).mp h)⟩
  have hlt : F.card < S.card :=
    Finset.card_lt_card (Finset.ssubset_iff_of_subset hsub |>.mpr ⟨b, b.property.1, hbF⟩)
  have hbadF : boundary G B F ⊆ insert c.val ((boundary G B S).filter (· ∈ T)) := by
    intro w hw
    rw [mem_boundary] at hw
    have hwF : w = c.val ∨ w ∈ T := by simpa [F] using hw.1
    rcases hwF with rfl | hwT
    · exact Finset.mem_insert_self _ _
    apply Finset.mem_insert_of_mem
    rw [Finset.mem_filter, mem_boundary]
    refine ⟨⟨hsub hw.1, hw.2.imp_right ?_⟩, hwT⟩
    rintro ⟨z, hzF, hwz⟩
    refine ⟨z, fun hzS => hzF ?_, hwz⟩
    by_cases hzc : z = c.val
    · exact Finset.mem_insert.mpr (Or.inl hzc)
    · exact Finset.mem_insert_of_mem (Set.mem_toFinset.mpr
        (comp_closed hwT ⟨hzS, hzc⟩ hwz))
  have hcard : (boundary G B F).card ≤ q := by
    apply (Finset.card_le_card hbadF).trans
    apply (Finset.card_insert_le _ _).trans
    rcases hlimit with hlim | ⟨z, hz, hzT⟩
    · have := Finset.card_filter_le (s := boundary G B S) (p := (· ∈ T))
      omega
    · have hl := Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨z, hz, hzT⟩)
      change ((boundary G B S).filter (· ∈ T)).card < (boundary G B S).card at hl
      omega
  have haT : a.val ∈ T := ⟨a.property, .rfl⟩
  have haF : a.val ∈ F := Finset.mem_insert_of_mem (Set.mem_toFinset.mpr haT)
  have haBad : a.val ∉ boundary G B F := by
    intro h
    rcases Finset.mem_insert.mp (hbadF h) with hc | hm
    · exact a.property.2 hc
    · exact ha (Finset.mem_filter.mp hm).1
  exact (not_le_of_gt hlt) (hmin (show P F from ⟨hcard, a, haF, haBad⟩) hlt.le)

private def HasCycle {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ k ∣ p.length

private def PathOfLength {V : Type} (G : SimpleGraph V) (x y : V) (n : ℕ) : Prop :=
  ∃ p : G.Walk x y, p.IsPath ∧ p.length = n

private lemma combine {V : Type} {G : SimpleGraph V} {x y : V} {p q : G.Walk x y}
    (hp : p.IsPath) (hq : q.IsPath) (hl : 1 < p.length ∨ 1 < q.length)
    (hinter : ∀ z ∈ p.support, z ∈ q.support → z = x ∨ z = y) :
    (p.append q.reverse).IsCycle := by
  apply hp.isCycle_append hq.reverse ?_ (by simpa using hl)
  apply List.disjoint_left.mpr
  intro z hzp hzq
  have hqp : z ∈ q.support := by
    simpa only [Walk.support_reverse, List.mem_reverse] using List.mem_of_mem_tail hzq
  rcases hinter z (List.mem_of_mem_tail hzp) hqp with rfl | rfl
  · exact (List.nodup_cons.mp (show (_ :: p.support.tail).Nodup by
      simpa only [Walk.cons_tail_support] using hp.support_nodup)).1 hzp
  · exact (List.nodup_cons.mp (show (_ :: q.reverse.support.tail).Nodup by
      simpa only [Walk.cons_tail_support] using hq.reverse.support_nodup)).1 hzq

private lemma preserves_reachable {A B : Type} {G : SimpleGraph A} {H : SimpleGraph B}
    (f : A → B) (hf : ∀ ⦃a b⦄, G.Adj a b → H.Reachable (f a) (f b))
    {a b : A} (h : G.Reachable a b) : H.Reachable (f a) (f b) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .rfl
  | cons hadj _ ih => exact (hf hadj).trans ih

private def addEdge {V : Type} (G : SimpleGraph V) (x y : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∨ (x ≠ y ∧ ((a = x ∧ b = y) ∨ (a = y ∧ b = x)))
  symm := ⟨fun a b h => by
    rcases h with h | ⟨hxy, h⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hxy, by tauto⟩⟩
  loopless := ⟨fun a h => by
    rcases h with h | ⟨hxy, h⟩
    · exact G.loopless.irrefl a h
    · rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact hxy (h₁.symm.trans h₂)
      · exact hxy (h₂.symm.trans h₁)⟩

private def side {V : Type} (x y : V) (M : Set V) : Set V := {v | v = x ∨ v = y ∨ v ∈ M}

private lemma sideConnected {V : Type} {G : SimpleGraph V} {x y : V}
    {M D : Set V} (hxy : x ≠ y)
    (hclosed : ∀ ⦃a b⦄, a ∈ M → b ∈ D → b ≠ x → b ≠ y → G.Adj a b → b ∈ M)
    (hD : (G.induce D).Connected) {r : V} (hr : r = x ∨ r = y) (hrD : r ∈ D) :
    ((addEdge G x y).induce (D ∩ side x y M)).Connected := by
  classical
  let S := side x y M
  let H := (addEdge G x y).induce (D ∩ S)
  have hrS : r ∈ S := hr.imp_right Or.inl
  let root : ↥(D ∩ S) := ⟨r, hrD, hrS⟩
  let f (v : D) : ↥(D ∩ S) := if hv : v.val ∈ S then ⟨v.val, v.property, hv⟩ else root
  have hf : ∀ ⦃a b : D⦄, (G.induce D).Adj a b → H.Reachable (f a) (f b) := by
    intro a b hab
    change G.Adj a.val b.val at hab
    have root_reach {v : V} (hvD : v ∈ D) (hvS : v ∈ S)
        (hv : v = x ∨ v = y) : H.Reachable ⟨v, hvD, hvS⟩ root := by
      rcases hv with hv | hv <;> rcases hr with hr | hr
      · rw [show (⟨v, hvD, hvS⟩ : ↥(D ∩ S)) = root from Subtype.ext (hv.trans hr.symm)]
      · exact (show H.Adj ⟨v, hvD, hvS⟩ root from Or.inr ⟨hxy, Or.inl ⟨hv, hr⟩⟩).reachable
      · exact (show H.Adj ⟨v, hvD, hvS⟩ root from Or.inr ⟨hxy, Or.inr ⟨hv, hr⟩⟩).reachable
      · rw [show (⟨v, hvD, hvS⟩ : ↥(D ∩ S)) = root from Subtype.ext (hv.trans hr.symm)]
    have adj_to_out {u v : V} (hu : u ∈ S) (hvD : v ∈ D) (hv : v ∉ S) (h : G.Adj u v) :
        u = x ∨ u = y := by
      rcases hu with he | he | hm
      · exact Or.inl he
      · exact Or.inr he
      · exact (hv (Or.inr (Or.inr (hclosed hm hvD
          (fun e => hv (Or.inl e)) (fun e => hv (Or.inr (Or.inl e))) h)))).elim
    by_cases ha : a.val ∈ S <;> by_cases hb : b.val ∈ S
    · rw [show f a = ⟨a.val, a.property, ha⟩ by simp [f, ha],
          show f b = ⟨b.val, b.property, hb⟩ by simp [f, hb]]
      exact (show H.Adj ⟨a.val, a.property, ha⟩ ⟨b.val, b.property, hb⟩ from
        Or.inl hab).reachable
    · simpa only [f, dif_pos ha, dif_neg hb] using root_reach a.property ha (adj_to_out ha b.property hb hab)
    · simpa only [f, dif_neg ha, dif_pos hb] using
        (root_reach b.property hb (adj_to_out hb a.property ha hab.symm)).symm
    · simp [f, ha, hb]
  let _ : Nonempty (D ∩ S : Set V) := ⟨root⟩
  apply Connected.mk
  intro a b
  have he (z : ↥(D ∩ S)) : f ⟨z.val, z.property.1⟩ = z := by simp [f, z.property.2]
  simpa only [he] using preserves_reachable f hf
    (hD ⟨a.val, a.property.1⟩ ⟨b.val, b.property.1⟩)


private lemma ncard_induce {V : Type} {G : SimpleGraph V} {S : Set V} (v : S)
    (h : G.neighborSet v.val ⊆ S) :
    ((G.induce S).neighborSet v).ncard = (G.neighborSet v.val).ncard := by
  apply Set.ncard_congr'
  exact {
    toFun := fun w => ⟨w.val.val, w.property⟩
    invFun := fun w => ⟨⟨w.val, h w.property⟩, w.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }


private lemma cycle_lift {U V : Type} {G : SimpleGraph U} {J : SimpleGraph V}
    (f : G ↪g J) {k : ℕ} (h : HasCycle G k) : HasCycle J k := by
  obtain ⟨v, p, hp, hd⟩ := h
  exact ⟨f v, p.map f.toHom, hp.map f.injective, by simpa using hd⟩

private lemma supported_map {V : Type} {G : SimpleGraph V} {S : Set V}
    {x y : S} (p : (G.induce S).Walk x y) :
    ∀ v ∈ (p.map (Embedding.induce S).toHom).support, v ∈ S := by
  simp only [Walk.support_map, List.mem_map]
  rintro v ⟨w, _, rfl⟩
  exact w.property

private lemma glue_sides {V : Type} {G : SimpleGraph V} {x y : V} {M N : Set V}
    (hdisj : Disjoint M N) {m n : ℕ} (hmn : 1 < m ∨ 1 < n)
    (hp : PathOfLength (G.induce (side x y M)) ⟨x, Or.inl rfl⟩ ⟨y, Or.inr (Or.inl rfl)⟩ m)
    (hq : PathOfLength (G.induce (side x y N)) ⟨x, Or.inl rfl⟩ ⟨y, Or.inr (Or.inl rfl)⟩ n)
    {k : ℕ} (hd : k ∣ m + n) : HasCycle G k := by
  obtain ⟨p, hpp, hpl⟩ := hp
  obtain ⟨q, hqp, hql⟩ := hq
  let f : G.induce (side x y M) ↪g G := Embedding.induce _
  let g : G.induce (side x y N) ↪g G := Embedding.induce _
  let a : G.Walk x y := p.map f.toHom
  let b : G.Walk x y := q.map g.toHom
  have hla : a.length = m := by
    change (p.map f.toHom).length = m
    rw [Walk.length_map, hpl]
  have hlb : b.length = n := by
    change (q.map g.toHom).length = n
    rw [Walk.length_map, hql]
  refine ⟨x, a.append b.reverse, ?_, ?_⟩
  · have ha : a.IsPath := hpp.map (f := f.toHom) f.injective
    have hb : b.IsPath := hqp.map (f := g.toHom) g.injective
    apply combine ha hb (by rwa [hla, hlb])
    intro v hva hvb
    have hm := supported_map p v hva
    have hn := supported_map q v hvb
    rcases hm with rfl | rfl | hm
    · exact Or.inl rfl
    · exact Or.inr rfl
    rcases hn with rfl | rfl | hn
    · exact Or.inl rfl
    · exact Or.inr rfl
    exact (Set.disjoint_left.mp hdisj hm hn).elim
  · simpa only [Walk.length_append, Walk.length_reverse, hla, hlb] using hd


private lemma good_in_induced {V : Type} [DecidableEq V] {G : SimpleGraph V} {B S : Finset V}
    {k : ℕ} (hd : ∀ v ∉ B, k ≤ (G.neighborSet v).ncard) (v : ↥(S : Set V))
    (hv : v.val ∉ boundary G B S) :
    k ≤ ((G.induce (S : Set V)).neighborSet v).ncard := by
  have hvB : v.val ∉ B := fun h => hv (mem_boundary.mpr ⟨v.property, Or.inl h⟩)
  have hs : G.neighborSet v.val ⊆ (S : Set V) := by
    intro w hw
    by_contra hwS
    exact hv (mem_boundary.mpr ⟨v.property, Or.inr ⟨w, hwS, hw⟩⟩)
  rw [ncard_induce v hs]
  exact hd v.val hvB

private lemma bad_subtype_card {V : Type} [DecidableEq V] {G : SimpleGraph V} {B S : Finset V} :
    ((boundary G B S).subtype (· ∈ (S : Set V))).card = (boundary G B S).card := by
  rw [Finset.card_subtype]
  congr 1
  apply Finset.filter_eq_self.mpr
  intro v hv
  exact (mem_boundary.mp hv).1



private def pathResidues {V : Type} (G : SimpleGraph V) (x y : V) : Set (ZMod 5) :=
  {r | ∃ p : G.Walk x y, p.IsPath ∧ (p.length : ZMod 5) = r}

section RemainingSteps

/-- Three distinct length residues for paths between two terminals, with at
most one exceptional internal vertex. The three-path case of
Chiba–Ota–Yamashita implies this residue form. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (x y z : V),
    4 ≤ Fintype.card V → x ≠ y → twoConn (addEdge G x y) →
    (∀ v, v ≠ x → v ≠ y → v ≠ z → 4 ≤ (G.neighborSet v).ncard) →
    3 ≤ (pathResidues G x y).ncard

/-- Cycles in the rooted case with a low-degree root and four-connected
root deletion. Connectivity is phrased by deletion of up to three vertices. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (c : V),
    twoConn G → 2 ≤ (G.neighborSet c).ncard → (G.neighborSet c).ncard ≤ 4 →
    (∀ v, v ≠ c → 5 ≤ (G.neighborSet v).ncard) →
    (∀ S : Finset V, S.card ≤ 3 → (G.induce {v : V | v ≠ c ∧ v ∉ S}).Connected) →
    HasCycle G 5

/-- The five-connected case. The connectivity condition is given by
deletion of at most four vertices, and the degree bound ensures the order. -/
def H3 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    Nonempty V → (∀ v, 5 ≤ (G.neighborSet v).ncard) →
    (∀ S : Finset V, S.card ≤ 4 → (G.induce {v : V | v ∉ S}).Connected) →
    HasCycle G 5

end RemainingSteps

private lemma conn_of_flat_delete {V : Type} {G : SimpleGraph V} {S : Set V} (w : S)
    (h : (G.induce {v : V | v ∈ S ∧ v ≠ w.val}).Connected) :
    ((G.induce S).induce {v : S | v ≠ w}).Connected := by
  let f : (G.induce {v : V | v ∈ S ∧ v ≠ w.val}) →g
      (G.induce S).induce {v : S | v ≠ w} :=
    ⟨fun v => ⟨⟨v, v.property.1⟩, fun he => v.property.2 (congrArg Subtype.val he)⟩,
      fun ha => ha⟩
  exact h.map f (fun ⟨v, hv⟩ =>
    ⟨⟨v.val, v.property, fun he => hv (Subtype.ext he)⟩, rfl⟩)

private lemma conn_flat_of_delete {V : Type} {G : SimpleGraph V} {S : Set V} (w : S)
    (h : ((G.induce S).induce {v : S | v ≠ w}).Connected) :
    (G.induce {v : V | v ∈ S ∧ v ≠ w.val}).Connected := by
  let f : ((G.induce S).induce {v : S | v ≠ w}) →g
      (G.induce {v : V | v ∈ S ∧ v ≠ w.val}) :=
    ⟨fun v => ⟨v.val.val, v.val.property, fun he => v.property (Subtype.ext he)⟩,
      fun ha => ha⟩
  exact h.map f (fun ⟨v, hv, hne⟩ =>
    ⟨⟨⟨v, hv⟩, fun he => hne (congrArg Subtype.val he)⟩, rfl⟩)

private lemma side_two_conn {V : Type} {G : SimpleGraph V} {x y : V}
    {M D : Set V} (hxy : x ≠ y) (hx : x ∈ D) (hy : y ∈ D) (hM : M ⊆ D)
    (hD : (G.induce D).Connected)
    (hdel : ∀ w ∈ side x y M, (G.induce {v : V | v ∈ D ∧ v ≠ w}).Connected)
    (hclosed : ∀ ⦃a b⦄, a ∈ M → b ∈ D → b ≠ x → b ≠ y → G.Adj a b → b ∈ M) :
    twoConn ((addEdge G x y).induce (side x y M)) := by
  have hsub : side x y M ⊆ D := by
    intro v hv
    rcases hv with rfl | rfl | hv
    · exact hx
    · exact hy
    · exact hM hv
  constructor
  · have hconn := sideConnected hxy hclosed hD (Or.inl rfl : x = x ∨ x = y) hx
    have heq : D ∩ side x y M = side x y M := Set.inter_eq_right.mpr hsub
    rwa [heq] at hconn
  · intro w
    apply conn_of_flat_delete
    let E := {v : V | v ∈ D ∧ v ≠ w.val}
    have hchoice : ∃ r, (r = x ∨ r = y) ∧ r ∈ E := by
      by_cases h : x = w.val
      · exact ⟨y, Or.inr rfl, hy, fun he => hxy (h.trans he.symm)⟩
      · exact ⟨x, Or.inl rfl, hx, h⟩
    obtain ⟨r, hr, hrE⟩ := hchoice
    have heq : E ∩ side x y M = {v : V | v ∈ side x y M ∧ v ≠ w.val} := by
      ext v
      change (v ∈ D ∧ v ≠ w.val) ∧ v ∈ side x y M ↔
        v ∈ side x y M ∧ v ≠ w.val
      exact ⟨fun ⟨⟨_, hn⟩, hs⟩ => ⟨hs, hn⟩, fun ⟨hs, hn⟩ => ⟨⟨hsub hs, hn⟩, hs⟩⟩
    rw [← heq]
    exact sideConnected hxy (fun {_ _} ha hb => hclosed ha hb.1)
      (hdel _ w.property) hr hrE

private lemma addEdge_induce {V : Type} {G : SimpleGraph V} {S : Set V}
    (x y : S) :
    addEdge (G.induce S) x y = (addEdge G x.val y.val).induce S := by
  ext a b
  change (G.Adj a.val b.val ∨
    (x ≠ y ∧ ((a = x ∧ b = y) ∨ (a = y ∧ b = x)))) ↔
    (G.Adj a.val b.val ∨
    (x.val ≠ y.val ∧ ((a.val = x.val ∧ b.val = y.val) ∨
      (a.val = y.val ∧ b.val = x.val))))
  rw [show (x ≠ y) ↔ x.val ≠ y.val from not_congr Subtype.ext_iff]
  simp only [Subtype.ext_iff]

private lemma connected_insert {V : Type} {G : SimpleGraph V} {S : Set V} {r u : V}
    (hS : (G.induce S).Connected) (hu : u ∈ S) (hru : G.Adj r u) :
    (G.induce (insert r S)).Connected := by
  let f : G.induce S →g G.induce (insert r S) :=
    ⟨fun v => ⟨v, Or.inr v.property⟩, fun h => h⟩
  let a : S := ⟨u, hu⟩
  rw [connected_iff_exists_forall_reachable]
  refine ⟨f a, fun v => ?_⟩
  rcases v.property with hv | hv
  · have he : (G.induce (insert r S)).Adj (f a) v := by
      change G.Adj u v.val
      simpa only [hv] using hru.symm
    exact he.reachable
  · exact (hS a ⟨v.val, hv⟩).map f

private lemma twoConn_insert {V : Type} {G : SimpleGraph V} {S : Set V} {r u v : V}
    (hS : twoConn (G.induce S)) (hr : r ∉ S) (hu : u ∈ S) (hv : v ∈ S)
    (huv : u ≠ v) (hru : G.Adj r u) (hrv : G.Adj r v) :
    twoConn (G.induce (insert r S)) := by
  refine ⟨connected_insert hS.1 hu hru, fun w => ?_⟩
  apply conn_of_flat_delete
  rcases w.property with hw | hw
  · have he : {a : V | a ∈ insert r S ∧ a ≠ w.val} = S := by
      ext a
      rw [Set.mem_ofPred_eq, Set.mem_insert_iff, hw]
      exact ⟨fun ⟨ha, hn⟩ => ha.resolve_left hn,
        fun ha => ⟨Or.inr ha, fun he => hr (he ▸ ha)⟩⟩
    rw [he]
    exact hS.1
  · have hwr : w.val ≠ r := fun he => hr (he ▸ hw)
    have he : {a : V | a ∈ insert r S ∧ a ≠ w.val} =
        insert r {a : V | a ∈ S ∧ a ≠ w.val} := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
      constructor
      · rintro ⟨ha | ha, hn⟩
        · exact Or.inl ha
        · exact Or.inr ⟨ha, hn⟩
      · rintro (rfl | ⟨ha, hn⟩)
        · exact ⟨Or.inl rfl, hwr.symm⟩
        · exact ⟨Or.inr ha, hn⟩
    rw [he]
    have hconn := conn_flat_of_delete (G := G) (⟨w.val, hw⟩ : S) (hS.2 ⟨w.val, hw⟩)
    by_cases huw : u = w.val
    · exact connected_insert hconn (show v ∈ {a | a ∈ S ∧ a ≠ w.val} from
        ⟨hv, fun h => huv (huw.trans h.symm)⟩) hrv
    · exact connected_insert hconn (show u ∈ {a | a ∈ S ∧ a ≠ w.val} from ⟨hu, huw⟩) hru

private lemma degree_bound {V : Type} [Finite V] {G : SimpleGraph V} {S : Set V}
    (v : S) (T : Set V) (h : G.neighborSet v.val ⊆ S ∪ T) :
    (G.neighborSet v.val).ncard ≤ ((G.induce S).neighborSet v).ncard + T.ncard := by
  have he : ((G.induce S).neighborSet v).ncard = (G.neighborSet v.val ∩ S).ncard := by
    apply Set.ncard_congr'
    exact {
      toFun := fun w => ⟨w.val.val, w.property, w.val.property⟩
      invFun := fun w => ⟨⟨w.val, w.property.2⟩, w.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [he]
  apply le_trans (Set.ncard_le_ncard (t := (G.neighborSet v.val ∩ S) ∪ T) ?_)
    (Set.ncard_union_le _ _)
  intro w hw
  rcases h hw with hS | hT
  · exact Or.inl ⟨hw, hS⟩
  · exact Or.inr hT

private lemma ncard_order_of_degree {V : Type} [Finite V] (G : SimpleGraph V) (v : V) :
    (G.neighborSet v).ncard + 1 ≤ (Set.univ : Set V).ncard := by
  rw [← Set.ncard_insert_of_notMem (show v ∉ G.neighborSet v from G.irrefl)]
  exact Set.ncard_le_ncard (Set.subset_univ _)

private lemma four_side {V : Type} [Finite V] {x y : V} {M : Set V}
    (hxy : x ≠ y) (hM : M.Nontrivial) (houtside : ∀ v ∈ M, v ≠ x ∧ v ≠ y) :
    4 ≤ (side x y M).ncard := by
  obtain ⟨u, hu, v, hv, huv⟩ := hM
  have hu' := houtside u hu
  have hv' := houtside v hv
  have hsub : ({x, y, u, v} : Set V) ⊆ side x y M := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr hu)
    · exact Or.inr (Or.inr hv)
  classical
  have hl := Set.ncard_le_ncard hsub
  have hcard : ({x, y, u, v} : Set V).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair huv]
    · simp [hu'.2.symm, hv'.2.symm]
    · simp [hxy, hu'.1.symm, hv'.1.symm]
  rwa [hcard] at hl

private lemma residues_on (h₁ : H1) {V : Type} [Fintype V] {G : SimpleGraph V}
    {x y z : V} {M : Set V} (hxy : x ≠ y) (horder : 4 ≤ (side x y M).ncard)
    (hconn : twoConn ((addEdge G x y).induce (side x y M)))
    (hdegree : ∀ v : side x y M, v.val ≠ x → v.val ≠ y → v.val ≠ z →
      4 ≤ ((G.induce (side x y M)).neighborSet v).ncard) :
    let S := side x y M
    3 ≤ (pathResidues (G.induce S) ⟨x, Or.inl rfl⟩ ⟨y, Or.inr (Or.inl rfl)⟩).ncard := by
  classical
  let S := side x y M
  let X : S := ⟨x, Or.inl rfl⟩
  let Y : S := ⟨y, Or.inr (Or.inl rfl)⟩
  let Z : S := if hz : z ∈ S then ⟨z, hz⟩ else X
  have hcard : 4 ≤ Fintype.card S := by rwa [Set.fintypeCard_eq_ncard]
  have hxy' : X ≠ Y := fun h => hxy (congrArg Subtype.val h)
  have hconn' : twoConn (addEdge (G.induce S) X Y) := by
    rw [addEdge_induce]
    exact hconn
  apply h₁ (G.induce S) X Y Z hcard hxy' hconn'
  intro v hx hy hz
  apply hdegree v (fun he => hx (Subtype.ext he)) (fun he => hy (Subtype.ext he))
  intro he
  have hzS : z ∈ S := he ▸ v.property
  apply hz
  rw [show Z = ⟨z, hzS⟩ by simp [Z, hzS]]
  exact Subtype.ext he

private lemma opposite_residues {A B : Set (ZMod 5)} (hA : 3 ≤ A.ncard) (hB : 3 ≤ B.ncard) :
    ∃ r ∈ A, -r ∈ B := by
  by_contra hn
  have hdisj : Disjoint A (Neg.neg '' B) := by
    rw [Set.disjoint_left]
    rintro r hr ⟨t, ht, rfl⟩
    exact hn ⟨-t, hr, by simpa using ht⟩
  have hle := Set.ncard_le_ncard (Set.subset_univ (A ∪ (Neg.neg '' B)))
  rw [Set.ncard_union_eq hdisj, Set.ncard_image_of_injective B neg_injective,
    Set.ncard_univ, Nat.card_eq_fintype_card, ZMod.card] at hle
  omega

private lemma join_residues {V : Type} {G : SimpleGraph V} {x y : V} {M N : Set V}
    (hxy : x ≠ y) (hdisj : Disjoint M N)
    (hp : 3 ≤ (pathResidues (G.induce (side x y M))
      ⟨x, Or.inl rfl⟩ ⟨y, Or.inr (Or.inl rfl)⟩).ncard)
    (hq : 3 ≤ (pathResidues (G.induce (side x y N))
      ⟨x, Or.inl rfl⟩ ⟨y, Or.inr (Or.inl rfl)⟩).ncard) :
    HasCycle G 5 := by
  obtain ⟨r, ⟨p, hpp, hpr⟩, ⟨q, hqp, hqr⟩⟩ := opposite_residues hp hq
  have hd : 5 ∣ p.length + q.length := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, hpr, hqr, add_neg_cancel]
  have hp0 : p.length ≠ 0 := fun h => hxy (congrArg Subtype.val (Walk.eq_of_length_eq_zero h))
  have hq0 : q.length ≠ 0 := fun h => hxy (congrArg Subtype.val (Walk.eq_of_length_eq_zero h))
  have hlong : 1 < p.length ∨ 1 < q.length := by
    have hm := Nat.dvd_iff_mod_eq_zero.mp hd
    omega
  exact glue_sides hdisj hlong ⟨p, hpp, rfl⟩ ⟨q, hqp, rfl⟩ hd

section Separations

variable {V : Type} [Fintype V] [DecidableEq V]

private def outside (C : Finset V) : Set V := {v | v ∉ C}

private structure Cut (G : SimpleGraph V) (C : Finset V) (P Q : Set V) : Prop where
  left_nonempty : P.Nonempty
  right_nonempty : Q.Nonempty
  left_outside : P ⊆ outside C
  right_outside : Q ⊆ outside C
  disjoint : Disjoint P Q
  cover : ∀ v ∉ C, v ∈ P ∨ v ∈ Q
  no_cross : ∀ a ∈ P, ∀ b ∈ Q, ¬ G.Adj a b

omit [Fintype V] [DecidableEq V] in
private lemma Cut.flip {G : SimpleGraph V} {C : Finset V} {P Q : Set V}
    (h : Cut G C P Q) : Cut G C Q P :=
  ⟨h.right_nonempty, h.left_nonempty, h.right_outside, h.left_outside, h.disjoint.symm,
    fun w hw => (h.cover w hw).symm, fun a ha b hb e => h.no_cross b hb a ha e.symm⟩

private lemma cut_of_not_connected {G : SimpleGraph V} {C : Finset V}
    (hne : (outside C).Nonempty) (h : ¬ (G.induce (outside C)).Connected) :
    ∃ P Q : Set V, Cut G C P Q := by
  classical
  let : Nonempty (outside C) := hne.to_subtype
  have hn : ∃ a b : outside C, ¬ (G.induce (outside C)).Reachable a b := by
    by_contra hh
    push Not at hh
    exact h (Connected.mk hh)
  obtain ⟨a, b, hab⟩ := hn
  let P := inComponent G a
  let Q := outside C \ P
  refine ⟨P, Q, ⟨a.val, a.property, .rfl⟩, ⟨b.val, b.property, ?_⟩, comp_subset G a,
    Set.sdiff_subset, Set.disjoint_sdiff_right, ?_, ?_⟩
  · exact fun hh => hab ((mem_comp G a b).mp hh)
  · intro v hv
    by_cases e : v ∈ P
    · exact Or.inl e
    · exact Or.inr ⟨hv, e⟩
  · intro u hu v hv huv
    exact hv.2 (comp_closed hu hv.1 huv)

omit [Fintype V] in
private lemma Cut.neighbor_subset {G : SimpleGraph V} {C : Finset V} {P Q : Set V}
    (h : Cut G C P Q) {v : V} (hv : v ∈ P) :
    G.neighborSet v ⊆ P ∪ (C : Set V) := by
  intro w hw
  by_cases hwC : w ∈ C
  · exact Or.inr hwC
  · exact (h.cover w hwC).elim Or.inl (fun hwQ => (h.no_cross v hv w hwQ hw).elim)

private lemma Cut.nontrivial_left {G : SimpleGraph V} {C : Finset V} {P Q : Set V}
    (h : Cut G C P Q) (hC : C.card ≤ 4)
    (hdegree : ∀ v ∉ C, 5 ≤ (G.neighborSet v).ncard) :
    P.Nontrivial := by
  obtain ⟨v, hv⟩ := h.left_nonempty
  by_contra hh
  have hsub : G.neighborSet v ⊆ (C : Set V) := by
    intro w hw
    rcases h.neighbor_subset hv hw with hwP | hwC
    · exact (hh ⟨v, hv, w, hwP, G.ne_of_adj hw⟩).elim
    · exact hwC
  have hd := (hdegree v (h.left_outside hv)).trans (Set.ncard_le_ncard hsub)
  rw [Set.ncard_coe_finset] at hd
  omega

private def sidesUniverse (C : Finset V) (x y : V) : Set V :=
  {v | v ∉ C ∨ v = x ∨ v = y}

private def deletionConn (G : SimpleGraph V) (D : Set V) : Prop :=
  (G.induce D).Connected ∧ ∀ w : V, (G.induce {v : V | v ∈ D ∧ v ≠ w}).Connected

omit [Fintype V] [DecidableEq V] in
private lemma deletionConn_univ {G : SimpleGraph V} (hG : twoConn G) :
    deletionConn G Set.univ := by
  refine ⟨?_, ?_⟩
  · let f : G →g G.induce Set.univ :=
      ⟨fun v => ⟨v, Set.mem_univ _⟩, fun h => h⟩
    exact hG.1.map f (fun v => ⟨v.val, rfl⟩)
  · intro w
    have he : {v : V | v ∈ (Set.univ : Set V) ∧ v ≠ w} = {v : V | v ≠ w} := by
      ext v
      simp
    rw [he]
    exact hG.2 w

omit [Fintype V] [DecidableEq V] in
private lemma Cut.side_conn {G : SimpleGraph V} {C : Finset V} {P Q : Set V} {x y : V}
    (h : Cut G C P Q) (hxy : x ≠ y)
    (hD : deletionConn G (sidesUniverse C x y)) :
    twoConn ((addEdge G x y).induce (side x y P)) := by
  refine side_two_conn hxy (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
    (fun w hw => Or.inl (h.left_outside hw)) hD.1 (fun w _ => hD.2 w) ?_
  intro a b ha hb hbx hby hab
  have hb' := (show b ∉ C ∨ b = x ∨ b = y from hb).resolve_right
    (not_or.mpr ⟨hbx, hby⟩)
  exact (h.cover b hb').resolve_right (fun hq => h.no_cross a ha b hq hab)

private lemma Cut.side_order {G : SimpleGraph V} {C : Finset V} {P Q M : Set V} {x y : V}
    (h : Cut G C P Q) (hxy : x ≠ y) (hx : x ∈ C) (hy : y ∈ C)
    (hC : C.card ≤ 4) (hdegree : ∀ v ∉ C, 5 ≤ (G.neighborSet v).ncard) (hM : P ⊆ M) :
    4 ≤ (side x y M).ncard := by
  have ha := four_side hxy (h.nontrivial_left hC hdegree)
    (fun _ hv => ⟨fun e => (h.left_outside hv) (e ▸ hx),
      fun e => (h.left_outside hv) (e ▸ hy)⟩)
  apply ha.trans (Set.ncard_le_ncard ?_)
  intro v hv
  exact hv.imp_right (Or.imp_right fun hp => hM hp)

private lemma Cut.side_degree {G : SimpleGraph V} {C : Finset V} {P Q M : Set V}
    {x y : V} (h : Cut G C P Q) (hM : P ⊆ M) (v : side x y M) (hv : v.val ∈ P)
    (T : Set V)
    (hcover : ∀ w ∈ C, G.Adj v.val w → w ∈ side x y M ∪ T) :
    (G.neighborSet v.val).ncard ≤ ((G.induce (side x y M)).neighborSet v).ncard + T.ncard := by
  apply degree_bound v T
  intro w hw
  rcases h.neighbor_subset hv hw with hwP | hwC
  · exact Or.inl (Or.inr (Or.inr (hM hwP)))
  · exact hcover w hwC hw

private lemma Cut.paths_one_omitted (h₁ : H1) {G : SimpleGraph V} {C : Finset V} {P Q : Set V}
    {x y c : V} (h : Cut G C P Q) (hxy : x ≠ y) (hx : x ∈ C) (hy : y ∈ C)
    (hC : C.card ≤ 4) (hdegree : ∀ v ∉ C, 5 ≤ (G.neighborSet v).ncard)
    (hD : deletionConn G (sidesUniverse C x y))
    (hcover : ∀ w ∈ C, w = x ∨ w = y ∨ w = c) :
    3 ≤ (pathResidues (G.induce (side x y P))
      ⟨x, Or.inl rfl⟩ ⟨y, Or.inr (Or.inl rfl)⟩).ncard := by
  apply residues_on h₁ (z := x) hxy (h.side_order hxy hx hy hC hdegree fun _ e => e)
    (h.side_conn hxy hD)
  intro v hvx hvy _
  have hp : v.val ∈ P := v.property.resolve_left hvx |>.resolve_left hvy
  have hdeg := hdegree v.val (h.left_outside hp)
  have hle := h.side_degree (fun _ e => e) v hp {c} (fun w hw _ => by
    rcases hcover w hw with e | e | e
    · exact Or.inl (Or.inl e)
    · exact Or.inl (Or.inr (Or.inl e))
    · exact Or.inr e)
  rw [Set.ncard_singleton] at hle
  omega

private lemma Cut.close_one_omitted (h₁ : H1) {G : SimpleGraph V} {C : Finset V} {P Q : Set V}
    {x y c : V} (h : Cut G C P Q) (hxy : x ≠ y) (hx : x ∈ C) (hy : y ∈ C)
    (hC : C.card ≤ 4) (hdegree : ∀ v ∉ C, 5 ≤ (G.neighborSet v).ncard)
    (hD : deletionConn G (sidesUniverse C x y))
    (hcover : ∀ w ∈ C, w = x ∨ w = y ∨ w = c) : HasCycle G 5 := by
  exact join_residues hxy h.disjoint
    (h.paths_one_omitted h₁ hxy hx hy hC hdegree hD hcover)
    (h.flip.paths_one_omitted h₁ hxy hx hy hC hdegree hD hcover)

omit [Fintype V] [DecidableEq V] in
private lemma side_insert_eq (x y r : V) (P : Set V) :
    side x y (insert r P) = insert r (side x y P) := by
  ext a
  change (a = x ∨ a = y ∨ a = r ∨ a ∈ P) ↔ (a = r ∨ a = x ∨ a = y ∨ a ∈ P)
  tauto

private lemma Cut.attach (h₁ : H1) {G : SimpleGraph V} {C : Finset V} {P Q : Set V}
    {x y r d : V} (h : Cut G C P Q) (hxy : x ≠ y) (hx : x ∈ C) (hy : y ∈ C)
    (hrx : r ≠ x) (hry : r ≠ y) (hrC : r ∈ C)
    (hC : C.card ≤ 4) (hdegree : ∀ v ∉ C, 5 ≤ (G.neighborSet v).ncard)
    (hD : deletionConn G (sidesUniverse C x y))
    (hcover : ∀ w ∈ C, w = x ∨ w = y ∨ w = r ∨ w = d)
    (hattach : (G.neighborSet r ∩ side x y P).Nontrivial) :
    3 ≤ (pathResidues (G.induce (side x y (insert r P)))
      ⟨x, Or.inl rfl⟩ ⟨y, Or.inr (Or.inl rfl)⟩).ncard := by
  have hr : r ∉ side x y P := fun he =>
    (h.left_outside (he.resolve_left hrx |>.resolve_left hry)) hrC
  have hn := h.side_conn hxy hD
  obtain ⟨u, hu, v, hv, huv⟩ := hattach
  have hcon : twoConn ((addEdge G x y).induce (side x y (insert r P))) := by
    rw [side_insert_eq]
    exact twoConn_insert hn hr hu.2 hv.2 huv (Or.inl hu.1) (Or.inl hv.1)
  apply residues_on h₁ (z := r) hxy
    (h.side_order hxy hx hy hC hdegree (fun _ e => Or.inr e)) hcon
  intro w hwx hwy hwr
  have hw : w.val ∈ P := w.property.resolve_left hwx |>.resolve_left hwy |>.resolve_left hwr
  have hd := hdegree w.val (h.left_outside hw)
  have hle := h.side_degree (fun _ e => Or.inr e) w hw {d} (fun z hz _ => by
    rcases hcover z hz with e | e | e | e
    · exact Or.inl (Or.inl e)
    · exact Or.inl (Or.inr (Or.inl e))
    · exact Or.inl (Or.inr (Or.inr (Or.inl e)))
    · exact Or.inr e)
  rw [Set.ncard_singleton] at hle
  omega

private lemma Cut.omit_if_one_attachment (h₁ : H1)
    {G : SimpleGraph V} {C : Finset V} {P Q : Set V}
    {x y r d : V} (h : Cut G C P Q) (hxy : x ≠ y) (hx : x ∈ C) (hy : y ∈ C)
    (hC : C.card ≤ 4) (hdegree : ∀ v ∉ C, 5 ≤ (G.neighborSet v).ncard)
    (hD : deletionConn G (sidesUniverse C x y))
    (hcover : ∀ w ∈ C, w = x ∨ w = y ∨ w = r ∨ w = d)
    (hattach : ¬ (G.neighborSet r ∩ side x y P).Nontrivial) :
    3 ≤ (pathResidues (G.induce (side x y P))
      ⟨x, Or.inl rfl⟩ ⟨y, Or.inr (Or.inl rfl)⟩).ncard := by
  classical
  let z : V := if hn : (G.neighborSet r ∩ side x y P).Nonempty then hn.choose else x
  have hz : ∀ w ∈ G.neighborSet r ∩ side x y P, w = z := by
    intro w hw
    have hn : (G.neighborSet r ∩ side x y P).Nonempty := ⟨w, hw⟩
    rw [show z = hn.choose by simp [z, hn]]
    by_contra he
    exact hattach ⟨w, hw, hn.choose, hn.choose_spec, he⟩
  apply residues_on h₁ (z := z) hxy (h.side_order hxy hx hy hC hdegree fun _ e => e)
    (h.side_conn hxy hD)
  intro w hwx hwy hwz
  have hw : w.val ∈ P := w.property.resolve_left hwx |>.resolve_left hwy
  have hd := hdegree w.val (h.left_outside hw)
  have hle := h.side_degree (fun _ e => e) w hw {d} (fun v hv hAdj => by
    rcases hcover v hv with e | e | e | e
    · exact Or.inl (Or.inl e)
    · exact Or.inl (Or.inr (Or.inl e))
    · subst v
      exact (hwz (hz w.val ⟨hAdj.symm, w.property⟩)).elim
    · exact Or.inr e)
  rw [Set.ncard_singleton] at hle
  omega

private lemma Cut.close_three (h₁ : H1) {G : SimpleGraph V} {C : Finset V} {P Q : Set V}
    {x y z c : V} (h : Cut G C P Q) (hxy : x ≠ y) (hx : x ∈ C) (hy : y ∈ C)
    (hzx : z ≠ x) (hzy : z ≠ y) (hz : z ∈ C)
    (hcx : c ≠ x) (hcy : c ≠ y) (hcz : c ≠ z) (hc : c ∈ C)
    (hC : C.card ≤ 4) (hdegree : ∀ v, v ≠ c → 5 ≤ (G.neighborSet v).ncard)
    (hD : deletionConn G (sidesUniverse C x y))
    (hcover : ∀ w ∈ C, w = x ∨ w = y ∨ w = z ∨ w = c) :
    HasCycle G 5 := by
  have hnormal : ∀ v ∉ C, 5 ≤ (G.neighborSet v).ncard :=
    fun v hv => hdegree v (fun e => hv (e ▸ hc))
  have swap (s : V) (hs : s ∈ C) : s = x ∨ s = y ∨ s = c ∨ s = z := by
    rcases hcover s hs with e | e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inr e))
    · exact Or.inr (Or.inr (Or.inl e))
  -- Reserve the third separator vertex for the side on which it has
  -- two neighbors. The original root is then available on the other side.
  have close {L R : Set V} (hLR : Cut G C L R)
      (hgood : (G.neighborSet z ∩ side x y L).Nontrivial) : HasCycle G 5 := by
    have hp :=
      hLR.attach h₁ hxy hx hy hzx hzy hz hC hnormal hD hcover hgood
    by_cases hb : (G.neighborSet c ∩ side x y R).Nontrivial
    · have hq :=
        hLR.flip.attach h₁ hxy hx hy hcx hcy hc hC hnormal hD swap hb
      apply join_residues (M := insert z L) (N := insert c R) hxy ?_ hp hq
      apply Set.disjoint_left.mpr
      intro v hv hw
      rcases hv with e | e <;> rcases hw with f | f
      · exact hcz (f.symm.trans e)
      · exact (hLR.right_outside f) (e ▸ hz)
      · exact (hLR.left_outside e) (f ▸ hc)
      · exact Set.disjoint_left.mp hLR.disjoint e f
    · have hq :=
        hLR.flip.omit_if_one_attachment h₁ hxy hx hy hC hnormal hD swap hb
      apply join_residues (M := insert z L) (N := R) hxy ?_ hp hq
      apply Set.disjoint_left.mpr
      intro v hv hw
      rcases hv with e | e
      · exact (hLR.right_outside hw) (e ▸ hz)
      · exact Set.disjoint_left.mp hLR.disjoint e hw
  by_cases hP : (G.neighborSet z ∩ side x y P).Nontrivial
  · exact close h hP
  by_cases hQ : (G.neighborSet z ∩ side x y Q).Nontrivial
  · exact close h.flip hQ
  have hncard {S : Set V} (hs : ¬ S.Nontrivial) : S.ncard ≤ 1 :=
    (Set.ncard_le_one (s := S)).mpr (fun a ha b hb => by
      by_contra he
      exact hs ⟨a, ha, b, hb, he⟩)
  have hsub : G.neighborSet z ⊆
      ((G.neighborSet z ∩ side x y P) ∪ (G.neighborSet z ∩ side x y Q)) ∪ {c} := by
    intro w hw
    by_cases hwC : w ∈ C
    · rcases hcover w hwC with e | e | e | e
      · exact Or.inl (Or.inl ⟨hw, Or.inl e⟩)
      · exact Or.inl (Or.inl ⟨hw, Or.inr (Or.inl e)⟩)
      · exact (G.ne_of_adj hw e.symm).elim
      · exact Or.inr e
    · rcases h.cover w hwC with e | e
      · exact Or.inl (Or.inl ⟨hw, Or.inr (Or.inr e)⟩)
      · exact Or.inl (Or.inr ⟨hw, Or.inr (Or.inr e)⟩)
  have hle := (Set.ncard_le_ncard hsub).trans (Set.ncard_union_le _ _)
  have hle' := Set.ncard_union_le (G.neighborSet z ∩ side x y P)
    (G.neighborSet z ∩ side x y Q)
  have hd := hdegree z hcz.symm
  have hp := hncard hP
  have hq := hncard hQ
  rw [Set.ncard_singleton] at hle
  omega

end Separations

section RootDeletion

variable {V : Type} [Fintype V] [DecidableEq V]

private def rootDeletion (G : SimpleGraph V) (c : V) (k : ℕ) : Prop :=
  ∀ S : Finset V, S.card ≤ k → (G.induce (outside (insert c S))).Connected

omit [Fintype V] in
private lemma rootDeletion_zero {G : SimpleGraph V} (hG : twoConn G) (c : V) :
    rootDeletion G c 0 := by
  intro S hs
  obtain rfl : S = ∅ := Finset.card_eq_zero.mp (by omega)
  have he : outside (insert c (∅ : Finset V)) = {v : V | v ≠ c} := by
    ext v
    simp [outside]
  rw [he]
  exact hG.2 c

omit [Fintype V] in
private lemma rootDeletion_succ {G : SimpleGraph V} {c : V} {k : ℕ} (h : rootDeletion G c k)
    (hs : ∀ S : Finset V, S.card = k + 1 → c ∉ S →
      (G.induce (outside (insert c S))).Connected) :
    rootDeletion G c (k + 1) := by
  intro S hS
  by_cases hc : c ∈ S
  · have he : insert c (S.erase c) = insert c S := by simp [hc]
    rw [← he]
    apply h
    rw [Finset.card_erase_of_mem hc]
    omega
  by_cases hsmall : S.card ≤ k
  · exact h S hsmall
  · exact hs S (by omega) hc

omit [Fintype V] in
private lemma deletionConn_root {G : SimpleGraph V} {c : V} {k : ℕ} {S : Finset V}
    (h : rootDeletion G c k) (hs : S.card + 1 ≤ k) :
    deletionConn G (outside (insert c S)) := by
  refine ⟨h S (by omega), fun v => ?_⟩
  have he : {w : V | w ∈ outside (insert c S) ∧ w ≠ v} =
      outside (insert c (insert v S)) := by
    ext w
    simp only [outside, Set.mem_ofPred_eq, Finset.mem_insert, not_or]
    tauto
  rw [he]
  apply h
  exact (Finset.card_insert_le v S).trans hs

omit [DecidableEq V] in
private lemma order_six {G : SimpleGraph V} {v : V} (hd : 5 ≤ (G.neighborSet v).ncard) :
    6 ≤ Fintype.card V := by
  have h := ncard_order_of_degree G v
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at h
  omega

omit [DecidableEq V] in
private lemma outside_nonempty {C : Finset V} (hV : 6 ≤ Fintype.card V) (hC : C.card ≤ 4) :
    (outside C).Nonempty := by
  have hn : ¬ (Finset.univ : Finset V) ⊆ C := by
    intro h
    have hm := Finset.card_le_card h
    rw [Finset.card_univ] at hm
    omega
  obtain ⟨v, _, hv⟩ := Finset.not_subset.mp hn
  exact ⟨v, hv⟩

private lemma rootDeletion_four (h₁ : H1) {G : SimpleGraph V} {c : V}
    (hG : twoConn G) (hV : 6 ≤ Fintype.card V)
    (hd : ∀ v, v ≠ c → 5 ≤ (G.neighborSet v).ncard)
    (hno : ¬ HasCycle G 5) : rootDeletion G c 3 := by
  classical
  have hC {S : Finset V} (hs : S.card ≤ 3) : (insert c S).card ≤ 4 :=
    (Finset.card_insert_le c S).trans (by omega)
  have hD {S : Finset V} (v : V) (hv : v ∉ insert c S) : 5 ≤ (G.neighborSet v).ncard :=
    hd v (fun e => hv (e ▸ Finset.mem_insert_self _ _))
  -- A new cut is examined with an ambient graph obtained by fewer deletions,
  -- which is already connected even after one further vertex is removed.
  have hzero := rootDeletion_zero hG c
  have hone : rootDeletion G c 1 := rootDeletion_succ hzero (by
    intro S hs hc
    obtain ⟨z, rfl⟩ := Finset.card_eq_one.mp hs
    have hcz : c ≠ z := by simpa using hc
    have hsmall : (insert c ({z} : Finset V)).card ≤ 4 := hC (by simp)
    by_contra hn
    obtain ⟨P, Q, h⟩ := cut_of_not_connected (outside_nonempty hV hsmall) hn
    have hscope : sidesUniverse (insert c ({z} : Finset V)) c z = Set.univ := by
      ext v
      simp only [sidesUniverse, Set.mem_ofPred_eq, Finset.mem_insert, Finset.mem_singleton,
        Set.mem_univ]
      tauto
    apply hno
    exact h.close_one_omitted h₁ hcz (by simp) (by simp) hsmall hD
      (by rw [hscope]; exact deletionConn_univ hG)
      (c := c) (fun w hw => by
        rcases Finset.mem_insert.mp hw with hw | hw
        · exact Or.inl hw
        · exact Or.inr (Or.inl (Finset.mem_singleton.mp hw))))
  have htwo : rootDeletion G c 2 := rootDeletion_succ hone (by
    intro S hs hc
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hs
    have hsmall : (insert c ({x, y} : Finset V)).card ≤ 4 := hC (by simp [hxy])
    by_contra hn
    obtain ⟨P, Q, h⟩ := cut_of_not_connected (outside_nonempty hV hsmall) hn
    have hc' : c ≠ x ∧ c ≠ y := by simpa using hc
    have hscope : sidesUniverse (insert c ({x, y} : Finset V)) x y =
        outside (insert c (∅ : Finset V)) := by
      ext v
      simp only [sidesUniverse, outside, Set.mem_ofPred_eq, Finset.mem_insert,
        Finset.mem_singleton, Finset.notMem_empty, or_false]
      constructor
      · rintro (hv | rfl | rfl)
        · exact fun he => hv (Or.inl he)
        · exact hc'.1.symm
        · exact hc'.2.symm
      · intro hv
        tauto
    apply hno
    exact h.close_one_omitted h₁ hxy (by simp) (by simp) hsmall hD
      (by rw [hscope]; exact deletionConn_root hone (by simp))
      (c := c) (fun w hw => by simpa [or_comm, or_left_comm] using hw))
  apply rootDeletion_succ htwo
  intro S hs hc
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hs
  have hc' : c ≠ x ∧ c ≠ y ∧ c ≠ z := by simpa using hc
  have hsmall : (insert c ({x, y, z} : Finset V)).card ≤ 4 := hC (by simp [hxy, hxz, hyz])
  by_contra hn
  obtain ⟨P, Q, h⟩ := cut_of_not_connected (outside_nonempty hV hsmall) hn
  have hscope : sidesUniverse (insert c ({x, y, z} : Finset V)) x y =
      outside (insert c ({z} : Finset V)) := by
    ext v
    simp only [sidesUniverse, outside, Set.mem_ofPred_eq, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (hv | rfl | rfl)
      · exact fun he => hv (he.imp_right (Or.inr ∘ Or.inr))
      · exact not_or.mpr ⟨hc'.1.symm, hxz⟩
      · exact not_or.mpr ⟨hc'.2.1.symm, hyz⟩
    · intro hv
      tauto
  apply hno
  exact h.close_three h₁ hxy (by simp) (by simp) hxz.symm hyz.symm (by simp)
    hc'.1 hc'.2.1 hc'.2.2 (by simp) hsmall hd
    (by rw [hscope]; exact deletionConn_root htwo (by simp))
    (fun w hw => by simpa [or_comm, or_left_comm] using hw)

private lemma root_two_neighbors {G : SimpleGraph V} (hG : twoConn G)
    (hV : 6 ≤ Fintype.card V) (c : V) : 2 ≤ (G.neighborSet c).ncard := by
  classical
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨y, hcy⟩ := hG.1.preconnected.exists_adj_of_nontrivial c
  let D : Set V := {v | v ≠ y}
  have hcard : D.ncard + 1 = Fintype.card V := by
    have he : D = (Set.univ : Set V) \ {y} := by ext v; simp [D]
    rw [he, Set.ncard_sdiff_singleton_add_one (Set.mem_univ _), Set.ncard_univ,
      Nat.card_eq_fintype_card]
  let : Nontrivial D := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [Set.fintypeCard_eq_ncard]
    omega)
  obtain ⟨z, hz⟩ := (hG.2 y).preconnected.exists_adj_of_nontrivial (⟨c, hcy.ne⟩ : D)
  by_contra hn
  have hle : (G.neighborSet c).ncard ≤ 1 := by omega
  have he := (Set.ncard_le_one (s := G.neighborSet c)).mp hle y hcy z.val hz
  exact z.property he.symm

private lemma full_five_connected (h₁ : H1) {G : SimpleGraph V} (hG : twoConn G)
    (hV : 6 ≤ Fintype.card V) (hd : ∀ v, 5 ≤ (G.neighborSet v).ncard)
    (hno : ¬ HasCycle G 5) (S : Finset V) (hS : S.card ≤ 4) :
    (G.induce (outside S)).Connected := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨c, hc⟩ := hne
    have hcard : (S.erase c).card ≤ 3 := by rw [Finset.card_erase_of_mem hc]; omega
    have he := rootDeletion_four h₁ (c := c) hG hV (fun v _ => hd v) hno (S.erase c) hcard
    rwa [Finset.insert_erase hc] at he
  · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp hne
    let f : G →g G.induce (outside (∅ : Finset V)) :=
      ⟨fun v => ⟨v, Finset.notMem_empty v⟩, fun h => h⟩
    exact hG.1.map f (fun v => ⟨v.val, rfl⟩)

end RootDeletion

theorem main : H1 → H2 → H3 → type_of% @Arxiv.«2605.02731».dean_conjecture.variants.five := by
  classical
  intro h₁ h₂ h₃ V _ _ G _ hG
  have hV : Nonempty V := by
    rcases isEmpty_or_nonempty V with hE | hN
    · exfalso
      have : Subsingleton V := ⟨fun a => isEmptyElim a⟩
      have h0 := G.minDegree_of_subsingleton
      omega
    · exact hN
  obtain ⟨v⟩ := hV
  have hd : ∀ w ∉ (∅ : Finset V), 5 ≤ (G.neighborSet w).ncard := by
    intro w _
    rw [← Set.fintypeCard_eq_ncard, card_neighborSet_eq_degree]
    exact hG.trans (G.minDegree_le_degree w)
  obtain ⟨S, hS, hboundary, w, hw, hgood⟩ :=
    exists_twoConn_core G ∅ 5 1 (by decide) (by decide) (by simp) hd ⟨v, by simp⟩
  let J := G.induce (S : Set V)
  let bad := (boundary G ∅ S).subtype (· ∈ (S : Set V))
  have hbad : bad.card ≤ 1 := by rwa [bad_subtype_card]
  let wS : ↥(S : Set V) := ⟨w, hw⟩
  let c : ↥(S : Set V) := if h : bad.Nonempty then h.choose else wS
  have hbound : ∀ a, a ≠ c → 5 ≤ (J.neighborSet a).ncard := by
    intro a ha
    apply good_in_induced hd a
    intro ham
    have hab := Finset.mem_subtype.mpr ham
    have hne : bad.Nonempty := ⟨a, hab⟩
    apply ha
    rw [show c = hne.choose by simp [c, hne]]
    exact Finset.card_le_one.mp hbad _ hab _ hne.choose_spec
  have horder : 6 ≤ Fintype.card (S : Set V) :=
    order_six (G := J) (v := wS) (good_in_induced hd wS hgood)
  have hJ : HasCycle J 5 := by
    by_contra hno
    by_cases hc : 5 ≤ (J.neighborSet c).ncard
    · have hfull : ∀ a, 5 ≤ (J.neighborSet a).ncard := by
        intro a
        by_cases he : a = c
        · simpa only [he] using hc
        · exact hbound a he
      exact hno (h₃ J ⟨wS⟩ hfull (full_five_connected h₁ hS horder hfull hno))
    · apply hno
      apply h₂ J c hS (root_two_neighbors hS horder c) (by omega) hbound
      intro T hT
      have hcut := rootDeletion_four h₁ hS horder hbound hno T hT
      have he : outside (insert c T) = {v | v ≠ c ∧ v ∉ T} := by
        ext a
        simp [outside]
      rwa [he] at hcut
  obtain ⟨u, p, hp, hlen⟩ := cycle_lift (Embedding.induce (G := G) (S : Set V)) hJ
  exact ⟨p.length, ⟨u, p, hp, rfl⟩, hlen⟩

end OMA.R_Arxiv_2605_02731_dean_conjecture_variants_five_R1
