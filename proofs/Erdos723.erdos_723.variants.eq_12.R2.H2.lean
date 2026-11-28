import OMAReductions.R_Erdos723_erdos_723_variants_eq_12_R2
import Mathlib

/-!
# Step H2 of reduction Erdos723.erdos_723.variants.eq_12.R2

Written with Claude Code (AI-assisted).

Every net of order 12 and degree 11 extends to a net of degree 13. This is the case
n = 12, d = 2 of Bruck's completion theorem (R. H. Bruck, Finite nets II, Pacific J. Math. 13
(1963)); for deficiency two it also follows from Shrikhande's characterisation of the
lattice graph. The statement and its attribution to Bruck come from the reduction file by
@sntntHb. The proof below is self-contained and reuses no other Lean development.

Outline. Call two cells unjoined when no line of the net contains both, and let `ag x z`
be the number of classes whose line through `x` contains `z`.
* Double counting gives `∑ z, ag x z = 132` and `∑ z, ag x z * ag y z = 110 + 12 * ag y x`.
  Hence the graph of unjoined pairs is regular of degree 22, two unjoined cells have 10 common
  neighbours and two joined cells have 2.
* A cell has no three pairwise joined neighbours (`claw`): their neighbourhoods inside the
  22 neighbours would need 27 cells among the 19 remaining ones.
* So the 22 neighbours of a cell split into two cliques of size 11 with no edges between
  them (`split`, `compl_clique`). A transversal is a clique of 12 cells.
* Every cell off a transversal is unjoined to one of its cells (`hit_lemma`), and the cells
  attached to a fixed cell of a transversal form a transversal again (`row_isT`).
* Take the two transversals through one cell. Sending a cell to its attachment point on each
  gives two new coordinates, orthogonal to the old classes and to each other (`graph_core`).
-/

open Finset

namespace Bruck12

section Graph

variable {X : Type} [Fintype X] [DecidableEq X] (adj : X → X → Prop) [DecidableRel adj]

/-- Neighbourhood of a point in the graph of unjoined pairs. -/
def nb (x : X) : Finset X := univ.filter (fun z => adj x z)

/-- The facts about the graph of unjoined pairs of a net of order 12 and degree 11
that the completion argument uses. -/
structure Hyp : Prop where
  symm : ∀ x y, adj x y → adj y x
  irrefl : ∀ x, ¬ adj x x
  deg : ∀ x, (nb adj x).card = 22
  lam : ∀ x y, adj x y → (nb adj x ∩ nb adj y).card = 10
  mu : ∀ x y, x ≠ y → ¬ adj x y → (nb adj x ∩ nb adj y).card = 2
  hit : ∀ T : Finset X, T.card = 12 → (∀ p ∈ T, ∀ q ∈ T, p ≠ q → adj p q) →
    ∀ x, x ∉ T → ∃ t ∈ T, adj t x

/-- A transversal: twelve pairwise unjoined points. -/
def IsT (T : Finset X) : Prop := T.card = 12 ∧ ∀ p ∈ T, ∀ q ∈ T, p ≠ q → adj p q

variable {adj}

omit [DecidableEq X] in
lemma mem_nb {x y : X} : y ∈ nb adj x ↔ adj x y := by
  simp [nb]

lemma claw (h : Hyp adj) {x y1 y2 y3 : X} (h1 : adj x y1) (h2 : adj x y2) (h3 : adj x y3)
    (n12 : y1 ≠ y2) (n13 : y1 ≠ y3) (n23 : y2 ≠ y3)
    (a12 : ¬ adj y1 y2) (a13 : ¬ adj y1 y3) (a23 : ¬ adj y2 y3) : False := by
  have m1 : y1 ∈ nb adj x := mem_nb.2 h1
  have m2 : y2 ∈ (nb adj x).erase y1 := mem_erase.2 ⟨n12.symm, mem_nb.2 h2⟩
  have m3 : y3 ∈ ((nb adj x).erase y1).erase y2 :=
    mem_erase.2 ⟨n23.symm, mem_erase.2 ⟨n13.symm, mem_nb.2 h3⟩⟩
  have c1 := card_erase_of_mem m1
  have c2 := card_erase_of_mem m2
  have c3 := card_erase_of_mem m3
  have c0 := h.deg x
  have sub : ∀ y, ¬ adj y y1 → ¬ adj y y2 → ¬ adj y y3 →
      nb adj x ∩ nb adj y ⊆ (((nb adj x).erase y1).erase y2).erase y3 := by
    intro y b1 b2 b3 z hz
    rw [mem_inter, mem_nb, mem_nb] at hz
    refine mem_erase.2 ⟨?_, mem_erase.2 ⟨?_, mem_erase.2 ⟨?_, mem_nb.2 hz.1⟩⟩⟩
    · intro e; rw [e] at hz; exact b3 hz.2
    · intro e; rw [e] at hz; exact b2 hz.2
    · intro e; rw [e] at hz; exact b1 hz.2
  have inter : ∀ y y', y ≠ y' → ¬ adj y y' → adj x y → adj x y' →
      ((nb adj x ∩ nb adj y) ∩ (nb adj x ∩ nb adj y')).card ≤ 1 := by
    intro y y' hne hna hy hy'
    have hsub : (nb adj x ∩ nb adj y) ∩ (nb adj x ∩ nb adj y') ⊆
        (nb adj y ∩ nb adj y').erase x := by
      intro z hz
      simp only [mem_inter, mem_nb] at hz
      refine mem_erase.2 ⟨?_, mem_inter.2 ⟨mem_nb.2 hz.1.2, mem_nb.2 hz.2.2⟩⟩
      intro e
      rw [e] at hz
      exact h.irrefl _ hz.1.1
    have hx : x ∈ nb adj y ∩ nb adj y' :=
      mem_inter.2 ⟨mem_nb.2 (h.symm _ _ hy), mem_nb.2 (h.symm _ _ hy')⟩
    have e1 := card_le_card hsub
    have e2 := card_erase_of_mem hx
    have e3 := h.mu y y' hne hna
    omega
  have sub1 := sub y1 (h.irrefl y1) a12 a13
  have sub2 := sub y2 (fun k => a12 (h.symm _ _ k)) (h.irrefl y2) a23
  have sub3 := sub y3 (fun k => a13 (h.symm _ _ k)) (fun k => a23 (h.symm _ _ k)) (h.irrefl y3)
  have i12 := inter y1 y2 n12 a12 h1 h2
  have i13 := inter y1 y3 n13 a13 h1 h3
  have i23 := inter y2 y3 n23 a23 h2 h3
  have l1 := h.lam x y1 h1
  have l2 := h.lam x y2 h2
  have l3 := h.lam x y3 h3
  have u12 := card_union_add_card_inter (nb adj x ∩ nb adj y1) (nb adj x ∩ nb adj y2)
  have u3 := card_union_add_card_inter ((nb adj x ∩ nb adj y1) ∪ (nb adj x ∩ nb adj y2))
    (nb adj x ∩ nb adj y3)
  have i3 : (((nb adj x ∩ nb adj y1) ∪ (nb adj x ∩ nb adj y2)) ∩ (nb adj x ∩ nb adj y3)).card
      ≤ 2 := by
    rw [union_inter_distrib_right]
    have := card_union_le ((nb adj x ∩ nb adj y1) ∩ (nb adj x ∩ nb adj y3))
      ((nb adj x ∩ nb adj y2) ∩ (nb adj x ∩ nb adj y3))
    omega
  have su3 := card_le_card (union_subset (union_subset sub1 sub2) sub3)
  omega

lemma clique_nb (h : Hyp adj) {x : X} {K : Finset X} (hK : K ⊆ nb adj x) (hc : K.card = 11)
    (hcl : ∀ p ∈ K, ∀ q ∈ K, p ≠ q → adj p q) {k : X} (hk : k ∈ K) :
    K.erase k = nb adj x ∩ nb adj k := by
  apply eq_of_subset_of_card_le
  · intro z hz
    rw [mem_erase] at hz
    exact mem_inter.2 ⟨hK hz.2, mem_nb.2 (hcl k hk z hz.2 hz.1.symm)⟩
  · have e1 := h.lam x k (mem_nb.1 (hK hk))
    have e2 := card_erase_of_mem hk
    omega

lemma split (h : Hyp adj) {x y : X} (hy : adj x y) :
    ((nb adj x \ nb adj y).erase y).card = 11 ∧
    ∀ p ∈ (nb adj x \ nb adj y).erase y, ∀ q ∈ (nb adj x \ nb adj y).erase y,
      p ≠ q → adj p q := by
  constructor
  · have e1 := card_sdiff_add_card_inter (nb adj x) (nb adj y)
    have e2 := h.lam x y hy
    have e3 := h.deg x
    have hmem : y ∈ nb adj x \ nb adj y :=
      mem_sdiff.2 ⟨mem_nb.2 hy, fun k => h.irrefl y (mem_nb.1 k)⟩
    have e4 := card_erase_of_mem hmem
    omega
  · intro p hp q hq hpq
    simp only [mem_erase, mem_sdiff, mem_nb] at hp hq
    by_contra hna
    exact claw h hy hp.2.1 hq.2.1 (Ne.symm hp.1) (Ne.symm hq.1) hpq hp.2.2 hq.2.2 hna

lemma compl_clique (h : Hyp adj) {x : X} {K : Finset X} (hK : K ⊆ nb adj x) (hc : K.card = 11)
    (hcl : ∀ p ∈ K, ∀ q ∈ K, p ≠ q → adj p q) :
    (nb adj x \ K).card = 11 ∧
    (∀ p ∈ nb adj x \ K, ∀ q ∈ nb adj x \ K, p ≠ q → adj p q) ∧
    (∀ k ∈ K, ∀ z ∈ nb adj x \ K, ¬ adj k z) := by
  have hno : ∀ k ∈ K, ∀ z ∈ nb adj x \ K, ¬ adj k z := by
    intro k hk z hz hkz
    rw [mem_sdiff] at hz
    have hzk : z ∈ K.erase k := by
      rw [clique_nb h hK hc hcl hk]
      exact mem_inter.2 ⟨hz.1, mem_nb.2 hkz⟩
    exact hz.2 (mem_of_mem_erase hzk)
  refine ⟨?_, ?_, hno⟩
  · have e1 := card_sdiff_add_card_inter (nb adj x) K
    rw [inter_eq_right.2 hK] at e1
    have e3 := h.deg x
    omega
  · obtain ⟨y, hy⟩ : K.Nonempty := card_pos.1 (by omega)
    have hxy : adj x y := mem_nb.1 (hK hy)
    have hsub : ∀ p ∈ nb adj x \ K, p ∈ (nb adj x \ nb adj y).erase y := by
      intro p hp
      have hp' := mem_sdiff.1 hp
      refine mem_erase.2 ⟨?_, mem_sdiff.2 ⟨hp'.1, fun k => hno y hy p hp (mem_nb.1 k)⟩⟩
      intro e
      rw [e] at hp'
      exact hp'.2 hy
    intro p hp q hq hpq
    exact (split h hxy).2 p (hsub p hp) q (hsub q hq) hpq

lemma isT_insert (h : Hyp adj) {x : X} {K : Finset X} (hK : K ⊆ nb adj x) (hc : K.card = 11)
    (hcl : ∀ p ∈ K, ∀ q ∈ K, p ≠ q → adj p q) : IsT adj (insert x K) := by
  have hx : x ∉ K := fun k => h.irrefl x (mem_nb.1 (hK k))
  refine ⟨by rw [card_insert_of_notMem hx, hc], ?_⟩
  intro p hp q hq hpq
  rcases mem_insert.1 hp with hp' | hp' <;> rcases mem_insert.1 hq with hq' | hq'
  · exact (hpq (hp'.trans hq'.symm)).elim
  · rw [hp']; exact mem_nb.1 (hK hq')
  · rw [hq']; exact h.symm _ _ (mem_nb.1 (hK hp'))
  · exact hcl p hp' q hq' hpq

lemma row_isT (h : Hyp adj) {T : Finset X} (hT : IsT adj T) {c : X} (hc : c ∈ T) :
    IsT adj (insert c (nb adj c \ T.erase c)) := by
  have hK : T.erase c ⊆ nb adj c := fun z hz =>
    mem_nb.2 (hT.2 c hc z (mem_of_mem_erase hz) (ne_of_mem_erase hz).symm)
  have hcard : (T.erase c).card = 11 := by
    have e1 := card_erase_of_mem hc
    have e2 := hT.1
    omega
  have hcl : ∀ p ∈ T.erase c, ∀ q ∈ T.erase c, p ≠ q → adj p q := fun p hp q hq hpq =>
    hT.2 p (mem_of_mem_erase hp) q (mem_of_mem_erase hq) hpq
  obtain ⟨k1, k2, -⟩ := compl_clique h hK hcard hcl
  exact isT_insert h sdiff_subset k1 k2

lemma common_mem (h : Hyp adj) {T : Finset X} (hT : IsT adj T) {p q z : X} (hp : p ∈ T)
    (hq : q ∈ T) (hpq : p ≠ q) (zp : adj z p) (zq : adj z q) : z ∈ T := by
  have hK : T.erase p ⊆ nb adj p := fun w hw =>
    mem_nb.2 (hT.2 p hp w (mem_of_mem_erase hw) (ne_of_mem_erase hw).symm)
  have hcard : (T.erase p).card = 11 := by
    have e1 := card_erase_of_mem hp
    have e2 := hT.1
    omega
  have hcl : ∀ a ∈ T.erase p, ∀ b ∈ T.erase p, a ≠ b → adj a b := fun a ha b hb hab =>
    hT.2 a (mem_of_mem_erase ha) b (mem_of_mem_erase hb) hab
  have hqK : q ∈ T.erase p := mem_erase.2 ⟨hpq.symm, hq⟩
  have hz : z ∈ (T.erase p).erase q := by
    rw [clique_nb h hK hcard hcl hqK]
    exact mem_inter.2 ⟨mem_nb.2 (h.symm _ _ zp), mem_nb.2 (h.symm _ _ zq)⟩
  exact mem_of_mem_erase (mem_of_mem_erase hz)

lemma third_mem (h : Hyp adj) {T1 T2 : Finset X} (h1 : IsT adj T1) (h2 : IsT adj T2)
    {p q r : X} (hpq : p ≠ q) (p1 : p ∈ T1) (q1 : q ∈ T1) (p2 : p ∈ T2) (q2 : q ∈ T2)
    (r2 : r ∈ T2) : r ∈ T1 := by
  by_cases hrp : r = p
  · rw [hrp]; exact p1
  by_cases hrq : r = q
  · rw [hrq]; exact q1
  exact common_mem h h1 p1 q1 hpq (h2.2 r r2 p p2 hrp) (h2.2 r r2 q q2 hrq)

lemma exists_rho (h : Hyp adj) {T : Finset X} (hT : IsT adj T) :
    ∃ ρ : X → X, (∀ p, ρ p ∈ T) ∧ (∀ p, p ∈ T → ρ p = p) ∧ (∀ p, p ∉ T → adj (ρ p) p) := by
  have key : ∀ p, ∃ c, c ∈ T ∧ (p ∈ T → c = p) ∧ (p ∉ T → adj c p) := by
    intro p
    by_cases hp : p ∈ T
    · exact ⟨p, hp, fun _ => rfl, fun k => (k hp).elim⟩
    · obtain ⟨t, ht, hadj⟩ := h.hit T hT.1 hT.2 p hp
      exact ⟨t, ht, fun k => (hp k).elim, fun _ => hadj⟩
  choose ρ h1 h2 h3 using key
  exact ⟨ρ, h1, h2, h3⟩

lemma rho_row {T : Finset X} {ρ : X → X} (h2 : ∀ p, p ∈ T → ρ p = p)
    (h3 : ∀ p, p ∉ T → adj (ρ p) p) (p : X) :
    p ∈ insert (ρ p) (nb adj (ρ p) \ T.erase (ρ p)) := by
  by_cases hp : p ∈ T
  · rw [h2 p hp]; exact mem_insert_self _ _
  · exact mem_insert_of_mem (mem_sdiff.2 ⟨mem_nb.2 (h3 p hp), fun k => hp (mem_of_mem_erase k)⟩)

lemma graph_core (h : Hyp adj) (o : X) : ∃ (C R : Finset X) (ρ κ : X → X),
    C.card = 12 ∧ R.card = 12 ∧ (∀ p, ρ p ∈ C) ∧ (∀ p, κ p ∈ R) ∧
    (∀ p q, ρ p = ρ q → p ≠ q → adj p q) ∧ (∀ p q, κ p = κ q → p ≠ q → adj p q) ∧
    (∀ p q, ρ p = ρ q → κ p = κ q → p = q) := by
  obtain ⟨y, hy⟩ : (nb adj o).Nonempty := card_pos.1 (by rw [h.deg o]; omega)
  have hoy : adj o y := mem_nb.1 hy
  obtain ⟨M, hMsub, mc, mcl⟩ : ∃ M : Finset X, M ⊆ nb adj o ∧ M.card = 11 ∧
      ∀ p ∈ M, ∀ q ∈ M, p ≠ q → adj p q :=
    ⟨(nb adj o \ nb adj y).erase y, fun z hz => (mem_sdiff.1 (mem_of_mem_erase hz)).1,
      (split h hoy).1, (split h hoy).2⟩
  obtain ⟨cc, ccl, hno⟩ := compl_clique h hMsub mc mcl
  have hR : IsT adj (insert o M) := isT_insert h hMsub mc mcl
  have hC : IsT adj (insert o (nb adj o \ M)) := isT_insert h sdiff_subset cc ccl
  obtain ⟨ρ, r1, r2, r3⟩ := exists_rho h hC
  obtain ⟨κ, k1, k2, k3⟩ := exists_rho h hR
  have oC : o ∈ insert o (nb adj o \ M) := mem_insert_self _ _
  have oR : o ∈ insert o M := mem_insert_self _ _
  refine ⟨insert o (nb adj o \ M), insert o M, ρ, κ, hC.1, hR.1, r1, k1, ?_, ?_, ?_⟩
  · intro p q e hpq
    have hp := rho_row r2 r3 p
    have hq := rho_row r2 r3 q
    rw [← e] at hq
    exact (row_isT h hC (r1 p)).2 p hp q hq hpq
  · intro p q e hpq
    have hp := rho_row k2 k3 p
    have hq := rho_row k2 k3 q
    rw [← e] at hq
    exact (row_isT h hR (k1 p)).2 p hp q hq hpq
  · intro p q e1 e2
    by_contra hpq
    have hp1 := rho_row r2 r3 p
    have hq1 := rho_row r2 r3 q
    rw [← e1] at hq1
    have hp2 := rho_row k2 k3 p
    have hq2 := rho_row k2 k3 q
    rw [← e2] at hq2
    have T1 := row_isT h hC (r1 p)
    have T2 := row_isT h hR (k1 p)
    have rT1 := third_mem h T1 T2 hpq hp1 hq1 hp2 hq2 (mem_insert_self _ _)
    have cT2 := third_mem h T2 T1 hpq hp2 hq2 hp1 hq1 (mem_insert_self _ _)
    rcases mem_insert.1 rT1 with hrc | hr
    · have hcR : ρ p ∈ insert o M := by rw [← hrc]; exact k1 p
      have hco : ρ p = o := by
        rcases mem_insert.1 (r1 p) with e | e
        · exact e
        · rcases mem_insert.1 hcR with e' | e'
          · exact e'
          · exact ((mem_sdiff.1 e).2 e').elim
      have allR : ∀ t, t ∈ insert (ρ p) (nb adj (ρ p) \ (insert o (nb adj o \ M)).erase (ρ p)) →
          t ∈ insert o M := by
        intro t ht
        rw [hco] at ht
        rcases mem_insert.1 ht with e | e
        · rw [e]; exact oR
        · have ht' := mem_sdiff.1 e
          have hto : t ≠ o := by
            intro e'
            rw [e'] at ht'
            exact h.irrefl _ (mem_nb.1 ht'.1)
          have htC : t ∉ insert o (nb adj o \ M) := fun k => ht'.2 (mem_erase.2 ⟨hto, k⟩)
          by_contra htR
          exact htC (mem_insert_of_mem (mem_sdiff.2 ⟨ht'.1, fun k => htR (mem_insert_of_mem k)⟩))
      have ep := k2 p (allR p hp1)
      have eq' := k2 q (allR q hq1)
      exact hpq (ep.symm.trans (e2.trans eq'))
    · have hr' := mem_sdiff.1 hr
      have adjcr : adj (ρ p) (κ p) := mem_nb.1 hr'.1
      have hne : κ p ≠ ρ p := by
        intro e
        rw [e] at adjcr
        exact h.irrefl _ adjcr
      have rnC : κ p ∉ insert o (nb adj o \ M) := fun k => hr'.2 (mem_erase.2 ⟨hne, k⟩)
      have rM : κ p ∈ M := by
        rcases mem_insert.1 (k1 p) with e | e
        · exact (rnC (by rw [e]; exact oC)).elim
        · exact e
      have cnR : ρ p ∉ insert o M := by
        rcases mem_insert.1 cT2 with e | e
        · exact (hne e.symm).elim
        · exact fun k => (mem_sdiff.1 e).2 (mem_erase.2 ⟨hne.symm, k⟩)
      have cS : ρ p ∈ nb adj o \ M := by
        rcases mem_insert.1 (r1 p) with e | e
        · exact (cnR (by rw [e]; exact oR)).elim
        · exact e
      exact hno (κ p) rM (ρ p) cS (h.symm _ _ adjcr)

theorem graph_main (h : Hyp adj) (o : X) : ∃ ρ κ : X → Fin 12,
    (∀ p q, ρ p = ρ q → p ≠ q → adj p q) ∧ (∀ p q, κ p = κ q → p ≠ q → adj p q) ∧
    (∀ p q, ρ p = ρ q → κ p = κ q → p = q) := by
  obtain ⟨C, R, ρ, κ, hC, hR, r1, k1, a1, a2, a3⟩ := graph_core h o
  obtain ⟨eC⟩ : Nonempty ({x // x ∈ C} ≃ Fin 12) := ⟨Finset.equivFinOfCardEq hC⟩
  obtain ⟨eR⟩ : Nonempty ({x // x ∈ R} ≃ Fin 12) := ⟨Finset.equivFinOfCardEq hR⟩
  have iC : ∀ p q, eC ⟨ρ p, r1 p⟩ = eC ⟨ρ q, r1 q⟩ → ρ p = ρ q := fun p q e =>
    congrArg Subtype.val (eC.injective e)
  have iR : ∀ p q, eR ⟨κ p, k1 p⟩ = eR ⟨κ q, k1 q⟩ → κ p = κ q := fun p q e =>
    congrArg Subtype.val (eR.injective e)
  exact ⟨fun p => eC ⟨ρ p, r1 p⟩, fun p => eR ⟨κ p, k1 p⟩,
    fun p q e hpq => a1 p q (iC p q e) hpq, fun p q e hpq => a2 p q (iR p q e) hpq,
    fun p q e1 e2 => a3 p q (iC p q e1) (iR p q e2)⟩

end Graph

section Net

variable (f : Fin 11 → Fin 12 × Fin 12 → Fin 12)

/-- Number of parallel classes in which `z` lies on the line through `x`. -/
def ag (x z : Fin 12 × Fin 12) : ℕ := (univ.filter (fun i => f i z = f i x)).card

/-- Two points are unjoined when no line of the net contains both. -/
def adjN (p q : Fin 12 × Fin 12) : Prop := ag f p q = 0

instance : DecidableRel (adjN f) := fun p q => inferInstanceAs (Decidable (ag f p q = 0))

variable {f}

lemma ag_eq_sum (x z : Fin 12 × Fin 12) : ag f x z = ∑ i, if f i z = f i x then 1 else 0 := by
  unfold ag
  rw [card_filter]

lemma ag_eq_zero {x z : Fin 12 × Fin 12} : ag f x z = 0 ↔ ∀ i, f i z ≠ f i x := by
  unfold ag
  rw [card_eq_zero, filter_eq_empty_iff]
  simp

lemma ag_self (x : Fin 12 × Fin 12) : ag f x x = 11 := by
  simp [ag]

lemma ag_comm (x z : Fin 12 × Fin 12) : ag f x z = ag f z x := by
  unfold ag
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and]
  exact eq_comm

lemma hit_lemma (T : Finset (Fin 12 × Fin 12)) (hT : T.card = 12)
    (hcl : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → ag f p q = 0) (x : Fin 12 × Fin 12) :
    ∃ t ∈ T, ag f t x = 0 := by
  by_contra hcon
  have h1 : ∀ t ∈ T, 1 ≤ ag f t x := fun t ht =>
    Nat.one_le_iff_ne_zero.2 (fun e => hcon ⟨t, ht, e⟩)
  have h2 : 12 ≤ ∑ t ∈ T, ag f t x := by
    have e := sum_le_sum h1
    simp only [sum_const, smul_eq_mul, mul_one, hT] at e
    exact e
  have h4 : ∀ i : Fin 11, (∑ t ∈ T, if f i x = f i t then 1 else 0) ≤ 1 := by
    intro i
    rw [← card_filter, card_le_one]
    intro t ht t' ht'
    simp only [mem_filter] at ht ht'
    by_contra hne
    exact (ag_eq_zero.1 (hcl t ht.1 t' ht'.1 hne)) i (ht'.2.symm.trans ht.2)
  have h3 : ∑ t ∈ T, ag f t x ≤ 11 := by
    simp_rw [ag_eq_sum]
    rw [sum_comm]
    have e := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin 11))) => h4 i)
    simp only [sum_const, smul_eq_mul, mul_one, card_univ, Fintype.card_fin] at e
    exact e
  omega

variable (hf : ∀ i j, i ≠ j → Function.Injective (fun x => (f i x, f j x)))
include hf

lemma ag_le_one {x z : Fin 12 × Fin 12} (hxz : x ≠ z) : ag f x z ≤ 1 := by
  unfold ag
  rw [card_le_one]
  intro i hi j hj
  by_contra hij
  simp only [mem_filter, mem_univ, true_and] at hi hj
  have e : (fun x => (f i x, f j x)) z = (fun x => (f i x, f j x)) x := by
    show (f i z, f j z) = (f i x, f j x)
    rw [hi, hj]
  exact hxz (hf i j hij e).symm

lemma fiber_card (i : Fin 11) (v : Fin 12) :
    (univ.filter (fun x : Fin 12 × Fin 12 => f i x = v)).card = 12 := by
  obtain ⟨j, hij⟩ : ∃ j : Fin 11, i ≠ j := by
    by_cases h0 : i = 0
    · exact ⟨1, by rw [h0]; decide⟩
    · exact ⟨0, h0⟩
  have hle : ∀ w : Fin 12, (univ.filter (fun x : Fin 12 × Fin 12 => f i x = w)).card ≤ 12 := by
    intro w
    have hinj : Set.InjOn (f j) (univ.filter (fun x : Fin 12 × Fin 12 => f i x = w) :
        Finset (Fin 12 × Fin 12)) := by
      intro a ha b hb hab
      have ha := (mem_filter.1 (mem_coe.1 ha)).2
      have hb := (mem_filter.1 (mem_coe.1 hb)).2
      apply hf i j hij
      show (f i a, f j a) = (f i b, f j b)
      rw [ha, hb, hab]
    have e := card_le_card_of_injOn (t := (univ : Finset (Fin 12))) (f j)
      (fun a _ => mem_univ (f j a)) hinj
    simpa using e
  have hsum : ∑ w : Fin 12, (univ.filter (fun x : Fin 12 × Fin 12 => f i x = w)).card = 144 := by
    rw [← card_eq_sum_card_fiberwise (fun x _ => mem_univ (f i x))]
    simp
  by_contra hne
  have hlt : (univ.filter (fun x : Fin 12 × Fin 12 => f i x = v)).card < 12 :=
    lt_of_le_of_ne (hle v) hne
  have e := sum_lt_sum (fun w (_ : w ∈ (univ : Finset (Fin 12))) => hle w) ⟨v, mem_univ v, hlt⟩
  simp only [sum_const, smul_eq_mul, card_univ, Fintype.card_fin] at e
  omega

lemma sum_ag (x : Fin 12 × Fin 12) : ∑ z, ag f x z = 132 := by
  simp_rw [ag_eq_sum]
  rw [sum_comm]
  have e : ∀ i : Fin 11, (∑ z : Fin 12 × Fin 12, if f i z = f i x then 1 else 0) = 12 := by
    intro i
    rw [← card_filter]
    exact fiber_card hf i (f i x)
  simp_rw [e]
  simp

lemma inter_card {i j : Fin 11} (hij : i ≠ j) (v w : Fin 12) :
    (univ.filter (fun z : Fin 12 × Fin 12 => f i z = v ∧ f j z = w)).card = 1 := by
  have hb : Function.Bijective (fun x : Fin 12 × Fin 12 => (f i x, f j x)) :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hf i j hij, rfl⟩
  obtain ⟨z, hz⟩ := hb.2 (v, w)
  have hz1 : f i z = v := congrArg Prod.fst hz
  have hz2 : f j z = w := congrArg Prod.snd hz
  rw [card_eq_one]
  refine ⟨z, ?_⟩
  ext z'
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    apply hb.1
    show (f i z', f j z') = (f i z, f j z)
    rw [h1, h2, hz1, hz2]
  · intro e
    rw [e]
    exact ⟨hz1, hz2⟩

lemma sum_ag_mul (x y : Fin 12 × Fin 12) :
    ∑ z, ag f x z * ag f y z = 110 + 12 * ag f y x := by
  have h1 : ∀ z, ag f x z * ag f y z =
      ∑ i, ∑ j, if f i z = f i x ∧ f j z = f j y then 1 else 0 := by
    intro z
    rw [ag_eq_sum, ag_eq_sum, sum_mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    by_cases c1 : f i z = f i x <;> by_cases c2 : f j z = f j y <;> simp [c1, c2]
  simp_rw [h1]
  rw [sum_comm]
  have h2 : ∀ i : Fin 11, (∑ z : Fin 12 × Fin 12, ∑ j : Fin 11,
      if f i z = f i x ∧ f j z = f j y then 1 else 0) =
      10 + if f i x = f i y then 12 else 0 := by
    intro i
    rw [sum_comm, ← add_sum_erase univ _ (mem_univ i)]
    have hA : (∑ z : Fin 12 × Fin 12, if f i z = f i x ∧ f i z = f i y then 1 else 0) =
        if f i x = f i y then 12 else 0 := by
      by_cases he : f i x = f i y
      · rw [if_pos he]
        have e : (∑ z : Fin 12 × Fin 12, if f i z = f i x ∧ f i z = f i y then 1 else 0) =
            ∑ z : Fin 12 × Fin 12, if f i z = f i x then 1 else 0 := by
          refine sum_congr rfl fun z _ => ?_
          by_cases hz : f i z = f i x
          · rw [if_pos hz, if_pos ⟨hz, hz.trans he⟩]
          · rw [if_neg hz, if_neg (fun k => hz k.1)]
        rw [e, ← card_filter]
        exact fiber_card hf i (f i x)
      · rw [if_neg he]
        apply sum_eq_zero
        intro z _
        rw [if_neg]
        rintro ⟨e1, e2⟩
        exact he (e1.symm.trans e2)
    have hB : (∑ j ∈ univ.erase i, ∑ z : Fin 12 × Fin 12,
        if f i z = f i x ∧ f j z = f j y then 1 else 0) = 10 := by
      have e : ∀ j ∈ univ.erase i, (∑ z : Fin 12 × Fin 12,
          if f i z = f i x ∧ f j z = f j y then 1 else 0) = 1 := by
        intro j hj
        rw [← card_filter]
        exact inter_card hf (ne_of_mem_erase hj).symm _ _
      rw [sum_congr rfl e]
      simp
    rw [hA, hB, add_comm]
  simp_rw [h2]
  rw [sum_add_distrib]
  have e : (∑ i : Fin 11, if f i x = f i y then 12 else 0) = 12 * ag f y x := by
    rw [ag_eq_sum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    by_cases c : f i x = f i y <;> simp [c]
  rw [e]
  simp

lemma deg_card (x : Fin 12 × Fin 12) :
    (univ.filter (fun z => ag f x z = 0)).card = 22 := by
  have hp : ∀ z, ag f x z + (if ag f x z = 0 then 1 else 0) =
      1 + (if z = x then 10 else 0) := by
    intro z
    by_cases hz : z = x
    · rw [hz, ag_self]
      simp
    · have b := ag_le_one hf (Ne.symm hz)
      rw [if_neg hz]
      by_cases h0 : ag f x z = 0
      · rw [if_pos h0, h0]
      · rw [if_neg h0]
        omega
  have hs : ∑ z, (ag f x z + (if ag f x z = 0 then 1 else 0)) =
      ∑ z, (1 + (if z = x then 10 else 0)) := sum_congr rfl fun z _ => hp z
  rw [sum_add_distrib, sum_add_distrib, sum_ag hf, ← card_filter] at hs
  simp only [sum_const, smul_eq_mul, mul_one, card_univ, Fintype.card_prod, Fintype.card_fin,
    sum_ite_eq', mem_univ, if_true] at hs
  omega

lemma lam_card {x y : Fin 12 × Fin 12} (hxy : ag f x y = 0) :
    (univ.filter (fun z => ag f x z = 0 ∧ ag f y z = 0)).card = 10 := by
  have hne : x ≠ y := by
    intro e
    rw [e, ag_self] at hxy
    omega
  have hyx : ag f y x = 0 := by rw [ag_comm]; exact hxy
  have hp : ∀ z, (if ag f x z = 0 ∧ ag f y z = 0 then 1 else 0) + ag f x z + ag f y z =
      1 + ag f x z * ag f y z + (if z = x then 10 else 0) + (if z = y then 10 else 0) := by
    intro z
    by_cases hzx : z = x
    · rw [hzx, ag_self, hyx, if_neg hne]
      simp
    · by_cases hzy : z = y
      · rw [hzy, ag_self, hxy, if_neg (Ne.symm hne)]
        simp
      · have b1 := ag_le_one hf (Ne.symm hzx)
        have b2 := ag_le_one hf (Ne.symm hzy)
        rw [if_neg hzx, if_neg hzy]
        have c1 : ag f x z = 0 ∨ ag f x z = 1 := by omega
        have c2 : ag f y z = 0 ∨ ag f y z = 1 := by omega
        rcases c1 with c1 | c1 <;> rcases c2 with c2 | c2 <;> rw [c1, c2] <;> simp
  have hs : ∑ z, ((if ag f x z = 0 ∧ ag f y z = 0 then 1 else 0) + ag f x z + ag f y z) =
      ∑ z, (1 + ag f x z * ag f y z + (if z = x then 10 else 0) + (if z = y then 10 else 0)) :=
    sum_congr rfl fun z _ => hp z
  simp only [sum_add_distrib] at hs
  rw [sum_ag hf, sum_ag hf, sum_ag_mul hf, hyx, ← card_filter] at hs
  simp only [sum_const, smul_eq_mul, mul_one, card_univ, Fintype.card_prod, Fintype.card_fin,
    sum_ite_eq', mem_univ, if_true] at hs
  omega

lemma mu_card {x y : Fin 12 × Fin 12} (hxy : ag f x y = 1) :
    (univ.filter (fun z => ag f x z = 0 ∧ ag f y z = 0)).card = 2 := by
  have hyx : ag f y x = 1 := by rw [ag_comm]; exact hxy
  have hp : ∀ z, (if ag f x z = 0 ∧ ag f y z = 0 then 1 else 0) + ag f x z + ag f y z =
      1 + ag f x z * ag f y z := by
    intro z
    by_cases hzx : z = x
    · rw [hzx, ag_self, hyx]
      simp
    · by_cases hzy : z = y
      · rw [hzy, ag_self, hxy]
        simp
      · have b1 := ag_le_one hf (Ne.symm hzx)
        have b2 := ag_le_one hf (Ne.symm hzy)
        have c1 : ag f x z = 0 ∨ ag f x z = 1 := by omega
        have c2 : ag f y z = 0 ∨ ag f y z = 1 := by omega
        rcases c1 with c1 | c1 <;> rcases c2 with c2 | c2 <;> rw [c1, c2] <;> simp
  have hs : ∑ z, ((if ag f x z = 0 ∧ ag f y z = 0 then 1 else 0) + ag f x z + ag f y z) =
      ∑ z, (1 + ag f x z * ag f y z) := sum_congr rfl fun z _ => hp z
  simp only [sum_add_distrib] at hs
  rw [sum_ag hf, sum_ag hf, sum_ag_mul hf, hyx, ← card_filter] at hs
  simp only [sum_const, smul_eq_mul, mul_one, card_univ, Fintype.card_prod, Fintype.card_fin]
    at hs
  omega

lemma hyp_of_net : Hyp (adjN f) := by
  have hint : ∀ x y : Fin 12 × Fin 12, nb (adjN f) x ∩ nb (adjN f) y =
      univ.filter (fun z => ag f x z = 0 ∧ ag f y z = 0) := by
    intro x y
    ext z
    simp only [mem_inter, mem_nb, mem_filter, mem_univ, true_and]
    exact Iff.rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y h
    show ag f y x = 0
    rw [ag_comm]
    exact h
  · intro x h
    have h' : ag f x x = 0 := h
    rw [ag_self] at h'
    omega
  · intro x
    exact deg_card hf x
  · intro x y h
    rw [hint]
    exact lam_card hf h
  · intro x y hne h
    have b := ag_le_one hf hne
    have h1 : ag f x y = 1 := by
      have h' : ¬ ag f x y = 0 := h
      omega
    rw [hint]
    exact mu_card hf h1
  · intro T hT hcl x _
    exact hit_lemma T hT hcl x

end Net

/-- The thirteen parallel classes: the eleven given ones and the two new ones. -/
def mkG (f : Fin 11 → Fin 12 × Fin 12 → Fin 12) (ρ κ : Fin 12 × Fin 12 → Fin 12) (i : Fin 13) :
    Fin 12 × Fin 12 → Fin 12 :=
  if h : i.val < 11 then f ⟨i.val, h⟩ else if i.val = 11 then ρ else κ

theorem bruck (f : Fin 11 → Fin 12 × Fin 12 → Fin 12)
    (hf : ∀ i j, i ≠ j → Function.Injective (fun x => (f i x, f j x))) :
    ∃ g : Fin 13 → Fin 12 × Fin 12 → Fin 12,
      ∀ i j, i ≠ j → Function.Injective (fun x => (g i x, g j x)) := by
  obtain ⟨ρ, κ, hρ, hκ, hinj⟩ := graph_main (hyp_of_net hf) ((0 : Fin 12), (0 : Fin 12))
  have fρ : ∀ (i : Fin 11) (u : Fin 12 × Fin 12 → Fin 12),
      (∀ p q, u p = u q → p ≠ q → adjN f p q) →
      Function.Injective (fun x => (f i x, u x)) := by
    intro i u hu p q e
    by_contra hpq
    have e1 : f i p = f i q := congrArg Prod.fst e
    have e2 : u p = u q := congrArg Prod.snd e
    exact ag_eq_zero.1 (hu p q e2 hpq) i e1.symm
  have sw : ∀ u v : Fin 12 × Fin 12 → Fin 12, Function.Injective (fun x => (u x, v x)) →
      Function.Injective (fun x => (v x, u x)) := by
    intro u v h p q e
    apply h
    have e1 : v p = v q := congrArg Prod.fst e
    have e2 : u p = u q := congrArg Prod.snd e
    show (u p, v p) = (u q, v q)
    rw [e1, e2]
  have key : ∀ i j : Fin 13, i.val < j.val →
      Function.Injective (fun x => (mkG f ρ κ i x, mkG f ρ κ j x)) := by
    intro i j hij
    by_cases hj : j.val < 11
    · have hi : i.val < 11 := by omega
      have e1 : mkG f ρ κ i = f ⟨i.val, hi⟩ := dif_pos hi
      have e2 : mkG f ρ κ j = f ⟨j.val, hj⟩ := dif_pos hj
      rw [e1, e2]
      refine hf _ _ ?_
      intro e
      rw [Fin.mk.injEq] at e
      omega
    · by_cases hj11 : j.val = 11
      · have hi : i.val < 11 := by omega
        have e1 : mkG f ρ κ i = f ⟨i.val, hi⟩ := dif_pos hi
        have e2 : mkG f ρ κ j = ρ := by
          unfold mkG
          rw [dif_neg hj, if_pos hj11]
        rw [e1, e2]
        exact fρ _ ρ hρ
      · have e2 : mkG f ρ κ j = κ := by
          unfold mkG
          rw [dif_neg hj, if_neg hj11]
        by_cases hi : i.val < 11
        · have e1 : mkG f ρ κ i = f ⟨i.val, hi⟩ := dif_pos hi
          rw [e1, e2]
          exact fρ _ κ hκ
        · have hi11 : i.val = 11 := by
            have hjl := j.isLt
            omega
          have e1 : mkG f ρ κ i = ρ := by
            unfold mkG
            rw [dif_neg hi, if_pos hi11]
          rw [e1, e2]
          intro p q e
          exact hinj p q (congrArg Prod.fst e) (congrArg Prod.snd e)
  refine ⟨mkG f ρ κ, fun i j hij => ?_⟩
  rcases Nat.lt_or_gt_of_ne (fun e => hij (Fin.ext e)) with h | h
  · exact key i j h
  · exact sw _ _ (key j i h)

end Bruck12

theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_eq_12_R2.H2 := by
  intro f hf
  exact Bruck12.bruck f hf
