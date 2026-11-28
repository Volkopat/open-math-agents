import OMAStatements.S_gillibert_geodesic_deletion

/-!
This reduction proves the complete case, Cayley graphs of elementary abelian
2-groups and 3-groups, and Cartesian product closure. Strong induction leaves H1,
the core outside these families and without a Cartesian
factor of order at least three, and H2, the known Cartesian-factor transitivity
theorem, which still needs formalization. The full conjecture remains open.

Proof: a shortest word in an elementary abelian 2-group has independent steps.
Extend those steps to a basis in the generating set. Its edges form a spanning
hypercube containing the geodesic. A translated and coordinate-permuted cube
geodesic is a partial prefix chain. The complement of that chain is connected,
as proved here by an explicit inversion-preserving routing argument.
The Cartesian closure proof uses geodesic projections, contiguous fibre segments,
and a surviving copy of the second factor joining the connected fibre complements.
Over F3, subtract a normalized linear relation from the all-one step coefficients.
At least one coefficient vanishes; all others are 0, 1 or -1, yielding a shorter
signed-generator walk. Independent steps extend to a basis and a spanning ternary
Hamming graph. This graph has a complete three-vertex factor, so product closure
proves the ternary family.

All proof code and the spanning-basis argument were written independently here.
Sources and context:
* Luc Gillibert and GPT 6 Astra, The Geodesic Deletion Conjecture (17 November
  2026), unrefereed, https://github.com/Gillibert/ConjecturesGillibert/blob/main/geodesic_deletion_conjecture.tex.
  This supplies the conjecture and the complete-graph example; statement PR #334.
  The formal special-case proofs below were written independently.
* Anna Bernasconi, Chris Godsil and Simone Severini, Quantum networks on cubelike
  graphs, Physical Review A 78 (2008), 052320, DOI 10.1103/PhysRevA.78.052320
  (refereed). This supplies standard cubelike terminology, not a deletion theorem.
* Abolghasem Soltani and Ali Iranmanesh, On the Edge Wiener Index, Filomat 28:3
  (2014), 541-549, DOI 10.2298/FIL1403541S (refereed), Theorem 2.14.
  This states the standard Cartesian-factor transitivity result. H2 retains its
  needed direction as an explicit hypothesis; no proof of H2 is claimed here.
* R. Hammack, W. Imrich and S. Klavzar, Handbook of Product Graphs, 2nd ed.,
  CRC Press (2011), Cartesian products and vertex-transitivity of factors.
  Scholarly monograph; refereeing status not verified.
No mathematical result from another agent's note or proof PR is used.
-/

namespace OMA.R_gillibert_geodesic_deletion_R1

open SimpleGraph
open scoped symmDiff BigOperators

set_option maxHeartbeats 8000000 in
/-- All cubelike graphs satisfy geodesic deletion. Auxiliary data are local lets. -/
lemma cubelike_family {V : Type} [Fintype V] [AddCommGroup V] [Module (ZMod 2) V]
    (S : Set V) (hconn : (SimpleGraph.fromRel (fun x y : V => y-x ∈ S)).Connected)
    (hcard : 3 ≤ Fintype.card V) {x y : V}
    (p : (SimpleGraph.fromRel (fun x y : V => y-x ∈ S)).Walk x y)
    (hp : p.length=(SimpleGraph.fromRel (fun x y : V => y-x ∈ S)).dist x y) :
    ((SimpleGraph.fromRel (fun x y : V => y-x ∈ S)).induce {v | v ∉ p.support}).Connected := by
  classical
  let HC_cube {α : Type} [LinearOrder α] : SimpleGraph (Finset α) :=
    SimpleGraph.fromRel (fun s t => ∃ a, a ∉ s ∧ insert a s = t)

  let HC_Inversion {α : Type} [LinearOrder α] (s : Finset α) : Prop := ∃ a b, a < b ∧ a ∉ s ∧ b ∈ s

  let HC_outside {α : Type} [LinearOrder α] : SimpleGraph {s : Finset α // HC_Inversion s} := HC_cube.induce {s | HC_Inversion s}

  have HC_cube_adj_erase {α : Type} [LinearOrder α] (s : Finset α) (a : α) (ha : a ∈ s) : HC_cube.Adj s (s.erase a) := by
    refine ⟨(Finset.erase_ne_self.mpr ha).symm,Or.inr ?_⟩
    exact ⟨a,Finset.notMem_erase a s,Finset.insert_erase ha⟩

  have HC_cube_adj_insert {α : Type} [LinearOrder α] (s : Finset α) (a : α) (ha : a ∉ s) : HC_cube.Adj s (insert a s) := by
    refine ⟨?_,Or.inl ⟨a,ha,rfl⟩⟩
    intro h
    have : a ∈ s := h ▸ Finset.mem_insert_self a s
    exact ha this

  have HC_inversion_anchors {α : Type} [LinearOrder α] {lo hi : α} (hlt : lo < hi) {s : Finset α}
      (hlo : lo ∉ s) (hhi : hi ∈ s) : HC_Inversion s := ⟨lo,hi,hlt,hlo,hhi⟩

  have HC_anchored_reachable {α : Type} [LinearOrder α] {lo hi : α} (hlt : lo < hi) (s : Finset α)
      (hlo : lo ∉ s) (hhi : hi ∈ s) :
      HC_outside.Reachable ⟨s,HC_inversion_anchors hlt hlo hhi⟩
        ⟨{hi},HC_inversion_anchors hlt (by simpa using hlt.ne) (by simp)⟩ := by
    revert hlo hhi
    refine Finset.strongInductionOn s ?_
    intro s ih hlo hhi
    by_cases heq : s = {hi}
    · subst s; exact Reachable.refl _
    · obtain ⟨a,ha,hane⟩ : ∃ a ∈ s, a ≠ hi := by
        by_contra! h
        apply heq
        apply Finset.eq_singleton_iff_unique_mem.mpr
        exact ⟨hhi,h⟩
      have hlo' : lo ∉ s.erase a := fun h => hlo (Finset.mem_of_mem_erase h)
      have hhi' : hi ∈ s.erase a := Finset.mem_erase.mpr ⟨hane.symm,hhi⟩
      have step : HC_outside.Adj ⟨s,HC_inversion_anchors hlt hlo hhi⟩
          ⟨s.erase a,HC_inversion_anchors hlt hlo' hhi'⟩ := HC_cube_adj_erase s a ha
      exact step.reachable.trans (ih (s.erase a) (Finset.erase_ssubset ha) hlo' hhi')

  have HC_all_inversions_reachable {α : Type} [LinearOrder α] {lo hi : α} (hlt : lo < hi)
      (hbot : ∀ a : α, lo ≤ a)
      (s : Finset α) (hs : HC_Inversion s) :
      HC_outside.Reachable ⟨s,hs⟩
        ⟨{hi},HC_inversion_anchors hlt (by simpa using hlt.ne) (by simp)⟩ := by
    obtain ⟨a,b,hab,ha,hb⟩ := hs
    have hbne : b ≠ lo := (lt_of_le_of_lt (hbot a) hab).ne'
    let t := s.erase lo
    have htinv : HC_Inversion t := ⟨a,b,hab,by simp [t,ha],by simp [t,hbne,hb]⟩
    have hlo : lo ∉ t := Finset.notMem_erase lo s
    have first : HC_outside.Reachable ⟨s,⟨a,b,hab,ha,hb⟩⟩ ⟨t,htinv⟩ := by
      by_cases h : lo ∈ s
      · exact (show HC_outside.Adj ⟨s,⟨a,b,hab,ha,hb⟩⟩ ⟨t,htinv⟩ from
          HC_cube_adj_erase s lo h).reachable
      · have heq : t = s := Finset.erase_eq_of_notMem h
        subst t
        simpa [Finset.erase_eq_of_notMem h] using (Reachable.refl (G := HC_outside) ⟨s,⟨a,b,hab,ha,hb⟩⟩)
    let z := insert hi t
    have hzlo : lo ∉ z := by simp [z,hlt.ne,hlo]
    have hzhi : hi ∈ z := Finset.mem_insert_self hi t
    have hzinv := HC_inversion_anchors hlt hzlo hzhi
    have second : HC_outside.Reachable ⟨t,htinv⟩ ⟨z,hzinv⟩ := by
      by_cases h : hi ∈ t
      · have heq : z = t := Finset.insert_eq_of_mem h
        subst z
        simpa [Finset.insert_eq_of_mem h] using (Reachable.refl (G := HC_outside) ⟨t,htinv⟩)
      · exact (show HC_outside.Adj ⟨t,htinv⟩ ⟨z,hzinv⟩ from HC_cube_adj_insert t hi h).reachable
    exact first.trans (second.trans (HC_anchored_reachable hlt z hzlo hzhi))

  have HC_outside_connected {α : Type} [LinearOrder α] {lo hi : α} (hlt : lo < hi)
      (hbot : ∀ a : α, lo ≤ a) :
      (HC_outside (α := α)).Connected := by
    apply (HC_outside.connected_iff_exists_forall_reachable).mpr
    refine ⟨⟨{hi},HC_inversion_anchors hlt (by simpa using hlt.ne) (by simp)⟩,?_⟩
    intro s
    exact (HC_all_inversions_reachable hlt hbot s.val s.property).symm

  let HC_initialSegment  (n k : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => i.val < k)

  have HC_inversion_not_prefix  {n : ℕ} (s : Finset (Fin n)) (hs : HC_Inversion s) (k : ℕ) :
      s ≠ HC_initialSegment n k := by
    obtain ⟨a,b,hab,ha,hb⟩ := hs
    intro heq
    rw [heq] at ha hb
    simp only [HC_initialSegment,Finset.mem_filter,Finset.mem_univ,true_and] at ha hb
    exact ha (lt_trans hab hb)

  have HC_not_inversion_iff_prefix  {n : ℕ} (s : Finset (Fin n)) :
      ¬ HC_Inversion s ↔ ∃ k ≤ n, s = HC_initialSegment n k := by
    classical
    constructor
    · intro hs
      let missing := Finset.univ \ s
      by_cases hmiss : missing.Nonempty
      · let a := missing.min' hmiss
        have hamiss : a ∈ missing := Finset.min'_mem missing hmiss
        have ha : a ∉ s := (Finset.mem_sdiff.mp hamiss).2
        refine ⟨a.val,Nat.le_of_lt a.isLt,?_⟩
        ext b
        simp only [HC_initialSegment,Finset.mem_filter,Finset.mem_univ,true_and]
        constructor
        · intro hb
          by_contra hlt
          have hab : a ≤ b := Nat.le_of_not_gt hlt
          rcases eq_or_lt_of_le hab with heq | hgt
          · exact ha (heq ▸ hb)
          · exact hs ⟨a,b,hgt,ha,hb⟩
        · intro hb
          by_contra hnot
          have hbmiss : b ∈ missing := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hnot⟩
          have := Finset.min'_le missing b hbmiss
          exact (not_le_of_gt hb) this
      · refine ⟨n,le_rfl,?_⟩
        ext b
        simp only [HC_initialSegment,Finset.mem_filter,Finset.mem_univ,true_and]
        constructor
        · intro _; exact b.isLt
        · intro _
          by_contra hb
          exact hmiss ⟨b,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hb⟩⟩
    · rintro ⟨k,hk,heq⟩ hs
      exact HC_inversion_not_prefix s hs k heq

  have HC_full_chain_complement_connected  (n : ℕ) (hn : 2 ≤ n) :
      ((HC_cube (α := Fin n)).induce {s | ¬ ∃ k ≤ n, s = HC_initialSegment n k}).Connected := by
    have sets : {s : Finset (Fin n) | ¬ ∃ k ≤ n, s = HC_initialSegment n k} = {s | HC_Inversion s} := by
      ext s
      exact (not_congr (HC_not_inversion_iff_prefix s)).symm.trans (not_not)
    rw [sets]
    exact HC_outside_connected (lo := ⟨0,by omega⟩) (hi := ⟨1,by omega⟩)
      (by change (0 : ℕ) < 1; omega) (by intro a; exact Nat.zero_le a.val)

  let HC_Allowed  (n K : ℕ) (s : Finset (Fin n)) : Prop :=
    ∀ k, k ≤ K → s ≠ HC_initialSegment n k

  let HC_partialOutside  (n K : ℕ) : SimpleGraph {s : Finset (Fin n) // HC_Allowed n K s} :=
    HC_cube.induce {s | HC_Allowed n K s}

  have HC_inversion_allowed  {n K : ℕ} {s : Finset (Fin n)} (hs : HC_Inversion s) : HC_Allowed n K s :=
    fun k _ => HC_inversion_not_prefix s hs k

  let HC_hub  (n : ℕ) (hn : 2 ≤ n) : Finset (Fin n) := {⟨1,by omega⟩}

  have HC_hub_inversion  (n : ℕ) (hn : 2 ≤ n) : HC_Inversion (HC_hub n hn) := by
    refine ⟨(⟨0,by omega⟩ : Fin n),(⟨1,by omega⟩ : Fin n),?_,?_,?_⟩
    · change (0:ℕ)<1; omega
    · intro h
      have hv : (0:ℕ)=1 := congrArg Fin.val (Finset.mem_singleton.mp h)
      omega
    · exact Finset.mem_singleton_self _

  have HC_inversion_reachable_hub  (n K : ℕ) (hn : 2 ≤ n) (s : Finset (Fin n))
      (hs : HC_Inversion s) :
      (HC_partialOutside n K).Reachable ⟨s,HC_inversion_allowed hs⟩
        ⟨HC_hub n hn,HC_inversion_allowed (HC_hub_inversion n hn)⟩ := by
    let lo : Fin n := ⟨0,by omega⟩
    let hi : Fin n := ⟨1,by omega⟩
    have hlt : lo < hi := by change (0:ℕ)<1; omega
    have hsub : {s : Finset (Fin n) | HC_Inversion s} ⊆ {s | HC_Allowed n K s} :=
      fun _ h => HC_inversion_allowed h
    exact (HC_all_inversions_reachable hlt (by intro a; exact Nat.zero_le a.val) s hs).map
      ((HC_cube (α := Fin n)).induceHomOfLE hsub).toHom

  have HC_partial_chain_complement_connected  (n K : ℕ) (hn : 2 ≤ n) :
      (HC_partialOutside n K).Connected := by
    let lo : Fin n := ⟨0,by omega⟩
    let hi : Fin n := ⟨1,by omega⟩
    have hlt : lo < hi := by change (0:ℕ)<1; omega
    have hubInv : HC_Inversion ({hi} : Finset (Fin n)) :=
      HC_inversion_anchors hlt (by simp [hlt.ne]) (by simp)
    apply (HC_partialOutside n K).connected_iff_exists_forall_reachable.mpr
    refine ⟨⟨{hi},HC_inversion_allowed hubInv⟩,?_⟩
    intro x
    apply Reachable.symm
    obtain ⟨s,hs⟩ := x
    by_cases hinv : HC_Inversion s
    · exact HC_inversion_reachable_hub n K hn s hinv
    · obtain ⟨j,hjn,hj⟩ := (HC_not_inversion_iff_prefix s).mp hinv
      have hKj : K < j := by by_contra! h; exact hs j h hj
      have hlo : lo ∈ s := by rw [hj]; simp [HC_initialSegment,lo]; omega
      let t := insert hi s
      have ht : HC_Allowed n K t := by
        intro k hk heq
        have hcoord : (⟨K,by omega⟩ : Fin n) ∈ s := by rw [hj]; simp [HC_initialSegment,hKj]
        have : (⟨K,by omega⟩ : Fin n) ∈ t := Finset.mem_insert_of_mem hcoord
        rw [heq] at this
        simp only [HC_initialSegment,Finset.mem_filter,Finset.mem_univ,true_and] at this
        omega
      have htlo : lo ∈ t := Finset.mem_insert_of_mem hlo
      let z := t.erase lo
      have hz : HC_Inversion z := HC_inversion_anchors hlt (Finset.notMem_erase lo t)
        (Finset.mem_erase.mpr ⟨hlt.ne',Finset.mem_insert_self hi s⟩)
      have first : (HC_partialOutside n K).Reachable ⟨s,hs⟩ ⟨t,ht⟩ := by
        by_cases h : hi ∈ s
        · have heq : t = s := Finset.insert_eq_of_mem h
          simpa only [heq] using (Reachable.refl (G := HC_partialOutside n K) ⟨s,hs⟩)
        · exact (show (HC_partialOutside n K).Adj ⟨s,hs⟩ ⟨t,ht⟩ from
            HC_cube_adj_insert s hi h).reachable
      have second : (HC_partialOutside n K).Adj ⟨t,ht⟩ ⟨z,HC_inversion_allowed hz⟩ :=
        HC_cube_adj_erase t lo htlo
      exact first.trans (second.reachable.trans (HC_inversion_reachable_hub n K hn z hz))

  have HC_xor_empty {α : Type} [LinearOrder α] (s : Finset α) : s ∆ ∅ = s := by
    ext x; simp [Finset.mem_symmDiff]

  have HC_empty_xor {α : Type} [LinearOrder α] (s : Finset α) : ∅ ∆ s = s := by
    rw [symmDiff_comm,HC_xor_empty]

  have HC_toggle_eq_erase {α : Type} [LinearOrder α] (s : Finset α) (a : α) (ha : a ∈ s) : s ∆ {a} = s.erase a := by
    ext x
    by_cases h : x = a
    · subst x; simp [Finset.mem_symmDiff,ha]
    · simp [Finset.mem_symmDiff,h]

  have HC_toggle_eq_insert {α : Type} [LinearOrder α] (s : Finset α) (a : α) (ha : a ∉ s) : s ∆ {a} = insert a s := by
    ext x
    by_cases h : x = a
    · subst x; simp [Finset.mem_symmDiff,ha]
    · simp [Finset.mem_symmDiff,h]

  have HC_cube_adj_iff_toggle {α : Type} [LinearOrder α] {s t : Finset α} : HC_cube.Adj s t ↔ ∃ a, t = s ∆ {a} := by
    constructor
    · rintro ⟨hne,⟨a,ha,rfl⟩ | ⟨a,ha,heq⟩⟩
      · exact ⟨a,(HC_toggle_eq_insert s a ha).symm⟩
      · refine ⟨a,?_⟩
        rw [← heq,HC_toggle_eq_erase _ a (Finset.mem_insert_self a t)]
        simp [ha]
    · rintro ⟨a,rfl⟩
      by_cases h : a ∈ s
      · rw [HC_toggle_eq_erase s a h];exact HC_cube_adj_erase s a h
      · rw [HC_toggle_eq_insert s a h];exact HC_cube_adj_insert s a h

  let HC_translateIso {α : Type} [LinearOrder α] (base : Finset α) : (HC_cube (α := α)) ≃g (HC_cube (α := α)) := {
    toFun s := base ∆ s
    invFun s := base ∆ s
    left_inv s := symmDiff_symmDiff_cancel_left _ _
    right_inv s := symmDiff_symmDiff_cancel_left _ _
    map_rel_iff' := by
      intro s t
      rw [HC_cube_adj_iff_toggle,HC_cube_adj_iff_toggle]
      constructor
      · rintro ⟨a,ha⟩
        have h := congrArg (fun z => base ∆ z) ha
        exact ⟨a,by simpa [← symmDiff_assoc] using h⟩
      · rintro ⟨a,rfl⟩
        exact ⟨a,(symmDiff_assoc _ _ _).symm⟩
  }

  have HC_walk_from_empty {α : Type} [LinearOrder α] (s : Finset α) : ∃ p : HC_cube.Walk ∅ s, p.length = s.card := by
    induction s using Finset.induction_on with
    | empty => exact ⟨Walk.nil,rfl⟩
    | @insert a s ha ih =>
      obtain ⟨p,hp⟩ := ih
      refine ⟨p.append (HC_cube_adj_insert s a ha).toWalk,?_⟩
      simp [hp,Finset.card_insert_of_notMem ha]

  have HC_walk_between {α : Type} [LinearOrder α] (s t : Finset α) : ∃ p : HC_cube.Walk s t, p.length = (s ∆ t).card := by
    obtain ⟨p,hp⟩ := HC_walk_from_empty (s ∆ t)
    refine ⟨(p.map (HC_translateIso s).toHom).copy
      (by simp [HC_translateIso,HC_xor_empty])
      (by simp [HC_translateIso,symmDiff_symmDiff_cancel_left]),?_⟩
    simpa only [Walk.length_copy,Walk.length_map] using hp

  let HC_flip {α : Type} [LinearOrder α] {s t : Finset α} (h : HC_cube.Adj s t) : α :=
    Classical.choose (HC_cube_adj_iff_toggle.mp h)

  have HC_flip_spec {α : Type} [LinearOrder α] {s t : Finset α} (h : HC_cube.Adj s t) : t = s ∆ {HC_flip h} :=
    Classical.choose_spec (HC_cube_adj_iff_toggle.mp h)

  let HC_flips {α : Type} [LinearOrder α] {s t : Finset α} (p : HC_cube.Walk s t) : List α := by
    induction p with
    | nil => exact []
    | cons h p ih => exact HC_flip h :: ih

  let HC_parity {α : Type} [LinearOrder α] (l : List α) : Finset α := l.foldr (fun a s => {a} ∆ s) ∅

  have HC_flips_length {α : Type} [LinearOrder α] {s t : Finset α} (p : HC_cube.Walk s t) : (HC_flips p).length = p.length := by
    induction p with
    | nil => rfl
    | cons h p ih => simpa only [HC_flips,Walk.length_cons,List.length_cons] using congrArg Nat.succ ih

  have HC_endpoint_parity {α : Type} [LinearOrder α] {s t : Finset α} (p : HC_cube.Walk s t) : t = s ∆ HC_parity (HC_flips p) := by
    induction p with
    | nil => simp [HC_flips,HC_parity,HC_xor_empty]
    | @cons s u t h p ih =>
      calc
        t = u ∆ HC_parity (HC_flips p) := ih
        _ = (s ∆ {HC_flip h}) ∆ HC_parity (HC_flips p) :=
          congrArg (fun z => z ∆ HC_parity (HC_flips p)) (HC_flip_spec h)
        _ = s ∆ HC_parity (HC_flips (Walk.cons h p)) := by simp [HC_flips,HC_parity,symmDiff_assoc]

  have HC_diff_eq_parity {α : Type} [LinearOrder α] {s t : Finset α} (p : HC_cube.Walk s t) : s ∆ t = HC_parity (HC_flips p) := by
    have h := congrArg (fun z => s ∆ z) (HC_endpoint_parity p)
    simpa only [symmDiff_symmDiff_cancel_left] using h

  have HC_parity_subset {α : Type} [LinearOrder α] (l : List α) : HC_parity l ⊆ l.toFinset := by
    induction l with
    | nil => simp [HC_parity]
    | cons a l ih =>
      intro x hx
      rcases Finset.mem_symmDiff.mp hx with h | h
      · have : x = a := Finset.mem_singleton.mp h.1
        simp [this]
      · simpa only [List.toFinset_cons] using (Finset.mem_insert_of_mem (b := a) (ih h.1))

  have HC_shortest_flips_nodup {α : Type} [LinearOrder α] {s t : Finset α} (p : HC_cube.Walk s t)
      (hp : p.length = HC_cube.dist s t) : (HC_flips p).Nodup := by
    obtain ⟨q,hq⟩ := HC_walk_between s t
    have upper : p.length ≤ (s ∆ t).card := by rw [hp,← hq];exact SimpleGraph.dist_le q
    have lower := Finset.card_le_card (HC_parity_subset (HC_flips p))
    rw [← HC_diff_eq_parity p] at lower
    have hc := List.toFinset_card_le (HC_flips p)
    have heq : (HC_flips p).toFinset.card = (HC_flips p).length := by rw [HC_flips_length] at *;omega
    exact Multiset.toFinset_card_eq_card_iff_nodup.mp heq

  have HC_parity_of_nodup {α : Type} [LinearOrder α] {l : List α} (h : l.Nodup) : HC_parity l = l.toFinset := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      have hd := List.nodup_cons.mp h
      change {a} ∆ HC_parity l = _
      rw [ih hd.2,symmDiff_comm,HC_toggle_eq_insert l.toFinset a (by simpa using hd.1)]
      simp

  have HC_getVert_parity {α : Type} [LinearOrder α] {s t : Finset α} (p : HC_cube.Walk s t) (i : ℕ) :
      p.getVert i = s ∆ HC_parity ((HC_flips p).take i) := by
    induction p generalizing i with
    | nil => simp [HC_flips,HC_parity,HC_xor_empty]
    | @cons s u t h p ih =>
      cases i with
      | zero => simp [HC_flips,HC_parity,HC_xor_empty]
      | succ i =>
        simp only [Walk.getVert_cons_succ,HC_flips,List.take_succ_cons,HC_parity]
        calc
          p.getVert i = u ∆ HC_parity ((HC_flips p).take i) := ih i
          _ = (s ∆ {HC_flip h}) ∆ HC_parity ((HC_flips p).take i) :=
            congrArg (fun z => z ∆ HC_parity ((HC_flips p).take i)) (HC_flip_spec h)
          _ = s ∆ ({HC_flip h} ∆ HC_parity ((HC_flips p).take i)) := symmDiff_assoc _ _ _

  have HC_coordinate_map_adj {α : Type} [LinearOrder α] {β : Type} [LinearOrder β] (e : α ≃ β) {s t : Finset α} (h : HC_cube.Adj s t) :
      HC_cube.Adj (e.finsetCongr s) (e.finsetCongr t) := by
    rcases h with ⟨hne,⟨a,ha,heq⟩ | ⟨a,ha,heq⟩⟩
    · refine ⟨fun he => hne (e.finsetCongr.injective he),Or.inl ⟨e a,?_,?_⟩⟩
      · simpa using ha
      · rw [← heq];simp
    · refine ⟨fun he => hne (e.finsetCongr.injective he),Or.inr ⟨e a,?_,?_⟩⟩
      · simpa using ha
      · rw [← heq];simp

  let HC_coordinateIso {α : Type} [LinearOrder α] {β : Type} [LinearOrder β] (e : α ≃ β) : (HC_cube (α := α)) ≃g (HC_cube (α := β)) := {
    toEquiv := e.finsetCongr
    map_rel_iff' := by
      intro s t
      constructor
      · intro h
        have h' := HC_coordinate_map_adj e.symm h
        simpa only [← Equiv.finsetCongr_symm,Equiv.symm_apply_apply] using h'
      · exact HC_coordinate_map_adj e
  }

  let HC_completeList {α : Type} [LinearOrder α] [Fintype α] (l : List α) : List α := l ++ (Finset.univ \ l.toFinset).toList

  have HC_completeList_nodup {α : Type} [LinearOrder α] [Fintype α] {l : List α} (h : l.Nodup) : (HC_completeList l).Nodup := by
    apply h.append (Finset.nodup_toList _)
    apply List.disjoint_left.mpr
    intro a ha hb
    have hnot := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2
    exact hnot (List.mem_toFinset.mpr ha)

  have HC_mem_completeList {α : Type} [LinearOrder α] [Fintype α] (l : List α) (a : α) : a ∈ HC_completeList l := by
    by_cases ha : a ∈ l
    · exact List.mem_append_left _ ha
    · exact List.mem_append_right _ (Finset.mem_toList.mpr
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,by simpa using ha⟩))

  let HC_listCoordinates {α : Type} [LinearOrder α] [Fintype α] (l : List α) (h : l.Nodup) : α ≃ Fin (HC_completeList l).length :=
    (List.Nodup.getEquivOfForallMemList (HC_completeList l) (HC_completeList_nodup h)
      (HC_mem_completeList l)).symm

  have HC_listCoordinates_val {α : Type} [LinearOrder α] [Fintype α] (l : List α) (h : l.Nodup) (a : α) :
      (HC_listCoordinates l h a).val = (HC_completeList l).idxOf a := rfl

  have HC_image_take_coordinates {α : Type} [LinearOrder α] [Fintype α] (l : List α) (h : l.Nodup) (i : ℕ) (hi : i ≤ l.length) :
      (HC_listCoordinates l h).finsetCongr ((l.take i).toFinset) =
        HC_initialSegment (HC_completeList l).length i := by
    let e := HC_listCoordinates l h
    ext z
    have hmem : z ∈ e.finsetCongr ((l.take i).toFinset) ↔ e.symm z ∈ (l.take i).toFinset := by
      simp [Equiv.finsetCongr_apply,Finset.mem_map,Equiv.apply_eq_iff_eq_symm_apply]
    rw [hmem]
    simp only [List.mem_toFinset,HC_initialSegment,Finset.mem_filter,Finset.mem_univ,true_and]
    have htake : (HC_completeList l).take i = l.take i := List.take_append_of_le_length hi
    have hidx : (HC_completeList l).idxOf (e.symm z) = z.val := by
      exact (congrArg Fin.val (e.apply_symm_apply z))
    simpa only [htake,hidx] using
      (List.mem_take_iff_idxOf_lt (n := i) (HC_mem_completeList l (e.symm z)))

  let HC_normalizingIso {α : Type} [LinearOrder α] [Fintype α] {s t : Finset α} (p : HC_cube.Walk s t)
      (hp : p.length = HC_cube.dist s t) :
      (HC_cube (α := α)) ≃g (HC_cube (α := Fin (HC_completeList (HC_flips p)).length)) :=
    (HC_translateIso s).trans (HC_coordinateIso (HC_listCoordinates (HC_flips p) (HC_shortest_flips_nodup p hp)))

  have HC_normalizing_getVert {α : Type} [LinearOrder α] [Fintype α] {s t : Finset α} (p : HC_cube.Walk s t)
      (hp : p.length = HC_cube.dist s t) (i : ℕ) (hi : i ≤ p.length) :
      HC_normalizingIso p hp (p.getVert i) = HC_initialSegment (HC_completeList (HC_flips p)).length i := by
    change (HC_listCoordinates (HC_flips p) (HC_shortest_flips_nodup p hp)).finsetCongr
      (s ∆ p.getVert i) = _
    rw [HC_getVert_parity p i,symmDiff_symmDiff_cancel_left,
      HC_parity_of_nodup ((HC_shortest_flips_nodup p hp).take (i := i))]
    exact HC_image_take_coordinates (HC_flips p) (HC_shortest_flips_nodup p hp) i (by simpa [HC_flips_length] using hi)

  have HC_normalizing_outside {α : Type} [LinearOrder α] [Fintype α] {s t : Finset α} (p : HC_cube.Walk s t)
      (hp : p.length = HC_cube.dist s t) (x : Finset α) :
      x ∉ p.support ↔ HC_Allowed (HC_completeList (HC_flips p)).length p.length (HC_normalizingIso p hp x) := by
    constructor
    · intro hx i hi heq
      have hxi : x = p.getVert i := (HC_normalizingIso p hp).injective
        (heq.trans (HC_normalizing_getVert p hp i hi).symm)
      exact hx (hxi ▸ p.getVert_mem_support i)
    · intro hx hmem
      obtain ⟨i,hix,hi⟩ := Walk.mem_support_iff_exists_getVert.mp hmem
      apply hx i hi
      calc
        HC_normalizingIso p hp x = HC_normalizingIso p hp (p.getVert i) := congrArg _ hix.symm
        _ = _ := HC_normalizing_getVert p hp i hi

  let HC_complementIso {α : Type} [LinearOrder α] [Fintype α] {s t : Finset α} (p : HC_cube.Walk s t)
      (hp : p.length = HC_cube.dist s t) :
      (HC_cube.induce {x | x ∉ p.support}) ≃g HC_partialOutside (HC_completeList (HC_flips p)).length p.length := {
    toFun x := ⟨HC_normalizingIso p hp x.val,(HC_normalizing_outside p hp x.val).mp x.property⟩
    invFun y := ⟨(HC_normalizingIso p hp).symm y.val,(HC_normalizing_outside p hp _).mpr
      (by simpa using y.property)⟩
    left_inv x := Subtype.ext ((HC_normalizingIso p hp).symm_apply_apply x.val)
    right_inv y := Subtype.ext ((HC_normalizingIso p hp).apply_symm_apply y.val)
    map_rel_iff' := by
      intro x y
      exact (HC_normalizingIso p hp).map_rel_iff
  }

  have HC_geodesic_complement_connected {α : Type} [LinearOrder α] [Fintype α] (hdim : 2 ≤ Fintype.card α)
      {s t : Finset α} (p : HC_cube.Walk s t) (hp : p.length = HC_cube.dist s t) :
      (HC_cube.induce {x | x ∉ p.support}).Connected := by
    have hcard := Fintype.card_congr (HC_listCoordinates (HC_flips p) (HC_shortest_flips_nodup p hp))
    simp only [Fintype.card_fin] at hcard
    have hm : 2 ≤ (HC_completeList (HC_flips p)).length := hcard ▸ hdim
    exact (HC_complementIso p hp).connected_iff.mpr
      (HC_partial_chain_complement_connected _ _ hm)

  have CB_add_self {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (x : V) : x+x=0 := by
    have h : (1:(ZMod 2))+1=0 := by decide
    calc
      x+x = ((1:(ZMod 2))+1) • x := by rw [add_smul,one_smul]
      _ = 0 := by rw [h,zero_smul]

  have CB_neg_self {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (x : V) : -x=x := by
    exact (eq_neg_iff_add_eq_zero.mpr (CB_add_self x)).symm

  have CB_sub_char_two {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (x y : V) : x-y=x+y := by rw [sub_eq_add_neg,CB_neg_self]

  have CB_field_cases  (x : (ZMod 2)) : x=0 ∨ x=1 := (by decide : ∀ x : (ZMod 2), x=0 ∨ x=1) x

  let CB_graph {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (S : Set V) : SimpleGraph V := SimpleGraph.fromRel (fun x y => y-x ∈ S)

  have CB_graph_adj_iff {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (S : Set V) (x y : V) : (CB_graph S).Adj x y ↔ x ≠ y ∧ y-x ∈ S := by
    simp only [CB_graph,SimpleGraph.fromRel_adj]
    rw [CB_sub_char_two x y,CB_sub_char_two y x,add_comm x y,or_self]

  let CB_translateIso {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (S : Set V) (a : V) : CB_graph S ≃g CB_graph S := {
    toFun x := a+x
    invFun x := -a+x
    left_inv x := by simp
    right_inv x := by simp
    map_rel_iff' := by
      intro x y
      simp [CB_graph_adj_iff,add_sub_add_left_eq_sub]
  }

  let CB_edgeDifference {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {S : Set V} {x y : V} (_ : (CB_graph S).Adj x y) : V := y-x

  let CB_steps {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {S : Set V} {x y : V} (p : (CB_graph S).Walk x y) : List V := by
    induction p with
    | nil => exact []
    | cons h p ih => exact CB_edgeDifference h :: ih

  have CB_steps_length {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {S : Set V} {x y : V} (p : (CB_graph S).Walk x y) :
      (CB_steps p).length = p.length := by
    induction p with
    | nil => rfl
    | cons h p ih => simpa only [CB_steps,Walk.length_cons,List.length_cons] using congrArg Nat.succ ih

  have CB_steps_mem {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {S : Set V} {x y : V} (p : (CB_graph S).Walk x y) :
      ∀ g ∈ CB_steps p, g ∈ S ∧ g ≠ 0 := by
    induction p with
    | nil => simp [CB_steps]
    | @cons x u y h p ih =>
      intro g hg
      simp only [CB_steps,List.mem_cons] at hg
      rcases hg with rfl | hg
      · have hs := (CB_graph_adj_iff S x u).mp h
        exact ⟨hs.2,sub_ne_zero.mpr hs.1.symm⟩
      · exact ih g hg

  have CB_steps_sum {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {S : Set V} {x y : V} (p : (CB_graph S).Walk x y) :
      (CB_steps p).sum = y-x := by
    induction p with
    | nil => simp [CB_steps]
    | @cons x u y h p ih =>
      simp only [CB_steps,List.sum_cons,CB_edgeDifference,ih]
      abel

  have CB_walk_sum {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (S : Set V) {ι : Type} (A : Finset ι) (g : ι → V)
      (hg : ∀ i ∈ A, g i ∈ S ∧ g i ≠ 0) :
      ∃ p : (CB_graph S).Walk 0 (∑ i ∈ A,g i), p.length=A.card := by
    classical
    revert hg
    induction A using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨Walk.nil,by simp⟩
    | @insert a A ha ih =>
      intro hg
      obtain ⟨p,hp⟩ := ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      have hga := hg a (Finset.mem_insert_self a A)
      have hadj : (CB_graph S).Adj (∑ i ∈ A,g i) (g a+∑ i ∈ A,g i) := by
        apply (CB_graph_adj_iff _ _ _).mpr
        exact ⟨(add_ne_right.mpr hga.2).symm,by simpa using hga.1⟩
      rw [Finset.sum_insert ha]
      refine ⟨p.append hadj.toWalk,?_⟩
      simp [hp,Finset.card_insert_of_notMem ha]

  have CB_walk_diff_mem_span {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {S : Set V} {x y : V} (p : (CB_graph S).Walk x y) :
      y-x ∈ Submodule.span (ZMod 2) S := by
    induction p with
    | nil => simp
    | @cons x u y h p ih =>
      have hs : u-x ∈ Submodule.span (ZMod 2) S :=
        Submodule.subset_span ((CB_graph_adj_iff S x u).mp h).2
      have hsum := (Submodule.span (ZMod 2) S).add_mem hs ih
      convert hsum using 1 <;> abel

  have CB_span_generators {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (S : Set V) (hconn : (CB_graph S).Connected) : Submodule.span (ZMod 2) S = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro y
    obtain ⟨p⟩ := hconn.preconnected 0 y
    simpa using CB_walk_diff_mem_span p

  have CB_steps_get_sum {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {S : Set V} {x y : V} (p : (CB_graph S).Walk x y) :
      (∑ i : Fin (CB_steps p).length,(CB_steps p).get i)=y-x := by
    calc
      (∑ i : Fin (CB_steps p).length,(CB_steps p).get i) = (List.ofFn (CB_steps p).get).sum :=
        (Fin.sum_ofFn _).symm
      _ = (CB_steps p).sum := by rw [List.ofFn_get]
      _ = y-x := CB_steps_sum p

  have CB_shortest_no_zero_subsum {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {S : Set V} {x y : V} (p : (CB_graph S).Walk x y)
      (hp : p.length=(CB_graph S).dist x y) (T : Finset (Fin (CB_steps p).length))
      (hzero : ∑ i ∈ T,(CB_steps p).get i=0) : T=∅ := by
    classical
    let g := (CB_steps p).get
    let U := Finset.univ \ T
    have hsum : (∑ i ∈ U,g i)=y-x := by
      have hs := Finset.sum_sdiff (f := g) (Finset.subset_univ T)
      change (∑ i ∈ U,g i)+(∑ i ∈ T,g i)=∑ i,g i at hs
      rw [hzero,add_zero] at hs
      exact hs.trans (CB_steps_get_sum p)
    obtain ⟨q,hq⟩ := CB_walk_sum S U g (by
      intro i hi
      exact CB_steps_mem p (g i) (List.get_mem _ i))
    let q' : (CB_graph S).Walk x y :=
      (q.map (CB_translateIso S x).toHom).copy (by simp [CB_translateIso])
        (by simp [CB_translateIso,hsum])
    have hlen : q'.length=U.card := by
      simpa only [q',Walk.length_copy,Walk.length_map] using hq
    have hshort := SimpleGraph.dist_le q'
    rw [← hp,hlen] at hshort
    have hcard : U.card=(CB_steps p).length-T.card := by
      dsimp [U]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ T)]
      simp
    have hTcard : T.card ≤ (CB_steps p).length := by
      simpa using Finset.card_le_card (Finset.subset_univ T)
    have hsteps := CB_steps_length p
    have hz : T.card=0 := by omega
    exact Finset.card_eq_zero.mp hz

  have CB_shortest_steps_linearIndependent {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {S : Set V} {x y : V} (p : (CB_graph S).Walk x y)
      (hp : p.length=(CB_graph S).dist x y) :
      LinearIndependent (ZMod 2) (fun i : Fin (CB_steps p).length => (CB_steps p).get i) := by
    classical
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    let T := Finset.univ.filter (fun j => c j ≠ 0)
    have hsum : (∑ j ∈ T,(CB_steps p).get j)=∑ j,c j • (CB_steps p).get j := by
      dsimp [T]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      rcases CB_field_cases (c j) with h | h <;> simp [h]
    have hT := CB_shortest_no_zero_subsum p hp T (hsum.trans hc)
    by_contra hni
    have hi : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hni⟩
    rw [hT] at hi
    exact Finset.notMem_empty i hi

  have CB_repr_sum_basis {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ι : Type} [Fintype ι] [LinearOrder ι] (b : Module.Basis ι (ZMod 2) V) (A : Finset ι) (j : ι) :
      b.repr (∑ i ∈ A,b i) j = if j ∈ A then 1 else 0 := by
    simp [map_sum,Module.Basis.repr_self,Finsupp.single_apply]

  let CB_vectorSubset {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ι : Type} [Fintype ι] [LinearOrder ι] (b : Module.Basis ι (ZMod 2) V) (v : V) : Finset ι :=
    Finset.univ.filter (fun i => b.repr v i=1)

  have CB_vectorSubset_sum {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ι : Type} [Fintype ι] [LinearOrder ι] (b : Module.Basis ι (ZMod 2) V) (A : Finset ι) :
      CB_vectorSubset b (∑ i ∈ A,b i)=A := by
    ext j
    simp only [CB_vectorSubset,Finset.mem_filter,Finset.mem_univ,true_and,CB_repr_sum_basis]
    by_cases hj : j ∈ A <;> simp [hj]

  have CB_sum_vectorSubset {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ι : Type} [Fintype ι] [LinearOrder ι] (b : Module.Basis ι (ZMod 2) V) (v : V) :
      (∑ i ∈ CB_vectorSubset b v,b i)=v := by
    calc
      (∑ i ∈ CB_vectorSubset b v,b i) = ∑ i,b.repr v i • b i := by
        simp only [CB_vectorSubset,Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        rcases CB_field_cases (b.repr v i) with h | h <;> simp [h]
      _ = v := b.sum_repr v

  let CB_basisEquiv {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ι : Type} [Fintype ι] [LinearOrder ι] (b : Module.Basis ι (ZMod 2) V) : Finset ι ≃ V := {
    toFun A := ∑ i ∈ A,b i
    invFun v := CB_vectorSubset b v
    left_inv := CB_vectorSubset_sum b
    right_inv := CB_sum_vectorSubset b
  }

  have CB_basisEquiv_toggle {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ι : Type} [Fintype ι] [LinearOrder ι] (b : Module.Basis ι (ZMod 2) V) (A : Finset ι) (i : ι) :
      CB_basisEquiv b (A ∆ {i}) = CB_basisEquiv b A+b i := by
    change (∑ j ∈ A ∆ {i},b j)=(∑ j ∈ A,b j)+b i
    by_cases hi : i ∈ A
    · rw [HC_toggle_eq_erase A i hi]
      exact (eq_sub_iff_add_eq.mpr (Finset.sum_erase_add A (fun j => b j) hi)).trans (CB_sub_char_two _ _)
    · rw [HC_toggle_eq_insert A i hi,Finset.sum_insert hi,add_comm]

  let CB_cubeToGraph {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ι : Type} [Fintype ι] [LinearOrder ι] (S : Set V) (b : Module.Basis ι (ZMod 2) V) (hb : ∀ i,b i ∈ S) :
      (HC_cube (α := ι)) →g CB_graph S := {
    toFun := CB_basisEquiv b
    map_rel' := by
      intro A B h
      obtain ⟨i,hi⟩ := HC_cube_adj_iff_toggle.mp h
      apply (CB_graph_adj_iff S _ _).mpr
      refine ⟨(CB_basisEquiv b).injective.ne h.ne,?_⟩
      have hdiff : CB_basisEquiv b B-CB_basisEquiv b A=b i := by
        rw [hi,CB_basisEquiv_toggle]
        simp
      rw [hdiff]
      exact hb i
  }

  have CB_basis_step_lift {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ι : Type} [Fintype ι] [LinearOrder ι] (b : Module.Basis ι (ZMod 2) V) (x y : V)
      (h : ∃ i,y-x=b i) :
      HC_cube.Adj ((CB_basisEquiv b).symm x) ((CB_basisEquiv b).symm y) := by
    obtain ⟨i,hi⟩ := h
    apply HC_cube_adj_iff_toggle.mpr
    refine ⟨i,(CB_basisEquiv b).injective ?_⟩
    have hy : y=x+b i := by simpa [add_comm] using (sub_eq_iff_eq_add.mp hi)
    calc
      CB_basisEquiv b ((CB_basisEquiv b).symm y)=y := (CB_basisEquiv b).apply_symm_apply y
      _ = x+b i := hy
      _ = CB_basisEquiv b ((CB_basisEquiv b).symm x)+b i := by rw [(CB_basisEquiv b).apply_symm_apply]
      _ = CB_basisEquiv b (((CB_basisEquiv b).symm x) ∆ {i}) := (CB_basisEquiv_toggle b _ i).symm

  have CB_lift_walk_to_basis {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ι : Type} [Fintype ι] [LinearOrder ι] (S : Set V) (b : Module.Basis ι (ZMod 2) V)
      {x y : V} (p : (CB_graph S).Walk x y) (hb : ∀ g ∈ CB_steps p,g ∈ Set.range b) :
      ∃ q : HC_cube.Walk ((CB_basisEquiv b).symm x) ((CB_basisEquiv b).symm y),
        q.length=p.length ∧ q.support.map (CB_basisEquiv b)=p.support := by
    induction p with
    | nil => exact ⟨Walk.nil,rfl,by simp⟩
    | @cons x u y h p ih =>
      obtain ⟨i,hi⟩ := hb (u-x) (by simp [CB_steps,CB_edgeDifference])
      have htail : ∀ g ∈ CB_steps p,g ∈ Set.range b :=
        fun g hg => hb g (List.mem_cons_of_mem _ hg)
      obtain ⟨q,hq,hqs⟩ := ih htail
      refine ⟨Walk.cons (CB_basis_step_lift b x u ⟨i,hi.symm⟩) q,?_,?_⟩
      · simpa only [Walk.length_cons] using congrArg Nat.succ hq
      · simp only [Walk.support_cons,List.map_cons,hqs]
        rw [(CB_basisEquiv b).apply_symm_apply]

  have CB_basis_geodesic_complement {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ι : Type} [Fintype ι] [LinearOrder ι] (S : Set V) (b : Module.Basis ι (ZMod 2) V)
      (hb : ∀ i,b i ∈ S) (hdim : 2 ≤ Fintype.card ι)
      {x y : V} (p : (CB_graph S).Walk x y) (hp : p.length=(CB_graph S).dist x y)
      (hbsteps : ∀ g ∈ CB_steps p,g ∈ Set.range b) :
      ((CB_graph S).induce {v | v ∉ p.support}).Connected := by
    classical
    let e := CB_basisEquiv b
    let f := CB_cubeToGraph S b hb
    obtain ⟨q,hq,hqs⟩ := CB_lift_walk_to_basis S b p hbsteps
    obtain ⟨r,hr⟩ := q.reachable.exists_walk_length_eq_dist
    let r' : (CB_graph S).Walk x y := (r.map f).copy (e.apply_symm_apply x) (e.apply_symm_apply y)
    have hbound : p.length ≤ HC_cube.dist (e.symm x) (e.symm y) := by
      calc
        p.length=(CB_graph S).dist x y := hp
        _ ≤ r'.length := SimpleGraph.dist_le r'
        _ = r.length := (Walk.length_copy (r.map f) _ _).trans (Walk.length_map f r)
        _ = _ := hr
    have hqshort : q.length=HC_cube.dist (e.symm x) (e.symm y) :=
      Nat.le_antisymm (hq ▸ hbound) (SimpleGraph.dist_le q)
    have hconn := HC_geodesic_complement_connected hdim q hqshort
    have hoff (A : Finset ι) : A ∉ q.support ↔ e A ∉ p.support := by
      constructor
      · intro hA heA
        rw [← hqs] at heA
        obtain ⟨B,hB,hBA⟩ := List.mem_map.mp heA
        exact hA ((e.injective hBA) ▸ hB)
      · intro he hA
        apply he
        rw [← hqs]
        exact List.mem_map.mpr ⟨A,hA,rfl⟩
    let g : (HC_cube.induce {A | A ∉ q.support}) →g
        ((CB_graph S).induce {v | v ∉ p.support}) := {
      toFun := fun A => ⟨e A.val,(hoff A.val).mp A.property⟩
      map_rel' := by intro A B h;exact f.map_adj h }
    have hsurj : Function.Surjective g := by
      intro v
      have hv : e (e.symm v.val) ∉ p.support := by rw [e.apply_symm_apply];exact v.property
      refine ⟨⟨e.symm v.val,(hoff _).mpr hv⟩,?_⟩
      exact Subtype.ext (e.apply_symm_apply v.val)
    exact hconn.map g hsurj

  have CB_geodesic_complement_connected_ordered {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [LinearOrder V] (S : Set V) (hconn : (CB_graph S).Connected)
      (hcard : 3 ≤ Fintype.card V) {x y : V} (p : (CB_graph S).Walk x y)
      (hp : p.length=(CB_graph S).dist x y) :
      ((CB_graph S).induce {v | v ∉ p.support}).Connected := by
    classical
    let v : Fin (CB_steps p).length → V := (CB_steps p).get
    have hlin : LinearIndependent (ZMod 2) v := CB_shortest_steps_linearIndependent p hp
    have hs : LinearIndepOn (ZMod 2) id (Set.range v) := hlin.linearIndepOn_id
    have hsub : Set.range v ⊆ S := by
      rintro z ⟨i,rfl⟩
      exact (CB_steps_mem p (v i) (List.get_mem _ i)).1
    have hspan : ⊤ ≤ Submodule.span (ZMod 2) S := by rw [CB_span_generators S hconn]
    let b := Module.Basis.extendLe hs hsub hspan
    have hbin : ∀ i,b i ∈ S := fun i => Module.Basis.extendLe_subset hs hsub hspan ⟨i,rfl⟩
    have hbsteps : ∀ z ∈ CB_steps p,z ∈ Set.range b := by
      intro z hz
      apply Module.Basis.subset_extendLe hs hsub hspan
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hz
      exact ⟨i,hi⟩
    have hecard := Fintype.card_congr (CB_basisEquiv b)
    rw [Fintype.card_finset] at hecard
    have hdim : 2 ≤ Fintype.card (hs.extend hsub) := by
      by_contra! h
      have hcases : Fintype.card (hs.extend hsub)=0 ∨ Fintype.card (hs.extend hsub)=1 := by omega
      rcases hcases with hz | ho
      · rw [hz] at hecard
        norm_num at hecard
        omega
      · rw [ho] at hecard
        norm_num at hecard
        omega
    exact CB_basis_geodesic_complement S b hbin hdim p hp hbsteps

  have CB_geodesic_complement_connected {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] (S : Set V) (hconn : (CB_graph S).Connected)
      (hcard : 3 ≤ Fintype.card V) {x y : V} (p : (CB_graph S).Walk x y)
      (hp : p.length=(CB_graph S).dist x y) :
      ((CB_graph S).induce {v | v ∉ p.support}).Connected := by
    classical
    letI : LinearOrder V := (Fintype.equivFin V).linearOrder
    exact CB_geodesic_complement_connected_ordered S hconn hcard p hp

  exact CB_geodesic_complement_connected S hconn hcard p hp

namespace Product

open SimpleGraph
open scoped Classical
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

lemma projection_left_shortest {x y : V × W} (p : (G □ H).Walk x y)
    (hp : p.length=(G □ H).dist x y) :
    p.ofBoxProdLeft.length=G.dist x.1 y.1 := by
  classical
  obtain ⟨r,hr⟩ := p.ofBoxProdLeft.reachable.exists_walk_length_eq_dist
  let alt : (G □ H).Walk x y :=
    ((r.boxProdLeft H x.2).append (p.ofBoxProdRight.boxProdRight G y.1)).copy
      (by rfl) (by rfl)
  have hbound := SimpleGraph.dist_le alt
  have halt : alt.length=r.length+p.ofBoxProdRight.length := by
    simp only [alt,Walk.length_copy]
    exact (Walk.length_append _ _).trans (congrArg₂ Nat.add
      (Walk.length_map _ r) (Walk.length_map _ p.ofBoxProdRight))
  have hsplit := p.length_boxProd
  have hlower := SimpleGraph.dist_le p.ofBoxProdLeft
  rw [← hp,halt,hr] at hbound
  omega

lemma projection_right_shortest {x y : V × W} (p : (G □ H).Walk x y)
    (hp : p.length=(G □ H).dist x y) :
    p.ofBoxProdRight.length=H.dist x.2 y.2 := by
  classical
  obtain ⟨r,hr⟩ := p.ofBoxProdRight.reachable.exists_walk_length_eq_dist
  let alt : (G □ H).Walk x y :=
    ((p.ofBoxProdLeft.boxProdLeft H x.2).append (r.boxProdRight G y.1)).copy
      (by rfl) (by rfl)
  have hbound := SimpleGraph.dist_le alt
  have halt : alt.length=p.ofBoxProdLeft.length+r.length := by
    simp only [alt,Walk.length_copy]
    exact (Walk.length_append _ _).trans (congrArg₂ Nat.add
      (Walk.length_map _ p.ofBoxProdLeft) (Walk.length_map _ r))
  have hsplit := p.length_boxProd
  have hlower := SimpleGraph.dist_le p.ofBoxProdRight
  rw [← hp,halt,hr] at hbound
  omega

lemma mem_left_projection {x y z : V × W} (p : (G □ H).Walk x y)
    (hz : z ∈ p.support) :
    z.1 ∈ p.ofBoxProdLeft.support := by
  classical
  induction p with
  | nil => simpa only [Walk.ofBoxProdLeft,Walk.support_nil,List.mem_singleton] using congrArg Prod.fst (List.mem_singleton.mp hz)
  | @cons x u y h p ih =>
    rw [Walk.support_cons] at hz
    rcases List.mem_cons.mp hz with hzx | hztail
    · subst z;exact Walk.start_mem_support _
    · rcases h with hG | hH
      · simpa [Walk.ofBoxProdLeft,Or.by_cases,hG] using
          (Or.inr (ih hztail) : z.1=x.1 ∨ z.1 ∈ p.ofBoxProdLeft.support)
      · have hnot : ¬ (G.Adj x.1 u.1 ∧ x.2=u.2) := by
          rintro ⟨hx,_⟩
          exact G.ne_of_adj hx hH.2
        rcases x with ⟨a,b⟩
        rcases u with ⟨c,d⟩
        have hac : a=c := hH.2
        subst c
        simpa [Walk.ofBoxProdLeft,Or.by_cases,hnot,hH] using ih hztail

lemma mem_right_projection {x y z : V × W} (p : (G □ H).Walk x y)
    (hz : z ∈ p.support) :
    z.2 ∈ p.ofBoxProdRight.support := by
  classical
  induction p with
  | nil => simpa only [Walk.ofBoxProdRight,Walk.support_nil,List.mem_singleton] using congrArg Prod.snd (List.mem_singleton.mp hz)
  | @cons x u y h p ih =>
    rw [Walk.support_cons] at hz
    rcases List.mem_cons.mp hz with hzx | hztail
    · subst z;exact Walk.start_mem_support _
    · rcases h with hG | hH
      · have hnot : ¬ (H.Adj x.2 u.2 ∧ x.1=u.1) := by
          rintro ⟨hx,_⟩
          exact H.ne_of_adj hx hG.2
        rcases x with ⟨a,b⟩
        rcases u with ⟨c,d⟩
        have hbd : b=d := hG.2
        subst d
        simpa [Walk.ofBoxProdRight,Or.by_cases,hnot,hG] using ih hztail
      · simpa [Walk.ofBoxProdRight,Or.by_cases,hH] using
          (Or.inr (ih hztail) : z.2=x.2 ∨ z.2 ∈ p.ofBoxProdRight.support)

lemma shortest_tail {A : Type*} {J : SimpleGraph A} {a b c : A} (h : J.Adj a b)
    (p : J.Walk b c) (hp : (Walk.cons h p).length=J.dist a c) :
    p.length=J.dist b c := by
  apply SimpleGraph.length_eq_dist_of_subwalk hp
  exact ⟨h.toWalk,Walk.nil,by simp⟩

lemma initial_fibre_prefix {x y : V × W} (p : (G □ H).Walk x y)
    (hp : p.length=(G □ H).dist x y) :
    ∃ (c : V) (q : G.Walk x.1 c) (r : G.Walk c y.1),
      q.append r=p.ofBoxProdLeft ∧ ∀ z, z ∈ q.support ↔ (z,x.2) ∈ p.support := by
  classical
  induction p with
  | @nil x =>
    rcases x with ⟨a,b⟩
    refine ⟨a,Walk.nil,Walk.nil,rfl,?_⟩
    intro z
    simp only [Walk.support_nil,List.mem_singleton,Prod.mk.injEq,and_true]
  | @cons x u y h p ih =>
    have htail := shortest_tail h p hp
    rcases x with ⟨a,b⟩
    rcases u with ⟨c,d⟩
    rcases h with hG | hH
    · have hbd : b=d := hG.2
      subst d
      obtain ⟨w,q,r,hqr,hq⟩ := ih htail
      refine ⟨w,Walk.cons hG.1 q,r,?_,?_⟩
      · simpa [Walk.ofBoxProdLeft,Or.by_cases,hG.1] using
          congrArg (fun s => Walk.cons hG.1 s) hqr
      · intro z
        rw [Walk.support_cons hG.1 q,Walk.support_cons (Or.inl hG) p]
        simpa only [Walk.support_cons,List.mem_cons,Prod.mk.injEq,and_true] using
          (or_congr (Iff.rfl : z=a ↔ z=a) (hq z))
    · have hac : a=c := hH.2
      subst c
      have hpath : (Walk.cons hH.1 p.ofBoxProdRight).IsPath := by
        apply Walk.isPath_of_length_eq_dist
        simpa [Walk.ofBoxProdRight,Or.by_cases,hH.1] using
          projection_right_shortest (Walk.cons (Or.inr hH) p) hp
      have hnot : b ∉ p.ofBoxProdRight.support := (Walk.cons_isPath_iff _ _).mp hpath |>.2
      have habs (z : V) : (z,b) ∉ p.support :=
        fun hz => hnot (mem_right_projection p hz)
      refine ⟨a,Walk.nil,(Walk.cons (Or.inr hH) p).ofBoxProdLeft,?_,?_⟩
      · exact Walk.nil_append _
      · intro z
        rw [Walk.support_cons (Or.inr hH) p]
        simp [habs z]

lemma fibre_is_geodesic {x y : V × W} (p : (G □ H).Walk x y)
    (hp : p.length=(G □ H).dist x y) (b : W) :
    (∀ z : V, (z,b) ∉ p.support) ∨
      ∃ (a c : V) (q : G.Walk a c), q.length=G.dist a c ∧
        ∀ z, z ∈ q.support ↔ (z,b) ∈ p.support := by
  classical
  induction p with
  | @nil x =>
    rcases x with ⟨a,c⟩
    by_cases hb : c=b
    · subst b
      refine Or.inr ⟨a,a,Walk.nil,by simp,?_⟩
      intro z
      simp only [Walk.support_nil,List.mem_singleton,Prod.mk.injEq,and_true]
    · left
      intro z hz
      exact hb (congrArg Prod.snd (List.mem_singleton.mp hz)).symm
  | @cons x u y h p ih =>
    by_cases hb : x.2=b
    · subst b
      obtain ⟨c,q,r,hqr,hq⟩ := initial_fibre_prefix (Walk.cons h p) hp
      refine Or.inr ⟨x.1,c,q,?_,hq⟩
      exact SimpleGraph.length_eq_dist_of_subwalk (projection_left_shortest _ hp)
        (Walk.isSubwalk_of_append_left hqr.symm)
    · have hfibre (z : V) : (z,b) ∈ (Walk.cons h p).support ↔ (z,b) ∈ p.support := by
        rw [Walk.support_cons,List.mem_cons]
        have hne : (z,b) ≠ x := fun he => hb (congrArg Prod.snd he).symm
        simp only [hne,false_or]
      rcases ih (shortest_tail h p hp) with hempty | ⟨a,c,q,hq,hqs⟩
      · exact Or.inl (fun z hz => hempty z ((hfibre z).mp hz))
      · exact Or.inr ⟨a,c,q,hq,fun z => (hqs z).trans (hfibre z).symm⟩

lemma connected_of_fibres_and_spine (hH : H.Connected) (D : Set (V × W))
    (hfibres : ∀ b, (G.induce {a | (a,b) ∉ D}).Connected)
    (a₀ : V) (hspine : ∀ b, (a₀,b) ∉ D) :
    ((G □ H).induce {x | x ∉ D}).Connected := by
  classical
  haveI := hH.nonempty
  let b₀ : W := Classical.arbitrary W
  let root : {x : V × W // x ∉ D} := ⟨(a₀,b₀),hspine b₀⟩
  let vertical : H →g ((G □ H).induce {x | x ∉ D}) := {
    toFun := fun b => ⟨(a₀,b),hspine b⟩
    map_rel' := by intro a b hab;exact Or.inr ⟨hab,rfl⟩ }
  refine (((G □ H).induce {x | x ∉ D}).connected_iff_exists_forall_reachable).mpr ⟨root,?_⟩
  intro x
  let horizontal : (G.induce {a | (a,x.val.2) ∉ D}) →g ((G □ H).induce {x | x ∉ D}) := {
    toFun := fun a => ⟨(a.val,x.val.2),a.property⟩
    map_rel' := by intro a b hab;exact Or.inl ⟨hab,rfl⟩ }
  exact ((hH b₀ x.val.2).map vertical).trans
    (((hfibres x.val.2) ⟨a₀,hspine x.val.2⟩ ⟨x.val.1,x.property⟩).map horizontal)

theorem geodesic_complement_product (hG : G.Connected) (hH : H.Connected)
    (hdel : ∀ {a c} (q : G.Walk a c), q.length=G.dist a c →
      (G.induce {z | z ∉ q.support}).Connected)
    {x y : V × W} (p : (G □ H).Walk x y) (hp : p.length=(G □ H).dist x y) :
    ((G □ H).induce {z | z ∉ p.support}).Connected := by
  classical
  have hcore := hdel p.ofBoxProdLeft (projection_left_shortest p hp)
  obtain ⟨a₀⟩ := hcore.nonempty
  apply connected_of_fibres_and_spine hH {z | z ∈ p.support} ?_ a₀.val ?_
  · intro b
    rcases fibre_is_geodesic p hp b with hempty | ⟨a,c,q,hq,hqs⟩
    · let f : G →g (G.induce {a | (a,b) ∉ p.support}) := {
        toFun := fun a => ⟨a,hempty a⟩
        map_rel' := by intro a c h;exact h }
      have hsurj : Function.Surjective f := fun a => ⟨a.val,Subtype.ext rfl⟩
      exact hG.map f hsurj
    · have hs : {a | (a,b) ∉ p.support} = {a | a ∉ q.support} := by
        ext z
        exact (not_congr (hqs z)).symm
      change (G.induce {a | (a,b) ∉ p.support}).Connected
      rw [hs]
      exact hdel q hq
  · intro b hz
    exact a₀.property (mem_left_projection p hz)

end Product

namespace Complete

open SimpleGraph
variable {V : Type*} [Fintype V]

theorem complete_complement_connected (hcard : 3 ≤ Fintype.card V)
    {u v : V} (p : (⊤ : SimpleGraph V).Walk u v)
    (hp : p.length=(⊤ : SimpleGraph V).dist u v) :
    ((⊤ : SimpleGraph V).induce {x | x ∉ p.support}).Connected := by
  classical
  have hlen : p.length ≤ 1 := by
    rw [hp]
    by_cases h : u=v <;> simp [SimpleGraph.dist_top,h]
  have hs : p.support.toFinset.card ≤ 2 := by
    have h := List.toFinset_card_le p.support
    rw [Walk.length_support] at h
    omega
  have hex : ∃ w : V, w ∉ p.support := by
    by_contra! hall
    have heq : p.support.toFinset=Finset.univ := by
      ext w
      simp [hall w]
    have hc : p.support.toFinset.card=Fintype.card V := by rw [heq];exact Finset.card_univ
    omega
  obtain ⟨w,hw⟩ := hex
  refine { preconnected := ?_, nonempty := ⟨⟨w,hw⟩⟩ }
  intro a b
  by_cases hab : a=b
  · subst b;exact Reachable.refl a
  · exact (show ((⊤ : SimpleGraph V).induce {x | x ∉ p.support}).Adj a b from
      fun heq => hab (Subtype.ext heq)).reachable

end Complete

/-- Transfer shortestness through a graph isomorphism. -/
lemma iso_shortest {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {u v : V} (p : G.Walk u v) (hp : p.length=G.dist u v) :
    (p.map e.toHom).length=H.dist (e u) (e v) := by
  obtain ⟨r,hr⟩ := (p.map e.toHom).reachable.exists_walk_length_eq_dist
  let r' : G.Walk u v := (r.map e.symm.toHom).copy (e.symm_apply_apply u) (e.symm_apply_apply v)
  apply Nat.le_antisymm
  · calc
      (p.map e.toHom).length=p.length := Walk.length_map _ _
      _ = G.dist u v := hp
      _ ≤ r'.length := SimpleGraph.dist_le r'
      _ = r.length := (Walk.length_copy _ _ _).trans (Walk.length_map _ _)
      _ = _ := hr
  · exact SimpleGraph.dist_le _

lemma iso_support {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {u v : V} (p : G.Walk u v) (x : V) :
    e x ∈ (p.map e.toHom).support ↔ x ∈ p.support := by
  rw [Walk.support_map]
  constructor
  · intro hx
    obtain ⟨y,hy,heq⟩ := List.mem_map.mp hx
    exact (e.injective heq) ▸ hy
  · intro hx
    exact List.mem_map.mpr ⟨x,hx,rfl⟩

lemma iso_complement_connected {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {u v : V} (p : G.Walk u v)
    (h : (H.induce {y | y ∉ (p.map e.toHom).support}).Connected) :
    (G.induce {x | x ∉ p.support}).Connected := by
  let e' : (G.induce {x | x ∉ p.support}) ≃g (H.induce {y | y ∉ (p.map e.toHom).support}) := {
    toFun x := ⟨e x.val,(not_congr (iso_support e p x.val)).mpr x.property⟩
    invFun y := ⟨e.symm y.val,(not_congr (iso_support e p _)).mp
      (by rw [e.apply_symm_apply];exact y.property)⟩
    left_inv x := Subtype.ext (e.symm_apply_apply x.val)
    right_inv y := Subtype.ext (e.apply_symm_apply y.val)
    map_rel_iff' := by intro x y;exact e.map_rel_iff }
  exact e'.connected_iff.mpr h

open scoped Classical BigOperators

set_option maxHeartbeats 8000000 in
/-- Geodesic deletion for finite elementary abelian 3-group Cayley graphs. -/
lemma ternary_family {V : Type} [Fintype V] [AddCommGroup V] [Module (ZMod 3) V]
    (S : Set V) (hS : ∀ g ∈ S, -g ∈ S)
    (hconn : (SimpleGraph.fromRel (fun x y : V => y-x ∈ S)).Connected)
    (hcard : 3 ≤ Fintype.card V) {x y : V}
    (p : (SimpleGraph.fromRel (fun x y : V => y-x ∈ S)).Walk x y)
    (hp : p.length=(SimpleGraph.fromRel (fun x y : V => y-x ∈ S)).dist x y) :
    ((SimpleGraph.fromRel (fun x y : V => y-x ∈ S)).induce {v | v ∉ p.support}).Connected := by
  classical
  let TH_graph  (ι : Type) : SimpleGraph (ι → (ZMod 3)) := {
    Adj x y := ∃ i, x i ≠ y i ∧ ∀ j, j ≠ i → x j=y j
    symm.symm := by
      intro x y ⟨i,hi,hrest⟩
      exact ⟨i,hi.symm,fun j hj => (hrest j hj).symm⟩
    loopless.irrefl := by intro x ⟨i,hi,_⟩;exact hi rfl
  }

  have TH_reachable_of_agree_outside {ι : Type} [Fintype ι] (A : Finset ι) (f g : ι → (ZMod 3))
      (h : ∀ i, i ∉ A → f i=g i) : (TH_graph ι).Reachable f g := by
    classical
    induction A using Finset.induction_on generalizing f with
    | empty =>
      have heq : f=g := funext (fun i => h i (Finset.notMem_empty _))
      subst g;exact Reachable.refl _
    | @insert i A hi ih =>
      let t := Function.update f i (g i)
      have ht : ∀ j, j ∉ A → t j=g j := by
        intro j hj
        by_cases hji : j=i
        · subst j;simp [t]
        · simp only [t,Function.update_of_ne hji]
          exact h j (by simpa only [Finset.mem_insert,not_or] using And.intro hji hj)
      have first : (TH_graph ι).Reachable f t := by
        by_cases heq : f i=g i
        · have hf : t=f := by ext j;by_cases hji : j=i <;> simp [t,hji,heq]
          simpa only [hf] using (Reachable.refl (G := TH_graph ι) f)
        · exact (show (TH_graph ι).Adj f t from
            ⟨i,by simpa [t] using heq,fun j hj => by simp [t,hj]⟩).reachable
      exact first.trans (ih t ht)

  have TH_connected {ι : Type} [Fintype ι] : (TH_graph ι).Connected := by
    refine { preconnected := ?_, nonempty := ⟨fun _ => 0⟩ }
    intro f g
    exact TH_reachable_of_agree_outside Finset.univ f g (by simp)

  let TH_coordinateIso {ι κ : Type} (e : ι ≃ κ) : TH_graph ι ≃g TH_graph κ := {
    toFun f j := f (e.symm j)
    invFun f i := f (e i)
    left_inv f := by funext i;simp
    right_inv f := by funext j;simp
    map_rel_iff' := by
      intro f g
      constructor
      · rintro ⟨j,hj,hrest⟩
        refine ⟨e.symm j,hj,?_⟩
        intro i hi
        simpa using hrest (e i) (fun he => hi (by simpa using congrArg e.symm he))
      · rintro ⟨i,hi,hrest⟩
        refine ⟨e i,by simpa using hi,?_⟩
        intro j hj
        exact hrest (e.symm j) (fun he => hj (by simpa using congrArg e he))
  }

  have TH_cons_adj  {n : ℕ} (a b : (ZMod 3)) (f g : Fin n → (ZMod 3)) :
      (TH_graph (Fin (n+1))).Adj (Fin.cons a f) (Fin.cons b g) ↔
        (a ≠ b ∧ f=g) ∨ ((TH_graph (Fin n)).Adj f g ∧ a=b) := by
    constructor
    · rintro ⟨i,hi,hrest⟩
      cases i using Fin.cases with
      | zero =>
        refine Or.inl ⟨by simpa using hi,funext fun j => ?_⟩
        simpa using hrest j.succ (by simp)
      | succ i =>
        refine Or.inr ⟨⟨i,by simpa using hi,?_⟩,?_⟩
        · intro j hj
          simpa using hrest j.succ (by simpa using hj)
        · simpa using hrest 0 (Fin.succ_ne_zero i).symm
    · rintro (⟨hab,rfl⟩ | ⟨⟨i,hi,hrest⟩,rfl⟩)
      · refine ⟨0,by simpa using hab,?_⟩
        intro j hj
        cases j using Fin.cases with
        | zero => exact False.elim (hj rfl)
        | succ j => rfl
      · refine ⟨i.succ,by simpa using hi,?_⟩
        intro j hj
        cases j using Fin.cases with
        | zero => rfl
        | succ j => simpa using hrest j (by simpa using hj)

  let TH_succIso  (n : ℕ) : TH_graph (Fin (n+1)) ≃g
      (⊤ : SimpleGraph (ZMod 3)) □ TH_graph (Fin n) := {
    toEquiv := (Fin.consEquiv (fun _ : Fin (n+1) => (ZMod 3))).symm
    map_rel_iff' := by
      intro f g
      change ((f 0 ≠ g 0 ∧ Fin.tail f=Fin.tail g) ∨
        (TH_graph (Fin n)).Adj (Fin.tail f) (Fin.tail g) ∧ f 0=g 0) ↔ _
      simpa only [Fin.cons_self_tail] using (TH_cons_adj (f 0) (g 0) (Fin.tail f) (Fin.tail g)).symm
  }

  have TH_geodesic_complement_connected {ι : Type} [Fintype ι] (hdim : 0 < Fintype.card ι)
      {f g : ι → (ZMod 3)} (p : (TH_graph ι).Walk f g) (hp : p.length=(TH_graph ι).dist f g) :
      ((TH_graph ι).induce {z | z ∉ p.support}).Connected := by
    classical
    obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hdim)
    let e : TH_graph ι ≃g (⊤ : SimpleGraph (ZMod 3)) □ TH_graph (Fin n) :=
      (TH_coordinateIso (Fintype.equivFinOfCardEq hn)).trans (TH_succIso n)
    have hdel : ∀ {a c} (q : (⊤ : SimpleGraph (ZMod 3)).Walk a c),
        q.length=(⊤ : SimpleGraph (ZMod 3)).dist a c →
        ((⊤ : SimpleGraph (ZMod 3)).induce {z | z ∉ q.support}).Connected := by
      intro a c q hq
      exact Complete.complete_complement_connected (by decide) q hq
    have hc := Product.geodesic_complement_product
      (by exact SimpleGraph.connected_top) (TH_connected (ι := Fin n)) hdel
      (p.map e.toHom) (iso_shortest e p hp)
    exact iso_complement_connected e p hc

  have TN_field_cases  (x : (ZMod 3)) : x=0 ∨ x=1 ∨ x= -1 :=
    (by decide : ∀ x : (ZMod 3), x=0 ∨ x=1 ∨ x= -1) x

  let TN_graph {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (S : Set V) : SimpleGraph V := SimpleGraph.fromRel (fun x y => y-x ∈ S)

  have TN_graph_adj_iff {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (S : Set V) (hS : ∀ g ∈ S, -g ∈ S) (x y : V) :
      (TN_graph S).Adj x y ↔ x ≠ y ∧ y-x ∈ S := by
    simp only [TN_graph,SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hne,hg | hg⟩
      · exact ⟨hne,hg⟩
      · exact ⟨hne,by simpa only [neg_sub] using hS (x-y) hg⟩
    · rintro ⟨hne,hg⟩
      exact ⟨hne,Or.inl hg⟩

  let TN_translateIso {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (S : Set V) (a : V) : TN_graph S ≃g TN_graph S := {
    toFun x := a+x
    invFun x := -a+x
    left_inv x := by simp
    right_inv x := by simp
    map_rel_iff' := by
      intro x y
      simp [TN_graph,SimpleGraph.fromRel_adj,add_sub_add_left_eq_sub]
  }

  let TN_edgeDifference {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {S : Set V} {x y : V} (_ : (TN_graph S).Adj x y) : V := y-x

  let TN_steps {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {S : Set V} {x y : V} (p : (TN_graph S).Walk x y) : List V := by
    induction p with
    | nil => exact []
    | cons h p ih => exact TN_edgeDifference h :: ih

  have TN_steps_length {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {S : Set V} {x y : V} (p : (TN_graph S).Walk x y) :
      (TN_steps p).length=p.length := by
    induction p with
    | nil => rfl
    | cons h p ih => simpa only [TN_steps,Walk.length_cons,List.length_cons] using congrArg Nat.succ ih

  have TN_steps_mem {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {S : Set V} (hS : ∀ g ∈ S, -g ∈ S) {x y : V} (p : (TN_graph S).Walk x y) :
      ∀ g ∈ TN_steps p, g ∈ S ∧ g ≠ 0 := by
    induction p with
    | nil => simp [TN_steps]
    | @cons x u y h p ih =>
      intro g hg
      simp only [TN_steps,List.mem_cons] at hg
      rcases hg with rfl | hg
      · have hs := (TN_graph_adj_iff S hS x u).mp h
        exact ⟨hs.2,sub_ne_zero.mpr hs.1.symm⟩
      · exact ih g hg

  have TN_steps_sum {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {S : Set V} {x y : V} (p : (TN_graph S).Walk x y) :
      (TN_steps p).sum=y-x := by
    induction p with
    | nil => simp [TN_steps]
    | @cons x u y h p ih => simp only [TN_steps,List.sum_cons,TN_edgeDifference,ih];abel

  have TN_steps_get_sum {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {S : Set V} {x y : V} (p : (TN_graph S).Walk x y) :
      (∑ i : Fin (TN_steps p).length,(TN_steps p).get i)=y-x := by
    calc
      (∑ i : Fin (TN_steps p).length,(TN_steps p).get i)=(List.ofFn (TN_steps p).get).sum := (Fin.sum_ofFn _).symm
      _=(TN_steps p).sum := by rw [List.ofFn_get]
      _=y-x := TN_steps_sum p

  have TN_walk_sum {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (S : Set V) (hS : ∀ g ∈ S, -g ∈ S) {ι : Type} (A : Finset ι) (g : ι → V)
      (hg : ∀ i ∈ A, g i ∈ S ∧ g i ≠ 0) :
      ∃ p : (TN_graph S).Walk 0 (∑ i ∈ A,g i), p.length=A.card := by
    classical
    revert hg
    induction A using Finset.induction_on with
    | empty => intro _;exact ⟨Walk.nil,by simp⟩
    | @insert a A ha ih =>
      intro hg
      obtain ⟨p,hp⟩ := ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      have hga := hg a (Finset.mem_insert_self a A)
      have hadj : (TN_graph S).Adj (∑ i ∈ A,g i) (g a+∑ i ∈ A,g i) := by
        apply (TN_graph_adj_iff S hS _ _).mpr
        exact ⟨(add_ne_right.mpr hga.2).symm,by simpa using hga.1⟩
      rw [Finset.sum_insert ha]
      refine ⟨p.append hadj.toWalk,?_⟩
      simp [hp,Finset.card_insert_of_notMem ha]

  have TN_walk_diff_mem_span {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {S : Set V} (hS : ∀ g ∈ S, -g ∈ S) {x y : V}
      (p : (TN_graph S).Walk x y) : y-x ∈ Submodule.span (ZMod 3) S := by
    induction p with
    | nil => simp
    | @cons x u y h p ih =>
      have hs : u-x ∈ Submodule.span (ZMod 3) S := Submodule.subset_span ((TN_graph_adj_iff S hS x u).mp h).2
      have hsum := (Submodule.span (ZMod 3) S).add_mem hs ih
      convert hsum using 1 <;> abel

  have TN_span_generators {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (S : Set V) (hS : ∀ g ∈ S, -g ∈ S) (hconn : (TN_graph S).Connected) :
      Submodule.span (ZMod 3) S=⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro y
    obtain ⟨p⟩ := hconn.preconnected 0 y
    simpa using TN_walk_diff_mem_span hS p

  have TN_shortest_steps_linearIndependent {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {S : Set V} (hS : ∀ g ∈ S, -g ∈ S) {x y : V}
      (p : (TN_graph S).Walk x y) (hp : p.length=(TN_graph S).dist x y) :
      LinearIndependent (ZMod 3) (fun i : Fin (TN_steps p).length => (TN_steps p).get i) := by
    classical
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    by_contra hci
    let g := (TN_steps p).get
    let w (j : Fin (TN_steps p).length) := (1-(c i)⁻¹*c j) • g j
    let A := Finset.univ.filter (fun j => w j ≠ 0)
    have hwi : w i=0 := by simp [w,inv_mul_cancel₀ hci]
    have hsum : (∑ j ∈ A,w j)=y-x := by
      calc
        (∑ j ∈ A,w j)=∑ j,w j := by
          simp only [A,Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro j _
          by_cases hz : w j=0 <;> simp [hz]
        _=(∑ j,g j)-(c i)⁻¹ • (∑ j,c j • g j) := by
          simp only [w,sub_smul,one_smul,mul_smul,Finset.sum_sub_distrib,Finset.smul_sum]
        _=y-x := by rw [hc,smul_zero,sub_zero];exact TN_steps_get_sum p
    have hwS : ∀ j ∈ A, w j ∈ S ∧ w j ≠ 0 := by
      intro j hj
      have hne := (Finset.mem_filter.mp hj).2
      have hgj := (TN_steps_mem hS p (g j) (List.get_mem _ j)).1
      refine ⟨?_,hne⟩
      rcases TN_field_cases (1-(c i)⁻¹*c j) with hz | ho | hm
      · exact False.elim (hne (by simp [w,hz]))
      · simpa [w,ho] using hgj
      · simpa [w,hm] using hS (g j) hgj
    obtain ⟨q,hq⟩ := TN_walk_sum S hS A w hwS
    let q' : (TN_graph S).Walk x y := (q.map (TN_translateIso S x).toHom).copy
      (by simp [TN_translateIso]) (by simp [TN_translateIso,hsum])
    have hlen : q'.length=A.card := by simpa only [q',Walk.length_copy,Walk.length_map] using hq
    have hproper : A ⊂ Finset.univ := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _,?_⟩
      intro heq
      have hi : i ∈ A := heq ▸ Finset.mem_univ i
      exact (Finset.mem_filter.mp hi).2 hwi
    have hcard := Finset.card_lt_card hproper
    simp only [Finset.card_univ,Fintype.card_fin] at hcard
    have hshort := SimpleGraph.dist_le q'
    rw [← hp,hlen] at hshort
    have hlength := TN_steps_length p
    omega

  let TN_hammingToGraph {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Type} [Fintype ι] (S : Set V) (hS : ∀ g ∈ S, -g ∈ S)
      (b : Module.Basis ι (ZMod 3) V) (hb : ∀ i,b i ∈ S) : TH_graph ι →g TN_graph S := {
    toFun := b.equivFun.symm
    map_rel' := by
      classical
      intro f g ⟨i,hi,hrest⟩
      apply (TN_graph_adj_iff S hS _ _).mpr
      refine ⟨fun he => hi (congrFun (b.equivFun.symm.injective he) i),?_⟩
      let c := g i-f i
      have hd : b.equivFun.symm g-b.equivFun.symm f=c • b i := by
        apply b.equivFun.injective
        ext j
        simp only [map_sub,LinearEquiv.apply_symm_apply,map_smul,Pi.sub_apply,Pi.smul_apply,
          Module.Basis.equivFun_self,smul_eq_mul]
        by_cases hij : i=j
        · subst j;simp [c]
        · have hj := hrest j (Ne.symm hij)
          simp [hij,hj]
      rw [hd]
      rcases TN_field_cases c with hz | ho | hm
      · exact False.elim (hi (sub_eq_zero.mp hz).symm)
      · simpa [ho] using hb i
      · simpa [hm] using hS (b i) (hb i)
  }

  have TN_basis_step_lift {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Type} [Fintype ι] (b : Module.Basis ι (ZMod 3) V) (x y : V) (h : ∃ i,y-x=b i) :
      (TH_graph ι).Adj (b.equivFun x) (b.equivFun y) := by
    classical
    obtain ⟨i,hi⟩ := h
    have hd : b.equivFun y-b.equivFun x=b.equivFun (b i) := by rw [← map_sub,hi]
    refine ⟨i,?_,?_⟩
    · intro he
      have h := congrFun hd i
      simp only [Pi.sub_apply,Module.Basis.equivFun_self,if_true] at h
      rw [he,sub_self] at h
      norm_num at h
    · intro j hj
      have h := congrFun hd j
      simp only [Pi.sub_apply,Module.Basis.equivFun_self,if_neg hj.symm] at h
      exact (sub_eq_zero.mp h).symm

  have TN_lift_walk_to_basis {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Type} [Fintype ι] (S : Set V) (b : Module.Basis ι (ZMod 3) V)
      {x y : V} (p : (TN_graph S).Walk x y) (hb : ∀ g ∈ TN_steps p,g ∈ Set.range b) :
      ∃ q : (TH_graph ι).Walk (b.equivFun x) (b.equivFun y),
        q.length=p.length ∧ q.support.map b.equivFun.symm=p.support := by
    induction p with
    | nil => exact ⟨Walk.nil,rfl,by simp⟩
    | @cons x u y h p ih =>
      obtain ⟨i,hi⟩ := hb (u-x) (by simp [TN_steps,TN_edgeDifference])
      have htail : ∀ g ∈ TN_steps p,g ∈ Set.range b :=
        fun g hg => hb g (List.mem_cons_of_mem _ hg)
      obtain ⟨q,hq,hqs⟩ := ih htail
      refine ⟨Walk.cons (TN_basis_step_lift b x u ⟨i,hi.symm⟩) q,?_,?_⟩
      · simpa only [Walk.length_cons] using congrArg Nat.succ hq
      · simp only [Walk.support_cons,List.map_cons,hqs]
        rw [b.equivFun.symm_apply_apply]

  have TN_basis_geodesic_complement {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Type} [Fintype ι] (S : Set V) (hS : ∀ g ∈ S, -g ∈ S)
      (b : Module.Basis ι (ZMod 3) V) (hb : ∀ i,b i ∈ S) (hdim : 0 < Fintype.card ι)
      {x y : V} (p : (TN_graph S).Walk x y) (hp : p.length=(TN_graph S).dist x y)
      (hbsteps : ∀ g ∈ TN_steps p,g ∈ Set.range b) :
      ((TN_graph S).induce {v | v ∉ p.support}).Connected := by
    classical
    let e := b.equivFun.symm.toEquiv
    let f := TN_hammingToGraph S hS b hb
    obtain ⟨q,hq,hqs⟩ := TN_lift_walk_to_basis S b p hbsteps
    obtain ⟨r,hr⟩ := q.reachable.exists_walk_length_eq_dist
    let r' : (TN_graph S).Walk x y := (r.map f).copy (e.apply_symm_apply x) (e.apply_symm_apply y)
    have hbound : p.length ≤ (TH_graph ι).dist (e.symm x) (e.symm y) := by
      calc
        p.length=(TN_graph S).dist x y := hp
        _ ≤ r'.length := SimpleGraph.dist_le r'
        _=r.length := (Walk.length_copy (r.map f) _ _).trans (Walk.length_map f r)
        _=_ := hr
    have hqshort : q.length=(TH_graph ι).dist (e.symm x) (e.symm y) :=
      Nat.le_antisymm (hq ▸ hbound) (SimpleGraph.dist_le q)
    have hconn := TH_geodesic_complement_connected hdim q hqshort
    have hoff (A : ι → (ZMod 3)) : A ∉ q.support ↔ e A ∉ p.support := by
      constructor
      · intro hA heA
        rw [← hqs] at heA
        obtain ⟨B,hB,hBA⟩ := List.mem_map.mp heA
        exact hA ((e.injective hBA) ▸ hB)
      · intro he hA
        apply he
        rw [← hqs]
        exact List.mem_map.mpr ⟨A,hA,rfl⟩
    let g : ((TH_graph ι).induce {A | A ∉ q.support}) →g
        ((TN_graph S).induce {v | v ∉ p.support}) := {
      toFun := fun A => ⟨e A.val,(hoff A.val).mp A.property⟩
      map_rel' := by intro A B h;exact f.map_adj h }
    have hsurj : Function.Surjective g := by
      intro v
      have hv : e (e.symm v.val) ∉ p.support := by rw [e.apply_symm_apply];exact v.property
      refine ⟨⟨e.symm v.val,(hoff _).mpr hv⟩,?_⟩
      exact Subtype.ext (e.apply_symm_apply v.val)
    exact hconn.map g hsurj

  have TN_geodesic_complement_connected {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Fintype V] (S : Set V) (hS : ∀ g ∈ S, -g ∈ S)
      (hconn : (TN_graph S).Connected) (hcard : 3 ≤ Fintype.card V)
      {x y : V} (p : (TN_graph S).Walk x y) (hp : p.length=(TN_graph S).dist x y) :
      ((TN_graph S).induce {v | v ∉ p.support}).Connected := by
    classical
    let v : Fin (TN_steps p).length → V := (TN_steps p).get
    have hlin : LinearIndependent (ZMod 3) v := TN_shortest_steps_linearIndependent hS p hp
    have hs : LinearIndepOn (ZMod 3) id (Set.range v) := hlin.linearIndepOn_id
    have hsub : Set.range v ⊆ S := by
      rintro z ⟨i,rfl⟩
      exact (TN_steps_mem hS p (v i) (List.get_mem _ i)).1
    have hspan : ⊤ ≤ Submodule.span (ZMod 3) S := by rw [TN_span_generators S hS hconn]
    let b := Module.Basis.extendLe hs hsub hspan
    have hbin : ∀ i,b i ∈ S := fun i => Module.Basis.extendLe_subset hs hsub hspan ⟨i,rfl⟩
    have hbsteps : ∀ z ∈ TN_steps p,z ∈ Set.range b := by
      intro z hz
      apply Module.Basis.subset_extendLe hs hsub hspan
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hz
      exact ⟨i,hi⟩
    have hecard := Fintype.card_congr b.equivFun.symm.toEquiv
    have hdim : 0 < Fintype.card (hs.extend hsub) := by
      by_contra! h
      have hz : Fintype.card (hs.extend hsub)=0 := Nat.eq_zero_of_le_zero h
      simp only [Fintype.card_fun,hz,pow_zero] at hecard
      omega
    exact TN_basis_geodesic_complement S hS b hbin hdim p hp hbsteps

  exact TN_geodesic_complement_connected S hS hconn hcard p hp

/-- An undirected difference graph already uses the symmetric hull of its generators. -/
lemma symmetric_generator_hull {V : Type} [AddCommGroup V] (S : Set V) :
    SimpleGraph.fromRel (fun x y : V => y-x ∈ S) =
      SimpleGraph.fromRel (fun x y : V => y-x ∈ {g | g ∈ S ∨ -g ∈ S}) := by
  ext x y
  simp only [SimpleGraph.fromRel_adj,Set.mem_setOf_eq,neg_sub]
  tauto

lemma ternary_family_any {V : Type} [Fintype V] [AddCommGroup V] [Module (ZMod 3) V]
    (S : Set V) (hconn : (SimpleGraph.fromRel (fun x y : V => y-x ∈ S)).Connected)
    (hcard : 3 ≤ Fintype.card V) {x y : V}
    (p : (SimpleGraph.fromRel (fun x y : V => y-x ∈ S)).Walk x y)
    (hp : p.length=(SimpleGraph.fromRel (fun x y : V => y-x ∈ S)).dist x y) :
    ((SimpleGraph.fromRel (fun x y : V => y-x ∈ S)).induce {v | v ∉ p.support}).Connected := by
  let T : Set V := {g | g ∈ S ∨ -g ∈ S}
  have hT : ∀ g ∈ T, -g ∈ T := by
    intro g hg
    rcases hg with hg | hg
    · exact Or.inr (by simpa only [neg_neg] using hg)
    · exact Or.inl hg
  have heq := symmetric_generator_hull S
  have hc : (SimpleGraph.fromRel (fun x y : V => y-x ∈ T)).Connected := by
    rw [← heq]
    exact hconn
  have hdel : ∀ {a c} (q : (SimpleGraph.fromRel (fun x y : V => y-x ∈ T)).Walk a c),
      q.length=(SimpleGraph.fromRel (fun x y : V => y-x ∈ T)).dist a c →
      ((SimpleGraph.fromRel (fun x y : V => y-x ∈ T)).induce {v | v ∉ q.support}).Connected := by
    intro a c q hq
    exact ternary_family T hT hc hcard q hq
  dsimp only [T] at hdel
  rw [← heq] at hdel
  exact hdel p hp

lemma iso_vertex_transitive {V W : Type} {G : SimpleGraph V} {J : SimpleGraph W}
    (e : G ≃g J) (h : OMA.S_gillibert_geodesic_deletion.IsVertexTransitive G) :
    OMA.S_gillibert_geodesic_deletion.IsVertexTransitive J := by
  intro x y
  obtain ⟨φ,hφ⟩ := h (e.symm x) (e.symm y)
  refine ⟨(e.symm.trans φ).trans e,?_⟩
  change e (φ (e.symm x))=y
  rw [hφ,e.apply_symm_apply]

/-- The open core: graphs outside the proved binary and ternary Cayley families and without a
nontrivial Cartesian factor of order at least three. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
    G.Connected → OMA.S_gillibert_geodesic_deletion.IsVertexTransitive G →
    3 ≤ Fintype.card V → G ≠ ⊤ →
    (¬ ∃ (q n : ℕ) (S : Set (Fin n → ZMod q)),
      (q=2 ∨ q=3) ∧
      Nonempty (G ≃g SimpleGraph.fromRel (fun x y : Fin n → ZMod q => y-x ∈ S))) →
    (¬ ∃ (m n : ℕ) (A : SimpleGraph (Fin m)) (B : SimpleGraph (Fin n)),
      3 ≤ m ∧ 2 ≤ n ∧ Nonempty (G ≃g A □ B)) →
    ∀ u v (p : G.Walk u v), p.IsPath → p.length=G.dist u v →
      (G.induce {x | x ∉ p.support}).Connected

/-- Known Cartesian-factor transitivity, left explicitly for formalization.
See Soltani and Iranmanesh, On the Edge Wiener Index (2014), Theorem 2.14;
also R. Hammack, W. Imrich and S. Klavzar, Handbook of Product Graphs,
2nd ed., CRC Press (2011), Cartesian products and vertex-transitivity of factors. -/
def H2 : Prop :=
  ∀ (m n : ℕ) (A : SimpleGraph (Fin m)) (B : SimpleGraph (Fin n)),
    A.Connected → B.Connected →
    OMA.S_gillibert_geodesic_deletion.IsVertexTransitive (A □ B) →
    OMA.S_gillibert_geodesic_deletion.IsVertexTransitive A

theorem main : H1 → H2 → type_of% @OMA.S_gillibert_geodesic_deletion.main := by
  classical
  intro h1 h2
  have core : ∀ k : ℕ, ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
      Fintype.card V=k → G.Connected →
      OMA.S_gillibert_geodesic_deletion.IsVertexTransitive G →
      3 ≤ Fintype.card V →
      ∀ u v (p : G.Walk u v), p.IsPath → p.length=G.dist u v →
        (G.induce {x | x ∉ p.support}).Connected := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro V _ G horder hconn htrans hsize u v p hpath hp
      by_cases hcomplete : G=⊤
      · subst G
        exact Complete.complete_complement_connected hsize p hp
      ·
        by_cases hsmall : ∃ (q n : ℕ) (S : Set (Fin n → ZMod q)),
            (q=2 ∨ q=3) ∧
            Nonempty (G ≃g SimpleGraph.fromRel (fun x y : Fin n → ZMod q => y-x ∈ S))
        · obtain ⟨q,n,S,hq,⟨e⟩⟩ := hsmall
          rcases hq with rfl | rfl
          · have hc := e.connected_iff.mp hconn
            have hn : 3 ≤ Fintype.card (Fin n → ZMod 2) := by
              rw [← Fintype.card_congr e.toEquiv]
              exact hsize
            exact iso_complement_connected e p
              (cubelike_family S hc hn (p.map e.toHom) (iso_shortest e p hp))
          · have hc := e.connected_iff.mp hconn
            have hn : 3 ≤ Fintype.card (Fin n → ZMod 3) := by
              rw [← Fintype.card_congr e.toEquiv]
              exact hsize
            exact iso_complement_connected e p
              (ternary_family_any S hc hn (p.map e.toHom) (iso_shortest e p hp))
        · by_cases hfactor : ∃ (m n : ℕ) (A : SimpleGraph (Fin m)) (B : SimpleGraph (Fin n)),
              3 ≤ m ∧ 2 ≤ n ∧ Nonempty (G ≃g A □ B)
          · obtain ⟨m,n,A,B,hm3,hn2,⟨e⟩⟩ := hfactor
            have hc := e.connected_iff.mp hconn
            have ht := h2 m n A B hc.ofBoxProdLeft hc.ofBoxProdRight (iso_vertex_transitive e htrans)
            have hmn : k=m*n := by
              calc
                k=Fintype.card V := horder.symm
                _=Fintype.card (Fin m × Fin n) := Fintype.card_congr e.toEquiv
                _=m*n := by simp only [Fintype.card_prod,Fintype.card_fin]
            have hm : m<k := by rw [hmn];nlinarith
            have hAdel : ∀ {a c} (q : A.Walk a c), q.length=A.dist a c →
                (A.induce {z | z ∉ q.support}).Connected := by
              intro a c q hq
              exact ih m hm A (Fintype.card_fin m) hc.ofBoxProdLeft ht
                (by simpa only [Fintype.card_fin] using hm3) a c q
                (q.isPath_of_length_eq_dist hq) hq
            exact iso_complement_connected e p
              (Product.geodesic_complement_product hc.ofBoxProdLeft hc.ofBoxProdRight hAdel
                (p.map e.toHom) (iso_shortest e p hp))
          · exact h1 G hconn htrans hsize hcomplete hsmall hfactor u v p hpath hp
  intro V _ G hconn htrans hsize u v p hpath hp
  exact core (Fintype.card V) G rfl hconn htrans hsize u v p hpath hp

end OMA.R_gillibert_geodesic_deletion_R1
