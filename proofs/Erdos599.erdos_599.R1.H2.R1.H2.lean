import OMAReductions.R_Erdos599_erdos_599_R1_H2_R1

open SimpleGraph

private theorem trimSource {V : Type} {G : SimpleGraph V} {A : Set V} {u t : V}
    (w : G.Walk u t) (hu : u ∈ A) (hw : w.IsPath) :
    ∃ x ∈ A, ∃ q : G.Walk x t, q.IsPath ∧ q.support ⊆ w.support ∧
      ∀ y ∈ q.support.tail, y ∉ A := by
  classical
  let eligible (n : ℕ) := ∃ x ∈ A, ∃ q : G.Walk x t,
    q.IsPath ∧ q.support ⊆ w.support ∧ q.length = n
  have h : ∃ n, eligible n := ⟨_, u, hu, w, hw, List.Subset.refl _, rfl⟩
  obtain ⟨x, hx, q, hp, hsub, hlen⟩ := Nat.find_spec h
  refine ⟨x, hx, q, hp, hsub, ?_⟩
  intro y hy hA
  have hmem : y ∈ q.support := List.mem_of_mem_tail hy
  have hne : y ≠ x := by
    rintro rfl
    have hn : (y :: q.support.tail).Nodup := by simpa using hp.support_nodup
    exact (List.nodup_cons.mp hn).1 hy
  have hshort := q.length_dropUntil_lt_length hmem hne
  have hmin := Nat.find_min' h (show eligible (q.dropUntil y hmem).length from
    ⟨y, hA, _, hp.dropUntil hmem,
      (fun _ hm => hsub (q.support_dropUntil_subset_support hmem hm)), rfl⟩)
  omega

theorem OMA.solution : OMA.R_Erdos599_erdos_599_R1_H2_R1.H2 := by
  classical
  intro V G A B hcover ι a b p S ha hb hp hdisj hsub hu hsep
  have packed (t : S) : ∃ i, t.val ∈ (p i).support := hsub t.property
  choose index hindex using packed
  have only (t : S) (z : V) (hz : z ∈ S) (h : z ∈ (p (index t)).support) : z = t.val :=
    (hu (index t)).unique ⟨hz, h⟩ ⟨t.property, hindex t⟩
  have hinj : Function.Injective index := by
    intro t u he
    exact Subtype.ext ((only t u.val u.property (he ▸ hindex u)).symm)
  have trimmed (t : S) : ∃ x ∈ A, ∃ q : G.Walk x t.val, q.IsPath ∧
      q.support ⊆ (p (index t)).support ∧ ∀ z ∈ q.support.tail, z ∉ A := by
    obtain ⟨x, hx, q, hq, hsubq, htail⟩ := trimSource
      ((p (index t)).takeUntil t.val (hindex t)) (ha _) ((hp _).takeUntil (hindex t))
    exact ⟨x, hx, q, hq,
      (fun _ hm => (p (index t)).support_takeUntil_subset_support (hindex t) (hsubq hm)), htail⟩
  choose x hx q hq hqsub htail using trimmed
  have hfront (t : S) (z : V) (hz : z ∈ (q t).support.dropLast) : z ∉ B := by
    intro hzB
    have hnd : ((q t).support.dropLast ++ [t.val]).Nodup := by
      simpa using (hq t).support_nodup
    have hne : t.val ≠ z := by
      rintro rfl
      exact (List.disjoint_of_nodup_append hnd) hz (by simp)
    have hm : z ∈ (q t).support := List.dropLast_subset _ hz
    obtain ⟨v, hvm, hvS⟩ := hsep _ (hx t) _ hzB _ ((hq t).takeUntil hm)
    have hv := only t v hvS (hqsub t ((q t).support_takeUntil_subset_support hm hvm))
    exact Walk.endpoint_notMem_support_takeUntil (hq t) hm hne (hv ▸ hvm)
  have surj := hcover S x q hx hq (fun t => ⟨htail t, hfront t⟩) (by
    intro t u hne
    exact (hdisj (hinj.ne hne)).mono (fun _ h => hqsub t h) (fun _ h => hqsub u h)) hsep
  have assigned (v : A) : ∃ t, x t = v.val := surj v.val v.property
  choose pick hpick using assigned
  have pickinj : Function.Injective pick := by
    intro u v he
    exact Subtype.ext ((hpick u).symm.trans (he ▸ hpick v))
  have hstart (v : A) : v.val ∈ (p (index (pick v))).support :=
    hpick v ▸ hqsub (pick v) (q (pick v)).start_mem_support
  refine ⟨fun v => b (index (pick v)), fun v => (p _).dropUntil v.val (hstart v),
    fun _ => hb _, ?_⟩
  intro v w hne
  exact (hdisj (hinj.ne (pickinj.ne hne))).mono
    (fun _ h => (p _).support_dropUntil_subset_support (hstart v) h)
    (fun _ h => (p _).support_dropUntil_subset_support (hstart w) h)
