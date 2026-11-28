import OMAStatements.S_oeis_a386575

namespace OMA.S_oeis_a386575

open Finset

private theorem chain_on {α : Type} {R S : α → α → Prop} {l : List α}
    (h : l.IsChain R) (imp : ∀ a ∈ l, ∀ b ∈ l, R a b → S a b) : l.IsChain S := by
  rw [List.isChain_iff_getElem] at h ⊢
  intro i hi
  exact imp _ (List.getElem_mem _) _ (List.getElem_mem _) (h i hi)

private theorem replicate_chain (n p : ℕ) :
    (List.replicate n p).IsChain (fun x y => (x == y) = true) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  simp

private theorem replicate_nonempty {n p : ℕ} (h : 0 < n) : List.replicate n p ≠ [] :=
  List.length_pos_iff.mp (by simpa using h)

private theorem same_values {l : List ℕ} {p : ℕ} (h : ∀ x ∈ l, x = p) :
    List.replicate l.length p = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    have hl := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    change p :: List.replicate l.length p = a :: l
    rw [ha, hl]

private theorem constant_run {l : List ℕ} (h : l.IsChain (fun x y => (x == y) = true)) :
    List.replicate l.length (l.headD 0) = l := by
  cases l with
  | nil => rfl
  | cons p l =>
    simp only [beq_iff_eq] at h
    apply same_values
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · rfl
    · exact ((List.pairwise_cons.mp h.pairwise).1 _ hx).symm

private theorem value_in_run {l : List ℕ} {x : ℕ}
    (h : l.IsChain (fun a b => (a == b) = true)) (hx : x ∈ l) : x = l.headD 0 := by
  have hm : x ∈ List.replicate l.length (l.headD 0) := by rwa [constant_run h]
  exact (List.mem_replicate.mp hm).2

private theorem count_blocks (w : List ℕ) (label : ℕ → ℕ) (p : ℕ) :
    ((w.map (fun x => List.replicate x (label x))).flatten).count p =
      (w.filter (fun x => label x == p)).sum := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    cases h : label x == p <;>
      simp [List.count_append, List.count_replicate, h, ih]

private theorem count_runs (bs : List (List ℕ)) (p : ℕ)
    (h : ∀ b ∈ bs, b.IsChain (fun x y => (x == y) = true)) :
    bs.flatten.count p = ((bs.filter (fun b => b.headD 0 == p)).map List.length).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hb := h b List.mem_cons_self
    have hc := congrArg (List.count p) (constant_run hb)
    have ht := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    rw [List.count_replicate] at hc
    simp only [List.flatten_cons, List.count_append, ← hc, ht, List.filter_cons]
    split <;> simp_all [List.headD]

private theorem runs_of_family {n : ℕ} : HasSeparableFamily n → HasDistinctRunPerm n := by
  classical
  rintro ⟨S, hzero, hsums, hdisjoint, w, hw, hmem, hchain⟩
  let label (x : ℕ) : ℕ := if h : ∃ p, x ∈ S p then Classical.choose h else 0
  have hlabel (x : ℕ) (hx : x ∈ w) : x ∈ S (label x) := by
    have he := (hmem x).mp hx
    simpa only [label, dif_pos he] using Classical.choose_spec he
  have hpositive (x : ℕ) (hx : x ∈ w) : 0 < x := by
    apply Nat.pos_of_ne_zero
    rintro rfl
    exact hzero (label 0) (hlabel 0 hx)
  have hlabels : w.IsChain (fun x y => label x ≠ label y) := by
    refine chain_on hchain ?_
    intro x hx y hy hxy he
    apply hxy (label x) (hlabel x hx)
    rw [he]
    exact hlabel y hy
  let bs := w.map (fun x => List.replicate x (label x))
  have hbs : [] ∉ bs := by
    intro hm
    obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
    exact replicate_nonempty (hpositive x hx) he
  have hinner (b : List ℕ) (hb : b ∈ bs) :
      b.IsChain (fun x y => (x == y) = true) := by
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hb
    exact replicate_chain x (label x)
  have houter : bs.IsChain (fun a b =>
      ∃ ha hb, ((a.getLast ha) == b.head hb) = false) := by
    rw [show bs = w.map (fun x => List.replicate x (label x)) from rfl, List.isChain_map]
    refine chain_on hlabels ?_
    intro x hx y hy h
    refine ⟨replicate_nonempty (hpositive x hx), replicate_nonempty (hpositive y hy), ?_⟩
    rw [List.getLast_replicate, List.head_replicate]
    simp [h]
  refine ⟨bs.flatten, ?_, ?_⟩
  · apply Multiset.ext.mpr
    intro p
    rw [Multiset.coe_count, Multiset.coe_count, Nat.primeFactorsList_count_eq,
      show bs.flatten.count p = (w.filter (fun x => label x == p)).sum from count_blocks w label p]
    have hfilter : (w.filter (fun x => label x == p)).toFinset = S p := by
      ext x
      simp only [List.mem_toFinset, List.mem_filter, beq_iff_eq]
      constructor
      · rintro ⟨hx, rfl⟩
        exact hlabel x hx
      · intro hx
        have hwx := (hmem x).mpr ⟨p, hx⟩
        refine ⟨hwx, ?_⟩
        by_contra h
        exact Finset.disjoint_left.mp (hdisjoint (label x) p h) (hlabel x hwx) hx
    have hs := List.sum_toFinset id (hw.filter (fun x => label x == p))
    rw [hfilter] at hs
    simpa using hs.symm.trans (hsums p)
  · rw [List.splitBy_flatten hbs hinner houter]
    simpa [bs, List.map_map, Function.comp_def] using hw

private theorem family_of_runs {n : ℕ} : HasDistinctRunPerm n → HasSeparableFamily n := by
  classical
  rintro ⟨l, hl, hn⟩
  let bs := l.splitBy (fun x y => x == y)
  let S (p : ℕ) := ((bs.filter (fun b => b.headD 0 == p)).map List.length).toFinset
  have hs (p d : ℕ) : d ∈ S p ↔ ∃ b ∈ bs, b.headD 0 = p ∧ b.length = d := by
    simp only [S, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq]
    aesop
  have hcount (p : ℕ) : l.count p = n.factorization p := by
    rw [← Multiset.coe_count, hl, Multiset.coe_count, Nat.primeFactorsList_count_eq]
  have hinner (b : List ℕ) (hb : b ∈ bs) :
      b.IsChain (fun x y => (x == y) = true) := List.isChain_of_mem_splitBy hb
  have hunique {a b : List ℕ} (ha : a ∈ bs) (hb : b ∈ bs) (he : a.length = b.length) :
      a = b := List.inj_on_of_nodup_map hn ha hb he
  refine ⟨S, ?_, ?_, ?_, bs.map List.length, hn, ?_, ?_⟩
  · intro p hp
    obtain ⟨b, hb, _, he⟩ := (hs p 0).mp hp
    exact (List.ne_nil_of_mem_splitBy hb) (List.length_eq_zero_iff.mp he)
  · intro p
    have hsub : (bs.filter (fun b => b.headD 0 == p)).Sublist bs := List.filter_sublist
    have hn' : ((bs.filter (fun b => b.headD 0 == p)).map List.length).Nodup :=
      (hsub.map _).nodup hn
    change (S p).sum id = n.factorization p
    unfold S
    rw [List.sum_toFinset id hn', List.map_id]
    rw [← count_runs bs p hinner, show bs.flatten = l from List.flatten_splitBy _ _, hcount]
  · intro p q hpq
    apply Finset.disjoint_left.mpr
    intro d hd hd'
    obtain ⟨a, ha, hap, hal⟩ := (hs p d).mp hd
    obtain ⟨b, hb, hbq, hbl⟩ := (hs q d).mp hd'
    have he := hunique ha hb (hal.trans hbl.symm)
    exact hpq (hap.symm.trans (he ▸ hbq))
  · intro d
    constructor
    · intro hd
      obtain ⟨b, hb, he⟩ := List.mem_map.mp hd
      exact ⟨b.headD 0, (hs _ _).mpr ⟨b, hb, rfl, he⟩⟩
    · rintro ⟨p, hp⟩
      obtain ⟨b, hb, _, he⟩ := (hs p d).mp hp
      exact List.mem_map.mpr ⟨b, hb, he⟩
  · rw [List.isChain_map]
    refine chain_on (List.isChain_getLast_head_splitBy (fun x y => x == y) l) ?_
    intro a ha b hb h p hp hq
    obtain ⟨ha', hb', hneq⟩ := h
    obtain ⟨u, hu, hup, hul⟩ := (hs p a.length).mp hp
    obtain ⟨v, hv, hvp, hvl⟩ := (hs p b.length).mp hq
    have hua := hunique hu ha hul
    have hvb := hunique hv hb hvl
    rw [hua] at hup
    rw [hvb] at hvp
    rw [value_in_run (hinner a ha) (List.getLast_mem ha'),
      value_in_run (hinner b hb) (List.head_mem hb'), hup, hvp] at hneq
    simp at hneq

end OMA.S_oeis_a386575

open OMA.S_oeis_a386575 in
theorem OMA.solution : type_of% @OMA.S_oeis_a386575.main := by
  intro n _
  exact ⟨runs_of_family, family_of_runs⟩
