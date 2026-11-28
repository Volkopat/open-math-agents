import FormalConjectures.Wikipedia.PetersenColoringConjecture

open SimpleGraph Finset PetersenColoringConjecture

private def lbl : Sym2 PetersenVertex → Fin 5 :=
  Sym2.lift ⟨fun x y => ((List.finRange 5).find? (fun i => decide (i ∉ x.1 ∧ i ∉ y.1))).getD 0,
    fun _ _ => by simp only [and_comm]⟩

private def edg (x : PetersenVertex) (i : Fin 5) : Sym2 PetersenVertex :=
  let s := (insert i x.1)ᶜ; s(x, if h : s.card = 2 then ⟨s, h⟩ else x)

private lemma hdec : ∀ x : PetersenVertex, ∀ e ∈ petersenGraph.incidenceFinset x, edg x (lbl e) = e := by
  decide +kernel

private lemma henc : ∀ x : PetersenVertex, ∀ i ∈ x.1ᶜ, lbl (edg x i) = i := by decide +kernel

private lemma hlbl : ∀ x : PetersenVertex, (petersenGraph.incidenceFinset x).image lbl = x.1ᶜ := by
  decide +kernel

private lemma himg : ∀ x : PetersenVertex, x.1ᶜ.image (edg x) = petersenGraph.incidenceFinset x := by
  decide +kernel

private lemma hsz : ∀ x y : PetersenVertex, ∀ e ∈ petersenGraph.incidenceFinset x,
    e ∈ petersenGraph.incidenceFinset y → (x.1ᶜ ∪ y.1ᶜ).card = 3 ∨ (x.1ᶜ ∪ y.1ᶜ).card = 5 := by
  decide +kernel

private lemma hagr : ∀ x y : PetersenVertex, ∀ i ∈ x.1ᶜ, i ∈ y.1ᶜ →
    ((x.1ᶜ ∪ y.1ᶜ).card = 3 ∨ (x.1ᶜ ∪ y.1ᶜ).card = 5) → edg x i = edg y i := by
  decide +kernel

theorem OMA.solution :
    type_of% @PetersenColoringConjecture.petersen_coloring_conjecture.variants.normal_five_edge_coloring := by
  intro V _ _ G _ hcub
  classical
  have hinc (u : V) (e : Sym2 V) : e ∈ G.incidenceFinset u ↔ e ∈ G.edgeFinset ∧ u ∈ e := by
    rw [incidenceFinset_eq_filter]; exact mem_filter
  have hboth (u v : V) : (G.edgeFinset.filter fun f => ∃ w, w ∈ s(u, v) ∧ w ∈ f) =
      G.incidenceFinset u ∪ G.incidenceFinset v := by
    ext f; simp only [mem_filter, Sym2.mem_iff, mem_union, hinc]; grind
  constructor
  · rintro ⟨φ, hφ⟩
    choose w hw using hφ
    have hloc (v : V) : (G.incidenceFinset v).image (lbl ∘ φ) = (w v).1ᶜ := by
      rw [← image_image, (hw v).1, hlbl]
    have hmap (v : V) (e : Sym2 V) (he : e ∈ G.incidenceFinset v) :=
      (hw v).1 ▸ mem_image_of_mem φ he
    refine ⟨lbl ∘ φ, ?_, ?_⟩
    · rintro e he f hf hne ⟨v, hve, hvf⟩ hef
      have he' := (hinc v e).2 ⟨he, hve⟩; have hf' := (hinc v f).2 ⟨hf, hvf⟩
      exact hne ((hw v).2 he' hf' ((hdec _ _ (hmap v e he')).symm.trans
        ((congrArg (edg (w v)) hef).trans (hdec _ _ (hmap v f hf')))))
    · intro e; induction e using Sym2.inductionOn with
      | _ u v =>
        intro he; rw [hboth, image_union, hloc, hloc]
        exact hsz _ _ _ (hmap u _ ((hinc ..).2 ⟨he, Sym2.mem_mk_left ..⟩))
          (hmap v _ ((hinc ..).2 ⟨he, Sym2.mem_mk_right ..⟩))
  · rintro ⟨c, hprop, hnorm⟩
    have hinj (v : V) : Set.InjOn c (G.incidenceFinset v : Set (Sym2 V)) :=
      fun e he f hf h => by_contra fun hne =>
        hprop e ((hinc v e).1 he).1 f ((hinc v f).1 hf).1 hne
          ⟨v, ((hinc v e).1 he).2, ((hinc v f).1 hf).2⟩ h
    let A (v : V) := (G.incidenceFinset v).image c
    have hcard (v : V) : (A v).card = 3 := by
      rw [card_image_of_injOn (hinj v), card_incidenceFinset_eq_degree, hcub]
    let w (v : V) : PetersenVertex := ⟨(A v)ᶜ, by simp [card_compl, hcard]⟩
    have hw (v : V) : (w v).1ᶜ = A v := compl_compl _
    let φ (e : Sym2 V) := edg (w e.out.1) (c e)
    have hφ (v : V) (e : Sym2 V) (he : e ∈ G.incidenceFinset v) : φ e = edg (w v) (c e) := by
      let u := e.out.1; have hu : u ∈ e := Sym2.out_fst_mem e
      obtain ⟨heG, hv⟩ := (hinc v e).1 he
      by_cases huv : u = v
      · simp [φ, u, huv]
      refine hagr _ _ _ (hw u ▸ mem_image_of_mem c ((hinc u e).2 ⟨heG, hu⟩))
        (hw v ▸ mem_image_of_mem c he) ?_
      rw [hw, hw]; have H := hnorm e heG
      rwa [(Sym2.mem_and_mem_iff huv).1 ⟨hu, hv⟩, hboth, image_union] at H
    refine ⟨φ, fun v => ⟨w v, ?_, fun e he f hf h => hinj v he hf ?_⟩⟩
    · calc _ = (G.incidenceFinset v).image (edg (w v) ∘ c) := image_congr (hφ v)
        _ = (A v).image (edg (w v)) := (image_image ..).symm
        _ = _ := hw v ▸ himg (w v)
    · rw [hφ v e he, hφ v f hf] at h
      exact (henc _ _ (hw v ▸ mem_image_of_mem c he)).symm.trans
        ((congrArg lbl h).trans (henc _ _ (hw v ▸ mem_image_of_mem c hf)))
