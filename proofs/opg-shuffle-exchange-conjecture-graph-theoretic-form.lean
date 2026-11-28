import OMAStatements.S_opg_shuffle_exchange_conjecture_graph_theoretic_form

/-!
# A three-letter shuffle-exchange mask that cannot be routed through five stages

Przemek Chojecki constructs a non-routable mask in Proposition 18 of
https://arxiv.org/abs/2607.15296. We specialize it to three letters.
The middle vertex of each path supplies two colors, one from each digit.
Two perfect matchings are forced to share two of their three entries.
Their remaining entries then agree, contradicting edge-disjointness.
-/

namespace ShuffleProof

open OMA.S_opg_shuffle_exchange_conjecture_graph_theoretic_form

def hi (w : Fin 9) : Fin 3 := ⟨w.val / 3, by omega⟩
def lo (w : Fin 9) : Fin 3 := ⟨w.val % 3, by omega⟩

private lemma shift_digit : ∀ i j : Fin 9, SEAdj 3 9 i j → lo i = hi j := by
  unfold SEAdj lo hi
  decide

private lemma digits_det : ∀ i j : Fin 9, hi i = hi j → lo i = lo j → i = j := by
  unfold lo hi
  decide

/-- The middle vertex colors a routed demand. Traversing each of the four
    layers gives one injectivity constraint; the two middle maps are onto by counting. -/
lemma route_colors (m : Fin 27 → Fin 9 × Fin 9) (hm : IsMask 3 9 m)
    (H : IsRearrangeable 3 3 5) :
    ∃ col : Fin 27 → Fin 9,
      Function.Injective (fun e => ((m e).1, hi (col e))) ∧
      Function.Bijective (fun e => (lo (m e).1, col e)) ∧
      Function.Bijective (fun e => (hi (m e).2, col e)) ∧
      Function.Injective (fun e => ((m e).2, lo (col e))) := by
  obtain ⟨P, ends, adj, disj⟩ := H m hm
  have src (e : Fin 27) : P e 0 = (m e).1 := (ends e (by decide)).1
  have dst (e : Fin 27) : P e 4 = (m e).2 := (ends e (by decide)).2
  have layer₁ (e : Fin 27) : lo (m e).1 = hi (P e 1) := by
    rw [← src]
    exact shift_digit _ _ (adj e 0 (by decide))
  have layer₂ (e : Fin 27) : lo (P e 1) = hi (P e 2) :=
    shift_digit _ _ (adj e 1 (by decide))
  have layer₃ (e : Fin 27) : lo (P e 2) = hi (P e 3) :=
    shift_digit _ _ (adj e 2 (by decide))
  have layer₄ (e : Fin 27) : lo (P e 3) = hi (m e).2 := by
    rw [← dst]
    exact shift_digit _ _ (adj e 3 (by decide))
  have first {e f : Fin 27} (a : lo (m e).1 = lo (m f).1)
      (b : hi (P e 2) = hi (P f 2)) : P e 1 = P f 1 := by
    apply digits_det
    · rwa [← layer₁, ← layer₁]
    · rwa [layer₂, layer₂]
  have last {e f : Fin 27} (a : lo (P e 2) = lo (P f 2))
      (b : hi (m e).2 = hi (m f).2) : P e 3 = P f 3 := by
    apply digits_det
    · rwa [← layer₃, ← layer₃]
    · rwa [layer₄, layer₄]
  have same {e f : Fin 27} (s : ℕ) (hs : s+1 < 5)
      (a : P e ⟨s, by omega⟩ = P f ⟨s, by omega⟩)
      (b : P e ⟨s+1, hs⟩ = P f ⟨s+1, hs⟩) : e = f := by
    by_contra h
    exact disj e f h s hs ⟨a, b⟩
  refine ⟨fun e => P e 2, ?_, (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, by decide⟩,
    (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, by decide⟩, ?_⟩
  · intro e f h
    have a := (Prod.mk.inj h).1
    apply same 0 (by decide) _ (first (congrArg lo a) (congrArg Prod.snd h))
    exact (src e).trans (a.trans (src f).symm)
  · intro e f h
    have b : P e 2 = P f 2 := congrArg Prod.snd h
    exact same 1 (by decide) (first (congrArg Prod.fst h) (congrArg hi b)) b
  · intro e f h
    have b : P e 2 = P f 2 := congrArg Prod.snd h
    exact same 2 (by decide) b (last (congrArg lo b) (congrArg Prod.fst h))
  · intro e f h
    have a := (Prod.mk.inj h).1
    apply same 3 (by decide) (last (congrArg Prod.snd h) (congrArg hi a)) _
    exact (dst e).trans (a.trans (dst f).symm)

def source (e : Fin 27) : Fin 9 := ⟨e.val / 3, by omega⟩

def edge (s : Fin 9) (i : Fin 3) : Fin 27 := ⟨3 * s.val + i.val, by omega⟩

/-- Start with three parallel copies of each indicated connection, then exchange
the destinations of requests 8 and 20. This is Chojecki's mask for three letters. -/
def target (e : Fin 27) : Fin 9 :=
  if e = 8 then 5 else if e = 20 then 6 else
    ![0, 3, 6, 1, 4, 7, 5, 8, 2] (source e)

def mask (e : Fin 27) : Fin 9 × Fin 9 := (source e, target e)

lemma regular : IsMask 3 9 mask := by
  unfold IsMask
  decide

lemma source_edge : ∀ s i, source (edge s i) = s := by decide
lemma edge_inj : ∀ s, Function.Injective (edge s) := by
  intro s i j h
  have he := congrArg Fin.val h
  change 3 * s.val + i.val = 3 * s.val + j.val at he
  exact Fin.ext (by omega)

lemma from_source : ∀ e, ∃ i, edge (source e) i = e := by decide

lemma full_seven : ∀ i, target (edge 7 i) = 8 := by decide
lemma full_eight : ∀ i, target (edge 8 i) = 2 := by decide

lemma into_zero : ∀ e, hi (target e) = 0 → source e = 8 ∨ lo (source e) = 0 := by decide
lemma from_one : ∀ e, lo (source e) = 1 → source e = 7 ∨ hi (target e) = 1 := by decide

lemma third_digit : ∀ a b x y : Fin 3,
    a ≠ b → x ≠ a → x ≠ b → y ≠ a → y ≠ b → x = y := by decide

lemma eq_of_digits : ∀ x y : Fin 9, hi x = hi y → lo x = lo y → x = y := by decide

lemma inj_on_range {A : Fin 3 → Fin 9} {f : Fin 9 → Fin 3}
    (h : Function.Injective (fun i => f (A i))) : Set.InjOn f (Set.range A) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ he
  exact congrArg A (h he)

/-- Two perfect matchings on a three-by-three grid that share two entries coincide. -/
lemma matching_subset (A B : Fin 3 → Fin 9)
    (hAh : Function.Injective (fun i => hi (A i)))
    (hAl : Function.Injective (fun i => lo (A i)))
    (hBh : Function.Injective (fun i => hi (B i)))
    (hBl : Function.Injective (fun i => lo (B i)))
    {x y : Fin 9} (hxy : x ≠ y)
    (hxA : x ∈ Set.range A) (hyA : y ∈ Set.range A)
    (hxB : x ∈ Set.range B) (hyB : y ∈ Set.range B) :
    Set.range A ⊆ Set.range B := by
  intro z hz
  by_cases hzx : z = x
  · simpa [hzx] using hxB
  by_cases hzy : z = y
  · simpa [hzy] using hyB
  obtain ⟨j, hj⟩ := (Finite.injective_iff_surjective.mp hBh) (hi z)
  have hB : B j ∈ Set.range B := ⟨j, rfl⟩
  have hn {w : Fin 9} (hw : w ∈ Set.range A) (hne : z ≠ w) : B j ≠ w := by
    intro he
    apply hne
    exact inj_on_range hAh hz hw (hj.symm.trans (congrArg hi he))
  refine ⟨j, eq_of_digits _ _ hj (third_digit (lo x) (lo y) _ _ ?_ ?_ ?_ ?_ ?_)⟩
  · exact fun h => hxy (inj_on_range hAl hxA hyA h)
  · exact fun h => hn hxA hzx (inj_on_range hBl hB hxB h)
  · exact fun h => hn hyA hzy (inj_on_range hBl hB hyB h)
  · exact fun h => hzx (inj_on_range hAl hz hxA h)
  · exact fun h => hzy (inj_on_range hAl hz hyA h)

lemma no_colours (col : Fin 27 → Fin 9)
    (hfirst : Function.Injective (fun e => ((mask e).1, hi (col e))))
    (hin : Function.Bijective (fun e => (lo (mask e).1, col e)))
    (hout : Function.Bijective (fun e => (hi (mask e).2, col e)))
    (hlast : Function.Injective (fun e => ((mask e).2, lo (col e)))) : False := by
  let X (s : Fin 9) (i : Fin 3) := col (edge s i)
  have hh (s : Fin 9) : Function.Injective (fun i => hi (X s i)) := by
    intro i j he
    apply edge_inj s
    apply hfirst
    exact Prod.ext (by simp [mask, source_edge]) he
  have hl (s t : Fin 9) (hs : ∀ i, target (edge s i) = t) :
      Function.Injective (fun i => lo (X s i)) := by
    intro i j he
    apply edge_inj s
    apply hlast
    exact Prod.ext (by simp [mask, hs]) he
  have inX {s : Fin 9} {e : Fin 27} (hs : source e = s) : col e ∈ Set.range (X s) := by
    obtain ⟨i, hi⟩ := from_source e
    exact ⟨i, by simpa [X, ← hs] using congrArg col hi⟩
  -- Compare the complete sets of colors entering and leaving block zero.
  have inEight (e : Fin 27) (hs : source e = 6) (ht : hi (target e) ≠ 0) :
      col e ∈ Set.range (X 8) := by
    obtain ⟨j, hj⟩ := hout.2 (0, col e)
    have hd : hi (target j) = 0 := congrArg Prod.fst hj
    have hc : col j = col e := congrArg Prod.snd hj
    rcases into_zero j hd with h | h
    · exact hc ▸ inX h
    · have hzero : lo (source e) = 0 := by rw [hs]; decide
      have he : j = e := hin.1 (Prod.ext (h.trans hzero.symm) hc)
      exact (ht (he ▸ hd)).elim
  -- In block one, every demand arriving at vertex 5 has a counterpart from vertex 7.
  have inSeven (e : Fin 27) (ht : target e = 5) (hs : lo (source e) ≠ 1) :
      col e ∈ Set.range (X 7) := by
    obtain ⟨j, hj⟩ := hin.2 (1, col e)
    have hd : lo (source j) = 1 := congrArg Prod.fst hj
    have hc : col j = col e := congrArg Prod.snd hj
    rcases from_one j hd with h | h
    · exact hc ▸ inX h
    · have hone : hi (target e) = 1 := by rw [ht]; decide
      have he : j = e := hout.1 (Prod.ext (h.trans hone.symm) hc)
      exact (hs (he ▸ hd)).elim
  have hc : col 18 ≠ col 19 := by
    intro h
    have hs : source 18 = source 19 := by decide
    have he : (18 : Fin 27) = 19 := hfirst (Prod.ext hs (congrArg hi h))
    exact (by decide : (18 : Fin 27) ≠ 19) he
  have incl := matching_subset (X 8) (X 7) (hh 8) (hl 8 2 full_eight)
    (hh 7) (hl 7 8 full_seven) hc
    (inEight 18 (by decide) (by decide)) (inEight 19 (by decide) (by decide))
    (inSeven 18 (by decide) (by decide)) (inSeven 19 (by decide) (by decide))
  obtain ⟨i, hi'⟩ := incl (inEight 20 (by decide) (by decide))
  have hdst : hi (target (edge 7 i)) = hi (target 20) := by rw [full_seven]; decide
  have he : edge 7 i = 20 := hout.1 (Prod.ext hdst hi')
  have hs := congrArg source he
  rw [source_edge] at hs
  exact (by decide : (7 : Fin 9) ≠ source 20) hs

end ShuffleProof

open ShuffleProof

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_shuffle_exchange_conjecture_graph_theoretic_form.main) := by
  intro hall
  have hroute := (hall 3 3 (by decide) (by decide)).1
  obtain ⟨col, hfirst, hin, hout, hlast⟩ := route_colors mask regular hroute
  exact no_colours col hfirst hin hout hlast
