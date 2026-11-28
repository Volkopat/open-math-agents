import OMAReductions.R_Erdos595_erdos_595_R2
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Order.Filter.Ultrafilter.Defs

/-!
Realize the finite graph constraints simultaneously by taking germs along
an ultrafilter extending the filter of cofinal sets of finite subsets.
Every prohibited clique would already occur in one finite witness.
-/

open Filter SimpleGraph

private def localAdj {I : Type} (F : Filter I) (G : I → SimpleGraph ℕ)
    (x y : Germ F ℕ) : Prop :=
  Quotient.liftOn₂ x y (fun a b => ∀ᶠ i in F, (G i).Adj (a i) (b i)) <| by
    intro a b a' b' ha hb
    change a =ᶠ[F] a' at ha
    change b =ᶠ[F] b' at hb
    apply propext
    constructor
    · intro h
      filter_upwards [ha, hb, h] with i hai hbi hi
      rwa [← hai, ← hbi]
    · intro h
      filter_upwards [ha, hb, h] with i hai hbi hi
      rwa [hai, hbi]

private def germGraph {I : Type} (F : Filter I) [NeBot F] (G : I → SimpleGraph ℕ) :
    SimpleGraph (Germ F ℕ) where
  Adj := localAdj F G
  symm := ⟨by
    intro x y
    refine Germ.inductionOn₂ x y ?_
    intro a b h
    change (∀ᶠ i in F, (G i).Adj (a i) (b i)) at h
    exact h.mono fun _ hi => hi.symm⟩
  loopless := ⟨by
    intro x
    refine Germ.inductionOn x ?_
    intro a h
    change (∀ᶠ i in F, (G i).Adj (a i) (a i)) at h
    obtain ⟨i, hi⟩ := h.exists
    exact hi.ne rfl⟩

private theorem germGraph_free {I : Type} (F : Filter I) [NeBot F]
    (G : I → SimpleGraph ℕ) (hG : ∀ i, (G i).CliqueFree 4) :
    (germGraph F G).CliqueFree 4 := by
  classical
  by_contra hn
  obtain ⟨C⟩ := (not_cliqueFree_iff_top_isContained (G := germGraph F G) 4).mp hn
  have reps (j : Fin 4) : ∃ f : I → ℕ, (f : Germ F ℕ) = C j :=
    Germ.inductionOn (C j) fun f => ⟨f, rfl⟩
  choose f hf using reps
  have adj (i j : Fin 4) (hij : i ≠ j) :
      ∀ᶠ w in F, (G w).Adj (f i w) (f j w) := by
    have h : (germGraph F G).Adj (C i) (C j) := C.toHom.map_rel' hij
    rw [← hf i, ← hf j] at h
    exact h
  have hlocal : ∀ᶠ w in F, ∀ i j : Fin 4, i ≠ j → (G w).Adj (f i w) (f j w) := by
    rw [eventually_all]
    intro i
    rw [eventually_all]
    intro j
    by_cases hij : i = j
    · simp [hij]
    · exact (adj i j hij).mono fun _ h _ => h
  obtain ⟨w, hw⟩ := hlocal.exists
  have C' : Copy (completeGraph (Fin 4)) (G w) :=
    ⟨⟨fun j => f j w, fun {i j} h => hw i j h⟩, fun i j h => by
      by_contra hn
      exact (hw i j hn).ne h⟩
  exact ((not_cliqueFree_iff_top_isContained (G := G w) 4).mpr ⟨C'⟩) (hG w)

private theorem sym2_germ_eq {I : Type} (F : Ultrafilter I) {a b c d : I → ℕ}
    (h : ∀ᶠ i in (F : Filter I), s(a i, b i) = s(c i, d i)) :
    s((a : Germ (F : Filter I) ℕ), (b : Germ (F : Filter I) ℕ)) =
      s((c : Germ (F : Filter I) ℕ), (d : Germ (F : Filter I) ℕ)) := by
  apply Sym2.eq_iff.mpr
  rcases F.eventually_or.mp (h.mono fun _ hi => Sym2.eq_iff.mp hi) with h' | h'
  · exact Or.inl ⟨Germ.coe_eq.mpr (h'.mono fun _ hi => hi.1), Germ.coe_eq.mpr (h'.mono fun _ hi => hi.2)⟩
  · exact Or.inr ⟨Germ.coe_eq.mpr (h'.mono fun _ hi => hi.1), Germ.coe_eq.mpr (h'.mono fun _ hi => hi.2)⟩

private theorem witnessOnNat {X : Type} {T : X → X → X → Prop} (S : Finset X)
    (hS : ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 4 ∧
      ∃ e : S → G.edgeSet, ∀ a b c : S, T a b c →
        ∃ x y z : Fin n, (e a : Sym2 (Fin n)) = s(x, y) ∧
          (e b : Sym2 (Fin n)) = s(y, z) ∧ (e c : Sym2 (Fin n)) = s(z, x)) :
    ∃ (G : SimpleGraph ℕ), G.CliqueFree 4 ∧
      ∃ e : S → G.edgeSet, ∀ a b c : S, T a b c →
        ∃ x y z : ℕ, (e a : Sym2 ℕ) = s(x, y) ∧
          (e b : Sym2 ℕ) = s(y, z) ∧ (e c : Sym2 ℕ) = s(z, x) := by
  classical
  obtain ⟨n, G, hG, e, he⟩ := hS
  let emb : Fin n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let K := G.map emb
  have hK : K.CliqueFree 4 := by
    cases n with
    | zero =>
      have hk : K = ⊥ := by
        ext a b
        simp [K, SimpleGraph.map_adj]
      rw [hk]
      exact cliqueFree_bot (by decide : (2 : ℕ) ≤ 4)
    | succ n =>
      exact (cliqueFree_map_iff (G := G) (f := emb)).mpr hG
  let e' (a : S) : K.edgeSet := ⟨emb.sym2Map (e a).val, by
    change _ ∈ (G.map emb).edgeSet
    rw [edgeSet_map]
    exact Set.mem_image_of_mem _ (e a).prop⟩
  refine ⟨K, hK, e', ?_⟩
  intro a b c habc
  obtain ⟨x, y, z, ha, hb, hc⟩ := he a b c habc
  refine ⟨x.val, y.val, z.val, ?_, ?_, ?_⟩
  · change emb.sym2Map (e a).val = _
    rw [ha]
    rfl
  · change emb.sym2Map (e b).val = _
    rw [hb]
    rfl
  · change emb.sym2Map (e c).val = _
    rw [hc]
    rfl

theorem OMA.solution : OMA.R_Erdos595_erdos_595_R2.H2 := by
  intro X T hfinite
  classical
  let U := Ultrafilter.of (atTop : Filter (Finset X))
  let V := Germ (U : Filter (Finset X)) ℕ
  have h_infinite : Infinite V := by
    apply Infinite.of_injective (fun a : ℕ => ((fun _ : Finset X => a) : V))
    intro a b h
    have hab : ∀ᶠ _ in (U : Filter (Finset X)), a = b := Germ.coe_eq.mp h
    exact hab.exists.choose_spec
  have hloc (S : Finset X) := witnessOnNat (T := T) S (hfinite S)
  choose G hfree e htriangle using hloc
  have ends (S : Finset X) (a : X) :
      ∃ p q : ℕ, ∀ ha : a ∈ S, (e S ⟨a, ha⟩ : Sym2 ℕ) = s(p, q) := by
    by_cases ha : a ∈ S
    · obtain ⟨⟨p, q⟩, hpq⟩ := Sym2.mk_surjective (e S ⟨a, ha⟩).val
      exact ⟨p, q, fun _ => hpq.symm⟩
    · exact ⟨0, 0, fun hb => (ha hb).elim⟩
  choose P Q hEnds using ends
  have member (a : X) : ∀ᶠ S in (U : Filter (Finset X)), a ∈ S := by
    apply Ultrafilter.of_le (atTop : Filter (Finset X))
    exact eventually_atTop.mpr ⟨{a}, fun _ h => h (Finset.mem_singleton_self _)⟩
  let A (a : X) : Finset X → ℕ := fun S => P S a
  let B (a : X) : Finset X → ℕ := fun S => Q S a
  let H := germGraph (U : Filter (Finset X)) G
  let E (a : X) : H.edgeSet := ⟨s((A a : V), (B a : V)), by
    change ∀ᶠ S in (U : Filter (Finset X)), (G S).Adj (P S a) (Q S a)
    filter_upwards [member a] with S ha
    change s(P S a, Q S a) ∈ (G S).edgeSet
    rw [← hEnds S a ha]
    exact (e S ⟨a, ha⟩).prop⟩
  refine ⟨V, h_infinite, H, germGraph_free _ G hfree, E, ?_⟩
  intro a b c habc
  have pick (S : Finset X) :
      ∃ x y z : ℕ, a ∈ S ∧ b ∈ S ∧ c ∈ S →
        s(P S a, Q S a) = s(x, y) ∧
          s(P S b, Q S b) = s(y, z) ∧ s(P S c, Q S c) = s(z, x) := by
    by_cases h : a ∈ S ∧ b ∈ S ∧ c ∈ S
    · obtain ⟨x, y, z, ha, hb, hc⟩ :=
        htriangle S ⟨a, h.1⟩ ⟨b, h.2.1⟩ ⟨c, h.2.2⟩ habc
      refine ⟨x, y, z, fun _ => ⟨?_, ?_, ?_⟩⟩
      · exact (hEnds S a h.1).symm.trans ha
      · exact (hEnds S b h.2.1).symm.trans hb
      · exact (hEnds S c h.2.2).symm.trans hc
    · exact ⟨0, 0, 0, fun h' => (h h').elim⟩
  choose x y z hp using pick
  refine ⟨(x : V), (y : V), (z : V), ?_, ?_, ?_⟩
  · exact sym2_germ_eq U (by
      filter_upwards [member a, member b, member c] with S ha hb hc
      exact (hp S ⟨ha, hb, hc⟩).1)
  · exact sym2_germ_eq U (by
      filter_upwards [member a, member b, member c] with S ha hb hc
      exact (hp S ⟨ha, hb, hc⟩).2.1)
  · exact sym2_germ_eq U (by
      filter_upwards [member a, member b, member c] with S ha hb hc
      exact (hp S ⟨ha, hb, hc⟩).2.2)

