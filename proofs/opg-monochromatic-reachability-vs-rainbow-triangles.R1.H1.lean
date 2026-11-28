import OMAReductions.R_opg_monochromatic_reachability_vs_rainbow_triangles_R1

/-!
The two-colour finite tournament lemma is the tournament case of Sands, Sauer,
and Woodrow, J. Combin. Theory Ser. B 33 (1982), 271–275.  The three-colour
conclusion is Theorem 1.1 in Georgakopoulos and Sprüssel, arXiv:0904.1967,
originally proved by Galeana-Sánchez and Rojas-Monroy in 2005.

Assign each vertex one colour missing from its incident arcs. Between different
classes the arc colour is forced. A path along cross-class arcs can be replaced
by a monochromatic path: whenever a new arc changes colour, its endpoint lies in
the third class and receives a direct arc from every vertex on the previous path.
Take a source class for cross-class reachability. The residual vertices with no
incoming cross-class arc share one missing colour and are handled by the
two-colour lemma.
-/

-- Credit: @gdyan2022

namespace TournamentReach
open Relation
open OMA.S_opg_monochromatic_reachability_vs_rainbow_triangles

/-- A finite nonempty subset of a preorder contains a minimal equivalence class. -/
theorem source_in {V : Type} [Fintype V] (S : Set V) (hn : S.Nonempty)
    (R : V → V → Prop) (hr : ∀ u, R u u)
    (ht : ∀ {u v w}, R u v → R v w → R u w) :
    ∃ x ∈ S, ∀ y ∈ S, R y x → R x y := by
  classical
  let cone (x : V) := Finset.univ.filter (R x)
  obtain ⟨x,hx,hmax⟩ := (Finset.univ.filter (fun x => x ∈ S)).exists_max_image (fun x => (cone x).card)
    (by obtain ⟨u,hu⟩ := hn; exact ⟨u, by simpa using hu⟩)
  refine ⟨x, (Finset.mem_filter.mp hx).2, ?_⟩
  intro y hy hyx
  by_contra hxy
  have sub : cone x ⊆ cone y := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht hyx (Finset.mem_filter.mp hz).2⟩
  have strict : cone x ⊂ cone y := (Finset.ssubset_iff_of_subset sub).mpr
    ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr y⟩,
       fun h => hxy (Finset.mem_filter.mp h).2⟩
  exact (Finset.card_lt_card strict).not_ge (hmax y (by simpa using hy))

/-- Finite tournament case of the two-colour theorem of Sands, Sauer and Woodrow.
The two preorders are the reflexive transitive closures of the two colour classes. -/
theorem two_relations {V : Type} [Fintype V] (S : Set V) (hn : S.Nonempty)
    (R B : V → V → Prop) (rr : ∀ x, R x x) (br : ∀ x, B x x)
    (rt : ∀ {a b c}, R a b → R b c → R a c)
    (bt : ∀ {a b c}, B a b → B b c → B a c)
    (total : ∀ x ∈ S, ∀ y ∈ S, R x y ∨ B x y ∨ R y x ∨ B y x) :
    ∃ x ∈ S, ∀ y ∈ S, R x y ∨ B x y := by
  let good : Set V := {x | x ∈ S ∧ ∀ y ∈ S, R y x → R x y ∨ B x y}
  have existsGood : good.Nonempty := by
    obtain ⟨x,hx,h⟩ := source_in S hn R rr rt
    exact ⟨x,hx,fun y hy hyx => Or.inl (h y hy hyx)⟩
  obtain ⟨x,hx,hmax⟩ := source_in good existsGood B br bt
  refine ⟨x,hx.1,?_⟩
  by_contra h
  let missed : Set V := {y | y ∈ S ∧ ¬ (R x y ∨ B x y)}
  have missNonempty : missed.Nonempty := by
    push Not at h
    obtain ⟨y,hy,hr,hb⟩ := h
    exact ⟨y,hy,not_or.mpr ⟨hr,hb⟩⟩
  obtain ⟨y,hy,hred⟩ := source_in missed missNonempty R rr rt
  have byx : B y x := by
    rcases total x hx.1 y hy.1 with h | h | h | h
    · exact False.elim (hy.2 (Or.inl h))
    · exact False.elim (hy.2 (Or.inr h))
    · exact False.elim (hy.2 (hx.2 y hy.1 h))
    · exact h
  have yg : y ∈ good := by
    refine ⟨hy.1,?_⟩
    intro z hz hzy
    by_contra bad
    have zm : z ∈ missed := by
      refine ⟨hz,?_⟩
      rintro (hxz | hxz)
      · exact hy.2 (Or.inl (rt hxz hzy))
      · exact bad (Or.inr (bt byx hxz))
    exact bad (Or.inl (hred z zm hzy))
  exact hy.2 (Or.inr (hmax y yg byx))


/-- Cross-class arcs of a fixed colour. -/
private def cross {V : Type} (G : Digraph V) (m : V → Fin 3) (x y : V) :=
  G.Adj x y ∧ m x ≠ m y

private def pure {V : Type} (G : Digraph V) (col : V → V → Fin 3) (m : V → Fin 3)
    (k : Fin 3) (x y : V) := cross G m x y ∧ col x y = k

private theorem third_unique {a b c d : Fin 3} (ab : a ≠ b) (ca : c ≠ a) (cb : c ≠ b)
    (da : d ≠ a) (db : d ≠ b) : c = d := by omega

section
variable {V : Type} {G : Digraph V} {col : V → V → Fin 3} {m : V → Fin 3}
variable (tour : IsTournament G)
variable (missing : ∀ {x y}, G.Adj x y → col x y ≠ m x ∧ col x y ≠ m y)
variable (triangle : ∀ {u v w}, G.Adj u v → G.Adj v w → G.Adj w u →
    col u v = col v w ∨ col v w = col w u ∨ col u v = col w u)

include tour missing triangle
private theorem shortcut {u v w : V} (huv : cross G m u v) (hvw : cross G m v w)
    (huw : m u ≠ m w) : cross G m u w := by
  refine ⟨?_,huw⟩
  by_contra bad
  have wu : G.Adj w u := (tour.2 w u (fun h => huw (congrArg m h.symm))).mpr bad
  obtain ⟨a,b⟩ := missing huv.1
  obtain ⟨c,d⟩ := missing hvw.1
  obtain ⟨e,f⟩ := missing wu
  have huv' := huv.2
  have hvw' := hvw.2
  rcases triangle huv.1 hvw.1 wu with eq | eq | eq <;> omega

/-- A vertex in the third class which receives the final arc also receives
a direct arc from the first vertex of the alternating path. -/
private theorem extend_to_third {k : Fin 3} {u v w : V}
    (P : TransGen (pure G col m k) u v) (hw : m w = k)
    (vw : cross G m v w) : cross G m u w := by
  induction P using TransGen.head_induction_on with
  | single e =>
    apply shortcut tour missing triangle e.1 vw
    rw [hw, ← e.2]
    exact (missing e.1.1).1.symm
  | head e _ ih =>
    apply shortcut tour missing triangle e.1 ih
    rw [hw, ← e.2]
    exact (missing e.1.1).1.symm

/-- Without a rainbow triangle, every path in the multipartite orientation
can be replaced by a monochromatic path with the same endpoints. -/
private theorem cross_pure {u v : V} (P : TransGen (cross G m) u v) :
    ∃ k : Fin 3, TransGen (pure G col m k) u v := by
  induction P with
  | single e => exact ⟨_, .single ⟨e,rfl⟩⟩
  | @tail y z _ e ih =>
    obtain ⟨k,p⟩ := ih
    by_cases eq : col y z = k
    · exact ⟨k,p.tail ⟨e,eq⟩⟩
    · have last : k ≠ m y := by
        cases p with
        | single f => simpa [← f.2] using (missing f.1.1).2
        | tail _ f => simpa [← f.2] using (missing f.1.1).2
      obtain ⟨a,b⟩ := missing e.1
      have yz := e.2
      have zk : m z = k := third_unique a b.symm yz.symm (Ne.symm eq) last
      have jump := extend_to_third tour missing triangle p zk e
      exact ⟨_,.single ⟨jump,rfl⟩⟩
end


private theorem two_other (a : Fin 3) : ∃ r b : Fin 3, ∀ k : Fin 3, k ≠ a → k = r ∨ k = b := by
  fin_cases a
  · exact ⟨1,2,by decide⟩
  · exact ⟨0,2,by decide⟩
  · exact ⟨0,1,by decide⟩

theorem missing_colour {V : Type} [Fintype V] [Nonempty V]
    (G : Digraph V) (col : V → V → Fin 3) (m : V → Fin 3)
    (tour : IsTournament G)
    (missing : ∀ {x y}, G.Adj x y → col x y ≠ m x ∧ col x y ≠ m y)
    (triangle : ∀ {u v w}, G.Adj u v → G.Adj v w → G.Adj w u →
      col u v = col v w ∨ col v w = col w u ∨ col u v = col w u) :
    ∃ v : V, ∀ w : V, w ≠ v → ∃ k : Fin 3, TransGen (fun x y => G.Adj x y ∧ col x y = k) v w := by
  classical
  let E (k : Fin 3) (u v : V) := G.Adj u v ∧ col u v = k
  let R := ReflTransGen (cross G m)
  obtain ⟨x,_,hmax⟩ := source_in (Set.univ : Set V) Set.univ_nonempty R
    (fun _ => .refl) (fun h h' => h.trans h')
  have diff (v : V) (hd : m x ≠ m v) : R x v := by
    by_cases h : G.Adj x v
    · exact .single ⟨h,hd⟩
    · have rev := (tour.2 v x (fun h => hd (congrArg m h.symm))).mpr h
      exact hmax v (Set.mem_univ v) (.single ⟨rev,hd.symm⟩)
  let S : Set V := {v | m v = m x ∧ ∀ u, ¬ cross G m u v}
  by_cases hasSources : S.Nonempty
  · obtain ⟨r,b,colors⟩ := two_other (m x)
    have total (u : V) (hu : u ∈ S) (v : V) (hv : v ∈ S) :
        ReflTransGen (E r) u v ∨ ReflTransGen (E b) u v ∨
        ReflTransGen (E r) v u ∨ ReflTransGen (E b) v u := by
      by_cases h : u = v
      · subst v; exact Or.inl .refl
      have pair (i j : V) (hi : i ∈ S) (hij : G.Adj i j) :
          ReflTransGen (E r) i j ∨ ReflTransGen (E b) i j := by
        obtain h | h := colors (col i j) (hi.1 ▸ (missing hij).1)
        · exact .inl (.single ⟨hij,h⟩)
        · exact .inr (.single ⟨hij,h⟩)
      by_cases uv : G.Adj u v
      · rcases pair u v hu uv with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (pair v u hv ((tour.2 v u (Ne.symm h)).mpr uv)))
    obtain ⟨v,hv,champ⟩ := two_relations S hasSources (ReflTransGen (E r)) (ReflTransGen (E b))
      (fun _ => .refl) (fun _ => .refl) (fun h h' => h.trans h') (fun h h' => h.trans h') total
    refine ⟨v,?_⟩
    intro w hw
    by_cases sw : w ∈ S
    · obtain h | h := champ w sw
      · exact ⟨r,(reflTransGen_iff_eq_or_transGen.mp h).resolve_left hw⟩
      · exact ⟨b,(reflTransGen_iff_eq_or_transGen.mp h).resolve_left hw⟩
    have direct (z : V) (hz : m v ≠ m z) : G.Adj v z := by
      apply (tour.2 v z (fun h => hz (congrArg m h))).mpr
      exact fun h => hv.2 z ⟨h,hz.symm⟩
    by_cases same : m v = m w
    · have wmx : m w = m x := same.symm.trans hv.1
      obtain ⟨z,zw⟩ : ∃ z : V, cross G m z w := by
        by_contra! none
        exact sw ⟨wmx,none⟩
      have vz : m v ≠ m z := fun e => zw.2 (e.symm.trans same)
      have edge := direct z vz
      obtain ⟨a,b'⟩ := missing edge
      obtain ⟨c,d⟩ := missing zw.1
      have eq : col z w = col v z := third_unique vz (same.symm ▸ d) c a b'
      exact ⟨col v z, (TransGen.single ⟨edge,rfl⟩).tail ⟨zw.1,eq⟩⟩
    · exact ⟨_,.single ⟨direct w same,rfl⟩⟩
  · refine ⟨x,?_⟩
    intro w hw
    have path : R x w := by
      by_cases same : m x = m w
      · have incoming : ∃ z, cross G m z w := by
          by_contra! none
          exact hasSources ⟨w,same.symm,none⟩
        obtain ⟨z,zw⟩ := incoming
        exact (diff z (fun h => zw.2 (h.symm.trans same))).tail zw
      · exact diff w same
    obtain ⟨k,p⟩ := cross_pure tour missing triangle ((reflTransGen_iff_eq_or_transGen.mp path).resolve_left hw)
    exact ⟨k,TransGen.mono (r := pure G col m k) (p := E k) (fun _ _ h => ⟨h.1.1,h.2⟩) x w p⟩

end TournamentReach

theorem OMA.solution : OMA.R_opg_monochromatic_reachability_vs_rainbow_triangles_R1.H1 := by
  classical
  intro V _ _ G col tour localTwo
  by_cases tri : ∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
      col a b ≠ col b c ∧ col b c ≠ col c a ∧ col a b ≠ col c a
  · exact Or.inl tri
  right
  have hmiss (v : V) : ∃ k : Fin 3, ∀ w, ¬ ((G.Adj v w ∧ col v w = k) ∨
      (G.Adj w v ∧ col w v = k)) := by simpa only [not_forall, not_exists] using localTwo v
  choose m hm using hmiss
  apply TournamentReach.missing_colour G col m tour
  · intro x y h
    exact ⟨fun e => hm x y (Or.inl ⟨h,e⟩),fun e => hm y x (Or.inr ⟨h,e⟩)⟩
  · intro u v w uv vw wu
    by_contra! bad
    exact tri ⟨u,v,w,uv,vw,wu,bad⟩
