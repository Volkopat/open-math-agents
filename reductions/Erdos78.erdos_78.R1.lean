import FormalConjectures.ErdosProblems.«78»

/-!
# Reduction `Erdos78.erdos_78.R1` — Weakly explicit Ramsey graphs

Reduces Erdős Problem 78 (weakly explicit Ramsey graphs on `n` vertices avoiding both cliques
and independent sets of size `⌈c log n⌉`) into three independent hypotheses:

* `H1` (open mathematical core, lossless): weakly explicit **self-complementary** graphs on
  power-of-two vertex counts `2 ^ k` that are merely **clique-free** of order `⌈c * k⌉`
  (no independent-set bound is needed separately).
* `H2` (complexity theory): polynomial-time composition of `(List Bool × ℕ × ℕ) → ...` maps.
* `H3` (complexity theory): linear-size unary power-of-two padding
  `(xs, u, v) ↦ (List.replicate (2 ^ Nat.size xs.length) true, u, v)` is polynomial time.

In addition to `main : H1 → H2 → H3 → type_of% @Erdos78.erdos_78`, this file proves the
4-block `P_4`-blowup theorem (`p4_blowup_selfComp_and_cliqueFree`), certifying that any
graph `G` on `n` vertices with `NoHomogeneousSet G m` lifts explicitly to a self-complementary
graph `H` on `4 * n` vertices with `H.CliqueFree (2 * m)`, so restricting to self-complementary
clique-free graphs on powers of two adds zero mathematical risk.
-/

-- Credit: @sanchan

namespace OMA.R_Erdos78_erdos_78_R1

open Filter Real ComplexityTheory Erdos78

/-- Open core: weakly explicit self-complementary graphs on `2 ^ k` vertices with no clique of
size `⌈c * k⌉`. By self-complementarity they also avoid independent sets of the same size. -/
def H1 : Prop :=
  ∃ c > (0 : ℝ), ∃ adj : List Bool × ℕ × ℕ → Bool, IsPolyTime adj ∧
    ∀ᶠ k : ℕ in atTop,
      Nonempty (explicitGraph adj (2 ^ k) ≃g (explicitGraph adj (2 ^ k))ᶜ) ∧
      (explicitGraph adj (2 ^ k)).CliqueFree ⌈c * (k : ℝ)⌉₊

/-- Composition of polynomial-time maps for the weakly explicit adjacency oracle types. -/
def H2 : Prop :=
  ∀ (f : List Bool × ℕ × ℕ → List Bool × ℕ × ℕ) (g : List Bool × ℕ × ℕ → Bool),
    IsPolyTime f → IsPolyTime g → IsPolyTime (g ∘ f)

/-- Unary padding to the next power of two is polynomial time (`2 ^ Nat.size m < 2 * m`). -/
def H3 : Prop :=
  IsPolyTime (fun x : List Bool × ℕ × ℕ =>
    (List.replicate (2 ^ Nat.size x.1.length) true, x.2))

/-- A self-complementary clique-free graph has no homogeneous set of the same size. -/
theorem noHom_of_selfComp {V : Type*} (G : SimpleGraph V) (m : ℕ)
    (hsc : Nonempty (G ≃g Gᶜ)) (hcf : G.CliqueFree m) : NoHomogeneousSet G m := by
  obtain ⟨e⟩ := hsc
  refine ⟨hcf, ?_⟩
  exact hcf.comap ⟨e.symm.toEmbedding.toCopy⟩

/-- The induced graph on the first `n` vertices embeds into the graph on `N ≥ n` vertices. -/
theorem padEmb (adj : List Bool × ℕ × ℕ → Bool) (n N : ℕ) (h : n ≤ N) :
    Nonempty (SimpleGraph.Embedding
      (SimpleGraph.fromRel fun u v : Fin n => adj (List.replicate N true, (u : ℕ), (v : ℕ)))
      (explicitGraph adj N)) :=
  ⟨{ toEmbedding := Fin.castLEEmb h
     map_rel_iff' := by
       intro a b
       simp [explicitGraph, SimpleGraph.fromRel_adj, Fin.ext_iff] }⟩

/-- `NoHomogeneousSet` transfers from `explicitGraph adj N` down to its `n`-vertex prefix. -/
theorem noHom_transfer (adj : List Bool × ℕ × ℕ → Bool) (n N m : ℕ) (h : n ≤ N)
    (H : NoHomogeneousSet (explicitGraph adj N) m) :
    NoHomogeneousSet
      (SimpleGraph.fromRel fun u v : Fin n => adj (List.replicate N true, (u : ℕ), (v : ℕ))) m := by
  obtain ⟨h1, h2⟩ := H
  obtain ⟨e⟩ := padEmb adj n N h
  exact ⟨h1.comap ⟨e.toCopy⟩, h2.comap ⟨(SimpleGraph.Embedding.complEquiv e).toCopy⟩⟩

/-- Binary length bound: for `n ≥ 2`, `Nat.size n ≤ 2 * log n / log 2`. -/
theorem size_le_two_log (n : ℕ) (hn : 2 ≤ n) :
    (Nat.size n : ℝ) ≤ 2 * Real.log n / Real.log 2 := by
  have hs : 0 < Nat.size n := Nat.size_pos.2 (by omega)
  have hp : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.1 (by omega)
  have hpR : (2 : ℝ) ^ (Nat.size n - 1) ≤ (n : ℝ) := by exact_mod_cast hp
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : ((Nat.size n - 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpR
  have hn2 : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hcast : ((Nat.size n - 1 : ℕ) : ℝ) = (Nat.size n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hcast] at hlog
  rw [le_div_iff₀ hl2]
  nlinarith

/-- Losslessness certificate (4-block `P_4`-blowup): every graph `G` on `Fin n` with
`NoHomogeneousSet G m` yields a self-complementary graph `H` on `Fin (4 * n)` with
`H.CliqueFree (2 * m)`. Thus restricting to self-complementary clique-free graphs adds no risk. -/
theorem p4_blowup_selfComp_and_cliqueFree {n m : ℕ} (G : SimpleGraph (Fin n))
    (hG : NoHomogeneousSet G m) :
    ∃ H : SimpleGraph (Fin (4 * n)), Nonempty (H ≃g Hᶜ) ∧ H.CliqueFree (2 * m) := by
  classical
  let P4 : Fin 4 → Fin 4 → Prop := fun i j =>
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨
    (i = 2 ∧ j = 1) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)
  let H0 : SimpleGraph (Fin 4 × Fin n) :=
    { Adj := fun p q =>
        (p.1 = q.1 ∧ (((p.1 = 0 ∨ p.1 = 3) ∧ G.Adj p.2 q.2) ∨
          ((p.1 = 1 ∨ p.1 = 2) ∧ Gᶜ.Adj p.2 q.2))) ∨ P4 p.1 q.1
      symm := ⟨by
        rintro ⟨i, x⟩ ⟨j, y⟩ h
        rcases h with ⟨rfl, ⟨h03, ha⟩ | ⟨h12, ha⟩⟩ | hp4
        · exact Or.inl ⟨rfl, Or.inl ⟨h03, ha.symm⟩⟩
        · exact Or.inl ⟨rfl, Or.inr ⟨h12, ha.symm⟩⟩
        · refine Or.inr ?_
          dsimp only [P4] at hp4 ⊢
          rcases hp4 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp⟩
      loopless := ⟨by
        rintro ⟨i, x⟩ h
        rcases h with ⟨_, ⟨_, ha⟩ | ⟨_, ha⟩⟩ | hp4
        · exact G.ne_of_adj ha rfl
        · exact Gᶜ.ne_of_adj ha rfl
        · dsimp only [P4] at hp4
          fin_cases i <;> simp at hp4⟩ }
  let perm : Fin 4 ≃ Fin 4 :=
    { toFun := fun i => match i with | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 3 | ⟨2, _⟩ => 0 | ⟨3, _⟩ => 2
      invFun := fun i => match i with | ⟨0, _⟩ => 2 | ⟨1, _⟩ => 0 | ⟨2, _⟩ => 3 | ⟨3, _⟩ => 1
      left_inv := fun i => by fin_cases i <;> rfl
      right_inv := fun i => by fin_cases i <;> rfl }
  have hπ_sc : Nonempty (H0 ≃g H0ᶜ) := by
    refine ⟨{ toEquiv := Equiv.prodCongr perm (Equiv.refl (Fin n))
              map_rel_iff' := by
                rintro ⟨i, x⟩ ⟨j, y⟩
                have hne : G.Adj x y → x ≠ y := G.ne_of_adj
                simp only [Equiv.prodCongr_apply, Equiv.refl_apply, Prod.map_apply,
                  SimpleGraph.compl_adj, ne_eq, Prod.mk.injEq]
                fin_cases i <;> fin_cases j <;>
                  simp [H0, P4, perm, SimpleGraph.compl_adj] <;> tauto }⟩
  have hcf0 : H0.CliqueFree (2 * m) := by
    intro S ⟨hScl, hScard⟩
    let S0 := S.filter (fun p : Fin 4 × Fin n => p.1 = 0)
    let S1 := S.filter (fun p : Fin 4 × Fin n => p.1 = 1)
    let S2 := S.filter (fun p : Fin 4 × Fin n => p.1 = 2)
    let S3 := S.filter (fun p : Fin 4 × Fin n => p.1 = 3)
    have hsum : S.card = S0.card + S1.card + S2.card + S3.card := by
      have hpart : S = S0 ∪ (S1 ∪ (S2 ∪ S3)) := by
        ext ⟨i, x⟩
        simp only [S0, S1, S2, S3, Finset.mem_union, Finset.mem_filter]
        fin_cases i <;> simp
      have hd23 : Disjoint S2 S3 := Finset.disjoint_filter.mpr (fun _ _ h2 h3 => by simp [h2] at h3)
      have hd123 : Disjoint S1 (S2 ∪ S3) := by
        rw [Finset.disjoint_union_right]
        exact ⟨Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by simp [h1] at h2),
          Finset.disjoint_filter.mpr (fun _ _ h1 h3 => by simp [h1] at h3)⟩
      have hd0123 : Disjoint S0 (S1 ∪ (S2 ∪ S3)) := by
        rw [Finset.disjoint_union_right, Finset.disjoint_union_right]
        exact ⟨Finset.disjoint_filter.mpr (fun _ _ h0 h1 => by simp [h0] at h1),
          Finset.disjoint_filter.mpr (fun _ _ h0 h2 => by simp [h0] at h2),
          Finset.disjoint_filter.mpr (fun _ _ h0 h3 => by simp [h0] at h3)⟩
      rw [hpart, Finset.card_union_of_disjoint hd0123, Finset.card_union_of_disjoint hd123,
        Finset.card_union_of_disjoint hd23]
      omega
    have hlt_G : ∀ r : Fin 4, (r = 0 ∨ r = 3) → (S.filter (fun p => p.1 = r)).card < m := by
      intro r hr
      by_contra hge
      push Not at hge
      obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hge
      let U := T.image Prod.snd
      have hinj : Set.InjOn Prod.snd (T : Set (Fin 4 × Fin n)) := by
        intro p hp q hq heq
        have hp' := (Finset.mem_filter.mp (hTsub hp)).2
        have hq' := (Finset.mem_filter.mp (hTsub hq)).2
        exact Prod.ext (hp'.trans hq'.symm) heq
      have hUcard : U.card = m := (Finset.card_image_of_injOn hinj).trans hTcard
      apply hG.1 U
      refine ⟨?_, hUcard⟩
      intro x hx y hy hxy
      obtain ⟨⟨i, x'⟩, hpx, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨⟨j, y'⟩, hpy, rfl⟩ := Finset.mem_image.mp hy
      have hi : i = r := (Finset.mem_filter.mp (hTsub hpx)).2
      have hj : j = r := (Finset.mem_filter.mp (hTsub hpy)).2
      have hne : (i, x') ≠ (j, y') := fun h => hxy (congrArg Prod.snd h)
      have hadj := hScl (Finset.mem_filter.mp (hTsub hpx)).1 (Finset.mem_filter.mp (hTsub hpy)).1 hne
      subst hi hj
      rcases hadj with ⟨_, ⟨_, ha⟩ | ⟨h12, _⟩⟩ | hp4
      · exact ha
      · rcases hr with rfl | rfl <;> simp at h12
      · dsimp only [P4] at hp4; rcases hr with rfl | rfl <;> simp at hp4
    have hlt_Gc : ∀ r : Fin 4, (r = 1 ∨ r = 2) → (S.filter (fun p => p.1 = r)).card < m := by
      intro r hr
      by_contra hge
      push Not at hge
      obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hge
      let U := T.image Prod.snd
      have hinj : Set.InjOn Prod.snd (T : Set (Fin 4 × Fin n)) := by
        intro p hp q hq heq
        have hp' := (Finset.mem_filter.mp (hTsub hp)).2
        have hq' := (Finset.mem_filter.mp (hTsub hq)).2
        exact Prod.ext (hp'.trans hq'.symm) heq
      have hUcard : U.card = m := (Finset.card_image_of_injOn hinj).trans hTcard
      apply hG.2 U
      refine ⟨?_, hUcard⟩
      intro x hx y hy hxy
      obtain ⟨⟨i, x'⟩, hpx, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨⟨j, y'⟩, hpy, rfl⟩ := Finset.mem_image.mp hy
      have hi : i = r := (Finset.mem_filter.mp (hTsub hpx)).2
      have hj : j = r := (Finset.mem_filter.mp (hTsub hpy)).2
      have hne : (i, x') ≠ (j, y') := fun h => hxy (congrArg Prod.snd h)
      have hadj := hScl (Finset.mem_filter.mp (hTsub hpx)).1 (Finset.mem_filter.mp (hTsub hpy)).1 hne
      subst hi hj
      rcases hadj with ⟨_, ⟨h03, _⟩ | ⟨_, ha⟩⟩ | hp4
      · rcases hr with rfl | rfl <;> simp at h03
      · exact ha
      · dsimp only [P4] at hp4; rcases hr with rfl | rfl <;> simp at hp4
    have h0lt : S0.card < m := hlt_G 0 (Or.inl rfl)
    have h1lt : S1.card < m := hlt_Gc 1 (Or.inl rfl)
    have h2lt : S2.card < m := hlt_Gc 2 (Or.inr rfl)
    have h3lt : S3.card < m := hlt_G 3 (Or.inr rfl)
    have hno : ∀ r s : Fin 4, r ≠ s → ¬ P4 r s →
        (S.filter (fun p => p.1 = r)).card = 0 ∨ (S.filter (fun p => p.1 = s)).card = 0 := by
      intro r s hrs hnp4
      by_contra hboth
      push Not at hboth
      obtain ⟨⟨i, x⟩, hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hboth.1)
      obtain ⟨⟨j, y⟩, hy⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hboth.2)
      have hi : i = r := (Finset.mem_filter.mp hx).2
      have hj : j = s := (Finset.mem_filter.mp hy).2
      have hne : (i, x) ≠ (j, y) := fun h => hrs (hi.symm.trans ((congrArg Prod.fst h).trans hj))
      have hadj := hScl (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hne
      subst hi hj
      rcases hadj with ⟨heq, _⟩ | hp4
      · exact hrs heq
      · exact hnp4 hp4
    have h02 : S0.card = 0 ∨ S2.card = 0 := hno 0 2 (by decide) (by dsimp only [P4]; decide)
    have h03 : S0.card = 0 ∨ S3.card = 0 := hno 0 3 (by decide) (by dsimp only [P4]; decide)
    have h13 : S1.card = 0 ∨ S3.card = 0 := hno 1 3 (by decide) (by dsimp only [P4]; decide)
    omega
  let e := finProdFinEquiv (m := 4) (n := n)
  let H : SimpleGraph (Fin (4 * n)) := H0.map e.toEmbedding
  have hIso : H0 ≃g H :=
    { toEquiv := e
      map_rel_iff' := by
        intro p q
        simp only [H, SimpleGraph.map_adj, Equiv.toEmbedding_apply]
        constructor
        · rintro ⟨p', q', hpq, hp, hq⟩
          rw [e.injective hp, e.injective hq] at hpq
          exact hpq
        · intro hpq
          exact ⟨p, q, hpq, rfl, rfl⟩ }
  have hIsoC : H0ᶜ ≃g Hᶜ :=
    { toEquiv := hIso.toEquiv
      map_rel_iff' := by
        intro p q
        simp [SimpleGraph.compl_adj, hIso.map_rel_iff] }
  obtain ⟨h0sc⟩ := hπ_sc
  refine ⟨H, ⟨hIso.symm.trans (h0sc.trans hIsoC)⟩, ?_⟩
  exact hcf0.comap ⟨hIso.symm.toEmbedding.toCopy⟩

theorem main : H1 → H2 → H3 → type_of% @Erdos78.erdos_78 := by
  rintro ⟨c, hc, adj, hadj, hev⟩ h2 h3
  set pad : List Bool × ℕ × ℕ → List Bool × ℕ × ℕ :=
    fun x => (List.replicate (2 ^ Nat.size x.1.length) true, x.2) with hpad
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 * c / Real.log 2, by positivity, adj ∘ pad, h2 pad adj h3 hadj, ?_⟩
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  refine eventually_atTop.2 ⟨max 2 (2 ^ K), fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hsK : K ≤ Nat.size n := by
    have : K < Nat.size n + 1 := by
      rw [Nat.lt_succ_iff]
      exact (Nat.lt_size.2 (le_trans (le_max_right _ _) hn)).le
    omega
  obtain ⟨hsc, hcf⟩ := hK _ hsK
  have hbig : NoHomogeneousSet (explicitGraph adj (2 ^ Nat.size n)) ⌈c * (Nat.size n : ℝ)⌉₊ :=
    noHom_of_selfComp (explicitGraph adj (2 ^ Nat.size n)) _ hsc hcf
  have hsub := noHom_transfer adj n (2 ^ Nat.size n) ⌈c * (Nat.size n : ℝ)⌉₊
    (Nat.lt_size_self n).le hbig
  have hgr : explicitGraph (adj ∘ pad) n =
      SimpleGraph.fromRel fun u v : Fin n =>
        adj (List.replicate (2 ^ Nat.size n) true, (u : ℕ), (v : ℕ)) := by
    simp [explicitGraph, hpad]
  have hm : ⌈c * (Nat.size n : ℝ)⌉₊ ≤ ⌈2 * c / Real.log 2 * Real.log n⌉₊ := by
    apply Nat.ceil_mono
    have hsz := size_le_two_log n hn2
    calc c * (Nat.size n : ℝ) ≤ c * (2 * Real.log n / Real.log 2) :=
          mul_le_mul_of_nonneg_left hsz hc.le
      _ = 2 * c / Real.log 2 * Real.log n := by ring
  rw [hgr]
  exact ⟨hsub.1.mono hm, hsub.2.mono hm⟩

end OMA.R_Erdos78_erdos_78_R1
