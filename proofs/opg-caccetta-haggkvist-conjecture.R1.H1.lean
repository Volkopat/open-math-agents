import OMAReductions.R_opg_caccetta_haggkvist_conjecture_R1

/-!
# Short directed cycles for minimum outdegree two

Caccetta and Häggkvist proved in 1978 that every finite nonempty loopless
digraph of minimum outdegree at least two has a simple directed cycle of
length at most ceil(n/2). This settles H1 of the parent reduction. The theorem applies equally to
vertices of unequal outdegrees and to graphs that contain symmetric subgraphs.

Choose a smallest nonempty set S with fewer than two exterior neighbors.
Every vertex of S has an internal successor. If S has at most ceil(n/2)
vertices, following successors suffices. Otherwise S has a unique exit z
and its complement is smaller than S. Starting from z, let l be the first
distance to S, and A the vertices of S reached by that round. Starting from
all of A, let m be the first distance out of S. The second search exits at z.
The two counts give |Sᶜ| + |A| ≥ 1 + 2l and |S| ≥ |A| + 2(m−1).
Thus 2(l+m)−1 ≤ n. The walks concatenate at the same entry vertex of A.

The single-exit lemma uses an arbitrary positive expansion rate. For every
admissible order and outdegree, the cyclic digraph with forward steps 1
through r attains ceil(n/r), even when testing positive closed walks.

Reference: L. Caccetta and R. Häggkvist, On minimal digraphs with given
girth, Congressus Numerantium 21 (1978), 181–187. For context see J. Shen,
On the girth of digraphs, Discrete Mathematics 211 (2000), 167–181,
https://doi.org/10.1016/S0012-365X(99)00323-4.
-/

-- Credit: @qtyan0721
-- Agent: codex
-- Model: gpt-6.2-astra

namespace OMA.CaccettaHaggkvist
open OMA.S_opg_caccetta_haggkvist_conjecture
open OMA.R_opg_caccetta_haggkvist_conjecture_R1

namespace Expansion

variable {V : Type} [Fintype V]

open scoped Classical in
/-- Vertices outside a set that receive an arc from it. -/
noncomputable def frontier (G : Digraph V) (U : Finset V) : Finset V :=
  Finset.univ.filter fun y => y ∉ U ∧ ∃ x ∈ U, G.Adj x y

theorem mem_frontier {G : Digraph V} {U : Finset V} {y : V} :
    y ∈ frontier G U ↔ y ∉ U ∧ ∃ x ∈ U, G.Adj x y := by
  classical
  simp [frontier]

open scoped Classical in
private noncomputable def ball (G : Digraph V) (A : Finset V) : ℕ → Finset V
  | 0 => A
  | i + 1 => ball G A i ∪ frontier G (ball G A i)

private theorem ball_step (G : Digraph V) (A : Finset V) (i : ℕ) :
    ball G A i ⊆ ball G A (i+1) := by
  classical
  exact Finset.subset_union_left

private theorem ball_nonempty (G : Digraph V) {A : Finset V} (hA : A.Nonempty) (i : ℕ) :
    (ball G A i).Nonempty := by
  induction i with
  | zero => exact hA
  | succ i ih => exact ih.mono (ball_step G A i)

private theorem card_ball_step (G : Digraph V) (A : Finset V) (i : ℕ) :
    (ball G A (i+1)).card = (ball G A i).card + (frontier G (ball G A i)).card := by
  classical
  apply Finset.card_union_of_disjoint
  exact Finset.disjoint_left.mpr (fun _ hx hy => (mem_frontier.mp hy).1 hx)

private def WalkOfLength (G : Digraph V) (x y : V) (k : ℕ) : Prop :=
  ∃ f : ℕ → V, f 0 = x ∧ f k = y ∧ ∀ i < k, G.Adj (f i) (f (i+1))

omit [Fintype V] in
private theorem walk_append {G : Digraph V} {x y z : V} {k l : ℕ}
    (p : WalkOfLength G x y k) (q : WalkOfLength G y z l) :
    WalkOfLength G x z (k+l) := by
  obtain ⟨f, hf, hk, ef⟩ := p
  obtain ⟨g, hg, hl, eg⟩ := q
  let w (i : ℕ) := if i < k then f i else g (i-k)
  refine ⟨w, ?_, ?_, ?_⟩
  · by_cases h : 0 < k
    · simpa [w, h] using hf
    · have he : k = 0 := by omega
      subst k
      simpa [w, ← hk, hf] using hg
  · simpa [w] using hl
  · intro i hi
    by_cases h : i+1 < k
    · simpa [w, h, show i < k by omega] using ef i (by omega)
    · by_cases he : i+1 = k
      · have hs := ef i (by omega)
        simpa [w, h, show i < k by omega, he, hk, hg] using hs
      · have ha : ¬ i < k := by omega
        have hs := eg (i-k) (by omega)
        simpa [w, h, ha, show i+1-k = (i-k)+1 by omega] using hs

private theorem ball_walk (G : Digraph V) (A : Finset V) (i : ℕ) {v : V}
    (hv : v ∈ ball G A i) : ∃ u ∈ A, ∃ k ≤ i, WalkOfLength G u v k := by
  classical
  induction i generalizing v with
  | zero => exact ⟨v, hv, 0, le_rfl, fun _ => v, rfl, rfl, by simp⟩
  | succ i ih =>
    rcases Finset.mem_union.mp hv with h | h
    · obtain ⟨u, hu, k, hk, p⟩ := ih h
      exact ⟨u, hu, k, by omega, p⟩
    · obtain ⟨w, hw, e⟩ := (mem_frontier.mp h).2
      obtain ⟨u, hu, k, hk, p⟩ := ih hw
      have q : WalkOfLength G w v 1 := by
        refine ⟨fun j => if j = 0 then w else v, by simp, by simp, ?_⟩
        intro j hj
        have : j = 0 := by omega
        simpa [this] using e
      exact ⟨u, hu, k+1, by omega, walk_append p q⟩

/-- Before leaving a region, a ball gains r vertices at each step for
which it and the next ball both stay inside. -/
private theorem first_exit (G : Digraph V) (A S : Finset V) (hA : A.Nonempty)
    (hAS : A ⊆ S) (r : ℕ) (hr : 0 < r) (hfull : (frontier G S).Nonempty)
    (hexpand : ∀ U : Finset V, U.Nonempty → U ⊂ S → frontier G U ⊆ S →
      r ≤ (frontier G U).card) :
    ∃ j, ball G A j ⊆ S ∧ ¬ ball G A (j+1) ⊆ S ∧
      A.card + r*j ≤ (ball G A j).card := by
  classical
  have bound (i : ℕ) (h : ball G A i ⊆ S) : A.card + r*i ≤ (ball G A i).card := by
    induction i with
    | zero => simp [ball]
    | succ i ih =>
      have hsub := (ball_step G A i).trans h
      have hne : ball G A i ≠ S := by
        intro eq
        obtain ⟨w, hw⟩ := hfull
        have hm : w ∈ frontier G (ball G A i) := eq ▸ hw
        exact (mem_frontier.mp hw).1 (h (Finset.mem_union_right _ hm))
      have hfsub : frontier G (ball G A i) ⊆ S := fun _ hv => h (Finset.mem_union_right _ hv)
      have he := hexpand _ (ball_nonempty G hA i) (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩) hfsub
      have hp := ih hsub
      rw [card_ball_step, Nat.mul_succ]
      omega
  have leaves : ∃ i, ¬ ball G A i ⊆ S := by
    by_contra! hall
    have h := bound (S.card+1) (hall _)
    have hc := Finset.card_le_card (hall (S.card+1))
    have hm := Nat.mul_le_mul_right (S.card+1) hr
    simp only [Nat.one_mul] at hm
    omega
  have hx := Nat.find_spec leaves
  cases he : Nat.find leaves with
  | zero => rw [he] at hx; exact (hx hAS).elim
  | succ j =>
    have hin : ball G A j ⊆ S := by
      by_contra bad
      have := Nat.find_min' leaves bad
      omega
    rw [he] at hx
    exact ⟨j, hin, hx, bound j hin⟩

open scoped Classical in
/-- A unique exit gives a short cycle through that very exit. On the inside,
a nonempty proper subset must gain r vertices while its frontier stays inside. On the
outside this must hold for every nonempty subset, including the whole outside.
The graph itself need not be strongly connected or have a transitive action. -/
theorem cycle_through_single_exit (G : Digraph V) (hloop : ∀ w, ¬ G.Adj w w)
    (S : Finset V) (z : V) (hcut : frontier G S = {z}) (r : ℕ) (hr : 0 < r)
    (hin : ∀ U : Finset V, U.Nonempty → U ⊂ S → frontier G U ⊆ S → r ≤ (frontier G U).card)
    (hout : ∀ U : Finset V, U.Nonempty → U ⊆ Sᶜ → r ≤ (frontier G U).card) :
    ∃ k, k ≤ ⌈(Fintype.card V : ℚ) / r⌉₊ ∧ 2 ≤ k ∧ ∃ c : Fin k → V,
      Function.Injective c ∧ (∀ i, G.Adj (c i) (c (finRotate k i))) ∧ z ∈ Set.range c := by
  classical
  let C := Sᶜ
  have hzf : z ∈ frontier G S := by rw [hcut]; simp
  have hz : z ∉ S := (mem_frontier.mp hzf).1
  have hzc : z ∈ C := Finset.mem_compl.mpr hz
  have hZ : ({z} : Finset V) ⊆ C := by simpa using hzc
  have hcpos : (frontier G C).Nonempty := Finset.card_pos.mp
    (hr.trans_le (hout C ⟨z, hzc⟩ (Finset.Subset.refl _)))
  obtain ⟨j, hpre, houtside, hcount⟩ := first_exit G {z} C (Finset.singleton_nonempty z)
    hZ r hr hcpos (fun U hU hsub _ => hout U hU hsub.subset)
  let P := ball G {z} (j+1)
  let A := P \ C
  have hA : A.Nonempty := by
    obtain ⟨x, hx, hxc⟩ := Finset.not_subset.mp houtside
    exact ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxc⟩⟩
  have hAS : A ⊆ S := by
    intro x hx
    simpa [C] using (Finset.mem_sdiff.mp hx).2
  have hfirst : 1 + r*(j+1) ≤ C.card + A.card := by
    have hf := hout _ (ball_nonempty G (Finset.singleton_nonempty z) j) hpre
    have hp := Finset.card_le_card_sdiff_add_card (s := P) (t := C)
    change (ball G {z} (j+1)).card ≤ A.card + C.card at hp
    rw [card_ball_step] at hp
    simp only [Finset.card_singleton] at hcount
    rw [Nat.mul_succ]
    omega
  obtain ⟨i, hbefore, hexit, hlast⟩ := first_exit G A S hA hAS r hr ⟨z, hzf⟩ hin
  obtain ⟨w, hw, hws⟩ := Finset.not_subset.mp hexit
  have hwz : w = z := by
    rcases Finset.mem_union.mp hw with h | h
    · exact (hws (hbefore h)).elim
    · obtain ⟨x, hx, e⟩ := (mem_frontier.mp h).2
      have hf : w ∈ frontier G S := mem_frontier.mpr ⟨hws, x, hbefore hx, e⟩
      simpa only [hcut, Finset.mem_singleton] using hf
  subst w
  obtain ⟨a, ha, t, ht, back⟩ := ball_walk G A (i+1) hw
  obtain ⟨u, hu, l, hl, out⟩ := ball_walk G {z} (j+1) (Finset.mem_sdiff.mp ha).1
  have huz : u = z := Finset.mem_singleton.mp hu
  subst u
  have hpos : 0 < l := by
    by_contra! h
    have he : l = 0 := by omega
    obtain ⟨f, hf, hf', _⟩ := out
    rw [he, hf] at hf'
    exact hz (by simpa only [hf'] using hAS ha)
  have hsize : C.card + S.card = Fintype.card V := by
    exact Finset.card_compl_add_card S
  have hlast' := hlast.trans (Finset.card_le_card hbefore)
  have hprod : (j+1+i)*r < Fintype.card V := by
    rw [Nat.mul_comm, Nat.mul_add]
    omega
  have hrq : (0 : ℚ) < (r : ℚ) := by exact_mod_cast hr
  have hceil : j+1+i < ⌈(Fintype.card V : ℚ) / r⌉₊ := by
    apply Nat.lt_ceil.mpr
    apply (lt_div_iff₀ hrq).mpr
    exact_mod_cast hprod
  obtain ⟨f, hzero, hend, hedge⟩ := walk_append out back
  obtain ⟨k, hk, htwo, c, hc, e, hroot⟩ :=
    cycle_through_of_closed_walk G hloop (l+t) f (by omega) (hend.trans hzero.symm) hedge
  exact ⟨k, by omega, htwo, c, hc, e, hzero ▸ hroot⟩

omit [Fintype V] in
/-- If every vertex in a finite region has an internal successor, there is a
simple cycle of length at most the region size. -/
private theorem cycle_in_region (G : Digraph V) (hloop : ∀ w, ¬ G.Adj w w)
    (S : Finset V) (hS : S.Nonempty) (hsucc : ∀ x ∈ S, ∃ y ∈ S, G.Adj x y) :
    ∃ k, k ≤ S.card ∧ HasDirectedCycleOfLength G k := by
  classical
  let D : Digraph {x // x ∈ S} := ⟨fun x y => G.Adj x.1 y.1⟩
  obtain ⟨v, hv⟩ := hS
  let : Nonempty {x // x ∈ S} := ⟨⟨v, hv⟩⟩
  have hdegree (x : {x // x ∈ S}) : 1 ≤ outdegree D x := by
    obtain ⟨y, hy, hxy⟩ := hsucc x.1 x.2
    apply Finset.card_pos.mpr
    exact ⟨⟨y, hy⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩⟩
  obtain ⟨k, hk, htwo, c, hc, e⟩ := cycle_of_min_outdegree_pos D (fun x => hloop x.1) hdegree
  exact ⟨k, by simpa using hk, htwo, (fun i => (c i).1), Subtype.val_injective.comp hc, e⟩

/-- A short cycle for arbitrary finite loopless digraphs of minimum outdegree
at least two (Caccetta–Häggkvist, 1978). Choose a smallest set with fewer
than two exterior neighbors. It either contains the required cycle or has a
unique exit to which the two successive expanding searches return. -/
theorem cycle_of_min_outdegree_two [Nonempty V] (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ w, ¬ G.Adj w w) (hdegree : ∀ w, 2 ≤ outdegree G w) :
    ∃ k, k ≤ ⌈(Fintype.card V : ℚ) / 2⌉₊ ∧ HasDirectedCycleOfLength G k := by
  classical
  let candidates := (Finset.univ : Finset (Finset V)).filter fun U =>
    U.Nonempty ∧ (frontier G U).card < 2
  have hempty : frontier G Finset.univ = ∅ := by ext x; simp [mem_frontier]
  have hcan : candidates.Nonempty := by
    refine ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.univ_nonempty, ?_⟩⟩
    simp [hempty]
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image candidates Finset.card hcan
  obtain ⟨hs, hcut⟩ := (Finset.mem_filter.mp hS).2
  have growth (U : Finset V) (hu : U.Nonempty) (hlt : U.card < S.card) :
      2 ≤ (frontier G U).card := by
    by_contra! hf
    have hc := hmin U (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu, hf⟩)
    omega
  have succ_in (x : V) (hx : x ∈ S) : ∃ y ∈ S, G.Adj x y := by
    have hlt : (frontier G S).card < (Finset.univ.filter (G.Adj x)).card :=
      hcut.trans_le (hdegree x)
    obtain ⟨y, hy, hout⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have e := (Finset.mem_filter.mp hy).2
    refine ⟨y, ?_, e⟩
    by_contra hyn
    exact hout (mem_frontier.mpr ⟨hyn, x, hx, e⟩)
  by_cases hsmall : S.card ≤ ⌈(Fintype.card V : ℚ) / 2⌉₊
  · obtain ⟨k, hk, hc⟩ := cycle_in_region G hloop S hs succ_in
    exact ⟨k, hk.trans hsmall, hc⟩
  have comp_lt : Sᶜ.card < S.card := by
    have htotal := Finset.card_compl_add_card S
    have hnat : Fintype.card V ≤ 2 * ⌈(Fintype.card V : ℚ) / 2⌉₊ := by
      have h := Nat.le_ceil ((Fintype.card V : ℚ) / 2)
      have h' := (div_le_iff₀ (by norm_num : (0:ℚ)<2)).mp h
      rw [mul_comm] at h'
      exact_mod_cast h'
    omega
  obtain ⟨x, hx⟩ := hs
  obtain ⟨y, hy, hxy⟩ := succ_in x hx
  have hyx : y ≠ x := by
    intro h
    exact hloop x (by simpa only [h] using hxy)
  have Tne : (S.erase x).Nonempty := ⟨y, Finset.mem_erase.mpr ⟨hyx, hy⟩⟩
  have hex : (frontier G S).Nonempty := by
    by_contra hn
    have hf : frontier G (S.erase x) ⊆ {x} := by
      intro t ht
      obtain ⟨hnot, u, hu, e⟩ := mem_frontier.mp ht
      have htS : t ∈ S := by
        by_contra htS
        exact hn ⟨t, mem_frontier.mpr ⟨htS, u, (Finset.mem_erase.mp hu).2, e⟩⟩
      by_contra htne
      exact hnot (Finset.mem_erase.mpr ⟨fun h => htne (Finset.mem_singleton.mpr h), htS⟩)
    have he := growth _ Tne (Finset.card_erase_lt_of_mem hx)
    have hle := Finset.card_le_card hf
    simp only [Finset.card_singleton] at hle
    omega
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (show (frontier G S).card = 1 by
    have := Finset.card_pos.mpr hex
    omega)
  obtain ⟨k, hk, ht, c, hi, he, _⟩ := cycle_through_single_exit G hloop S z hz 2 (by decide)
    (fun U hU hprop _ => growth U hU (Finset.card_lt_card hprop))
    (fun U hU hsub => growth U hU ((Finset.card_le_card hsub).trans_lt comp_lt))
  exact ⟨k, by simpa using hk, ht, c, hi, he⟩

end Expansion

/-- Enumerating all outneighbors without repetition computes the outdegree. -/
private theorem degree_of_enumeration {V I : Type} [Fintype V] [Fintype I]
    (G : Digraph V) [DecidableRel G.Adj] (v : V) (f : I → V) (hi : Function.Injective f)
    (h : ∀ w, G.Adj v w ↔ ∃ i, f i = w) : outdegree G v = Fintype.card I := by
  classical
  unfold outdegree
  have heq : Finset.univ.filter (G.Adj v) = Finset.univ.image f := by
    ext w
    simpa only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] using h w
  rw [heq, Finset.card_image_of_injective _ hi, Finset.card_univ]

open scoped Classical in
/-- For every order N and every 1 ≤ r < N, the cyclic digraph with forward
steps 1 through r attains the ceiling exactly. Even a nonsimple nonempty
closed walk needs at least ceil(N/r) steps, since its total positive advance
is divisible by N. -/
theorem cyclic_steps_exact_girth (n r : ℕ) (hr : 0 < r) (hrn : r < n+1) :
    ∃ D : Digraph (ZMod (n+1)), (∀ v, ¬ D.Adj v v) ∧ (∀ v, outdegree D v = r) ∧
      HasDirectedCycleOfLength D ⌈((n+1 : ℕ) : ℚ) / r⌉₊ ∧
      ∀ t, 0 < t → ∀ c : Fin t → ZMod (n+1), (∀ i, D.Adj (c i) (c (finRotate t i))) →
        ⌈((n+1 : ℕ) : ℚ) / r⌉₊ ≤ t := by
  classical
  let step (i : Fin r) : ZMod (n+1) := ((i.val+1 : ℕ) : ZMod (n+1))
  have hval (i : Fin r) : (step i).val = i.val+1 :=
    ZMod.val_natCast_of_lt (by have := i.isLt; omega)
  have hinj : Function.Injective step := by
    intro i j heq
    have h := congrArg ZMod.val heq
    rw [hval, hval] at h
    exact Fin.ext (by omega)
  let D : Digraph (ZMod (n+1)) := ⟨fun x y => ∃ i, y = x + step i⟩
  let decD : DecidableRel D.Adj := fun _ _ => Classical.propDecidable _
  let : DecidableRel D.Adj := decD
  have hloop (v) : ¬ D.Adj v v := by
    rintro ⟨i, h⟩
    have hz : step i = 0 := add_left_cancel (show v + step i = v + 0 by simpa using h.symm)
    have hv := congrArg ZMod.val hz
    rw [hval, ZMod.val_zero] at hv
    omega
  have hdeg (v) : @outdegree _ _ D decD v = r := by
    have hi : Function.Injective (fun i => v + step i) := fun _ _ h => hinj (add_left_cancel h)
    refine (degree_of_enumeration D v (fun i => v + step i) hi ?_).trans (Fintype.card_fin r)
    intro w
    constructor
    · rintro ⟨i, h⟩; exact ⟨i, h.symm⟩
    · rintro ⟨i, h⟩; exact ⟨i, h.symm⟩
  have lower (t : ℕ) (ht : 0 < t) (c : Fin t → ZMod (n+1))
      (edges : ∀ i, D.Adj (c i) (c (finRotate t i))) : ⌈((n+1 : ℕ) : ℚ) / r⌉₊ ≤ t := by
    have edges' (i : Fin t) : ∃ a : Fin r, c (finRotate t i) = c i + step a := edges i
    choose a ha using edges'
    let d (i : Fin t) := (a i).val+1
    have hz : ((∑ i, d i : ℕ) : ZMod (n+1)) = 0 := by
      rw [Nat.cast_sum]
      calc ∑ i, ((d i : ℕ) : ZMod (n+1)) = ∑ i, (c (finRotate t i) - c i) := by
             apply Finset.sum_congr rfl
             intro i _
             change step (a i) = c (finRotate t i) - c i
             rw [ha i, add_sub_cancel_left]
           _ = 0 := by rw [Finset.sum_sub_distrib, Equiv.sum_comp, sub_self]
    have hdvd := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have : NeZero t := ⟨by omega⟩
    have hpos : 0 < ∑ i, d i :=
      Finset.sum_pos (fun i _ => Nat.succ_pos (a i).val) Finset.univ_nonempty
    have hsize : ∑ i, d i ≤ t*r := by
      calc ∑ i, d i ≤ ∑ _i : Fin t, r := Finset.sum_le_sum (fun i _ => (a i).isLt)
           _ = _ := by simp
    have hn := (Nat.le_of_dvd hpos hdvd).trans hsize
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ (show (0 : ℚ) < r by exact_mod_cast hr)).mpr
    exact_mod_cast hn
  let gstep (i : Fin r) : Multiplicative (ZMod (n+1)) := Multiplicative.ofAdd (step i)
  let E := Finset.univ.image gstep
  have hgi : Function.Injective gstep := Multiplicative.ofAdd.injective.comp hinj
  have hcard : E.card = r := by simp [E, Finset.card_image_of_injective _ hgi]
  obtain ⟨t, hlen, ht, c, hc, he⟩ := cycle_of_cayley_subgraph D hloop
    Multiplicative.toAdd.toEmbedding E r hr hcard.ge (by
      intro x s hs
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
      exact ⟨i, rfl⟩)
  have hup : t ≤ ⌈((n+1 : ℕ) : ℚ) / r⌉₊ := by simpa only [ZMod.card] using hlen
  have heq := le_antisymm hup (lower t (by omega) c he)
  exact ⟨D, hloop, hdeg, heq ▸ ⟨ht, c, hc, he⟩, lower⟩

/-- The original H1 follows directly from the unrestricted degree-two theorem. -/
theorem degree_two_step : OMA.R_opg_caccetta_haggkvist_conjecture_R1.H1 := by
  intro V _ _ G _ hloop hdegree _
  exact Expansion.cycle_of_min_outdegree_two G hloop hdegree

/-- H2 alone now suffices for the full conjecture as stated in the catalog. -/
theorem conjecture_of_remaining_step :
    OMA.R_opg_caccetta_haggkvist_conjecture_R1.H2 → type_of% @OMA.S_opg_caccetta_haggkvist_conjecture.main :=
  OMA.R_opg_caccetta_haggkvist_conjecture_R1.main degree_two_step

end OMA.CaccettaHaggkvist

theorem OMA.solution : OMA.R_opg_caccetta_haggkvist_conjecture_R1.H1 :=
  OMA.CaccettaHaggkvist.degree_two_step
