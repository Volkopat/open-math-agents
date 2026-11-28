import OMAReductions.R_Erdos599_erdos_599_R2
import Mathlib

/-!
# Finite Vertex Menger's Theorem (`Erdos599.erdos_599.R2.H2`)

We prove the finite vertex form of Menger's theorem via unit-capacity 0-1 max-flow = min-cut
on the vertex-splitting digraph `Node V = src | snk | vin v | vout v`:
- Arcs: `src → vin a` (`a ∈ A`), `vin v → vout v`, `vout u → vin v` (`G.Adj u v`), `vout b → snk` (`b ∈ B`).
- By irreflexivity of `G`, `arc` has no antiparallel edges (`arc x y → ¬ arc y x`).
- Every 0-1 flow `E` automatically satisfies `indeg E x = outdeg E x ≤ 1` at all internal nodes.
- Taking a maximum-value 0-1 flow `E`, the residual augmenting-path lemma shows `snk` is
  unreachable from `src`, yielding a cut `K` of size `outdeg E src` which projects to a
  vertex hitting set `C` of size `≤ outdeg E src`.
- Flow decomposition by induction on `outdeg E src` extracts `outdeg E src` pairwise
  vertex-disjoint `A`–`B` simple paths in `G`.

Credit: @yhay81
-/

namespace Erdos599R2H2

private inductive Node (V : Type) where
  | src : Node V
  | snk : Node V
  | vin : V → Node V
  | vout : V → Node V
  deriving DecidableEq

private def nodeEquiv (V : Type) : (Unit ⊕ Unit ⊕ V ⊕ V) ≃ Node V where
  toFun
    | .inl () => .src
    | .inr (.inl ()) => .snk
    | .inr (.inr (.inl v)) => .vin v
    | .inr (.inr (.inr v)) => .vout v
  invFun
    | .src => .inl ()
    | .snk => .inr (.inl ())
    | .vin v => .inr (.inr (.inl v))
    | .vout v => .inr (.inr (.inr v))
  left_inv := by rintro (⟨⟩ | ⟨⟩ | v | v) <;> rfl
  right_inv := by rintro (_ | _ | v | v) <;> rfl

private def arc {V : Type} (G : SimpleGraph V) (A B : Set V) : Node V → Node V → Prop
  | .src, .vin a => a ∈ A
  | .vin v, .vout w => v = w
  | .vout u, .vin v => G.Adj u v
  | .vout b, .snk => b ∈ B
  | _, _ => False

private lemma arc_not_to_src {V : Type} (G : SimpleGraph V) (A B : Set V) (x : Node V) :
    ¬ arc G A B x .src := by
  cases x <;> simp [arc]

private lemma arc_not_from_snk {V : Type} (G : SimpleGraph V) (A B : Set V) (y : Node V) :
    ¬ arc G A B .snk y := by
  cases y <;> simp [arc]

private lemma arc_asymm {V : Type} (G : SimpleGraph V) (A B : Set V) {x y : Node V}
    (h : arc G A B x y) : ¬ arc G A B y x := by
  cases x <;> cases y <;> simp [arc] at h ⊢
  · subst h; exact G.loopless.irrefl _
  · rintro rfl; exact G.loopless.irrefl _ h

private lemma arc_ne {V : Type} (G : SimpleGraph V) (A B : Set V) {x y : Node V}
    (h : arc G A B x y) : x ≠ y := by
  cases x <;> cases y <;> simp [arc] at h ⊢

private def indeg {U : Type} [DecidableEq U] (E : Finset (U × U)) (x : U) : ℕ :=
  (E.filter (fun e => e.2 = x)).card

private def outdeg {U : Type} [DecidableEq U] (E : Finset (U × U)) (x : U) : ℕ :=
  (E.filter (fun e => e.1 = x)).card

private def net {U : Type} [DecidableEq U] (E : Finset (U × U)) (x : U) : ℤ :=
  (outdeg E x : ℤ) - (indeg E x : ℤ)

private def IsFlow {V : Type} [DecidableEq V] (G : SimpleGraph V) (A B : Set V)
    (E : Finset (Node V × Node V)) : Prop :=
  (∀ e ∈ E, arc G A B e.1 e.2) ∧
  (∀ x : Node V, x ≠ .src → x ≠ .snk → indeg E x = outdeg E x)

private lemma isFlow_empty {V : Type} [DecidableEq V] (G : SimpleGraph V) (A B : Set V) :
    IsFlow G A B ∅ := by
  refine ⟨fun _ h => (Finset.notMem_empty _ h).elim, fun x _ _ => ?_⟩
  simp [indeg, outdeg]

private lemma indeg_src_eq_zero {V : Type} [DecidableEq V] {G : SimpleGraph V} {A B : Set V}
    {E : Finset (Node V × Node V)} (hE : ∀ e ∈ E, arc G A B e.1 e.2) :
    indeg E .src = 0 := by
  unfold indeg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he h2
  have ha := hE e he
  rw [h2] at ha
  exact arc_not_to_src G A B e.1 ha

private lemma outdeg_snk_eq_zero {V : Type} [DecidableEq V] {G : SimpleGraph V} {A B : Set V}
    {E : Finset (Node V × Node V)} (hE : ∀ e ∈ E, arc G A B e.1 e.2) :
    outdeg E .snk = 0 := by
  unfold outdeg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he h1
  have ha := hE e he
  rw [h1] at ha
  exact arc_not_from_snk G A B e.2 ha

private lemma outdeg_vin_le_one {V : Type} [DecidableEq V] {G : SimpleGraph V} {A B : Set V}
    {E : Finset (Node V × Node V)} (hE : ∀ e ∈ E, arc G A B e.1 e.2) (v : V) :
    outdeg E (.vin v) ≤ 1 := by
  have hsub : E.filter (fun e => e.1 = .vin v) ⊆ {(.vin v, .vout v)} := by
    intro e he
    rcases e with ⟨x, y⟩
    rcases Finset.mem_filter.mp he with ⟨he1, he2⟩
    dsimp only at he2
    subst he2
    rw [Finset.mem_singleton]
    have ha := hE _ he1
    cases y with
    | vout w =>
      simp only [arc] at ha
      subst ha; rfl
    | _ => simp [arc] at ha
  exact (Finset.card_le_card hsub).trans (by simp)

private lemma indeg_vout_le_one {V : Type} [DecidableEq V] {G : SimpleGraph V} {A B : Set V}
    {E : Finset (Node V × Node V)} (hE : ∀ e ∈ E, arc G A B e.1 e.2) (v : V) :
    indeg E (.vout v) ≤ 1 := by
  have hsub : E.filter (fun e => e.2 = .vout v) ⊆ {(.vin v, .vout v)} := by
    intro e he
    rcases e with ⟨x, y⟩
    rcases Finset.mem_filter.mp he with ⟨he1, he2⟩
    dsimp only at he2
    subst he2
    rw [Finset.mem_singleton]
    have ha := hE _ he1
    cases x with
    | vin u =>
      simp only [arc] at ha
      subst ha; rfl
    | _ => simp [arc] at ha
  exact (Finset.card_le_card hsub).trans (by simp)

private lemma indeg_vin_le_one {V : Type} [DecidableEq V] {G : SimpleGraph V} {A B : Set V}
    {E : Finset (Node V × Node V)} (hE : IsFlow G A B E) (v : V) :
    indeg E (.vin v) ≤ 1 := by
  rw [hE.2 (.vin v) (by simp) (by simp)]
  exact outdeg_vin_le_one hE.1 v

private lemma outdeg_vout_le_one {V : Type} [DecidableEq V] {G : SimpleGraph V} {A B : Set V}
    {E : Finset (Node V × Node V)} (hE : IsFlow G A B E) (v : V) :
    outdeg E (.vout v) ≤ 1 := by
  rw [← hE.2 (.vout v) (by simp) (by simp)]
  exact indeg_vout_le_one hE.1 v

/- ### Part 1: Residual graph and augmenting-path toggle -/

private def res {V : Type} [DecidableEq V] (G : SimpleGraph V) (A B : Set V)
    (E : Finset (Node V × Node V)) (x y : Node V) : Prop :=
  (arc G A B x y ∧ (x, y) ∉ E) ∨ (arc G A B y x ∧ (y, x) ∈ E)

private def IsResPath {V : Type} [DecidableEq V] (G : SimpleGraph V) (A B : Set V)
    (E : Finset (Node V × Node V)) : List (Node V) → Prop
  | [] => False
  | [_] => True
  | x :: y :: rest => res G A B E x y ∧ IsResPath G A B E (y :: rest)

private lemma isResPath_suffix {V : Type} [DecidableEq V] {G : SimpleGraph V} {A B : Set V}
    {E : Finset (Node V × Node V)} :
    ∀ {L₁ L₂ : List (Node V)}, L₂ ≠ [] → IsResPath G A B E (L₁ ++ L₂) → IsResPath G A B E L₂
  | [], _, _, h => h
  | [_], L₂, hne, h => by
    cases L₂ with
    | nil => exact (hne rfl).elim
    | cons y rest => exact h.2
  | _ :: y :: t, L₂, hne, h =>
    isResPath_suffix (L₁ := y :: t) hne h.2

private lemma exists_resPath_of_reflTransGen {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {A B : Set V} {E : Finset (Node V × Node V)} {u w : Node V}
    (h : Relation.ReflTransGen (res G A B E) u w) :
    ∃ L : List (Node V), IsResPath G A B E L ∧ L.head? = some u ∧ L.getLast? = some w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[w], trivial, rfl, rfl⟩
  | @head a b hab _ ih =>
    obtain ⟨L, hL, hhead, hlast⟩ := ih
    cases L with
    | nil => simp at hhead
    | cons x rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      exact ⟨a :: x :: rest, ⟨hab, hL⟩, rfl, by simpa using hlast⟩

private lemma exists_nodup_resPath {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {A B : Set V} {E : Finset (Node V × Node V)} :
    ∀ (n : ℕ) (L : List (Node V)), L.length ≤ n → IsResPath G A B E L →
      ∃ L' : List (Node V), L'.Nodup ∧ IsResPath G A B E L' ∧
        L'.head? = L.head? ∧ L'.getLast? = L.getLast? ∧ ∀ z ∈ L', z ∈ L
  | 0, L, hlen, hL => by
    cases L with
    | nil => exact hL.elim
    | cons _ _ => simp at hlen
  | n + 1, L, hlen, hL => by
    cases L with
    | nil => exact hL.elim
    | cons x rest =>
      cases rest with
      | nil => exact ⟨[x], List.nodup_singleton x, trivial, rfl, rfl, fun _ h => h⟩
      | cons y tail =>
        by_cases hx : x ∈ y :: tail
        · obtain ⟨p₁, p₂, hp⟩ := List.append_of_mem hx
          have hsub : IsResPath G A B E (x :: p₂) := by
            have h1 : IsResPath G A B E (p₁ ++ x :: p₂) := hp ▸ hL.2
            exact isResPath_suffix (List.cons_ne_nil x p₂) h1
          have hlen' : (x :: p₂).length ≤ n := by
            have := congrArg List.length hp
            simp only [List.length_cons, List.length_append] at this hlen ⊢
            omega
          obtain ⟨L', hnd, hres, hhd, hlt, hmem⟩ := exists_nodup_resPath n (x :: p₂) hlen' hsub
          refine ⟨L', hnd, hres, by simpa using hhd, ?_, ?_⟩
          · rw [hlt]
            have hlast1 : (x :: y :: tail).getLast? = (y :: tail).getLast? := by simp
            rw [hlast1, hp, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil x p₂)]
          · intro z hz
            have hz' := hmem z hz
            exact List.mem_cons_of_mem x (hp ▸ List.mem_append_right p₁ hz')
        · have hlen' : (y :: tail).length ≤ n := by simp at hlen ⊢; omega
          obtain ⟨L', hnd, hres, hhd, hlt, hmem⟩ := exists_nodup_resPath n (y :: tail) hlen' hL.2
          cases L' with
          | nil => simp at hhd
          | cons y' rest' =>
            simp only [List.head?_cons, Option.some.injEq] at hhd
            subst hhd
            have hx' : x ∉ y' :: rest' := fun h => hx (hmem x h)
            refine ⟨x :: y' :: rest', List.nodup_cons.mpr ⟨hx', hnd⟩, ⟨hL.1, hres⟩, rfl, ?_, ?_⟩
            · simpa using hlt
            · intro z hz
              rcases List.mem_cons.mp hz with rfl | hz'
              · exact List.mem_cons_self ..
              · exact List.mem_cons_of_mem x (hmem z hz')

private noncomputable def toggleEdge {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (A B : Set V) (E : Finset (Node V × Node V))
    (x y : Node V) : Finset (Node V × Node V) :=
  by classical exact if arc G A B x y then insert (x, y) E else E.erase (y, x)

private noncomputable def togglePath {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (A B : Set V) (E : Finset (Node V × Node V)) :
    List (Node V) → Finset (Node V × Node V)
  | [] => E
  | [_] => E
  | x :: y :: rest => togglePath G A B (toggleEdge G A B E x y) (y :: rest)

private lemma outdeg_insert_of_notMem {U : Type} [DecidableEq U] (E : Finset (U × U))
    {x y : U} (hnot : (x, y) ∉ E) (z : U) :
    outdeg (insert (x, y) E) z = outdeg E z + if z = x then 1 else 0 := by
  unfold outdeg
  rw [Finset.filter_insert]
  by_cases hzx : z = x
  · subst hzx
    simp only [ite_true]
    rw [Finset.card_insert_of_notMem (by simp [hnot])]
  · have hne : x ≠ z := Ne.symm hzx
    simp [hzx, hne]

private lemma indeg_insert_of_notMem {U : Type} [DecidableEq U] (E : Finset (U × U))
    {x y : U} (hnot : (x, y) ∉ E) (z : U) :
    indeg (insert (x, y) E) z = indeg E z + if z = y then 1 else 0 := by
  unfold indeg
  rw [Finset.filter_insert]
  by_cases hzy : z = y
  · subst hzy
    simp only [ite_true]
    rw [Finset.card_insert_of_notMem (by simp [hnot])]
  · have hne : y ≠ z := Ne.symm hzy
    simp [hzy, hne]

private lemma outdeg_erase_of_mem {U : Type} [DecidableEq U] (E : Finset (U × U))
    {x y : U} (hmem : (x, y) ∈ E) (z : U) :
    (outdeg (E.erase (x, y)) z : ℤ) = (outdeg E z : ℤ) - if z = x then 1 else 0 := by
  unfold outdeg
  rw [Finset.filter_erase]
  by_cases hzx : z = x
  · subst hzx
    simp only [ite_true]
    have hm : (z, y) ∈ E.filter (fun e => e.1 = z) := Finset.mem_filter.mpr ⟨hmem, rfl⟩
    have hcard := Finset.card_erase_add_one hm
    omega
  · have hnot : (x, y) ∉ E.filter (fun e => e.1 = z) := by simp [Ne.symm hzx]
    rw [Finset.erase_eq_of_notMem hnot]
    simp [hzx]

private lemma indeg_erase_of_mem {U : Type} [DecidableEq U] (E : Finset (U × U))
    {x y : U} (hmem : (x, y) ∈ E) (z : U) :
    (indeg (E.erase (x, y)) z : ℤ) = (indeg E z : ℤ) - if z = y then 1 else 0 := by
  unfold indeg
  rw [Finset.filter_erase]
  by_cases hzy : z = y
  · subst hzy
    simp only [ite_true]
    have hm : (x, z) ∈ E.filter (fun e => e.2 = z) := Finset.mem_filter.mpr ⟨hmem, rfl⟩
    have hcard := Finset.card_erase_add_one hm
    omega
  · have hnot : (x, y) ∉ E.filter (fun e => e.2 = z) := by simp [Ne.symm hzy]
    rw [Finset.erase_eq_of_notMem hnot]
    simp [hzy]

private lemma toggleEdge_spec {V : Type} [DecidableEq V] {G : SimpleGraph V} {A B : Set V}
    {E : Finset (Node V × Node V)} (hE : ∀ e ∈ E, arc G A B e.1 e.2)
    {x y : Node V} (hres : res G A B E x y) :
    (∀ e ∈ toggleEdge G A B E x y, arc G A B e.1 e.2) ∧
    (∀ z : Node V, net (toggleEdge G A B E x y) z =
      net E z + (if z = x then 1 else 0) - (if z = y then 1 else 0)) ∧
    (∀ u v : Node V, u ≠ x → v ≠ x →
      (res G A B (toggleEdge G A B E x y) u v ↔ res G A B E u v)) := by
  classical
  unfold toggleEdge
  rcases hres with ⟨hxy, hnot⟩ | ⟨hyx, hmem⟩
  · rw [if_pos hxy]
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      rcases Finset.mem_insert.mp he with rfl | he'
      · exact hxy
      · exact hE e he'
    · intro z
      unfold net
      rw [outdeg_insert_of_notMem E hnot z, indeg_insert_of_notMem E hnot z]
      push_cast; ring
    · intro u v hu hv
      have h1 : (u, v) ≠ (x, y) := fun h => hu (congrArg Prod.fst h)
      have h2 : (v, u) ≠ (x, y) := fun h => hv (congrArg Prod.fst h)
      simp [res, h1, h2]
  · have hnot_xy : ¬ arc G A B x y := fun h => arc_asymm G A B hyx h
    rw [if_neg hnot_xy]
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      exact hE e (Finset.mem_of_mem_erase he)
    · intro z
      unfold net
      rw [outdeg_erase_of_mem E hmem z, indeg_erase_of_mem E hmem z]
      ring
    · intro u v hu hv
      have h1 : (u, v) ≠ (y, x) := fun h => hv (congrArg Prod.snd h)
      have h2 : (v, u) ≠ (y, x) := fun h => hu (congrArg Prod.snd h)
      simp [res, h1, h2]

private lemma isResPath_congr_of_nodup {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {A B : Set V} {E₁ E₂ : Finset (Node V × Node V)} :
    ∀ {L : List (Node V)},
      (∀ u ∈ L, ∀ v ∈ L, res G A B E₁ u v ↔ res G A B E₂ u v) →
      IsResPath G A B E₁ L → IsResPath G A B E₂ L
  | [], _, h => h
  | [_], _, _ => trivial
  | a :: b :: _rest, hiff, ⟨hab, hrest⟩ =>
    ⟨(hiff a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ (List.mem_cons_self ..))).mp hab,
     isResPath_congr_of_nodup
       (fun u hu v hv => hiff u (List.mem_cons_of_mem _ hu) v (List.mem_cons_of_mem _ hv)) hrest⟩

private lemma togglePath_spec {V : Type} [DecidableEq V] {G : SimpleGraph V} {A B : Set V} :
    ∀ (L : List (Node V)) (E : Finset (Node V × Node V)) (u w : Node V),
      (∀ e ∈ E, arc G A B e.1 e.2) →
      L.Nodup → IsResPath G A B E L → L.head? = some u → L.getLast? = some w →
      (∀ e ∈ togglePath G A B E L, arc G A B e.1 e.2) ∧
      (∀ z : Node V, net (togglePath G A B E L) z =
        net E z + (if z = u then 1 else 0) - (if z = w then 1 else 0))
  | [], _, _, _, _, _, hL, _, _ => hL.elim
  | [a], E, u, w, hE, _, _, hhd, hlt => by
    simp only [List.head?_cons, Option.some.injEq] at hhd
    simp only [List.getLast?_singleton, Option.some.injEq] at hlt
    subst hhd; subst hlt
    refine ⟨hE, fun z => by simp [togglePath]⟩
  | x :: y :: rest, E, u, w, hE, hnd, hres, hhd, hlt => by
    simp only [List.head?_cons, Option.some.injEq] at hhd
    subst hhd
    have hlt' : (y :: rest).getLast? = some w := by simpa using hlt
    have ⟨hx_not, hnd'⟩ := List.nodup_cons.mp hnd
    have ⟨hE₁_arc, hE₁_net, hE₁_res⟩ := toggleEdge_spec hE hres.1
    have hres₁ : IsResPath G A B (toggleEdge G A B E x y) (y :: rest) :=
      isResPath_congr_of_nodup
        (fun a ha b hb => (hE₁_res a b (fun h : a = x => hx_not (h ▸ ha))
          (fun h : b = x => hx_not (h ▸ hb))).symm)
        hres.2
    have ⟨hE'_arc, hE'_net⟩ :=
      togglePath_spec (y :: rest) (toggleEdge G A B E x y) y w hE₁_arc hnd' hres₁ rfl hlt'
    refine ⟨hE'_arc, fun z => ?_⟩
    change net (togglePath G A B (toggleEdge G A B E x y) (y :: rest)) z = _
    rw [hE'_net z, hE₁_net z]
    ring

private lemma augment_flow {V : Type} [DecidableEq V] {G : SimpleGraph V} {A B : Set V}
    {E : Finset (Node V × Node V)} (hE : IsFlow G A B E)
    (hreach : Relation.ReflTransGen (res G A B E) .src .snk) :
    ∃ E' : Finset (Node V × Node V), IsFlow G A B E' ∧ outdeg E' .src = outdeg E .src + 1 := by
  obtain ⟨L, hL, hhd, hlt⟩ := exists_resPath_of_reflTransGen hreach
  obtain ⟨L', hnd, hres, hhd', hlt', _⟩ := exists_nodup_resPath L.length L le_rfl hL
  rw [hhd] at hhd'
  rw [hlt] at hlt'
  have ⟨harc', hnet'⟩ := togglePath_spec L' E .src .snk hE.1 hnd hres hhd' hlt'
  refine ⟨togglePath G A B E L', ⟨harc', ?_⟩, ?_⟩
  · intro x hx1 hx2
    have h1 := hnet' x
    simp only [hx1, hx2, ite_false, add_zero, sub_zero] at h1
    have h0 : net E x = 0 := by unfold net; rw [hE.2 x hx1 hx2]; ring
    rw [h0] at h1
    unfold net at h1
    omega
  · have h1 := hnet' .src
    have hne : (Node.src : Node V) ≠ .snk := by simp
    simp only [ite_true, hne, ite_false, sub_zero] at h1
    unfold net at h1
    rw [indeg_src_eq_zero hE.1, indeg_src_eq_zero harc'] at h1
    omega

/- ### Part 2: Min-cut equality and vertex hitting set -/

private lemma sum_outdeg_eq {U : Type} [DecidableEq U] (E : Finset (U × U)) (R : Finset U) :
    ∑ x ∈ R, (outdeg E x : ℤ) = ∑ e ∈ E, if e.1 ∈ R then (1 : ℤ) else 0 := by
  have h1 : ∀ x ∈ R, (outdeg E x : ℤ) = ∑ e ∈ E, if e.1 = x then (1 : ℤ) else 0 := by
    intro x _
    unfold outdeg
    rw [Finset.card_filter]
    simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hm : e.1 ∈ R
  · rw [if_pos hm, Finset.sum_eq_single e.1]
    · simp
    · intro x _ hne; simp [Ne.symm hne]
    · intro h; exact (h hm).elim
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro x hx
    have hne : e.1 ≠ x := fun h => hm (h ▸ hx)
    simp [hne]

private lemma sum_indeg_eq {U : Type} [DecidableEq U] (E : Finset (U × U)) (R : Finset U) :
    ∑ x ∈ R, (indeg E x : ℤ) = ∑ e ∈ E, if e.2 ∈ R then (1 : ℤ) else 0 := by
  have h1 : ∀ x ∈ R, (indeg E x : ℤ) = ∑ e ∈ E, if e.2 = x then (1 : ℤ) else 0 := by
    intro x _
    unfold indeg
    rw [Finset.card_filter]
    simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hm : e.2 ∈ R
  · rw [if_pos hm, Finset.sum_eq_single e.2]
    · simp
    · intro x _ hne; simp [Ne.symm hne]
    · intro h; exact (h hm).elim
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro x hx
    have hne : e.2 ≠ x := fun h => hm (h ▸ hx)
    simp [hne]

private def edgeVert {V : Type} : Node V × Node V → Finset V
  | (.src, .vin a) => {a}
  | (.vin v, .vout _) => {v}
  | (.vout u, .vin _) => {u}
  | (.vout b, .snk) => {b}
  | _ => ∅

private lemma edgeVert_card_le_one {V : Type} (e : Node V × Node V) :
    (edgeVert e).card ≤ 1 := by
  rcases e with ⟨x, y⟩
  cases x <;> cases y <;> simp [edgeVert]

private lemma cut_from_unreach {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A B : Set V}
    {E : Finset (Node V × Node V)} (hE : IsFlow G A B E)
    (hunreach : ¬ Relation.ReflTransGen (res G A B E) .src .snk) :
    ∃ C : Finset V, C.card ≤ outdeg E .src ∧
      ∀ a ∈ A, ∀ b ∈ B, ∀ p : G.Walk a b, ∃ v ∈ C, v ∈ p.support := by
  classical
  let : Fintype (Node V) := Fintype.ofEquiv _ (nodeEquiv V)
  let R : Finset (Node V) := Finset.univ.filter (fun x => Relation.ReflTransGen (res G A B E) .src x)
  have hsrcR : (Node.src : Node V) ∈ R := by
    simp [R, Relation.ReflTransGen.refl]
  have hsnkR : (Node.snk : Node V) ∉ R := by
    simp [R, hunreach]
  have hclosed_arc : ∀ x y : Node V, arc G A B x y → x ∈ R → y ∉ R → (x, y) ∈ E := by
    intro x y ha hxR hyR
    by_contra hnot
    have hrx : Relation.ReflTransGen (res G A B E) .src x := (Finset.mem_filter.mp hxR).2
    have hry : Relation.ReflTransGen (res G A B E) .src y :=
      hrx.tail (Or.inl ⟨ha, hnot⟩)
    exact hyR (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hry⟩)
  have hback_E : ∀ e ∈ E, e.2 ∈ R → e.1 ∈ R := by
    intro e he h2
    have hr2 : Relation.ReflTransGen (res G A B E) .src e.2 := (Finset.mem_filter.mp h2).2
    have hr1 : Relation.ReflTransGen (res G A B E) .src e.1 :=
      hr2.tail (Or.inr ⟨hE.1 e he, he⟩)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr1⟩
  let K : Finset (Node V × Node V) := E.filter (fun e => e.1 ∈ R ∧ e.2 ∉ R)
  have hK_card : K.card = outdeg E .src := by
    have hLHS : ∑ x ∈ R, net E x = (outdeg E .src : ℤ) := by
      rw [Finset.sum_eq_single .src]
      · unfold net; rw [indeg_src_eq_zero hE.1]; simp
      · intro x hxR hxsrc
        have hxsnk : x ≠ .snk := fun h => hsnkR (h ▸ hxR)
        unfold net; rw [hE.2 x hxsrc hxsnk]; ring
      · intro h; exact (h hsrcR).elim
    have hRHS : ∑ x ∈ R, net E x = (K.card : ℤ) := by
      calc ∑ x ∈ R, net E x
          = ∑ x ∈ R, (outdeg E x : ℤ) - ∑ x ∈ R, (indeg E x : ℤ) := by
              simp only [net, Finset.sum_sub_distrib]
        _ = (∑ e ∈ E, if e.1 ∈ R then (1 : ℤ) else 0) -
              (∑ e ∈ E, if e.2 ∈ R then (1 : ℤ) else 0) := by
              rw [sum_outdeg_eq, sum_indeg_eq]
        _ = ∑ e ∈ E, ((if e.1 ∈ R then (1 : ℤ) else 0) - (if e.2 ∈ R then (1 : ℤ) else 0)) := by
              rw [Finset.sum_sub_distrib]
        _ = ∑ e ∈ E, if e.1 ∈ R ∧ e.2 ∉ R then (1 : ℤ) else 0 := by
              apply Finset.sum_congr rfl
              intro e he
              by_cases h1 : e.1 ∈ R <;> by_cases h2 : e.2 ∈ R
              · simp [h1, h2]
              · simp [h1, h2]
              · exact (h1 (hback_E e he h2)).elim
              · simp [h1, h2]
        _ = (K.card : ℤ) := by
              unfold K
              rw [Finset.card_filter]
              simp
    omega
  let C : Finset V := K.biUnion edgeVert
  have hC_card : C.card ≤ outdeg E .src := by
    calc C.card ≤ ∑ e ∈ K, (edgeVert e).card := Finset.card_biUnion_le
      _ ≤ ∑ _e ∈ K, 1 := Finset.sum_le_sum (fun e _ => edgeVert_card_le_one e)
      _ = K.card := by simp
      _ = outdeg E .src := hK_card
  refine ⟨C, hC_card, ?_⟩
  have hwalk : ∀ {a b : V} (p : G.Walk a b), b ∈ B → Node.vin a ∈ R →
      ∃ v ∈ C, v ∈ p.support := by
    intro a b p hb
    induction p with
    | @nil u =>
      intro hu_in
      by_cases hu_out : Node.vout u ∈ R
      · have he : (Node.vout u, Node.snk) ∈ K :=
          Finset.mem_filter.mpr ⟨hclosed_arc _ _ hb hu_out hsnkR, hu_out, hsnkR⟩
        exact ⟨u, Finset.mem_biUnion.mpr ⟨_, he, by simp [edgeVert]⟩, by simp⟩
      · have he : (Node.vin u, Node.vout u) ∈ K :=
          Finset.mem_filter.mpr ⟨hclosed_arc _ _ rfl hu_in hu_out, hu_in, hu_out⟩
        exact ⟨u, Finset.mem_biUnion.mpr ⟨_, he, by simp [edgeVert]⟩, by simp⟩
    | @cons u c b hadj q ih =>
      intro hu_in
      by_cases hu_out : Node.vout u ∈ R
      · by_cases hc_in : Node.vin c ∈ R
        · obtain ⟨v, hvC, hvq⟩ := ih hb hc_in
          exact ⟨v, hvC, List.mem_cons_of_mem u hvq⟩
        · have he : (Node.vout u, Node.vin c) ∈ K :=
            Finset.mem_filter.mpr ⟨hclosed_arc _ _ hadj hu_out hc_in, hu_out, hc_in⟩
          exact ⟨u, Finset.mem_biUnion.mpr ⟨_, he, by simp [edgeVert]⟩, by simp⟩
      · have he : (Node.vin u, Node.vout u) ∈ K :=
          Finset.mem_filter.mpr ⟨hclosed_arc _ _ rfl hu_in hu_out, hu_in, hu_out⟩
        exact ⟨u, Finset.mem_biUnion.mpr ⟨_, he, by simp [edgeVert]⟩, by simp⟩
  intro a ha b hb p
  by_cases ha_in : Node.vin a ∈ R
  · exact hwalk p hb ha_in
  · have he : (Node.src, Node.vin a) ∈ K :=
      Finset.mem_filter.mpr ⟨hclosed_arc _ _ ha hsrcR ha_in, hsrcR, ha_in⟩
    exact ⟨a, Finset.mem_biUnion.mpr ⟨_, he, by simp [edgeVert]⟩, p.start_mem_support⟩

/- ### Part 3: Flow decomposition into vertex-disjoint A-B paths -/

private def IsFlowChain {V : Type} [DecidableEq V] (G : SimpleGraph V) (A B : Set V)
    (E : Finset (Node V × Node V)) : List V → Prop
  | [] => False
  | [v] => (Node.vin v, Node.vout v) ∈ E
  | u :: v :: rest =>
      (Node.vin u, Node.vout u) ∈ E ∧ (Node.vout u, Node.vin v) ∈ E ∧
      IsFlowChain G A B E (v :: rest)

private lemma isFlowChain_mem_vin_vout {V : Type} [DecidableEq V] {G : SimpleGraph V}
    {A B : Set V} {E : Finset (Node V × Node V)} :
    ∀ {L : List V}, IsFlowChain G A B E L → ∀ v ∈ L, (Node.vin v, Node.vout v) ∈ E
  | [], h => h.elim
  | [a], h => fun v hv => by rw [List.mem_singleton.mp hv]; exact h
  | u :: v :: rest, ⟨h1, _, hrest⟩ => fun w hw => by
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact h1
    · exact isFlowChain_mem_vin_vout hrest w hw'

private lemma isFlowChain_append_one {V : Type} [DecidableEq V] {G : SimpleGraph V}
    {A B : Set V} {E : Finset (Node V × Node V)} :
    ∀ {L : List V} {u w : V},
      IsFlowChain G A B E L → L.getLast? = some u →
      (Node.vout u, Node.vin w) ∈ E → (Node.vin w, Node.vout w) ∈ E →
      IsFlowChain G A B E (L ++ [w])
  | [], _, _, h, _, _, _ => h.elim
  | [a], u, w, h, hlt, huv, hww => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hlt
    subst hlt
    exact ⟨h, huv, hww⟩
  | a :: b :: rest, u, w, ⟨h1, h2, hrest⟩, hlt, huv, hww => by
    have hlt' : (b :: rest).getLast? = some u := by simpa using hlt
    exact ⟨h1, h2, isFlowChain_append_one hrest hlt' huv hww⟩

private lemma isFlowChain_prev_mem {V : Type} [DecidableEq V] {G : SimpleGraph V}
    {A B : Set V} {E : Finset (Node V × Node V)} :
    ∀ {L : List V} {x : V},
      IsFlowChain G A B E L → x ∈ L → L.head? ≠ some x →
      ∃ u ∈ L, u ≠ x ∧ (Node.vout u, Node.vin x) ∈ E ∧
        (L.Nodup → L.getLast? = some u → False)
  | [], _, h, _, _ => h.elim
  | [a], x, _, hx, hhd => by
    have hxa : x = a := List.mem_singleton.mp hx
    subst hxa; exact (hhd rfl).elim
  | a :: b :: rest, x, ⟨_, hab, hrest⟩, hx, hhd => by
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact (hhd rfl).elim
    · by_cases hxb : x = b
      · subst hxb
        refine ⟨a, List.mem_cons_self .., ?_, hab, ?_⟩
        · intro heq
          -- Wait: if a = x, then hhd already ruled out some x = some a!
          exact hhd (by simp [heq])
        · intro hnd hlast
          have hlast' : (x :: rest).getLast? = some a := by simpa using hlast
          have ha_mem : a ∈ x :: rest := List.mem_of_getLast? hlast'
          exact (List.nodup_cons.mp hnd).1 ha_mem
      · have hhd' : (b :: rest).head? ≠ some x := by simp [Ne.symm hxb]
        obtain ⟨u, huL, hux, huv, hnotlast⟩ := isFlowChain_prev_mem hrest hx' hhd'
        refine ⟨u, List.mem_cons_of_mem a huL, hux, huv, ?_⟩
        intro hnd hlast
        have hlast' : (b :: rest).getLast? = some u := by simpa using hlast
        exact hnotlast (List.nodup_cons.mp hnd).2 hlast'

private lemma chain_to_walk {V : Type} [DecidableEq V] {G : SimpleGraph V} {A B : Set V}
    {E : Finset (Node V × Node V)} (hE : ∀ e ∈ E, arc G A B e.1 e.2) :
    ∀ {L : List V} {a b : V},
      IsFlowChain G A B E L → L.head? = some a → L.getLast? = some b →
      ∃ p : G.Walk a b, p.support = L
  | [], _, _, h, _, _ => h.elim
  | [u], a, b, _, hhd, hlt => by
    simp only [List.head?_cons, Option.some.injEq] at hhd
    simp only [List.getLast?_singleton, Option.some.injEq] at hlt
    subst hhd; subst hlt
    exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | u :: v :: rest, a, b, ⟨_, huv, hrest⟩, hhd, hlt => by
    simp only [List.head?_cons, Option.some.injEq] at hhd
    subst hhd
    have hlt' : (v :: rest).getLast? = some b := by simpa using hlt
    obtain ⟨q, hq⟩ := chain_to_walk hE hrest rfl hlt'
    have hadj : G.Adj u v := hE _ huv
    exact ⟨SimpleGraph.Walk.cons hadj q, by simp [hq]⟩

private def chainEdges {V : Type} [DecidableEq V] : List V → Finset (Node V × Node V)
  | [] => ∅
  | [v] => {(Node.vin v, Node.vout v)}
  | u :: v :: rest =>
      insert (Node.vin u, Node.vout u) (insert (Node.vout u, Node.vin v) (chainEdges (v :: rest)))

private lemma mem_chainEdges_of_mem {V : Type} [DecidableEq V] :
    ∀ {L : List V} {v : V}, v ∈ L → (Node.vin v, Node.vout v) ∈ chainEdges L
  | [], _, hv => by simp at hv
  | [x], v, hv => by
    simp only [List.mem_singleton] at hv
    subst hv; simp [chainEdges]
  | x :: y :: tail, v, hv => by
    rcases List.mem_cons.mp hv with rfl | hv'
    · simp [chainEdges]
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (mem_chainEdges_of_mem hv'))

private lemma chainEdges_subset {V : Type} [DecidableEq V] {G : SimpleGraph V} {A B : Set V}
    {E : Finset (Node V × Node V)} :
    ∀ {L : List V}, IsFlowChain G A B E L → chainEdges L ⊆ E
  | [], h => h.elim
  | [v], h => by simpa [chainEdges, IsFlowChain] using h
  | u :: v :: rest, ⟨h1, h2, hrest⟩ => by
    intro e he
    simp only [chainEdges, Finset.mem_insert] at he
    rcases he with rfl | rfl | he'
    · exact h1
    · exact h2
    · exact chainEdges_subset hrest he'

private lemma chainEdges_node_mem {V : Type} [DecidableEq V] :
    ∀ {L : List V} {e : Node V × Node V}, e ∈ chainEdges L →
      (∃ u ∈ L, e.1 = Node.vin u ∨ e.1 = Node.vout u) ∧
      (∃ v ∈ L, e.2 = Node.vin v ∨ e.2 = Node.vout v)
  | [], _, h => (Finset.notMem_empty _ h).elim
  | [a], e, h => by
    simp only [chainEdges, Finset.mem_singleton] at h
    subst h
    exact ⟨⟨a, List.mem_cons_self .., Or.inl rfl⟩, ⟨a, List.mem_cons_self .., Or.inr rfl⟩⟩
  | u :: v :: rest, e, h => by
    simp only [chainEdges, Finset.mem_insert] at h
    rcases h with rfl | rfl | h'
    · exact ⟨⟨u, List.mem_cons_self .., Or.inl rfl⟩, ⟨u, List.mem_cons_self .., Or.inr rfl⟩⟩
    · exact ⟨⟨u, List.mem_cons_self .., Or.inr rfl⟩,
             ⟨v, List.mem_cons_of_mem u (List.mem_cons_self ..), Or.inl rfl⟩⟩
    · obtain ⟨⟨a, ha, hae⟩, ⟨b, hb, hbe⟩⟩ := chainEdges_node_mem h'
      exact ⟨⟨a, List.mem_cons_of_mem u ha, hae⟩, ⟨b, List.mem_cons_of_mem u hb, hbe⟩⟩

private lemma chainEdges_deg {V : Type} [DecidableEq V] :
    ∀ {L : List V} {a b : V}, L.Nodup → L.head? = some a → L.getLast? = some b →
      ∀ x : Node V,
        outdeg (chainEdges L) x = (if ∃ v ∈ L, x = Node.vin v then 1 else 0) +
          (if ∃ v ∈ L, x = Node.vout v ∧ v ≠ b then 1 else 0) ∧
        indeg (chainEdges L) x = (if ∃ v ∈ L, x = Node.vout v then 1 else 0) +
          (if ∃ v ∈ L, x = Node.vin v ∧ v ≠ a then 1 else 0)
  | [], _, _, _, hhd, _ => by simp at hhd
  | [u], a, b, _, hhd, hlt => by
    simp only [List.head?_cons, Option.some.injEq] at hhd
    simp only [List.getLast?_singleton, Option.some.injEq] at hlt
    subst hhd; subst hlt
    intro x
    cases x with
    | vin w =>
      by_cases hw : w = u
      · subst hw; simp [chainEdges, outdeg, indeg, Finset.filter_singleton]
      · simp [chainEdges, outdeg, indeg, Finset.filter_singleton, hw, Ne.symm hw]
    | vout w =>
      by_cases hw : w = u
      · subst hw; simp [chainEdges, outdeg, indeg, Finset.filter_singleton]
      · simp [chainEdges, outdeg, indeg, Finset.filter_singleton, hw, Ne.symm hw]
    | _ => simp [chainEdges, outdeg, indeg, Finset.filter_singleton]
  | u :: v :: rest, a, b, hnd, hhd, hlt => by
    simp only [List.head?_cons, Option.some.injEq] at hhd
    subst hhd
    have hlt' : (v :: rest).getLast? = some b := by simpa using hlt
    have ⟨hu_not, hnd'⟩ := List.nodup_cons.mp hnd
    have hub : u ≠ b := fun h => hu_not (h ▸ List.mem_of_getLast? hlt')
    have huv : u ≠ v := fun h => hu_not (h ▸ List.mem_cons_self ..)
    have hu_not_rest : u ∉ rest := fun h => hu_not (List.mem_cons_of_mem v h)
    have hnot1 : (Node.vout u, Node.vin v) ∉ chainEdges (v :: rest) := by
      intro hm
      obtain ⟨⟨w, hw, hw1⟩, _⟩ := chainEdges_node_mem hm
      rcases hw1 with h | h
      · simp at h
      · simp only [Node.vout.injEq] at h; exact hu_not (h ▸ hw)
    have hnot2 : (Node.vin u, Node.vout u) ∉ insert (Node.vout u, Node.vin v) (chainEdges (v :: rest)) := by
      intro hm
      rcases Finset.mem_insert.mp hm with h | h
      · simp at h
      · obtain ⟨⟨w, hw, hw1⟩, _⟩ := chainEdges_node_mem h
        rcases hw1 with h' | h'
        · simp only [Node.vin.injEq] at h'; exact hu_not (h' ▸ hw)
        · simp at h'
    have hih := chainEdges_deg hnd' rfl hlt'
    intro x
    have hce : chainEdges (u :: v :: rest) =
        insert (Node.vin u, Node.vout u) (insert (Node.vout u, Node.vin v) (chainEdges (v :: rest))) := rfl
    have hout : outdeg (chainEdges (u :: v :: rest)) x =
        outdeg (chainEdges (v :: rest)) x +
        (if x = Node.vout u then 1 else 0) + (if x = Node.vin u then 1 else 0) := by
      rw [hce, outdeg_insert_of_notMem _ hnot2, outdeg_insert_of_notMem _ hnot1]
    have hin : indeg (chainEdges (u :: v :: rest)) x =
        indeg (chainEdges (v :: rest)) x +
        (if x = Node.vin v then 1 else 0) + (if x = Node.vout u then 1 else 0) := by
      rw [hce, indeg_insert_of_notMem _ hnot2, indeg_insert_of_notMem _ hnot1]
    rw [hout, hin, (hih x).1, (hih x).2]
    cases x with
    | vin w =>
      by_cases hwu : w = u
      · subst hwu; simp [huv, hu_not_rest]
      · by_cases hwv : w = v
        · subst hwv; simp [Ne.symm huv]
        · simp [hwu, hwv]
    | vout w =>
      by_cases hwu : w = u
      · subst hwu; simp [huv, hu_not_rest, hub]
      · by_cases hwv : w = v
        · subst hwv
          by_cases hwb : w = b
          · subst hwb; simp [hwu]
          · simp [hwu, hwb]
        · simp [hwu, hwv]
    | _ => simp

private lemma outdeg_sdiff {U : Type} [DecidableEq U] {E P : Finset (U × U)}
    (hsub : P ⊆ E) (x : U) :
    outdeg (E \ P) x + outdeg P x = outdeg E x := by
  unfold outdeg
  have hEq : (E \ P).filter (fun e => e.1 = x) =
      E.filter (fun e => e.1 = x) \ P.filter (fun e => e.1 = x) := by
    ext e; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
  rw [hEq]
  exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset_filter _ hsub)

private lemma indeg_sdiff {U : Type} [DecidableEq U] {E P : Finset (U × U)}
    (hsub : P ⊆ E) (x : U) :
    indeg (E \ P) x + indeg P x = indeg E x := by
  unfold indeg
  have hEq : (E \ P).filter (fun e => e.2 = x) =
      E.filter (fun e => e.2 = x) \ P.filter (fun e => e.2 = x) := by
    ext e; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
  rw [hEq]
  exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset_filter _ hsub)

private lemma extract_path_from_flow {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A B : Set V}
    {E : Finset (Node V × Node V)} (hE : IsFlow G A B E) (hpos : 0 < outdeg E .src) :
    ∃ (a b : V) (p : G.Walk a b) (E' : Finset (Node V × Node V)),
      a ∈ A ∧ b ∈ B ∧ p.IsPath ∧
      IsFlow G A B E' ∧ E' ⊆ E ∧ outdeg E' .src + 1 = outdeg E .src ∧
      (∀ v ∈ p.support, (Node.vin v, Node.vout v) ∈ E ∧ (Node.vin v, Node.vout v) ∉ E') := by
  classical
  -- Pick a₀ ∈ A with (.src, .vin a₀) ∈ E
  have hne_src : (E.filter (fun e => e.1 = Node.src)).Nonempty :=
    Finset.card_pos.mp hpos
  obtain ⟨⟨x₀, y₀⟩, he₀⟩ := hne_src
  rcases Finset.mem_filter.mp he₀ with ⟨he₀1, he₀2⟩
  dsimp only at he₀2
  subst he₀2
  have ha₀_arc := hE.1 _ he₀1
  cases y₀ with
  | vin a₀ =>
    have ha₀A : a₀ ∈ A := ha₀_arc
    have hsrc_a₀ : (Node.src, Node.vin a₀) ∈ E := he₀1
    have ha₀_out_pos : 0 < outdeg E (.vin a₀) := by
      rw [← hE.2 (.vin a₀) (by simp) (by simp)]
      exact Finset.card_pos.mpr ⟨(Node.src, Node.vin a₀), Finset.mem_filter.mpr ⟨hsrc_a₀, rfl⟩⟩
    have ha₀_edge : (Node.vin a₀, Node.vout a₀) ∈ E := by
      obtain ⟨⟨x, y⟩, he⟩ := Finset.card_pos.mp ha₀_out_pos
      rcases Finset.mem_filter.mp he with ⟨he1, he2⟩
      dsimp only at he2
      subst he2
      have ha := hE.1 _ he1
      cases y with
      | vout w =>
        simp only [arc] at ha
        subst ha; exact he1
      | _ => simp [arc] at ha
    -- Pick a maximum-length Nodup flow chain starting at a₀
    let Good (k : ℕ) : Prop :=
      ∃ L : List V, L.length = k ∧ L.Nodup ∧ IsFlowChain G A B E L ∧ L.head? = some a₀
    have hgood1 : Good 1 := ⟨[a₀], rfl, List.nodup_singleton a₀, ha₀_edge, rfl⟩
    have hbound : ∀ k, Good k → k ≤ Fintype.card V := by
      rintro k ⟨L, rfl, hnd, _, _⟩
      exact hnd.length_le_card
    let S : Finset ℕ := (Finset.range (Fintype.card V + 1)).filter Good
    have h1S : 1 ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound 1 hgood1)), hgood1⟩
    obtain ⟨kmax, hkmax_mem, hkmax_ge⟩ := S.exists_max_image id ⟨1, h1S⟩
    obtain ⟨L, hLlen, hLnd, hLchain, hLhd⟩ := (Finset.mem_filter.mp hkmax_mem).2
    have hLne : L ≠ [] := by intro h; rw [h] at hLhd; simp at hLhd
    have ⟨b, hb_last⟩ : ∃ b, L.getLast? = some b := by
      have aux : ∀ l : List V, l ≠ [] → ∃ b, l.getLast? = some b := by
        intro l
        induction l with
        | nil => intro h; exact (h rfl).elim
        | cons x xs ih =>
          intro _
          cases xs with
          | nil => exact ⟨x, rfl⟩
          | cons y ys =>
            obtain ⟨b, hb⟩ := ih (List.cons_ne_nil y ys)
            exact ⟨b, by simpa using hb⟩
      exact aux L hLne
    have hb_mem : b ∈ L := List.mem_of_getLast? hb_last
    have hb_vv : (Node.vin b, Node.vout b) ∈ E := isFlowChain_mem_vin_vout hLchain b hb_mem
    have hb_out_pos : 0 < outdeg E (.vout b) := by
      rw [← hE.2 (.vout b) (by simp) (by simp)]
      exact Finset.card_pos.mpr ⟨(Node.vin b, Node.vout b), Finset.mem_filter.mpr ⟨hb_vv, rfl⟩⟩
    obtain ⟨⟨xb, yb⟩, heb⟩ := Finset.card_pos.mp hb_out_pos
    rcases Finset.mem_filter.mp heb with ⟨heb1, heb2⟩
    dsimp only at heb2
    subst heb2
    have heb_arc := hE.1 _ heb1
    -- yb must be .snk (cannot be .vin w since either w ∈ L contradicts indeg ≤ 1 or w ∉ L contradicts maximality)
    cases yb with
    | snk =>
      have hbB : b ∈ B := heb_arc
      have hb_snk : (Node.vout b, Node.snk) ∈ E := heb1
      obtain ⟨p, hp_supp⟩ := chain_to_walk hE.1 hLchain hLhd hb_last
      have hp_path : p.IsPath := (SimpleGraph.Walk.isPath_def p).mpr (hp_supp ▸ hLnd)
      let P : Finset (Node V × Node V) :=
        insert (Node.src, Node.vin a₀) (insert (Node.vout b, Node.snk) (chainEdges L))
      have hP_sub : P ⊆ E := by
        intro e he
        simp only [P, Finset.mem_insert] at he
        rcases he with rfl | rfl | he'
        · exact hsrc_a₀
        · exact hb_snk
        · exact chainEdges_subset hLchain he'
      have hnot_snk : (Node.vout b, Node.snk) ∉ chainEdges L := by
        intro hm
        obtain ⟨_, ⟨_, _, h2⟩⟩ := chainEdges_node_mem hm
        rcases h2 with h | h <;> simp at h
      have hnot_src : (Node.src, Node.vin a₀) ∉ insert (Node.vout b, Node.snk) (chainEdges L) := by
        intro hm
        rcases Finset.mem_insert.mp hm with h | h
        · simp at h
        · obtain ⟨⟨_, _, h1⟩, _⟩ := chainEdges_node_mem h
          rcases h1 with h' | h' <;> simp at h'
      have hP_deg : ∀ x : Node V,
          outdeg P x = (if x = Node.src then 1 else 0) +
            (if ∃ v ∈ L, x = Node.vin v then 1 else 0) +
            (if ∃ v ∈ L, x = Node.vout v then 1 else 0) ∧
          indeg P x = (if x = Node.snk then 1 else 0) +
            (if ∃ v ∈ L, x = Node.vin v then 1 else 0) +
            (if ∃ v ∈ L, x = Node.vout v then 1 else 0) := by
        intro x
        have hch := chainEdges_deg hLnd hLhd hb_last x
        have hout : outdeg P x = outdeg (chainEdges L) x +
            (if x = Node.vout b then 1 else 0) + (if x = Node.src then 1 else 0) := by
          unfold P
          rw [outdeg_insert_of_notMem _ hnot_src, outdeg_insert_of_notMem _ hnot_snk]
        have hin : indeg P x = indeg (chainEdges L) x +
            (if x = Node.snk then 1 else 0) + (if x = Node.vin a₀ then 1 else 0) := by
          unfold P
          rw [indeg_insert_of_notMem _ hnot_src, indeg_insert_of_notMem _ hnot_snk]
        rw [hout, hin, hch.1, hch.2]
        have ha₀_mem : a₀ ∈ L := List.mem_of_head? hLhd
        cases x with
        | src => simp
        | snk => simp
        | vin w =>
          by_cases hwa : w = a₀
          · subst hwa; simp [ha₀_mem]
          · simp [hwa]
        | vout w =>
          by_cases hwb : w = b
          · subst hwb; simp [hb_mem]
          · simp [hwb]
      let E' : Finset (Node V × Node V) := E \ P
      refine ⟨a₀, b, p, E', ha₀A, hbB, hp_path, ⟨?_, ?_⟩, Finset.sdiff_subset, ?_, ?_⟩
      · intro e he; exact hE.1 e (Finset.sdiff_subset he)
      · intro x hx1 hx2
        change indeg (E \ P) x = outdeg (E \ P) x
        have ho := outdeg_sdiff hP_sub x
        have hi := indeg_sdiff hP_sub x
        have hcons := hE.2 x hx1 hx2
        have hpd := hP_deg x
        simp only [hx1, hx2, ite_false, zero_add] at hpd
        omega
      · change outdeg (E \ P) .src + 1 = outdeg E .src
        have ho := outdeg_sdiff hP_sub .src
        have hps := (hP_deg .src).1
        simp only [ite_true] at hps
        have h0 : ¬ ∃ v ∈ L, (Node.src : Node V) = Node.vin v := by simp
        have h1 : ¬ ∃ v ∈ L, (Node.src : Node V) = Node.vout v := by simp
        simp only [h0, h1, ite_false, add_zero] at hps
        omega
      · intro v hv
        rw [hp_supp] at hv
        refine ⟨isFlowChain_mem_vin_vout hLchain v hv, ?_⟩
        intro hm
        have hmem_P : (Node.vin v, Node.vout v) ∈ P :=
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (mem_chainEdges_of_mem hv))
        exact (Finset.mem_sdiff.mp hm).2 hmem_P
    | vin w =>
      -- Contradiction: either w ∈ L (violates indeg ≤ 1) or w ∉ L (violates maximality of kmax)
      by_cases hwL : w ∈ L
      · by_cases hwa : w = a₀
        · subst hwa
          have h2 : 2 ≤ indeg E (.vin w) := by
            unfold indeg
            have hsub : {(Node.src, Node.vin w), (Node.vout b, Node.vin w)} ⊆
                E.filter (fun e => e.2 = Node.vin w) := by
              intro e he
              simp only [Finset.mem_insert, Finset.mem_singleton] at he
              rcases he with rfl | rfl
              · exact Finset.mem_filter.mpr ⟨hsrc_a₀, rfl⟩
              · exact Finset.mem_filter.mpr ⟨heb1, rfl⟩
            have hcard2 : ({(Node.src, Node.vin w), (Node.vout b, Node.vin w)} :
                Finset (Node V × Node V)).card = 2 := by
              rw [Finset.card_pair]; simp
            exact hcard2 ▸ Finset.card_le_card hsub
          have h1 := indeg_vin_le_one hE w
          omega
        · have hhd_ne : L.head? ≠ some w := by rw [hLhd]; simp [Ne.symm hwa]
          obtain ⟨u, _, _, huv, hnotlast⟩ := isFlowChain_prev_mem hLchain hwL hhd_ne
          have hub : u ≠ b := fun h => hnotlast hLnd (h ▸ hb_last)
          have h2 : 2 ≤ indeg E (.vin w) := by
            unfold indeg
            have hsub : {(Node.vout u, Node.vin w), (Node.vout b, Node.vin w)} ⊆
                E.filter (fun e => e.2 = Node.vin w) := by
              intro e he
              simp only [Finset.mem_insert, Finset.mem_singleton] at he
              rcases he with rfl | rfl
              · exact Finset.mem_filter.mpr ⟨huv, rfl⟩
              · exact Finset.mem_filter.mpr ⟨heb1, rfl⟩
            have hcard2 : ({(Node.vout u, Node.vin w), (Node.vout b, Node.vin w)} :
                Finset (Node V × Node V)).card = 2 := by
              rw [Finset.card_pair]; simp [hub]
            exact hcard2 ▸ Finset.card_le_card hsub
          have h1 := indeg_vin_le_one hE w
          omega
      · have hw_out_pos : 0 < outdeg E (.vin w) := by
          rw [← hE.2 (.vin w) (by simp) (by simp)]
          exact Finset.card_pos.mpr ⟨(Node.vout b, Node.vin w), Finset.mem_filter.mpr ⟨heb1, rfl⟩⟩
        have hw_edge : (Node.vin w, Node.vout w) ∈ E := by
          obtain ⟨⟨x, y⟩, he⟩ := Finset.card_pos.mp hw_out_pos
          rcases Finset.mem_filter.mp he with ⟨he1, he2⟩
          dsimp only at he2
          subst he2
          have ha := hE.1 _ he1
          cases y with
          | vout z => simp only [arc] at ha; subst ha; exact he1
          | _ => simp [arc] at ha
        have hgood_next : Good (kmax + 1) := by
          refine ⟨L ++ [w], by simp [hLlen], ?_,
            isFlowChain_append_one hLchain hb_last heb1 hw_edge, ?_⟩
          · rw [List.nodup_append]
            refine ⟨hLnd, List.nodup_singleton w, fun x hx y hy => ?_⟩
            rw [List.mem_singleton.mp hy]
            exact fun h => hwL (h ▸ hx)
          · cases L with
            | nil => exact (hLne rfl).elim
            | cons x rest => simpa using hLhd
        have hmem_S : kmax + 1 ∈ S := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound _ hgood_next)), hgood_next⟩
        have hle := hkmax_ge (kmax + 1) hmem_S
        simp only [id_eq] at hle
        omega
    | _ => simp [arc] at heb_arc
  | _ => simp [arc] at ha₀_arc

private lemma flow_decomp {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A B : Set V} :
    ∀ (k : ℕ) (E : Finset (Node V × Node V)),
      IsFlow G A B E → outdeg E .src = k →
      let paths : Set (Finset V) := {s | ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
        p.IsPath ∧ p.support.toFinset = s}
      ∃ F : Finset (Finset V),
        (↑F ⊆ paths) ∧
        (F : Set (Finset V)).Pairwise Disjoint ∧
        F.card = k ∧
        ∀ s ∈ F, ∀ v ∈ s, (Node.vin v, Node.vout v) ∈ E
  | 0, E, _, _ => ⟨∅, by simp, by simp, rfl, by simp⟩
  | k + 1, E, hE, hval => by
    obtain ⟨a, b, p, E', ha, hb, hp, hE', hsub, hval', hvv⟩ :=
      extract_path_from_flow hE (by omega)
    have hvalE' : outdeg E' .src = k := by omega
    obtain ⟨F', hF'_sub, hF'_disj, hF'_card, hF'_vv⟩ := flow_decomp k E' hE' hvalE'
    let s : Finset V := p.support.toFinset
    have hs_disj : ∀ t ∈ F', Disjoint s t := by
      intro t ht
      rw [Finset.disjoint_left]
      intro v hvs hvt
      have hv1 := (hvv v (List.mem_toFinset.mp hvs)).2
      have hv2 := hF'_vv t ht v hvt
      exact hv1 hv2
    have hs_notMem : s ∉ F' := by
      intro hmem
      have ha_s : a ∈ s := List.mem_toFinset.mpr p.start_mem_support
      exact (Finset.disjoint_left.mp (hs_disj s hmem) ha_s ha_s).elim
    refine ⟨insert s F', ?_, ?_, ?_, ?_⟩
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht'
      · exact ⟨a, ha, b, hb, p, hp, rfl⟩
      · exact hF'_sub ht'
    · rw [Finset.coe_insert, Set.pairwise_insert]
      exact ⟨hF'_disj, fun t ht _ => ⟨hs_disj t ht, (hs_disj t ht).symm⟩⟩
    · rw [Finset.card_insert_of_notMem hs_notMem, hF'_card]
    · intro t ht v hv
      rcases Finset.mem_insert.mp ht with rfl | ht'
      · exact (hvv v (List.mem_toFinset.mp hv)).1
      · exact hsub (hF'_vv t ht' v hv)

end Erdos599R2H2

theorem OMA.solution : OMA.R_Erdos599_erdos_599_R2.H2 := by
  classical
  intro V _ _ G A B paths
  let : Fintype (Erdos599R2H2.Node V) := Fintype.ofEquiv _ (Erdos599R2H2.nodeEquiv V)
  let Flows : Finset (Finset (Erdos599R2H2.Node V × Erdos599R2H2.Node V)) :=
    Finset.univ.filter (Erdos599R2H2.IsFlow G A B)
  have hne : Flows.Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Erdos599R2H2.isFlow_empty G A B⟩⟩
  obtain ⟨E, hE_mem, hE_max⟩ := Flows.exists_max_image (fun E => Erdos599R2H2.outdeg E .src) hne
  have hE : Erdos599R2H2.IsFlow G A B E := (Finset.mem_filter.mp hE_mem).2
  have hunreach : ¬ Relation.ReflTransGen (Erdos599R2H2.res G A B E) .src .snk := by
    intro hreach
    obtain ⟨E', hE', hval'⟩ := Erdos599R2H2.augment_flow hE hreach
    have hE'_mem : E' ∈ Flows := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE'⟩
    have hle := hE_max E' hE'_mem
    omega
  obtain ⟨C, hC_card, hC_hit⟩ := Erdos599R2H2.cut_from_unreach hE hunreach
  obtain ⟨F, hF_sub, hF_disj, hF_card, _⟩ := Erdos599R2H2.flow_decomp (Erdos599R2H2.outdeg E .src) E hE rfl
  refine ⟨F, C, hF_sub, hF_disj, hF_card ▸ hC_card, ?_⟩
  rintro s ⟨a, ha, b, hb, p, _, rfl⟩
  obtain ⟨v, hvC, hvp⟩ := hC_hit a ha b hb p
  exact ⟨v, hvC, List.mem_toFinset.mpr hvp⟩
