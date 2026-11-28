import OMAStatements.S_opg_partitionning_a_tournament_into_k_strongly_connected_subtournaments

/-!
# Partitioning Highly Connected Tournaments into `k`-Strong Subtournaments

We prove `OMA.S_opg_partitionning_a_tournament_into_k_strongly_connected_subtournaments.main`
(Thomassen's 1982 tournament partition conjecture): for all `p ≥ 1` and `k₁, ..., k_p ≥ 1`,
there exists `g` such that every `g`-strong tournament can be partitioned into `p` nontrivial
subtournaments that are `k_i`-strong respectively.

Proof architecture (combining Göring 2000, Pokrovskiy 2015 arXiv:1406.7552, and
Kühn–Osthus–Townsend 2016 arXiv:1309.7677):
1. Directed paths, shortest (backwards-transitive) paths, and basic tournament degree bounds.
2. Directed vertex Menger's theorem via Göring's short edge-deletion induction.
3. Pokrovskiy's theorem: every strongly `452k`-connected tournament is `k`-linked.
4. Kühn–Osthus–Townsend linkage structure theorem (greedy dominating sets, backwards-transitive
   path reachability lemma, and safe colouring Claims 1–5) giving `t` disjoint sets `V_1, ..., V_t`
   such that every `V_j ∪ R` (`R ⊆ V \ ⋃ V_i`) is strongly `K`-connected.
-/

namespace OMA.P_opg_partitionning_a_tournament_into_k_strongly_connected_subtournaments

open OMA.S_opg_partitionning_a_tournament_into_k_strongly_connected_subtournaments

/-! ## Part 1: Directed paths and basic tournament lemmas -/

/-- A simple directed path in a relation `R`. -/
private def IsDirPath {V : Type*} (R : V → V → Prop) (P : List V) : Prop :=
  P ≠ [] ∧ P.Nodup ∧ ∀ i : ℕ, (hi : i + 1 < P.length) → R P[i] P[i + 1]

/-- A simple directed path in `R` starting at `u` and ending at `v`. -/
private def IsDirPathBetween {V : Type*} (R : V → V → Prop) (u v : V) (P : List V) : Prop :=
  IsDirPath R P ∧ ∃ h : P ≠ [], P.head h = u ∧ P.getLast h = v

/-- A simple directed path in `R` starting in `A` and ending in `B`. -/
private def IsABPath {V : Type*} (R : V → V → Prop) (A B : Finset V) (P : List V) : Prop :=
  IsDirPath R P ∧ ∃ h : P ≠ [], P.head h ∈ A ∧ P.getLast h ∈ B

/-- An `(A, B)`-separator in `R`: every `A`-`B` path meets `S`. -/
private def IsABSep {V : Type*} (R : V → V → Prop) (A B S : Finset V) : Prop :=
  ∀ P : List V, IsABPath R A B P → ∃ x ∈ P, x ∈ S

private lemma isDirPath_singleton {V : Type*} (R : V → V → Prop) (x : V) :
    IsDirPath R [x] := by
  refine ⟨List.cons_ne_nil _ _, List.nodup_singleton x, fun i hi => ?_⟩
  simp at hi

private lemma isDirPath_mono {V : Type*} {R₁ R₂ : V → V → Prop}
    (hsub : ∀ x y, R₁ x y → R₂ x y) {P : List V} (hP : IsDirPath R₁ P) :
    IsDirPath R₂ P :=
  ⟨hP.1, hP.2.1, fun i hi => hsub _ _ (hP.2.2 i hi)⟩

private lemma isDirPath_take {V : Type*} {R : V → V → Prop} {P : List V}
    (hP : IsDirPath R P) {m : ℕ} (hm : m < P.length) :
    IsDirPath R (P.take (m + 1)) := by
  have hlen : (P.take (m + 1)).length = m + 1 := List.length_take_of_le (by omega)
  refine ⟨by intro h; rw [h] at hlen; simp at hlen, hP.2.1.take, fun i hi => ?_⟩
  rw [hlen] at hi
  rw [List.getElem_take, List.getElem_take]
  exact hP.2.2 i (by omega)

private lemma isDirPath_drop {V : Type*} {R : V → V → Prop} {P : List V}
    (hP : IsDirPath R P) {m : ℕ} (hm : m < P.length) :
    IsDirPath R (P.drop m) := by
  have hlen : (P.drop m).length = P.length - m := List.length_drop
  refine ⟨by intro h; rw [h] at hlen; simp at hlen; omega, hP.2.1.drop, fun i hi => ?_⟩
  rw [hlen] at hi
  rw [List.getElem_drop, List.getElem_drop]
  have hidx : m + (i + 1) = (m + i) + 1 := by omega
  simpa only [hidx] using hP.2.2 (m + i) (by omega)

private lemma isDirPath_append {V : Type*} {R : V → V → Prop} {P Q : List V}
    (hP : IsDirPath R P) (hQ : IsDirPath R Q)
    (hdisj : ∀ x ∈ P, x ∉ Q)
    (hedge : R (P.getLast hP.1) (Q.head hQ.1)) :
    IsDirPath R (P ++ Q) := by
  refine ⟨by simp [hP.1], List.nodup_append.mpr ⟨hP.2.1, hQ.2.1, fun a ha b hb h => hdisj a ha (h ▸ hb)⟩, fun i hi => ?_⟩
  rw [List.length_append] at hi
  by_cases h1 : i + 1 < P.length
  · rw [List.getElem_append_left (by omega), List.getElem_append_left h1]
    exact hP.2.2 i h1
  · by_cases h2 : i < P.length
    · have hi_eq : i = P.length - 1 := by omega
      have hi1_eq : i + 1 = P.length := by omega
      rw [List.getElem_append_left h2, List.getElem_append_right (by omega)]
      have hL : P[i] = P.getLast hP.1 := by
        rw [List.getLast_eq_getElem]; congr 1
      have hR : Q[i + 1 - P.length] = Q.head hQ.1 := by
        have h0 : i + 1 - P.length = 0 := by omega
        simp [h0, List.head_eq_getElem_zero]
      rw [hL, hR]
      exact hedge
    · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      have hidx : i + 1 - P.length = (i - P.length) + 1 := by omega
      simpa only [hidx] using hQ.2.2 (i - P.length) (by omega)

private lemma isDirPath_append_tail {V : Type*} {R : V → V → Prop} {P Q : List V}
    (hP : IsDirPath R P) (hQ : IsDirPath R Q)
    (hlink : P.getLast hP.1 = Q.head hQ.1)
    (hdisj : ∀ x ∈ P, x ∈ Q → x = P.getLast hP.1) :
    IsDirPath R (P ++ Q.tail) := by
  cases hQeq : Q with
  | nil => exact absurd hQeq hQ.1
  | cons q₀ Qt =>
    subst hQeq
    simp only [List.tail_cons]
    cases hQt : Qt with
    | nil =>
      simpa using hP
    | cons q₁ Qt' =>
      subst hQt
      have hQtail : IsDirPath R (q₁ :: Qt') := by
        have := isDirPath_drop hQ (m := 1) (by simp)
        simpa using this
      have hdisj' : ∀ x ∈ P, x ∉ (q₁ :: Qt') := by
        intro x hxP hxQt
        have hxQ : x ∈ q₀ :: q₁ :: Qt' := List.mem_cons_of_mem q₀ hxQt
        have hx_eq : x = P.getLast hP.1 := hdisj x hxP hxQ
        have hq0_eq : q₀ = P.getLast hP.1 := by simpa [List.head_cons] using hlink.symm
        rw [hx_eq, ← hq0_eq] at hxQt
        exact (List.nodup_cons.mp hQ.2.1).1 hxQt
      have hedge : R (P.getLast hP.1) ((q₁ :: Qt').head (List.cons_ne_nil _ _)) := by
        have h01 := hQ.2.2 0 (by simp)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h01
        have hq0_eq : P.getLast hP.1 = q₀ := by simpa [List.head_cons] using hlink
        rw [hq0_eq, List.head_cons]
        exact h01
      exact isDirPath_append hP hQtail hdisj' hedge

/-- Any `ReflTransGen` walk yields a simple directed path using only vertices of the walk. -/
private lemma exists_dirPath_of_reflTransGen {V : Type*} [DecidableEq V]
    {R : V → V → Prop} {S : Set V} {u v : V}
    (hu : u ∈ S)
    (hwalk : Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ R x y) u v) :
    ∃ P : List V, IsDirPathBetween R u v P ∧ ∀ x ∈ P, x ∈ S := by
  induction hwalk with
  | refl =>
    exact ⟨[u], ⟨isDirPath_singleton R u, List.cons_ne_nil _ _, rfl, rfl⟩,
      fun x hx => by simp only [List.mem_singleton] at hx; exact hx ▸ hu⟩
  | @tail b c _ hbc ih =>
    obtain ⟨P, ⟨hP, hne, hhead, hlast⟩, hPS⟩ := ih
    by_cases hcP : c ∈ P
    · -- Truncate P at the occurrence of c
      obtain ⟨idx, hidx, hPc⟩ := List.getElem_of_mem hcP
      refine ⟨P.take (idx + 1), ⟨isDirPath_take hP hidx, ?_⟩, ?_⟩
      · have hne' : P.take (idx + 1) ≠ [] := by
          intro h; have := congrArg List.length h
          rw [List.length_take_of_le (by omega)] at this; simp at this
        refine ⟨hne', ?_, ?_⟩
        · rw [List.head_eq_getElem_zero, List.getElem_take, ← List.head_eq_getElem_zero]
          exact hhead
        · rw [List.getLast_eq_getElem]
          have hlen : (P.take (idx + 1)).length = idx + 1 := List.length_take_of_le (by omega)
          simp only [hlen, Nat.add_sub_cancel, List.getElem_take]
          exact hPc
      · intro x hx
        exact hPS x (List.mem_of_mem_take hx)
    · -- Append c to P
      have hPc_path : IsDirPath R (P ++ [c]) := by
        apply isDirPath_append hP (isDirPath_singleton R c)
        · intro x hxP hxc
          simp only [List.mem_singleton] at hxc
          exact hcP (hxc ▸ hxP)
        · rw [hlast, List.head_cons]
          exact hbc.2.2
      refine ⟨P ++ [c], ⟨hPc_path, by simp, ?_, ?_⟩, ?_⟩
      · rw [List.head_append_of_ne_nil hne]; exact hhead
      · simp
      · intro x hx
        rcases List.mem_append.mp hx with hxP | hxc
        · exact hPS x hxP
        · simp only [List.mem_singleton] at hxc
          exact hxc ▸ hbc.2.1

/-- Conversely, a simple directed path in `S` gives a `ReflTransGen` walk in `S`. -/
private lemma reflTransGen_of_dirPath {V : Type*} {R : V → V → Prop} {S : Set V}
    {P : List V} (hP : IsDirPath R P) (hPS : ∀ x ∈ P, x ∈ S) :
    ∀ i j : ℕ, (hi : i ≤ j) → (hj : j < P.length) →
      Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ R x y) P[i] P[j] := by
  intro i j hij hj
  induction j with
  | zero =>
    have hi0 : i = 0 := by omega
    subst hi0
    exact Relation.ReflTransGen.refl
  | succ j ih =>
    by_cases hlt : i ≤ j
    · exact (ih hlt (by omega)).tail
        ⟨hPS _ (List.getElem_mem (by omega)), hPS _ (List.getElem_mem hj), hP.2.2 j hj⟩
    · have heq : i = j + 1 := by omega
      subst heq
      exact Relation.ReflTransGen.refl

private lemma reflTransGen_of_isDirPathBetween {V : Type*} {R : V → V → Prop} {S : Set V}
    {u v : V} {P : List V} (hP : IsDirPathBetween R u v P) (hPS : ∀ x ∈ P, x ∈ S) :
    Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ R x y) u v := by
  obtain ⟨hdir, hne, hhead, hlast⟩ := hP
  have hlen : 0 < P.length := List.length_pos_of_ne_nil hne
  have h := reflTransGen_of_dirPath hdir hPS 0 (P.length - 1) (Nat.zero_le _) (by omega)
  rwa [← List.head_eq_getElem_zero hne, hhead, ← List.getLast_eq_getElem hne, hlast] at h

/-- Shorten any `u`-`v` path in `R` to a shortest `u`-`v` path inside the same vertex set.
In a tournament, such a path is backwards-transitive (`R P[b] P[a]` for all `a + 2 ≤ b`). -/
private lemma exists_chordless_dirPath {V : Type*} [DecidableEq V] {R : V → V → Prop}
    {u v : V} {P₀ : List V} (hP₀ : IsDirPathBetween R u v P₀) :
    ∃ P : List V, IsDirPathBetween R u v P ∧ (∀ x ∈ P, x ∈ P₀) ∧
      ∀ a b : ℕ, (ha : a + 2 ≤ b) → (hb : b < P.length) → ¬ R P[a] P[b] := by
  classical
  let pred : ℕ → Prop := fun L =>
    ∃ P : List V, P.length = L ∧ IsDirPathBetween R u v P ∧ ∀ x ∈ P, x ∈ P₀
  have hex : ∃ L, pred L := ⟨P₀.length, P₀, rfl, hP₀, fun _ h => h⟩
  let Lmin := Nat.find hex
  obtain ⟨P, hPlen, hP, hPsub⟩ := Nat.find_spec hex
  refine ⟨P, hP, hPsub, fun a b hab hb hR => ?_⟩
  -- Shortcut across the chord P[a] → P[b]: take P.take (a + 1) ++ P.drop b
  have hdir := hP.1
  have h1 := isDirPath_take hdir (m := a) (by omega)
  have h2 := isDirPath_drop hdir (m := b) hb
  have hdisj : ∀ x ∈ P.take (a + 1), x ∉ P.drop b := by
    intro x hx1 hx2
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx1
    obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hx2
    rw [List.length_take_of_le (by omega)] at hi
    rw [List.length_drop] at hj
    rw [List.getElem_take] at heq
    rw [List.getElem_drop] at heq
    have hidx_eq := (List.nodup_iff_injective_getElem.mp hdir.2.1)
      (a₁ := ⟨i, by omega⟩) (a₂ := ⟨b + j, by omega⟩) heq.symm
    have : i = b + j := congrArg Fin.val hidx_eq
    omega
  have hedge : R ((P.take (a + 1)).getLast h1.1) ((P.drop b).head h2.1) := by
    rw [List.getLast_eq_getElem, List.head_eq_getElem_zero]
    have hl : (P.take (a + 1)).length = a + 1 := List.length_take_of_le (by omega)
    simp only [hl, Nat.add_sub_cancel, List.getElem_take, List.getElem_drop, Nat.add_zero]
    exact hR
  let Q := P.take (a + 1) ++ P.drop b
  have hQ_dir : IsDirPath R Q := isDirPath_append h1 h2 hdisj hedge
  have hQ_bet : IsDirPathBetween R u v Q := by
    obtain ⟨_, hne, hhead, hlast⟩ := hP
    refine ⟨hQ_dir, hQ_dir.1, ?_, ?_⟩
    · rw [List.head_append_of_ne_nil h1.1, List.head_eq_getElem_zero, List.getElem_take,
        ← List.head_eq_getElem_zero]
      exact hhead
    · rw [List.getLast_append_of_ne_nil _ h2.1, List.getLast_eq_getElem]
      have hld : (P.drop b).length = P.length - b := List.length_drop
      rw [List.getElem_drop]
      have hidx : b + ((P.drop b).length - 1) = P.length - 1 := by omega
      rw [List.getLast_eq_getElem hne] at hlast
      simpa only [hidx] using hlast
  have hQ_sub : ∀ x ∈ Q, x ∈ P₀ := by
    intro x hx
    rcases List.mem_append.mp hx with hx1 | hx2
    · exact hPsub x (List.mem_of_mem_take hx1)
    · exact hPsub x (List.mem_of_mem_drop hx2)
  have hQ_len : Q.length < Lmin := by
    dsimp only [Q]
    rw [List.length_append, List.length_take_of_le (by omega), List.length_drop]
    omega
  exact Nat.find_min hex hQ_len ⟨Q, rfl, hQ_bet, hQ_sub⟩

/-! ## Part 2: Directed Vertex Menger's Theorem (Göring 2000) -/

private lemma menger_directed_aux {V : Type} [Fintype V] [DecidableEq V] :
    ∀ (m : ℕ) (R : V → V → Prop) [DecidableRel R],
      (∀ x, ¬ R x x) →
      (Finset.univ.filter fun p : V × V => R p.1 p.2).card ≤ m →
      ∀ (A B : Finset V) (k : ℕ),
        (∀ S : Finset V, IsABSep R A B S → k ≤ S.card) →
        ∃ Ps : Fin k → List V,
          (∀ i, IsABPath R A B (Ps i)) ∧
          (∀ i j, i ≠ j → Disjoint (Ps i).toFinset (Ps j).toFinset)
  | 0, R, _, _hloopless, hcard0, A, B, k, hsep => by
    have hno_edge : ∀ x y, ¬ R x y := by
      intro x y hxy
      have hpos : 0 < (Finset.univ.filter fun p : V × V => R p.1 p.2).card :=
        Finset.card_pos.mpr ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩⟩
      omega
    have hAB_sep : IsABSep R A B (A ∩ B) := by
      rintro P ⟨⟨hne, _, hstep⟩, _, hhead, hlast⟩
      cases P with
      | nil => exact absurd rfl hne
      | cons x xs =>
        cases xs with
        | nil =>
          simp only [List.head_cons, List.getLast_singleton] at hhead hlast
          exact ⟨x, List.mem_cons_self, Finset.mem_inter.mpr ⟨hhead, hlast⟩⟩
        | cons y ys =>
          exact absurd (hstep 0 (by simp)) (hno_edge _ _)
    have hk_le : k ≤ (A ∩ B).card := hsep (A ∩ B) hAB_sep
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hk_le
    let e : Fin k ≃ T := (Fintype.equivFinOfCardEq (by simp [hTcard])).symm
    refine ⟨fun i => [(e i).1], ?_, ?_⟩
    · intro i
      have hmem := Finset.mem_inter.mp (hTsub (e i).2)
      exact ⟨isDirPath_singleton R _, List.cons_ne_nil _ _, by simpa using hmem.1, by simpa using hmem.2⟩
    · intro i j hij
      simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.disjoint_singleton]
      intro heq
      exact hij (e.injective (Subtype.ext heq))
  | m + 1, R, decR, hloopless, hcard_le, A, B, k, hsep => by
    classical
    by_cases hempty : (Finset.univ.filter fun p : V × V => R p.1 p.2).card = 0
    · exact menger_directed_aux 0 R hloopless (by omega) A B k hsep
    · obtain ⟨⟨u, v⟩, huv_mem⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hempty)
      have huv : R u v := (Finset.mem_filter.mp huv_mem).2
      have huv_ne : u ≠ v := fun h => hloopless u (h ▸ huv)
      let R' : V → V → Prop := fun x y => R x y ∧ ¬ (x = u ∧ y = v)
      have hR'_sub : ∀ x y, R' x y → R x y := fun _ _ h => h.1
      have hR'_loopless : ∀ x, ¬ R' x x := fun x h => hloopless x h.1
      have hR'_card : (Finset.univ.filter fun p : V × V => R' p.1 p.2).card ≤ m := by
        have hssub : (Finset.univ.filter fun p : V × V => R' p.1 p.2) ⊂
            (Finset.univ.filter fun p : V × V => R p.1 p.2) := by
          rw [Finset.ssubset_iff_of_subset]
          · exact ⟨(u, v), huv_mem, by simp [R']⟩
          · intro p hp
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
            exact hp.1
        have hlt := Finset.card_lt_card hssub
        omega
      by_cases hall : ∀ S : Finset V, IsABSep R' A B S → k ≤ S.card
      · obtain ⟨Ps, hPs, hdisj⟩ := menger_directed_aux m R' hR'_loopless hR'_card A B k hall
        exact ⟨Ps, fun i => ⟨isDirPath_mono hR'_sub (hPs i).1, (hPs i).2⟩, hdisj⟩
      · push Not at hall
        obtain ⟨S, hS_sep, hS_lt⟩ := hall
        -- Find an (A,B)-path in R avoiding S; it must use edge (u, v), so u ∉ S and v ∉ S
        have hS_not_R : ¬ IsABSep R A B S := fun h => by have := hsep S h; omega
        unfold IsABSep at hS_not_R
        push Not at hS_not_R
        obtain ⟨P₀, hP₀_ab, hP₀_noS⟩ := hS_not_R
        have hP₀_uses_uv : ∃ idx : ℕ, ∃ hidx : idx + 1 < P₀.length,
            P₀[idx] = u ∧ P₀[idx + 1] = v := by
          by_contra hno
          push Not at hno
          have hP₀_R' : IsABPath R' A B P₀ := by
            refine ⟨⟨hP₀_ab.1.1, hP₀_ab.1.2.1, fun i hi => ?_⟩, hP₀_ab.2⟩
            refine ⟨hP₀_ab.1.2.2 i hi, ?_⟩
            rintro ⟨hu_eq, hv_eq⟩
            exact hno i hi hu_eq hv_eq
          obtain ⟨x, hxP, hxS⟩ := hS_sep P₀ hP₀_R'
          exact hP₀_noS x hxP hxS
        obtain ⟨idx₀, hidx₀, hu₀, hv₀⟩ := hP₀_uses_uv
        have hu_nS : u ∉ S := by
          rw [← hu₀]; exact hP₀_noS _ (List.getElem_mem (by omega))
        have hv_nS : v ∉ S := by
          rw [← hv₀]; exact hP₀_noS _ (List.getElem_mem hidx₀)
        let Su : Finset V := insert u S
        let Sv : Finset V := insert v S
        have hSu_sepR : IsABSep R A B Su := by
          intro P hP
          by_cases huses : ∃ j : ℕ, ∃ hj : j + 1 < P.length, P[j] = u ∧ P[j + 1] = v
          · obtain ⟨j, hj, hju, _⟩ := huses
            exact ⟨u, hju ▸ List.getElem_mem (by omega), Finset.mem_insert_self u S⟩
          · push Not at huses
            have hP' : IsABPath R' A B P := by
              refine ⟨⟨hP.1.1, hP.1.2.1, fun j hj => ⟨hP.1.2.2 j hj, ?_⟩⟩, hP.2⟩
              rintro ⟨h1, h2⟩; exact huses j hj h1 h2
            obtain ⟨x, hxP, hxS⟩ := hS_sep P hP'
            exact ⟨x, hxP, Finset.mem_insert_of_mem hxS⟩
        have hSu_card : Su.card = k := by
          have h1 : k ≤ Su.card := hsep Su hSu_sepR
          have h2 : Su.card = S.card + 1 := Finset.card_insert_of_notMem hu_nS
          omega
        have hSv_card : Sv.card = k := by
          rw [Finset.card_insert_of_notMem hv_nS]
          have h2 : Su.card = S.card + 1 := Finset.card_insert_of_notMem hu_nS
          omega
        -- Claim 1: every (A, Su)-separator in R' has size ≥ k
        have hsep_left : ∀ T : Finset V, IsABSep R' A Su T → k ≤ T.card := by
          intro T hT
          apply hsep T
          intro P hP
          obtain ⟨hdir, hne, hhead, hlast⟩ := hP
          by_cases huses : ∃ j : ℕ, ∃ hj : j + 1 < P.length, P[j] = u ∧ P[j + 1] = v
          · obtain ⟨j, hj, hju, _⟩ := huses
            let Ppre := P.take (j + 1)
            have hpre_R' : IsABPath R' A Su Ppre := by
              have hdir_pre := isDirPath_take hdir (m := j) (by omega)
              have hlen : Ppre.length = j + 1 := List.length_take_of_le (by omega)
              refine ⟨⟨hdir_pre.1, hdir_pre.2.1, fun i hi => ?_⟩, hdir_pre.1, ?_, ?_⟩
              · rw [hlen] at hi
                refine ⟨hdir_pre.2.2 i (by omega), ?_⟩
                rintro ⟨hiu, _⟩
                rw [List.getElem_take] at hiu
                have hidx_eq := (List.nodup_iff_injective_getElem.mp hdir.2.1)
                  (a₁ := ⟨i, by omega⟩) (a₂ := ⟨j, by omega⟩) (hiu.trans hju.symm)
                have : i = j := congrArg Fin.val hidx_eq
                omega
              · rw [List.head_eq_getElem_zero, List.getElem_take, ← List.head_eq_getElem_zero]
                exact hhead
              · rw [List.getLast_eq_getElem]
                simp only [Ppre, hlen, Nat.add_sub_cancel, List.getElem_take]
                rw [hju]; exact Finset.mem_insert_self u S
            obtain ⟨x, hxpre, hxT⟩ := hT Ppre hpre_R'
            exact ⟨x, List.mem_of_mem_take hxpre, hxT⟩
          · push Not at huses
            have hP' : IsABPath R' A B P := by
              refine ⟨⟨hdir.1, hdir.2.1, fun j hj => ⟨hdir.2.2 j hj, ?_⟩⟩, hne, hhead, hlast⟩
              rintro ⟨h1, h2⟩; exact huses j hj h1 h2
            obtain ⟨s, hsP, hsS⟩ := hS_sep P hP'
            obtain ⟨j, hj, hjs⟩ := List.getElem_of_mem hsP
            let Ppre := P.take (j + 1)
            have hpre_R' : IsABPath R' A Su Ppre := by
              have hdir_pre := isDirPath_take hP'.1 (m := j) hj
              have hlen : Ppre.length = j + 1 := List.length_take_of_le (by omega)
              refine ⟨hdir_pre, hdir_pre.1, ?_, ?_⟩
              · rw [List.head_eq_getElem_zero, List.getElem_take, ← List.head_eq_getElem_zero]
                exact hhead
              · rw [List.getLast_eq_getElem]
                simp only [Ppre, hlen, Nat.add_sub_cancel, List.getElem_take]
                rw [hjs]; exact Finset.mem_insert_of_mem hsS
            obtain ⟨x, hxpre, hxT⟩ := hT Ppre hpre_R'
            exact ⟨x, List.mem_of_mem_take hxpre, hxT⟩
        -- Claim 2: every (Sv, B)-separator in R' has size ≥ k
        have hsep_right : ∀ T : Finset V, IsABSep R' Sv B T → k ≤ T.card := by
          intro T hT
          apply hsep T
          intro P hP
          obtain ⟨hdir, hne, hhead, hlast⟩ := hP
          by_cases huses : ∃ j : ℕ, ∃ hj : j + 1 < P.length, P[j] = u ∧ P[j + 1] = v
          · obtain ⟨j, hj, hju, hjv⟩ := huses
            let Psuf := P.drop (j + 1)
            have hsuf_R' : IsABPath R' Sv B Psuf := by
              have hdir_suf := isDirPath_drop hdir (m := j + 1) hj
              have hlen : Psuf.length = P.length - (j + 1) := List.length_drop
              refine ⟨⟨hdir_suf.1, hdir_suf.2.1, fun i hi => ?_⟩, hdir_suf.1, ?_, ?_⟩
              · rw [hlen] at hi
                refine ⟨hdir_suf.2.2 i (by omega), ?_⟩
                rintro ⟨hiu, _⟩
                rw [List.getElem_drop] at hiu
                have hidx_eq := (List.nodup_iff_injective_getElem.mp hdir.2.1)
                  (a₁ := ⟨j + 1 + i, by omega⟩) (a₂ := ⟨j, by omega⟩) (hiu.trans hju.symm)
                have : j + 1 + i = j := congrArg Fin.val hidx_eq
                omega
              · rw [List.head_eq_getElem_zero]
                simp only [Psuf, List.getElem_drop, Nat.add_zero, hjv]
                exact Finset.mem_insert_self v S
              · rw [List.getLast_eq_getElem]
                have hidx : (j + 1) + (Psuf.length - 1) = P.length - 1 := by omega
                rw [List.getElem_drop]
                rw [List.getLast_eq_getElem hne] at hlast
                simpa only [hidx] using hlast
            obtain ⟨x, hxsuf, hxT⟩ := hT Psuf hsuf_R'
            exact ⟨x, List.mem_of_mem_drop hxsuf, hxT⟩
          · push Not at huses
            have hP' : IsABPath R' A B P := by
              refine ⟨⟨hdir.1, hdir.2.1, fun j hj => ⟨hdir.2.2 j hj, ?_⟩⟩, hne, hhead, hlast⟩
              rintro ⟨h1, h2⟩; exact huses j hj h1 h2
            obtain ⟨s, hsP, hsS⟩ := hS_sep P hP'
            obtain ⟨j, hj, hjs⟩ := List.getElem_of_mem hsP
            let Psuf := P.drop j
            have hsuf_R' : IsABPath R' Sv B Psuf := by
              have hdir_suf := isDirPath_drop hP'.1 (m := j) hj
              have hlen : Psuf.length = P.length - j := List.length_drop
              refine ⟨hdir_suf, hdir_suf.1, ?_, ?_⟩
              · rw [List.head_eq_getElem_zero]
                simp only [Psuf, List.getElem_drop, Nat.add_zero, hjs]
                exact Finset.mem_insert_of_mem hsS
              · rw [List.getLast_eq_getElem]
                have hidx : j + (Psuf.length - 1) = P.length - 1 := by omega
                rw [List.getElem_drop]
                rw [List.getLast_eq_getElem hne] at hlast
                simpa only [hidx] using hlast
            obtain ⟨x, hxsuf, hxT⟩ := hT Psuf hsuf_R'
            exact ⟨x, List.mem_of_mem_drop hxsuf, hxT⟩
        -- Apply IH to (A, Su) and (Sv, B) in R'
        obtain ⟨Ps, hPs, hPs_disj⟩ := menger_directed_aux m R' hR'_loopless hR'_card A Su k hsep_left
        obtain ⟨Qs, hQs, hQs_disj⟩ := menger_directed_aux m R' hR'_loopless hR'_card Sv B k hsep_right
        -- Endpoint bijections: last(Ps i) bijects Fin k onto Su, head(Qs j) bijects Fin k onto Sv
        let endP : Fin k → V := fun i => (Ps i).getLast (hPs i).1.1
        let startQ : Fin k → V := fun j => (Qs j).head (hQs j).1.1
        have hendP_mem : ∀ i, endP i ∈ Su := fun i => (hPs i).2.choose_spec.2
        have hstartQ_mem : ∀ j, startQ j ∈ Sv := fun j => (hQs j).2.choose_spec.1
        have hendP_inj : Function.Injective endP := by
          intro i₁ i₂ heq
          by_contra hne
          have h1 : endP i₁ ∈ (Ps i₁).toFinset := List.mem_toFinset.mpr (List.getLast_mem _)
          have h2 : endP i₁ ∈ (Ps i₂).toFinset := heq ▸ List.mem_toFinset.mpr (List.getLast_mem _)
          exact Finset.disjoint_left.mp (hPs_disj i₁ i₂ hne) h1 h2
        have hstartQ_inj : Function.Injective startQ := by
          intro j₁ j₂ heq
          by_contra hne
          have h1 : startQ j₁ ∈ (Qs j₁).toFinset := List.mem_toFinset.mpr (List.head_mem _)
          have h2 : startQ j₁ ∈ (Qs j₂).toFinset := heq ▸ List.mem_toFinset.mpr (List.head_mem _)
          exact Finset.disjoint_left.mp (hQs_disj j₁ j₂ hne) h1 h2
        have hendP_surj : ∀ x ∈ Su, ∃ i, endP i = x := by
          have himg : Finset.univ.image endP = Su :=
            Finset.eq_of_subset_of_card_le
              (Finset.image_subset_iff.mpr fun i _ => hendP_mem i)
              (by rw [Finset.card_image_of_injective _ hendP_inj, Finset.card_univ, Fintype.card_fin, hSu_card])
          intro x hx
          rw [← himg, Finset.mem_image] at hx
          obtain ⟨i, _, hi⟩ := hx; exact ⟨i, hi⟩
        have hstartQ_surj : ∀ x ∈ Sv, ∃ j, startQ j = x := by
          have himg : Finset.univ.image startQ = Sv :=
            Finset.eq_of_subset_of_card_le
              (Finset.image_subset_iff.mpr fun j _ => hstartQ_mem j)
              (by rw [Finset.card_image_of_injective _ hstartQ_inj, Finset.card_univ, Fintype.card_fin, hSv_card])
          intro x hx
          rw [← himg, Finset.mem_image] at hx
          obtain ⟨j, _, hj⟩ := hx; exact ⟨j, hj⟩
        -- Ps i only meets Su at endP i, and Qs j only meets Sv at startQ j
        have hPs_meet_Su : ∀ i x, x ∈ Ps i → x ∈ Su → x = endP i := by
          intro i x hxP hxSu
          obtain ⟨i', hi'⟩ := hendP_surj x hxSu
          by_cases heq : i = i'
          · rw [heq, hi']
          · exact absurd (hi' ▸ List.mem_toFinset.mpr (List.getLast_mem _))
              (Finset.disjoint_left.mp (hPs_disj i i' heq) (List.mem_toFinset.mpr hxP))
        have hQs_meet_Sv : ∀ j x, x ∈ Qs j → x ∈ Sv → x = startQ j := by
          intro j x hxQ hxSv
          obtain ⟨j', hj'⟩ := hstartQ_surj x hxSv
          by_cases heq : j = j'
          · rw [heq, hj']
          · exact absurd (hj' ▸ List.mem_toFinset.mpr (List.head_mem _))
              (Finset.disjoint_left.mp (hQs_disj j j' heq) (List.mem_toFinset.mpr hxQ))
        -- Crucial disjointness: any common vertex of Ps i and Qs j lies in S (and equals endP i = startQ j)
        have hPQ_meet : ∀ i j w, w ∈ Ps i → w ∈ Qs j → w ∈ S ∧ w = endP i ∧ w = startQ j := by
          intro i j w hwP hwQ
          have hwS : w ∈ S := by
            by_contra hw_nS
            obtain ⟨idxP, hidxP, hPw⟩ := List.getElem_of_mem hwP
            obtain ⟨idxQ, hidxQ, hQw⟩ := List.getElem_of_mem hwQ
            let Ppre := (Ps i).take (idxP + 1)
            let Qsuf := (Qs j).drop idxQ
            have hPpre_noS : ∀ x ∈ Ppre, x ∉ S := by
              intro x hx hxS
              have hxP := List.mem_of_mem_take hx
              have hx_end := hPs_meet_Su i x hxP (Finset.mem_insert_of_mem hxS)
              obtain ⟨r, hr, hrx⟩ := List.getElem_of_mem hx
              rw [List.length_take_of_le (by omega)] at hr
              rw [List.getElem_take] at hrx
              have hlen_i : (Ps i).length - 1 < (Ps i).length := Nat.sub_lt (List.length_pos_of_ne_nil (hPs i).1.1) Nat.one_pos
              have hlast_eq : (Ps i)[(Ps i).length - 1] = endP i := (List.getLast_eq_getElem (hPs i).1.1).symm
              have hr_eq : r = (Ps i).length - 1 := congrArg Fin.val ((List.nodup_iff_injective_getElem.mp (hPs i).1.2.1)
                (a₁ := ⟨r, by omega⟩) (a₂ := ⟨(Ps i).length - 1, hlen_i⟩) (hrx.trans (hx_end.trans hlast_eq.symm)))
              have hidxP_last : idxP = (Ps i).length - 1 := by omega
              have hw_eq_x : w = x := by
                have hget : (Ps i)[idxP] = (Ps i)[(Ps i).length - 1] := by simp only [hidxP_last]
                rw [← hPw, hget, hlast_eq, hx_end]
              exact hw_nS (hw_eq_x ▸ hxS)
            have hQsuf_noS : ∀ x ∈ Qsuf, x ∉ S := by
              intro x hx hxS
              have hxQ := List.mem_of_mem_drop hx
              have hx_start := hQs_meet_Sv j x hxQ (Finset.mem_insert_of_mem hxS)
              obtain ⟨r, hr, hrx⟩ := List.getElem_of_mem hx
              rw [List.length_drop] at hr
              rw [List.getElem_drop] at hrx
              have h0_lt : 0 < (Qs j).length := List.length_pos_of_ne_nil (hQs j).1.1
              have hfirst_eq : (Qs j)[0] = startQ j := (List.head_eq_getElem_zero (hQs j).1.1).symm
              have hr_eq : idxQ + r = 0 := congrArg Fin.val ((List.nodup_iff_injective_getElem.mp (hQs j).1.2.1)
                (a₁ := ⟨idxQ + r, by omega⟩) (a₂ := ⟨0, h0_lt⟩) (hrx.trans (hx_start.trans hfirst_eq.symm)))
              have hidxQ_zero : idxQ = 0 := by omega
              have hw_eq_x : w = x := by
                have hget : (Qs j)[idxQ] = (Qs j)[0] := by simp only [hidxQ_zero]
                rw [← hQw, hget, hfirst_eq, hx_start]
              exact hw_nS (hw_eq_x ▸ hxS)
            -- Walk from head(Ps i) to w in Ppre, then w to last(Qs j) in Qsuf, all in (↑S)ᶜ
            let U : Set V := (S : Set V)ᶜ
            have hdir1 := isDirPath_take (hPs i).1 (m := idxP) hidxP
            have hdir2 := isDirPath_drop (hQs j).1 (m := idxQ) hidxQ
            have hU1 : ∀ x ∈ Ppre, x ∈ U := fun x hx => hPpre_noS x hx
            have hU2 : ∀ x ∈ Qsuf, x ∈ U := fun x hx => hQsuf_noS x hx
            have hw1 : Relation.ReflTransGen (fun x y => x ∈ U ∧ y ∈ U ∧ R' x y)
                ((Ps i).head (hPs i).1.1) w := by
              have hlen1 : (List.take (idxP + 1) (Ps i)).length = idxP + 1 := List.length_take_of_le (by omega)
              have hw := reflTransGen_of_dirPath hdir1 hU1 0 idxP (Nat.zero_le _) (by omega)
              rw [List.head_eq_getElem_zero]
              simpa only [Ppre, List.getElem_take, hPw] using hw
            have hw2 : Relation.ReflTransGen (fun x y => x ∈ U ∧ y ∈ U ∧ R' x y)
                w ((Qs j).getLast (hQs j).1.1) := by
              have hlen2 : (List.drop idxQ (Qs j)).length = (Qs j).length - idxQ := List.length_drop
              have hw := reflTransGen_of_dirPath hdir2 hU2 0 ((List.drop idxQ (Qs j)).length - 1) (Nat.zero_le _) (by omega)
              have hidx_last : idxQ + ((List.drop idxQ (Qs j)).length - 1) = (Qs j).length - 1 := by omega
              rw [List.getLast_eq_getElem]
              simpa only [Qsuf, List.getElem_drop, Nat.add_zero, hQw, hidx_last] using hw
            have ha_in_U : (Ps i).head (hPs i).1.1 ∈ U := by
              have h0 : (Ps i).head (hPs i).1.1 ∈ Ppre := by
                have : Ppre[0]'(by rw [List.length_take_of_le (by omega)]; omega) ∈ Ppre := List.getElem_mem _
                simpa [Ppre, List.getElem_take, List.head_eq_getElem_zero] using this
              exact hU1 _ h0
            obtain ⟨W, ⟨hWdir, hWne, hWhead, hWlast⟩, hWU⟩ :=
              exists_dirPath_of_reflTransGen ha_in_U (hw1.trans hw2)
            have hW_ab : IsABPath R' A B W :=
              ⟨hWdir, hWne, hWhead ▸ (hPs i).2.choose_spec.1, hWlast ▸ (hQs j).2.choose_spec.2⟩
            obtain ⟨x, hxW, hxS⟩ := hS_sep W hW_ab
            exact hWU x hxW hxS
          exact ⟨hwS, hPs_meet_Su i w hwP (Finset.mem_insert_of_mem hwS),
            hQs_meet_Sv j w hwQ (Finset.mem_insert_of_mem hwS)⟩
        -- Match each i : Fin k with the corresponding j : Fin k via endP i (s ↦ s, u ↦ v)
        let target : Fin k → V := fun i => if endP i = u then v else endP i
        have htarget_mem : ∀ i, target i ∈ Sv := by
          intro i
          dsimp only [target]
          split_ifs with heq
          · exact Finset.mem_insert_self v S
          · have hmem := hendP_mem i
            rcases Finset.mem_insert.mp hmem with h1 | h2
            · exact absurd h1 heq
            · exact Finset.mem_insert_of_mem h2
        have htarget_inj : Function.Injective target := by
          intro i₁ i₂ heq
          dsimp only [target] at heq
          split_ifs at heq with h1 h2 h2
          · exact hendP_inj (h1.trans h2.symm)
          · have hmem := hendP_mem i₂
            rcases Finset.mem_insert.mp hmem with hu2 | hs2
            · exact absurd hu2 h2
            · exact absurd (heq ▸ hs2) hv_nS
          · have hmem := hendP_mem i₁
            rcases Finset.mem_insert.mp hmem with hu1 | hs1
            · exact absurd hu1 h1
            · exact absurd (heq.symm ▸ hs1) hv_nS
          · exact hendP_inj heq
        choose matchJ hmatchJ using fun i => hstartQ_surj (target i) (htarget_mem i)
        have hmatchJ_inj : Function.Injective matchJ := fun i₁ i₂ h =>
          htarget_inj ((hmatchJ i₁).symm.trans ((congrArg startQ h).trans (hmatchJ i₂)))
        -- Glue Ps i and Qs (matchJ i)
        let glued : Fin k → List V := fun i =>
          if endP i = u then Ps i ++ Qs (matchJ i) else Ps i ++ (Qs (matchJ i)).tail
        refine ⟨glued, ?_, ?_⟩
        · intro i
          dsimp only [glued]
          split_ifs with heq
          · have hstart_v : startQ (matchJ i) = v := by
              rw [hmatchJ i]; simp [target, heq]
            have hdisj_PQ : ∀ x ∈ Ps i, x ∉ Qs (matchJ i) := by
              intro x hxP hxQ
              have ⟨hxS, hx_end, _⟩ := hPQ_meet i (matchJ i) x hxP hxQ
              exact hu_nS (heq ▸ hx_end ▸ hxS)
            have hdir := isDirPath_append (isDirPath_mono hR'_sub (hPs i).1)
              (isDirPath_mono hR'_sub (hQs (matchJ i)).1) hdisj_PQ
              (by change R (endP i) (startQ (matchJ i)); rw [heq, hstart_v]; exact huv)
            refine ⟨hdir, hdir.1, ?_, ?_⟩
            · rw [List.head_append_of_ne_nil (hPs i).1.1]
              exact (hPs i).2.choose_spec.1
            · rw [List.getLast_append_of_ne_nil _ (hQs (matchJ i)).1.1]
              exact (hQs (matchJ i)).2.choose_spec.2
          · have hlink : endP i = startQ (matchJ i) := by
              rw [hmatchJ i]; simp [target, heq]
            have hdisj_PQ : ∀ x ∈ Ps i, x ∈ Qs (matchJ i) → x = endP i := fun x hxP hxQ =>
              (hPQ_meet i (matchJ i) x hxP hxQ).2.1
            have hdir := isDirPath_append_tail (isDirPath_mono hR'_sub (hPs i).1)
              (isDirPath_mono hR'_sub (hQs (matchJ i)).1) hlink hdisj_PQ
            refine ⟨hdir, hdir.1, ?_, ?_⟩
            · rw [List.head_append_of_ne_nil (hPs i).1.1]
              exact (hPs i).2.choose_spec.1
            · have hne_Q := (hQs (matchJ i)).1.1
              by_cases ht_nil : (Qs (matchJ i)).tail = []
              · simp only [ht_nil, List.append_nil]
                have hQ_len1 : (Qs (matchJ i)).length = 1 := by
                  cases hq : Qs (matchJ i) with
                  | nil => exact absurd hq hne_Q
                  | cons a l => simp [hq] at ht_nil; subst ht_nil; simp
                have hlast_eq_head : (Qs (matchJ i)).getLast hne_Q = startQ (matchJ i) := by
                  dsimp only [startQ]
                  rw [List.getLast_eq_getElem, List.head_eq_getElem_zero]; simp only [hQ_len1]
                change endP i ∈ B
                rw [hlink, ← hlast_eq_head]
                exact (hQs (matchJ i)).2.choose_spec.2
              · rw [List.getLast_append_of_ne_nil _ ht_nil]
                have hlast_tail_gen : ∀ (l : List V) (h1 : l ≠ []) (h2 : l.tail ≠ []),
                    l.tail.getLast h2 = l.getLast h1 := by
                  intro l; cases l with
                  | nil => intro h1; exact absurd rfl h1
                  | cons a l' =>
                    cases l' with
                    | nil => intro _ h2; exact absurd rfl h2
                    | cons b t => intro _ _; simp
                rw [hlast_tail_gen (Qs (matchJ i)) hne_Q ht_nil]
                exact (hQs (matchJ i)).2.choose_spec.2
        · -- Pairwise disjointness of glued paths
          intro i₁ i₂ hne
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          rw [List.mem_toFinset] at hx1 hx2
          have hmem_glued : ∀ i, x ∈ glued i → x ∈ Ps i ∨ x ∈ Qs (matchJ i) := by
            intro i hx
            dsimp only [glued] at hx
            split_ifs at hx
            · exact List.mem_append.mp hx
            · rcases List.mem_append.mp hx with h | h
              · exact Or.inl h
              · exact Or.inr (List.mem_of_mem_tail h)
          rcases hmem_glued i₁ hx1 with hP1 | hQ1 <;> rcases hmem_glued i₂ hx2 with hP2 | hQ2
          · exact Finset.disjoint_left.mp (hPs_disj i₁ i₂ hne)
              (List.mem_toFinset.mpr hP1) (List.mem_toFinset.mpr hP2)
          · have ⟨hxS, hx_end, hx_start⟩ := hPQ_meet i₁ (matchJ i₂) x hP1 hQ2
            have hne_u1 : endP i₁ ≠ u := fun h => hu_nS (h ▸ hx_end ▸ hxS)
            have ht1 : target i₁ = x := by simp [target, hne_u1, hx_end]
            have ht2 : target i₂ = x := by rw [← hmatchJ i₂, ← hx_start]
            exact hne (htarget_inj (ht1.trans ht2.symm))
          · have ⟨hxS, hx_end, hx_start⟩ := hPQ_meet i₂ (matchJ i₁) x hP2 hQ1
            have hne_u2 : endP i₂ ≠ u := fun h => hu_nS (h ▸ hx_end ▸ hxS)
            have ht2 : target i₂ = x := by simp [target, hne_u2, hx_end]
            have ht1 : target i₁ = x := by rw [← hmatchJ i₁, ← hx_start]
            exact hne (htarget_inj (ht1.trans ht2.symm))
          · exact Finset.disjoint_left.mp (hQs_disj (matchJ i₁) (matchJ i₂) (fun h => hne (hmatchJ_inj h)))
              (List.mem_toFinset.mpr hQ1) (List.mem_toFinset.mpr hQ2)

/-- Directed vertex Menger's theorem: in any loopless finite digraph, if every `(A, B)`-separator
has size at least `k`, then there exist `k` pairwise vertex-disjoint directed paths from `A` to `B`. -/
private theorem menger_directed {V : Type} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) [DecidableRel R] (hloopless : ∀ x, ¬ R x x)
    (A B : Finset V) (k : ℕ)
    (hsep : ∀ S : Finset V, IsABSep R A B S → k ≤ S.card) :
    ∃ Ps : Fin k → List V,
      (∀ i, IsABPath R A B (Ps i)) ∧
      (∀ i j, i ≠ j → Disjoint (Ps i).toFinset (Ps j).toFinset) :=
  menger_directed_aux _ R hloopless le_rfl A B k hsep

/-- Menger corollary for `k`-strong sets: if `G` is `k`-strong on `S`, and `A, B ⊆ S` have size `≥ k`,
then there are `k` vertex-disjoint paths in `S` from `A` to `B`. -/
private lemma menger_of_isKStrongOn {V : Type} [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj] (hloopless : ∀ x, ¬ G.Adj x x)
    {S : Finset V} {k : ℕ} (hstrong : IsKStrongOn G (S : Set V) k)
    {A B : Finset V} (hAS : A ⊆ S) (hBS : B ⊆ S) (hAk : k ≤ A.card) (hBk : k ≤ B.card) :
    ∃ Ps : Fin k → List V,
      (∀ i, IsABPath (fun x y => x ∈ S ∧ y ∈ S ∧ G.Adj x y) A B (Ps i)) ∧
      (∀ i j, i ≠ j → Disjoint (Ps i).toFinset (Ps j).toFinset) := by
  let R : V → V → Prop := fun x y => x ∈ S ∧ y ∈ S ∧ G.Adj x y
  apply menger_directed R (fun x h => hloopless x h.2.2) A B k
  intro X hXsep
  by_contra hlt
  push Not at hlt
  have hA_diff : (A \ X).Nonempty := Finset.card_pos.mp (by
    have := Finset.card_sdiff_add_card_inter A X
    have hle : (A ∩ X).card ≤ X.card := Finset.card_le_card Finset.inter_subset_right
    omega)
  have hB_diff : (B \ X).Nonempty := Finset.card_pos.mp (by
    have := Finset.card_sdiff_add_card_inter B X
    have hle : (B ∩ X).card ≤ X.card := Finset.card_le_card Finset.inter_subset_right
    omega)
  obtain ⟨a, ha⟩ := hA_diff
  obtain ⟨b, hb⟩ := hB_diff
  rw [Finset.mem_sdiff] at ha hb
  have haS : a ∈ (S : Set V) \ (X : Set V) := ⟨hAS ha.1, ha.2⟩
  have hbS : b ∈ (S : Set V) \ (X : Set V) := ⟨hBS hb.1, hb.2⟩
  have hwalk := hstrong.2 X hlt a haS b hbS
  obtain ⟨P, ⟨hPdir, hPne, hPhead, hPlast⟩, hPmem⟩ := exists_dirPath_of_reflTransGen haS hwalk
  have hP_R : IsABPath R A B P := by
    refine ⟨⟨hPdir.1, hPdir.2.1, fun i hi => ?_⟩, hPne, hPhead ▸ ha.1, hPlast ▸ hb.1⟩
    exact ⟨(hPmem _ (List.getElem_mem (by omega))).1, (hPmem _ (List.getElem_mem hi)).1, hPdir.2.2 i hi⟩
  obtain ⟨x, hxP, hxX⟩ := hXsep P hP_R
  exact (hPmem x hxP).2 hxX

/-! ## Part 3: Tournament degree bounds, greedy dominating sets, and Pokrovskiy's linkedness theorem -/

section TournamentAPI

variable {V : Type} [Fintype V] [DecidableEq V]

private def opDigraph (G : Digraph V) : Digraph V :=
  ⟨fun u v => G.Adj v u⟩

private local instance instDecidableRelOpDigraph {G : Digraph V} [DecidableRel G.Adj] :
    DecidableRel (opDigraph G).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj v u))

omit [Fintype V] [DecidableEq V] in
private lemma isTournament_op {G : Digraph V} (hT : IsTournament G) :
    IsTournament (opDigraph G) :=
  ⟨hT.1, fun u v hne => hT.2 v u hne.symm⟩

omit [Fintype V] [DecidableEq V] in
private lemma isStrongOn_op_iff {G : Digraph V} {S : Set V} :
    IsStrongOn (opDigraph G) S ↔ IsStrongOn G S := by
  constructor
  · intro h u hu v hv
    have hrev := h v hv u hu
    induction hrev with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, hbc.2.2⟩ (ih hbc.1)
  · intro h u hu v hv
    have hrev := h v hv u hu
    induction hrev with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, hbc.2.2⟩ (ih hbc.1)

omit [Fintype V] [DecidableEq V] in
private lemma isKStrongOn_op_iff {G : Digraph V} {S : Set V} {k : ℕ} :
    IsKStrongOn (opDigraph G) S k ↔ IsKStrongOn G S k := by
  simp only [IsKStrongOn, isStrongOn_op_iff]

private def outNbr (G : Digraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) : Finset V :=
  S.filter (fun w => G.Adj v w)

private def inNbr (G : Digraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) : Finset V :=
  S.filter (fun w => G.Adj w v)

private def outDeg (G : Digraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) : ℕ :=
  (outNbr G S v).card

private def inDeg (G : Digraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) : ℕ :=
  (inNbr G S v).card

omit [Fintype V] [DecidableEq V] in
private lemma outNbr_op_eq_inNbr {G : Digraph V} [DecidableRel G.Adj] (S : Finset V) (v : V) :
    outNbr (opDigraph G) S v = inNbr G S v := by
  ext w; simp only [outNbr, inNbr, Finset.mem_filter]; rfl

omit [Fintype V] [DecidableEq V] in
private lemma outDeg_op_eq_inDeg {G : Digraph V} [DecidableRel G.Adj] (S : Finset V) (v : V) :
    outDeg (opDigraph G) S v = inDeg G S v :=
  congrArg Finset.card (outNbr_op_eq_inNbr S v)

omit [Fintype V] [DecidableEq V] in
private lemma inDeg_op_eq_outDeg {G : Digraph V} [DecidableRel G.Adj] (S : Finset V) (v : V) :
    inDeg (opDigraph G) S v = outDeg G S v := by
  unfold inDeg outDeg inNbr outNbr
  congr 1

omit [Fintype V] in
private lemma outDeg_add_inDeg_eq {G : Digraph V} [DecidableRel G.Adj] (hT : IsTournament G)
    {S : Finset V} {v : V} (hv : v ∈ S) :
    outDeg G S v + inDeg G S v + 1 = S.card := by
  have hdisj : Disjoint (outNbr G S v) (inNbr G S v) := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    simp only [outNbr, inNbr, Finset.mem_filter] at h1 h2
    have hne : v ≠ w := fun h => hT.1 v (h ▸ h1.2)
    exact ((hT.2 v w hne).mp h1.2) h2.2
  have hunion : insert v (outNbr G S v ∪ inNbr G S v) = S := by
    ext w
    simp only [Finset.mem_insert, Finset.mem_union, outNbr, inNbr, Finset.mem_filter]
    constructor
    · rintro (rfl | ⟨hw, _⟩ | ⟨hw, _⟩)
      · exact hv
      · exact hw
      · exact hw
    · intro hw
      by_cases heq : w = v
      · exact Or.inl heq
      · right
        by_cases hadj : G.Adj v w
        · exact Or.inl ⟨hw, hadj⟩
        · exact Or.inr ⟨hw, not_not.mp fun h => hadj ((hT.2 v w (Ne.symm heq)).mpr h)⟩
  have hv_nmem : v ∉ outNbr G S v ∪ inNbr G S v := by
    simp [outNbr, inNbr, hT.1 v]
  have hcard := congrArg Finset.card hunion
  rw [Finset.card_insert_of_notMem hv_nmem, Finset.card_union_of_disjoint hdisj] at hcard
  exact hcard

omit [Fintype V] [DecidableEq V] in
private lemma sum_outDeg_eq_sum_inDeg (G : Digraph V) [DecidableRel G.Adj] (S : Finset V) :
    ∑ v ∈ S, outDeg G S v = ∑ v ∈ S, inDeg G S v := by
  simp only [outDeg, inDeg, outNbr, inNbr, Finset.card_filter]
  rw [Finset.sum_comm]

omit [Fintype V] in
private lemma two_mul_sum_outDeg {G : Digraph V} [DecidableRel G.Adj] (hT : IsTournament G)
    (S : Finset V) :
    2 * ∑ v ∈ S, outDeg G S v = S.card * (S.card - 1) := by
  have hsum : ∑ v ∈ S, (outDeg G S v + inDeg G S v) = S.card * (S.card - 1) := by
    have hterm : ∀ v ∈ S, outDeg G S v + inDeg G S v = S.card - 1 := fun v hv => by
      have := outDeg_add_inDeg_eq hT hv; omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
  rw [Finset.sum_add_distrib, ← sum_outDeg_eq_sum_inDeg G S] at hsum
  omega

omit [Fintype V] in
private lemma exists_large_outDeg {G : Digraph V} [DecidableRel G.Adj] (hT : IsTournament G)
    {S : Finset V} (hne : S.Nonempty) :
    ∃ v ∈ S, S.card - 1 ≤ 2 * outDeg G S v := by
  by_contra hall
  push Not at hall
  have hsum_lt : ∑ v ∈ S, (2 * outDeg G S v) < ∑ _v ∈ S, (S.card - 1) :=
    Finset.sum_lt_sum_of_nonempty hne hall
  rw [← Finset.mul_sum, two_mul_sum_outDeg hT S, Finset.sum_const, smul_eq_mul] at hsum_lt
  omega

omit [Fintype V] in
private lemma exists_large_inDeg {G : Digraph V} [DecidableRel G.Adj] (hT : IsTournament G)
    {S : Finset V} (hne : S.Nonempty) :
    ∃ v ∈ S, S.card - 1 ≤ 2 * inDeg G S v := by
  simpa only [outDeg_op_eq_inDeg] using
    exists_large_outDeg (isTournament_op hT) hne

omit [Fintype V] in
/-- KOT Proposition 2.6: fewer than `2k` vertices have out-degree `< k` (for `k ≥ 1`). -/
private lemma card_small_outDeg_lt {G : Digraph V} [DecidableRel G.Adj] (hT : IsTournament G)
    (S : Finset V) {k : ℕ} (hk : 1 ≤ k) :
    (S.filter fun v => outDeg G S v < k).card < 2 * k := by
  by_contra hge
  push Not at hge
  obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hge
  have hBS : B ⊆ S := hBsub.trans (Finset.filter_subset _ _)
  have hsum_le : 2 * ∑ v ∈ B, outDeg G B v ≤ 2 * (2 * k * (k - 1)) := by
    have hle : ∑ v ∈ B, outDeg G B v ≤ ∑ _v ∈ B, (k - 1) := by
      refine Finset.sum_le_sum fun v hv => ?_
      have hv_lt : outDeg G S v < k := (Finset.mem_filter.mp (hBsub hv)).2
      have hmono : outDeg G B v ≤ outDeg G S v :=
        Finset.card_le_card (Finset.filter_subset_filter _ hBS)
      omega
    rw [Finset.sum_const, hBcard, smul_eq_mul] at hle
    omega
  rw [two_mul_sum_outDeg hT B, hBcard] at hsum_le
  have h1 : 2 * (2 * k * (k - 1)) < 2 * k * (2 * k - 1) := by
    have hmul : 2 * (k - 1) < 2 * k - 1 := by omega
    calc 2 * (2 * k * (k - 1)) = 2 * k * (2 * (k - 1)) := by ring
      _ < 2 * k * (2 * k - 1) := Nat.mul_lt_mul_of_pos_left hmul (by omega)
  omega

omit [Fintype V] in
/-- Pick `m` vertices of largest out-degree in `S`; each has `2 * outDeg ≥ |S| - m`. -/
private lemma exists_top_outDeg_subset {G : Digraph V} [DecidableRel G.Adj] (hT : IsTournament G)
    (S : Finset V) {m : ℕ} (hm : m ≤ S.card) :
    ∃ X ⊆ S, X.card = m ∧ ∀ x ∈ X, S.card - m ≤ 2 * outDeg G S x := by
  induction m with
  | zero => exact ⟨∅, Finset.empty_subset _, Finset.card_empty, fun x hx => by simp at hx⟩
  | succ m ih =>
    -- Pick the (m+1) vertices greedily by always pulling out a max outDeg vertex of S \ X
    -- Better: directly prove by induction on m that we can pick X of size m with
    -- ∀ x ∈ X, ∀ u ∈ S \ X, outDeg G S u ≤ outDeg G S x!
    suffices hgen : ∀ r : ℕ, r ≤ S.card →
        ∃ X ⊆ S, X.card = r ∧ ∀ x ∈ X, ∀ u ∈ S \ X, outDeg G S u ≤ outDeg G S x by
      obtain ⟨X, hXS, hXcard, hXmax⟩ := hgen (m + 1) hm
      refine ⟨X, hXS, hXcard, fun x hx => ?_⟩
      let T' := insert x (S \ X)
      have hT'_sub : T' ⊆ S := Finset.insert_subset (hXS hx) Finset.sdiff_subset
      have hx_nsdiff : x ∉ S \ X := fun h => (Finset.mem_sdiff.mp h).2 hx
      have hT'_card : T'.card = S.card - m := by
        rw [Finset.card_insert_of_notMem hx_nsdiff, Finset.card_sdiff_of_subset hXS, hXcard]
        omega
      obtain ⟨u, huT', hu_deg⟩ := exists_large_outDeg hT (S := T') ⟨x, Finset.mem_insert_self _ _⟩
      have hu_le : outDeg G T' u ≤ outDeg G S x := by
        have h1 : outDeg G T' u ≤ outDeg G S u :=
          Finset.card_le_card (Finset.filter_subset_filter _ hT'_sub)
        rcases Finset.mem_insert.mp huT' with rfl | hu_sd
        · exact h1
        · exact h1.trans (hXmax x hx u hu_sd)
      rw [hT'_card] at hu_deg
      omega
    intro r hr
    induction r with
    | zero => exact ⟨∅, Finset.empty_subset _, Finset.card_empty, fun x hx => by simp at hx⟩
    | succ r ihr =>
      obtain ⟨X, hXS, hXcard, hXmax⟩ := ihr (by omega)
      have hne : (S \ X).Nonempty := Finset.card_pos.mp (by
        rw [Finset.card_sdiff_of_subset hXS, hXcard]; omega)
      obtain ⟨v, hv_sd, hv_max⟩ := Finset.exists_max_image (S \ X) (outDeg G S) hne
      have hv_nX : v ∉ X := (Finset.mem_sdiff.mp hv_sd).2
      refine ⟨insert v X, Finset.insert_subset (Finset.sdiff_subset hv_sd) hXS,
        by rw [Finset.card_insert_of_notMem hv_nX, hXcard], fun x hx u hu => ?_⟩
      have hu_sd : u ∈ S \ X := Finset.mem_sdiff.mpr
        ⟨(Finset.mem_sdiff.mp hu).1, fun h => (Finset.mem_sdiff.mp hu).2 (Finset.mem_insert_of_mem h)⟩
      rcases Finset.mem_insert.mp hx with rfl | hxX
      · exact hv_max u hu_sd
      · exact hXmax x hxX u hu_sd

omit [Fintype V] in
private lemma exists_top_inDeg_subset {G : Digraph V} [DecidableRel G.Adj] (hT : IsTournament G)
    (S : Finset V) {m : ℕ} (hm : m ≤ S.card) :
    ∃ Y ⊆ S, Y.card = m ∧ ∀ y ∈ Y, S.card - m ≤ 2 * inDeg G S y := by
  simpa only [outDeg_op_eq_inDeg] using
    exists_top_outDeg_subset (isTournament_op hT) S hm

omit [Fintype V] in
/-- A `g`-strong tournament on `S` has minimum out-degree and in-degree at least `g`. -/
private lemma min_outDeg_of_isKStrongOn {G : Digraph V} [DecidableRel G.Adj] (hT : IsTournament G)
    {S : Finset V} {g : ℕ} (hstrong : IsKStrongOn G (S : Set V) g) {v : V} (hv : v ∈ S) :
    g ≤ outDeg G S v := by
  by_contra hlt
  push Not at hlt
  let X := outNbr G S v
  have hXlt : X.card < g := hlt
  have hS_gt : g < S.card := by simpa [Set.ncard_coe_finset] using hstrong.1
  have hv_nX : v ∉ X := by simp [X, outNbr, hT.1 v]
  have hrem : (S \ insert v X).Nonempty := Finset.card_pos.mp (by
    have hsub : insert v X ⊆ S := Finset.insert_subset hv (Finset.filter_subset _ _)
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_insert_of_notMem hv_nX]
    omega)
  obtain ⟨w, hw⟩ := hrem
  rw [Finset.mem_sdiff, Finset.mem_insert, not_or] at hw
  have hv_mem : v ∈ (S : Set V) \ (X : Set V) := ⟨hv, hv_nX⟩
  have hw_mem : w ∈ (S : Set V) \ (X : Set V) := ⟨hw.1, hw.2.2⟩
  have hwalk := hstrong.2 X hXlt v hv_mem w hw_mem
  cases hwalk using Relation.ReflTransGen.head_induction_on with
  | refl => exact hw.2.1 rfl
  | @head a b hab _ _ =>
    exact hab.2.1.2 (Finset.mem_filter.mpr ⟨hab.2.1.1, hab.2.2⟩)

omit [Fintype V] in
private lemma min_inDeg_of_isKStrongOn {G : Digraph V} [DecidableRel G.Adj] (hT : IsTournament G)
    {S : Finset V} {g : ℕ} (hstrong : IsKStrongOn G (S : Set V) g) {v : V} (hv : v ∈ S) :
    g ≤ inDeg G S v := by
  have hstrong_op : IsKStrongOn (opDigraph G) (S : Set V) g := isKStrongOn_op_iff.mpr hstrong
  rw [← outDeg_op_eq_inDeg]
  exact min_outDeg_of_isKStrongOn (isTournament_op hT) hstrong_op hv

/-- Pokrovskiy Lemma 2.1 (with constant `13`): any tournament on `S` with `13 * m ≤ |S|`
contains disjoint sets `X, Y ⊆ S` of size `m` such that every bijection `X → Y` can be realized
by `m` vertex-disjoint directed paths in `S`. -/
private lemma pokrovskiy_large_linkage {G : Digraph V} [DecidableRel G.Adj] (hT : IsTournament G)
    (S : Finset V) {m : ℕ} (hm : 13 * m ≤ S.card) :
    ∃ X Y : Finset V, X ⊆ S ∧ Y ⊆ S ∧ Disjoint X Y ∧ X.card = m ∧ Y.card = m ∧
      ∀ (x y : Fin m → V), Function.Injective x → Function.Injective y →
        (∀ i, x i ∈ X) → (∀ i, y i ∈ Y) →
        ∃ Ps : Fin m → List V,
          (∀ i, IsDirPathBetween G.Adj (x i) (y i) (Ps i) ∧ ∀ w ∈ Ps i, w ∈ S) ∧
          (∀ i j, i ≠ j → Disjoint (Ps i).toFinset (Ps j).toFinset) := by
  classical
  cases m with
  | zero =>
    refine ⟨∅, ∅, Finset.empty_subset _, Finset.empty_subset _, Finset.disjoint_empty_left _,
      rfl, rfl, fun _ _ _ _ _ _ => ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩⟩
  | succ m' =>
    let m := m' + 1
    have hm_pos : 1 ≤ m := Nat.succ_pos m'
    obtain ⟨X, hXS, hXcard, hXdeg⟩ := exists_top_outDeg_subset hT S (by omega : m ≤ S.card)
    have hSX_card : (S \ X).card = S.card - m := by
      rw [Finset.card_sdiff_of_subset hXS, hXcard]
    obtain ⟨Y, hYSX, hYcard, hYdeg_sub⟩ := exists_top_inDeg_subset hT (S \ X) (by omega : m ≤ (S \ X).card)
    have hYS : Y ⊆ S := hYSX.trans Finset.sdiff_subset
    have hXY_disj : Disjoint X Y := Finset.disjoint_of_subset_right hYSX disjoint_sdiff_self_right
    have hYdeg : ∀ y ∈ Y, S.card - 2 * m ≤ 2 * inDeg G S y := fun y hy => by
      have h1 := hYdeg_sub y hy
      have h2 : inDeg G (S \ X) y ≤ inDeg G S y :=
        Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)
      omega
    -- Check if there is a pair (x ∈ X, y ∈ Y) with a large complete bipartite directed cut (W' → U')
    let goodPair := fun (x y : V) =>
      let I := outNbr G S x ∩ inNbr G S y
      let U := insert x (outNbr G S x) \ insert y (inNbr G S y)
      let W := insert y (inNbr G S y) \ insert x (outNbr G S x)
      ∃ M : Finset (V × V),
        (∀ p ∈ M, p.1 ∈ U ∧ p.2 ∈ W ∧ G.Adj p.1 p.2) ∧
        (M : Set (V × V)).Pairwise (fun p q => p.1 ≠ q.1 ∧ p.2 ≠ q.2) ∧
        4 * m + 1 ≤ I.card + M.card
    by_cases hall_good : ∀ x ∈ X, ∀ y ∈ Y, goodPair x y
    · -- Case A: every (x, y) ∈ X × Y has ≥ 4m+1 internally disjoint paths of length ≤ 3 in S
      refine ⟨X, Y, hXS, hYS, hXY_disj, hXcard, hYcard, fun x y hx_inj hy_inj hxX hyY => ?_⟩
      -- Helper: for any x ∈ X, y ∈ Y and any forbidden set F ⊆ S \ {x, y} of size ≤ 4m,
      -- there is a path from x to y of length ≤ 3 in S whose internal vertices avoid F.
      have hfind_one : ∀ (a b : V), a ∈ X → b ∈ Y →
          ∀ F : Finset V, F.card ≤ 4 * m →
            ∃ P : List V, IsDirPathBetween G.Adj a b P ∧ P.length ≤ 4 ∧
              (∀ w ∈ P, w ∈ S) ∧ ∀ w ∈ P, w ≠ a → w ≠ b → w ∉ F := by
        intro a b haX hbY F hFcard
        have hab_ne : a ≠ b := fun h => Finset.disjoint_left.mp hXY_disj haX (h ▸ hbY)
        obtain ⟨M, hM_mem, hM_disj, hM_big⟩ := hall_good a haX b hbY
        let I := outNbr G S a ∩ inNbr G S b
        let U := insert a (outNbr G S a) \ insert b (inNbr G S b)
        let W := insert b (inNbr G S b) \ insert a (outNbr G S a)
        -- First check if some w ∈ I \ F exists
        by_cases hIF : (I \ F).Nonempty
        · obtain ⟨w, hw⟩ := hIF
          rw [Finset.mem_sdiff, Finset.mem_inter] at hw
          have hw1 := Finset.mem_filter.mp hw.1.1
          have hw2 := Finset.mem_filter.mp hw.1.2
          have hwa : w ≠ a := fun h => hT.1 a (h ▸ hw1.2)
          have hwb : w ≠ b := fun h => hT.1 b (h ▸ hw2.2)
          refine ⟨[a, w, b], ⟨⟨by simp, by simp [hwa.symm, hab_ne, hwb], fun i hi => ?_⟩,
            by simp, rfl, rfl⟩, by simp, ?_, ?_⟩
          · have hi' : i = 0 ∨ i = 1 := by simp at hi; omega
            rcases hi' with rfl | rfl
            · exact hw1.2
            · exact hw2.2
          · intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with rfl | rfl | rfl
            · exact hXS haX
            · exact hw1.1
            · exact hYS hbY
          · intro z hz hza hzb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with rfl | rfl | rfl
            · exact absurd rfl hza
            · exact hw.2
            · exact absurd rfl hzb
        · -- Every vertex of I lies in F; so at most |F| - |I| pairs of M can touch F (excluding {a, b})!
          have hI_sub_F : I ⊆ F := Finset.sdiff_eq_empty_iff_subset.mp (Finset.not_nonempty_iff_eq_empty.mp hIF)
          let F_rem := F \ I
          have hFrem_card : F_rem.card = F.card - I.card := Finset.card_sdiff_of_subset hI_sub_F
          -- Each z ∈ F_rem hits at most one pair p ∈ M (since U and W are disjoint and M is a matching!)
          have hUW_disj : Disjoint U W := by
            rw [Finset.disjoint_left]; intro z hz1 hz2
            exact (Finset.mem_sdiff.mp hz1).2 (Finset.mem_sdiff.mp hz2).1
          let badM := M.filter fun p => (p.1 ≠ a ∧ p.1 ∈ F_rem) ∨ (p.2 ≠ b ∧ p.2 ∈ F_rem)
          have hbad_le : badM.card ≤ F_rem.card := by
            -- Map each p ∈ badM to its hitting vertex in F_rem; this map is injective!
            have hex_hit : ∀ p ∈ badM, ∃ z ∈ F_rem, z = p.1 ∨ z = p.2 := by
              intro p hp
              rcases (Finset.mem_filter.mp hp).2 with ⟨_, h1⟩ | ⟨_, h2⟩
              · exact ⟨p.1, h1, Or.inl rfl⟩
              · exact ⟨p.2, h2, Or.inr rfl⟩
            let hit : V × V → V := fun p => if p.1 ≠ a ∧ p.1 ∈ F_rem then p.1 else p.2
            have hhit_mem : ∀ p ∈ badM, hit p ∈ F_rem := by
              intro p hp; dsimp only [hit]
              split_ifs with h1
              · exact h1.2
              · rcases (Finset.mem_filter.mp hp).2 with h | h
                · exact absurd h h1
                · exact h.2
            have hhit_inj : Set.InjOn hit (badM : Set (V × V)) := by
              intro p hp q hq heq
              by_contra hne
              have hpM := (Finset.mem_filter.mp hp).1
              have hqM := (Finset.mem_filter.mp hq).1
              have hp_mem := hM_mem p hpM
              have hq_mem := hM_mem q hqM
              have hpair := hM_disj hpM hqM hne
              dsimp only [hit] at heq
              split_ifs at heq with h1 h2 h2
              · exact hpair.1 heq
              · exact Finset.disjoint_left.mp hUW_disj hp_mem.1 (heq ▸ hq_mem.2.1)
              · exact Finset.disjoint_left.mp hUW_disj hq_mem.1 (heq.symm ▸ hp_mem.2.1)
              · exact hpair.2 heq
            calc badM.card = (badM.image hit).card := (Finset.card_image_of_injOn hhit_inj).symm
              _ ≤ F_rem.card := Finset.card_le_card (Finset.image_subset_iff.mpr hhit_mem)
          have hgoodM : (M \ badM).Nonempty := Finset.card_pos.mp (by
            have hsub : badM ⊆ M := Finset.filter_subset _ _
            rw [Finset.card_sdiff_of_subset hsub]
            change 4 * m + 1 ≤ I.card + M.card at hM_big
            have := Finset.card_le_card hI_sub_F
            omega)
          obtain ⟨⟨u, w⟩, huw⟩ := hgoodM
          rw [Finset.mem_sdiff] at huw
          have huwM := hM_mem (u, w) huw.1
          have hnotbad : ¬ ((u ≠ a ∧ u ∈ F_rem) ∨ (w ≠ b ∧ w ∈ F_rem)) := fun h =>
            huw.2 (Finset.mem_filter.mpr ⟨huw.1, h⟩)
          have hu_nI : u ∉ I := fun h =>
            (Finset.mem_sdiff.mp huwM.1).2 (Finset.mem_insert_of_mem (Finset.mem_inter.mp h).2)
          have hw_nI : w ∉ I := fun h =>
            (Finset.mem_sdiff.mp huwM.2.1).2 (Finset.mem_insert_of_mem (Finset.mem_inter.mp h).1)
          have hu_nF : u ≠ a → u ∉ F := fun hne hF =>
            hnotbad (Or.inl ⟨hne, Finset.mem_sdiff.mpr ⟨hF, hu_nI⟩⟩)
          have hw_nF : w ≠ b → w ∉ F := fun hne hF =>
            hnotbad (Or.inr ⟨hne, Finset.mem_sdiff.mpr ⟨hF, hw_nI⟩⟩)
          have hu_nb : u ≠ b := fun h =>
            (Finset.mem_sdiff.mp huwM.1).2 (by rw [h]; exact Finset.mem_insert_self b _)
          have hw_na : w ≠ a := fun h =>
            (Finset.mem_sdiff.mp huwM.2.1).2 (by rw [h]; exact Finset.mem_insert_self a _)
          have huw_ne : u ≠ w := fun h => hT.1 u (h ▸ huwM.2.2)
          have huS : u ∈ S := by
            rcases Finset.mem_insert.mp (Finset.mem_sdiff.mp huwM.1).1 with rfl | h
            · exact hXS haX
            · exact (Finset.mem_filter.mp h).1
          have hwS : w ∈ S := by
            rcases Finset.mem_insert.mp (Finset.mem_sdiff.mp huwM.2.1).1 with rfl | h
            · exact hYS hbY
            · exact (Finset.mem_filter.mp h).1
          by_cases hua : u = a <;> by_cases hwb : w = b
          · -- Path [a, b]
            have hab_adj : G.Adj a b := by rw [← hua, ← hwb]; exact huwM.2.2
            refine ⟨[a, b], ⟨⟨by simp, by simp [hab_ne], fun i hi => ?_⟩, by simp, rfl, rfl⟩,
              by simp, fun z hz => by simp at hz; rcases hz with rfl | rfl; exact hXS haX; exact hYS hbY,
              fun z hz h1 h2 => by simp at hz; tauto⟩
            have : i = 0 := by simp at hi; omega
            subst this; exact hab_adj
          · -- Path [a, w, b]
            have haw_adj : G.Adj a w := by rw [← hua]; exact huwM.2.2
            have hwb_adj : G.Adj w b := by
              rcases Finset.mem_insert.mp (Finset.mem_sdiff.mp huwM.2.1).1 with h | h
              · exact absurd h hwb
              · exact (Finset.mem_filter.mp h).2
            refine ⟨[a, w, b], ⟨⟨by simp, by simp [hw_na.symm, hab_ne, hwb], fun i hi => ?_⟩,
              by simp, rfl, rfl⟩, by simp,
              fun z hz => by simp at hz; rcases hz with rfl | rfl | rfl; exact hXS haX; exact hwS; exact hYS hbY,
              fun z hz h1 h2 => by simp at hz; rcases hz with rfl | rfl | rfl; exact absurd rfl h1; exact hw_nF hwb; exact absurd rfl h2⟩
            have : i = 0 ∨ i = 1 := by simp at hi; omega
            rcases this with rfl | rfl; exact haw_adj; exact hwb_adj
          · -- Path [a, u, b]
            have hub_adj : G.Adj u b := by rw [← hwb]; exact huwM.2.2
            have hau_adj : G.Adj a u := by
              rcases Finset.mem_insert.mp (Finset.mem_sdiff.mp huwM.1).1 with h | h
              · exact absurd h hua
              · exact (Finset.mem_filter.mp h).2
            refine ⟨[a, u, b], ⟨⟨by simp, by simp [Ne.symm hua, hab_ne, hu_nb], fun i hi => ?_⟩,
              by simp, rfl, rfl⟩, by simp,
              fun z hz => by simp at hz; rcases hz with rfl | rfl | rfl; exact hXS haX; exact huS; exact hYS hbY,
              fun z hz h1 h2 => by simp at hz; rcases hz with rfl | rfl | rfl; exact absurd rfl h1; exact hu_nF hua; exact absurd rfl h2⟩
            have : i = 0 ∨ i = 1 := by simp at hi; omega
            rcases this with rfl | rfl; exact hau_adj; exact hub_adj
          · -- Path [a, u, w, b]
            have hau_adj : G.Adj a u := by
              rcases Finset.mem_insert.mp (Finset.mem_sdiff.mp huwM.1).1 with h | h
              · exact absurd h hua
              · exact (Finset.mem_filter.mp h).2
            have hwb_adj : G.Adj w b := by
              rcases Finset.mem_insert.mp (Finset.mem_sdiff.mp huwM.2.1).1 with h | h
              · exact absurd h hwb
              · exact (Finset.mem_filter.mp h).2
            refine ⟨[a, u, w, b], ⟨⟨by simp, by simp [Ne.symm hua, hw_na.symm, hab_ne, huw_ne, hu_nb, hwb],
              fun i hi => ?_⟩, by simp, rfl, rfl⟩, by simp,
              fun z hz => by simp at hz; rcases hz with rfl | rfl | rfl | rfl; exact hXS haX; exact huS; exact hwS; exact hYS hbY,
              fun z hz h1 h2 => by
                simp at hz; rcases hz with rfl | rfl | rfl | rfl
                · exact absurd rfl h1
                · exact hu_nF hua
                · exact hw_nF hwb
                · exact absurd rfl h2⟩
            have : i = 0 ∨ i = 1 ∨ i = 2 := by simp at hi; omega
            rcases this with rfl | rfl | rfl; exact hau_adj; exact huwM.2.2; exact hwb_adj
      -- Greedily build P_0, ..., P_{m-1} avoiding X ∪ Y (other endpoints) and previous paths
      have hbuild : ∀ (r : ℕ) (hr : r ≤ m),
          ∃ Ps : Fin r → List V,
            (∀ i : Fin r, IsDirPathBetween G.Adj (x ⟨i.val, by omega⟩) (y ⟨i.val, by omega⟩) (Ps i) ∧
              (Ps i).length ≤ 4 ∧
              (∀ w ∈ Ps i, w ∈ S) ∧
              (∀ w ∈ Ps i, w ≠ x ⟨i.val, by omega⟩ → w ≠ y ⟨i.val, by omega⟩ → w ∉ X ∪ Y)) ∧
            (∀ i j : Fin r, i ≠ j → Disjoint (Ps i).toFinset (Ps j).toFinset) := by
        intro r
        induction r with
        | zero =>
          intro _; exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
        | succ r ih =>
          intro hr
          obtain ⟨Ps, hPs, hPs_disj⟩ := ih (by omega)
          let F : Finset V := (X ∪ Y) ∪ (Finset.univ.biUnion fun i : Fin r => (Ps i).toFinset)
          have hF_card : F.card ≤ 4 * m := by
            have h1 : (X ∪ Y).card ≤ 2 * m := by
              rw [Finset.card_union_of_disjoint hXY_disj, hXcard, hYcard]; omega
            -- Each Ps i contributes at most 2 internal vertices outside X ∪ Y!
            let intV : Finset V := Finset.univ.biUnion fun i : Fin r =>
              (Ps i).toFinset \ (X ∪ Y)
            have hF_eq : F ⊆ (X ∪ Y) ∪ intV := by
              intro z hz
              rcases Finset.mem_union.mp hz with h | h
              · exact Finset.mem_union_left _ h
              · by_cases hXY : z ∈ X ∪ Y
                · exact Finset.mem_union_left _ hXY
                · rw [Finset.mem_biUnion] at h
                  obtain ⟨i, _, hi⟩ := h
                  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨hi, hXY⟩⟩)
            have hint_le : intV.card ≤ 2 * r := by
              calc intV.card ≤ ∑ i : Fin r, ((Ps i).toFinset \ (X ∪ Y)).card := Finset.card_biUnion_le
                _ ≤ ∑ _i : Fin r, 2 := by
                  refine Finset.sum_le_sum fun i _ => ?_
                  have hlen := (hPs i).2.1
                  have hhead_mem : x ⟨i.val, by omega⟩ ∈ (Ps i).toFinset := by
                    obtain ⟨_, hne, hh, _⟩ := (hPs i).1
                    exact List.mem_toFinset.mpr (hh ▸ List.head_mem hne)
                  have hlast_mem : y ⟨i.val, by omega⟩ ∈ (Ps i).toFinset := by
                    obtain ⟨_, hne, _, hl⟩ := (hPs i).1
                    exact List.mem_toFinset.mpr (hl ▸ List.getLast_mem hne)
                  have hne_xy : x ⟨i.val, by omega⟩ ≠ y ⟨i.val, by omega⟩ := fun h =>
                    Finset.disjoint_left.mp hXY_disj (hxX _) (h ▸ hyY _)
                  have hpair_sub : ({x ⟨i.val, by omega⟩, y ⟨i.val, by omega⟩} : Finset V) ⊆
                      (Ps i).toFinset ∩ (X ∪ Y) := by
                    intro z hz
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                    rcases hz with rfl | rfl
                    · exact Finset.mem_inter.mpr ⟨hhead_mem, Finset.mem_union_left _ (hxX _)⟩
                    · exact Finset.mem_inter.mpr ⟨hlast_mem, Finset.mem_union_right _ (hyY _)⟩
                  have hpair_c : 2 ≤ ((Ps i).toFinset ∩ (X ∪ Y)).card := by
                    have h2 : ({x ⟨i.val, by omega⟩, y ⟨i.val, by omega⟩} : Finset V).card = 2 :=
                      Finset.card_pair hne_xy
                    exact h2 ▸ Finset.card_le_card hpair_sub
                  have htot : (Ps i).toFinset.card ≤ 4 := (List.toFinset_card_le _).trans hlen
                  have hsd := Finset.card_sdiff_add_card_inter (Ps i).toFinset (X ∪ Y)
                  omega
                _ = 2 * r := by simp [Nat.mul_comm]
            calc F.card ≤ ((X ∪ Y) ∪ intV).card := Finset.card_le_card hF_eq
              _ ≤ (X ∪ Y).card + intV.card := Finset.card_union_le _ _
              _ ≤ 2 * m + 2 * r := by omega
              _ ≤ 4 * m := by omega
          obtain ⟨Pnew, hPnew_bet, hPnew_len, hPnew_S, hPnew_F⟩ :=
            hfind_one (x ⟨r, hr⟩) (y ⟨r, hr⟩) (hxX _) (hyY _) F hF_card
          refine ⟨fun i => if hi : i.val < r then Ps ⟨i.val, hi⟩ else Pnew, ?_, ?_⟩
          · intro i
            by_cases hi : i.val < r
            · simp only [hi, ↓reduceDIte]
              exact hPs ⟨i.val, hi⟩
            · have hi_eq : i.val = r := by omega
              simp only [hi, ↓reduceDIte]
              have hxeq : x ⟨i.val, by omega⟩ = x ⟨r, hr⟩ := congrArg x (Fin.ext hi_eq)
              have hyeq : y ⟨i.val, by omega⟩ = y ⟨r, hr⟩ := congrArg y (Fin.ext hi_eq)
              rw [hxeq, hyeq]
              exact ⟨hPnew_bet, hPnew_len, hPnew_S, fun w hw h1 h2 hXY =>
                hPnew_F w hw h1 h2 (Finset.mem_union_left _ hXY)⟩
          · intro i j hij
            by_cases hi : i.val < r <;> by_cases hj : j.val < r
            · simp only [hi, hj, ↓reduceDIte]
              exact hPs_disj ⟨i.val, hi⟩ ⟨j.val, hj⟩ (fun h => hij (Fin.ext (congrArg (Fin.val : Fin r → ℕ) h)))
            · simp only [hi, hj, ↓reduceDIte]
              rw [Finset.disjoint_right]
              intro w hw_new hw_old
              rw [List.mem_toFinset] at hw_new
              by_cases hwx : w = x ⟨r, hr⟩
              · subst hwx
                have hwx_ne_i : x ⟨r, hr⟩ ≠ x ⟨i.val, by omega⟩ := fun h => by
                  have : r = i.val := congrArg Fin.val (hx_inj h); omega
                have hwy_ne_i : x ⟨r, hr⟩ ≠ y ⟨i.val, by omega⟩ := fun h =>
                  Finset.disjoint_left.mp hXY_disj (hxX _) (h ▸ hyY _)
                exact (hPs ⟨i.val, hi⟩).2.2.2 _ (List.mem_toFinset.mp hw_old) hwx_ne_i hwy_ne_i
                  (Finset.mem_union_left _ (hxX _))
              · by_cases hwy : w = y ⟨r, hr⟩
                · subst hwy
                  have hwx_ne_i : y ⟨r, hr⟩ ≠ x ⟨i.val, by omega⟩ := fun h =>
                    Finset.disjoint_left.mp hXY_disj (h ▸ hxX _) (hyY _)
                  have hwy_ne_i : y ⟨r, hr⟩ ≠ y ⟨i.val, by omega⟩ := fun h => by
                    have : r = i.val := congrArg Fin.val (hy_inj h); omega
                  exact (hPs ⟨i.val, hi⟩).2.2.2 _ (List.mem_toFinset.mp hw_old) hwx_ne_i hwy_ne_i
                    (Finset.mem_union_right _ (hyY _))
                · exact hPnew_F w hw_new hwx hwy
                    (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨⟨i.val, hi⟩, Finset.mem_univ _, hw_old⟩))
            · simp only [hi, hj, ↓reduceDIte]
              rw [Finset.disjoint_left]
              intro w hw_new hw_old
              rw [List.mem_toFinset] at hw_new
              by_cases hwx : w = x ⟨r, hr⟩
              · subst hwx
                have hwx_ne_j : x ⟨r, hr⟩ ≠ x ⟨j.val, by omega⟩ := fun h => by
                  have : r = j.val := congrArg Fin.val (hx_inj h); omega
                have hwy_ne_j : x ⟨r, hr⟩ ≠ y ⟨j.val, by omega⟩ := fun h =>
                  Finset.disjoint_left.mp hXY_disj (hxX _) (h ▸ hyY _)
                exact (hPs ⟨j.val, hj⟩).2.2.2 _ (List.mem_toFinset.mp hw_old) hwx_ne_j hwy_ne_j
                  (Finset.mem_union_left _ (hxX _))
              · by_cases hwy : w = y ⟨r, hr⟩
                · subst hwy
                  have hwx_ne_j : y ⟨r, hr⟩ ≠ x ⟨j.val, by omega⟩ := fun h =>
                    Finset.disjoint_left.mp hXY_disj (h ▸ hxX _) (hyY _)
                  have hwy_ne_j : y ⟨r, hr⟩ ≠ y ⟨j.val, by omega⟩ := fun h => by
                    have : r = j.val := congrArg Fin.val (hy_inj h); omega
                  exact (hPs ⟨j.val, hj⟩).2.2.2 _ (List.mem_toFinset.mp hw_old) hwx_ne_j hwy_ne_j
                    (Finset.mem_union_right _ (hyY _))
                · exact hPnew_F w hw_new hwx hwy
                    (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨⟨j.val, hj⟩, Finset.mem_univ _, hw_old⟩))
            · exact absurd (Fin.ext (by omega)) hij
      obtain ⟨Ps, hPs, hPs_disj⟩ := hbuild m le_rfl
      exact ⟨Ps, fun i => ⟨(hPs i).1, (hPs i).2.2.1⟩, hPs_disj⟩
    · -- Case B: some (a, b) ∈ X × Y fails goodPair -> take maximum matching M; W' → U' is a complete bipartite digraph!
      push Not at hall_good
      obtain ⟨a, haX, b, hbY, hnot_good⟩ := hall_good
      let I := outNbr G S a ∩ inNbr G S b
      let U := insert a (outNbr G S a) \ insert b (inNbr G S b)
      let W := insert b (inNbr G S b) \ insert a (outNbr G S a)
      let validM := fun M : Finset (V × V) =>
        (∀ p ∈ M, p.1 ∈ U ∧ p.2 ∈ W ∧ G.Adj p.1 p.2) ∧
        (M : Set (V × V)).Pairwise (fun p q => p.1 ≠ q.1 ∧ p.2 ≠ q.2)
      let allM : Finset (Finset (V × V)) := (U ×ˢ W).powerset.filter validM
      have hempty_in : (∅ : Finset (V × V)) ∈ allM := by
        simp [allM, validM]
      obtain ⟨M, hM_in, hM_max⟩ := Finset.exists_max_image allM Finset.card ⟨∅, hempty_in⟩
      have hM_valid : validM M := (Finset.mem_filter.mp hM_in).2
      have hM_lt : I.card + M.card < 4 * m + 1 := by
        by_contra hge; push Not at hge
        exact hnot_good ⟨M, hM_valid.1, hM_valid.2, hge⟩
      let U' := U \ M.image Prod.fst
      let W' := W \ M.image Prod.snd
      have hU_sub_S : U ⊆ S := by
        intro z hz
        rcases Finset.mem_insert.mp (Finset.mem_sdiff.mp hz).1 with rfl | h
        · exact hXS haX
        · exact (Finset.mem_filter.mp h).1
      have hW_sub_S : W ⊆ S := by
        intro z hz
        rcases Finset.mem_insert.mp (Finset.mem_sdiff.mp hz).1 with rfl | h
        · exact hYS hbY
        · exact (Finset.mem_filter.mp h).1
      -- Bound |U'| and |W'| from below
      have hU_card : outDeg G S a ≤ U.card + I.card + 1 := by
        have h1 : (insert a (outNbr G S a) ∩ insert b (inNbr G S b)).card ≤ I.card + 2 := by
          have hsub : insert a (outNbr G S a) ∩ insert b (inNbr G S b) ⊆ insert a (insert b I) := by
            intro z hz
            simp only [Finset.mem_inter, Finset.mem_insert, I] at hz ⊢
            tauto
          calc (insert a (outNbr G S a) ∩ insert b (inNbr G S b)).card
              ≤ (insert a (insert b I)).card := Finset.card_le_card hsub
            _ ≤ (insert b I).card + 1 := Finset.card_insert_le _ _
            _ ≤ I.card + 2 := by have := Finset.card_insert_le b I; omega
        have ha_nout : a ∉ outNbr G S a := by simp [outNbr, hT.1 a]
        have hsd := Finset.card_sdiff_add_card_inter (insert a (outNbr G S a)) (insert b (inNbr G S b))
        rw [Finset.card_insert_of_notMem ha_nout] at hsd
        change U.card + (insert a (outNbr G S a) ∩ insert b (inNbr G S b)).card = outDeg G S a + 1 at hsd
        omega
      have hW_card : inDeg G S b ≤ W.card + I.card + 1 := by
        have h1 : (insert b (inNbr G S b) ∩ insert a (outNbr G S a)).card ≤ I.card + 2 := by
          have hsub : insert b (inNbr G S b) ∩ insert a (outNbr G S a) ⊆ insert a (insert b I) := by
            intro z hz
            simp only [Finset.mem_inter, Finset.mem_insert, I] at hz ⊢
            tauto
          calc (insert b (inNbr G S b) ∩ insert a (outNbr G S a)).card
              ≤ (insert a (insert b I)).card := Finset.card_le_card hsub
            _ ≤ (insert b I).card + 1 := Finset.card_insert_le _ _
            _ ≤ I.card + 2 := by have := Finset.card_insert_le b I; omega
        have hb_nin : b ∉ inNbr G S b := by simp [inNbr, hT.1 b]
        have hsd := Finset.card_sdiff_add_card_inter (insert b (inNbr G S b)) (insert a (outNbr G S a))
        rw [Finset.card_insert_of_notMem hb_nin] at hsd
        change W.card + (insert b (inNbr G S b) ∩ insert a (outNbr G S a)).card = inDeg G S b + 1 at hsd
        omega
      have hU'_ge : m ≤ U'.card := by
        have h1 : (M.image Prod.fst).card ≤ M.card := Finset.card_image_le
        have hsd := Finset.card_sdiff_add_card_inter U (M.image Prod.fst)
        change U'.card + (U ∩ M.image Prod.fst).card = U.card at hsd
        have hle : (U ∩ M.image Prod.fst).card ≤ (M.image Prod.fst).card :=
          Finset.card_le_card Finset.inter_subset_right
        have hdeg := hXdeg a haX
        omega
      have hW'_ge : m ≤ W'.card := by
        have h1 : (M.image Prod.snd).card ≤ M.card := Finset.card_image_le
        have hsd := Finset.card_sdiff_add_card_inter W (M.image Prod.snd)
        change W'.card + (W ∩ M.image Prod.snd).card = W.card at hsd
        have hle : (W ∩ M.image Prod.snd).card ≤ (M.image Prod.snd).card :=
          Finset.card_le_card Finset.inter_subset_right
        have hdeg := hYdeg b hbY
        omega
      -- Every edge between U' and W' goes from W' to U' (by maximality of M!)
      have hUW'_disj : Disjoint W' U' := by
        rw [Finset.disjoint_left]; intro z hz1 hz2
        exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz1).1).2
          (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz2).1).1
      have hW'_to_U' : ∀ w ∈ W', ∀ u ∈ U', G.Adj w u := by
        intro w hw u hu
        have hwu_ne : w ≠ u := fun h => Finset.disjoint_left.mp hUW'_disj hw (h ▸ hu)
        by_contra hnot
        have huw : G.Adj u w := not_not.mp fun h => hnot ((hT.2 w u hwu_ne).mpr h)
        have huU : u ∈ U := (Finset.mem_sdiff.mp hu).1
        have hwW : w ∈ W := (Finset.mem_sdiff.mp hw).1
        have hu_nM : ∀ p ∈ M, p.1 ≠ u := fun p hp h =>
          (Finset.mem_sdiff.mp hu).2 (Finset.mem_image.mpr ⟨p, hp, h⟩)
        have hw_nM : ∀ p ∈ M, p.2 ≠ w := fun p hp h =>
          (Finset.mem_sdiff.mp hw).2 (Finset.mem_image.mpr ⟨p, hp, h⟩)
        have huw_nM : (u, w) ∉ M := fun h => hu_nM (u, w) h rfl
        have hM'_in : insert (u, w) M ∈ allM := by
          rw [Finset.mem_filter, Finset.mem_powerset]
          refine ⟨Finset.insert_subset (Finset.mem_product.mpr ⟨huU, hwW⟩)
              (Finset.mem_powerset.mp (Finset.mem_filter.mp hM_in).1), ?_, ?_⟩
          · intro p hp
            rcases Finset.mem_insert.mp hp with rfl | hpM
            · exact ⟨huU, hwW, huw⟩
            · exact hM_valid.1 p hpM
          · intro p hp q hq hpq
            simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hp hq
            rcases hp with rfl | hpM <;> rcases hq with rfl | hqM
            · exact absurd rfl hpq
            · exact ⟨(hu_nM q hqM).symm, (hw_nM q hqM).symm⟩
            · exact ⟨hu_nM p hpM, hw_nM p hpM⟩
            · exact hM_valid.2 hpM hqM hpq
        have hcard_le := hM_max (insert (u, w) M) hM'_in
        rw [Finset.card_insert_of_notMem huw_nM] at hcard_le
        omega
      obtain ⟨X', hX'W, hX'card⟩ := Finset.exists_subset_card_eq hW'_ge
      obtain ⟨Y', hY'U, hY'card⟩ := Finset.exists_subset_card_eq hU'_ge
      refine ⟨X', Y', hX'W.trans (Finset.sdiff_subset.trans hW_sub_S),
        hY'U.trans (Finset.sdiff_subset.trans hU_sub_S),
        Finset.disjoint_of_subset_left hX'W (Finset.disjoint_of_subset_right hY'U hUW'_disj), hX'card, hY'card,
        fun x y hx_inj hy_inj hxX' hyY' => ?_⟩
      refine ⟨fun i => [x i, y i], ?_, ?_⟩
      · intro i
        have hadj : G.Adj (x i) (y i) := hW'_to_U' (x i) (hX'W (hxX' i)) (y i) (hY'U (hyY' i))
        have hne : x i ≠ y i := fun h => hT.1 (x i) (h ▸ hadj)
        refine ⟨⟨⟨by simp, by simp [hne], fun idx hidx => ?_⟩, by simp, rfl, rfl⟩, ?_⟩
        · have : idx = 0 := by simp at hidx; omega
          subst this; exact hadj
        · intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl
          · exact hW_sub_S (Finset.sdiff_subset (hX'W (hxX' i)))
          · exact hU_sub_S (Finset.sdiff_subset (hY'U (hyY' i)))
      · intro i j hij
        rw [Finset.disjoint_left]
        intro z hz1 hz2
        simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
          Finset.mem_insert, Finset.mem_singleton] at hz1 hz2
        rcases hz1 with rfl | rfl <;> rcases hz2 with h | h
        · exact hij (hx_inj h)
        · exact Finset.disjoint_left.mp hUW'_disj (hX'W (hxX' i)) (h ▸ hY'U (hyY' j))
        · exact Finset.disjoint_left.mp hUW'_disj (hX'W (hxX' j)) (h.symm ▸ hY'U (hyY' i))
        · exact hij (hy_inj h)

omit [Fintype V] in
/-- Pokrovskiy Lemma 2.2 (size 2): in any tournament on `S` with `|S| ≥ 2`, there exist two
distinct vertices `v₁, v₂ ∈ S` with `G.Adj v₁ v₂` such that if `E` is the set of vertices in
`S \ {v₁, v₂}` not in-dominated by `{v₁, v₂}`, then every `u ∈ E` has `2 * |E| ≤ outDeg G S u`. -/
private lemma greedy_indom_two {G : Digraph V} [DecidableRel G.Adj] (hT : IsTournament G)
    {S : Finset V} (hS : 2 ≤ S.card) :
    ∃ v₁ v₂ : V, v₁ ∈ S ∧ v₂ ∈ S ∧ v₁ ≠ v₂ ∧ G.Adj v₁ v₂ ∧
      let E := S.filter fun w => w ≠ v₁ ∧ w ≠ v₂ ∧ G.Adj v₁ w ∧ G.Adj v₂ w
      ∀ u ∈ E, 2 * E.card ≤ outDeg G S u := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, haS, ha_max⟩ := Finset.exists_max_image S (inDeg G S) hne
  let E₁ := outNbr G S a
  by_cases hE1 : E₁.Nonempty
  · obtain ⟨b, hbE1, hb_max⟩ := Finset.exists_max_image E₁ (inDeg G E₁) hE1
    have hbS : b ∈ S := (Finset.mem_filter.mp hbE1).1
    have hab : G.Adj a b := (Finset.mem_filter.mp hbE1).2
    have hne_ab : a ≠ b := fun h => hT.1 a (h ▸ hab)
    refine ⟨a, b, haS, hbS, hne_ab, hab, ?_⟩
    dsimp only
    intro u hu
    have hu_filt := Finset.mem_filter.mp hu
    have huE1 : u ∈ E₁ := Finset.mem_filter.mpr ⟨hu_filt.1, hu_filt.2.2.2.1⟩
    -- outDeg G S u ≥ E₁.card
    have hout_ge : E₁.card ≤ outDeg G S u := by
      have h1 := outDeg_add_inDeg_eq hT haS
      have h2 := outDeg_add_inDeg_eq hT hu_filt.1
      have h3 := ha_max u hu_filt.1
      change E₁.card + inDeg G S a + 1 = S.card at h1
      omega
    -- 2 * E.card ≤ E₁.card (since b has max inDeg in E₁)
    have hE_eq : (S.filter fun w => w ≠ a ∧ w ≠ b ∧ G.Adj a w ∧ G.Adj b w) = outNbr G E₁ b := by
      ext w
      simp only [Finset.mem_filter, outNbr, E₁]
      constructor
      · rintro ⟨hwS, _, _, haw, hbw⟩; exact ⟨⟨hwS, haw⟩, hbw⟩
      · rintro ⟨⟨hwS, haw⟩, hbw⟩
        exact ⟨hwS, fun h => hT.1 a (h ▸ haw), fun h => hT.1 b (h ▸ hbw), haw, hbw⟩
    rw [hE_eq]
    obtain ⟨c, hcE1, hc_deg⟩ := exists_large_inDeg hT hE1
    have hb_in : E₁.card - 1 ≤ 2 * inDeg G E₁ b := hc_deg.trans (Nat.mul_le_mul_left 2 (hb_max c hcE1))
    have hb_sum := outDeg_add_inDeg_eq hT hbE1
    change (outNbr G E₁ b).card + inDeg G E₁ b + 1 = E₁.card at hb_sum
    omega
  · -- E₁ = ∅: a in-dominates all of S \ {a}! Pick any other vertex b ∈ S \ {a}; then G.Adj b a.
    have hne' : (S.erase a).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem haS]; omega)
    obtain ⟨b, hb_er⟩ := hne'
    have hbS : b ∈ S := Finset.mem_of_mem_erase hb_er
    have hba_ne : b ≠ a := Finset.ne_of_mem_erase hb_er
    have hba : G.Adj b a := by
      by_contra hnot
      have hab : G.Adj a b := not_not.mp fun h => hnot ((hT.2 b a hba_ne).mpr h)
      exact hE1 ⟨b, Finset.mem_filter.mpr ⟨hbS, hab⟩⟩
    refine ⟨b, a, hbS, haS, hba_ne, hba, ?_⟩
    dsimp only
    intro u hu
    have hu_filt := Finset.mem_filter.mp hu
    exact absurd ⟨u, Finset.mem_filter.mpr ⟨hu_filt.1, hu_filt.2.2.2.2⟩⟩ hE1

omit [Fintype V] in
/-- Dual of `greedy_indom_two`: two vertices `v₁, v₂ ∈ S` with `G.Adj v₁ v₂` (tail `v₁`, head `v₂`)
such that if `E` is the set of vertices in `S \ {v₁, v₂}` not out-dominated by `{v₁, v₂}`,
then every `u ∈ E` has `2 * |E| ≤ inDeg G S u`. -/
private lemma greedy_outdom_two {G : Digraph V} [DecidableRel G.Adj] (hT : IsTournament G)
    {S : Finset V} (hS : 2 ≤ S.card) :
    ∃ v₁ v₂ : V, v₁ ∈ S ∧ v₂ ∈ S ∧ v₁ ≠ v₂ ∧ G.Adj v₁ v₂ ∧
      let E := S.filter fun w => w ≠ v₁ ∧ w ≠ v₂ ∧ G.Adj w v₁ ∧ G.Adj w v₂
      ∀ u ∈ E, 2 * E.card ≤ inDeg G S u := by
  obtain ⟨a, b, ha, hb, hne, hab, hE⟩ := greedy_indom_two (isTournament_op hT) hS
  refine ⟨b, a, hb, ha, hne.symm, hab, ?_⟩
  dsimp only
  have hEq : (S.filter fun w => w ≠ b ∧ w ≠ a ∧ G.Adj w b ∧ G.Adj w a) =
      (S.filter fun w => w ≠ a ∧ w ≠ b ∧ (opDigraph G).Adj a w ∧ (opDigraph G).Adj b w) := by
    ext w; simp only [Finset.mem_filter]; dsimp only [opDigraph]; tauto
  rw [hEq]
  intro u hu
  rw [← outDeg_op_eq_inDeg]
  exact hE u hu

omit [Fintype V] in
/-- Repeatedly extract `r` pairwise disjoint 2-vertex partial greedy in-dominating sets from `S`. -/
private lemma extract_greedy_indoms {G : Digraph V} [DecidableRel G.Adj] (hT : IsTournament G)
    (S : Finset V) (r : ℕ) (hS : 2 * r ≤ S.card) :
    ∃ t h : Fin r → V,
      (∀ i, t i ∈ S ∧ h i ∈ S ∧ t i ≠ h i ∧ G.Adj (t i) (h i)) ∧
      (∀ i j, i ≠ j → Disjoint ({t i, h i} : Finset V) ({t j, h j} : Finset V)) ∧
      ∀ i : Fin r,
        let used := Finset.univ.biUnion fun j : Fin r => ({t j, h j} : Finset V)
        let E := (S \ used).filter fun w => G.Adj (t i) w ∧ G.Adj (h i) w
        ∀ u ∈ E, 2 * E.card ≤ outDeg G S u := by
  induction r generalizing S with
  | zero =>
    exact ⟨Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ r ih =>
    obtain ⟨v₁, v₂, hv1, hv2, hne, hadj, hE0⟩ := greedy_indom_two hT (by omega : 2 ≤ S.card)
    let S' := S \ {v₁, v₂}
    have hS'_card : S'.card = S.card - 2 := by
      have hsub : ({v₁, v₂} : Finset V) ⊆ S := by
        intro z hz; simp at hz; rcases hz with rfl | rfl; exact hv1; exact hv2
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_pair hne]
    obtain ⟨t', h', hmem', hdisj', hE'⟩ := ih S' (by omega)
    let t : Fin (r + 1) → V := Fin.cons v₁ t'
    let h : Fin (r + 1) → V := Fin.cons v₂ h'
    have hsub_S' : S' ⊆ S := Finset.sdiff_subset
    have hv_disj' : ∀ j : Fin r, Disjoint ({v₁, v₂} : Finset V) ({t' j, h' j} : Finset V) := by
      intro j
      rw [Finset.disjoint_right]
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact (Finset.mem_sdiff.mp (hmem' j).1).2
      · exact (Finset.mem_sdiff.mp (hmem' j).2.1).2
    refine ⟨t, h, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · exact ⟨hv1, hv2, hne, hadj⟩
      · intro j
        have hm := hmem' j
        exact ⟨hsub_S' hm.1, hsub_S' hm.2.1, hm.2.2⟩
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;> intro hij
      · exact absurd rfl hij
      · exact hv_disj' j'
      · exact (hv_disj' i').symm
      · exact hdisj' i' j' (fun heq => hij (congrArg Fin.succ heq))
    · intro i
      dsimp only
      let used := Finset.univ.biUnion fun j : Fin (r + 1) => ({t j, h j} : Finset V)
      have hused_eq : used = ({v₁, v₂} : Finset V) ∪
          (Finset.univ.biUnion fun j : Fin r => ({t' j, h' j} : Finset V)) := by
        ext z
        simp only [used, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
        constructor
        · rintro ⟨j, hj⟩
          revert hj
          refine Fin.cases ?_ (fun j' => ?_) j <;> intro hj
          · exact Or.inl (by simpa [t, h] using hj)
          · exact Or.inr ⟨j', by simpa [t, h] using hj⟩
        · rintro (hz | ⟨j', hj'⟩)
          · exact ⟨0, by simpa [t, h] using hz⟩
          · exact ⟨j'.succ, by simpa [t, h] using hj'⟩
      refine Fin.cases ?_ (fun i' => ?_) i
      · intro u hu
        simp only [t, h, Fin.cons_zero] at hu ⊢
        let E₀ := S.filter fun w => w ≠ v₁ ∧ w ≠ v₂ ∧ G.Adj v₁ w ∧ G.Adj v₂ w
        have hsubE : ((S \ used).filter fun w => G.Adj v₁ w ∧ G.Adj v₂ w) ⊆ E₀ := by
          intro w hw
          simp only [Finset.mem_filter, Finset.mem_sdiff] at hw
          simp only [E₀, Finset.mem_filter]
          have hwn1 : w ≠ v₁ := fun heq => hw.1.2 (hused_eq ▸ Finset.mem_union_left _ (heq ▸ Finset.mem_insert_self _ _))
          have hwn2 : w ≠ v₂ := fun heq => hw.1.2 (hused_eq ▸ Finset.mem_union_left _ (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
          exact ⟨hw.1.1, hwn1, hwn2, hw.2.1, hw.2.2⟩
        have hc := Finset.card_le_card hsubE
        have hbd : 2 * E₀.card ≤ outDeg G S u := hE0 u (hsubE hu)
        change 2 * ((S \ used).filter fun w => G.Adj v₁ w ∧ G.Adj v₂ w).card ≤ outDeg G S u
        omega
      · intro u hu
        simp only [t, h, Fin.cons_succ] at hu ⊢
        have hsd_eq : S \ used = S' \ (Finset.univ.biUnion fun j : Fin r => ({t' j, h' j} : Finset V)) := by
          rw [hused_eq, Finset.sdiff_union_distrib]
          ext z; simp [S', Finset.mem_sdiff]
          tauto
        rw [hsd_eq] at hu ⊢
        have h1 := hE' i' u hu
        have h2 : outDeg G S' u ≤ outDeg G S u :=
          Finset.card_le_card (Finset.filter_subset_filter _ hsub_S')
        omega

/-- Helper: greedily choose `r` distinct elements from `S`, where the `i`-th element lies in `A i`,
provided `|A i| ≥ r` for all `i`. -/
private lemma greedy_distinct_choice {α : Type*} [DecidableEq α] :
    ∀ (r : ℕ) (A : Fin r → Finset α),
      (∀ i, r ≤ (A i).card) →
      ∃ f : Fin r → α, Function.Injective f ∧ ∀ i, f i ∈ A i
  | 0, _, _ => ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | r + 1, A, hA => by
    obtain ⟨f', hf'_inj, hf'_mem⟩ :=
      greedy_distinct_choice r (fun i => A i.castSucc) (fun i => by have := hA i.castSucc; omega)
    let used : Finset α := Finset.univ.image f'
    have hused_le : used.card ≤ r := (Finset.card_image_le).trans (by simp)
    have hrem : (A (Fin.last r) \ used).Nonempty := Finset.card_pos.mp (by
      have hsd := Finset.card_sdiff_add_card_inter (A (Fin.last r)) used
      have hinter : (A (Fin.last r) ∩ used).card ≤ used.card := Finset.card_le_card Finset.inter_subset_right
      have hlast := hA (Fin.last r)
      omega)
    obtain ⟨x, hx⟩ := hrem
    rw [Finset.mem_sdiff] at hx
    refine ⟨Fin.snoc f' x, ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;> intro heq
      · rfl
      · simp only [Fin.snoc_last, Fin.snoc_castSucc] at heq
        exact absurd (Finset.mem_image.mpr ⟨j', Finset.mem_univ _, heq.symm⟩) hx.2
      · simp only [Fin.snoc_last, Fin.snoc_castSucc] at heq
        exact absurd (Finset.mem_image.mpr ⟨i', Finset.mem_univ _, heq⟩) hx.2
      · simp only [Fin.snoc_castSucc] at heq
        exact congrArg Fin.castSucc (hf'_inj heq)
    · intro i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · simpa only [Fin.snoc_last] using hx.1
      · simpa only [Fin.snoc_castSucc] using hf'_mem i'

omit [Fintype V] in
/-- Extract a `k`-sublinkage from a `5 * k`-linkage between `X` and `Y` inside `T`,
tracking that each path meets `X` only at its start and `Y` only at its end. -/
private lemma pokrovskiy_sublink {G : Digraph V} {T X Y : Finset V} {k : ℕ}
    (hX_card : X.card = 5 * k) (hY_card : Y.card = 5 * k)
    (hlink : ∀ (u v : Fin (5 * k) → V), Function.Injective u → Function.Injective v →
      (∀ i, u i ∈ X) → (∀ i, v i ∈ Y) →
      ∃ P : Fin (5 * k) → List V,
        (∀ i, IsDirPathBetween G.Adj (u i) (v i) (P i) ∧ ∀ w ∈ P i, w ∈ T) ∧
        ∀ i j, i ≠ j → Disjoint (P i).toFinset (P j).toFinset)
    (u0 v0 : Fin k → V) (hu0_inj : Function.Injective u0) (hv0_inj : Function.Injective v0)
    (hu0_mem : ∀ i, u0 i ∈ X) (hv0_mem : ∀ i, v0 i ∈ Y) :
    ∃ P : Fin k → List V,
      (∀ i, IsDirPathBetween G.Adj (u0 i) (v0 i) (P i)) ∧
      (∀ i, (P i).toFinset ⊆ T) ∧
      (∀ i j, i ≠ j → Disjoint (P i).toFinset (P j).toFinset) ∧
      (∀ i w, w ∈ P i → w ∈ X → w = u0 i) ∧
      (∀ i w, w ∈ P i → w ∈ Y → w = v0 i) := by
  let remX := X \ Finset.univ.image u0
  let remY := Y \ Finset.univ.image v0
  have hremX_c : remX.card = 4 * k := by
    rw [Finset.card_sdiff_of_subset (Finset.image_subset_iff.mpr fun i _ => hu0_mem i),
      Finset.card_image_of_injective _ hu0_inj, Finset.card_univ, Fintype.card_fin, hX_card]; omega
  have hremY_c : remY.card = 4 * k := by
    rw [Finset.card_sdiff_of_subset (Finset.image_subset_iff.mpr fun i _ => hv0_mem i),
      Finset.card_image_of_injective _ hv0_inj, Finset.card_univ, Fintype.card_fin, hY_card]; omega
  let eRemX : Fin (4 * k) ≃ remX := (Fintype.equivFinOfCardEq (by simp [hremX_c])).symm
  let eRemY : Fin (4 * k) ≃ remY := (Fintype.equivFinOfCardEq (by simp [hremY_c])).symm
  let u : Fin (5 * k) → V := fun j => if hj : j.val < k then u0 ⟨j.val, hj⟩ else (eRemX ⟨j.val - k, by omega⟩).1
  let v : Fin (5 * k) → V := fun j => if hj : j.val < k then v0 ⟨j.val, hj⟩ else (eRemY ⟨j.val - k, by omega⟩).1
  have hu_inj : Function.Injective u := by
    intro j₁ j₂ heq; dsimp only [u] at heq
    split_ifs at heq with h1 h2 h2
    · exact Fin.ext (congrArg (Fin.val : Fin k → ℕ) (hu0_inj heq))
    · have hmem : u0 ⟨j₁.val, h1⟩ ∈ Finset.univ.image u0 := Finset.mem_image.mpr ⟨⟨j₁.val, h1⟩, Finset.mem_univ _, rfl⟩
      exact absurd (heq ▸ hmem) (Finset.mem_sdiff.mp (eRemX ⟨j₂.val - k, by omega⟩).2).2
    · have hmem : u0 ⟨j₂.val, h2⟩ ∈ Finset.univ.image u0 := Finset.mem_image.mpr ⟨⟨j₂.val, h2⟩, Finset.mem_univ _, rfl⟩
      exact absurd (heq.symm ▸ hmem) (Finset.mem_sdiff.mp (eRemX ⟨j₁.val - k, by omega⟩).2).2
    · have hval : j₁.val - k = j₂.val - k := congrArg (Fin.val : Fin (4 * k) → ℕ) (eRemX.injective (Subtype.ext heq))
      exact Fin.ext (by omega)
  have hv_inj : Function.Injective v := by
    intro j₁ j₂ heq; dsimp only [v] at heq
    split_ifs at heq with h1 h2 h2
    · exact Fin.ext (congrArg (Fin.val : Fin k → ℕ) (hv0_inj heq))
    · have hmem : v0 ⟨j₁.val, h1⟩ ∈ Finset.univ.image v0 := Finset.mem_image.mpr ⟨⟨j₁.val, h1⟩, Finset.mem_univ _, rfl⟩
      exact absurd (heq ▸ hmem) (Finset.mem_sdiff.mp (eRemY ⟨j₂.val - k, by omega⟩).2).2
    · have hmem : v0 ⟨j₂.val, h2⟩ ∈ Finset.univ.image v0 := Finset.mem_image.mpr ⟨⟨j₂.val, h2⟩, Finset.mem_univ _, rfl⟩
      exact absurd (heq.symm ▸ hmem) (Finset.mem_sdiff.mp (eRemY ⟨j₁.val - k, by omega⟩).2).2
    · have hval : j₁.val - k = j₂.val - k := congrArg (Fin.val : Fin (4 * k) → ℕ) (eRemY.injective (Subtype.ext heq))
      exact Fin.ext (by omega)
  have hu_mem : ∀ j, u j ∈ X := fun j => by dsimp only [u]; split_ifs; exact hu0_mem _; exact (Finset.mem_sdiff.mp (eRemX _).2).1
  have hv_mem : ∀ j, v j ∈ Y := fun j => by dsimp only [v]; split_ifs; exact hv0_mem _; exact (Finset.mem_sdiff.mp (eRemY _).2).1
  obtain ⟨P_all, hP_all, hP_disj⟩ := hlink u v hu_inj hv_inj hu_mem hv_mem
  refine ⟨fun i => P_all ⟨i.val, by omega⟩,
    fun i => by simpa only [u, v, i.isLt, ↓reduceDIte] using (hP_all ⟨i.val, by omega⟩).1,
    fun i w hw => (hP_all ⟨i.val, by omega⟩).2 w (List.mem_toFinset.mp hw),
    fun i j hij => hP_disj ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ (fun h => hij (Fin.ext (Fin.mk.inj h))),
    ?_, ?_⟩
  · intro i w hwP hwX
    have himg : Finset.univ.image u = X :=
      Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr fun j _ => hu_mem j)
        (by rw [Finset.card_image_of_injective _ hu_inj, Finset.card_univ, Fintype.card_fin, hX_card])
    rw [← himg, Finset.mem_image] at hwX
    obtain ⟨j, _, rfl⟩ := hwX
    by_cases heq : j = ⟨i.val, by omega⟩
    · subst heq; simp [u, i.isLt]
    · obtain ⟨_, hne, hhead, _⟩ := (hP_all j).1
      exact absurd (List.mem_toFinset.mpr (hhead ▸ List.head_mem hne))
        (Finset.disjoint_left.mp (hP_disj ⟨i.val, by omega⟩ j (Ne.symm heq)) (List.mem_toFinset.mpr hwP))
  · intro i w hwP hwY
    have himg : Finset.univ.image v = Y :=
      Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr fun j _ => hv_mem j)
        (by rw [Finset.card_image_of_injective _ hv_inj, Finset.card_univ, Fintype.card_fin, hY_card])
    rw [← himg, Finset.mem_image] at hwY
    obtain ⟨j, _, rfl⟩ := hwY
    by_cases heq : j = ⟨i.val, by omega⟩
    · subst heq; simp [v, i.isLt]
    · obtain ⟨_, hne, _, hlast⟩ := (hP_all j).1
      exact absurd (List.mem_toFinset.mpr (hlast ▸ List.getLast_mem hne))
        (Finset.disjoint_left.mp (hP_disj ⟨i.val, by omega⟩ j (Ne.symm heq)) (List.mem_toFinset.mpr hwP))

/-- **Pokrovskiy's Theorem (2015, arXiv:1406.7552, constant 600):**
Every strongly `600 * k`-connected tournament on `S` is `k`-linked: for any `2k` distinct
vertices `x 0, ..., x (k-1), y 0, ..., y (k-1) ∈ S`, there exist `k` pairwise vertex-disjoint
directed paths in `S` with `P i` going from `x i` to `y i`. -/
private theorem pokrovskiy_linked {G : Digraph V} [DecidableRel G.Adj] (hT : IsTournament G)
    {S : Finset V} {k : ℕ} (hstrong : IsKStrongOn G (S : Set V) (600 * k))
    (x y : Fin k → V) (hx_inj : Function.Injective x) (hy_inj : Function.Injective y)
    (hxS : ∀ i, x i ∈ S) (hyS : ∀ i, y i ∈ S) (hxy_disj : ∀ i j, x i ≠ y j) :
    ∃ Ps : Fin k → List V,
      (∀ i, IsDirPathBetween G.Adj (x i) (y i) (Ps i) ∧ ∀ w ∈ Ps i, w ∈ S) ∧
      (∀ i j, i ≠ j → Disjoint (Ps i).toFinset (Ps j).toFinset) := by
  classical
  cases k with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ k' =>
    let k := k' + 1
    have hk_pos : 1 ≤ k := Nat.succ_pos k'
    have hS_deg_out : ∀ v ∈ S, 600 * k ≤ outDeg G S v := fun v hv =>
      min_outDeg_of_isKStrongOn hT hstrong hv
    have hS_deg_in : ∀ v ∈ S, 600 * k ≤ inDeg G S v := fun v hv =>
      min_inDeg_of_isKStrongOn hT hstrong hv
    have hS_card : 1200 * k + 1 ≤ S.card := by
      have hgt : 600 * k < S.card := by simpa [Set.ncard_coe_finset] using hstrong.1
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
      have h1 := hS_deg_out v hv
      have h2 := hS_deg_in v hv
      have h3 := outDeg_add_inDeg_eq hT hv
      omega
    let terms : Finset V := Finset.univ.image x ∪ Finset.univ.image y
    have hterms_sub : terms ⊆ S := by
      intro w hw
      rcases Finset.mem_union.mp hw with h | h <;> rw [Finset.mem_image] at h
      · obtain ⟨i, _, rfl⟩ := h; exact hxS i
      · obtain ⟨i, _, rfl⟩ := h; exact hyS i
    have hterms_card : terms.card = 2 * k := by
      have hdisj : Disjoint (Finset.univ.image x) (Finset.univ.image y) := by
        rw [Finset.disjoint_left]
        intro w h1 h2
        rw [Finset.mem_image] at h1 h2
        obtain ⟨i, _, rfl⟩ := h1; obtain ⟨j, _, hj⟩ := h2
        exact hxy_disj i j hj.symm
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hx_inj,
        Finset.card_image_of_injective _ hy_inj, Finset.card_univ, Fintype.card_fin]
      omega
    let S' := S \ terms
    have hS'_card : S'.card = S.card - 2 * k := by
      rw [Finset.card_sdiff_of_subset hterms_sub, hterms_card]
    -- Extract 65k partial greedy in-dominators D⁻_i = {t⁻_i, h⁻_i} in S'
    obtain ⟨tm, hm, hmem_m, hdisj_m, hEm⟩ :=
      extract_greedy_indoms hT S' (65 * k) (by omega)
    let Dm : Finset V := Finset.univ.biUnion fun i : Fin (65 * k) => ({tm i, hm i} : Finset V)
    have hDm_sub : Dm ⊆ S' := by
      intro w hw; rw [Finset.mem_biUnion] at hw
      obtain ⟨i, _, hi⟩ := hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl; exact (hmem_m i).1; exact (hmem_m i).2.1
    have hDm_card : Dm.card = 130 * k := by
      rw [Finset.card_biUnion (fun i _ j _ hij => hdisj_m i j hij)]
      have hterm : ∀ i : Fin (65 * k), ({tm i, hm i} : Finset V).card = 2 := fun i =>
        Finset.card_pair (hmem_m i).2.2.1
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
      omega
    -- Extract 65k partial greedy out-dominators D⁺_i = {t⁺_i, h⁺_i} in S' \ Dm (using opDigraph!)
    let S'' := S' \ Dm
    have hS''_card : S''.card = S'.card - 130 * k := by
      rw [Finset.card_sdiff_of_subset hDm_sub, hDm_card]
    obtain ⟨hp_op, tp_op, hmem_p_op, hdisj_p_op, hEp_op⟩ :=
      extract_greedy_indoms (isTournament_op hT) S'' (65 * k) (by omega)
    -- In G: G.Adj (tp i) (hp i) (tail tp i → head hp i)
    let tp : Fin (65 * k) → V := tp_op
    let hp : Fin (65 * k) → V := hp_op
    have hmem_p : ∀ i, tp i ∈ S'' ∧ hp i ∈ S'' ∧ tp i ≠ hp i ∧ G.Adj (tp i) (hp i) := fun i =>
      ⟨(hmem_p_op i).2.1, (hmem_p_op i).1, (hmem_p_op i).2.2.1.symm, (hmem_p_op i).2.2.2⟩
    have hdisj_p : ∀ i j, i ≠ j → Disjoint ({tp i, hp i} : Finset V) ({tp j, hp j} : Finset V) := by
      intro i j hij
      have h := hdisj_p_op i j hij
      rwa [Finset.pair_comm (hp_op i), Finset.pair_comm (hp_op j)] at h
    let Dp : Finset V := Finset.univ.biUnion fun i : Fin (65 * k) => ({tp i, hp i} : Finset V)
    have hDp_sub : Dp ⊆ S'' := by
      intro w hw; rw [Finset.mem_biUnion] at hw
      obtain ⟨i, _, hi⟩ := hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl; exact (hmem_p i).1; exact (hmem_p i).2.1
    have hDp_card : Dp.card = 130 * k := by
      rw [Finset.card_biUnion (fun i _ j _ hij => hdisj_p i j hij)]
      have hterm : ∀ i : Fin (65 * k), ({tp i, hp i} : Finset V).card = 2 := fun i =>
        Finset.card_pair (hmem_p i).2.2.1
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
      omega
    -- X = terms ∪ Dm ∪ Dp has size 262 * k
    let X : Finset V := terms ∪ Dm ∪ Dp
    have hX_sub : X ⊆ S := by
      refine Finset.union_subset (Finset.union_subset hterms_sub (hDm_sub.trans Finset.sdiff_subset))
        (hDp_sub.trans (Finset.sdiff_subset.trans Finset.sdiff_subset))
    have hX_card : X.card ≤ 262 * k := by
      calc X.card ≤ (terms ∪ Dm).card + Dp.card := Finset.card_union_le _ _
        _ ≤ terms.card + Dm.card + Dp.card := by have := Finset.card_union_le terms Dm; omega
        _ = 262 * k := by rw [hterms_card, hDm_card, hDp_card]; omega
    -- T⁻ = heads {hm i}, T⁺ = tails {tp i}, each of size 65 * k = 13 * (5 * k)
    have hhm_inj : Function.Injective hm := by
      intro i j heq; by_contra hne
      exact Finset.disjoint_left.mp (hdisj_m i j hne)
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have htp_inj : Function.Injective tp := by
      intro i j heq; by_contra hne
      exact Finset.disjoint_left.mp (hdisj_p i j hne)
        (Finset.mem_insert_self _ _) (heq ▸ Finset.mem_insert_self _ _)
    let Tm : Finset V := Finset.univ.image hm
    let Tp : Finset V := Finset.univ.image tp
    have hTm_card : Tm.card = 65 * k := by
      rw [Finset.card_image_of_injective _ hhm_inj, Finset.card_univ, Fintype.card_fin]
    have hTp_card : Tp.card = 65 * k := by
      rw [Finset.card_image_of_injective _ htp_inj, Finset.card_univ, Fintype.card_fin]
    -- Apply Pokrovskiy Lemma 2.1 to Tm and Tp with m = 5 * k
    obtain ⟨Xm, Ym, hXm_Tm, hYm_Tm, hXYm_disj, hXm_card, hYm_card, hlink_m⟩ :=
      pokrovskiy_large_linkage hT Tm (m := 5 * k) (by rw [hTm_card]; omega)
    obtain ⟨Xp, Yp, hXp_Tp, hYp_Tp, hXYp_disj, hXp_card, hYp_card, hlink_p⟩ :=
      pokrovskiy_large_linkage hT Tp (m := 5 * k) (by rw [hTp_card]; omega)
    -- Choose indices idxM : Fin k ↪ Fin (65k) with hm (idxM i) ∈ Xm, and idxP : Fin k ↪ Fin (65k) with tp (idxP i) ∈ Yp
    obtain ⟨Xm_sub, hXm_sub_Xm, hXm_sub_card⟩ := Finset.exists_subset_card_eq (by omega : k ≤ Xm.card)
    obtain ⟨Yp_sub, hYp_sub_Yp, hYp_sub_card⟩ := Finset.exists_subset_card_eq (by omega : k ≤ Yp.card)
    let eXm : Fin k ≃ Xm_sub := (Fintype.equivFinOfCardEq (by simp [hXm_sub_card])).symm
    let eYp : Fin k ≃ Yp_sub := (Fintype.equivFinOfCardEq (by simp [hYp_sub_card])).symm
    have hidxM_ex : ∀ i : Fin k, ∃ a : Fin (65 * k), hm a = (eXm i).1 := fun i => by
      have := hXm_Tm (hXm_sub_Xm (eXm i).2)
      rw [Finset.mem_image] at this; obtain ⟨a, _, ha⟩ := this; exact ⟨a, ha⟩
    have hidxP_ex : ∀ i : Fin k, ∃ a : Fin (65 * k), tp a = (eYp i).1 := fun i => by
      have := hYp_Tp (hYp_sub_Yp (eYp i).2)
      rw [Finset.mem_image] at this; obtain ⟨a, _, ha⟩ := this; exact ⟨a, ha⟩
    choose idxM hidxM using hidxM_ex
    choose idxP hidxP using hidxP_ex
    have hidxM_inj : Function.Injective idxM := fun i j h =>
      eXm.injective (Subtype.ext ((hidxM i).symm.trans ((congrArg hm h).trans (hidxM j))))
    have hidxP_inj : Function.Injective idxP := fun i j h =>
      eYp.injective (Subtype.ext ((hidxP i).symm.trans ((congrArg tp h).trans (hidxP j))))
    -- Step 1: By Menger on S_mid := (S \ X) ∪ Ym ∪ Xp, get 5k vertex-disjoint paths from Ym to Xp
    let S_mid : Finset V := (S \ X) ∪ Ym ∪ Xp
    have hYm_X : Ym ⊆ X := fun w hw => by
      have h1 := hYm_Tm hw; rw [Finset.mem_image] at h1
      obtain ⟨a, _, rfl⟩ := h1
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩))
    have hXp_X : Xp ⊆ X := fun w hw => by
      have h1 := hXp_Tp hw; rw [Finset.mem_image] at h1
      obtain ⟨a, _, rfl⟩ := h1
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, Finset.mem_insert_self _ _⟩)
    have hSmid_sub : S_mid ⊆ S :=
      Finset.union_subset (Finset.union_subset Finset.sdiff_subset (hYm_X.trans hX_sub)) (hXp_X.trans hX_sub)
    have hSmid_strong : IsKStrongOn G (S_mid : Set V) (5 * k) := by
      let del : Finset V := S \ S_mid
      have hdel_sub : del ⊆ X := by
        intro w hw
        rw [Finset.mem_sdiff] at hw
        by_contra hnot
        exact hw.2 (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hw.1, hnot⟩)))
      have hdel_card : del.card ≤ 262 * k := (Finset.card_le_card hdel_sub).trans hX_card
      have hSmid_eq : (S_mid : Set V) = (S : Set V) \ (del : Set V) := by
        ext w; simp only [Finset.mem_coe, Set.mem_sdiff, del, Finset.mem_sdiff]
        constructor
        · intro h; exact ⟨hSmid_sub h, fun h2 => h2.2 h⟩
        · rintro ⟨hwS, hnot⟩; by_contra h; exact hnot ⟨hwS, h⟩
      refine ⟨?_, ?_⟩
      · rw [Set.ncard_coe_finset]
        have hsd := Finset.card_sdiff_add_card_inter S S_mid
        have hinter : S ∩ S_mid = S_mid := Finset.inter_eq_right.mpr hSmid_sub
        rw [hinter] at hsd
        change del.card + S_mid.card = S.card at hsd
        omega
      · intro Z hZ
        rw [hSmid_eq, Set.sdiff_sdiff]
        have hZU : (del ∪ Z).card < 600 * k := by
          have := Finset.card_union_le del Z; omega
        simpa only [Finset.coe_union] using hstrong.2 (del ∪ Z) hZU
    obtain ⟨Qs, hQs, hQs_disj⟩ := menger_of_isKStrongOn G hT.1 hSmid_strong
      (Finset.subset_union_right.trans Finset.subset_union_left)
      Finset.subset_union_right (by omega) (by omega)
    -- Step 2: Choose 2k distinct neighbors x'_i ∈ outNbr S (x i) \ X and y'_i ∈ inNbr S (y i) \ X
    let nbrPool : Fin (2 * k) → Finset V := fun t =>
      if ht : t.val < k then outNbr G S (x ⟨t.val, ht⟩) \ X
      else inNbr G S (y ⟨t.val - k, by omega⟩) \ X
    have hnbrPool_ge : ∀ t : Fin (2 * k), 2 * k ≤ (nbrPool t).card := by
      intro t; dsimp only [nbrPool]
      split_ifs with ht
      · have h1 := hS_deg_out (x ⟨t.val, ht⟩) (hxS _)
        have hsd := Finset.card_sdiff_add_card_inter (outNbr G S (x ⟨t.val, ht⟩)) X
        have hinter : (outNbr G S (x ⟨t.val, ht⟩) ∩ X).card ≤ X.card :=
          Finset.card_le_card Finset.inter_subset_right
        change (outNbr G S (x ⟨t.val, ht⟩) \ X).card + (outNbr G S (x ⟨t.val, ht⟩) ∩ X).card =
          outDeg G S (x ⟨t.val, ht⟩) at hsd
        omega
      · have h1 := hS_deg_in (y ⟨t.val - k, by omega⟩) (hyS _)
        have hsd := Finset.card_sdiff_add_card_inter (inNbr G S (y ⟨t.val - k, by omega⟩)) X
        have hinter : (inNbr G S (y ⟨t.val - k, by omega⟩) ∩ X).card ≤ X.card :=
          Finset.card_le_card Finset.inter_subset_right
        change (inNbr G S (y ⟨t.val - k, by omega⟩) \ X).card + (inNbr G S (y ⟨t.val - k, by omega⟩) ∩ X).card =
          inDeg G S (y ⟨t.val - k, by omega⟩) at hsd
        omega
    obtain ⟨f1, hf1_inj, hf1_mem⟩ := greedy_distinct_choice (2 * k) nbrPool hnbrPool_ge
    let x' : Fin k → V := fun i => f1 ⟨i.val, by omega⟩
    let y' : Fin k → V := fun i => f1 ⟨k + i.val, by omega⟩
    let X' : Finset V := X ∪ Finset.univ.image f1
    have hX'_card : X'.card ≤ 264 * k := by
      calc X'.card ≤ X.card + (Finset.univ.image f1).card := Finset.card_union_le _ _
        _ ≤ 262 * k + 2 * k := by
          have h1 : (Finset.univ.image f1).card ≤ 2 * k := Finset.card_image_le.trans (by simp)
          omega
        _ = 264 * k := by omega
    -- Step 3: For each i, if x'_i is uncovered by D⁻_{idxM i}, pick x''_i ∈ outNbr S (x'_i) \ (E⁻_i ∪ X'), etc.
    let Em : Fin k → Finset V := fun i =>
      (S \ X).filter fun w => G.Adj (tm (idxM i)) w ∧ G.Adj (hm (idxM i)) w
    let Ep : Fin k → Finset V := fun i =>
      (S \ X).filter fun w => G.Adj w (tp (idxP i)) ∧ G.Adj w (hp (idxP i))
    have hEm_deg : ∀ i, ∀ u ∈ Em i, 2 * (Em i).card ≤ outDeg G S u := by
      intro i u hu
      have hsub : Em i ⊆ (S' \ Dm).filter fun w => G.Adj (tm (idxM i)) w ∧ G.Adj (hm (idxM i)) w := by
        intro w hw; simp only [Em, Finset.mem_filter, Finset.mem_sdiff] at hw
        simp only [Finset.mem_filter, Finset.mem_sdiff, S', X, Finset.mem_union, not_or] at hw ⊢
        exact ⟨⟨⟨hw.1.1, hw.1.2.1.1⟩, hw.1.2.1.2⟩, hw.2⟩
      have h1 := hEm (idxM i) u (hsub hu)
      change 2 * ((S' \ Dm).filter fun w => G.Adj (tm (idxM i)) w ∧ G.Adj (hm (idxM i)) w).card ≤ outDeg G S' u at h1
      have h2 := Finset.card_le_card hsub
      have h3 : outDeg G S' u ≤ outDeg G S u :=
        Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)
      omega
    have hEp_deg : ∀ i, ∀ u ∈ Ep i, 2 * (Ep i).card ≤ inDeg G S u := by
      intro i u hu
      let Ep_op := (S'' \ (Finset.univ.biUnion fun j : Fin (65 * k) => ({hp_op j, tp_op j} : Finset V))).filter
        fun w => (opDigraph G).Adj (hp_op (idxP i)) w ∧ (opDigraph G).Adj (tp_op (idxP i)) w
      have hsub : Ep i ⊆ Ep_op := by
        intro w hw
        simp only [Ep, Finset.mem_filter, Finset.mem_sdiff, X, Finset.mem_union, not_or] at hw
        refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hw.1.1, hw.1.2.1.1⟩, hw.1.2.1.2⟩, ?_⟩, hw.2.2, hw.2.1⟩
        intro hmem; apply hw.1.2.2
        rw [Finset.mem_biUnion] at hmem ⊢
        obtain ⟨j, _, hj⟩ := hmem
        exact ⟨j, Finset.mem_univ _, by simpa only [Finset.pair_comm] using hj⟩
      have h1 : 2 * Ep_op.card ≤ outDeg (opDigraph G) S'' u := hEp_op (idxP i) u (hsub hu)
      have h2 := Finset.card_le_card hsub
      have h3 : inDeg G S'' u ≤ inDeg G S u :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.sdiff_subset.trans Finset.sdiff_subset))
      have h4 : outDeg (opDigraph G) S'' u = inDeg G S'' u := rfl
      omega
    -- Pool for second hops x''_i, y''_i (for those that need a second hop; if not in E, pick a dummy outside X' or use a fresh vertex)
    -- Even cleaner: ALWAYS pick a distinct x''_i / y''_i in outNbr(x'_i) \ (Em i ∪ X') when x'_i ∈ Em i,
    -- and when x'_i ∉ Em i just put {x'_i} in the pool? Wait: x'_i is ALREADY disjoint from X' \ {x'_i} and from all other pools!
    let hopPool : Fin (2 * k) → Finset V := fun t =>
      if ht : t.val < k then
        let i : Fin k := ⟨t.val, ht⟩
        if x' i ∈ Em i then outNbr G S (x' i) \ (Em i ∪ X') else {x' i}
      else
        let i : Fin k := ⟨t.val - k, by omega⟩
        if y' i ∈ Ep i then inNbr G S (y' i) \ (Ep i ∪ X') else {y' i}
    -- Build f2 : Fin (2k) → V choosing x''_i (for t < k) and y''_i (for t ≥ k) all distinct,
    -- with f2 t = x' i when x' i ∉ Em i, and f2 t ∈ outNbr(x' i) \ (Em i ∪ X') when x' i ∈ Em i!
    have hf2_ex : ∃ f2 : Fin (2 * k) → V, Function.Injective f2 ∧
        (∀ t, f2 t ∈ hopPool t) ∧
        (∀ i : Fin k, x' i ∈ Em i → f2 ⟨i.val, by omega⟩ ∉ X') ∧
        (∀ i : Fin k, y' i ∈ Ep i → f2 ⟨k + i.val, by omega⟩ ∉ X') := by
      -- For indices needing a hop, their pool is disjoint from X' and has size ≥ 2k!
      let needHop : Finset (Fin (2 * k)) := Finset.univ.filter fun t =>
        if ht : t.val < k then x' ⟨t.val, ht⟩ ∈ Em ⟨t.val, ht⟩
        else y' ⟨t.val - k, by omega⟩ ∈ Ep ⟨t.val - k, by omega⟩
      have hpool_big : ∀ t ∈ needHop, 2 * k ≤ (hopPool t).card := by
        intro t ht_mem
        have ht_cond := (Finset.mem_filter.mp ht_mem).2
        dsimp only [hopPool]
        split_ifs with ht hmem hmem
        · have hx'_S : x' ⟨t.val, ht⟩ ∈ S := by
            have := hf1_mem ⟨t.val, by omega⟩; dsimp only [nbrPool] at this
            simp only [ht, ↓reduceDIte, Finset.mem_sdiff] at this
            exact (Finset.mem_filter.mp this.1).1
          have hdeg1 := hS_deg_out (x' ⟨t.val, ht⟩) hx'_S
          have hdeg2 := hEm_deg ⟨t.val, ht⟩ (x' ⟨t.val, ht⟩) hmem
          have hsd := Finset.card_sdiff_add_card_inter (outNbr G S (x' ⟨t.val, ht⟩)) (Em ⟨t.val, ht⟩ ∪ X')
          have hinter : (outNbr G S (x' ⟨t.val, ht⟩) ∩ (Em ⟨t.val, ht⟩ ∪ X')).card ≤
              (Em ⟨t.val, ht⟩).card + X'.card :=
            (Finset.card_le_card Finset.inter_subset_right).trans (Finset.card_union_le _ _)
          change (outNbr G S (x' ⟨t.val, ht⟩) \ (Em ⟨t.val, ht⟩ ∪ X')).card +
              (outNbr G S (x' ⟨t.val, ht⟩) ∩ (Em ⟨t.val, ht⟩ ∪ X')).card =
              outDeg G S (x' ⟨t.val, ht⟩) at hsd
          omega
        · simp only [ht, ↓reduceDIte] at ht_cond; exact absurd ht_cond hmem
        · have hy'_S : y' ⟨t.val - k, by omega⟩ ∈ S := by
            have hteq : (⟨k + (t.val - k), by omega⟩ : Fin (2 * k)) = t := Fin.ext (by dsimp; omega)
            have := hf1_mem t; dsimp only [nbrPool] at this
            simp only [ht, ↓reduceDIte, Finset.mem_sdiff] at this
            change f1 ⟨k + (t.val - k), by omega⟩ ∈ S
            rw [hteq]
            exact (Finset.mem_filter.mp this.1).1
          have hdeg1 := hS_deg_in (y' ⟨t.val - k, by omega⟩) hy'_S
          have hdeg2 := hEp_deg ⟨t.val - k, by omega⟩ (y' ⟨t.val - k, by omega⟩) hmem
          have hsd := Finset.card_sdiff_add_card_inter (inNbr G S (y' ⟨t.val - k, by omega⟩)) (Ep ⟨t.val - k, by omega⟩ ∪ X')
          have hinter : (inNbr G S (y' ⟨t.val - k, by omega⟩) ∩ (Ep ⟨t.val - k, by omega⟩ ∪ X')).card ≤
              (Ep ⟨t.val - k, by omega⟩).card + X'.card :=
            (Finset.card_le_card Finset.inter_subset_right).trans (Finset.card_union_le _ _)
          change (inNbr G S (y' ⟨t.val - k, by omega⟩) \ (Ep ⟨t.val - k, by omega⟩ ∪ X')).card +
              (inNbr G S (y' ⟨t.val - k, by omega⟩) ∩ (Ep ⟨t.val - k, by omega⟩ ∪ X')).card =
              inDeg G S (y' ⟨t.val - k, by omega⟩) at hsd
          omega
        · simp only [ht, ↓reduceDIte] at ht_cond; exact absurd ht_cond hmem
      -- Pick distinct elements for all t ∈ needHop, and for t ∉ needHop use f1 t (which is in X'!)
      let extPool : Fin (2 * k) → Finset V := fun t =>
        if t ∈ needHop then hopPool t else S
      have hext_ge : ∀ t, 2 * k ≤ (extPool t).card := by
        intro t; dsimp only [extPool]; split_ifs with ht
        · exact hpool_big t ht
        · omega
      obtain ⟨g, hg_inj, hg_mem⟩ := greedy_distinct_choice (2 * k) extPool hext_ge
      let f2 : Fin (2 * k) → V := fun t => if t ∈ needHop then g t else f1 t
      have hf2_need_nX' : ∀ t ∈ needHop, g t ∉ X' := by
        intro t ht
        have hm := hg_mem t; simp only [extPool, ht, ↓reduceIte] at hm
        have htc := (Finset.mem_filter.mp ht).2
        dsimp only [hopPool] at hm
        split_ifs at hm with h1 h2 h2
        · exact fun h => (Finset.mem_sdiff.mp hm).2 (Finset.mem_union_right _ h)
        · simp only [h1, ↓reduceDIte] at htc; exact absurd htc h2
        · exact fun h => (Finset.mem_sdiff.mp hm).2 (Finset.mem_union_right _ h)
        · simp only [h1, ↓reduceDIte] at htc; exact absurd htc h2
      have hf1_in_X' : ∀ t, f1 t ∈ X' := fun t =>
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩)
      refine ⟨f2, ?_, ?_, ?_, ?_⟩
      · intro t₁ t₂ heq
        dsimp only [f2] at heq
        split_ifs at heq with h1 h2 h2
        · exact hg_inj heq
        · exact absurd (heq ▸ hf1_in_X' t₂) (hf2_need_nX' t₁ h1)
        · exact absurd (heq.symm ▸ hf1_in_X' t₁) (hf2_need_nX' t₂ h2)
        · exact hf1_inj heq
      · intro t
        dsimp only [f2]
        split_ifs with ht
        · have hm := hg_mem t; simpa only [extPool, ht, ↓reduceIte] using hm
        · have htc : ¬ (if h1 : t.val < k then x' ⟨t.val, h1⟩ ∈ Em ⟨t.val, h1⟩
              else y' ⟨t.val - k, by omega⟩ ∈ Ep ⟨t.val - k, by omega⟩) := fun h =>
            ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          dsimp only [hopPool]
          split_ifs with h1 h2 h2
          · simp only [h1, ↓reduceDIte] at htc; exact absurd h2 htc
          · simp only [Finset.mem_singleton, x']
          · simp only [h1, ↓reduceDIte] at htc; exact absurd h2 htc
          · simp only [Finset.mem_singleton, y']; congr 1; exact Fin.ext (by dsimp; omega)
      · intro i hi
        have ht : (⟨i.val, by omega⟩ : Fin (2 * k)) ∈ needHop := by
          simp [needHop, i.isLt, hi]
        simpa only [f2, ht, ↓reduceIte] using hf2_need_nX' ⟨i.val, by omega⟩ ht
      · intro i hi
        have ht : (⟨k + i.val, by omega⟩ : Fin (2 * k)) ∈ needHop := by
          have hnot : ¬ (k + i.val < k) := by omega
          have hsub : k + i.val - k = i.val := by omega
          simp [needHop, hnot, hsub, hi]
        simpa only [f2, ht, ↓reduceIte] using hf2_need_nX' ⟨k + i.val, by omega⟩ ht
    obtain ⟨f2, hf2_inj, hf2_mem, hf2_x_nX', hf2_y_nX'⟩ := hf2_ex
    let x'' : Fin k → V := fun i => f2 ⟨i.val, by omega⟩
    let y'' : Fin k → V := fun i => f2 ⟨k + i.val, by omega⟩
    -- Step 4: Among the 5k disjoint paths Qs : Fin (5k) → List V, at least k avoid B_avoid := image f1 ∪ image f2 (size ≤ 4k)!
    let B_avoid : Finset V := Finset.univ.image f1 ∪ Finset.univ.image f2
    have hB_card : B_avoid.card ≤ 4 * k := by
      calc B_avoid.card ≤ (Finset.univ.image f1).card + (Finset.univ.image f2).card := Finset.card_union_le _ _
        _ ≤ 2 * k + 2 * k := by
          have h1 : (Finset.univ.image f1).card ≤ 2 * k := Finset.card_image_le.trans (by simp)
          have h2 : (Finset.univ.image f2).card ≤ 2 * k := Finset.card_image_le.trans (by simp)
          omega
        _ = 4 * k := by omega
    let goodQ : Finset (Fin (5 * k)) := Finset.univ.filter fun j => Disjoint (Qs j).toFinset B_avoid
    have hgoodQ_ge : k ≤ goodQ.card := by
      let badQ := Finset.univ \ goodQ
      have hbadQ_le : badQ.card ≤ B_avoid.card := by
        have hex : ∀ j ∈ badQ, ∃ w ∈ B_avoid, w ∈ (Qs j).toFinset := by
          intro j hj
          have hnd : ¬ Disjoint (Qs j).toFinset B_avoid := by
            intro hd; exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩)
          rw [Finset.not_disjoint_iff] at hnd
          obtain ⟨w, hw1, hw2⟩ := hnd; exact ⟨w, hw2, hw1⟩
        choose pick hpick_B hpick_Q using hex
        -- Injectivity of pick on badQ since Qs are pairwise disjoint!
        let pick' : Fin (5 * k) → V := fun j => if hj : j ∈ badQ then pick j hj else x ⟨0, hk_pos⟩
        have hinj : Set.InjOn pick' (badQ : Set (Fin (5 * k))) := by
          intro j₁ hj₁ j₂ hj₂ heq
          by_contra hne
          simp only [pick', Finset.mem_coe.mp hj₁, Finset.mem_coe.mp hj₂, ↓reduceDIte] at heq
          exact Finset.disjoint_left.mp (hQs_disj j₁ j₂ hne)
            (hpick_Q j₁ (Finset.mem_coe.mp hj₁)) (heq ▸ hpick_Q j₂ (Finset.mem_coe.mp hj₂))
        calc badQ.card = (badQ.image pick').card := (Finset.card_image_of_injOn hinj).symm
          _ ≤ B_avoid.card := Finset.card_le_card (Finset.image_subset_iff.mpr fun j hj => by
            simpa only [pick', hj, ↓reduceDIte] using hpick_B j hj)
      have hsd := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin (5 * k))) goodQ
      have hinter : Finset.univ ∩ goodQ = goodQ := Finset.inter_eq_right.mpr (Finset.subset_univ _)
      rw [hinter, Finset.card_univ, Fintype.card_fin] at hsd
      change badQ.card + goodQ.card = 5 * k at hsd
      omega
    obtain ⟨goodQ_sub, hgoodQ_sub, hgoodQ_sub_card⟩ := Finset.exists_subset_card_eq hgoodQ_ge
    let eQ : Fin k ≃ goodQ_sub := (Fintype.equivFinOfCardEq (by simp [hgoodQ_sub_card])).symm
    let Q' : Fin k → List V := fun i => Qs (eQ i).1
    -- Step 5: Link Xm → Ym in Tm and Xp → Yp in Tp via `pokrovskiy_sublink`!
    let uM0 : Fin k → V := fun i => hm (idxM i)
    let vM0 : Fin k → V := fun i => (Q' i).head (hQs (eQ i).1).1.1
    have huM0_mem : ∀ i, uM0 i ∈ Xm := fun i => hXm_sub_Xm (by dsimp [uM0]; rw [hidxM i]; exact (eXm i).2)
    have hvM0_mem : ∀ i, vM0 i ∈ Ym := fun i => (hQs (eQ i).1).2.choose_spec.1
    have huM0_inj : Function.Injective uM0 := fun i j h => hidxM_inj (hhm_inj h)
    have hvM0_inj : Function.Injective vM0 := by
      intro i j heq; by_contra hne
      have h1 : vM0 i ∈ (Q' i).toFinset := List.mem_toFinset.mpr (List.head_mem _)
      have h2 : vM0 i ∈ (Q' j).toFinset := heq ▸ List.mem_toFinset.mpr (List.head_mem _)
      exact Finset.disjoint_left.mp (hQs_disj (eQ i).1 (eQ j).1 (fun h => hne (eQ.injective (Subtype.ext h)))) h1 h2
    obtain ⟨Pm, hPm_bet, hPm_sub_Tm, hPm_disj, _, hPm_meet_Ym⟩ :=
      pokrovskiy_sublink hXm_card hYm_card hlink_m uM0 vM0 huM0_inj hvM0_inj huM0_mem hvM0_mem
    let uP0 : Fin k → V := fun i => (Q' i).getLast (hQs (eQ i).1).1.1
    let vP0 : Fin k → V := fun i => tp (idxP i)
    have huP0_mem : ∀ i, uP0 i ∈ Xp := fun i => (hQs (eQ i).1).2.choose_spec.2
    have hvP0_mem : ∀ i, vP0 i ∈ Yp := fun i => hYp_sub_Yp (by dsimp [vP0]; rw [hidxP i]; exact (eYp i).2)
    have huP0_inj : Function.Injective uP0 := by
      intro i j heq; by_contra hne
      have h1 : uP0 i ∈ (Q' i).toFinset := List.mem_toFinset.mpr (List.getLast_mem _)
      have h2 : uP0 i ∈ (Q' j).toFinset := heq ▸ List.mem_toFinset.mpr (List.getLast_mem _)
      exact Finset.disjoint_left.mp (hQs_disj (eQ i).1 (eQ j).1 (fun h => hne (eQ.injective (Subtype.ext h)))) h1 h2
    have hvP0_inj : Function.Injective vP0 := fun i j h => hidxP_inj (htp_inj h)
    obtain ⟨Pp, hPp_bet, hPp_sub_Tp, hPp_disj, hPp_meet_Xp, _⟩ :=
      pokrovskiy_sublink hXp_card hYp_card hlink_p uP0 vP0 huP0_inj hvP0_inj huP0_mem hvP0_mem
    have hQ'_meet_Ym : ∀ i w, w ∈ Q' i → w ∈ Ym → w = vM0 i := by
      intro i w hwQ hwYm
      have hhead_inj : Function.Injective (fun j : Fin (5 * k) => (Qs j).head (hQs j).1.1) := by
        intro j₁ j₂ heq; by_contra hne
        dsimp only at heq
        have h2 : (Qs j₁).head (hQs j₁).1.1 ∈ (Qs j₂).toFinset := by
          rw [heq]; exact List.mem_toFinset.mpr (List.head_mem _)
        exact Finset.disjoint_left.mp (hQs_disj j₁ j₂ hne)
          (List.mem_toFinset.mpr (List.head_mem _)) h2
      have himg : Finset.univ.image (fun j : Fin (5 * k) => (Qs j).head (hQs j).1.1) = Ym :=
        Finset.eq_of_subset_of_card_le
          (Finset.image_subset_iff.mpr fun j _ => (hQs j).2.choose_spec.1)
          (by rw [Finset.card_image_of_injective _ hhead_inj, Finset.card_univ, Fintype.card_fin, hYm_card])
      rw [← himg, Finset.mem_image] at hwYm
      obtain ⟨j, _, rfl⟩ := hwYm
      by_cases heq : j = (eQ i).1
      · rw [heq]
      · exact absurd (List.mem_toFinset.mpr (List.head_mem _))
          (Finset.disjoint_left.mp (hQs_disj (eQ i).1 j (Ne.symm heq)) (List.mem_toFinset.mpr hwQ))
    have hQ'_meet_Xp : ∀ i w, w ∈ Q' i → w ∈ Xp → w = uP0 i := by
      intro i w hwQ hwXp
      have hlast_inj : Function.Injective (fun j : Fin (5 * k) => (Qs j).getLast (hQs j).1.1) := by
        intro j₁ j₂ heq; by_contra hne
        dsimp only at heq
        have h2 : (Qs j₁).getLast (hQs j₁).1.1 ∈ (Qs j₂).toFinset := by
          rw [heq]; exact List.mem_toFinset.mpr (List.getLast_mem _)
        exact Finset.disjoint_left.mp (hQs_disj j₁ j₂ hne)
          (List.mem_toFinset.mpr (List.getLast_mem _)) h2
      have himg : Finset.univ.image (fun j : Fin (5 * k) => (Qs j).getLast (hQs j).1.1) = Xp :=
        Finset.eq_of_subset_of_card_le
          (Finset.image_subset_iff.mpr fun j _ => (hQs j).2.choose_spec.2)
          (by rw [Finset.card_image_of_injective _ hlast_inj, Finset.card_univ, Fintype.card_fin, hXp_card])
      rw [← himg, Finset.mem_image] at hwXp
      obtain ⟨j, _, rfl⟩ := hwXp
      by_cases heq : j = (eQ i).1
      · rw [heq]
      · exact absurd (List.mem_toFinset.mpr (List.getLast_mem _))
          (Finset.disjoint_left.mp (hQs_disj (eQ i).1 j (Ne.symm heq)) (List.mem_toFinset.mpr hwQ))
    -- Step 6: Assemble each path P_i by gluing:
    --   left_i (x_i → x'_i → [x''_i] → [tm (idxM i)] → hm (idxM i))
    --   ++ (Pm i).tail (in Tm, from hm (idxM i) to vM0 i)
    --   ++ (Q' i).tail (in S_mid, from vM0 i to uP0 i)
    --   ++ (Pp i).tail (in Tp, from uP0 i to tp (idxP i))
    --   ++ right_i (tp (idxP i) → [hp (idxP i)] → [y''_i] → y'_i → y_i).tail
    -- Notice: all 5 regions are pairwise disjoint (except at the exact glue points)!
    --   - Terms {x_i, y_i} ⊆ terms
    --   - B_avoid = {x'_i, y'_i, x''_i, y''_i} ⊆ S \ X (and disjoint from Q' j!)
    --   - Tails tm (idxM i) ∈ Dm \ Tm, heads hp (idxP i) ∈ Dp \ Tp
    --   - Pm i ⊆ Tm ⊆ Dm
    --   - Q' i ⊆ (S \ X) ∪ Ym ∪ Xp (meeting Tm only at vM0 i, Tp only at uP0 i, and disjoint from B_avoid!)
    --   - Pp i ⊆ Tp ⊆ Dp
    -- Build walk inside the per-i disjoint vertex set W i, then extract simple path via exists_dirPath_of_reflTransGen!
    -- OH!! GENIUS!! Using `exists_dirPath_of_reflTransGen` on disjoint vertex sets `W i` avoids ALL manual `List.append` / `Nodup` / `.tail` boilerplate!!
    let W : Fin k → Finset V := fun i =>
      ({x i, y i, x' i, y' i, x'' i, y'' i, tm (idxM i), hp (idxP i)} : Finset V) ∪
        (Pm i).toFinset ∪ (Q' i).toFinset ∪ (Pp i).toFinset
    -- Helper: classify every vertex of W i into pairwise disjoint global buckets!
    -- Bucket 1: terms (only {x i, y i})
    -- Bucket 2: B_avoid (only {x' i, y' i, x'' i, y'' i}, since Q' i is disjoint from B_avoid and X is disjoint from B_avoid!)
    -- Bucket 3: Dm \ Tm (only {tm (idxM i)})
    -- Bucket 4: Tm (only Pm i ∪ {vM0 i} = Pm i)
    -- Bucket 5: S \ (X ∪ B_avoid) (only Q' i \ (Ym ∪ Xp))
    -- Bucket 6: Tp (only Pp i)
    -- Bucket 7: Dp \ Tp (only {hp (idxP i)})
    have hB_disj_X : Disjoint B_avoid X := by
      rw [Finset.disjoint_left]
      intro w hwB hwX
      rcases Finset.mem_union.mp hwB with h1 | h2
      · rw [Finset.mem_image] at h1
        obtain ⟨t, _, rfl⟩ := h1
        have hm := hf1_mem t; dsimp only [nbrPool] at hm
        split_ifs at hm <;> exact (Finset.mem_sdiff.mp hm).2 hwX
      · rw [Finset.mem_image] at h2
        obtain ⟨t, _, rfl⟩ := h2
        have hm := hf2_mem t; dsimp only [hopPool] at hm
        split_ifs at hm with hlt hE
        · exact (Finset.mem_sdiff.mp hm).2 (Finset.mem_union_right _ (Finset.mem_union_left _ hwX))
        · rw [Finset.mem_singleton] at hm
          have h1m := hf1_mem ⟨t.val, by omega⟩; dsimp only [nbrPool] at h1m
          simp only [hlt, ↓reduceDIte] at h1m
          have hfx : f1 ⟨t.val, by omega⟩ = f2 t := hm.symm
          exact (Finset.mem_sdiff.mp h1m).2 (hfx ▸ hwX)
        · exact (Finset.mem_sdiff.mp hm).2 (Finset.mem_union_right _ (Finset.mem_union_left _ hwX))
        · rw [Finset.mem_singleton] at hm
          have h1m := hf1_mem ⟨k + (t.val - k), by omega⟩; dsimp only [nbrPool] at h1m
          have hnot : ¬ (k + (t.val - k) < k) := by omega
          simp only [hnot, ↓reduceDIte] at h1m
          have hfy : f1 ⟨k + (t.val - k), by omega⟩ = f2 t := hm.symm
          exact (Finset.mem_sdiff.mp h1m).2 (hfy ▸ hwX)
    have hDm_disj_terms : Disjoint Dm terms := Finset.disjoint_of_subset_left hDm_sub disjoint_sdiff_self_left
    have hDp_disj_terms : Disjoint Dp terms :=
      Finset.disjoint_of_subset_left (hDp_sub.trans Finset.sdiff_subset) disjoint_sdiff_self_left
    have hDp_disj_Dm : Disjoint Dp Dm := Finset.disjoint_of_subset_left hDp_sub disjoint_sdiff_self_left
    have htm_nTm : ∀ a : Fin (65 * k), tm a ∉ Tm := by
      intro a hmem; rw [Finset.mem_image] at hmem
      obtain ⟨b, _, hba⟩ := hmem
      by_cases heq : a = b
      · exact (hmem_m a).2.2.1 (heq ▸ hba.symm)
      · exact Finset.disjoint_left.mp (hdisj_m a b heq)
          (Finset.mem_insert_self _ _) (hba ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hhp_nTp : ∀ a : Fin (65 * k), hp a ∉ Tp := by
      intro a hmem; rw [Finset.mem_image] at hmem
      obtain ⟨b, _, hba⟩ := hmem
      by_cases heq : a = b
      · exact (hmem_p a).2.2.1 (heq ▸ hba)
      · exact Finset.disjoint_left.mp (hdisj_p a b heq)
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) (hba ▸ Finset.mem_insert_self _ _)
    have hTm_sub_Dm : Tm ⊆ Dm := by
      intro w hw; rw [Finset.mem_image] at hw; obtain ⟨a, _, rfl⟩ := hw
      exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
    have hTp_sub_Dp : Tp ⊆ Dp := by
      intro w hw; rw [Finset.mem_image] at hw; obtain ⟨a, _, rfl⟩ := hw
      exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, Finset.mem_insert_self _ _⟩
    have hQ'_sub_Smid : ∀ i, (Q' i).toFinset ⊆ S_mid := fun i w hw => by
      have hwQ := List.mem_toFinset.mp hw
      have hdir := (hQs (eQ i).1).1
      obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hwQ
      dsimp only [Q'] at hidx
      by_cases hlen : (Qs (eQ i).1).length = 1
      · have hi0 : idx = 0 := by omega
        subst hi0
        have := (hQs (eQ i).1).2.choose_spec.1
        rw [List.head_eq_getElem_zero] at this
        exact Finset.mem_union_left _ (Finset.mem_union_right _ this)
      · by_cases hlt : idx + 1 < (Qs (eQ i).1).length
        · exact (hdir.2.2 idx hlt).1
        · have hsub : idx - 1 + 1 = idx := by omega
          simpa only [Q', hsub] using (hdir.2.2 (idx - 1) (by omega)).2.1
    have hQ'_disj_B : ∀ i, Disjoint (Q' i).toFinset B_avoid := fun i =>
      (Finset.mem_filter.mp (hgoodQ_sub (eQ i).2)).2
    have hW_mem_base : ∀ t : Fin k,
        ({x t, y t, x' t, y' t, x'' t, y'' t, tm (idxM t), hp (idxP t)} : Finset V) ⊆ W t :=
      fun t => Finset.subset_union_left.trans (Finset.subset_union_left.trans Finset.subset_union_left)
    -- Disjointness of W i and W j for i ≠ j!
    have hW_disj : ∀ i j, i ≠ j → Disjoint (W i) (W j) := by
      intro i j hij
      rw [Finset.disjoint_left]
      intro w hwi hwj
      -- Classify w by membership in terms / Dm / Dp / B_avoid / S \ (X ∪ B_avoid)
      have hW_cases : ∀ t, w ∈ W t →
          (w = x t ∨ w = y t) ∨
          (w = x' t ∨ w = y' t ∨ w = x'' t ∨ w = y'' t) ∨
          (w = tm (idxM t)) ∨
          (w = hp (idxP t)) ∨
          (w ∈ (Pm t).toFinset) ∨
          (w ∈ (Q' t).toFinset) ∨
          (w ∈ (Pp t).toFinset) := by
        intro t hw
        simp only [W, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with (((h | hPm) | hQ) | hPp)
        · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact Or.inl (Or.inl rfl)
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr (Or.inl (Or.inl rfl))
          · exact Or.inr (Or.inl (Or.inr (Or.inl rfl)))
          · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl rfl))))
          · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr rfl))))
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hPm))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hQ)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hPp)))))
      have hnot_xy_other : ∀ t₁ t₂, t₁ ≠ t₂ → (w = x t₁ ∨ w = y t₁) → w ∈ W t₂ → False := by
        intro t₁ t₂ hne hxy hw2
        have hw_terms : w ∈ terms := by
          rcases hxy with rfl | rfl
          · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t₁, Finset.mem_univ _, rfl⟩)
          · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t₁, Finset.mem_univ _, rfl⟩)
        have hw_X : w ∈ X := Finset.mem_union_left _ (Finset.mem_union_left _ hw_terms)
        rcases hW_cases t₂ hw2 with h | h | h | h | h | h | h
        · rcases hxy with rfl | rfl <;> rcases h with h' | h'
          · exact hne (hx_inj h')
          · exact hxy_disj t₁ t₂ h'
          · exact hxy_disj t₂ t₁ h'.symm
          · exact hne (hy_inj h')
        · have hwB : w ∈ B_avoid := by
            rcases h with rfl | rfl | rfl | rfl
            · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨t₂.val, by omega⟩, Finset.mem_univ _, rfl⟩)
            · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨k + t₂.val, by omega⟩, Finset.mem_univ _, rfl⟩)
            · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨t₂.val, by omega⟩, Finset.mem_univ _, rfl⟩)
            · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨k + t₂.val, by omega⟩, Finset.mem_univ _, rfl⟩)
          exact Finset.disjoint_left.mp hB_disj_X hwB hw_X
        · exact Finset.disjoint_left.mp hDm_disj_terms
            (h ▸ Finset.mem_biUnion.mpr ⟨idxM t₂, Finset.mem_univ _, Finset.mem_insert_self _ _⟩) hw_terms
        · exact Finset.disjoint_left.mp hDp_disj_terms
            (h ▸ Finset.mem_biUnion.mpr ⟨idxP t₂, Finset.mem_univ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩) hw_terms
        · exact Finset.disjoint_left.mp hDm_disj_terms (hTm_sub_Dm (hPm_sub_Tm t₂ h)) hw_terms
        · have hwSm := hQ'_sub_Smid t₂ h
          rcases Finset.mem_union.mp hwSm with h1 | h2
          · rcases Finset.mem_union.mp h1 with h3 | h4
            · exact (Finset.mem_sdiff.mp h3).2 hw_X
            · exact Finset.disjoint_left.mp hDm_disj_terms (hTm_sub_Dm (hYm_Tm h4)) hw_terms
          · exact Finset.disjoint_left.mp hDp_disj_terms (hTp_sub_Dp (hXp_Tp h2)) hw_terms
        · exact Finset.disjoint_left.mp hDp_disj_terms (hTp_sub_Dp (hPp_sub_Tp t₂ h)) hw_terms
      have hnot_B_other : ∀ t₁ t₂, t₁ ≠ t₂ →
          (w = x' t₁ ∨ w = y' t₁ ∨ w = x'' t₁ ∨ w = y'' t₁) → w ∈ W t₂ → False := by
        intro t₁ t₂ hne hB1 hw2
        have hwB : w ∈ B_avoid := by
          rcases hB1 with rfl | rfl | rfl | rfl
          · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨t₁.val, by omega⟩, Finset.mem_univ _, rfl⟩)
          · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨k + t₁.val, by omega⟩, Finset.mem_univ _, rfl⟩)
          · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨t₁.val, by omega⟩, Finset.mem_univ _, rfl⟩)
          · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨k + t₁.val, by omega⟩, Finset.mem_univ _, rfl⟩)
        have hwW1 : w ∈ W t₁ := by
          apply hW_mem_base t₁
          rcases hB1 with rfl | rfl | rfl | rfl
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))))
        rcases hW_cases t₂ hw2 with h | h | h | h | h | h | h
        · exact hnot_xy_other t₂ t₁ hne.symm h hwW1
        · -- Both in {x', y', x'', y''} for t₁ ≠ t₂!
          have hf1_eq : ∀ a b : Fin (2 * k), f1 a = f1 b → a = b := fun _ _ h => hf1_inj h
          have hf2_eq : ∀ a b : Fin (2 * k), f2 a = f2 b → a = b := fun _ _ h => hf2_inj h
          have hx'_n_x'' : ∀ a b : Fin k, a ≠ b → x' a ≠ x'' b := by
            intro a b hab heq
            by_cases hbE : x' b ∈ Em b
            · have hfx : f1 ⟨a.val, by omega⟩ = f2 ⟨b.val, by omega⟩ := heq
              exact hf2_x_nX' b hbE (hfx ▸ Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨a.val, by omega⟩, Finset.mem_univ _, rfl⟩))
            · have hm := hf2_mem ⟨b.val, by omega⟩
              simp only [hopPool, b.isLt, ↓reduceDIte, hbE, ↓reduceIte, Finset.mem_singleton] at hm
              have hval : a.val = b.val := Fin.mk.inj (hf1_inj (heq.trans hm))
              exact hab (Fin.ext hval)
          have hx'_n_y'' : ∀ a b : Fin k, x' a ≠ y'' b := by
            intro a b heq
            by_cases hbE : y' b ∈ Ep b
            · have hfx : f1 ⟨a.val, by omega⟩ = f2 ⟨k + b.val, by omega⟩ := heq
              exact hf2_y_nX' b hbE (hfx ▸ Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨a.val, by omega⟩, Finset.mem_univ _, rfl⟩))
            · have hm := hf2_mem ⟨k + b.val, by omega⟩
              have hnot : ¬ (k + b.val < k) := by omega
              have hsub : k + b.val - k = b.val := by omega
              simp only [hopPool, hnot, ↓reduceDIte, hsub, hbE, ↓reduceIte, Finset.mem_singleton] at hm
              have hval : a.val = k + b.val := Fin.mk.inj (hf1_inj (heq.trans hm))
              omega
          have hy'_n_x'' : ∀ a b : Fin k, y' a ≠ x'' b := by
            intro a b heq
            by_cases hbE : x' b ∈ Em b
            · have hfx : f1 ⟨k + a.val, by omega⟩ = f2 ⟨b.val, by omega⟩ := heq
              exact hf2_x_nX' b hbE (hfx ▸ Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨k + a.val, by omega⟩, Finset.mem_univ _, rfl⟩))
            · have hm := hf2_mem ⟨b.val, by omega⟩
              simp only [hopPool, b.isLt, ↓reduceDIte, hbE, ↓reduceIte, Finset.mem_singleton] at hm
              have hval : k + a.val = b.val := Fin.mk.inj (hf1_inj (heq.trans hm))
              omega
          have hy'_n_y'' : ∀ a b : Fin k, a ≠ b → y' a ≠ y'' b := by
            intro a b hab heq
            by_cases hbE : y' b ∈ Ep b
            · have hfx : f1 ⟨k + a.val, by omega⟩ = f2 ⟨k + b.val, by omega⟩ := heq
              exact hf2_y_nX' b hbE (hfx ▸ Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨k + a.val, by omega⟩, Finset.mem_univ _, rfl⟩))
            · have hm := hf2_mem ⟨k + b.val, by omega⟩
              have hnot : ¬ (k + b.val < k) := by omega
              have hsub : k + b.val - k = b.val := by omega
              simp only [hopPool, hnot, ↓reduceDIte, hsub, hbE, ↓reduceIte, Finset.mem_singleton] at hm
              have hval : k + a.val = k + b.val := Fin.mk.inj (hf1_inj (heq.trans hm))
              exact hab (Fin.ext (by omega))
          rcases hB1 with rfl | rfl | rfl | rfl <;> rcases h with h' | h' | h' | h'
          · exact hne (Fin.ext (Fin.mk.inj (hf1_inj h')))
          · have hval : t₁.val = k + t₂.val := Fin.mk.inj (hf1_inj h'); omega
          · exact hx'_n_x'' t₁ t₂ hne h'
          · exact hx'_n_y'' t₁ t₂ h'
          · have hval : k + t₁.val = t₂.val := Fin.mk.inj (hf1_inj h'); omega
          · have hval : k + t₁.val = k + t₂.val := Fin.mk.inj (hf1_inj h'); exact hne (Fin.ext (by omega))
          · exact hy'_n_x'' t₁ t₂ h'
          · exact hy'_n_y'' t₁ t₂ hne h'
          · exact hx'_n_x'' t₂ t₁ hne.symm h'.symm
          · exact hy'_n_x'' t₂ t₁ h'.symm
          · exact hne (Fin.ext (Fin.mk.inj (hf2_inj h')))
          · have hval : t₁.val = k + t₂.val := Fin.mk.inj (hf2_inj h'); omega
          · exact hx'_n_y'' t₂ t₁ h'.symm
          · exact hy'_n_y'' t₂ t₁ hne.symm h'.symm
          · have hval : k + t₁.val = t₂.val := Fin.mk.inj (hf2_inj h'); omega
          · have hval : k + t₁.val = k + t₂.val := Fin.mk.inj (hf2_inj h'); exact hne (Fin.ext (by omega))
        · exact Finset.disjoint_left.mp hB_disj_X hwB
            (Finset.mem_union_left _ (Finset.mem_union_right _
              (h ▸ Finset.mem_biUnion.mpr ⟨idxM t₂, Finset.mem_univ _, Finset.mem_insert_self _ _⟩)))
        · exact Finset.disjoint_left.mp hB_disj_X hwB
            (Finset.mem_union_right _
              (h ▸ Finset.mem_biUnion.mpr ⟨idxP t₂, Finset.mem_univ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩))
        · exact Finset.disjoint_left.mp hB_disj_X hwB
            (Finset.mem_union_left _ (Finset.mem_union_right _ (hTm_sub_Dm (hPm_sub_Tm t₂ h))))
        · exact Finset.disjoint_left.mp (hQ'_disj_B t₂) h hwB
        · exact Finset.disjoint_left.mp hB_disj_X hwB
            (Finset.mem_union_right _ (hTp_sub_Dp (hPp_sub_Tp t₂ h)))
      have hnot_tm_other : ∀ t₁ t₂, t₁ ≠ t₂ → w = tm (idxM t₁) → w ∈ W t₂ → False := by
        intro t₁ t₂ hne htm1 hw2
        have hw_Dm : w ∈ Dm := htm1 ▸ Finset.mem_biUnion.mpr ⟨idxM t₁, Finset.mem_univ _, Finset.mem_insert_self _ _⟩
        have hw_X : w ∈ X := Finset.mem_union_left _ (Finset.mem_union_right _ hw_Dm)
        have hwW1 : w ∈ W t₁ := htm1 ▸ hW_mem_base t₁
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_insert_self _ _)))))))
        rcases hW_cases t₂ hw2 with h | h | h | h | h | h | h
        · exact hnot_xy_other t₂ t₁ hne.symm h hwW1
        · exact hnot_B_other t₂ t₁ hne.symm h hwW1
        · exact Finset.disjoint_left.mp (hdisj_m (idxM t₁) (idxM t₂) (fun e => hne (hidxM_inj e)))
            (Finset.mem_insert_self _ _) (htm1.symm.trans h ▸ Finset.mem_insert_self _ _)
        · exact Finset.disjoint_left.mp hDp_disj_Dm
            (h ▸ Finset.mem_biUnion.mpr ⟨idxP t₂, Finset.mem_univ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩) hw_Dm
        · exact htm_nTm (idxM t₁) (htm1 ▸ hPm_sub_Tm t₂ h)
        · have hwSm := hQ'_sub_Smid t₂ h
          rcases Finset.mem_union.mp hwSm with h1 | h2
          · rcases Finset.mem_union.mp h1 with h3 | h4
            · exact (Finset.mem_sdiff.mp h3).2 hw_X
            · exact htm_nTm (idxM t₁) (htm1 ▸ hYm_Tm h4)
          · exact Finset.disjoint_left.mp hDp_disj_Dm (hTp_sub_Dp (hXp_Tp h2)) hw_Dm
        · exact Finset.disjoint_left.mp hDp_disj_Dm (hTp_sub_Dp (hPp_sub_Tp t₂ h)) hw_Dm
      have hnot_hp_other : ∀ t₁ t₂, t₁ ≠ t₂ → w = hp (idxP t₁) → w ∈ W t₂ → False := by
        intro t₁ t₂ hne hhp1 hw2
        have hw_Dp : w ∈ Dp := hhp1 ▸ Finset.mem_biUnion.mpr ⟨idxP t₁, Finset.mem_univ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
        have hw_X : w ∈ X := Finset.mem_union_right _ hw_Dp
        have hwW1 : w ∈ W t₁ := hhp1 ▸ hW_mem_base t₁
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))))))
        rcases hW_cases t₂ hw2 with h | h | h | h | h | h | h
        · exact hnot_xy_other t₂ t₁ hne.symm h hwW1
        · exact hnot_B_other t₂ t₁ hne.symm h hwW1
        · exact hnot_tm_other t₂ t₁ hne.symm h hwW1
        · exact Finset.disjoint_left.mp (hdisj_p (idxP t₁) (idxP t₂) (fun e => hne (hidxP_inj e)))
            (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
            (hhp1.symm.trans h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        · exact Finset.disjoint_left.mp hDp_disj_Dm hw_Dp (hTm_sub_Dm (hPm_sub_Tm t₂ h))
        · have hwSm := hQ'_sub_Smid t₂ h
          rcases Finset.mem_union.mp hwSm with h1 | h2
          · rcases Finset.mem_union.mp h1 with h3 | h4
            · exact (Finset.mem_sdiff.mp h3).2 hw_X
            · exact Finset.disjoint_left.mp hDp_disj_Dm hw_Dp (hTm_sub_Dm (hYm_Tm h4))
          · exact hhp_nTp (idxP t₁) (hhp1 ▸ hXp_Tp h2)
        · exact hhp_nTp (idxP t₁) (hhp1 ▸ hPp_sub_Tp t₂ h)
      rcases hW_cases i hwi with h1 | h1 | h1 | h1 | h1 | h1 | h1
      · exact hnot_xy_other i j hij h1 hwj
      · exact hnot_B_other i j hij h1 hwj
      · exact hnot_tm_other i j hij h1 hwj
      · exact hnot_hp_other i j hij h1 hwj
      · rcases hW_cases j hwj with h2 | h2 | h2 | h2 | h2 | h2 | h2
        · exact hnot_xy_other j i hij.symm h2 hwi
        · exact hnot_B_other j i hij.symm h2 hwi
        · exact hnot_tm_other j i hij.symm h2 hwi
        · exact hnot_hp_other j i hij.symm h2 hwi
        · exact Finset.disjoint_left.mp (hPm_disj i j hij) h1 h2
        · -- w ∈ Pm i (⊆ Tm ⊆ Dm) and w ∈ Q' j (⊆ (S\X) ∪ Ym ∪ Xp) ⇒ w ∈ Ym ⇒ w = vM0 i AND w = vM0 j!
          have hwYm : w ∈ Ym := by
            have hwSm := hQ'_sub_Smid j h2
            rcases Finset.mem_union.mp hwSm with ha | hb
            · rcases Finset.mem_union.mp ha with hc | hd
              · exact absurd (Finset.mem_union_left _ (Finset.mem_union_right _ (hTm_sub_Dm (hPm_sub_Tm i h1))))
                  (Finset.mem_sdiff.mp hc).2
              · exact hd
            · exact absurd (hTp_sub_Dp (hXp_Tp hb))
                (Finset.disjoint_right.mp hDp_disj_Dm (hTm_sub_Dm (hPm_sub_Tm i h1)))
          have heq1 := hPm_meet_Ym i w (List.mem_toFinset.mp h1) hwYm
          have heq2 := hQ'_meet_Ym j w (List.mem_toFinset.mp h2) hwYm
          exact hij (hvM0_inj (heq1.symm.trans heq2))
        · exact Finset.disjoint_left.mp hDp_disj_Dm (hTp_sub_Dp (hPp_sub_Tp j h2)) (hTm_sub_Dm (hPm_sub_Tm i h1))
      · rcases hW_cases j hwj with h2 | h2 | h2 | h2 | h2 | h2 | h2
        · exact hnot_xy_other j i hij.symm h2 hwi
        · exact hnot_B_other j i hij.symm h2 hwi
        · exact hnot_tm_other j i hij.symm h2 hwi
        · exact hnot_hp_other j i hij.symm h2 hwi
        · have hwYm : w ∈ Ym := by
            have hwSm := hQ'_sub_Smid i h1
            rcases Finset.mem_union.mp hwSm with ha | hb
            · rcases Finset.mem_union.mp ha with hc | hd
              · exact absurd (Finset.mem_union_left _ (Finset.mem_union_right _ (hTm_sub_Dm (hPm_sub_Tm j h2))))
                  (Finset.mem_sdiff.mp hc).2
              · exact hd
            · exact absurd (hTp_sub_Dp (hXp_Tp hb))
                (Finset.disjoint_right.mp hDp_disj_Dm (hTm_sub_Dm (hPm_sub_Tm j h2)))
          have heq1 := hQ'_meet_Ym i w (List.mem_toFinset.mp h1) hwYm
          have heq2 := hPm_meet_Ym j w (List.mem_toFinset.mp h2) hwYm
          exact hij (hvM0_inj (heq1.symm.trans heq2))
        · exact Finset.disjoint_left.mp
            (hQs_disj (eQ i).1 (eQ j).1 (fun h => hij (eQ.injective (Subtype.ext h)))) h1 h2
        · have hwXp : w ∈ Xp := by
            have hwSm := hQ'_sub_Smid i h1
            rcases Finset.mem_union.mp hwSm with ha | hb
            · rcases Finset.mem_union.mp ha with hc | hd
              · exact absurd (Finset.mem_union_right _ (hTp_sub_Dp (hPp_sub_Tp j h2)))
                  (Finset.mem_sdiff.mp hc).2
              · exact absurd (hTm_sub_Dm (hYm_Tm hd))
                  (Finset.disjoint_left.mp hDp_disj_Dm (hTp_sub_Dp (hPp_sub_Tp j h2)))
            · exact hb
          have heq1 := hQ'_meet_Xp i w (List.mem_toFinset.mp h1) hwXp
          have heq2 := hPp_meet_Xp j w (List.mem_toFinset.mp h2) hwXp
          exact hij (huP0_inj (heq1.symm.trans heq2))
      · rcases hW_cases j hwj with h2 | h2 | h2 | h2 | h2 | h2 | h2
        · exact hnot_xy_other j i hij.symm h2 hwi
        · exact hnot_B_other j i hij.symm h2 hwi
        · exact hnot_tm_other j i hij.symm h2 hwi
        · exact hnot_hp_other j i hij.symm h2 hwi
        · exact Finset.disjoint_left.mp hDp_disj_Dm (hTp_sub_Dp (hPp_sub_Tp i h1)) (hTm_sub_Dm (hPm_sub_Tm j h2))
        · have hwXp : w ∈ Xp := by
            have hwSm := hQ'_sub_Smid j h2
            rcases Finset.mem_union.mp hwSm with ha | hb
            · rcases Finset.mem_union.mp ha with hc | hd
              · exact absurd (Finset.mem_union_right _ (hTp_sub_Dp (hPp_sub_Tp i h1)))
                  (Finset.mem_sdiff.mp hc).2
              · exact absurd (hTm_sub_Dm (hYm_Tm hd))
                  (Finset.disjoint_left.mp hDp_disj_Dm (hTp_sub_Dp (hPp_sub_Tp i h1)))
            · exact hb
          have heq1 := hPp_meet_Xp i w (List.mem_toFinset.mp h1) hwXp
          have heq2 := hQ'_meet_Xp j w (List.mem_toFinset.mp h2) hwXp
          exact hij (huP0_inj (heq1.symm.trans heq2))
        · exact Finset.disjoint_left.mp (hPp_disj i j hij) h1 h2
    -- Every W i ⊆ S and has a ReflTransGen walk from x i to y i!
    have hW_sub_S : ∀ i, W i ⊆ S := by
      intro i w hw
      have hB_S : ∀ t, f1 t ∈ S ∧ f2 t ∈ S := by
        intro t
        have h1 : f1 t ∈ S := by
          have hm := hf1_mem t; dsimp only [nbrPool] at hm
          split_ifs at hm <;> exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hm).1).1
        have h2 : f2 t ∈ S := by
          have hm := hf2_mem t; dsimp only [hopPool] at hm
          split_ifs at hm with hlt hE
          · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hm).1).1
          · rw [Finset.mem_singleton] at hm; rw [hm]
            have hm' := hf1_mem ⟨t.val, by omega⟩; dsimp only [nbrPool] at hm'
            simp only [hlt, ↓reduceDIte] at hm'; exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hm').1).1
          · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hm).1).1
          · rw [Finset.mem_singleton] at hm; rw [hm]
            have hm' := hf1_mem ⟨k + (t.val - k), by omega⟩; dsimp only [nbrPool] at hm'
            have hnot : ¬ (k + (t.val - k) < k) := by omega
            simp only [hnot, ↓reduceDIte] at hm'; exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hm').1).1
        exact ⟨h1, h2⟩
      simp only [W, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with (((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hPm) | hQ') | hPp
      · exact hxS i
      · exact hyS i
      · exact (hB_S ⟨i.val, by omega⟩).1
      · exact (hB_S ⟨k + i.val, by omega⟩).1
      · exact (hB_S ⟨i.val, by omega⟩).2
      · exact (hB_S ⟨k + i.val, by omega⟩).2
      · exact Finset.sdiff_subset (hmem_m (idxM i)).1
      · exact Finset.sdiff_subset (Finset.sdiff_subset (hmem_p (idxP i)).2.1)
      · exact Finset.sdiff_subset (hDm_sub (hTm_sub_Dm (hPm_sub_Tm i hPm)))
      · exact hSmid_sub (hQ'_sub_Smid i hQ')
      · exact Finset.sdiff_subset (Finset.sdiff_subset (hDp_sub (hTp_sub_Dp (hPp_sub_Tp i hPp))))
    have hW_walk : ∀ i, ∃ P : List V, IsDirPathBetween G.Adj (x i) (y i) P ∧ ∀ w ∈ P, w ∈ W i := by
      intro i
      let Wi : Set V := (W i : Set V)
      have hxW : x i ∈ Wi := hW_mem_base i (Finset.mem_insert_self _ _)
      have hyW : y i ∈ Wi := hW_mem_base i (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have hx'W : x' i ∈ Wi := hW_mem_base i (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
      have hy'W : y' i ∈ Wi := hW_mem_base i (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))
      have hx''W : x'' i ∈ Wi := hW_mem_base i (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))))
      have hy''W : y'' i ∈ Wi := hW_mem_base i (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))))
      have htmW : tm (idxM i) ∈ Wi := hW_mem_base i (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))))))
      have hhpW : hp (idxP i) ∈ Wi := hW_mem_base i (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))))))
      have hhmW : hm (idxM i) ∈ Wi := by
        obtain ⟨_, hne, hh, _⟩ := hPm_bet i
        change (Pm i).head hne = hm (idxM i) at hh
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (List.mem_toFinset.mpr (hh ▸ List.head_mem hne))))
      have htpW : tp (idxP i) ∈ Wi := by
        obtain ⟨_, hne, _, hl⟩ := hPp_bet i
        change (Pp i).getLast hne = tp (idxP i) at hl
        exact Finset.mem_union_right _ (List.mem_toFinset.mpr (hl ▸ List.getLast_mem hne))
      -- Step a: x i → x' i
      have hstep_x : Relation.ReflTransGen (fun a b => a ∈ Wi ∧ b ∈ Wi ∧ G.Adj a b) (x i) (x' i) := by
        have hm := hf1_mem ⟨i.val, by omega⟩; dsimp only [nbrPool] at hm
        rw [dif_pos i.isLt] at hm
        exact Relation.ReflTransGen.single ⟨hxW, hx'W, (Finset.mem_filter.mp (Finset.mem_sdiff.mp hm).1).2⟩
      -- Step b: x' i → x'' i (0 or 1 step)
      have hstep_x' : Relation.ReflTransGen (fun a b => a ∈ Wi ∧ b ∈ Wi ∧ G.Adj a b) (x' i) (x'' i) := by
        have hm := hf2_mem ⟨i.val, by omega⟩; dsimp only [hopPool] at hm
        rw [dif_pos i.isLt] at hm
        split_ifs at hm with hE
        · exact Relation.ReflTransGen.single ⟨hx'W, hx''W, (Finset.mem_filter.mp (Finset.mem_sdiff.mp hm).1).2⟩
        · rw [Finset.mem_singleton] at hm
          change x'' i = x' i at hm
          rw [hm]
      -- Step c: x'' i → hm (idxM i) (1 or 2 steps, since x'' i ∈ S \ X and x'' i ∉ Em i!)
      have hstep_xm : Relation.ReflTransGen (fun a b => a ∈ Wi ∧ b ∈ Wi ∧ G.Adj a b) (x'' i) (hm (idxM i)) := by
        have hx''_nEm : x'' i ∉ Em i := by
          have hm := hf2_mem ⟨i.val, by omega⟩; dsimp only [hopPool] at hm
          rw [dif_pos i.isLt] at hm
          split_ifs at hm with hE
          · exact fun h => (Finset.mem_sdiff.mp hm).2 (Finset.mem_union_left _ h)
          · rw [Finset.mem_singleton] at hm; change x'' i = x' i at hm; rw [hm]; exact hE
        have hx''_S : x'' i ∈ S := hW_sub_S i hx''W
        have hx''_nX : x'' i ∉ X := Finset.disjoint_left.mp hB_disj_X
          (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨i.val, by omega⟩, Finset.mem_univ _, rfl⟩))
        have hnot_both : ¬ (G.Adj (tm (idxM i)) (x'' i) ∧ G.Adj (hm (idxM i)) (x'' i)) := fun h =>
          hx''_nEm (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hx''_S, hx''_nX⟩, h⟩)
        have hne_hm : x'' i ≠ hm (idxM i) := fun h =>
          hx''_nX (Finset.mem_union_left _ (Finset.mem_union_right _
            (h ▸ Finset.mem_biUnion.mpr ⟨idxM i, Finset.mem_univ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)))
        have hne_tm : x'' i ≠ tm (idxM i) := fun h =>
          hx''_nX (Finset.mem_union_left _ (Finset.mem_union_right _
            (h ▸ Finset.mem_biUnion.mpr ⟨idxM i, Finset.mem_univ _, Finset.mem_insert_self _ _⟩)))
        by_cases hadj_h : G.Adj (x'' i) (hm (idxM i))
        · exact Relation.ReflTransGen.single ⟨hx''W, hhmW, hadj_h⟩
        · have hrev_h : G.Adj (hm (idxM i)) (x'' i) :=
            not_not.mp fun h => hadj_h ((hT.2 _ _ hne_hm).mpr h)
          have hadj_t : G.Adj (x'' i) (tm (idxM i)) := by
            by_contra hnot
            have hrev_t : G.Adj (tm (idxM i)) (x'' i) :=
              not_not.mp fun h => hnot ((hT.2 _ _ hne_tm).mpr h)
            exact hnot_both ⟨hrev_t, hrev_h⟩
          exact (Relation.ReflTransGen.single ⟨hx''W, htmW, hadj_t⟩).trans
            (Relation.ReflTransGen.single ⟨htmW, hhmW, (hmem_m (idxM i)).2.2.2⟩)
      -- Step d: hm (idxM i) → vM0 i via Pm i
      have hstep_Pm : Relation.ReflTransGen (fun a b => a ∈ Wi ∧ b ∈ Wi ∧ G.Adj a b) (hm (idxM i)) (vM0 i) :=
        reflTransGen_of_isDirPathBetween (hPm_bet i) fun w hw =>
          Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (List.mem_toFinset.mpr hw)))
      -- Step e: vM0 i → uP0 i via Q' i
      have hstep_Q' : Relation.ReflTransGen (fun a b => a ∈ Wi ∧ b ∈ Wi ∧ G.Adj a b) (vM0 i) (uP0 i) := by
        have hbet : IsDirPathBetween G.Adj (vM0 i) (uP0 i) (Q' i) :=
          ⟨isDirPath_mono (fun _ _ h => h.2.2) (hQs (eQ i).1).1, (hQs (eQ i).1).1.1, rfl, rfl⟩
        exact reflTransGen_of_isDirPathBetween hbet fun w hw =>
          Finset.mem_union_left _ (Finset.mem_union_right _ (List.mem_toFinset.mpr hw))
      -- Step f: uP0 i → tp (idxP i) via Pp i
      have hstep_Pp : Relation.ReflTransGen (fun a b => a ∈ Wi ∧ b ∈ Wi ∧ G.Adj a b) (uP0 i) (tp (idxP i)) :=
        reflTransGen_of_isDirPathBetween (hPp_bet i) fun w hw =>
          Finset.mem_union_right _ (List.mem_toFinset.mpr hw)
      -- Step g: tp (idxP i) → y'' i (1 or 2 steps, since y'' i ∉ Ep i!)
      have hstep_py : Relation.ReflTransGen (fun a b => a ∈ Wi ∧ b ∈ Wi ∧ G.Adj a b) (tp (idxP i)) (y'' i) := by
        have hy''_nEp : y'' i ∉ Ep i := by
          have hm := hf2_mem ⟨k + i.val, by omega⟩; dsimp only [hopPool] at hm
          have hnot : ¬ (k + i.val < k) := by omega
          have hsub : k + i.val - k = i.val := by omega
          simp only [hnot, ↓reduceDIte, hsub] at hm
          split_ifs at hm with hE
          · exact fun h => (Finset.mem_sdiff.mp hm).2 (Finset.mem_union_left _ h)
          · rw [Finset.mem_singleton] at hm; change y'' i = y' i at hm; rw [hm]; exact hE
        have hy''_S : y'' i ∈ S := hW_sub_S i hy''W
        have hy''_nX : y'' i ∉ X := Finset.disjoint_left.mp hB_disj_X
          (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨k + i.val, by omega⟩, Finset.mem_univ _, rfl⟩))
        have hnot_both : ¬ (G.Adj (y'' i) (tp (idxP i)) ∧ G.Adj (y'' i) (hp (idxP i))) := fun h =>
          hy''_nEp (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hy''_S, hy''_nX⟩, h⟩)
        have hne_tp : tp (idxP i) ≠ y'' i := fun h =>
          hy''_nX (Finset.mem_union_right _
            (h ▸ Finset.mem_biUnion.mpr ⟨idxP i, Finset.mem_univ _, Finset.mem_insert_self _ _⟩))
        have hne_hp : hp (idxP i) ≠ y'' i := fun h =>
          hy''_nX (Finset.mem_union_right _
            (h ▸ Finset.mem_biUnion.mpr ⟨idxP i, Finset.mem_univ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩))
        by_cases hadj_t : G.Adj (tp (idxP i)) (y'' i)
        · exact Relation.ReflTransGen.single ⟨htpW, hy''W, hadj_t⟩
        · have hrev_t : G.Adj (y'' i) (tp (idxP i)) :=
            not_not.mp fun h => hadj_t ((hT.2 _ _ hne_tp).mpr h)
          have hadj_h : G.Adj (hp (idxP i)) (y'' i) := by
            by_contra hnot
            have hrev_h : G.Adj (y'' i) (hp (idxP i)) :=
              not_not.mp fun h => hnot ((hT.2 _ _ hne_hp).mpr h)
            exact hnot_both ⟨hrev_t, hrev_h⟩
          exact (Relation.ReflTransGen.single ⟨htpW, hhpW, (hmem_p (idxP i)).2.2.2⟩).trans
            (Relation.ReflTransGen.single ⟨hhpW, hy''W, hadj_h⟩)
      -- Step h: y'' i → y' i (0 or 1 step)
      have hstep_y' : Relation.ReflTransGen (fun a b => a ∈ Wi ∧ b ∈ Wi ∧ G.Adj a b) (y'' i) (y' i) := by
        have hm := hf2_mem ⟨k + i.val, by omega⟩; dsimp only [hopPool] at hm
        have hnot : ¬ (k + i.val < k) := by omega
        have hsub : k + i.val - k = i.val := by omega
        simp only [hnot, ↓reduceDIte, hsub] at hm
        split_ifs at hm with hE
        · exact Relation.ReflTransGen.single ⟨hy''W, hy'W, (Finset.mem_filter.mp (Finset.mem_sdiff.mp hm).1).2⟩
        · rw [Finset.mem_singleton] at hm; change y'' i = y' i at hm; rw [hm]
      -- Step i: y' i → y i
      have hstep_y : Relation.ReflTransGen (fun a b => a ∈ Wi ∧ b ∈ Wi ∧ G.Adj a b) (y' i) (y i) := by
        have hm := hf1_mem ⟨k + i.val, by omega⟩; dsimp only [nbrPool] at hm
        have hnot : ¬ (k + i.val < k) := by omega
        have hsub : k + i.val - k = i.val := by omega
        simp only [hnot, ↓reduceDIte, hsub] at hm
        exact Relation.ReflTransGen.single ⟨hy'W, hyW, (Finset.mem_filter.mp (Finset.mem_sdiff.mp hm).1).2⟩
      have hfull := (((((((hstep_x.trans hstep_x').trans hstep_xm).trans hstep_Pm).trans hstep_Q').trans hstep_Pp).trans hstep_py).trans hstep_y').trans hstep_y
      exact exists_dirPath_of_reflTransGen hxW hfull
    choose Ps hPs_bet hPs_W using hW_walk
    refine ⟨Ps, fun i => ⟨hPs_bet i, fun w hw => hW_sub_S i (hPs_W i w hw)⟩, fun i j hij => ?_⟩
    exact Finset.disjoint_of_subset_left
      (fun w hw => hPs_W i w (List.mem_toFinset.mp hw))
      (Finset.disjoint_of_subset_right
        (fun w hw => hPs_W j w (List.mem_toFinset.mp hw))
        (hW_disj i j hij))

/-! ## Part 4: Short multi-paths, transitive dominating sets (KOT 2.4/2.5), and backwards-transitive paths (KOT 2.7) -/

/-- Short multi-paths lemma (KOT Propositions 2.1–2.2 via Pokrovskiy linkedness):
Given `r` distinct disjoint pairs `(x i, y i)` in `S`, if `S` is strongly `(600 * r * q * s + 2 * r)`-connected
(with `s ≥ 1`), then for each `i : Fin r` there exist `q` internally vertex-disjoint directed paths
`P i a` from `x i` to `y i` in `S`, disjoint from all other terminals and mutually internally
vertex-disjoint across all `(i, a)`, with total internal vertices at most `|S| / s`. -/
private lemma multi_short_paths {G : Digraph V} [DecidableRel G.Adj] (hT : IsTournament G)
    {S : Finset V} {r q s : ℕ} (hs : 1 ≤ s)
    (hstrong : IsKStrongOn G (S : Set V) (600 * (r * q * s) + 2 * r))
    (x y : Fin r → V) (hx_inj : Function.Injective x) (hy_inj : Function.Injective y)
    (hxS : ∀ i, x i ∈ S) (hyS : ∀ i, y i ∈ S) (hxy_disj : ∀ i j, x i ≠ y j) :
    ∃ P : Fin r → Fin q → List V,
      (∀ i a, IsDirPathBetween G.Adj (x i) (y i) (P i a) ∧ ∀ w ∈ P i a, w ∈ S) ∧
      (∀ i a, ∀ w ∈ P i a, w ≠ x i → w ≠ y i →
        w ∉ (Finset.univ.image x ∪ Finset.univ.image y)) ∧
      (∀ i₁ a₁ i₂ a₂, (i₁, a₁) ≠ (i₂, a₂) →
        Disjoint ((P i₁ a₁).toFinset \ {x i₁, y i₁}) ((P i₂ a₂).toFinset \ {x i₂, y i₂})) ∧
      (Finset.univ.biUnion fun p : Fin r × Fin q => (P p.1 p.2).toFinset \ {x p.1, y p.1}).card ≤ S.card / s := by
  classical
  let terms : Finset V := Finset.univ.image x ∪ Finset.univ.image y
  have hterms_sub : terms ⊆ S := by
    intro w hw; rcases Finset.mem_union.mp hw with h | h <;> rw [Finset.mem_image] at h
    · obtain ⟨i, _, rfl⟩ := h; exact hxS i
    · obtain ⟨i, _, rfl⟩ := h; exact hyS i
  have hterms_card : terms.card = 2 * r := by
    have hdisj : Disjoint (Finset.univ.image x) (Finset.univ.image y) := by
      rw [Finset.disjoint_left]; intro w h1 h2; rw [Finset.mem_image] at h1 h2
      obtain ⟨i, _, rfl⟩ := h1; obtain ⟨j, _, hj⟩ := h2; exact hxy_disj i j hj.symm
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hx_inj,
      Finset.card_image_of_injective _ hy_inj, Finset.card_univ, Fintype.card_fin]; omega
  let M : ℕ := r * q * s
  -- Index Fin M ≃ Fin r × Fin q × Fin s
  let eM : Fin M ≃ Fin r × Fin q × Fin s :=
    (Fintype.equivFinOfCardEq (by simp [M, mul_assoc])).symm
  -- Pick 2M distinct out/in neighbors outside `terms`
  let pool : Fin (2 * M) → Finset V := fun t =>
    if ht : t.val < M then outNbr G S (x (eM ⟨t.val, ht⟩).1) \ terms
    else inNbr G S (y (eM ⟨t.val - M, by omega⟩).1) \ terms
  have hpool_ge : ∀ t : Fin (2 * M), 2 * M ≤ (pool t).card := by
    intro t; dsimp only [pool]; split_ifs with ht
    · have hd := min_outDeg_of_isKStrongOn hT hstrong (hxS (eM ⟨t.val, ht⟩).1)
      have hsd := Finset.card_sdiff_add_card_inter (outNbr G S (x (eM ⟨t.val, ht⟩).1)) terms
      have hint : (outNbr G S (x (eM ⟨t.val, ht⟩).1) ∩ terms).card ≤ terms.card :=
        Finset.card_le_card Finset.inter_subset_right
      change (outNbr G S (x (eM ⟨t.val, ht⟩).1) \ terms).card +
          (outNbr G S (x (eM ⟨t.val, ht⟩).1) ∩ terms).card =
          outDeg G S (x (eM ⟨t.val, ht⟩).1) at hsd
      omega
    · have hd := min_inDeg_of_isKStrongOn hT hstrong (hyS (eM ⟨t.val - M, by omega⟩).1)
      have hsd := Finset.card_sdiff_add_card_inter (inNbr G S (y (eM ⟨t.val - M, by omega⟩).1)) terms
      have hint : (inNbr G S (y (eM ⟨t.val - M, by omega⟩).1) ∩ terms).card ≤ terms.card :=
        Finset.card_le_card Finset.inter_subset_right
      change (inNbr G S (y (eM ⟨t.val - M, by omega⟩).1) \ terms).card +
          (inNbr G S (y (eM ⟨t.val - M, by omega⟩).1) ∩ terms).card =
          inDeg G S (y (eM ⟨t.val - M, by omega⟩).1) at hsd
      omega
  obtain ⟨f, hf_inj, hf_mem⟩ := greedy_distinct_choice (2 * M) pool hpool_ge
  let x' : Fin M → V := fun m => f ⟨m.val, by omega⟩
  let y' : Fin M → V := fun m => f ⟨M + m.val, by omega⟩
  have hx'_inj : Function.Injective x' := fun m₁ m₂ h => Fin.ext (congrArg (Fin.val : Fin (2 * M) → ℕ) (hf_inj h))
  have hy'_inj : Function.Injective y' := fun m₁ m₂ h => Fin.ext (by have : M + m₁.val = M + m₂.val := congrArg (Fin.val : Fin (2 * M) → ℕ) (hf_inj h); omega)
  have hxy'_disj : ∀ m₁ m₂, x' m₁ ≠ y' m₂ := fun m₁ m₂ h => by
    have : m₁.val = M + m₂.val := congrArg (Fin.val : Fin (2 * M) → ℕ) (hf_inj h); omega
  have hx'_mem : ∀ m, x' m ∈ S \ terms ∧ G.Adj (x (eM m).1) (x' m) := fun m => by
    have hm := hf_mem ⟨m.val, by omega⟩; dsimp only [pool] at hm
    simp only [m.isLt, ↓reduceDIte, Finset.mem_sdiff, outNbr, Finset.mem_filter] at hm
    exact ⟨Finset.mem_sdiff.mpr ⟨hm.1.1, hm.2⟩, hm.1.2⟩
  have hy'_mem : ∀ m, y' m ∈ S \ terms ∧ G.Adj (y' m) (y (eM m).1) := fun m => by
    have hm := hf_mem ⟨M + m.val, by omega⟩; dsimp only [pool] at hm
    have hnot : ¬ (M + m.val < M) := by omega
    have hsub : M + m.val - M = m.val := by omega
    simp only [hnot, ↓reduceDIte, hsub, Finset.mem_sdiff, inNbr, Finset.mem_filter] at hm
    exact ⟨Finset.mem_sdiff.mpr ⟨hm.1.1, hm.2⟩, hm.1.2⟩
  -- S \ terms is (600 * M)-strong!
  have hS'_strong : IsKStrongOn G ((S \ terms : Finset V) : Set V) (600 * M) := by
    refine ⟨?_, ?_⟩
    · rw [Set.ncard_coe_finset, Finset.card_sdiff_of_subset hterms_sub, hterms_card]
      have hgt : 600 * M + 2 * r < S.card := by simpa [Set.ncard_coe_finset] using hstrong.1
      omega
    · intro Z hZ
      have heq : (((S \ terms : Finset V) : Set V) \ (Z : Set V)) =
          ((S : Set V) \ ((terms ∪ Z : Finset V) : Set V)) := by
        ext w; simp; tauto
      rw [heq]
      have hUZ : (terms ∪ Z).card < 600 * M + 2 * r := by
        have := Finset.card_union_le terms Z; omega
      exact hstrong.2 (terms ∪ Z) hUZ
  obtain ⟨Qs, hQs, hQs_disj⟩ := pokrovskiy_linked hT hS'_strong x' y' hx'_inj hy'_inj
    (fun m => (hx'_mem m).1) (fun m => (hy'_mem m).1) hxy'_disj
  -- Pigeonhole over b : Fin s
  let U : Fin s → Finset V := fun b =>
    Finset.univ.biUnion fun p : Fin r × Fin q => (Qs (eM.symm (p.1, p.2, b))).toFinset
  have hU_disj : ∀ b₁ b₂ : Fin s, b₁ ≠ b₂ → Disjoint (U b₁) (U b₂) := by
    intro b₁ b₂ hne
    rw [Finset.disjoint_left]; intro w hw1 hw2
    rw [Finset.mem_biUnion] at hw1 hw2
    obtain ⟨p₁, _, hp1⟩ := hw1; obtain ⟨p₂, _, hp2⟩ := hw2
    have hm_ne : eM.symm (p₁.1, p₁.2, b₁) ≠ eM.symm (p₂.1, p₂.2, b₂) := fun h => by
      have := eM.symm.injective h; exact hne (congrArg (fun z => z.2.2) this)
    exact Finset.disjoint_left.mp (hQs_disj _ _ hm_ne) hp1 hp2
  have hU_sub_S : ∀ b, U b ⊆ S := fun b w hw => by
    rw [Finset.mem_biUnion] at hw; obtain ⟨p, _, hp⟩ := hw
    exact Finset.sdiff_subset ((hQs _).2 w (List.mem_toFinset.mp hp))
  have hsum_U : ∑ b : Fin s, (U b).card ≤ S.card := by
    rw [← Finset.card_biUnion (fun b₁ _ b₂ _ hne => hU_disj b₁ b₂ hne)]
    exact Finset.card_le_card (Finset.biUnion_subset.mpr fun b _ => hU_sub_S b)
  obtain ⟨b₀, _, hb₀_min⟩ := Finset.exists_min_image Finset.univ (fun b : Fin s => (U b).card)
    ⟨⟨0, hs⟩, Finset.mem_univ _⟩
  have hb₀_le : (U b₀).card ≤ S.card / s := by
    have hmul : s * (U b₀).card ≤ ∑ b : Fin s, (U b).card := by
      calc s * (U b₀).card = ∑ _b : Fin s, (U b₀).card := by simp [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ b : Fin s, (U b).card := Finset.sum_le_sum fun b _ => hb₀_min b (Finset.mem_univ _)
    exact (Nat.le_div_iff_mul_le hs).mpr (by rw [Nat.mul_comm]; exact hmul.trans hsum_U)
  -- Define P i a := [x i] ++ Qs (eM.symm (i, a, b₀)) ++ [y i]
  let P : Fin r → Fin q → List V := fun i a =>
    [x i] ++ Qs (eM.symm (i, a, b₀)) ++ [y i]
  have hP_int : ∀ i a, (P i a).toFinset \ {x i, y i} = (Qs (eM.symm (i, a, b₀))).toFinset := by
    intro i a
    ext w
    simp only [P, List.toFinset_append, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨(rfl | hQ) | rfl, hnot⟩
      · exact absurd (Or.inl rfl) hnot
      · exact hQ
      · exact absurd (Or.inr rfl) hnot
    · intro hQ
      have hwS' := (hQs (eM.symm (i, a, b₀))).2 w (List.mem_toFinset.mp hQ)
      have hwnT := (Finset.mem_sdiff.mp hwS').2
      refine ⟨Or.inl (Or.inr hQ), ?_⟩
      rintro (rfl | rfl)
      · exact hwnT (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
      · exact hwnT (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · intro i a
    set m := eM.symm (i, a, b₀)
    have hQm := hQs m
    have heM_eq : (eM m).1 = i := by simp [m]
    have hx_nQ : ∀ w ∈ ([x i] : List V), w ∉ Qs m := by
      intro w hw hQ; simp only [List.mem_singleton] at hw; subst hw
      exact (Finset.mem_sdiff.mp (hQm.2 (x i) hQ)).2
        (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    have hdir1 : IsDirPath G.Adj ([x i] ++ Qs m) := by
      apply isDirPath_append (isDirPath_singleton G.Adj (x i)) hQm.1.1 hx_nQ
      obtain ⟨_, hne, hh, _⟩ := hQm.1
      rw [List.getLast_singleton, hh]
      simpa only [heM_eq] using (hx'_mem m).2
    have hQ1_ny : ∀ w ∈ ([x i] ++ Qs m), w ∉ ([y i] : List V) := by
      intro w hw hyw; simp only [List.mem_singleton] at hyw; subst hyw
      rcases List.mem_append.mp hw with h1 | h2
      · simp only [List.mem_singleton] at h1; exact hxy_disj i i h1.symm
      · exact (Finset.mem_sdiff.mp (hQm.2 (y i) h2)).2
          (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    have hdir2 : IsDirPath G.Adj (P i a) := by
      apply isDirPath_append hdir1 (isDirPath_singleton G.Adj (y i)) hQ1_ny
      obtain ⟨_, hne, _, hl⟩ := hQm.1
      rw [List.getLast_append_of_ne_nil _ hne, hl, List.head_cons]
      simpa only [heM_eq] using (hy'_mem m).2
    refine ⟨⟨hdir2, hdir2.1, ?_, ?_⟩, ?_⟩
    · simp [P]
    · simp [P]
    · intro w hw
      simp only [P, List.mem_append, List.mem_singleton] at hw
      rcases hw with (rfl | hQ) | rfl
      · exact hxS i
      · exact Finset.sdiff_subset (hQm.2 w hQ)
      · exact hyS i
  · intro i a w hw hwx hwy
    have hw_int : w ∈ (P i a).toFinset \ {x i, y i} :=
      Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hw, by simp [hwx, hwy]⟩
    rw [hP_int] at hw_int
    exact (Finset.mem_sdiff.mp ((hQs (eM.symm (i, a, b₀))).2 w (List.mem_toFinset.mp hw_int))).2
  · intro i₁ a₁ i₂ a₂ hne
    rw [hP_int, hP_int]
    apply hQs_disj
    intro heq
    have hthis : (i₁, a₁, b₀) = (i₂, a₂, b₀) := eM.symm.injective heq
    exact hne (Prod.ext (congrArg (fun z => z.1) hthis) (congrArg (fun z => z.2.1) hthis))
  · have heq : (Finset.univ.biUnion fun p : Fin r × Fin q => (P p.1 p.2).toFinset \ {x p.1, y p.1}) = U b₀ := by
      ext w; simp [U, hP_int]
    rw [heq]; exact hb₀_le

/-- A transitive list in `G`: nonempty, nodup, with every earlier vertex having an edge to every later vertex. -/
private def IsTransitiveList (G : Digraph V) (L : List V) : Prop :=
  L ≠ [] ∧ L.Nodup ∧ ∀ i j : ℕ, (hij : i < j) → (hj : j < L.length) → G.Adj L[i] L[j]

omit [Fintype V] in
/-- KOT Lemma 2.4: greedy out-dominating transitive tournament `A` with sink `v` and small uncovered set `E`. -/
private lemma transitive_out_dom_set {G : Digraph V} [DecidableRel G.Adj] (hT : IsTournament G)
    {S : Finset V} {v : V} (hv : v ∈ S) :
    ∀ c : ℕ, 1 ≤ c →
      ∃ (A : List V) (E : Finset V),
        IsTransitiveList G A ∧ A.length ≤ c ∧
        (∃ h : A ≠ [], A.getLast h = v) ∧
        (∀ a ∈ A, a ∈ S) ∧
        E ⊆ S \ A.toFinset ∧
        (∀ w ∈ E, ∀ a ∈ A, G.Adj w a) ∧
        (∀ w ∈ S \ (A.toFinset ∪ E), ∃ a ∈ A, G.Adj a w) ∧
        2 ^ (c - 1) * E.card ≤ inDeg G S v
  | 0, hc => absurd hc (by omega)
  | 1, _ => by
    refine ⟨[v], inNbr G S v,
      ⟨by simp, by simp, fun i j hij hj => by simp at hj; omega⟩,
      by simp, ⟨by simp, rfl⟩,
      fun a ha => by simp at ha; exact ha ▸ hv,
      ?_, ?_, ?_, ?_⟩
    · intro w hw
      rw [Finset.mem_sdiff, List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_singleton]
      have hwf := Finset.mem_filter.mp hw
      exact ⟨hwf.1, fun h => hT.1 v (h ▸ hwf.2)⟩
    · intro w hw a ha; simp at ha; subst ha; exact (Finset.mem_filter.mp hw).2
    · intro w hw
      rw [Finset.mem_sdiff, Finset.mem_union, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
        Finset.mem_singleton, not_or] at hw
      refine ⟨v, List.mem_cons_self, ?_⟩
      by_contra hnot
      have hrev : G.Adj w v := not_not.mp fun h => hnot ((hT.2 v w (Ne.symm hw.2.1)).mpr h)
      exact hw.2.2 (Finset.mem_filter.mpr ⟨hw.1, hrev⟩)
    · simp [inDeg]
  | c + 2, _ => by
    obtain ⟨A, E, hA_trans, hA_len, ⟨hA_ne, hA_last⟩, hA_S, hE_sub, hE_in, hA_dom, hE_card⟩ :=
      transitive_out_dom_set hT hv (c + 1) (by omega)
    by_cases hE_emp : E = ∅
    · subst hE_emp
      exact ⟨A, ∅, hA_trans, by omega, ⟨hA_ne, hA_last⟩, hA_S, hE_sub, hE_in, hA_dom, by simp⟩
    · have hE_ne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hE_emp
      obtain ⟨w, hwE, hw_deg⟩ := exists_large_outDeg hT hE_ne
      have hw_S : w ∈ S := (Finset.mem_sdiff.mp (hE_sub hwE)).1
      have hw_nA : w ∉ A := fun h => (Finset.mem_sdiff.mp (hE_sub hwE)).2 (List.mem_toFinset.mpr h)
      let A' := w :: A
      let E' := inNbr G E w
      have hE'_card : 2 * E'.card ≤ E.card := by
        have hsum := outDeg_add_inDeg_eq hT hwE
        change outDeg G E w + E'.card + 1 = E.card at hsum
        omega
      refine ⟨A', E', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨List.cons_ne_nil _ _, List.nodup_cons.mpr ⟨hw_nA, hA_trans.2.1⟩, fun i j hij hj => ?_⟩
        cases i with
        | zero =>
          cases j with
          | zero => omega
          | succ j' =>
            simp only [A', List.getElem_cons_zero, List.getElem_cons_succ]
            exact hE_in w hwE (A[j']'(by simp [A'] at hj; omega)) (List.getElem_mem (by simp [A'] at hj; omega))
        | succ i' =>
          cases j with
          | zero => omega
          | succ j' =>
            simp only [A', List.getElem_cons_succ]
            exact hA_trans.2.2 i' j' (by omega) (by simp [A'] at hj; omega)
      · simp [A']; omega
      · refine ⟨List.cons_ne_nil _ _, ?_⟩
        rw [List.getLast_cons hA_ne]; exact hA_last
      · intro a ha; rcases List.mem_cons.mp ha with rfl | haA
        · exact hw_S
        · exact hA_S a haA
      · intro z hz
        have hzf := Finset.mem_filter.mp hz
        rw [Finset.mem_sdiff]
        refine ⟨(Finset.mem_sdiff.mp (hE_sub hzf.1)).1, ?_⟩
        simp only [A', List.toFinset_cons, Finset.mem_insert, not_or]
        exact ⟨fun h => hT.1 w (h ▸ hzf.2), (Finset.mem_sdiff.mp (hE_sub hzf.1)).2⟩
      · intro z hz a ha
        have hzf := Finset.mem_filter.mp hz
        rcases List.mem_cons.mp ha with rfl | haA
        · exact hzf.2
        · exact hE_in z hzf.1 a haA
      · intro z hz
        rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hz
        by_cases hzE : z ∈ E
        · have hzw_ne : z ≠ w := fun h => hz.2.1 (by simp [A', h])
          refine ⟨w, List.mem_cons_self, ?_⟩
          by_contra hnot
          have hrev : G.Adj z w := not_not.mp fun h => hnot ((hT.2 w z hzw_ne.symm).mpr h)
          exact hz.2.2 (Finset.mem_filter.mpr ⟨hzE, hrev⟩)
        · have hz_nA : z ∉ A.toFinset := fun h => hz.2.1 (by simp [A', h])
          obtain ⟨a, haA, haz⟩ := hA_dom z (Finset.mem_sdiff.mpr ⟨hz.1, by simp [hz_nA, hzE]⟩)
          exact ⟨a, List.mem_cons_of_mem w haA, haz⟩
      · have hpow : 2 ^ (c + 2 - 1) = 2 ^ (c + 1 - 1) * 2 := by
          have : c + 2 - 1 = (c + 1 - 1) + 1 := by omega
          rw [this, pow_succ]
        rw [hpow, mul_assoc]
        exact (Nat.mul_le_mul_left _ hE'_card).trans hE_card

omit [Fintype V] in
/-- KOT Lemma 2.5 (dual of 2.4): greedy in-dominating transitive tournament `B` with source `v` and small uncovered set `E`. -/
private lemma transitive_in_dom_set {G : Digraph V} [DecidableRel G.Adj] (hT : IsTournament G)
    {S : Finset V} {v : V} (hv : v ∈ S) (c : ℕ) (hc : 1 ≤ c) :
    ∃ (B : List V) (E : Finset V),
      IsTransitiveList G B ∧ B.length ≤ c ∧
      (∃ h : B ≠ [], B.head h = v) ∧
      (∀ b ∈ B, b ∈ S) ∧
      E ⊆ S \ B.toFinset ∧
      (∀ w ∈ E, ∀ b ∈ B, G.Adj b w) ∧
      (∀ w ∈ S \ (B.toFinset ∪ E), ∃ b ∈ B, G.Adj w b) ∧
      2 ^ (c - 1) * E.card ≤ outDeg G S v := by
  obtain ⟨A, E, hA_trans, hA_len, ⟨hA_ne, hA_last⟩, hA_S, hE_sub, hE_in, hA_dom, hE_card⟩ :=
    transitive_out_dom_set (isTournament_op hT) hv c hc
  let B := A.reverse
  have hB_ne : B ≠ [] := by simp [B, hA_ne]
  have hB_toF : B.toFinset = A.toFinset := by ext w; simp [B]
  refine ⟨B, E, ?_, by simp [B, hA_len], ⟨hB_ne, by simp [B, List.head_reverse, hA_last]⟩,
    fun b hb => hA_S b (List.mem_reverse.mp hb),
    by rwa [hB_toF],
    fun w hw b hb => hE_in w hw b (List.mem_reverse.mp hb),
    fun w hw => by
      rw [hB_toF] at hw
      obtain ⟨a, haA, haw⟩ := hA_dom w hw
      exact ⟨a, List.mem_reverse.mpr haA, haw⟩,
    by rw [← inDeg_op_eq_outDeg]; exact hE_card⟩
  · refine ⟨hB_ne, List.nodup_reverse.mpr hA_trans.2.1, fun i j hij hj => ?_⟩
    have hlen : B.length = A.length := List.length_reverse
    rw [List.getElem_reverse, List.getElem_reverse]
    exact hA_trans.2.2 (A.length - 1 - j) (A.length - 1 - i) (by omega) (by omega)

omit [Fintype V] in
/-- KOT Lemma 2.7 (forward half): given `ℓ` vertex-disjoint backwards-transitive paths `Q j`
each of length `≥ k + 1` (`k ≥ 1`), there exist `U ⊆ U' ⊆ ⋃ Q` with `|U| ≤ 2k(k+1)`,
`|U'| = ℓ(k+1)` such that for any `S_del` with `|S_del| < k` and any `v ∈ (⋃ Q) \ S_del`,
there is a directed walk in `(U' ∪ {v}) \ S_del` from `v` to some `u ∈ U \ S_del`. -/
private lemma backwards_transitive_reach_out {G : Digraph V} [DecidableRel G.Adj] (hT : IsTournament G)
    {k ℓ : ℕ} (hk : 1 ≤ k) (Q : Fin ℓ → List V)
    (hQ_dir : ∀ j, IsDirPath G.Adj (Q j))
    (hQ_len : ∀ j, k + 1 ≤ (Q j).length)
    (hQ_bt : ∀ j (a b : ℕ), (hab : a + 2 ≤ b) → (hb : b < (Q j).length) → G.Adj (Q j)[b] (Q j)[a])
    (hQ_disj : ∀ j₁ j₂, j₁ ≠ j₂ → Disjoint (Q j₁).toFinset (Q j₂).toFinset) :
    ∃ U U' : Finset V,
      U ⊆ U' ∧
      U' ⊆ Finset.univ.biUnion (fun j => (Q j).toFinset) ∧
      U.card ≤ 2 * k * (k + 1) ∧
      U'.card = ℓ * (k + 1) ∧
      ∀ (S_del : Finset V), S_del.card < k →
        ∀ v ∈ (Finset.univ.biUnion fun j => (Q j).toFinset) \ S_del,
          ∃ u ∈ U \ S_del,
            Relation.ReflTransGen
              (fun x y => x ∈ ((insert v U') \ S_del : Finset V) ∧
                          y ∈ ((insert v U') \ S_del : Finset V) ∧ G.Adj x y) v u := by
  classical
  -- Layer T i = { (Q j)[i] | j : Fin ℓ } for i : Fin (k + 1)
  let layer : Fin (k + 1) → Finset V := fun i =>
    Finset.univ.image fun j : Fin ℓ => (Q j)[i.val]'(by have := hQ_len j; omega)
  have hlayer_inj : ∀ i : Fin (k + 1),
      Function.Injective (fun j : Fin ℓ => (Q j)[i.val]'(by have := hQ_len j; omega)) := by
    intro i j₁ j₂ heq; by_contra hne
    dsimp only at heq
    have hmem2 : (Q j₁)[i.val]'(by have := hQ_len j₁; omega) ∈ (Q j₂).toFinset := by
      rw [heq]; exact List.mem_toFinset.mpr (List.getElem_mem _)
    exact Finset.disjoint_left.mp (hQ_disj j₁ j₂ hne)
      (List.mem_toFinset.mpr (List.getElem_mem _)) hmem2
  have hlayer_card : ∀ i : Fin (k + 1), (layer i).card = ℓ := fun i => by
    rw [Finset.card_image_of_injective _ (hlayer_inj i), Finset.card_univ, Fintype.card_fin]
  have hlayer_disj : ∀ i₁ i₂ : Fin (k + 1), i₁ ≠ i₂ → Disjoint (layer i₁) (layer i₂) := by
    intro i₁ i₂ hne
    rw [Finset.disjoint_left]; intro w h1 h2
    rw [Finset.mem_image] at h1 h2
    obtain ⟨j₁, _, rfl⟩ := h1; obtain ⟨j₂, _, hj2⟩ := h2
    by_cases hj : j₁ = j₂
    · subst hj
      have := congrArg Fin.val ((List.nodup_iff_injective_getElem.mp (hQ_dir j₁).2.1)
        (a₁ := ⟨i₁.val, by have := hQ_len j₁; omega⟩)
        (a₂ := ⟨i₂.val, by have := hQ_len j₁; omega⟩) hj2.symm)
      exact hne (Fin.ext this)
    · exact Finset.disjoint_left.mp (hQ_disj j₁ j₂ hj)
        (List.mem_toFinset.mpr (List.getElem_mem _)) (hj2 ▸ List.mem_toFinset.mpr (List.getElem_mem _))
  -- For each layer i, pick U_i ⊆ layer i of size min (2k) ℓ of LOWEST out-degree in layer i!
  have hUi_ex : ∀ i : Fin (k + 1),
      ∃ Ui ⊆ layer i, Ui.card = min (2 * k) ℓ ∧
        ∀ u ∈ Ui, ∀ w ∈ layer i \ Ui, outDeg G (layer i) u ≤ outDeg G (layer i) w := by
    intro i
    -- Lowest out-degree in G = highest in-degree in G (since outDeg + inDeg + 1 = |layer i|)
    -- Pick top (min 2k ℓ) in-degree vertices in layer i!
    suffices hgen : ∀ r : ℕ, r ≤ (layer i).card →
        ∃ Ui ⊆ layer i, Ui.card = r ∧
          ∀ u ∈ Ui, ∀ w ∈ layer i \ Ui, outDeg G (layer i) u ≤ outDeg G (layer i) w by
      exact hgen (min (2 * k) ℓ) (by rw [hlayer_card i]; exact Nat.min_le_right _ _)
    intro r hr
    induction r with
    | zero => exact ⟨∅, Finset.empty_subset _, rfl, fun u hu => by simp at hu⟩
    | succ r ih =>
      obtain ⟨Ui, hUi_sub, hUi_c, hUi_min⟩ := ih (by omega)
      have hne : (layer i \ Ui).Nonempty := Finset.card_pos.mp (by
        rw [Finset.card_sdiff_of_subset hUi_sub, hUi_c]; omega)
      obtain ⟨v, hv_sd, hv_min⟩ := Finset.exists_min_image (layer i \ Ui) (outDeg G (layer i)) hne
      have hv_nUi : v ∉ Ui := (Finset.mem_sdiff.mp hv_sd).2
      refine ⟨insert v Ui, Finset.insert_subset (Finset.sdiff_subset hv_sd) hUi_sub,
        by rw [Finset.card_insert_of_notMem hv_nUi, hUi_c], fun u hu w hw => ?_⟩
      have hw_sd : w ∈ layer i \ Ui := Finset.mem_sdiff.mpr
        ⟨(Finset.mem_sdiff.mp hw).1, fun h => (Finset.mem_sdiff.mp hw).2 (Finset.mem_insert_of_mem h)⟩
      rcases Finset.mem_insert.mp hu with rfl | huUi
      · exact hv_min w hw_sd
      · exact hUi_min u huUi w hw_sd
  choose Ui hUi_sub hUi_card hUi_min using hUi_ex
  let U' : Finset V := Finset.univ.biUnion layer
  let U : Finset V := Finset.univ.biUnion Ui
  have hU_sub_U' : U ⊆ U' := Finset.biUnion_mono (fun i _ => hUi_sub i)
  have hU'_sub_Q : U' ⊆ Finset.univ.biUnion (fun j => (Q j).toFinset) := by
    intro w hw; rw [Finset.mem_biUnion] at hw; obtain ⟨i, _, hi⟩ := hw
    rw [Finset.mem_image] at hi; obtain ⟨j, _, rfl⟩ := hi
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, List.mem_toFinset.mpr (List.getElem_mem _)⟩
  have hU_card : U.card ≤ 2 * k * (k + 1) := by
    calc U.card ≤ ∑ i : Fin (k + 1), (Ui i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin (k + 1), (2 * k) := Finset.sum_le_sum fun i _ => by rw [hUi_card i]; exact Nat.min_le_left _ _
      _ = 2 * k * (k + 1) := by simp [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hU'_card : U'.card = ℓ * (k + 1) := by
    rw [Finset.card_biUnion (fun i₁ _ i₂ _ hne => hlayer_disj i₁ i₂ hne)]
    simp [hlayer_card, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  refine ⟨U, U', hU_sub_U', hU'_sub_Q, hU_card, hU'_card, fun S_del hS_lt v hv => ?_⟩
  rw [Finset.mem_sdiff] at hv
  -- Helper for Case (i)+(ii): if w ∈ layer i and layer i is disjoint from S_del, walk of length ≤ 2 in layer i to U!
  have hclean_layer : ∀ (i : Fin (k + 1)) (w : V), w ∈ layer i → Disjoint (layer i) S_del →
      ∃ u ∈ U \ S_del,
        Relation.ReflTransGen
          (fun x y => x ∈ (layer i : Finset V) ∧ y ∈ (layer i : Finset V) ∧ G.Adj x y) w u := by
    intro i w hw_li hli_disj
    by_cases hwU : w ∈ Ui i
    · exact ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hwU⟩,
        Finset.disjoint_left.mp hli_disj hw_li⟩, Relation.ReflTransGen.refl⟩
    · have hℓ_pos : 0 < ℓ := by
        have := Finset.card_pos.mpr ⟨w, hw_li⟩; rw [hlayer_card i] at this; exact this
      have hUi_ne : (Ui i).Nonempty := Finset.card_pos.mp (by rw [hUi_card i]; omega)
      obtain ⟨u, hu_Ui⟩ := hUi_ne
      have hu_li : u ∈ layer i := hUi_sub i hu_Ui
      have hu_in_U : u ∈ U \ S_del := Finset.mem_sdiff.mpr
        ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hu_Ui⟩, Finset.disjoint_left.mp hli_disj hu_li⟩
      refine ⟨u, hu_in_U, ?_⟩
      by_cases hwu : G.Adj w u
      · exact Relation.ReflTransGen.single ⟨hw_li, hu_li, hwu⟩
      · -- Since outDeg(u) ≤ outDeg(w) in layer i and G.Adj u w, some out-neighbor z of w in layer i has G.Adj z u!
        have hwu_ne : w ≠ u := fun h => hwU (h ▸ hu_Ui)
        have huw : G.Adj u w := not_not.mp fun h => hwu ((hT.2 w u hwu_ne).mpr h)
        have hdeg_le : outDeg G (layer i) u ≤ outDeg G (layer i) w :=
          hUi_min i u hu_Ui w (Finset.mem_sdiff.mpr ⟨hw_li, hwU⟩)
        have hex_z : ∃ z ∈ outNbr G (layer i) w, G.Adj z u := by
          by_contra hno; push Not at hno
          have hsub : insert w (outNbr G (layer i) w) ⊆ outNbr G (layer i) u := by
            intro z hz
            rcases Finset.mem_insert.mp hz with rfl | hz_out
            · exact Finset.mem_filter.mpr ⟨hw_li, huw⟩
            · have hzf := Finset.mem_filter.mp hz_out
              have hzu_ne : z ≠ u := fun h => hwu (h ▸ hzf.2)
              have huz : G.Adj u z := not_not.mp fun h => hno z hz_out ((hT.2 z u hzu_ne).mpr h)
              exact Finset.mem_filter.mpr ⟨hzf.1, huz⟩
          have hw_nout : w ∉ outNbr G (layer i) w := by simp [outNbr, hT.1 w]
          have hc := Finset.card_le_card hsub
          rw [Finset.card_insert_of_notMem hw_nout] at hc
          change outDeg G (layer i) w + 1 ≤ outDeg G (layer i) u at hc
          omega
        obtain ⟨z, hz_out, hzu⟩ := hex_z
        have hzf := Finset.mem_filter.mp hz_out
        exact (Relation.ReflTransGen.single ⟨hw_li, hzf.1, hzf.2⟩).trans
          (Relation.ReflTransGen.single ⟨hzf.1, hu_li, hzu⟩)
  -- Helper: inside a single clean path Q j (disjoint from S_del), any two vertices in Q j ∩ U' are mutually reachable in U' \ S_del (when k ≥ 2)!
  have hQ_reach : ∀ (j : Fin ℓ) (a b : Fin (k + 1)),
      2 ≤ k → Disjoint (Q j).toFinset S_del →
      Relation.ReflTransGen
        (fun x y => x ∈ (U' \ S_del : Finset V) ∧ y ∈ (U' \ S_del : Finset V) ∧ G.Adj x y)
        ((Q j)[a.val]'(by have := hQ_len j; omega))
        ((Q j)[b.val]'(by have := hQ_len j; omega)) := by
    intro j a b hk2 hQj_disj
    have hmem_U' : ∀ t : Fin (k + 1), (Q j)[t.val]'(by have := hQ_len j; omega) ∈ U' \ S_del := fun t =>
      Finset.mem_sdiff.mpr
        ⟨Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩,
         Finset.disjoint_left.mp hQj_disj (List.mem_toFinset.mpr (List.getElem_mem _))⟩
    -- Forward walk: a ≤ b using consecutive path edges
    have hfwd : ∀ c d : Fin (k + 1), c.val ≤ d.val →
        Relation.ReflTransGen
          (fun x y => x ∈ (U' \ S_del : Finset V) ∧ y ∈ (U' \ S_del : Finset V) ∧ G.Adj x y)
          ((Q j)[c.val]'(by have := hQ_len j; omega))
          ((Q j)[d.val]'(by have := hQ_len j; omega)) := by
      intro c d hcd
      obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hcd
      induction r generalizing d with
      | zero =>
        have heq : c = d := Fin.ext (by omega)
        subst heq; exact Relation.ReflTransGen.refl
      | succ r ih =>
        let d' : Fin (k + 1) := ⟨c.val + r, by omega⟩
        have h1 := ih d' (by dsimp [d']; omega) rfl
        have hstep := (hQ_dir j).2.2 (c.val + r) (by have := hQ_len j; omega)
        have hd_eq : d.val = c.val + r + 1 := by omega
        exact h1.tail ⟨hmem_U' d', hmem_U' d, by simpa only [← hd_eq] using hstep⟩
    by_cases hle : a.val ≤ b.val
    · exact hfwd a b hle
    · by_cases hgap : b.val + 2 ≤ a.val
      · exact Relation.ReflTransGen.single ⟨hmem_U' a, hmem_U' b, hQ_bt j b.val a.val hgap (by have := hQ_len j; omega)⟩
      · by_cases htop : a.val + 1 < k + 1
        · let a1 : Fin (k + 1) := ⟨a.val + 1, htop⟩
          exact (hfwd a a1 (by dsimp [a1]; omega)).trans
            (Relation.ReflTransGen.single ⟨hmem_U' a1, hmem_U' b,
              hQ_bt j b.val a1.val (by dsimp [a1]; omega) (by have := hQ_len j; omega)⟩)
        · let b1 : Fin (k + 1) := ⟨b.val - 1, by omega⟩
          exact (Relation.ReflTransGen.single ⟨hmem_U' a, hmem_U' b1,
            hQ_bt j b1.val a.val (by dsimp [b1]; omega) (by have := hQ_len j; omega)⟩).trans
            (hfwd b1 b (by dsimp [b1]; omega))
  -- Lift any walk in U' \ S_del to (insert v U') \ S_del
  have hlift : ∀ {A : Finset V}, A ⊆ (insert v U') \ S_del →
      ∀ {x y : V},
        Relation.ReflTransGen (fun a b => a ∈ A ∧ b ∈ A ∧ G.Adj a b) x y →
        Relation.ReflTransGen
          (fun a b => a ∈ ((insert v U') \ S_del : Finset V) ∧
                      b ∈ ((insert v U') \ S_del : Finset V) ∧ G.Adj a b) x y :=
    fun hsub _ _ hw => Relation.ReflTransGen.mono (fun _ _ h => ⟨hsub h.1, hsub h.2.1, h.2.2⟩) _ _ hw
  -- Now prove the main claim for ANY w ∈ U' \ S_del first!
  have hreach_U' : ∀ w ∈ U' \ S_del, ∃ u ∈ U \ S_del,
      Relation.ReflTransGen
        (fun x y => x ∈ (U' \ S_del : Finset V) ∧ y ∈ (U' \ S_del : Finset V) ∧ G.Adj x y) w u := by
    intro w hw
    rw [Finset.mem_sdiff] at hw
    have hw_bi := hw.1
    rw [Finset.mem_biUnion] at hw_bi
    obtain ⟨i, _, hw_li⟩ := hw_bi
    by_cases hwU : w ∈ Ui i
    · exact ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hwU⟩, hw.2⟩,
        Relation.ReflTransGen.refl⟩
    · by_cases hli_clean : Disjoint (layer i) S_del
      · obtain ⟨u, hu, hwalk⟩ := hclean_layer i w hw_li hli_clean
        have hsub : layer i ⊆ U' \ S_del := fun z hz =>
          Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hz⟩,
            Finset.disjoint_left.mp hli_clean hz⟩
        exact ⟨u, hu, Relation.ReflTransGen.mono (fun _ _ h => ⟨hsub h.1, hsub h.2.1, h.2.2⟩) _ _ hwalk⟩
      · -- Case (iii): layer i meets S_del (so S_del.Nonempty and k ≥ 2!), and w ∈ layer i \ Ui i (so ℓ > 2k and outDeg(w) ≥ k in layer i!)
        have hS_ne : S_del.Nonempty := by
          rw [Finset.not_disjoint_iff] at hli_clean
          obtain ⟨z, _, hzS⟩ := hli_clean; exact ⟨z, hzS⟩
        have hS_pos : 1 ≤ S_del.card := Finset.card_pos.mpr hS_ne
        have hk2 : 2 ≤ k := by omega
        -- Since w ∈ layer i \ Ui i, we have |Ui i| < |layer i| = ℓ, so 2 * k < ℓ, and |Ui i| = 2 * k!
        have hℓ_gt : 2 * k < ℓ := by
          have hcard_lt : (Ui i).card < (layer i).card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hUi_sub i, fun h => hwU (h ▸ hw_li)⟩)
          rw [hUi_card i, hlayer_card i] at hcard_lt
          omega
        -- Hence outDeg G (layer i) w ≥ k (by Proposition 2.6: < 2k vertices have outDeg < k, and all of Ui i have outDeg ≤ outDeg w!)
        have hw_deg_ge : k ≤ outDeg G (layer i) w := by
          by_contra hlt; push Not at hlt
          have hsub_small : insert w (Ui i) ⊆ (layer i).filter fun z => outDeg G (layer i) z < k := by
            intro z hz
            rcases Finset.mem_insert.mp hz with rfl | hzUi
            · exact Finset.mem_filter.mpr ⟨hw_li, hlt⟩
            · have hle := hUi_min i z hzUi w (Finset.mem_sdiff.mpr ⟨hw_li, hwU⟩)
              exact Finset.mem_filter.mpr ⟨hUi_sub i hzUi, by omega⟩
          have hc := Finset.card_le_card hsub_small
          rw [Finset.card_insert_of_notMem hwU, hUi_card i, Nat.min_eq_left (by omega)] at hc
          have hprop := card_small_outDeg_lt hT (layer i) hk
          omega
        -- Among the ≥ k out-neighbors of w in layer i, each lies in a distinct path Q j; since |S_del| < k, some Q j₀ is disjoint from S_del!
        have hex_j0 : ∃ j₀ : Fin ℓ,
            G.Adj w ((Q j₀)[i.val]'(by have := hQ_len j₀; omega)) ∧ Disjoint (Q j₀).toFinset S_del := by
          let outIdx : Finset (Fin ℓ) := Finset.univ.filter fun j =>
            G.Adj w ((Q j)[i.val]'(by have := hQ_len j; omega))
          have houtIdx_ge : k ≤ outIdx.card := by
            have himg : outIdx.image (fun j : Fin ℓ => (Q j)[i.val]'(by have := hQ_len j; omega)) =
                outNbr G (layer i) w := by
              ext z; simp only [Finset.mem_image, outIdx, Finset.mem_filter, Finset.mem_univ, true_and,
                outNbr, layer]
              constructor
              · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, rfl⟩, hj⟩
              · rintro ⟨⟨j, rfl⟩, hj⟩; exact ⟨j, hj, rfl⟩
            rw [← Finset.card_image_of_injective outIdx (hlayer_inj i), himg]
            exact hw_deg_ge
          let badJ : Finset (Fin ℓ) := outIdx.filter fun j => ¬ Disjoint (Q j).toFinset S_del
          have hbadJ_le : badJ.card ≤ S_del.card := by
            have hex : ∀ j ∈ badJ, ∃ z ∈ S_del, z ∈ (Q j).toFinset := by
              intro j hj
              have hnd := (Finset.mem_filter.mp hj).2
              rw [Finset.not_disjoint_iff] at hnd
              obtain ⟨z, hz1, hz2⟩ := hnd; exact ⟨z, hz2, hz1⟩
            choose pick hpS hpQ using hex
            let pick' : Fin ℓ → V := fun j => if hj : j ∈ badJ then pick j hj else w
            have hinj : Set.InjOn pick' (badJ : Set (Fin ℓ)) := by
              intro j₁ hj₁ j₂ hj₂ heq; by_contra hne
              simp only [pick', Finset.mem_coe.mp hj₁, Finset.mem_coe.mp hj₂, ↓reduceDIte] at heq
              exact Finset.disjoint_left.mp (hQ_disj j₁ j₂ hne)
                (hpQ j₁ (Finset.mem_coe.mp hj₁)) (heq ▸ hpQ j₂ (Finset.mem_coe.mp hj₂))
            calc badJ.card = (badJ.image pick').card := (Finset.card_image_of_injOn hinj).symm
              _ ≤ S_del.card := Finset.card_le_card (Finset.image_subset_iff.mpr fun j hj => by
                simpa only [pick', hj, ↓reduceDIte] using hpS j hj)
          have hgood : (outIdx \ badJ).Nonempty := Finset.card_pos.mp (by
            have hsub : badJ ⊆ outIdx := Finset.filter_subset _ _
            rw [Finset.card_sdiff_of_subset hsub]; omega)
          obtain ⟨j₀, hj₀⟩ := hgood
          rw [Finset.mem_sdiff] at hj₀
          refine ⟨j₀, (Finset.mem_filter.mp hj₀.1).2, ?_⟩
          by_contra hnd; exact hj₀.2 (Finset.mem_filter.mpr ⟨hj₀.1, hnd⟩)
        obtain ⟨j₀, hwj₀, hj₀_clean⟩ := hex_j0
        -- Among the k + 1 disjoint layers, at least one layer i' is disjoint from S_del!
        have hex_i' : ∃ i' : Fin (k + 1), Disjoint (layer i') S_del := by
          let badI : Finset (Fin (k + 1)) := Finset.univ.filter fun t => ¬ Disjoint (layer t) S_del
          have hbadI_le : badI.card ≤ S_del.card := by
            have hex : ∀ t ∈ badI, ∃ z ∈ S_del, z ∈ layer t := by
              intro t ht; have hnd := (Finset.mem_filter.mp ht).2
              rw [Finset.not_disjoint_iff] at hnd; obtain ⟨z, hz1, hz2⟩ := hnd; exact ⟨z, hz2, hz1⟩
            choose pick hpS hpL using hex
            let pick' : Fin (k + 1) → V := fun t => if ht : t ∈ badI then pick t ht else w
            have hinj : Set.InjOn pick' (badI : Set (Fin (k + 1))) := by
              intro t₁ ht₁ t₂ ht₂ heq; by_contra hne
              simp only [pick', Finset.mem_coe.mp ht₁, Finset.mem_coe.mp ht₂, ↓reduceDIte] at heq
              exact Finset.disjoint_left.mp (hlayer_disj t₁ t₂ hne)
                (hpL t₁ (Finset.mem_coe.mp ht₁)) (heq ▸ hpL t₂ (Finset.mem_coe.mp ht₂))
            calc badI.card = (badI.image pick').card := (Finset.card_image_of_injOn hinj).symm
              _ ≤ S_del.card := Finset.card_le_card (Finset.image_subset_iff.mpr fun t ht => by
                simpa only [pick', ht, ↓reduceDIte] using hpS t ht)
          have hgood : (Finset.univ \ badI).Nonempty := Finset.card_pos.mp (by
            rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]; omega)
          obtain ⟨i', hi'⟩ := hgood
          rw [Finset.mem_sdiff] at hi'
          refine ⟨i', ?_⟩
          by_contra hnd; exact hi'.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnd⟩)
        obtain ⟨i', hi'_clean⟩ := hex_i'
        -- Walk: w → Q j₀[i] → Q j₀[i'] (via hQ_reach) → u ∈ U \ S_del (via hclean_layer)!
        have hq0_U' : (Q j₀)[i.val]'(by have := hQ_len j₀; omega) ∈ U' \ S_del :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨j₀, Finset.mem_univ _, rfl⟩⟩,
            Finset.disjoint_left.mp hj₀_clean (List.mem_toFinset.mpr (List.getElem_mem _))⟩
        have h1 : Relation.ReflTransGen
            (fun x y => x ∈ (U' \ S_del : Finset V) ∧ y ∈ (U' \ S_del : Finset V) ∧ G.Adj x y)
            w ((Q j₀)[i.val]'(by have := hQ_len j₀; omega)) :=
          Relation.ReflTransGen.single ⟨Finset.mem_sdiff.mpr hw, hq0_U', hwj₀⟩
        have h2 := hQ_reach j₀ i i' hk2 hj₀_clean
        have hq'_li' : (Q j₀)[i'.val]'(by have := hQ_len j₀; omega) ∈ layer i' :=
          Finset.mem_image.mpr ⟨j₀, Finset.mem_univ _, rfl⟩
        obtain ⟨u, hu, h3_raw⟩ := hclean_layer i' _ hq'_li' hi'_clean
        have hsub_li' : layer i' ⊆ U' \ S_del := fun z hz =>
          Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨i', Finset.mem_univ _, hz⟩,
            Finset.disjoint_left.mp hi'_clean hz⟩
        have h3 : Relation.ReflTransGen
            (fun x y => x ∈ (U' \ S_del : Finset V) ∧ y ∈ (U' \ S_del : Finset V) ∧ G.Adj x y)
            ((Q j₀)[i'.val]'(by have := hQ_len j₀; omega)) u :=
          Relation.ReflTransGen.mono (fun _ _ h => ⟨hsub_li' h.1, hsub_li' h.2.1, h.2.2⟩) _ _ h3_raw
        exact ⟨u, hu, (h1.trans h2).trans h3⟩
  -- Finally handle v ∈ U' vs v ∉ U'!
  by_cases hvU' : v ∈ U'
  · obtain ⟨u, hu, hw⟩ := hreach_U' v (Finset.mem_sdiff.mpr ⟨hvU', hv.2⟩)
    exact ⟨u, hu, hlift (Finset.sdiff_subset_sdiff (Finset.subset_insert v U') le_rfl) hw⟩
  · -- Case (iv): v = (Q j)[idx] with idx ≥ k + 1, so v has edges to (Q j)[0], ..., (Q j)[k - 1] (k distinct vertices in U'!)
    have hv_bi := hv.1
    rw [Finset.mem_biUnion] at hv_bi
    obtain ⟨j, _, hvQj⟩ := hv_bi
    obtain ⟨idx, hidx, hQidx⟩ := List.getElem_of_mem (List.mem_toFinset.mp hvQj)
    have hidx_ge : k + 1 ≤ idx := by
      by_contra hlt; push Not at hlt
      exact hvU' (Finset.mem_biUnion.mpr ⟨⟨idx, hlt⟩, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hQidx⟩⟩)
    -- Among the k distinct vertices (Q j)[0], ..., (Q j)[k - 1], at least one avoids S_del (since |S_del| < k)!
    let prefixK : Finset V := Finset.univ.image fun a : Fin k => (Q j)[a.val]'(by have := hQ_len j; omega)
    have hpre_card : prefixK.card = k := by
      rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
      intro a₁ a₂ heq
      have := congrArg Fin.val ((List.nodup_iff_injective_getElem.mp (hQ_dir j).2.1)
        (a₁ := ⟨a₁.val, by have := hQ_len j; omega⟩) (a₂ := ⟨a₂.val, by have := hQ_len j; omega⟩) heq)
      exact Fin.ext this
    have hrem : (prefixK \ S_del).Nonempty := Finset.card_pos.mp (by
      have hsd := Finset.card_sdiff_add_card_inter prefixK S_del
      have hint : (prefixK ∩ S_del).card ≤ S_del.card := Finset.card_le_card Finset.inter_subset_right
      omega)
    obtain ⟨w, hw_sd⟩ := hrem
    rw [Finset.mem_sdiff] at hw_sd
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hw_sd.1
    have hadj_vw : G.Adj v ((Q j)[a.val]'(by have := hQ_len j; omega)) := by
      rw [← hQidx]
      exact hQ_bt j a.val idx (by omega) hidx
    have hw_U' : (Q j)[a.val]'(by have := hQ_len j; omega) ∈ U' \ S_del :=
      Finset.mem_sdiff.mpr
        ⟨Finset.mem_biUnion.mpr ⟨⟨a.val, by omega⟩, Finset.mem_univ _,
          Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩, hw_sd.2⟩
    obtain ⟨u, hu, hwalk⟩ := hreach_U' _ hw_U'
    have hsub : U' \ S_del ⊆ (insert v U') \ S_del :=
      Finset.sdiff_subset_sdiff (Finset.subset_insert v U') le_rfl
    have hv_in : v ∈ (insert v U') \ S_del := Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self _ _, hv.2⟩
    exact ⟨u, hu, (Relation.ReflTransGen.single ⟨hv_in, hsub hw_U', hadj_vw⟩).trans (hlift hsub hwalk)⟩

omit [Fintype V] in
/-- KOT Lemma 2.7 (backward half, by duality via `opDigraph` and `List.reverse`). -/
private lemma backwards_transitive_reach_in {G : Digraph V} [DecidableRel G.Adj] (hT : IsTournament G)
    {k ℓ : ℕ} (hk : 1 ≤ k) (Q : Fin ℓ → List V)
    (hQ_dir : ∀ j, IsDirPath G.Adj (Q j))
    (hQ_len : ∀ j, k + 1 ≤ (Q j).length)
    (hQ_bt : ∀ j (a b : ℕ), (hab : a + 2 ≤ b) → (hb : b < (Q j).length) → G.Adj (Q j)[b] (Q j)[a])
    (hQ_disj : ∀ j₁ j₂, j₁ ≠ j₂ → Disjoint (Q j₁).toFinset (Q j₂).toFinset) :
    ∃ W W' : Finset V,
      W ⊆ W' ∧
      W' ⊆ Finset.univ.biUnion (fun j => (Q j).toFinset) ∧
      W.card ≤ 2 * k * (k + 1) ∧
      W'.card = ℓ * (k + 1) ∧
      ∀ (S_del : Finset V), S_del.card < k →
        ∀ v ∈ (Finset.univ.biUnion fun j => (Q j).toFinset) \ S_del,
          ∃ w ∈ W \ S_del,
            Relation.ReflTransGen
              (fun x y => x ∈ ((insert v W') \ S_del : Finset V) ∧
                          y ∈ ((insert v W') \ S_del : Finset V) ∧ G.Adj x y) w v := by
  let Qrev : Fin ℓ → List V := fun j => (Q j).reverse
  have hQrev_toF : ∀ j, (Qrev j).toFinset = (Q j).toFinset := fun j => by ext z; simp [Qrev]
  have hQrev_dir : ∀ j, IsDirPath (opDigraph G).Adj (Qrev j) := by
    intro j
    refine ⟨by simp [Qrev, (hQ_dir j).1], List.nodup_reverse.mpr (hQ_dir j).2.1, fun i hi => ?_⟩
    have hlen : (Qrev j).length = (Q j).length := List.length_reverse
    rw [List.getElem_reverse, List.getElem_reverse]
    change G.Adj (Q j)[(Q j).length - 1 - (i + 1)] (Q j)[(Q j).length - 1 - i]
    have hidx : (Q j).length - 1 - (i + 1) + 1 = (Q j).length - 1 - i := by omega
    simpa only [hidx] using (hQ_dir j).2.2 ((Q j).length - 1 - (i + 1)) (by omega)
  have hQrev_bt : ∀ j (a b : ℕ), (hab : a + 2 ≤ b) → (hb : b < (Qrev j).length) →
      (opDigraph G).Adj (Qrev j)[b] (Qrev j)[a] := by
    intro j a b hab hb
    have hlen : (Qrev j).length = (Q j).length := List.length_reverse
    rw [List.getElem_reverse, List.getElem_reverse]
    exact hQ_bt j ((Q j).length - 1 - b) ((Q j).length - 1 - a) (by omega) (by omega)
  obtain ⟨W, W', hWW', hW'sub, hWcard, hW'card, hreach⟩ :=
    backwards_transitive_reach_out (isTournament_op hT) hk Qrev hQrev_dir
      (fun j => by simp [Qrev, hQ_len j]) hQrev_bt
      (fun j₁ j₂ hne => by simpa only [hQrev_toF] using hQ_disj j₁ j₂ hne)
  have hbi_eq : Finset.univ.biUnion (fun j => (Qrev j).toFinset) =
      Finset.univ.biUnion (fun j => (Q j).toFinset) := by
    ext z; simp [hQrev_toF]
  rw [hbi_eq] at hW'sub hreach
  refine ⟨W, W', hWW', hW'sub, hWcard, hW'card, fun S_del hS v hv => ?_⟩
  obtain ⟨w, hw, hwalk_op⟩ := hreach S_del hS v hv
  refine ⟨w, hw, ?_⟩
  clear hw
  induction hwalk_op with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, hbc.2.2⟩ ih

/-! ## Part 5: Kühn–Osthus–Townsend Theorem 1.5 (Safe Colourings, Claims 1–5) & Main Theorem -/

private def WalkIn (G : Digraph V) (S : Finset V) (u v : V) : Prop :=
  Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ G.Adj x y) u v

omit [Fintype V] [DecidableEq V] in
private lemma walkIn_mono {G : Digraph V} {S₁ S₂ : Finset V} (h : S₁ ⊆ S₂) {u v : V}
    (hw : WalkIn G S₁ u v) : WalkIn G S₂ u v :=
  Relation.ReflTransGen.mono (fun _ _ e => ⟨h e.1, h e.2.1, e.2.2⟩) _ _ hw

private def colClass {t : ℕ} (col : V → Option (Fin t)) (j : Fin t) : Finset V :=
  Finset.univ.filter fun v => col v = some j

private def colored {t : ℕ} (col : V → Option (Fin t)) : Finset V :=
  Finset.univ.filter fun v => (col v).isSome

private def ColExtends {t : ℕ} (col₁ col₂ : V → Option (Fin t)) : Prop :=
  ∀ v j, col₁ v = some j → col₂ v = some j

omit [Fintype V] [DecidableEq V] in
private lemma colExtends_refl {t : ℕ} (col : V → Option (Fin t)) : ColExtends col col :=
  fun _ _ h => h

omit [Fintype V] [DecidableEq V] in
private lemma colExtends_trans {t : ℕ} {c₁ c₂ c₃ : V → Option (Fin t)}
    (h12 : ColExtends c₁ c₂) (h23 : ColExtends c₂ c₃) : ColExtends c₁ c₃ :=
  fun v j h => h23 v j (h12 v j h)

omit [DecidableEq V] in
private lemma colClass_mono {t : ℕ} {c₁ c₂ : V → Option (Fin t)} (h : ColExtends c₁ c₂) (j : Fin t) :
    colClass c₁ j ⊆ colClass c₂ j := fun v hv => by
  simp only [colClass, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  exact h v j hv

omit [DecidableEq V] in
private lemma colored_mono {t : ℕ} {c₁ c₂ : V → Option (Fin t)} (h : ColExtends c₁ c₂) :
    colored c₁ ⊆ colored c₂ := fun v hv => by
  simp only [colored, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  cases hc : c₁ v with
  | none => simp [hc] at hv
  | some j => rw [h v j hc]; rfl

omit [DecidableEq V] in
private lemma colClass_disjoint {t : ℕ} (col : V → Option (Fin t)) {j₁ j₂ : Fin t} (hne : j₁ ≠ j₂) :
    Disjoint (colClass col j₁) (colClass col j₂) := by
  rw [Finset.disjoint_left]; intro v h1 h2
  simp only [colClass, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  exact hne (Option.some.inj (h1.symm.trans h2))

private def FwdSafe (G : Digraph V) {t : ℕ} (k : ℕ) (D EB : Finset V)
    (col : V → Option (Fin t)) (v : V) : Prop :=
  ∀ j, col v = some j → ∀ S_del : Finset V, S_del.card < k → v ∉ S_del →
    ∃ u ∈ (colClass col j \ (D ∪ EB)) \ S_del, WalkIn G (colClass col j \ S_del) v u

private def BwdSafe (G : Digraph V) {t : ℕ} (k : ℕ) (D EA : Finset V)
    (col : V → Option (Fin t)) (v : V) : Prop :=
  ∀ j, col v = some j → ∀ S_del : Finset V, S_del.card < k → v ∉ S_del →
    ∃ u ∈ (colClass col j \ (D ∪ EA)) \ S_del, WalkIn G (colClass col j \ S_del) u v

private def AllSafe (G : Digraph V) {t : ℕ} (k : ℕ) (D EA EB : Finset V)
    (col : V → Option (Fin t)) : Prop :=
  ∀ v, FwdSafe G k D EB col v ∧ BwdSafe G k D EA col v

private lemma fwdSafe_of_not_mem {G : Digraph V} {t : ℕ} {k : ℕ} {D EB : Finset V}
    {col : V → Option (Fin t)} {v : V} (hv : v ∉ D ∪ EB) :
    FwdSafe G k D EB col v := by
  intro j hcv S_del _ hvS
  refine ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨?_, hv⟩, hvS⟩, Relation.ReflTransGen.refl⟩
  simp [colClass, hcv]

private lemma bwdSafe_of_not_mem {G : Digraph V} {t : ℕ} {k : ℕ} {D EA : Finset V}
    {col : V → Option (Fin t)} {v : V} (hv : v ∉ D ∪ EA) :
    BwdSafe G k D EA col v := by
  intro j hcv S_del _ hvS
  refine ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨?_, hv⟩, hvS⟩, Relation.ReflTransGen.refl⟩
  simp [colClass, hcv]

private lemma fwdSafe_mono {G : Digraph V} {t : ℕ} {k : ℕ} {D EB : Finset V}
    {c₁ c₂ : V → Option (Fin t)} (hext : ColExtends c₁ c₂) {v : V}
    (hv_col : (c₁ v).isSome) (hsafe : FwdSafe G k D EB c₁ v) :
    FwdSafe G k D EB c₂ v := by
  intro j hcv2 S_del hS hvS
  cases hc1 : c₁ v with
  | none => simp [hc1] at hv_col
  | some j₁ =>
    have hj : j₁ = j := Option.some.inj ((hext v j₁ hc1).symm.trans hcv2)
    subst hj
    obtain ⟨u, hu, hw⟩ := hsafe j₁ hc1 S_del hS hvS
    have hsub := colClass_mono hext j₁
    exact ⟨u, Finset.sdiff_subset_sdiff (Finset.sdiff_subset_sdiff hsub le_rfl) le_rfl hu,
      walkIn_mono (Finset.sdiff_subset_sdiff hsub le_rfl) hw⟩

private lemma bwdSafe_mono {G : Digraph V} {t : ℕ} {k : ℕ} {D EA : Finset V}
    {c₁ c₂ : V → Option (Fin t)} (hext : ColExtends c₁ c₂) {v : V}
    (hv_col : (c₁ v).isSome) (hsafe : BwdSafe G k D EA c₁ v) :
    BwdSafe G k D EA c₂ v := by
  intro j hcv2 S_del hS hvS
  cases hc1 : c₁ v with
  | none => simp [hc1] at hv_col
  | some j₁ =>
    have hj : j₁ = j := Option.some.inj ((hext v j₁ hc1).symm.trans hcv2)
    subst hj
    obtain ⟨u, hu, hw⟩ := hsafe j₁ hc1 S_del hS hvS
    have hsub := colClass_mono hext j₁
    exact ⟨u, Finset.sdiff_subset_sdiff (Finset.sdiff_subset_sdiff hsub le_rfl) le_rfl hu,
      walkIn_mono (Finset.sdiff_subset_sdiff hsub le_rfl) hw⟩

private lemma fwdSafe_of_k_outNbrs {G : Digraph V} {t : ℕ} {k : ℕ} {D EB : Finset V}
    {col : V → Option (Fin t)} {v : V} {j : Fin t} (hcv : col v = some j)
    {W : Finset V} (hWk : k ≤ W.card)
    (hW : ∀ w ∈ W, col w = some j ∧ G.Adj v w ∧ FwdSafe G k D EB col w) :
    FwdSafe G k D EB col v := by
  intro j' hcv' S_del hS hvS
  have hj : j' = j := Option.some.inj (hcv'.symm.trans hcv)
  subst hj
  have hrem : (W \ S_del).Nonempty := Finset.card_pos.mp (by
    have hsd := Finset.card_sdiff_add_card_inter W S_del
    have hint : (W ∩ S_del).card ≤ S_del.card := Finset.card_le_card Finset.inter_subset_right
    omega)
  obtain ⟨w, hw⟩ := hrem
  rw [Finset.mem_sdiff] at hw
  obtain ⟨hcw, hvw, hwsafe⟩ := hW w hw.1
  obtain ⟨u, hu, hwalk⟩ := hwsafe j' hcw S_del hS hw.2
  have hv_mem : v ∈ colClass col j' \ S_del :=
    Finset.mem_sdiff.mpr ⟨by simp [colClass, hcv], hvS⟩
  have hw_mem : w ∈ colClass col j' \ S_del :=
    Finset.mem_sdiff.mpr ⟨by simp [colClass, hcw], hw.2⟩
  exact ⟨u, hu, (Relation.ReflTransGen.single ⟨hv_mem, hw_mem, hvw⟩).trans hwalk⟩

private lemma bwdSafe_of_k_inNbrs {G : Digraph V} {t : ℕ} {k : ℕ} {D EA : Finset V}
    {col : V → Option (Fin t)} {v : V} {j : Fin t} (hcv : col v = some j)
    {W : Finset V} (hWk : k ≤ W.card)
    (hW : ∀ w ∈ W, col w = some j ∧ G.Adj w v ∧ BwdSafe G k D EA col w) :
    BwdSafe G k D EA col v := by
  intro j' hcv' S_del hS hvS
  have hj : j' = j := Option.some.inj (hcv'.symm.trans hcv)
  subst hj
  have hrem : (W \ S_del).Nonempty := Finset.card_pos.mp (by
    have hsd := Finset.card_sdiff_add_card_inter W S_del
    have hint : (W ∩ S_del).card ≤ S_del.card := Finset.card_le_card Finset.inter_subset_right
    omega)
  obtain ⟨w, hw⟩ := hrem
  rw [Finset.mem_sdiff] at hw
  obtain ⟨hcw, hwv, hwsafe⟩ := hW w hw.1
  obtain ⟨u, hu, hwalk⟩ := hwsafe j' hcw S_del hS hw.2
  have hv_mem : v ∈ colClass col j' \ S_del :=
    Finset.mem_sdiff.mpr ⟨by simp [colClass, hcv], hvS⟩
  have hw_mem : w ∈ colClass col j' \ S_del :=
    Finset.mem_sdiff.mpr ⟨by simp [colClass, hcw], hw.2⟩
  exact ⟨u, hu, hwalk.trans (Relation.ReflTransGen.single ⟨hw_mem, hv_mem, hwv⟩)⟩

/-- Paint a set `U` of uncoloured vertices with colour `j`. -/
private def paintSet {t : ℕ} (col : V → Option (Fin t)) (U : Finset V) (j : Fin t) :
    V → Option (Fin t) :=
  fun v => if v ∈ U ∧ col v = none then some j else col v

omit [Fintype V] in
private lemma paintSet_extends {t : ℕ} (col : V → Option (Fin t)) (U : Finset V) (j : Fin t) :
    ColExtends col (paintSet col U j) := by
  intro v j' h
  simp [paintSet, h]

private lemma paintSet_colored_sub {t : ℕ} (col : V → Option (Fin t)) (U : Finset V) (j : Fin t) :
    colored (paintSet col U j) ⊆ colored col ∪ U := by
  intro v hv
  simp only [colored, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  simp only [paintSet] at hv
  simp only [Finset.mem_union, colored, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs at hv with h
  · exact Or.inr h.1
  · exact Or.inl hv

/-- Greedy colouring helper: for each vertex `v ∈ targets` (already coloured), pick `k` distinct
uncoloured vertices from `pool v \ F` and colour them the same colour as `v`! -/
private lemma greedy_colour_nbrs {t : ℕ} (k : ℕ) (col : V → Option (Fin t))
    (targets : Finset V) (pool : V → Finset V) (F : Finset V)
    (htarg_col : ∀ v ∈ targets, (col v).isSome)
    (hdeg : ∀ v ∈ targets, (colored col).card + k * targets.card + F.card ≤ (pool v).card) :
    ∃ (col' : V → Option (Fin t)) (added : Finset V),
      ColExtends col col' ∧
      Disjoint added (colored col) ∧
      Disjoint added F ∧
      added.card ≤ k * targets.card ∧
      colored col' = colored col ∪ added ∧
      ∀ v ∈ targets, ∀ j, col v = some j →
        ∃ W ⊆ added ∩ pool v, W.card = k ∧ ∀ w ∈ W, col' w = some j := by
  classical
  induction targets using Finset.induction_on generalizing col with
  | empty =>
    refine ⟨col, ∅, colExtends_refl col, Finset.disjoint_empty_left _,
      Finset.disjoint_empty_left _, by simp, by simp, fun v hv => by simp at hv⟩
  | @insert v₀ T hv₀_nT ih =>
    have hT_col : ∀ v ∈ T, (col v).isSome := fun v hv => htarg_col v (Finset.mem_insert_of_mem hv)
    have hT_deg : ∀ v ∈ T, (colored col).card + k * T.card + F.card ≤ (pool v).card := by
      intro v hv
      have := hdeg v (Finset.mem_insert_of_mem hv)
      rw [Finset.card_insert_of_notMem hv₀_nT] at this
      have : k * T.card ≤ k * (T.card + 1) := Nat.mul_le_mul_left k (Nat.le_succ _)
      omega
    obtain ⟨col₁, add₁, hext₁, hdisj_col₁, hdisj_F₁, hcard₁, hcolored₁, hgood₁⟩ :=
      ih col hT_col hT_deg
    -- Now pick k vertices for v₀ from pool v₀ \ (colored col₁ ∪ F)
    have hrem_ge : k ≤ (pool v₀ \ (colored col₁ ∪ F)).card := by
      have h1 := hdeg v₀ (Finset.mem_insert_self v₀ T)
      rw [Finset.card_insert_of_notMem hv₀_nT] at h1
      have hc1 : (colored col₁).card ≤ (colored col).card + k * T.card := by
        rw [hcolored₁, Finset.card_union_of_disjoint hdisj_col₁.symm]; omega
      have hsd := Finset.card_sdiff_add_card_inter (pool v₀) (colored col₁ ∪ F)
      have hint : (pool v₀ ∩ (colored col₁ ∪ F)).card ≤ (colored col₁).card + F.card :=
        (Finset.card_le_card Finset.inter_subset_right).trans (Finset.card_union_le _ _)
      have hmul : k * (T.card + 1) = k * T.card + k := by ring
      omega
    obtain ⟨W₀, hW₀_sub, hW₀_card⟩ := Finset.exists_subset_card_eq hrem_ge
    cases hv₀_c : col v₀ with
    | none =>
      have := htarg_col v₀ (Finset.mem_insert_self _ _)
      simp [hv₀_c] at this
    | some j₀ =>
      let col₂ := paintSet col₁ W₀ j₀
      have hW₀_disj_col₁ : Disjoint W₀ (colored col₁) := by
        rw [Finset.disjoint_left]; intro w hw
        exact fun h => (Finset.mem_sdiff.mp (hW₀_sub hw)).2 (Finset.mem_union_left _ h)
      have hW₀_disj_F : Disjoint W₀ F := by
        rw [Finset.disjoint_left]; intro w hw
        exact fun h => (Finset.mem_sdiff.mp (hW₀_sub hw)).2 (Finset.mem_union_right _ h)
      have hW₀_none : ∀ w ∈ W₀, col₁ w = none := fun w hw => by
        have hnc : w ∉ colored col₁ := Finset.disjoint_left.mp hW₀_disj_col₁ hw
        simp only [colored, Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_ne_none,
          ne_eq, not_not] at hnc
        exact hnc
      have hcolored₂ : colored col₂ = colored col₁ ∪ W₀ := by
        ext w
        simp only [colored, col₂, paintSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
        by_cases hw : w ∈ W₀
        · simp [hw, hW₀_none w hw]
        · simp [hw]
      refine ⟨col₂, add₁ ∪ W₀, colExtends_trans hext₁ (paintSet_extends col₁ W₀ j₀), ?_, ?_, ?_, ?_, ?_⟩
      · rw [Finset.disjoint_union_left]
        exact ⟨hdisj_col₁, Finset.disjoint_of_subset_right (colored_mono hext₁) hW₀_disj_col₁⟩
      · exact Finset.disjoint_union_left.mpr ⟨hdisj_F₁, hW₀_disj_F⟩
      · rw [Finset.card_insert_of_notMem hv₀_nT]
        have := Finset.card_union_le add₁ W₀
        have hmul : k * (T.card + 1) = k * T.card + k := by ring
        omega
      · rw [hcolored₂, hcolored₁, Finset.union_assoc]
      · intro v hv j hcv
        rcases Finset.mem_insert.mp hv with rfl | hvT
        · have hj : j = j₀ := Option.some.inj (hcv.symm.trans hv₀_c)
          subst hj
          refine ⟨W₀, fun w hw => Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hw,
            (Finset.mem_sdiff.mp (hW₀_sub hw)).1⟩, hW₀_card, fun w hw => ?_⟩
          simp [col₂, paintSet, hw, hW₀_none w hw]
        · obtain ⟨W, hWsub, hWcard, hWcol⟩ := hgood₁ v hvT j hcv
          refine ⟨W, fun w hw => ?_, hWcard, fun w hw => paintSet_extends col₁ W₀ j₀ w j (hWcol w hw)⟩
          have hwi := Finset.mem_inter.mp (hWsub hw)
          exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hwi.1, hwi.2⟩

/-- Core Kühn–Osthus–Townsend theorem (for `k ≥ 2`, `t ≥ 2`):
Every strongly `g_KOT k t`-connected tournament on `V` admits a partition `part : V → Fin t`
such that every part `part ⁻¹' {j}` is strongly `k`-connected (and has size `> k ≥ 2`). -/
private def gKOT (k t : ℕ) : ℕ :=
  let c := 128 * k * k * t
  let D_bd := 2 * k * t * c
  let N3 := (k + 1) ^ 2 * (D_bd + 4 * k * k * t)
  let N41 := N3 + (k + 1) ^ 2 * k * k * t
  let q := 13 * k ^ 4 * t
  let N43_pre := N41 + 2 * q * k * t * (k + 1) + q
  10 * (N43_pre + 600 * (k * t * q * 8) + 10 * k * t + 10)

private lemma two_pow_ge_succ (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

/-- Core KOT Claims 3–4 under the WLOG assumption `|EA| ≤ |EB|`: builds a safe partial
colouring `col4` of size `≤ N41 + q + n / 8` and internally vertex-disjoint monochromatic
`i`-paths `P_all i` from `sink(B_i)` to `source(A_i)` for every `i : Fin (k * t)`. -/
private theorem kot_build_col4 {k t : ℕ} (hk : 2 ≤ k) (ht : 2 ≤ t)
    (G₀ : Digraph V) [DecidableRel G₀.Adj] (hT₀ : IsTournament G₀)
    (hstrong₀ : IsKStrongOn G₀ Set.univ (gKOT k t))
    (x y : Fin (k * t) → V)
    (A B : Fin (k * t) → List V) (EA_i EB_i : Fin (k * t) → Finset V)
    (_hx_inj : Function.Injective x) (_hy_inj : Function.Injective y) (_hxy_disj : ∀ i j, x i ≠ y j)
    (hx_min : ∀ i, ∀ u : V, u ∉ Finset.univ.image x ∪ Finset.univ.image y → inDeg G₀ Finset.univ (x i) ≤ inDeg G₀ Finset.univ u)
    (hy_min : ∀ i, ∀ u : V, u ∉ Finset.univ.image x ∪ Finset.univ.image y → outDeg G₀ Finset.univ (y i) ≤ outDeg G₀ Finset.univ u)
    (hA_tr : ∀ i, IsTransitiveList G₀ (A i) ∧ (A i).length ≤ 128 * k * k * t ∧ ∃ h : A i ≠ [], (A i).getLast h = x i)
    (hB_tr : ∀ i, IsTransitiveList G₀ (B i) ∧ (B i).length ≤ 128 * k * k * t ∧ ∃ h : B i ≠ [], (B i).head h = y i)
    (hA_disj : ∀ i j, i ≠ j → Disjoint (A i).toFinset (A j).toFinset)
    (hB_disj : ∀ i j, i ≠ j → Disjoint (B i).toFinset (B j).toFinset)
    (hAB_disj : ∀ i j, Disjoint (A i).toFinset (B j).toFinset)
    (_hEA_props : ∀ i, Disjoint (EA_i i) ((Finset.univ.biUnion fun i => (A i).toFinset) ∪ (Finset.univ.biUnion fun i => (B i).toFinset)) ∧ ∀ w ∈ EA_i i, ∀ a ∈ A i, G₀.Adj w a)
    (_hEB_props : ∀ i, Disjoint (EB_i i) ((Finset.univ.biUnion fun i => (A i).toFinset) ∪ (Finset.univ.biUnion fun i => (B i).toFinset)) ∧ ∀ w ∈ EB_i i, ∀ b ∈ B i, G₀.Adj b w)
    (_hA_dom : ∀ i, ∀ w ∈ Finset.univ \ (((Finset.univ.biUnion fun i => (A i).toFinset) ∪ (Finset.univ.biUnion fun i => (B i).toFinset)) ∪ EA_i i), ∃ a ∈ A i, G₀.Adj a w)
    (_hB_dom : ∀ i, ∀ w ∈ Finset.univ \ (((Finset.univ.biUnion fun i => (A i).toFinset) ∪ (Finset.univ.biUnion fun i => (B i).toFinset)) ∪ EB_i i), ∃ b ∈ B i, G₀.Adj w b)
    (hEA_bd : ∀ i, 2 ^ (128 * k * k * t - 1) * (EA_i i).card ≤ inDeg G₀ Finset.univ (x i))
    (hEB_bd : ∀ i, 2 ^ (128 * k * k * t - 1) * (EB_i i).card ≤ outDeg G₀ Finset.univ (y i))
    (hEA_le_EB : (Finset.univ.biUnion EA_i).card ≤ (Finset.univ.biUnion EB_i).card) :
    ∃ (col4 : V → Option (Fin t)) (P_all : Fin (k * t) → List V),
      (∀ i v, v ∈ (A i).toFinset ∪ (B i).toFinset → col4 v = some ⟨i.val / k, Nat.div_lt_of_lt_mul i.isLt⟩) ∧
      AllSafe G₀ k ((Finset.univ.biUnion fun i => (A i).toFinset) ∪ (Finset.univ.biUnion fun i => (B i).toFinset))
        (Finset.univ.biUnion EA_i) (Finset.univ.biUnion EB_i) col4 ∧
      (colored col4).card ≤
        ((k + 1) ^ 2 * (2 * k * t * (128 * k * k * t) + 4 * k * k * t) + (k + 1) ^ 2 * k * k * t) +
          (13 * k ^ 4 * t) + Fintype.card V / 8 ∧
      (∀ i : Fin (k * t),
        IsDirPathBetween G₀.Adj ((B i).getLast (hB_tr i).1.1) ((A i).head (hA_tr i).1.1) (P_all i) ∧
        (∀ w ∈ P_all i, col4 w = some ⟨i.val / k, Nat.div_lt_of_lt_mul i.isLt⟩) ∧
        Disjoint ((P_all i).toFinset \ {(B i).getLast (hB_tr i).1.1, (A i).head (hA_tr i).1.1})
          ((Finset.univ.biUnion fun i => (A i).toFinset) ∪ (Finset.univ.biUnion fun i => (B i).toFinset))) ∧
      (∀ i₁ i₂ : Fin (k * t), i₁ ≠ i₂ →
        Disjoint ((P_all i₁).toFinset \ {(B i₁).getLast (hB_tr i₁).1.1, (A i₁).head (hA_tr i₁).1.1})
                 ((P_all i₂).toFinset \ {(B i₂).getLast (hB_tr i₂).1.1, (A i₂).head (hA_tr i₂).1.1})) := by
  classical
  let c : ℕ := 128 * k * k * t
  let D_bd : ℕ := 2 * k * t * c
  let N3 : ℕ := (k + 1) ^ 2 * (D_bd + 4 * k * k * t)
  let N41 : ℕ := N3 + (k + 1) ^ 2 * k * k * t
  let q : ℕ := 13 * k ^ 4 * t
  let N43_pre : ℕ := N41 + 2 * q * k * t * (k + 1) + q
  let g : ℕ := gKOT k t
  have hg_eq : g = 10 * (N43_pre + 600 * (k * t * q * 8) + 10 * k * t + 10) := rfl
  have hkt_pos : 1 ≤ k * t := Nat.mul_pos (by omega) (by omega)
  have hc_ge : 128 * k * k * t ≤ 2 ^ (c - 1) := by
    have h1 := two_pow_ge_succ (c - 1)
    have hc_pos : 1 ≤ c := by
      dsimp only [c]
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega)
    omega
  let n : ℕ := Fintype.card V
  let D : Finset V := (Finset.univ.biUnion fun i => (A i).toFinset) ∪ (Finset.univ.biUnion fun i => (B i).toFinset)
  let EA : Finset V := Finset.univ.biUnion EA_i
  let EB : Finset V := Finset.univ.biUnion EB_i
  have hU₀ : IsKStrongOn G₀ ((Finset.univ : Finset V) : Set V) g := by simpa using hstrong₀
  have hdeg₀_out : ∀ v : V, g ≤ outDeg G₀ Finset.univ v := fun v =>
    min_outDeg_of_isKStrongOn hT₀ hU₀ (Finset.mem_univ v)
  have hdeg₀_in : ∀ v : V, g ≤ inDeg G₀ Finset.univ v := fun v =>
    min_inDeg_of_isKStrongOn hT₀ hU₀ (Finset.mem_univ v)
  have hn_ge : 2 * g + 1 ≤ n := by
    have hgt : g < n := by simpa [n, Set.ncard_coe_finset] using hU₀.1
    obtain ⟨v, _⟩ := Finset.card_pos.mp (by rw [Finset.card_univ]; change 0 < n; omega : 0 < (Finset.univ : Finset V).card)
    have h1 := hdeg₀_out v
    have h2 := hdeg₀_in v
    have h3 := outDeg_add_inDeg_eq hT₀ (Finset.mem_univ v)
    simp only [Finset.card_univ] at h3
    omega
  let E : Finset V := EA ∪ EB
  let XY : Finset V := Finset.univ.image x ∪ Finset.univ.image y
  -- Crucial degree bounds: for EVERY u ∉ XY, 128 * k * |EA| ≤ inDeg u and 64 * k * |E| ≤ outDeg u!
  have hEA_deg_bd : ∀ u : V, u ∉ XY → 128 * k * EA.card ≤ inDeg G₀ Finset.univ u := by
    intro u hu
    have hsum : ∑ i : Fin (k * t), (EA_i i).card * (2 ^ (c - 1)) ≤ ∑ _i : Fin (k * t), inDeg G₀ Finset.univ u := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Nat.mul_comm]
      exact (hEA_bd i).trans (hx_min i u hu)
    rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    have hbi : EA.card ≤ ∑ i : Fin (k * t), (EA_i i).card := Finset.card_biUnion_le
    have hmul : EA.card * (128 * k * k * t) ≤ (∑ i : Fin (k * t), (EA_i i).card) * 2 ^ (c - 1) :=
      Nat.mul_le_mul hbi hc_ge
    have hcomb : EA.card * (128 * k * k * t) ≤ (k * t) * inDeg G₀ Finset.univ u := hmul.trans hsum
    have hrew : EA.card * (128 * k * k * t) = (k * t) * (128 * k * EA.card) := by ring
    rw [hrew] at hcomb
    exact Nat.le_of_mul_le_mul_left hcomb hkt_pos
  have hEB_deg_bd : ∀ u : V, u ∉ XY → 128 * k * EB.card ≤ outDeg G₀ Finset.univ u := by
    intro u hu
    have hsum : ∑ i : Fin (k * t), (EB_i i).card * (2 ^ (c - 1)) ≤ ∑ _i : Fin (k * t), outDeg G₀ Finset.univ u := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Nat.mul_comm]
      exact (hEB_bd i).trans (hy_min i u hu)
    rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    have hbi : EB.card ≤ ∑ i : Fin (k * t), (EB_i i).card := Finset.card_biUnion_le
    have hmul : EB.card * (128 * k * k * t) ≤ (∑ i : Fin (k * t), (EB_i i).card) * 2 ^ (c - 1) :=
      Nat.mul_le_mul hbi hc_ge
    have hcomb : EB.card * (128 * k * k * t) ≤ (k * t) * outDeg G₀ Finset.univ u := hmul.trans hsum
    have hrew : EB.card * (128 * k * k * t) = (k * t) * (128 * k * EB.card) := by ring
    rw [hrew] at hcomb
    exact Nat.le_of_mul_le_mul_left hcomb hkt_pos
  have hE_deg_bd : ∀ u : V, u ∉ XY → 64 * k * E.card ≤ outDeg G₀ Finset.univ u := by
    intro u hu
    have h1 : E.card ≤ EA.card + EB.card := Finset.card_union_le EA EB
    change EA.card ≤ EB.card at hEA_le_EB
    have h1' : E.card ≤ 2 * EB.card := by omega
    have h2 := hEB_deg_bd u hu
    calc 64 * k * E.card ≤ 64 * k * (2 * EB.card) := Nat.mul_le_mul_left _ h1'
      _ = 128 * k * EB.card := by ring
      _ ≤ outDeg G₀ Finset.univ u := h2
  have hE_le_n : 64 * k * E.card ≤ n := by
    have hXY_card : XY.card ≤ 2 * k * t := by
      calc XY.card ≤ (Finset.univ.image x).card + (Finset.univ.image y).card := Finset.card_union_le _ _
        _ ≤ k * t + k * t := by
          have h1 : (Finset.univ.image x).card ≤ k * t := Finset.card_image_le.trans (by simp)
          have h2 : (Finset.univ.image y).card ≤ k * t := Finset.card_image_le.trans (by simp)
          omega
        _ = 2 * k * t := by ring
    have h2kt_le_g : 2 * k * t ≤ g := by
      rw [hg_eq]
      have : 2 * k * t ≤ 10 * k * t := by
        calc 2 * k * t = 2 * (k * t) := by ring
          _ ≤ 10 * (k * t) := Nat.mul_le_mul_right _ (by omega)
          _ = 10 * k * t := by ring
      omega
    have hrem : (Finset.univ \ XY).Nonempty := Finset.card_pos.mp (by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]; change 0 < n - XY.card; omega)
    obtain ⟨u, hu⟩ := hrem
    have h1 := hE_deg_bd u (Finset.mem_sdiff.mp hu).2
    have h2 : outDeg G₀ Finset.univ u ≤ n := Finset.card_le_univ _
    omega
  have hEA_gap : ∀ u : V, u ∉ XY → 2 * (N43_pre + 10 * k * t + 10) + EA.card ≤ inDeg G₀ Finset.univ u := by
    intro u hu
    have h1 : 2 * EA.card ≤ inDeg G₀ Finset.univ u :=
      (Nat.mul_le_mul_right EA.card (by omega : 2 ≤ 128 * k)).trans (hEA_deg_bd u hu)
    have h2 := hdeg₀_in u
    omega
  have hE_gap : ∀ u : V, u ∉ XY → 2 * (N43_pre + 10 * k * t + 10) + E.card ≤ outDeg G₀ Finset.univ u := by
    intro u hu
    have h1 : 2 * E.card ≤ outDeg G₀ Finset.univ u :=
      (Nat.mul_le_mul_right E.card (by omega : 2 ≤ 64 * k)).trans (hE_deg_bd u hu)
    have h2 := hdeg₀_out u
    omega
  -- Colour assignment helper: block j* = { i : Fin (k*t) | i.val / k = j.val }
  let blockOf : Fin (k * t) → Fin t := fun i => ⟨i.val / k, Nat.div_lt_of_lt_mul i.isLt⟩
  let idxOf : Fin t → Fin k → Fin (k * t) := fun j a => ⟨j.val * k + a.val, by
    calc j.val * k + a.val < j.val * k + k := Nat.add_lt_add_left a.isLt _
      _ = (j.val + 1) * k := by ring
      _ ≤ t * k := Nat.mul_le_mul_right k j.isLt
      _ = k * t := by ring⟩
  have hblock_idx : ∀ j a, blockOf (idxOf j a) = j := fun j a => by
    ext; dsimp [blockOf, idxOf]
    rw [Nat.mul_comm j.val k, Nat.mul_add_div (by omega), Nat.div_eq_of_lt a.isLt, Nat.add_zero]
  have hidx_inj : ∀ j, Function.Injective (idxOf j) := fun j a₁ a₂ h => by
    have := congrArg Fin.val h; dsimp [idxOf] at this; exact Fin.ext (by omega)
  have hD_card : D.card ≤ D_bd := by
    calc D.card ≤ (Finset.univ.biUnion fun i => (A i).toFinset).card +
          (Finset.univ.biUnion fun i => (B i).toFinset).card := Finset.card_union_le _ _
      _ ≤ (∑ i : Fin (k * t), (A i).toFinset.card) + (∑ i : Fin (k * t), (B i).toFinset.card) :=
          Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
      _ ≤ (∑ _i : Fin (k * t), c) + (∑ _i : Fin (k * t), c) :=
          Nat.add_le_add (Finset.sum_le_sum fun i _ => (List.toFinset_card_le _).trans (hA_tr i).2.1)
            (Finset.sum_le_sum fun i _ => (List.toFinset_card_le _).trans (hB_tr i).2.1)
      _ = D_bd := by simp [D_bd, Finset.sum_const, smul_eq_mul]; ring
  have hXY_sub_D : XY ⊆ D := by
    intro w hw; rcases Finset.mem_union.mp hw with h | h <;> rw [Finset.mem_image] at h
    · obtain ⟨i, _, rfl⟩ := h
      obtain ⟨hne, hl⟩ := (hA_tr i).2.2
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, List.mem_toFinset.mpr (hl ▸ List.getLast_mem hne)⟩)
    · obtain ⟨i, _, rfl⟩ := h
      obtain ⟨hne, hh⟩ := (hB_tr i).2.2
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, List.mem_toFinset.mpr (hh ▸ List.head_mem hne)⟩)
  -- Initial colouring col0: colour A_i ∪ B_i with blockOf i
  let col0 : V → Option (Fin t) := fun v =>
    if h : ∃ i : Fin (k * t), v ∈ (A i).toFinset ∪ (B i).toFinset then some (blockOf h.choose) else none
  have hcol0_AB : ∀ i v, v ∈ (A i).toFinset ∪ (B i).toFinset → col0 v = some (blockOf i) := by
    intro i v hv
    have hex : ∃ i' : Fin (k * t), v ∈ (A i').toFinset ∪ (B i').toFinset := ⟨i, hv⟩
    simp only [col0, hex, ↓reduceDIte]
    congr 1
    have hch := hex.choose_spec
    have heq : hex.choose = i := by
      by_contra hne
      rcases Finset.mem_union.mp hch with h1 | h1 <;> rcases Finset.mem_union.mp hv with h2 | h2
      · exact Finset.disjoint_left.mp (hA_disj _ _ hne) h1 h2
      · exact Finset.disjoint_left.mp (hAB_disj _ _) h1 h2
      · exact Finset.disjoint_left.mp (hAB_disj _ _) h2 h1
      · exact Finset.disjoint_left.mp (hB_disj _ _ hne) h1 h2
    rw [heq]
  have hcol0_colored : colored col0 = D := by
    ext v; simp only [colored, col0, D, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_biUnion]
    split_ifs with h
    · simp only [Option.isSome_some, true_iff]
      obtain ⟨i, ha | hb⟩ := h
      · exact Or.inl ⟨i, ha⟩
      · exact Or.inr ⟨i, hb⟩
    · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
      rintro (⟨i, ha⟩ | ⟨i, hb⟩)
      · exact h ⟨i, Or.inl ha⟩
      · exact h ⟨i, Or.inr hb⟩
  -- CLAIM 3: Colour additional vertices so all coloured vertices are safe, total ≤ N3!
  -- Step 3a: For each v ∈ XY, pick k uncoloured in-nbrs and k uncoloured out-nbrs (any, even in E!)
  have hXY_col0 : ∀ v ∈ XY, (col0 v).isSome := fun v hv => by
    have : v ∈ colored col0 := hcol0_colored ▸ hXY_sub_D hv
    exact (Finset.mem_filter.mp this).2
  have hXY_card : XY.card ≤ 2 * k * t := by
    calc XY.card ≤ (Finset.univ.image x).card + (Finset.univ.image y).card := Finset.card_union_le _ _
      _ ≤ k * t + k * t := Nat.add_le_add
          ((Finset.card_image_le).trans (by simp)) ((Finset.card_image_le).trans (by simp))
      _ = 2 * k * t := by ring
  have hkXY_le : k * XY.card ≤ 2 * k * k * t := by
    calc k * XY.card ≤ k * (2 * k * t) := Nat.mul_le_mul_left k hXY_card
      _ = 2 * k * k * t := by ring
  have h4kkt_eq : 2 * k * k * t + 2 * k * k * t = 4 * k * k * t := by ring
  have hD4_le_N3 : D_bd + 4 * k * k * t ≤ N3 := by
    dsimp only [N3]; exact Nat.le_mul_of_pos_left _ (by positivity)
  have hk1D4_le_N3 : (k + 1) * (D_bd + 4 * k * k * t) ≤ N3 := by
    calc (k + 1) * (D_bd + 4 * k * k * t)
        ≤ (k + 1) * ((k + 1) * (D_bd + 4 * k * k * t)) := Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
      _ = N3 := by dsimp only [N3]; ring
  obtain ⟨col3a, add3a, hext3a, hdisj_col3a, _, hcard3a, hcol3a_eq, hgood3a⟩ :=
    greedy_colour_nbrs k col0 XY (fun v => inNbr G₀ Finset.univ v) ∅ hXY_col0 (by
      intro v _; rw [hcol0_colored, Finset.card_empty]
      have hd := hdeg₀_in v
      change D.card + k * XY.card + 0 ≤ inDeg G₀ Finset.univ v
      omega)
  obtain ⟨col3b, add3b, hext3b, hdisj_col3b, _, hcard3b, hcol3b_eq, hgood3b⟩ :=
    greedy_colour_nbrs k col3a XY (fun v => outNbr G₀ Finset.univ v) ∅
      (fun v hv => by have := colored_mono hext3a (hcol0_colored ▸ hXY_sub_D hv); exact (Finset.mem_filter.mp this).2) (by
      intro v _; rw [hcol3a_eq, Finset.card_union_of_disjoint hdisj_col3a.symm, hcol0_colored, Finset.card_empty]
      have hd := hdeg₀_out v
      change D.card + add3a.card + k * XY.card + 0 ≤ outDeg G₀ Finset.univ v
      omega)
  have hcol3b_card : (colored col3b).card ≤ D_bd + 4 * k * k * t := by
    rw [hcol3b_eq, Finset.card_union_of_disjoint hdisj_col3b.symm,
      hcol3a_eq, Finset.card_union_of_disjoint hdisj_col3a.symm, hcol0_colored]
    omega
  -- Step 3b: For every v ∈ colored col3b \ XY, pick k uncoloured in-nbrs outside EA!
  let T3b : Finset V := colored col3b \ XY
  obtain ⟨col3c, add3c, hext3c, hdisj_col3c, hdisj_EA3c, hcard3c, hcol3c_eq, hgood3c⟩ :=
    greedy_colour_nbrs k col3b T3b (fun v => inNbr G₀ Finset.univ v) EA
      (fun v hv => (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).2) (by
      intro v hv
      have hv_nXY : v ∉ XY := (Finset.mem_sdiff.mp hv).2
      have hgap := hEA_gap v hv_nXY
      have hT3b_le : T3b.card ≤ D_bd + 4 * k * k * t := (Finset.card_le_card Finset.sdiff_subset).trans hcol3b_card
      have hmul : (colored col3b).card + k * T3b.card ≤ (k + 1) * (D_bd + 4 * k * k * t) := by
        calc (colored col3b).card + k * T3b.card
            ≤ (D_bd + 4 * k * k * t) + k * (D_bd + 4 * k * k * t) :=
              Nat.add_le_add hcol3b_card (Nat.mul_le_mul_left k hT3b_le)
          _ = (k + 1) * (D_bd + 4 * k * k * t) := by ring
      change (colored col3b).card + k * T3b.card + EA.card ≤ inDeg G₀ Finset.univ v
      omega)
  have hcol3c_card : (colored col3c).card ≤ (k + 1) * (D_bd + 4 * k * k * t) := by
    rw [hcol3c_eq, Finset.card_union_of_disjoint hdisj_col3c.symm]
    have hT3b_le : T3b.card ≤ D_bd + 4 * k * k * t := (Finset.card_le_card Finset.sdiff_subset).trans hcol3b_card
    calc (colored col3b).card + add3c.card
        ≤ (D_bd + 4 * k * k * t) + k * (D_bd + 4 * k * k * t) :=
          Nat.add_le_add hcol3b_card (hcard3c.trans (Nat.mul_le_mul_left k hT3b_le))
      _ = (k + 1) * (D_bd + 4 * k * k * t) := by ring
  -- Step 3c: For every v ∈ colored col3c \ XY, pick k uncoloured out-nbrs outside E!
  let T3c : Finset V := colored col3c \ XY
  obtain ⟨col3, add3, hext3d, hdisj_col3d, hdisj_E3d, hcard3d, hcol3_eq, hgood3d⟩ :=
    greedy_colour_nbrs k col3c T3c (fun v => outNbr G₀ Finset.univ v) E
      (fun v hv => (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).2) (by
      intro v hv
      have hv_nXY : v ∉ XY := (Finset.mem_sdiff.mp hv).2
      have hgap := hE_gap v hv_nXY
      have hT3c_le : T3c.card ≤ (k + 1) * (D_bd + 4 * k * k * t) := (Finset.card_le_card Finset.sdiff_subset).trans hcol3c_card
      have hmul : (colored col3c).card + k * T3c.card ≤ N3 := by
        calc (colored col3c).card + k * T3c.card
            ≤ (k + 1) * (D_bd + 4 * k * k * t) + k * ((k + 1) * (D_bd + 4 * k * k * t)) :=
              Nat.add_le_add hcol3c_card (Nat.mul_le_mul_left k hT3c_le)
          _ = N3 := by dsimp only [N3]; ring
      change (colored col3c).card + k * T3c.card + E.card ≤ outDeg G₀ Finset.univ v
      omega)
  have hext03 : ColExtends col0 col3 := colExtends_trans (colExtends_trans hext3a hext3b) (colExtends_trans hext3c hext3d)
  have hcol3_card : (colored col3).card ≤ N3 := by
    rw [hcol3_eq, Finset.card_union_of_disjoint hdisj_col3d.symm]
    have hT3c_le : T3c.card ≤ (k + 1) * (D_bd + 4 * k * k * t) := (Finset.card_le_card Finset.sdiff_subset).trans hcol3c_card
    calc (colored col3c).card + add3.card
        ≤ (k + 1) * (D_bd + 4 * k * k * t) + k * ((k + 1) * (D_bd + 4 * k * k * t)) :=
          Nat.add_le_add hcol3c_card (hcard3d.trans (Nat.mul_le_mul_left k hT3c_le))
      _ = N3 := by dsimp only [N3]; ring
  -- Verify AllSafe for col3!
  have hcol3_safe : AllSafe G₀ k D EA EB col3 := by
    -- First: every vertex in add3 is outside D ∪ E, hence both fwdSafe and bwdSafe!
    have hadd3_safe : ∀ w ∈ add3, FwdSafe G₀ k D EB col3 w ∧ BwdSafe G₀ k D EA col3 w := by
      intro w hw
      have hwnD : w ∉ D := fun h => Finset.disjoint_left.mp hdisj_col3d hw
        (colored_mono (colExtends_trans (colExtends_trans hext3a hext3b) hext3c) (hcol0_colored ▸ h))
      have hwnE : w ∉ E := Finset.disjoint_left.mp hdisj_E3d hw
      have hwnEA : w ∉ EA := fun h => hwnE (Finset.mem_union_left _ h)
      have hwnEB : w ∉ EB := fun h => hwnE (Finset.mem_union_right _ h)
      exact ⟨fwdSafe_of_not_mem (by simp only [Finset.mem_union, not_or]; exact ⟨hwnD, hwnEB⟩),
        bwdSafe_of_not_mem (by simp only [Finset.mem_union, not_or]; exact ⟨hwnD, hwnEA⟩)⟩
    -- Next: every vertex in colored col3c \ XY has k out-nbrs in add3 (fwdSafe!)
    have hT3c_fwd : ∀ v ∈ T3c, FwdSafe G₀ k D EB col3 v := by
      intro v hv
      have hvc : (col3c v).isSome := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).2
      cases hc : col3c v with
      | none => simp [hc] at hvc
      | some j =>
        obtain ⟨W, hWsub, hWcard, hWcol⟩ := hgood3d v hv j hc
        exact fwdSafe_of_k_outNbrs (hext3d v j hc) hWcard.ge fun w hw => by
          have hwi := Finset.mem_inter.mp (hWsub hw)
          exact ⟨hWcol w hw, (Finset.mem_filter.mp hwi.2).2, (hadd3_safe w hwi.1).1⟩
    -- Next: every vertex in add3c is outside D ∪ EA (bwdSafe!) AND in T3c (fwdSafe!)
    have hadd3c_bwd : ∀ w ∈ add3c, BwdSafe G₀ k D EA col3 w := by
      intro w hw
      have hwnD : w ∉ D := fun h => Finset.disjoint_left.mp hdisj_col3c hw
        (colored_mono (colExtends_trans hext3a hext3b) (hcol0_colored ▸ h))
      have hwnEA : w ∉ EA := Finset.disjoint_left.mp hdisj_EA3c hw
      exact bwdSafe_of_not_mem (by simp only [Finset.mem_union, not_or]; exact ⟨hwnD, hwnEA⟩)
    -- Next: every vertex in T3b has k in-nbrs in add3c (bwdSafe!)
    have hT3b_bwd : ∀ v ∈ T3b, BwdSafe G₀ k D EA col3 v := by
      intro v hv
      have hvc : (col3b v).isSome := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).2
      cases hc : col3b v with
      | none => simp [hc] at hvc
      | some j =>
        obtain ⟨W, hWsub, hWcard, hWcol⟩ := hgood3c v hv j hc
        exact bwdSafe_of_k_inNbrs (hext3d v j (hext3c v j hc)) hWcard.ge fun w hw => by
          have hwi := Finset.mem_inter.mp (hWsub hw)
          exact ⟨hext3d w j (hWcol w hw), (Finset.mem_filter.mp hwi.2).2, hadd3c_bwd w hwi.1⟩
    -- Next: every vertex in XY has k in-nbrs in add3a (⊆ T3b, bwdSafe!) and k out-nbrs in add3b (⊆ T3c, fwdSafe!)
    have hXY_safe : ∀ v ∈ XY, FwdSafe G₀ k D EB col3 v ∧ BwdSafe G₀ k D EA col3 v := by
      intro v hv
      have hvc := hXY_col0 v hv
      cases hc : col0 v with
      | none => simp [hc] at hvc
      | some j =>
        refine ⟨?_, ?_⟩
        · obtain ⟨W, hWsub, hWcard, hWcol⟩ := hgood3b v hv j (hext3a v j hc)
          exact fwdSafe_of_k_outNbrs (hext03 v j hc) hWcard.ge fun w hw => by
            have hwi := Finset.mem_inter.mp (hWsub hw)
            have hw_nXY : w ∉ XY := fun h => Finset.disjoint_left.mp hdisj_col3b hwi.1
              (colored_mono hext3a (hcol0_colored ▸ hXY_sub_D h))
            have hw_T3c : w ∈ T3c := Finset.mem_sdiff.mpr
              ⟨colored_mono hext3c (hcol3b_eq ▸ Finset.mem_union_right _ hwi.1), hw_nXY⟩
            exact ⟨hext3d w j (hext3c w j (hWcol w hw)), (Finset.mem_filter.mp hwi.2).2, hT3c_fwd w hw_T3c⟩
        · obtain ⟨W, hWsub, hWcard, hWcol⟩ := hgood3a v hv j hc
          exact bwdSafe_of_k_inNbrs (hext03 v j hc) hWcard.ge fun w hw => by
            have hwi := Finset.mem_inter.mp (hWsub hw)
            have hw_nXY : w ∉ XY := fun h => Finset.disjoint_left.mp hdisj_col3a hwi.1 (hcol0_colored ▸ hXY_sub_D h)
            have hw_T3b : w ∈ T3b := Finset.mem_sdiff.mpr
              ⟨colored_mono hext3b (hcol3a_eq ▸ Finset.mem_union_right _ hwi.1), hw_nXY⟩
            exact ⟨hext3d w j (hext3c w j (hext3b w j (hWcol w hw))), (Finset.mem_filter.mp hwi.2).2, hT3b_bwd w hw_T3b⟩
    intro v
    by_cases hvc : v ∈ colored col3
    · by_cases hv_add3 : v ∈ add3
      · exact hadd3_safe v hv_add3
      · have hv_col3c : v ∈ colored col3c := by
          rw [hcol3_eq, Finset.mem_union] at hvc; exact hvc.resolve_right hv_add3
        by_cases hv_XY : v ∈ XY
        · exact hXY_safe v hv_XY
        · have hv_T3c : v ∈ T3c := Finset.mem_sdiff.mpr ⟨hv_col3c, hv_XY⟩
          refine ⟨hT3c_fwd v hv_T3c, ?_⟩
          by_cases hv_add3c : v ∈ add3c
          · exact hadd3c_bwd v hv_add3c
          · have hv_col3b : v ∈ colored col3b := by
              rw [hcol3c_eq, Finset.mem_union] at hv_col3c; exact hv_col3c.resolve_right hv_add3c
            exact hT3b_bwd v (Finset.mem_sdiff.mpr ⟨hv_col3b, hv_XY⟩)
    · have hnone : col3 v = none := by
        simp only [colored, Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_ne_none,
          ne_eq, not_not] at hvc; exact hvc
      exact ⟨fun j hj => by simp [hnone] at hj, fun j hj => by simp [hnone] at hj⟩
  -- CLAIM 4: Construct i-paths P_i from sink(B_i) to source(A_i) for all i : Fin (k*t)!
  let srcA : Fin (k * t) → V := fun i => (A i).head (hA_tr i).1.1
  let snkB : Fin (k * t) → V := fun i => (B i).getLast (hB_tr i).1.1
  have hsrcA_inj : Function.Injective srcA := by
    intro i₁ i₂ heq; by_contra hne
    have h1 : srcA i₁ ∈ (A i₁).toFinset := List.mem_toFinset.mpr (List.head_mem _)
    have h2 : srcA i₂ ∈ (A i₂).toFinset := List.mem_toFinset.mpr (List.head_mem _)
    exact Finset.disjoint_left.mp (hA_disj i₁ i₂ hne) h1 (heq ▸ h2)
  have hsnkB_inj : Function.Injective snkB := by
    intro i₁ i₂ heq; by_contra hne
    have h1 : snkB i₁ ∈ (B i₁).toFinset := List.mem_toFinset.mpr (List.getLast_mem _)
    have h2 : snkB i₂ ∈ (B i₂).toFinset := List.mem_toFinset.mpr (List.getLast_mem _)
    exact Finset.disjoint_left.mp (hB_disj i₁ i₂ hne) h1 (heq ▸ h2)
  have hsnk_src_disj : ∀ i₁ i₂, snkB i₁ ≠ srcA i₂ := fun i₁ i₂ h => by
    have h1 : srcA i₂ ∈ (A i₂).toFinset := List.mem_toFinset.mpr (List.head_mem _)
    have h2 : snkB i₁ ∈ (B i₁).toFinset := List.mem_toFinset.mpr (List.getLast_mem _)
    exact Finset.disjoint_left.mp (hAB_disj i₂ i₁) h1 (h ▸ h2)
  -- Step 4a: Greedily pick a maximal set I_short of indices having short i-paths (length ≤ k+1, i.e. ≤ k+2 vertices)
  -- with pairwise disjoint uncoloured internal vertices!
  have hpack_ex : ∃ s : Finset (Fin (k * t)),
      (∃ P : Fin (k * t) → List V,
        (∀ i ∈ s, IsDirPathBetween G₀.Adj (snkB i) (srcA i) (P i) ∧ (P i).length ≤ k + 2 ∧
          ∀ w ∈ (P i).toFinset \ {snkB i, srcA i}, w ∉ colored col3) ∧
        (∀ i₁ ∈ s, ∀ i₂ ∈ s, i₁ ≠ i₂ →
          Disjoint ((P i₁).toFinset \ {snkB i₁, srcA i₁}) ((P i₂).toFinset \ {snkB i₂, srcA i₂}))) ∧
      ∀ s' : Finset (Fin (k * t)),
        (∃ P' : Fin (k * t) → List V,
          (∀ i ∈ s', IsDirPathBetween G₀.Adj (snkB i) (srcA i) (P' i) ∧ (P' i).length ≤ k + 2 ∧
            ∀ w ∈ (P' i).toFinset \ {snkB i, srcA i}, w ∉ colored col3) ∧
          (∀ i₁ ∈ s', ∀ i₂ ∈ s', i₁ ≠ i₂ →
            Disjoint ((P' i₁).toFinset \ {snkB i₁, srcA i₁}) ((P' i₂).toFinset \ {snkB i₂, srcA i₂}))) →
        s'.card ≤ s.card := by
    let validS := (Finset.univ : Finset (Fin (k * t))).powerset.filter fun s =>
      ∃ P : Fin (k * t) → List V,
        (∀ i ∈ s, IsDirPathBetween G₀.Adj (snkB i) (srcA i) (P i) ∧ (P i).length ≤ k + 2 ∧
          ∀ w ∈ (P i).toFinset \ {snkB i, srcA i}, w ∉ colored col3) ∧
        (∀ i₁ ∈ s, ∀ i₂ ∈ s, i₁ ≠ i₂ →
          Disjoint ((P i₁).toFinset \ {snkB i₁, srcA i₁}) ((P i₂).toFinset \ {snkB i₂, srcA i₂}))
    have hempty_in : (∅ : Finset (Fin (k * t))) ∈ validS := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.empty_subset _, fun _ => [], fun _ h => by simp at h, fun _ h => by simp at h⟩
    obtain ⟨s, hs_in, hs_max⟩ := Finset.exists_max_image validS Finset.card ⟨∅, hempty_in⟩
    refine ⟨s, (Finset.mem_filter.mp hs_in).2, fun s' hs' => ?_⟩
    exact hs_max s' (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hs'⟩)
  obtain ⟨I_short, ⟨P_short, hPshort_prop, hPshort_disj⟩, hIshort_max⟩ := hpack_ex
  let I_long : Finset (Fin (k * t)) := Finset.univ \ I_short
  -- Colour internal vertices of P_short i (i ∈ I_short) with blockOf i
  let shortInt : Fin (k * t) → Finset V := fun i => (P_short i).toFinset \ {snkB i, srcA i}
  let shortAll : Finset V := I_short.biUnion shortInt
  have hshortAll_disj_col3 : Disjoint shortAll (colored col3) := by
    rw [Finset.disjoint_left]; intro w hw
    rw [Finset.mem_biUnion] at hw; obtain ⟨i, hi, hwi⟩ := hw
    exact (hPshort_prop i hi).2.2 w hwi
  have hshortAll_card : shortAll.card ≤ k * k * t := by
    calc shortAll.card ≤ ∑ i ∈ I_short, (shortInt i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ I_short, k := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hlen := (hPshort_prop i hi).2.1
        obtain ⟨_, hne, hh, hl⟩ := (hPshort_prop i hi).1
        have hsub : ({snkB i, srcA i} : Finset V) ⊆ (P_short i).toFinset := by
          intro z hz; simp at hz; rcases hz with rfl | rfl
          · exact List.mem_toFinset.mpr (hh ▸ List.head_mem hne)
          · exact List.mem_toFinset.mpr (hl ▸ List.getLast_mem hne)
        rw [Finset.card_sdiff_of_subset hsub, Finset.card_pair (hsnk_src_disj i i)]
        have := List.toFinset_card_le (P_short i)
        omega
      _ ≤ k * k * t := by
        rw [Finset.sum_const, smul_eq_mul]
        have hle : I_short.card ≤ k * t := (Finset.card_le_univ _).trans (by simp)
        calc I_short.card * k ≤ (k * t) * k := Nat.mul_le_mul_right k hle
          _ = k * k * t := by ring
  let col4a : V → Option (Fin t) := fun v =>
    if h : ∃ i ∈ I_short, v ∈ shortInt i then some (blockOf h.choose) else col3 v
  have hext3_4a : ColExtends col3 col4a := by
    intro v j hcv; dsimp only [col4a]
    split_ifs with h
    · obtain ⟨i, hi, hvi⟩ := h
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hcv]⟩) ((hPshort_prop i hi).2.2 v hvi)
    · exact hcv
  have hcol4a_short : ∀ i ∈ I_short, ∀ v ∈ shortInt i, col4a v = some (blockOf i) := by
    intro i hi v hv
    have hex : ∃ i' ∈ I_short, v ∈ shortInt i' := ⟨i, hi, hv⟩
    simp only [col4a, hex, ↓reduceDIte]
    congr 1
    obtain ⟨hi', hvi'⟩ := hex.choose_spec
    by_contra hne
    exact Finset.disjoint_left.mp (hPshort_disj hex.choose hi' i hi (fun h => hne (congrArg blockOf h))) hvi' hv
  have hcol4a_colored : colored col4a = colored col3 ∪ shortAll := by
    ext v; simp only [colored, col4a, shortAll, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_biUnion]
    split_ifs with h
    · simp only [Option.isSome_some, true_iff]; exact Or.inr h
    · simp only [h, or_false]
  -- Claim 4.1: make all vertices in shortAll safe using greedy_colour_nbrs (inNbrs avoiding EA, then outNbrs avoiding E)!
  have hshort_nXY : ∀ v ∈ shortAll, v ∉ XY := fun v hv hXY =>
    Finset.disjoint_left.mp hshortAll_disj_col3 hv (colored_mono hext03 (hcol0_colored ▸ hXY_sub_D hXY))
  obtain ⟨col4b, add4b, hext4b, hdisj_col4b, hdisj_EA4b, hcard4b, hcol4b_eq, hgood4b⟩ :=
    greedy_colour_nbrs k col4a shortAll (fun v => inNbr G₀ Finset.univ v) EA
      (fun v hv => by have : v ∈ colored col4a := hcol4a_colored ▸ Finset.mem_union_right _ hv; exact (Finset.mem_filter.mp this).2) (by
      intro v hv
      have hgap := hEA_gap v (hshort_nXY v hv)
      dsimp only [N43_pre] at hgap
      rw [hcol4a_colored, Finset.card_union_of_disjoint hshortAll_disj_col3.symm]
      have hbound : (colored col3).card + shortAll.card + k * shortAll.card ≤ N41 := by
        have hk1 : (k + 1) * (k * k * t) ≤ (k + 1) ^ 2 * k * k * t := by
          calc (k + 1) * (k * k * t) ≤ (k + 1) * ((k + 1) * (k * k * t)) := Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
            _ = (k + 1) ^ 2 * k * k * t := by ring
        have hs : shortAll.card + k * shortAll.card ≤ (k + 1) * (k * k * t) := by
          calc shortAll.card + k * shortAll.card = (k + 1) * shortAll.card := by ring
            _ ≤ (k + 1) * (k * k * t) := Nat.mul_le_mul_left _ hshortAll_card
        dsimp only [N41]; omega
      change (colored col3).card + shortAll.card + k * shortAll.card + EA.card ≤ inDeg G₀ Finset.univ v
      omega)
  let T4b : Finset V := shortAll ∪ add4b
  have hT4b_nXY : ∀ v ∈ T4b, v ∉ XY := fun v hv hXY => by
    rcases Finset.mem_union.mp hv with h1 | h2
    · exact hshort_nXY v h1 hXY
    · exact Finset.disjoint_left.mp hdisj_col4b h2 (colored_mono (colExtends_trans hext03 hext3_4a) (hcol0_colored ▸ hXY_sub_D hXY))
  have hT4b_card : T4b.card ≤ (k + 1) * (k * k * t) := by
    calc T4b.card ≤ shortAll.card + add4b.card := Finset.card_union_le shortAll add4b
      _ ≤ k * k * t + k * (k * k * t) := Nat.add_le_add hshortAll_card (hcard4b.trans (Nat.mul_le_mul_left k hshortAll_card))
      _ = (k + 1) * (k * k * t) := by ring
  obtain ⟨col41, add41, hext41, hdisj_col41, hdisj_E41, hcard41, hcol41_eq, hgood41⟩ :=
    greedy_colour_nbrs k col4b T4b (fun v => outNbr G₀ Finset.univ v) E
      (fun v hv => by
        have : v ∈ colored col4b := by
          rw [hcol4b_eq, hcol4a_colored]
          rcases Finset.mem_union.mp hv with h1 | h2
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ h1)
          · exact Finset.mem_union_right _ h2
        exact (Finset.mem_filter.mp this).2) (by
      intro v hv
      have hgap := hE_gap v (hT4b_nXY v hv)
      dsimp only [N43_pre] at hgap
      rw [hcol4b_eq, Finset.card_union_of_disjoint hdisj_col4b.symm,
        hcol4a_colored, Finset.card_union_of_disjoint hshortAll_disj_col3.symm]
      have hbound : (colored col3).card + shortAll.card + add4b.card + k * T4b.card ≤ N41 := by
        have h1 : shortAll.card + add4b.card ≤ (k + 1) * (k * k * t) := by
          calc shortAll.card + add4b.card ≤ k * k * t + k * (k * k * t) :=
                Nat.add_le_add hshortAll_card (hcard4b.trans (Nat.mul_le_mul_left k hshortAll_card))
            _ = (k + 1) * (k * k * t) := by ring
        have h2 : k * T4b.card ≤ k * ((k + 1) * (k * k * t)) := Nat.mul_le_mul_left k hT4b_card
        have h3 : (k + 1) * (k * k * t) + k * ((k + 1) * (k * k * t)) = (k + 1) ^ 2 * k * k * t := by ring
        dsimp only [N41]; omega
      change (colored col3).card + shortAll.card + add4b.card + k * T4b.card + E.card ≤ outDeg G₀ Finset.univ v
      omega)
  have hext3_41 : ColExtends col3 col41 := colExtends_trans (colExtends_trans hext3_4a hext4b) hext41
  have hcol41_card : (colored col41).card ≤ N41 := by
    rw [hcol41_eq, Finset.card_union_of_disjoint hdisj_col41.symm,
      hcol4b_eq, Finset.card_union_of_disjoint hdisj_col4b.symm,
      hcol4a_colored, Finset.card_union_of_disjoint hshortAll_disj_col3.symm]
    have h1 : shortAll.card + add4b.card ≤ (k + 1) * (k * k * t) := by
      calc shortAll.card + add4b.card ≤ k * k * t + k * (k * k * t) :=
            Nat.add_le_add hshortAll_card (hcard4b.trans (Nat.mul_le_mul_left k hshortAll_card))
        _ = (k + 1) * (k * k * t) := by ring
    have h2 : add41.card ≤ k * ((k + 1) * (k * k * t)) := hcard41.trans (Nat.mul_le_mul_left k hT4b_card)
    have h3 : (k + 1) * (k * k * t) + k * ((k + 1) * (k * k * t)) = (k + 1) ^ 2 * k * k * t := by ring
    dsimp only [N41]; omega
  have hcol41_safe : AllSafe G₀ k D EA EB col41 := by
    have hadd41_safe : ∀ w ∈ add41, FwdSafe G₀ k D EB col41 w ∧ BwdSafe G₀ k D EA col41 w := by
      intro w hw
      have hwnD : w ∉ D := fun h => Finset.disjoint_left.mp hdisj_col41 hw
        (colored_mono (colExtends_trans hext03 (colExtends_trans hext3_4a hext4b)) (hcol0_colored ▸ h))
      have hwnE : w ∉ E := Finset.disjoint_left.mp hdisj_E41 hw
      have hwnEA : w ∉ EA := fun h => hwnE (Finset.mem_union_left _ h)
      have hwnEB : w ∉ EB := fun h => hwnE (Finset.mem_union_right _ h)
      exact ⟨fwdSafe_of_not_mem (by simp only [Finset.mem_union, not_or]; exact ⟨hwnD, hwnEB⟩),
        bwdSafe_of_not_mem (by simp only [Finset.mem_union, not_or]; exact ⟨hwnD, hwnEA⟩)⟩
    have hT4b_fwd : ∀ v ∈ T4b, FwdSafe G₀ k D EB col41 v := by
      intro v hv
      have hvc : (col4b v).isSome := by
        have : v ∈ colored col4b := by
          rw [hcol4b_eq, hcol4a_colored]
          rcases Finset.mem_union.mp hv with h1 | h2
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ h1)
          · exact Finset.mem_union_right _ h2
        exact (Finset.mem_filter.mp this).2
      cases hc : col4b v with
      | none => simp [hc] at hvc
      | some j =>
        obtain ⟨W, hWsub, hWcard, hWcol⟩ := hgood41 v hv j hc
        exact fwdSafe_of_k_outNbrs (hext41 v j hc) hWcard.ge fun w hw => by
          have hwi := Finset.mem_inter.mp (hWsub hw)
          exact ⟨hWcol w hw, (Finset.mem_filter.mp hwi.2).2, (hadd41_safe w hwi.1).1⟩
    have hadd4b_bwd : ∀ w ∈ add4b, BwdSafe G₀ k D EA col41 w := by
      intro w hw
      have hwnD : w ∉ D := fun h => Finset.disjoint_left.mp hdisj_col4b hw
        (colored_mono (colExtends_trans hext03 hext3_4a) (hcol0_colored ▸ h))
      have hwnEA : w ∉ EA := Finset.disjoint_left.mp hdisj_EA4b hw
      exact bwdSafe_of_not_mem (by simp only [Finset.mem_union, not_or]; exact ⟨hwnD, hwnEA⟩)
    intro v
    by_cases hv3 : v ∈ colored col3
    · have h3s := (Finset.mem_filter.mp hv3).2
      exact ⟨fwdSafe_mono hext3_41 h3s (hcol3_safe v).1, bwdSafe_mono hext3_41 h3s (hcol3_safe v).2⟩
    · by_cases hvs : v ∈ shortAll
      · refine ⟨hT4b_fwd v (Finset.mem_union_left _ hvs), ?_⟩
        have hvc : (col4a v).isSome := by
          have : v ∈ colored col4a := hcol4a_colored ▸ Finset.mem_union_right _ hvs
          exact (Finset.mem_filter.mp this).2
        cases hc : col4a v with
        | none => simp [hc] at hvc
        | some j =>
          obtain ⟨W, hWsub, hWcard, hWcol⟩ := hgood4b v hvs j hc
          exact bwdSafe_of_k_inNbrs (hext41 v j (hext4b v j hc)) hWcard.ge fun w hw => by
            have hwi := Finset.mem_inter.mp (hWsub hw)
            exact ⟨hext41 w j (hWcol w hw), (Finset.mem_filter.mp hwi.2).2, hadd4b_bwd w hwi.1⟩
      · by_cases hv4b : v ∈ add4b
        · exact ⟨hT4b_fwd v (Finset.mem_union_right _ hv4b), hadd4b_bwd v hv4b⟩
        · by_cases hv41 : v ∈ add41
          · exact hadd41_safe v hv41
          · have hnone : col41 v = none := by
              have hnc : v ∉ colored col41 := by
                rw [hcol41_eq, hcol4b_eq, hcol4a_colored]
                simp [hv3, hvs, hv4b, hv41]
              simp only [colored, Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_ne_none,
                ne_eq, not_not] at hnc; exact hnc
            exact ⟨fun j hj => by simp [hnone] at hj, fun j hj => by simp [hnone] at hj⟩
  -- Key property of I_long: ANY directed path from snkB i to srcA i (i ∈ I_long) with uncoloured internal vertices has length ≥ k + 3!
  have hlong_min_len : ∀ i ∈ I_long, ∀ P : List V,
      IsDirPathBetween G₀.Adj (snkB i) (srcA i) P →
      (∀ w ∈ P.toFinset \ {snkB i, srcA i}, w ∉ colored col41) →
      k + 3 ≤ P.length := by
    intro i hi P hP hP_uncol
    by_contra hlt; push Not at hlt
    have hi_nshort : i ∉ I_short := (Finset.mem_sdiff.mp hi).2
    have hP_uncol3 : ∀ w ∈ P.toFinset \ {snkB i, srcA i}, w ∉ colored col3 := fun w hw h3 =>
      hP_uncol w hw (colored_mono hext3_41 h3)
    have hP_disj_short : ∀ i' ∈ I_short, Disjoint (P.toFinset \ {snkB i, srcA i}) (shortInt i') := by
      intro i' hi'; rw [Finset.disjoint_left]; intro w hwP hwi'
      exact hP_uncol w hwP (colored_mono (colExtends_trans hext4b hext41)
        (hcol4a_colored ▸ Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i', hi', hwi'⟩)))
    let P' : Fin (k * t) → List V := fun r => if r = i then P else P_short r
    have hle_max := hIshort_max (insert i I_short) ⟨P', ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hi_nshort] at hle_max; omega
    · intro r hr; rcases Finset.mem_insert.mp hr with rfl | hrS
      · simp only [P', ↓reduceIte]; exact ⟨hP, by omega, hP_uncol3⟩
      · have hne : r ≠ i := fun h => hi_nshort (h ▸ hrS)
        simp only [P', hne, ↓reduceIte]; exact hPshort_prop r hrS
    · intro r₁ hr₁ r₂ hr₂ hne
      rcases Finset.mem_insert.mp hr₁ with rfl | h1 <;> rcases Finset.mem_insert.mp hr₂ with rfl | h2
      · exact absurd rfl hne
      · simp only [P', ↓reduceIte, hne.symm]; exact hP_disj_short r₂ h2
      · simp only [P', ↓reduceIte, hne]; exact (hP_disj_short r₁ h1).symm
      · have h1' : r₁ ≠ i := fun h => hi_nshort (h ▸ h1)
        have h2' : r₂ ≠ i := fun h => hi_nshort (h ▸ h2)
        simp only [P', h1', h2', ↓reduceIte]; exact hPshort_disj r₁ h1 r₂ h2 hne
  -- CLAIM 4.2: Use multi_short_paths on T' = (univ \ colored col41) ∪ {snkB i, srcA i | i ∈ I_long}
  let rL : ℕ := I_long.card
  let eL : Fin rL ≃ I_long := (Fintype.equivFinOfCardEq (by simp [rL])).symm
  let xL : Fin rL → V := fun u => snkB (eL u).1
  let yL : Fin rL → V := fun u => srcA (eL u).1
  let termsL : Finset V := Finset.univ.image xL ∪ Finset.univ.image yL
  let S_long : Finset V := (Finset.univ \ colored col41) ∪ termsL
  have hSlong_strong : IsKStrongOn G₀ (S_long : Set V) (600 * (rL * q * 8) + 2 * rL) := by
    let del : Finset V := Finset.univ \ S_long
    have hdel_sub : del ⊆ colored col41 := fun w hw => by
      rw [Finset.mem_sdiff] at hw; by_contra hnot
      exact hw.2 (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩))
    have hdel_card : del.card ≤ N41 := (Finset.card_le_card hdel_sub).trans hcol41_card
    have hrL_le : rL ≤ k * t := (Finset.card_le_univ _).trans (by simp)
    have hbound : del.card + (600 * (rL * q * 8) + 2 * rL) ≤ g := by
      have h1 : 600 * (rL * q * 8) ≤ 600 * (k * t * q * 8) :=
        Nat.mul_le_mul_left 600 (Nat.mul_le_mul_right 8 (Nat.mul_le_mul_right q hrL_le))
      have h2 : 2 * rL ≤ 10 * k * t := by
        have : 10 * k * t = 10 * (k * t) := by ring
        omega
      omega
    refine ⟨?_, ?_⟩
    · rw [Set.ncard_coe_finset]
      have hsd := Finset.card_sdiff_add_card_inter (Finset.univ : Finset V) S_long
      rw [Finset.inter_eq_right.mpr (Finset.subset_univ _), Finset.card_univ] at hsd
      change del.card + S_long.card = n at hsd
      omega
    · intro Z hZ
      have heq : (S_long : Set V) \ (Z : Set V) = Set.univ \ ((del ∪ Z : Finset V) : Set V) := by
        ext w
        simp only [Set.mem_sdiff, Finset.mem_coe, Set.mem_univ, Finset.mem_univ, true_and, Finset.mem_union,
          del, Finset.mem_sdiff, not_or, not_not]
      rw [heq]
      have hUZ : (del ∪ Z).card < g := by have := Finset.card_union_le del Z; omega
      exact hstrong₀.2 (del ∪ Z) hUZ
  obtain ⟨P_raw, hPraw_bet, hPraw_avoid, hPraw_disj, hPraw_size⟩ :=
    multi_short_paths hT₀ (s := 8) (by omega) hSlong_strong xL yL
      (fun u₁ u₂ h => eL.injective (Subtype.ext (hsnkB_inj h)))
      (fun u₁ u₂ h => eL.injective (Subtype.ext (hsrcA_inj h)))
      (fun u => Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)))
      (fun u => Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)))
      (fun u₁ u₂ => hsnk_src_disj _ _)
  -- Shorten every P_raw u a to a chordless (backwards-transitive!) path P_long u a
  have hPlong_ex : ∀ u : Fin rL, ∀ a : Fin q,
      ∃ P : List V, IsDirPathBetween G₀.Adj (xL u) (yL u) P ∧ (∀ w ∈ P, w ∈ P_raw u a) ∧
        ∀ p₁ p₂ : ℕ, (hgap : p₁ + 2 ≤ p₂) → (hp₂ : p₂ < P.length) → G₀.Adj P[p₂] (P[p₁]'(by omega)) := by
    intro u a
    obtain ⟨P, hP, hPsub, hchord⟩ := exists_chordless_dirPath (hPraw_bet u a).1
    refine ⟨P, hP, hPsub, fun p₁ p₂ hgap hp₂ => ?_⟩
    have hne : P[p₁]'(by omega) ≠ P[p₂] := fun heq => by
      have hval : p₁ = p₂ := Fin.mk.inj ((List.nodup_iff_injective_getElem.mp hP.1.2.1)
        (a₁ := ⟨p₁, by omega⟩) (a₂ := ⟨p₂, hp₂⟩) heq)
      omega
    exact not_not.mp fun hnot => hchord p₁ p₂ hgap hp₂ ((hT₀.2 _ _ hne).mpr hnot)
  choose P_long hPlong_bet hPlong_sub hPlong_bt using hPlong_ex
  -- For each (u, a), extract its interior list intList u a := (P_long u a).tail.dropLast
  let intList : Fin rL → Fin q → List V := fun u a => ((P_long u a).drop 1).take ((P_long u a).length - 2)
  have hPlong_uncol : ∀ u a, ∀ w ∈ (P_long u a).toFinset \ {xL u, yL u}, w ∉ colored col41 := by
    intro u a w hw
    rw [Finset.mem_sdiff, List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton, not_or] at hw
    have hw_raw := hPlong_sub u a w hw.1
    have hw_Slong := (hPraw_bet u a).2 w hw_raw
    have hw_nterms := hPraw_avoid u a w hw_raw hw.2.1 hw.2.2
    rcases Finset.mem_union.mp hw_Slong with h1 | h2
    · exact (Finset.mem_sdiff.mp h1).2
    · exact absurd h2 hw_nterms
  have hPlong_len : ∀ u a, k + 3 ≤ (P_long u a).length := fun u a =>
    hlong_min_len (eL u).1 (eL u).2 (P_long u a) (hPlong_bet u a) (hPlong_uncol u a)
  have hintList_len : ∀ u a, (intList u a).length = (P_long u a).length - 2 := fun u a => by
    dsimp only [intList]
    rw [List.length_take_of_le (by rw [List.length_drop]; have := hPlong_len u a; omega)]
  have hintList_get : ∀ u a (idx : ℕ) (hidx : idx < (intList u a).length),
      (intList u a)[idx] = (P_long u a)[idx + 1]'(by rw [hintList_len] at hidx; omega) := by
    intro u a idx hidx
    dsimp only [intList]
    rw [List.getElem_take, List.getElem_drop]; congr 1; omega
  have hintList_toF : ∀ u a, (intList u a).toFinset = (P_long u a).toFinset \ {xL u, yL u} := by
    intro u a
    have hdir := (hPlong_bet u a).1
    obtain ⟨_, hne, hh, hl⟩ := hPlong_bet u a
    have hlen := hPlong_len u a
    ext w
    rw [List.mem_toFinset, Finset.mem_sdiff, List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro hw
      obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hw
      rw [hintList_get u a idx hidx]
      have hidx_lt : idx + 1 < (P_long u a).length := by rw [hintList_len] at hidx; omega
      refine ⟨List.getElem_mem hidx_lt, ?_, ?_⟩
      · intro heq
        have h0 : (P_long u a)[0]'(by omega) = xL u := by rw [← List.head_eq_getElem_zero]; exact hh
        have hval : idx + 1 = 0 := Fin.mk.inj ((List.nodup_iff_injective_getElem.mp hdir.2.1)
          (a₁ := ⟨idx + 1, hidx_lt⟩) (a₂ := ⟨0, by omega⟩) (heq.trans h0.symm))
        omega
      · intro heq
        have hlast : (P_long u a)[(P_long u a).length - 1]'(by omega) = yL u := by
          rw [← List.getLast_eq_getElem]; exact hl
        have hval : idx + 1 = (P_long u a).length - 1 := Fin.mk.inj ((List.nodup_iff_injective_getElem.mp hdir.2.1)
          (a₁ := ⟨idx + 1, hidx_lt⟩) (a₂ := ⟨(P_long u a).length - 1, by omega⟩) (heq.trans hlast.symm))
        rw [hintList_len] at hidx; omega
    · rintro ⟨hwP, hwx, hwy⟩
      obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hwP
      have hidx_ne0 : idx ≠ 0 := fun h0 => hwx (by subst h0; rw [← List.head_eq_getElem_zero]; exact hh)
      have hidx_nelast : idx ≠ (P_long u a).length - 1 := fun hlast =>
        hwy (by subst hlast; rw [← List.getLast_eq_getElem]; exact hl)
      have hidx' : idx - 1 < (intList u a).length := by rw [hintList_len]; omega
      have heq : (intList u a)[idx - 1] = (P_long u a)[idx] := by
        rw [hintList_get u a (idx - 1) hidx']; congr 1; omega
      rw [← heq]; exact List.getElem_mem hidx'
  have hintList_dir : ∀ u a, IsDirPath G₀.Adj (intList u a) := by
    intro u a
    have hdir := (hPlong_bet u a).1
    have hlen := hPlong_len u a
    refine ⟨by intro h; have := congrArg List.length h; rw [hintList_len] at this; simp at this; omega,
      hdir.2.1.drop.take, fun i hi => ?_⟩
    rw [hintList_get u a i (by omega), hintList_get u a (i + 1) hi]
    exact hdir.2.2 (i + 1) (by rw [hintList_len] at hi; omega)
  have hintList_bt : ∀ u a (p₁ p₂ : ℕ), (hgap : p₁ + 2 ≤ p₂) → (hp₂ : p₂ < (intList u a).length) →
      G₀.Adj (intList u a)[p₂] ((intList u a)[p₁]'(by omega)) := by
    intro u a p₁ p₂ hgap hp₂
    rw [hintList_get u a p₂ hp₂, hintList_get u a p₁ (by omega)]
    exact hPlong_bt u a (p₁ + 1) (p₂ + 1) (by omega) (by rw [hintList_len] at hp₂; omega)
  have hintList_disj : ∀ u₁ a₁ u₂ a₂, (u₁, a₁) ≠ (u₂, a₂) →
      Disjoint (intList u₁ a₁).toFinset (intList u₂ a₂).toFinset := by
    intro u₁ a₁ u₂ a₂ hne
    rw [hintList_toF, hintList_toF]
    exact Finset.disjoint_of_subset_left
      (Finset.sdiff_subset_sdiff (fun w hw => List.mem_toFinset.mpr (hPlong_sub u₁ a₁ w (List.mem_toFinset.mp hw))) le_rfl)
      (Finset.disjoint_of_subset_right
        (Finset.sdiff_subset_sdiff (fun w hw => List.mem_toFinset.mpr (hPlong_sub u₂ a₂ w (List.mem_toFinset.mp hw))) le_rfl)
        (hPraw_disj u₁ a₁ u₂ a₂ hne))
  have hintAll_size : (Finset.univ.biUnion fun p : Fin rL × Fin q => (intList p.1 p.2).toFinset).card ≤ n / 8 := by
    have hsub : (Finset.univ.biUnion fun p : Fin rL × Fin q => (intList p.1 p.2).toFinset) ⊆
        (Finset.univ.biUnion fun p : Fin rL × Fin q => (P_raw p.1 p.2).toFinset \ {xL p.1, yL p.1}) := by
      intro w hw; rw [Finset.mem_biUnion] at hw ⊢
      obtain ⟨p, _, hp⟩ := hw; rw [hintList_toF] at hp
      exact ⟨p, Finset.mem_univ _, Finset.sdiff_subset_sdiff
        (fun z hz => List.mem_toFinset.mpr (hPlong_sub p.1 p.2 z (List.mem_toFinset.mp hz))) le_rfl hp⟩
    calc (Finset.univ.biUnion fun p : Fin rL × Fin q => (intList p.1 p.2).toFinset).card
        ≤ (Finset.univ.biUnion fun p : Fin rL × Fin q => (P_raw p.1 p.2).toFinset \ {xL p.1, yL p.1}).card :=
          Finset.card_le_card hsub
      _ ≤ S_long.card / 8 := hPraw_size
      _ ≤ n / 8 := Nat.div_le_div_right (Finset.card_le_univ _)
  -- CLAIM 4.3: Apply KOT Lemma 2.7 for each colour j : Fin t!
  let idxJ : Fin t → Finset (Fin rL) := fun j => Finset.univ.filter fun u => blockOf (eL u).1 = j
  let pairsJ : Fin t → Finset (Fin rL × Fin q) := fun j => idxJ j ×ˢ Finset.univ
  let unionJ : Fin t → Finset V := fun j => (pairsJ j).biUnion fun p => (intList p.1 p.2).toFinset
  have hunionJ_disj : ∀ j₁ j₂ : Fin t, j₁ ≠ j₂ → Disjoint (unionJ j₁) (unionJ j₂) := by
    intro j₁ j₂ hne; rw [Finset.disjoint_left]; intro w h1 h2
    rw [Finset.mem_biUnion] at h1 h2
    obtain ⟨p₁, hp1, hw1⟩ := h1; obtain ⟨p₂, hp2, hw2⟩ := h2
    have hpne : p₁ ≠ p₂ := by
      intro heq; subst heq
      have h1' := (Finset.mem_filter.mp (Finset.mem_product.mp hp1).1).2
      have h2' := (Finset.mem_filter.mp (Finset.mem_product.mp hp2).1).2
      exact hne (h1'.symm.trans h2')
    exact Finset.disjoint_left.mp (hintList_disj p₁.1 p₁.2 p₂.1 p₂.2 hpne) hw1 hw2
  have hunionJ_disj_col41 : ∀ j, Disjoint (unionJ j) (colored col41) := by
    intro j; rw [Finset.disjoint_left]; intro w hw
    rw [Finset.mem_biUnion] at hw; obtain ⟨p, _, hwp⟩ := hw
    rw [hintList_toF] at hwp; exact hPlong_uncol p.1 p.2 w hwp
  -- For each j : Fin t, invoke backwards_transitive_reach_out and backwards_transitive_reach_in!
  have hUW_ex : ∀ j : Fin t,
      ∃ U U' W W' : Finset V,
        U ⊆ U' ∧ U' ⊆ unionJ j ∧ U.card ≤ 2 * k * (k + 1) ∧ U'.card ≤ k * q * (k + 1) ∧
        W ⊆ W' ∧ W' ⊆ unionJ j ∧ W.card ≤ 2 * k * (k + 1) ∧ W'.card ≤ k * q * (k + 1) ∧
        (∀ S_del : Finset V, S_del.card < k → ∀ v ∈ unionJ j \ S_del,
          (∃ u ∈ U \ S_del, WalkIn G₀ ((insert v U') \ S_del) v u) ∧
          (∃ w ∈ W \ S_del, WalkIn G₀ ((insert v W') \ S_del) w v)) := by
    intro j
    let ℓj := (pairsJ j).card
    let eJ : Fin ℓj ≃ pairsJ j := (Fintype.equivFinOfCardEq (by simp [ℓj])).symm
    let Qj : Fin ℓj → List V := fun r => intList (eJ r).1.1 (eJ r).1.2
    have hbi_eq : (Finset.univ.biUnion fun r : Fin ℓj => (Qj r).toFinset) = unionJ j := by
      ext w; simp only [unionJ, Qj, Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨r, hr⟩; exact ⟨(eJ r).1, (eJ r).2, hr⟩
      · rintro ⟨p, hp, hwp⟩; exact ⟨eJ.symm ⟨p, hp⟩, by simpa using hwp⟩
    have hℓj_le : ℓj ≤ k * q := by
      have hidx_le : (idxJ j).card ≤ k := by
        let f : Fin rL → Fin k := fun u => ⟨(eL u).1.val % k, Nat.mod_lt _ (by omega)⟩
        have hinj : Set.InjOn f (idxJ j : Set (Fin rL)) := by
          intro u₁ hu₁ u₂ hu₂ heq
          have hb1 : (eL u₁).1.val / k = j.val := congrArg Fin.val (Finset.mem_filter.mp (Finset.mem_coe.mp hu₁)).2
          have hb2 : (eL u₂).1.val / k = j.val := congrArg Fin.val (Finset.mem_filter.mp (Finset.mem_coe.mp hu₂)).2
          have hm : (eL u₁).1.val % k = (eL u₂).1.val % k := congrArg Fin.val heq
          have hval : (eL u₁).1.val = (eL u₂).1.val := by
            have d1 := Nat.div_add_mod (eL u₁).1.val k
            have d2 := Nat.div_add_mod (eL u₂).1.val k
            rw [← d1, ← d2, hb1, hb2, hm]
          exact eL.injective (Subtype.ext (Fin.ext hval))
        calc (idxJ j).card = ((idxJ j).image f).card := (Finset.card_image_of_injOn hinj).symm
          _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_univ _
          _ = k := by simp
      dsimp only [ℓj, pairsJ]
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
      exact Nat.mul_le_mul_right q hidx_le
    obtain ⟨U, U', hUU', hU'sub, hUc, hU'c, hreach_out⟩ :=
      backwards_transitive_reach_out hT₀ (by omega : 1 ≤ k) Qj
        (fun r => hintList_dir _ _)
        (fun r => by rw [hintList_len]; have := hPlong_len (eJ r).1.1 (eJ r).1.2; omega)
        (fun r a b hab hb => hintList_bt _ _ a b hab hb)
        (fun r₁ r₂ hne => hintList_disj _ _ _ _ (fun h => hne (eJ.injective (Subtype.ext h))))
    obtain ⟨W, W', hWW', hW'sub, hWc, hW'c, hreach_in⟩ :=
      backwards_transitive_reach_in hT₀ (by omega : 1 ≤ k) Qj
        (fun r => hintList_dir _ _)
        (fun r => by rw [hintList_len]; have := hPlong_len (eJ r).1.1 (eJ r).1.2; omega)
        (fun r a b hab hb => hintList_bt _ _ a b hab hb)
        (fun r₁ r₂ hne => hintList_disj _ _ _ _ (fun h => hne (eJ.injective (Subtype.ext h))))
    rw [hbi_eq] at hU'sub hW'sub hreach_out hreach_in
    refine ⟨U, U', W, W', hUU', hU'sub, hUc, by rw [hU'c]; exact Nat.mul_le_mul_right _ hℓj_le,
      hWW', hW'sub, hWc, by rw [hW'c]; exact Nat.mul_le_mul_right _ hℓj_le,
      fun S_del hS v hv => ⟨hreach_out S_del hS v hv, hreach_in S_del hS v hv⟩⟩
  choose Uj U'j Wj W'j hUU'j hU'sub hUjc hU'jc hWW'j hW'sub hWjc hW'jc hUWreach using hUW_ex
  -- Colour U'j ∪ W'j with colour j for each j : Fin t
  let UW'j : Fin t → Finset V := fun j => U'j j ∪ W'j j
  let UW'_all : Finset V := Finset.univ.biUnion UW'j
  have hUW'j_sub : ∀ j, UW'j j ⊆ unionJ j := fun j => Finset.union_subset (hU'sub j) (hW'sub j)
  have hUW'_card : UW'_all.card ≤ 2 * q * k * t * (k + 1) := by
    calc UW'_all.card ≤ ∑ j : Fin t, (UW'j j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j : Fin t, (2 * k * q * (k + 1)) := Finset.sum_le_sum fun j _ => by
        calc (UW'j j).card ≤ (U'j j).card + (W'j j).card := Finset.card_union_le (U'j j) (W'j j)
          _ ≤ k * q * (k + 1) + k * q * (k + 1) := Nat.add_le_add (hU'jc j) (hW'jc j)
          _ = 2 * k * q * (k + 1) := by ring
      _ = 2 * q * k * t * (k + 1) := by simp [Finset.sum_const, smul_eq_mul]; ring
  let col42 : V → Option (Fin t) := fun v =>
    if h : ∃ j : Fin t, v ∈ UW'j j then some h.choose else col41 v
  have hext41_42 : ColExtends col41 col42 := by
    intro v j hcv; dsimp only [col42]
    split_ifs with h
    · obtain ⟨j', hj'⟩ := h
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hcv]⟩)
        (Finset.disjoint_left.mp (hunionJ_disj_col41 j') (hUW'j_sub j' hj'))
    · exact hcv
  have hcol42_UW' : ∀ j v, v ∈ UW'j j → col42 v = some j := by
    intro j v hv
    have hex : ∃ j' : Fin t, v ∈ UW'j j' := ⟨j, hv⟩
    simp only [col42, hex, ↓reduceDIte]; congr 1
    by_contra hne
    exact Finset.disjoint_left.mp (hunionJ_disj hex.choose j hne) (hUW'j_sub _ hex.choose_spec) (hUW'j_sub j hv)
  have hcol42_colored : colored col42 = colored col41 ∪ UW'_all := by
    ext v; simp only [colored, col42, UW'_all, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_biUnion]
    split_ifs with h
    · simp only [Option.isSome_some, true_iff]; exact Or.inr h
    · simp only [h, or_false]
  -- Greedily colour Z_in (k in-nbrs outside EA for each v ∈ ⋃ Wj) then Z_out (k out-nbrs outside E for each v ∈ ⋃ Uj ∪ Z_in)!
  let W_all : Finset V := Finset.univ.biUnion Wj
  let U_all : Finset V := Finset.univ.biUnion Uj
  have hW_all_card : W_all.card ≤ 2 * k * (k + 1) * t := by
    calc W_all.card ≤ ∑ j : Fin t, (Wj j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j : Fin t, (2 * k * (k + 1)) := Finset.sum_le_sum fun j _ => hWjc j
      _ = 2 * k * (k + 1) * t := by simp [Finset.sum_const, smul_eq_mul]; ring
  have hU_all_card : U_all.card ≤ 2 * k * (k + 1) * t := by
    calc U_all.card ≤ ∑ j : Fin t, (Uj j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j : Fin t, (2 * k * (k + 1)) := Finset.sum_le_sum fun j _ => hUjc j
      _ = 2 * k * (k + 1) * t := by simp [Finset.sum_const, smul_eq_mul]; ring
  have hW_nXY : ∀ v ∈ W_all, v ∉ XY := fun v hv hXY => by
    rw [Finset.mem_biUnion] at hv; obtain ⟨j, _, hvj⟩ := hv
    exact Finset.disjoint_left.mp (hunionJ_disj_col41 j) (hW'sub j (hWW'j j hvj))
      (colored_mono (colExtends_trans hext03 hext3_41) (hcol0_colored ▸ hXY_sub_D hXY))
  have hU_nXY : ∀ v ∈ U_all, v ∉ XY := fun v hv hXY => by
    rw [Finset.mem_biUnion] at hv; obtain ⟨j, _, hvj⟩ := hv
    exact Finset.disjoint_left.mp (hunionJ_disj_col41 j) (hU'sub j (hUU'j j hvj))
      (colored_mono (colExtends_trans hext03 hext3_41) (hcol0_colored ▸ hXY_sub_D hXY))
  have hZ_in_bd : k * W_all.card ≤ 2 * k ^ 2 * (k + 1) * t := by
    calc k * W_all.card ≤ k * (2 * k * (k + 1) * t) := Nat.mul_le_mul_left k hW_all_card
      _ = 2 * k ^ 2 * (k + 1) * t := by ring
  have hZ_tot_bd : 2 * k ^ 2 * (k + 1) * t + k * (2 * k * (k + 1) * t + 2 * k ^ 2 * (k + 1) * t) < q := by
    dsimp only [q]
    have h1 : k + 1 ≤ 2 * k := by omega
    have h2 : k + 2 ≤ 2 * k := by omega
    have h3 : (k + 1) * (k + 2) ≤ 4 * k * k := by
      calc (k + 1) * (k + 2) ≤ (2 * k) * (2 * k) := Nat.mul_le_mul h1 h2
        _ = 4 * k * k := by ring
    have h4 : 2 * k ^ 2 * (k + 1) * t + k * (2 * k * (k + 1) * t + 2 * k ^ 2 * (k + 1) * t) =
        2 * k ^ 2 * ((k + 1) * (k + 2)) * t := by ring
    rw [h4]
    have h5 : 2 * k ^ 2 * ((k + 1) * (k + 2)) * t ≤ 8 * k ^ 4 * t := by
      calc 2 * k ^ 2 * ((k + 1) * (k + 2)) * t
          ≤ 2 * k ^ 2 * (4 * k * k) * t := Nat.mul_le_mul_right t (Nat.mul_le_mul_left _ h3)
        _ = 8 * k ^ 4 * t := by ring
    have hk4_pos : 1 ≤ k ^ 4 * t := Nat.mul_pos (by positivity) (by omega)
    have h8_13 : 8 * (k ^ 4 * t) < 13 * (k ^ 4 * t) := Nat.mul_lt_mul_of_pos_right (by omega) hk4_pos
    have h8eq : 8 * k ^ 4 * t = 8 * (k ^ 4 * t) := by ring
    have h13eq : 13 * k ^ 4 * t = 13 * (k ^ 4 * t) := by ring
    omega
  obtain ⟨col43a, Z_in, hext43a, hdisj_col43a, hdisj_EA43a, hcard_Zin, hcol43a_eq, hgood43a⟩ :=
    greedy_colour_nbrs k col42 W_all (fun v => inNbr G₀ Finset.univ v) EA
      (fun v hv => by
        rw [Finset.mem_biUnion] at hv; obtain ⟨j, _, hvj⟩ := hv
        have := hcol42_UW' j v (Finset.mem_union_right _ (hWW'j j hvj)); simp [this]) (by
      intro v hv
      have hgap := hEA_gap v (hW_nXY v hv)
      have hc42 : (colored col42).card ≤ N41 + 2 * q * k * t * (k + 1) := by
        rw [hcol42_colored]; exact (Finset.card_union_le _ _).trans (Nat.add_le_add hcol41_card hUW'_card)
      dsimp only [N43_pre] at hgap
      change (colored col42).card + k * W_all.card + EA.card ≤ inDeg G₀ Finset.univ v
      omega)
  let T43b : Finset V := U_all ∪ Z_in
  have hT43b_nXY : ∀ v ∈ T43b, v ∉ XY := fun v hv hXY => by
    rcases Finset.mem_union.mp hv with h1 | h2
    · exact hU_nXY v h1 hXY
    · exact Finset.disjoint_left.mp hdisj_col43a h2
        (colored_mono (colExtends_trans hext03 (colExtends_trans hext3_41 hext41_42)) (hcol0_colored ▸ hXY_sub_D hXY))
  obtain ⟨col43b, Z_out, hext43b, hdisj_col43b, hdisj_E43b, hcard_Zout, hcol43b_eq, hgood43b⟩ :=
    greedy_colour_nbrs k col43a T43b (fun v => outNbr G₀ Finset.univ v) E
      (fun v hv => by
        rcases Finset.mem_union.mp hv with h1 | h2
        · rw [Finset.mem_biUnion] at h1; obtain ⟨j, _, hvj⟩ := h1
          have := hext43a v j (hcol42_UW' j v (Finset.mem_union_left _ (hUU'j j hvj))); simp [this]
        · have : v ∈ colored col43a := hcol43a_eq ▸ Finset.mem_union_right _ h2
          exact (Finset.mem_filter.mp this).2) (by
      intro v hv
      have hgap := hE_gap v (hT43b_nXY v hv)
      have hc43a : (colored col43a).card ≤ N41 + 2 * q * k * t * (k + 1) + Z_in.card := by
        rw [hcol43a_eq, Finset.card_union_of_disjoint hdisj_col43a.symm, hcol42_colored]
        have := Finset.card_union_le (colored col41) UW'_all; omega
      have hTcard : T43b.card ≤ 2 * k * (k + 1) * t + 2 * k ^ 2 * (k + 1) * t := by
        have h1 : T43b.card ≤ U_all.card + Z_in.card := Finset.card_union_le U_all Z_in
        omega
      have hmul : k * T43b.card ≤ k * (2 * k * (k + 1) * t + 2 * k ^ 2 * (k + 1) * t) :=
        Nat.mul_le_mul_left k hTcard
      dsimp only [N43_pre] at hgap
      change (colored col43a).card + k * T43b.card + E.card ≤ outDeg G₀ Finset.univ v
      omega)
  let Z : Finset V := Z_in ∪ Z_out
  have hZ_lt_q : Z.card < q := by
    have h1 : Z.card ≤ Z_in.card + Z_out.card := Finset.card_union_le Z_in Z_out
    have hTcard : T43b.card ≤ 2 * k * (k + 1) * t + 2 * k ^ 2 * (k + 1) * t :=
      (Finset.card_union_le U_all Z_in).trans (by omega)
    have hmul : k * T43b.card ≤ k * (2 * k * (k + 1) * t + 2 * k ^ 2 * (k + 1) * t) :=
      Nat.mul_le_mul_left k hTcard
    omega
  -- Final sweep of Claim 4.3: colour all remaining uncoloured vertices of unionJ j with colour j!
  let col4 : V → Option (Fin t) := fun v =>
    if (col43b v).isSome then col43b v
    else if h : ∃ j : Fin t, v ∈ unionJ j then some h.choose else none
  have hext43b_4 : ColExtends col43b col4 := fun v j h => by simp [col4, h]
  have hext41_4 : ColExtends col41 col4 :=
    colExtends_trans hext41_42 (colExtends_trans (colExtends_trans hext43a hext43b) hext43b_4)
  have hext04 : ColExtends col0 col4 := colExtends_trans (colExtends_trans hext03 hext3_41) hext41_4
  -- Every vertex in col4 is SAFE!
  have hcol4_safe : AllSafe G₀ k D EA EB col4 := by
    have hZout_safe : ∀ w ∈ Z_out, FwdSafe G₀ k D EB col4 w ∧ BwdSafe G₀ k D EA col4 w := by
      intro w hw
      have hwnD : w ∉ D := fun h => Finset.disjoint_left.mp hdisj_col43b hw
        (colored_mono (colExtends_trans hext03 (colExtends_trans hext3_41 (colExtends_trans hext41_42 hext43a)))
          (hcol0_colored ▸ h))
      have hwnE : w ∉ E := Finset.disjoint_left.mp hdisj_E43b hw
      have hwnEA : w ∉ EA := fun h => hwnE (Finset.mem_union_left _ h)
      have hwnEB : w ∉ EB := fun h => hwnE (Finset.mem_union_right _ h)
      exact ⟨fwdSafe_of_not_mem (by simp only [Finset.mem_union, not_or]; exact ⟨hwnD, hwnEB⟩),
        bwdSafe_of_not_mem (by simp only [Finset.mem_union, not_or]; exact ⟨hwnD, hwnEA⟩)⟩
    have hT43b_fwd : ∀ v ∈ T43b, FwdSafe G₀ k D EB col4 v := by
      intro v hv
      have hvc : (col43a v).isSome := by
        rcases Finset.mem_union.mp hv with h1 | h2
        · rw [Finset.mem_biUnion] at h1; obtain ⟨j, _, hvj⟩ := h1
          have := hext43a v j (hcol42_UW' j v (Finset.mem_union_left _ (hUU'j j hvj))); simp [this]
        · have hvc' : v ∈ colored col43a := hcol43a_eq ▸ Finset.mem_union_right _ h2
          exact (Finset.mem_filter.mp hvc').2
      cases hc : col43a v with
      | none => simp [hc] at hvc
      | some j =>
        obtain ⟨W, hWsub, hWcard, hWcol⟩ := hgood43b v hv j hc
        exact fwdSafe_of_k_outNbrs (hext43b_4 v j (hext43b v j hc)) hWcard.ge fun w hw => by
          have hwi := Finset.mem_inter.mp (hWsub hw)
          exact ⟨hext43b_4 w j (hWcol w hw), (Finset.mem_filter.mp hwi.2).2, (hZout_safe w hwi.1).1⟩
    have hZin_bwd : ∀ w ∈ Z_in, BwdSafe G₀ k D EA col4 w := by
      intro w hw
      have hwnD : w ∉ D := fun h => Finset.disjoint_left.mp hdisj_col43a hw
        (colored_mono (colExtends_trans hext03 (colExtends_trans hext3_41 hext41_42)) (hcol0_colored ▸ h))
      have hwnEA : w ∉ EA := Finset.disjoint_left.mp hdisj_EA43a hw
      exact bwdSafe_of_not_mem (by simp only [Finset.mem_union, not_or]; exact ⟨hwnD, hwnEA⟩)
    have hWj_bwd : ∀ j, ∀ v ∈ Wj j, BwdSafe G₀ k D EA col4 v := by
      intro j v hv
      have hcv42 : col42 v = some j := hcol42_UW' j v (Finset.mem_union_right _ (hWW'j j hv))
      obtain ⟨W, hWsub, hWcard, hWcol⟩ := hgood43a v (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hv⟩) j hcv42
      exact bwdSafe_of_k_inNbrs (hext43b_4 v j (hext43b v j (hext43a v j hcv42))) hWcard.ge fun w hw => by
        have hwi := Finset.mem_inter.mp (hWsub hw)
        exact ⟨hext43b_4 w j (hext43b w j (hWcol w hw)), (Finset.mem_filter.mp hwi.2).2, hZin_bwd w hwi.1⟩
    have hUj_fwd : ∀ j, ∀ v ∈ Uj j, FwdSafe G₀ k D EB col4 v := fun j v hv =>
      hT43b_fwd v (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hv⟩))
    have hU'j_sub_col4 : ∀ j, U'j j ⊆ colClass col4 j := fun j w hw => by
      simp only [colClass, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hext43b_4 w j (hext43b w j (hext43a w j (hcol42_UW' j w (Finset.mem_union_left _ hw))))
    have hW'j_sub_col4 : ∀ j, W'j j ⊆ colClass col4 j := fun j w hw => by
      simp only [colClass, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hext43b_4 w j (hext43b w j (hext43a w j (hcol42_UW' j w (Finset.mem_union_right _ hw))))
    -- Every vertex v ∈ unionJ j that has col4 v = some j is BOTH fwdSafe and bwdSafe by KOT Lemma 2.7!
    have hunionJ_safe : ∀ j v, v ∈ unionJ j → col4 v = some j →
        FwdSafe G₀ k D EB col4 v ∧ BwdSafe G₀ k D EA col4 v := by
      intro j v hvj hcv
      refine ⟨?_, ?_⟩
      · intro j' hcv' S_del hS hvS
        have hj : j' = j := Option.some.inj (hcv'.symm.trans hcv)
        subst hj
        obtain ⟨⟨u, hu, hwalk1⟩, _⟩ := hUWreach j' S_del hS v (Finset.mem_sdiff.mpr ⟨hvj, hvS⟩)
        rw [Finset.mem_sdiff] at hu
        obtain ⟨u₂, hu₂, hwalk2⟩ := hUj_fwd j' u hu.1 j'
          (by simpa [colClass] using hU'j_sub_col4 j' (hUU'j j' hu.1)) S_del hS hu.2
        have hsub : insert v (U'j j') ⊆ colClass col4 j' :=
          Finset.insert_subset (by simp [colClass, hcv]) (hU'j_sub_col4 j')
        exact ⟨u₂, hu₂, (walkIn_mono (Finset.sdiff_subset_sdiff hsub le_rfl) hwalk1).trans hwalk2⟩
      · intro j' hcv' S_del hS hvS
        have hj : j' = j := Option.some.inj (hcv'.symm.trans hcv)
        subst hj
        obtain ⟨_, ⟨w, hw, hwalk1⟩⟩ := hUWreach j' S_del hS v (Finset.mem_sdiff.mpr ⟨hvj, hvS⟩)
        rw [Finset.mem_sdiff] at hw
        obtain ⟨u₂, hu₂, hwalk2⟩ := hWj_bwd j' w hw.1 j'
          (by simpa [colClass] using hW'j_sub_col4 j' (hWW'j j' hw.1)) S_del hS hw.2
        have hsub : insert v (W'j j') ⊆ colClass col4 j' :=
          Finset.insert_subset (by simp [colClass, hcv]) (hW'j_sub_col4 j')
        exact ⟨u₂, hu₂, hwalk2.trans (walkIn_mono (Finset.sdiff_subset_sdiff hsub le_rfl) hwalk1)⟩
    intro v
    by_cases hv41 : v ∈ colored col41
    · have h41s := (Finset.mem_filter.mp hv41).2
      exact ⟨fwdSafe_mono hext41_4 h41s (hcol41_safe v).1, bwdSafe_mono hext41_4 h41s (hcol41_safe v).2⟩
    · by_cases hvUW : v ∈ UW'_all
      · rw [Finset.mem_biUnion] at hvUW; obtain ⟨j, _, hvj⟩ := hvUW
        exact hunionJ_safe j v (hUW'j_sub j hvj)
          (hext43b_4 v j (hext43b v j (hext43a v j (hcol42_UW' j v hvj))))
      · by_cases hvZin : v ∈ Z_in
        · exact ⟨hT43b_fwd v (Finset.mem_union_right _ hvZin), hZin_bwd v hvZin⟩
        · by_cases hvZout : v ∈ Z_out
          · exact hZout_safe v hvZout
          · have hnone43b : col43b v = none := by
              have hnc : v ∉ colored col43b := by
                rw [hcol43b_eq, hcol43a_eq, hcol42_colored]
                simp [hv41, hvUW, hvZin, hvZout]
              simp only [colored, Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_ne_none,
                ne_eq, not_not] at hnc; exact hnc
            by_cases hvU : ∃ j : Fin t, v ∈ unionJ j
            · have hcv : col4 v = some hvU.choose := by simp [col4, hnone43b, hvU]
              exact hunionJ_safe hvU.choose v hvU.choose_spec hcv
            · have hnone4 : col4 v = none := by simp [col4, hnone43b, hvU]
              exact ⟨fun j hj => by simp [hnone4] at hj, fun j hj => by simp [hnone4] at hj⟩
  -- For EVERY i : Fin (k*t), there is an i-path P_i from snkB i to srcA i whose internal vertices all have colour `blockOf i` in col4!
  have hall_paths : ∀ i : Fin (k * t), ∃ P : List V,
      IsDirPathBetween G₀.Adj (snkB i) (srcA i) P ∧
      (∀ w ∈ P, col4 w = some (blockOf i)) ∧
      (i ∈ I_short → P.toFinset \ {snkB i, srcA i} = shortInt i) ∧
      (∀ hiL : i ∈ I_long, ∃ a₀ : Fin q,
        P.toFinset \ {snkB i, srcA i} = (intList (eL.symm ⟨i, hiL⟩) a₀).toFinset) := by
    intro i
    by_cases hi : i ∈ I_short
    · refine ⟨P_short i, (hPshort_prop i hi).1, fun w hw => ?_, fun _ => rfl,
        fun hiL => absurd hi (Finset.mem_sdiff.mp hiL).2⟩
      by_cases hws : w = snkB i
      · subst hws
        exact hext04 _ _ (hcol0_AB i _ (Finset.mem_union_right _ (List.mem_toFinset.mpr (List.getLast_mem _))))
      · by_cases hwa : w = srcA i
        · subst hwa
          exact hext04 _ _ (hcol0_AB i _ (Finset.mem_union_left _ (List.mem_toFinset.mpr (List.head_mem _))))
        · exact hext41_4 w _ (hext41 w _ (hext4b w _ (hcol4a_short i hi w
            (Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hw, by simp [hws, hwa]⟩))))
    · have hiL : i ∈ I_long := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩
      let u : Fin rL := eL.symm ⟨i, hiL⟩
      -- Since Z.card < q and the q sets (intList u a).toFinset are pairwise disjoint, some a₀ avoids Z!
      have hex_a0 : ∃ a₀ : Fin q, Disjoint (intList u a₀).toFinset Z := by
        let badA := (Finset.univ : Finset (Fin q)).filter fun a => ¬ Disjoint (intList u a).toFinset Z
        have hbadA_le : badA.card ≤ Z.card := by
          have hex : ∀ a ∈ badA, ∃ z ∈ Z, z ∈ (intList u a).toFinset := by
            intro a ha; have hnd := (Finset.mem_filter.mp ha).2
            rw [Finset.not_disjoint_iff] at hnd; obtain ⟨z, hz1, hz2⟩ := hnd; exact ⟨z, hz2, hz1⟩
          choose pick hpZ hpI using hex
          let pick' : Fin q → V := fun a => if ha : a ∈ badA then pick a ha else x i
          have hinj : Set.InjOn pick' (badA : Set (Fin q)) := by
            intro a₁ ha₁ a₂ ha₂ heq; by_contra hne
            simp only [pick', Finset.mem_coe.mp ha₁, Finset.mem_coe.mp ha₂, ↓reduceDIte] at heq
            exact Finset.disjoint_left.mp (hintList_disj u a₁ u a₂ (by simp [hne]))
              (hpI a₁ (Finset.mem_coe.mp ha₁)) (heq ▸ hpI a₂ (Finset.mem_coe.mp ha₂))
          calc badA.card = (badA.image pick').card := (Finset.card_image_of_injOn hinj).symm
            _ ≤ Z.card := Finset.card_le_card (Finset.image_subset_iff.mpr fun a ha => by
              simpa only [pick', ha, ↓reduceDIte] using hpZ a ha)
        have hrem : (Finset.univ \ badA).Nonempty := Finset.card_pos.mp (by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]; omega)
        obtain ⟨a₀, ha₀⟩ := hrem; rw [Finset.mem_sdiff] at ha₀
        refine ⟨a₀, ?_⟩; by_contra hnd; exact ha₀.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnd⟩)
      obtain ⟨a₀, ha₀_disj⟩ := hex_a0
      have hxu : xL u = snkB i := by simp [xL, u]
      have hyu : yL u = srcA i := by simp [yL, u]
      refine ⟨P_long u a₀, hxu ▸ hyu ▸ hPlong_bet u a₀, fun w hw => ?_, fun h => absurd h hi,
        fun _ => ⟨a₀, by rw [hintList_toF, hxu, hyu]⟩⟩
      by_cases hws : w = snkB i
      · subst hws
        exact hext04 _ _ (hcol0_AB i _ (Finset.mem_union_right _ (List.mem_toFinset.mpr (List.getLast_mem _))))
      · by_cases hwa : w = srcA i
        · subst hwa
          exact hext04 _ _ (hcol0_AB i _ (Finset.mem_union_left _ (List.mem_toFinset.mpr (List.head_mem _))))
        · have hw_int : w ∈ (intList u a₀).toFinset := by
            rw [hintList_toF, hxu, hyu]; exact Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hw, by simp [hws, hwa]⟩
          have hw_uJ : w ∈ unionJ (blockOf i) := by
            refine Finset.mem_biUnion.mpr ⟨(u, a₀), Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, hw_int⟩
            simp [idxJ, u]
          by_cases hw_UW : w ∈ UW'j (blockOf i)
          · exact hext43b_4 w _ (hext43b w _ (hext43a w _ (hcol42_UW' (blockOf i) w hw_UW)))
          · -- w is not in col41, not in UW'_all (disjoint across j!), not in Z_in, not in Z_out -> gets colour blockOf i in final sweep!
            have hw_n41 : w ∉ colored col41 := Finset.disjoint_left.mp (hunionJ_disj_col41 (blockOf i)) hw_uJ
            have hw_nZ : w ∉ Z := Finset.disjoint_left.mp ha₀_disj hw_int
            have hw_nUW' : w ∉ UW'_all := by
              intro h; rw [Finset.mem_biUnion] at h; obtain ⟨j', _, hj'⟩ := h
              by_cases heq : j' = blockOf i
              · exact hw_UW (heq ▸ hj')
              · exact Finset.disjoint_left.mp (hunionJ_disj j' (blockOf i) heq) (hUW'j_sub j' hj') hw_uJ
            have hnone43b : col43b w = none := by
              have hnc : w ∉ colored col43b := by
                rw [hcol43b_eq, hcol43a_eq, hcol42_colored]
                simp only [Z, Finset.mem_union, not_or] at hw_nZ ⊢
                exact ⟨⟨⟨hw_n41, hw_nUW'⟩, hw_nZ.1⟩, hw_nZ.2⟩
              simp only [colored, Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_ne_none,
                ne_eq, not_not] at hnc; exact hnc
            have hex : ∃ j : Fin t, w ∈ unionJ j := ⟨blockOf i, hw_uJ⟩
            simp only [col4, hnone43b, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hex, ↓reduceDIte]
            congr 1
            by_contra hne
            exact Finset.disjoint_left.mp (hunionJ_disj hex.choose (blockOf i) hne) hex.choose_spec hw_uJ
  -- Size of colored col4 ≤ N41 + q + n / 8!
  have hcol4_card : (colored col4).card ≤ N41 + q + n / 8 := by
    have hsub : colored col4 ⊆ colored col41 ∪ Z ∪
        (Finset.univ.biUnion fun p : Fin rL × Fin q => (intList p.1 p.2).toFinset) := by
      intro w hw
      by_cases h41 : w ∈ colored col41
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h41)
      · by_cases hZ : w ∈ Z
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hZ)
        · have hw_union : ∃ j, w ∈ unionJ j := by
            by_contra hno
            have hnone43b : col43b w = none := by
              have hnc : w ∉ colored col43b := by
                rw [hcol43b_eq, hcol43a_eq, hcol42_colored]
                have hnoUW : w ∉ UW'_all := fun h => by
                  rw [Finset.mem_biUnion] at h; obtain ⟨j, _, hj⟩ := h; exact hno ⟨j, hUW'j_sub j hj⟩
                simp only [Z, Finset.mem_union, not_or] at hZ ⊢
                exact ⟨⟨⟨h41, hnoUW⟩, hZ.1⟩, hZ.2⟩
              simp only [colored, Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_ne_none,
                ne_eq, not_not] at hnc; exact hnc
            have hnone4 : col4 w = none := by simp [col4, hnone43b, hno]
            have := (Finset.mem_filter.mp hw).2
            simp [hnone4] at this
          obtain ⟨j, hj⟩ := hw_union
          rw [Finset.mem_biUnion] at hj; obtain ⟨p, _, hp⟩ := hj
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, hp⟩)
    calc (colored col4).card ≤ (colored col41 ∪ Z ∪ (Finset.univ.biUnion fun p : Fin rL × Fin q => (intList p.1 p.2).toFinset)).card :=
          Finset.card_le_card hsub
      _ ≤ (colored col41).card + Z.card + (Finset.univ.biUnion fun p : Fin rL × Fin q => (intList p.1 p.2).toFinset).card := by
          have h1 := Finset.card_union_le (colored col41 ∪ Z) (Finset.univ.biUnion fun p : Fin rL × Fin q => (intList p.1 p.2).toFinset)
          have h2 := Finset.card_union_le (colored col41) Z
          omega
      _ ≤ N41 + q + n / 8 := by omega
  choose P_all hPall_bet hPall_col4 hPall_short hPall_long using hall_paths
  have hPint_disj_D : ∀ i : Fin (k * t), Disjoint ((P_all i).toFinset \ {snkB i, srcA i}) D := by
    intro i
    by_cases hi : i ∈ I_short
    · rw [hPall_short i hi]
      exact Finset.disjoint_of_subset_left
        (Finset.subset_biUnion_of_mem shortInt hi)
        (Finset.disjoint_of_subset_right
          (hcol0_colored ▸ colored_mono hext03)
          hshortAll_disj_col3)
    · have hiL : i ∈ I_long := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩
      obtain ⟨a₀, ha₀⟩ := hPall_long i hiL
      rw [ha₀]
      have hsub_uJ : (intList (eL.symm ⟨i, hiL⟩) a₀).toFinset ⊆ unionJ (blockOf i) := by
        intro w hw
        refine Finset.mem_biUnion.mpr ⟨(eL.symm ⟨i, hiL⟩, a₀), Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, hw⟩
        simp [idxJ]
      exact Finset.disjoint_of_subset_left hsub_uJ
        (Finset.disjoint_of_subset_right
          (hcol0_colored ▸ colored_mono (colExtends_trans hext03 hext3_41))
          (hunionJ_disj_col41 (blockOf i)))
  have hPint_disj_Pint : ∀ i₁ i₂ : Fin (k * t), i₁ ≠ i₂ →
      Disjoint ((P_all i₁).toFinset \ {snkB i₁, srcA i₁}) ((P_all i₂).toFinset \ {snkB i₂, srcA i₂}) := by
    intro i₁ i₂ hne
    have hshort_sub_col41 : ∀ i ∈ I_short, shortInt i ⊆ colored col41 := fun i hi =>
      (Finset.subset_biUnion_of_mem shortInt hi).trans
        ((Finset.subset_union_right.trans hcol4a_colored.symm.subset).trans
          (colored_mono (colExtends_trans hext4b hext41)))
    have hlong_sub_uJ : ∀ (i : Fin (k * t)) (hiL : i ∈ I_long) (a₀ : Fin q),
        (intList (eL.symm ⟨i, hiL⟩) a₀).toFinset ⊆ unionJ (blockOf i) := fun i hiL a₀ w hw =>
      Finset.mem_biUnion.mpr ⟨(eL.symm ⟨i, hiL⟩, a₀), Finset.mem_product.mpr ⟨by simp [idxJ], Finset.mem_univ _⟩, hw⟩
    by_cases h1 : i₁ ∈ I_short
    · rw [hPall_short i₁ h1]
      by_cases h2 : i₂ ∈ I_short
      · rw [hPall_short i₂ h2]
        exact hPshort_disj i₁ h1 i₂ h2 hne
      · have h2L : i₂ ∈ I_long := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h2⟩
        obtain ⟨a₂, ha₂⟩ := hPall_long i₂ h2L
        rw [ha₂]
        exact (Finset.disjoint_of_subset_left (hlong_sub_uJ i₂ h2L a₂)
          (Finset.disjoint_of_subset_right (hshort_sub_col41 i₁ h1)
            (hunionJ_disj_col41 (blockOf i₂)))).symm
    · have h1L : i₁ ∈ I_long := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h1⟩
      obtain ⟨a₁, ha₁⟩ := hPall_long i₁ h1L
      rw [ha₁]
      by_cases h2 : i₂ ∈ I_short
      · rw [hPall_short i₂ h2]
        exact Finset.disjoint_of_subset_left (hlong_sub_uJ i₁ h1L a₁)
          (Finset.disjoint_of_subset_right (hshort_sub_col41 i₂ h2)
            (hunionJ_disj_col41 (blockOf i₁)))
      · have h2L : i₂ ∈ I_long := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h2⟩
        obtain ⟨a₂, ha₂⟩ := hPall_long i₂ h2L
        rw [ha₂]
        refine hintList_disj _ _ _ _ fun heq => hne ?_
        have hfst : eL.symm ⟨i₁, h1L⟩ = eL.symm ⟨i₂, h2L⟩ := congrArg Prod.fst heq
        exact congrArg Subtype.val (eL.symm.injective hfst)
  exact ⟨col4, P_all, fun i v hv => hext04 v _ (hcol0_AB i v hv), hcol4_safe, hcol4_card,
    fun i => ⟨hPall_bet i, hPall_col4 i, hPint_disj_D i⟩, hPint_disj_Pint⟩

/-- Core KOT Claims 1, 2, 5 under the WLOG assumption `|EA| ≤ |EB|`: extends `col4`
from `kot_build_col4` over all of `E` in 3 sweeps and completes the `k`-strong `t`-partition. -/
private theorem kot_partition_wlog {k t : ℕ} (hk : 2 ≤ k) (ht : 2 ≤ t)
    (G₀ : Digraph V) [DecidableRel G₀.Adj] (hT₀ : IsTournament G₀)
    (hstrong₀ : IsKStrongOn G₀ Set.univ (gKOT k t))
    (x y : Fin (k * t) → V)
    (A B : Fin (k * t) → List V) (EA_i EB_i : Fin (k * t) → Finset V)
    (hx_inj : Function.Injective x) (hy_inj : Function.Injective y) (hxy_disj : ∀ i j, x i ≠ y j)
    (hx_min : ∀ i, ∀ u : V, u ∉ Finset.univ.image x ∪ Finset.univ.image y → inDeg G₀ Finset.univ (x i) ≤ inDeg G₀ Finset.univ u)
    (hy_min : ∀ i, ∀ u : V, u ∉ Finset.univ.image x ∪ Finset.univ.image y → outDeg G₀ Finset.univ (y i) ≤ outDeg G₀ Finset.univ u)
    (hA_tr : ∀ i, IsTransitiveList G₀ (A i) ∧ (A i).length ≤ 128 * k * k * t ∧ ∃ h : A i ≠ [], (A i).getLast h = x i)
    (hB_tr : ∀ i, IsTransitiveList G₀ (B i) ∧ (B i).length ≤ 128 * k * k * t ∧ ∃ h : B i ≠ [], (B i).head h = y i)
    (hA_disj : ∀ i j, i ≠ j → Disjoint (A i).toFinset (A j).toFinset)
    (hB_disj : ∀ i j, i ≠ j → Disjoint (B i).toFinset (B j).toFinset)
    (hAB_disj : ∀ i j, Disjoint (A i).toFinset (B j).toFinset)
    (hEA_props : ∀ i, Disjoint (EA_i i) ((Finset.univ.biUnion fun i => (A i).toFinset) ∪ (Finset.univ.biUnion fun i => (B i).toFinset)) ∧ ∀ w ∈ EA_i i, ∀ a ∈ A i, G₀.Adj w a)
    (hEB_props : ∀ i, Disjoint (EB_i i) ((Finset.univ.biUnion fun i => (A i).toFinset) ∪ (Finset.univ.biUnion fun i => (B i).toFinset)) ∧ ∀ w ∈ EB_i i, ∀ b ∈ B i, G₀.Adj b w)
    (hA_dom : ∀ i, ∀ w ∈ Finset.univ \ (((Finset.univ.biUnion fun i => (A i).toFinset) ∪ (Finset.univ.biUnion fun i => (B i).toFinset)) ∪ EA_i i), ∃ a ∈ A i, G₀.Adj a w)
    (hB_dom : ∀ i, ∀ w ∈ Finset.univ \ (((Finset.univ.biUnion fun i => (A i).toFinset) ∪ (Finset.univ.biUnion fun i => (B i).toFinset)) ∪ EB_i i), ∃ b ∈ B i, G₀.Adj w b)
    (hEA_bd : ∀ i, 2 ^ (128 * k * k * t - 1) * (EA_i i).card ≤ inDeg G₀ Finset.univ (x i))
    (hEB_bd : ∀ i, 2 ^ (128 * k * k * t - 1) * (EB_i i).card ≤ outDeg G₀ Finset.univ (y i))
    (hEA_le_EB : (Finset.univ.biUnion EA_i).card ≤ (Finset.univ.biUnion EB_i).card) :
    ∃ part : V → Fin t, ∀ j : Fin t, IsKStrongOn G₀ (part ⁻¹' {j}) k := by
  classical
  let c : ℕ := 128 * k * k * t
  let D_bd : ℕ := 2 * k * t * c
  let N3 : ℕ := (k + 1) ^ 2 * (D_bd + 4 * k * k * t)
  let N41 : ℕ := N3 + (k + 1) ^ 2 * k * k * t
  let q : ℕ := 13 * k ^ 4 * t
  let N43_pre : ℕ := N41 + 2 * q * k * t * (k + 1) + q
  let g : ℕ := gKOT k t
  have hg_eq : g = 10 * (N43_pre + 600 * (k * t * q * 8) + 10 * k * t + 10) := rfl
  have hkt_pos : 1 ≤ k * t := Nat.mul_pos (by omega) (by omega)
  have hc_ge : 128 * k * k * t ≤ 2 ^ (c - 1) := by
    have h1 := two_pow_ge_succ (c - 1)
    have hc_pos : 1 ≤ c := by
      dsimp only [c]
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega)
    omega
  let n : ℕ := Fintype.card V
  let D : Finset V := (Finset.univ.biUnion fun i => (A i).toFinset) ∪ (Finset.univ.biUnion fun i => (B i).toFinset)
  let EA : Finset V := Finset.univ.biUnion EA_i
  let EB : Finset V := Finset.univ.biUnion EB_i
  let E : Finset V := EA ∪ EB
  let XY : Finset V := Finset.univ.image x ∪ Finset.univ.image y
  have hU₀ : IsKStrongOn G₀ ((Finset.univ : Finset V) : Set V) g := by simpa using hstrong₀
  have hdeg₀_out : ∀ v : V, g ≤ outDeg G₀ Finset.univ v := fun v =>
    min_outDeg_of_isKStrongOn hT₀ hU₀ (Finset.mem_univ v)
  have hdeg₀_in : ∀ v : V, g ≤ inDeg G₀ Finset.univ v := fun v =>
    min_inDeg_of_isKStrongOn hT₀ hU₀ (Finset.mem_univ v)
  have hn_ge : 2 * g + 1 ≤ n := by
    have hgt : g < n := by simpa [n, Set.ncard_coe_finset] using hU₀.1
    obtain ⟨v, _⟩ := Finset.card_pos.mp (by rw [Finset.card_univ]; change 0 < n; omega : 0 < (Finset.univ : Finset V).card)
    have h1 := hdeg₀_out v; have h2 := hdeg₀_in v
    have h3 := outDeg_add_inDeg_eq hT₀ (Finset.mem_univ v)
    simp only [Finset.card_univ] at h3; omega
  have hEA_deg_bd : ∀ u : V, u ∉ XY → 128 * k * EA.card ≤ inDeg G₀ Finset.univ u := by
    intro u hu
    have hsum : ∑ i : Fin (k * t), (EA_i i).card * (2 ^ (c - 1)) ≤ ∑ _i : Fin (k * t), inDeg G₀ Finset.univ u :=
      Finset.sum_le_sum fun i _ => by rw [Nat.mul_comm]; exact (hEA_bd i).trans (hx_min i u hu)
    rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    have hcomb : EA.card * (128 * k * k * t) ≤ (k * t) * inDeg G₀ Finset.univ u :=
      (Nat.mul_le_mul Finset.card_biUnion_le hc_ge).trans hsum
    have hrew : EA.card * (128 * k * k * t) = (k * t) * (128 * k * EA.card) := by ring
    rw [hrew] at hcomb; exact Nat.le_of_mul_le_mul_left hcomb hkt_pos
  have hEB_deg_bd : ∀ u : V, u ∉ XY → 128 * k * EB.card ≤ outDeg G₀ Finset.univ u := by
    intro u hu
    have hsum : ∑ i : Fin (k * t), (EB_i i).card * (2 ^ (c - 1)) ≤ ∑ _i : Fin (k * t), outDeg G₀ Finset.univ u :=
      Finset.sum_le_sum fun i _ => by rw [Nat.mul_comm]; exact (hEB_bd i).trans (hy_min i u hu)
    rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    have hcomb : EB.card * (128 * k * k * t) ≤ (k * t) * outDeg G₀ Finset.univ u :=
      (Nat.mul_le_mul Finset.card_biUnion_le hc_ge).trans hsum
    have hrew : EB.card * (128 * k * k * t) = (k * t) * (128 * k * EB.card) := by ring
    rw [hrew] at hcomb; exact Nat.le_of_mul_le_mul_left hcomb hkt_pos
  have hE_deg_bd : ∀ u : V, u ∉ XY → 64 * k * E.card ≤ outDeg G₀ Finset.univ u := by
    intro u hu
    have h1 : E.card ≤ EA.card + EB.card := Finset.card_union_le EA EB
    change EA.card ≤ EB.card at hEA_le_EB
    have h1' : E.card ≤ 2 * EB.card := by omega
    calc 64 * k * E.card ≤ 64 * k * (2 * EB.card) := Nat.mul_le_mul_left _ h1'
      _ = 128 * k * EB.card := by ring
      _ ≤ outDeg G₀ Finset.univ u := hEB_deg_bd u hu
  have hE_le_n : 64 * k * E.card ≤ n := by
    have hXY_card : XY.card ≤ 2 * k * t := by
      calc XY.card ≤ (Finset.univ.image x).card + (Finset.univ.image y).card := Finset.card_union_le _ _
        _ ≤ k * t + k * t := Nat.add_le_add (Finset.card_image_le.trans (by simp)) (Finset.card_image_le.trans (by simp))
        _ = 2 * k * t := by ring
    have h2kt_le_g : 2 * k * t ≤ g := by
      rw [hg_eq]
      have : 2 * k * t ≤ 10 * k * t := by
        calc 2 * k * t = 2 * (k * t) := by ring
          _ ≤ 10 * (k * t) := Nat.mul_le_mul_right _ (by omega)
          _ = 10 * k * t := by ring
      omega
    have hrem : (Finset.univ \ XY).Nonempty := Finset.card_pos.mp (by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]; change 0 < n - XY.card; omega)
    obtain ⟨u, hu⟩ := hrem
    have h1 := hE_deg_bd u (Finset.mem_sdiff.mp hu).2
    have h2 : outDeg G₀ Finset.univ u ≤ n := Finset.card_le_univ _
    omega
  have hEA_gap : ∀ u : V, u ∉ XY → 2 * (N43_pre + 10 * k * t + 10) + EA.card ≤ inDeg G₀ Finset.univ u := by
    intro u hu
    have h1 : 2 * EA.card ≤ inDeg G₀ Finset.univ u :=
      (Nat.mul_le_mul_right EA.card (by omega : 2 ≤ 128 * k)).trans (hEA_deg_bd u hu)
    have h2 := hdeg₀_in u; omega
  have hE_gap : ∀ u : V, u ∉ XY → 2 * (N43_pre + 10 * k * t + 10) + E.card ≤ outDeg G₀ Finset.univ u := by
    intro u hu
    have h1 : 2 * E.card ≤ outDeg G₀ Finset.univ u :=
      (Nat.mul_le_mul_right E.card (by omega : 2 ≤ 64 * k)).trans (hE_deg_bd u hu)
    have h2 := hdeg₀_out u; omega
  let blockOf : Fin (k * t) → Fin t := fun i => ⟨i.val / k, Nat.div_lt_of_lt_mul i.isLt⟩
  let idxOf : Fin t → Fin k → Fin (k * t) := fun j a => ⟨j.val * k + a.val, by
    calc j.val * k + a.val < j.val * k + k := Nat.add_lt_add_left a.isLt _
      _ = (j.val + 1) * k := by ring
      _ ≤ t * k := Nat.mul_le_mul_right k j.isLt
      _ = k * t := by ring⟩
  have hblock_idx : ∀ j a, blockOf (idxOf j a) = j := fun j a => by
    ext; dsimp [blockOf, idxOf]
    rw [Nat.mul_comm j.val k, Nat.mul_add_div (by omega), Nat.div_eq_of_lt a.isLt, Nat.add_zero]
  have hidx_inj : ∀ j, Function.Injective (idxOf j) := fun j a₁ a₂ h => by
    have := congrArg Fin.val h; dsimp [idxOf] at this; exact Fin.ext (by omega)
  have hXY_sub_D : XY ⊆ D := by
    intro w hw; rcases Finset.mem_union.mp hw with h | h <;> rw [Finset.mem_image] at h
    · obtain ⟨i, _, rfl⟩ := h; obtain ⟨hne, hl⟩ := (hA_tr i).2.2
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, List.mem_toFinset.mpr (hl ▸ List.getLast_mem hne)⟩)
    · obtain ⟨i, _, rfl⟩ := h; obtain ⟨hne, hh⟩ := (hB_tr i).2.2
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, List.mem_toFinset.mpr (hh ▸ List.head_mem hne)⟩)
  let col0 : V → Option (Fin t) := fun v =>
    if h : ∃ i : Fin (k * t), v ∈ (A i).toFinset ∪ (B i).toFinset then some (blockOf h.choose) else none
  have hcol0_AB : ∀ i v, v ∈ (A i).toFinset ∪ (B i).toFinset → col0 v = some (blockOf i) := by
    intro i v hv
    have hex : ∃ i' : Fin (k * t), v ∈ (A i').toFinset ∪ (B i').toFinset := ⟨i, hv⟩
    simp only [col0, hex, ↓reduceDIte]; congr 1
    have hch := hex.choose_spec
    have heq : hex.choose = i := by
      by_contra hne
      rcases Finset.mem_union.mp hch with h1 | h1 <;> rcases Finset.mem_union.mp hv with h2 | h2
      · exact Finset.disjoint_left.mp (hA_disj _ _ hne) h1 h2
      · exact Finset.disjoint_left.mp (hAB_disj _ _) h1 h2
      · exact Finset.disjoint_left.mp (hAB_disj _ _) h2 h1
      · exact Finset.disjoint_left.mp (hB_disj _ _ hne) h1 h2
    rw [heq]
  have hcol0_colored : colored col0 = D := by
    ext v; simp only [colored, col0, D, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_biUnion]
    split_ifs with h
    · simp only [Option.isSome_some, true_iff]; obtain ⟨i, ha | hb⟩ := h
      · exact Or.inl ⟨i, ha⟩
      · exact Or.inr ⟨i, hb⟩
    · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
      rintro (⟨i, ha⟩ | ⟨i, hb⟩)
      · exact h ⟨i, Or.inl ha⟩
      · exact h ⟨i, Or.inr hb⟩
  let srcA : Fin (k * t) → V := fun i => (A i).head (hA_tr i).1.1
  let snkB : Fin (k * t) → V := fun i => (B i).getLast (hB_tr i).1.1
  have hsrcA_inj : Function.Injective srcA := by
    intro i₁ i₂ heq; by_contra hne
    have h1 : srcA i₁ ∈ (A i₁).toFinset := List.mem_toFinset.mpr (List.head_mem _)
    have h2 : srcA i₂ ∈ (A i₂).toFinset := List.mem_toFinset.mpr (List.head_mem _)
    exact Finset.disjoint_left.mp (hA_disj i₁ i₂ hne) h1 (heq ▸ h2)
  obtain ⟨col4, P_all, hcol4_AB, hcol4_safe, hcol4_card, hPall_props, hPint_disj_Pint⟩ :=
    kot_build_col4 hk ht G₀ hT₀ hstrong₀ x y A B EA_i EB_i hx_inj hy_inj hxy_disj
      hx_min hy_min hA_tr hB_tr hA_disj hB_disj hAB_disj hEA_props hEB_props hA_dom hB_dom
      hEA_bd hEB_bd hEA_le_EB
  have hPall_bet : ∀ i, IsDirPathBetween G₀.Adj (snkB i) (srcA i) (P_all i) := fun i => (hPall_props i).1
  have hPall_col4 : ∀ i, ∀ w ∈ P_all i, col4 w = some (blockOf i) := fun i => (hPall_props i).2.1
  have hPint_disj_D : ∀ i, Disjoint ((P_all i).toFinset \ {snkB i, srcA i}) D := fun i => (hPall_props i).2.2
  have hext04 : ColExtends col0 col4 := by
    intro v j hcv; dsimp only [col0] at hcv
    by_cases h : ∃ i, v ∈ (A i).toFinset ∪ (B i).toFinset
    · simp only [h, ↓reduceDIte, Option.some.injEq] at hcv
      rw [← hcv]; exact hcol4_AB h.choose v h.choose_spec
    · simp only [h, ↓reduceDIte, reduceCtorEq] at hcv
  -- CLAIM 5: Colour all remaining uncoloured vertices of E in 3 sweeps (Case 1, Case 2, Case 3) while maintaining AllSafe!
  let cntA : V → Fin t → ℕ := fun v j => ((Finset.univ : Finset (Fin k)).filter fun a => v ∈ EA_i (idxOf j a)).card
  let cntB : V → Fin t → ℕ := fun v j => ((Finset.univ : Finset (Fin k)).filter fun a => v ∈ EB_i (idxOf j a)).card
  -- Crucial KOT helper: for any v ∉ D and any colouring col extending col0 with AllSafe,
  -- if col v = some j and cntA v j ≤ cntB v j, then v is BwdSafe!
  -- Symmetrically, if col v = some j and cntB v j ≤ cntA v j, then v is FwdSafe!
  have hbwd_of_cnt : ∀ (col : V → Option (Fin t)), ColExtends col0 col →
      (∀ d ∈ D, BwdSafe G₀ k D EA col d) →
      ∀ v j, v ∉ D → col v = some j → cntA v j ≤ cntB v j → BwdSafe G₀ k D EA col v := by
    intro col hext hDsafe v j hvD hcv hcnt
    -- For each a with v ∉ EA_i (idxOf j a), pick wA a ∈ A (idxOf j a) with G₀.Adj (wA a) v
    -- For each a with v ∈ EB_i (idxOf j a), pick wB a = head(B (idxOf j a)) ∈ B (idxOf j a) with G₀.Adj (wB a) v
    let SA : Finset (Fin k) := Finset.univ.filter fun a => v ∉ EA_i (idxOf j a)
    let SB : Finset (Fin k) := Finset.univ.filter fun a => v ∈ EB_i (idxOf j a)
    have hex_wA : ∀ a : Fin k, a ∈ SA → ∃ w ∈ (A (idxOf j a)).toFinset, G₀.Adj w v := fun a ha => by
      have hnEA := (Finset.mem_filter.mp ha).2
      have hv_n : v ∉ D ∪ EA_i (idxOf j a) := by simp only [Finset.mem_union, not_or]; exact ⟨hvD, hnEA⟩
      obtain ⟨w, hwA, hwv⟩ := hA_dom (idxOf j a) v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv_n⟩)
      exact ⟨w, List.mem_toFinset.mpr hwA, hwv⟩
    choose wA hwA_mem hwA_adj using hex_wA
    let pickA : Fin k → V := fun a => if ha : a ∈ SA then wA a ha else x (idxOf j a)
    let pickB : Fin k → V := fun a => (B (idxOf j a)).head (hB_tr (idxOf j a)).1.1
    let WA : Finset V := SA.image pickA
    let WB : Finset V := SB.image pickB
    have hWA_card : WA.card = SA.card := by
      apply Finset.card_image_of_injOn
      intro a₁ ha₁ a₂ ha₂ heq; by_contra hne
      simp only [pickA, Finset.mem_coe.mp ha₁, Finset.mem_coe.mp ha₂, ↓reduceDIte] at heq
      exact Finset.disjoint_left.mp (hA_disj _ _ (fun h => hne (hidx_inj j h)))
        (hwA_mem a₁ (Finset.mem_coe.mp ha₁)) (heq ▸ hwA_mem a₂ (Finset.mem_coe.mp ha₂))
    have hWB_card : WB.card = SB.card := by
      apply Finset.card_image_of_injOn
      intro a₁ _ a₂ _ heq; by_contra hne
      have h1 : pickB a₁ ∈ (B (idxOf j a₁)).toFinset := List.mem_toFinset.mpr (List.head_mem _)
      have h2 : pickB a₂ ∈ (B (idxOf j a₂)).toFinset := List.mem_toFinset.mpr (List.head_mem _)
      exact Finset.disjoint_left.mp (hB_disj _ _ (fun h => hne (hidx_inj j h))) h1 (heq ▸ h2)
    have hWAB_disj : Disjoint WA WB := by
      rw [Finset.disjoint_left]; intro w h1 h2
      rw [Finset.mem_image] at h1 h2
      obtain ⟨a₁, ha₁, rfl⟩ := h1; obtain ⟨a₂, _, h2'⟩ := h2
      simp only [pickA, ha₁, ↓reduceDIte] at h2'
      have h2B : pickB a₂ ∈ (B (idxOf j a₂)).toFinset := List.mem_toFinset.mpr (List.head_mem _)
      exact Finset.disjoint_left.mp (hAB_disj (idxOf j a₁) (idxOf j a₂))
        (hwA_mem a₁ ha₁) (h2' ▸ h2B)
    have hSA_card : SA.card + cntA v j = k := by
      have hdisj : Disjoint SA ((Finset.univ : Finset (Fin k)).filter fun a => v ∈ EA_i (idxOf j a)) := by
        rw [Finset.disjoint_left]; intro a ha1 ha2
        exact (Finset.mem_filter.mp ha1).2 (Finset.mem_filter.mp ha2).2
      have hunion : SA ∪ ((Finset.univ : Finset (Fin k)).filter fun a => v ∈ EA_i (idxOf j a)) = Finset.univ := by
        ext a; simp only [SA, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        exact iff_true_intro (em' _)
      have h := Finset.card_union_of_disjoint hdisj
      rw [hunion, Finset.card_univ, Fintype.card_fin] at h
      exact h.symm
    have hW_card : k ≤ (WA ∪ WB).card := by
      rw [Finset.card_union_of_disjoint hWAB_disj, hWA_card, hWB_card]; change k ≤ SA.card + cntB v j; omega
    apply bwdSafe_of_k_inNbrs hcv hW_card
    intro w hw; rcases Finset.mem_union.mp hw with h1 | h2
    · rw [Finset.mem_image] at h1; obtain ⟨a, ha, rfl⟩ := h1
      simp only [pickA, ha, ↓reduceDIte]
      have hwA := hwA_mem a ha
      have hwD : wA a ha ∈ D := Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨idxOf j a, Finset.mem_univ _, hwA⟩)
      have hc0 := hcol0_AB (idxOf j a) (wA a ha) (Finset.mem_union_left _ hwA)
      rw [hblock_idx j a] at hc0
      exact ⟨hext _ j hc0, hwA_adj a ha, hDsafe _ hwD⟩
    · rw [Finset.mem_image] at h2; obtain ⟨a, ha, rfl⟩ := h2
      have hwB : pickB a ∈ (B (idxOf j a)).toFinset := List.mem_toFinset.mpr (List.head_mem _)
      have hwD : pickB a ∈ D := Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨idxOf j a, Finset.mem_univ _, hwB⟩)
      have hc0 := hcol0_AB (idxOf j a) (pickB a) (Finset.mem_union_right _ hwB)
      rw [hblock_idx j a] at hc0
      have hadj := (hEB_props (idxOf j a)).2 v (Finset.mem_filter.mp ha).2 (pickB a) (List.head_mem _)
      exact ⟨hext _ j hc0, hadj, hDsafe _ hwD⟩
  have hfwd_of_cnt : ∀ (col : V → Option (Fin t)), ColExtends col0 col →
      (∀ d ∈ D, FwdSafe G₀ k D EB col d) →
      ∀ v j, v ∉ D → col v = some j → cntB v j ≤ cntA v j → FwdSafe G₀ k D EB col v := by
    intro col hext hDsafe v j hvD hcv hcnt
    let SB : Finset (Fin k) := Finset.univ.filter fun a => v ∉ EB_i (idxOf j a)
    let SA : Finset (Fin k) := Finset.univ.filter fun a => v ∈ EA_i (idxOf j a)
    have hex_wB : ∀ a : Fin k, a ∈ SB → ∃ w ∈ (B (idxOf j a)).toFinset, G₀.Adj v w := fun a ha => by
      have hnEB := (Finset.mem_filter.mp ha).2
      have hv_n : v ∉ D ∪ EB_i (idxOf j a) := by simp only [Finset.mem_union, not_or]; exact ⟨hvD, hnEB⟩
      obtain ⟨w, hwB, hvw⟩ := hB_dom (idxOf j a) v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv_n⟩)
      exact ⟨w, List.mem_toFinset.mpr hwB, hvw⟩
    choose wB hwB_mem hwB_adj using hex_wB
    let pickB : Fin k → V := fun a => if ha : a ∈ SB then wB a ha else y (idxOf j a)
    let pickA : Fin k → V := fun a => (A (idxOf j a)).head (hA_tr (idxOf j a)).1.1
    let WB : Finset V := SB.image pickB
    let WA : Finset V := SA.image pickA
    have hWB_card : WB.card = SB.card := by
      apply Finset.card_image_of_injOn
      intro a₁ ha₁ a₂ ha₂ heq; by_contra hne
      simp only [pickB, Finset.mem_coe.mp ha₁, Finset.mem_coe.mp ha₂, ↓reduceDIte] at heq
      exact Finset.disjoint_left.mp (hB_disj _ _ (fun h => hne (hidx_inj j h)))
        (hwB_mem a₁ (Finset.mem_coe.mp ha₁)) (heq ▸ hwB_mem a₂ (Finset.mem_coe.mp ha₂))
    have hWA_card : WA.card = SA.card := by
      apply Finset.card_image_of_injOn
      intro a₁ _ a₂ _ heq; by_contra hne
      have h1 : pickA a₁ ∈ (A (idxOf j a₁)).toFinset := List.mem_toFinset.mpr (List.head_mem _)
      have h2 : pickA a₂ ∈ (A (idxOf j a₂)).toFinset := List.mem_toFinset.mpr (List.head_mem _)
      exact Finset.disjoint_left.mp (hA_disj _ _ (fun h => hne (hidx_inj j h))) h1 (heq ▸ h2)
    have hWBA_disj : Disjoint WB WA := by
      rw [Finset.disjoint_left]; intro w h1 h2
      rw [Finset.mem_image] at h1 h2
      obtain ⟨a₁, ha₁, rfl⟩ := h1; obtain ⟨a₂, _, h2'⟩ := h2
      simp only [pickB, ha₁, ↓reduceDIte] at h2'
      have h2A : pickA a₂ ∈ (A (idxOf j a₂)).toFinset := List.mem_toFinset.mpr (List.head_mem _)
      exact Finset.disjoint_left.mp (hAB_disj (idxOf j a₂) (idxOf j a₁))
        (h2' ▸ h2A) (hwB_mem a₁ ha₁)
    have hSB_card : SB.card + cntB v j = k := by
      have hdisj : Disjoint SB ((Finset.univ : Finset (Fin k)).filter fun a => v ∈ EB_i (idxOf j a)) := by
        rw [Finset.disjoint_left]; intro a ha1 ha2
        exact (Finset.mem_filter.mp ha1).2 (Finset.mem_filter.mp ha2).2
      have hunion : SB ∪ ((Finset.univ : Finset (Fin k)).filter fun a => v ∈ EB_i (idxOf j a)) = Finset.univ := by
        ext a; simp only [SB, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        exact iff_true_intro (em' _)
      have h := Finset.card_union_of_disjoint hdisj
      rw [hunion, Finset.card_univ, Fintype.card_fin] at h
      exact h.symm
    have hW_card : k ≤ (WB ∪ WA).card := by
      rw [Finset.card_union_of_disjoint hWBA_disj, hWB_card, hWA_card]; change k ≤ SB.card + cntA v j; omega
    apply fwdSafe_of_k_outNbrs hcv hW_card
    intro w hw; rcases Finset.mem_union.mp hw with h1 | h2
    · rw [Finset.mem_image] at h1; obtain ⟨a, ha, rfl⟩ := h1
      simp only [pickB, ha, ↓reduceDIte]
      have hwB := hwB_mem a ha
      have hwD : wB a ha ∈ D := Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨idxOf j a, Finset.mem_univ _, hwB⟩)
      have hc0 := hcol0_AB (idxOf j a) (wB a ha) (Finset.mem_union_right _ hwB)
      rw [hblock_idx j a] at hc0
      exact ⟨hext _ j hc0, hwB_adj a ha, hDsafe _ hwD⟩
    · rw [Finset.mem_image] at h2; obtain ⟨a, ha, rfl⟩ := h2
      have hwA : pickA a ∈ (A (idxOf j a)).toFinset := List.mem_toFinset.mpr (List.head_mem _)
      have hwD : pickA a ∈ D := Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨idxOf j a, Finset.mem_univ _, hwA⟩)
      have hc0 := hcol0_AB (idxOf j a) (pickA a) (Finset.mem_union_left _ hwA)
      rw [hblock_idx j a] at hc0
      have hadj := (hEA_props (idxOf j a)).2 v (Finset.mem_filter.mp ha).2 (pickA a) (List.head_mem _)
      exact ⟨hext _ j hc0, hadj, hDsafe _ hwD⟩
  -- Sweep 1 (Case 1): E₁ = {v ∈ E | (∃ j₁, cntA v j₁ ≤ cntB v j₁) ∧ (∃ j₂, cntB v j₂ ≤ cntA v j₂)}
  let E1 : Finset V := E.filter fun v => (∃ j₁ : Fin t, cntA v j₁ ≤ cntB v j₁) ∧ (∃ j₂ : Fin t, cntB v j₂ ≤ cntA v j₂)
  let E2 : Finset V := E.filter fun v => ∀ j : Fin t, cntA v j < cntB v j
  let E3 : Finset V := E.filter fun v => ∀ j : Fin t, cntB v j < cntA v j
  have hE_cover : E = E1 ∪ E2 ∪ E3 := by
    ext v; simp only [E1, E2, E3, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hv
      by_cases h1 : ∃ j₁ : Fin t, cntA v j₁ ≤ cntB v j₁
      · by_cases h2 : ∃ j₂ : Fin t, cntB v j₂ ≤ cntA v j₂
        · exact Or.inl (Or.inl ⟨hv, h1, h2⟩)
        · push Not at h2; exact Or.inl (Or.inr ⟨hv, h2⟩)
      · push Not at h1; exact Or.inr ⟨hv, h1⟩
    · rintro ((⟨hv, _⟩ | ⟨hv, _⟩) | ⟨hv, _⟩) <;> exact hv
  -- Inductively colour any subset S ⊆ E1 (Case 1), tracking |colored| ≤ |colored col4| + (k + 1) * |S|!
  have hsweep1 : ∀ S : Finset V, S ⊆ E1 →
      ∃ col : V → Option (Fin t), ColExtends col4 col ∧ AllSafe G₀ k D EA EB col ∧
        S ⊆ colored col ∧ (colored col).card ≤ (colored col4).card + (k + 1) * S.card := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; exact ⟨col4, colExtends_refl col4, hcol4_safe, Finset.empty_subset _, by simp⟩
    | @insert v₀ T hv₀_nT ih =>
      intro hsub
      obtain ⟨col, hext, hsafe, hTcol, hcard⟩ := ih ((Finset.subset_insert _ _).trans hsub)
      by_cases hv₀_col : v₀ ∈ colored col
      · refine ⟨col, hext, hsafe, Finset.insert_subset hv₀_col hTcol, ?_⟩
        rw [Finset.card_insert_of_notMem hv₀_nT]
        have : (k + 1) * T.card ≤ (k + 1) * (T.card + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
        omega
      · have hv₀_E1 := hsub (Finset.mem_insert_self v₀ T)
        obtain ⟨hv₀_E, ⟨j₁, hj1⟩, ⟨j₂, hj2⟩⟩ := Finset.mem_filter.mp hv₀_E1
        have hv₀_none : col v₀ = none := by
          simp only [colored, Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_ne_none,
            ne_eq, not_not] at hv₀_col; exact hv₀_col
        have hv₀_nD : v₀ ∉ D := fun h => hv₀_col (colored_mono (colExtends_trans hext04 hext) (hcol0_colored ▸ h))
        -- Count uncoloured vertices outside E: at least n - |colored col| - |E| ≥ 2 * k!
        let avail : Finset V := Finset.univ \ (colored col ∪ E)
        have havail_ge : 2 * k ≤ avail.card := by
          have hT_le : T.card ≤ E.card := Finset.card_le_card
            ((Finset.subset_insert v₀ T).trans (hsub.trans (Finset.filter_subset _ _)))
          have hT_mul : (k + 1) * T.card ≤ (k + 1) * E.card := Nat.mul_le_mul_left _ hT_le
          have hcol4_le' : (colored col4).card ≤ N41 + q + n / 8 := hcol4_card
          have hcol_le : (colored col).card ≤ N41 + q + n / 8 + (k + 1) * E.card := by omega
          have hsd := Finset.card_sdiff_add_card_inter (Finset.univ : Finset V) (colored col ∪ E)
          rw [Finset.inter_eq_right.mpr (Finset.subset_univ _), Finset.card_univ] at hsd
          change avail.card + (colored col ∪ E).card = n at hsd
          have hun := Finset.card_union_le (colored col) E
          have h2k_le : 2 * k ≤ 10 * k * t := by
            calc 2 * k ≤ 10 * k := by omega
              _ ≤ 10 * k * t := Nat.le_mul_of_pos_right _ (by omega)
          have h1 : 8 * (N41 + q + 2 * k) ≤ n := by
            have : N41 + q + 2 * k ≤ N43_pre + 10 * k * t + 10 := by dsimp only [N43_pre]; omega
            omega
          have h2a : (k + 1) * E.card + E.card = (k + 2) * E.card := by ring
          have h2 : (k + 2) * E.card ≤ 2 * k * E.card := Nat.mul_le_mul_right _ (by omega)
          have h3 : 32 * (2 * k * E.card) = 64 * k * E.card := by ring
          omega
        -- Partition avail into out-nbrs and in-nbrs of v₀ (v₀ ∉ avail since v₀ ∈ E!)
        have hv₀_navail : v₀ ∉ avail := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_union_right _ hv₀_E)
        have hsplit : avail.card = (outNbr G₀ avail v₀).card + (inNbr G₀ avail v₀).card := by
          have hsum := outDeg_add_inDeg_eq hT₀ (S := insert v₀ avail) (Finset.mem_insert_self _ _)
          have h1 : outNbr G₀ (insert v₀ avail) v₀ = outNbr G₀ avail v₀ := by
            ext w; simp only [outNbr, Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hw, hadj⟩
              · exact absurd hadj (hT₀.1 _)
              · exact ⟨hw, hadj⟩
            · rintro ⟨hw, hadj⟩; exact ⟨Or.inr hw, hadj⟩
          have h2 : inNbr G₀ (insert v₀ avail) v₀ = inNbr G₀ avail v₀ := by
            ext w; simp only [inNbr, Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hw, hadj⟩
              · exact absurd hadj (hT₀.1 _)
              · exact ⟨hw, hadj⟩
            · rintro ⟨hw, hadj⟩; exact ⟨Or.inr hw, hadj⟩
          rw [Finset.card_insert_of_notMem hv₀_navail] at hsum
          change (outNbr G₀ (insert v₀ avail) v₀).card + (inNbr G₀ (insert v₀ avail) v₀).card + 1 = avail.card + 1 at hsum
          rw [h1, h2] at hsum; omega
        have hext0 : ColExtends col0 col := colExtends_trans hext04 hext
        by_cases hout : k ≤ (outNbr G₀ avail v₀).card
        · -- Case 1.1: colour v₀ and k out-nbrs in avail with j₁!
          obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hout
          let col' := paintSet col (insert v₀ W) j₁
          have hext' : ColExtends col col' := paintSet_extends col (insert v₀ W) j₁
          have hW_ncol : ∀ w ∈ W, col w = none := fun w hw => by
            have hnc : w ∉ colored col := fun h => (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hWsub hw)).1).2 (Finset.mem_union_left _ h)
            simp only [colored, Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_ne_none,
              ne_eq, not_not] at hnc; exact hnc
          have hW_safe : ∀ w ∈ W, FwdSafe G₀ k D EB col' w ∧ BwdSafe G₀ k D EA col' w := fun w hw => by
            have hwa := (Finset.mem_filter.mp (hWsub hw)).1
            have hwnD : w ∉ D := fun h => (Finset.mem_sdiff.mp hwa).2 (Finset.mem_union_left _ (colored_mono hext0 (hcol0_colored ▸ h)))
            have hwnE : w ∉ E := fun h => (Finset.mem_sdiff.mp hwa).2 (Finset.mem_union_right _ h)
            have hwnEA : w ∉ EA := fun h => hwnE (Finset.mem_union_left _ h)
            have hwnEB : w ∉ EB := fun h => hwnE (Finset.mem_union_right _ h)
            exact ⟨fwdSafe_of_not_mem (by simp only [Finset.mem_union, not_or]; exact ⟨hwnD, hwnEB⟩),
              bwdSafe_of_not_mem (by simp only [Finset.mem_union, not_or]; exact ⟨hwnD, hwnEA⟩)⟩
          have hv₀_col' : col' v₀ = some j₁ := by simp [col', paintSet, hv₀_none]
          have hv₀_fwd : FwdSafe G₀ k D EB col' v₀ :=
            fwdSafe_of_k_outNbrs hv₀_col' hWcard.ge fun w hw =>
              ⟨by simp [col', paintSet, hw, hW_ncol w hw], (Finset.mem_filter.mp (hWsub hw)).2, (hW_safe w hw).1⟩
          have hv₀_bwd : BwdSafe G₀ k D EA col' v₀ :=
            hbwd_of_cnt col' (colExtends_trans hext0 hext')
              (fun d hd => bwdSafe_mono hext' (Finset.mem_filter.mp (colored_mono hext0 (hcol0_colored ▸ hd))).2 (hsafe d).2)
              v₀ j₁ hv₀_nD hv₀_col' hj1
          refine ⟨col', colExtends_trans hext hext', ?_, ?_, ?_⟩
          · intro w
            by_cases hwc : w ∈ colored col
            · have hws := (Finset.mem_filter.mp hwc).2
              exact ⟨fwdSafe_mono hext' hws (hsafe w).1, bwdSafe_mono hext' hws (hsafe w).2⟩
            · by_cases hw0 : w = v₀
              · subst hw0; exact ⟨hv₀_fwd, hv₀_bwd⟩
              · by_cases hwW : w ∈ W
                · exact hW_safe w hwW
                · have hnone : col' w = none := by
                    have hnc : col w = none := by
                      simp only [colored, Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_ne_none,
                        ne_eq, not_not] at hwc; exact hwc
                    simp [col', paintSet, hw0, hwW, hnc]
                  exact ⟨fun j hj => by simp [hnone] at hj, fun j hj => by simp [hnone] at hj⟩
          · refine Finset.insert_subset (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hv₀_col']⟩)
              (hTcol.trans (colored_mono hext'))
          · rw [Finset.card_insert_of_notMem hv₀_nT]
            have hsub' := paintSet_colored_sub col (insert v₀ W) j₁
            have h1 := Finset.card_le_card hsub'
            change (colored col').card ≤ _ at h1
            have h2 := Finset.card_union_le (colored col) (insert v₀ W)
            have h3 := Finset.card_insert_le v₀ W
            have hstep : (k + 1) * (T.card + 1) = (k + 1) * T.card + (k + 1) := by ring
            omega
        · -- Case 1.2: colour v₀ and k in-nbrs in avail with j₂!
          have hin : k ≤ (inNbr G₀ avail v₀).card := by omega
          obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hin
          let col' := paintSet col (insert v₀ W) j₂
          have hext' : ColExtends col col' := paintSet_extends col (insert v₀ W) j₂
          have hW_ncol : ∀ w ∈ W, col w = none := fun w hw => by
            have hnc : w ∉ colored col := fun h => (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hWsub hw)).1).2 (Finset.mem_union_left _ h)
            simp only [colored, Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_ne_none,
              ne_eq, not_not] at hnc; exact hnc
          have hW_safe : ∀ w ∈ W, FwdSafe G₀ k D EB col' w ∧ BwdSafe G₀ k D EA col' w := fun w hw => by
            have hwa := (Finset.mem_filter.mp (hWsub hw)).1
            have hwnD : w ∉ D := fun h => (Finset.mem_sdiff.mp hwa).2 (Finset.mem_union_left _ (colored_mono hext0 (hcol0_colored ▸ h)))
            have hwnE : w ∉ E := fun h => (Finset.mem_sdiff.mp hwa).2 (Finset.mem_union_right _ h)
            have hwnEA : w ∉ EA := fun h => hwnE (Finset.mem_union_left _ h)
            have hwnEB : w ∉ EB := fun h => hwnE (Finset.mem_union_right _ h)
            exact ⟨fwdSafe_of_not_mem (by simp only [Finset.mem_union, not_or]; exact ⟨hwnD, hwnEB⟩),
              bwdSafe_of_not_mem (by simp only [Finset.mem_union, not_or]; exact ⟨hwnD, hwnEA⟩)⟩
          have hv₀_col' : col' v₀ = some j₂ := by simp [col', paintSet, hv₀_none]
          have hv₀_bwd : BwdSafe G₀ k D EA col' v₀ :=
            bwdSafe_of_k_inNbrs hv₀_col' hWcard.ge fun w hw =>
              ⟨by simp [col', paintSet, hw, hW_ncol w hw], (Finset.mem_filter.mp (hWsub hw)).2, (hW_safe w hw).2⟩
          have hv₀_fwd : FwdSafe G₀ k D EB col' v₀ :=
            hfwd_of_cnt col' (colExtends_trans hext0 hext')
              (fun d hd => fwdSafe_mono hext' (Finset.mem_filter.mp (colored_mono hext0 (hcol0_colored ▸ hd))).2 (hsafe d).1)
              v₀ j₂ hv₀_nD hv₀_col' hj2
          refine ⟨col', colExtends_trans hext hext', ?_, ?_, ?_⟩
          · intro w
            by_cases hwc : w ∈ colored col
            · have hws := (Finset.mem_filter.mp hwc).2
              exact ⟨fwdSafe_mono hext' hws (hsafe w).1, bwdSafe_mono hext' hws (hsafe w).2⟩
            · by_cases hw0 : w = v₀
              · subst hw0; exact ⟨hv₀_fwd, hv₀_bwd⟩
              · by_cases hwW : w ∈ W
                · exact hW_safe w hwW
                · have hnone : col' w = none := by
                    have hnc : col w = none := by
                      simp only [colored, Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_ne_none,
                        ne_eq, not_not] at hwc; exact hwc
                    simp [col', paintSet, hw0, hwW, hnc]
                  exact ⟨fun j hj => by simp [hnone] at hj, fun j hj => by simp [hnone] at hj⟩
          · refine Finset.insert_subset (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hv₀_col']⟩)
              (hTcol.trans (colored_mono hext'))
          · rw [Finset.card_insert_of_notMem hv₀_nT]
            have hsub' := paintSet_colored_sub col (insert v₀ W) j₂
            have h1 := Finset.card_le_card hsub'
            change (colored col').card ≤ _ at h1
            have h2 := Finset.card_union_le (colored col) (insert v₀ W)
            have h3 := Finset.card_insert_le v₀ W
            have hstep : (k + 1) * (T.card + 1) = (k + 1) * T.card + (k + 1) := by ring
            omega
  obtain ⟨col5a, hext5a, hsafe5a, hE1_col, _⟩ := hsweep1 E1 le_rfl
  -- Sweep 2 (Case 2): inductively colour S ⊆ E2!
  have hsweep2 : ∀ S : Finset V, S ⊆ E2 →
      ∃ col : V → Option (Fin t), ColExtends col5a col ∧ AllSafe G₀ k D EA EB col ∧ S ⊆ colored col := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; exact ⟨col5a, colExtends_refl col5a, hsafe5a, Finset.empty_subset _⟩
    | @insert v₀ T hv₀_nT ih =>
      intro hsub
      obtain ⟨col, hext, hsafe, hTcol⟩ := ih ((Finset.subset_insert _ _).trans hsub)
      by_cases hv₀_col : v₀ ∈ colored col
      · exact ⟨col, hext, hsafe, Finset.insert_subset hv₀_col hTcol⟩
      · have hv₀_E2 := hsub (Finset.mem_insert_self v₀ T)
        obtain ⟨hv₀_E, hv₀_lt⟩ := Finset.mem_filter.mp hv₀_E2
        have hv₀_none : col v₀ = none := by
          simp only [colored, Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_ne_none,
            ne_eq, not_not] at hv₀_col; exact hv₀_col
        have hext0 : ColExtends col0 col := colExtends_trans (colExtends_trans hext04 hext5a) hext
        have hv₀_nD : v₀ ∉ D := fun h => hv₀_col (colored_mono hext0 (hcol0_colored ▸ h))
        let avail : Finset V := Finset.univ \ (colored col ∪ E)
        by_cases hout : k ≤ (outNbr G₀ avail v₀).card
        · -- Case 2.1: colour v₀ and k out-nbrs in avail with colour 0!
          let j0 : Fin t := ⟨0, by omega⟩
          obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hout
          let col' := paintSet col (insert v₀ W) j0
          have hext' : ColExtends col col' := paintSet_extends col (insert v₀ W) j0
          have hW_ncol : ∀ w ∈ W, col w = none := fun w hw => by
            have hnc : w ∉ colored col := fun h => (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hWsub hw)).1).2 (Finset.mem_union_left _ h)
            simp only [colored, Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_ne_none,
              ne_eq, not_not] at hnc; exact hnc
          have hW_safe : ∀ w ∈ W, FwdSafe G₀ k D EB col' w ∧ BwdSafe G₀ k D EA col' w := fun w hw => by
            have hwa := (Finset.mem_filter.mp (hWsub hw)).1
            have hwnD : w ∉ D := fun h => (Finset.mem_sdiff.mp hwa).2 (Finset.mem_union_left _ (colored_mono hext0 (hcol0_colored ▸ h)))
            have hwnE : w ∉ E := fun h => (Finset.mem_sdiff.mp hwa).2 (Finset.mem_union_right _ h)
            have hwnEA : w ∉ EA := fun h => hwnE (Finset.mem_union_left _ h)
            have hwnEB : w ∉ EB := fun h => hwnE (Finset.mem_union_right _ h)
            exact ⟨fwdSafe_of_not_mem (by simp only [Finset.mem_union, not_or]; exact ⟨hwnD, hwnEB⟩),
              bwdSafe_of_not_mem (by simp only [Finset.mem_union, not_or]; exact ⟨hwnD, hwnEA⟩)⟩
          have hv₀_col' : col' v₀ = some j0 := by simp [col', paintSet, hv₀_none]
          have hv₀_fwd : FwdSafe G₀ k D EB col' v₀ :=
            fwdSafe_of_k_outNbrs hv₀_col' hWcard.ge fun w hw =>
              ⟨by simp [col', paintSet, hw, hW_ncol w hw], (Finset.mem_filter.mp (hWsub hw)).2, (hW_safe w hw).1⟩
          have hv₀_bwd : BwdSafe G₀ k D EA col' v₀ :=
            hbwd_of_cnt col' (colExtends_trans hext0 hext')
              (fun d hd => bwdSafe_mono hext' (Finset.mem_filter.mp (colored_mono hext0 (hcol0_colored ▸ hd))).2 (hsafe d).2)
              v₀ j0 hv₀_nD hv₀_col' (hv₀_lt j0).le
          refine ⟨col', colExtends_trans hext hext', ?_,
            Finset.insert_subset (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hv₀_col']⟩) (hTcol.trans (colored_mono hext'))⟩
          intro w
          by_cases hwc : w ∈ colored col
          · have hws := (Finset.mem_filter.mp hwc).2
            exact ⟨fwdSafe_mono hext' hws (hsafe w).1, bwdSafe_mono hext' hws (hsafe w).2⟩
          · by_cases hw0 : w = v₀
            · subst hw0; exact ⟨hv₀_fwd, hv₀_bwd⟩
            · by_cases hwW : w ∈ W
              · exact hW_safe w hwW
              · have hnone : col' w = none := by
                  have hnc : col w = none := by
                    simp only [colored, Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_ne_none,
                      ne_eq, not_not] at hwc; exact hwc
                  simp [col', paintSet, hw0, hwW, hnc]
                exact ⟨fun j hj => by simp [hnone] at hj, fun j hj => by simp [hnone] at hj⟩
        · -- Case 2.2: by averaging over t colours, some colour j has ≥ k out-nbrs of v₀!
          push Not at hout
          have hv₀_nXY : v₀ ∉ XY := fun h => hv₀_nD (hXY_sub_D h)
          have hgap := hE_gap v₀ hv₀_nXY
          have hcol_out_ge : k * t ≤ (outNbr G₀ (colored col) v₀).card := by
            have hsub_out : outNbr G₀ Finset.univ v₀ ⊆ outNbr G₀ (colored col) v₀ ∪ outNbr G₀ avail v₀ ∪ E := by
              intro w hw
              have hwf := Finset.mem_filter.mp hw
              by_cases hwc : w ∈ colored col
              · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwc, hwf.2⟩))
              · by_cases hwE : w ∈ E
                · exact Finset.mem_union_right _ hwE
                · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr
                    ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [hwc, hwE]⟩, hwf.2⟩))
            have h1 := Finset.card_le_card hsub_out
            have h2 := Finset.card_union_le (outNbr G₀ (colored col) v₀ ∪ outNbr G₀ avail v₀) E
            have h3 := Finset.card_union_le (outNbr G₀ (colored col) v₀) (outNbr G₀ avail v₀)
            change outDeg G₀ Finset.univ v₀ ≤ _ at h1
            have hkt_le : k + k * t ≤ 10 * k * t := by
              have h1' : k ≤ k * t := Nat.le_mul_of_pos_right k (by omega)
              have h2' : 10 * k * t = 10 * (k * t) := by ring
              omega
            omega
          have hex_j : ∃ j : Fin t, k ≤ (outNbr G₀ (colClass col j) v₀).card := by
            by_contra hno; push Not at hno
            have hpart : outNbr G₀ (colored col) v₀ = Finset.univ.biUnion fun j : Fin t => outNbr G₀ (colClass col j) v₀ := by
              ext w; simp only [outNbr, colored, colClass, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
              constructor
              · rintro ⟨hwc, hadj⟩
                cases hc : col w with
                | none => simp [hc] at hwc
                | some j => exact ⟨j, rfl, hadj⟩
              · rintro ⟨j, hcw, hadj⟩; exact ⟨by simp [hcw], hadj⟩
            have hle : (outNbr G₀ (colored col) v₀).card ≤ ∑ j : Fin t, (outNbr G₀ (colClass col j) v₀).card := by
              rw [hpart]; exact Finset.card_biUnion_le
            have hsum_lt : ∑ j : Fin t, (outNbr G₀ (colClass col j) v₀).card ≤ ∑ _j : Fin t, (k - 1) :=
              Finset.sum_le_sum fun j _ => by have := hno j; omega
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum_lt
            have : t * (k - 1) < k * t := by
              rw [Nat.mul_comm k t]; exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
            omega
          obtain ⟨j, hj_ge⟩ := hex_j
          let col' := paintSet col {v₀} j
          have hext' : ColExtends col col' := paintSet_extends col {v₀} j
          have hv₀_col' : col' v₀ = some j := by simp [col', paintSet, hv₀_none]
          have hv₀_fwd : FwdSafe G₀ k D EB col' v₀ :=
            fwdSafe_of_k_outNbrs hv₀_col' hj_ge fun w hw => by
              have hwf := Finset.mem_filter.mp hw
              have hcw : col w = some j := (Finset.mem_filter.mp hwf.1).2
              exact ⟨hext' w j hcw, hwf.2, fwdSafe_mono hext' (by simp [hcw]) (hsafe w).1⟩
          have hv₀_bwd : BwdSafe G₀ k D EA col' v₀ :=
            hbwd_of_cnt col' (colExtends_trans hext0 hext')
              (fun d hd => bwdSafe_mono hext' (Finset.mem_filter.mp (colored_mono hext0 (hcol0_colored ▸ hd))).2 (hsafe d).2)
              v₀ j hv₀_nD hv₀_col' (hv₀_lt j).le
          refine ⟨col', colExtends_trans hext hext', ?_,
            Finset.insert_subset (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hv₀_col']⟩) (hTcol.trans (colored_mono hext'))⟩
          intro w
          by_cases hwc : w ∈ colored col
          · have hws := (Finset.mem_filter.mp hwc).2
            exact ⟨fwdSafe_mono hext' hws (hsafe w).1, bwdSafe_mono hext' hws (hsafe w).2⟩
          · by_cases hw0 : w = v₀
            · subst hw0; exact ⟨hv₀_fwd, hv₀_bwd⟩
            · have hnone : col' w = none := by
                have hnc : col w = none := by
                  simp only [colored, Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_ne_none,
                    ne_eq, not_not] at hwc; exact hwc
                simp [col', paintSet, hw0, hnc]
              exact ⟨fun j' hj' => by simp [hnone] at hj', fun j' hj' => by simp [hnone] at hj'⟩
  obtain ⟨col5b, hext5b, hsafe5b, hE2_col⟩ := hsweep2 E2 le_rfl
  -- Key invariant after Sweeps 1 & 2: EVERY vertex in EB \ EA is ALREADY coloured in col5b!
  have hEB_sub_EA_or_col5b : ∀ w : V, w ∈ EB → w ∉ EA → w ∈ colored col5b := by
    intro w hwEB hwnEA
    have hwE : w ∈ E := Finset.mem_union_right _ hwEB
    have hcntA0 : ∀ j : Fin t, cntA w j = 0 := fun j => by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro a _ hmem; exact hwnEA (Finset.mem_biUnion.mpr ⟨idxOf j a, Finset.mem_univ _, hmem⟩)
    rw [hE_cover] at hwE
    rcases Finset.mem_union.mp hwE with h12 | h3
    · rcases Finset.mem_union.mp h12 with h1 | h2
      · exact colored_mono hext5b (hE1_col h1)
      · exact hE2_col h2
    · have hlt := (Finset.mem_filter.mp h3).2 ⟨0, by omega⟩
      rw [hcntA0 ⟨0, by omega⟩] at hlt; omega
  -- Sweep 3 (Case 3): inductively colour S ⊆ E3!
  have hsweep3 : ∀ S : Finset V, S ⊆ E3 →
      ∃ col : V → Option (Fin t), ColExtends col5b col ∧ AllSafe G₀ k D EA EB col ∧ S ⊆ colored col := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; exact ⟨col5b, colExtends_refl col5b, hsafe5b, Finset.empty_subset _⟩
    | @insert v₀ T hv₀_nT ih =>
      intro hsub
      obtain ⟨col, hext, hsafe, hTcol⟩ := ih ((Finset.subset_insert _ _).trans hsub)
      by_cases hv₀_col : v₀ ∈ colored col
      · exact ⟨col, hext, hsafe, Finset.insert_subset hv₀_col hTcol⟩
      · have hv₀_E3 := hsub (Finset.mem_insert_self v₀ T)
        obtain ⟨hv₀_E, hv₀_lt⟩ := Finset.mem_filter.mp hv₀_E3
        have hv₀_none : col v₀ = none := by
          simp only [colored, Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_ne_none,
            ne_eq, not_not] at hv₀_col; exact hv₀_col
        have hext0 : ColExtends col0 col := colExtends_trans (colExtends_trans (colExtends_trans hext04 hext5a) hext5b) hext
        have hv₀_nD : v₀ ∉ D := fun h => hv₀_col (colored_mono hext0 (hcol0_colored ▸ h))
        let availA : Finset V := Finset.univ \ (colored col ∪ EA)
        -- Every w ∈ availA is ALSO outside EB (by hEB_sub_EA_or_col5b!)
        have havailA_nEB : ∀ w ∈ availA, w ∉ EB := fun w hw hwEB => by
          have hwncol : w ∉ colored col := fun h => (Finset.mem_sdiff.mp hw).2 (Finset.mem_union_left _ h)
          have hwnEA : w ∉ EA := fun h => (Finset.mem_sdiff.mp hw).2 (Finset.mem_union_right _ h)
          exact hwncol (colored_mono hext (hEB_sub_EA_or_col5b w hwEB hwnEA))
        by_cases hin : k ≤ (inNbr G₀ availA v₀).card
        · -- Case 3.1: colour v₀ and k in-nbrs in availA with colour 0!
          let j0 : Fin t := ⟨0, by omega⟩
          obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hin
          let col' := paintSet col (insert v₀ W) j0
          have hext' : ColExtends col col' := paintSet_extends col (insert v₀ W) j0
          have hW_ncol : ∀ w ∈ W, col w = none := fun w hw => by
            have hnc : w ∉ colored col := fun h => (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hWsub hw)).1).2 (Finset.mem_union_left _ h)
            simp only [colored, Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_ne_none,
              ne_eq, not_not] at hnc; exact hnc
          have hW_safe : ∀ w ∈ W, FwdSafe G₀ k D EB col' w ∧ BwdSafe G₀ k D EA col' w := fun w hw => by
            have hwa := (Finset.mem_filter.mp (hWsub hw)).1
            have hwnD : w ∉ D := fun h => (Finset.mem_sdiff.mp hwa).2 (Finset.mem_union_left _ (colored_mono hext0 (hcol0_colored ▸ h)))
            have hwnEA : w ∉ EA := fun h => (Finset.mem_sdiff.mp hwa).2 (Finset.mem_union_right _ h)
            have hwnEB : w ∉ EB := havailA_nEB w hwa
            exact ⟨fwdSafe_of_not_mem (by simp only [Finset.mem_union, not_or]; exact ⟨hwnD, hwnEB⟩),
              bwdSafe_of_not_mem (by simp only [Finset.mem_union, not_or]; exact ⟨hwnD, hwnEA⟩)⟩
          have hv₀_col' : col' v₀ = some j0 := by simp [col', paintSet, hv₀_none]
          have hv₀_bwd : BwdSafe G₀ k D EA col' v₀ :=
            bwdSafe_of_k_inNbrs hv₀_col' hWcard.ge fun w hw =>
              ⟨by simp [col', paintSet, hw, hW_ncol w hw], (Finset.mem_filter.mp (hWsub hw)).2, (hW_safe w hw).2⟩
          have hv₀_fwd : FwdSafe G₀ k D EB col' v₀ :=
            hfwd_of_cnt col' (colExtends_trans hext0 hext')
              (fun d hd => fwdSafe_mono hext' (Finset.mem_filter.mp (colored_mono hext0 (hcol0_colored ▸ hd))).2 (hsafe d).1)
              v₀ j0 hv₀_nD hv₀_col' (hv₀_lt j0).le
          refine ⟨col', colExtends_trans hext hext', ?_,
            Finset.insert_subset (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hv₀_col']⟩) (hTcol.trans (colored_mono hext'))⟩
          intro w
          by_cases hwc : w ∈ colored col
          · have hws := (Finset.mem_filter.mp hwc).2
            exact ⟨fwdSafe_mono hext' hws (hsafe w).1, bwdSafe_mono hext' hws (hsafe w).2⟩
          · by_cases hw0 : w = v₀
            · subst hw0; exact ⟨hv₀_fwd, hv₀_bwd⟩
            · by_cases hwW : w ∈ W
              · exact hW_safe w hwW
              · have hnone : col' w = none := by
                  have hnc : col w = none := by
                    simp only [colored, Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_ne_none,
                      ne_eq, not_not] at hwc; exact hwc
                  simp [col', paintSet, hw0, hwW, hnc]
                exact ⟨fun j hj => by simp [hnone] at hj, fun j hj => by simp [hnone] at hj⟩
        · -- Case 3.2: by averaging over t colours, some colour j has ≥ k in-nbrs of v₀!
          push Not at hin
          have hv₀_nXY : v₀ ∉ XY := fun h => hv₀_nD (hXY_sub_D h)
          have hgap := hEA_gap v₀ hv₀_nXY
          have hcol_in_ge : k * t ≤ (inNbr G₀ (colored col) v₀).card := by
            have hsub_in : inNbr G₀ Finset.univ v₀ ⊆ inNbr G₀ (colored col) v₀ ∪ inNbr G₀ availA v₀ ∪ EA := by
              intro w hw
              have hwf := Finset.mem_filter.mp hw
              by_cases hwc : w ∈ colored col
              · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwc, hwf.2⟩))
              · by_cases hwEA : w ∈ EA
                · exact Finset.mem_union_right _ hwEA
                · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr
                    ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [hwc, hwEA]⟩, hwf.2⟩))
            have h1 := Finset.card_le_card hsub_in
            have h2 := Finset.card_union_le (inNbr G₀ (colored col) v₀ ∪ inNbr G₀ availA v₀) EA
            have h3 := Finset.card_union_le (inNbr G₀ (colored col) v₀) (inNbr G₀ availA v₀)
            change inDeg G₀ Finset.univ v₀ ≤ _ at h1
            have hkt_le : k + k * t ≤ 10 * k * t := by
              have h1' : k ≤ k * t := Nat.le_mul_of_pos_right k (by omega)
              have h2' : 10 * k * t = 10 * (k * t) := by ring
              omega
            omega
          have hex_j : ∃ j : Fin t, k ≤ (inNbr G₀ (colClass col j) v₀).card := by
            by_contra hno; push Not at hno
            have hpart : inNbr G₀ (colored col) v₀ = Finset.univ.biUnion fun j : Fin t => inNbr G₀ (colClass col j) v₀ := by
              ext w; simp only [inNbr, colored, colClass, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
              constructor
              · rintro ⟨hwc, hadj⟩
                cases hc : col w with
                | none => simp [hc] at hwc
                | some j => exact ⟨j, rfl, hadj⟩
              · rintro ⟨j, hcw, hadj⟩; exact ⟨by simp [hcw], hadj⟩
            have hle : (inNbr G₀ (colored col) v₀).card ≤ ∑ j : Fin t, (inNbr G₀ (colClass col j) v₀).card := by
              rw [hpart]; exact Finset.card_biUnion_le
            have hsum_lt : ∑ j : Fin t, (inNbr G₀ (colClass col j) v₀).card ≤ ∑ _j : Fin t, (k - 1) :=
              Finset.sum_le_sum fun j _ => by have := hno j; omega
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum_lt
            have : t * (k - 1) < k * t := by
              rw [Nat.mul_comm k t]; exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
            omega
          obtain ⟨j, hj_ge⟩ := hex_j
          let col' := paintSet col {v₀} j
          have hext' : ColExtends col col' := paintSet_extends col {v₀} j
          have hv₀_col' : col' v₀ = some j := by simp [col', paintSet, hv₀_none]
          have hv₀_bwd : BwdSafe G₀ k D EA col' v₀ :=
            bwdSafe_of_k_inNbrs hv₀_col' hj_ge fun w hw => by
              have hwf := Finset.mem_filter.mp hw
              have hcw : col w = some j := (Finset.mem_filter.mp hwf.1).2
              exact ⟨hext' w j hcw, hwf.2, bwdSafe_mono hext' (by simp [hcw]) (hsafe w).2⟩
          have hv₀_fwd : FwdSafe G₀ k D EB col' v₀ :=
            hfwd_of_cnt col' (colExtends_trans hext0 hext')
              (fun d hd => fwdSafe_mono hext' (Finset.mem_filter.mp (colored_mono hext0 (hcol0_colored ▸ hd))).2 (hsafe d).1)
              v₀ j hv₀_nD hv₀_col' (hv₀_lt j).le
          refine ⟨col', colExtends_trans hext hext', ?_,
            Finset.insert_subset (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hv₀_col']⟩) (hTcol.trans (colored_mono hext'))⟩
          intro w
          by_cases hwc : w ∈ colored col
          · have hws := (Finset.mem_filter.mp hwc).2
            exact ⟨fwdSafe_mono hext' hws (hsafe w).1, bwdSafe_mono hext' hws (hsafe w).2⟩
          · by_cases hw0 : w = v₀
            · subst hw0; exact ⟨hv₀_fwd, hv₀_bwd⟩
            · have hnone : col' w = none := by
                have hnc : col w = none := by
                  simp only [colored, Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_ne_none,
                    ne_eq, not_not] at hwc; exact hwc
                simp [col', paintSet, hw0, hnc]
              exact ⟨fun j' hj' => by simp [hnone] at hj', fun j' hj' => by simp [hnone] at hj'⟩
  obtain ⟨col5, hext5c, hsafe5, hE3_col⟩ := hsweep3 E3 le_rfl
  have hext4_5 : ColExtends col4 col5 := colExtends_trans hext5a (colExtends_trans hext5b hext5c)
  have hext05 : ColExtends col0 col5 := colExtends_trans hext04 hext4_5
  have hE_col5 : E ⊆ colored col5 := by
    rw [hE_cover]
    exact Finset.union_subset (Finset.union_subset
      (hE1_col.trans (colored_mono (colExtends_trans hext5b hext5c)))
      (hE2_col.trans (colored_mono hext5c))) hE3_col
  -- Final partition: assign all remaining uncoloured vertices (all outside D ∪ E!) to colour 0!
  let j0 : Fin t := ⟨0, by omega⟩
  let part : V → Fin t := fun v => (col5 v).getD j0
  let colF : V → Option (Fin t) := fun v => some (part v)
  have hext5F : ColExtends col5 colF := fun v j h => by simp [colF, part, h]
  have hcolF_safe : AllSafe G₀ k D EA EB colF := by
    intro v
    by_cases hvc : v ∈ colored col5
    · have hvs := (Finset.mem_filter.mp hvc).2
      exact ⟨fwdSafe_mono hext5F hvs (hsafe5 v).1, bwdSafe_mono hext5F hvs (hsafe5 v).2⟩
    · have hvnD : v ∉ D := fun h => hvc (colored_mono hext05 (hcol0_colored ▸ h))
      have hvnE : v ∉ E := fun h => hvc (hE_col5 h)
      have hvnEA : v ∉ EA := fun h => hvnE (Finset.mem_union_left _ h)
      have hvnEB : v ∉ EB := fun h => hvnE (Finset.mem_union_right _ h)
      exact ⟨fwdSafe_of_not_mem (by simp only [Finset.mem_union, not_or]; exact ⟨hvnD, hvnEB⟩),
        bwdSafe_of_not_mem (by simp only [Finset.mem_union, not_or]; exact ⟨hvnD, hvnEA⟩)⟩
  -- CLAIM 1 & 2: Every part `part ⁻¹' {j}` is strongly k-connected!
  refine ⟨part, fun j => ?_⟩
  have hpart_eq : (part ⁻¹' {j} : Set V) = (colClass colF j : Set V) := by
    ext v; simp [colClass, colF]
  rw [hpart_eq]
  have hblocks_disj : ∀ a₁ a₂ : Fin k, a₁ ≠ a₂ →
      Disjoint ((A (idxOf j a₁)).toFinset ∪ (B (idxOf j a₁)).toFinset ∪ (P_all (idxOf j a₁)).toFinset)
               ((A (idxOf j a₂)).toFinset ∪ (B (idxOf j a₂)).toFinset ∪ (P_all (idxOf j a₂)).toFinset) := by
    intro a₁ a₂ hne
    set i₁ := idxOf j a₁
    set i₂ := idxOf j a₂
    have hi_ne : i₁ ≠ i₂ := fun h => hne (hidx_inj j h)
    have hsplit : ∀ i w, w ∈ (A i).toFinset ∪ (B i).toFinset ∪ (P_all i).toFinset →
        w ∈ (A i).toFinset ∪ (B i).toFinset ∨ w ∈ (P_all i).toFinset \ {snkB i, srcA i} := by
      intro i w hw
      rcases Finset.mem_union.mp hw with hAB | hP
      · exact Or.inl hAB
      · by_cases hws : w = snkB i
        · have hlast : snkB i ∈ (B i).toFinset := List.mem_toFinset.mpr (List.getLast_mem _)
          exact Or.inl (Finset.mem_union_right _ (hws ▸ hlast))
        · by_cases hwa : w = srcA i
          · have hhd : srcA i ∈ (A i).toFinset := List.mem_toFinset.mpr (List.head_mem _)
            exact Or.inl (Finset.mem_union_left _ (hwa ▸ hhd))
          · exact Or.inr (Finset.mem_sdiff.mpr ⟨hP, by simp [hws, hwa]⟩)
    have hAB_sub_D : ∀ i, (A i).toFinset ∪ (B i).toFinset ⊆ D := fun i w hw => by
      rcases Finset.mem_union.mp hw with hA | hB
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hA⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hB⟩)
    rw [Finset.disjoint_left]
    intro w hw₁ hw₂
    rcases hsplit i₁ w hw₁ with hAB₁ | hint₁ <;> rcases hsplit i₂ w hw₂ with hAB₂ | hint₂
    · rcases Finset.mem_union.mp hAB₁ with hA₁ | hB₁ <;> rcases Finset.mem_union.mp hAB₂ with hA₂ | hB₂
      · exact Finset.disjoint_left.mp (hA_disj i₁ i₂ hi_ne) hA₁ hA₂
      · exact Finset.disjoint_left.mp (hAB_disj i₁ i₂) hA₁ hB₂
      · exact Finset.disjoint_left.mp (hAB_disj i₂ i₁) hA₂ hB₁
      · exact Finset.disjoint_left.mp (hB_disj i₁ i₂ hi_ne) hB₁ hB₂
    · exact Finset.disjoint_left.mp (hPint_disj_D i₂) hint₂ (hAB_sub_D i₁ hAB₁)
    · exact Finset.disjoint_left.mp (hPint_disj_D i₁) hint₁ (hAB_sub_D i₂ hAB₂)
    · exact Finset.disjoint_left.mp (hPint_disj_Pint i₁ i₂ hi_ne) hint₁ hint₂
  refine ⟨?_, ?_⟩
  · -- |colClass colF j| > k (contains A (idxOf j a) and B (idxOf j a) for all a : Fin k -> ≥ 2k > k!)
    rw [Set.ncard_coe_finset]
    let headsA : Finset V := Finset.univ.image fun a : Fin k => (A (idxOf j a)).head (hA_tr _).1.1
    let headsB : Finset V := Finset.univ.image fun a : Fin k => (B (idxOf j a)).head (hB_tr _).1.1
    have hdisjAB : Disjoint headsA headsB := by
      rw [Finset.disjoint_left]; intro w h1 h2; rw [Finset.mem_image] at h1 h2
      obtain ⟨a₁, _, rfl⟩ := h1; obtain ⟨a₂, _, h2'⟩ := h2
      exact Finset.disjoint_left.mp (hAB_disj (idxOf j a₁) (idxOf j a₂))
        (List.mem_toFinset.mpr (List.head_mem _)) (h2' ▸ List.mem_toFinset.mpr (List.head_mem _))
    have hsub : headsA ∪ headsB ⊆ colClass colF j := by
      intro w hw; simp only [colClass, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Finset.mem_union.mp hw with h1 | h2
      · rw [Finset.mem_image] at h1
        obtain ⟨a, _, rfl⟩ := h1
        have hmem : (A (idxOf j a)).head (hA_tr _).1.1 ∈ (A (idxOf j a)).toFinset := List.mem_toFinset.mpr (List.head_mem _)
        have hc0 := hcol0_AB (idxOf j a) _ (Finset.mem_union_left _ hmem)
        rw [hblock_idx j a] at hc0; exact hext5F _ j (hext05 _ j hc0)
      · rw [Finset.mem_image] at h2
        obtain ⟨a, _, rfl⟩ := h2
        have hmem : (B (idxOf j a)).head (hB_tr _).1.1 ∈ (B (idxOf j a)).toFinset := List.mem_toFinset.mpr (List.head_mem _)
        have hc0 := hcol0_AB (idxOf j a) _ (Finset.mem_union_right _ hmem)
        rw [hblock_idx j a] at hc0; exact hext5F _ j (hext05 _ j hc0)
    have hA_c : headsA.card = k := by
      rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
      intro a₁ a₂ h; exact hidx_inj j (hsrcA_inj h)
    have hB_c : headsB.card = k := by
      rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
      intro a₁ a₂ h; by_contra hne
      dsimp only at h
      have h1 : (B (idxOf j a₁)).head (hB_tr _).1.1 ∈ (B (idxOf j a₁)).toFinset := List.mem_toFinset.mpr (List.head_mem _)
      have h2 : (B (idxOf j a₂)).head (hB_tr _).1.1 ∈ (B (idxOf j a₂)).toFinset := List.mem_toFinset.mpr (List.head_mem _)
      rw [h] at h1
      exact Finset.disjoint_left.mp (hB_disj _ _ (fun e => hne (hidx_inj j e))) h1 h2
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisjAB, hA_c, hB_c] at this
    omega
  · -- IsStrongOn G₀ (colClass colF j \ S_del) for any S_del with S_del.card < k!
    intro S_del hS_lt u hu v hv
    have huF : u ∈ colClass colF j \ S_del := by simpa [Finset.mem_sdiff] using hu
    have hvF : v ∈ colClass colF j \ S_del := by simpa [Finset.mem_sdiff] using hv
    have hu_col : colF u = some j := (Finset.mem_filter.mp (Finset.mem_sdiff.mp huF).1).2
    have hv_col : colF v = some j := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hvF).1).2
    -- Step 1 (Safety): walk from u to u' ∈ (colClass colF j \ (D ∪ EB)) \ S_del,
    -- and from v' ∈ (colClass colF j \ (D ∪ EA)) \ S_del to v!
    obtain ⟨u', hu', hwalk_u⟩ := (hcolF_safe u).1 j hu_col S_del hS_lt (Finset.mem_sdiff.mp huF).2
    obtain ⟨v', hv', hwalk_v⟩ := (hcolF_safe v).2 j hv_col S_del hS_lt (Finset.mem_sdiff.mp hvF).2
    -- Step 2 (Claim 1): since |S_del| < k, some a₀ : Fin k has block (A ∪ B ∪ P) disjoint from S_del!
    let block : Fin k → Finset V := fun a =>
      (A (idxOf j a)).toFinset ∪ (B (idxOf j a)).toFinset ∪ (P_all (idxOf j a)).toFinset
    have hex_a0 : ∃ a₀ : Fin k, Disjoint (block a₀) S_del := by
      let badA := (Finset.univ : Finset (Fin k)).filter fun a => ¬ Disjoint (block a) S_del
      have hbadA_le : badA.card ≤ S_del.card := by
        have hex : ∀ a ∈ badA, ∃ z ∈ S_del, z ∈ block a := by
          intro a ha; have hnd := (Finset.mem_filter.mp ha).2
          rw [Finset.not_disjoint_iff] at hnd; obtain ⟨z, hz1, hz2⟩ := hnd; exact ⟨z, hz2, hz1⟩
        choose pick hpS hpB using hex
        let pick' : Fin k → V := fun a => if ha : a ∈ badA then pick a ha else u
        have hinj : Set.InjOn pick' (badA : Set (Fin k)) := by
          intro a₁ ha₁ a₂ ha₂ heq; by_contra hne
          simp only [pick', Finset.mem_coe.mp ha₁, Finset.mem_coe.mp ha₂, ↓reduceDIte] at heq
          exact Finset.disjoint_left.mp (hblocks_disj a₁ a₂ hne)
            (hpB a₁ (Finset.mem_coe.mp ha₁)) (heq ▸ hpB a₂ (Finset.mem_coe.mp ha₂))
        calc badA.card = (badA.image pick').card := (Finset.card_image_of_injOn hinj).symm
          _ ≤ S_del.card := Finset.card_le_card (Finset.image_subset_iff.mpr fun a ha => by
            simpa only [pick', ha, ↓reduceDIte] using hpS a ha)
      have hrem : (Finset.univ \ badA).Nonempty := Finset.card_pos.mp (by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]; omega)
      obtain ⟨a₀, ha₀⟩ := hrem; rw [Finset.mem_sdiff] at ha₀
      refine ⟨a₀, ?_⟩; by_contra hnd; exact ha₀.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnd⟩)
    obtain ⟨a₀, ha₀_disj⟩ := hex_a0
    set i₀ := idxOf j a₀
    have hblk_sub : block a₀ ⊆ colClass colF j \ S_del := by
      intro w hw
      refine Finset.mem_sdiff.mpr ⟨?_, Finset.disjoint_left.mp ha₀_disj hw⟩
      simp only [colClass, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Finset.mem_union.mp hw with hAB | hP
      · have hc0 := hcol0_AB i₀ w hAB; rw [hblock_idx j a₀] at hc0
        exact hext5F w j (hext05 w j hc0)
      · have hc4 := hPall_col4 i₀ w (List.mem_toFinset.mp hP); rw [hblock_idx j a₀] at hc4
        exact hext5F w j (hext4_5 w j hc4)
    -- Walk: u' → b ∈ B i₀ → snkB i₀ →(P_all i₀)→ srcA i₀ → a ∈ A i₀ → v' inside colClass colF j \ S_del!
    have hu'_nDEB : u' ∉ D ∪ EB_i i₀ := by
      have h1 := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hu').1).2
      simp only [Finset.mem_union, not_or] at h1 ⊢
      exact ⟨h1.1, fun h => h1.2 (Finset.mem_biUnion.mpr ⟨i₀, Finset.mem_univ _, h⟩)⟩
    have hv'_nDEA : v' ∉ D ∪ EA_i i₀ := by
      have h1 := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv').1).2
      simp only [Finset.mem_union, not_or] at h1 ⊢
      exact ⟨h1.1, fun h => h1.2 (Finset.mem_biUnion.mpr ⟨i₀, Finset.mem_univ _, h⟩)⟩
    obtain ⟨b, hbB, hu'b⟩ := hB_dom i₀ u' (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hu'_nDEB⟩)
    obtain ⟨a, haA, hav'⟩ := hA_dom i₀ v' (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv'_nDEA⟩)
    have hu'_in : u' ∈ colClass colF j \ S_del :=
      Finset.sdiff_subset_sdiff Finset.sdiff_subset le_rfl hu'
    have hv'_in : v' ∈ colClass colF j \ S_del :=
      Finset.sdiff_subset_sdiff Finset.sdiff_subset le_rfl hv'
    have hb_in : b ∈ colClass colF j \ S_del :=
      hblk_sub (Finset.mem_union_left _ (Finset.mem_union_right _ (List.mem_toFinset.mpr hbB)))
    have hsnk_in : snkB i₀ ∈ colClass colF j \ S_del :=
      hblk_sub (Finset.mem_union_left _ (Finset.mem_union_right _ (List.mem_toFinset.mpr (List.getLast_mem _))))
    have hsrc_in : srcA i₀ ∈ colClass colF j \ S_del :=
      hblk_sub (Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.mpr (List.head_mem _))))
    have ha_in : a ∈ colClass colF j \ S_del :=
      hblk_sub (Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.mpr haA)))
    have hw1 : WalkIn G₀ (colClass colF j \ S_del) u' b :=
      Relation.ReflTransGen.single ⟨hu'_in, hb_in, hu'b⟩
    have hw2 : WalkIn G₀ (colClass colF j \ S_del) b (snkB i₀) := by
      by_cases hbeq : b = snkB i₀
      · rw [hbeq]; exact Relation.ReflTransGen.refl
      · obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hbB
        have hlt : idx < (B i₀).length - 1 := by
          have : idx ≠ (B i₀).length - 1 := fun h => hbeq (by subst h; exact (List.getLast_eq_getElem _).symm)
          omega
        have hadj : G₀.Adj (B i₀)[idx] (snkB i₀) := by
          dsimp only [snkB]; rw [List.getLast_eq_getElem]
          exact (hB_tr i₀).1.2.2 idx ((B i₀).length - 1) hlt (by omega)
        exact Relation.ReflTransGen.single ⟨hb_in, hsnk_in, hadj⟩
    have hw3 : WalkIn G₀ (colClass colF j \ S_del) (snkB i₀) (srcA i₀) := by
      have h := reflTransGen_of_isDirPathBetween (S := ((colClass colF j \ S_del : Finset V) : Set V))
        (hPall_bet i₀) (fun w hw => hblk_sub (Finset.mem_union_right _ (List.mem_toFinset.mpr hw)))
      exact h
    have hw4 : WalkIn G₀ (colClass colF j \ S_del) (srcA i₀) a := by
      by_cases haeq : srcA i₀ = a
      · rw [haeq]; exact Relation.ReflTransGen.refl
      · obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem haA
        have hpos : 0 < idx := by
          have : idx ≠ 0 := fun h => haeq (by subst h; exact List.head_eq_getElem_zero _)
          omega
        have hadj : G₀.Adj (srcA i₀) (A i₀)[idx] := by
          dsimp only [srcA]; rw [List.head_eq_getElem_zero]
          exact (hA_tr i₀).1.2.2 0 idx hpos hidx
        exact Relation.ReflTransGen.single ⟨hsrc_in, ha_in, hadj⟩
    have hw5 : WalkIn G₀ (colClass colF j \ S_del) a v' :=
      Relation.ReflTransGen.single ⟨ha_in, hv'_in, hav'⟩
    have htotal : WalkIn G₀ (colClass colF j \ S_del) u v :=
      ((((((hwalk_u.trans hw1).trans hw2).trans hw3).trans hw4).trans hw5).trans hwalk_v)
    exact Relation.ReflTransGen.mono (fun x y h => by
      simp only [Finset.mem_sdiff] at h; simp only [Set.mem_sdiff, Finset.mem_coe]; exact h) _ _ htotal


/-- Core KOT construction: builds `(x, y, A, B, EA_i, EB_i)` and applies `kot_partition_wlog`
either to `G` (if `|EA| ≤ |EB|`) or to `opDigraph G` (if `|EB| < |EA|`). -/
private theorem kot_partition_uniform {G : Digraph V} [DecidableRel G.Adj] (hT : IsTournament G)
    {k t : ℕ} (hk : 2 ≤ k) (ht : 2 ≤ t)
    (hstrong : IsKStrongOn G Set.univ (gKOT k t)) :
    ∃ part : V → Fin t, ∀ j : Fin t, IsKStrongOn G (part ⁻¹' {j}) k := by
  classical
  let c : ℕ := 128 * k * k * t
  let D_bd : ℕ := 2 * k * t * c
  let N3 : ℕ := (k + 1) ^ 2 * (D_bd + 4 * k * k * t)
  let N41 : ℕ := N3 + (k + 1) ^ 2 * k * k * t
  let q : ℕ := 13 * k ^ 4 * t
  let N43_pre : ℕ := N41 + 2 * q * k * t * (k + 1) + q
  let g : ℕ := gKOT k t
  have hg_eq : g = 10 * (N43_pre + 600 * (k * t * q * 8) + 10 * k * t + 10) := rfl
  have hkt_pos : 1 ≤ k * t := Nat.mul_pos (by omega) (by omega)
  have hU_strong : IsKStrongOn G ((Finset.univ : Finset V) : Set V) g := by simpa using hstrong
  have hdeg_out : ∀ v : V, g ≤ outDeg G Finset.univ v := fun v =>
    min_outDeg_of_isKStrongOn hT hU_strong (Finset.mem_univ v)
  have hdeg_in : ∀ v : V, g ≤ inDeg G Finset.univ v := fun v =>
    min_inDeg_of_isKStrongOn hT hU_strong (Finset.mem_univ v)
  let n : ℕ := Fintype.card V
  have hn_ge : 2 * g + 1 ≤ n := by
    have hgt : g < n := by simpa [n, Set.ncard_coe_finset] using hU_strong.1
    obtain ⟨v, _⟩ := Finset.card_pos.mp (by rw [Finset.card_univ]; change 0 < n; omega : 0 < (Finset.univ : Finset V).card)
    have h1 := hdeg_out v
    have h2 := hdeg_in v
    have h3 := outDeg_add_inDeg_eq hT (Finset.mem_univ v)
    simp only [Finset.card_univ] at h3
    omega
  have h2kt_le_g : 2 * (k * t) ≤ g := by
    rw [hg_eq]
    have : 10 * k * t = 10 * (k * t) := by ring
    omega
  have hex_low_in : ∃ X : Finset V, X.card = k * t ∧
      ∀ u ∈ X, ∀ w ∈ Finset.univ \ X, inDeg G Finset.univ u ≤ inDeg G Finset.univ w := by
    have hcard_le : k * t ≤ (Finset.univ : Finset V).card := by
      rw [Finset.card_univ]; change k * t ≤ n; omega
    suffices hgen : ∀ r : ℕ, r ≤ (Finset.univ : Finset V).card →
        ∃ X : Finset V, X.card = r ∧
          ∀ u ∈ X, ∀ w ∈ Finset.univ \ X, inDeg G Finset.univ u ≤ inDeg G Finset.univ w by
      exact hgen (k * t) hcard_le
    intro r hr
    induction r with
    | zero => exact ⟨∅, rfl, fun u hu => by simp at hu⟩
    | succ r ih =>
      obtain ⟨X, hXc, hXmin⟩ := ih (by omega)
      have hne : ((Finset.univ : Finset V) \ X).Nonempty := Finset.card_pos.mp (by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hXc]; omega)
      obtain ⟨v, hv_sd, hv_min⟩ := Finset.exists_min_image (Finset.univ \ X) (inDeg G Finset.univ) hne
      have hv_nX : v ∉ X := (Finset.mem_sdiff.mp hv_sd).2
      refine ⟨insert v X, by rw [Finset.card_insert_of_notMem hv_nX, hXc], fun u hu w hw => ?_⟩
      have hw_sd : w ∈ Finset.univ \ X := Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, fun h => (Finset.mem_sdiff.mp hw).2 (Finset.mem_insert_of_mem h)⟩
      rcases Finset.mem_insert.mp hu with rfl | huX
      · exact hv_min w hw_sd
      · exact hXmin u huX w hw_sd
  obtain ⟨Xset, hXset_c, hXset_min⟩ := hex_low_in
  have hex_low_out : ∃ Y ⊆ Finset.univ \ Xset, Y.card = k * t ∧
      ∀ u ∈ Y, ∀ w ∈ (Finset.univ \ Xset) \ Y, outDeg G Finset.univ u ≤ outDeg G Finset.univ w := by
    have hcard_le : k * t ≤ (Finset.univ \ Xset).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hXset_c]
      change k * t ≤ n - k * t; omega
    suffices hgen : ∀ r : ℕ, r ≤ (Finset.univ \ Xset).card →
        ∃ Y ⊆ Finset.univ \ Xset, Y.card = r ∧
          ∀ u ∈ Y, ∀ w ∈ (Finset.univ \ Xset) \ Y, outDeg G Finset.univ u ≤ outDeg G Finset.univ w by
      exact hgen (k * t) hcard_le
    intro r hr
    induction r with
    | zero => exact ⟨∅, Finset.empty_subset _, rfl, fun u hu => by simp at hu⟩
    | succ r ih =>
      obtain ⟨Y, hYsub, hYc, hYmin⟩ := ih (by omega)
      have hne : ((Finset.univ \ Xset) \ Y).Nonempty := Finset.card_pos.mp (by
        rw [Finset.card_sdiff_of_subset hYsub, hYc]; omega)
      obtain ⟨v, hv_sd, hv_min⟩ := Finset.exists_min_image ((Finset.univ \ Xset) \ Y) (outDeg G Finset.univ) hne
      have hv_nY : v ∉ Y := (Finset.mem_sdiff.mp hv_sd).2
      refine ⟨insert v Y, Finset.insert_subset (Finset.sdiff_subset hv_sd) hYsub,
        by rw [Finset.card_insert_of_notMem hv_nY, hYc], fun u hu w hw => ?_⟩
      have hw_sd : w ∈ (Finset.univ \ Xset) \ Y := Finset.mem_sdiff.mpr
        ⟨(Finset.mem_sdiff.mp hw).1, fun h => (Finset.mem_sdiff.mp hw).2 (Finset.mem_insert_of_mem h)⟩
      rcases Finset.mem_insert.mp hu with rfl | huY
      · exact hv_min w hw_sd
      · exact hYmin u huY w hw_sd
  obtain ⟨Yset, hYset_sub, hYset_c, hYset_min⟩ := hex_low_out
  let eX : Fin (k * t) ≃ Xset := (Fintype.equivFinOfCardEq (by simp [hXset_c])).symm
  let eY : Fin (k * t) ≃ Yset := (Fintype.equivFinOfCardEq (by simp [hYset_c])).symm
  let x : Fin (k * t) → V := fun i => (eX i).1
  let y : Fin (k * t) → V := fun i => (eY i).1
  have hx_inj : Function.Injective x := fun i j h => eX.injective (Subtype.ext h)
  have hy_inj : Function.Injective y := fun i j h => eY.injective (Subtype.ext h)
  have himgX : Finset.univ.image x = Xset := by
    ext w; simp only [Finset.mem_image, Finset.mem_univ, true_and, x]
    constructor
    · rintro ⟨i, rfl⟩; exact (eX i).2
    · intro hw; exact ⟨eX.symm ⟨w, hw⟩, by simp⟩
  have himgY : Finset.univ.image y = Yset := by
    ext w; simp only [Finset.mem_image, Finset.mem_univ, true_and, y]
    constructor
    · rintro ⟨i, rfl⟩; exact (eY i).2
    · intro hw; exact ⟨eY.symm ⟨w, hw⟩, by simp⟩
  have hxy_disj : ∀ i j, x i ≠ y j := fun i j h => by
    change (eX i).1 = (eY j).1 at h
    exact (Finset.mem_sdiff.mp (hYset_sub (eY j).2)).2 (h ▸ (eX i).2)
  let reserved : Finset V := Xset ∪ Yset
  have hbuild_A : ∀ (r : ℕ) (hr : r ≤ k * t),
      ∃ (A : Fin r → List V) (EA : Fin r → Finset V),
        (∀ i, IsTransitiveList G (A i) ∧ (A i).length ≤ c ∧
          (∃ h : A i ≠ [], (A i).getLast h = x ⟨i.val, by omega⟩) ∧
          Disjoint ((A i).toFinset.erase (x ⟨i.val, by omega⟩)) reserved) ∧
        (∀ i j, i ≠ j → Disjoint (A i).toFinset (A j).toFinset) ∧
        (∀ i, Disjoint (EA i) (reserved ∪ Finset.univ.biUnion fun j => (A j).toFinset) ∧
          (∀ w ∈ EA i, ∀ a ∈ A i, G.Adj w a) ∧
          (∀ w ∈ Finset.univ \ (reserved ∪ (Finset.univ.biUnion fun j => (A j).toFinset) ∪ EA i),
            ∃ a ∈ A i, G.Adj a w) ∧
          2 ^ (c - 1) * (EA i).card ≤ inDeg G Finset.univ (x ⟨i.val, by omega⟩)) := by
    intro r
    induction r with
    | zero =>
      intro _; exact ⟨Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    | succ r ih =>
      intro hr
      obtain ⟨A', EA', hA', hdisj', hEA'⟩ := ih (by omega)
      let used : Finset V := reserved ∪ Finset.univ.biUnion fun j : Fin r => (A' j).toFinset
      let xr : V := x ⟨r, hr⟩
      let S_step : Finset V := insert xr (Finset.univ \ used)
      obtain ⟨Ar, Er_raw, hAr_tr, hAr_len, hAr_last, hAr_sub, hEr_sub, hEr_in, hAr_dom, hEr_card⟩ :=
        transitive_out_dom_set hT (Finset.mem_insert_self xr (Finset.univ \ used)) c
          (by dsimp [c]; exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega))
      let Er := Er_raw \ used
      have hAr_disj_used : Disjoint (Ar.toFinset.erase xr) used := by
        rw [Finset.disjoint_left]; intro w hw
        rw [Finset.mem_erase, List.mem_toFinset] at hw
        rcases Finset.mem_insert.mp (hAr_sub w hw.2) with rfl | hsd
        · exact absurd rfl hw.1
        · exact (Finset.mem_sdiff.mp hsd).2
      have hAr_disj_prev : ∀ j : Fin r, Disjoint Ar.toFinset (A' j).toFinset := by
        intro j; rw [Finset.disjoint_left]; intro w hw1 hw2
        by_cases hwx : w = xr
        · subst hwx
          have hxr_res : xr ∈ reserved := Finset.mem_union_left _ (eX ⟨r, hr⟩).2
          by_cases hweq : xr = x ⟨j.val, by omega⟩
          · have : r = j.val := congrArg (Fin.val : Fin (k * t) → ℕ) (hx_inj hweq); omega
          · exact Finset.disjoint_left.mp (hA' j).2.2.2 (Finset.mem_erase.mpr ⟨hweq, hw2⟩) hxr_res
        · exact Finset.disjoint_left.mp hAr_disj_used (Finset.mem_erase.mpr ⟨hwx, hw1⟩)
            (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hw2⟩))
      let A : Fin (r + 1) → List V := Fin.snoc A' Ar
      let EA : Fin (r + 1) → Finset V := Fin.snoc (fun j => EA' j \ Ar.toFinset) Er
      have hunion_eq : reserved ∪ (Finset.univ.biUnion fun j : Fin (r + 1) => (A j).toFinset) =
          used ∪ Ar.toFinset := by
        ext w; simp only [used, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
        constructor
        · rintro (hr_mem | ⟨j, hj⟩)
          · exact Or.inl (Or.inl hr_mem)
          · revert hj; refine Fin.lastCases ?_ (fun j' => ?_) j <;> intro hj
            · exact Or.inr (by simpa [A] using hj)
            · exact Or.inl (Or.inr ⟨j', by simpa [A] using hj⟩)
        · rintro ((hr_mem | ⟨j', hj'⟩) | hAr)
          · exact Or.inl hr_mem
          · exact Or.inr ⟨j'.castSucc, by simpa [A] using hj'⟩
          · exact Or.inr ⟨Fin.last r, by simpa [A] using hAr⟩
      refine ⟨A, EA, ?_, ?_, ?_⟩
      · intro i; refine Fin.lastCases ?_ (fun i' => ?_) i
        · simp only [A, Fin.snoc_last, Fin.val_last]
          exact ⟨hAr_tr, hAr_len, hAr_last,
            Finset.disjoint_of_subset_right Finset.subset_union_left hAr_disj_used⟩
        · simp only [A, Fin.snoc_castSucc, Fin.val_castSucc]
          exact hA' i'
      · intro i j
        refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;> intro hij
        · exact absurd rfl hij
        · simp only [A, Fin.snoc_last, Fin.snoc_castSucc]; exact hAr_disj_prev j'
        · simp only [A, Fin.snoc_last, Fin.snoc_castSucc]; exact (hAr_disj_prev i').symm
        · simp only [A, Fin.snoc_castSucc]; exact hdisj' i' j' (fun h => hij (congrArg Fin.castSucc h))
      · intro i; refine Fin.lastCases ?_ (fun i' => ?_) i
        · simp only [A, EA, Fin.snoc_last, Fin.val_last, hunion_eq]
          refine ⟨?_, fun w hw => hEr_in w (Finset.sdiff_subset hw), ?_, ?_⟩
          · rw [Finset.disjoint_union_right]
            exact ⟨disjoint_sdiff_self_left,
              Finset.disjoint_of_subset_left Finset.sdiff_subset
                (Finset.disjoint_of_subset_left hEr_sub disjoint_sdiff_self_left)⟩
          · intro w hw
            rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_union] at hw
            have hw_nused : w ∉ used := fun h => hw.2 (Or.inl (Or.inl h))
            have hw_nAr : w ∉ Ar.toFinset := fun h => hw.2 (Or.inl (Or.inr h))
            have hw_nEr : w ∉ Er_raw := fun h => hw.2 (Or.inr (Finset.mem_sdiff.mpr ⟨h, hw_nused⟩))
            exact hAr_dom w (Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hw_nused⟩),
              by simp [hw_nAr, hw_nEr]⟩)
          · have h1 : Er.card ≤ Er_raw.card := Finset.card_le_card Finset.sdiff_subset
            have h2 : inDeg G S_step xr ≤ inDeg G Finset.univ xr :=
              Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
            exact (Nat.mul_le_mul_left _ h1).trans (hEr_card.trans h2)
        · simp only [A, EA, Fin.snoc_castSucc, Fin.val_castSucc, hunion_eq]
          obtain ⟨hD', hIn', hDom', hC'⟩ := hEA' i'
          refine ⟨?_, fun w hw => hIn' w (Finset.sdiff_subset hw), ?_, ?_⟩
          · rw [Finset.disjoint_union_right]
            exact ⟨Finset.disjoint_of_subset_left Finset.sdiff_subset hD', disjoint_sdiff_self_left⟩
          · intro w hw
            rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_union] at hw
            have hw_nused : w ∉ used := fun h => hw.2 (Or.inl (Or.inl h))
            have hw_nAr : w ∉ Ar.toFinset := fun h => hw.2 (Or.inl (Or.inr h))
            have hw_nEA' : w ∉ EA' i' := fun h => hw.2 (Or.inr (Finset.mem_sdiff.mpr ⟨h, hw_nAr⟩))
            have hnu : w ∉ reserved ∧ ∀ j : Fin r, w ∉ A' j := by
              simp only [used, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and,
                List.mem_toFinset, not_or, not_exists] at hw_nused; exact hw_nused
            exact hDom' w (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [hnu.1, hnu.2, hw_nEA']⟩)
          · exact (Nat.mul_le_mul_left _ (Finset.card_le_card Finset.sdiff_subset)).trans hC'
  obtain ⟨A, EA_pre, hA_props, hA_disj, hEA_pre⟩ := hbuild_A (k * t) le_rfl
  let A_all : Finset V := Finset.univ.biUnion fun i => (A i).toFinset
  let resB : Finset V := reserved ∪ A_all
  have hbuild_B : ∀ (r : ℕ) (hr : r ≤ k * t),
      ∃ (B : Fin r → List V) (EB : Fin r → Finset V),
        (∀ i, IsTransitiveList G (B i) ∧ (B i).length ≤ c ∧
          (∃ h : B i ≠ [], (B i).head h = y ⟨i.val, by omega⟩) ∧
          Disjoint ((B i).toFinset.erase (y ⟨i.val, by omega⟩)) resB) ∧
        (∀ i j, i ≠ j → Disjoint (B i).toFinset (B j).toFinset) ∧
        (∀ i, Disjoint (EB i) (resB ∪ Finset.univ.biUnion fun j => (B j).toFinset) ∧
          (∀ w ∈ EB i, ∀ b ∈ B i, G.Adj b w) ∧
          (∀ w ∈ Finset.univ \ (resB ∪ (Finset.univ.biUnion fun j => (B j).toFinset) ∪ EB i),
            ∃ b ∈ B i, G.Adj w b) ∧
          2 ^ (c - 1) * (EB i).card ≤ outDeg G Finset.univ (y ⟨i.val, by omega⟩)) := by
    intro r
    induction r with
    | zero =>
      intro _; exact ⟨Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    | succ r ih =>
      intro hr
      obtain ⟨B', EB', hB', hdisj', hEB'⟩ := ih (by omega)
      let used : Finset V := resB ∪ Finset.univ.biUnion fun j : Fin r => (B' j).toFinset
      let yr : V := y ⟨r, hr⟩
      let S_step : Finset V := insert yr (Finset.univ \ used)
      obtain ⟨Br, Er_raw, hBr_tr, hBr_len, hBr_head, hBr_sub, hEr_sub, hEr_out, hBr_dom, hEr_card⟩ :=
        transitive_in_dom_set hT (Finset.mem_insert_self yr (Finset.univ \ used)) c
          (by dsimp [c]; exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega))
      let Er := Er_raw \ used
      have hBr_disj_used : Disjoint (Br.toFinset.erase yr) used := by
        rw [Finset.disjoint_left]; intro w hw
        rw [Finset.mem_erase, List.mem_toFinset] at hw
        rcases Finset.mem_insert.mp (hBr_sub w hw.2) with rfl | hsd
        · exact absurd rfl hw.1
        · exact (Finset.mem_sdiff.mp hsd).2
      have hBr_disj_prev : ∀ j : Fin r, Disjoint Br.toFinset (B' j).toFinset := by
        intro j; rw [Finset.disjoint_left]; intro w hw1 hw2
        by_cases hwy : w = yr
        · subst hwy
          have hyr_res : yr ∈ resB := Finset.mem_union_left _ (Finset.mem_union_right _ (eY ⟨r, hr⟩).2)
          by_cases hweq : yr = y ⟨j.val, by omega⟩
          · have : r = j.val := congrArg (Fin.val : Fin (k * t) → ℕ) (hy_inj hweq); omega
          · exact Finset.disjoint_left.mp (hB' j).2.2.2 (Finset.mem_erase.mpr ⟨hweq, hw2⟩) hyr_res
        · exact Finset.disjoint_left.mp hBr_disj_used (Finset.mem_erase.mpr ⟨hwy, hw1⟩)
            (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hw2⟩))
      let B : Fin (r + 1) → List V := Fin.snoc B' Br
      let EB : Fin (r + 1) → Finset V := Fin.snoc (fun j => EB' j \ Br.toFinset) Er
      have hunion_eq : resB ∪ (Finset.univ.biUnion fun j : Fin (r + 1) => (B j).toFinset) =
          used ∪ Br.toFinset := by
        ext w; simp only [used, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
        constructor
        · rintro (hr_mem | ⟨j, hj⟩)
          · exact Or.inl (Or.inl hr_mem)
          · revert hj; refine Fin.lastCases ?_ (fun j' => ?_) j <;> intro hj
            · exact Or.inr (by simpa [B] using hj)
            · exact Or.inl (Or.inr ⟨j', by simpa [B] using hj⟩)
        · rintro ((hr_mem | ⟨j', hj'⟩) | hBr)
          · exact Or.inl hr_mem
          · exact Or.inr ⟨j'.castSucc, by simpa [B] using hj'⟩
          · exact Or.inr ⟨Fin.last r, by simpa [B] using hBr⟩
      refine ⟨B, EB, ?_, ?_, ?_⟩
      · intro i; refine Fin.lastCases ?_ (fun i' => ?_) i
        · simp only [B, Fin.snoc_last, Fin.val_last]
          exact ⟨hBr_tr, hBr_len, hBr_head,
            Finset.disjoint_of_subset_right Finset.subset_union_left hBr_disj_used⟩
        · simp only [B, Fin.snoc_castSucc, Fin.val_castSucc]
          exact hB' i'
      · intro i j
        refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;> intro hij
        · exact absurd rfl hij
        · simp only [B, Fin.snoc_last, Fin.snoc_castSucc]; exact hBr_disj_prev j'
        · simp only [B, Fin.snoc_last, Fin.snoc_castSucc]; exact (hBr_disj_prev i').symm
        · simp only [B, Fin.snoc_castSucc]; exact hdisj' i' j' (fun h => hij (congrArg Fin.castSucc h))
      · intro i; refine Fin.lastCases ?_ (fun i' => ?_) i
        · simp only [B, EB, Fin.snoc_last, Fin.val_last, hunion_eq]
          refine ⟨?_, fun w hw => hEr_out w (Finset.sdiff_subset hw), ?_, ?_⟩
          · rw [Finset.disjoint_union_right]
            exact ⟨disjoint_sdiff_self_left,
              Finset.disjoint_of_subset_left Finset.sdiff_subset
                (Finset.disjoint_of_subset_left hEr_sub disjoint_sdiff_self_left)⟩
          · intro w hw
            rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_union] at hw
            have hw_nused : w ∉ used := fun h => hw.2 (Or.inl (Or.inl h))
            have hw_nBr : w ∉ Br.toFinset := fun h => hw.2 (Or.inl (Or.inr h))
            have hw_nEr : w ∉ Er_raw := fun h => hw.2 (Or.inr (Finset.mem_sdiff.mpr ⟨h, hw_nused⟩))
            exact hBr_dom w (Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hw_nused⟩),
              by simp [hw_nBr, hw_nEr]⟩)
          · have h1 : Er.card ≤ Er_raw.card := Finset.card_le_card Finset.sdiff_subset
            have h2 : outDeg G S_step yr ≤ outDeg G Finset.univ yr :=
              Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
            exact (Nat.mul_le_mul_left _ h1).trans (hEr_card.trans h2)
        · simp only [B, EB, Fin.snoc_castSucc, Fin.val_castSucc, hunion_eq]
          obtain ⟨hD', hOut', hDom', hC'⟩ := hEB' i'
          refine ⟨?_, fun w hw => hOut' w (Finset.sdiff_subset hw), ?_, ?_⟩
          · rw [Finset.disjoint_union_right]
            exact ⟨Finset.disjoint_of_subset_left Finset.sdiff_subset hD', disjoint_sdiff_self_left⟩
          · intro w hw
            rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_union] at hw
            have hw_nused : w ∉ used := fun h => hw.2 (Or.inl (Or.inl h))
            have hw_nBr : w ∉ Br.toFinset := fun h => hw.2 (Or.inl (Or.inr h))
            have hw_nEB' : w ∉ EB' i' := fun h => hw.2 (Or.inr (Finset.mem_sdiff.mpr ⟨h, hw_nBr⟩))
            have hnu : w ∉ resB ∧ ∀ j : Fin r, w ∉ B' j := by
              simp only [used, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and,
                List.mem_toFinset, not_or, not_exists] at hw_nused; exact hw_nused
            exact hDom' w (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [hnu.1, hnu.2, hw_nEB']⟩)
          · exact (Nat.mul_le_mul_left _ (Finset.card_le_card Finset.sdiff_subset)).trans hC'
  obtain ⟨B, EB_i, hB_props, hB_disj, hEB_props⟩ := hbuild_B (k * t) le_rfl
  let B_all : Finset V := Finset.univ.biUnion fun i => (B i).toFinset
  let D : Finset V := A_all ∪ B_all
  let EA_i : Fin (k * t) → Finset V := fun i => EA_pre i \ B_all
  have hAB_disj : ∀ i j, Disjoint (A i).toFinset (B j).toFinset := by
    intro i j; rw [Finset.disjoint_right]; intro w hwB hwA
    by_cases hwy : w = y j
    · subst hwy
      have hy_res : y j ∈ reserved := Finset.mem_union_right _ (eY j).2
      exact Finset.disjoint_left.mp (hA_props i).2.2.2
        (Finset.mem_erase.mpr ⟨(hxy_disj i j).symm, hwA⟩) hy_res
    · exact Finset.disjoint_left.mp (hB_props j).2.2.2 (Finset.mem_erase.mpr ⟨hwy, hwB⟩)
        (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hwA⟩))
  have hres_sub_D : reserved ⊆ D := by
    intro w hw; rcases Finset.mem_union.mp hw with hx | hy
    · rw [← himgX, Finset.mem_image] at hx; obtain ⟨i, _, rfl⟩ := hx
      obtain ⟨hne, hl⟩ := (hA_props i).2.2.1
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, List.mem_toFinset.mpr (hl ▸ List.getLast_mem hne)⟩)
    · rw [← himgY, Finset.mem_image] at hy; obtain ⟨i, _, rfl⟩ := hy
      obtain ⟨hne, hh⟩ := (hB_props i).2.2.1
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, List.mem_toFinset.mpr (hh ▸ List.head_mem hne)⟩)
  have hresB_D : resB ∪ B_all = D := by
    ext w; simp only [resB, D, Finset.mem_union]
    constructor
    · rintro ((h | h) | h); exact Finset.mem_union.mp (hres_sub_D h); exact Or.inl h; exact Or.inr h
    · rintro (h | h); exact Or.inl (Or.inr h); exact Or.inr h
  let EA : Finset V := Finset.univ.biUnion EA_i
  let EB : Finset V := Finset.univ.biUnion EB_i
  have hD_rev : ((Finset.univ.biUnion fun j => (B j).reverse.toFinset) ∪
      (Finset.univ.biUnion fun j => (A j).reverse.toFinset)) = D := by
    ext w
    simp only [D, A_all, B_all, Finset.mem_union, Finset.mem_biUnion, List.toFinset_reverse]
    exact or_comm
  by_cases hle : EA.card ≤ EB.card
  · apply kot_partition_wlog hk ht G hT hstrong x y A B EA_i EB_i hx_inj hy_inj hxy_disj
    · intro i u hu; rw [himgX, himgY] at hu
      exact hXset_min (x i) (eX i).2 u (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => hu (Finset.mem_union_left _ h)⟩)
    · intro i u hu; rw [himgX, himgY] at hu
      exact hYset_min (y i) (eY i).2 u (Finset.mem_sdiff.mpr
        ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => hu (Finset.mem_union_left _ h)⟩,
         fun h => hu (Finset.mem_union_right _ h)⟩)
    · intro i; exact ⟨(hA_props i).1, (hA_props i).2.1, (hA_props i).2.2.1⟩
    · intro i; exact ⟨(hB_props i).1, (hB_props i).2.1, (hB_props i).2.2.1⟩
    · exact hA_disj
    · exact hB_disj
    · exact hAB_disj
    · intro i; refine ⟨?_, fun w hw => (hEA_pre i).2.1 w (Finset.sdiff_subset hw)⟩
      rw [Finset.disjoint_union_right]
      exact ⟨Finset.disjoint_of_subset_left Finset.sdiff_subset
        (Finset.disjoint_of_subset_right Finset.subset_union_right (hEA_pre i).1), disjoint_sdiff_self_left⟩
    · intro i; refine ⟨?_, (hEB_props i).2.1⟩
      have h1 := (hEB_props i).1; change Disjoint (EB_i i) (resB ∪ B_all) at h1; rwa [hresB_D] at h1
    · intro i w hw
      rw [Finset.mem_sdiff, Finset.mem_union] at hw
      have hw_nD : w ∉ D := fun h => hw.2 (Or.inl h)
      have hw_nres : w ∉ reserved := fun h => hw_nD (hres_sub_D h)
      have hw_nA : w ∉ A_all := fun h => hw_nD (Finset.mem_union_left _ h)
      have hw_nB : w ∉ B_all := fun h => hw_nD (Finset.mem_union_right _ h)
      have hw_nEA : w ∉ EA_pre i := fun h => hw.2 (Or.inr (Finset.mem_sdiff.mpr ⟨h, hw_nB⟩))
      have hw_nA' : ∀ j : Fin (k * t), w ∉ A j := by
        simp only [A_all, Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_toFinset, not_exists] at hw_nA; exact hw_nA
      exact (hEA_pre i).2.2.1 w (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [hw_nres, hw_nA', hw_nEA]⟩)
    · intro i w hw
      have h1 := (hEB_props i).2.2.1 w
      change w ∈ Finset.univ \ ((resB ∪ B_all) ∪ EB_i i) → _ at h1
      rw [hresB_D] at h1
      exact h1 hw
    · intro i; exact (Nat.mul_le_mul_left _ (Finset.card_le_card Finset.sdiff_subset)).trans (hEA_pre i).2.2.2
    · intro i; exact (hEB_props i).2.2.2
    · exact hle
  · obtain ⟨part, hpart⟩ := kot_partition_wlog hk ht (opDigraph G) (isTournament_op hT)
      (isKStrongOn_op_iff.mpr hstrong) y x (fun i => (B i).reverse) (fun i => (A i).reverse) EB_i EA_i
      hy_inj hx_inj (fun i j => (hxy_disj j i).symm)
      (by intro i u hu
          have h1 : u ∉ Xset := fun h => hu (Finset.mem_union_right _ (himgX ▸ h))
          have h2 : u ∉ Yset := fun h => hu (Finset.mem_union_left _ (himgY ▸ h))
          rw [inDeg_op_eq_outDeg, inDeg_op_eq_outDeg]
          exact hYset_min (y i) (eY i).2 u (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h1⟩, h2⟩))
      (by intro i u hu
          have h1 : u ∉ Xset := fun h => hu (Finset.mem_union_right _ (himgX ▸ h))
          rw [outDeg_op_eq_inDeg, outDeg_op_eq_inDeg]
          exact hXset_min (x i) (eX i).2 u (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h1⟩))
      (by intro i
          obtain ⟨⟨hne, hnd, htr⟩, hlen, ⟨_, hh⟩, _⟩ := hB_props i
          refine ⟨⟨by simp [hne], List.nodup_reverse.mpr hnd, fun a b hab hb => ?_⟩,
            by simpa only [List.length_reverse] using hlen, ⟨by simp [hne], by simp [List.getLast_reverse, hh]⟩⟩
          rw [List.getElem_reverse, List.getElem_reverse]
          exact htr ((B i).length - 1 - b) ((B i).length - 1 - a) (by simp at hb; omega) (by simp at hb; omega))
      (by intro i
          obtain ⟨⟨hne, hnd, htr⟩, hlen, ⟨_, hl⟩, _⟩ := hA_props i
          refine ⟨⟨by simp [hne], List.nodup_reverse.mpr hnd, fun a b hab hb => ?_⟩,
            by simpa only [List.length_reverse] using hlen, ⟨by simp [hne], by simp [List.head_reverse, hl]⟩⟩
          rw [List.getElem_reverse, List.getElem_reverse]
          exact htr ((A i).length - 1 - b) ((A i).length - 1 - a) (by simp at hb; omega) (by simp at hb; omega))
      (by intro i j hij; simpa only [List.toFinset_reverse] using hB_disj i j hij)
      (by intro i j hij; simpa only [List.toFinset_reverse] using hA_disj i j hij)
      (by intro i j; simpa only [List.toFinset_reverse] using (hAB_disj j i).symm)
      (by intro i; rw [hD_rev]
          refine ⟨by have h1 := (hEB_props i).1; change Disjoint (EB_i i) (resB ∪ B_all) at h1; rwa [hresB_D] at h1,
            fun w hw b hb => (hEB_props i).2.1 w hw b (List.mem_reverse.mp hb)⟩)
      (by intro i; rw [hD_rev]
          refine ⟨by rw [Finset.disjoint_union_right]; exact ⟨Finset.disjoint_of_subset_left Finset.sdiff_subset
              (Finset.disjoint_of_subset_right Finset.subset_union_right (hEA_pre i).1), disjoint_sdiff_self_left⟩,
            fun w hw a ha => (hEA_pre i).2.1 w (Finset.sdiff_subset hw) a (List.mem_reverse.mp ha)⟩)
      (by intro i w hw; rw [hD_rev] at hw
          have h1 := (hEB_props i).2.2.1 w
          change w ∈ Finset.univ \ ((resB ∪ B_all) ∪ EB_i i) → _ at h1
          rw [hresB_D] at h1
          obtain ⟨b, hbB, hwb⟩ := h1 hw
          exact ⟨b, List.mem_reverse.mpr hbB, hwb⟩)
      (by intro i w hw; rw [hD_rev] at hw
          rw [Finset.mem_sdiff, Finset.mem_union] at hw
          have hw_nD : w ∉ D := fun h => hw.2 (Or.inl h)
          have hw_nres : w ∉ reserved := fun h => hw_nD (hres_sub_D h)
          have hw_nA : w ∉ A_all := fun h => hw_nD (Finset.mem_union_left _ h)
          have hw_nB : w ∉ B_all := fun h => hw_nD (Finset.mem_union_right _ h)
          have hw_nEA : w ∉ EA_pre i := fun h => hw.2 (Or.inr (Finset.mem_sdiff.mpr ⟨h, hw_nB⟩))
          have hw_nA' : ∀ j : Fin (k * t), w ∉ A j := by
            simp only [A_all, Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_toFinset, not_exists] at hw_nA; exact hw_nA
          obtain ⟨a, haA, haw⟩ := (hEA_pre i).2.2.1 w (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [hw_nres, hw_nA', hw_nEA]⟩)
          exact ⟨a, List.mem_reverse.mpr haA, haw⟩)
      (by intro i; rw [inDeg_op_eq_outDeg]; exact (hEB_props i).2.2.2)
      (by intro i; rw [outDeg_op_eq_inDeg]; exact (Nat.mul_le_mul_left _ (Finset.card_le_card Finset.sdiff_subset)).trans (hEA_pre i).2.2.2)
      (by change EB.card ≤ EA.card; omega)
    exact ⟨part, fun j => isKStrongOn_op_iff.mp (hpart j)⟩

end TournamentAPI

private lemma isKStrongOn_mono {V : Type} [Fintype V] {G : Digraph V} {S : Set V}
    {k₁ k₂ : ℕ} (hle : k₁ ≤ k₂) (h : IsKStrongOn G S k₂) : IsKStrongOn G S k₁ :=
  ⟨lt_of_le_of_lt hle h.1, fun X hX => h.2 X (lt_of_lt_of_le hX hle)⟩

theorem prove_main : type_of% @OMA.S_opg_partitionning_a_tournament_into_k_strongly_connected_subtournaments.main := by
  classical
  intro p k hp hk
  by_cases hp1 : p = 1
  · subst hp1
    refine ⟨max 2 (k ⟨0, by omega⟩), fun V _ G _ hstrong => ?_⟩
    refine ⟨fun _ => ⟨0, by omega⟩, fun i => ?_⟩
    have hi0 : i = ⟨0, by omega⟩ := Fin.ext (by omega)
    subst hi0
    have hpre : ((fun _ : V => (⟨0, by omega⟩ : Fin 1)) ⁻¹' {⟨0, by omega⟩}) = Set.univ := by
      ext v; simp
    rw [hpre]
    have h1 := isKStrongOn_mono (le_max_right 2 (k ⟨0, by omega⟩)) hstrong
    have h2 : 2 < (Set.univ : Set V).ncard := lt_of_le_of_lt (le_max_left 2 _) hstrong.1
    exact ⟨by omega, h1⟩
  · have hp2 : 2 ≤ p := by omega
    let K : ℕ := max 2 (Finset.univ.sup k)
    have hK2 : 2 ≤ K := le_max_left 2 _
    have hk_le_K : ∀ i : Fin p, k i ≤ K := fun i =>
      (Finset.le_sup (f := k) (Finset.mem_univ i)).trans (le_max_right 2 _)
    refine ⟨gKOT K p, fun V _ G hT hstrong => ?_⟩
    obtain ⟨part, hpart⟩ := kot_partition_uniform hT hK2 hp2 hstrong
    refine ⟨part, fun i => ?_⟩
    have hKi := hpart i
    exact ⟨by have := hKi.1; omega, isKStrongOn_mono (hk_le_K i) hKi⟩

end OMA.P_opg_partitionning_a_tournament_into_k_strongly_connected_subtournaments

theorem OMA.solution :
    type_of% @OMA.S_opg_partitionning_a_tournament_into_k_strongly_connected_subtournaments.main :=
  OMA.P_opg_partitionning_a_tournament_into_k_strongly_connected_subtournaments.prove_main
