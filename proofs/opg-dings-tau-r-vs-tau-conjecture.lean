import OMAStatements.S_opg_dings_tau_r_vs_tau_conjecture

/-!
The edge clutter of the nine-cycle is a counterexample to the stated version of
Ding's conjecture at multiplicity two. The definition of LehmanProperty in the
statement requires every inclusion-minimal transversal to have the same size.
The nine-cycle has minimal transversals of cardinalities five and six.
-/
-- Credit: @marcusbuffett

open Finset OMA.S_opg_dings_tau_r_vs_tau_conjecture

namespace OMA.OddCycleClutter

abbrev V := Fin 9
def edges : Finset (Finset V) := univ.image fun i : V => {i, i+1}

def C : Clutter V where
  ground := univ
  edges := edges
  sub := by simp
  antichain := by decide +kernel

def costs (r : ℕ) (H : Clutter V) : Set ℕ := {t | ∃ w : V → ℕ,
  (∀ v, v ∉ H.ground → w v = 0) ∧ (∀ A ∈ H.edges, r ≤ ∑ v ∈ A, w v) ∧
  ∑ v ∈ H.ground, w v = t}

theorem le_cost {r H t} (hw : t ∈ costs r H) : tauR r H ≤ t := Nat.sInf_le hw

theorem has_one {H : Clutter V} (h : 0 < tau H) : (costs 1 H).Nonempty := by
  by_contra! empty
  change 0 < sInf (costs 1 H) at h
  simp [empty] at h

set_option maxRecDepth 4096 in
/-- The all-ones vector is a double cover, while the support of any single cover has at least five vertices. -/
theorem gap_cycle : Gap 2 C := by
  have cert : ∀ s : Finset V, (∀ e ∈ edges, (e ∩ s).Nonempty) → 5 ≤ s.card := by decide +kernel
  have cover : 9 ∈ costs 2 C := by
    refine ⟨fun _ => 1, by simp [C], ?_, by decide⟩
    exact (by decide +kernel : ∀ e ∈ edges, 2 ≤ ∑ _v ∈ e, 1)
  have one : 9 ∈ costs 1 C := by
    refine ⟨fun _ => 1, by simp [C], ?_, by decide⟩
    exact (by decide +kernel : ∀ e ∈ edges, 1 ≤ ∑ _v ∈ e, 1)
  obtain ⟨w, _, hw, hc⟩ := Nat.sInf_mem (show (costs 1 C).Nonempty from ⟨9,one⟩)
  let s := univ.filter fun v : V => 0 < w v
  have hs : 5 ≤ s.card := by
    apply cert
    intro e he
    by_contra h
    have zero : ∀ v ∈ e, w v = 0 := by
      intro v hv
      by_contra hn
      exact h ⟨v, mem_inter.mpr ⟨hv, mem_filter.mpr ⟨mem_univ _, Nat.pos_of_ne_zero hn⟩⟩⟩
    have := hw e he
    rw [sum_eq_zero zero] at this
    omega
  have hle : s.card ≤ ∑ v : V, w v := by
    calc
      s.card = ∑ _v ∈ s, 1 := by simp
      _ ≤ ∑ v ∈ s, w v := sum_le_sum fun v hv => (mem_filter.mp hv).2
      _ ≤ ∑ v : V, w v := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; omega)
  change (∑ v : V, w v) = tau C at hc
  unfold Gap
  have := le_cost cover
  omega

def color (j v : V) : Bool := decide ((v-j).val % 2 = 0)

theorem subedge {X Y : Finset V} {e : Finset V} (he : e ∈ (minor C X Y).edges) :
    ∃ a ∈ edges, e ⊆ a := by
  simp only [minor, minimals, mem_filter, mem_image] at he
  obtain ⟨a, ⟨ha, _⟩, rfl⟩ := he.1
  exact ⟨a, ha, sdiff_subset⟩

/-- After deleting a ground vertex the surviving pairs lie on a path. Split a double cover into two single covers by assigning the vertices of weight one according to the path coloring. -/
theorem proper {X Y : Finset V} (hp : (X ∪ Y).Nonempty) : ¬ Gap 2 (minor C X Y) := by
  let H := minor C X Y
  change ¬ tauR 2 H < 2 * tau H
  intro h
  have pos : 0 < tau H := by omega
  obtain ⟨t, w, hw0, hw1, ht⟩ := has_one pos
  have ex : (costs 2 H).Nonempty := by
    refine ⟨_, fun v => 2 * w v, ?_, ?_, rfl⟩
    · intro v hv; simp [hw0 v hv]
    · intro e he
      rw [← mul_sum]
      have := hw1 e he
      omega
  obtain ⟨f, hf0, hf2, hsum⟩ := Nat.sInf_mem ex
  change (∑ v ∈ H.ground, f v) = tauR 2 H at hsum
  obtain ⟨j, hj⟩ := hp
  let pick (b : Bool) (v : V) : ℕ := if 2 ≤ f v ∨ (0 < f v ∧ color j v = b) then 1 else 0
  have cert : ∀ (j : V) (a : Finset V), a ∈ edges → ∀ b : Bool,
      (a.filter fun v => v ≠ j ∧ color j v = b).card ≤ 1 := by decide +kernel
  have bound (b : Bool) : tau H ≤ ∑ v ∈ H.ground, pick b v := by
    apply le_cost (r := 1)
    refine ⟨pick b, ?_, ?_, rfl⟩
    · intro v hv; simp [pick,hf0 v hv]
    · intro e he
      obtain ⟨a, ha, hea⟩ := subedge he
      have hmem (v) (hv : v ∈ e) : v ≠ j := by
        have hx := H.sub e he hv
        exact fun eq => (mem_sdiff.mp hx).2 (eq ▸ hj)
      by_contra! hz
      have none (v) (hv : v ∈ e) : pick b v = 0 := by
        have hsmall := single_le_sum (f := pick b) (fun _ _ => Nat.zero_le _) hv
        omega
      let s := a.filter fun v => v ≠ j ∧ color j v = !b
      have hb : ∑ v ∈ e, f v ≤ s.card := by
        calc
          _ ≤ ∑ v ∈ e, (if v ∈ s then 1 else 0) := by
            apply sum_le_sum
            intro v hv
            have hn := none v hv
            simp only [pick, ite_eq_right_iff, one_ne_zero, imp_false] at hn
            by_cases hzero : f v = 0
            · simp [hzero]
            have hcol : color j v = !b := by
              cases b <;> cases hh : color j v <;> simp_all
            have hvs : v ∈ s := mem_filter.mpr ⟨hea hv, hmem v hv, hcol⟩
            simp [hvs]
            omega
          _ ≤ ∑ v : V, (if v ∈ s then 1 else 0) :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; omega)
          _ = _ := by simp
      have hs : s.card ≤ 1 := cert j a ha (!b)
      have hf := hf2 e he
      omega
  have htotal : (∑ v ∈ H.ground, pick true v) + (∑ v ∈ H.ground, pick false v) ≤ ∑ v ∈ H.ground, f v := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro v _
    cases hh : color j v <;> simp [pick,hh] <;> split_ifs <;> omega
  have htrue := bound true
  have hfalse := bound false
  omega

/-- Every minor edge lies in an original pair. This rules out the large edge of a higher-order degenerate plane, and the absence of triangles rules out the remaining plane. -/
theorem no_j {k : ℕ} (hk : 2 ≤ k) : ¬ HasJMinor C k := by
  rintro ⟨X,Y,_,_,_,f,hf,_,_,h⟩
  have large := (h (univ.erase 0)).mp (Or.inr rfl)
  obtain ⟨a, ha, hsub⟩ := subedge large
  have hlen := card_le_card hsub
  have two : ∀ a ∈ edges, a.card = 2 := by decide +kernel
  rw [two a ha, card_image_of_injective _ hf, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at hlen
  obtain rfl : k = 2 := by omega
  let pair (u v : V) := ∃ t ∈ edges, ({u,v} : Finset V) ⊆ t
  have tri : ∀ u v w : V, u ≠ v → u ≠ w → v ≠ w → pair u v → pair u w → pair v w → False := by
    decide +kernel
  have edge (i j : Fin 3) (hij : ({i,j} : Finset (Fin 3)) ∈ jEdges 2) : pair (f i) (f j) := by
    obtain ⟨t, ht, sub⟩ := subedge ((h _).mp hij)
    exact ⟨t, ht, by simpa using sub⟩
  exact tri (f 0) (f 1) (f 2) (fun e => (by decide : (0 : Fin 3) ≠ 1) (hf e))
    (fun e => (by decide : (0 : Fin 3) ≠ 2) (hf e))
    (fun e => (by decide : (1 : Fin 3) ≠ 2) (hf e))
    (edge 0 1 (Or.inl ⟨1, by decide, rfl⟩))
    (edge 0 2 (Or.inl ⟨2, by decide, rfl⟩))
    (edge 1 2 (Or.inr (by decide)))

/-- The blocker contains two inclusion-minimal covers of unequal size. -/
theorem no_lehman : ¬ LehmanProperty C := by
  rintro ⟨_, A, B, _, _, _, hB, _, hsize, _⟩
  let small : Finset V := {0,2,4,6,8}
  let big : Finset V := {1,2,4,5,7,8}
  have hs : small ∈ (blocker C).edges := by decide +kernel
  have hb : big ∈ (blocker C).edges := by decide +kernel
  obtain ⟨i, hi⟩ := (hB _).mp hs
  obtain ⟨j, hj⟩ := (hB _).mp hb
  have he := (hsize i).trans (hsize j).symm
  rw [hi,hj] at he
  exact (by decide : small.card ≠ big.card) he

end OMA.OddCycleClutter

open OMA.OddCycleClutter in
theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_dings_tau_r_vs_tau_conjecture.main) := by
  intro h
  have hmin : MinorMinimalGap 2 C := ⟨gap_cycle, fun _ _ _ _ _ hp => proper hp⟩
  obtain ⟨k, hk, hj⟩ | hl := h V 2 (by decide) C hmin
  · exact no_j hk hj
  · exact no_lehman hl
