import OMAReductions.R_Erdos19_erdos_19_R1_H1_R1

/-!
Reduction Erdos19.erdos_19.R1.H1.R1.H1.R1 of step Erdos19.erdos_19.R1.H1.R1.H1.

We establish general structural and coloring results for completed finite linear spaces
with a critical core `S`:
1. Any linear space with `L.card ≤ n` is `n`-colorable (injective assignment).
2. Any linear space with at most two large blocks (`|L_3| ≤ 2`) is `n`-colorable
   via `EFLInterval.relabel_at_most_two` and `EFLInterval.color_family`.
3. Any linear space with `|L_3| = 3` having two disjoint large blocks is `n`-colorable
   by relabeling all three large blocks to intervals.
4. Symmetric-block modular coloring in `Fin n` (generalizing interval endpoint sums):
   if every large block `A` is closed under `x ↦ sym A - x` and intersecting large blocks
   have distinct `sym` values, then `L` is `n`-colorable.
5. Exact point-degree / excess identity `r(v) + ex(v) = n - 1` and critical pair-excess
   slack bound `ex(u) + ex(v) + miss(u) + miss(v) + 4 ≤ n` for `{u, v} ∈ S`.
6. Complete resolution of `n ≤ b.card + 3` for all `n` (no critical space with `|L_3| ≥ 3`).
7. Complete resolution of all orders `n ≤ 7` (combining `n ≤ b.card + 3` for `n ≤ 6`
   with a complete structural analysis and `Fin 7` modular coloring for `n = 7`).

The remaining target splits cleanly into three strictly reduced hypotheses:
- `H1`: orders `8 ≤ n ≤ 10` (with `n < L.card`, `3 ≤ |L_3|`, `∀ b ∈ L, b.card + 4 ≤ n`,
  and pairwise-intersecting large blocks when `|L_3| = 3`);
- `H2`: orders `n = 11` and `n = 12` under the same structural reductions;
- `H3`: the checked `n = 13` families under the same structural reductions (`∀ b ∈ L, b.card ≤ 9`).
-/

-- Credit: @sanchan

namespace OMA.R_Erdos19_erdos_19_R1_H1_R1_H1_R1

open scoped Classical

/- ### Part 1: Basic and general coloring lemmas -/

private theorem card_filter_add_card_filter_not {α : Type*} (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (s.filter p).card + (s.filter fun x => ¬ p x).card = s.card := by
  have hunion : s.filter p ∪ s.filter (fun x => ¬ p x) = s := by
    ext x; simp; tauto
  have hdisj : Disjoint (s.filter p) (s.filter fun x => ¬ p x) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_filter.mp hx2).2 (Finset.mem_filter.mp hx1).2
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

private theorem card_sdiff_sub {α : Type*} [DecidableEq α] {s t : Finset α} (h : s ⊆ t) :
    (t \ s).card = t.card - s.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h]

private theorem card_le_n_colorable {n : ℕ} (L : Finset (Finset (Fin n)))
    (hle : L.card ≤ n) :
    ∃ c : L → Fin n, ∀ A B : L, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B := by
  let e : L ≃ Fin L.card := Fintype.equivFinOfCardEq (Fintype.card_coe L)
  refine ⟨fun A => Fin.castLE hle (e A), ?_⟩
  intro A B hne _ heq
  exact hne (e.injective (Fin.ext (by simpa using congrArg Fin.val heq)))

theorem pullback_coloring {n : ℕ} (L : Finset (Finset (Fin n))) (e : Fin n ≃ Fin n)
    (hc : let K := L.image (Finset.map e.toEmbedding)
      ∃ c : K → Fin n, ∀ A B : K, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B) :
    ∃ c : L → Fin n, ∀ A B : L, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B := by
  let K := L.image (Finset.map e.toEmbedding)
  obtain ⟨c, proper⟩ := hc
  let f : L → K := fun A => ⟨A.val.map e.toEmbedding, Finset.mem_image_of_mem _ A.property⟩
  refine ⟨fun A => c (f A), ?_⟩
  intro A B hne hi
  apply proper (f A) (f B)
  · intro eq
    exact hne (Subtype.ext (Finset.map_injective _ (congrArg Subtype.val eq)))
  · obtain ⟨x, hx⟩ := hi
    exact ⟨e x, Finset.mem_inter.mpr ⟨Finset.mem_map_of_mem _ (Finset.mem_inter.mp hx).1,
      Finset.mem_map_of_mem _ (Finset.mem_inter.mp hx).2⟩⟩

theorem relabel_bounds {n : ℕ} (L : Finset (Finset (Fin n))) (e : Fin n ≃ Fin n)
    (hsize : ∀ a ∈ L, 2 ≤ a.card)
    (hlin : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → (a ∩ b).card ≤ 1) :
    let K := L.image (Finset.map e.toEmbedding)
    (∀ a ∈ K, 2 ≤ a.card) ∧ (∀ a ∈ K, ∀ b ∈ K, a ≠ b → (a ∩ b).card ≤ 1) := by
  constructor
  · intro a ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    simpa only [Finset.card_map] using hsize u hu
  · intro a ha b hb hne
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hb
    rw [← Finset.map_inter, Finset.card_map]
    exact hlin u hu w hw (fun eq => hne (congrArg (Finset.map e.toEmbedding) eq))

private theorem at_most_two_large_colorable {n : ℕ} (hn : 0 < n) (L : Finset (Finset (Fin n)))
    (hsize : ∀ a ∈ L, 2 ≤ a.card)
    (hlin : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → (a ∩ b).card ≤ 1)
    (hsmall : (L.filter fun b => 3 ≤ b.card).card ≤ 2) :
    ∃ c : L → Fin n, ∀ A B : L, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B := by
  obtain ⟨e, he⟩ := EFLInterval.relabel_at_most_two L hsmall
  obtain ⟨ksize, klin⟩ := relabel_bounds L e hsize hlin
  exact pullback_coloring L e (EFLInterval.color_family hn _ klin ksize he)

private theorem interval_of_convex {n : ℕ} (U : Finset (Fin n)) (hne : U.Nonempty)
    (hconv : ∀ a ∈ U, ∀ b ∈ U, ∀ x : Fin n, a ≤ x → x ≤ b → x ∈ U) :
    ∃ l r : Fin n, U = Finset.Icc l r := by
  refine ⟨U.min' hne, U.max' hne, ?_⟩
  ext x
  constructor
  · exact fun hx => Finset.mem_Icc.mpr ⟨U.min'_le x hx, U.le_max' x hx⟩
  · exact fun hx => hconv _ (U.min'_mem hne) _ (U.max'_mem hne) x
      (Finset.mem_Icc.mp hx).1 (Finset.mem_Icc.mp hx).2

/-- If `A` and `B` are disjoint, a single permutation maps `A`, `B`, and any third set `C`
to contiguous intervals in `Fin n`. -/
private theorem relabel_three_with_disjoint {n : ℕ} (A B C : Finset (Fin n))
    (hdisj : Disjoint A B) :
    ∃ e : Fin n ≃ Fin n, ∀ U : Finset (Fin n), U = A ∨ U = B ∨ U = C → U.Nonempty →
      ∃ l r : Fin n, U.map e.toEmbedding = Finset.Icc l r := by
  let tag (x : Fin n) : ℕ :=
    if x ∈ A then (if x ∈ C then 1 else 0)
    else if x ∈ B then (if x ∈ C then 3 else 4)
    else if x ∈ C then 2 else 5
  let key (x : Fin n) : ℕ := tag x * n + x.val
  have residue (x : Fin n) : key x % n = x.val := by
    simp [key, Nat.mod_eq_of_lt x.isLt]
  have inj : Function.Injective key := by
    intro x y h
    exact Fin.ext ((residue x).symm.trans ((congrArg (· % n) h).trans (residue y)))
  let emb : Fin n ↪ ℕ := ⟨key, inj⟩
  let T := (Finset.univ : Finset (Fin n)).map emb
  let t (x : Fin n) : T := ⟨key x, Finset.mem_map_of_mem emb (Finset.mem_univ x)⟩
  have bij : Function.Bijective t := by
    constructor
    · intro x y h
      exact inj (congrArg Subtype.val h)
    · intro y
      obtain ⟨x, _, hx⟩ := Finset.mem_map.mp y.property
      exact ⟨x, Subtype.ext hx⟩
  have cardT : T.card = n := by simp [T]
  let iso := T.orderIsoOfFin cardT
  let e := (Equiv.ofBijective t bij).trans iso.symm.toEquiv
  have back (x : Fin n) : iso (e x) = t x := iso.apply_symm_apply _
  have ordered (x y : Fin n) (h : e x ≤ e y) : tag x ≤ tag y := by
    have hkey := iso.monotone h
    rw [back, back] at hkey
    change tag x * n + x.val ≤ tag y * n + y.val at hkey
    by_contra! hbad
    have hh := Nat.mul_le_mul_right n (show tag y + 1 ≤ tag x by omega)
    rw [Nat.add_mul, one_mul] at hh
    have := y.isLt
    omega
  have not_both (x : Fin n) (hxA : x ∈ A) : x ∉ B := Finset.disjoint_left.mp hdisj hxA
  have memA (x : Fin n) : x ∈ A ↔ tag x ≤ 1 := by
    dsimp [tag]
    by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;> by_cases hC : x ∈ C <;> simp [hA, hB, hC]
  have memC (x : Fin n) : x ∈ C ↔ 1 ≤ tag x ∧ tag x ≤ 3 := by
    dsimp [tag]
    by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;> by_cases hC : x ∈ C <;> simp [hA, hB, hC]
  have memB (x : Fin n) : x ∈ B ↔ 3 ≤ tag x ∧ tag x ≤ 4 := by
    dsimp [tag]
    by_cases hA : x ∈ A
    · have hB := not_both x hA
      by_cases hC : x ∈ C <;> simp [hA, hB, hC]
    · by_cases hB : x ∈ B <;> by_cases hC : x ∈ C <;> simp [hA, hB, hC]
  refine ⟨e, ?_⟩
  intro U hU hne
  apply interval_of_convex _ hne.map
  intro a ha b hb x hl hr
  obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hb
  have h₁ := ordered u (e.symm x) (by simpa using hl)
  have h₂ := ordered (e.symm x) v (by simpa using hr)
  refine Finset.mem_map.mpr ⟨e.symm x, ?_, by simp⟩
  rcases hU with rfl | rfl | rfl
  · exact (memA _).mpr (h₂.trans ((memA _).mp hv))
  · exact (memB _).mpr ⟨((memB _).mp hu).1.trans h₁, h₂.trans ((memB _).mp hv).2⟩
  · exact (memC _).mpr ⟨((memC _).mp hu).1.trans h₁, h₂.trans ((memC _).mp hv).2⟩

theorem three_large_with_disjoint_colorable {n : ℕ} (hn : 0 < n)
    (L : Finset (Finset (Fin n)))
    (hsize : ∀ a ∈ L, 2 ≤ a.card)
    (hlin : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → (a ∩ b).card ≤ 1)
    (h3 : (L.filter fun b => 3 ≤ b.card).card = 3)
    (hdisj : ∃ A ∈ L.filter (fun b => 3 ≤ b.card),
      ∃ B ∈ L.filter (fun b => 3 ≤ b.card), Disjoint A B) :
    ∃ c : L → Fin n, ∀ A B : L, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B := by
  let F := L.filter fun b => 3 ≤ b.card
  obtain ⟨A, hAF, B, hBF, hAB⟩ := hdisj
  have hneAB : A ≠ B := by
    intro eq
    subst eq
    have hA3 : 3 ≤ A.card := (Finset.mem_filter.mp hAF).2
    have hAe : A = ∅ := disjoint_self.mp hAB
    rw [hAe] at hA3
    simp at hA3
  have hrem_card : ((F.erase A).erase B).card = 1 := by
    have hB' : B ∈ F.erase A := Finset.mem_erase.mpr ⟨hneAB.symm, hBF⟩
    rw [Finset.card_erase_of_mem hB', Finset.card_erase_of_mem hAF]
    have hF3 : F.card = 3 := h3
    omega
  obtain ⟨C, hCeq⟩ := Finset.card_eq_one.mp hrem_card
  have hcov : ∀ U ∈ F, U = A ∨ U = B ∨ U = C := by
    intro U hUF
    by_cases hUA : U = A
    · exact Or.inl hUA
    · by_cases hUB : U = B
      · exact Or.inr (Or.inl hUB)
      · right; right
        have hUin : U ∈ (F.erase A).erase B :=
          Finset.mem_erase.mpr ⟨hUB, Finset.mem_erase.mpr ⟨hUA, hUF⟩⟩
        rw [hCeq] at hUin
        exact Finset.mem_singleton.mp hUin
  obtain ⟨e, he⟩ := relabel_three_with_disjoint A B C hAB
  obtain ⟨ksize, klin⟩ := relabel_bounds L e hsize hlin
  apply pullback_coloring L e
  apply EFLInterval.color_family hn _ klin ksize
  intro S hS hs
  obtain ⟨U, hUL, rfl⟩ := Finset.mem_image.mp hS
  rw [Finset.card_map] at hs
  exact he U (hcov U (Finset.mem_filter.mpr ⟨hUL, hs⟩)) (Finset.card_pos.mp (by omega))

private theorem pair_min_add_max {n : ℕ} [NeZero n] {A : Finset (Fin n)} {x y : Fin n}
    (hcard : A.card = 2) (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) :
    A.min' ⟨x, hx⟩ + A.max' ⟨x, hx⟩ = x + y := by
  have hA : A = {x, y} := by
    apply Eq.symm
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)
    · rw [Finset.card_pair hxy, hcard]
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have hmin : A.min' ⟨x, hx⟩ = x := by
      apply le_antisymm (A.min'_le x hx)
      have hm : A.min' ⟨x, hx⟩ ∈ ({x, y} : Finset (Fin n)) := by rw [← hA]; exact A.min'_mem ⟨x, hx⟩
      rcases Finset.mem_insert.mp hm with h1 | h2
      · rw [h1]
      · rw [Finset.mem_singleton.mp h2]; exact hlt.le
    have hmax : A.max' ⟨x, hx⟩ = y := by
      apply le_antisymm _ (A.le_max' y hy)
      have hm : A.max' ⟨x, hx⟩ ∈ ({x, y} : Finset (Fin n)) := by rw [← hA]; exact A.max'_mem ⟨x, hx⟩
      rcases Finset.mem_insert.mp hm with h1 | h2
      · rw [h1]; exact hlt.le
      · rw [Finset.mem_singleton.mp h2]
    rw [hmin, hmax]
  · have hmin : A.min' ⟨x, hx⟩ = y := by
      apply le_antisymm (A.min'_le y hy)
      have hm : A.min' ⟨x, hx⟩ ∈ ({x, y} : Finset (Fin n)) := by rw [← hA]; exact A.min'_mem ⟨x, hx⟩
      rcases Finset.mem_insert.mp hm with h1 | h2
      · rw [h1]; exact hgt.le
      · rw [Finset.mem_singleton.mp h2]
    have hmax : A.max' ⟨x, hx⟩ = x := by
      apply le_antisymm _ (A.le_max' x hx)
      have hm : A.max' ⟨x, hx⟩ ∈ ({x, y} : Finset (Fin n)) := by rw [← hA]; exact A.max'_mem ⟨x, hx⟩
      rcases Finset.mem_insert.mp hm with h1 | h2
      · rw [h1]
      · rw [Finset.mem_singleton.mp h2]; exact hgt.le
    rw [hmin, hmax, add_comm]

/-- Symmetric-block modular coloring in `Fin n`: pairs receive the sum of their endpoints,
while each large block `A` receives its symmetry sum `sym A`. -/
theorem symmetric_modular_coloring {n : ℕ} (hn : 0 < n)
    (L : Finset (Finset (Fin n)))
    (hsize : ∀ a ∈ L, 2 ≤ a.card)
    (hlin : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → (a ∩ b).card ≤ 1)
    (sym : Finset (Fin n) → Fin n)
    (hsym : ∀ A ∈ L, 3 ≤ A.card → ∀ x ∈ A, sym A - x ∈ A)
    (hdist : ∀ A ∈ L, ∀ B ∈ L, 3 ≤ A.card → 3 ≤ B.card →
      A ≠ B → (A ∩ B).Nonempty → sym A ≠ sym B) :
    ∃ c : L → Fin n, ∀ A B : L, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B := by
  let _ : NeZero n := ⟨hn.ne'⟩
  have hne_of : ∀ a : L, a.val.Nonempty := fun a =>
    Finset.card_pos.mp (by have := hsize a.val a.property; omega)
  let c : L → Fin n := fun a =>
    if 3 ≤ a.val.card then sym a.val
    else a.val.min' (hne_of a) + a.val.max' (hne_of a)
  refine ⟨c, ?_⟩
  intro A B hne hmeet heq
  obtain ⟨x, hx⟩ := hmeet
  obtain ⟨hxA, hxB⟩ := Finset.mem_inter.mp hx
  have hvalne : A.val ≠ B.val := fun h => hne (Subtype.ext h)
  have hcap := hlin A.val A.property B.val B.property hvalne
  by_cases hA3 : 3 ≤ A.val.card <;> by_cases hB3 : 3 ≤ B.val.card
  · simp only [c, if_pos hA3, if_pos hB3] at heq
    exact hdist A.val A.property B.val B.property hA3 hB3 hvalne ⟨x, hx⟩ heq
  · have hB2 : B.val.card = 2 := by have := hsize B.val B.property; omega
    have hBe : (B.val.erase x).card = 1 := by rw [Finset.card_erase_of_mem hxB, hB2]
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hBe
    have hyB : y ∈ B.val := (Finset.mem_erase.mp (by rw [hy]; simp)).2
    have hyx : y ≠ x := (Finset.mem_erase.mp (by rw [hy]; simp)).1
    have hcolB : c B = x + y := by
      simp only [c, if_neg hB3]
      exact pair_min_add_max hB2 hxB hyB hyx.symm
    have hcolA : c A = sym A.val := by simp [c, hA3]
    have hsum : sym A.val = x + y := by rw [← hcolA, heq, hcolB]
    have hyA : y ∈ A.val := by
      have hsub := hsym A.val A.property hA3 x hxA
      rwa [hsum, add_sub_cancel_left] at hsub
    have h2 : 2 ≤ (A.val ∩ B.val).card := by
      calc 2 = ({x, y} : Finset (Fin n)).card := (Finset.card_pair hyx.symm).symm
        _ ≤ (A.val ∩ B.val).card := Finset.card_le_card (Finset.insert_subset
            (Finset.mem_inter.mpr ⟨hxA, hxB⟩)
            (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hyA, hyB⟩)))
    omega
  · have hA2 : A.val.card = 2 := by have := hsize A.val A.property; omega
    have hAe : (A.val.erase x).card = 1 := by rw [Finset.card_erase_of_mem hxA, hA2]
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hAe
    have hyA : y ∈ A.val := (Finset.mem_erase.mp (by rw [hy]; simp)).2
    have hyx : y ≠ x := (Finset.mem_erase.mp (by rw [hy]; simp)).1
    have hcolA : c A = x + y := by
      simp only [c, if_neg hA3]
      exact pair_min_add_max hA2 hxA hyA hyx.symm
    have hcolB : c B = sym B.val := by simp [c, hB3]
    have hsum : sym B.val = x + y := by rw [← hcolB, ← heq, hcolA]
    have hyB : y ∈ B.val := by
      have hsub := hsym B.val B.property hB3 x hxB
      rwa [hsum, add_sub_cancel_left] at hsub
    have h2 : 2 ≤ (A.val ∩ B.val).card := by
      calc 2 = ({x, y} : Finset (Fin n)).card := (Finset.card_pair hyx.symm).symm
        _ ≤ (A.val ∩ B.val).card := Finset.card_le_card (Finset.insert_subset
            (Finset.mem_inter.mpr ⟨hxA, hxB⟩)
            (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hyA, hyB⟩)))
    omega
  · have hA2 : A.val.card = 2 := by have := hsize A.val A.property; omega
    have hB2 : B.val.card = 2 := by have := hsize B.val B.property; omega
    have hAe : (A.val.erase x).card = 1 := by rw [Finset.card_erase_of_mem hxA, hA2]
    have hBe : (B.val.erase x).card = 1 := by rw [Finset.card_erase_of_mem hxB, hB2]
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hAe
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hBe
    have hyA : y ∈ A.val := (Finset.mem_erase.mp (by rw [hy]; simp)).2
    have hyx : y ≠ x := (Finset.mem_erase.mp (by rw [hy]; simp)).1
    have hzB : z ∈ B.val := (Finset.mem_erase.mp (by rw [hz]; simp)).2
    have hzx : z ≠ x := (Finset.mem_erase.mp (by rw [hz]; simp)).1
    have hcolA : c A = x + y := by
      simp only [c, if_neg hA3]
      exact pair_min_add_max hA2 hxA hyA hyx.symm
    have hcolB : c B = x + z := by
      simp only [c, if_neg hB3]
      exact pair_min_add_max hB2 hxB hzB hzx.symm
    have hyz : y = z := add_left_cancel (by rw [← hcolA, heq, hcolB])
    subst hyz
    have h2 : 2 ≤ (A.val ∩ B.val).card := by
      calc 2 = ({x, y} : Finset (Fin n)).card := (Finset.card_pair hyx.symm).symm
        _ ≤ (A.val ∩ B.val).card := Finset.card_le_card (Finset.insert_subset
            (Finset.mem_inter.mpr ⟨hxA, hxB⟩)
            (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hyA, hzB⟩)))
    omega

private theorem n7_subset_four_triples_colorable (L : Finset (Finset (Fin 7)))
    (hsize : ∀ a ∈ L, 2 ≤ a.card)
    (hlin : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → (a ∩ b).card ≤ 1)
    (hsub : ∀ a ∈ L, 3 ≤ a.card →
      a = ({0, 1, 2} : Finset (Fin 7)) ∨ a = {0, 3, 4} ∨ a = {0, 5, 6} ∨ a = {1, 3, 5}) :
    ∃ c : L → Fin 7, ∀ A B : L, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B := by
  let sym : Finset (Fin 7) → Fin 7 := fun a =>
    if a = {0, 1, 2} then 2
    else if a = {0, 3, 4} then 0
    else if a = {0, 5, 6} then 5
    else 6
  refine symmetric_modular_coloring (by omega) L hsize hlin sym ?_ ?_
  · intro A hA hA3 x hx
    rcases hsub A hA hA3 with rfl | rfl | rfl | rfl
    · revert x hx; decide
    · revert x hx; decide
    · revert x hx; decide
    · revert x hx; decide
  · intro A hA B hB hA3 hB3 hne _
    rcases hsub A hA hA3 with rfl | rfl | rfl | rfl <;>
      rcases hsub B hB hB3 with rfl | rfl | rfl | rfl <;>
      first | exact (hne rfl).elim | decide

/- ### Part 2: Linear-space point-degree, excess, and critical core slack -/

theorem point_degree_plus_excess {n : ℕ} (_hn : 0 < n)
    (L : Finset (Finset (Fin n)))
    (hsize : ∀ a ∈ L, 2 ≤ a.card)
    (hlin : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → (a ∩ b).card ≤ 1)
    (hcovers : ∀ i j : Fin n, i ≠ j → ∃ e ∈ L, i ∈ e ∧ j ∈ e)
    (v : Fin n) :
    (L.filter fun b => v ∈ b).card +
      ∑ b ∈ L.filter (fun b => 3 ≤ b.card ∧ v ∈ b), (b.card - 2) = n - 1 := by
  let Iv := L.filter fun b => v ∈ b
  have hpart : Iv.biUnion (fun b => b.erase v) = Finset.univ.erase v := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true, Iv]
    constructor
    · rintro ⟨_, _, hxv, _⟩; exact hxv
    · intro hxv
      obtain ⟨e, heL, hxe, hve⟩ := hcovers x v hxv
      exact ⟨e, ⟨heL, hve⟩, hxv, hxe⟩
  have hdisj : (Iv : Set (Finset (Fin n))).PairwiseDisjoint (fun b => b.erase v) := by
    intro a ha b hb hab
    change Disjoint (a.erase v) (b.erase v)
    rw [Finset.disjoint_left]
    intro x hxa hxb
    have haL : a ∈ L := (Finset.mem_filter.mp ha).1
    have hva : v ∈ a := (Finset.mem_filter.mp ha).2
    have hbL : b ∈ L := (Finset.mem_filter.mp hb).1
    have hvb : v ∈ b := (Finset.mem_filter.mp hb).2
    have hxv : x ≠ v := (Finset.mem_erase.mp hxa).1
    have hxa' : x ∈ a := (Finset.mem_erase.mp hxa).2
    have hxb' : x ∈ b := (Finset.mem_erase.mp hxb).2
    have h2 : 2 ≤ (a ∩ b).card := by
      calc 2 = ({v, x} : Finset (Fin n)).card := (Finset.card_pair hxv.symm).symm
        _ ≤ (a ∩ b).card := Finset.card_le_card (Finset.insert_subset
            (Finset.mem_inter.mpr ⟨hva, hvb⟩)
            (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hxa', hxb'⟩)))
    have hcap := hlin a haL b hbL hab
    omega
  have hcard : n - 1 = ∑ b ∈ Iv, (b.card - 1) := by
    calc n - 1 = (Finset.univ.erase v).card := by simp
      _ = (Iv.biUnion (fun b => b.erase v)).card := by rw [hpart]
      _ = ∑ b ∈ Iv, (b.erase v).card := Finset.card_biUnion hdisj
      _ = ∑ b ∈ Iv, (b.card - 1) := by
        refine Finset.sum_congr rfl fun b hb => ?_
        exact Finset.card_erase_of_mem (Finset.mem_filter.mp hb).2
  have hsplit : ∑ b ∈ Iv, (b.card - 1) = Iv.card + ∑ b ∈ Iv, (b.card - 2) := by
    have hterm : ∀ b ∈ Iv, b.card - 1 = 1 + (b.card - 2) := by
      intro b hb
      have := hsize b (Finset.mem_filter.mp hb).1
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  have hfilt : ∑ b ∈ Iv, (b.card - 2) =
      ∑ b ∈ L.filter (fun b => 3 ≤ b.card ∧ v ∈ b), (b.card - 2) := by
    have heq : Iv.filter (fun b => 3 ≤ b.card) = L.filter (fun b => 3 ≤ b.card ∧ v ∈ b) := by
      ext b; simp [Iv]; tauto
    rw [← heq]
    symm
    exact Finset.sum_filter_of_ne fun b _ hne => by omega
  dsimp only [Iv] at hcard hsplit hfilt
  omega

theorem block_degree_eq_sum {n : ℕ}
    (L S : Finset (Finset (Fin n))) (hSL : S ⊆ L)
    (hlin : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → (a ∩ b).card ≤ 1)
    {a : Finset (Fin n)} (ha : a ∈ S) :
    ((S.erase a).filter fun b => (a ∩ b).Nonempty).card =
      ∑ x ∈ a, ((S.filter fun b => x ∈ b).erase a).card := by
  have hunion : (S.erase a).filter (fun b => (a ∩ b).Nonempty) =
      a.biUnion (fun x => (S.filter fun b => x ∈ b).erase a) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_biUnion, Finset.Nonempty,
      Finset.mem_inter]
    constructor
    · rintro ⟨⟨hba, hbS⟩, x, hxa, hxb⟩
      exact ⟨x, hxa, hba, hbS, hxb⟩
    · rintro ⟨x, hxa, hba, hbS, hxb⟩
      exact ⟨⟨hba, hbS⟩, x, hxa, hxb⟩
  have hdisj : (a : Set (Fin n)).PairwiseDisjoint
      (fun x => (S.filter fun b => x ∈ b).erase a) := by
    intro x hx y hy hxy
    change Disjoint ((S.filter fun b => x ∈ b).erase a) ((S.filter fun b => y ∈ b).erase a)
    rw [Finset.disjoint_left]
    intro b hbx hby
    have hba : b ≠ a := (Finset.mem_erase.mp hbx).1
    have hbS : b ∈ S := (Finset.mem_filter.mp (Finset.mem_erase.mp hbx).2).1
    have hxb : x ∈ b := (Finset.mem_filter.mp (Finset.mem_erase.mp hbx).2).2
    have hyb : y ∈ b := (Finset.mem_filter.mp (Finset.mem_erase.mp hby).2).2
    have h2 : 2 ≤ (a ∩ b).card := by
      calc 2 = ({x, y} : Finset (Fin n)).card := (Finset.card_pair hxy).symm
        _ ≤ (a ∩ b).card := Finset.card_le_card (Finset.insert_subset
            (Finset.mem_inter.mpr ⟨hx, hxb⟩)
            (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hy, hyb⟩)))
    have hcap := hlin a (hSL ha) b (hSL hbS) hba.symm
    omega
  rw [hunion, Finset.card_biUnion hdisj]

/-- Fundamental critical pair-excess and slack inequality for a 2-block `{u, v} ∈ S`. -/
theorem pair_excess_and_slack {n : ℕ} (hn : 0 < n)
    (L S : Finset (Finset (Fin n))) (hSL : S ⊆ L)
    (hsize : ∀ a ∈ L, 2 ≤ a.card)
    (hlin : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → (a ∩ b).card ≤ 1)
    (hcovers : ∀ i j : Fin n, i ≠ j → ∃ e ∈ L, i ∈ e ∧ j ∈ e)
    (hcrit : ∀ a ∈ S, n ≤ ((S.erase a).filter fun b => (a ∩ b).Nonempty).card)
    {u v : Fin n} (huv : u ≠ v) (he : ({u, v} : Finset (Fin n)) ∈ S) :
    (∑ b ∈ L.filter (fun b => 3 ≤ b.card ∧ u ∈ b), (b.card - 2)) +
      (∑ b ∈ L.filter (fun b => 3 ≤ b.card ∧ v ∈ b), (b.card - 2)) +
      ((L \ S).filter fun b => u ∈ b).card +
      ((L \ S).filter fun b => v ∈ b).card + 4 ≤ n := by
  have hdeg := hcrit _ he
  rw [block_degree_eq_sum L S hSL hlin he, Finset.sum_pair huv] at hdeg
  have hsplit_pt : ∀ x : Fin n, ({u, v} : Finset (Fin n)) ∈ S.filter (fun b => x ∈ b) →
      ((S.filter fun b => x ∈ b).erase {u, v}).card + 1 +
      ((L \ S).filter fun b => x ∈ b).card +
      (∑ b ∈ L.filter (fun b => 3 ≤ b.card ∧ x ∈ b), (b.card - 2)) = n - 1 := by
    intro x hxmem
    have hpart : (S.filter fun b => x ∈ b) ∪ ((L \ S).filter fun b => x ∈ b) =
        L.filter fun b => x ∈ b := by
      ext b
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro (⟨hbS, hxb⟩ | ⟨⟨hbL, _⟩, hxb⟩)
        · exact ⟨hSL hbS, hxb⟩
        · exact ⟨hbL, hxb⟩
      · rintro ⟨hbL, hxb⟩
        by_cases hbS : b ∈ S
        · exact Or.inl ⟨hbS, hxb⟩
        · exact Or.inr ⟨⟨hbL, hbS⟩, hxb⟩
    have hdisj : Disjoint (S.filter fun b => x ∈ b) ((L \ S).filter fun b => x ∈ b) := by
      rw [Finset.disjoint_left]
      intro b hb1 hb2
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hb2).1).2 (Finset.mem_filter.mp hb1).1
    have hcard_union : (S.filter fun b => x ∈ b).card +
        ((L \ S).filter fun b => x ∈ b).card = (L.filter fun b => x ∈ b).card := by
      rw [← Finset.card_union_of_disjoint hdisj, hpart]
    have herase : ((S.filter fun b => x ∈ b).erase {u, v}).card + 1 =
        (S.filter fun b => x ∈ b).card := Finset.card_erase_add_one hxmem
    have hpt := point_degree_plus_excess hn L hsize hlin hcovers x
    omega
  have hu := hsplit_pt u (Finset.mem_filter.mpr ⟨he, by simp⟩)
  have hv := hsplit_pt v (Finset.mem_filter.mpr ⟨he, by simp⟩)
  omega

/-- Every block of `L` with `x ∈ a` and `a.card = 2` is of the form `{x, y}` with `y ≠ x`. -/
private theorem pair_block_eq {n : ℕ} {a : Finset (Fin n)} {x : Fin n}
    (hcard : a.card = 2) (hx : x ∈ a) :
    ∃ y : Fin n, y ≠ x ∧ a = {x, y} := by
  have he : (a.erase x).card = 1 := by rw [Finset.card_erase_of_mem hx, hcard]
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp he
  have hyin : y ∈ a.erase x := by rw [hy]; simp
  obtain ⟨hyx, hya⟩ := Finset.mem_erase.mp hyin
  refine ⟨y, hyx, ?_⟩
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · exact Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hya)
  · rw [Finset.card_pair hyx.symm, hcard]

/- ### Part 3: Complete resolution of `n ≤ B.card + 3` for all `n` -/

theorem large_block_gap_le_three_colorable {n : ℕ} (L : Finset (Finset (Fin n)))
    (hsize : ∀ a ∈ L, 2 ≤ a.card)
    (hlin : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → (a ∩ b).card ≤ 1)
    (hcovers : ∀ i j : Fin n, i ≠ j → ∃ e ∈ L, i ∈ e ∧ j ∈ e)
    (hcore : ∃ S ⊆ L, (∀ a ∈ L, 3 ≤ a.card → a ∈ S) ∧
      ∀ a ∈ S, n ≤ ((S.erase a).filter fun b => (a ∩ b).Nonempty).card)
    (hgap : ∃ B ∈ L, n ≤ B.card + 3) :
    ∃ c : L → Fin n, ∀ A B : L, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B := by
  by_cases hn0 : n = 0
  · subst hn0
    refine ⟨fun A => False.elim ?_, fun A => False.elim ?_⟩
    · have h1 := hsize A.val A.property
      have h2 : A.val.card ≤ 0 := by simpa using Finset.card_le_univ A.val
      omega
    · have h1 := hsize A.val A.property
      have h2 : A.val.card ≤ 0 := by simpa using Finset.card_le_univ A.val
      omega
  have hn : 0 < n := by omega
  let L3 := L.filter fun b => 3 ≤ b.card
  by_cases hL3_small : L3.card ≤ 2
  · exact at_most_two_large_colorable hn L hsize hlin hL3_small
  exfalso
  have hL3_ge3 : 3 ≤ L3.card := by omega
  obtain ⟨S, hSL, hL3S, hcrit⟩ := hcore
  obtain ⟨B0, hB0L, hB0gap⟩ := hgap
  -- Ensure we have a block `B ∈ L3` with `n ≤ B.card + 3`.
  have hB_ex : ∃ B ∈ L3, n ≤ B.card + 3 := by
    by_cases hB03 : 3 ≤ B0.card
    · exact ⟨B0, Finset.mem_filter.mpr ⟨hB0L, hB03⟩, hB0gap⟩
    · have hne : L3.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨B, hBL3⟩ := hne
      have hB3 := (Finset.mem_filter.mp hBL3).2
      exact ⟨B, hBL3, by omega⟩
  obtain ⟨B, hBL3, hBgap⟩ := hB_ex
  have hBL : B ∈ L := (Finset.mem_filter.mp hBL3).1
  have hB3 : 3 ≤ B.card := (Finset.mem_filter.mp hBL3).2
  let W : Finset (Fin n) := Finset.univ \ B
  have hWcard_eq : W.card + B.card = n := by
    have hsub : B ⊆ Finset.univ := Finset.subset_univ B
    have := card_sdiff_sub hsub
    have hBc : B.card ≤ n := by simpa using Finset.card_le_univ B
    simp only [W, Finset.card_univ, Fintype.card_fin] at this ⊢
    omega
  have hWle3 : W.card ≤ 3 := by omega
  -- Every large block other than `B` has at least 2 points in `W`.
  have hA_in_W : ∀ A ∈ L3.erase B, 2 ≤ (A ∩ W).card := by
    intro A hA
    have hAB : A ≠ B := (Finset.mem_erase.mp hA).1
    have hAL3 : A ∈ L3 := (Finset.mem_erase.mp hA).2
    have hAL : A ∈ L := (Finset.mem_filter.mp hAL3).1
    have hA3 : 3 ≤ A.card := (Finset.mem_filter.mp hAL3).2
    have hcap := hlin A hAL B hBL hAB
    have hsplit : (A ∩ B).card + (A ∩ W).card = A.card := by
      have hunion : (A ∩ B) ∪ (A ∩ W) = A := by
        ext x; simp [W]; tauto
      have hdisj : Disjoint (A ∩ B) (A ∩ W) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx2).2).2 (Finset.mem_inter.mp hx1).2
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    omega
  have hrem_ge2 : 2 ≤ (L3.erase B).card := by
    rw [Finset.card_erase_of_mem hBL3]; omega
  obtain ⟨A1, hA1rem, A2, hA2rem, hA12⟩ := Finset.one_lt_card.mp (by omega : 1 < (L3.erase B).card)
  -- No block in `L3.erase B` can cover all of `W`, hence `W.card = 3` and each meets `W` in 2 points.
  have hAW_lt : ∀ A ∈ L3.erase B, (A ∩ W).card < W.card := by
    intro A hA
    have hle : (A ∩ W).card ≤ W.card := Finset.card_le_card Finset.inter_subset_right
    by_contra! hge
    have hAW_eq : A ∩ W = W := Finset.eq_of_subset_of_card_le Finset.inter_subset_right hge
    have hWsubA : W ⊆ A := hAW_eq ▸ Finset.inter_subset_left
    have hother : ∃ A' ∈ L3.erase B, A' ≠ A := by
      by_cases h1 : A1 = A
      · exact ⟨A2, hA2rem, h1 ▸ hA12.symm⟩
      · exact ⟨A1, hA1rem, h1⟩
    obtain ⟨A', hA'rem, hA'ne⟩ := hother
    have h2 : 2 ≤ (A' ∩ W).card := hA_in_W A' hA'rem
    have hsub : A' ∩ W ⊆ A' ∩ A := Finset.inter_subset_inter_left hWsubA
    have hcap := hlin A' (Finset.mem_filter.mp (Finset.mem_erase.mp hA'rem).2).1
      A (Finset.mem_filter.mp (Finset.mem_erase.mp hA).2).1 hA'ne
    have := Finset.card_le_card hsub
    omega
  have hWcard : W.card = 3 := by
    have h1 := hA_in_W A1 hA1rem
    have h2 := hAW_lt A1 hA1rem
    omega
  have hBcard : B.card = n - 3 := by omega
  have hn_ge6 : 6 ≤ n := by omega
  have hAW2 : ∀ A ∈ L3.erase B, (A ∩ W).card = 2 ∧ (A ∩ B).card = 1 ∧ A.card = 3 := by
    intro A hA
    have h1 := hA_in_W A hA
    have h2 := hAW_lt A hA
    have hAW : (A ∩ W).card = 2 := by omega
    have hAB : A ≠ B := (Finset.mem_erase.mp hA).1
    have hAL3 := (Finset.mem_erase.mp hA).2
    have hAL := (Finset.mem_filter.mp hAL3).1
    have hA3 := (Finset.mem_filter.mp hAL3).2
    have hcap := hlin A hAL B hBL hAB
    have hsplit : (A ∩ B).card + (A ∩ W).card = A.card := by
      have hunion : (A ∩ B) ∪ (A ∩ W) = A := by ext x; simp [W]; tauto
      have hdisj : Disjoint (A ∩ B) (A ∩ W) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx2).2).2 (Finset.mem_inter.mp hx1).2
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    omega
  -- Map `A ↦ A ∩ W` injects `L3.erase B` into `W.powersetCard 2` (size 3).
  have hrem_le3 : (L3.erase B).card ≤ 3 := by
    have hinj : Set.InjOn (fun A => A ∩ W) (L3.erase B : Set (Finset (Fin n))) := by
      intro X hX Y hY hXY
      dsimp only at hXY
      by_contra hne
      have hX2 := (hAW2 X hX).1
      have hsub : X ∩ W ⊆ X ∩ Y := by
        intro x hx
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
          (Finset.mem_inter.mp (by rw [← hXY]; exact hx)).1⟩
      have hcap := hlin X (Finset.mem_filter.mp (Finset.mem_erase.mp hX).2).1
        Y (Finset.mem_filter.mp (Finset.mem_erase.mp hY).2).1 hne
      have := Finset.card_le_card hsub
      omega
    have himg : (L3.erase B).image (fun A => A ∩ W) ⊆ W.powersetCard 2 := by
      intro P hP
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hP
      exact Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, (hAW2 A hA).1⟩
    calc (L3.erase B).card
        = ((L3.erase B).image (fun A => A ∩ W)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (W.powersetCard 2).card := Finset.card_le_card himg
      _ = Nat.choose W.card 2 := Finset.card_powersetCard 2 W
      _ = 3 := by rw [hWcard]; decide
  -- Excess lower bounds on `B` and `W`.
  let ex (x : Fin n) : ℕ := ∑ b ∈ L.filter (fun b => 3 ≤ b.card ∧ x ∈ b), (b.card - 2)
  have hex_B : ∀ y ∈ B, n - 5 ≤ ex y := by
    intro y hy
    have hmem : B ∈ L.filter (fun b => 3 ≤ b.card ∧ y ∈ b) :=
      Finset.mem_filter.mpr ⟨hBL, hB3, hy⟩
    have hle := Finset.single_le_sum (f := fun b : Finset (Fin n) => b.card - 2)
      (fun _ _ => Nat.zero_le _) hmem
    dsimp only [ex]
    omega
  have hex_B_extra : ∀ y ∈ B, ∀ A ∈ L3.erase B, y ∈ A → n - 4 ≤ ex y := by
    intro y hy A hA hyA
    have hAB : A ≠ B := (Finset.mem_erase.mp hA).1
    have hAL3 := (Finset.mem_erase.mp hA).2
    have hAL := (Finset.mem_filter.mp hAL3).1
    have hA3 := (Finset.mem_filter.mp hAL3).2
    have hsub : ({B, A} : Finset (Finset (Fin n))) ⊆ L.filter (fun b => 3 ≤ b.card ∧ y ∈ b) := by
      refine Finset.insert_subset (Finset.mem_filter.mpr ⟨hBL, hB3, hy⟩) ?_
      exact Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr ⟨hAL, hA3, hyA⟩)
    have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun b : Finset (Fin n) => b.card - 2)
      hsub (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_pair hAB.symm] at hle
    dsimp only [ex]
    omega
  have hex_W_one : ∀ u ∈ W, ∀ A ∈ L3.erase B, u ∈ A → 1 ≤ ex u := by
    intro u _ A hA huA
    have hAL3 := (Finset.mem_erase.mp hA).2
    have hmem : A ∈ L.filter (fun b => 3 ≤ b.card ∧ u ∈ b) :=
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hAL3).1, (Finset.mem_filter.mp hAL3).2, huA⟩
    have hle := Finset.single_le_sum (f := fun b : Finset (Fin n) => b.card - 2)
      (fun _ _ => Nat.zero_le _) hmem
    have hA3 := (Finset.mem_filter.mp hAL3).2
    dsimp only [ex]
    omega
  have hex_W_two : ∀ u ∈ W, ∀ X ∈ L3.erase B, ∀ Y ∈ L3.erase B, X ≠ Y →
      u ∈ X → u ∈ Y → 2 ≤ ex u := by
    intro u _ X hX Y hY hXY huX huY
    have hXL3 := (Finset.mem_erase.mp hX).2
    have hYL3 := (Finset.mem_erase.mp hY).2
    have hsub : ({X, Y} : Finset (Finset (Fin n))) ⊆ L.filter (fun b => 3 ≤ b.card ∧ u ∈ b) := by
      refine Finset.insert_subset
        (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hXL3).1, (Finset.mem_filter.mp hXL3).2, huX⟩) ?_
      exact Finset.singleton_subset_iff.mpr
        (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hYL3).1, (Finset.mem_filter.mp hYL3).2, huY⟩)
    have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun b : Finset (Fin n) => b.card - 2)
      hsub (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_pair hXY] at hle
    have hX3 := (Finset.mem_filter.mp hXL3).2
    have hY3 := (Finset.mem_filter.mp hYL3).2
    dsimp only [ex]
    omega
  -- Split on `(L3.erase B).card = 3` vs `(L3.erase B).card = 2`.
  rcases (show (L3.erase B).card = 3 ∨ (L3.erase B).card = 2 by omega) with h3 | h2
  · -- Case 1: 3 triples meet `W` in all 3 pairs of `W`, so every `u ∈ W` has `ex u ≥ 2`.
    have himg_eq : (L3.erase B).image (fun A => A ∩ W) = W.powersetCard 2 := by
      have hinj : Set.InjOn (fun A => A ∩ W) (L3.erase B : Set (Finset (Fin n))) := by
        intro X hX Y hY hXY
        dsimp only at hXY
        by_contra hne
        have hX2 := (hAW2 X hX).1
        have hsub : X ∩ W ⊆ X ∩ Y := fun x hx => Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp (by rw [← hXY]; exact hx)).1⟩
        have hcap := hlin X (Finset.mem_filter.mp (Finset.mem_erase.mp hX).2).1
          Y (Finset.mem_filter.mp (Finset.mem_erase.mp hY).2).1 hne
        have := Finset.card_le_card hsub
        omega
      apply Finset.eq_of_subset_of_card_le
      · intro P hP
        obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hP
        exact Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, (hAW2 A hA).1⟩
      · rw [Finset.card_image_of_injOn hinj, h3, Finset.card_powersetCard, hWcard]
        decide
    have hW_ex2 : ∀ u ∈ W, 2 ≤ ex u := by
      intro u hu
      have hWe : (W.erase u).card = 2 := by rw [Finset.card_erase_of_mem hu, hWcard]
      obtain ⟨v1, v2, hv12, hWeq⟩ := Finset.card_eq_two.mp hWe
      have hv1W : v1 ∈ W := (Finset.mem_erase.mp (by rw [hWeq]; simp)).2
      have hv1u : v1 ≠ u := (Finset.mem_erase.mp (by rw [hWeq]; simp)).1
      have hv2W : v2 ∈ W := (Finset.mem_erase.mp (by rw [hWeq]; simp)).2
      have hv2u : v2 ≠ u := (Finset.mem_erase.mp (by rw [hWeq]; simp)).1
      have hp1 : ({u, v1} : Finset (Fin n)) ∈ (L3.erase B).image (fun A => A ∩ W) := by
        rw [himg_eq]
        exact Finset.mem_powersetCard.mpr
          ⟨Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv1W),
           Finset.card_pair hv1u.symm⟩
      have hp2 : ({u, v2} : Finset (Fin n)) ∈ (L3.erase B).image (fun A => A ∩ W) := by
        rw [himg_eq]
        exact Finset.mem_powersetCard.mpr
          ⟨Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv2W),
           Finset.card_pair hv2u.symm⟩
      obtain ⟨X, hX, hXW⟩ := Finset.mem_image.mp hp1
      obtain ⟨Y, hY, hYW⟩ := Finset.mem_image.mp hp2
      have hXY : X ≠ Y := by
        intro eq; subst eq
        have : v1 ∈ ({u, v2} : Finset (Fin n)) := by rw [← hYW, hXW]; simp
        simp [hv1u, hv12] at this
      exact hex_W_two u hu X hX Y hY hXY
        (Finset.mem_inter.mp (by rw [hXW]; simp)).1
        (Finset.mem_inter.mp (by rw [hYW]; simp)).1
    -- Every block in `(S.erase B).filter (meets B)` must lie in `L3.erase B` (no `S`-edges cross `B` and `W`).
    have hsub_deg : (S.erase B).filter (fun b => (B ∩ b).Nonempty) ⊆ L3.erase B := by
      intro b hb
      obtain ⟨hbSe, y, hyBb⟩ := Finset.mem_filter.mp hb
      obtain ⟨hbB, hbS⟩ := Finset.mem_erase.mp hbSe
      obtain ⟨hyB, hyb⟩ := Finset.mem_inter.mp hyBb
      have hbL : b ∈ L := hSL hbS
      by_cases hb3 : 3 ≤ b.card
      · exact Finset.mem_erase.mpr ⟨hbB, Finset.mem_filter.mpr ⟨hbL, hb3⟩⟩
      · exfalso
        have hb2 : b.card = 2 := by have := hsize b hbL; omega
        obtain ⟨u, huy, rfl⟩ := pair_block_eq hb2 hyb
        have huW : u ∈ W := by
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, ?_⟩
          intro huB
          have h2' : 2 ≤ (B ∩ {y, u}).card := by
            calc 2 = ({y, u} : Finset (Fin n)).card := (Finset.card_pair huy.symm).symm
              _ ≤ (B ∩ {y, u}).card := Finset.card_le_card (Finset.insert_subset
                  (Finset.mem_inter.mpr ⟨hyB, by simp⟩)
                  (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨huB, by simp⟩)))
          have := hlin B hBL {y, u} hbL hbB.symm
          omega
        have hslack := pair_excess_and_slack hn L S hSL hsize hlin hcovers hcrit huy.symm hbS
        have hyex := hex_B y hyB
        have huex := hW_ex2 u huW
        change ex y + ex u + _ + _ + 4 ≤ n at hslack
        omega
    have hBS : B ∈ S := hL3S B hBL hB3
    have hdegB := hcrit B hBS
    have hle := Finset.card_le_card hsub_deg
    omega
  · -- Case 2: `(L3.erase B).card = 2`, write `L3.erase B = {A1, A2}` and bound `d_S(A1) ≤ n - 2`.
    have hL3_eq : L3.erase B = {A1, A2} := by
      apply Eq.symm
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.insert_subset hA1rem (Finset.singleton_subset_iff.mpr hA2rem)
      · rw [Finset.card_pair hA12, h2]
    have hA1L3 : A1 ∈ L3 := (Finset.mem_erase.mp hA1rem).2
    have hA2L3 : A2 ∈ L3 := (Finset.mem_erase.mp hA2rem).2
    have hA1L : A1 ∈ L := (Finset.mem_filter.mp hA1L3).1
    have hA2L : A2 ∈ L := (Finset.mem_filter.mp hA2L3).1
    have hA1B : A1 ≠ B := (Finset.mem_erase.mp hA1rem).1
    have hA2B : A2 ≠ B := (Finset.mem_erase.mp hA2rem).1
    have hA1W2 := (hAW2 A1 hA1rem).1
    have hA2W2 := (hAW2 A2 hA2rem).1
    have hA1B1 := (hAW2 A1 hA1rem).2.1
    have hA2B1 := (hAW2 A2 hA2rem).2.1
    -- `A1 ∩ W` and `A2 ∩ W` are two 2-subsets of the 3-set `W`, so they meet in a unique `u0`.
    have hinter_pos : 1 ≤ ((A1 ∩ W) ∩ (A2 ∩ W)).card := by
      have hun := Finset.card_union_add_card_inter (A1 ∩ W) (A2 ∩ W)
      have hsub : (A1 ∩ W) ∪ (A2 ∩ W) ⊆ W :=
        Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
      have hle := Finset.card_le_card hsub
      omega
    obtain ⟨u0, hu0⟩ := Finset.card_pos.mp (by omega : 0 < ((A1 ∩ W) ∩ (A2 ∩ W)).card)
    have hu0A1 : u0 ∈ A1 := (Finset.mem_inter.mp (Finset.mem_inter.mp hu0).1).1
    have hu0W : u0 ∈ W := (Finset.mem_inter.mp (Finset.mem_inter.mp hu0).1).2
    have hu0A2 : u0 ∈ A2 := (Finset.mem_inter.mp (Finset.mem_inter.mp hu0).2).1
    have hu0A1W : u0 ∈ A1 ∩ W := Finset.mem_inter.mpr ⟨hu0A1, hu0W⟩
    have hu0A2W : u0 ∈ A2 ∩ W := Finset.mem_inter.mpr ⟨hu0A2, hu0W⟩
    obtain ⟨u1, hu1eq⟩ := Finset.card_eq_one.mp (by rw [Finset.card_erase_of_mem hu0A1W, hA1W2])
    obtain ⟨u2, hu2eq⟩ := Finset.card_eq_one.mp (by rw [Finset.card_erase_of_mem hu0A2W, hA2W2])
    have hu1_in : u1 ∈ (A1 ∩ W).erase u0 := by rw [hu1eq]; simp
    have hu2_in : u2 ∈ (A2 ∩ W).erase u0 := by rw [hu2eq]; simp
    have hu10 : u1 ≠ u0 := (Finset.mem_erase.mp hu1_in).1
    have hu1A1 : u1 ∈ A1 := (Finset.mem_inter.mp (Finset.mem_erase.mp hu1_in).2).1
    have hu1W : u1 ∈ W := (Finset.mem_inter.mp (Finset.mem_erase.mp hu1_in).2).2
    have hu20 : u2 ≠ u0 := (Finset.mem_erase.mp hu2_in).1
    have hu2A2 : u2 ∈ A2 := (Finset.mem_inter.mp (Finset.mem_erase.mp hu2_in).2).1
    have hu2W : u2 ∈ W := (Finset.mem_inter.mp (Finset.mem_erase.mp hu2_in).2).2
    have hu12 : u1 ≠ u2 := by
      intro eq; subst eq
      have h2' : 2 ≤ (A1 ∩ A2).card := by
        calc 2 = ({u0, u1} : Finset (Fin n)).card := (Finset.card_pair hu10.symm).symm
          _ ≤ (A1 ∩ A2).card := Finset.card_le_card (Finset.insert_subset
              (Finset.mem_inter.mpr ⟨hu0A1, hu0A2⟩)
              (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hu1A1, hu2A2⟩)))
      have := hlin A1 hA1L A2 hA2L hA12
      omega
    have hW_eq : W = {u0, u1, u2} := by
      apply Eq.symm
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.insert_subset hu0W (Finset.insert_subset hu1W
          (Finset.singleton_subset_iff.mpr hu2W))
      · rw [Finset.card_insert_of_notMem (by simp [hu10.symm, hu20.symm]),
            Finset.card_pair hu12, hWcard]
    obtain ⟨x1, hx1eq⟩ := Finset.card_eq_one.mp hA1B1
    obtain ⟨x2, hx2eq⟩ := Finset.card_eq_one.mp hA2B1
    have hx1A1 : x1 ∈ A1 := (Finset.mem_inter.mp (by rw [hx1eq]; simp)).1
    have hx1B : x1 ∈ B := (Finset.mem_inter.mp (by rw [hx1eq]; simp)).2
    have hx2A2 : x2 ∈ A2 := (Finset.mem_inter.mp (by rw [hx2eq]; simp)).1
    have hx2B : x2 ∈ B := (Finset.mem_inter.mp (by rw [hx2eq]; simp)).2
    have hx12 : x1 ≠ x2 := by
      intro eq; subst eq
      have hx1u0 : x1 ≠ u0 := fun h => (Finset.mem_sdiff.mp hu0W).2 (h ▸ hx1B)
      have h2' : 2 ≤ (A1 ∩ A2).card := by
        calc 2 = ({u0, x1} : Finset (Fin n)).card := (Finset.card_pair hx1u0.symm).symm
          _ ≤ (A1 ∩ A2).card := Finset.card_le_card (Finset.insert_subset
              (Finset.mem_inter.mpr ⟨hu0A1, hu0A2⟩)
              (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hx1A1, hx2A2⟩)))
      have := hlin A1 hA1L A2 hA2L hA12
      omega
    have hA1_eq : A1 = {u0, u1, x1} := by
      have hx1u0 : x1 ≠ u0 := fun h => (Finset.mem_sdiff.mp hu0W).2 (h ▸ hx1B)
      have hx1u1 : x1 ≠ u1 := fun h => (Finset.mem_sdiff.mp hu1W).2 (h ▸ hx1B)
      apply Eq.symm
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.insert_subset hu0A1 (Finset.insert_subset hu1A1
          (Finset.singleton_subset_iff.mpr hx1A1))
      · rw [Finset.card_insert_of_notMem (by simp [hu10.symm, hx1u0.symm]),
            Finset.card_pair hx1u1.symm, (hAW2 A1 hA1rem).2.2]
    -- Count `d_S(A1)` by splitting into `L3.erase A1` (card 2) and size-2 blocks `{u1, z}`.
    let D := (S.erase A1).filter fun b => (A1 ∩ b).Nonempty
    let D3 := D.filter fun b => 3 ≤ b.card
    let D2 := D.filter fun b => ¬ (3 ≤ b.card)
    have hD_card : D.card = D3.card + D2.card := by
      simpa [D3, D2] using (card_filter_add_card_filter_not D (fun b => 3 ≤ b.card)).symm
    have hD3_le : D3.card ≤ 2 := by
      have hsub : D3 ⊆ {B, A2} := by
        intro b hb
        have hbD := (Finset.mem_filter.mp hb).1
        have hb3 := (Finset.mem_filter.mp hb).2
        have hbSe := (Finset.mem_filter.mp hbD).1
        have hbA1 := (Finset.mem_erase.mp hbSe).1
        have hbL := hSL (Finset.mem_erase.mp hbSe).2
        by_cases hbB : b = B
        · simp [hbB]
        · have hbin : b ∈ L3.erase B :=
            Finset.mem_erase.mpr ⟨hbB, Finset.mem_filter.mpr ⟨hbL, hb3⟩⟩
          rw [hL3_eq] at hbin
          simp only [Finset.mem_insert, Finset.mem_singleton] at hbin ⊢
          rcases hbin with rfl | rfl
          · exact (hbA1 rfl).elim
          · exact Or.inr rfl
      calc D3.card ≤ ({B, A2} : Finset (Finset (Fin n))).card := Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    let F4 : Finset (Fin n) := {u0, u1, x1, x2}
    have hF4_card : F4.card = 4 := by
      have hx1u0 : x1 ≠ u0 := fun h => (Finset.mem_sdiff.mp hu0W).2 (h ▸ hx1B)
      have hx2u0 : x2 ≠ u0 := fun h => (Finset.mem_sdiff.mp hu0W).2 (h ▸ hx2B)
      have hx1u1 : x1 ≠ u1 := fun h => (Finset.mem_sdiff.mp hu1W).2 (h ▸ hx1B)
      have hx2u1 : x2 ≠ u1 := fun h => (Finset.mem_sdiff.mp hu1W).2 (h ▸ hx2B)
      simp only [F4]
      rw [Finset.card_insert_of_notMem (by simp [hu10.symm, hx1u0.symm, hx2u0.symm]),
          Finset.card_insert_of_notMem (by simp [hx1u1.symm, hx2u1.symm]),
          Finset.card_pair hx12]
    have hD2_sub : D2 ⊆ (Finset.univ \ F4).image (fun z => ({u1, z} : Finset (Fin n))) := by
      intro b hb
      have hbD := (Finset.mem_filter.mp hb).1
      have hb_not3 := (Finset.mem_filter.mp hb).2
      have hbSe := (Finset.mem_filter.mp hbD).1
      have hmeet := (Finset.mem_filter.mp hbD).2
      have hbA1 := (Finset.mem_erase.mp hbSe).1
      have hbS := (Finset.mem_erase.mp hbSe).2
      have hbL := hSL hbS
      have hb2 : b.card = 2 := by have := hsize b hbL; omega
      obtain ⟨a, ha⟩ := hmeet
      obtain ⟨haA1, hab⟩ := Finset.mem_inter.mp ha
      obtain ⟨z, hza, rfl⟩ := pair_block_eq hb2 hab
      have hz_not_A1 : z ∉ A1 := by
        intro hzA1
        have h2' : 2 ≤ (A1 ∩ {a, z}).card := by
          calc 2 = ({a, z} : Finset (Fin n)).card := (Finset.card_pair hza.symm).symm
            _ ≤ (A1 ∩ {a, z}).card := Finset.card_le_card (Finset.insert_subset
                (Finset.mem_inter.mpr ⟨haA1, by simp⟩)
                (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hzA1, by simp⟩)))
        have := hlin A1 hA1L {a, z} hbL hbA1.symm
        omega
      have hslack := pair_excess_and_slack hn L S hSL hsize hlin hcovers hcrit hza.symm hbS
      change ex a + ex z + _ + _ + 4 ≤ n at hslack
      rw [hA1_eq] at haA1
      simp only [Finset.mem_insert, Finset.mem_singleton] at haA1
      rcases haA1 with ha_eq | ha_eq | ha_eq
      · -- `a = u0`: `z ∈ B` gives `ex u0 ≥ 2` and `ex z ≥ n - 5`, impossible.
        subst a
        exfalso
        have hzB : z ∈ B := by
          by_contra hz_notB
          have hzW : z ∈ W := Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz_notB⟩
          rw [hW_eq] at hzW
          simp only [Finset.mem_insert, Finset.mem_singleton] at hzW
          rcases hzW with hz_eq | hz_eq | hz_eq
          · exact hza hz_eq
          · exact hz_not_A1 (hz_eq ▸ hu1A1)
          · subst z
            have h2' : 2 ≤ (A2 ∩ {u0, u2}).card := by
              calc 2 = ({u0, u2} : Finset (Fin n)).card := (Finset.card_pair hu20.symm).symm
                _ ≤ (A2 ∩ {u0, u2}).card := Finset.card_le_card (Finset.insert_subset
                    (Finset.mem_inter.mpr ⟨hu0A2, by simp⟩)
                    (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hu2A2, by simp⟩)))
            have hneA2 : A2 ≠ {u0, u2} := by
              intro eq
              have := (hAW2 A2 hA2rem).2.2
              rw [eq] at this
              omega
            have := hlin A2 hA2L {u0, u2} hbL hneA2
            omega
        have hu0ex := hex_W_two u0 hu0W A1 hA1rem A2 hA2rem hA12 hu0A1 hu0A2
        have hzex := hex_B z hzB
        omega
      · -- `a = u1`: show `z ∉ F4`.
        subst a
        refine Finset.mem_image.mpr ⟨z, Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, ?_⟩, rfl⟩
        simp only [F4, Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨fun h => hz_not_A1 (h ▸ hu0A1), hza, fun h => hz_not_A1 (h ▸ hx1A1), ?_⟩
        intro hzx2
        subst z
        have hu1ex := hex_W_one u1 hu1W A1 hA1rem hu1A1
        have hx2ex := hex_B_extra x2 hx2B A2 hA2rem hx2A2
        omega
      · -- `a = x1`: `z = u2` gives `ex x1 ≥ n - 4` and `ex u2 ≥ 1`, impossible.
        subst a
        exfalso
        have hz_notB : z ∉ B := by
          intro hzB
          have h2' : 2 ≤ (B ∩ {x1, z}).card := by
            calc 2 = ({x1, z} : Finset (Fin n)).card := (Finset.card_pair hza.symm).symm
              _ ≤ (B ∩ {x1, z}).card := Finset.card_le_card (Finset.insert_subset
                  (Finset.mem_inter.mpr ⟨hx1B, by simp⟩)
                  (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hzB, by simp⟩)))
          have hneB : B ≠ {x1, z} := by
            intro eq; rw [eq] at hB3; omega
          have := hlin B hBL {x1, z} hbL hneB
          omega
        have hzW : z ∈ W := Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz_notB⟩
        rw [hW_eq] at hzW
        simp only [Finset.mem_insert, Finset.mem_singleton] at hzW
        have hzu2 : z = u2 := by
          rcases hzW with hz_eq | hz_eq | hz_eq
          · exact (hz_not_A1 (hz_eq ▸ hu0A1)).elim
          · exact (hz_not_A1 (hz_eq ▸ hu1A1)).elim
          · exact hz_eq
        subst z
        have hx1ex := hex_B_extra x1 hx1B A1 hA1rem hx1A1
        have hu2ex := hex_W_one u2 hu2W A2 hA2rem hu2A2
        omega
    have hD2_le : D2.card ≤ n - 4 := by
      calc D2.card
          ≤ ((Finset.univ \ F4).image (fun z => ({u1, z} : Finset (Fin n)))).card :=
            Finset.card_le_card hD2_sub
        _ ≤ (Finset.univ \ F4).card := Finset.card_image_le
        _ = n - 4 := by
            rw [card_sdiff_sub (Finset.subset_univ F4), Finset.card_univ, Fintype.card_fin,
              hF4_card]
    have hA1S : A1 ∈ S := hL3S A1 hA1L (Finset.mem_filter.mp hA1L3).2
    have hdegA1 : n ≤ D.card := hcrit A1 hA1S
    omega

/- ### Part 4: Complete resolution of `n ≤ 6` -/

private theorem n_le_six_colorable {n : ℕ} (hn6 : n ≤ 6) (L : Finset (Finset (Fin n)))
    (hsize : ∀ a ∈ L, 2 ≤ a.card)
    (hlin : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → (a ∩ b).card ≤ 1)
    (hcovers : ∀ i j : Fin n, i ≠ j → ∃ e ∈ L, i ∈ e ∧ j ∈ e)
    (hcore : ∃ S ⊆ L, (∀ a ∈ L, 3 ≤ a.card → a ∈ S) ∧
      ∀ a ∈ S, n ≤ ((S.erase a).filter fun b => (a ∩ b).Nonempty).card) :
    ∃ c : L → Fin n, ∀ A B : L, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B := by
  by_cases hn0 : n = 0
  · subst hn0
    exact card_le_n_colorable L (by
      have : L = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro a ha
        have h1 := hsize a ha
        have h2 : a.card ≤ 0 := by simpa using Finset.card_le_univ a
        omega
      simp [this])
  by_cases hL3 : (L.filter fun b => 3 ≤ b.card).card ≤ 2
  · exact at_most_two_large_colorable (by omega) L hsize hlin hL3
  · obtain ⟨B, hB⟩ := Finset.card_pos.mp (by omega : 0 < (L.filter fun b => 3 ≤ b.card).card)
    obtain ⟨hBL, hB3⟩ := Finset.mem_filter.mp hB
    exact large_block_gap_le_three_colorable L hsize hlin hcovers hcore ⟨B, hBL, by omega⟩

/- ### Part 5: Complete resolution of `n = 7` -/

private theorem fin7_equiv_of_seven (p0 p1 p2 p3 p4 p5 p6 : Fin 7)
    (h01 : p0 ≠ p1) (h02 : p0 ≠ p2) (h03 : p0 ≠ p3) (h04 : p0 ≠ p4) (h05 : p0 ≠ p5) (h06 : p0 ≠ p6)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4) (h15 : p1 ≠ p5) (h16 : p1 ≠ p6)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h25 : p2 ≠ p5) (h26 : p2 ≠ p6)
    (h34 : p3 ≠ p4) (h35 : p3 ≠ p5) (h36 : p3 ≠ p6)
    (h45 : p4 ≠ p5) (h46 : p4 ≠ p6) (h56 : p5 ≠ p6) :
    ∃ e : Fin 7 ≃ Fin 7, e p0 = 0 ∧ e p1 = 1 ∧ e p2 = 2 ∧ e p3 = 3 ∧
      e p4 = 4 ∧ e p5 = 5 ∧ e p6 = 6 := by
  let f : Fin 7 → Fin 7 := fun i =>
    match i.val with
    | 0 => p0
    | 1 => p1
    | 2 => p2
    | 3 => p3
    | 4 => p4
    | 5 => p5
    | _ => p6
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  let e : Fin 7 ≃ Fin 7 := (Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)).symm
  refine ⟨e, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact Equiv.symm_apply_eq _ |>.mpr rfl

private theorem n_eq_seven_colorable (L : Finset (Finset (Fin 7)))
    (hsize : ∀ a ∈ L, 2 ≤ a.card)
    (hlin : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → (a ∩ b).card ≤ 1)
    (hcovers : ∀ i j : Fin 7, i ≠ j → ∃ e ∈ L, i ∈ e ∧ j ∈ e)
    (hcore : ∃ S ⊆ L, (∀ a ∈ L, 3 ≤ a.card → a ∈ S) ∧
      ∀ a ∈ S, 7 ≤ ((S.erase a).filter fun b => (a ∩ b).Nonempty).card) :
    ∃ c : L → Fin 7, ∀ A B : L, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B := by
  let L3 := L.filter fun b => 3 ≤ b.card
  by_cases hL3_small : L3.card ≤ 2
  · exact at_most_two_large_colorable (by omega) L hsize hlin hL3_small
  by_cases hbig : ∃ b ∈ L, 4 ≤ b.card
  · obtain ⟨b, hbL, hb4⟩ := hbig
    exact large_block_gap_le_three_colorable L hsize hlin hcovers hcore ⟨b, hbL, by omega⟩
  push Not at hbig
  have hall3 : ∀ b ∈ L3, b.card = 3 := by
    intro b hb
    have h1 := (Finset.mem_filter.mp hb).2
    have h2 := hbig b (Finset.mem_filter.mp hb).1
    omega
  obtain ⟨S, hSL, hL3S, hcrit⟩ := hcore
  -- Excess at `v` equals the number of triples containing `v`.
  let ex (v : Fin 7) : ℕ := (L3.filter fun b => v ∈ b).card
  have hex_eq : ∀ v : Fin 7,
      (∑ b ∈ L.filter (fun b => 3 ≤ b.card ∧ v ∈ b), (b.card - 2)) = ex v := by
    intro v
    have hf : L.filter (fun b => 3 ≤ b.card ∧ v ∈ b) = L3.filter (fun b => v ∈ b) := by
      ext b; simp [L3]; tauto
    rw [hf]
    have h1 : ∀ b ∈ L3.filter (fun b => v ∈ b), b.card - 2 = 1 := by
      intro b hb; have := hall3 b (Finset.mem_filter.mp hb).1; omega
    rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one]
  -- Every vertex lies in at most 3 triples.
  have hex_le3 : ∀ v : Fin 7, ex v ≤ 3 := by
    intro v
    let Iv := L3.filter fun b => v ∈ b
    have hdisj : (Iv : Set (Finset (Fin 7))).PairwiseDisjoint (fun b => b.erase v) := by
      intro a ha b hb hab
      change Disjoint (a.erase v) (b.erase v)
      rw [Finset.disjoint_left]
      intro x hxa hxb
      have hxv : x ≠ v := (Finset.mem_erase.mp hxa).1
      have h2 : 2 ≤ (a ∩ b).card := by
        calc 2 = ({v, x} : Finset (Fin 7)).card := (Finset.card_pair hxv.symm).symm
          _ ≤ (a ∩ b).card := Finset.card_le_card (Finset.insert_subset
              (Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2⟩)
              (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr
                ⟨(Finset.mem_erase.mp hxa).2, (Finset.mem_erase.mp hxb).2⟩)))
      have := hlin a (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
        b (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1 hab
      omega
    have hsub : Iv.biUnion (fun b => b.erase v) ⊆ Finset.univ.erase v := by
      intro x hx
      obtain ⟨b, _, hxb⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hxb).1, Finset.mem_univ x⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_biUnion hdisj] at hle
    have hsum2 : ∑ b ∈ Iv, (b.erase v).card = 2 * ex v := by
      have hterm : ∀ b ∈ Iv, (b.erase v).card = 2 := by
        intro b hb
        rw [Finset.card_erase_of_mem (Finset.mem_filter.mp hb).2,
          hall3 b (Finset.mem_filter.mp hb).1]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, mul_comm]
    have h6 : (Finset.univ.erase v).card = 6 := by simp
    omega
  -- Double count: `∑ v, ex v = 3 * L3.card`.
  have hsum_ex : ∑ v : Fin 7, ex v = 3 * L3.card := by
    calc ∑ v : Fin 7, ex v
        = ∑ v : Fin 7, ∑ b ∈ L3, if v ∈ b then 1 else 0 := by
          refine Finset.sum_congr rfl fun v _ => ?_
          dsimp only [ex]
          rw [Finset.card_filter]
      _ = ∑ b ∈ L3, ∑ v : Fin 7, if v ∈ b then 1 else 0 := Finset.sum_comm
      _ = ∑ b ∈ L3, b.card := by
          refine Finset.sum_congr rfl fun b _ => ?_
          simp
      _ = 3 * L3.card := by
          rw [Finset.sum_congr rfl hall3, Finset.sum_const, smul_eq_mul, mul_comm]
  have hL3_le7 : L3.card ≤ 7 := by
    have hle : ∑ v : Fin 7, ex v ≤ ∑ _v : Fin 7, 3 :=
      Finset.sum_le_sum fun v _ => hex_le3 v
    simp at hle
    omega
  -- Pair slack specialized to `n = 7`: `ex u + ex v + miss u + miss v ≤ 3`.
  have hslack7 : ∀ {u v : Fin 7}, u ≠ v → ({u, v} : Finset (Fin 7)) ∈ S →
      ex u + ex v + ((L \ S).filter fun b => u ∈ b).card +
        ((L \ S).filter fun b => v ∈ b).card ≤ 3 := by
    intro u v huv he
    have h := pair_excess_and_slack (by omega) L S hSL hsize hlin hcovers hcrit huv he
    rw [hex_eq u, hex_eq v] at h
    omega
  -- Helper: if every vertex has `ex v ≥ 2`, then `S ⊆ L3`, contradicting `d_S ≥ 7`.
  have hno_all_ge2 : (∀ v : Fin 7, 2 ≤ ex v) → False := by
    intro hall2
    have hS_sub : S ⊆ L3 := by
      intro b hbS
      have hbL := hSL hbS
      by_cases hb3 : 3 ≤ b.card
      · exact Finset.mem_filter.mpr ⟨hbL, hb3⟩
      · exfalso
        have hb2 : b.card = 2 := by have := hsize b hbL; omega
        obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < b.card)
        obtain ⟨v, hvu, rfl⟩ := pair_block_eq hb2 hu
        have hs := hslack7 hvu.symm hbS
        have := hall2 u
        have := hall2 v
        omega
    obtain ⟨T, hTL3⟩ := Finset.card_pos.mp (by omega : 0 < L3.card)
    have hTS : T ∈ S := hL3S T (Finset.mem_filter.mp hTL3).1 (Finset.mem_filter.mp hTL3).2
    have hdeg := hcrit T hTS
    have hle : ((S.erase T).filter fun b => (T ∩ b).Nonempty).card ≤ (L3.erase T).card :=
      Finset.card_le_card (fun b hb => Finset.mem_erase.mpr
        ⟨(Finset.mem_erase.mp (Finset.mem_filter.mp hb).1).1,
         hS_sub (Finset.mem_erase.mp (Finset.mem_filter.mp hb).1).2⟩)
    rw [Finset.card_erase_of_mem hTL3] at hle
    omega
  -- Helper: if `ex v0 = 3`, then the 3 triples at `v0` partition `univ.erase v0`, so `∀ v, 1 ≤ ex v`.
  have hex3_cover : ∀ v0 : Fin 7, ex v0 = 3 →
      (L3.filter fun b => v0 ∈ b).biUnion (fun b => b.erase v0) = Finset.univ.erase v0 ∧
      ∀ v : Fin 7, 1 ≤ ex v := by
    intro v0 hv0
    let Iv := L3.filter fun b => v0 ∈ b
    have hdisj : (Iv : Set (Finset (Fin 7))).PairwiseDisjoint (fun b => b.erase v0) := by
      intro a ha b hb hab
      change Disjoint (a.erase v0) (b.erase v0)
      rw [Finset.disjoint_left]
      intro x hxa hxb
      have hxv : x ≠ v0 := (Finset.mem_erase.mp hxa).1
      have h2 : 2 ≤ (a ∩ b).card := by
        calc 2 = ({v0, x} : Finset (Fin 7)).card := (Finset.card_pair hxv.symm).symm
          _ ≤ (a ∩ b).card := Finset.card_le_card (Finset.insert_subset
              (Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2⟩)
              (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr
                ⟨(Finset.mem_erase.mp hxa).2, (Finset.mem_erase.mp hxb).2⟩)))
      have := hlin a (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
        b (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1 hab
      omega
    have hsub : Iv.biUnion (fun b => b.erase v0) ⊆ Finset.univ.erase v0 := by
      intro x hx
      obtain ⟨b, _, hxb⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hxb).1, Finset.mem_univ x⟩
    have hcard_u : (Iv.biUnion (fun b => b.erase v0)).card = 6 := by
      rw [Finset.card_biUnion hdisj]
      have hterm : ∀ b ∈ Iv, (b.erase v0).card = 2 := by
        intro b hb
        rw [Finset.card_erase_of_mem (Finset.mem_filter.mp hb).2,
          hall3 b (Finset.mem_filter.mp hb).1]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
      change ex v0 * 2 = 6
      omega
    have heq : Iv.biUnion (fun b => b.erase v0) = Finset.univ.erase v0 :=
      Finset.eq_of_subset_of_card_le hsub (by simp [hcard_u])
    refine ⟨heq, fun v => ?_⟩
    by_cases hvv : v = v0
    · subst hvv; omega
    · have hvmem : v ∈ Iv.biUnion (fun b => b.erase v0) := by rw [heq]; simp [hvv]
      obtain ⟨T, hTIv, hvT⟩ := Finset.mem_biUnion.mp hvmem
      exact Finset.card_pos.mpr ⟨T, Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hTIv).1, (Finset.mem_erase.mp hvT).2⟩⟩
  -- Step 1: Prove `L3.card ≤ 4`.
  have hL3_le4 : L3.card ≤ 4 := by
    by_contra! hge5
    have hex_v0 : ∃ v0 : Fin 7, ex v0 = 3 := by
      by_contra hno
      push Not at hno
      have hle2 : ∀ v : Fin 7, ex v ≤ 2 := fun v => by have := hex_le3 v; have := hno v; omega
      have hsum_le : ∑ v : Fin 7, ex v ≤ ∑ _v : Fin 7, 2 := Finset.sum_le_sum fun v _ => hle2 v
      simp at hsum_le
      omega
    obtain ⟨v0, hv0⟩ := hex_v0
    obtain ⟨hcov_v0, hall1⟩ := hex3_cover v0 hv0
    let Iv := L3.filter fun b => v0 ∈ b
    let Out := L3 \ Iv
    have hOut_card : Out.card = L3.card - 3 := by
      have hsub : Iv ⊆ L3 := Finset.filter_subset _ _
      dsimp only [Out]
      rw [card_sdiff_sub hsub]
      change L3.card - ex v0 = L3.card - 3
      omega
    obtain ⟨T4, hT4Out, T5, hT5Out, hT45⟩ := Finset.one_lt_card.mp (by omega : 1 < Out.card)
    have hT4L3 : T4 ∈ L3 := (Finset.mem_sdiff.mp hT4Out).1
    have hT5L3 : T5 ∈ L3 := (Finset.mem_sdiff.mp hT5Out).1
    have hv0_T4 : v0 ∉ T4 := fun h => (Finset.mem_sdiff.mp hT4Out).2 (Finset.mem_filter.mpr ⟨hT4L3, h⟩)
    have hv0_T5 : v0 ∉ T5 := fun h => (Finset.mem_sdiff.mp hT5Out).2 (Finset.mem_filter.mpr ⟨hT5L3, h⟩)
    have hcap45 : (T4 ∩ T5).card ≤ 1 :=
      hlin T4 (Finset.mem_filter.mp hT4L3).1 T5 (Finset.mem_filter.mp hT5L3).1 hT45
    have hun45_ge : 5 ≤ (T4 ∪ T5).card := by
      have := Finset.card_union_add_card_inter T4 T5
      rw [hall3 T4 hT4L3, hall3 T5 hT5L3] at this
      omega
    -- Every vertex in `T4 ∪ T5` has `ex u ≥ 2`.
    have hex_ge2_u : ∀ u ∈ T4 ∪ T5, 2 ≤ ex u := by
      intro u hu
      have huv0 : u ≠ v0 := by
        intro eq; subst eq
        rcases Finset.mem_union.mp hu with h | h
        · exact hv0_T4 h
        · exact hv0_T5 h
      have humem : u ∈ Iv.biUnion (fun b => b.erase v0) := by rw [hcov_v0]; simp [huv0]
      obtain ⟨Ti, hTiIv, huTi⟩ := Finset.mem_biUnion.mp humem
      have hTiL3 : Ti ∈ L3 := (Finset.mem_filter.mp hTiIv).1
      have hv0Ti : v0 ∈ Ti := (Finset.mem_filter.mp hTiIv).2
      have huTi' : u ∈ Ti := (Finset.mem_erase.mp huTi).2
      rcases Finset.mem_union.mp hu with hu4 | hu5
      · have hne : Ti ≠ T4 := fun h => hv0_T4 (h ▸ hv0Ti)
        have hsub : ({Ti, T4} : Finset (Finset (Fin 7))) ⊆ L3.filter (fun b => u ∈ b) :=
          Finset.insert_subset (Finset.mem_filter.mpr ⟨hTiL3, huTi'⟩)
            (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr ⟨hT4L3, hu4⟩))
        have := Finset.card_le_card hsub
        rw [Finset.card_pair hne] at this
        exact this
      · have hne : Ti ≠ T5 := fun h => hv0_T5 (h ▸ hv0Ti)
        have hsub : ({Ti, T5} : Finset (Finset (Fin 7))) ⊆ L3.filter (fun b => u ∈ b) :=
          Finset.insert_subset (Finset.mem_filter.mpr ⟨hTiL3, huTi'⟩)
            (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr ⟨hT5L3, hu5⟩))
        have := Finset.card_le_card hsub
        rw [Finset.card_pair hne] at this
        exact this
    let R := (Finset.univ.erase v0) \ (T4 ∪ T5)
    have hsub45 : T4 ∪ T5 ⊆ Finset.univ.erase v0 := by
      intro u hu
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ u⟩
      intro eq; subst eq
      rcases Finset.mem_union.mp hu with h | h
      · exact hv0_T4 h
      · exact hv0_T5 h
    have hRcard : R.card + (T4 ∪ T5).card = 6 := by
      have := card_sdiff_sub hsub45
      have h6 : (Finset.univ.erase v0).card = 6 := by simp
      have hle := Finset.card_le_card hsub45
      dsimp only [R]
      omega
    by_cases hR0 : R.card = 0
    · apply hno_all_ge2
      intro u
      by_cases huv0 : u = v0
      · subst huv0; omega
      · have huR : u ∉ R := by rw [Finset.card_eq_zero.mp hR0]; simp
        have hu45 : u ∈ T4 ∪ T5 := by
          by_contra hnot
          exact huR (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨huv0, Finset.mem_univ u⟩, hnot⟩)
        exact hex_ge2_u u hu45
    · have hR1 : R.card = 1 := by omega
      obtain ⟨y, hyR⟩ := Finset.card_eq_one.mp hR1
      have hy_in : y ∈ R := by rw [hyR]; simp
      have hyv0 : y ≠ v0 := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hy_in).1).1
      have hy_not45 : y ∉ T4 ∪ T5 := (Finset.mem_sdiff.mp hy_in).2
      have hun45_5 : (T4 ∪ T5).card = 5 := by omega
      have hcap45_1 : (T4 ∩ T5).card = 1 := by
        have := Finset.card_union_add_card_inter T4 T5
        rw [hall3 T4 hT4L3, hall3 T5 hT5L3] at this
        omega
      obtain ⟨x, hx45⟩ := Finset.card_eq_one.mp hcap45_1
      have hx_in : x ∈ T4 ∩ T5 := by rw [hx45]; simp
      have hxT4 : x ∈ T4 := (Finset.mem_inter.mp hx_in).1
      have hxT5 : x ∈ T5 := (Finset.mem_inter.mp hx_in).2
      have hxv0 : x ≠ v0 := fun h => hv0_T4 (h ▸ hxT4)
      -- `ex x = 3`: `x` lies in one triple of `Iv`, plus `T4` and `T5`.
      have hex_x : ex x = 3 := by
        have hxmem : x ∈ Iv.biUnion (fun b => b.erase v0) := by rw [hcov_v0]; simp [hxv0]
        obtain ⟨Tx, hTxIv, hxTx⟩ := Finset.mem_biUnion.mp hxmem
        have hTxL3 := (Finset.mem_filter.mp hTxIv).1
        have hv0Tx := (Finset.mem_filter.mp hTxIv).2
        have hxTx' := (Finset.mem_erase.mp hxTx).2
        have hne1 : Tx ≠ T4 := fun h => hv0_T4 (h ▸ hv0Tx)
        have hne2 : Tx ≠ T5 := fun h => hv0_T5 (h ▸ hv0Tx)
        have hsub : ({Tx, T4, T5} : Finset (Finset (Fin 7))) ⊆ L3.filter (fun b => x ∈ b) :=
          Finset.insert_subset (Finset.mem_filter.mpr ⟨hTxL3, hxTx'⟩)
            (Finset.insert_subset (Finset.mem_filter.mpr ⟨hT4L3, hxT4⟩)
              (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr ⟨hT5L3, hxT5⟩)))
        have hle := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem (by simp [hne1, hne2]), Finset.card_pair hT45] at hle
        have := hex_le3 x
        dsimp only [ex] at this ⊢
        omega
      -- Every vertex other than `y` has `ex u ≥ 2`.
      have hex_ne_y : ∀ u : Fin 7, u ≠ y → 2 ≤ ex u := by
        intro u huy
        by_cases huv0 : u = v0
        · subst huv0; omega
        · have hu45 : u ∈ T4 ∪ T5 := by
            by_contra hnot
            have huR : u ∈ R :=
              Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨huv0, Finset.mem_univ u⟩, hnot⟩
            rw [hyR] at huR
            exact huy (Finset.mem_singleton.mp huR)
          exact hex_ge2_u u hu45
      -- Show `L3.card = 5`: any 6th triple `T6` either hits `y` (giving `∀ u, 2 ≤ ex u`) or lies in `(T4 ∪ T5).erase x`.
      have hL3_eq5 : L3.card = 5 := by
        by_contra hne5
        have hOut_ge3 : 3 ≤ Out.card := by omega
        have hrest : ((Out.erase T4).erase T5).Nonempty := by
          have hT5in : T5 ∈ Out.erase T4 := Finset.mem_erase.mpr ⟨hT45.symm, hT5Out⟩
          apply Finset.card_pos.mp
          rw [Finset.card_erase_of_mem hT5in, Finset.card_erase_of_mem hT4Out]
          omega
        obtain ⟨T6, hT6in⟩ := hrest
        have hT65 : T6 ≠ T5 := (Finset.mem_erase.mp hT6in).1
        have hT64 : T6 ≠ T4 := (Finset.mem_erase.mp (Finset.mem_erase.mp hT6in).2).1
        have hT6Out : T6 ∈ Out := (Finset.mem_erase.mp (Finset.mem_erase.mp hT6in).2).2
        have hT6L3 : T6 ∈ L3 := (Finset.mem_sdiff.mp hT6Out).1
        have hv0_T6 : v0 ∉ T6 := fun h =>
          (Finset.mem_sdiff.mp hT6Out).2 (Finset.mem_filter.mpr ⟨hT6L3, h⟩)
        by_cases hy6 : y ∈ T6
        · apply hno_all_ge2
          intro u
          by_cases huy : u = y
          · subst u
            have hymem : y ∈ Iv.biUnion (fun b => b.erase v0) := by rw [hcov_v0]; simp [hyv0]
            obtain ⟨Ty, hTyIv, hyTy⟩ := Finset.mem_biUnion.mp hymem
            have hne : Ty ≠ T6 := fun h => hv0_T6 (h ▸ (Finset.mem_filter.mp hTyIv).2)
            have hsub : ({Ty, T6} : Finset (Finset (Fin 7))) ⊆ L3.filter (fun b => y ∈ b) :=
              Finset.insert_subset
                (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hTyIv).1, (Finset.mem_erase.mp hyTy).2⟩)
                (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr ⟨hT6L3, hy6⟩))
            have := Finset.card_le_card hsub
            rw [Finset.card_pair hne] at this
            exact this
          · exact hex_ne_y u huy
        · -- `v0 ∉ T6`, `y ∉ T6`, and `x ∉ T6` (since `ex x = 3` already accounted for).
          have hx_not6 : x ∉ T6 := by
            intro hx6
            have hxmem : x ∈ Iv.biUnion (fun b => b.erase v0) := by rw [hcov_v0]; simp [hxv0]
            obtain ⟨Tx, hTxIv, hxTx⟩ := Finset.mem_biUnion.mp hxmem
            have hTxL3 := (Finset.mem_filter.mp hTxIv).1
            have hv0Tx := (Finset.mem_filter.mp hTxIv).2
            have hne1 : Tx ≠ T4 := fun h => hv0_T4 (h ▸ hv0Tx)
            have hne2 : Tx ≠ T5 := fun h => hv0_T5 (h ▸ hv0Tx)
            have hne3 : Tx ≠ T6 := fun h => hv0_T6 (h ▸ hv0Tx)
            have hsub : ({Tx, T4, T5, T6} : Finset (Finset (Fin 7))) ⊆
                L3.filter (fun b => x ∈ b) :=
              Finset.insert_subset (Finset.mem_filter.mpr ⟨hTxL3, (Finset.mem_erase.mp hxTx).2⟩)
                (Finset.insert_subset (Finset.mem_filter.mpr ⟨hT4L3, hxT4⟩)
                  (Finset.insert_subset (Finset.mem_filter.mpr ⟨hT5L3, hxT5⟩)
                    (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr ⟨hT6L3, hx6⟩))))
            have hle := Finset.card_le_card hsub
            rw [Finset.card_insert_of_notMem (by simp [hne1, hne2, hne3]),
                Finset.card_insert_of_notMem (by simp [hT45, hT64.symm]),
                Finset.card_pair hT65.symm] at hle
            dsimp only [ex] at hex_x
            omega
          -- Then `T6 ⊆ (T4 ∩ T6) ∪ (T5 ∩ T6)` has size ≤ 1 + 1 = 2, contradicting `T6.card = 3`.
          have hsub6 : T6 ⊆ (T6 ∩ T4) ∪ (T6 ∩ T5) := by
            intro u hu
            have huv0 : u ≠ v0 := fun h => hv0_T6 (h ▸ hu)
            have huy : u ≠ y := fun h => hy6 (h ▸ hu)
            have hu45 : u ∈ T4 ∪ T5 := by
              by_contra hnot
              have huR : u ∈ R :=
                Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨huv0, Finset.mem_univ u⟩, hnot⟩
              rw [hyR] at huR
              exact huy (Finset.mem_singleton.mp huR)
            rcases Finset.mem_union.mp hu45 with hu4 | hu5
            · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hu, hu4⟩)
            · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hu, hu5⟩)
          have hle := Finset.card_le_card hsub6
          have hu_le := Finset.card_union_le (T6 ∩ T4) (T6 ∩ T5)
          have hc1 := hlin T6 (Finset.mem_filter.mp hT6L3).1 T4 (Finset.mem_filter.mp hT4L3).1 hT64
          have hc2 := hlin T6 (Finset.mem_filter.mp hT6L3).1 T5 (Finset.mem_filter.mp hT5L3).1 hT65
          have hT6c := hall3 T6 hT6L3
          omega
      -- With `L3.card = 5`, bound `d_S(T4) ≤ 4 + 2 = 6 < 7`.
      let D := (S.erase T4).filter fun b => (T4 ∩ b).Nonempty
      let D3 := D.filter fun b => 3 ≤ b.card
      let D2 := D.filter fun b => ¬ (3 ≤ b.card)
      have hD_card : D.card = D3.card + D2.card := by
        simpa [D3, D2] using (card_filter_add_card_filter_not D (fun b => 3 ≤ b.card)).symm
      have hD3_le : D3.card ≤ 4 := by
        have hsub : D3 ⊆ L3.erase T4 := fun b hb =>
          Finset.mem_erase.mpr
            ⟨(Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1).1,
             Finset.mem_filter.mpr
              ⟨hSL (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1).2,
               (Finset.mem_filter.mp hb).2⟩⟩
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hT4L3] at this
        omega
      have hD2_sub : D2 ⊆ (T4.erase x).image (fun u => ({u, y} : Finset (Fin 7))) := by
        intro b hb
        have hbD := (Finset.mem_filter.mp hb).1
        have hb_not3 := (Finset.mem_filter.mp hb).2
        have hbSe := (Finset.mem_filter.mp hbD).1
        have hmeet := (Finset.mem_filter.mp hbD).2
        have hbS := (Finset.mem_erase.mp hbSe).2
        have hbL := hSL hbS
        have hb2 : b.card = 2 := by have := hsize b hbL; omega
        obtain ⟨u, hu⟩ := hmeet
        obtain ⟨huT4, hub⟩ := Finset.mem_inter.mp hu
        obtain ⟨w, hwu, rfl⟩ := pair_block_eq hb2 hub
        have huy : u ≠ y := fun h => hy_not45 (Finset.mem_union_left _ (h ▸ huT4))
        have hwy : w = y := by
          by_contra hne
          have hs := hslack7 hwu.symm hbS
          have := hex_ne_y u huy
          have := hex_ne_y w hne
          omega
        subst w
        have hux : u ≠ x := by
          intro hux; subst u
          have hs := hslack7 hwu.symm hbS
          have := hall1 y
          omega
        exact Finset.mem_image.mpr ⟨u, Finset.mem_erase.mpr ⟨hux, huT4⟩, rfl⟩
      have hD2_le : D2.card ≤ 2 := by
        calc D2.card ≤ ((T4.erase x).image (fun u => ({u, y} : Finset (Fin 7)))).card :=
              Finset.card_le_card hD2_sub
          _ ≤ (T4.erase x).card := Finset.card_image_le
          _ = 2 := by rw [Finset.card_erase_of_mem hxT4, hall3 T4 hT4L3]
      have hT4S : T4 ∈ S := hL3S T4 (Finset.mem_filter.mp hT4L3).1 (Finset.mem_filter.mp hT4L3).2
      have hdeg : 7 ≤ D.card := hcrit T4 hT4S
      omega
  -- Step 2: Split on `L3.card = 3` vs `L3.card = 4`.
  rcases (show L3.card = 3 ∨ L3.card = 4 by omega) with hL3_3 | hL3_4
  · -- Case `L3.card = 3`.
    by_cases hdisj : ∃ A ∈ L3, ∃ B ∈ L3, Disjoint A B
    · exact three_large_with_disjoint_colorable (by omega) L hsize hlin hL3_3 hdisj
    push Not at hdisj
    have hmeet_all : ∀ A ∈ L3, ∀ B ∈ L3, (A ∩ B).Nonempty := by
      intro A hA B hB
      exact Finset.not_disjoint_iff_nonempty_inter.mp (hdisj A hA B hB)
    obtain ⟨A, hAL3, hrem2⟩ : ∃ A ∈ L3, (L3.erase A).card = 2 := by
      obtain ⟨A, hA⟩ := Finset.card_pos.mp (by omega : 0 < L3.card)
      exact ⟨A, hA, by rw [Finset.card_erase_of_mem hA, hL3_3]⟩
    obtain ⟨B, C, hBC, hL3_er⟩ := Finset.card_eq_two.mp hrem2
    have hBL3 : B ∈ L3 := (Finset.mem_erase.mp (by rw [hL3_er]; simp)).2
    have hAB : A ≠ B := (Finset.mem_erase.mp (by rw [hL3_er]; simp)).1.symm
    have hCL3 : C ∈ L3 := (Finset.mem_erase.mp (by rw [hL3_er]; simp)).2
    have hAC : A ≠ C := (Finset.mem_erase.mp (by rw [hL3_er]; simp)).1.symm
    have hL3_eq : L3 = {A, B, C} := by
      ext X
      by_cases hXA : X = A
      · simp [hXA, hAL3]
      · have : X ∈ L3 ↔ X ∈ L3.erase A := by simp [hXA]
        rw [this, hL3_er]; simp [hXA]
    have hAL := (Finset.mem_filter.mp hAL3).1
    have hBL := (Finset.mem_filter.mp hBL3).1
    have hCL := (Finset.mem_filter.mp hCL3).1
    by_cases hstar : ((A ∩ B) ∩ C).Nonempty
    · -- 3-star: map `A, B, C` to `{0,1,2}, {0,3,4}, {0,5,6}`.
      obtain ⟨v, hv⟩ := hstar
      have hvA : v ∈ A := (Finset.mem_inter.mp (Finset.mem_inter.mp hv).1).1
      have hvB : v ∈ B := (Finset.mem_inter.mp (Finset.mem_inter.mp hv).1).2
      have hvC : v ∈ C := (Finset.mem_inter.mp hv).2
      obtain ⟨a1, a2, ha12, hAe⟩ := Finset.card_eq_two.mp
        (by rw [Finset.card_erase_of_mem hvA, hall3 A hAL3])
      obtain ⟨b1, b2, hb12, hBe⟩ := Finset.card_eq_two.mp
        (by rw [Finset.card_erase_of_mem hvB, hall3 B hBL3])
      obtain ⟨c1, c2, hc12, hCe⟩ := Finset.card_eq_two.mp
        (by rw [Finset.card_erase_of_mem hvC, hall3 C hCL3])
      have ha1A : a1 ∈ A := (Finset.mem_erase.mp (by rw [hAe]; simp)).2
      have ha1v : a1 ≠ v := (Finset.mem_erase.mp (by rw [hAe]; simp)).1
      have ha2A : a2 ∈ A := (Finset.mem_erase.mp (by rw [hAe]; simp)).2
      have ha2v : a2 ≠ v := (Finset.mem_erase.mp (by rw [hAe]; simp)).1
      have hb1B : b1 ∈ B := (Finset.mem_erase.mp (by rw [hBe]; simp)).2
      have hb1v : b1 ≠ v := (Finset.mem_erase.mp (by rw [hBe]; simp)).1
      have hb2B : b2 ∈ B := (Finset.mem_erase.mp (by rw [hBe]; simp)).2
      have hb2v : b2 ≠ v := (Finset.mem_erase.mp (by rw [hBe]; simp)).1
      have hc1C : c1 ∈ C := (Finset.mem_erase.mp (by rw [hCe]; simp)).2
      have hc1v : c1 ≠ v := (Finset.mem_erase.mp (by rw [hCe]; simp)).1
      have hc2C : c2 ∈ C := (Finset.mem_erase.mp (by rw [hCe]; simp)).2
      have hc2v : c2 ≠ v := (Finset.mem_erase.mp (by rw [hCe]; simp)).1
      have huniq : ∀ {X Y : Finset (Fin 7)}, X ∈ L → Y ∈ L → X ≠ Y →
          v ∈ X → v ∈ Y → ∀ {x y : Fin 7}, x ∈ X → y ∈ Y → x ≠ v → x ≠ y := by
        intro X Y hXL hYL hXY hvX hvY x y hxX hyY hxv hxy
        subst hxy
        have h2 : 2 ≤ (X ∩ Y).card := by
          calc 2 = ({v, x} : Finset (Fin 7)).card := (Finset.card_pair hxv.symm).symm
            _ ≤ (X ∩ Y).card := Finset.card_le_card (Finset.insert_subset
                (Finset.mem_inter.mpr ⟨hvX, hvY⟩)
                (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hxX, hyY⟩)))
        have := hlin X hXL Y hYL hXY
        omega
      obtain ⟨e, he0, he1, he2, he3, he4, he5, he6⟩ := fin7_equiv_of_seven v a1 a2 b1 b2 c1 c2
        ha1v.symm ha2v.symm hb1v.symm hb2v.symm hc1v.symm hc2v.symm
        ha12 (huniq hAL hBL hAB hvA hvB ha1A hb1B ha1v) (huniq hAL hBL hAB hvA hvB ha1A hb2B ha1v)
        (huniq hAL hCL hAC hvA hvC ha1A hc1C ha1v) (huniq hAL hCL hAC hvA hvC ha1A hc2C ha1v)
        (huniq hAL hBL hAB hvA hvB ha2A hb1B ha2v) (huniq hAL hBL hAB hvA hvB ha2A hb2B ha2v)
        (huniq hAL hCL hAC hvA hvC ha2A hc1C ha2v) (huniq hAL hCL hAC hvA hvC ha2A hc2C ha2v)
        hb12 (huniq hBL hCL hBC hvB hvC hb1B hc1C hb1v) (huniq hBL hCL hBC hvB hvC hb1B hc2C hb1v)
        (huniq hBL hCL hBC hvB hvC hb2B hc1C hb2v) (huniq hBL hCL hBC hvB hvC hb2B hc2C hb2v)
        hc12
      have hAeq : A = {v, a1, a2} := by
        rw [← Finset.insert_erase hvA, hAe]
      have hBeq : B = {v, b1, b2} := by
        rw [← Finset.insert_erase hvB, hBe]
      have hCeq : C = {v, c1, c2} := by
        rw [← Finset.insert_erase hvC, hCe]
      obtain ⟨ksize, klin⟩ := relabel_bounds L e hsize hlin
      apply pullback_coloring L e
      apply n7_subset_four_triples_colorable _ ksize klin
      intro U hU hU3
      obtain ⟨X, hXL, rfl⟩ := Finset.mem_image.mp hU
      rw [Finset.card_map] at hU3
      have hXL3 : X ∈ L3 := Finset.mem_filter.mpr ⟨hXL, hU3⟩
      rw [hL3_eq] at hXL3
      simp only [Finset.mem_insert, Finset.mem_singleton] at hXL3
      rcases hXL3 with rfl | rfl | rfl
      · left; rw [hAeq]; simp [he0, he1, he2]
      · right; left; rw [hBeq]; simp [he0, he3, he4]
      · right; right; left; rw [hCeq]; simp [he0, he5, he6]
    · -- 3-triangle: `A ∩ B = {x}`, `A ∩ C = {z}`, `B ∩ C = {y}`, map to `{0,1,2}, {0,3,4}, {1,3,5}`.
      rw [Finset.not_nonempty_iff_eq_empty] at hstar
      obtain ⟨x, hxAB⟩ := hmeet_all A hAL3 B hBL3
      obtain ⟨z, hzAC⟩ := hmeet_all A hAL3 C hCL3
      obtain ⟨y, hyBC⟩ := hmeet_all B hBL3 C hCL3
      have hxA := (Finset.mem_inter.mp hxAB).1
      have hxB := (Finset.mem_inter.mp hxAB).2
      have hzA := (Finset.mem_inter.mp hzAC).1
      have hzC := (Finset.mem_inter.mp hzAC).2
      have hyB := (Finset.mem_inter.mp hyBC).1
      have hyC := (Finset.mem_inter.mp hyBC).2
      have hx_notC : x ∉ C := fun h => by
        have : x ∈ (A ∩ B) ∩ C := Finset.mem_inter.mpr ⟨hxAB, h⟩
        rw [hstar] at this; exact Finset.notMem_empty _ this
      have hz_notB : z ∉ B := fun h => by
        have : z ∈ (A ∩ B) ∩ C := Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hzA, h⟩, hzC⟩
        rw [hstar] at this; exact Finset.notMem_empty _ this
      have hy_notA : y ∉ A := fun h => by
        have : y ∈ (A ∩ B) ∩ C := Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨h, hyB⟩, hyC⟩
        rw [hstar] at this; exact Finset.notMem_empty _ this
      have hxz : x ≠ z := fun h => hx_notC (h ▸ hzC)
      have hxy : x ≠ y := fun h => hx_notC (h ▸ hyC)
      have hzy : z ≠ y := fun h => hz_notB (h ▸ hyB)
      obtain ⟨a, haeq⟩ := Finset.card_eq_one.mp (by
        have hz' : z ∈ A.erase x := Finset.mem_erase.mpr ⟨hxz.symm, hzA⟩
        rw [Finset.card_erase_of_mem hz', Finset.card_erase_of_mem hxA, hall3 A hAL3])
      obtain ⟨b, hbeq⟩ := Finset.card_eq_one.mp (by
        have hy' : y ∈ B.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hyB⟩
        rw [Finset.card_erase_of_mem hy', Finset.card_erase_of_mem hxB, hall3 B hBL3])
      obtain ⟨c, hceq⟩ := Finset.card_eq_one.mp (by
        have hy' : y ∈ C.erase z := Finset.mem_erase.mpr ⟨hzy.symm, hyC⟩
        rw [Finset.card_erase_of_mem hy', Finset.card_erase_of_mem hzC, hall3 C hCL3])
      have ha_in : a ∈ (A.erase x).erase z := by rw [haeq]; simp
      have hb_in : b ∈ (B.erase x).erase y := by rw [hbeq]; simp
      have hc_in : c ∈ (C.erase z).erase y := by rw [hceq]; simp
      have haz : a ≠ z := (Finset.mem_erase.mp ha_in).1
      have hax : a ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp ha_in).2).1
      have haA : a ∈ A := (Finset.mem_erase.mp (Finset.mem_erase.mp ha_in).2).2
      have hby : b ≠ y := (Finset.mem_erase.mp hb_in).1
      have hbx : b ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hb_in).2).1
      have hbB : b ∈ B := (Finset.mem_erase.mp (Finset.mem_erase.mp hb_in).2).2
      have hcy : c ≠ y := (Finset.mem_erase.mp hc_in).1
      have hcz : c ≠ z := (Finset.mem_erase.mp (Finset.mem_erase.mp hc_in).2).1
      have hcC : c ∈ C := (Finset.mem_erase.mp (Finset.mem_erase.mp hc_in).2).2
      have ha_notB : a ∉ B := fun h => by
        have h2 : 2 ≤ (A ∩ B).card := by
          calc 2 = ({x, a} : Finset (Fin 7)).card := (Finset.card_pair hax.symm).symm
            _ ≤ (A ∩ B).card := Finset.card_le_card (Finset.insert_subset
                (Finset.mem_inter.mpr ⟨hxA, hxB⟩)
                (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨haA, h⟩)))
        have := hlin A hAL B hBL hAB; omega
      have ha_notC : a ∉ C := fun h => by
        have h2 : 2 ≤ (A ∩ C).card := by
          calc 2 = ({z, a} : Finset (Fin 7)).card := (Finset.card_pair haz.symm).symm
            _ ≤ (A ∩ C).card := Finset.card_le_card (Finset.insert_subset
                (Finset.mem_inter.mpr ⟨hzA, hzC⟩)
                (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨haA, h⟩)))
        have := hlin A hAL C hCL hAC; omega
      have hb_notC : b ∉ C := fun h => by
        have h2 : 2 ≤ (B ∩ C).card := by
          calc 2 = ({y, b} : Finset (Fin 7)).card := (Finset.card_pair hby.symm).symm
            _ ≤ (B ∩ C).card := Finset.card_le_card (Finset.insert_subset
                (Finset.mem_inter.mpr ⟨hyB, hyC⟩)
                (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hbB, h⟩)))
        have := hlin B hBL C hCL hBC; omega
      have hay : a ≠ y := fun h => ha_notB (h ▸ hyB)
      have hab : a ≠ b := fun h => ha_notB (h ▸ hbB)
      have hac : a ≠ c := fun h => ha_notC (h ▸ hcC)
      have hbz : b ≠ z := fun h => hb_notC (h ▸ hzC)
      have hbc : b ≠ c := fun h => hb_notC (h ▸ hcC)
      have hcx : c ≠ x := fun h => hx_notC (h ▸ hcC)
      let S6 : Finset (Fin 7) := {x, z, a, y, b, c}
      have hS6_card : S6.card = 6 := by
        simp only [S6]
        rw [Finset.card_insert_of_notMem (by simp [hxz, hax.symm, hxy, hbx.symm, hcx.symm]),
            Finset.card_insert_of_notMem (by simp [haz.symm, hzy, hbz.symm, hcz.symm]),
            Finset.card_insert_of_notMem (by simp [hay, hab, hac]),
            Finset.card_insert_of_notMem (by simp [hby.symm, hcy.symm]),
            Finset.card_pair hbc]
      have hrem1 : (Finset.univ \ S6).card = 1 := by
        rw [card_sdiff_sub (Finset.subset_univ S6), Finset.card_univ, Fintype.card_fin, hS6_card]
      obtain ⟨w, hweq⟩ := Finset.card_eq_one.mp hrem1
      have hw_not : w ∉ S6 := (Finset.mem_sdiff.mp (by rw [hweq]; simp)).2
      simp only [S6, Finset.mem_insert, Finset.mem_singleton, not_or] at hw_not
      obtain ⟨hwx, hwz, hwa, hwy, hwb, hwc⟩ := hw_not
      obtain ⟨e, he0, he1, he2, he3, he4, he5, _⟩ := fin7_equiv_of_seven x z a y b c w
        hxz hax.symm hxy hbx.symm hcx.symm (Ne.symm hwx)
        haz.symm hzy hbz.symm hcz.symm (Ne.symm hwz)
        hay hab hac (Ne.symm hwa)
        hby.symm hcy.symm (Ne.symm hwy)
        hbc (Ne.symm hwb) (Ne.symm hwc)
      have hAeq : A = {x, z, a} := by
        apply Eq.symm; apply Finset.eq_of_subset_of_card_le
        · exact Finset.insert_subset hxA (Finset.insert_subset hzA (Finset.singleton_subset_iff.mpr haA))
        · rw [Finset.card_insert_of_notMem (by simp [hxz, hax.symm]),
              Finset.card_pair haz.symm, hall3 A hAL3]
      have hBeq : B = {x, y, b} := by
        apply Eq.symm; apply Finset.eq_of_subset_of_card_le
        · exact Finset.insert_subset hxB (Finset.insert_subset hyB (Finset.singleton_subset_iff.mpr hbB))
        · rw [Finset.card_insert_of_notMem (by simp [hxy, hbx.symm]),
              Finset.card_pair hby.symm, hall3 B hBL3]
      have hCeq : C = {z, y, c} := by
        apply Eq.symm; apply Finset.eq_of_subset_of_card_le
        · exact Finset.insert_subset hzC (Finset.insert_subset hyC (Finset.singleton_subset_iff.mpr hcC))
        · rw [Finset.card_insert_of_notMem (by simp [hzy, hcz.symm]),
              Finset.card_pair hcy.symm, hall3 C hCL3]
      obtain ⟨ksize, klin⟩ := relabel_bounds L e hsize hlin
      apply pullback_coloring L e
      apply n7_subset_four_triples_colorable _ ksize klin
      intro U hU hU3
      obtain ⟨X, hXL, rfl⟩ := Finset.mem_image.mp hU
      rw [Finset.card_map] at hU3
      have hXL3 : X ∈ L3 := Finset.mem_filter.mpr ⟨hXL, hU3⟩
      rw [hL3_eq] at hXL3
      simp only [Finset.mem_insert, Finset.mem_singleton] at hXL3
      rcases hXL3 with rfl | rfl | rfl
      · left; rw [hAeq]; simp [he0, he1, he2]
      · right; left; rw [hBeq]; simp [he0, he3, he4]
      · right; right; right; rw [hCeq]; simp [he1, he3, he5]
  · -- Case `L3.card = 4`.
    by_cases hv3 : ∃ v : Fin 7, ex v = 3
    · -- Unique critical 4-triple configuration: 3-star at `v` plus transversal `D`.
      obtain ⟨v, hv⟩ := hv3
      obtain ⟨hcov_v, _⟩ := hex3_cover v hv
      let Iv := L3.filter fun b => v ∈ b
      have hIv3 : Iv.card = 3 := hv
      obtain ⟨A, hAIv, hrem2⟩ : ∃ A ∈ Iv, (Iv.erase A).card = 2 := by
        obtain ⟨A, hA⟩ := Finset.card_pos.mp (by omega : 0 < Iv.card)
        exact ⟨A, hA, by rw [Finset.card_erase_of_mem hA, hIv3]⟩
      obtain ⟨B, C, hBC, hIv_er⟩ := Finset.card_eq_two.mp hrem2
      have hBIv : B ∈ Iv := (Finset.mem_erase.mp (by rw [hIv_er]; simp)).2
      have hAB : A ≠ B := (Finset.mem_erase.mp (by rw [hIv_er]; simp)).1.symm
      have hCIv : C ∈ Iv := (Finset.mem_erase.mp (by rw [hIv_er]; simp)).2
      have hAC : A ≠ C := (Finset.mem_erase.mp (by rw [hIv_er]; simp)).1.symm
      have hIv_eq : Iv = {A, B, C} := by
        ext X
        by_cases hXA : X = A
        · simp [hXA, hAIv]
        · have : X ∈ Iv ↔ X ∈ Iv.erase A := by simp [hXA]
          rw [this, hIv_er]; simp [hXA]
      have hAL3 := (Finset.mem_filter.mp hAIv).1
      have hBL3 := (Finset.mem_filter.mp hBIv).1
      have hCL3 := (Finset.mem_filter.mp hCIv).1
      have hvA := (Finset.mem_filter.mp hAIv).2
      have hvB := (Finset.mem_filter.mp hBIv).2
      have hvC := (Finset.mem_filter.mp hCIv).2
      have hOut1 : (L3 \ Iv).card = 1 := by
        rw [card_sdiff_sub (Finset.filter_subset _ _), hL3_4, hIv3]
      obtain ⟨D, hDeq⟩ := Finset.card_eq_one.mp hOut1
      have hD_in : D ∈ L3 \ Iv := by rw [hDeq]; simp
      have hDL3 : D ∈ L3 := (Finset.mem_sdiff.mp hD_in).1
      have hvD : v ∉ D := fun h => (Finset.mem_sdiff.mp hD_in).2 (Finset.mem_filter.mpr ⟨hDL3, h⟩)
      have hL3_eq : L3 = {A, B, C, D} := by
        ext X
        constructor
        · intro hX
          by_cases hXIv : X ∈ Iv
          · rw [hIv_eq] at hXIv; simp only [Finset.mem_insert, Finset.mem_singleton] at hXIv ⊢
            rcases hXIv with rfl | rfl | rfl <;> tauto
          · have hXout : X ∈ L3 \ Iv := Finset.mem_sdiff.mpr ⟨hX, hXIv⟩
            rw [hDeq] at hXout
            simp [Finset.mem_singleton.mp hXout]
        · intro hX
          simp only [Finset.mem_insert, Finset.mem_singleton] at hX
          rcases hX with rfl | rfl | rfl | rfl <;> assumption
      -- `D` is disjoint from `{v}` and meets each of `A.erase v, B.erase v, C.erase v` in 1 point.
      have hD_sub : D ⊆ (D ∩ A.erase v) ∪ ((D ∩ B.erase v) ∪ (D ∩ C.erase v)) := by
        intro u hu
        have huv : u ≠ v := fun h => hvD (h ▸ hu)
        have humem : u ∈ Iv.biUnion (fun b => b.erase v) := by rw [hcov_v]; simp [huv]
        obtain ⟨T, hTIv, huT⟩ := Finset.mem_biUnion.mp humem
        rw [hIv_eq] at hTIv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hTIv
        rcases hTIv with rfl | rfl | rfl
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hu, huT⟩)
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hu, huT⟩))
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hu, huT⟩))
      have hDA_le : (D ∩ A.erase v).card ≤ 1 := by
        calc (D ∩ A.erase v).card ≤ (D ∩ A).card :=
              Finset.card_le_card (Finset.inter_subset_inter_left (Finset.erase_subset _ _))
          _ ≤ 1 := hlin D (Finset.mem_filter.mp hDL3).1 A (Finset.mem_filter.mp hAL3).1
              (fun h => hvD (h ▸ hvA))
      have hDB_le : (D ∩ B.erase v).card ≤ 1 := by
        calc (D ∩ B.erase v).card ≤ (D ∩ B).card :=
              Finset.card_le_card (Finset.inter_subset_inter_left (Finset.erase_subset _ _))
          _ ≤ 1 := hlin D (Finset.mem_filter.mp hDL3).1 B (Finset.mem_filter.mp hBL3).1
              (fun h => hvD (h ▸ hvB))
      have hDC_le : (D ∩ C.erase v).card ≤ 1 := by
        calc (D ∩ C.erase v).card ≤ (D ∩ C).card :=
              Finset.card_le_card (Finset.inter_subset_inter_left (Finset.erase_subset _ _))
          _ ≤ 1 := hlin D (Finset.mem_filter.mp hDL3).1 C (Finset.mem_filter.mp hCL3).1
              (fun h => hvD (h ▸ hvC))
      have hsumD : 3 ≤ (D ∩ A.erase v).card + (D ∩ B.erase v).card + (D ∩ C.erase v).card := by
        have h1 := Finset.card_le_card hD_sub
        have h2 := Finset.card_union_le (D ∩ A.erase v) ((D ∩ B.erase v) ∪ (D ∩ C.erase v))
        have h3 := Finset.card_union_le (D ∩ B.erase v) (D ∩ C.erase v)
        have hDc := hall3 D hDL3
        omega
      obtain ⟨a1, ha1eq⟩ := Finset.card_eq_one.mp (by omega : (D ∩ A.erase v).card = 1)
      obtain ⟨b1, hb1eq⟩ := Finset.card_eq_one.mp (by omega : (D ∩ B.erase v).card = 1)
      obtain ⟨c1, hc1eq⟩ := Finset.card_eq_one.mp (by omega : (D ∩ C.erase v).card = 1)
      have ha1D : a1 ∈ D := (Finset.mem_inter.mp (by rw [ha1eq]; simp)).1
      have ha1Ae : a1 ∈ A.erase v := (Finset.mem_inter.mp (by rw [ha1eq]; simp)).2
      have hb1D : b1 ∈ D := (Finset.mem_inter.mp (by rw [hb1eq]; simp)).1
      have hb1Be : b1 ∈ B.erase v := (Finset.mem_inter.mp (by rw [hb1eq]; simp)).2
      have hc1D : c1 ∈ D := (Finset.mem_inter.mp (by rw [hc1eq]; simp)).1
      have hc1Ce : c1 ∈ C.erase v := (Finset.mem_inter.mp (by rw [hc1eq]; simp)).2
      obtain ⟨a2, ha2eq⟩ := Finset.card_eq_one.mp (by
        rw [Finset.card_erase_of_mem ha1Ae, Finset.card_erase_of_mem hvA, hall3 A hAL3])
      obtain ⟨b2, hb2eq⟩ := Finset.card_eq_one.mp (by
        rw [Finset.card_erase_of_mem hb1Be, Finset.card_erase_of_mem hvB, hall3 B hBL3])
      obtain ⟨c2, hc2eq⟩ := Finset.card_eq_one.mp (by
        rw [Finset.card_erase_of_mem hc1Ce, Finset.card_erase_of_mem hvC, hall3 C hCL3])
      have ha1v : a1 ≠ v := (Finset.mem_erase.mp ha1Ae).1
      have ha1A : a1 ∈ A := (Finset.mem_erase.mp ha1Ae).2
      have hb1v : b1 ≠ v := (Finset.mem_erase.mp hb1Be).1
      have hb1B : b1 ∈ B := (Finset.mem_erase.mp hb1Be).2
      have hc1v : c1 ≠ v := (Finset.mem_erase.mp hc1Ce).1
      have hc1C : c1 ∈ C := (Finset.mem_erase.mp hc1Ce).2
      have ha2_in : a2 ∈ (A.erase v).erase a1 := by rw [ha2eq]; simp
      have hb2_in : b2 ∈ (B.erase v).erase b1 := by rw [hb2eq]; simp
      have hc2_in : c2 ∈ (C.erase v).erase c1 := by rw [hc2eq]; simp
      have ha21 : a2 ≠ a1 := (Finset.mem_erase.mp ha2_in).1
      have ha2v : a2 ≠ v := (Finset.mem_erase.mp (Finset.mem_erase.mp ha2_in).2).1
      have ha2A : a2 ∈ A := (Finset.mem_erase.mp (Finset.mem_erase.mp ha2_in).2).2
      have hb21 : b2 ≠ b1 := (Finset.mem_erase.mp hb2_in).1
      have hb2v : b2 ≠ v := (Finset.mem_erase.mp (Finset.mem_erase.mp hb2_in).2).1
      have hb2B : b2 ∈ B := (Finset.mem_erase.mp (Finset.mem_erase.mp hb2_in).2).2
      have hc21 : c2 ≠ c1 := (Finset.mem_erase.mp hc2_in).1
      have hc2v : c2 ≠ v := (Finset.mem_erase.mp (Finset.mem_erase.mp hc2_in).2).1
      have hc2C : c2 ∈ C := (Finset.mem_erase.mp (Finset.mem_erase.mp hc2_in).2).2
      have hAL := (Finset.mem_filter.mp hAL3).1
      have hBL := (Finset.mem_filter.mp hBL3).1
      have hCL := (Finset.mem_filter.mp hCL3).1
      have huniq : ∀ {X Y : Finset (Fin 7)}, X ∈ L → Y ∈ L → X ≠ Y →
          v ∈ X → v ∈ Y → ∀ {x y : Fin 7}, x ∈ X → y ∈ Y → x ≠ v → x ≠ y := by
        intro X Y hXL hYL hXY hvX hvY x y hxX hyY hxv hxy
        subst hxy
        have h2 : 2 ≤ (X ∩ Y).card := by
          calc 2 = ({v, x} : Finset (Fin 7)).card := (Finset.card_pair hxv.symm).symm
            _ ≤ (X ∩ Y).card := Finset.card_le_card (Finset.insert_subset
                (Finset.mem_inter.mpr ⟨hvX, hvY⟩)
                (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hxX, hyY⟩)))
        have := hlin X hXL Y hYL hXY
        omega
      have ha1b1 := huniq hAL hBL hAB hvA hvB ha1A hb1B ha1v
      have ha1c1 := huniq hAL hCL hAC hvA hvC ha1A hc1C ha1v
      have hb1c1 := huniq hBL hCL hBC hvB hvC hb1B hc1C hb1v
      obtain ⟨e, he0, he1, he2, he3, he4, he5, he6⟩ := fin7_equiv_of_seven v a1 a2 b1 b2 c1 c2
        ha1v.symm ha2v.symm hb1v.symm hb2v.symm hc1v.symm hc2v.symm
        ha21.symm ha1b1 (huniq hAL hBL hAB hvA hvB ha1A hb2B ha1v)
        ha1c1 (huniq hAL hCL hAC hvA hvC ha1A hc2C ha1v)
        (huniq hAL hBL hAB hvA hvB ha2A hb1B ha2v) (huniq hAL hBL hAB hvA hvB ha2A hb2B ha2v)
        (huniq hAL hCL hAC hvA hvC ha2A hc1C ha2v) (huniq hAL hCL hAC hvA hvC ha2A hc2C ha2v)
        hb21.symm hb1c1 (huniq hBL hCL hBC hvB hvC hb1B hc2C hb1v)
        (huniq hBL hCL hBC hvB hvC hb2B hc1C hb2v) (huniq hBL hCL hBC hvB hvC hb2B hc2C hb2v)
        hc21.symm
      have hAeq : A = {v, a1, a2} := by
        apply Eq.symm; apply Finset.eq_of_subset_of_card_le
        · exact Finset.insert_subset hvA (Finset.insert_subset ha1A (Finset.singleton_subset_iff.mpr ha2A))
        · rw [Finset.card_insert_of_notMem (by simp [ha1v.symm, ha2v.symm]),
              Finset.card_pair ha21.symm, hall3 A hAL3]
      have hBeq : B = {v, b1, b2} := by
        apply Eq.symm; apply Finset.eq_of_subset_of_card_le
        · exact Finset.insert_subset hvB (Finset.insert_subset hb1B (Finset.singleton_subset_iff.mpr hb2B))
        · rw [Finset.card_insert_of_notMem (by simp [hb1v.symm, hb2v.symm]),
              Finset.card_pair hb21.symm, hall3 B hBL3]
      have hCeq : C = {v, c1, c2} := by
        apply Eq.symm; apply Finset.eq_of_subset_of_card_le
        · exact Finset.insert_subset hvC (Finset.insert_subset hc1C (Finset.singleton_subset_iff.mpr hc2C))
        · rw [Finset.card_insert_of_notMem (by simp [hc1v.symm, hc2v.symm]),
              Finset.card_pair hc21.symm, hall3 C hCL3]
      have hDeq' : D = {a1, b1, c1} := by
        apply Eq.symm; apply Finset.eq_of_subset_of_card_le
        · exact Finset.insert_subset ha1D (Finset.insert_subset hb1D (Finset.singleton_subset_iff.mpr hc1D))
        · rw [Finset.card_insert_of_notMem (by simp [ha1b1, ha1c1]),
              Finset.card_pair hb1c1, hall3 D hDL3]
      obtain ⟨ksize, klin⟩ := relabel_bounds L e hsize hlin
      apply pullback_coloring L e
      apply n7_subset_four_triples_colorable _ ksize klin
      intro U hU hU3
      obtain ⟨X, hXL, rfl⟩ := Finset.mem_image.mp hU
      rw [Finset.card_map] at hU3
      have hXL3 : X ∈ L3 := Finset.mem_filter.mpr ⟨hXL, hU3⟩
      rw [hL3_eq] at hXL3
      simp only [Finset.mem_insert, Finset.mem_singleton] at hXL3
      rcases hXL3 with rfl | rfl | rfl | rfl
      · left; rw [hAeq]; simp [he0, he1, he2]
      · right; left; rw [hBeq]; simp [he0, he3, he4]
      · right; right; left; rw [hCeq]; simp [he0, he5, he6]
      · right; right; right; rw [hDeq']; simp [he1, he3, he5]
    · -- No vertex of excess 3 (`∀ v, ex v ≤ 2`) with `L3.card = 4` is impossible in a critical core.
      exfalso
      push Not at hv3
      have hle2 : ∀ v : Fin 7, ex v ≤ 2 := fun v => by have := hex_le3 v; have := hv3 v; omega
      have hsum12 : ∑ v : Fin 7, ex v = 12 := by omega
      by_cases hex0 : ∃ u : Fin 7, ex u = 0
      · -- Subcase 2a: some `u` has `ex u = 0`, so every `v ≠ u` has `ex v = 2`.
        obtain ⟨u, hu0⟩ := hex0
        have hall2_ne : ∀ v : Fin 7, v ≠ u → ex v = 2 := by
          intro v hvu
          by_contra hne
          have hvle1 : ex v ≤ 1 := by have := hle2 v; omega
          have hsum_split : ∑ x : Fin 7, ex x =
              ex u + ex v + ∑ x ∈ (Finset.univ.erase u).erase v, ex x := by
            have hv_in : v ∈ Finset.univ.erase u := Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩
            rw [← Finset.add_sum_erase Finset.univ ex (Finset.mem_univ u),
                ← Finset.add_sum_erase (Finset.univ.erase u) ex hv_in, add_assoc]
          have hrest : ∑ x ∈ (Finset.univ.erase u).erase v, ex x ≤ 10 := by
            calc ∑ x ∈ (Finset.univ.erase u).erase v, ex x
                ≤ ∑ _x ∈ (Finset.univ.erase u).erase v, 2 :=
                  Finset.sum_le_sum fun x _ => hle2 x
              _ = 10 := by
                  have hv_in : v ∈ Finset.univ.erase u :=
                    Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩
                  rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hv_in]
                  simp
          omega
        obtain ⟨T, hTL3⟩ := Finset.card_pos.mp (by omega : 0 < L3.card)
        have hu_notT : u ∉ T := by
          intro huT
          have : 0 < ex u := Finset.card_pos.mpr ⟨T, Finset.mem_filter.mpr ⟨hTL3, huT⟩⟩
          omega
        let D := (S.erase T).filter fun b => (T ∩ b).Nonempty
        let D3 := D.filter fun b => 3 ≤ b.card
        let D2 := D.filter fun b => ¬ (3 ≤ b.card)
        have hD_card : D.card = D3.card + D2.card := by
          simpa [D3, D2] using (card_filter_add_card_filter_not D (fun b => 3 ≤ b.card)).symm
        have hD3_le : D3.card ≤ 3 := by
          have hsub : D3 ⊆ L3.erase T := fun b hb =>
            Finset.mem_erase.mpr
              ⟨(Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1).1,
               Finset.mem_filter.mpr
                ⟨hSL (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1).2,
                 (Finset.mem_filter.mp hb).2⟩⟩
          have := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem hTL3] at this
          omega
        have hD2_sub : D2 ⊆ T.image (fun a => ({a, u} : Finset (Fin 7))) := by
          intro b hb
          have hbD := (Finset.mem_filter.mp hb).1
          have hb_not3 := (Finset.mem_filter.mp hb).2
          have hbS := (Finset.mem_erase.mp (Finset.mem_filter.mp hbD).1).2
          have hbL := hSL hbS
          have hb2 : b.card = 2 := by have := hsize b hbL; omega
          obtain ⟨a, ha⟩ := (Finset.mem_filter.mp hbD).2
          obtain ⟨haT, hab⟩ := Finset.mem_inter.mp ha
          obtain ⟨w, hwa, rfl⟩ := pair_block_eq hb2 hab
          have hau : a ≠ u := fun h => hu_notT (h ▸ haT)
          have hwu : w = u := by
            by_contra hne
            have hs := hslack7 hwa.symm hbS
            have := hall2_ne a hau
            have := hall2_ne w hne
            omega
          subst w
          exact Finset.mem_image.mpr ⟨a, haT, rfl⟩
        have hD2_le : D2.card ≤ 3 := by
          calc D2.card ≤ (T.image (fun a => ({a, u} : Finset (Fin 7)))).card :=
                Finset.card_le_card hD2_sub
            _ ≤ T.card := Finset.card_image_le
            _ = 3 := hall3 T hTL3
        have hTS : T ∈ S := hL3S T (Finset.mem_filter.mp hTL3).1 (Finset.mem_filter.mp hTL3).2
        have hdeg : 7 ≤ D.card := hcrit T hTS
        omega
      · -- Subcase 2b: `∀ v, 1 ≤ ex v ∧ ex v ≤ 2`, so exactly 2 vertices `p ≠ q` have `ex = 1`.
        push Not at hex0
        have hall1 : ∀ v : Fin 7, 1 ≤ ex v := fun v => by have := hex0 v; omega
        let Low := Finset.univ.filter fun v : Fin 7 => ex v = 1
        let High := Finset.univ.filter fun v : Fin 7 => ex v ≠ 1
        have hLH_card : Low.card + High.card = 7 := by
          simpa [Low, High] using card_filter_add_card_filter_not
            (Finset.univ : Finset (Fin 7)) (fun v => ex v = 1)
        have hLow_card : Low.card = 2 := by
          have hsum_part : ∑ v : Fin 7, ex v = ∑ v ∈ Low, ex v + ∑ v ∈ High, ex v := by
            simpa [Low, High] using (Finset.sum_filter_add_sum_filter_not
              (Finset.univ : Finset (Fin 7)) (fun v => ex v = 1) ex).symm
          have hLow_s : ∑ v ∈ Low, ex v = Low.card := by
            have : ∀ v ∈ Low, ex v = 1 := fun v hv => (Finset.mem_filter.mp hv).2
            rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_one]
          have hHigh_s : ∑ v ∈ High, ex v = 2 * High.card := by
            have : ∀ v ∈ High, ex v = 2 := fun v hv => by
              have h1 := hall1 v; have h2 := hle2 v; have hne := (Finset.mem_filter.mp hv).2; omega
            rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_comm]
          omega
        obtain ⟨p, q, hpq, hLow_eq⟩ := Finset.card_eq_two.mp hLow_card
        have hpLow : p ∈ Low := by rw [hLow_eq]; simp
        have hqLow : q ∈ Low := by rw [hLow_eq]; simp
        have hex_p : ex p = 1 := (Finset.mem_filter.mp hpLow).2
        have hex_q : ex q = 1 := (Finset.mem_filter.mp hqLow).2
        have hex_other : ∀ v : Fin 7, v ≠ p → v ≠ q → ex v = 2 := by
          intro v hvp hvq
          have hv_notLow : v ∉ Low := by rw [hLow_eq]; simp [hvp, hvq]
          have hne1 : ex v ≠ 1 := fun h => hv_notLow (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩)
          have h1 := hall1 v; have h2 := hle2 v; omega
        obtain ⟨Tp, hTp_eq⟩ := Finset.card_eq_one.mp hex_p
        obtain ⟨Tq, hTq_eq⟩ := Finset.card_eq_one.mp hex_q
        have hTp_in : Tp ∈ L3.filter (fun b => p ∈ b) := by rw [hTp_eq]; simp
        have hTq_in : Tq ∈ L3.filter (fun b => q ∈ b) := by rw [hTq_eq]; simp
        have hTpL3 : Tp ∈ L3 := (Finset.mem_filter.mp hTp_in).1
        have hpTp : p ∈ Tp := (Finset.mem_filter.mp hTp_in).2
        have hTqL3 : Tq ∈ L3 := (Finset.mem_filter.mp hTq_in).1
        have hqTq : q ∈ Tq := (Finset.mem_filter.mp hTq_in).2
        by_cases hqTp : q ∈ Tp
        · -- If `q ∈ Tp`, the 3 other triples lie in `univ \ {p, q}` (size 5), with the 3rd point `a`
          -- of `Tp` in only 1 of them, so the remaining 2 triples lie inside 4 points: contradiction.
          have hTpe : ((Tp.erase p).erase q).card = 1 := by
            have hq' : q ∈ Tp.erase p := Finset.mem_erase.mpr ⟨hpq.symm, hqTp⟩
            rw [Finset.card_erase_of_mem hq', Finset.card_erase_of_mem hpTp, hall3 Tp hTpL3]
          obtain ⟨a, ha_eq⟩ := Finset.card_eq_one.mp hTpe
          have ha_in : a ∈ (Tp.erase p).erase q := by rw [ha_eq]; simp
          have haq : a ≠ q := (Finset.mem_erase.mp ha_in).1
          have hap : a ≠ p := (Finset.mem_erase.mp (Finset.mem_erase.mp ha_in).2).1
          have haTp : a ∈ Tp := (Finset.mem_erase.mp (Finset.mem_erase.mp ha_in).2).2
          have hex_a : ex a = 2 := hex_other a hap haq
          let Rest := (L3.erase Tp).filter fun T => a ∉ T
          have hRest_ge2 : 2 ≤ Rest.card := by
            have hIn : ((L3.erase Tp).filter fun T => a ∈ T).card = 1 := by
              have heq : (L3.erase Tp).filter (fun T => a ∈ T) =
                  (L3.filter fun T => a ∈ T).erase Tp := by
                ext T; simp; tauto
              rw [heq, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hTpL3, haTp⟩)]
              change ex a - 1 = 1; omega
            have hsum := card_filter_add_card_filter_not (L3.erase Tp) (fun T => a ∈ T)
            rw [Finset.card_erase_of_mem hTpL3, hL3_4] at hsum
            change ((L3.erase Tp).filter fun T => a ∈ T).card + Rest.card = 3 at hsum
            omega
          obtain ⟨X, hXR, Y, hYR, hXY⟩ := Finset.one_lt_card.mp (by omega : 1 < Rest.card)
          have hXL3 : X ∈ L3 := (Finset.mem_erase.mp (Finset.mem_filter.mp hXR).1).2
          have hXTp : X ≠ Tp := (Finset.mem_erase.mp (Finset.mem_filter.mp hXR).1).1
          have haX : a ∉ X := (Finset.mem_filter.mp hXR).2
          have hYL3 : Y ∈ L3 := (Finset.mem_erase.mp (Finset.mem_filter.mp hYR).1).2
          have hYTp : Y ≠ Tp := (Finset.mem_erase.mp (Finset.mem_filter.mp hYR).1).1
          have haY : a ∉ Y := (Finset.mem_filter.mp hYR).2
          have hp_not : ∀ T ∈ L3, T ≠ Tp → p ∉ T := fun T hT hne hpT => by
            have : T ∈ L3.filter (fun b => p ∈ b) := Finset.mem_filter.mpr ⟨hT, hpT⟩
            rw [hTp_eq] at this; exact hne (Finset.mem_singleton.mp this)
          have hTp_eq_Tq : Tq = Tp := by
            have : Tp ∈ L3.filter (fun b => q ∈ b) := Finset.mem_filter.mpr ⟨hTpL3, hqTp⟩
            rw [hTq_eq] at this; exact (Finset.mem_singleton.mp this).symm
          have hq_not : ∀ T ∈ L3, T ≠ Tp → q ∉ T := fun T hT hne hqT => by
            have : T ∈ L3.filter (fun b => q ∈ b) := Finset.mem_filter.mpr ⟨hT, hqT⟩
            rw [hTq_eq, hTp_eq_Tq] at this; exact hne (Finset.mem_singleton.mp this)
          let F3 : Finset (Fin 7) := {p, q, a}
          have hF3_card : F3.card = 3 := by
            simp only [F3]
            rw [Finset.card_insert_of_notMem (by simp [hpq, hap.symm]), Finset.card_pair haq.symm]
          have hXY_sub : X ∪ Y ⊆ Finset.univ \ F3 := by
            intro u hu
            refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, ?_⟩
            simp only [F3, Finset.mem_insert, Finset.mem_singleton, not_or]
            rcases Finset.mem_union.mp hu with huX | huY
            · exact ⟨fun h => hp_not X hXL3 hXTp (h ▸ huX),
                     fun h => hq_not X hXL3 hXTp (h ▸ huX),
                     fun h => haX (h ▸ huX)⟩
            · exact ⟨fun h => hp_not Y hYL3 hYTp (h ▸ huY),
                     fun h => hq_not Y hYL3 hYTp (h ▸ huY),
                     fun h => haY (h ▸ huY)⟩
          have hle4 : (X ∪ Y).card ≤ 4 := by
            calc (X ∪ Y).card ≤ (Finset.univ \ F3).card := Finset.card_le_card hXY_sub
              _ = 4 := by rw [card_sdiff_sub (Finset.subset_univ F3), Finset.card_univ,
                  Fintype.card_fin, hF3_card]
          have hun := Finset.card_union_add_card_inter X Y
          have hcap := hlin X (Finset.mem_filter.mp hXL3).1 Y (Finset.mem_filter.mp hYL3).1 hXY
          rw [hall3 X hXL3, hall3 Y hYL3] at hun
          omega
        · -- `q ∉ Tp`, so `Tp ≠ Tq`. Any `ex = 2` vertex lying in `Tp` or `Tq` has ZERO `S`-edges!
          have hno_S_edge : ∀ {u r : Fin 7}, ex u = 2 → r ∈ ({p, q} : Finset (Fin 7)) →
              (∃ T ∈ L3, u ∈ T ∧ r ∈ T) →
              ∀ z : Fin 7, z ≠ u → ({u, z} : Finset (Fin 7)) ∉ S := by
            intro u r hu2 hr hTr z hzu heS
            obtain ⟨T, hTL3, huT, hrT⟩ := hTr
            have heL : ({u, z} : Finset (Fin 7)) ∈ L := hSL heS
            have hslack := hslack7 hzu.symm heS
            have hz1 : ex z = 1 := by have := hall1 z; omega
            have hmiss_u : ((L \ S).filter fun b => u ∈ b).card = 0 := by omega
            -- `u` lies in 2 triples (`ex u = 2`) and thus in 2 edges of `L` (`r(u) = 6 - 2 = 4`).
            have hdeg_u := point_degree_plus_excess (by omega) L hsize hlin hcovers u
            rw [hex_eq u, hu2] at hdeg_u
            -- The 2 triples containing `u` cover 4 vertices ≠ u; only 2 vertices remain,
            -- one is `z`, and the other `w` cannot lie in `{p, q}` because `r` is already in `T`!
            have hr_ne_u : r ≠ u := by
              intro h; subst h
              simp only [Finset.mem_insert, Finset.mem_singleton] at hr
              rcases hr with rfl | rfl <;> omega
            have hz_ne_r : z ≠ r := by
              intro hzr; subst z
              have h2 : 2 ≤ (T ∩ {u, r}).card := by
                calc 2 = ({u, r} : Finset (Fin 7)).card := (Finset.card_pair hzu.symm).symm
                  _ ≤ (T ∩ {u, r}).card := Finset.card_le_card (Finset.insert_subset
                      (Finset.mem_inter.mpr ⟨huT, by simp⟩)
                      (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hrT, by simp⟩)))
              have hne : T ≠ {u, r} := by
                intro eq; have := hall3 T hTL3; rw [eq, Finset.card_pair hzu.symm] at this; omega
              have := hlin T (Finset.mem_filter.mp hTL3).1 {u, r} heL hne
              omega
            -- Count size-2 blocks of `L` containing `u`: there are `4 - 2 = 2` of them.
            let E2u := (L.filter fun b => u ∈ b) \ (L3.filter fun b => u ∈ b)
            have hE2u_card : E2u.card = 2 := by
              have hsub : L3.filter (fun b => u ∈ b) ⊆ L.filter (fun b => u ∈ b) :=
                Finset.filter_subset_filter _ (Finset.filter_subset _ _)
              dsimp only [E2u]
              rw [card_sdiff_sub hsub]
              change (L.filter fun b => u ∈ b).card - ex u = 2
              omega
            have he_in_E2u : ({u, z} : Finset (Fin 7)) ∈ E2u := by
              refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨heL, by simp⟩, ?_⟩
              intro h
              have := hall3 _ (Finset.mem_filter.mp h).1
              rw [Finset.card_pair hzu.symm] at this; omega
            obtain ⟨e2, he2_eq⟩ := Finset.card_eq_one.mp
              (by rw [Finset.card_erase_of_mem he_in_E2u, hE2u_card])
            have he2_in : e2 ∈ E2u.erase {u, z} := by rw [he2_eq]; simp
            have he2_ne : e2 ≠ {u, z} := (Finset.mem_erase.mp he2_in).1
            have he2L : e2 ∈ L := (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_erase.mp he2_in).2).1).1
            have hue2 : u ∈ e2 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_erase.mp he2_in).2).1).2
            have he2_not3 : ¬ (3 ≤ e2.card) := fun h =>
              (Finset.mem_sdiff.mp (Finset.mem_erase.mp he2_in).2).2
                (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨he2L, h⟩, hue2⟩)
            have he2_2 : e2.card = 2 := by have := hsize e2 he2L; omega
            obtain ⟨w, hwu, rfl⟩ := pair_block_eq he2_2 hue2
            have hw_ne_z : w ≠ z := fun h => he2_ne (by rw [h])
            have hw_ne_r : w ≠ r := by
              intro hwr; subst w
              have h2 : 2 ≤ (T ∩ {u, r}).card := by
                calc 2 = ({u, r} : Finset (Fin 7)).card := (Finset.card_pair hwu.symm).symm
                  _ ≤ (T ∩ {u, r}).card := Finset.card_le_card (Finset.insert_subset
                      (Finset.mem_inter.mpr ⟨huT, by simp⟩)
                      (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hrT, by simp⟩)))
              have hne : T ≠ {u, r} := by
                intro eq; have := hall3 T hTL3; rw [eq, Finset.card_pair hwu.symm] at this; omega
              have := hlin T (Finset.mem_filter.mp hTL3).1 {u, r} he2L hne
              omega
            -- Since `z ∈ Low`, `r ∈ Low`, `z ≠ r`, and `Low = {p, q}`, we must have `w ∉ {p, q}`!
            have hzLow : z ∈ ({p, q} : Finset (Fin 7)) := by
              rw [← hLow_eq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz1⟩
            have hw_not_pq : w ∉ ({p, q} : Finset (Fin 7)) := by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hr hzLow ⊢
              rcases hr with rfl | rfl <;> rcases hzLow with rfl | rfl <;> simp_all
            have hw2 : ex w = 2 := by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw_not_pq
              exact hex_other w hw_not_pq.1 hw_not_pq.2
            -- By `hmiss_u = 0`, `{u, w} ∈ S`, contradicting `ex u + ex w = 4 > 3`!
            have he2S : ({u, w} : Finset (Fin 7)) ∈ S := by
              by_contra hnotS
              have hmem : ({u, w} : Finset (Fin 7)) ∈ (L \ S).filter (fun b => u ∈ b) :=
                Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨he2L, hnotS⟩, by simp⟩
              have hpos : 0 < ((L \ S).filter fun b => u ∈ b).card := Finset.card_pos.mpr ⟨_, hmem⟩
              omega
            have hs2 := hslack7 hwu.symm he2S
            omega
          -- Pick a vertex `c ∈ Tq.erase q` with `c ∉ Tp`.
          have hTqTp : Tq ≠ Tp := fun h => hqTp (h ▸ hqTq)
          have hcap_pq := hlin Tq (Finset.mem_filter.mp hTqL3).1 Tp (Finset.mem_filter.mp hTpL3).1 hTqTp
          have hc_ex : ((Tq.erase q) \ Tp).Nonempty := by
            apply Finset.card_pos.mp
            have h1 : (Tq.erase q).card = 2 := by rw [Finset.card_erase_of_mem hqTq, hall3 Tq hTqL3]
            have h2 : ((Tq.erase q) ∩ Tp).card ≤ 1 := by
              calc ((Tq.erase q) ∩ Tp).card ≤ (Tq ∩ Tp).card :=
                    Finset.card_le_card (Finset.inter_subset_inter_right (Finset.erase_subset _ _))
                _ ≤ 1 := hcap_pq
            have h3 := Finset.card_sdiff_add_card_inter (Tq.erase q) Tp
            omega
          obtain ⟨c, hc_in⟩ := hc_ex
          have hcq : c ≠ q := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hc_in).1).1
          have hcTq : c ∈ Tq := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hc_in).1).2
          have hc_notTp : c ∉ Tp := (Finset.mem_sdiff.mp hc_in).2
          have hcp : c ≠ p := fun h => hc_notTp (h ▸ hpTp)
          have hc_ex2 : ex c = 2 := hex_other c hcp hcq
          -- Now bound `d_S(Tp) ≤ 3 + 3 = 6 < 7`!
          let D := (S.erase Tp).filter fun b => (Tp ∩ b).Nonempty
          let D3 := D.filter fun b => 3 ≤ b.card
          let D2 := D.filter fun b => ¬ (3 ≤ b.card)
          have hD_card : D.card = D3.card + D2.card := by
            simpa [D3, D2] using (card_filter_add_card_filter_not D (fun b => 3 ≤ b.card)).symm
          have hD3_le : D3.card ≤ 3 := by
            have hsub : D3 ⊆ L3.erase Tp := fun b hb =>
              Finset.mem_erase.mpr
                ⟨(Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1).1,
                 Finset.mem_filter.mpr
                  ⟨hSL (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1).2,
                   (Finset.mem_filter.mp hb).2⟩⟩
            have := Finset.card_le_card hsub
            rw [Finset.card_erase_of_mem hTpL3] at this
            omega
          have hD2_sub : D2 ⊆ (Finset.univ \ (insert c Tp)).image (fun w => ({p, w} : Finset (Fin 7))) := by
            intro b hb
            have hbD := (Finset.mem_filter.mp hb).1
            have hb_not3 := (Finset.mem_filter.mp hb).2
            have hbSe := (Finset.mem_filter.mp hbD).1
            have hbTp := (Finset.mem_erase.mp hbSe).1
            have hbS := (Finset.mem_erase.mp hbSe).2
            have hbL := hSL hbS
            have hb2 : b.card = 2 := by have := hsize b hbL; omega
            obtain ⟨a, ha⟩ := (Finset.mem_filter.mp hbD).2
            obtain ⟨haTp, hab⟩ := Finset.mem_inter.mp ha
            obtain ⟨w, hwa, rfl⟩ := pair_block_eq hb2 hab
            have hap : a = p := by
              by_contra hne
              have haq : a ≠ q := fun h => hqTp (h ▸ haTp)
              have ha2 : ex a = 2 := hex_other a hne haq
              exact hno_S_edge ha2 (by simp) ⟨Tp, hTpL3, haTp, hpTp⟩ w hwa hbS
            subst a
            have hw_notTp : w ∉ Tp := by
              intro hwTp
              have h2 : 2 ≤ (Tp ∩ {p, w}).card := by
                calc 2 = ({p, w} : Finset (Fin 7)).card := (Finset.card_pair hwa.symm).symm
                  _ ≤ (Tp ∩ {p, w}).card := Finset.card_le_card (Finset.insert_subset
                      (Finset.mem_inter.mpr ⟨hpTp, by simp⟩)
                      (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hwTp, by simp⟩)))
              have := hlin Tp (Finset.mem_filter.mp hTpL3).1 {p, w} hbL hbTp.symm
              omega
            have hwc : w ≠ c := by
              intro hwc; subst w
              have heS' : ({c, p} : Finset (Fin 7)) ∈ S := by
                rwa [Finset.pair_comm]
              exact hno_S_edge hc_ex2 (by simp) ⟨Tq, hTqL3, hcTq, hqTq⟩ p hcp.symm heS'
            exact Finset.mem_image.mpr ⟨w,
              Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, by simp [hwc, hw_notTp]⟩, rfl⟩
          have hD2_le : D2.card ≤ 3 := by
            calc D2.card ≤ ((Finset.univ \ (insert c Tp)).image
                  (fun w => ({p, w} : Finset (Fin 7)))).card := Finset.card_le_card hD2_sub
              _ ≤ (Finset.univ \ (insert c Tp)).card := Finset.card_image_le
              _ = 3 := by
                  rw [card_sdiff_sub (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
                    Finset.card_insert_of_notMem hc_notTp, hall3 Tp hTpL3]
          have hTpS : Tp ∈ S := hL3S Tp (Finset.mem_filter.mp hTpL3).1 (Finset.mem_filter.mp hTpL3).2
          have hdeg : 7 ≤ D.card := hcrit Tp hTpS
          omega

/- ### Part 6: Reduced hypotheses and main theorem -/

/-- Critical linear spaces on 8 to 10 points with more than n blocks, at least 3 large
blocks of size at most n - 4, and pairwise intersecting large blocks when there are 3. -/
def H1 : Prop := ∀ (n : ℕ) (L : Finset (Finset (Fin n))),
    8 ≤ n → n ≤ 10 →
    (∀ a ∈ L, 2 ≤ a.card) →
    (∀ a ∈ L, ∀ b ∈ L, a ≠ b → (a ∩ b).card ≤ 1) →
    (∀ i j : Fin n, i ≠ j → ∃ e ∈ L, i ∈ e ∧ j ∈ e) →
    (∃ S ⊆ L, (∀ a ∈ L, 3 ≤ a.card → a ∈ S) ∧
      ∀ a ∈ S, n ≤ ((S.erase a).filter fun b => (a ∩ b).Nonempty).card) →
    n < L.card →
    3 ≤ (L.filter fun b => 3 ≤ b.card).card →
    (∀ b ∈ L, b.card + 4 ≤ n) →
    ((L.filter fun b => 3 ≤ b.card).card = 3 →
      ∀ a ∈ L.filter (fun b => 3 ≤ b.card), ∀ b ∈ L.filter (fun b => 3 ≤ b.card),
        (a ∩ b).Nonempty) →
    ∃ c : L → Fin n, ∀ A B : L, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B

/-- Critical linear spaces on 11 or 12 points with more than n blocks, at least 3 large
blocks of size at most n - 4, and pairwise intersecting large blocks when there are 3. -/
def H2 : Prop := ∀ (n : ℕ) (L : Finset (Finset (Fin n))),
    11 ≤ n → n ≤ 12 →
    (∀ a ∈ L, 2 ≤ a.card) →
    (∀ a ∈ L, ∀ b ∈ L, a ≠ b → (a ∩ b).card ≤ 1) →
    (∀ i j : Fin n, i ≠ j → ∃ e ∈ L, i ∈ e ∧ j ∈ e) →
    (∃ S ⊆ L, (∀ a ∈ L, 3 ≤ a.card → a ∈ S) ∧
      ∀ a ∈ S, n ≤ ((S.erase a).filter fun b => (a ∩ b).Nonempty).card) →
    n < L.card →
    3 ≤ (L.filter fun b => 3 ≤ b.card).card →
    (∀ b ∈ L, b.card + 4 ≤ n) →
    ((L.filter fun b => 3 ≤ b.card).card = 3 →
      ∀ a ∈ L.filter (fun b => 3 ≤ b.card), ∀ b ∈ L.filter (fun b => 3 ≤ b.card),
        (a ∩ b).Nonempty) →
    ∃ c : L → Fin n, ∀ A B : L, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B

/-- Checked critical linear spaces on 13 points with at least 14 blocks, at least 3 large
blocks of size at most 9, and pairwise intersecting large blocks when there are 3. -/
def H3 : Prop := ∀ (L : Finset (Finset (Fin 13))),
    (∀ a ∈ L, 2 ≤ a.card) →
    (∀ a ∈ L, ∀ b ∈ L, a ≠ b → (a ∩ b).card ≤ 1) →
    (∀ i j : Fin 13, i ≠ j → ∃ e ∈ L, i ∈ e ∧ j ∈ e) →
    (∃ S ⊆ L, (∀ a ∈ L, 3 ≤ a.card → a ∈ S) ∧
      ∀ a ∈ S, 13 ≤ ((S.erase a).filter fun b => (a ∩ b).Nonempty).card) →
    14 ≤ L.card →
    3 ≤ (L.filter fun b => 3 ≤ b.card).card →
    (∀ b ∈ L, b.card ≤ 9) →
    ((L.filter fun b => 3 ≤ b.card).card = 3 →
      ∀ a ∈ L.filter (fun b => 3 ≤ b.card), ∀ b ∈ L.filter (fun b => 3 ≤ b.card),
        (a ∩ b).Nonempty) →
    (L.card ≤ 32 ∨ 55 ≤ L.card ∨
      ((L.filter fun b => 3 ≤ b.card).biUnion id).card ≤ 11 ∨
      (∃ b ∈ L, 7 ≤ b.card) ∨ 20 ≤ (L.filter fun b => 3 ≤ b.card).card) →
    ∃ c : L → Fin 13, ∀ A B : L, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B

theorem main : H1 → H2 → H3 → OMA.R_Erdos19_erdos_19_R1_H1_R1.H1 := by
  intro h1 h2 h3 n L hsize hlin hcovers hcore hrange
  by_cases hcard : L.card ≤ n
  · exact card_le_n_colorable L hcard
  have hgt : n < L.card := by omega
  by_cases hgap : ∃ b ∈ L, n ≤ b.card + 3
  · exact large_block_gap_le_three_colorable L hsize hlin hcovers hcore hgap
  push Not at hgap
  have hgap4 : ∀ b ∈ L, b.card + 4 ≤ n := fun b hb => by have := hgap b hb; omega
  by_cases hn6 : n ≤ 6
  · exact n_le_six_colorable hn6 L hsize hlin hcovers hcore
  by_cases hn7 : n = 7
  · subst hn7
    exact n_eq_seven_colorable L hsize hlin hcovers hcore
  have hn_pos : 0 < n := by omega
  by_cases hL3_small : (L.filter fun b => 3 ≤ b.card).card ≤ 2
  · exact at_most_two_large_colorable hn_pos L hsize hlin hL3_small
  have hL3_ge3 : 3 ≤ (L.filter fun b => 3 ≤ b.card).card := by omega
  by_cases h3disj : (L.filter fun b => 3 ≤ b.card).card = 3 ∧
      ∃ A ∈ L.filter (fun b => 3 ≤ b.card),
        ∃ B ∈ L.filter (fun b => 3 ≤ b.card), Disjoint A B
  · exact three_large_with_disjoint_colorable hn_pos L hsize hlin h3disj.1 h3disj.2
  have h3meet : (L.filter fun b => 3 ≤ b.card).card = 3 →
      ∀ a ∈ L.filter (fun b => 3 ≤ b.card), ∀ b ∈ L.filter (fun b => 3 ≤ b.card),
        (a ∩ b).Nonempty := by
    intro h3 a ha b hb
    by_contra hnot
    rw [Finset.not_nonempty_iff_eq_empty] at hnot
    exact h3disj ⟨h3, a, ha, b, hb, Finset.disjoint_iff_inter_eq_empty.mpr hnot⟩
  rcases hrange with hn12 | ⟨rfl, h13cond⟩
  · by_cases hn10 : n ≤ 10
    · exact h1 n L (by omega) hn10 hsize hlin hcovers hcore hgt hL3_ge3 hgap4 h3meet
    · exact h2 n L (by omega) hn12 hsize hlin hcovers hcore hgt hL3_ge3 hgap4 h3meet
  · exact h3 L hsize hlin hcovers hcore (by omega) hL3_ge3
      (fun b hb => by have := hgap4 b hb; omega) h3meet h13cond

end OMA.R_Erdos19_erdos_19_R1_H1_R1_H1_R1
