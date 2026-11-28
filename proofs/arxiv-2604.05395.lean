import OMAStatements.S_arxiv_2604_05395
namespace OMA.P_arxiv_2604_05395

open OMA.S_arxiv_2604_05395

/-- The Fano plane lattice `PG(2, 2)`: the finite modular lattice of all subspaces of `(ZMod 2)^3`. -/
private abbrev FanoLat := Submodule (ZMod 2) (Fin 3 → ZMod 2)

private noncomputable instance : Fintype FanoLat := by
  classical
  exact Fintype.ofInjective (fun S : FanoLat => (S : Set (Fin 3 → ZMod 2)))
    (fun _ _ h => SetLike.coe_injective h)

/-- Concrete 1-dimensional subspace spanned by a nonzero vector `v ∈ (ZMod 2)^3`. -/
private def lineSub (v : Fin 3 → ZMod 2) : FanoLat :=
  Submodule.span (ZMod 2) {v}

/-- Concrete 2-dimensional subspace `{x | x 2 = 0}` (the plane `z = 0`). -/
private def planeZ0 : FanoLat where
  carrier := { x | x 2 = 0 }
  add_mem' := by
    intro a b ha hb
    change a 2 = 0 at ha
    change b 2 = 0 at hb
    change a 2 + b 2 = 0
    rw [ha, hb, add_zero]
  zero_mem' := rfl
  smul_mem' := by
    intro c x hx
    change x 2 = 0 at hx
    change c * x 2 = 0
    rw [hx, mul_zero]

private def vA : Fin 3 → ZMod 2 := ![1, 0, 0]
private def vB : Fin 3 → ZMod 2 := ![0, 1, 0]
private def vD : Fin 3 → ZMod 2 := ![0, 0, 1]

private def p0 : FanoLat := ⊥
private lemma p0_le (z : FanoLat) : p0 ≤ z := bot_le
private def pA : FanoLat := lineSub vA
private def pB : FanoLat := lineSub vB
private def pD : FanoLat := lineSub vD
private def pH : FanoLat := planeZ0

private lemma vA_ne0 : vA ≠ 0 := fun h => absurd (congrFun h 0) (by decide)
private lemma vB_ne0 : vB ≠ 0 := fun h => absurd (congrFun h 1) (by decide)
private lemma vD_ne0 : vD ≠ 0 := fun h => absurd (congrFun h 2) (by decide)

private lemma mem_lineSub_iff (v x : Fin 3 → ZMod 2) :
    x ∈ lineSub v ↔ x = 0 ∨ x = v := by
  rw [lineSub, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    match c with
    | 0 => exact Or.inl (zero_smul _ _)
    | 1 => exact Or.inr (one_smul _ _)
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

private lemma lineSub_isAtom {v : Fin 3 → ZMod 2} (hv : v ≠ 0) :
    ∀ u : FanoLat, u < lineSub v → u = p0 := by
  intro u hu
  rw [p0, eq_bot_iff]
  intro x hx
  have hmem : x ∈ lineSub v := hu.le hx
  rw [mem_lineSub_iff] at hmem
  rcases hmem with rfl | rfl
  · exact Submodule.zero_mem _
  · exfalso
    apply hu.ne
    apply le_antisymm hu.le
    rw [lineSub, Submodule.span_singleton_le_iff_mem]
    exact hx

private lemma lineSub_ne_bot {v : Fin 3 → ZMod 2} (hv : v ≠ 0) : lineSub v ≠ p0 := by
  intro h
  have hm : v ∈ lineSub v := Submodule.subset_span (Set.mem_singleton v)
  rw [h] at hm
  exact hv ((Submodule.mem_bot (ZMod 2)).mp hm)

private lemma pA_ne_bot : pA ≠ p0 := lineSub_ne_bot vA_ne0
private lemma pB_ne_bot : pB ≠ p0 := lineSub_ne_bot vB_ne0
private lemma pD_ne_bot : pD ≠ p0 := lineSub_ne_bot vD_ne0

private lemma pA_ne_pB : pA ≠ pB := by
  intro h
  have hv : vA ∈ pB := h ▸ Submodule.subset_span (Set.mem_singleton vA)
  rw [pB, mem_lineSub_iff] at hv
  rcases hv with h0 | h1
  · exact absurd (congrFun h0 0) (by decide)
  · exact absurd (congrFun h1 0) (by decide)

private lemma pA_ne_pD : pA ≠ pD := by
  intro h
  have hv : vA ∈ pD := h ▸ Submodule.subset_span (Set.mem_singleton vA)
  rw [pD, mem_lineSub_iff] at hv
  rcases hv with h0 | h1
  · exact absurd (congrFun h0 0) (by decide)
  · exact absurd (congrFun h1 0) (by decide)

private lemma pB_ne_pD : pB ≠ pD := by
  intro h
  have hv : vB ∈ pD := h ▸ Submodule.subset_span (Set.mem_singleton vB)
  rw [pD, mem_lineSub_iff] at hv
  rcases hv with h0 | h1
  · exact absurd (congrFun h0 1) (by decide)
  · exact absurd (congrFun h1 1) (by decide)

private lemma pA_lt_pH : pA < pH := by
  constructor
  · rw [pA, lineSub, Submodule.span_singleton_le_iff_mem]
    change vA 2 = 0; decide
  · intro hle
    have hvb : vB ∈ pA := hle (show vB 2 = 0 by decide)
    rw [pA, mem_lineSub_iff] at hvb
    rcases hvb with h0 | h1
    · exact absurd (congrFun h0 1) (by decide)
    · exact absurd (congrFun h1 1) (by decide)

private lemma pB_lt_pH : pB < pH := by
  constructor
  · rw [pB, lineSub, Submodule.span_singleton_le_iff_mem]
    change vB 2 = 0; decide
  · intro hle
    have hva : vA ∈ pB := hle (show vA 2 = 0 by decide)
    rw [pB, mem_lineSub_iff] at hva
    rcases hva with h0 | h1
    · exact absurd (congrFun h0 0) (by decide)
    · exact absurd (congrFun h1 0) (by decide)

private lemma pH_incomp_pD : ¬ pH ≤ pD ∧ ¬ pD ≤ pH := by
  constructor
  · intro hle
    have hva : vA ∈ pD := hle (show vA 2 = 0 by decide)
    rw [pD, mem_lineSub_iff] at hva
    rcases hva with h0 | h1
    · exact absurd (congrFun h0 0) (by decide)
    · exact absurd (congrFun h1 0) (by decide)
  · intro hle
    have hvd : vD ∈ pH := hle (Submodule.subset_span (Set.mem_singleton vD))
    have : vD 2 = 0 := hvd
    exact absurd this (by decide)

private lemma lines_incomp {u₁ u₂ : Fin 3 → ZMod 2} (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (hne : lineSub u₁ ≠ lineSub u₂) :
    ¬ lineSub u₁ ≤ lineSub u₂ ∧ ¬ lineSub u₂ ≤ lineSub u₁ := by
  constructor
  · intro hle
    have hlt : lineSub u₁ < lineSub u₂ := lt_of_le_of_ne hle hne
    exact lineSub_ne_bot hu₁ (lineSub_isAtom hu₂ _ hlt)
  · intro hle
    have hlt : lineSub u₂ < lineSub u₁ := lt_of_le_of_ne hle hne.symm
    exact lineSub_ne_bot hu₂ (lineSub_isAtom hu₁ _ hlt)

/-- Key geometric property of `PG(2, 2)`: for any two lines `L₁, L₂` and any element
`w ∉ {⊥, L₁, L₂}`, there exists a line `L₃ ∉ {L₁, L₂}` with `L₃ ≤ w`. -/
private lemma exists_third_line {v₁ v₂ : Fin 3 → ZMod 2} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (w : FanoLat) (hw0 : w ≠ p0) (hw1 : w ≠ lineSub v₁) (hw2 : w ≠ lineSub v₂) :
    ∃ v₃ : Fin 3 → ZMod 2, v₃ ≠ 0 ∧ lineSub v₃ ≤ w ∧
      lineSub v₃ ≠ lineSub v₁ ∧ lineSub v₃ ≠ lineSub v₂ := by
  by_cases hex : ∃ x ∈ w, x ≠ 0 ∧ x ≠ v₁ ∧ x ≠ v₂
  · rcases hex with ⟨x, hxw, hx0, hx1, hx2⟩
    refine ⟨x, hx0, ?_, ?_, ?_⟩
    · rw [lineSub, Submodule.span_singleton_le_iff_mem]; exact hxw
    · intro heq
      have hxm : x ∈ lineSub v₁ := heq ▸ Submodule.subset_span (Set.mem_singleton x)
      rw [mem_lineSub_iff] at hxm
      rcases hxm with rfl | rfl <;> contradiction
    · intro heq
      have hxm : x ∈ lineSub v₂ := heq ▸ Submodule.subset_span (Set.mem_singleton x)
      rw [mem_lineSub_iff] at hxm
      rcases hxm with rfl | rfl <;> contradiction
  · exfalso
    push Not at hex
    have hsub : ∀ x ∈ w, x = 0 ∨ x = v₁ ∨ x = v₂ := by
      intro x hxw
      by_cases h0 : x = 0; · exact Or.inl h0
      by_cases h1 : x = v₁; · exact Or.inr (Or.inl h1)
      exact Or.inr (Or.inr (hex x hxw h0 h1))
    by_cases h1w : v₁ ∈ w
    · by_cases h2w : v₂ ∈ w
      · by_cases hv12 : v₁ = v₂
        · apply hw1
          apply le_antisymm
          · intro x hxw
            rw [mem_lineSub_iff]
            rcases hsub x hxw with rfl | rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr rfl
            · exact Or.inr hv12.symm
          · rw [lineSub, Submodule.span_singleton_le_iff_mem]; exact h1w
        · have hsum_mem : v₁ + v₂ ∈ w := w.add_mem h1w h2w
          have hsum_ne0 : v₁ + v₂ ≠ 0 := by
            intro h0
            apply hv12
            ext i
            have hi : v₁ i + v₂ i = 0 := congrFun h0 i
            have hz2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
            exact hz2 _ _ hi
          have hsum_ne1 : v₁ + v₂ ≠ v₁ := fun h => hv₂ (by simpa using h)
          have hsum_ne2 : v₁ + v₂ ≠ v₂ := fun h => hv₁ (by simpa using h)
          exact hsum_ne2 (hex (v₁ + v₂) hsum_mem hsum_ne0 hsum_ne1)
      · apply hw1
        apply le_antisymm
        · intro x hxw
          rw [mem_lineSub_iff]
          rcases hsub x hxw with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exact absurd hxw h2w
        · rw [lineSub, Submodule.span_singleton_le_iff_mem]; exact h1w
    · by_cases h2w : v₂ ∈ w
      · apply hw2
        apply le_antisymm
        · intro x hxw
          rw [mem_lineSub_iff]
          rcases hsub x hxw with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact absurd hxw h1w
          · exact Or.inr rfl
        · rw [lineSub, Submodule.span_singleton_le_iff_mem]; exact h2w
      · apply hw0
        rw [p0, eq_bot_iff]
        intro x hxw
        rcases hsub x hxw with rfl | rfl | rfl
        · exact Submodule.zero_mem _
        · exact absurd hxw h1w
        · exact absurd hxw h2w

/-! ### Algebraic proof that `FanoLat` is not integral over any field `K` -/

private abbrev StdChain := { l : List FanoLat // l.Pairwise (· ≤ ·) }

private def stdMon {R : Type} [CommRing R] (ι : FanoLat → R) (l : StdChain) : R :=
  (l.1.map ι).prod

private def chain1 (x : FanoLat) : StdChain := ⟨[x], by simp⟩

private def chain2 (x y : FanoLat) (h : x ≤ y) : StdChain := ⟨[x, y], by simp [h]⟩

private lemma stdMon_chain1 {R : Type} [CommRing R] (ι : FanoLat → R) (x : FanoLat) :
    stdMon ι (chain1 x) = ι x := by
  simp [stdMon, chain1]

private lemma stdMon_chain2 {R : Type} [CommRing R] (ι : FanoLat → R)
    (x y : FanoLat) (h : x ≤ y) :
    stdMon ι (chain2 x y h) = ι x * ι y := by
  simp [stdMon, chain2]

private lemma chain2_inj {x₁ y₁ x₂ y₂ : FanoLat} {h₁ : x₁ ≤ y₁} {h₂ : x₂ ≤ y₂}
    (heq : chain2 x₁ y₁ h₁ = chain2 x₂ y₂ h₂) : x₁ = x₂ ∧ y₁ = y₂ := by
  have hlist : ([x₁, y₁] : List FanoLat) = [x₂, y₂] := congrArg Subtype.val heq
  simpa using hlist

private lemma prod_incomp_bot
    {K : Type} [Field K] {R : Type} [CommRing R] [Algebra K R] {ι : FanoLat → R}
    (hasl2 : ∀ x y : FanoLat, ¬ x ≤ y → ¬ y ≤ x →
      ι x * ι y ∈ Submodule.span K { r : R | ∃ u v : FanoLat, u ≤ v ∧ u < x ∧ u < y ∧ r = ι u * ι v })
    {x y : FanoLat} (hxy : ¬ x ≤ y) (hyx : ¬ y ≤ x)
    (hinf : ∀ u : FanoLat, u < x → u < y → u = p0) :
    ∃ c : FanoLat → K, ι x * ι y = ι p0 * ∑ w : FanoLat, c w • ι w := by
  classical
  have hmem := hasl2 x y hxy hyx
  have hsub : Submodule.span K { r : R | ∃ u v : FanoLat, u ≤ v ∧ u < x ∧ u < y ∧ r = ι u * ι v } ≤
      Submodule.span K (Set.range (fun w : FanoLat => ι p0 * ι w)) := by
    apply Submodule.span_le.mpr
    rintro r ⟨u, v, _, hux, huy, rfl⟩
    have hu0 : u = p0 := hinf u hux huy
    subst hu0
    exact Submodule.subset_span ⟨v, rfl⟩
  have hmem' : ι x * ι y ∈ Submodule.span K (Set.range (fun w : FanoLat => ι p0 * ι w)) := hsub hmem
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem'
  rcases hmem' with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rw [← hc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [Algebra.mul_smul_comm]

private lemma coeff_eq_of_std_eq
    {K : Type} [Field K] {R : Type} [CommRing R] [Algebra K R] {ι : FanoLat → R}
    (hli : LinearIndependent K (stdMon ι))
    {s : Finset StdChain} {a b : StdChain → K}
    (heq : ∑ l ∈ s, a l • stdMon ι l = ∑ l ∈ s, b l • stdMon ι l)
    {l₀ : StdChain} (hl₀ : l₀ ∈ s) : a l₀ = b l₀ := by
  have hsub : ∑ l ∈ s, (a l - b l) • stdMon ι l = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, heq, sub_self]
  have hzero := (linearIndependent_iff'.mp hli) s (fun l => a l - b l) hsub l₀ hl₀
  exact sub_eq_zero.mp hzero

private lemma fano_not_integral : ¬ IsIntegralPoset FanoLat := by
  classical
  rintro ⟨K, _, R, _, _, _, ι, hli, _, hasl2⟩
  have hli' : LinearIndependent K (stdMon ι) := hli
  have h0_ne : ι p0 ≠ 0 := by
    rw [← stdMon_chain1 ι p0]
    exact hli'.ne_zero (chain1 p0)
  -- Helper: linear independence of `{ι x, ι p0}` for `x ≠ p0`.
  have hsub_ne0 : ∀ (x : FanoLat) (s : K), x ≠ p0 → ι x - s • ι p0 ≠ 0 := by
    intro x s hne h0
    have hc1_ne : chain1 x ≠ chain1 p0 := by
      intro heq
      have : ([x] : List FanoLat) = [p0] := congrArg Subtype.val heq
      exact hne (by simpa using this)
    let S1 : Finset StdChain := {chain1 x, chain1 p0}
    let f : StdChain → K := fun l => if l = chain1 x then 1 else -s
    have hsum : ∑ l ∈ S1, f l • stdMon ι l = 0 := by
      rw [Finset.sum_pair hc1_ne]
      simp only [f, if_pos rfl, if_neg hc1_ne.symm, one_smul, neg_smul, stdMon_chain1]
      rw [← sub_eq_add_neg]
      exact h0
    have h1 := (linearIndependent_iff'.mp hli') S1 f hsum (chain1 x) (Finset.mem_insert_self _ _)
    simp only [f, if_pos rfl] at h1
    exact one_ne_zero h1
  -- Set `S2` of all degree-2 standard chains.
  let S2 : Finset StdChain :=
    Finset.univ.image (fun p : { p : FanoLat × FanoLat // p.1 ≤ p.2 } => chain2 p.1.1 p.1.2 p.2)
  have hmem_S2 : ∀ (x y : FanoLat) (h : x ≤ y), chain2 x y h ∈ S2 := by
    intro x y h
    exact Finset.mem_image.mpr ⟨⟨(x, y), h⟩, Finset.mem_univ _, rfl⟩
  -- Rewrite any sum over `S2` as a double sum over `x, y : FanoLat` with `x ≤ y`.
  have hsum_S2 : ∀ (a : StdChain → K),
      ∑ l ∈ S2, a l • stdMon ι l =
      ∑ x : FanoLat, ∑ y : FanoLat,
        if hxy : x ≤ y then a (chain2 x y hxy) • (ι x * ι y) else 0 := by
    intro a
    rw [Finset.sum_image]
    · -- Convert sum over subtype `{p : FanoLat × FanoLat // p.1 ≤ p.2}` to double sum.
      have h1 : ∑ p : { p : FanoLat × FanoLat // p.1 ≤ p.2 },
          a (chain2 p.1.1 p.1.2 p.2) • stdMon ι (chain2 p.1.1 p.1.2 p.2) =
          ∑ p : FanoLat × FanoLat,
            if hxy : p.1 ≤ p.2 then a (chain2 p.1 p.2 hxy) • (ι p.1 * ι p.2) else 0 := by
        let F := (Finset.univ : Finset (FanoLat × FanoLat)).filter (fun p => p.1 ≤ p.2)
        have h1a : ∑ p : { p : FanoLat × FanoLat // p.1 ≤ p.2 },
            a (chain2 p.1.1 p.1.2 p.2) • stdMon ι (chain2 p.1.1 p.1.2 p.2) =
            ∑ p ∈ F, if hxy : p.1 ≤ p.2 then a (chain2 p.1 p.2 hxy) • (ι p.1 * ι p.2) else 0 := by
          apply Finset.sum_bij (fun p _ => p.1)
          · intro p _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.2⟩
          · intro p₁ _ p₂ _ h; exact Subtype.ext h
          · intro p hp; exact ⟨⟨p, (Finset.mem_filter.mp hp).2⟩, Finset.mem_univ _, rfl⟩
          · intro p _; rw [dif_pos p.2, stdMon_chain2]
        rw [h1a]
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro p _ hp
        have hnot : ¬ p.1 ≤ p.2 := fun h => hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        rw [dif_neg hnot]
      rw [h1, Fintype.sum_prod_type]
    · intro p₁ _ p₂ _ heq
      rcases chain2_inj heq with ⟨h1, h2⟩
      exact Subtype.ext (Prod.ext h1 h2)
  -- Core atom-multiplication lemma: expanding `(∑ w, c w • ι w) * ι v` into the `S2` basis!
  have hmul_atom : ∀ (u₀ : Fin 3 → ZMod 2), u₀ ≠ 0 → ∀ (c : FanoLat → K),
      ∃ a : StdChain → K,
        (∑ w : FanoLat, c w • ι w) * ι (lineSub u₀) = ∑ l ∈ S2, a l • stdMon ι l ∧
        (∀ (w : FanoLat) (hw : lineSub u₀ ≤ w), a (chain2 (lineSub u₀) w hw) = c w) ∧
        (∀ (x y : FanoLat) (hxy : x ≤ y), x ≠ p0 → x ≠ lineSub u₀ → a (chain2 x y hxy) = 0) := by
    intro u₀ hu₀ c
    let v := lineSub u₀
    have hv_ne0 : v ≠ p0 := lineSub_ne_bot hu₀
    have hincomp : ∀ w : FanoLat, ¬ v ≤ w → w ≠ p0 →
        ∃ d : FanoLat → K, ι w * ι v = ∑ z : FanoLat, d z • (ι p0 * ι z) := by
      intro w hvw hw0
      have hwv : ¬ w ≤ v := by
        intro hle
        have hlt : w < v := lt_of_le_of_ne hle (fun heq => hvw (le_of_eq heq.symm))
        exact hw0 (lineSub_isAtom hu₀ w hlt)
      rcases prod_incomp_bot hasl2 hwv hvw (fun u _ huv => lineSub_isAtom hu₀ u huv) with ⟨d, hd⟩
      refine ⟨d, ?_⟩
      rw [hd, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      rw [Algebra.mul_smul_comm]
    choose d_fn hd_fn using fun (w : FanoLat) (hw : ¬ v ≤ w ∧ w ≠ p0) => hincomp w hw.1 hw.2
    let a : StdChain → K := fun l =>
      if hlen : l.1.length = 2 then
        let x := l.1.get ⟨0, by omega⟩
        let y := l.1.get ⟨1, by omega⟩
        if x = v then c y
        else if x = p0 then
          (if y = v then c p0 else 0) +
          ∑ w : FanoLat, if hw : ¬ v ≤ w ∧ w ≠ p0 then c w * d_fn w hw y else 0
        else 0
      else 0
    have ha_v : ∀ (w : FanoLat) (hw : v ≤ w), a (chain2 v w hw) = c w := by
      intro w hw; simp [a, chain2]
    have ha_other : ∀ (x y : FanoLat) (hxy : x ≤ y), x ≠ p0 → x ≠ v → a (chain2 x y hxy) = 0 := by
      intro x y hxy hx0 hxv; simp [a, chain2, hx0, hxv]
    have ha_p0 : ∀ z : FanoLat, a (chain2 p0 z (p0_le z)) =
        (if z = v then c p0 else 0) +
        ∑ w : FanoLat, if hw : ¬ v ≤ w ∧ w ≠ p0 then c w * d_fn w hw z else 0 := by
      intro z; simp [a, chain2, hv_ne0.symm]
    refine ⟨a, ?_, ha_v, ha_other⟩
    rw [hsum_S2]
    -- The outer sum over `x : FanoLat` only has nonzero terms at `x = v` and `x = p0`.
    have houter : (∑ x : FanoLat, ∑ y : FanoLat,
          if hxy : x ≤ y then a (chain2 x y hxy) • (ι x * ι y) else 0) =
        (∑ y : FanoLat, if hvy : v ≤ y then c y • (ι v * ι y) else 0) +
        (∑ z : FanoLat, a (chain2 p0 z (p0_le z)) • (ι p0 * ι z)) := by
      have hzero : ∀ x : FanoLat, x ≠ v → x ≠ p0 →
          (∑ y : FanoLat, if hxy : x ≤ y then a (chain2 x y hxy) • (ι x * ι y) else 0) = 0 := by
        intro x hxv hx0
        apply Finset.sum_eq_zero
        intro y _
        split_ifs with hxy
        · rw [ha_other x y hxy hx0 hxv, zero_smul]
        · rfl
      rw [← Finset.sum_subset (s₁ := ({v, p0} : Finset FanoLat)) (Finset.subset_univ _)]
      · rw [Finset.sum_pair hv_ne0]
        congr 1
        · apply Finset.sum_congr rfl; intro y _
          split_ifs with hvy
          · rw [ha_v y hvy]
          · rfl
        · apply Finset.sum_congr rfl; intro z _
          rw [dif_pos (p0_le z)]
      · intro x _ hxnot
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxnot
        exact hzero x hxnot.1 hxnot.2
    rw [houter]
    -- Expand the second sum (`x = p0`):
    have hsecond : (∑ z : FanoLat, a (chain2 p0 z (p0_le z)) • (ι p0 * ι z)) =
        c p0 • (ι p0 * ι v) +
        ∑ w : FanoLat, if hw : ¬ v ≤ w ∧ w ≠ p0 then c w • (ι w * ι v) else 0 := by
      have hsplit : ∀ z : FanoLat, a (chain2 p0 z (p0_le z)) • (ι p0 * ι z) =
          (if z = v then c p0 • (ι p0 * ι z) else 0) +
          ∑ w : FanoLat, if hw : ¬ v ≤ w ∧ w ≠ p0 then (c w * d_fn w hw z) • (ι p0 * ι z) else 0 := by
        intro z
        rw [ha_p0 z, add_smul, Finset.sum_smul]
        congr 1
        · split_ifs <;> simp
        · apply Finset.sum_congr rfl; intro w _
          split_ifs <;> simp
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib]
      congr 1
      · simp
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro w _
        split_ifs with hw
        · rw [hd_fn w hw, Finset.smul_sum]
          apply Finset.sum_congr rfl; intro z _
          rw [mul_smul]
        · simp
    rw [hsecond, Finset.sum_mul]
    -- Combine the 3 disjoint pieces of `w : FanoLat` (`v ≤ w`, `w = p0`, `¬ v ≤ w ∧ w ≠ p0`)!
    have hcombine : ∀ w : FanoLat,
        (c w • ι w) * ι v =
        (if v ≤ w then c w • (ι v * ι w) else 0) +
        (if w = p0 then c p0 • (ι p0 * ι v) else 0) +
        (if ¬ v ≤ w ∧ w ≠ p0 then c w • (ι w * ι v) else 0) := by
      intro w
      by_cases hvw : v ≤ w
      · have hw0 : w ≠ p0 := fun h => hv_ne0 (le_antisymm (h ▸ hvw) (p0_le v))
        rw [if_pos hvw, if_neg hw0, if_neg (by tauto), add_zero, add_zero,
            Algebra.smul_mul_assoc, mul_comm (ι w) (ι v)]
      · by_cases hw0 : w = p0
        · subst hw0
          rw [if_neg hvw, if_pos rfl, if_neg (by tauto), zero_add, add_zero,
              Algebra.smul_mul_assoc]
        · rw [if_neg hvw, if_neg hw0, if_pos ⟨hvw, hw0⟩, zero_add, zero_add,
              Algebra.smul_mul_assoc]
    calc ∑ w : FanoLat, (c w • ι w) * ι v
        = ∑ w : FanoLat, ((if v ≤ w then c w • (ι v * ι w) else 0) +
            (if w = p0 then c p0 • (ι p0 * ι v) else 0) +
            (if ¬ v ≤ w ∧ w ≠ p0 then c w • (ι w * ι v) else 0)) :=
          Finset.sum_congr rfl (fun w _ => hcombine w)
      _ = (∑ w : FanoLat, if v ≤ w then c w • (ι v * ι w) else 0) +
          (∑ w : FanoLat, if w = p0 then c p0 • (ι p0 * ι v) else 0) +
          (∑ w : FanoLat, if ¬ v ≤ w ∧ w ≠ p0 then c w • (ι w * ι v) else 0) := by
          simp only [Finset.sum_add_distrib]
      _ = (∑ w : FanoLat, if hvw : v ≤ w then c w • (ι v * ι w) else 0) +
          (c p0 • (ι p0 * ι v) +
            ∑ w : FanoLat, if hw : ¬ v ≤ w ∧ w ≠ p0 then c w • (ι w * ι v) else 0) := by
          simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, add_assoc]
          rfl
  -- Step 1: For any two distinct lines `v₁, v₂`, `ι v₁ * ι v₂ = ι p0 * (c₀ • ι p0 + α • ι v₁ + β • ι v₂)`.
  have hline_prod : ∀ (u₁ u₂ : Fin 3 → ZMod 2), u₁ ≠ 0 → u₂ ≠ 0 → lineSub u₁ ≠ lineSub u₂ →
      ∃ c₀ α β : K, ι (lineSub u₁) * ι (lineSub u₂) =
        ι p0 * (c₀ • ι p0 + α • ι (lineSub u₁) + β • ι (lineSub u₂)) := by
    intro u₁ u₂ hu₁ hu₂ hne
    let v₁ := lineSub u₁
    let v₂ := lineSub u₂
    have hinc := lines_incomp hu₁ hu₂ hne
    rcases prod_incomp_bot hasl2 hinc.1 hinc.2 (fun u hu1 _ => lineSub_isAtom hu₁ u hu1) with ⟨c, hc⟩
    have hc_zero : ∀ w : FanoLat, w ≠ p0 → w ≠ v₁ → w ≠ v₂ → c w = 0 := by
      intro w hw0 hw1 hw2
      rcases exists_third_line hu₁ hu₂ w hw0 hw1 hw2 with ⟨u₃, hu₃, hv3_le, hv3_ne1, hv3_ne2⟩
      let v₃ := lineSub u₃
      have hinc23 := lines_incomp hu₂ hu₃ hv3_ne2.symm
      rcases prod_incomp_bot hasl2 hinc23.1 hinc23.2 (fun u hu2 _ => lineSub_isAtom hu₂ u hu2) with ⟨c', hc'⟩
      have heq_cancel : (∑ z : FanoLat, c z • ι z) * ι v₃ = (∑ z : FanoLat, c' z • ι z) * ι v₁ := by
        apply mul_left_cancel₀ h0_ne
        calc ι p0 * ((∑ z : FanoLat, c z • ι z) * ι v₃)
            = (ι p0 * ∑ z : FanoLat, c z • ι z) * ι v₃ := by ring
          _ = (ι v₁ * ι v₂) * ι v₃ := by rw [← hc]
          _ = ι v₁ * (ι v₂ * ι v₃) := by ring
          _ = ι v₁ * (ι p0 * ∑ z : FanoLat, c' z • ι z) := by rw [hc']
          _ = ι p0 * ((∑ z : FanoLat, c' z • ι z) * ι v₁) := by ring
      rcases hmul_atom u₃ hu₃ c with ⟨aL, haL_eq, haL_v, _⟩
      rcases hmul_atom u₁ hu₁ c' with ⟨aR, haR_eq, _, haR_other⟩
      rw [haL_eq, haR_eq] at heq_cancel
      have hcoeff := coeff_eq_of_std_eq hli' heq_cancel (hmem_S2 v₃ w hv3_le)
      rw [haL_v w hv3_le, haR_other v₃ w hv3_le (lineSub_ne_bot hu₃) hv3_ne1] at hcoeff
      exact hcoeff
    refine ⟨c p0, c v₁, c v₂, ?_⟩
    rw [hc]
    congr 1
    rw [← Finset.sum_subset (s₁ := ({p0, v₁, v₂} : Finset FanoLat)) (Finset.subset_univ _)]
    · have hv10 : v₁ ≠ p0 := lineSub_ne_bot hu₁
      have hv20 : v₂ ≠ p0 := lineSub_ne_bot hu₂
      have h1 : p0 ∉ ({v₁, v₂} : Finset FanoLat) := by simp [hv10.symm, hv20.symm]
      rw [Finset.sum_insert h1, Finset.sum_pair hne]
      abel
    · intro w _ hwnot
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hwnot
      rw [hc_zero w hwnot.1 hwnot.2.1 hwnot.2.2, zero_smul]
  -- Apply Step 1 to `(pD, pA)` and `(pD, pB)`.
  rcases hline_prod vD vA vD_ne0 vA_ne0 pA_ne_pD.symm with ⟨cA, αA, βA, hDA⟩
  rcases hline_prod vD vB vD_ne0 vB_ne0 pB_ne_pD.symm with ⟨cB, αB, βB, hDB⟩
  -- Step 2: Write `ι pH * ι pD = ι p0 * ∑ w, m w • ι w`.
  rcases prod_incomp_bot hasl2 pH_incomp_pD.1 pH_incomp_pD.2
      (fun u _ huD => lineSub_isAtom vD_ne0 u huD) with ⟨m, hm⟩
  -- Step 3: Show `m pH = βA` and `m pH = βB`, hence `βA = βB`!
  have hm_eq : ∀ (uX : Fin 3 → ZMod 2) (huX : uX ≠ 0) (hXH : lineSub uX ≤ pH)
      (cX αX βX : K),
      ι pD * ι (lineSub uX) = ι p0 * (cX • ι p0 + αX • ι pD + βX • ι (lineSub uX)) →
      m pH = βX := by
    intro uX huX hXH cX αX βX hDX
    let pX := lineSub uX
    have hpX_ne0 : pX ≠ p0 := lineSub_ne_bot huX
    have hcancel : (∑ w : FanoLat, m w • ι w) * ι pX =
        cX • (ι p0 * ι pH) + (∑ w : FanoLat, (αX * m w) • (ι p0 * ι w)) + βX • (ι pX * ι pH) := by
      apply mul_left_cancel₀ h0_ne
      calc ι p0 * ((∑ w : FanoLat, m w • ι w) * ι pX)
          = (ι p0 * ∑ w : FanoLat, m w • ι w) * ι pX := by ring
        _ = (ι pH * ι pD) * ι pX := by rw [← hm]
        _ = ι pH * (ι pD * ι pX) := by ring
        _ = ι pH * (ι p0 * (cX • ι p0 + αX • ι pD + βX • ι pX)) := by rw [hDX]
        _ = ι p0 * (cX • (ι p0 * ι pH) + αX • (ι pH * ι pD) + βX • (ι pX * ι pH)) := by
            simp only [mul_add, Algebra.mul_smul_comm]
            congr 1
            · congr 1 <;> (congr 1; ring)
            · congr 1; ring
        _ = ι p0 * (cX • (ι p0 * ι pH) + (∑ w : FanoLat, (αX * m w) • (ι p0 * ι w)) +
            βX • (ι pX * ι pH)) := by
            congr 1; congr 1; congr 1
            rw [hm, Finset.mul_sum, Finset.smul_sum]
            apply Finset.sum_congr rfl; intro w _
            rw [Algebra.mul_smul_comm, smul_smul]
    rcases hmul_atom uX huX m with ⟨aL, haL_eq, haL_v, _⟩
    let bR : StdChain → K := fun l =>
      if l = chain2 pX pH hXH then βX
      else if hlen : l.1.length = 2 then
        let x := l.1.get ⟨0, by omega⟩
        let y := l.1.get ⟨1, by omega⟩
        if x = p0 then (if y = pH then cX else 0) + αX * m y else 0
      else 0
    have hbR_eq : cX • (ι p0 * ι pH) + (∑ w : FanoLat, (αX * m w) • (ι p0 * ι w)) +
        βX • (ι pX * ι pH) = ∑ l ∈ S2, bR l • stdMon ι l := by
      rw [hsum_S2]
      symm
      have hzero : ∀ x : FanoLat, x ≠ pX → x ≠ p0 →
          (∑ y : FanoLat, if hxy : x ≤ y then bR (chain2 x y hxy) • (ι x * ι y) else 0) = 0 := by
        intro x hxX hx0
        apply Finset.sum_eq_zero; intro y _
        split_ifs with hxy
        · have hne : chain2 x y hxy ≠ chain2 pX pH hXH := fun h => hxX (chain2_inj h).1
          dsimp only [bR]
          rw [if_neg hne]
          simp [chain2, hx0]
        · rfl
      rw [← Finset.sum_subset (s₁ := ({pX, p0} : Finset FanoLat)) (Finset.subset_univ _)]
      · rw [Finset.sum_pair hpX_ne0]
        have hpX_sum : (∑ y : FanoLat, if hXy : pX ≤ y then bR (chain2 pX y hXy) • (ι pX * ι y) else 0) =
            βX • (ι pX * ι pH) := by
          rw [← Finset.sum_subset (s₁ := ({pH} : Finset FanoLat)) (Finset.subset_univ _)]
          · rw [Finset.sum_singleton, dif_pos hXH]
            dsimp only [bR]
            rw [if_pos rfl]
          · intro y _ hy
            have hyne : y ≠ pH := by simpa using hy
            split_ifs with hXy
            · have hne : chain2 pX y hXy ≠ chain2 pX pH hXH := fun h => hyne (chain2_inj h).2
              dsimp only [bR]
              rw [if_neg hne]
              simp [chain2, hpX_ne0]
            · rfl
        have hp0_sum : (∑ y : FanoLat, if h0y : p0 ≤ y then bR (chain2 p0 y h0y) • (ι p0 * ι y) else 0) =
            cX • (ι p0 * ι pH) + ∑ w : FanoLat, (αX * m w) • (ι p0 * ι w) := by
          have hterm : ∀ y : FanoLat,
              (if h0y : p0 ≤ y then bR (chain2 p0 y h0y) • (ι p0 * ι y) else 0) =
              (if y = pH then cX • (ι p0 * ι y) else 0) + (αX * m y) • (ι p0 * ι y) := by
            intro y
            rw [dif_pos (p0_le y)]
            have hne : chain2 p0 y (p0_le y) ≠ chain2 pX pH hXH := fun h => hpX_ne0 (chain2_inj h).1.symm
            dsimp only [bR]
            rw [if_neg hne]
            simp only [chain2, List.length_cons, List.length_nil, ↓reduceDIte,
              List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ, if_true, add_smul]
            congr 1
            by_cases hy : y = pH <;> simp [hy]
          simp_rw [hterm]
          rw [Finset.sum_add_distrib]
          simp
        rw [hpX_sum, hp0_sum]
        abel
      · intro x _ hxnot
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxnot
        exact hzero x hxnot.1 hxnot.2
    rw [haL_eq, hbR_eq] at hcancel
    have hcoeff := coeff_eq_of_std_eq hli' hcancel (hmem_S2 pX pH hXH)
    rw [haL_v pH hXH] at hcoeff
    simpa [bR] using hcoeff
  have hβA : m pH = βA := hm_eq vA vA_ne0 pA_lt_pH.le cA αA βA hDA
  have hβB : m pH = βB := hm_eq vB vB_ne0 pB_lt_pH.le cB αB βB hDB
  have hβeq : βA = βB := hβA.symm.trans hβB
  -- Step 4: Final 10-line domain contradiction!
  let β : K := βA
  let kA : K := cA + αA * β
  let kB : K := cB + αB * β
  have hfacA : (ι pD - β • ι p0) * (ι pA - αA • ι p0) = kA • (ι p0 * ι p0) := by
    have hDA' : ι pD * ι pA = ι p0 * (cA • ι p0 + αA • ι pD + β • ι pA) := hDA
    have h1 : ι pD * ι pA = cA • (ι p0 * ι p0) + αA • (ι p0 * ι pD) + β • (ι p0 * ι pA) := by
      rw [hDA']
      simp only [mul_add, Algebra.mul_smul_comm]
    calc (ι pD - β • ι p0) * (ι pA - αA • ι p0)
        = ι pD * ι pA - αA • (ι p0 * ι pD) - β • (ι p0 * ι pA) + (αA * β) • (ι p0 * ι p0) := by
          simp only [sub_mul, mul_sub, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_sub,
            smul_smul, mul_comm (ι pD) (ι p0)]
          abel
      _ = (cA + αA * β) • (ι p0 * ι p0) := by
          rw [h1, add_smul]
          abel
  have hfacB : (ι pD - β • ι p0) * (ι pB - αB • ι p0) = kB • (ι p0 * ι p0) := by
    have hDB' : ι pD * ι pB = ι p0 * (cB • ι p0 + αB • ι pD + β • ι pB) := by
      have htmp : ι pD * ι pB = ι p0 * (cB • ι p0 + αB • ι pD + βB • ι pB) := hDB
      rw [← hβeq] at htmp
      exact htmp
    have h1 : ι pD * ι pB = cB • (ι p0 * ι p0) + αB • (ι p0 * ι pD) + β • (ι p0 * ι pB) := by
      rw [hDB']
      simp only [mul_add, Algebra.mul_smul_comm]
    calc (ι pD - β • ι p0) * (ι pB - αB • ι p0)
        = ι pD * ι pB - αB • (ι p0 * ι pD) - β • (ι p0 * ι pB) + (αB * β) • (ι p0 * ι p0) := by
          simp only [sub_mul, mul_sub, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_sub,
            smul_smul, mul_comm (ι pD) (ι p0)]
          abel
      _ = (cB + αB * β) • (ι p0 * ι p0) := by
          rw [h1, add_smul]
          abel
  have hkB_ne0 : kB ≠ 0 := by
    intro hk0
    rw [hk0, zero_smul] at hfacB
    rcases mul_eq_zero.mp hfacB with hD0 | hB0
    · exact hsub_ne0 pD β pD_ne_bot hD0
    · exact hsub_ne0 pB αB pB_ne_bot hB0
  have hprod0 : (ι pD - β • ι p0) *
      (kB • (ι pA - αA • ι p0) - kA • (ι pB - αB • ι p0)) = 0 := by
    calc (ι pD - β • ι p0) * (kB • (ι pA - αA • ι p0) - kA • (ι pB - αB • ι p0))
        = kB • ((ι pD - β • ι p0) * (ι pA - αA • ι p0)) -
          kA • ((ι pD - β • ι p0) * (ι pB - αB • ι p0)) := by
          simp only [mul_sub, Algebra.mul_smul_comm]
      _ = kB • (kA • (ι p0 * ι p0)) - kA • (kB • (ι p0 * ι p0)) := by rw [hfacA, hfacB]
      _ = (kB * kA - kA * kB) • (ι p0 * ι p0) := by simp only [smul_smul, sub_smul]
      _ = 0 := by rw [mul_comm kB kA, sub_self, zero_smul]
  have hlin0 : kB • (ι pA - αA • ι p0) - kA • (ι pB - αB • ι p0) = 0 := by
    rcases mul_eq_zero.mp hprod0 with hD0 | hlin
    · exact absurd hD0 (hsub_ne0 pD β pD_ne_bot)
    · exact hlin
  -- Contradict linear independence of `{chain1 pA, chain1 pB, chain1 p0}`!
  have hcAB : chain1 pA ≠ chain1 pB := fun h => pA_ne_pB (by simpa [chain1] using congrArg Subtype.val h)
  have hcA0 : chain1 pA ≠ chain1 p0 := fun h => pA_ne_bot (by simpa [chain1] using congrArg Subtype.val h)
  have hcB0 : chain1 pB ≠ chain1 p0 := fun h => pB_ne_bot (by simpa [chain1] using congrArg Subtype.val h)
  let S1 : Finset StdChain := {chain1 pA, chain1 pB, chain1 p0}
  let g : StdChain → K := fun l =>
    if l = chain1 pA then kB
    else if l = chain1 pB then -kA
    else kA * αB - kB * αA
  have hsum0 : ∑ l ∈ S1, g l • stdMon ι l = 0 := by
    have h1 : chain1 pA ∉ ({chain1 pB, chain1 p0} : Finset StdChain) := by simp [hcAB, hcA0]
    rw [Finset.sum_insert h1, Finset.sum_pair hcB0]
    simp only [g, if_pos rfl, if_neg hcAB.symm, if_neg hcA0.symm, if_neg hcB0.symm, stdMon_chain1,
      if_true, ← add_assoc]
    calc kB • ι pA + (-kA) • ι pB + (kA * αB - kB * αA) • ι p0
        = kB • (ι pA - αA • ι p0) - kA • (ι pB - αB • ι p0) := by
          simp only [smul_sub, smul_smul, sub_smul, neg_smul]
          abel
      _ = 0 := hlin0
  have hkB0 := (linearIndependent_iff'.mp hli') S1 g hsum0 (chain1 pA) (Finset.mem_insert_self _ _)
  simp only [g, if_pos rfl] at hkB0
  exact hkB_ne0 hkB0

end OMA.P_arxiv_2604_05395

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2604_05395.main) :=
  fun h => OMA.P_arxiv_2604_05395.fano_not_integral (h OMA.P_arxiv_2604_05395.FanoLat inferInstance)
