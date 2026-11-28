import FormalConjectures.ErdosProblems.«556»
/-!
Credit: @fqlx; original lower construction and absorption interfaces: @senamakel.

A four-lemma decomposition of the known Benevides–Skokan large-even theorem.
The three absorption statements are the same exact statements as accepted R1.
The stability statement explicitly retains its permutation of the three colors.
All four hypotheses have accompanying complete, kernel-checked proofs. This
reduction is a packaging boundary for the project's 512 KiB per-file limit.
It uses no result from the earlier component-based R3 draft.
-/

-- Reduction Erdos556.erdos_556.variants.benevides_skokan_large_even.R1 of Erdős Problem 556 — benevides skokan large even
-- Credit: @senamakel
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

open Filter SimpleGraph
open scoped Fin.NatCast

namespace OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R3


theorem rc4_no_cycle (N m : ℕ) (G : SimpleGraph (Fin N)) (P : Fin N → Prop)
    (hP : ∀ u v, P u → P v → u = v) (L : Fin N → ℕ)
    (hL : ∀ u v, G.Adj u v → ¬ P u → ¬ P v → L u = L v)
    (hc : ∀ j, ∃ a b : ℕ, ∀ v : Fin N, ¬ P v → L v = j →
      (a ≤ v.val ∧ v.val < a + m) ∨ (b ≤ v.val ∧ v.val < b + m)) :
    ¬ cycleGraph (2 * m + 2) ⊑ G := by
  classical
  have : NeZero (2 * m + 2) := ⟨by omega⟩
  rintro ⟨f⟩
  have hinj := f.injective
  -- choose the base index
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin (2 * m + 2), ∀ i, P (f i) → i = i0 := by
    by_cases hh : ∃ i, P (f i)
    · obtain ⟨i, hi⟩ := hh
      exact ⟨i, fun j hj => hinj (hP _ _ hj hi)⟩
    · push Not at hh
      exact ⟨0, fun j hj => absurd hj (hh j)⟩
  let idx : ℕ → Fin (2 * m + 2) := fun t => i0 + ((t + 1 : ℕ) : Fin (2 * m + 2))
  have hidx_ne : ∀ t, t < 2 * m + 1 → idx t ≠ i0 := by
    intro t ht h
    have h2 : ((t + 1 : ℕ) : Fin (2 * m + 2)) = 0 := by
      have := congrArg (fun x => x - i0) h
      simpa [idx] using this
    have := congrArg Fin.val h2
    rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega)] at this
    simp at this
  have hidx_inj : ∀ a b, a < 2 * m + 1 → b < 2 * m + 1 → idx a = idx b → a = b := by
    intro a b ha hb h
    have h2 : ((a + 1 : ℕ) : Fin (2 * m + 2)) = ((b + 1 : ℕ) : Fin (2 * m + 2)) := by
      simpa [idx] using h
    have := congrArg Fin.val h2
    rw [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hnP : ∀ t, t < 2 * m + 1 → ¬ P (f (idx t)) := by
    intro t ht h
    exact hidx_ne t ht (hi0 _ h)
  have hadj : ∀ t, G.Adj (f (idx (t + 1))) (f (idx t)) := by
    intro t
    apply f.toHom.map_adj
    rw [cycleGraph_adj]
    left
    simp only [idx]
    push_cast
    abel
  have hlab : ∀ t, t < 2 * m + 1 → L (f (idx t)) = L (f (idx 0)) := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [← ih (by omega)]
      exact hL _ _ (hadj t) (hnP _ ht) (hnP _ (by omega))
  obtain ⟨a, b, hab⟩ := hc (L (f (idx 0)))
  let S : Finset ℕ := Finset.range (2 * m + 1)
  have hmaps : ∀ t ∈ S, (f (idx t)).val ∈ Finset.Ico a (a + m) ∪ Finset.Ico b (b + m) := by
    intro t ht
    have ht' : t < 2 * m + 1 := Finset.mem_range.mp ht
    rcases hab _ (hnP t ht') (hlab t ht') with h | h
    · exact Finset.mem_union_left _ (Finset.mem_Ico.mpr h)
    · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr h)
  have hinjOn : Set.InjOn (fun t => (f (idx t)).val) S := by
    intro x hx y hy hxy
    exact hidx_inj x y (Finset.mem_range.mp hx) (Finset.mem_range.mp hy)
      (hinj (Fin.ext hxy))
  have h1 := Finset.card_le_card_of_injOn _ hmaps hinjOn
  have h2 := Finset.card_union_le (Finset.Ico a (a + m)) (Finset.Ico b (b + m))
  simp [S] at h1 h2
  omega


theorem rc4_key_red : ∀ s t : ℕ, s ≤ 6 → t ≤ 6 → s ≠ 4 → t ≠ 4 →
    (if s = 6 ∨ t = 6 then 2 else if s = 5 ∨ t = 5 then 1 else if s = 4 ∨ t = 4 then 0 else if s / 2 = t / 2 then 0 else if s + t = 3 then 1 else 2) = 0 →
    (fun s : ℕ => if s < 2 then 0 else if s < 4 then 1 else s + 10) s = (fun s : ℕ => if s < 2 then 0 else if s < 4 then 1 else s + 10) t := by
  intro s t hs ht
  interval_cases s <;> interval_cases t <;> decide

theorem rc4_key_green : ∀ s t : ℕ, s ≤ 6 → t ≤ 6 → s ≠ 5 → t ≠ 5 →
    (if s = 6 ∨ t = 6 then 2 else if s = 5 ∨ t = 5 then 1 else if s = 4 ∨ t = 4 then 0 else if s / 2 = t / 2 then 0 else if s + t = 3 then 1 else 2) = 1 →
    (fun s : ℕ => if s = 0 ∨ s = 3 then 0 else if s < 4 then 1 else s + 10) s = (fun s : ℕ => if s = 0 ∨ s = 3 then 0 else if s < 4 then 1 else s + 10) t := by
  intro s t hs ht
  interval_cases s <;> interval_cases t <;> decide

theorem rc4_key_blue : ∀ s t : ℕ, s ≤ 6 → t ≤ 6 → s ≠ 6 → t ≠ 6 →
    (if s = 6 ∨ t = 6 then 2 else if s = 5 ∨ t = 5 then 1 else if s = 4 ∨ t = 4 then 0 else if s / 2 = t / 2 then 0 else if s + t = 3 then 1 else 2) = 2 →
    (fun s : ℕ => if s = 0 ∨ s = 2 then 0 else if s < 4 then 1 else s + 10) s = (fun s : ℕ => if s = 0 ∨ s = 2 then 0 else if s < 4 then 1 else s + 10) t := by
  intro s t hs ht
  interval_cases s <;> interval_cases t <;> decide

theorem rc4_lower (m : ℕ) (hm : 1 ≤ m) (N : ℕ) (hN : N ≤ 4 * m + 3)
    (ty : ℕ → ℕ) (hty : ∀ v, ty v = if v < m then 0 else if v < 2 * m then 1 else
      if v < 3 * m then 2 else if v < 4 * m then 3 else v - 4 * m + 4)
    (κ : ℕ → ℕ → ℕ) (hκ : ∀ s t, κ s t = if s = 6 ∨ t = 6 then 2 else
      if s = 5 ∨ t = 5 then 1 else if s = 4 ∨ t = 4 then 0 else
      if s / 2 = t / 2 then 0 else if s + t = 3 then 1 else 2) :
    ∃ c : Fin 3 → SimpleGraph (Fin N), (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c ∧
      ∀ i, ¬ cycleGraph (2 * m + 2) ⊑ c i := by
  have hκs : ∀ s t, κ s t = κ t s := by
    intro s t; rw [hκ, hκ]; split_ifs <;> omega
  have hκ3 : ∀ s t, κ s t < 3 := by
    intro s t; rw [hκ]; split_ifs <;> omega
  have hty6 : ∀ v : Fin N, ty v.val ≤ 6 := by
    intro v; have := v.isLt; rw [hty]; split_ifs <;> omega
  let c : Fin 3 → SimpleGraph (Fin N) := fun i =>
    SimpleGraph.fromRel (fun u v : Fin N => κ (ty u.val) (ty v.val) = i.val)
  have hcadj : ∀ i u v, (c i).Adj u v ↔ u ≠ v ∧ κ (ty u.val) (ty v.val) = i.val := by
    intro i u v
    simp only [c, fromRel_adj]
    rw [hκs (ty v.val)]
    simp
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · ext u v
    simp only [top_adj, iSup_adj, hcadj]
    constructor
    · intro h; exact ⟨⟨_, hκ3 _ _⟩, h, rfl⟩
    · rintro ⟨_, h, _⟩; exact h
  · intro i j hij
    rw [SimpleGraph.disjoint_left]
    intro u v h1 h2
    rw [hcadj] at h1 h2
    exact hij (Fin.ext (h1.2.symm.trans h2.2))
  · have hP : ∀ k : ℕ, 4 ≤ k → k ≤ 6 → ∀ u v : Fin N, ty u.val = k → ty v.val = k → u = v := by
      intro k _ _ u v hu hv
      apply Fin.ext
      rw [hty] at hu hv
      split_ifs at hu hv <;> omega
    have hcl : ∀ (f : ℕ → ℕ) (A0 B0 A1 B1 : ℕ) (k : ℕ), 4 ≤ k → k ≤ 6 →
        (∀ s, s < 4 → f s ≤ 1) → (∀ s, 4 ≤ s → f s = s + 10) →
        (∀ v : Fin N, ty v.val < 4 → f (ty v.val) = 0 →
          (A0 ≤ v.val ∧ v.val < A0 + m) ∨ (B0 ≤ v.val ∧ v.val < B0 + m)) →
        (∀ v : Fin N, ty v.val < 4 → f (ty v.val) = 1 →
          (A1 ≤ v.val ∧ v.val < A1 + m) ∨ (B1 ≤ v.val ∧ v.val < B1 + m)) →
        ∀ j, ∃ a b : ℕ, ∀ v : Fin N, ¬ ty v.val = k → f (ty v.val) = j →
          (a ≤ v.val ∧ v.val < a + m) ∨ (b ≤ v.val ∧ v.val < b + m) := by
      intro f A0 B0 A1 B1 k _ _ hf1 hf2 h0 h1 j
      by_cases hj0 : j = 0
      · refine ⟨A0, B0, fun v _ hv => ?_⟩
        have hlt : ty v.val < 4 := by
          by_contra hc; rw [hf2 _ (by omega)] at hv; omega
        exact h0 v hlt (hv.trans hj0)
      by_cases hj1 : j = 1
      · refine ⟨A1, B1, fun v _ hv => ?_⟩
        have hlt : ty v.val < 4 := by
          by_contra hc; rw [hf2 _ (by omega)] at hv; omega
        exact h1 v hlt (hv.trans hj1)
      refine ⟨4 * m + j - 14, 4 * m + j - 14, fun v _ hv => ?_⟩
      have hge : 4 ≤ ty v.val := by
        by_contra hc; have := hf1 (ty v.val) (by omega); omega
      rw [hf2 _ hge] at hv
      left
      have hv' := hv
      rw [hty] at hv'
      have := v.isLt
      split_ifs at hv' <;> omega
    have hint : ∀ v : Fin N, (ty v.val = 0 → v.val < m) ∧ (ty v.val = 1 → m ≤ v.val ∧ v.val < 2 * m) ∧
        (ty v.val = 2 → 2 * m ≤ v.val ∧ v.val < 3 * m) ∧ (ty v.val = 3 → 3 * m ≤ v.val ∧ v.val < 4 * m) := by
      intro v; refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> have e := hty v.val <;> split_ifs at e <;> omega
    intro i
    have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi3 with rfl | rfl | rfl
    · -- red, hub r
      refine rc4_no_cycle N m (c 0) (fun v => ty v.val = 4) (fun u v hu hv => hP 4 le_rfl
        (by norm_num) u v hu hv)
        (fun v => (fun s => if s < 2 then 0 else if s < 4 then 1 else s + 10) (ty v.val))
        ?_ ?_
      · have key := rc4_key_red
        intro u v h hu hv
        rw [hcadj] at h
        exact key _ _ (hty6 u) (hty6 v) hu hv (by rw [← hκ]; simpa using h.2)
      · refine hcl (fun s => if s < 2 then 0 else if s < 4 then 1 else s + 10) 0 m (2 * m) (3 * m)
          4 le_rfl (by norm_num) ?_ ?_ ?_ ?_
        · intro s hs; split_ifs <;> omega
        · intro s hs; split_ifs <;> omega
        · intro v h4 h; have hv := hint v; try dsimp only at h
          generalize ty v.val = s at h4 h hv; split_ifs at h <;> omega
        · intro v h4 h; have hv := hint v; try dsimp only at h
          generalize ty v.val = s at h4 h hv; split_ifs at h <;> omega
    · -- green, hub g
      refine rc4_no_cycle N m (c 1) (fun v => ty v.val = 5) (fun u v hu hv => hP 5 (by norm_num)
        (by norm_num) u v hu hv)
        (fun v => (fun s => if s = 0 ∨ s = 3 then 0 else if s < 4 then 1 else s + 10) (ty v.val))
        ?_ ?_
      · have key := rc4_key_green
        intro u v h hu hv
        rw [hcadj] at h
        exact key _ _ (hty6 u) (hty6 v) hu hv (by rw [← hκ]; simpa using h.2)
      · refine hcl (fun s => if s = 0 ∨ s = 3 then 0 else if s < 4 then 1 else s + 10) 0 (3 * m) m
          (2 * m) 5 (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
        · intro s hs; split_ifs <;> omega
        · intro s hs; split_ifs <;> omega
        · intro v h4 h; have hv := hint v; try dsimp only at h
          generalize ty v.val = s at h4 h hv; split_ifs at h <;> omega
        · intro v h4 h; have hv := hint v; try dsimp only at h
          generalize ty v.val = s at h4 h hv; split_ifs at h <;> omega
    · -- blue, hub b
      refine rc4_no_cycle N m (c 2) (fun v => ty v.val = 6) (fun u v hu hv => hP 6 (by norm_num)
        le_rfl u v hu hv)
        (fun v => (fun s => if s = 0 ∨ s = 2 then 0 else if s < 4 then 1 else s + 10) (ty v.val))
        ?_ ?_
      · have key := rc4_key_blue
        intro u v h hu hv
        rw [hcadj] at h
        exact key _ _ (hty6 u) (hty6 v) hu hv (by rw [← hκ]; simpa using h.2)
      · refine hcl (fun s => if s = 0 ∨ s = 2 then 0 else if s < 4 then 1 else s + 10) 0 (2 * m) m
          (3 * m) 6 (by norm_num) le_rfl ?_ ?_ ?_ ?_
        · intro s hs; split_ifs <;> omega
        · intro s hs; split_ifs <;> omega
        · intro v h4 h; have hv := hint v; try dsimp only at h
          generalize ty v.val = s at h4 h hv; split_ifs at h <;> omega
        · intro v h4 h; have hv := hint v; try dsimp only at h
          generalize ty v.val = s at h4 h hv; split_ifs at h <;> omega

/-- Benevides–Skokan, Lemma 5 (colourings of type EC1). Blocks `A, B, C, D` are `f⁻¹ 0, …, f⁻¹ 3`
on the `2n` vertices; colours `0, 1, 2` are red, green, blue. There is `α₀ > 0` such that for
every `0 < α ≤ α₀`, for all large even `n`, every 3-colouring of `K_{2n}` with every block of size
`≥ (1 - α)·2n/4` and with red `[A,B]`, `[C,D]`, green `[A,D]`, `[B,C]`, blue `[A,C]`, `[B,D]`
all `(1 - α)`-dense contains a monochromatic `C_n`. -/
def H1 : Prop :=
  ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ →
    ∀ᶠ n : ℕ in atTop, Even n →
      ∀ c : Fin 3 → SimpleGraph (Fin (2 * n)), (⊤ : SimpleGraph (Fin (2 * n))).IsEdgeColouring c →
        ∀ f : Fin (2 * n) → Fin 4,
          (∀ j, (1 - α) * n / 2 ≤ (Nat.card {v // f v = j} : ℝ)) →
          (∀ k S T, (k, S, T) ∈ ([(0, {0}, {1}), (0, {2}, {3}), (1, {0}, {3}), (1, {1}, {2}), (2, {0}, {2}), (2, {1}, {3})] : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4))) →
            (1 - α) * Nat.card {v // f v ∈ S} * Nat.card {v // f v ∈ T} ≤
              (Nat.card {e : Fin (2 * n) × Fin (2 * n) // f e.1 ∈ S ∧ f e.2 ∈ T ∧ (c k).Adj e.1 e.2} : ℝ)) →
          ∃ i, cycleGraph n ⊑ c i

/-- Benevides–Skokan, Lemma 6 (colourings of type EC2): as `H1`, with red `[A,B]`,
green `[A ∪ B, C]` and blue `[A ∪ B, D]` all `(1 - α)`-dense. -/
def H2 : Prop :=
  ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ →
    ∀ᶠ n : ℕ in atTop, Even n →
      ∀ c : Fin 3 → SimpleGraph (Fin (2 * n)), (⊤ : SimpleGraph (Fin (2 * n))).IsEdgeColouring c →
        ∀ f : Fin (2 * n) → Fin 4,
          (∀ j, (1 - α) * n / 2 ≤ (Nat.card {v // f v = j} : ℝ)) →
          (∀ k S T, (k, S, T) ∈ ([(0, {0}, {1}), (1, {0, 1}, {2}), (2, {0, 1}, {3})] : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4))) →
            (1 - α) * Nat.card {v // f v ∈ S} * Nat.card {v // f v ∈ T} ≤
              (Nat.card {e : Fin (2 * n) × Fin (2 * n) // f e.1 ∈ S ∧ f e.2 ∈ T ∧ (c k).Adj e.1 e.2} : ℝ)) →
          ∃ i, cycleGraph n ⊑ c i

/-- Benevides–Skokan, Lemma 7 with `c₁ = 4/5`, `c₂ = 3/10` (colourings of type EC3): there is
`μ₀ > 0` such that for every `0 < μ ≤ μ₀` there is `δ₀ > 0` such that, for all large even `n`
and every `0 < δ ≤ δ₀`, every 3-colouring of `K_{2n}` of type `EC3(μ, 4/5, 3/10, δ)`
(`|A|, |B|, |C| ≥ (1 - c₁μ)·2n/4`, `|D| ≥ μ·2n/4`, `|A| ≥ max(|B|, |C|, |D|) + μ·2n/4`,
`|A ∪ D| ≤ (1 + c₂μ)·2n/2`, and the six EC1 pairs `(1 - δ)`-dense) contains a monochromatic `C_n`. -/
def H3 : Prop :=
  ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ → ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ᶠ n : ℕ in atTop, Even n → ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ c : Fin 3 → SimpleGraph (Fin (2 * n)), (⊤ : SimpleGraph (Fin (2 * n))).IsEdgeColouring c →
        ∀ f : Fin (2 * n) → Fin 4,
          (let a : Fin 4 → ℝ := (fun j => Nat.card {v // f v = j});
            (1 - 4 / 5 * μ) * n / 2 ≤ min (a 0) (min (a 1) (a 2)) ∧ μ * n / 2 ≤ a 3 ∧
            max (a 1) (max (a 2) (a 3)) + μ * n / 2 ≤ a 0 ∧ a 0 + a 3 ≤ (1 + 3 / 10 * μ) * n) →
          (∀ k S T, (k, S, T) ∈ ([(0, {0}, {1}), (0, {2}, {3}), (1, {0}, {3}), (1, {1}, {2}), (2, {0}, {2}), (2, {1}, {3})] : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4))) →
            (1 - δ) * Nat.card {v // f v ∈ S} * Nat.card {v // f v ∈ T} ≤
              (Nat.card {e : Fin (2 * n) × Fin (2 * n) // f e.1 ∈ S ∧ f e.2 ∈ T ∧ (c k).Adj e.1 e.2} : ℝ)) →
          ∃ i, cycleGraph n ⊑ c i

/-- The proved stability alternative, allowing its necessary color permutation. -/
def H4 : Prop :=
  ∃ α₀ μ₀ : ℝ, 0 < α₀ ∧ 0 < μ₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ →
    ∀ μ₁ : ℝ, 0 < μ₁ → μ₁ ≤ μ₀ → ∃ μ : ℝ, 0 < μ ∧ μ < μ₁ ∧
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, Even n →
    ∀ c : Fin 3 → SimpleGraph (Fin (2 * n)),
      (⊤ : SimpleGraph (Fin (2 * n))).IsEdgeColouring c →
      (∃ i, cycleGraph n ⊑ c i) ∨
      ∃ (σ : Equiv.Perm (Fin 3)) (f : Fin (2 * n) → Fin 4),
        let a : Fin 4 → ℝ := fun j => Nat.card {v // f v = j}
        let J : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4)) :=
          [(0,{0},{1}),(0,{2},{3}),(1,{0},{3}),(1,{1},{2}),(2,{0},{2}),(2,{1},{3})]
        let D := fun (β : ℝ) (L : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4))) =>
          ∀ k S T, (k,S,T) ∈ L →
            (1 - β) * Nat.card {v // f v ∈ S} * Nat.card {v // f v ∈ T} ≤
              (Nat.card {e : Fin (2 * n) × Fin (2 * n) //
                f e.1 ∈ S ∧ f e.2 ∈ T ∧ (c (σ k)).Adj e.1 e.2} : ℝ)
        ((∀ j, (1 - α) * n / 2 ≤ a j) ∧ D α J) ∨
        ((∀ j, (1 - α) * n / 2 ≤ a j) ∧ D α [(0,{0},{1}),(1,{0,1},{2}),(2,{0,1},{3})]) ∨
        (((1 - 4 / 5 * μ) * n / 2 ≤ min (a 0) (min (a 1) (a 2)) ∧
          μ * n / 2 ≤ a 3 ∧ max (a 1) (max (a 2) (a 3)) + μ * n / 2 ≤ a 0 ∧
          a 0 + a 3 ≤ (1 + 3 / 10 * μ) * n) ∧ D δ J)

theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos556.erdos_556.variants.benevides_skokan_large_even := by
  intro h1 h2 h3 h4
  obtain ⟨a1, ha1, h1⟩ := h1
  obtain ⟨a2, ha2, h2⟩ := h2
  obtain ⟨u3, hu3, h3⟩ := h3
  obtain ⟨a4, u4, ha4, hu4, h4⟩ := h4
  have hα : 0 < min (min a1 a2) a4 := lt_min (lt_min ha1 ha2) ha4
  obtain ⟨μ, hμ, hμ1, h4⟩ := h4 (min (min a1 a2) a4) hα (min_le_right _ _) (min u3 u4)
    (lt_min hu3 hu4) (min_le_right _ _)
  obtain ⟨δ, hδ, h3⟩ := h3 μ hμ (le_trans hμ1.le (min_le_left _ _))
  have e1 := h1 (min (min a1 a2) a4) hα (le_trans (min_le_left _ _) (min_le_left _ _))
  have e2 := h2 (min (min a1 a2) a4) hα (le_trans (min_le_left _ _) (min_le_right _ _))
  have e4 := h4 δ hδ
  filter_upwards [e1, e2, h3, e4, eventually_ge_atTop 4] with n h1n h2n h3n h4n hn4 hev
  have up : ∀ c : Fin 3 → SimpleGraph (Fin (2 * n)),
      (⊤ : SimpleGraph (Fin (2 * n))).IsEdgeColouring c → ∃ i, cycleGraph n ⊑ c i := by
    intro c hc
    rcases h4n hev c hc with h | ⟨σ, f, h⟩
    · exact h
    · have hc' : (⊤ : SimpleGraph (Fin (2 * n))).IsEdgeColouring (fun k => c (σ k)) := by
        constructor
        · rw [hc.1]
          exact (Equiv.iSup_comp (g := c) σ).symm
        · intro i j hij
          exact hc.2 (σ i) (σ j) (fun heq => hij (σ.injective heq))
      rcases h with ⟨hs, hd⟩ | ⟨hs, hd⟩ | ⟨hs, hd⟩
      · obtain ⟨i, hi⟩ := h1n hev (fun k => c (σ k)) hc' f hs hd
        exact ⟨σ i, hi⟩
      · obtain ⟨i, hi⟩ := h2n hev (fun k => c (σ k)) hc' f hs hd
        exact ⟨σ i, hi⟩
      · obtain ⟨i, hi⟩ := h3n hev δ hδ le_rfl (fun k => c (σ k)) hc' f hs hd
        exact ⟨σ i, hi⟩
  unfold multicolourRamsey
  apply le_antisymm
  · exact Nat.sInf_le up
  · refine le_csInf ⟨2 * n, up⟩ ?_
    intro N hN
    by_contra hlt
    push Not at hlt
    obtain ⟨r, hr⟩ := hev
    obtain ⟨c, hc, hno⟩ := rc4_lower (r - 1) (by omega) N (by omega)
      (fun v => if v < r - 1 then 0 else if v < 2 * (r - 1) then 1 else
        if v < 3 * (r - 1) then 2 else if v < 4 * (r - 1) then 3 else v - 4 * (r - 1) + 4)
      (fun _ => rfl)
      (fun s t => if s = 6 ∨ t = 6 then 2 else
        if s = 5 ∨ t = 5 then 1 else if s = 4 ∨ t = 4 then 0 else
        if s / 2 = t / 2 then 0 else if s + t = 3 then 1 else 2)
      (fun _ _ => rfl)
    obtain ⟨i, hi⟩ := hN c hc
    have hn : n = 2 * (r - 1) + 2 := by omega
    rw [hn] at hi
    exact hno i hi

end OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R3
