import FormalConjectures.Wikipedia.AlonSaksSeymourConjecture

/-! The quadratic form of the complete graph detects the kernel of the side-sum map.
Original proof by @Genbox (PR #117); finite-sum and infimum steps simplified using Mathlib. -/

open AlonSaksSeymourConjecture Finset SimpleGraph
open scoped BigOperators Classical

noncomputable def OMA.gpSum {n : ℕ} (A : Finset (Fin n)) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  ∑ v ∈ A, LinearMap.proj v

lemma OMA.gpSum_apply {n : ℕ} (A : Finset (Fin n)) (x : Fin n → ℝ) :
    OMA.gpSum A x = ∑ v ∈ A, x v := by
  simp [OMA.gpSum, LinearMap.sum_apply]

noncomputable def OMA.gpWeight {n : ℕ} (A : Finset (Fin n)) (x : Fin n → ℝ)
    (v : Fin n) : ℝ :=
  if v ∈ A then x v else 0

lemma OMA.gpWeight_sum {n : ℕ} (A : Finset (Fin n)) (x : Fin n → ℝ) :
    (∑ v, OMA.gpWeight A x v) = OMA.gpSum A x := by
  simp [OMA.gpWeight, OMA.gpSum_apply]

lemma OMA.gpTerm {n : ℕ} {A B : Finset (Fin n)} (h : Disjoint A B)
    (x : Fin n → ℝ) (u v : Fin n) :
    OMA.gpWeight A x u * OMA.gpWeight B x v + OMA.gpWeight B x u * OMA.gpWeight A x v =
      if InBiclique A B u v then x u * x v else 0 := by
  by_cases huA : u ∈ A
  · have huB : u ∉ B := fun huB => Finset.disjoint_left.mp h huA huB
    by_cases hvB : v ∈ B <;> simp [OMA.gpWeight, InBiclique, huA, huB, hvB]
  · by_cases huB : u ∈ B
    · by_cases hvA : v ∈ A <;> simp [OMA.gpWeight, InBiclique, huA, huB, hvA]
    · simp [OMA.gpWeight, InBiclique, huA, huB]

lemma OMA.gpPairSum {n k : ℕ} {A B : Fin k → Finset (Fin n)}
    (h : IsBicliquePartition (completeGraph (Fin n)) k A B) (x : Fin n → ℝ)
    (u v : Fin n) :
    (∑ i, (OMA.gpWeight (A i) x u * OMA.gpWeight (B i) x v
      + OMA.gpWeight (B i) x u * OMA.gpWeight (A i) x v)) =
      if u = v then 0 else x u * x v := by
  simp_rw [OMA.gpTerm (h.disjoint _)]
  by_cases huv : u = v
  · subst v
    have hnone (i : Fin k) : ¬ InBiclique (A i) (B i) u u := by
      intro hi
      exact (show u ≠ u from (h.adj_iff u u).2 ⟨i, hi⟩) rfl
    simp [hnone]
  · obtain ⟨i, hi⟩ := (h.adj_iff u v).1 huv
    rw [if_neg huv, Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      exact if_neg (fun hj => hji (h.unique u v j i hj hi))
    · simp

lemma OMA.gpQuadratic {n k : ℕ} {A B : Fin k → Finset (Fin n)}
    (h : IsBicliquePartition (completeGraph (Fin n)) k A B) (x : Fin n → ℝ) :
    (∑ v, x v) * (∑ v, x v) - (∑ v, x v * x v) =
      ∑ i, (OMA.gpSum (A i) x * OMA.gpSum (B i) x
        + OMA.gpSum (B i) x * OMA.gpSum (A i) x) := by
  calc
    _ = ∑ u, ∑ v, if u = v then 0 else x u * x v := by
      have hi (u v : Fin n) : (if u = v then 0 else x u * x v) =
          x u * x v - (if u = v then x u * x v else 0) := by
        split_ifs <;> simp
      simp [hi, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    _ = ∑ u, ∑ v, ∑ i,
        (OMA.gpWeight (A i) x u * OMA.gpWeight (B i) x v
          + OMA.gpWeight (B i) x u * OMA.gpWeight (A i) x v) := by
      simp_rw [OMA.gpPairSum h]
    _ = ∑ i, ∑ u, ∑ v,
        (OMA.gpWeight (A i) x u * OMA.gpWeight (B i) x v
          + OMA.gpWeight (B i) x u * OMA.gpWeight (A i) x v) := by
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin n)))
        (t := (Finset.univ : Finset (Fin k)))]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, OMA.gpWeight_sum]

lemma OMA.gpLower {n k : ℕ} {A B : Fin k → Finset (Fin n)}
    (h : IsBicliquePartition (completeGraph (Fin n)) k A B) : n - 1 ≤ k := by
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ × (Fin k → ℝ) :=
    (OMA.gpSum Finset.univ).prod (LinearMap.pi fun i => OMA.gpSum (A i))
  have hL : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    rw [eq_bot_iff]
    intro x hx
    have hxL : L x = 0 := LinearMap.mem_ker.mp hx
    have hxTotal : (∑ v, x v) = 0 := by
      simpa [L, OMA.gpSum_apply] using congrArg Prod.fst hxL
    have hxA (i : Fin k) : OMA.gpSum (A i) x = 0 := by
      simpa [L] using congrFun (congrArg Prod.snd hxL) i
    have hsquare : (∑ v, x v * x v) = 0 := by
      have hf := OMA.gpQuadratic h x
      simpa [hxTotal, hxA] using hf
    rw [Submodule.mem_bot]
    funext v
    have hv := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => mul_self_nonneg (x w))).mp
      hsquare v (Finset.mem_univ v)
    exact mul_self_eq_zero.mp hv
  have hd := LinearMap.finrank_le_finrank_of_injective hL
  simp only [Module.finrank_pi, Fintype.card_fin, Module.finrank_prod, Module.finrank_self] at hd
  omega

lemma OMA.gpUpper (n : ℕ) :
    ∃ A B : Fin (n - 1) → Finset (Fin n),
      IsBicliquePartition (completeGraph (Fin n)) (n - 1) A B := by
  let A (i : Fin (n - 1)) : Finset (Fin n) := {⟨i.val + 1, by omega⟩}
  let B (i : Fin (n - 1)) : Finset (Fin n) := Finset.univ.filter fun u => u.val < i.val + 1
  have hA (i : Fin (n - 1)) (u : Fin n) : u ∈ A i ↔ u.val = i.val + 1 := by
    simp only [A, Finset.mem_singleton]
    exact Fin.ext_iff
  have hB (i : Fin (n - 1)) (u : Fin n) : u ∈ B i ↔ u.val < i.val + 1 := by simp [B]
  have hmem (i : Fin (n - 1)) (u v : Fin n) :
      InBiclique (A i) (B i) u v ↔
        (u.val = i.val + 1 ∧ v.val < i.val + 1)
          ∨ (u.val < i.val + 1 ∧ v.val = i.val + 1) := by
    simp [InBiclique, hA, hB]
  refine ⟨A, B, ⟨?_, ?_, ?_⟩⟩
  · intro i
    rw [Finset.disjoint_left]
    intro u hu hv
    have := (hA i u).mp hu
    have := (hB i u).mp hv
    omega
  · intro u v
    change u ≠ v ↔ _
    constructor
    · intro huv
      have hvals : u.val ≠ v.val := fun h => huv (Fin.ext h)
      by_cases hvu : v.val < u.val
      · refine ⟨⟨u.val - 1, by omega⟩, (hmem _ _ _).2 (Or.inl ⟨?_, ?_⟩)⟩ <;> dsimp <;> omega
      · refine ⟨⟨v.val - 1, by omega⟩, (hmem _ _ _).2 (Or.inr ⟨?_, ?_⟩)⟩ <;> dsimp <;> omega
    · rintro ⟨i, hi⟩ rfl
      rcases (hmem i u u).1 hi with h | h <;> omega
  · intro u v i j hi hj
    apply Fin.ext
    rcases (hmem i u v).1 hi with hi | hi <;>
      rcases (hmem j u v).1 hj with hj | hj <;> omega

theorem OMA.solution : type_of% @AlonSaksSeymourConjecture.alon_saks_seymour_conjecture.variants.graham_pollak := by
  intro n
  have hUpper := OMA.gpUpper n
  refine le_antisymm (Nat.sInf_le hUpper) (le_csInf ⟨n - 1, hUpper⟩ ?_)
  rintro k ⟨A, B, h⟩
  exact OMA.gpLower h
