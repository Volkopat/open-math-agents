import FormalConjectures.ErdosProblems.«138»

/-!
Reduction `Erdos138.erdos_138.variants.quotient.R1` of Erdős Problem 138 quotient
(USD 500 open Erdős prize problem: does `W(k + 1) / W(k) -> infinity`?).
Credit: @B221393

- `H1`: Van der Waerden existence and positivity for 2-colorings: for every `k >= 1`,
  `monoAP_guarantee_set 2 k` is nonempty and `1 <= W k`.
- `H2`: Coloring-blowup step (the open combinatorial heart of the USD 500 problem):
  for every amplification factor `M`, for all sufficiently large `k`, any `k`-AP-free
  2-coloring of `[1, W(k) - 1]` can be blown up to a `(k + 1)`-AP-free 2-coloring of
  `[1, M * W(k)]`.
- `main`: Unconditionally proves restriction monotonicity (`coloring_restrict_avoid`),
  extracts an extremal `k`-AP-free 2-coloring of `[1, W(k) - 1]` from the `sInf`
  definition of `W(k)`, applies `H2` to deduce `M * W(k) < W(k + 1)`, and concludes
  `Filter.atTop.Tendsto (fun k => (W (k + 1) : Q) / W k) Filter.atTop`.
-/

namespace OMA.R_Erdos138_erdos_138_variants_quotient_R1

/-- Van der Waerden existence and positivity for 2 colors: for every `k >= 1`, a guaranteeing
interval exists and `1 <= W k`. -/
def H1 : Prop :=
  ∀ k : ℕ, 1 ≤ k → (Erdos138.monoAP_guarantee_set 2 k).Nonempty ∧ 1 ≤ Erdos138.W k

/-- Coloring-blowup core of Erdős Problem 138 quotient: for every factor `M`, for all
sufficiently large `k`, the existence of a `k`-AP-free 2-coloring of `[1, W(k) - 1]` yields
a `(k + 1)`-AP-free 2-coloring of `[1, M * W(k)]`. -/
def H2 : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    (∃ c : Finset.Icc 1 (Erdos138.W k - 1) → Fin 2, ¬ ContainsMonoAPofLength c k) →
    ∃ c' : Finset.Icc 1 (M * Erdos138.W k) → Fin 2, ¬ ContainsMonoAPofLength c' (k + 1)

lemma coloring_restrict_avoid {N M r : ℕ} (hNM : N ≤ M)
    (c' : Finset.Icc 1 M → Fin 2) (havoid : ¬ ContainsMonoAPofLength c' r) :
    ∃ c : Finset.Icc 1 N → Fin 2, ¬ ContainsMonoAPofLength c r := by
  let ι : Finset.Icc 1 N → Finset.Icc 1 M := fun x =>
    ⟨x.1, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp x.2).1, le_trans (Finset.mem_Icc.mp x.2).2 hNM⟩⟩
  refine ⟨fun x => c' (ι x), ?_⟩
  rintro ⟨col, ap, hap, hcol⟩
  apply havoid
  refine ⟨col, ι '' ap, ?_, ?_⟩
  · convert hap using 1
    ext z
    simp only [Set.mem_image, ι]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.1, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp x.2).1,
        le_trans (Finset.mem_Icc.mp x.2).2 hNM⟩⟩, ⟨x, hx, rfl⟩, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hcol x hx

theorem main : H1 → H2 → type_of% @Erdos138.erdos_138.variants.quotient := by
  intro h1 h2
  rw [Filter.tendsto_atTop_atTop]
  intro b
  let M : ℕ := Nat.ceil (max b (0 : ℚ)) + 1
  rcases h2 M with ⟨K, hK⟩
  refine ⟨max K 1, ?_⟩
  intro k hk
  have hkK : K ≤ k := le_trans (le_max_left _ _) hk
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
  have hWk_pos : 1 ≤ Erdos138.W k := (h1 k hk1).2
  have hWk1_ne : (Erdos138.monoAP_guarantee_set 2 (k + 1)).Nonempty :=
    (h1 (k + 1) (by omega)).1
  have hex_k : ∃ c : Finset.Icc 1 (Erdos138.W k - 1) → Fin 2, ¬ ContainsMonoAPofLength c k := by
    have hlt : Erdos138.W k - 1 < Erdos138.W k := by omega
    have hnotmem : Erdos138.W k - 1 ∉ Erdos138.monoAP_guarantee_set 2 k :=
      fun hmem => not_le_of_gt hlt (Nat.sInf_le hmem)
    simpa only [Erdos138.monoAP_guarantee_set, Set.mem_ofPred_eq, not_forall] using hnotmem
  rcases hK k hkK hex_k with ⟨c', hc'⟩
  have hWk1_mem : Erdos138.W (k + 1) ∈ Erdos138.monoAP_guarantee_set 2 (k + 1) :=
    Nat.sInf_mem hWk1_ne
  have hMW_lt : M * Erdos138.W k < Erdos138.W (k + 1) := by
    by_contra hle
    push Not at hle
    rcases coloring_restrict_avoid hle c' hc' with ⟨c, hc⟩
    exact hc (hWk1_mem c)
  have hWk_qpos : (0 : ℚ) < (Erdos138.W k : ℚ) := by exact_mod_cast (by omega : 0 < Erdos138.W k)
  have hM_le : (M : ℚ) ≤ (Erdos138.W (k + 1) : ℚ) / (Erdos138.W k : ℚ) := by
    rw [le_div_iff₀ hWk_qpos]
    have hnat : M * Erdos138.W k ≤ Erdos138.W (k + 1) := le_of_lt hMW_lt
    exact_mod_cast hnat
  have hb_le_M : b ≤ (M : ℚ) := by
    have h1' : b ≤ max b (0 : ℚ) := le_max_left _ _
    have h2' : max b (0 : ℚ) ≤ (Nat.ceil (max b (0 : ℚ)) : ℚ) := Nat.le_ceil _
    have h3' : (Nat.ceil (max b (0 : ℚ)) : ℚ) ≤ (M : ℚ) := by exact_mod_cast Nat.le_succ _
    exact le_trans h1' (le_trans h2' h3')
  exact le_trans hb_le_M hM_le

end OMA.R_Erdos138_erdos_138_variants_quotient_R1
