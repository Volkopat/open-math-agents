import OMAStatements.S_itp_gaussian_interference_channel

-- Credit: @Pixelstorm44

namespace OMA.R_itp_gaussian_interference_channel_R1

open OMA.S_itp_gaussian_interference_channel
open scoped BigOperators

/-- Preserve d averages exactly, using at most d+1 of the original phases. -/
theorem compress_phases {m d : ℕ} (v : Fin m → Fin d → ℝ) (w : Fin m → ℝ)
    (hpos : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    ∃ (k : ℕ) (_ : k ≤ d + 1) (pick : Fin k → Fin m) (u : Fin k → ℝ),
      (∀ i, 0 < u i) ∧ (∑ i, u i = 1) ∧
      ∀ j, ∑ i, u i * v (pick i) j = ∑ i, w i * v i j := by
  classical
  have hx : ∑ i, w i • v i ∈ convexHull ℝ (Set.range v) :=
    (convex_convexHull ℝ _).sum_mem (fun i _ => hpos i) hsum
      (fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩)
  obtain ⟨ι, inst, z, u, hz, hind, hu, hu_sum, havg⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  choose pick hpick using fun i => hz (Set.mem_range_self i)
  let e := (Fintype.equivFin ι).symm
  have hdim := hind.card_le_finrank_succ.trans
    (Nat.add_le_add_right (Submodule.finrank_le (vectorSpan ℝ (Set.range z))) 1)
  refine ⟨Fintype.card ι, by simpa [Module.finrank_pi] using hdim,
    fun i => pick (e i), fun i => u (e i), fun i => hu (e i),
    (e.sum_comp u).trans hu_sum, ?_⟩
  intro j
  simp_rw [hpick]
  rw [e.sum_comp (fun i => u i * z i j)]
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun havg j

/-- The two power coordinates and the seven decoding bounds are sufficient
statistics for coded time sharing. All nine averages use the same weights. -/
theorem hk_ten_phases (a b P₁ P₂ : ℝ) (r : ℝ × ℝ) :
    InGaussianHKRegion a b P₁ P₂ r.1 r.2 ↔
      0 ≤ r.1 ∧ 0 ≤ r.2 ∧
      ∃ (k : ℕ) (_ : k ≤ 10) (w c p C P : Fin k → ℝ),
        (∀ i, 0 < w i) ∧ (∑ i, w i = 1) ∧
        (∀ i, 0 ≤ c i ∧ 0 ≤ p i ∧ 0 ≤ C i ∧ 0 ≤ P i) ∧
        (∑ i, w i * (c i + p i) ≤ P₁) ∧ (∑ i, w i * (C i + P i) ≤ P₂) ∧
        let cap := fun (x : ℝ) => (1 / 2 : ℝ) * log2 (1 + x)
        let A := fun i x => cap (x / (1 + a^2 * P i))
        let B := fun i x => cap (x / (1 + b^2 * p i))
        let E := fun (f : Fin k → ℝ) => ∑ i, w i * f i
        r.1 ≤ E (fun i => A i (c i + p i)) ∧
        r.2 ≤ E (fun i => B i (C i + P i)) ∧
        r.1 + r.2 ≤ E (fun i => A i (c i + p i + a^2 * C i) + B i (P i)) ∧
        r.1 + r.2 ≤ E (fun i => A i (p i) + B i (C i + P i + b^2 * c i)) ∧
        r.1 + r.2 ≤ E (fun i => A i (p i + a^2 * C i) + B i (P i + b^2 * c i)) ∧
        2*r.1 + r.2 ≤ E (fun i => A i (c i + p i + a^2 * C i) + A i (p i) + B i (P i + b^2 * c i)) ∧
        r.1 + 2*r.2 ≤ E (fun i => B i (C i + P i + b^2 * c i) + B i (P i) + A i (p i + a^2 * C i)) := by
  constructor
  · rintro ⟨hr, hs, m, w, c, p, C, P, hw, hw_sum, hnonneg,
      h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩
    let cap := fun (x : ℝ) => (1 / 2 : ℝ) * log2 (1 + x)
    let A := fun i x => cap (x / (1 + a^2 * P i))
    let B := fun i x => cap (x / (1 + b^2 * p i))
    let v : Fin m → Fin 9 → ℝ := fun i =>
      ![c i + p i,
        C i + P i,
        A i (c i + p i),
        B i (C i + P i),
        A i (c i + p i + a^2 * C i) + B i (P i),
        A i (p i) + B i (C i + P i + b^2 * c i),
        A i (p i + a^2 * C i) + B i (P i + b^2 * c i),
        A i (c i + p i + a^2 * C i) + A i (p i) + B i (P i + b^2 * c i),
        B i (C i + P i + b^2 * c i) + B i (P i) + A i (p i + a^2 * C i)]
    obtain ⟨k, hk, pick, u, hu, hu_sum, he⟩ := compress_phases v w hw hw_sum
    refine ⟨hr, hs, k, hk, u, c ∘ pick, p ∘ pick, C ∘ pick, P ∘ pick,
      hu, hu_sum, fun i => hnonneg (pick i), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (he 0).trans_le h₀
    · exact (he 1).trans_le h₁
    · exact le_trans h₂ (he 2).ge
    · exact le_trans h₃ (he 3).ge
    · exact le_trans h₄ (he 4).ge
    · exact le_trans h₅ (he 5).ge
    · exact le_trans h₆ (he 6).ge
    · exact le_trans h₇ (he 7).ge
    · exact le_trans h₈ (he 8).ge
  · rintro ⟨hr, hs, k, _, w, c, p, C, P, hw, hw_sum, hrest⟩
    exact ⟨hr, hs, k, w, c, p, C, P, fun i => (hw i).le, hw_sum, hrest⟩

/-- Coding theorem for mixtures of at most ten Gaussian superposition phases. -/
def H1 : Prop :=
  ∀ (a b P₁ P₂ : ℝ), 0 ≤ a → 0 ≤ b → 0 < P₁ → 0 < P₂ →
    { r : ℝ × ℝ |
      0 ≤ r.1 ∧ 0 ≤ r.2 ∧
      ∃ (k : ℕ) (_ : k ≤ 10) (w c p C P : Fin k → ℝ),
        (∀ i, 0 < w i) ∧ (∑ i, w i = 1) ∧
        (∀ i, 0 ≤ c i ∧ 0 ≤ p i ∧ 0 ≤ C i ∧ 0 ≤ P i) ∧
        (∑ i, w i * (c i + p i) ≤ P₁) ∧ (∑ i, w i * (C i + P i) ≤ P₂) ∧
        let cap := fun (x : ℝ) => (1 / 2 : ℝ) * log2 (1 + x)
        let A := fun i x => cap (x / (1 + a^2 * P i))
        let B := fun i x => cap (x / (1 + b^2 * p i))
        let E := fun (f : Fin k → ℝ) => ∑ i, w i * f i
        r.1 ≤ E (fun i => A i (c i + p i)) ∧
        r.2 ≤ E (fun i => B i (C i + P i)) ∧
        r.1 + r.2 ≤ E (fun i => A i (c i + p i + a^2 * C i) + B i (P i)) ∧
        r.1 + r.2 ≤ E (fun i => A i (p i) + B i (C i + P i + b^2 * c i)) ∧
        r.1 + r.2 ≤ E (fun i => A i (p i + a^2 * C i) + B i (P i + b^2 * c i)) ∧
        2*r.1 + r.2 ≤ E (fun i => A i (c i + p i + a^2 * C i) + A i (p i) + B i (P i + b^2 * c i)) ∧
        r.1 + 2*r.2 ≤ E (fun i => B i (C i + P i + b^2 * c i) + B i (P i) + A i (p i + a^2 * C i)) } ⊆ closure { r : ℝ × ℝ | InGaussianICAchievable a b P₁ P₂ r.1 r.2 }

/-- Converse with approximation by mixtures of at most ten phases. -/
def H2 : Prop :=
  ∀ (a b P₁ P₂ : ℝ), 0 ≤ a → 0 ≤ b → 0 < P₁ → 0 < P₂ →
    { r : ℝ × ℝ | InGaussianICAchievable a b P₁ P₂ r.1 r.2 } ⊆ closure
    { r : ℝ × ℝ |
      0 ≤ r.1 ∧ 0 ≤ r.2 ∧
      ∃ (k : ℕ) (_ : k ≤ 10) (w c p C P : Fin k → ℝ),
        (∀ i, 0 < w i) ∧ (∑ i, w i = 1) ∧
        (∀ i, 0 ≤ c i ∧ 0 ≤ p i ∧ 0 ≤ C i ∧ 0 ≤ P i) ∧
        (∑ i, w i * (c i + p i) ≤ P₁) ∧ (∑ i, w i * (C i + P i) ≤ P₂) ∧
        let cap := fun (x : ℝ) => (1 / 2 : ℝ) * log2 (1 + x)
        let A := fun i x => cap (x / (1 + a^2 * P i))
        let B := fun i x => cap (x / (1 + b^2 * p i))
        let E := fun (f : Fin k → ℝ) => ∑ i, w i * f i
        r.1 ≤ E (fun i => A i (c i + p i)) ∧
        r.2 ≤ E (fun i => B i (C i + P i)) ∧
        r.1 + r.2 ≤ E (fun i => A i (c i + p i + a^2 * C i) + B i (P i)) ∧
        r.1 + r.2 ≤ E (fun i => A i (p i) + B i (C i + P i + b^2 * c i)) ∧
        r.1 + r.2 ≤ E (fun i => A i (p i + a^2 * C i) + B i (P i + b^2 * c i)) ∧
        2*r.1 + r.2 ≤ E (fun i => A i (c i + p i + a^2 * C i) + A i (p i) + B i (P i + b^2 * c i)) ∧
        r.1 + 2*r.2 ≤ E (fun i => B i (C i + P i + b^2 * c i) + B i (P i) + A i (p i + a^2 * C i)) }

theorem main : H1 → H2 → type_of% @OMA.S_itp_gaussian_interference_channel.main := by
  intro coding converse a b P₁ P₂ ha hb hP₁ hP₂
  have set_eq := Set.ext (a := { r : ℝ × ℝ | InGaussianHKRegion a b P₁ P₂ r.1 r.2 })
    (b := { r : ℝ × ℝ | _ }) (hk_ten_phases a b P₁ P₂)
  rw [set_eq]
  exact Set.Subset.antisymm (closure_minimal (converse a b P₁ P₂ ha hb hP₁ hP₂) isClosed_closure)
    (closure_minimal (coding a b P₁ P₂ ha hb hP₁ hP₂) isClosed_closure)

end OMA.R_itp_gaussian_interference_channel_R1
