import FormalConjectures.ErdosProblems.«30»
import Mathlib.Combinatorics.Additive.Energy

/-!
Erdős–Turán upper bound h(N) ≤ √N + 2 N^{1/4} via window counting and additive energy.

For a Sidon set `A` and `B = {0, ..., u}`, the additive energy `E[A, B]` is at most
`|A| (u + 1) + (u + 1) u`: quadruples with `a₁ = a₂` force `b₁ = b₂`, and for `a₁ ≠ a₂`
the pair `(b₁, b₂)` determines `(a₁, a₂)` by the Sidon property.
Combined with Mathlib's `|A|² |B|² ≤ |A + B| E[A, B]` this gives the window bound
`|A|² (u + 1) ≤ (|A| + u) (N + u + 1)` for `A ⊆ [0, N]`. Taking `u = ⌊N^{3/4}⌋` and
writing `t = N^{1/4}` yields `|A|² ≤ |A| + t³ + |A| t + t⁴`, hence `|A| ≤ t² + 2 t`.
-/

namespace OMA.E30

open Finset Filter
open scoped Pointwise

/-- Additive energy of a Sidon set against an initial segment `{0, ..., u}`. -/
theorem energy_le (A : Finset ℕ) (hS : IsSidon (A : Set ℕ)) (u : ℕ) :
    Finset.addEnergy A (Finset.range (u + 1)) ≤ A.card * (u + 1) + (u + 1) * u := by
  unfold Finset.addEnergy
  rw [← Finset.card_filter_add_card_filter_not (fun x : (ℕ × ℕ) × ℕ × ℕ => x.1.1 = x.1.2)]
  apply add_le_add
  · have h := Finset.card_le_card_of_injOn (fun x : (ℕ × ℕ) × ℕ × ℕ => (x.1.1, x.2.1))
      (s := Finset.filter (fun x : (ℕ × ℕ) × ℕ × ℕ => x.1.1 = x.1.2)
        (Finset.filter (fun x : (ℕ × ℕ) × ℕ × ℕ => x.1.1 + x.2.1 = x.1.2 + x.2.2)
          ((A ×ˢ A) ×ˢ (Finset.range (u + 1)) ×ˢ (Finset.range (u + 1)))))
      (t := A ×ˢ Finset.range (u + 1)) ?_ ?_
    · simpa [Finset.card_product] using h
    · rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
      exact ⟨hx.1.1.1.1, hx.1.1.2.1⟩
    · rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ hx ⟨⟨c₁, c₂⟩, ⟨d₁, d₂⟩⟩ hy hxy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx hy
      simp only [Prod.mk.injEq] at hxy ⊢
      obtain ⟨⟨_, h1⟩, h2⟩ := hx
      obtain ⟨⟨_, h3⟩, h4⟩ := hy
      omega
  · have h := Finset.card_le_card_of_injOn (fun x : (ℕ × ℕ) × ℕ × ℕ => x.2)
      (s := Finset.filter (fun x : (ℕ × ℕ) × ℕ × ℕ => ¬ x.1.1 = x.1.2)
        (Finset.filter (fun x : (ℕ × ℕ) × ℕ × ℕ => x.1.1 + x.2.1 = x.1.2 + x.2.2)
          ((A ×ˢ A) ×ˢ (Finset.range (u + 1)) ×ˢ (Finset.range (u + 1)))))
      (t := (Finset.range (u + 1)).offDiag) ?_ ?_
    · rw [Finset.offDiag_card, Finset.card_range] at h
      have e : (u + 1) * (u + 1) = (u + 1) * u + (u + 1) := by ring
      omega
    · rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
      simp only [Finset.mem_coe, Finset.mem_offDiag, Finset.mem_range]
      obtain ⟨⟨⟨_, hb₁, hb₂⟩, h1⟩, h2⟩ := hx
      refine ⟨hb₁, hb₂, ?_⟩
      intro hb
      apply h2
      omega
    · rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ hx ⟨⟨c₁, c₂⟩, ⟨d₁, d₂⟩⟩ hy hxy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx hy
      simp only [Prod.mk.injEq] at hxy ⊢
      obtain ⟨⟨⟨⟨ha₁, ha₂⟩, _⟩, h1⟩, h2⟩ := hx
      obtain ⟨⟨⟨⟨hc₁, hc₂⟩, _⟩, h3⟩, h4⟩ := hy
      obtain ⟨rfl, rfl⟩ := hxy
      have hsum : a₁ + c₂ = c₁ + a₂ := by omega
      rcases hS a₁ (Finset.mem_coe.mpr ha₁) c₁ (Finset.mem_coe.mpr hc₁) c₂
          (Finset.mem_coe.mpr hc₂) a₂ (Finset.mem_coe.mpr ha₂) hsum with h | h
      · exact ⟨⟨h.1, h.2.symm⟩, rfl, rfl⟩
      · exact absurd h.1 h2

/-- Window bound with an arbitrary left end point `m`. -/
theorem window_bound_gen (A : Finset ℕ) (hS : IsSidon (A : Set ℕ)) (m D u : ℕ)
    (hA : ∀ x ∈ A, m ≤ x ∧ x ≤ m + D) :
    A.card ^ 2 * (u + 1) ≤ (A.card + u) * (D + u + 1) := by
  have h1 := Finset.le_card_add_mul_addEnergy A (Finset.range (u + 1))
  rw [Finset.card_range] at h1
  have h2 : (A + Finset.range (u + 1)).card ≤ D + u + 1 := by
    have hsub : A + Finset.range (u + 1) ⊆ Finset.Icc m (m + D + u) := by
      intro y hy
      rw [Finset.mem_add] at hy
      obtain ⟨a, ha, b, hb, rfl⟩ := hy
      have := hA a ha
      rw [Finset.mem_range] at hb
      rw [Finset.mem_Icc]
      omega
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    omega
  have h3 := energy_le A hS u
  have key : (u + 1) * (A.card ^ 2 * (u + 1)) ≤ (u + 1) * ((A.card + u) * (D + u + 1)) := by
    calc (u + 1) * (A.card ^ 2 * (u + 1)) = A.card ^ 2 * (u + 1) ^ 2 := by ring
      _ ≤ (A + Finset.range (u + 1)).card * Finset.addEnergy A (Finset.range (u + 1)) := h1
      _ ≤ (D + u + 1) * (A.card * (u + 1) + (u + 1) * u) := Nat.mul_le_mul h2 h3
      _ = (u + 1) * ((A.card + u) * (D + u + 1)) := by ring
  exact Nat.le_of_mul_le_mul_left key (Nat.succ_pos u)

/-- Erdős–Turán window counting: a Sidon set in `[0, D]` satisfies
`|A|² (u + 1) ≤ (|A| + u) (D + u + 1)` for every `u`. -/
theorem window_bound (A : Finset ℕ) (hS : IsSidon (A : Set ℕ)) (D u : ℕ)
    (hA : ∀ x ∈ A, x ≤ D) : A.card ^ 2 * (u + 1) ≤ (A.card + u) * (D + u + 1) :=
  window_bound_gen A hS 0 D u (fun x hx => ⟨Nat.zero_le x, by simpa using hA x hx⟩)

/-- Some Sidon subset of `{1, ..., N}` attains `h N`. -/
theorem exists_sidon_attaining (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsSidon (A : Set ℕ) ∧ A.card = Erdos30.h N := by
  unfold Erdos30.h Finset.maxSidonSubsetCard
  have hne : ((Finset.Icc 1 N).powerset.filter fun B : Finset ℕ => IsSidon (B : Set ℕ)).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, by
      intro a ha
      simp at ha⟩⟩
  obtain ⟨A, hA, hmax⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  exact ⟨A, hA.1, hA.2, hmax.symm⟩

/-- Real-variable core: from the window inequality with `u = ⌊t³⌋`, `N = t⁴`, get `k ≤ t² + 2t`. -/
theorem core (k t U : ℝ) (ht : 1 ≤ t) (hk : 0 ≤ k) (hU1 : t ^ 3 < U) (hU2 : U - 1 ≤ t ^ 3)
    (hw : k ^ 2 * U ≤ (k + (U - 1)) * (t ^ 4 + U)) : k ≤ t ^ 2 + 2 * t := by
  have hU0 : 0 < U := by nlinarith [pow_pos (by linarith : (0 : ℝ) < t) 3]
  have h2 : k * t ^ 4 ≤ k * t * U := by
    have : t ^ 4 ≤ t * U := by
      have := mul_le_mul_of_nonneg_left hU1.le (by linarith : (0 : ℝ) ≤ t)
      nlinarith
    nlinarith
  have h4 : U * (U - 1) ≤ U * t ^ 3 := mul_le_mul_of_nonneg_left hU2 hU0.le
  have hb : U * k ^ 2 ≤ U * (k + t ^ 3 + k * t + t ^ 4) := by
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ t) 4]
  have hb' : k ^ 2 ≤ k + t ^ 3 + k * t + t ^ 4 := le_of_mul_le_mul_left hb hU0
  by_contra hcon
  push Not at hcon
  have ht2 : 0 < t ^ 2 + 2 * t := by positivity
  have hp : 0 < (k - (t ^ 2 + 2 * t)) * (k - 1 - t + (t ^ 2 + 2 * t)) := by
    apply mul_pos <;> nlinarith
  have ht3 : t ≤ t ^ 3 := by nlinarith
  nlinarith

/-- Erdős–Turán: `h N ≤ √N + 2 N^{1/4}` for every `N ≥ 1`. -/
theorem h_le (N : ℕ) (hN : 1 ≤ N) :
    (Erdos30.h N : ℝ) ≤ (N : ℝ).sqrt + 2 * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  obtain ⟨A, hsub, hS, hcard⟩ := exists_sidon_attaining N
  set t : ℝ := (N : ℝ) ^ (4⁻¹ : ℝ) with htdef
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have ht1 : 1 ≤ t := Real.one_le_rpow hN1 (by norm_num)
  have ht4 : t ^ 4 = (N : ℝ) := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have hsq : (N : ℝ).sqrt = t ^ 2 := by
    rw [← ht4, show t ^ 4 = (t ^ 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  set u : ℕ := ⌊t ^ 3⌋₊ with hudef
  have hx0 : (0 : ℝ) ≤ t ^ 3 := by positivity
  have hu1 : (u : ℝ) ≤ t ^ 3 := Nat.floor_le hx0
  have hu2 : t ^ 3 < (u : ℝ) + 1 := Nat.lt_floor_add_one _
  have hw := window_bound A hS N u (fun x hx => (Finset.mem_Icc.mp (hsub hx)).2)
  have hwR : ((A.card : ℕ) : ℝ) ^ 2 * ((u : ℝ) + 1) ≤
      ((A.card : ℝ) + ((u : ℝ) + 1 - 1)) * (t ^ 4 + ((u : ℝ) + 1)) := by
    have := (Nat.cast_le (α := ℝ)).mpr hw
    push_cast at this
    rw [ht4]
    linarith
  have hk := core (A.card : ℝ) t ((u : ℝ) + 1) ht1 (Nat.cast_nonneg _) hu2 (by linarith) hwR
  rw [← hcard, hsq]
  exact hk

end OMA.E30

theorem OMA.solution : type_of% @Erdos30.erdos_30.variants.erdos_turan := by
  refine ⟨2, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
  exact OMA.E30.h_le N hN
