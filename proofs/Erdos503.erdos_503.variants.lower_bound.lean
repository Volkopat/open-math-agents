import FormalConjectures.ErdosProblems.«503»

-- Problem: Erdős Problem 503 — lower bound
-- Credit: @luciusacarr (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Take a regular simplex g_0..g_n in ℝ^n with edge √2; the points g_i + g_j form a
-- two-distance set of size C(n+1,2), and every two-distance set is isosceles.

open scoped EuclideanGeometry
open Finset

namespace OMA

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem cross (a b c d : E) (h1 : ‖a - d‖ ^ 2 = 2) (h2 : ‖c - b‖ ^ 2 = 2)
    (h3 : ‖a - b‖ ^ 2 = 2) (h4 : ‖c - d‖ ^ 2 = 2) : inner ℝ (a - c) (b - d) = 0 := by
  rw [norm_sub_sq_real] at h1 h2 h3 h4
  simp only [inner_sub_left, inner_sub_right]
  linarith

theorem sq_share (x a b : E) (h : ‖a - b‖ ^ 2 = 2) : ‖(x + a) - (x + b)‖ ^ 2 = 2 := by
  rw [add_sub_add_left_eq_sub]; exact h

theorem sq_disj (a b c d : E) (h1 : ‖a - d‖ ^ 2 = 2) (h2 : ‖c - b‖ ^ 2 = 2)
    (h3 : ‖a - b‖ ^ 2 = 2) (h4 : ‖c - d‖ ^ 2 = 2) (h5 : ‖a - c‖ ^ 2 = 2) (h6 : ‖b - d‖ ^ 2 = 2) :
    ‖(a + b) - (c + d)‖ ^ 2 = 4 := by
  have : (a + b) - (c + d) = (a - c) + (b - d) := by abel
  rw [this, norm_add_sq_real, cross a b c d h1 h2 h3 h4, h5, h6]
  norm_num

/-- Squared distance between two distinct pair-sums is 2 or 4. -/
theorem pair_sq {N : ℕ} (g : Fin N → E) (hg : ∀ a b, a ≠ b → ‖g a - g b‖ ^ 2 = 2)
    (s t : Finset (Fin N)) (hs : s.card = 2) (ht : t.card = 2) (hst : s ≠ t) :
    ‖(∑ a ∈ s, g a) - (∑ a ∈ t, g a)‖ ^ 2 = 2 ∨ ‖(∑ a ∈ s, g a) - (∑ a ∈ t, g a)‖ ^ 2 = 4 := by
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hs
  obtain ⟨k, l, hkl, rfl⟩ := Finset.card_eq_two.mp ht
  rw [Finset.sum_pair hij, Finset.sum_pair hkl]
  by_cases hik : i = k
  · subst hik
    have hjl : j ≠ l := fun h => hst (by rw [h])
    exact Or.inl (sq_share _ _ _ (hg j l hjl))
  by_cases hil : i = l
  · subst hil
    have hjk : j ≠ k := fun h => hst (by rw [h, Finset.pair_comm])
    left
    rw [add_comm (g k) (g i)]
    exact sq_share _ _ _ (hg j k hjk)
  by_cases hjk : j = k
  · subst hjk
    left
    rw [add_comm (g i) (g j)]
    exact sq_share _ _ _ (hg i l hil)
  by_cases hjl : j = l
  · subst hjl
    left
    rw [add_comm (g i) (g j), add_comm (g k) (g j)]
    exact sq_share _ _ _ (hg i k hik)
  right
  exact sq_disj _ _ _ _ (hg i l hil) (hg k j (Ne.symm hjk)) (hg i j hij) (hg k l hkl)
    (hg i k hik) (hg j l hjl)

theorem dist_of_sq (x y : E) (c : ℝ) (h : ‖x - y‖ ^ 2 = c) : dist x y = Real.sqrt c := by
  rw [dist_eq_norm, ← h, Real.sqrt_sq (norm_nonneg _)]

/-- The pair-sums of a regular simplex form an isosceles set of size `C(N,2)`. -/
theorem simplex_set {N : ℕ} (hN : 2 ≤ N) (g : Fin N → E)
    (hg : ∀ a b, a ≠ b → ‖g a - g b‖ ^ 2 = 2) :
    ∃ A : Set E, A.IsIsosceles ∧ A.ncard = N.choose 2 := by
  classical
  set P : Finset (Finset (Fin N)) := Finset.powersetCard 2 Finset.univ with hP
  set f : Finset (Fin N) → E := fun s => ∑ a ∈ s, g a with hf
  have hval : ∀ s ∈ P, ∀ t ∈ P, s ≠ t → dist (f s) (f t) = Real.sqrt 2 ∨ dist (f s) (f t) = Real.sqrt 4 := by
    intro s hs t ht hst
    rw [hP, Finset.mem_powersetCard] at hs ht
    exact (pair_sq g hg s t hs.2 ht.2 hst).imp (dist_of_sq _ _ _) (dist_of_sq _ _ _)
  have hinj : Set.InjOn f (P : Set (Finset (Fin N))) := by
    intro s hs t ht hfst
    by_contra hne
    have h := hval s hs t ht hne
    rw [hfst, dist_self] at h
    rcases h with h|h <;> linarith
      [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2), Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 4)]
  refine ⟨((P.image f : Finset E) : Set E), ⟨?_, ?_⟩, ?_⟩
  · have hpos : 0 < P.card := by
      rw [hP, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      exact Nat.choose_pos hN
    obtain ⟨s, hs⟩ := Finset.card_pos.mp hpos
    exact ⟨⟨f s, Finset.mem_coe.mpr (Finset.mem_image_of_mem f hs)⟩⟩
  · intro x hx y hy z hz hxy hyz hxz
    rw [Finset.mem_coe, Finset.mem_image] at hx hy hz
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    obtain ⟨u, hu, rfl⟩ := hz
    have h1 := hval s hs t ht (fun h => hxy (by rw [h]))
    have h2 := hval t ht u hu (fun h => hyz (by rw [h]))
    have h3 := hval u hu s hs (fun h => hxz (by rw [h]))
    unfold IsIsosceles
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
    all_goals first
      | exact Or.inl (h1.trans h2.symm)
      | exact Or.inr (Or.inl (h2.trans h3.symm))
      | exact Or.inr (Or.inr (h3.trans h1.symm))
  · rw [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj, hP, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin]

/-- The simplex vertices. -/
noncomputable def gg (n : ℕ) (a : Fin (n + 1)) : EuclideanSpace ℝ (Fin n) :=
  if h : (a : ℕ) < n then EuclideanSpace.single ⟨a, h⟩ (1 : ℝ)
  else WithLp.toLp 2 (fun _ : Fin n => (1 + Real.sqrt (n + 1)) / n)

theorem tt_eq (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * ((1 + Real.sqrt (n + 1)) / n) ^ 2 - 2 * ((1 + Real.sqrt (n + 1)) / n) = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hs : Real.sqrt ((n : ℝ) + 1) ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
  field_simp
  nlinarith

theorem gg_simplex (n : ℕ) (hn : 1 ≤ n) (a b : Fin (n + 1)) (hab : a ≠ b) :
    ‖gg n a - gg n b‖ ^ 2 = 2 := by
  classical
  have key : ∀ a b : Fin (n + 1), (a : ℕ) < (b : ℕ) → ‖gg n a - gg n b‖ ^ 2 = 2 := by
    intro a b hlt
    have ha : (a : ℕ) < n := by have := b.2; omega
    rw [EuclideanSpace.real_norm_sq_eq]
    by_cases hb : (b : ℕ) < n
    · simp only [gg, dif_pos ha, dif_pos hb, PiLp.sub_apply, PiLp.single_apply]
      have hne : (⟨a, ha⟩ : Fin n) ≠ ⟨b, hb⟩ := by
        intro h; rw [Fin.mk.injEq] at h; omega
      have hpt : ∀ i : Fin n, ((if i = ⟨a, ha⟩ then (1 : ℝ) else 0) - (if i = ⟨b, hb⟩ then 1 else 0)) ^ 2
          = (if i = ⟨a, ha⟩ then (1 : ℝ) else 0) + (if i = ⟨b, hb⟩ then 1 else 0) := by
        intro i
        split_ifs with h₁ h₂ <;> norm_num
        exact hne (h₁.symm.trans h₂)
      simp only [hpt, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      norm_num
    · simp only [gg, dif_pos ha, dif_neg hb, PiLp.sub_apply, PiLp.single_apply]
      have hsum : ∀ t : ℝ, ∑ x : Fin n, ((if x = ⟨a, ha⟩ then (1 : ℝ) else 0) - t) ^ 2
          = 1 - 2 * t + n * t ^ 2 := by
        intro t
        have hpt : ∀ i : Fin n, ((if i = ⟨a, ha⟩ then (1 : ℝ) else 0) - t) ^ 2
            = (if i = ⟨a, ha⟩ then (1 - 2 * t : ℝ) else 0) + t ^ 2 := by
          intro i
          split_ifs <;> ring
        simp only [hpt, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      refine (hsum _).trans ?_
      have := tt_eq n hn
      linarith
  rcases lt_or_gt_of_ne (fun h => hab (Fin.ext h)) with h | h
  · exact key a b h
  · rw [← neg_sub, norm_neg]; exact key b a h

end OMA

theorem OMA.solution : type_of% @Erdos503.erdos_503.variants.lower_bound := by
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨({0} : Set (ℝ^0)).ncard, ⟨{0}, ⟨⟨⟨0, rfl⟩⟩, ?_⟩, rfl⟩, by simp⟩
    intro x hx y hy z hz hxy
    exact absurd (hx.trans hy.symm) hxy
  · obtain ⟨A, hA, hcard⟩ := OMA.simplex_set (N := n + 1) (by omega) (OMA.gg n)
      (OMA.gg_simplex n hn)
    exact ⟨A.ncard, ⟨A, hA, rfl⟩, by rw [hcard]⟩
