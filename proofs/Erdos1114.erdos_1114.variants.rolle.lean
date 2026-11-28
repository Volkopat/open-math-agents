import FormalConjectures.ErdosProblems.«1114»

-- Shorter proof of Erdos1114.erdos_1114.variants.rolle via exact root-set equality
-- Credit: @raider99k

open Finset Polynomial

theorem OMA.solution : type_of% @Erdos1114.erdos_1114.variants.rolle := by
  intro N a d hd f hdeg hr
  have hstep {j k : ℕ} (h : j < k) : a + d * (j + 1) ≤ a + d * k := by
    nlinarith [show (j : ℝ) + 1 ≤ k by exact_mod_cast h]
  have hex (k : Fin N) : ∃ x ∈ Set.Ioo (a + d * k) (a + d * (k + 1)), f.derivative.eval x = 0 :=
    exists_hasDerivAt_eq_zero (by linarith) f.continuous.continuousOn
      (by rw [hr k k.2.le, ← Nat.cast_succ, hr (k + 1) k.2]) fun x _ => f.hasDerivAt x
  choose c hc0 hc1 using hex
  have hinj : Function.Injective c := fun i j hij => by
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · linarith [(hc0 i).2, (hc0 j).1, hstep h]
    · linarith [(hc0 j).2, (hc0 i).1, hstep h]
  have hf' : f.derivative ≠ 0 := fun h => by
    have := derivative_eq_zero.mp h; omega
  have hsub : univ.image c ⊆ f.derivative.roots.toFinset := by
    intro x hx
    obtain ⟨k, _, rfl⟩ := mem_image.mp hx
    exact Multiset.mem_toFinset.mpr ((mem_roots hf').mpr (hc1 k))
  have heq : univ.image c = f.derivative.roots.toFinset :=
    eq_of_subset_of_card_le hsub <| by
      rw [card_image_of_injective _ hinj, card_fin]
      have := natDegree_derivative_le f
      have := card_roots' f.derivative
      exact (Multiset.toFinset_card_le _).trans (by omega)
  have hall : ∀ x, f.derivative.eval x = 0 → ∃ k : Fin N, c k = x := fun x hx => by
    simpa [← heq] using Multiset.mem_toFinset.mpr ((mem_roots hf').mpr hx)
  refine ⟨fun k hk => ⟨c ⟨k, hk⟩, ⟨hc0 ⟨k, hk⟩, hc1 ⟨k, hk⟩⟩, fun y ⟨hy, hy0⟩ => ?_⟩, fun x hx => ?_⟩
  · obtain ⟨j, rfl⟩ := hall y hy0
    rcases lt_trichotomy j.1 k with h | h | h
    · linarith [(hc0 j).2, hy.1, hstep h]
    · exact congrArg c (Fin.ext h)
    · linarith [(hc0 j).1, hy.2, hstep h]
  · obtain ⟨k, rfl⟩ := hall x hx
    exact ⟨k, k.2, hc0 k⟩
