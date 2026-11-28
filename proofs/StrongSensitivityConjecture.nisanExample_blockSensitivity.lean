import FormalConjectures.Paper.StrongSensitivityConjecture

/-!
Shorter proof of `StrongSensitivityConjecture.nisanExample_blockSensitivity` (Nisan 1989).
For `n = 4 * m`, the accepting condition is `w = 2 * m ∨ w = 2 * m + 1`, a single weighted
sum bound covers all four weight regimes for the upper bound, and an explicit
`Fin (2 * m) ⊕ Fin m` block family gives the lower bound.
-/

open Finset StrongSensitivityConjecture in
theorem OMA.solution : type_of% @StrongSensitivityConjecture.nisanExample_blockSensitivity := by
  rintro _ ⟨m, rfl⟩ hm
  have hnis (x : Fin (4 * m) → Bool) :
      nisanExample (4 * m) x = true ↔ #{j | x j} = 2 * m ∨ #{j | x j} = 2 * m + 1 := by
    simp only [nisanExample, decide_eq_true_eq, mem_insert, mem_singleton]
    rw [show ((4 * m : ℕ) : ℚ) / 2 = (2 * m : ℕ) by push_cast; ring,
      ← Nat.cast_add_one, Nat.cast_inj, Nat.cast_inj]
  have hflip (x : Fin (4 * m) → Bool) (B : Finset (Fin (4 * m))) :
      #{j | flip x B j} + #{j ∈ B | x j} = #{j | x j} + #{j ∈ B | !x j} := by
    simp only [card_filter]
    rw [← univ_inter B, ← sum_ite_mem, ← sum_ite_mem, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ B <;> cases hx : x j <;> simp [StrongSensitivityConjecture.flip, hj, hx]
  rw [show 3 * (4 * m) / 4 = 3 * m by omega]
  apply le_antisymm
  · refine Finset.sup_le fun x _ => ?_
    classical
    refine Finset.sup_le fun cB hcB => ?_
    obtain ⟨hd, hs⟩ := (mem_filter.mp hcB).2
    have hdisj_sum (p : Fin (4 * m) → Prop) [DecidablePred p] :
        ∑ B ∈ cB, #{j ∈ B | p j} ≤ #{j | p j} := by
      rw [← card_biUnion (t := fun B => B.filter p)
        fun B hB C hC h => disjoint_filter_filter (hd hB hC h)]
      exact card_le_card (biUnion_subset.mpr fun B _ => filter_subset_filter _ (subset_univ B))
    have hA := hdisj_sum (fun j => x j = true)
    have hZ := hdisj_sum (fun j => (!x j) = true)
    set W := #{j | x j}
    have htot : W + #{j | !x j} = 4 * m := by
      simpa [Bool.not_eq_true] using card_filter_add_card_filter_not (s := univ) (fun j => x j = true)
    have hbound (α β c : ℕ) (hcap : α * W + β * #{j | !x j} ≤ 3 * m * (c + 1))
        (h : ∀ w' a b, w' + a = W + b →
          ¬ ((w' = 2 * m ∨ w' = 2 * m + 1) ↔ (W = 2 * m ∨ W = 2 * m + 1)) →
          c + 1 ≤ α * a + β * b) : cB.card ≤ 3 * m := by
      have := sum_le_sum fun B hB => h _ _ _ (hflip x B) (by
        have := hs B hB; rwa [Ne, Bool.eq_iff_iff, hnis, hnis] at this)
      simp only [sum_const, smul_eq_mul, sum_add_distrib, ← mul_sum] at this
      nlinarith
    by_cases h1 : W = 2 * m
    · exact hbound 2 1 1 (by omega) (by omega)
    · by_cases h2 : W = 2 * m + 1
      · exact hbound 1 2 1 (by omega) (by omega)
      · by_cases h3 : W < 2 * m
        · obtain ⟨d, hd⟩ : ∃ d, W + d + 1 = 2 * m := ⟨2 * m - W - 1, by omega⟩
          exact hbound 0 1 d (by nlinarith) (by omega)
        · obtain ⟨d, hd⟩ : ∃ d, 2 * m + d + 2 = W := ⟨W - 2 * m - 2, by omega⟩
          exact hbound 1 0 d (by nlinarith) (by omega)
  · classical
    let x : Fin (4 * m) → Bool := fun i => decide (i.1 < 2 * m)
    have hwx : #{j | x j} = 2 * m := by
      have : ({j | x j = true} : Finset _) = Iio ⟨2 * m, by omega⟩ := by
        ext j; simp [x, Fin.lt_def]
      rw [this, Fin.card_Iio]
    let B : Fin (2 * m) ⊕ Fin m → Finset (Fin (4 * m))
      | .inl k => {⟨k.1, by omega⟩}
      | .inr k => {⟨2 * m + 2 * k.1, by omega⟩, ⟨2 * m + 2 * k.1 + 1, by omega⟩}
    have hdisj : ∀ ⦃u v⦄, u ≠ v → Disjoint (B u) (B v) := by
      rintro (k | k) (l | l) huv <;>
        simp only [B, disjoint_left, mem_singleton, mem_insert, Fin.ext_iff] <;>
        intro i h1 h2 <;> (try omega) <;> exact huv (by congr 1; ext; omega)
    have hinj : Function.Injective B := fun u v h => by_contra fun huv => by
      have hd := hdisj huv; rw [h, disjoint_self, bot_eq_empty] at hd; cases v <;> simp [B] at hd
    refine le_trans ?_ (le_sup (f := blockSensitivityAt _) (mem_univ x))
    refine le_trans ?_ (le_sup (f := card) (mem_filter.mpr ⟨mem_univ (univ.image B), ?_, ?_⟩))
    · rw [card_image_of_injective _ hinj]; simp; omega
    · rintro _ hb1 _ hb2 hne
      obtain ⟨u, -, rfl⟩ := mem_image.mp hb1
      obtain ⟨v, -, rfl⟩ := mem_image.mp hb2
      exact hdisj fun h => hne (h ▸ rfl)
    · rintro _ hb
      obtain ⟨u, -, rfl⟩ := mem_image.mp hb
      have hw := hflip x (B u)
      rw [Ne, Bool.eq_iff_iff, hnis, hnis, hwx]
      suffices #{j ∈ B u | x j} = 1 ∧ #{j ∈ B u | !x j} = 0 ∨
          #{j ∈ B u | x j} = 0 ∧ #{j ∈ B u | !x j} = 2 by omega
      rcases u with k | k
      · left; simp [B, x, filter_singleton, k.2]
      · right; simp [B, x, filter_insert, filter_singleton, Fin.ext_iff,
          show 2 * m ≤ 2 * m + 2 * k.1 + 1 by omega]
