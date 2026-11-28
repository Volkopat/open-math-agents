import OMAReductions.R_Erdos835_erdos_835_variants_johnson_R1

/-!
# The intersecting-block lemma for Erdős 835

Mendelsohn's Theorem on Steiner Systems, Lemma 2, uses alternating
intersection counts to show that the blocks of each derived design meet.
Here we obtain the same cancellation by centering the color indicators.
-/

-- Credit: @Alewawa

open Finset SimpleGraph
open scoped BigOperators

namespace Erdos835Intersecting

lemma lower_set_sums {α ι : Type*} [DecidableEq α] [Fintype α] [Fintype ι]
    (B : ι → Finset α) (g : ι → ℤ) (r : ℕ)
    (hcard : ∀ u, (B u).card = r)
    (hstar : ∀ T : Finset α, T.card + 1 = r →
      (∑ u, if T ⊆ B u then g u else 0) = 0) :
    ∀ T : Finset α, T.card < r → (∑ u, if T ⊆ B u then g u else 0) = 0 := by
  classical
  intro T hT
  obtain ⟨n, hn⟩ : ∃ n : ℕ, T.card + n + 1 = r := ⟨r - T.card - 1, by omega⟩
  clear hT
  induction n generalizing T with
  | zero => exact hstar T (by omega)
  | succ n ih =>
      have hzero : (∑ y ∈ Tᶜ, ∑ u, if insert y T ⊆ B u then g u else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro y hy
        apply ih (insert y T)
        rw [card_insert_of_notMem (mem_compl.mp hy)]
        omega
      rw [Finset.sum_comm] at hzero
      have hcount (u : ι) :
          (∑ y ∈ Tᶜ, if insert y T ⊆ B u then g u else 0) =
            ((r - T.card : ℕ) : ℤ) * (if T ⊆ B u then g u else 0) := by
        by_cases hsub : T ⊆ B u
        · simp only [insert_subset_iff, hsub, and_true, if_true]
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          have hset : (Tᶜ.filter fun y => y ∈ B u) = B u \ T := by
            ext y
            simp [and_comm]
          rw [hset, card_sdiff_of_subset hsub, hcard u]
        · simp [insert_subset_iff, hsub]
      simp_rw [hcount, ← Finset.mul_sum] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left (by exact_mod_cast (show r - T.card ≠ 0 by omega))

lemma sum_over_disjoint_sets {α ι : Type*} [DecidableEq α] [Fintype ι]
    (B : ι → Finset α) (g : ι → ℤ) (R : Finset α) :
    (∑ u, if Disjoint R (B u) then g u else 0) =
      ∑ T ∈ R.powerset, (-1 : ℤ) ^ T.card * (∑ u, if T ⊆ B u then g u else 0) := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hfilter : (R.powerset.filter fun T => T ⊆ B u) = (R ∩ B u).powerset := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_inter_iff]
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter, hfilter, ← Finset.sum_mul, Finset.sum_powerset_neg_one_pow_card]
  by_cases hd : Disjoint R (B u)
  · simp [hd, Finset.disjoint_iff_inter_eq_empty.mp hd]
  · simp [hd, mt Finset.disjoint_iff_inter_eq_empty.mpr hd]

lemma star_sum {k : ℕ} {x : Fin (2 * k)} (hk : 3 ≤ k)
    (c : (J(2 * k, k).induce {v | x ∈ v.val}).Coloring (Fin (k + 1)))
    (a : Fin (k + 1)) (T : Finset (Fin (2 * k))) (hT : T.card + 1 = k - 1) :
    (∑ u, if T ⊆ u.val.val.erase x then
      (if c u = a then ((k + 1 : ℕ) : ℤ) else 0) - 1 else 0) = 0 := by
  classical
  by_cases hx : x ∈ T
  · apply Finset.sum_eq_zero
    intro u _
    exact if_neg fun h => notMem_erase x _ (h hx)
  let A := insert x T
  let V := {u : {s : Finset (Fin (2 * k)) // s.card = k} // x ∈ u.val}
  let S : Finset V := Finset.univ.filter fun u => A ⊆ u.val.val
  have hA : A.card + 1 = k := by
    dsimp [A]
    rw [Finset.card_insert_of_notMem hx]
    omega
  have hselect (u : V) :
      T ⊆ u.val.val.erase x ↔ A ⊆ u.val.val := by
    simp [A, Finset.subset_erase, Finset.insert_subset_iff, hx, u.property]
  simp_rw [hselect]
  rw [← Finset.sum_filter]
  change (∑ u ∈ S, ((if c u = a then ((k + 1 : ℕ) : ℤ) else 0) - 1)) = 0
  have hinj : Set.InjOn (fun u : V => c u) (S : Set V) := by
    intro u hu v hv hcol
    by_contra hne
    have huh : A ⊆ u.val.val := (Finset.mem_filter.mp hu).2
    have hvh : A ⊆ v.val.val := (Finset.mem_filter.mp hv).2
    have hint := Finset.card_le_card (Finset.subset_inter huh hvh)
    have hne' : u.val ≠ v.val := fun h => hne (Subtype.ext h)
    have hAdj : J(2 * k, k).Adj u.val v.val := by
      apply (johnson_adj_iff_ge).2
      exact ⟨hne', by omega⟩
    exact (c.valid (v := u) (w := v) hAdj) hcol
  let extend (y : (Aᶜ : Finset (Fin (2 * k)))) : S :=
    ⟨⟨⟨insert y.val A, by rw [card_insert_of_notMem (mem_compl.mp y.property)]; omega⟩,
        Finset.mem_insert_of_mem (Finset.mem_insert_self x T)⟩,
      by exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.subset_insert _ _⟩⟩
  have hextend : Function.Injective extend := by
    intro y z h
    have hs : insert y.val A = insert z.val A := congrArg (fun u : S => u.val.val.val) h
    have hy : y.val ∈ insert z.val A := hs ▸ Finset.mem_insert_self _ _
    exact Subtype.ext ((Finset.mem_insert.mp hy).resolve_right (mem_compl.mp y.property))
  have hcount := Finset.card_le_card_of_injective hextend
  rw [Finset.card_compl, Fintype.card_fin] at hcount
  have himage : S.image (fun u : V => c u) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Fintype.card_fin]
    have hle := Finset.card_le_univ (S.image fun u : V => c u)
    rw [Finset.card_image_of_injOn hinj, Fintype.card_fin] at hle
    omega
  have hs : (∑ u ∈ S, ((if c u = a then ((k + 1 : ℕ) : ℤ) else 0) - 1)) =
      (∑ a' : Fin (k + 1), ((if a' = a then ((k + 1 : ℕ) : ℤ) else 0) - 1)) := by
    apply Finset.sum_nbij (fun u : V => c u) (by simp) hinj
    · intro a' _
      have hmem : a' ∈ S.image (fun u : V => c u) := by rw [himage]; exact Finset.mem_univ _
      exact Finset.mem_image.mp hmem
    · intros
      rfl
  rw [hs]
  simp [Finset.sum_sub_distrib]

theorem distinct_colors_at_singleton_intersection : OMA.R_Erdos835_erdos_835_variants_johnson_R1.H2 := by
  classical
  intro k x hk he c v w hi hsame
  let V := {u : {s : Finset (Fin (2 * k)) // s.card = k} // x ∈ u.val}
  let B (u : V) := u.val.val.erase x
  let g (u : V) : ℤ := (if c u = c v then ((k + 1 : ℕ) : ℤ) else 0) - 1
  have hcard (u : V) : (B u).card = k - 1 := by
    simp [B, Finset.card_erase_of_mem u.property, u.val.property]
  have hzero := lower_set_sums B g (k - 1) hcard (star_sum hk c (c v))
  have hsign : (-1 : ℤ) ^ (B v).card = -1 := by
    rw [hcard v]
    have hodd : Odd (k - 1) := by
      obtain ⟨t, ht⟩ := he
      exact ⟨t - 1, by omega⟩
    exact hodd.neg_one_pow
  have hidentity : (∑ u : V, if Disjoint (B v) (B u) then g u else 0) =
      -g v := by
    rw [sum_over_disjoint_sets]
    have hV : (B v).card = k - 1 := hcard v
    calc
      _ = (-1 : ℤ) ^ (B v).card * (∑ u : V, if B v ⊆ B u then g u else 0) := by
        apply Finset.sum_eq_single (B v)
        · intro T hT hne
          have hsub := Finset.mem_powerset.mp hT
          have hlt := Finset.card_lt_card ((Finset.ssubset_iff_subset_ne).2 ⟨hsub, hne⟩)
          rw [hzero T (by omega), mul_zero]
        · simp
      _ = -g v := by
        rw [hsign]
        have hself : (∑ u : V, if B v ⊆ B u then g u else 0) = g v := by
          calc
            _ = (if B v ⊆ B v then g v else 0) := by
              apply Finset.sum_eq_single v
              · intro u _ hne
                apply if_neg
                intro hsub
                have hEq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard u, hcard v])
                have hvu : v.val.val = u.val.val := by
                  have hx' := congrArg (insert x) hEq
                  simpa [B, Finset.insert_erase v.property, Finset.insert_erase u.property] using hx'
                exact hne (Subtype.ext (Subtype.ext hvu.symm))
              · simp
            _ = g v := by simp
        rw [hself, neg_one_mul]
  let E : Finset V := Finset.univ.filter fun u => Disjoint (B v) (B u)
  have hsum : (∑ u ∈ E, g u) = -g v := by simpa only [E, Finset.sum_filter] using hidentity
  have hw : w ∈ E := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.disjoint_left.mpr ?_⟩
    intro y hyv hyw
    have hm : y ∈ v.val.val ∩ w.val.val :=
      Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp hyv).2, (Finset.mem_erase.mp hyw).2⟩
    rw [hi, Finset.mem_singleton] at hm
    exact (Finset.mem_erase.mp hyv).1 hm
  let A := insert x (v.val.val)ᶜ
  have hA : A.card = k + 1 := by
    dsimp [A]
    rw [Finset.card_insert_of_notMem (by simpa using v.property),
      Finset.card_compl, Fintype.card_fin, v.val.property]
    omega
  have hsub (u : V) (hu : u ∈ E) : u.val.val ⊆ A := by
    have hd := (Finset.mem_filter.mp hu).2
    intro y hy
    by_cases hxy : y = x
    · exact Finset.mem_insert.mpr (Or.inl hxy)
    · refine Finset.mem_insert.mpr (Or.inr (Finset.mem_compl.mpr ?_))
      intro hyv
      exact Finset.disjoint_left.mp hd (Finset.mem_erase.mpr ⟨hxy, hyv⟩)
        (Finset.mem_erase.mpr ⟨hxy, hy⟩)
  have hinj : Set.InjOn (fun u : V => c u) (E : Set V) := by
    intro u hu z hz hcol
    by_contra hne
    have hle := Finset.card_le_card (Finset.union_subset (hsub u hu) (hsub z hz))
    have hsumcards := Finset.card_union_add_card_inter u.val.val z.val.val
    rw [u.val.property, z.val.property] at hsumcards
    have hne' : u.val ≠ z.val := fun h => hne (Subtype.ext h)
    have hAdj : J(2 * k, k).Adj u.val z.val := by
      apply (johnson_adj_iff_ge).2
      exact ⟨hne', by omega⟩
    exact (c.valid (v := u) (w := z) hAdj) hcol
  have hE := Finset.card_le_univ (E.image fun u : V => c u)
  rw [Finset.card_image_of_injOn hinj, Fintype.card_fin] at hE
  have hbound : (∑ u ∈ E.erase w, (-1 : ℤ)) ≤ ∑ u ∈ E.erase w, g u := by
    apply Finset.sum_le_sum
    intro u _
    by_cases hu : c u = c v <;> simp [g, hu]
  rw [Finset.sum_const, nsmul_eq_mul] at hbound
  have hcount := Finset.card_erase_of_mem hw
  rw [← Finset.sum_erase_add _ g hw] at hsum
  have hsv : g v = (k : ℤ) := by simp [g]
  have hsw : g w = (k : ℤ) := by simp [g, hsame.symm]
  omega

end Erdos835Intersecting

theorem OMA.solution : OMA.R_Erdos835_erdos_835_variants_johnson_R1.H2 := by
  exact Erdos835Intersecting.distinct_colors_at_singleton_intersection
