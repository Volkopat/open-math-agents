import OMAReductions.R_CasasAlvero_casas_alvero_conjecture_R1
import Mathlib

open Polynomial

-- The unique possible nonzero root contributes its multiplicity times its value.
-- The zero root sum therefore rules it out in characteristic zero.
theorem OMA.solution : OMA.R_CasasAlvero_casas_alvero_conjecture_R1.H2 := by
  intro K _ _ Q hm hs hnext hroots
  classical
  have hz : ∀ r ∈ Q.roots, r = 0 := by
    intro r hr
    by_contra hne
    have he := Q.roots.sum_eq_nsmul_single r (fun x hxr hx => by
      by_contra hx0
      exact hxr (hroots x hx r hr hx0 hne))
    have hc : (Q.roots.count r : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Multiset.count_ne_zero.mpr hr)
    have heq := hs.nextCoeff_eq_neg_sum_roots_of_monic hm
    rw [hnext, he, nsmul_eq_mul] at heq
    exact hne ((mul_eq_zero.mp (neg_eq_zero.mp heq.symm)).resolve_left hc)
  rw [hs.eq_prod_roots_of_monic hm, Multiset.eq_replicate_card.mpr hz]
  simp
