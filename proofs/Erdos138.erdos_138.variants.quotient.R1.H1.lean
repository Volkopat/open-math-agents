import OMAReductions.R_Erdos138_erdos_138_variants_quotient_R1

/-! A finite-interval consequence of Mathlib's van der Waerden theorem and Rado selection. -/

namespace OMA.W138

/-- Rado selection transfers a progression in an infinite coloring to a finite interval. -/
theorem exists_interval (k : ℕ) (_hk : 1 ≤ k) : (Erdos138.monoAP_guarantee_set 2 k).Nonempty := by
  classical
  by_contra h
  have bad (N : ℕ) : ∃ c : Finset.Icc 1 N → Fin 2, ¬ ContainsMonoAPofLength c k := by
    by_contra! hn
    exact h ⟨N, hn⟩
  choose colors avoid using bad
  let bound (T : Finset ℕ) := T.sup id + 1
  let incl (T : Finset ℕ) (x : T) : Finset.Icc 1 (bound T) :=
    ⟨x.val + 1, Finset.mem_Icc.mpr ⟨by omega, Nat.succ_le_succ (Finset.le_sup (f := id) x.property)⟩⟩
  obtain ⟨c, hc⟩ := Finset.rado_selection_subtype (β := fun _ : ℕ => Fin 2)
    (fun T x => colors (bound T) (incl T x))
  obtain ⟨d, hd, b, col, hcol⟩ := Combinatorics.exists_mono_homothetic_copy (Finset.range k) c
  let term (j : Fin k) := d * j.val + b
  let S := Finset.univ.image term
  have hs (j : Fin k) : term j ∈ S := Finset.mem_image_of_mem term (Finset.mem_univ j)
  obtain ⟨T, hST, agree⟩ := hc S
  let point (j : Fin k) := incl T ⟨term j, hST (hs j)⟩
  have point_val (j : Fin k) : (point j).val = b + 1 + j.val * d := by
    change d*j.val+b+1 = _
    ring
  apply avoid (bound T)
  refine ⟨col, Set.range point, ⟨b+1, d, ?_, ?_⟩, ?_⟩
  · have inj : Function.Injective point := by
      intro x y hxy
      have e := congrArg Subtype.val hxy
      rw [point_val, point_val, Nat.add_left_cancel_iff] at e
      exact Fin.ext (Nat.eq_of_mul_eq_mul_right hd e)
    rw [ENat.card_image_of_injective _ _ Subtype.val_injective,
      ← ENat.card_congr (Equiv.ofInjective point inj), ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  · ext x
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, by exact_mod_cast j.isLt, by simpa [nsmul_eq_mul] using (point_val j).symm⟩
    · rintro ⟨j, hj, rfl⟩
      let i : Fin k := ⟨j, by exact_mod_cast hj⟩
      exact ⟨point i, ⟨i, rfl⟩, by simpa [i, nsmul_eq_mul] using point_val i⟩
  · rintro _ ⟨i, rfl⟩
    exact (agree ⟨term i, hs i⟩).symm.trans (hcol i.val (Finset.mem_range.mpr i.isLt))

end OMA.W138

namespace OMA.W138

lemma positive_W (k : ℕ) (hk : 1 ≤ k) (hn : (Erdos138.monoAP_guarantee_set 2 k).Nonempty) :
    1 ≤ Erdos138.W k := by
  apply le_csInf hn
  intro N hN
  by_contra h
  have : N = 0 := by omega
  subst N
  obtain ⟨_, ap, hap, _⟩ := hN (fun _ => 0)
  have hempty : Subtype.val '' ap = (∅ : Set ℕ) := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro _ ⟨x, _, rfl⟩
    have hx := Finset.mem_Icc.mp x.property
    omega
  rw [hempty] at hap
  exact Set.not_isAPOfLength_empty (by exact_mod_cast (show 0 < k by omega)) hap

end OMA.W138

theorem OMA.solution : OMA.R_Erdos138_erdos_138_variants_quotient_R1.H1 := by
  intro k hk
  have hex := OMA.W138.exists_interval k hk
  exact ⟨hex, OMA.W138.positive_W k hk hex⟩
