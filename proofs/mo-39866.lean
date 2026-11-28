import OMAStatements.S_mo_39866
import Mathlib

-- Problem: mo-39866, a Noetherian local ring whose maximal ideal is principal is a principal
-- ideal ring.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- The final unit-multiple membership step uses Ideal.mul_unit_mem_iff_mem.
-- Let m = (t). By Krull's intersection theorem the powers of m intersect in 0, so a nonzero
-- ideal I has a largest k with I <= m^k = (t^k). Pick x in I outside m^(k+1); then x = t^k u
-- with u not in m, so u is a unit and t^k lies in I. Hence I = (t^k).

theorem OMA.solution : type_of% @OMA.S_mo_39866.main := by
  intro R _ _ _ hprin
  obtain ⟨⟨t, ht⟩⟩ := hprin
  have hm : IsLocalRing.maximalIdeal R = Ideal.span {t} := ht
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · subst hI
    exact bot_isPrincipal
  have hex : ∃ n : ℕ, ¬ I ≤ IsLocalRing.maximalIdeal R ^ n := by
    by_contra hcon
    apply hI
    rw [eq_bot_iff, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top]
    exact le_iInf fun n => not_not.mp fun hn => hcon ⟨n, hn⟩
  classical
  have hn0 : ¬ I ≤ IsLocalRing.maximalIdeal R ^ Nat.find hex := Nat.find_spec hex
  have hn0pos : Nat.find hex ≠ 0 := by
    intro h0
    apply hn0
    rw [h0, pow_zero, Ideal.one_eq_top]
    exact le_top
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0pos
  have hIk : I ≤ IsLocalRing.maximalIdeal R ^ k := by
    by_contra hcon
    exact Nat.find_min hex (by omega : k < Nat.find hex) hcon
  rw [hk] at hn0
  obtain ⟨x, hxI, hxn⟩ := SetLike.not_le_iff_exists.mp hn0
  have hIk' : I ≤ Ideal.span {t ^ k} := by
    rw [hm, Ideal.span_singleton_pow] at hIk
    exact hIk
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp (hIk' hxI)
  have hunit : IsUnit u := by
    by_contra hnu
    have hum : u ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal u).mpr hnu
    apply hxn
    rw [hu, Nat.succ_eq_add_one, pow_succ]
    refine Ideal.mul_mem_mul ?_ hum
    rw [hm, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  refine ⟨⟨t ^ k, ?_⟩⟩
  show I = Ideal.span {t ^ k}
  apply le_antisymm hIk'
  rw [Ideal.span_singleton_le_iff_mem]
  exact (I.mul_unit_mem_iff_mem hunit).mp (hu ▸ hxI)
