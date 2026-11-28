import FormalConjectures.Wikipedia.EswarathasanLevineConjecture

/-!
# Shorter proof of `EswarathasanLevineConjecture.harmonicNumDivisibleSet_two_empty`
-/

theorem OMA.solution : type_of% @EswarathasanLevineConjecture.harmonicNumDivisibleSet_two_empty := by
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  rintro n ⟨hn, hdvd⟩
  have h := padicValRat_two_harmonic n
  have h2 := Int.natCast_dvd.mp hdvd
  have h1 : 1 ≤ padicValNat 2 (harmonic n).num.natAbs :=
    one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr (harmonic_pos (by omega)).ne')) h2
  have h0 : padicValNat 2 (harmonic n).den = 0 := padicValNat.eq_zero_of_not_dvd fun hd =>
    Nat.not_coprime_of_dvd_of_dvd (by decide) h2 hd (harmonic n).reduced
  rw [padicValRat, padicValInt, h0] at h
  omega
