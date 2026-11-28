import OMAReductions.R_OeisA78680_conjecture_R1_H2_R1

/-!
For 43 of the 102 coefficients, modular witnesses let Lean verify primality
of an explicit number of the form d * 2^e + 1 by Proth's theorem.
Separate the remaining coefficients from the exceptional case d = 10223,
whose published exponent is 31172165.
-/

namespace OMA.R_OeisA78680_conjecture_R1_H2_R1_H2_R1

private theorem fromCertificate {d e a : ℕ}
    (certificate : 0 < e ∧ d < 2 ^ e ∧ 65536 ≤ d * 2 ^ e ∧
      a ^ (d * 2 ^ (e - 1)) ≡ d * 2 ^ e [MOD d * 2 ^ e + 1]) :
    ∃ e : ℕ, 65536 ≤ d * 2 ^ e ∧ (d * 2 ^ e + 1).Prime := by
  obtain ⟨he, hbound, hbig, hmod⟩ := certificate
  have hd : 0 < d := by
    by_contra! hn
    have hz : d = 0 := by omega
    simp [hz] at hbig
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
  refine ⟨j + 1, hbig, OMA.ProthAudit.prime_of_mod_certificate d j a hd hbound ?_⟩
  change _ % _ = _ % _ at hmod
  have h : d * 2 ^ (j + 1) % (d * 2 ^ (j + 1) + 1) = d * 2 ^ (j + 1) :=
    Nat.mod_eq_of_lt (Nat.lt_succ_self _)
  simpa only [Nat.succ_sub_one] using hmod.trans h

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem certified :
    ∀ d ∈ [3443, 4861, 6319, 7493, 7909, 7957, 8543, 9323, 10583, 10967, 12527, 14119,
      16519, 16987, 17597, 17701, 19021, 23779, 24151, 25171, 25339, 25861, 30091, 31951,
      32393, 34565, 35987, 36781, 38029, 42257, 43429, 45737, 46159, 46403, 47179, 47911,
      51617, 52909, 56543, 57503, 63379, 64039, 65477],
      ∃ e : ℕ, 65536 ≤ d * 2 ^ e ∧ (d * 2 ^ e + 1).Prime := by
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 3443) (e := 3137) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 4861) (e := 2492) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 6319) (e := 4606) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 7493) (e := 5249) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 7909) (e := 2174) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 7957) (e := 5064) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 8543) (e := 5793) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 9323) (e := 3013) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 10583) (e := 2689) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 10967) (e := 2719) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 12527) (e := 2435) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 14119) (e := 2710) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 16519) (e := 3434) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 16987) (e := 2748) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 17597) (e := 3799) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 17701) (e := 2700) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 19021) (e := 2608) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 23779) (e := 5234) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 24151) (e := 2508) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 25171) (e := 2456) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 25339) (e := 4438) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 25861) (e := 4848) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 30091) (e := 2184) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 31951) (e := 3084) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 32393) (e := 4365) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 34565) (e := 3361) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 35987) (e := 2795) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 36781) (e := 4824) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 38029) (e := 2778) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 42257) (e := 2667) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 43429) (e := 4290) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 45737) (e := 2375) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 46159) (e := 4790) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 46403) (e := 3057) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 47179) (e := 2918) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 47911) (e := 5568) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 51617) (e := 2675) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 52909) (e := 3518) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 56543) (e := 2501) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 57503) (e := 5697) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 63379) (e := 2070) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 64039) (e := 2246) (a := 3) (by decide +kernel))
  · exact fromCertificate
      (OMA.A78680.witness_semantics (k := 65477) (e := 5887) (a := 3) (by decide +kernel))

/-- The remaining coefficients other than 10223. -/
def H1 : Prop :=
  ∀ d ∈ [383, 2897, 3061, 4037, 4847, 5297, 5359, 5897, 6977, 7013, 7651, 8423,
    13787, 14027, 16817, 18107, 18203, 19249, 20851, 21167, 21803, 25819, 27653, 27923,
    28433, 32161, 33661, 34711, 34999, 36983, 37561, 39079, 39781, 40547, 44131, 44903,
    46157, 46187, 46471, 47897, 48833, 49219, 50693, 51917, 52771, 53941, 54001, 54739,
    54767, 59569, 60443, 60541, 60829, 62093, 62761, 63017, 64007, 65057],
    ∃ e : ℕ, 65536 ≤ d * 2 ^ e ∧ (d * 2 ^ e + 1).Prime

/-- The coefficient 10223, for which the known witness has a very large exponent. -/
def H2 : Prop :=
  ∃ e : ℕ, 65536 ≤ 10223 * 2 ^ e ∧ (10223 * 2 ^ e + 1).Prime

theorem main : H1 → H2 → OMA.R_OeisA78680_conjecture_R1_H2_R1.H2 := by
  intro remaining exceptional
  let allCoefficients : List ℕ := [383, 2897, 3061, 3443, 4037, 4847, 4861, 5297, 5359, 5897, 6319, 6977,
    7013, 7493, 7651, 7909, 7957, 8423, 8543, 9323, 10223, 10583, 10967, 12527,
    13787, 14027, 14119, 16519, 16817, 16987, 17597, 17701, 18107, 18203, 19021, 19249,
    20851, 21167, 21803, 23779, 24151, 25171, 25339, 25819, 25861, 27653, 27923, 28433,
    30091, 31951, 32161, 32393, 33661, 34565, 34711, 34999, 35987, 36781, 36983, 37561,
    38029, 39079, 39781, 40547, 42257, 43429, 44131, 44903, 45737, 46157, 46159, 46187,
    46403, 46471, 47179, 47897, 47911, 48833, 49219, 50693, 51617, 51917, 52771, 52909,
    53941, 54001, 54739, 54767, 56543, 57503, 59569, 60443, 60541, 60829, 62093, 62761,
    63017, 63379, 64007, 64039, 65057, 65477]
  let checkedCoefficients : List ℕ := [3443, 4861, 6319, 7493, 7909, 7957, 8543, 9323, 10583, 10967, 12527, 14119,
    16519, 16987, 17597, 17701, 19021, 23779, 24151, 25171, 25339, 25861, 30091, 31951,
    32393, 34565, 35987, 36781, 38029, 42257, 43429, 45737, 46159, 46403, 47179, 47911,
    51617, 52909, 56543, 57503, 63379, 64039, 65477]
  let remainingCoefficients : List ℕ := [383, 2897, 3061, 4037, 4847, 5297, 5359, 5897, 6977, 7013, 7651, 8423,
    13787, 14027, 16817, 18107, 18203, 19249, 20851, 21167, 21803, 25819, 27653, 27923,
    28433, 32161, 33661, 34711, 34999, 36983, 37561, 39079, 39781, 40547, 44131, 44903,
    46157, 46187, 46471, 47897, 48833, 49219, 50693, 51917, 52771, 53941, 54001, 54739,
    54767, 59569, 60443, 60541, 60829, 62093, 62761, 63017, 64007, 65057]
  let partition := (checkedCoefficients ++ remainingCoefficients) ++ [10223]
  change ∀ d ∈ allCoefficients, ∃ e : ℕ, 65536 ≤ d * 2 ^ e ∧ (d * 2 ^ e + 1).Prime
  have partitionCheck : allCoefficients.all (fun d => partition.contains d) = true := by
    decide +kernel
  intro d hd
  have hm : d ∈ partition := List.contains_iff_mem.mp (List.all_eq_true.mp partitionCheck d hd)
  simp only [partition, List.mem_append, List.mem_singleton] at hm
  rcases hm with (h | h) | rfl
  · exact certified d h
  · exact remaining d h
  · exact exceptional

end OMA.R_OeisA78680_conjecture_R1_H2_R1_H2_R1
