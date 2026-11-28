import OMAReductions.R_SierpinskiNumber_prime_sierpinski_problem_R1_H1_R1_H2_R1

namespace ModCertificates

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private def modularPower (m a : ℕ) : ℕ → ℕ :=
  Nat.binaryRec 1 (fun b _ x => (x * x * (if b then a else 1)) % m)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private def squareChain (m : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | t + 1, x => squareChain m t ((x * x) % m)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem cast_mod {d m : ℕ} (hd : d ∣ m) (x : ℕ) :
    ((x % m : ℕ) : ZMod d) = x := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_mod_of_dvd _ hd]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem cast_modularPower {d m : ℕ} (hd : d ∣ m) (a k : ℕ) :
    ((modularPower m a k : ℕ) : ZMod d) = (a : ZMod d) ^ k := by
  induction k using Nat.binaryRec with
  | zero => simp [modularPower]
  | bit b n ih =>
    by_cases h : n = 0 ∧ b = false
    · obtain ⟨rfl, rfl⟩ := h
      simp [modularPower]
    · rw [modularPower, Nat.binaryRec_eq b n (Or.inr (by
        intro hn
        cases b <;> simp_all)), cast_mod hd]
      push_cast
      unfold modularPower at ih
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add, mul_assoc]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem cast_squareChain {d m : ℕ} (hd : d ∣ m) (t x : ℕ) :
    ((squareChain m t x : ℕ) : ZMod d) = (x : ZMod d) ^ (2 ^ t) := by
  induction t generalizing x with
  | zero => simp [squareChain]
  | succ t ih =>
    rw [squareChain, ih, cast_mod hd, Nat.cast_mul, ← pow_two, ← pow_mul,
      pow_succ']

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_of_certificate (k t a : ℕ) (hk : 0 < k) (hsize : k < 2 ^ (t + 1))
    (hc : let m := k * 2 ^ (t + 1) + 1
          squareChain m t (modularPower m a k) + 1 = m) :
    (k * 2 ^ (t + 1) + 1).Prime := by
  let m := k * 2 ^ (t + 1) + 1
  change m.Prime
  change squareChain m t (modularPower m a k) + 1 = m at hc
  have hm : 0 < m := by dsimp [m]; omega
  have hm' : 1 < m := by
    dsimp [m]
    have hpos : 0 < k * 2 ^ (t + 1) := by positivity
    omega
  by_contra hn
  let d := m.minFac
  have hd : d.Prime := Nat.minFac_prime hm'.ne'
  have hdm : d ∣ m := Nat.minFac_dvd m
  have hmOdd : m % 2 = 1 := by
    dsimp [m]
    rw [pow_succ, ← Nat.mul_assoc]
    omega
  have hd2 : 2 < d := by
    refine lt_of_le_of_ne hd.two_le ?_
    intro h
    have h2m : 2 ∣ m := h ▸ hdm
    simp [Nat.dvd_iff_mod_eq_zero, hmOdd] at h2m
  let : Fact d.Prime := ⟨hd⟩
  let : Fact (2 < d) := ⟨hd2⟩
  let x : ZMod d := (a : ZMod d) ^ k
  have hneg : x ^ (2 ^ t) = -1 := by
    have h := congrArg (fun j : ℕ => (j : ZMod d)) hc
    push_cast at h
    rw [cast_squareChain hdm, cast_modularPower hdm,
      (ZMod.natCast_eq_zero_iff _ _).mpr hdm] at h
    exact eq_neg_of_add_eq_zero_left h
  have hx : x ^ (2 ^ (t + 1)) = 1 := by
    rw [pow_succ, pow_mul, hneg]
    norm_num
  have hx0 : x ≠ 0 := by
    rintro h
    simp [h] at hx
  have ho : orderOf x = 2 ^ (t + 1) := by
    apply orderOf_eq_of_pow_and_pow_div_prime (by positivity) hx
    intro p hp hpd
    have hp2 : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd)
    subst p
    rw [pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2), hneg]
    exact ZMod.neg_one_ne_one
  have hle : 2 ^ (t + 1) ≤ d - 1 :=
    Nat.le_of_dvd (by omega) (ho ▸ ZMod.orderOf_dvd_card_sub_one hx0)
  have hs := Nat.minFac_sq_le_self hm hn
  change d ^ 2 ≤ m at hs
  have hstrict : m < d ^ 2 := by
    have hb : (2 ^ (t + 1) : ℕ) + 1 ≤ d := by omega
    have hsquare := Nat.mul_le_mul hb hb
    have hkbound : k * 2 ^ (t + 1) ≤ 2 ^ (t + 1) * 2 ^ (t + 1) :=
      Nat.mul_le_mul_right _ hsize.le
    dsimp [m]
    nlinarith
  omega



set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_383 : (383 * 2 ^ 6393 + 1).Prime := by
  apply prime_of_certificate 383 6392 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_8543 : (8543 * 2 ^ 5793 + 1).Prime := by
  apply prime_of_certificate 8543 5792 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_25339 : (25339 * 2 ^ 4438 + 1).Prime := by
  apply prime_of_certificate 25339 4437 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_36781 : (36781 * 2 ^ 4824 + 1).Prime := by
  apply prime_of_certificate 36781 4823 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_47911 : (47911 * 2 ^ 5568 + 1).Prime := by
  apply prime_of_certificate 47911 5567 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_57503 : (57503 * 2 ^ 5697 + 1).Prime := by
  apply prime_of_certificate 57503 5696 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_73189 : (73189 * 2 ^ 4278 + 1).Prime := by
  apply prime_of_certificate 73189 4277 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_74959 : (74959 * 2 ^ 4274 + 1).Prime := by
  apply prime_of_certificate 74959 4273 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_77267 : (77267 * 2 ^ 4159 + 1).Prime := by
  apply prime_of_certificate 77267 4158 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_81919 : (81919 * 2 ^ 5602 + 1).Prime := by
  apply prime_of_certificate 81919 5601 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_82549 : (82549 * 2 ^ 7530 + 1).Prime := by
  apply prime_of_certificate 82549 7529 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_92119 : (92119 * 2 ^ 4882 + 1).Prime := by
  apply prime_of_certificate 92119 4881 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_92567 : (92567 * 2 ^ 5063 + 1).Prime := by
  apply prime_of_certificate 92567 5062 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_101183 : (101183 * 2 ^ 5229 + 1).Prime := by
  apply prime_of_certificate 101183 5228 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_117361 : (117361 * 2 ^ 5392 + 1).Prime := by
  apply prime_of_certificate 117361 5391 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_122041 : (122041 * 2 ^ 6312 + 1).Prime := by
  apply prime_of_certificate 122041 6311 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_127819 : (127819 * 2 ^ 5266 + 1).Prime := by
  apply prime_of_certificate 127819 5265 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_132257 : (132257 * 2 ^ 5891 + 1).Prime := by
  apply prime_of_certificate 132257 5890 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_152809 : (152809 * 2 ^ 5978 + 1).Prime := by
  apply prime_of_certificate 152809 5977 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_158611 : (158611 * 2 ^ 4888 + 1).Prime := by
  apply prime_of_certificate 158611 4887 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_165721 : (165721 * 2 ^ 4104 + 1).Prime := by
  apply prime_of_certificate 165721 4103 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_175727 : (175727 * 2 ^ 6083 + 1).Prime := by
  apply prime_of_certificate 175727 6082 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_183473 : (183473 * 2 ^ 6825 + 1).Prime := by
  apply prime_of_certificate 183473 6824 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_185149 : (185149 * 2 ^ 4570 + 1).Prime := by
  apply prime_of_certificate 185149 4569 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_197117 : (197117 * 2 ^ 6679 + 1).Prime := by
  apply prime_of_certificate 197117 6678 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_219301 : (219301 * 2 ^ 4128 + 1).Prime := by
  apply prime_of_certificate 219301 4127 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_236641 : (236641 * 2 ^ 7552 + 1).Prime := by
  apply prime_of_certificate 236641 7551 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_239251 : (239251 * 2 ^ 4264 + 1).Prime := by
  apply prime_of_certificate 239251 4263 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_246167 : (246167 * 2 ^ 8011 + 1).Prime := by
  apply prime_of_certificate 246167 8010 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_248783 : (248783 * 2 ^ 4269 + 1).Prime := by
  apply prime_of_certificate 248783 4268 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_250501 : (250501 * 2 ^ 5504 + 1).Prime := by
  apply prime_of_certificate 250501 5503 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_251179 : (251179 * 2 ^ 6294 + 1).Prime := by
  apply prime_of_certificate 251179 6293 3 (by decide) (by decide)
  decide +kernel

end ModCertificates

open ModCertificates

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
theorem OMA.solution : OMA.R_SierpinskiNumber_prime_sierpinski_problem_R1_H1_R1_H2_R1.H2 := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact ⟨6393, by decide, prime_383⟩
  · exact ⟨5793, by decide, prime_8543⟩
  · exact ⟨4438, by decide, prime_25339⟩
  · exact ⟨4824, by decide, prime_36781⟩
  · exact ⟨5568, by decide, prime_47911⟩
  · exact ⟨5697, by decide, prime_57503⟩
  · exact ⟨4278, by decide, prime_73189⟩
  · exact ⟨4274, by decide, prime_74959⟩
  · exact ⟨4159, by decide, prime_77267⟩
  · exact ⟨5602, by decide, prime_81919⟩
  · exact ⟨7530, by decide, prime_82549⟩
  · exact ⟨4882, by decide, prime_92119⟩
  · exact ⟨5063, by decide, prime_92567⟩
  · exact ⟨5229, by decide, prime_101183⟩
  · exact ⟨5392, by decide, prime_117361⟩
  · exact ⟨6312, by decide, prime_122041⟩
  · exact ⟨5266, by decide, prime_127819⟩
  · exact ⟨5891, by decide, prime_132257⟩
  · exact ⟨5978, by decide, prime_152809⟩
  · exact ⟨4888, by decide, prime_158611⟩
  · exact ⟨4104, by decide, prime_165721⟩
  · exact ⟨6083, by decide, prime_175727⟩
  · exact ⟨6825, by decide, prime_183473⟩
  · exact ⟨4570, by decide, prime_185149⟩
  · exact ⟨6679, by decide, prime_197117⟩
  · exact ⟨4128, by decide, prime_219301⟩
  · exact ⟨7552, by decide, prime_236641⟩
  · exact ⟨4264, by decide, prime_239251⟩
  · exact ⟨8011, by decide, prime_246167⟩
  · exact ⟨4269, by decide, prime_248783⟩
  · exact ⟨5504, by decide, prime_250501⟩
  · exact ⟨6294, by decide, prime_251179⟩