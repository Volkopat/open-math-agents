import OMAStatements.S_arxiv_2610_34808
import Mathlib

namespace OMAProof2610

open OMA.S_arxiv_2610_34808

theorem tot_dvd {p m : ℕ} (hp : p.Prime) (h : p ∣ m) : (p * m).totient = p * m.totient :=
  Nat.totient_mul_of_prime_of_dvd hp h

theorem tot_ndvd {p m : ℕ} (hp : p.Prime) (h : ¬ p ∣ m) :
    (p * m).totient = (p - 1) * m.totient := by
  rw [Nat.totient_mul ((Nat.Prime.coprime_iff_not_dvd hp).2 h), Nat.totient_prime hp]

theorem sound {q : ℕ} (hq : q.Prime) {u v m : ℕ} (h : Generated q u v m) :
    m.totient = 2^u * q^v := by
  induction h with
  | one => simp
  | newPrime p hp form fresh old ih =>
    rw [tot_ndvd hp fresh, ih, form]; simp only [Nat.add_sub_cancel]; ring
  | moreTwo already old ih =>
    rw [tot_dvd Nat.prime_two already, ih]; ring
  | moreQ already old ih =>
    rw [tot_dvd hq already, ih]; ring

theorem dvd_form {q u v d : ℕ} (hq : q.Prime) (h : d ∣ 2^u * q^v) :
    ∃ a ≤ u, ∃ b ≤ v, d = 2^a * q^b := by
  obtain ⟨d1, d2, h1, h2, rfl⟩ := Nat.dvd_mul.mp h
  obtain ⟨a, ha, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  obtain ⟨b, hb, rfl⟩ := (Nat.dvd_prime_pow hq).mp h2
  exact ⟨a, ha, b, hb, rfl⟩

theorem prime_dvd_form {q u v p : ℕ} (hq : q.Prime) (hp : p.Prime) (h : p ∣ 2^u * q^v) :
    p = 2 ∨ p = q := by
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · left; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
  · right; exact (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h)

theorem odd_of_prime {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) : ¬ 2 ∣ q := by
  intro h
  exact h2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h).symm

theorem complete {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) :
    ∀ n u v : ℕ, n.totient = 2^u * q^v → Generated q u v n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro u v hn
  have hq1 : 1 < q := hq.one_lt
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · interval_cases n
    · simp at hn; have : 0 < 2^u * q^v := by positivity
      omega
    · simp only [Nat.totient_one] at hn
      have hu : u = 0 := by
        by_contra hu
        have : 2 ∣ 2^u * q^v := Dvd.dvd.mul_right (dvd_pow_self 2 hu) _
        rw [← hn] at this; omega
      have hv : v = 0 := by
        by_contra hv
        have : q ∣ 2^u * q^v := Dvd.dvd.mul_left (dvd_pow_self q hv) _
        rw [← hn] at this; exact absurd (Nat.le_of_dvd one_pos this) (by omega)
      subst hu hv; exact Generated.one
  · set p := n.minFac with hpdef
    have hp : p.Prime := Nat.minFac_prime (by omega)
    obtain ⟨m, hm⟩ : p ∣ n := Nat.minFac_dvd n
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp at hm; omega
      · exact h
    have hmn : m < n := by
      rw [hm]; have := hp.two_le; nlinarith
    by_cases hpm : p ∣ m
    · have ht : n.totient = p * m.totient := by rw [hm]; exact tot_dvd hp hpm
      have hpd : p ∣ 2^u * q^v := by rw [← hn, ht]; exact dvd_mul_right _ _
      rcases prime_dvd_form hq hp hpd with hp2 | hpq
      · have hu : u ≠ 0 := by
          rintro rfl
          rw [hp2] at hpd; simp at hpd
          exact odd_of_prime hq h2 (Nat.prime_two.dvd_of_dvd_pow hpd)
        have hmt : m.totient = 2^(u-1) * q^v := by
          have : 2 * m.totient = 2 * (2^(u-1) * q^v) := by
            rw [← hp2, ← ht, hn, hp2, ← mul_assoc, ← pow_succ']
            congr 2; omega
          omega
        have := Generated.moreTwo (hp2 ▸ hpm) (ih m hmn _ _ hmt)
        rw [Nat.sub_add_cancel (by omega), ← hp2, ← hm] at this
        exact this
      · have hv : v ≠ 0 := by
          rintro rfl
          rw [hpq] at hpd; simp at hpd
          exact h2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hpd))
        have hmt : m.totient = 2^u * q^(v-1) := by
          have : q * m.totient = q * (2^u * q^(v-1)) := by
            rw [← hpq, ← ht, hn, hpq]
            rw [show 2 ^ u * q ^ v = q * (2^u * q^(v-1)) by
              rw [show v = (v - 1) + 1 by omega, pow_succ]; simp only [Nat.add_sub_cancel]; ring]
          exact Nat.eq_of_mul_eq_mul_left (by omega) this
        have := Generated.moreQ (hpq ▸ hpm) (ih m hmn _ _ hmt)
        rw [Nat.sub_add_cancel (by omega), show q * m = n by rw [hm, hpq]] at this
        exact this
    · have ht : n.totient = (p - 1) * m.totient := by rw [hm]; exact tot_ndvd hp hpm
      have hpd : p - 1 ∣ 2^u * q^v := by rw [← hn, ht]; exact dvd_mul_right _ _
      obtain ⟨a, ha, b, hb, hab⟩ := dvd_form hq hpd
      have hmt : m.totient = 2^(u-a) * q^(v-b) := by
        have e : 2^u * q^v = (2^a * q^b) * (2^(u-a) * q^(v-b)) := by
          rw [show 2^u = 2^a * 2^(u-a) by rw [← pow_add]; congr 1; omega,
            show q^v = q^b * q^(v-b) by rw [← pow_add]; congr 1; omega]
          ring
        have : (2^a * q^b) * m.totient = (2^a * q^b) * (2^(u-a) * q^(v-b)) := by
          rw [← e, ← hn, ht, hab]
        exact Nat.eq_of_mul_eq_mul_left (by positivity) this
      have := Generated.newPrime p hp (by rw [← hab]; have := hp.two_le; omega) hpm
        (ih m hmn _ _ hmt)
      rw [Nat.add_sub_cancel' ha, Nat.add_sub_cancel' hb, ← hm] at this
      exact this

theorem cover_check : ∀ c < 36, ∃ p ∈ [3, 5, 7, 13, 19, 37, 73], p ∣ 2^c * 420381167 + 1 := by
  decide

theorem not_prime_cover {q : ℕ} (hq : q % 560403480 = 420381167) (a : ℕ) :
    ¬ (2^a * q + 1).Prime := by
  have hL : q ≡ 420381167 [MOD 70050435] := by
    unfold Nat.ModEq
    rw [← Nat.mod_mod_of_dvd q (show 70050435 ∣ 560403480 by norm_num), hq]
  have h36 : 2^36 ≡ 1 [MOD 70050435] := by
    unfold Nat.ModEq; norm_num
  have hpow : 2^a ≡ 2^(a%36) [MOD 70050435] := by
    have := (h36.pow (a/36)).mul_right (2^(a%36))
    rw [one_pow, one_mul, ← pow_mul, ← pow_add, Nat.div_add_mod] at this
    exact this
  have key : 2^a * q + 1 ≡ 2^(a%36) * 420381167 + 1 [MOD 70050435] :=
    (hpow.mul hL).add_right 1
  obtain ⟨p, hpP, hpd⟩ := cover_check (a%36) (Nat.mod_lt _ (by norm_num))
  have hpL : p ∣ 70050435 ∧ 2 ≤ p ∧ p ≤ 73 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpP
    rcases hpP with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  have hd := (key.dvd_iff hpL.1).mpr hpd
  have hqr : 420381167 ≤ q := by rw [← hq]; exact Nat.mod_le _ _
  have : q ≤ 2^a * q := Nat.le_mul_of_pos_left _ (by positivity)
  exact Nat.not_prime_of_dvd_of_lt hd hpL.2.1 (by omega)

theorem mod8 {q : ℕ} (hq : q % 560403480 = 420381167) : q % 8 = 7 := by
  rw [← Nat.mod_mod_of_dvd q (show 8 ∣ 560403480 by norm_num), hq]

theorem ne_fermat {q : ℕ} (hq : q % 560403480 = 420381167) (a : ℕ) : q ≠ 2^a + 1 := by
  have h8 := mod8 hq
  rintro rfl
  rcases a with _|_|_|a
  · norm_num at h8
  · norm_num at h8
  · norm_num at h8
  · rw [pow_succ, pow_succ, pow_succ] at h8; omega

theorem inv3 {q : ℕ} (hq : q.Prime) (hM : q % 560403480 = 420381167) {u v m : ℕ}
    (h : Generated q u v m) : v ≤ 1 → v = 0 ∧ ¬ q ∣ m := by
  have hqr : 420381167 ≤ q := by rw [← hM]; exact Nat.mod_le _ _
  induction h with
  | one => intro _; exact ⟨rfl, hq.not_dvd_one⟩
  | @newPrime m u v a b p hp form fresh old ih =>
    intro hv
    obtain ⟨hv0, hqm⟩ := ih (by omega)
    rcases Nat.lt_or_ge b 1 with hb | hb
    · have hb0 : b = 0 := by omega
      subst hb0
      refine ⟨by omega, fun hd => ?_⟩
      rcases (Nat.Prime.dvd_mul hq).mp hd with h1 | h1
      · have := (Nat.prime_dvd_prime_iff_eq hq hp).mp h1
        rw [form, pow_zero, mul_one] at this
        exact ne_fermat hM a this
      · exact hqm h1
    · have hb1 : b = 1 := by omega
      subst hb1
      rw [pow_one] at form
      exact absurd (form ▸ hp) (not_prime_cover hM a)
  | moreTwo already old ih =>
    intro hv
    obtain ⟨hv0, hqm⟩ := ih hv
    refine ⟨hv0, fun hd => ?_⟩
    rcases (Nat.Prime.dvd_mul hq).mp hd with h1 | h1
    · have := Nat.le_of_dvd (by norm_num) h1; omega
    · exact hqm h1
  | moreQ already old ih =>
    intro hv
    exact absurd already (ih (by omega)).2

theorem part2 : {q : ℕ | q.Prime ∧ q % 560403480 = 420381167}.Infinite := by
  refine (Nat.infinite_setOfPred_prime_and_modEq (q := 560403480) (a := 420381167)
    (by norm_num) (by decide)).mono ?_
  intro p hp
  exact ⟨hp.1, hp.2⟩

theorem nd {p a b : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) : ¬ p ∣ a * b := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact ha h
  · exact hb h

theorem dv {p a b : ℕ} (hp : p.Prime) (h : p ∣ a * b) (ha : ¬ p ∣ a) : p ∣ b := by
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact absurd h ha
  · exact h

theorem three_ndvd_pow (s : ℕ) : ¬ 3 ∣ 2^s := fun h => by
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h; omega

theorem ne_zero_of_tot {n h q : ℕ} (hq : q.Prime) (hn : n.totient = 2^h * q) : n ≠ 0 := by
  rintro rfl
  rw [Nat.totient_zero] at hn
  have := Nat.mul_pos (pow_pos two_pos h) hq.pos
  omega

theorem other_preimage {q : ℕ} (hq : q.Prime) {s n : ℕ} (hn : n.totient = 2^s * q) :
    ∃ m : ℕ, m ≠ n ∧ m.totient = n.totient := by
  have n0 := ne_zero_of_tot hq hn
  by_cases e1 : 2 ∣ n
  · obtain ⟨n1, rfl⟩ := e1
    by_cases e2 : 2 ∣ n1
    · by_cases e3 : 3 ∣ n1
      · obtain ⟨n2, rfl⟩ := e3
        have e2' : 2 ∣ n2 := dv Nat.prime_two e2 (by norm_num)
        by_cases e4 : 3 ∣ n2
        · obtain ⟨n3, rfl⟩ := e4
          have e2'' : 2 ∣ n3 := dv Nat.prime_two e2' (by norm_num)
          have hA : (2 * (3 * (3 * n3))).totient = 3 * (2 * (3 * n3)).totient := by
            rw [show 2 * (3 * (3 * n3)) = 3 * (2 * (3 * n3)) by ring]
            exact tot_dvd Nat.prime_three ⟨2 * n3, by ring⟩
          have h3d : 3 ∣ 2^s * q^1 := by rw [pow_one, ← hn, hA]; exact dvd_mul_right _ _
          have hq3 : q = 3 := by
            rcases prime_dvd_form hq Nat.prime_three h3d with h | h
            · omega
            · exact h.symm
          subst hq3
          have hB : (2 * (3 * n3)).totient = 2^s := by omega
          have e5 : ¬ 3 ∣ n3 := by
            intro h
            have := tot_dvd Nat.prime_three (dvd_mul_of_dvd_right h 2)
            rw [show 3 * (2 * n3) = 2 * (3 * n3) by ring, hB] at this
            exact three_ndvd_pow s ⟨_, this⟩
          have e5' : ¬ 3 ∣ 2 * n3 := nd Nat.prime_three (by norm_num) e5
          have hC : (2 * (3 * n3)).totient = 4 * n3.totient := by
            rw [show 2 * (3 * n3) = 3 * (2 * n3) by ring, tot_ndvd Nat.prime_three e5',
              tot_dvd Nat.prime_two e2'']
            ring
          have e6 : ¬ 7 ∣ n3 := by
            intro h
            have h7 := Nat.totient_dvd_of_dvd h
            rw [Nat.totient_prime (by norm_num)] at h7
            have : 3 ∣ 2^s := by
              rw [← hB, hC]; exact Dvd.dvd.mul_left ((show 3 ∣ 6 by norm_num).trans h7) _
            exact three_ndvd_pow s this
          refine ⟨7 * (2 * n3), by omega, ?_⟩
          rw [tot_ndvd (by norm_num) (nd (by norm_num) (by norm_num) e6), hA, hC,
            tot_dvd Nat.prime_two e2'']
          ring
        · have e4' : ¬ 3 ∣ 2 * n2 := nd Nat.prime_three (by norm_num) e4
          refine ⟨2 * (2 * n2), by omega, ?_⟩
          rw [tot_dvd Nat.prime_two (dvd_mul_right 2 n2),
            show 2 * (3 * n2) = 3 * (2 * n2) by ring, tot_ndvd Nat.prime_three e4']
      · refine ⟨3 * n1, by omega, ?_⟩
        rw [tot_ndvd Nat.prime_three e3, tot_dvd Nat.prime_two e2]
    · refine ⟨n1, by omega, ?_⟩
      rw [tot_ndvd Nat.prime_two e2]; simp
  · refine ⟨2 * n, by omega, ?_⟩
    rw [tot_ndvd Nat.prime_two e1]; simp

theorem form_of_mul {q h c X : ℕ} (hq : q.Prime) (h2 : q ≠ 2) (e : 2^c * X = 2^h * q) :
    ∃ h', X = 2^h' * q := by
  have hX : X ∣ 2^h * q^1 := ⟨2^c, by rw [pow_one, ← e]; ring⟩
  obtain ⟨a, -, b, hb, rfl⟩ := dvd_form hq hX
  rcases Nat.lt_or_ge b 1 with hb0 | hb1
  · have : b = 0 := by omega
    subst this
    have hqd : q ∣ 2^(c+a) := ⟨2^h, by rw [pow_add, pow_zero, mul_one] at *; rw [e]; ring⟩
    exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
      (hq.dvd_of_dvd_pow hqd)) h2
  · have : b = 1 := by omega
    subst this
    exact ⟨a, by rw [pow_one]⟩

theorem sq_eq_q {q p N h : ℕ} (hq : q.Prime) (hp : p.Prime) (hp2 : p ≠ 2) (hd : p * p ∣ N)
    (hN : N.totient = 2^h * q) : p = q := by
  have h1 := Nat.totient_dvd_of_dvd hd
  rw [tot_dvd hp dvd_rfl, hN] at h1
  have : p ∣ 2^h * q^1 := by rw [pow_one]; exact (dvd_mul_right p _).trans h1
  rcases prime_dvd_form hq hp this with h | h
  · exact absurd h hp2
  · exact h

theorem strip {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) {p c : ℕ} (hp : p.Prime) (hc : p - 1 = 2^c)
    (hp2 : p ≠ 2) {N h : ℕ} (hN2 : 2 ∣ N) (hφ : N.totient = 2^h * q) (hsq : ¬ p * p ∣ N) :
    ∃ A h', A ∣ N ∧ 2 ∣ A ∧ ¬ p ∣ A ∧ A.totient = 2^h' * q := by
  by_cases hd : p ∣ N
  · obtain ⟨A, rfl⟩ := hd
    have hpA : ¬ p ∣ A := fun h' => hsq (mul_dvd_mul_left p h')
    have h2A : 2 ∣ A := dv Nat.prime_two hN2 (odd_of_prime hp hp2)
    rw [tot_ndvd hp hpA, hc] at hφ
    obtain ⟨h', e⟩ := form_of_mul hq h2 hφ
    exact ⟨A, h', dvd_mul_left A p, h2A, hpA, e⟩
  · exact ⟨N, h, dvd_rfl, hN2, hd, hφ⟩

theorem three_preimages {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) {s n : ℕ}
    (hn : n.totient = 2^s * q) : ∃ t ≥ 3, ∃ x y z : ℕ,
      x < y ∧ y < z ∧ x.totient = 2^t * q ∧ y.totient = 2^t * q ∧ z.totient = 2^t * q := by
  obtain ⟨h0, hN⟩ : ∃ h0, (2 * n).totient = 2^h0 * q := by
    by_cases e : 2 ∣ n
    · exact ⟨s + 1, by rw [tot_dvd Nat.prime_two e, hn]; ring⟩
    · exact ⟨s, by rw [tot_ndvd Nat.prime_two e, hn]; simp⟩
  by_cases h9 : 3 * 3 ∣ 2 * n
  · have := sq_eq_q hq Nat.prime_three (by norm_num) h9 hN
    subst this
    exact ⟨3, le_rfl, 35, 39, 45, by norm_num, by norm_num, by decide, by decide, by decide⟩
  by_cases h25 : 5 * 5 ∣ 2 * n
  · have := sq_eq_q hq (by norm_num : Nat.Prime 5) (by norm_num) h25 hN
    subst this
    exact ⟨3, le_rfl, 41, 55, 75, by norm_num, by norm_num, by decide, by decide, by decide⟩
  obtain ⟨N1, h1, hN1d, hN12, hN15, hN1φ⟩ := strip hq h2 (p := 5) (c := 2) (by norm_num)
    (by norm_num) (by norm_num) (dvd_mul_right 2 n) hN h25
  have h9' : ¬ 3 * 3 ∣ N1 := fun h => h9 (h.trans hN1d)
  obtain ⟨A, h', hAd, hA2, hA3, hAφ⟩ := strip hq h2 (p := 3) (c := 1) Nat.prime_three
    (by norm_num) (by norm_num) hN12 hN1φ h9'
  have hA5 : ¬ 5 ∣ A := fun h => hN15 (h.trans hAd)
  have hA0 := ne_zero_of_tot hq hAφ
  refine ⟨h' + 3, by omega, 8 * A, 10 * A, 12 * A, by omega, by omega, ?_, ?_, ?_⟩
  · rw [show 8 * A = 2 * (2 * (2 * A)) by ring, tot_dvd Nat.prime_two (dvd_mul_right 2 _),
      tot_dvd Nat.prime_two (dvd_mul_right 2 _), tot_dvd Nat.prime_two hA2, hAφ]
    ring
  · rw [show 10 * A = 5 * (2 * A) by ring,
      tot_ndvd (by norm_num) (nd (by norm_num) (by norm_num) hA5),
      tot_dvd Nat.prime_two hA2, hAφ]
    ring
  · rw [show 12 * A = 3 * (2 * (2 * A)) by ring,
      tot_ndvd Nat.prime_three (nd Nat.prime_three (by norm_num)
        (nd Nat.prime_three (by norm_num) hA3)),
      tot_dvd Nat.prime_two (dvd_mul_right 2 _), tot_dvd Nat.prime_two hA2, hAφ]
    ring

end OMAProof2610

open OMAProof2610 in
theorem OMA.solution : type_of% @OMA.S_arxiv_2610_34808.main := by
  refine ⟨?_, part2, ?_⟩
  · intro q hq h2 s _
    refine ⟨fun n => ⟨fun hn => ?_, fun hg => ?_⟩, fun n hn => other_preimage hq hn,
      fun n hn => three_preimages hq h2 hn⟩
    · exact complete hq h2 n s 1 (by rw [hn, pow_one])
    · rw [sound hq hg, pow_one]
  · intro q hq hM s _ n hn
    have hg := complete hq (by have := mod8 hM; omega) n s 1 (by rw [hn, pow_one])
    have := (inv3 hq hM hg le_rfl).1
    omega
