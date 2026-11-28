import OMAStatements.S_oeis_a005408
import Mathlib

/-!
# A005408: primes with one coach and the first q odd integers

Working in `ZMod p`, the condition `2^m = 1 or -1` is `4^m = 1`, so `sord2 p` is the order of 4.
A coach step sends `a` to `c` with `2^v * c = p - a`, so every element `t` of the top row
satisfies `4^m * t^2 = 1` for some `m`, and conversely every such residue is reached.
Counting squares of `1..(p-1)/2` against powers of 4 gives both directions; for composite `p`
the least prime factor lies among the first q odd integers but is not coprime to `p`.
-/

namespace OMA.A005408

open OMA.S_oeis_a005408

theorem topRow_induction (p : ℕ) (P : ℕ → Prop) (h1 : P 1)
    (hs : ∀ a, P a → P (coachF p a)) : ∀ a ∈ topRow p, P a := by
  rintro a ⟨k, rfl⟩
  induction k with
  | zero => simpa using h1
  | succ k ih => rw [Function.iterate_succ_apply']; exact hs _ ih

theorem topRow_step (p t : ℕ) (h : t ∈ topRow p) : coachF p t ∈ topRow p := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k + 1, by rw [Function.iterate_succ_apply']⟩

theorem coach_spec (p a : ℕ) (hp : Odd p) (ha : Odd a) (hap : a < p) :
    ∃ w : ℕ, 2 ^ (1 + w) * coachF p a = p - a ∧ Odd (coachF p a) ∧ 2 * coachF p a < p := by
  have hne : p - a ≠ 0 := by omega
  have h2 : 2 ∣ p - a := by
    obtain ⟨x, hx⟩ := hp
    obtain ⟨y, hy⟩ := ha
    omega
  have hv : 1 ≤ padicValNat 2 (p - a) := one_le_padicValNat_of_dvd hne h2
  have hmul : 2 ^ padicValNat 2 (p - a) * coachF p a = p - a := by
    unfold coachF
    exact Nat.mul_div_cancel' pow_padicValNat_dvd
  have hodd : Odd (coachF p a) := by
    rw [← Nat.not_even_iff_odd]
    intro he
    obtain ⟨c, hc⟩ := he
    apply pow_succ_padicValNat_not_dvd (p := 2) hne
    have h6 : 2 ^ (padicValNat 2 (p - a) + 1) * c
        = 2 ^ padicValNat 2 (p - a) * coachF p a := by
      rw [hc]
      ring
    exact ⟨c, (h6.trans hmul).symm⟩
  obtain ⟨w, hw⟩ := Nat.exists_eq_add_of_le hv
  have hmul' : 2 ^ (1 + w) * coachF p a = p - a := by
    rw [← hw]
    exact hmul
  refine ⟨w, hmul', hodd, ?_⟩
  have h3 : 2 * (2 ^ w * coachF p a) = p - a := by
    rw [← hmul']
    ring
  have h4 : coachF p a ≤ 2 ^ w * coachF p a := Nat.le_mul_of_pos_left _ (by positivity)
  have ha1 : 0 < a := ha.pos
  omega

theorem topRow_inv (p : ℕ) (hp : Odd p) (hp3 : 2 < p) :
    ∀ a ∈ topRow p, Odd a ∧ 2 * a < p ∧ Nat.Coprime a p := by
  apply topRow_induction
  · exact ⟨odd_one, by omega, Nat.coprime_one_left p⟩
  · rintro a ⟨ha, hap, hc⟩
    obtain ⟨w, hmul, hodd, hlt⟩ := coach_spec p a hp ha (by omega)
    refine ⟨hodd, hlt, ?_⟩
    have h1 : Nat.Coprime (p - a) p := (Nat.coprime_self_sub_left (by omega)).2 hc
    exact Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ hmul) h1

theorem two_ne (p : ℕ) [Fact p.Prime] (hp3 : 2 < p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have h2 := (ZMod.natCast_eq_zero_iff 2 p).1 h1
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem four_ne (p : ℕ) [Fact p.Prime] (hp3 : 2 < p) : (4 : ZMod p) ≠ 0 := by
  have h : (4 : ZMod p) = 2 ^ 2 := by norm_num
  rw [h]
  exact pow_ne_zero _ (two_ne p hp3)

theorem two_pow_sq (p : ℕ) (n : ℕ) : ((2 : ZMod p) ^ n) ^ 2 = 4 ^ n := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

theorem sq_inj (p : ℕ) [Fact p.Prime] (N a : ℕ) (hN : 2 * N < p) (ha : 2 * a < p)
    (ha0 : 0 < a) (h : (N : ZMod p) ^ 2 = (a : ZMod p) ^ 2) : N = a := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h1 | h1
  · have h2 := (ZMod.natCast_eq_natCast_iff' N a p).1 h1
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
    exact h2
  · exfalso
    have h2 : ((N + a : ℕ) : ZMod p) = 0 := by
      push_cast
      rw [h1]
      ring
    have h3 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by omega) h3
    omega

theorem topRow_pow (p : ℕ) [Fact p.Prime] (hp : Odd p) (hp3 : 2 < p) :
    ∀ t ∈ topRow p, t ∈ topRow p ∧ ∃ m : ℕ, (4 : ZMod p) ^ m * (t : ZMod p) ^ 2 = 1 := by
  apply topRow_induction
  · exact ⟨⟨0, rfl⟩, 0, by simp⟩
  · rintro a ⟨hmem, m, hm⟩
    obtain ⟨hodd, h2a, -⟩ := topRow_inv p hp hp3 a hmem
    obtain ⟨w, hmul, -, -⟩ := coach_spec p a hp hodd (by omega)
    refine ⟨topRow_step p a hmem, m + (1 + w), ?_⟩
    have hc : (2 : ZMod p) ^ (1 + w) * (coachF p a : ZMod p) = -(a : ZMod p) := by
      have h := congrArg (Nat.cast : ℕ → ZMod p) hmul
      push_cast [Nat.cast_sub (by omega : a ≤ p)] at h
      simpa using h
    calc (4 : ZMod p) ^ (m + (1 + w)) * (coachF p a : ZMod p) ^ 2
        = (4 : ZMod p) ^ m * ((2 : ZMod p) ^ (1 + w) * (coachF p a : ZMod p)) ^ 2 := by
          rw [mul_pow, two_pow_sq]
          ring
      _ = 1 := by
          rw [hc, neg_sq]
          exact hm

theorem reach (p : ℕ) [Fact p.Prime] (hp : Odd p) (hp3 : 2 < p) (m : ℕ) :
    ∃ t ∈ topRow p, ∃ i : ℕ, 2 * (2 ^ i * t) < p ∧
      (4 : ZMod p) ^ m * ((2 ^ i * t : ℕ) : ZMod p) ^ 2 = 1 := by
  induction m with
  | zero => exact ⟨1, ⟨0, rfl⟩, 0, by omega, by simp⟩
  | succ m ih =>
    obtain ⟨t, ht, i, hlt, heq⟩ := ih
    cases i with
    | zero =>
      obtain ⟨hodd, h2t, -⟩ := topRow_inv p hp hp3 t ht
      obtain ⟨w, hmul, -, -⟩ := coach_spec p t hp hodd (by omega)
      refine ⟨coachF p t, topRow_step p t ht, w, ?_, ?_⟩
      · have h3 : 2 * (2 ^ w * coachF p t) = p - t := by
          rw [← hmul]
          ring
        have := hodd.pos
        omega
      · have hc : (2 : ZMod p) ^ (1 + w) * (coachF p t : ZMod p) = -(t : ZMod p) := by
          have h := congrArg (Nat.cast : ℕ → ZMod p) hmul
          push_cast [Nat.cast_sub (by omega : t ≤ p)] at h
          simpa using h
        simp only [pow_zero, one_mul] at heq
        calc (4 : ZMod p) ^ (m + 1) * ((2 ^ w * coachF p t : ℕ) : ZMod p) ^ 2
            = (4 : ZMod p) ^ m * ((2 : ZMod p) ^ (1 + w) * (coachF p t : ZMod p)) ^ 2 := by
              push_cast
              rw [mul_pow, mul_pow, two_pow_sq, two_pow_sq]
              ring
          _ = 1 := by
              rw [hc, neg_sq]
              exact heq
    | succ i =>
      have h5 : 2 ^ (i + 1) * t = 2 * (2 ^ i * t) := by ring
      refine ⟨t, ht, i, by omega, ?_⟩
      rw [← heq]
      push_cast
      ring

theorem pm_iff (p : ℕ) [Fact p.Prime] (m : ℕ) :
    (2 ^ m ≡ 1 [MOD p] ∨ 2 ^ m ≡ p - 1 [MOD p]) ↔ (4 : ZMod p) ^ m = 1 := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have h4 : (4 : ZMod p) ^ m = ((2 : ZMod p) ^ m) ^ 2 := by
    rw [show (4 : ZMod p) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
  rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_natCast_iff, h4,
    ← one_pow (M := ZMod p) 2, sq_eq_sq_iff_eq_or_eq_neg]
  push_cast [Nat.cast_sub hp1]
  simp

theorem sord2_eq (p : ℕ) [Fact p.Prime] : sord2 p = orderOf (4 : ZMod p) := by
  unfold sord2
  split_ifs with h
  · symm
    rw [orderOf_eq_iff (Nat.find_spec h).1]
    refine ⟨(pm_iff p _).1 (Nat.find_spec h).2, ?_⟩
    intro m hm hm0 h1
    exact Nat.find_min h hm ⟨hm0, (pm_iff p m).2 h1⟩
  · symm
    rw [orderOf_eq_zero_iff']
    intro n hn h1
    exact h ⟨n, hn, (pm_iff p n).2 h1⟩

theorem exists_small_sq (p : ℕ) [Fact p.Prime] (d : ℕ) (hd : p = 2 * d + 1) (x : ZMod p)
    (hx : x ≠ 0) : ∃ n ∈ Finset.Icc 1 d, ((n : ℕ) : ZMod p) ^ 2 = x ^ 2 := by
  have hv : x.val < p := ZMod.val_lt x
  have hv0 : x.val ≠ 0 := by rwa [Ne, ZMod.val_eq_zero]
  have hcast : ((x.val : ℕ) : ZMod p) = x := ZMod.natCast_zmod_val x
  by_cases h : x.val ≤ d
  · exact ⟨x.val, Finset.mem_Icc.2 ⟨by omega, h⟩, by rw [hcast]⟩
  · refine ⟨p - x.val, Finset.mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩
    rw [Nat.cast_sub hv.le, hcast, ZMod.natCast_self, zero_sub, neg_sq]

theorem inv_pow (p : ℕ) (d : ℕ) (hd0 : 0 < d) (h4 : (4 : ZMod p) ^ d = 1) (x : ZMod p)
    (k : ℕ) (hk : x = 4 ^ k) : ∃ m : ℕ, (4 : ZMod p) ^ m * x = 1 :=
  ⟨d * k - k, by
    rw [hk, ← pow_add, Nat.sub_add_cancel (Nat.le_mul_of_pos_left k hd0), pow_mul, h4, one_pow]⟩

theorem pow_inv (p : ℕ) (d : ℕ) (hd0 : 0 < d) (h4 : (4 : ZMod p) ^ d = 1) (x : ZMod p)
    (m : ℕ) (hm : (4 : ZMod p) ^ m * x = 1) : ∃ k : ℕ, x = 4 ^ k :=
  ⟨d * m - m, by
    calc x = (4 : ZMod p) ^ (d * m) * x := by rw [pow_mul, h4, one_pow, one_mul]
      _ = (4 : ZMod p) ^ (d * m - m) * ((4 : ZMod p) ^ m * x) := by
          rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (Nat.le_mul_of_pos_left m hd0)]
      _ = (4 : ZMod p) ^ (d * m - m) := by rw [hm, mul_one]⟩

theorem sq_mem_pow (p : ℕ) [Fact p.Prime] (hp3 : 2 < p) (d : ℕ) (hd : p = 2 * d + 1)
    (ho : orderOf (4 : ZMod p) = d) (a : ℕ) (ha0 : 0 < a) (ha : a ≤ d) :
    ∃ k : ℕ, (a : ZMod p) ^ 2 = 4 ^ k := by
  classical
  have hcard4 : ((Finset.range d).image (fun k : ℕ => (4 : ZMod p) ^ k)).card = d := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro x hx y hy hxy
    refine pow_injOn_Iio_orderOf ?_ ?_ hxy
    · rw [ho]
      simpa using hx
    · rw [ho]
      simpa using hy
  have hcardS : ((Finset.Icc 1 d).image (fun n : ℕ => (n : ZMod p) ^ 2)).card ≤ d := by
    refine Finset.card_image_le.trans ?_
    simp
  have hsub : (Finset.range d).image (fun k : ℕ => (4 : ZMod p) ^ k) ⊆
      (Finset.Icc 1 d).image (fun n : ℕ => (n : ZMod p) ^ 2) := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨n, hn, hn2⟩ := exists_small_sq p d hd ((2 : ZMod p) ^ k)
      (pow_ne_zero _ (two_ne p hp3))
    refine Finset.mem_image.2 ⟨n, hn, ?_⟩
    rw [hn2, show (4 : ZMod p) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hmem : (a : ZMod p) ^ 2 ∈ (Finset.Icc 1 d).image (fun n : ℕ => (n : ZMod p) ^ 2) :=
    Finset.mem_image.2 ⟨a, Finset.mem_Icc.2 ⟨ha0, ha⟩, rfl⟩
  rw [← heq] at hmem
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hmem
  exact ⟨k, hk.symm⟩

theorem forward (p : ℕ) (h : oneCoach p) :
    ∃ q : ℕ, 0 < q ∧ (p = 4 * q - 1 ∨ p = 4 * q + 1) ∧ topRow p = firstOdds q := by
  obtain ⟨hprime, hp3, htot⟩ := h
  have : Fact p.Prime := ⟨hprime⟩
  rw [Nat.totient_prime hprime, sord2_eq] at htot
  have hodd : Odd p := hprime.odd_of_ne_two (by omega)
  have hd : p = 2 * orderOf (4 : ZMod p) + 1 := by omega
  have hd0 : 0 < orderOf (4 : ZMod p) := by omega
  have h4 : (4 : ZMod p) ^ orderOf (4 : ZMod p) = 1 := pow_orderOf_eq_one _
  obtain ⟨x, hx⟩ := hodd
  refine ⟨(p + 1) / 4, by omega, by omega, ?_⟩
  have hodd : Odd p := ⟨x, hx⟩
  ext a
  constructor
  · intro ha
    obtain ⟨⟨y, hy⟩, h2a, -⟩ := topRow_inv p hodd hp3 a ha
    exact ⟨y, by omega, hy⟩
  · rintro ⟨i, hi, rfl⟩
    have h2a : 2 * (2 * i + 1) < p := by omega
    obtain ⟨k, hk⟩ := sq_mem_pow p hp3 _ hd rfl (2 * i + 1) (by omega) (by omega)
    obtain ⟨m, hm⟩ := inv_pow p _ hd0 h4 _ k hk
    obtain ⟨t, ht, j, hlt, heq⟩ := reach p hodd hp3 m
    have hsq : ((2 ^ j * t : ℕ) : ZMod p) ^ 2 = ((2 * i + 1 : ℕ) : ZMod p) ^ 2 :=
      mul_left_cancel₀ (pow_ne_zero m (four_ne p hp3)) (heq.trans hm.symm)
    have hN := sq_inj p _ _ hlt h2a (by omega) hsq
    cases j with
    | zero =>
      rw [pow_zero, one_mul] at hN
      rw [← hN]
      exact ht
    | succ j =>
      exfalso
      have h5 : 2 ^ (j + 1) * t = 2 * (2 ^ j * t) := by ring
      omega

theorem backward (p q : ℕ) (hq : 0 < q) (hpq : p = 4 * q - 1 ∨ p = 4 * q + 1)
    (hrow : topRow p = firstOdds q) : oneCoach p := by
  have hp3 : 2 < p := by omega
  have hodd : Odd p := Nat.odd_iff.2 (by omega)
  have hprime : p.Prime := by
    by_contra hnp
    have hr : (p.minFac).Prime := Nat.minFac_prime (by omega)
    have hdvd : p.minFac ∣ p := Nat.minFac_dvd p
    have hsq : p.minFac ^ 2 ≤ p := Nat.minFac_sq_le_self (by omega) hnp
    have hr2 : p.minFac ≠ 2 := by
      intro h2
      rw [h2] at hdvd
      obtain ⟨x, hx⟩ := hodd
      omega
    have hrodd : Odd p.minFac := hr.odd_of_ne_two hr2
    obtain ⟨y, hy⟩ := hrodd
    have hr3 : 3 ≤ p.minFac := by
      have := hr.two_le
      omega
    have h3r : 3 * p.minFac ≤ p := by nlinarith
    have hmem : p.minFac ∈ firstOdds q := ⟨y, by omega, hy⟩
    rw [← hrow] at hmem
    obtain ⟨-, -, hc⟩ := topRow_inv p hodd hp3 _ hmem
    have := Nat.Coprime.eq_one_of_dvd hc hdvd
    omega
  have : Fact p.Prime := ⟨hprime⟩
  refine ⟨hprime, hp3, ?_⟩
  rw [Nat.totient_prime hprime, sord2_eq]
  obtain ⟨s, hs⟩ := hodd
  have hodd : Odd p := ⟨s, hs⟩
  have h4s : (4 : ZMod p) ^ s = 1 := by
    have h := ZMod.pow_card_sub_one_eq_one (two_ne p hp3)
    have h2 : p - 1 = 2 * s := by omega
    rw [h2, pow_mul] at h
    rw [← h]
    norm_num
  have hdvd : orderOf (4 : ZMod p) ∣ s := orderOf_dvd_of_pow_eq_one h4s
  have hs0 : 0 < s := by omega
  have hd0 : 0 < orderOf (4 : ZMod p) := Nat.pos_of_dvd_of_pos hdvd hs0
  have hle : orderOf (4 : ZMod p) ≤ s := Nat.le_of_dvd hs0 hdvd
  have h4 : (4 : ZMod p) ^ orderOf (4 : ZMod p) = 1 := pow_orderOf_eq_one _
  have hge : s ≤ orderOf (4 : ZMod p) := by
    classical
    have hcardS : ((Finset.Icc 1 s).image (fun n : ℕ => (n : ZMod p) ^ 2)).card = s := by
      rw [Finset.card_image_of_injOn]
      · simp
      · intro x hx y hy hxy
        have hx' := Finset.mem_Icc.1 (Finset.mem_coe.1 hx)
        have hy' := Finset.mem_Icc.1 (Finset.mem_coe.1 hy)
        exact sq_inj p x y (by omega) (by omega) (by omega) hxy
    have hcard4 : ((Finset.range (orderOf (4 : ZMod p))).image
        (fun k : ℕ => (4 : ZMod p) ^ k)).card ≤ orderOf (4 : ZMod p) := by
      refine Finset.card_image_le.trans ?_
      simp
    have hsub : (Finset.Icc 1 s).image (fun n : ℕ => (n : ZMod p) ^ 2) ⊆
        (Finset.range (orderOf (4 : ZMod p))).image (fun k : ℕ => (4 : ZMod p) ^ k) := by
      intro x hx
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx
      have hn' := Finset.mem_Icc.1 hn
      obtain ⟨e, o, ⟨z, hz⟩, hno⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n ≠ 0)
      have hon : o ≤ n := by
        rw [hno]
        exact Nat.le_mul_of_pos_left _ (by positivity)
      have homem : o ∈ firstOdds q := ⟨z, by omega, hz⟩
      rw [← hrow] at homem
      obtain ⟨-, m, hm⟩ := topRow_pow p hodd hp3 o homem
      obtain ⟨k, hk⟩ := pow_inv p _ hd0 h4 _ m hm
      refine Finset.mem_image.2 ⟨(e + k) % orderOf (4 : ZMod p),
        Finset.mem_range.2 (Nat.mod_lt _ hd0), ?_⟩
      rw [pow_mod_orderOf, hno, pow_add, ← hk]
      push_cast
      rw [mul_pow, two_pow_sq]
    have := Finset.card_le_card hsub
    omega
  omega

end OMA.A005408

theorem OMA.solution : type_of% @OMA.S_oeis_a005408.main := by
  intro p
  constructor
  · exact OMA.A005408.forward p
  · rintro ⟨q, hq, hpq, hrow⟩
    exact OMA.A005408.backward p q hq hpq hrow
