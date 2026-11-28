import OMAStatements.S_oeis_a221855
import Mathlib

open Finset

namespace OMAOrbit

/-- Fixed-point criterion for the multiplier `c`. -/
theorem unit_pow_smul_eq_iff {N : ℕ} (c : ℕ) (hc0 : 0 < c) (hc : c.Coprime N) (x : ZMod N)
    (k : ℕ) : (ZMod.unitOfCoprime c hc ^ k) • x = x ↔ (c : ZMod (addOrderOf x)) ^ k = 1 := by
  have hk : 1 ≤ c ^ k := Nat.one_le_pow _ _ hc0
  have h1 : (ZMod.unitOfCoprime c hc ^ k) • x = ((c ^ k : ℕ) : ZMod N) * x := by
    rw [Units.smul_def, smul_eq_mul, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]
    push_cast; ring
  have h2 : ((c ^ k : ℕ) : ZMod N) * x = x ↔ (c ^ k - 1) • x = 0 := by
    rw [nsmul_eq_mul, Nat.cast_sub hk, sub_mul, Nat.cast_one, one_mul, sub_eq_zero]
  rw [h1, h2, ← addOrderOf_dvd_iff_nsmul_eq_zero, ← ZMod.natCast_eq_zero_iff, Nat.cast_sub hk,
    sub_eq_zero, Nat.cast_pow, Nat.cast_one]

theorem card_filter_dvd_range {L o : ℕ} (ho : 0 < o) (hoL : o ∣ L) :
    ((range L).filter (fun k => o ∣ k)).card = L / o := by
  obtain ⟨q, rfl⟩ := hoL
  rw [Nat.mul_div_cancel_left q ho]
  have : (range (o * q)).filter (fun k => o ∣ k) = (range q).image (fun i => o * i) := by
    ext k
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hk, i, rfl⟩
      exact ⟨i, Nat.lt_of_mul_lt_mul_left hk, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨Nat.mul_lt_mul_of_pos_left hi ho, dvd_mul_right o i⟩
  rw [this, card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left ho h), card_range]

/-- Orbit count of multiplication by `c` on `ZMod N`. -/
theorem card_orbits {N : ℕ} [NeZero N] (c : ℕ) (hc0 : 0 < c) (hc : c.Coprime N) :
    Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (ZMod.unitOfCoprime c hc)) (ZMod N))
      = ∑ m ∈ N.divisors, m.totient / orderOf (c : ZMod m) := by
  classical
  set u := ZMod.unitOfCoprime c hc with hu
  set L := orderOf u with hLdef
  have hL : 0 < L := orderOf_pos u
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Subgroup.zpowers u) (ZMod N)
  simp only [Fintype.card_eq_nat_card, Nat.card_zpowers] at hB
  have hfix : ∀ g : Subgroup.zpowers u, Nat.card (MulAction.fixedBy (ZMod N) g)
      = (univ.filter (fun x : ZMod N => g • x = x)).card := by
    intro g
    rw [← Fintype.card_eq_nat_card, ← Set.toFinset_card]
    congr 1
    ext x
    simp [MulAction.mem_fixedBy]
  have hstab : ∀ x : ZMod N, (univ.filter (fun g : Subgroup.zpowers u => g • x = x)).card
      = L / orderOf (c : ZMod (addOrderOf x)) := by
    intro x
    have hcL : (c : ZMod (addOrderOf x)) ^ L = 1 := by
      rw [← unit_pow_smul_eq_iff c hc0 hc x L, pow_orderOf_eq_one, one_smul]
    have ho : 0 < orderOf (c : ZMod (addOrderOf x)) :=
      orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨L, hL, hcL⟩)
    have hoL : orderOf (c : ZMod (addOrderOf x)) ∣ L := orderOf_dvd_of_pow_eq_one hcL
    rw [← card_filter_dvd_range ho hoL]
    symm
    refine Finset.card_bij (fun k _ => (⟨u ^ k, k, by simp⟩ : Subgroup.zpowers u)) ?_ ?_ ?_
    · intro k hk
      simp only [mem_filter, mem_range, mem_univ, true_and] at hk ⊢
      rw [Submonoid.smul_def]
      exact (unit_pow_smul_eq_iff c hc0 hc x k).mpr (orderOf_dvd_iff_pow_eq_one.mp hk.2)
    · intro a ha b hb hab
      simp only [mem_filter, mem_range] at ha hb
      have h : u ^ a = u ^ b := congrArg Subtype.val hab
      exact pow_injOn_Iio_orderOf ha.1 hb.1 h
    · intro g hg
      simp only [mem_filter, mem_univ, true_and] at hg
      have hg2 := (isOfFinOrder_of_finite u).mem_zpowers_iff_mem_range_orderOf.mp g.2
      simp only [mem_image, mem_range] at hg2
      obtain ⟨k, hk, hgk⟩ := hg2
      refine ⟨k, ?_, Subtype.ext hgk⟩
      simp only [mem_filter, mem_range]
      refine ⟨hk, orderOf_dvd_of_pow_eq_one ?_⟩
      rw [← unit_pow_smul_eq_iff c hc0 hc x k, hgk]
      rw [Submonoid.smul_def] at hg
      exact hg
  have hswap : ∑ g : Subgroup.zpowers u, (univ.filter (fun x : ZMod N => g • x = x)).card
      = ∑ x : ZMod N, (univ.filter (fun g : Subgroup.zpowers u => g • x = x)).card := by
    simp only [card_eq_sum_ones, sum_filter]
    exact sum_comm
  have hgroup : ∑ x : ZMod N, L / orderOf (c : ZMod (addOrderOf x))
      = ∑ m ∈ N.divisors, m.totient * (L / orderOf (c : ZMod m)) := by
    rw [← sum_fiberwise_of_maps_to (s := univ) (t := N.divisors) (g := addOrderOf)
      (fun x _ => Nat.mem_divisors.mpr
        ⟨by simpa [ZMod.card] using addOrderOf_dvd_card (x := x), NeZero.ne N⟩)]
    apply sum_congr rfl
    intro m hm
    rw [sum_congr rfl (fun x hx => by rw [(mem_filter.1 hx).2]), sum_const, smul_eq_mul]
    congr 1
    have hmN : m ∣ Fintype.card (ZMod N) := by
      rw [ZMod.card]; exact Nat.dvd_of_mem_divisors hm
    have := IsAddCyclic.card_addOrderOf_eq_totient (α := ZMod N) hmN
    simpa using this
  have hdiv : ∀ m ∈ N.divisors, orderOf (c : ZMod m) ∣ m.totient ∧ orderOf (c : ZMod m) ∣ L := by
    intro m hm
    have hmN : m ∣ N := Nat.dvd_of_mem_divisors hm
    have hcm : c.Coprime m := Nat.Coprime.coprime_dvd_right hmN hc
    have e1 : orderOf (c : ZMod m) = orderOf (ZMod.unitOfCoprime c hcm) := by
      rw [← orderOf_units, ZMod.coe_unitOfCoprime]
    refine ⟨?_, ?_⟩
    · rw [e1]; exact orderOf_dvd_of_pow_eq_one (ZMod.pow_totient _)
    · apply orderOf_dvd_of_pow_eq_one
      have h1 : ((u ^ L : (ZMod N)ˣ) : ZMod N) = 1 := by
        rw [hLdef, pow_orderOf_eq_one, Units.val_one]
      rw [Units.val_pow_eq_pow_val, hu, ZMod.coe_unitOfCoprime] at h1
      have h2 := congrArg (ZMod.castHom hmN (ZMod m)) h1
      rw [map_pow, map_natCast, map_one] at h2
      exact h2
  have key : Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers u) (ZMod N)) * L
      = (∑ m ∈ N.divisors, m.totient / orderOf (c : ZMod m)) * L := by
    have e : Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers u) (ZMod N))
        = Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers u) (ZMod N))) := rfl
    rw [e, ← hB, sum_congr rfl (fun g _ => hfix g), hswap, sum_congr rfl (fun x _ => hstab x),
      hgroup, sum_mul]
    apply sum_congr rfl
    intro m hm
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hdiv m hm
    have ho : 0 < orderOf (c : ZMod m) := by
      rcases Nat.eq_zero_or_pos (orderOf (c : ZMod m)) with h | h
      · rw [h, zero_mul] at hb; omega
      · exact h
    rw [ha, hb, Nat.mul_div_cancel_left _ ho, Nat.mul_div_cancel_left _ ho]
    ring
  exact Nat.eq_of_mul_eq_mul_right hL key

/-- Order modulo a coprime product is the lcm of the orders. -/
theorem orderOf_natCast_mul (c a b : ℕ) (hab : a.Coprime b) :
    orderOf (c : ZMod (a * b)) = Nat.lcm (orderOf (c : ZMod a)) (orderOf (c : ZMod b)) := by
  rw [← MulEquiv.orderOf_eq (ZMod.chineseRemainder hab).toMulEquiv (c : ZMod (a * b))]
  have h : (ZMod.chineseRemainder hab).toMulEquiv (c : ZMod (a * b))
      = ((c : ZMod a), (c : ZMod b)) := by
    rw [RingEquiv.toMulEquiv_eq_coe, RingEquiv.coe_toMulEquiv, map_natCast]
    rfl
  rw [h, Prod.orderOf]

/-- Divisor sums over `2^n * 5^n`. -/
theorem sum_divisors_two_five (n : ℕ) (f : ℕ → ℕ) :
    ∑ m ∈ (2 ^ n * 5 ^ n).divisors, f m
      = ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), f (2 ^ i * 5 ^ j) := by
  have hcop : (2 ^ n).Coprime (5 ^ n) := by
    apply Nat.Coprime.pow; norm_num
  rw [Nat.divisors_mul, Finset.mul_def, sum_image (fun p hp q hq h =>
    hcop.mul_injOn_divisors (by simpa using hp) (by simpa using hq) h), sum_product,
    Nat.divisors_prime_pow Nat.prime_two, sum_map]
  apply sum_congr rfl
  intro i _
  rw [Nat.divisors_prime_pow (by norm_num : Nat.Prime 5), sum_map]
  rfl


theorem natCast_pow_eq_one_iff (c e M : ℕ) (hc : 0 < c) :
    ((c : ZMod M)) ^ e = 1 ↔ M ∣ c ^ e - 1 := by
  have hk : 1 ≤ c ^ e := Nat.one_le_pow _ _ hc
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hk, sub_eq_zero, Nat.cast_pow, Nat.cast_one]

theorem tot2 (i : ℕ) : (2 ^ i).totient = if i = 0 then 1 else 2 ^ (i - 1) := by
  rcases i with _ | i
  · simp
  · rw [Nat.totient_prime_pow_succ Nat.prime_two]
    simp

theorem tot5 (l : ℕ) : (5 ^ (l + 1)).totient = 4 * 5 ^ l := by
  rw [Nat.totient_prime_pow_succ (by norm_num : Nat.Prime 5)]
  ring

-- a = 1 + 2^(e+2) t0 with t0 odd gives a^(2^m) = 1 + 2^(m+e+2) t with t odd
theorem pow_two_pow_gen (a t0 e : ℕ) (ha : a = 1 + 2 ^ (e + 2) * t0) (ht0 : t0 % 2 = 1)
    (m : ℕ) : ∃ t, t % 2 = 1 ∧ a ^ (2 ^ m) = 1 + 2 ^ (m + e + 2) * t := by
  induction m with
  | zero => exact ⟨t0, ht0, by rw [pow_zero, pow_one, ha]; ring_nf⟩
  | succ m ih =>
    obtain ⟨t, ht, h⟩ := ih
    refine ⟨t + 2 * (2 ^ (m + e) * t ^ 2), ?_, ?_⟩
    · rw [Nat.add_mul_mod_self_left]; exact ht
    · rw [pow_succ, pow_mul, h]; ring

-- a = 1 + 5 t0 with 5 not dividing t0 gives a^(5^m) = 1 + 5^(m+1) t with 5 not dividing t
theorem pow_five_pow_gen (a t0 : ℕ) (ha : a = 1 + 5 * t0) (ht0 : t0 % 5 ≠ 0) (m : ℕ) :
    ∃ t, t % 5 ≠ 0 ∧ a ^ (5 ^ m) = 1 + 5 ^ (m + 1) * t := by
  induction m with
  | zero => exact ⟨t0, ht0, by rw [pow_zero, pow_one, ha]; ring⟩
  | succ m ih =>
    obtain ⟨t, ht, h⟩ := ih
    refine ⟨t + 5 * (2 * 5 ^ m * t ^ 2 + 2 * 5 ^ (2 * m + 1) * t ^ 3 + 5 ^ (3 * m + 2) * t ^ 4
      + 5 ^ (4 * m + 2) * t ^ 5), ?_, ?_⟩
    · rw [Nat.add_mul_mod_self_left]; exact ht
    · rw [pow_succ, pow_mul, h]; ring

theorem pow_mod_five_four (o : ℕ) (h : 13 ^ o % 5 = 1) : 4 ∣ o := by
  induction o using Nat.strong_induction_on with
  | _ o ih =>
    rcases Nat.lt_or_ge o 4 with ho | ho
    · interval_cases o <;> simp_all
    · obtain ⟨p, rfl⟩ : ∃ p, o = p + 4 := ⟨o - 4, by omega⟩
      have e : 13 ^ (p + 4) % 5 = 13 ^ p % 5 := by
        rw [pow_add, Nat.mul_mod]; norm_num
      have := ih p (by omega) (by rw [← e]; exact h)
      omega

theorem orderOf_c_two_pow (i : ℕ) :
    orderOf ((13 : ℕ) : ZMod (2 ^ i)) = if i ≤ 2 then 1 else 2 ^ (i - 2) := by
  split_ifs with h
  · rw [orderOf_eq_one_iff]
    have e : ((13 : ℕ) : ZMod (2 ^ i)) = ((1 : ℕ) : ZMod (2 ^ i)) := by
      rw [ZMod.natCast_eq_natCast_iff']
      interval_cases i <;> rfl
    rw [e, Nat.cast_one]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 3 := ⟨i - 3, by omega⟩
    rw [show k + 3 - 2 = k + 1 by omega]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply orderOf_eq_prime_pow
    · rw [natCast_pow_eq_one_iff _ _ _ (by norm_num)]
      obtain ⟨t, ht, h⟩ := pow_two_pow_gen 13 3 0 (by norm_num) (by norm_num) k
      rw [h, Nat.add_sub_cancel_left]
      intro hd
      have h2 : 2 ^ (k + 0 + 2) * 2 ∣ 2 ^ (k + 0 + 2) * t := by
        rw [← pow_succ]; exact hd
      have h3 := Nat.dvd_of_mul_dvd_mul_left (by positivity) h2
      omega
    · rw [natCast_pow_eq_one_iff _ _ _ (by norm_num)]
      obtain ⟨t, ht, h⟩ := pow_two_pow_gen 13 3 0 (by norm_num) (by norm_num) (k + 1)
      rw [h, Nat.add_sub_cancel_left]
      exact ⟨t, by ring⟩

theorem orderOf_c_five_pow (j : ℕ) :
    orderOf ((13 : ℕ) : ZMod (5 ^ j)) = if j = 0 then 1 else 4 * 5 ^ (j - 1) := by
  split_ifs with h
  · subst h
    rw [orderOf_eq_one_iff]
    have e : ((13 : ℕ) : ZMod (5 ^ 0)) = ((1 : ℕ) : ZMod (5 ^ 0)) := by
      rw [ZMod.natCast_eq_natCast_iff']; rfl
    rw [e, Nat.cast_one]
  · obtain ⟨l, rfl⟩ : ∃ l, j = l + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hy : orderOf (((13 : ℕ) : ZMod (5 ^ (l + 1))) ^ 4) = 5 ^ l := by
      rcases l with _ | l
      · rw [pow_zero, orderOf_eq_one_iff, natCast_pow_eq_one_iff _ _ _ (by norm_num)]
        norm_num
      · apply orderOf_eq_prime_pow
        · rw [← pow_mul, natCast_pow_eq_one_iff _ _ _ (by norm_num), pow_mul]
          obtain ⟨t, ht, h⟩ := pow_five_pow_gen (13 ^ 4) 5712 (by norm_num) (by norm_num) l
          rw [h, Nat.add_sub_cancel_left]
          intro hd
          have h2 : 5 ^ (l + 1) * 5 ∣ 5 ^ (l + 1) * t := by
            rw [← pow_succ]; exact hd
          have h3 := Nat.dvd_of_mul_dvd_mul_left (by positivity) h2
          omega
        · rw [← pow_mul, natCast_pow_eq_one_iff _ _ _ (by norm_num), pow_mul]
          obtain ⟨t, ht, h⟩ := pow_five_pow_gen (13 ^ 4) 5712 (by norm_num) (by norm_num) (l + 1)
          rw [h, Nat.add_sub_cancel_left]
          exact ⟨t, by ring⟩
    have h4 : 4 ∣ orderOf ((13 : ℕ) : ZMod (5 ^ (l + 1))) := by
      apply pow_mod_five_four
      have h1 := pow_orderOf_eq_one ((13 : ℕ) : ZMod (5 ^ (l + 1)))
      rw [natCast_pow_eq_one_iff _ _ _ (by norm_num)] at h1
      have h2 : 5 ∣ 13 ^ orderOf ((13 : ℕ) : ZMod (5 ^ (l + 1))) - 1 :=
        (dvd_pow_self 5 (Nat.succ_ne_zero l)).trans h1
      have hpos : 1 ≤ 13 ^ orderOf ((13 : ℕ) : ZMod (5 ^ (l + 1))) := Nat.one_le_pow _ _ (by norm_num)
      generalize 13 ^ orderOf ((13 : ℕ) : ZMod (5 ^ (l + 1))) = X at h2 hpos ⊢
      omega
    have h5 := orderOf_pow' ((13 : ℕ) : ZMod (5 ^ (l + 1))) (n := 4) (by norm_num)
    rw [hy, Nat.gcd_eq_right h4] at h5
    omega

def a13 (i : ℕ) : ℕ := if i ≤ 1 then 1 else 2

def b13 (i : ℕ) : ℕ := if i ≤ 1 then 1 else if i = 2 then 2 else if i = 3 then 4 else 8

theorem lcm_of_dvd {a b : ℕ} (h : a ∣ b) : Nat.lcm a b = b :=
  Nat.dvd_antisymm (Nat.lcm_dvd h dvd_rfl) (Nat.dvd_lcm_right a b)

theorem term13 (i j : ℕ) :
    (2 ^ i * 5 ^ j).totient / orderOf ((13 : ℕ) : ZMod (2 ^ i * 5 ^ j))
      = if j = 0 then a13 i else b13 i := by
  have hcop : (2 ^ i).Coprime (5 ^ j) := Nat.Coprime.pow _ _ (by norm_num)
  rw [orderOf_natCast_mul _ _ _ hcop, orderOf_c_two_pow, orderOf_c_five_pow,
    Nat.totient_mul hcop, tot2]
  rcases (show i ≤ 2 ∨ i = 3 ∨ ∃ k, i = k + 4 by
    rcases Nat.lt_or_ge i 4 with h | h
    · omega
    · right; right; exact ⟨i - 4, by omega⟩) with hi | rfl | ⟨k, rfl⟩
  · have hb : (if i = 0 then 1 else 2 ^ (i - 1)) = b13 i := by
      unfold b13; interval_cases i <;> rfl
    have ha : a13 i = b13 i := by
      unfold a13 b13; interval_cases i <;> rfl
    rw [hb, if_pos hi, ha]
    rcases j with _ | l
    · simp
    · rw [if_neg (Nat.succ_ne_zero l), if_neg (Nat.succ_ne_zero l), Nat.add_sub_cancel, tot5,
        Nat.lcm_one_left]
      apply Nat.div_eq_of_eq_mul_left (by positivity)
      ring
  · rw [if_neg (show ¬ (3 : ℕ) = 0 by norm_num), if_neg (show ¬ (3 : ℕ) ≤ 2 by norm_num),
      show (3 : ℕ) - 2 = 1 from rfl, show (3 : ℕ) - 1 = 2 from rfl, pow_one]
    rcases j with _ | l
    · rw [if_pos rfl, if_pos rfl, pow_zero, Nat.totient_one, Nat.lcm_one_right, mul_one]
      unfold a13
      rw [if_neg (show ¬ (3 : ℕ) ≤ 1 by norm_num)]
      norm_num
    · rw [if_neg (Nat.succ_ne_zero l), if_neg (Nat.succ_ne_zero l), Nat.add_sub_cancel, tot5,
        lcm_of_dvd (Dvd.dvd.mul_right (by norm_num : (2 : ℕ) ∣ 4) _)]
      unfold b13
      rw [if_neg (show ¬ (3 : ℕ) ≤ 1 by norm_num), if_neg (show ¬ (3 : ℕ) = 2 by norm_num),
        if_pos (show (3 : ℕ) = 3 from rfl)]
      apply Nat.div_eq_of_eq_mul_left (by positivity)
      ring
  · rw [if_neg (show ¬ (k + 4 = 0) by omega), if_neg (show ¬ (k + 4 ≤ 2) by omega),
      show k + 4 - 2 = k + 2 by omega, show k + 4 - 1 = k + 3 by omega]
    rcases j with _ | l
    · rw [if_pos rfl, if_pos rfl, pow_zero, Nat.totient_one, Nat.lcm_one_right, mul_one]
      unfold a13
      rw [if_neg (show ¬ (k + 4 ≤ 1) by omega)]
      apply Nat.div_eq_of_eq_mul_left (by positivity)
      ring
    · rw [if_neg (Nat.succ_ne_zero l), if_neg (Nat.succ_ne_zero l), Nat.add_sub_cancel, tot5,
        show 2 ^ (k + 2) = 4 * 2 ^ k by ring, Nat.lcm_mul_left,
        Nat.Coprime.lcm_eq_mul (Nat.Coprime.pow _ _ (by norm_num))]
      unfold b13
      rw [if_neg (show ¬ (k + 4 ≤ 1) by omega), if_neg (show ¬ (k + 4 = 2) by omega),
        if_neg (show ¬ (k + 4 = 3) by omega)]
      apply Nat.div_eq_of_eq_mul_left (by positivity)
      ring

theorem sum13 (n : ℕ) :
    ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), (if j = 0 then a13 i else b13 i)
      = ∑ i ∈ range (n + 1), a13 i + n * ∑ i ∈ range (n + 1), b13 i := by
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [sum_range_succ']
  simp only [Nat.succ_ne_zero, if_false, if_true, sum_const, card_range, smul_eq_mul]
  ring

theorem sumA13 (n : ℕ) (hn : 3 ≤ n) : ∑ i ∈ range (n + 1), a13 i = 2 * n := by
  induction n, hn using Nat.le_induction with
  | base => simp [sum_range_succ, a13]
  | succ n hn ih =>
    rw [sum_range_succ, show a13 (n + 1) = 2 by unfold a13; rw [if_neg (by omega)]]
    omega

theorem sumB13 (n : ℕ) (hn : 3 ≤ n) : ∑ i ∈ range (n + 1), b13 i + 16 = 8 * n := by
  induction n, hn using Nat.le_induction with
  | base => simp [sum_range_succ, b13]
  | succ n hn ih =>
    rw [sum_range_succ, show b13 (n + 1) = 8 by
      unfold b13; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]]
    omega

theorem card13 (n : ℕ) (hc : Nat.Coprime 13 (10 ^ n)) :
    Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (ZMod.unitOfCoprime 13 hc))
      (ZMod (10 ^ n))) = ∑ i ∈ range (n + 1), a13 i + n * ∑ i ∈ range (n + 1), b13 i := by
  have : NeZero (10 ^ n) := ⟨by positivity⟩
  rw [card_orbits 13 (by norm_num) hc, show (10 : ℕ) ^ n = 2 ^ n * 5 ^ n by rw [← mul_pow]; norm_num,
    sum_divisors_two_five n (fun m => m.totient / orderOf ((13 : ℕ) : ZMod m))]
  simp only [term13]
  exact sum13 n

theorem a_eq (n : ℕ) : OMA.S_oeis_a221855.a n
    = ((∑ i ∈ range (n + 1), a13 i + n * ∑ i ∈ range (n + 1), b13 i : ℕ) : ℤ) := by
  unfold OMA.S_oeis_a221855.a
  rw [card13]

theorem a_closed (n : ℕ) (hn : 2 < n) :
    OMA.S_oeis_a221855.a n = 2 * (n : ℤ) * (4 * n - 7) := by
  rw [a_eq]
  have hA := sumA13 n (by omega)
  have hB := sumB13 n (by omega)
  generalize ∑ i ∈ range (n + 1), a13 i = SA at hA ⊢
  generalize ∑ i ∈ range (n + 1), b13 i = SB at hB ⊢
  have hA' : (SA : ℤ) = 2 * n := by exact_mod_cast hA
  have hB' : (SB : ℤ) + 16 = 8 * n := by exact_mod_cast hB
  push_cast
  linear_combination hA' + (n : ℤ) * hB'

theorem a_one : OMA.S_oeis_a221855.a 1 = 4 := by
  rw [a_eq]; simp [sum_range_succ, a13, b13]

theorem a_two : OMA.S_oeis_a221855.a 2 = 12 := by
  rw [a_eq]; simp [sum_range_succ, a13, b13]

end OMAOrbit

open OMAOrbit in
theorem OMA.solution : type_of% @OMA.S_oeis_a221855.main := by
  refine ⟨fun n hn => a_closed n hn, fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
    rw [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
      show k + 6 - 3 = k + 3 by omega, a_closed (k + 6) (by omega), a_closed (k + 5) (by omega),
      a_closed (k + 4) (by omega), a_closed (k + 3) (by omega)]
    push_cast
    ring
  · have v3 := a_closed 3 (by norm_num)
    have v4 := a_closed 4 (by norm_num)
    have v5 := a_closed 5 (by norm_num)
    norm_num at v3 v4 v5
    have e1 : ((PowerSeries.X : PowerSeries ℤ) - 1) ^ 3 * OMA.S_oeis_a221855.series
        = PowerSeries.X ^ 3 * OMA.S_oeis_a221855.series
          - PowerSeries.C 3 * (PowerSeries.X ^ 2 * OMA.S_oeis_a221855.series)
          + PowerSeries.C 3 * (PowerSeries.X ^ 1 * OMA.S_oeis_a221855.series)
          - OMA.S_oeis_a221855.series := by
      simp only [map_ofNat]; ring
    have e2 : (2 * PowerSeries.X * (4 * PowerSeries.X ^ 4 - 7 * PowerSeries.X ^ 3
        - 3 * PowerSeries.X ^ 2 - 2) : PowerSeries ℤ)
        = PowerSeries.C 8 * PowerSeries.X ^ 5 - PowerSeries.C 14 * PowerSeries.X ^ 4
          - PowerSeries.C 6 * PowerSeries.X ^ 3 - PowerSeries.C 4 * PowerSeries.X ^ 1 := by
      simp only [map_ofNat]; ring
    rw [e1, e2]
    refine PowerSeries.ext (fun k => ?_)
    simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_X_pow, OMA.S_oeis_a221855.series, PowerSeries.coeff_mk]
    rcases (show k ≤ 5 ∨ ∃ m, k = m + 6 by
      rcases Nat.lt_or_ge k 6 with h | h
      · left; omega
      · right; exact ⟨k - 6, by omega⟩) with hk | ⟨m, rfl⟩
    · interval_cases k <;> simp [a_one, a_two, v3, v4, v5]
    · simp only [show ¬ (m + 6 = 5) from by omega, show ¬ (m + 6 = 4) from by omega,
        show ¬ (m + 6 = 3) from by omega, show ¬ (m + 6 = 1) from by omega,
        show 3 ≤ m + 6 from by omega, show 2 ≤ m + 6 from by omega,
        show 1 ≤ m + 6 from by omega,
        show m + 6 - 3 = m + 3 from by omega, show m + 6 - 2 = m + 4 from by omega,
        show m + 6 - 1 = m + 5 from by omega, show ¬ (m + 3 = 0) from by omega,
        show ¬ (m + 4 = 0) from by omega, show ¬ (m + 5 = 0) from by omega,
        show ¬ (m + 6 = 0) from by omega, if_true, if_false]
      rw [a_closed (m + 3) (by omega), a_closed (m + 4) (by omega), a_closed (m + 5) (by omega),
        a_closed (m + 6) (by omega)]
      push_cast
      ring
