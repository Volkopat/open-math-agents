import OMAStatements.S_oeis_a334166
import Mathlib

/-!
# OEIS A334166: gaps between members are at most 6

Every positive multiple of 6 is a member: writing `k = 2^a * 3^b * m` with `m` coprime to 6,
one of `k`, `3 * k` has the form `2^a * 3^(2j+1) * m`, and such numbers are Zumkeller.
-/

open Finset

namespace OMAProof

/-- Half-sum form of the Zumkeller property. -/
def Half (n : ℕ) : Prop := ∃ s ⊆ n.divisors, 2 * ∑ i ∈ s, i = ∑ i ∈ n.divisors, i

theorem mul_inj {a b a' b' : ℕ} (h1 : Nat.Coprime a b') (h2 : Nat.Coprime a' b) (ha : 0 < a)
    (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have e1 : a ∣ a' := h1.dvd_of_dvd_mul_right (Dvd.intro _ h)
  have e2 : a' ∣ a := h2.dvd_of_dvd_mul_right (Dvd.intro _ h.symm)
  have e : a = a' := Nat.dvd_antisymm e1 e2
  subst e
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left ha h⟩

theorem Half.mul {n m : ℕ} (hn : Half n) (hc : Nat.Coprime n m) : Half (n * m) := by
  obtain ⟨s, hs, hsum⟩ := hn
  refine ⟨(s ×ˢ m.divisors).image (fun p => p.1 * p.2), ?_, ?_⟩
  · intro x hx
    simp only [mem_image, mem_product, Prod.exists] at hx
    obtain ⟨a, b, ⟨ha, hb⟩, rfl⟩ := hx
    have ha' := Nat.mem_divisors.1 (hs ha)
    have hb' := Nat.mem_divisors.1 hb
    exact Nat.mem_divisors.2 ⟨mul_dvd_mul ha'.1 hb'.1, mul_ne_zero ha'.2 hb'.2⟩
  · rw [sum_image, sum_product, ← sum_mul_sum, hc.sum_divisors_mul, ← hsum, mul_assoc]
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' h
    simp only [coe_product, Set.mem_prod, mem_coe] at hab hab'
    have ha := Nat.mem_divisors.1 (hs hab.1)
    have hb := Nat.mem_divisors.1 hab.2
    have ha' := Nat.mem_divisors.1 (hs hab'.1)
    have hb' := Nat.mem_divisors.1 hab'.2
    have := mul_inj ((hc.coprime_dvd_left ha.1).coprime_dvd_right hb'.1)
      ((hc.coprime_dvd_left ha'.1).coprime_dvd_right hb.1)
      (Nat.pos_of_dvd_of_pos ha.1 (Nat.pos_of_ne_zero ha.2)) h
    exact Prod.ext this.1 this.2

theorem Half.zumkeller {n : ℕ} (h0 : 0 < n) (hn : Half n) : OMA.S_oeis_a334166.Zumkeller n := by
  obtain ⟨s, hs, hsum⟩ := hn
  have := sum_sdiff (f := fun i : ℕ => i) hs
  exact ⟨h0, s, hs, by omega⟩

theorem geom2 (a : ℕ) : (∑ i ∈ range a, 2 ^ i) + 1 = 2 ^ a := by
  induction a with
  | zero => simp
  | succ n ih => rw [sum_range_succ, pow_succ]; omega

theorem geom3 (n : ℕ) : ∑ e ∈ range (2 * n), 3 ^ e = 4 * ∑ t ∈ range n, 9 ^ t := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h9 : (9 : ℕ) ^ n = 3 ^ (2 * n) := by rw [pow_mul]; norm_num
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, h9, pow_succ]
    ring

def hx (a i : ℕ) : ℕ := if i < a then i else if i = a then a else 0

def hy (a i : ℕ) : ℕ := if i < a then 1 else 0

theorem pow23_inj {x y x' y' : ℕ} (h : 2 ^ x * 3 ^ y = 2 ^ x' * 3 ^ y') : x = x' ∧ y = y' := by
  have c : ∀ u v : ℕ, Nat.Coprime (2 ^ u) (3 ^ v) := fun u v =>
    Nat.Coprime.pow u v (by norm_num)
  have := mul_inj (c x y') (c x' y) (by positivity) h
  exact ⟨Nat.pow_right_injective (le_refl 2) this.1,
    Nat.pow_right_injective (by norm_num : 2 ≤ 3) this.2⟩

theorem half_base (a j : ℕ) (ha : 1 ≤ a) : Half (2 ^ a * 3 ^ (2 * j + 1)) := by
  refine ⟨(range (a + 2) ×ˢ range (j + 1)).image
    (fun p => 2 ^ hx a p.1 * 3 ^ (2 * p.2 + hy a p.1)), ?_, ?_⟩
  · intro x hx'
    simp only [mem_image, mem_product, Prod.exists, mem_range] at hx'
    obtain ⟨i, t, ⟨hi, ht⟩, rfl⟩ := hx'
    refine Nat.mem_divisors.2 ⟨mul_dvd_mul (pow_dvd_pow _ ?_) (pow_dvd_pow _ ?_), by positivity⟩
    · unfold hx; split_ifs <;> omega
    · unfold hy; split_ifs <;> omega
  · rw [sum_image]
    · have hK := geom2 a
      have hsig : ∑ i ∈ (2 ^ a * 3 ^ (2 * j + 1)).divisors, i
          = ((∑ i ∈ range a, 2 ^ i) + 2 ^ a) * (4 * ∑ t ∈ range (j + 1), 9 ^ t) := by
        rw [Nat.Coprime.sum_divisors_mul (Nat.Coprime.pow _ _ (by norm_num)),
          Nat.sum_divisors_prime_pow Nat.prime_two, Nat.sum_divisors_prime_pow Nat.prime_three,
          sum_range_succ, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, geom3]
      have hs : ∑ p ∈ range (a + 2) ×ˢ range (j + 1), 2 ^ hx a p.1 * 3 ^ (2 * p.2 + hy a p.1)
          = (3 * (∑ i ∈ range a, 2 ^ i) + 2 ^ a + 1) * ∑ t ∈ range (j + 1), 9 ^ t := by
        have h1 : ∑ i ∈ range (a + 2), 2 ^ hx a i * 3 ^ hy a i
            = 3 * (∑ i ∈ range a, 2 ^ i) + 2 ^ a + 1 := by
          rw [sum_range_succ, sum_range_succ, mul_sum]
          have e1 : ∑ i ∈ range a, 2 ^ hx a i * 3 ^ hy a i = ∑ i ∈ range a, 3 * 2 ^ i := by
            refine sum_congr rfl fun i hi => ?_
            have hi' := mem_range.1 hi
            simp [hx, hy, hi', mul_comm]
          rw [e1]
          simp [hx, hy]
        rw [sum_product, ← h1, sum_mul_sum]
        refine sum_congr rfl fun i _ => sum_congr rfl fun t _ => ?_
        rw [pow_add, pow_mul]
        norm_num
        ring
      rw [hs, hsig, ← hK]
      ring
    · rintro ⟨i, t⟩ hit ⟨i', t'⟩ hit' h
      simp only [coe_product, Set.mem_prod, mem_coe, mem_range] at hit hit'
      have := pow23_inj h
      obtain ⟨e1, e2⟩ := this
      simp only at e1 e2
      unfold hx at e1
      unfold hy at e2
      refine Prod.ext ?_ ?_
      · simp only; split_ifs at e1 e2 <;> omega
      · simp only; split_ifs at e1 e2 <;> omega

theorem member_six {k : ℕ} (hk : 0 < k) (h6 : 6 ∣ k) : OMA.S_oeis_a334166.member k := by
  obtain ⟨a, k1, h2, hk1⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk.ne' 2 (by norm_num)
  have hk10 : k1 ≠ 0 := by rintro rfl; simp at h2
  obtain ⟨b, m, h3, hk2⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk10 3 (by norm_num)
  have hm0 : m ≠ 0 := by rintro rfl; simp at h3
  have h2m : ¬ 2 ∣ m := fun h => h2 (hk2 ▸ Dvd.dvd.mul_left h _)
  have h2k : 2 ∣ k := (by norm_num : 2 ∣ 6).trans h6
  have h3k : 3 ∣ k := (by norm_num : 3 ∣ 6).trans h6
  have ha : 1 ≤ a := by
    by_contra hcon
    have : a = 0 := by omega
    subst this
    rw [hk1] at h2k
    simp at h2k
    exact h2 h2k
  have hb : 1 ≤ b := by
    by_contra hcon
    have : b = 0 := by omega
    subst this
    rw [hk1, hk2] at h3k
    simp only [pow_zero, one_mul] at h3k
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3k with h | h
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    · exact h3 h
  have hcop : ∀ c : ℕ, Nat.Coprime (2 ^ a * 3 ^ c) m := fun c =>
    Nat.Coprime.mul_left
      (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2m))
      (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3))
  have hZ : ∀ j : ℕ, OMA.S_oeis_a334166.Zumkeller (2 ^ a * 3 ^ (2 * j + 1) * m) := fun j =>
    Half.zumkeller (Nat.pos_of_ne_zero (by positivity)) ((half_base a j ha).mul (hcop _))
  rcases Nat.even_or_odd' b with ⟨j, hj | hj⟩
  · refine ⟨3, Nat.mem_divisors.2 ⟨h3k, hk.ne'⟩, ?_⟩
    have : 3 * k = 2 ^ a * 3 ^ (2 * j + 1) * m := by
      rw [hk1, hk2, hj]; ring
    rw [this]
    exact hZ j
  · refine ⟨1, Nat.mem_divisors.2 ⟨one_dvd _, hk.ne'⟩, ?_⟩
    have : 1 * k = 2 ^ a * 3 ^ (2 * j + 1) * m := by
      rw [hk1, hk2, hj]; ring
    rw [this]
    exact hZ j

end OMAProof

theorem OMA.solution : type_of% @OMA.S_oeis_a334166.main := by
  intro x y _ _ _ hz
  by_contra hcon
  exact hz (6 * (x / 6 + 1)) (by omega) (by omega)
    (OMAProof.member_six (by omega) ⟨_, rfl⟩)
