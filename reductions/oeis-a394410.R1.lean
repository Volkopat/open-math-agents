import OMAStatements.S_oeis_a394410
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Linarith

/-! OEIS A394410. The finite cases use Lucas-Pratt certificates. In each
certificate the listed primes multiply to the predecessor of the number tested.
A generator has full order, as verified by modular exponentiation in Lean.
The 343-digit case corresponds to p = 157. Candidate factors for its
certificate were obtained from FactorDB and are verified below. -/

namespace OMA.R_oeis_a394410_R1

open OMA.S_oeis_a394410

/-- The first unresolved input, a(10), is a certified 62-digit prime. -/
def H1 : Prop :=
  let p := OMA.S_oeis_a394410.a 10
  Nat.Prime ((p ^ p + 1) / (p + 1))

/-- On the remaining terms, it suffices to exclude prime divisors in the
progression 1 modulo 2p up to the square root of the quotient. -/
def H2 : Prop :=
  ∀ n : ℕ, 11 ≤ n → Nat.Prime (OMA.S_oeis_a394410.a n) →
    let p := OMA.S_oeis_a394410.a n
    ∀ k : ℕ, let q := 2 * p * k + 1
      Nat.Prime q → q ^ 2 ≤ (p ^ p + 1) / (p + 1) → ¬ q ∣ p ^ p + 1

lemma quotient_as_geometric_sum {p : ℕ} (ho : Odd p) :
    (((p ^ p + 1) / (p + 1) : ℕ) : ℤ) =
      ∑ i ∈ Finset.range p, (-(p : ℤ)) ^ i := by
  have hd : p + 1 ∣ p ^ p + 1 := by
    simpa only [one_pow] using ho.nat_add_dvd_pow_add_pow (x := p) (y := 1)
  have hquot : (((p ^ p + 1) / (p + 1) : ℕ) : ℤ) * ((p : ℤ) + 1) = (p : ℤ) ^ p + 1 := by
    exact_mod_cast Nat.div_mul_cancel hd
  have hgeom := geom_sum_mul_neg (-(p : ℤ)) p
  rw [ho.neg_pow] at hgeom
  simp only [sub_neg_eq_add, add_comm (1 : ℤ)] at hgeom
  exact mul_right_cancel₀ (by omega : (p : ℤ) + 1 ≠ 0) (hquot.trans hgeom.symm)

/-- All potential prime factors occur in a single arithmetic progression. -/
theorem prime_factor_progression {p q : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hq : Nat.Prime q) (hdvd : q ∣ (p ^ p + 1) / (p + 1)) :
    2 * p ∣ q - 1 := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  have hc := congrArg (fun a : ℤ => (a : ZMod q)) (quotient_as_geometric_sum ho)
  simp only [Int.cast_natCast, Int.cast_sum, Int.cast_pow, Int.cast_neg] at hc
  have hs : (∑ i ∈ Finset.range p, (-(p : ZMod q)) ^ i) = 0 :=
    hc.symm.trans ((ZMod.natCast_eq_zero_iff _ _).mpr hdvd)
  have hn1 : -(p : ZMod q) ≠ 1 := by
    intro he
    have h0 : (p : ZMod q) = 0 := by simpa [he] using hs
    rw [h0, neg_zero] at he
    exact zero_ne_one he
  have hpow : (-(p : ZMod q)) ^ p = 1 := by
    apply sub_eq_zero.mp
    simpa only [hs, zero_mul] using (geom_sum_mul (-(p : ZMod q)) p).symm
  have hn0 : -(p : ZMod q) ≠ 0 := by
    intro he
    rw [he, zero_pow hp.ne_zero] at hpow
    exact zero_ne_one hpow
  have horder : orderOf (-(p : ZMod q)) = p :=
    ((Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hpow)).resolve_left
      fun h => hn1 (orderOf_eq_one_iff.mp h)
  let u := Units.mk0 (-(p : ZMod q)) hn0
  have hu : orderOf u = p := by
    rw [← orderOf_units]
    exact horder
  have hpdiv := orderOf_dvd_card (x := u)
  rw [hu, ZMod.card_units_eq_totient, Nat.totient_prime hq] at hpdiv
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact hp.not_dvd_one hpdiv
  exact (Nat.coprime_two_left.mpr ho).mul_dvd_of_dvd_of_dvd
    (even_iff_two_dvd.mp (hq.even_sub_one hq2)) hpdiv

private lemma next_odd {x y : ℕ} (hx : Odd x) (hy : Odd y) :
    Odd ((x ^ 2 + y ^ 2) / 2) := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  refine ⟨u ^ 2 + v ^ 2 + u + v, ?_⟩
  have h : (2 * u + 1) ^ 2 + (2 * v + 1) ^ 2 =
      4 * (u ^ 2 + v ^ 2 + u + v) + 2 := by ring
  rw [h]
  omega

theorem odd_at_positive_index (n : ℕ) : Odd (a (n + 1)) := by
  suffices h : ∀ k, Odd (a (k + 1)) ∧ Odd (a (k + 2)) from (h n).1
  intro k
  induction k with
  | zero => exact ⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩
  | succ k ih => exact ⟨ih.2, next_odd ih.2 ih.1⟩

/-- A composite quotient has a prime factor in the designated progression
whose square is at most the quotient. -/
lemma prime_of_progression_test {p : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (test : ∀ k : ℕ, let q := 2 * p * k + 1
      Nat.Prime q → q ^ 2 ≤ (p ^ p + 1) / (p + 1) → ¬ q ∣ p ^ p + 1) :
    Nat.Prime ((p ^ p + 1) / (p + 1)) := by
  let t := (p ^ p + 1) / (p + 1)
  have hp3 : 3 ≤ p := hp.odd_iff.mp ho
  have ht : 2 ≤ t := by
    apply (Nat.le_div_iff_mul_le (Nat.succ_pos p)).mpr
    have e : p ^ 2 ≤ p ^ p := Nat.pow_le_pow_right hp.pos hp.two_le
    have b := Nat.mul_le_mul_right p hp3
    nlinarith
  by_contra h
  have hq := Nat.minFac_prime (show t ≠ 1 by omega)
  have hd := Nat.minFac_dvd t
  have hs := Nat.minFac_sq_le_self (show 0 < t by omega) h
  obtain ⟨k, hk⟩ := prime_factor_progression hp ho hq hd
  have eq : 2 * p * k + 1 = t.minFac := by have := hq.two_le; omega
  have he := test k
  dsimp only at he
  rw [eq] at he
  have den : p + 1 ∣ p ^ p + 1 := by
    simpa only [one_pow] using ho.nat_add_dvd_pow_add_pow (x := p) (y := 1)
  exact he hq hs (hd.trans (Nat.div_dvd_of_dvd den))

/-- A Lucas certificate with a fully factored predecessor. -/
lemma certify {p : ℕ} (g : ZMod p) (factors : List ℕ)
    (hprod : p - 1 = factors.prod)
    (hfull : g ^ (p - 1) = 1)
    (hfactors : ∀ r ∈ factors, Nat.Prime r ∧ g ^ ((p - 1) / r) ≠ 1) :
    Nat.Prime p := by
  apply lucas_primality p g hfull
  intro q hq hdvd
  rw [hprod] at hdvd
  have contains (xs : List ℕ) (hs : ∀ r ∈ xs, Nat.Prime r)
      (hd : q ∣ xs.prod) : q ∈ xs := by
    induction xs with
    | nil => exact (hq.not_dvd_one hd).elim
    | cons r rs ih =>
      rcases hq.dvd_mul.mp hd with h | h
      · exact List.mem_cons.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (hs r (by simp))).mp h))
      · exact List.mem_cons.mpr (Or.inr (ih (fun a ha => hs a (List.mem_cons_of_mem _ ha)) h))
  exact (hfactors q (contains factors (fun r hr => (hfactors r hr).1) hdvd)).2

lemma prime_18913 : Nat.Prime 18913 := by
  apply certify (7 : ZMod 18913) [2, 2, 2, 2, 2, 3, 197] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_41761 : Nat.Prime 41761 := by
  apply certify (19 : ZMod 41761) [2, 2, 2, 2, 2, 3, 3, 5, 29] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_184417 : Nat.Prime 184417 := by
  apply certify (10 : ZMod 184417) [2, 2, 2, 2, 2, 3, 17, 113] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_45957792327018709121 : Nat.Prime 45957792327018709121 := by
  apply certify (6 : ZMod 45957792327018709121) [2, 2, 2, 2, 2, 2, 2, 5, 17, 29, 18913, 41761, 184417] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_18913, by reduce_mod_char; decide⟩
  · exact ⟨prime_41761, by reduce_mod_char; decide⟩
  · exact ⟨prime_184417, by reduce_mod_char; decide⟩

lemma prime_22921 : Nat.Prime 22921 := by
  apply certify (7 : ZMod 22921) [2, 2, 2, 3, 5, 191] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_1558409 : Nat.Prime 1558409 := by
  apply certify (3 : ZMod 1558409) [2, 2, 2, 83, 2347] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_3116819 : Nat.Prime 3116819 := by
  apply certify (2 : ZMod 3116819) [2, 1558409] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_1558409, by reduce_mod_char; decide⟩

lemma prime_12941 : Nat.Prime 12941 := by
  apply certify (2 : ZMod 12941) [2, 2, 5, 647] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_1941151 : Nat.Prime 1941151 := by
  apply certify (3 : ZMod 1941151) [2, 3, 5, 5, 12941] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_12941, by reduce_mod_char; decide⟩

lemma prime_11646907 : Nat.Prime 11646907 := by
  apply certify (2 : ZMod 11646907) [2, 3, 1941151] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_1941151, by reduce_mod_char; decide⟩

lemma prime_24467076893433443 : Nat.Prime 24467076893433443 := by
  apply certify (2 : ZMod 24467076893433443) [2, 337, 3116819, 11646907] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_3116819, by reduce_mod_char; decide⟩
  · exact ⟨prime_11646907, by reduce_mod_char; decide⟩

lemma prime_30391 : Nat.Prime 30391 := by
  apply certify (3 : ZMod 30391) [2, 3, 5, 1013] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_25929540419 : Nat.Prime 25929540419 := by
  apply certify (2 : ZMod 25929540419) [2, 223, 1913, 30391] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_30391, by reduce_mod_char; decide⟩

lemma prime_518590808381 : Nat.Prime 518590808381 := by
  apply certify (2 : ZMod 518590808381) [2, 2, 5, 25929540419] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_25929540419, by reduce_mod_char; decide⟩

lemma prime_19616587 : Nat.Prime 19616587 := by
  apply certify (2 : ZMod 19616587) [2, 3, 11, 29, 37, 277] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_186239092314521 : Nat.Prime 186239092314521 := by
  apply certify (15 : ZMod 186239092314521) [2, 2, 2, 5, 7, 41, 827, 19616587] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_19616587, by reduce_mod_char; decide⟩

lemma prime_26003074547138051063 : Nat.Prime 26003074547138051063 := by
  apply certify (5 : ZMod 26003074547138051063) [2, 7, 9973, 186239092314521] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_186239092314521, by reduce_mod_char; decide⟩

lemma prime_4669516433332080193964896543490122829 : Nat.Prime 4669516433332080193964896543490122829 := by
  apply certify (2 : ZMod 4669516433332080193964896543490122829) [2, 2, 7, 83, 149, 518590808381, 26003074547138051063] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_518590808381, by reduce_mod_char; decide⟩
  · exact ⟨prime_26003074547138051063, by reduce_mod_char; decide⟩

lemma prime_10432944231518126190458416657023933731548823182242327927044209 : Nat.Prime 10432944231518126190458416657023933731548823182242327927044209 := by
  apply certify (7 : ZMod 10432944231518126190458416657023933731548823182242327927044209) [2, 2, 2, 2, 3, 83, 22921, 24467076893433443, 4669516433332080193964896543490122829] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_22921, by reduce_mod_char; decide⟩
  · exact ⟨prime_24467076893433443, by reduce_mod_char; decide⟩
  · exact ⟨prime_4669516433332080193964896543490122829, by reduce_mod_char; decide⟩

lemma prime_15913 : Nat.Prime 15913 := by
  apply certify (5 : ZMod 15913) [2, 2, 2, 3, 3, 13, 17] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_58787 : Nat.Prime 58787 := by
  apply certify (2 : ZMod 58787) [2, 7, 13, 17, 19] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_245753 : Nat.Prime 245753 := by
  apply certify (3 : ZMod 245753) [2, 2, 2, 13, 17, 139] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_251057 : Nat.Prime 251057 := by
  apply certify (3 : ZMod 251057) [2, 2, 2, 2, 13, 17, 71] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_127529 : Nat.Prime 127529 := by
  apply certify (3 : ZMod 127529) [2, 2, 2, 19, 839] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_1530349 : Nat.Prime 1530349 := by
  apply certify (6 : ZMod 1530349) [2, 2, 3, 127529] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_127529, by reduce_mod_char; decide⟩

lemma prime_18557449 : Nat.Prime 18557449 := by
  apply certify (23 : ZMod 18557449) [2, 2, 2, 3, 7, 13, 29, 293] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_1402653058171 : Nat.Prime 1402653058171 := by
  apply certify (12 : ZMod 1402653058171) [2, 3, 5, 7, 13, 199, 263, 9817] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_17146111 : Nat.Prime 17146111 := by
  apply certify (3 : ZMod 17146111) [2, 3, 5, 521, 1097] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_1924513790863 : Nat.Prime 1924513790863 := by
  apply certify (3 : ZMod 1924513790863) [2, 3, 13, 1439, 17146111] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_17146111, by reduce_mod_char; decide⟩

lemma prime_1900543 : Nat.Prime 1900543 := by
  apply certify (3 : ZMod 1900543) [2, 3, 7, 37, 1223] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_281420912955937 : Nat.Prime 281420912955937 := by
  apply certify (5 : ZMod 281420912955937) [2, 2, 2, 2, 2, 3, 13, 59, 2011, 1900543] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_1900543, by reduce_mod_char; decide⟩

lemma prime_57943 : Nat.Prime 57943 := by
  apply certify (5 : ZMod 57943) [2, 3, 3, 3, 29, 37] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_6702423024329 : Nat.Prime 6702423024329 := by
  apply certify (3 : ZMod 6702423024329) [2, 2, 2, 2467, 5861, 57943] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_57943, by reduce_mod_char; decide⟩

lemma prime_87828551310807217 : Nat.Prime 87828551310807217 := by
  apply certify (15 : ZMod 87828551310807217) [2, 2, 2, 2, 3, 3, 7, 13, 6702423024329] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_6702423024329, by reduce_mod_char; decide⟩

lemma prime_46567 : Nat.Prime 46567 := by
  apply certify (3 : ZMod 46567) [2, 3, 3, 13, 199] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_13331 : Nat.Prime 13331 := by
  apply certify (2 : ZMod 13331) [2, 5, 31, 43] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_418007 : Nat.Prime 418007 := by
  apply certify (5 : ZMod 418007) [2, 29, 7207] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_2508043 : Nat.Prime 2508043 := by
  apply certify (2 : ZMod 2508043) [2, 3, 418007] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_418007, by reduce_mod_char; decide⟩

lemma prime_66869442467 : Nat.Prime 66869442467 := by
  apply certify (2 : ZMod 66869442467) [2, 13331, 2508043] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_13331, by reduce_mod_char; decide⟩
  · exact ⟨prime_2508043, by reduce_mod_char; decide⟩

lemma prime_2024041062784512851 : Nat.Prime 2024041062784512851 := by
  apply certify (6 : ZMod 2024041062784512851) [2, 5, 5, 13, 46567, 66869442467] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_46567, by reduce_mod_char; decide⟩
  · exact ⟨prime_66869442467, by reduce_mod_char; decide⟩

lemma prime_46153 : Nat.Prime 46153 := by
  apply certify (5 : ZMod 46153) [2, 2, 2, 3, 3, 641] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_276919 : Nat.Prime 276919 := by
  apply certify (11 : ZMod 276919) [2, 3, 46153] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_46153, by reduce_mod_char; decide⟩

lemma prime_892073200291369 : Nat.Prime 892073200291369 := by
  apply certify (11 : ZMod 892073200291369) [2, 2, 2, 3, 23, 1721, 3391, 276919] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_276919, by reduce_mod_char; decide⟩

lemma prime_14346217726594562459197 : Nat.Prime 14346217726594562459197 := by
  apply certify (17 : ZMod 14346217726594562459197) [2, 2, 3, 3, 7, 13, 4909, 892073200291369] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_892073200291369, by reduce_mod_char; decide⟩

lemma prime_80107 : Nat.Prime 80107 := by
  apply certify (2 : ZMod 80107) [2, 3, 13, 13, 79] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_13313 : Nat.Prime 13313 := by
  apply certify (3 : ZMod 13313) [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 13] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_26627 : Nat.Prime 26627 := by
  apply certify (2 : ZMod 26627) [2, 13313] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_13313, by reduce_mod_char; decide⟩

lemma prime_159763 : Nat.Prime 159763 := by
  apply certify (2 : ZMod 159763) [2, 3, 26627] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_26627, by reduce_mod_char; decide⟩

lemma prime_831975408281 : Nat.Prime 831975408281 := by
  apply certify (3 : ZMod 831975408281) [2, 2, 2, 5, 101, 1289, 159763] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_159763, by reduce_mod_char; decide⟩

lemma prime_5590874743648321 : Nat.Prime 5590874743648321 := by
  apply certify (11 : ZMod 5590874743648321) [2, 2, 2, 2, 2, 2, 3, 5, 7, 831975408281] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_831975408281, by reduce_mod_char; decide⟩

lemma prime_6730563356028044964614717 : Nat.Prime 6730563356028044964614717 := by
  apply certify (2 : ZMod 6730563356028044964614717) [2, 2, 13, 17, 17, 80107, 5590874743648321] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_80107, by reduce_mod_char; decide⟩
  · exact ⟨prime_5590874743648321, by reduce_mod_char; decide⟩

lemma prime_1631023 : Nat.Prime 1631023 := by
  apply certify (5 : ZMod 1631023) [2, 3, 23, 53, 223] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_48930691 : Nat.Prime 48930691 := by
  apply certify (10 : ZMod 48930691) [2, 3, 5, 1631023] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_1631023, by reduce_mod_char; decide⟩

lemma prime_11971 : Nat.Prime 11971 := by
  apply certify (10 : ZMod 11971) [2, 3, 3, 5, 7, 19] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_98993 : Nat.Prime 98993 := by
  apply certify (3 : ZMod 98993) [2, 2, 2, 2, 23, 269] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_201549749 : Nat.Prime 201549749 := by
  apply certify (2 : ZMod 201549749) [2, 2, 509, 98993] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_98993, by reduce_mod_char; decide⟩

lemma prime_808571116422079597 : Nat.Prime 808571116422079597 := by
  apply certify (5 : ZMod 808571116422079597) [2, 2, 3, 3, 3, 29, 107, 11971, 201549749] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_11971, by reduce_mod_char; decide⟩
  · exact ⟨prime_201549749, by reduce_mod_char; decide⟩

lemma prime_18515925534213339494282994637 : Nat.Prime 18515925534213339494282994637 := by
  apply certify (2 : ZMod 18515925534213339494282994637) [2, 2, 3, 3, 13, 48930691, 808571116422079597] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_48930691, by reduce_mod_char; decide⟩
  · exact ⟨prime_808571116422079597, by reduce_mod_char; decide⟩

lemma prime_13423877 : Nat.Prime 13423877 := by
  apply certify (2 : ZMod 13423877) [2, 2, 401, 8369] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_6221977 : Nat.Prime 6221977 := by
  apply certify (5 : ZMod 6221977) [2, 2, 2, 3, 131, 1979] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_14909173 : Nat.Prime 14909173 := by
  apply certify (6 : ZMod 14909173) [2, 2, 3, 1061, 1171] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_89455039 : Nat.Prime 89455039 := by
  apply certify (3 : ZMod 89455039) [2, 3, 14909173] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_14909173, by reduce_mod_char; decide⟩

lemma prime_2683651171 : Nat.Prime 2683651171 := by
  apply certify (2 : ZMod 2683651171) [2, 3, 5, 89455039] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_89455039, by reduce_mod_char; decide⟩

lemma prime_5510213234455072111 : Nat.Prime 5510213234455072111 := by
  apply certify (13 : ZMod 5510213234455072111) [2, 3, 5, 11, 6221977, 2683651171] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_6221977, by reduce_mod_char; decide⟩
  · exact ⟨prime_2683651171, by reduce_mod_char; decide⟩

lemma prime_1557775024247223873930732947821 : Nat.Prime 1557775024247223873930732947821 := by
  apply certify (6 : ZMod 1557775024247223873930732947821) [2, 2, 3, 3, 3, 3, 5, 13, 13423877, 5510213234455072111] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_13423877, by reduce_mod_char; decide⟩
  · exact ⟨prime_5510213234455072111, by reduce_mod_char; decide⟩

lemma prime_12944257 : Nat.Prime 12944257 := by
  apply certify (5 : ZMod 12944257) [2, 2, 2, 2, 2, 2, 2, 3, 13, 2593] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_1993415579 : Nat.Prime 1993415579 := by
  apply certify (2 : ZMod 1993415579) [2, 7, 11, 12944257] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_12944257, by reduce_mod_char; decide⟩

lemma prime_6215467 : Nat.Prime 6215467 := by
  apply certify (2 : ZMod 6215467) [2, 3, 953, 1087] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_335697372671 : Nat.Prime 335697372671 := by
  apply certify (13 : ZMod 335697372671) [2, 5, 11, 491, 6215467] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_6215467, by reduce_mod_char; decide⟩

lemma prime_134597 : Nat.Prime 134597 := by
  apply certify (3 : ZMod 134597) [2, 2, 7, 11, 19, 23] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_84121 : Nat.Prime 84121 := by
  apply certify (13 : ZMod 84121) [2, 2, 2, 3, 5, 701] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_504727 : Nat.Prime 504727 := by
  apply certify (13 : ZMod 504727) [2, 3, 84121] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_84121, by reduce_mod_char; decide⟩

lemma prime_8075633 : Nat.Prime 8075633 := by
  apply certify (3 : ZMod 8075633) [2, 2, 2, 2, 504727] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_504727, by reduce_mod_char; decide⟩

lemma prime_4791301937363609 : Nat.Prime 4791301937363609 := by
  apply certify (3 : ZMod 4791301937363609) [2, 2, 2, 19, 29, 134597, 8075633] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_134597, by reduce_mod_char; decide⟩
  · exact ⟨prime_8075633, by reduce_mod_char; decide⟩

lemma prime_200099407444133736898476769702780335780863053 : Nat.Prime 200099407444133736898476769702780335780863053 := by
  apply certify (2 : ZMod 200099407444133736898476769702780335780863053) [2, 2, 3, 7, 13, 67, 853, 1993415579, 335697372671, 4791301937363609] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_1993415579, by reduce_mod_char; decide⟩
  · exact ⟨prime_335697372671, by reduce_mod_char; decide⟩
  · exact ⟨prime_4791301937363609, by reduce_mod_char; decide⟩

lemma prime_124579813 : Nat.Prime 124579813 := by
  apply certify (2 : ZMod 124579813) [2, 2, 3, 7, 41, 61, 593] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_5730671399 : Nat.Prime 5730671399 := by
  apply certify (13 : ZMod 5730671399) [2, 23, 124579813] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_124579813, by reduce_mod_char; decide⟩

lemma prime_45845371193 : Nat.Prime 45845371193 := by
  apply certify (3 : ZMod 45845371193) [2, 2, 2, 5730671399] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_5730671399, by reduce_mod_char; decide⟩

lemma prime_385376190248359 : Nat.Prime 385376190248359 := by
  apply certify (6 : ZMod 385376190248359) [2, 3, 3, 467, 45845371193] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_45845371193, by reduce_mod_char; decide⟩

lemma prime_23629 : Nat.Prime 23629 := by
  apply certify (2 : ZMod 23629) [2, 2, 3, 11, 179] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩

lemma prime_12995951 : Nat.Prime 12995951 := by
  apply certify (11 : ZMod 12995951) [2, 5, 5, 11, 23629] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_23629, by reduce_mod_char; decide⟩

lemma prime_45928080712531 : Nat.Prime 45928080712531 := by
  apply certify (2 : ZMod 45928080712531) [2, 3, 3, 3, 3, 5, 4363, 12995951] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_12995951, by reduce_mod_char; decide⟩

lemma prime_1138924545509343739 : Nat.Prime 1138924545509343739 := by
  apply certify (3 : ZMod 1138924545509343739) [2, 3, 4133, 45928080712531] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_45928080712531, by reduce_mod_char; decide⟩

lemma prime_26698669195830035929639 : Nat.Prime 26698669195830035929639 := by
  apply certify (3 : ZMod 26698669195830035929639) [2, 3, 3907, 1138924545509343739] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_1138924545509343739, by reduce_mod_char; decide⟩

lemma prime_346925561398998693363198745164754923736919 : Nat.Prime 346925561398998693363198745164754923736919 := by
  apply certify (7 : ZMod 346925561398998693363198745164754923736919) [2, 23, 733, 385376190248359, 26698669195830035929639] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_385376190248359, by reduce_mod_char; decide⟩
  · exact ⟨prime_26698669195830035929639, by reduce_mod_char; decide⟩

lemma prime_5682640695715598597289195445798685650810733221 : Nat.Prime 5682640695715598597289195445798685650810733221 := by
  apply certify (2 : ZMod 5682640695715598597289195445798685650810733221) [2, 2, 3, 3, 5, 7, 13, 346925561398998693363198745164754923736919] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_346925561398998693363198745164754923736919, by reduce_mod_char; decide⟩

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 8192 in
lemma prime_3610674520568329405459071335304556918624821560331986013888631685758611388122113301633101835921047025427043478640629387386415503713486773922388609062634694203854853166695692495595837056285464730809495964484508839337484703281179717890621735258296719450661702077441654855948085900910899941664480583529973080757464941119429914486420618493798744201 : Nat.Prime 3610674520568329405459071335304556918624821560331986013888631685758611388122113301633101835921047025427043478640629387386415503713486773922388609062634694203854853166695692495595837056285464730809495964484508839337484703281179717890621735258296719450661702077441654855948085900910899941664480583529973080757464941119429914486420618493798744201 := by
  apply certify (19 : ZMod 3610674520568329405459071335304556918624821560331986013888631685758611388122113301633101835921047025427043478640629387386415503713486773922388609062634694203854853166695692495595837056285464730809495964484508839337484703281179717890621735258296719450661702077441654855948085900910899941664480583529973080757464941119429914486420618493798744201) [2, 2, 2, 3, 3, 5, 5, 7, 13, 13, 17, 29, 53, 157, 313, 397, 1483, 1873, 3499, 6007, 8269, 9829, 15913, 58787, 245753, 251057, 1530349, 18557449, 1402653058171, 1924513790863, 281420912955937, 87828551310807217, 2024041062784512851, 14346217726594562459197, 6730563356028044964614717, 18515925534213339494282994637, 1557775024247223873930732947821, 200099407444133736898476769702780335780863053, 5682640695715598597289195445798685650810733221] (by decide) (by reduce_mod_char)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨by norm_num, by reduce_mod_char; decide⟩
  · exact ⟨prime_15913, by reduce_mod_char; decide⟩
  · exact ⟨prime_58787, by reduce_mod_char; decide⟩
  · exact ⟨prime_245753, by reduce_mod_char; decide⟩
  · exact ⟨prime_251057, by reduce_mod_char; decide⟩
  · exact ⟨prime_1530349, by reduce_mod_char; decide⟩
  · exact ⟨prime_18557449, by reduce_mod_char; decide⟩
  · exact ⟨prime_1402653058171, by reduce_mod_char; decide⟩
  · exact ⟨prime_1924513790863, by reduce_mod_char; decide⟩
  · exact ⟨prime_281420912955937, by reduce_mod_char; decide⟩
  · exact ⟨prime_87828551310807217, by reduce_mod_char; decide⟩
  · exact ⟨prime_2024041062784512851, by reduce_mod_char; decide⟩
  · exact ⟨prime_14346217726594562459197, by reduce_mod_char; decide⟩
  · exact ⟨prime_6730563356028044964614717, by reduce_mod_char; decide⟩
  · exact ⟨prime_18515925534213339494282994637, by reduce_mod_char; decide⟩
  · exact ⟨prime_1557775024247223873930732947821, by reduce_mod_char; decide⟩
  · exact ⟨prime_200099407444133736898476769702780335780863053, by reduce_mod_char; decide⟩
  · exact ⟨prime_5682640695715598597289195445798685650810733221, by reduce_mod_char; decide⟩

theorem tenth_term_prime : Nat.Prime (a 10) := by
  exact prime_10432944231518126190458416657023933731548823182242327927044209

theorem first_four_indices (n : ℕ) (hn : 1 ≤ n) (hsmall : n ≤ 4) (hp : Nat.Prime (a n)) :
    Nat.Prime ((a n ^ a n + 1) / (a n + 1)) := by
  have h : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases h with rfl | rfl | rfl | rfl
  · exact (Nat.not_prime_one hp).elim
  · exact (by norm_num : Nat.Prime 7)
  · exact (by norm_num : Nat.Prime 521)
  · exact prime_45957792327018709121

theorem composite_indices_six_to_nine {n : ℕ} (hl : 6 ≤ n) (hu : n ≤ 9) :
    ¬ Nat.Prime (a n) := by
  have h : n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> intro hp
  · have hd : 37 ∣ a 6 := Nat.dvd_of_mod_eq_zero (by decide)
    have h := (Nat.dvd_prime hp).mp hd
    rcases h with h | h <;> exact (by decide : 37 ≠ _) h
  · have hd : 5 ∣ a 7 := Nat.dvd_of_mod_eq_zero (by decide)
    have h := (Nat.dvd_prime hp).mp hd
    rcases h with h | h <;> exact (by decide : 5 ≠ _) h
  · have hd : 41 ∣ a 8 := Nat.dvd_of_mod_eq_zero (by decide)
    have h := (Nat.dvd_prime hp).mp hd
    rcases h with h | h <;> exact (by decide : 41 ≠ _) h
  · have hd : 482743365352513 ∣ a 9 := Nat.dvd_of_mod_eq_zero (by decide)
    have h := (Nat.dvd_prime hp).mp hd
    rcases h with h | h <;> exact (by decide : 482743365352513 ≠ _) h

theorem first_nine_indices (n : ℕ) (hn : 1 ≤ n) (hsmall : n ≤ 9) (hp : Nat.Prime (a n)) :
    Nat.Prime ((a n ^ a n + 1) / (a n + 1)) := by
  by_cases h : n ≤ 4
  · exact first_four_indices n hn h hp
  by_cases h5 : n = 5
  · subst n
    exact prime_3610674520568329405459071335304556918624821560331986013888631685758611388122113301633101835921047025427043478640629387386415503713486773922388609062634694203854853166695692495595837056285464730809495964484508839337484703281179717890621735258296719450661702077441654855948085900910899941664480583529973080757464941119429914486420618493798744201
  · exact (composite_indices_six_to_nine (by omega) hsmall hp).elim

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a394410.main := by
  intro htenth hlater n hn hp
  by_cases hs : n ≤ 9
  · exact first_nine_indices n hn hs hp
  by_cases ht : n = 10
  · subst n
    exact htenth
  have ho : Odd (a n) := by
    cases n with
    | zero => omega
    | succ n => exact odd_at_positive_index n
  exact prime_of_progression_test hp ho (hlater n (by omega) hp)

end OMA.R_oeis_a394410_R1
