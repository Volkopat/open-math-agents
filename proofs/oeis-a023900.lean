import OMAStatements.S_oeis_a023900
import Mathlib

namespace A023900

open OMA.S_oeis_a023900

lemma min_sum (q : ℕ) :
    ∑ k ∈ Finset.range (2 * q + 1), min (k + 1) (2 * q - k) = q * (q + 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have e : 2 * (q + 1) + 1 = (2 * q + 1) + 1 + 1 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ']
    have h : ∀ k ∈ Finset.range (2 * q + 1),
        min (k + 1 + 1) (2 * (q + 1) - (k + 1)) = min (k + 1) (2 * q - k) + 1 := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      omega
    have m1 : min (0 + 1) (2 * (q + 1) - 0) = 1 := by omega
    have m2 : min (2 * q + 1 + 1 + 1) (2 * (q + 1) - (2 * q + 1 + 1)) = 0 := by omega
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ih, m1, m2, Finset.sum_const,
      Finset.card_range, smul_eq_mul]
    ring

lemma total (q : ℕ) : ∑ i ∈ Finset.Icc 1 (2 * q + 1), term (2 * q + 1) i = -1 := by
  have hI : Finset.Icc 1 (2 * q + 1) = (Finset.range (2 * q + 1)).image (fun k => k + 1) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro h
      exact ⟨i - 1, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  rw [hI, Finset.sum_image (by intro x _ y _ h; exact Nat.add_right_cancel h)]
  have h : ∀ k ∈ Finset.range (2 * q + 1), term (2 * q + 1) (k + 1) =
      4 * ((min (k + 1) (2 * q - k) : ℕ) : ℤ) - (2 * (q : ℤ) + 1) := by
    intro k hk
    unfold term
    have e : 2 * q + 1 - (k + 1) = 2 * q - k := by omega
    rw [e]
    push_cast
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Nat.cast_sum, min_sum,
    Finset.sum_const, Finset.card_range]
  simp only [nsmul_eq_mul]
  push_cast
  ring

lemma term_scale (d e k : ℕ) : term (d * e) (d * k) = (d : ℤ) * term e k := by
  unfold term
  rw [← Nat.mul_sub, Nat.mul_min_mul_left]
  push_cast
  ring

lemma sieve (m : ℕ) (hm : 0 < m) (f : ℕ → ℤ) :
    ∑ i ∈ (Finset.Icc 1 m).filter (fun i => i.gcd m = 1), f i =
      ∑ d ∈ m.divisors, ArithmeticFunction.moebius d * ∑ k ∈ Finset.Icc 1 (m / d), f (d * k) := by
  have hmu : ∀ g : ℕ, ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℤ) =
      if g = 1 then 1 else 0 := by
    intro g
    have h := congrArg (fun F : ArithmeticFunction ℤ => F g)
      ArithmeticFunction.moebius_mul_coe_zeta
    simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
    exact h
  have step1 : ∀ i ∈ Finset.Icc 1 m, (if i.gcd m = 1 then f i else 0) =
      ∑ d ∈ m.divisors, (if d ∣ i then ArithmeticFunction.moebius d * f i else 0) := by
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    have hdiv : (i.gcd m).divisors = m.divisors.filter (fun d => d ∣ i) := by
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, _⟩
        exact ⟨⟨h2, by omega⟩, h1⟩
      · rintro ⟨⟨h2, _⟩, h1⟩
        exact ⟨⟨h1, h2⟩, Nat.gcd_ne_zero_right (by omega)⟩
    rw [← Finset.sum_filter, ← hdiv, ← Finset.sum_mul, hmu]
    split_ifs <;> simp
  rw [Finset.sum_filter, Finset.sum_congr rfl step1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  congr 1
  have himg : (Finset.Icc 1 m).filter (fun i => d ∣ i) =
      (Finset.Icc 1 (m / d)).image (fun k => d * k) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, k, rfl⟩
      refine ⟨k, ⟨?_, ?_⟩, rfl⟩
      · rcases k with _ | k
        · simp at h1
        · omega
      · exact (Nat.le_div_iff_mul_le hdpos).mpr (by rw [mul_comm]; exact h2)
    · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_right d k⟩
      · exact Nat.mul_pos hdpos (by omega)
      · have h3 := (Nat.le_div_iff_mul_le hdpos).mp h2
        rw [mul_comm]
        exact h3
  rw [himg, Finset.sum_image]
  intro x _ y _ hxy
  exact Nat.eq_of_mul_eq_mul_left hdpos hxy

lemma coprime_sum (m : ℕ) (hodd : Odd m) :
    ∑ i ∈ (Finset.Icc 1 m).filter (fun i => i.gcd m = 1), term m i = -(a m) := by
  have hm : 0 < m := hodd.pos
  rw [sieve m hm (term m)]
  unfold a
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  obtain ⟨e, he⟩ := (Nat.mem_divisors.mp hd).1
  have hde : m / d = e := by
    rw [he]
    exact Nat.mul_div_cancel_left e hdpos
  have hoe : Odd e := by
    rw [he] at hodd
    exact (Nat.odd_mul.mp hodd).2
  obtain ⟨q, rfl⟩ := hoe
  rw [hde]
  have h : ∀ k ∈ Finset.Icc 1 (2 * q + 1), term m (d * k) = (d : ℤ) * term (2 * q + 1) k := by
    intro k _
    rw [he]
    exact term_scale d (2 * q + 1) k
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, total q]
  ring

lemma noncoprime_sum (m : ℕ) (hodd : Odd m) :
    ∑ i ∈ (Finset.Icc 1 m).filter (fun i => 1 < i.gcd m), term m i = -1 + a m := by
  have hm : 0 < m := hodd.pos
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 m)
    (fun i => i.gcd m = 1) (term m)
  have hfilt : (Finset.Icc 1 m).filter (fun i => ¬ i.gcd m = 1) =
      (Finset.Icc 1 m).filter (fun i => 1 < i.gcd m) := by
    apply Finset.filter_congr
    intro i _
    have h1 := Nat.gcd_pos_of_pos_right i hm
    omega
  have hc := coprime_sum m hodd
  obtain ⟨q, hq⟩ := hodd
  have htot : ∑ i ∈ Finset.Icc 1 m, term m i = -1 := by
    rw [hq]
    exact total q
  rw [hfilt, hc, htot] at hsplit
  linarith

lemma a_mult (x y : ℕ) (h : Nat.Coprime x y) : a (x * y) = a x * a y := by
  have hmult : ArithmeticFunction.IsMultiplicative
      (ArithmeticFunction.pmul
        ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)
        ArithmeticFunction.moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) :=
    (ArithmeticFunction.isMultiplicative_id.natCast.pmul
      ArithmeticFunction.isMultiplicative_moebius).mul
        ArithmeticFunction.isMultiplicative_zeta.natCast
  have ha : ∀ n, a n = (ArithmeticFunction.pmul
        ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)
        ArithmeticFunction.moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) n := by
    intro n
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    unfold a
    apply Finset.sum_congr rfl
    intro d _
    simp [ArithmeticFunction.pmul_apply]
  rw [ha, ha, ha, hmult.map_mul_of_coprime h]

lemma a_two_pow (s : ℕ) : a (2 ^ (s + 1)) = -1 := by
  unfold a
  rw [Nat.sum_divisors_prime_pow Nat.prime_two, Finset.sum_range_succ', Finset.sum_range_succ']
  have h0 : ∀ x ∈ Finset.range s,
      ((2 ^ (x + 1 + 1) : ℕ) : ℤ) * ArithmeticFunction.moebius (2 ^ (x + 1 + 1)) = 0 := by
    intro x _
    rw [ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two (by omega)]
    simp
  rw [Finset.sum_eq_zero h0]
  simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two]

lemma a_even_part (s m : ℕ) (hodd : Odd m) : a (2 ^ (s + 1) * m) = -(a m) := by
  rw [a_mult _ _ (Nat.Coprime.pow_left (s + 1) (Nat.coprime_two_left.mpr hodd)), a_two_pow]
  ring

end A023900

theorem OMA.solution : type_of% @OMA.S_oeis_a023900.main := by
  intro n t m hn hodd hnm
  have hm : 0 < m := hodd.pos
  have hI := A023900.coprime_sum m hodd
  have hII := A023900.noncoprime_sum m hodd
  rcases t with _ | s
  · have hnm' : n = m := by
      rw [hnm]
      simp
    subst hnm'
    rw [if_pos rfl, if_neg (lt_irrefl _), hI, hII]
    constructor <;> ring
  · have h2 : 2 ≤ 2 ^ (s + 1) := by
      have h3 : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
      have h4 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
      omega
    have hlt : m < n := by
      rw [hnm]
      nlinarith
    rw [if_neg (show ¬ m = n by omega), if_pos hlt, hI, hII, hnm,
      A023900.a_even_part s m hodd]
    constructor <;> ring
