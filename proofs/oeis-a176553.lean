import OMAStatements.S_oeis_a176553
import Mathlib

namespace OMA.A176553

open OMA.S_oeis_a176553

/-- Integer version of the Loeschian form. -/
def IsL (n : ℤ) : Prop := ∃ x y : ℤ, n = x ^ 2 + x * y + y ^ 2

theorem IsL.mul {a b : ℤ} (ha : IsL a) (hb : IsL b) : IsL (a * b) := by
  obtain ⟨x, y, rfl⟩ := ha
  obtain ⟨u, v, rfl⟩ := hb
  exact ⟨x * u - y * v, x * v + y * u + y * v, by ring⟩

theorem IsL.sq (a : ℤ) : IsL (a ^ 2) := ⟨a, 0, by ring⟩

theorem IsL.three : IsL 3 := ⟨1, 1, by norm_num⟩

theorem IsL.pow {a : ℤ} (ha : IsL a) (n : ℕ) : IsL (a ^ n) := by
  induction n with
  | zero => exact ⟨1, 0, by norm_num⟩
  | succ n ih => rw [pow_succ]; exact ih.mul ha

theorem isL_to_nat {m : ℕ} (h : IsL (m : ℤ)) : IsLoeschian m := by
  obtain ⟨x, y, h⟩ := h
  have key : ∀ a b : ℤ, 0 ≤ a → 0 ≤ b → (m : ℤ) = a ^ 2 + a * b + b ^ 2 →
      IsLoeschian m := by
    intro a b ha hb hab
    refine ⟨a.toNat, b.toNat, ?_⟩
    have h1 : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha
    have h2 : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb
    have : (m : ℤ) = ((a.toNat ^ 2 + a.toNat * b.toNat + b.toNat ^ 2 : ℕ) : ℤ) := by
      push_cast; rw [h1, h2]; exact hab
    exact_mod_cast this
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · exact key x y hx hy h
  · rcases le_total (-y) x with hxy | hxy
    · exact key (x + y) (-y) (by linarith) (by linarith) (by rw [h]; ring)
    · exact key x (-y - x) hx (by linarith) (by rw [h]; ring)
  · rcases le_total (-x) y with hxy | hxy
    · exact key (x + y) (-x) (by linarith) (by linarith) (by rw [h]; ring)
    · exact key y (-x - y) hy (by linarith) (by rw [h]; ring)
  · exact key (-x) (-y) (by linarith) (by linarith) (by rw [h]; ring)

theorem exists_root (p : ℕ) [Fact p.Prime] (h : p % 3 = 1) :
    ∃ z : ZMod p, z ^ 2 + z + 1 = 0 := by
  have h3 : 3 ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]; omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 3 h3
  have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by rintro rfl; simp at hg
  refine ⟨(g : ZMod p), ?_⟩
  have h1 : ((g : ZMod p) - 1) * ((g : ZMod p) ^ 2 + g + 1) = 0 := by
    have : ((g ^ 3 : (ZMod p)ˣ) : ZMod p) = 1 := by rw [hg3]; rfl
    push_cast at this
    linear_combination this
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exfalso; apply hg1; ext; exact sub_eq_zero.1 h2
  · exact h2

theorem prime_isL (p : ℕ) (hp : p.Prime) (h : p % 3 = 1) : IsL (p : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_root p h
  obtain ⟨k, hk⟩ : ∃ k, k = Nat.sqrt p := ⟨_, rfl⟩
  have hk1 : p < (k + 1) * (k + 1) := by rw [hk]; exact Nat.lt_succ_sqrt p
  have hk2 : k * k ≤ p := by rw [hk]; exact Nat.sqrt_le p
  have hk3 : k * k ≠ p := by
    intro e
    have hkp : k ∣ p := ⟨k, e.symm⟩
    have h2 := hp.two_le
    rcases (Nat.dvd_prime hp).1 hkp with h1 | h1
    · rw [h1] at e; omega
    · rw [h1] at e; nlinarith
  have hcard : Fintype.card (ZMod p) < Fintype.card (Fin (k + 1) × Fin (k + 1)) := by
    rw [ZMod.card, Fintype.card_prod, Fintype.card_fin]; exact hk1
  obtain ⟨⟨a, b⟩, ⟨c, d⟩, hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun ab : Fin (k + 1) × Fin (k + 1) =>
      ((ab.1.val : ℕ) : ZMod p) - z * ((ab.2.val : ℕ) : ZMod p)) hcard
  simp only at hf
  obtain ⟨x, hx⟩ : ∃ x : ℤ, x = (a.val : ℤ) - c.val := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℤ, y = (b.val : ℤ) - d.val := ⟨_, rfl⟩
  have hxz : ((x : ℤ) : ZMod p) = z * ((y : ℤ) : ZMod p) := by
    rw [hx, hy]; push_cast; linear_combination hf
  have hN : (((x ^ 2 + x * y + y ^ 2 : ℤ)) : ZMod p) = 0 := by
    push_cast; rw [hxz]; linear_combination ((y : ℤ) : ZMod p) ^ 2 * hz
  have hdvd : (p : ℤ) ∣ x ^ 2 + x * y + y ^ 2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hN
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hne
    have h1 : a = c := Fin.ext (by omega)
    have h2 : b = d := Fin.ext (by omega)
    rw [h1, h2]
  have hx2 : x ^ 2 ≤ (k : ℤ) ^ 2 := by
    have h1 : -(k : ℤ) ≤ x := by omega
    have h2 : x ≤ k := by omega
    nlinarith
  have hy2 : y ^ 2 ≤ (k : ℤ) ^ 2 := by
    have h1 : -(k : ℤ) ≤ y := by omega
    have h2 : y ≤ k := by omega
    nlinarith
  have hkp : (k : ℤ) ^ 2 < p := by
    have : k * k < p := lt_of_le_of_ne hk2 hk3
    have : ((k * k : ℕ) : ℤ) < p := by exact_mod_cast this
    push_cast at this
    nlinarith
  have hpos : 0 < x ^ 2 + x * y + y ^ 2 := by
    rcases hxy with h0 | h0
    · have : 0 < x ^ 2 := by positivity
      nlinarith [sq_nonneg (x + 2 * y)]
    · have : 0 < y ^ 2 := by positivity
      nlinarith [sq_nonneg (2 * x + y)]
  have hlt : x ^ 2 + x * y + y ^ 2 < 3 * p := by
    nlinarith [sq_nonneg (x - y)]
  obtain ⟨c', hc'⟩ := hdvd
  have hppos : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hc1 : 0 < c' := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have hc3 : c' < 3 := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have hcc : c' = 1 ∨ c' = 2 := by omega
  rcases hcc with rfl | rfl
  · exact ⟨x, y, by linarith⟩
  · exfalso
    have hpodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h2 | h2
      · omega
      · exact h2
    rcases Int.even_or_odd' x with ⟨s, rfl | rfl⟩ <;>
      rcases Int.even_or_odd' y with ⟨t, rfl | rfl⟩
    · have : (p : ℤ) = 2 * (s ^ 2 + s * t + t ^ 2) := by linarith
      obtain ⟨T, hT⟩ : ∃ T, T = s ^ 2 + s * t + t ^ 2 := ⟨_, rfl⟩
      rw [← hT] at this
      omega
    · have : (p : ℤ) * 2 = 2 * (2 * s ^ 2 + 2 * s * t + s + 2 * t ^ 2 + 2 * t) + 1 := by
        rw [← hc']; ring
      obtain ⟨T, hT⟩ : ∃ T, T = 2 * s ^ 2 + 2 * s * t + s + 2 * t ^ 2 + 2 * t := ⟨_, rfl⟩
      rw [← hT] at this
      omega
    · have : (p : ℤ) * 2 = 2 * (2 * s ^ 2 + 2 * s * t + 2 * s + 2 * t ^ 2 + t) + 1 := by
        rw [← hc']; ring
      obtain ⟨T, hT⟩ : ∃ T, T = 2 * s ^ 2 + 2 * s * t + 2 * s + 2 * t ^ 2 + t := ⟨_, rfl⟩
      rw [← hT] at this
      omega
    · have : (p : ℤ) * 2 =
          2 * (2 * s ^ 2 + 2 * s * t + 3 * s + 2 * t ^ 2 + 3 * t + 1) + 1 := by
        rw [← hc']; ring
      obtain ⟨T, hT⟩ : ∃ T, T = 2 * s ^ 2 + 2 * s * t + 3 * s + 2 * t ^ 2 + 3 * t + 1 :=
        ⟨_, rfl⟩
      rw [← hT] at this
      omega

theorem sum_mod3 (q : ℕ) (hq : q % 3 = 2) (n : ℕ) :
    (∑ k ∈ Finset.range (2 * n), q ^ k) % 3 = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ]
    have h3 : 3 ∣ 1 + q := by omega
    have he : q ^ (2 * n) + q ^ (2 * n + 1) = q ^ (2 * n) * (1 + q) := by ring
    have hd : 3 ∣ q ^ (2 * n) + q ^ (2 * n + 1) := by
      rw [he]; exact Dvd.dvd.mul_left h3 _
    omega

theorem primepow_isL (q e : ℕ) (hq : q.Prime)
    (hs : ¬ 3 ∣ ArithmeticFunction.sigma 1 (q ^ e)) : IsL ((q ^ e : ℕ) : ℤ) := by
  push_cast
  have hq3 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases hq3 with h | h | h
  · have h3 : q = 3 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 (Nat.dvd_of_mod_eq_zero h)).symm
    subst h3
    exact IsL.three.pow e
  · exact (prime_isL q hq h).pow e
  · rcases Nat.even_or_odd' e with ⟨n, rfl | rfl⟩
    · rw [mul_comm, pow_mul]; exact IsL.sq _
    · exfalso
      apply hs
      rw [ArithmeticFunction.sigma_one_apply_prime_pow hq]
      exact Nat.dvd_of_mod_eq_zero (sum_mod3 q h (n + 1))

theorem sigma_isL : ∀ m : ℕ, 0 < m → ¬ 3 ∣ ArithmeticFunction.sigma 1 m → IsL (m : ℤ) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hs
    rcases Nat.lt_or_ge m 2 with h | h
    · have h1 : m = 1 := by omega
      subst h1
      exact ⟨1, 0, by norm_num⟩
    · obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
      obtain ⟨e, m', hm', hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' q hq.ne_one
      have he : e ≠ 0 := by
        intro he
        subst he
        rw [pow_zero, one_mul] at hmeq
        subst hmeq
        exact hm' hqm
      have hcop : Nat.Coprime (q ^ e) m' :=
        Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hq).2 hm')
      have hmul : ArithmeticFunction.sigma 1 (q ^ e * m') =
          ArithmeticFunction.sigma 1 (q ^ e) * ArithmeticFunction.sigma 1 m' :=
        ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
      rw [hmeq, hmul] at hs
      have hs1 : ¬ 3 ∣ ArithmeticFunction.sigma 1 (q ^ e) :=
        fun hh => hs (Dvd.dvd.mul_right hh _)
      have hs2 : ¬ 3 ∣ ArithmeticFunction.sigma 1 m' :=
        fun hh => hs (Dvd.dvd.mul_left hh _)
      have hm'pos : 0 < m' := by
        rcases Nat.eq_zero_or_pos m' with h0 | h0
        · rw [h0, mul_zero] at hmeq; omega
        · exact h0
      have hqe : 1 < q ^ e := Nat.one_lt_pow he hq.one_lt
      have hlt : m' < m := by rw [hmeq]; nlinarith
      have h1 := primepow_isL q e hq hs1
      have h2 := ih m' hlt hm'pos hs2
      have h3 := h1.mul h2
      rw [hmeq]
      push_cast at h3 ⊢
      exact h3

theorem flat_sum_mod3 (L : List ℕ) :
    ((L.flatMap (fun d => (Nat.digits 10 d).reverse)).reverse).sum ≡ L.sum [MOD 3] := by
  rw [List.sum_reverse]
  induction L with
  | nil => simp [Nat.ModEq]
  | cons a L ih =>
    simp only [List.flatMap_cons, List.sum_append, List.sum_cons, List.sum_reverse]
    exact Nat.ModEq.add (Nat.modEq_three_digits_sum a).symm ih

theorem divConcat_modEq (m : ℕ) (hm : 0 < m) :
    divConcat m ≡ ArithmeticFunction.sigma 1 m [MOD 3] := by
  unfold divConcat
  simp only
  refine (Nat.ofDigits_modEq 10 3 _).trans ?_
  rw [show 10 % 3 = 1 from rfl, Nat.ofDigits_one]
  refine (flat_sum_mod3 _).trans ?_
  rw [ArithmeticFunction.sigma_one_apply]
  have hnd : ((List.range (m + 1)).filter (fun d => decide (1 ≤ d ∧ d ∣ m))).Nodup :=
    List.Nodup.filter _ List.nodup_range
  have hsum := List.sum_toFinset (fun d : ℕ => d) hnd
  rw [List.map_id'] at hsum
  rw [← hsum]
  have hset : ((List.range (m + 1)).filter (fun d => decide (1 ≤ d ∧ d ∣ m))).toFinset =
      m.divisors := by
    ext d
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq,
      Nat.mem_divisors]
    constructor
    · rintro ⟨_, _, hd⟩
      exact ⟨hd, hm.ne'⟩
    · rintro ⟨hd, _⟩
      exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd hm hd), Nat.pos_of_dvd_of_pos hd hm, hd⟩
  rw [hset]

theorem le_divConcat (m : ℕ) (hm : 0 < m) : m ≤ divConcat m := by
  unfold divConcat
  simp only [List.range_succ, List.filter_append, List.flatMap_append, List.reverse_append]
  have hf : List.filter (fun d => decide (1 ≤ d ∧ d ∣ m)) [m] = [m] := by
    simp; omega
  rw [hf]
  simp [Nat.ofDigits_append, Nat.ofDigits_digits]

theorem divConcat_two : divConcat 2 = 12 := by
  norm_num [divConcat, List.range_succ, List.filter_cons, Nat.ofDigits_cons]

end OMA.A176553

open OMA.A176553 OMA.S_oeis_a176553 in
theorem OMA.solution : type_of% @OMA.S_oeis_a176553.main := by
  intro m hm h
  apply isL_to_nat
  apply sigma_isL m hm
  intro h3
  have hmod := divConcat_modEq m hm
  have hd3 : divConcat m % 3 = 0 := by
    have h4 := Nat.mod_eq_zero_of_dvd h3
    unfold Nat.ModEq at hmod
    omega
  rcases h with h1 | hp
  · omega
  · have h5 : divConcat m = 3 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero hd3)).symm
    have hle := le_divConcat m hm
    have hcases : m = 1 ∨ m = 2 ∨ m = 3 := by omega
    rcases hcases with rfl | rfl | rfl
    · simp at h3
    · rw [divConcat_two] at h5; omega
    · have : ArithmeticFunction.sigma 1 3 = 4 := by
        rw [ArithmeticFunction.sigma_one_apply, Nat.Prime.divisors Nat.prime_three]; rfl
      rw [this] at h3; omega
