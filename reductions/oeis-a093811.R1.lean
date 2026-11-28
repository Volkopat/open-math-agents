import OMAStatements.S_oeis_a093811

/-!
# Digit products of divisors near powers of ten

For a divisor d of 10^k-b, put q=(10^k-b)/d. If q does not divide b, a
block of h nines in d is impossible whenever 10^h exceeds q and b. Each
disjoint block then loses a factor of 8/9. Large cofactors are controlled
instead by an Euler product for the sum of negative powers of divisors.
Together these estimates show that only cofactors dividing b contribute
to the leading asymptotic term for b=2 and b=4.

M. F. Hasler identified the dominant divisors and conjectured the two
limits in OEIS A093811 and A397260. The linear-scale limit follows David
Radcliffe's divisor-count argument from A093811.
-/

/-! Radcliffe's vanishing ratio (OEIS A093811). The divisor bound below uses
an elementary estimate on each exponent in the prime factorization. -/

namespace H093811
open OMA.S_oeis_a093811 Finset Filter
open scoped Topology

/-- Each fixed positive integral power of the divisor count is O(n). -/
private theorem divisor_subpower (h : ℕ) (hh : 0 < h) :
    ∀ n : ℕ, 0 < n → n.divisors.card^h ≤ (h^h)^(2^h)*n := by
  let D := h^h
  intro n hn
  let S := n.primeFactors
  have hlocal (p : ℕ) (hp : p ∈ S) (e : ℕ) :
      (e+1)^h ≤ (if p < 2^h then D else 1)*p^e := by
    by_cases hsmall : p < 2^h
    · rw [if_pos hsmall]
      have hpart : e+1 ≤ h*(e/h+1) := by
        have hu := Nat.mod_lt e hh
        have hd := Nat.mod_add_div e h
        rw [Nat.mul_add, Nat.mul_one]
        omega
      have hlin := hpart.trans (Nat.mul_le_mul_left h (e/h).lt_two_pow_self)
      calc
        (e+1)^h ≤ (h*2^(e/h))^h := Nat.pow_le_pow_left hlin h
        _ = D*2^(e/h*h) := by rw [mul_pow, pow_mul]
        _ ≤ D*2^e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.div_mul_le_self _ _))
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.prime_of_mem_primeFactors hp).two_le _)
    · rw [if_neg hsmall, one_mul]
      calc
        (e+1)^h ≤ (2^e)^h := Nat.pow_le_pow_left e.lt_two_pow_self h
        _ = (2^h)^e := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ ≤ p^e := Nat.pow_le_pow_left (by omega) _
  have hcard : (S.filter (· < 2^h)).card ≤ 2^h := by
    apply (card_le_card (t := range (2^h)) ?_).trans_eq (card_range _)
    exact fun p hp => mem_range.mpr (mem_filter.mp hp).2
  rw [Nat.card_divisors hn.ne', ← prod_pow]
  calc
    _ ≤ ∏ p ∈ S, (if p < 2^h then D else 1)*p^(n.factorization p) :=
      prod_le_prod' fun p hp => hlocal p hp _
    _ = (∏ p ∈ S, if p < 2^h then D else 1)*n := by
      rw [prod_mul_distrib]
      exact congrArg (_ * ·) (Nat.prod_primeFactors_pow_factorization hn.ne').symm
    _ ≤ _ := by
      rw [← Finset.prod_filter, Finset.prod_const]
      exact Nat.mul_le_mul_right n (Nat.pow_le_pow_right (pow_pos hh _) hcard)

private theorem power_from_divisors (K : ℕ)
    (hK : ∀ n : ℕ, 0 < n → n.divisors.card^50 ≤ K*n) :
    ∀ n : ℕ, 0 < n → (digitProductSum n)^50 ≤ (K*10^48)*n^49 := by
  intro n hn
  let L := (Nat.digits 10 n).length
  have hsum : digitProductSum n ≤ n.divisors.card*9^L := by
    unfold digitProductSum
    apply Finset.sum_le_card_nsmul
    intro d hd
    calc
      _ ≤ 9^(Nat.digits 10 d).length :=
        List.prod_le_pow_card _ _ fun a ha => Nat.le_of_lt_succ (Nat.digits_lt_base (by decide : 1<10) ha)
      _ ≤ 9^L := Nat.pow_le_pow_right (by decide) (Nat.le_length_digits_le _ _ _ (Nat.divisor_le hd))
  have hd : (9^L)^50 ≤ (10*n)^48 := by
    calc
      _ = (9^50)^L := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ (10^48)^L := Nat.pow_le_pow_left (by decide : 9^50 ≤ 10^48) _
      _ = (10^L)^48 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ _ := Nat.pow_le_pow_left (Nat.base_pow_length_digits_le 10 n (by decide) hn.ne') _
  calc
    _ ≤ (n.divisors.card*9^L)^50 := Nat.pow_le_pow_left hsum _
    _ ≤ (K*n)*(10*n)^48 := by rw [mul_pow]; exact Nat.mul_le_mul (hK n hn) hd
    _ = _ := by ring

theorem digit_sum_power_bound (n : ℕ) (hn : 0 < n) :
    (digitProductSum n)^50 ≤ (((50:ℕ)^50)^(2^50)*10^48)*n^49 :=
  power_from_divisors _ (divisor_subpower 50 (by decide)) n hn

private theorem ratio_of_power (K : ℕ)
    (hK : ∀ n : ℕ, 0 < n → (digitProductSum n)^50 ≤ K*n^49) :
    Tendsto (fun n : ℕ => (digitProductSum n : ℝ)/n) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_gt ((K:ℝ)/ε^50)
  filter_upwards [eventually_ge_atTop (N+1)] with n hn
  have npos : 0 < n := by omega
  have hnr : 0 < (n:ℝ) := by exact_mod_cast npos
  have hlt : (K:ℝ) < (n:ℝ)*ε^50 := (div_lt_iff₀ (pow_pos hε _)).mp
    (hN.trans_le (by exact_mod_cast (show N ≤ n by omega)))
  have hpow : (digitProductSum n : ℝ)^50 ≤ (K:ℝ)*(n:ℝ)^49 := by exact_mod_cast hK n npos
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  apply (pow_lt_pow_iff_left₀ (by positivity) hε.le (by decide : 50 ≠ 0)).mp
  rw [div_pow, div_lt_iff₀ (pow_pos hnr _)]
  calc
    _ ≤ _ := hpow
    _ < ((n:ℝ)*ε^50)*(n:ℝ)^49 := mul_lt_mul_of_pos_right hlt (pow_pos hnr _)
    _ = _ := by ring

theorem ratio_limit : Tendsto (fun n : ℕ => (digitProductSum n : ℝ)/n) atTop (𝓝 0) :=
  ratio_of_power _ digit_sum_power_bound

private theorem strict_of_power {K n : ℕ} (hbound : (digitProductSum n)^50 ≤ K*n^49)
    (hn : K < n) : digitProductSum n < n := by
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have h := hbound.trans_lt (Nat.mul_lt_mul_of_pos_right hn (pow_pos hnpos 49))
  by_contra! hge
  have hle := Nat.pow_le_pow_left hge 50
  have he : n^50 = n*n^49 := by rw [show 50 = 49+1 by decide, pow_succ, Nat.mul_comm]
  exact (Nat.not_lt_of_ge hle) (he.symm ▸ h)

/-- An explicit finite cutoff for possible exceptions. -/
theorem strict_large (n : ℕ) (hn : (50^50)^(2^50)*10^48 < n) : digitProductSum n < n :=
  strict_of_power (digit_sum_power_bound n (Nat.zero_lt_of_lt hn)) hn

end H093811

namespace Hasler093811

/-- A maximal decimal block in the low k positions forces q to divide b. -/
theorem no_nines {k j h b q d : ℕ} (hj : j+h ≤ k) (hq : q < 10^h)
    (hb : b < 10^h) (hn : 10^k ∣ q*d+b) (hx : ¬q ∣ b) :
    d / 10^j % 10^h + 1 ≠ 10^h := by
  intro hmax
  let J := 10^j
  let B := 10^h
  have hJ : 0 < J := by dsimp [J]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  let t := J - d%J
  have ht : t ≤ J := Nat.sub_le _ _
  have hdecomp : d+t = ((d/J/B)+1)*(B*J) := by
    have h₁ := Nat.mod_add_div d J
    have h₂ := Nat.mod_add_div (d/J) B
    have hr := Nat.mod_lt d hJ
    change d / J % B + 1 = B at hmax
    have he : d/J + 1 = B*(d/J/B+1) := by nlinarith only [h₂,hmax]
    have hshift : d+t = J*(d/J+1) := by dsimp [t]; rw [Nat.mul_add,Nat.mul_one]; omega
    rw [hshift, he]
    ring
  have hlow : B*J ∣ q*d+b := by
    simpa [B,J,←pow_add,Nat.add_comm] using (pow_dvd_pow 10 hj).trans hn
  have hnew : B*J ∣ q*(d+t) := by
    rw [hdecomp]
    exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
  have eq : b ≡ q*t [MOD B*J] := by
    apply Nat.ModEq.add_left_cancel' (q*d)
    rw [← Nat.mul_add]
    exact hlow.modEq_zero_nat.trans hnew.modEq_zero_nat.symm
  have hbl : b < B*J := lt_of_lt_of_le hb (by simpa using Nat.mul_le_mul_left B hJ)
  have hqt : q*t < B*J :=
    (Nat.mul_le_mul_left q ht).trans_lt (Nat.mul_lt_mul_of_pos_right hq hJ)
  exact hx (eq.eq_of_lt_of_lt hbl hqt ▸ dvd_mul_right q t)

private theorem loose (h d : ℕ) : (Nat.digits 10 d).prod ≤ 9^h * (Nat.digits 10 (d/10^h)).prod := by
  induction h generalizing d with
  | zero => simp
  | succ h ih =>
    by_cases hz : d=0
    · simp [hz]
      exact (show 0 < 9^(h+1) by positivity)
    rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 10) hz, List.prod_cons]
    have H := Nat.mul_le_mul (show d%10 ≤ 9 by omega) (ih (d/10))
    simpa only [Nat.div_div_eq_div_mul, pow_succ', Nat.mul_assoc] using H

/-- One deficient block loses a factor of at least 8/9 in the digit product.
A truncated leading block satisfies the same bound. -/
private theorem deficient (h d : ℕ) (hd : d%10^h+1 ≠ 10^h) :
    (Nat.digits 10 d).prod*9 ≤ 8*9^h*(Nat.digits 10 (d/10^h)).prod := by
  induction h generalizing d with
  | zero => exact False.elim (hd (by simp [Nat.mod_one]))
  | succ h ih =>
    by_cases hz : d=0
    · have H : 0 < 9^h := by positivity
      simp [hz, pow_succ]
      omega
    rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 10) hz, List.prod_cons]
    by_cases h₉ : d%10 = 9
    · have hn : d/10%10^h+1 ≠ 10^h := by
        intro he
        apply hd
        have hr := Nat.mod_lt (d/10) (by positivity : 0 < 10^h)
        rw [pow_succ', Nat.mod_mul]
        omega
      have H := Nat.mul_le_mul_left 9 (ih (d/10) hn)
      rw [h₉]
      rw [Nat.div_div_eq_div_mul] at H
      simpa only [Nat.div_div_eq_div_mul, pow_succ'] using (by
        convert H using 1 <;> ring : (9 * (Nat.digits 10 (d/10)).prod)*9 ≤
          8*(9*9^h)*(Nat.digits 10 (d/(10*10^h))).prod)
    · have hr := Nat.mod_lt d (by decide : 0 < 10)
      have H := Nat.mul_le_mul_right 9 (Nat.mul_le_mul (show d%10 ≤ 8 by omega) (loose h (d/10)))
      rw [pow_succ']
      simpa only [Nat.div_div_eq_div_mul, pow_succ', Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using H

theorem small_cofactor {k h t b q d : ℕ} (ht : h*t ≤ k) (hq : q < 10^h)
    (hb : b < 10^h) (hn : 10^k ∣ q*d+b) (hx : ¬q ∣ b) (hd : d < 10^k) :
    (Nat.digits 10 d).prod * 9^t ≤ 8^t * 9^k := by
  have H (u : ℕ) (hu : h*u ≤ k) : (Nat.digits 10 d).prod * 9^u ≤
      8^u * 9^(h*u) * (Nat.digits 10 (d/10^(h*u))).prod := by
    induction u with
    | zero => simp
    | succ u ih =>
      rw [Nat.mul_succ] at hu ⊢
      have h₁ := ih (by omega)
      have h₂ := deficient h (d/10^(h*u)) (no_nines hu hq hb hn hx)
      rw [Nat.div_div_eq_div_mul, ← pow_add] at h₂
      calc
        _ ≤ (8^u*9^(h*u)) * ((Nat.digits 10 (d/10^(h*u))).prod*9) := by
          simpa only [pow_succ, Nat.mul_assoc] using Nat.mul_le_mul_right 9 h₁
        _ ≤ (8^u*9^(h*u)) * (8*9^h*(Nat.digits 10 (d/10^(h*u+h))).prod) :=
          Nat.mul_le_mul_left _ h₂
        _ = _ := by rw [pow_succ, pow_add]; ring
  have he : h*t+(k-h*t) = k := by omega
  have hlen : d/10^(h*t) < 10^(k-h*t) := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    simpa only [← pow_add, Nat.add_comm (k-h*t), he] using hd
  have hl := (Nat.digits_length_le_iff (by decide : 1 < 10) (d/10^(h*t))).mpr hlen
  have HH : (Nat.digits 10 (d/10^(h*t))).prod ≤ 9^(k-h*t) :=
    (List.prod_le_pow_card _ 9 (fun x hx => Nat.le_of_lt_succ (Nat.digits_lt_base (by decide : 1<10) hx))).trans
      (Nat.pow_le_pow_right (by decide) hl)
  calc
    _ ≤ _ := H t ht
    _ ≤ 8^t*9^(h*t)*9^(k-h*t) := Nat.mul_le_mul_left _ HH
    _ = _ := by rw [Nat.mul_assoc, ← pow_add, he]

end Hasler093811

namespace H093811
open Finset Filter Real
open scoped Topology ArithmeticFunction.zeta

private theorem euler_divisors {b : ℝ} (hb : 0 < b) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (d:ℝ)^(-b) =
      ∏ p ∈ n.primeFactors, ∑ i ∈ range (n.factorization p + 1), ((p:ℝ)^(-b))^i := by
  let f : ArithmeticFunction ℝ := ⟨fun x => (x:ℝ)^(-b), by simp [hb.ne']⟩
  have hf : f.IsMultiplicative := by
    refine ⟨by simp [f], fun {m n} _ => ?_⟩
    change ((m*n:ℕ):ℝ)^(-b) = (m:ℝ)^(-b)*(n:ℝ)^(-b)
    rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
  let g : ArithmeticFunction ℝ := (ArithmeticFunction.zeta : ArithmeticFunction ℕ) * f
  have hg : g.IsMultiplicative := ArithmeticFunction.isMultiplicative_zeta.natCast.mul hf
  change (∑ d ∈ n.divisors, f d) = _
  rw [← ArithmeticFunction.coe_zeta_mul_apply, hg.multiplicative_factorization _ hn]
  apply prod_congr n.support_factorization
  intro p hp
  change ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) * f) (p^_) = _
  rw [ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow (Nat.prime_of_mem_primeFactors hp)]
  apply sum_congr rfl
  intro i hi
  change ((p^i:ℕ):ℝ)^(-b) = ((p:ℝ)^(-b))^i
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity), mul_comm, Real.rpow_mul_natCast (by positivity)]

private theorem sum_prime_weights {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    ∑ p ∈ S, (p:ℝ)^(-b) ≤ ((1 + S.card:ℝ)^(1-b))/(1-b) := by
  have hs : ∑ p ∈ S, (p:ℝ)^(-b) ≤ ∑ i ∈ range S.card, (1 + ((i+1:ℕ):ℝ))^(-b) := by
    induction S using Finset.induction_on_max with
    | empty => simp
    | insert a S hmax ih =>
      have hnot : a ∉ S := fun ha => (hmax a ha).false
      have ha := hS a (mem_insert_self a S)
      have hS' := fun p (hp : p ∈ S) => hS p (mem_insert_of_mem hp)
      have hle : S.card ≤ a-2 := by
        have hsub : S ⊆ Ico 2 a := fun p hp => mem_Ico.mpr ⟨hS' p hp, hmax p hp⟩
        simpa using card_le_card hsub
      rw [sum_insert hnot, card_insert_of_notMem hnot, sum_range_succ]
      apply (add_le_add (Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 1 + ((S.card+1:ℕ):ℝ))
        (by exact_mod_cast (show 1+(S.card+1)≤a by omega)) (by linarith : -b≤0)) (ih hS')).trans_eq
      ring
  apply hs.trans
  have hanti : AntitoneOn (fun x : ℝ => x^(-b)) (Set.Icc 1 (1+S.card:ℝ)) :=
    fun _ hx _ _ hxy => Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hx.1) hxy (by linarith)
  apply hanti.sum_le_integral.trans
  rw [integral_rpow (Or.inl (by linarith : -1 < -b))]
  simp only [one_rpow, show -b+1 = 1-b by ring]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

theorem divisor_weight_bound {b : ℝ} (hb : 0 < b) (hb1 : b < 1) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (d:ℝ)^(-b) ≤
    exp ((1-(2:ℝ)^(-b))⁻¹ * ((1 + n.primeFactors.card:ℝ)^(1-b)/(1-b))) := by
  let C : ℝ := (1-(2:ℝ)^(-b))⁻¹
  have htwo : (2:ℝ)^(-b) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hC : 0 ≤ C := inv_nonneg.mpr (by linarith)
  rw [euler_divisors hb hn]
  calc
    _ ≤ ∏ p ∈ n.primeFactors, exp (C*(p:ℝ)^(-b)) := by
      apply prod_le_prod (fun _ _ => by positivity)
      intro p hp
      let x := (p:ℝ)^(-b)
      have hx : 0 ≤ x := Real.rpow_nonneg (by positivity) _
      have hx2 : x ≤ (2:ℝ)^(-b) := Real.rpow_le_rpow_of_nonpos (by norm_num)
        (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le) (by linarith)
      have hden : 0 < 1-x := by linarith
      have hCx : (1-x)⁻¹ ≤ C := by
        simpa [C, one_div] using one_div_le_one_div_of_le (by linarith : 0<1-(2:ℝ)^(-b)) (by linarith : 1-(2:ℝ)^(-b) ≤ 1-x)
      calc
        _ ≤ (1-x)⁻¹ := by
          rw [← one_div, le_div_iff₀ hden, geom_sum_mul_neg]
          exact sub_le_self _ (pow_nonneg hx _)
        _ = (1-x)⁻¹*x+1 := by field_simp; ring
        _ ≤ C*x+1 := by gcongr
        _ ≤ _ := Real.add_one_le_exp _
    _ = exp (C * ∑ p ∈ n.primeFactors, (p:ℝ)^(-b)) := by rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (sum_prime_weights hb hb1 _ fun _ hp => (Nat.prime_of_mem_primeFactors hp).two_le) hC)

theorem divisor_tail_bound {a b Q : ℝ} (hab : b ≤ a) (hb : 0 < b) (hb1 : b < 1)
    (hQ : 0 < Q) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors.filter (fun d : ℕ => Q ≤ (d:ℝ)), (d:ℝ)^(-a) ≤
    Q^(b-a) * exp ((1-(2:ℝ)^(-b))⁻¹ * ((1 + n.primeFactors.card:ℝ)^(1-b)/(1-b))) := by
  classical
  calc
    _ ≤ ∑ d ∈ n.divisors.filter (fun d : ℕ => Q ≤ (d:ℝ)), Q^(b-a)*(d:ℝ)^(-b) := by
      apply sum_le_sum
      intro d hd
      obtain ⟨hdiv,hq⟩ := mem_filter.mp hd
      have hpos : 0 < (d:ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hdiv
      calc
        _ = (d:ℝ)^(b-a)*(d:ℝ)^(-b) := by rw [← Real.rpow_add hpos]; ring_nf
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hQ hq (by linarith)) (by positivity)
    _ = Q^(b-a) * ∑ d ∈ n.divisors.filter (fun d : ℕ => Q ≤ (d:ℝ)), (d:ℝ)^(-b) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun _ _ _ => by positivity)).trans (divisor_weight_bound hb hb1 hn)) (Real.rpow_nonneg hQ.le _)


private theorem prime_card_le_four_mul {n k : ℕ} (hn : 0 < n) (hnk : n ≤ 10^k) :
    n.primeFactors.card ≤ 4*k := by
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  calc
    2^n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ n.primeFactors, p := prod_le_prod' fun _ hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
    _ ≤ 10^k := hnk
    _ ≤ (2^4)^k := Nat.pow_le_pow_left (by decide) _
    _ = _ := (pow_mul _ _ _).symm

/-- Uniform in any family of positive integers of at most exponential growth. -/
theorem large_cofactor_tail {a : ℝ} (ha : 4/5 < a) (N : ℕ → ℕ)
    (hN : ∀ᶠ k : ℕ in atTop, 0 < N k ∧ N k ≤ 10^k) :
    Tendsto (fun k : ℕ => ∑ d ∈ (N k).divisors.filter
      (fun d : ℕ => exp ((k:ℝ)^(1/3:ℝ)) ≤ (d:ℝ)), (d:ℝ)^(-a)) atTop (𝓝 0) := by
  let C : ℝ := (1-(2:ℝ)^(-(4/5:ℝ)))⁻¹
  have hC : 0 ≤ C := inv_nonneg.mpr (sub_nonneg.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ)<2) (by norm_num : -(4/5:ℝ)<0)).le)
  let c : ℝ := (a-4/5)/2
  have hc : 0 < c := by dsimp [c]; linarith
  have hsmall : ∀ᶠ k : ℕ in atTop, 25*C*(k:ℝ)^(-(2/15:ℝ)) ≤ c := by
    have hlim : Tendsto (fun k : ℕ => 25*C*(k:ℝ)^(-(2/15:ℝ))) atTop (𝓝 0) := by
      simpa using (((tendsto_rpow_neg_atTop (by norm_num : 0 < (2/15:ℝ))).comp
        tendsto_natCast_atTop_atTop).const_mul (25*C))
    exact hlim.eventually_le_const hc
  have hdecay : Tendsto (fun k : ℕ => exp (-c*(k:ℝ)^(1/3:ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (((tendsto_rpow_atTop (by norm_num : 0<(1/3:ℝ))).comp
      tendsto_natCast_atTop_atTop).const_mul_atTop_of_neg (neg_lt_zero.mpr hc))
  apply squeeze_zero' (Eventually.of_forall (fun _ => sum_nonneg fun _ _ => by positivity)) _ hdecay
  filter_upwards [hN,hsmall,eventually_ge_atTop 1] with k hnk hsmall hk
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : 0 < (k:ℝ) := by linarith
  have hcard : ((N k).primeFactors.card:ℝ) ≤ 4*(k:ℝ) := by
    exact_mod_cast prime_card_le_four_mul hnk.1 hnk.2
  have hr : (1+((N k).primeFactors.card:ℝ))^(1/5:ℝ) ≤ 5*(k:ℝ)^(1/5:ℝ) := by
    calc
      _ ≤ (5*(k:ℝ))^(1/5:ℝ) := Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ = (5:ℝ)^(1/5:ℝ)*(k:ℝ)^(1/5:ℝ) := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        calc
          (5:ℝ)^(1/5:ℝ) ≤ (5:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 5 := Real.rpow_one _) (by positivity)
  have hmul := mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hkpos.le (1/3:ℝ))
  rw [mul_assoc, ← Real.rpow_add hkpos, show -(2/15:ℝ) + 1/3 = 1/5 by norm_num] at hmul
  apply (divisor_tail_bound (le_of_lt ha) (by norm_num : 0 < (4/5:ℝ)) (by norm_num)
    (Real.exp_pos _) hnk.1.ne').trans
  rw [← Real.exp_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  change _ + C * _ ≤ _
  norm_num only [show (1:ℝ)-4/5=1/5 by norm_num]
  have hbound := mul_le_mul_of_nonneg_left hr hC
  dsimp [c] at hmul ⊢
  linarith

end H093811

namespace Hasler093811
open Finset Filter Real
open scoped Topology

/-- The integral decimal cutoff dominates the real exponential cutoff. -/
theorem decimal_cutoff_le (k : ℕ) (hk : 1 ≤ k) :
    exp ((k:ℝ)^(1/3:ℝ)) ≤ (10:ℝ)^(Nat.nthRoot 3 k) := by
  let m := Nat.nthRoot 3 k
  have hm : 1 ≤ m := (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).mpr (by simpa using hk)
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hc : (k:ℝ) < ((m:ℝ)+1)^3 := by
    exact_mod_cast Nat.lt_pow_nthRoot_add_one (by decide : 3 ≠ 0) k
  have hr : (k:ℝ)^(1/3:ℝ) ≤ (m:ℝ)+1 := by
    have H := Real.rpow_le_rpow (Nat.cast_nonneg k) hc.le (by norm_num : (0:ℝ) ≤ 1/3)
    rwa [← Real.rpow_natCast_mul (by positivity : 0 ≤ (m:ℝ)+1),
      show ((3:ℕ):ℝ)*(1/3:ℝ) = 1 by norm_num, Real.rpow_one] at H
  have h₂ : exp 2 ≤ 10 := by
    rw [show (2:ℝ) = 1+1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  calc
    _ ≤ exp ((m:ℝ)*2) := Real.exp_le_exp.mpr (by linarith)
    _ = (exp 2)^m := Real.exp_nat_mul _ _
    _ ≤ (10:ℝ)^m := pow_le_pow_left₀ (Real.exp_pos _).le h₂ _

/-- Change the real-valued cutoff to a decimal block length, uniformly in the
integer family and the exponent. -/
theorem decimal_cutoff_tail {a : ℝ} {N : ℕ → ℕ}
    (h : Tendsto (fun k : ℕ => ∑ d ∈ (N k).divisors.filter
      (fun d : ℕ => exp ((k:ℝ)^(1/3:ℝ)) ≤ (d:ℝ)), (d:ℝ)^(-a)) atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => ∑ d ∈ (N k).divisors.filter
      (fun d : ℕ => 10^(Nat.nthRoot 3 k) ≤ d), (d:ℝ)^(-a)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun k => sum_nonneg fun d _ => by positivity)) _ h
  filter_upwards [eventually_ge_atTop 1] with k hk
  apply sum_le_sum_of_subset_of_nonneg _ (fun d _ _ => by positivity)
  intro d hd
  obtain ⟨hdiv,hq⟩ := mem_filter.mp hd
  exact mem_filter.mpr ⟨hdiv, (decimal_cutoff_le k hk).trans (by exact_mod_cast hq)⟩

end Hasler093811

namespace Digit93811
open Finset

private theorem digit_weight {d q k : ℕ} (hd : 0 < d) (hq : 0 < q) (h : d*q ≤ 10^k) :
    ((Nat.digits 10 d).prod : ℝ)/(9:ℝ)^k ≤ 9*(q:ℝ)^(-(Real.logb 10 9)) := by
  let a : ℝ := Real.logb 10 9
  have ha : 0 ≤ a := (Real.logb_pos (by norm_num) (by norm_num)).le
  have ht : (10:ℝ)^a = 9 := Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)
  have powers (j : ℕ) : ((10:ℝ)^j)^a = 9^j := by
    rw [← Real.rpow_natCast (10:ℝ) j, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num), ht, Real.rpow_natCast]
  let L := (Nat.digits 10 d).length
  have hp : (Nat.digits 10 d).prod ≤ 9^L :=
    List.prod_le_pow_card _ _ fun z hz => Nat.le_of_lt_succ (Nat.digits_lt_base (by decide : 1<10) hz)
  have hl : 10^L*q ≤ 10*(10^k) := by
    calc
      _ ≤ (10*d)*q := Nat.mul_le_mul_right q (Nat.base_pow_length_digits_le 10 d (by decide) hd.ne')
      _ ≤ _ := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 10 h
  have hqpos : 0 < (q:ℝ)^a := Real.rpow_pos_of_pos (by exact_mod_cast hq) _
  have hreal : (10:ℝ)^L*q ≤ 10*(10:ℝ)^k := by exact_mod_cast hl
  have hm := Real.rpow_le_rpow (by positivity) hreal ha
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by norm_num) (by positivity),
    powers, ht, powers] at hm
  have hdp : ((Nat.digits 10 d).prod : ℝ) ≤ (9:ℝ)^L := by exact_mod_cast hp
  have hh := (mul_le_mul_of_nonneg_right hdp hqpos.le).trans hm
  change _ ≤ 9*(q:ℝ)^(-a)
  rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hqpos]
  exact hh

/-- Change variables to the cofactor after controlling each individual digit product. -/
theorem large_weight {n k Q : ℕ} (hn : n ≤ 10^k) :
    ((∑ d ∈ n.divisors.filter (fun d => Q ≤ n/d), (Nat.digits 10 d).prod : ℕ) : ℝ) / (9:ℝ)^k ≤
      9 * ∑ q ∈ n.divisors.filter (fun q : ℕ => Q ≤ q), (q:ℝ)^(-(Real.logb 10 9)) := by
  classical
  have hs : (∑ d ∈ n.divisors.filter (fun d => Q ≤ n/d), ((n/d : ℕ) : ℝ)^(-(Real.logb 10 9))) =
      ∑ q ∈ n.divisors.filter (fun q : ℕ => Q ≤ q), (q:ℝ)^(-(Real.logb 10 9)) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    exact Nat.sum_div_divisors n (fun q => if Q ≤ q then (q:ℝ)^(-(Real.logb 10 9)) else 0)
  rw [Nat.cast_sum, Finset.sum_div, ← hs, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hdiv := (Finset.mem_filter.mp hd).1
  obtain ⟨hdvd, hnz⟩ := Nat.mem_divisors.mp hdiv
  apply digit_weight (Nat.pos_of_mem_divisors hdiv)
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hnz) hdvd) (Nat.pos_of_mem_divisors hdiv))
  exact (Nat.mul_div_cancel' hdvd).le.trans hn

end Digit93811

namespace Hasler093811
open Finset Filter
open scoped Topology

theorem small_sum
    (block : ∀ {k h t b q d : ℕ}, h*t ≤ k → q < 10^h → b < 10^h →
      10^k ∣ q*d+b → ¬q∣b → d < 10^k →
      (Nat.digits 10 d).prod * 9^t ≤ 8^t * 9^k)
    {k m b : ℕ} (hb : 0 < b) (hb10 : b < 10) (hm : 1 ≤ m) (hk : m^3 ≤ k) :
    let n := 10^k - b
    ((∑ d ∈ n.divisors.filter (fun d => n/d < 10^m ∧ ¬ n/d ∣ b),
      (Nat.digits 10 d).prod : ℕ) : ℝ) / (9 : ℝ)^k ≤
      (10 : ℝ)^m * (8/9 : ℝ)^(m^2) := by
  let n := 10^k - b
  let S := n.divisors.filter (fun d => n/d < 10^m ∧ ¬ n/d ∣ b)
  change ((∑ d ∈ S, (Nat.digits 10 d).prod : ℕ) : ℝ) / _ ≤ _
  have hm10 : 10 ≤ 10^m := by simpa using Nat.pow_le_pow_right (by decide : 0 < 10) hm
  have hkpos : 1 ≤ k := by
    have : 1 ≤ m^3 := Nat.one_le_pow _ _ hm
    omega
  have hk10 : 10 ≤ 10^k := by simpa using Nat.pow_le_pow_right (by decide : 0 < 10) hkpos
  have hn : 0 < n := by dsimp [n]; omega
  have hD {d : ℕ} (hd : d ∈ S) := (mem_filter.mp hd).1
  have hcard : S.card ≤ 10^m := by
    rw [← card_range (10^m)]
    apply card_le_card_of_injOn (fun d => n/d)
    · intro d hd
      exact mem_range.mpr (mem_filter.mp hd).2.1
    · intro d hd e he heq
      change n/d = n/e at heq
      have hdvd := (Nat.mem_divisors.mp (hD hd)).1
      have hevd := (Nat.mem_divisors.mp (hD he)).1
      have hdprod := Nat.div_mul_cancel hdvd
      have heprod := Nat.div_mul_cancel hevd
      have hpos : 0 < n/e := Nat.div_pos (Nat.le_of_dvd hn hevd) (Nat.pos_of_mem_divisors (hD he))
      exact Nat.eq_of_mul_eq_mul_left hpos ((heq ▸ hdprod).trans heprod.symm)
  have each (d : ℕ) (hd : d ∈ S) :
      ((Nat.digits 10 d).prod : ℝ) ≤ (8/9 : ℝ)^(m^2) * (9 : ℝ)^k := by
    have hdvd := (Nat.mem_divisors.mp (hD hd)).1
    have heq : n/d*d + b = 10^k := by rw [Nat.div_mul_cancel hdvd]; dsimp [n]; omega
    have hdk : d < 10^k := by
      have := Nat.le_of_dvd hn hdvd
      dsimp [n] at this
      omega
    have hpoint := block (h := m) (t := m^2) (b := b) (q := n/d) (d := d)
      (by simpa [pow_succ, Nat.mul_comm] using hk) (mem_filter.mp hd).2.1
      (by omega) (heq ▸ dvd_refl _) (mem_filter.mp hd).2.2 hdk
    rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact_mod_cast hpoint
  rw [div_le_iff₀ (by positivity), Nat.cast_sum]
  calc
    _ ≤ ∑ _d ∈ S, (8/9 : ℝ)^(m^2) * (9 : ℝ)^k := sum_le_sum each
    _ = (S.card : ℝ) * ((8/9 : ℝ)^(m^2) * (9 : ℝ)^k) := by simp
    _ ≤ ((10 : ℝ)^m) * ((8/9 : ℝ)^(m^2) * (9 : ℝ)^k) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard
    _ = _ := by ring

theorem small_bound_tendsto :
    Tendsto (fun m : ℕ => (10 : ℝ)^m * (8/9 : ℝ)^(m^2)) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity)
    (g := fun m : ℕ => (1/2 : ℝ)^m)
  · filter_upwards [eventually_ge_atTop 32] with m hm
    have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 8/9)
      (by norm_num : (8/9 : ℝ) ≤ 1) hm
    have h' : (10 : ℝ) * (8/9 : ℝ)^m ≤ 1/2 := by
      have hnum : (10 : ℝ) * (8/9 : ℝ)^32 ≤ 1/2 := by norm_num
      linarith
    rw [sq, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h' m
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

end Hasler093811

namespace Hasler093811
open Finset Filter
open scoped Topology

theorem remainder_of_large {b : ℕ}
    (small : ∀ {k m : ℕ}, 1 ≤ m → m^3 ≤ k →
      let n := 10^k-b
      ((∑ d ∈ n.divisors.filter (fun d => n/d < 10^m ∧ ¬ n/d ∣ b),
        (Nat.digits 10 d).prod : ℕ) : ℝ) / (9 : ℝ)^k ≤
        (10 : ℝ)^m * (8/9 : ℝ)^(m^2))
    (decay : Tendsto (fun m : ℕ => (10 : ℝ)^m * (8/9 : ℝ)^(m^2)) atTop (nhds 0))
    (large : Tendsto (fun k : ℕ =>
      let n := 10^k-b
      ((∑ d ∈ n.divisors.filter (fun d => 10^(Nat.nthRoot 3 k) ≤ n/d),
        (Nat.digits 10 d).prod : ℕ) : ℝ) / (9 : ℝ)^k) atTop (nhds 0)) :
    Tendsto (fun k : ℕ =>
      let n := 10^k-b
      ((∑ d ∈ n.divisors.filter (fun d => ¬ n/d ∣ b),
        (Nat.digits 10 d).prod : ℕ) : ℝ) / (9 : ℝ)^k) atTop (nhds 0) := by
  have root : Tendsto (Nat.nthRoot 3) atTop atTop := by
    apply tendsto_atTop.2
    intro l
    filter_upwards [eventually_ge_atTop (l^3)] with k hk
    exact (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).2 hk
  have upper := (decay.comp root).add large
  rw [zero_add] at upper
  apply squeeze_zero' (Eventually.of_forall fun _ => by dsimp; positivity) _ upper
  filter_upwards [root.eventually_ge_atTop 1] with k hk
  let m := Nat.nthRoot 3 k
  let n := 10^k-b
  let S := n.divisors.filter (fun d => n/d < 10^m ∧ ¬ n/d ∣ b)
  let L := n.divisors.filter (fun d => 10^m ≤ n/d)
  let R := n.divisors.filter (fun d => ¬ n/d ∣ b)
  let f (d : ℕ) := (Nat.digits 10 d).prod
  have hsub : R ⊆ S ∪ L := by
    intro d hd
    obtain ⟨hd₀, hdb⟩ := mem_filter.mp hd
    rcases lt_or_ge (n/d) (10^m) with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨hd₀, h, hdb⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hd₀, h⟩)
  have hdis : Disjoint S L := by
    apply disjoint_left.2
    intro d hs hl
    exact (mem_filter.mp hs).2.1.not_ge (mem_filter.mp hl).2
  have hsum := sum_le_sum_of_subset (f := f) hsub
  rw [sum_union hdis] at hsum
  have hreal : ((∑ d ∈ R, f d : ℕ) : ℝ) ≤
      ((∑ d ∈ S, f d : ℕ) : ℝ) + ((∑ d ∈ L, f d : ℕ) : ℝ) := by exact_mod_cast hsum
  have hm : m^3 ≤ k := Nat.pow_nthRoot_le (.inl (by decide : 3 ≠ 0))
  calc
    _ ≤ (((∑ d ∈ S, f d : ℕ) : ℝ) + ((∑ d ∈ L, f d : ℕ) : ℝ)) / (9 : ℝ)^k :=
      div_le_div_of_nonneg_right hreal (by positivity)
    _ = _ := add_div _ _ _
    _ ≤ _ := add_le_add (small hk hm) (le_refl _)

private theorem cofactor_eq {n d q : ℕ} (hn : 0 < n) (hd : d ∈ n.divisors)
    (hq : q ∣ n) (hp : 0 < q) : n/d = q ↔ d = n/q := by
  have inv {x : ℕ} (hx : x ∣ n) (hx0 : 0 < x) : n/(n/x) = x :=
    Nat.div_eq_of_eq_mul_right (Nat.div_pos (Nat.le_of_dvd hn hx) hx0) (Nat.div_mul_cancel hx).symm
  constructor
  · rintro rfl
    exact (inv (Nat.mem_divisors.mp hd).1 (Nat.pos_of_mem_divisors hd)).symm
  · rintro rfl
    exact inv hq hp

theorem remainder_set_four {n : ℕ} (h4 : 4 ∣ n) :
    n.divisors.filter (fun d => ¬ n/d ∣ 4) = n.divisors \ {n,n/2,n/4} := by
  by_cases hn : n = 0
  · simp [hn]
  have hc (q : ℕ) : q ∣ 4 ↔ q = 1 ∨ q = 2 ∨ q = 4 := by
    calc
      q ∣ 4 ↔ q ∈ (4 : ℕ).divisors := by simp [Nat.mem_divisors]
      _ ↔ _ := by rw [show (4 : ℕ).divisors = {1,2,4} by decide]; simp
  ext d
  simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  apply and_congr_right
  intro hd
  rw [hc, cofactor_eq (by omega) hd (one_dvd _) (by decide),
    cofactor_eq (by omega) hd (dvd_trans (by decide : 2 ∣ 4) h4) (by decide),
    cofactor_eq (by omega) hd h4 (by decide), Nat.div_one]

theorem remainder_set_two {n : ℕ} (h2 : 2 ∣ n) :
    n.divisors.filter (fun d => ¬ n/d ∣ 2) = n.divisors \ {n,n/2} := by
  by_cases hn : n = 0
  · simp [hn]
  have hc (q : ℕ) : q ∣ 2 ↔ q = 1 ∨ q = 2 := by
    calc
      q ∣ 2 ↔ q ∈ (2 : ℕ).divisors := by simp [Nat.mem_divisors]
      _ ↔ _ := by rw [show (2 : ℕ).divisors = {1,2} by decide]; simp
  ext d
  simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  apply and_congr_right
  intro hd
  rw [hc, cofactor_eq (by omega) hd (one_dvd _) (by decide),
    cofactor_eq (by omega) hd h2 (by decide), Nat.div_one]

theorem four_remainder_limit
    (rest : Tendsto (fun k : ℕ =>
      let n := 10^k-4
      ((∑ d ∈ n.divisors.filter (fun d => ¬ n/d ∣ 4),
        (Nat.digits 10 d).prod : ℕ) : ℝ) / (9 : ℝ)^k) atTop (nhds 0)) :
    Tendsto (fun k : ℕ =>
      let n : ℕ := 10^k-4
      ((∑ d ∈ n.divisors \ {n,n/2,n/4}, (Nat.digits 10 d).prod : ℕ) : ℝ) / (9 : ℝ)^k)
      atTop (nhds 0) := by
  apply rest.congr'
  filter_upwards [eventually_ge_atTop 2] with k hk
  have h : 4 ∣ (10^k-4 : ℕ) := by
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, k = 2+t := ⟨k-2, by omega⟩
    apply Nat.dvd_sub _ (dvd_refl _)
    rw [pow_add]
    exact dvd_mul_of_dvd_left (by decide : 4 ∣ (10 : ℕ)^2) _
  dsimp only
  rw [remainder_set_four h]

theorem two_remainder_limit
    (rest : Tendsto (fun k : ℕ =>
      let n := 10^k-2
      ((∑ d ∈ n.divisors.filter (fun d => ¬ n/d ∣ 2),
        (Nat.digits 10 d).prod : ℕ) : ℝ) / (9 : ℝ)^k) atTop (nhds 0)) :
    Tendsto (fun k : ℕ =>
      let n : ℕ := 10^k-2
      ((∑ d ∈ n.divisors \ {n,n/2}, (Nat.digits 10 d).prod : ℕ) : ℝ) / (9 : ℝ)^k)
      atTop (nhds 0) := by
  apply rest.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  have h : 2 ∣ (10^k-2 : ℕ) := by
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, k = 1+t := ⟨k-1, by omega⟩
    apply Nat.dvd_sub _ (dvd_refl _)
    rw [pow_add]
    exact dvd_mul_of_dvd_left (by decide : 2 ∣ (10 : ℕ)^1) _
  dsimp only
  rw [remainder_set_two h]

end Hasler093811

namespace Digit93811
open OMA.S_oeis_a093811

private theorem dp_last {x : ℕ} (hx : x < 10) (hpos : x ≠ 0) (y : ℕ) :
    (Nat.digits 10 (x + 10*y)).prod = x * (Nat.digits 10 y).prod := by
  simp only [Nat.digits_add 10 (by decide) x y hx (Or.inl hpos), List.prod_cons]

private theorem dp_nines {a : ℕ} (ha : 0 < a) (t : ℕ) :
    (Nat.digits 10 (a*10^t-1)).prod = (Nat.digits 10 (a-1)).prod * 9^t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hp : 0 < a * 10^t := by positivity
    rw [pow_succ, ← Nat.mul_assoc, show a * 10^t * 10 - 1 = 9+10*(a*10^t-1) by omega,
      dp_last (by decide) (by decide), ih, pow_succ]
    ring

private theorem dp_decimal {a x : ℕ} (ha : 0 < a) (hx : x < 10) (hpos : x ≠ 0) (t : ℕ) :
    (Nat.digits 10 (10*(a*10^t-1)+x)).prod = x * (Nat.digits 10 (a-1)).prod * 9^t := by
  rw [Nat.add_comm, dp_last hx hpos, dp_nines ha]
  ring

/-- At offset two the index and its half contribute exactly 12 times 9^(k-1). -/
theorem two_split (t : ℕ) :
    let n : ℕ := 10^(t+1)-2
    digitProductSum n = (∑ d ∈ n.divisors \ {n,n/2}, (Nat.digits 10 d).prod) + 12*9^t := by
  dsimp only
  let dp (x : ℕ) := (Nat.digits 10 x).prod
  let p := 10^t
  have hp : 0 < p := by dsimp [p]; positivity
  let a := 10*p-2
  let b := 5*p-1
  have hab : a=2*b := by dsimp [a,b]; omega
  have han : a≠0 := by dsimp [a]; omega
  have hne : a≠b := by dsimp [a,b]; omega
  have hda : dp a = 8*9^t := by
    change (Nat.digits 10 (10*p-2)).prod = _
    rw [show 10*p-2 = 10*(1*10^t-1)+8 by change 10*p-2=10*(1*p-1)+8; omega,
      dp_decimal (by decide) (by decide) (by decide)]
    have : (Nat.digits 10 (1-1)).prod = 1 := by decide
    rw [this, Nat.mul_one]
  have hdb : dp b = 4*9^t := by
    exact (dp_nines (a:=5) (by decide) t).trans (by rfl)
  have hset : ({a,b} : Finset ℕ) ⊆ a.divisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨dvd_rfl, han⟩
    · exact Nat.mem_divisors.mpr ⟨⟨2, by simpa [Nat.mul_comm] using hab⟩, han⟩
  have hsum := Finset.sum_sdiff hset (f:=dp)
  rw [Finset.sum_pair hne, hda, hdb] at hsum
  have hN : 10^(t+1)-2=a := by dsimp [a,p]; rw [pow_succ,Nat.mul_comm]
  rw [hN, show a/2=b by omega]
  change (∑ d ∈ a.divisors, dp d) = (∑ d ∈ a.divisors \ {a,b}, dp d) + 12*9^t
  omega

theorem two_main (t : ℕ) : 12*9^t ≤ digitProductSum (10^(t+1)-2) := by
  rw [two_split]
  exact Nat.le_add_left _ _

open Filter

theorem two_eventually : ∀ᶠ k : ℕ in atTop,
    (4/3 : ℝ)*9^k ≤ (digitProductSum (10^k-2) : ℝ) := by
  filter_upwards [eventually_ge_atTop 1] with k hk
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have h : 12*(9:ℝ)^t ≤ (digitProductSum (10^(t+1)-2) : ℝ) := by exact_mod_cast two_main t
  rw [pow_succ]
  linarith

theorem two_limit
    (rest : Tendsto (fun k : ℕ => let n : ℕ := 10^k-2
      ((∑ d ∈ n.divisors \ {n,n/2}, (Nat.digits 10 d).prod : ℕ) : ℝ)/(9:ℝ)^k)
      atTop (nhds 0)) :
    Tendsto (fun k : ℕ => (digitProductSum (10^k-2) : ℝ)/(9:ℝ)^k)
      atTop (nhds (4/3:ℝ)) := by
  have h := rest.add (tendsto_const_nhds (x := (4/3 : ℝ)))
  rw [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  dsimp only [Pi.add_apply]
  rw [two_split, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  simp only [pow_succ (9:ℝ)]
  field_simp
  ring

end Digit93811

namespace Digit93811
open OMA.S_oeis_a093811 Filter
open scoped Topology

/-- M. F. Hasler identified these three digit products in the examples for OEIS A397260.
Their exact contribution at exponent t+2 is 94 times 9^t. -/
theorem four_split (t : ℕ) :
    let n : ℕ := 10^(t+2)-4
    digitProductSum n =
      (∑ d ∈ n.divisors \ {n,n/2,n/4}, (Nat.digits 10 d).prod) + 94*9^t := by
  dsimp only
  let p := 10^t
  have hp : 0 < p := by dsimp [p]; positivity
  let c := 25*p-1
  let b := 50*p-2
  let a := 100*p-4
  have hac : a = 4*c := by dsimp [a,c]; omega
  have hab : a = 2*b := by dsimp [a,b]; omega
  have han : a ≠ 0 := by dsimp [a]; omega
  have hab' : a ≠ b := by dsimp [a,b]; omega
  have hac' : a ≠ c := by dsimp [a,c]; omega
  have hbc' : b ≠ c := by dsimp [b,c]; omega
  have hdc : (Nat.digits 10 c).prod = 8*9^t := (dp_nines (a:=25) (by decide) t).trans (by rfl)
  have hdb : (Nat.digits 10 b).prod = 32*9^t := by
    rw [show b=10*(5*10^t-1)+8 by change 50*p-2=10*(5*p-1)+8; omega,
      dp_decimal (by decide) (by decide) (by decide)]
    rfl
  have hda : (Nat.digits 10 a).prod = 54*9^t := by
    rw [show a=10*(10*10^t-1)+6 by change 100*p-4=10*(10*p-1)+6; omega,
      dp_decimal (by decide) (by decide) (by decide)]
    rfl
  have hset : ({a,b,c} : Finset ℕ) ⊆ a.divisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨dvd_rfl, han⟩
    · exact Nat.mem_divisors.mpr ⟨⟨2, by simpa [Nat.mul_comm] using hab⟩, han⟩
    · exact Nat.mem_divisors.mpr ⟨⟨4, by simpa [Nat.mul_comm] using hac⟩, han⟩
  have hsum := Finset.sum_sdiff hset (f := fun d => (Nat.digits 10 d).prod)
  rw [Finset.sum_insert (by simp [hab',hac']), Finset.sum_pair hbc', hda, hdb, hdc] at hsum
  have hN : 10^(t+2)-4 = a := by dsimp [a,p]; rw [pow_add]; norm_num; omega
  rw [hN, show a/2 = b by omega, show a/4 = c by omega, digitProductSum]
  omega

/-- Once the other divisors have vanishing normalized sum,
the three largest specified contributions determine the offset-four limit. -/
theorem four_limit
    (rest : Tendsto (fun k : ℕ =>
      let n : ℕ := 10^k-4
      ((∑ d ∈ n.divisors \ {n,n/2,n/4}, (Nat.digits 10 d).prod : ℕ) : ℝ) / (9 : ℝ)^k)
      atTop (nhds 0)) :
    Tendsto (fun k : ℕ => (digitProductSum (10^k-4) : ℝ) / (9 : ℝ)^k)
      atTop (nhds (94/81 : ℝ)) := by
  have h := rest.add (tendsto_const_nhds (x := (94/81 : ℝ)))
  rw [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with k hk
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, k = t+2 := ⟨k-2, by omega⟩
  dsimp only [Pi.add_apply]
  rw [four_split t, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
  field_simp
  ring

end Digit93811

namespace Digit93811
open OMA.S_oeis_a093811 Filter
open scoped Topology

theorem sharp
    (lower : ∀ᶠ k : ℕ in atTop, (4/3 : ℝ) * 9^k ≤ (digitProductSum (10^k-2) : ℝ))
    (upper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (digitProductSum n : ℝ) / 9 ^ (Real.logb 10 n) ≤ 4/3 + ε) :
    Tendsto (fun k : ℕ => (digitProductSum (10^k-2) : ℝ) / (9 : ℝ)^k)
      atTop (nhds (4/3 : ℝ)) ∧
    limsup (fun n : ℕ => (digitProductSum n : ℝ) / (9 : ℝ)^(Real.logb 10 n))
      atTop = (4/3 : ℝ) := by
  let r (n : ℕ) := (digitProductSum n : ℝ) / (9 : ℝ)^(Real.logb 10 n)
  let w (k : ℕ) := 10^k - 2
  have hw : Tendsto w atTop atTop := by
    apply tendsto_atTop.2
    intro m
    filter_upwards [eventually_ge_atTop (m+2)] with k hk
    have h : k < 10^k := Nat.lt_pow_self (by decide)
    dsimp [w]
    omega
  have compare : ∀ᶠ k : ℕ in atTop, (digitProductSum (w k) : ℝ) / 9^k ≤ r (w k) := by
    filter_upwards [hw.eventually_gt_atTop 0] with k hk
    have hle : (w k : ℝ) ≤ (10 : ℝ)^k := by
      exact_mod_cast (Nat.sub_le (10^k) 2)
    have hlog : Real.logb 10 (w k) ≤ (k : ℝ) := by
      have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 10)
        (by exact_mod_cast hk) hle
      simpa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 10)] using h
    have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 9) hlog
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    simpa using hpow
  have lower' : ∀ᶠ k : ℕ in atTop, (4/3 : ℝ) ≤ (digitProductSum (w k) : ℝ) / 9^k := by
    filter_upwards [lower] with k hk
    exact (le_div_iff₀ (by positivity)).2 hk
  have upper' (b : ℝ) (hb : 4/3 < b) : ∀ᶠ n in atTop, r n ≤ b := by
    simpa [r] using upper (b-4/3) (by linarith)
  have freq : ∃ᶠ n : ℕ in atTop, (4/3 : ℝ) ≤ r n := by
    rw [frequently_atTop]
    intro N
    obtain ⟨k, hkN, hl, hc⟩ :=
      ((hw.eventually_ge_atTop N).and (lower'.and compare)).exists
    exact ⟨w k, hkN, hl.trans hc⟩
  constructor
  · apply tendsto_order.2
    constructor
    · intro a ha
      exact lower'.mono fun _ h => ha.trans_le h
    · intro b hb
      obtain ⟨c, hc, hcb⟩ := exists_between hb
      filter_upwards [compare, hw.eventually (upper' c hc)] with k h1 h2
      exact (h1.trans h2).trans_lt hcb
  · change limsup r atTop = 4/3
    have bounded : atTop.IsBoundedUnder (· ≤ ·) r := ⟨2, upper' _ (by norm_num)⟩
    have cobounded : atTop.IsCoboundedUnder (· ≤ ·) r := .of_frequently_ge freq
    exact le_antisymm ((limsup_le_iff' cobounded bounded).2 upper')
      (le_limsup_of_frequently_le freq bounded)

end Digit93811

namespace Digit93811
open OMA.S_oeis_a093811 Filter

/-- Each positive index is dominated by a strict record at or before that index. -/
private theorem record_before (n : ℕ) (hn : 0 < n) :
    ∃ m ≤ n, recordAt m ∧ digitProductSum n ≤ digitProductSum m := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hr : recordAt n
    · exact ⟨n, le_rfl, hr, le_rfl⟩
    have hfail : ¬ ∀ m : ℕ, 0 < m → m < n → digitProductSum m < digitProductSum n :=
      fun hh => hr ⟨hn, hh⟩
    push Not at hfail
    obtain ⟨m, hm, hmn, hF⟩ := hfail
    obtain ⟨i, him, hi, hFi⟩ := ih m hmn hm
    exact ⟨i, him.trans hmn.le, hi, hF.trans hFi⟩

/-- An eventual upper envelope on record indices controls the full sequence. -/
theorem upper_of_records
    (hr : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, recordAt n →
      (digitProductSum n : ℝ) / (9 : ℝ)^(Real.logb 10 n) ≤ 4/3 + ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (digitProductSum n : ℝ) / (9 : ℝ)^(Real.logb 10 n) ≤ 4/3 + ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.1 (hr ε hε)
  let C : ℕ := ∑ j ∈ Finset.range N, digitProductSum j
  have hscale : Tendsto (fun n : ℕ => (9 : ℝ)^(Real.logb 10 n)) atTop atTop :=
    (tendsto_rpow_atTop_of_base_gt_one 9 (by norm_num)).comp
      ((Real.tendsto_logb_atTop (b:=10) (by norm_num)).comp tendsto_natCast_atTop_atTop)
  filter_upwards [hscale.eventually_ge_atTop (C : ℝ), eventually_gt_atTop 0] with n hC hn
  obtain ⟨m,hmn,hm,hval⟩ := record_before n hn
  have hF : (digitProductSum n : ℝ) ≤ digitProductSum m := by exact_mod_cast hval
  apply (div_le_iff₀ (by positivity)).2
  by_cases hNm : N ≤ m
  · have hh := (div_le_iff₀ (by positivity : (0:ℝ)<9^(Real.logb 10 m))).1 (hN m hNm hm)
    refine hF.trans (hh.trans (mul_le_mul_of_nonneg_left ?_ (by linarith)))
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hm.1) (by exact_mod_cast hmn))
  · have hFm : digitProductSum m ≤ C := Finset.single_le_sum (f:=digitProductSum)
      (fun j _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    have hF' : (digitProductSum n : ℝ) ≤ C := by exact_mod_cast hval.trans hFm
    refine hF'.trans (hC.trans ?_)
    have hp : (0:ℝ) ≤ 9^(Real.logb 10 n) := by positivity
    nlinarith

end Digit93811

namespace Digit93811
open Finset Filter OMA.S_oeis_a093811 Hasler093811
open scoped Topology

/-- Cofactors that do not divide the offset have vanishing normalized mass. -/
theorem remaining (b : ℕ) (hb : 0 < b) (hb10 : b < 10) :
    Tendsto (fun k : ℕ => let n := 10^k-b
      ((∑ d ∈ n.divisors.filter (fun d => ¬ n/d ∣ b), (Nat.digits 10 d).prod : ℕ) : ℝ) /
        (9:ℝ)^k) atTop (nhds 0) := by
  apply remainder_of_large (fun hm hk => small_sum small_cofactor hb hb10 hm hk) small_bound_tendsto
  have ha : (4/5 : ℝ) < Real.logb 10 9 := by
    rw [Real.logb, lt_div_iff₀ (Real.log_pos (by norm_num))]
    have h := Real.log_lt_log (by norm_num : (0:ℝ)<10^4) (by norm_num : (10:ℝ)^4<9^5)
    rw [Real.log_pow, Real.log_pow] at h
    norm_num at h
    linarith
  let N (k : ℕ) := 10^k-b
  have hN : ∀ᶠ k : ℕ in atTop, 0 < N k ∧ N k ≤ 10^k := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hten : 10 ≤ 10^k := by simpa using Nat.pow_le_pow_right (by decide : 0<10) hk
    dsimp [N]
    omega
  have ht := decimal_cutoff_tail (H093811.large_cofactor_tail ha N hN)
  have hu := ht.const_mul 9
  rw [mul_zero] at hu
  apply squeeze_zero' (Eventually.of_forall fun k => by dsimp; positivity) _ hu
  exact Eventually.of_forall fun k => large_weight (Nat.sub_le (10^k) b)

theorem minus_four :
    Tendsto (fun k : ℕ => (digitProductSum (10^k-4) : ℝ)/(9:ℝ)^k) atTop (nhds (94/81:ℝ)) := by
  apply four_limit
  apply (remaining 4 (by decide) (by decide)).congr'
  filter_upwards [eventually_ge_atTop 2] with k hk
  have hd : 4 ∣ 10^k-4 := Nat.dvd_sub (dvd_trans (by decide : 4 ∣ 10^2)
    (pow_dvd_pow 10 hk)) (dvd_refl 4)
  dsimp only
  rw [remainder_set_four hd]

theorem minus_two :
    Tendsto (fun k : ℕ => (digitProductSum (10^k-2) : ℝ)/(9:ℝ)^k) atTop (nhds (4/3:ℝ)) := by
  apply two_limit
  apply (remaining 2 (by decide) (by decide)).congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hd : 2 ∣ 10^k-2 := Nat.dvd_sub (dvd_trans (by decide : 2 ∣ 10^1)
    (pow_dvd_pow 10 hk)) (dvd_refl 2)
  dsimp only
  rw [remainder_set_two hd]

end Digit93811

namespace H093811
open OMA.S_oeis_a093811 Finset

private theorem record_check {n b : ℕ} (hn : 0 < n) (hb : digitProductSum n = b)
    (h : ∀ i : Fin n, i.val ≠ 0 → digitProductSum i.val < b) : recordAt n :=
  ⟨hn, fun m hm hmn => hb ▸ h ⟨m,hmn⟩ hm.ne'⟩

set_option maxRecDepth 100000 in
theorem record_six : recordAt 6 := record_check (b := 12) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem record_ninety_six : recordAt 96 := record_check (b := 132) (by decide) (by decide +kernel) (by decide +kernel)

end H093811

namespace OMA.R_oeis_a093811_R1
open OMA.S_oeis_a093811 Filter

/-- Patel's strict cutoff, restricted to a finite range by the divisor-count bound. -/
def H1 : Prop := ∀ n : ℕ, 798 < n → n ≤ (50^50)^(2^50)*10^48 → digitProductSum n < n

/-- Strict records at offset four beyond the checked initial indices. -/
def H2 : Prop := ∀ k : ℕ, 2 < k → recordAt (10^k-4)

/-- Strict records at offset two. -/
def H3 : Prop := ∀ k : ℕ, 4 < k → recordAt (10^k-2)

/-- Only strict record indices need a global upper envelope. -/
def H4 : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, recordAt n →
  (digitProductSum n : ℝ) / (9 : ℝ)^(Real.logb 10 n) ≤ 4/3 + ε

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a093811.main := by
  intro hcut hfour htwo hrecords
  refine ⟨?_, ?_, htwo, Digit93811.minus_four, Digit93811.minus_two, H093811.ratio_limit, ?_⟩
  · intro n hn
    exact (le_or_gt n _).elim (hcut n hn) (H093811.strict_large n)
  · intro k hk
    by_cases h : 2 < k
    · exact hfour k h
    · obtain rfl | rfl : k=1 ∨ k=2 := by omega
      · exact H093811.record_six
      · exact H093811.record_ninety_six
  · exact (Digit93811.sharp Digit93811.two_eventually (Digit93811.upper_of_records hrecords)).2

end OMA.R_oeis_a093811_R1
