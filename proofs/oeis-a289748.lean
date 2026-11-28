import OMAStatements.S_oeis_a289748
import Mathlib

namespace OMA.A289748Proof

open OMA.S_oeis_a289748

-- The Thue-Morse sequence

theorem tmLe (k : ℕ) : tm k ≤ 1 := by
  unfold tm
  omega

theorem tmEven (k : ℕ) : tm (2 * k) = tm k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · unfold tm
    rw [Nat.digits_def' (b := 2) (by norm_num) (show 0 < 2 * k by omega)]
    have h1 : 2 * k % 2 = 0 := by omega
    have h2 : 2 * k / 2 = k := by omega
    rw [h1, h2, List.sum_cons, zero_add]

theorem tmOdd (k : ℕ) : tm (2 * k + 1) + tm k = 1 := by
  unfold tm
  rw [Nat.digits_def' (b := 2) (by norm_num) (show 0 < 2 * k + 1 by omega)]
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  rw [h1, h2, List.sum_cons]
  omega

theorem tmWit (a : ℕ) : ∃ j, a ≤ j ∧ tm j = 1 := by
  have h := tmOdd a
  have h2 := tmEven a
  have h3 := tmLe (2 * a)
  by_cases ha : tm (2 * a) = 1
  · exact ⟨2 * a, by omega, ha⟩
  · exact ⟨2 * a + 1, by omega, by omega⟩

-- The explicit digits: d 0 = 1, d (2j+1) = 1, d (2j+2) = tm j

def D (i : ℕ) : ℕ := if i % 2 = 1 then 1 else if i = 0 then 1 else tm (i / 2 - 1)

theorem DLe (i : ℕ) : D i ≤ 1 := by
  unfold D
  split_ifs
  · exact le_refl 1
  · exact le_refl 1
  · exact tmLe _

theorem DZero : D 0 = 1 := by
  simp [D]

theorem DOdd (j : ℕ) : D (2 * j + 1) = 1 := by
  unfold D
  rw [if_pos (show (2 * j + 1) % 2 = 1 by omega)]

theorem DEven (j : ℕ) : D (2 * j + 2) = tm j := by
  unfold D
  rw [if_neg (show ¬ ((2 * j + 2) % 2 = 1) by omega), if_neg (show ¬ (2 * j + 2 = 0) by omega)]
  congr 1
  omega

theorem DEven' (n : ℕ) : D (2 * (n + 1)) = tm n := by
  rw [show 2 * (n + 1) = 2 * n + 2 by ring]
  exact DEven n

theorem DWitOdd (m : ℕ) : ∃ i, Odd i ∧ D (m + i) = 1 := by
  rcases Nat.even_or_odd m with ⟨a, ha⟩ | ⟨a, ha⟩
  · refine ⟨1, ⟨0, rfl⟩, ?_⟩
    rw [show m + 1 = 2 * a + 1 by omega, DOdd]
  · obtain ⟨j, hj, htj⟩ := tmWit a
    refine ⟨2 * (j - a) + 1, ⟨j - a, rfl⟩, ?_⟩
    rw [show m + (2 * (j - a) + 1) = 2 * j + 2 by omega, DEven, htj]

theorem DWitEven (m : ℕ) (hm : 1 ≤ m) : ∃ i, Even i ∧ D (m + i) = 1 := by
  rcases Nat.even_or_odd m with ⟨a, ha⟩ | ⟨a, ha⟩
  · obtain ⟨j, hj, htj⟩ := tmWit (a - 1)
    refine ⟨2 * (j - (a - 1)), ⟨j - (a - 1), two_mul _⟩, ?_⟩
    rw [show m + 2 * (j - (a - 1)) = 2 * j + 2 by omega, DEven, htj]
  · refine ⟨0, ⟨0, rfl⟩, ?_⟩
    rw [show m + 0 = 2 * a + 1 by omega, DOdd]

-- Geometric series and powers

theorem geoNegHalf : HasSum (fun n : ℕ => (-1/2 : ℝ) ^ n) (2/3) := by
  have h := hasSum_geometric_of_abs_lt_one (r := (-1/2 : ℝ))
    (by rw [abs_lt]; constructor <;> norm_num)
  convert h using 1
  norm_num

theorem geoQuarter : HasSum (fun n : ℕ => (1/4 : ℝ) ^ n) (4/3) := by
  have h := hasSum_geometric_of_lt_one (r := (1/4 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

theorem geoHi : HasSum (fun i : ℕ => ((1/2 : ℝ) ^ i + (-1/2 : ℝ) ^ i) / 2) (4/3) := by
  have h := (hasSum_geometric_two.add geoNegHalf).div_const 2
  rw [show (4/3 : ℝ) = (2 + 2/3) / 2 by norm_num]
  exact h

theorem geoLo : HasSum (fun i : ℕ => ((-1/2 : ℝ) ^ i - (1/2 : ℝ) ^ i) / 2) (-2/3) := by
  have h := (geoNegHalf.sub hasSum_geometric_two).div_const 2
  rw [show (-2/3 : ℝ) = (2/3 - 2) / 2 by norm_num]
  exact h

theorem powHalfOdd (k : ℕ) : (1/2 : ℝ) ^ (2 * k + 1) = (1/4) ^ k * (1/2) := by
  rw [pow_succ, pow_mul, show (1/2 : ℝ) ^ 2 = 1/4 by norm_num]

theorem divTwoPow (x : ℝ) (n : ℕ) : x / 2 ^ n = x * (1/2 : ℝ) ^ n := by
  rw [one_div_pow, mul_one_div]

-- The Thue-Morse constant in base 4: tau = 1/3 + U/4 with U = Sum tm k 4^(-k)

theorem sumTm4 : Summable (fun k : ℕ => (tm k : ℝ) * (1/4 : ℝ) ^ k) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) geoQuarter.summable
  · positivity
  · exact mul_le_of_le_one_left (by positivity) (by exact_mod_cast tmLe k)

theorem tauSum : HasSum (fun k : ℕ => (tm k : ℝ) / 2 ^ (k + 1))
    (1/3 + (∑' k : ℕ, (tm k : ℝ) * (1/4 : ℝ) ^ k) / 4) := by
  have hU := sumTm4.hasSum
  have he : HasSum (fun k : ℕ => (tm (2 * k) : ℝ) / 2 ^ (2 * k + 1))
      ((∑' k : ℕ, (tm k : ℝ) * (1/4 : ℝ) ^ k) / 2) := by
    have hf : (fun k : ℕ => (tm (2 * k) : ℝ) / 2 ^ (2 * k + 1)) =
        (fun k : ℕ => (tm k : ℝ) * (1/4 : ℝ) ^ k / 2) := by
      funext k
      rw [divTwoPow, tmEven, powHalfOdd]
      ring
    rw [hf]
    exact hU.div_const 2
  have ho : HasSum (fun k : ℕ => (tm (2 * k + 1) : ℝ) / 2 ^ (2 * k + 1 + 1))
      ((4/3 - ∑' k : ℕ, (tm k : ℝ) * (1/4 : ℝ) ^ k) / 4) := by
    have hf : (fun k : ℕ => (tm (2 * k + 1) : ℝ) / 2 ^ (2 * k + 1 + 1)) =
        (fun k : ℕ => ((1/4 : ℝ) ^ k - (tm k : ℝ) * (1/4 : ℝ) ^ k) / 4) := by
      funext k
      have h1 : (tm (2 * k + 1) : ℝ) + tm k = 1 := by exact_mod_cast tmOdd k
      have h2 : (tm (2 * k + 1) : ℝ) = 1 - tm k := by linarith
      rw [divTwoPow, h2, pow_succ, powHalfOdd]
      ring
    rw [hf]
    exact (geoQuarter.sub hU).div_const 4
  have h := HasSum.even_add_odd (f := fun k : ℕ => (tm k : ℝ) / 2 ^ (k + 1)) he ho
  convert h using 1
  ring

theorem tauEq : tau = 1/3 + (∑' k : ℕ, (tm k : ℝ) * (1/4 : ℝ) ^ k) / 4 :=
  tauSum.tsum_eq

-- The explicit digits represent tau in base -2, and give M = tau + 4/3 in base 2

theorem evenPart (ρ : ℝ) (hρ : ρ ^ 2 = 1/4) :
    HasSum (fun k : ℕ => (D (2 * k) : ℝ) * ρ ^ (2 * k))
      (1 + (∑' k : ℕ, (tm k : ℝ) * (1/4 : ℝ) ^ k) / 4) := by
  have h1 : HasSum (fun n : ℕ => (D (2 * (n + 1)) : ℝ) * ρ ^ (2 * (n + 1)))
      ((∑' k : ℕ, (tm k : ℝ) * (1/4 : ℝ) ^ k) / 4) := by
    have hf : (fun n : ℕ => (D (2 * (n + 1)) : ℝ) * ρ ^ (2 * (n + 1))) =
        (fun n : ℕ => (tm n : ℝ) * (1/4 : ℝ) ^ n / 4) := by
      funext n
      rw [DEven', pow_mul, hρ, pow_succ]
      ring
    rw [hf]
    exact sumTm4.hasSum.div_const 4
  have h2 := (hasSum_nat_add_iff (f := fun k : ℕ => (D (2 * k) : ℝ) * ρ ^ (2 * k)) 1).mp h1
  simp only [Finset.sum_range_one, mul_zero, pow_zero, DZero, Nat.cast_one, mul_one] at h2
  rw [add_comm]
  exact h2

theorem oddPart (ρ : ℝ) (hρ : ρ ^ 2 = 1/4) :
    HasSum (fun k : ℕ => (D (2 * k + 1) : ℝ) * ρ ^ (2 * k + 1)) (4/3 * ρ) := by
  have hf : (fun k : ℕ => (D (2 * k + 1) : ℝ) * ρ ^ (2 * k + 1)) =
      (fun k : ℕ => (1/4 : ℝ) ^ k * ρ) := by
    funext k
    rw [DOdd, Nat.cast_one, one_mul, pow_succ, pow_mul, hρ]
  rw [hf]
  exact geoQuarter.mul_right ρ

theorem DSum (ρ : ℝ) (hρ : ρ ^ 2 = 1/4) :
    HasSum (fun i : ℕ => (D i : ℝ) * ρ ^ i)
      (1 + (∑' k : ℕ, (tm k : ℝ) * (1/4 : ℝ) ^ k) / 4 + 4/3 * ρ) :=
  HasSum.even_add_odd (f := fun i : ℕ => (D i : ℝ) * ρ ^ i) (evenPart ρ hρ) (oddPart ρ hρ)

theorem DSumR : HasSum (fun i : ℕ => (D i : ℝ) * (-1/2 : ℝ) ^ i) tau := by
  have h := DSum (-1/2) (by norm_num)
  rw [tauEq]
  convert h using 1
  ring

theorem DSumQ : HasSum (fun i : ℕ => (D i : ℝ) * (1/2 : ℝ) ^ i) (tau + 4/3) := by
  have h := DSum (1/2) (by norm_num)
  rw [tauEq]
  convert h using 1
  ring

-- Tails of a base -2 expansion with digits 0, 1 lie in [-2/3, 4/3]

theorem sumR (e : ℕ → ℕ) (he : ∀ i, e i ≤ 1) :
    Summable (fun i : ℕ => (e i : ℝ) * (-1/2 : ℝ) ^ i) := by
  refine Summable.of_norm_bounded hasSum_geometric_two.summable (fun i => ?_)
  show ‖(e i : ℝ) * (-1/2 : ℝ) ^ i‖ ≤ (1/2 : ℝ) ^ i
  rw [norm_mul, norm_pow]
  have h1 : ‖(-1/2 : ℝ)‖ = 1/2 := by
    rw [Real.norm_eq_abs, abs_of_neg (show (-1/2 : ℝ) < 0 by norm_num)]
    norm_num
  have h2 : ‖(e i : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ e i by positivity)]
    exact_mod_cast he i
  rw [h1]
  exact mul_le_of_le_one_left (by positivity) h2

theorem termLe (e : ℕ → ℕ) (he : ∀ i, e i ≤ 1) (i : ℕ) :
    (e i : ℝ) * (-1/2 : ℝ) ^ i ≤ ((1/2 : ℝ) ^ i + (-1/2 : ℝ) ^ i) / 2 := by
  have hq : (0 : ℝ) < (1/2 : ℝ) ^ i := by positivity
  have h0 : (0 : ℝ) ≤ e i := by positivity
  have h1 : (e i : ℝ) ≤ 1 := by exact_mod_cast he i
  rw [show (-1/2 : ℝ) = -(1/2) by norm_num]
  rcases Nat.even_or_odd i with hi | hi
  · rw [hi.neg_pow]
    nlinarith
  · rw [hi.neg_pow]
    nlinarith

theorem termGe (e : ℕ → ℕ) (he : ∀ i, e i ≤ 1) (i : ℕ) :
    ((-1/2 : ℝ) ^ i - (1/2 : ℝ) ^ i) / 2 ≤ (e i : ℝ) * (-1/2 : ℝ) ^ i := by
  have hq : (0 : ℝ) < (1/2 : ℝ) ^ i := by positivity
  have h0 : (0 : ℝ) ≤ e i := by positivity
  have h1 : (e i : ℝ) ≤ 1 := by exact_mod_cast he i
  rw [show (-1/2 : ℝ) = -(1/2) by norm_num]
  rcases Nat.even_or_odd i with hi | hi
  · rw [hi.neg_pow]
    nlinarith
  · rw [hi.neg_pow]
    nlinarith

theorem tailLe (e : ℕ → ℕ) (he : ∀ i, e i ≤ 1) :
    ∑' i : ℕ, (e i : ℝ) * (-1/2 : ℝ) ^ i ≤ 4/3 :=
  hasSum_le (termLe e he) (sumR e he).hasSum geoHi

theorem tailGe (e : ℕ → ℕ) (he : ∀ i, e i ≤ 1) :
    -2/3 ≤ ∑' i : ℕ, (e i : ℝ) * (-1/2 : ℝ) ^ i :=
  hasSum_le (termGe e he) geoLo (sumR e he).hasSum

theorem tailLtOdd (e : ℕ → ℕ) (he : ∀ i, e i ≤ 1) (i0 : ℕ) (hi0 : Odd i0) (he0 : e i0 = 1) :
    ∑' i : ℕ, (e i : ℝ) * (-1/2 : ℝ) ^ i < 4/3 := by
  have hq : (0 : ℝ) < (1/2 : ℝ) ^ i0 := by positivity
  have hlt : (e i0 : ℝ) * (-1/2 : ℝ) ^ i0 < ((1/2 : ℝ) ^ i0 + (-1/2 : ℝ) ^ i0) / 2 := by
    rw [he0, show (-1/2 : ℝ) = -(1/2) by norm_num, hi0.neg_pow]
    push_cast
    linarith
  exact hasSum_lt (f := fun i : ℕ => (e i : ℝ) * (-1/2 : ℝ) ^ i)
    (g := fun i : ℕ => ((1/2 : ℝ) ^ i + (-1/2 : ℝ) ^ i) / 2) (i := i0)
    (termLe e he) hlt (sumR e he).hasSum geoHi

theorem tailGtEven (e : ℕ → ℕ) (he : ∀ i, e i ≤ 1) (i0 : ℕ) (hi0 : Even i0) (he0 : e i0 = 1) :
    -2/3 < ∑' i : ℕ, (e i : ℝ) * (-1/2 : ℝ) ^ i := by
  have hq : (0 : ℝ) < (1/2 : ℝ) ^ i0 := by positivity
  have hlt : ((-1/2 : ℝ) ^ i0 - (1/2 : ℝ) ^ i0) / 2 < (e i0 : ℝ) * (-1/2 : ℝ) ^ i0 := by
    rw [he0, show (-1/2 : ℝ) = -(1/2) by norm_num, hi0.neg_pow]
    push_cast
    linarith
  exact hasSum_lt (f := fun i : ℕ => ((-1/2 : ℝ) ^ i - (1/2 : ℝ) ^ i) / 2)
    (g := fun i : ℕ => (e i : ℝ) * (-1/2 : ℝ) ^ i) (i := i0)
    (termGe e he) hlt geoLo (sumR e he).hasSum

theorem DTailLt (m : ℕ) : ∑' i : ℕ, (D (m + i) : ℝ) * (-1/2 : ℝ) ^ i < 4/3 := by
  obtain ⟨i, hi, h1⟩ := DWitOdd m
  exact tailLtOdd (fun i => D (m + i)) (fun i => DLe _) i hi h1

theorem DTailGt (m : ℕ) (hm : 1 ≤ m) : -2/3 < ∑' i : ℕ, (D (m + i) : ℝ) * (-1/2 : ℝ) ^ i := by
  obtain ⟨i, hi, h1⟩ := DWitEven m hm
  exact tailGtEven (fun i => D (m + i)) (fun i => DLe _) i hi h1

-- Uniqueness: tails agree, so digits agree

theorem tsumSucc (e : ℕ → ℕ) (he : ∀ i, e i ≤ 1) :
    ∑' i : ℕ, (e i : ℝ) * (-1/2 : ℝ) ^ i =
      e 0 + (-1/2) * ∑' i : ℕ, (e (i + 1) : ℝ) * (-1/2 : ℝ) ^ i := by
  rw [(sumR e he).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, mul_one, pow_succ]
  congr 1
  apply tsum_congr
  intro i
  ring

theorem tailSucc (c : ℕ → ℕ) (hc : ∀ i, c i ≤ 1) (n : ℕ) :
    ∑' i : ℕ, (c (n + i) : ℝ) * (-1/2 : ℝ) ^ i =
      c n + (-1/2) * ∑' i : ℕ, (c (n + 1 + i) : ℝ) * (-1/2 : ℝ) ^ i := by
  have h := tsumSucc (fun i => c (n + i)) (fun i => hc _)
  have h3 : (fun i : ℕ => (c (n + (i + 1)) : ℝ) * (-1/2 : ℝ) ^ i) =
      (fun i : ℕ => (c (n + 1 + i) : ℝ) * (-1/2 : ℝ) ^ i) := by
    funext i
    rw [show n + (i + 1) = n + 1 + i by omega]
  rw [h3, add_zero] at h
  exact h

theorem digitEq (d : ℕ → ℕ) (hd : ∀ i, d i ≤ 1) (n : ℕ)
    (h : ∑' i : ℕ, (d (n + i) : ℝ) * (-1/2 : ℝ) ^ i = ∑' i : ℕ, (D (n + i) : ℝ) * (-1/2 : ℝ) ^ i) :
    d n = D n := by
  rw [tailSucc d hd n, tailSucc D DLe n] at h
  have a1 := tailGe (fun i => d (n + 1 + i)) (fun i => hd _)
  have a2 := tailLe (fun i => d (n + 1 + i)) (fun i => hd _)
  have b1 := DTailGt (n + 1) (by omega)
  have b2 := DTailLt (n + 1)
  have c1 : d n = 0 ∨ d n = 1 := by have := hd n; omega
  have c2 : D n = 0 ∨ D n = 1 := by have := DLe n; omega
  rcases c1 with h1 | h1 <;> rcases c2 with h2 | h2
  · rw [h1, h2]
  · rw [h1, h2] at h
    push_cast at h
    linarith
  · rw [h1, h2] at h
    push_cast at h
    linarith
  · rw [h1, h2]

theorem tailsEq (d : ℕ → ℕ) (hd : ∀ i, d i ≤ 1)
    (hs : HasSum (fun i : ℕ => (d i : ℝ) * (-1/2 : ℝ) ^ i) tau) (n : ℕ) :
    ∑' i : ℕ, (d (n + i) : ℝ) * (-1/2 : ℝ) ^ i = ∑' i : ℕ, (D (n + i) : ℝ) * (-1/2 : ℝ) ^ i := by
  induction n with
  | zero =>
    simp only [zero_add]
    rw [hs.tsum_eq, DSumR.tsum_eq]
  | succ n ih =>
    have hdn := digitEq d hd n ih
    rw [tailSucc d hd n, tailSucc D DLe n, hdn] at ih
    linarith

theorem eqD (d : ℕ → ℕ) (hd : ∀ i, d i ≤ 1)
    (hs : HasSum (fun i : ℕ => (d i : ℝ) * (-1/2 : ℝ) ^ i) tau) : d = D := by
  funext n
  exact digitEq d hd n (tailsEq d hd hs n)

end OMA.A289748Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a289748.main := by
  refine ⟨⟨OMA.A289748Proof.D, And.intro OMA.A289748Proof.DLe OMA.A289748Proof.DSumR⟩, ?_⟩
  intro d hd
  rcases hd with ⟨h1, h2⟩
  have hdD : d = OMA.A289748Proof.D := OMA.A289748Proof.eqD d h1 h2
  subst hdD
  exact OMA.A289748Proof.DSumQ
