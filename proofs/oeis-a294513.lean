import OMAStatements.S_oeis_a294513

namespace LangCriterion

/-- The numerator of `A / B` for natural numbers `A` and `B > 0`. -/
theorem num_div_nat (A B : ℕ) (hB : 0 < B) :
    ((A : ℚ) / B).num = ((A / Nat.gcd A B : ℕ) : ℤ) := by
  have hg0 : 0 < Nat.gcd A B := Nat.gcd_pos_of_pos_right A hB
  have hA : Nat.gcd A B ∣ A := Nat.gcd_dvd_left A B
  have hB' : Nat.gcd A B ∣ B := Nat.gcd_dvd_right A B
  have hcop : Nat.Coprime (A / Nat.gcd A B) (B / Nat.gcd A B) := Nat.coprime_div_gcd_div_gcd hg0
  have hBg : 0 < B / Nat.gcd A B := Nat.div_pos (Nat.le_of_dvd hB hB') hg0
  have hg' : ((Nat.gcd A B : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hg0.ne'
  have e : (A : ℚ) / B =
      (((A / Nat.gcd A B : ℕ) : ℤ) : ℚ) / (((B / Nat.gcd A B : ℕ) : ℤ) : ℚ) := by
    simp only [Int.cast_natCast]
    rw [Nat.cast_div hA hg', Nat.cast_div hB' hg']
    field_simp
  rw [e, Rat.num_div_eq_of_coprime (by exact_mod_cast hBg)]
  rw [Int.natAbs_natCast, Int.natAbs_natCast]
  exact hcop

/-- For `q > 0`, `N / q = (N * q.den) / q.num` as a quotient of natural numbers. -/
theorem div_eq (q : ℚ) (hq : 0 < q) (N : ℕ) :
    (N : ℚ) / q = ((N * q.den : ℕ) : ℚ) / (q.num.natAbs : ℕ) := by
  have hnum : ((q.num.natAbs : ℕ) : ℤ) = q.num := by
    rw [Int.natCast_natAbs, abs_of_nonneg (Rat.num_nonneg.mpr hq.le)]
  have hnum' : ((q.num.natAbs : ℕ) : ℚ) = (q.num : ℚ) := by rw [← Int.cast_natCast, hnum]
  have hn0 : (q.num : ℚ) ≠ 0 := by exact_mod_cast (Rat.num_pos.mpr hq).ne'
  have hd0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  rw [hnum']
  conv_lhs => rw [← Rat.num_div_den q]
  push_cast
  field_simp

/-- The harmonic-mean identity with the factor 2: for `q > 0` with odd numerator and `N > 0` with
`N * q.den` even, `q.den = 2 * (N / (2 q)).num / N` holds iff `N` is coprime to the numerator. -/
theorem hm_criterion_two (q : ℚ) (hq : 0 < q) (N : ℕ) (hN : 0 < N) (hodd : Odd q.num.natAbs)
    (heven : 2 ∣ N * q.den) :
    ((q.den : ℚ) = 2 * (((N : ℚ) / (2 * q)).num : ℚ) / N) ↔ Nat.Coprime N q.num.natAbs := by
  have hP : 0 < q.num.natAbs := Int.natAbs_pos.mpr (Rat.num_pos.mpr hq).ne'
  have hQ : 0 < q.den := q.den_pos
  have hcop : Nat.Coprime q.den q.num.natAbs := q.reduced.symm
  have e : (N : ℚ) / (2 * q) = ((N * q.den : ℕ) : ℚ) / ((2 * q.num.natAbs : ℕ) : ℚ) := by
    rw [mul_comm (2 : ℚ) q, ← div_div, div_eq q hq N]
    push_cast
    ring
  have hG : Nat.gcd (N * q.den) (2 * q.num.natAbs) = 2 * Nat.gcd N q.num.natAbs := by
    rw [Nat.Coprime.gcd_mul (N * q.den) (Nat.coprime_two_left.mpr hodd), Nat.gcd_eq_right heven,
      Nat.Coprime.gcd_mul_right_cancel N hcop]
  have hGd : 2 * Nat.gcd N q.num.natAbs ∣ N * q.den := by
    rw [← hG]; exact Nat.gcd_dvd_left _ _
  rw [e, num_div_nat _ _ (by omega), hG]
  have hg0 : 0 < Nat.gcd N q.num.natAbs := Nat.gcd_pos_of_pos_left _ hN
  have hg' : ((Nat.gcd N q.num.natAbs : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hg0.ne'
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hQ' : (q.den : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
  have e2 : 2 * ((((N * q.den / (2 * Nat.gcd N q.num.natAbs) : ℕ) : ℤ) : ℚ)) / N =
      (q.den : ℚ) / Nat.gcd N q.num.natAbs := by
    rw [Int.cast_natCast, Nat.cast_div hGd (by positivity)]
    push_cast
    field_simp
  rw [e2]
  constructor
  · intro h
    have h1 : ((Nat.gcd N q.num.natAbs : ℕ) : ℚ) = 1 := by
      field_simp at h
      linarith
    exact_mod_cast h1
  · intro h
    rw [Nat.Coprime] at h
    rw [h]
    simp

/-! ### A single-pass kernel computation of the reduced partial sums -/

/-- Add `1/D` to the fraction `p.1 / p.2` and reduce. -/
def step (p : ℕ × ℕ) (D : ℕ) : ℕ × ℕ :=
  ((p.1 * D + p.2) / Nat.gcd (p.1 * D + p.2) (p.2 * D),
    (p.2 * D) / Nat.gcd (p.1 * D + p.2) (p.2 * D))

/-- `pairs d N` is the reduced fraction `Sum_{k<N} 1/(d k)`. -/
def pairs (d : ℕ → ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | N + 1 => step (pairs d N) (d N)

theorem step_spec (p : ℕ × ℕ) (D : ℕ) (hy : 0 < p.2) (hD : 0 < D) :
    0 < (step p D).2 ∧ Nat.Coprime (step p D).1 (step p D).2 ∧
      ((step p D).1 : ℚ) / (step p D).2 = (p.1 : ℚ) / p.2 + 1 / (D : ℚ) := by
  have hB : 0 < p.2 * D := Nat.mul_pos hy hD
  have hg0 : 0 < Nat.gcd (p.1 * D + p.2) (p.2 * D) := Nat.gcd_pos_of_pos_right _ hB
  have hA : Nat.gcd (p.1 * D + p.2) (p.2 * D) ∣ p.1 * D + p.2 := Nat.gcd_dvd_left _ _
  have hB' : Nat.gcd (p.1 * D + p.2) (p.2 * D) ∣ p.2 * D := Nat.gcd_dvd_right _ _
  have hg' : ((Nat.gcd (p.1 * D + p.2) (p.2 * D) : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hg0.ne'
  refine ⟨Nat.div_pos (Nat.le_of_dvd hB hB') hg0, Nat.coprime_div_gcd_div_gcd hg0, ?_⟩
  simp only [step]
  rw [Nat.cast_div hA hg', Nat.cast_div hB' hg']
  have hy' : (p.2 : ℚ) ≠ 0 := by exact_mod_cast hy.ne'
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  push_cast
  field_simp

theorem pairs_spec (d : ℕ → ℕ) (hd : ∀ k, 0 < d k) (N : ℕ) :
    0 < (pairs d N).2 ∧ Nat.Coprime (pairs d N).1 (pairs d N).2 ∧
      ((pairs d N).1 : ℚ) / (pairs d N).2 = ∑ k ∈ Finset.range N, (1 : ℚ) / (d k : ℚ) := by
  induction N with
  | zero => simp [pairs]
  | succ N ih =>
    obtain ⟨h1, -, h3⟩ := ih
    obtain ⟨g1, g2, g3⟩ := step_spec (pairs d N) (d N) h1 (hd N)
    refine ⟨g1, g2, ?_⟩
    rw [pairs, g3, h3, Finset.sum_range_succ]

/-- The numerator of the sum, read off the pair. -/
theorem num_eq (d : ℕ → ℕ) (hd : ∀ k, 0 < d k) (N : ℕ) :
    (∑ k ∈ Finset.range N, (1 : ℚ) / (d k : ℚ)).num.natAbs = (pairs d N).1 := by
  obtain ⟨h1, h2, h3⟩ := pairs_spec d hd N
  rw [← h3]
  have : (((pairs d N).1 : ℤ) : ℚ) / (((pairs d N).2 : ℤ) : ℚ) =
      ((pairs d N).1 : ℚ) / (pairs d N).2 := by push_cast; rfl
  rw [← this, Rat.num_div_eq_of_coprime (by exact_mod_cast h1) (by simpa using h2)]
  simp

/-- Walk n = N, ..., N + fuel - 1, checking that gcd(n+1, numerator of Sum_{k<=n}) = 1 exactly
when n is not in the list `L`. -/
def chk (d : ℕ → ℕ) (L : List ℕ) : ℕ → ℕ → ℕ × ℕ → Bool
  | 0, _, _ => true
  | fuel + 1, N, p =>
    let p' := step p (d N)
    ((Nat.gcd (N + 1) p'.1 == 1) == !(L.contains N)) && chk d L fuel (N + 1) p'

theorem chk_spec (d : ℕ → ℕ) (L : List ℕ) (fuel : ℕ) :
    ∀ N, chk d L fuel N (pairs d N) = true → ∀ n, N ≤ n → n < N + fuel →
      (Nat.gcd (n + 1) (pairs d (n + 1)).1 = 1 ↔ n ∉ L) := by
  induction fuel with
  | zero => intro N _ n h1 h2; omega
  | succ fuel ih =>
    intro N h n h1 h2
    simp only [chk, Bool.and_eq_true] at h
    obtain ⟨hN, hrest⟩ := h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · have e : pairs d (N + 1) = step (pairs d N) (d N) := rfl
      rw [e]
      revert hN
      cases hc : L.contains N <;> simp_all
    · exact ih (N + 1) hrest n (by omega) (by omega)

end LangCriterion

namespace OMA.S_oeis_a294513


/-- The denominator (k+1)(3k+2) of the k-th summand. -/
def d (k : ℕ) : ℕ := (k + 1) * (3 * k + 2)

theorem d_pos (k : ℕ) : 0 < d k := by unfold d; positivity

theorem term_eq (k : ℕ) : (1 : ℚ) / ((k + 1) * (3 * k + 2)) = 1 / (d k : ℚ) := by
  simp [d]

theorem V_eq (n : ℕ) : V n = ∑ k ∈ Finset.range (n + 1), (1 : ℚ) / (d k : ℚ) := by
  simp only [V, term_eq]

theorem term_pos (k : ℕ) : 0 < (1 : ℚ) / (d k : ℚ) := by
  have := d_pos k
  positivity

theorem val_term (k : ℕ) : padicValRat 2 (1 / (d k : ℚ)) = -(padicValNat 2 (d k) : ℤ) := by
  rw [one_div, padicValRat.inv, padicValRat.of_nat]

theorem pow_two_mod_three (E : ℕ) : 2 ^ E % 3 = if E % 2 = 0 then 1 else 2 := by
  induction E with
  | zero => simp
  | succ E ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs with h1 h2 h2 <;> omega

/-- One of k+1, 3k+2 is odd, so a power of 2 dividing d k divides one of them. -/
theorem split (E k : ℕ) (h : 2 ^ E ∣ d k) : 2 ^ E ∣ k + 1 ∨ 2 ^ E ∣ 3 * k + 2 := by
  unfold d at h
  rcases Nat.even_or_odd k with he | ho
  · right
    have hodd : Odd (k + 1) := by
      rw [Nat.odd_iff]; rw [Nat.even_iff] at he; omega
    exact (Nat.Coprime.pow_left E (Nat.coprime_two_left.mpr hodd)).dvd_of_dvd_mul_left h
  · left
    have hodd : Odd (3 * k + 2) := by
      rw [Nat.odd_iff]; rw [Nat.odd_iff] at ho; omega
    exact (Nat.Coprime.pow_left E (Nat.coprime_two_left.mpr hodd)).dvd_of_dvd_mul_right h

/-- `e(k) < E` from non-divisibility. -/
theorem val_lt (E k : ℕ) (h : ¬ 2 ^ E ∣ d k) : padicValNat 2 (d k) < E := by
  by_contra hc
  push_neg at hc
  exact h ((padicValNat_dvd_iff_le (d_pos k).ne').mpr hc)

/-- Sum of positive rationals whose valuations are all at least c. -/
theorem le_sum {c : ℤ} {F : ℕ → ℚ} {S : Finset ℕ} (hS : S.Nonempty)
    (hF : ∀ i ∈ S, c ≤ padicValRat 2 (F i)) (hpos : ∀ i, 0 < F i) :
    c ≤ padicValRat 2 (∑ i ∈ S, F i) := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton k =>
    rw [Finset.sum_singleton]
    exact hF k (by simp)
  | cons s S' Hnot Hne Hind =>
    rw [Finset.cons_eq_insert, Finset.sum_insert Hnot]
    have h1 := hF s (by simp)
    have h2 := Hind (fun i hi => hF i (by simp [hi]))
    have hne : F s + ∑ i ∈ S', F i ≠ 0 :=
      (add_pos (hpos s) (Finset.sum_pos (fun i _ => hpos i) Hne)).ne'
    exact le_trans (le_min h1 h2) (padicValRat.min_le_padicValRat_add hne)

/-- The special case 2^A with A = 2j+3: the valuation of V(3,2; 2^A - 1) is -(A-1). -/
theorem val_special (j : ℕ) :
    padicValRat 2 (V (2 * 4 ^ (j + 1) - 1)) = -((2 * j + 2 : ℕ) : ℤ) := by
  set P := 4 ^ (j + 1) with hPdef
  have hP4 : 4 ≤ P := by
    rw [hPdef]; exact le_self_pow₀ (by norm_num) (by omega)
  have hP3 : P % 3 = 1 := by
    rw [hPdef, Nat.pow_mod]; norm_num
  have hPeven : P % 2 = 0 := by
    rw [hPdef, Nat.pow_mod]; norm_num
  have hP2 : P = 2 ^ (2 * j + 2) := by
    rw [hPdef, show 2 * j + 2 = 2 * (j + 1) by ring, pow_mul]; norm_num
  -- the four special indices
  obtain ⟨kb, hkb⟩ : ∃ kb, 3 * kb + 2 = 2 * P := ⟨(2 * P - 2) / 3, by omega⟩
  obtain ⟨kc, hkc⟩ : ∃ kc, 3 * kc + 2 = 5 * P := ⟨(5 * P - 2) / 3, by omega⟩
  set ka := P - 1 with hka
  set kd := 2 * P - 1 with hkd
  set S : Finset ℕ := {ka, kb, kc, kd} with hS
  have hsub : S ⊆ Finset.range (2 * P - 1 + 1) := by
    intro x hx
    simp only [hS, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_range]
    omega
  rw [V_eq, ← Finset.sum_sdiff hsub]
  -- the sum over S
  have hSsum : ∑ k ∈ S, (1 : ℚ) / (d k : ℚ) =
      1 / (d ka : ℚ) + 1 / (d kb : ℚ) + 1 / (d kc : ℚ) + 1 / (d kd : ℚ) := by
    rw [hS, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
      Finset.sum_insert (by simp; omega), Finset.sum_singleton]
    ring
  set k := ka with hk
  have hkodd : k % 2 = 1 := by omega
  have hPk : P = k + 1 := by omega
  set X : ℕ := 5 * (5 * k + 6) * (2 * k + 3) * (6 * k + 5) + 3 * (3 * k + 2) * (2 * k + 3) * (6 * k + 5)
    + 5 * (5 * k + 6) * (3 * k + 2) * (10 * k + 9) with hX
  set Y : ℕ := (3 * k + 2) * (5 * (5 * k + 6)) * (2 * k + 3) * (6 * k + 5) with hY
  have o5 : Odd (5 * k + 6) := by rw [Nat.odd_iff]; omega
  have o2 : Odd (2 * k + 3) := by rw [Nat.odd_iff]; omega
  have o6 : Odd (6 * k + 5) := by rw [Nat.odd_iff]; omega
  have o3 : Odd (3 * k + 2) := by rw [Nat.odd_iff]; omega
  have o10 : Odd (10 * k + 9) := by rw [Nat.odd_iff]; omega
  have odd5 : Odd 5 := by decide
  have odd3 : Odd 3 := by decide
  have hXodd : X % 2 = 1 := by
    rw [← Nat.odd_iff, hX]
    exact ((((odd5.mul o5).mul o2).mul o6).add_odd (((odd3.mul o3).mul o2).mul o6)).add_odd
      (((odd5.mul o5).mul o3).mul o10)
  have hYodd : Y % 2 = 1 := by
    rw [← Nat.odd_iff, hY]
    exact ((o3.mul (odd5.mul o5)).mul o2).mul o6
  have hSval : ∑ k ∈ S, (1 : ℚ) / (d k : ℚ) = (X : ℚ) / (((k + 1) * Y : ℕ) : ℚ) := by
    rw [hSsum]
    have ha : ((d ka : ℕ) : ℚ) = ((k : ℚ) + 1) * (3 * k + 2) := by
      simp [d, hk]
    have hb : ((d kb : ℕ) : ℚ) = ((2 * (k : ℚ) + 3) / 3) * (2 * (k + 1)) := by
      have : (3 : ℚ) * kb + 2 = 2 * (k + 1) := by
        have := hkb; rw [hPk] at this; exact_mod_cast this
      simp only [d]; push_cast
      have e1 : (kb : ℚ) + 1 = (2 * (k : ℚ) + 3) / 3 := by linarith
      rw [e1, this]
    have hc : ((d kc : ℕ) : ℚ) = ((5 * (k : ℚ) + 6) / 3) * (5 * (k + 1)) := by
      have : (3 : ℚ) * kc + 2 = 5 * (k + 1) := by
        have := hkc; rw [hPk] at this; exact_mod_cast this
      simp only [d]; push_cast
      have e1 : (kc : ℚ) + 1 = (5 * (k : ℚ) + 6) / 3 := by linarith
      rw [e1, this]
    have hd : ((d kd : ℕ) : ℚ) = (2 * (k : ℚ) + 2) * (6 * k + 5) := by
      have : kd = 2 * k + 1 := by omega
      rw [this]; simp [d]; ring
    rw [ha, hb, hc, hd, hX, hY]
    push_cast
    field_simp
    ring
  have hvS : padicValRat 2 (∑ k ∈ S, (1 : ℚ) / (d k : ℚ)) = -((2 * j + 2 : ℕ) : ℤ) := by
    rw [hSval]
    have hX0 : X ≠ 0 := by omega
    have hY0 : Y ≠ 0 := by omega
    rw [padicValRat.div (by exact_mod_cast hX0) (by positivity), padicValRat.of_nat,
      padicValRat.of_nat, padicValNat.mul (by omega) hY0,
      padicValNat.eq_zero_of_not_dvd (by omega : ¬ 2 ∣ X),
      padicValNat.eq_zero_of_not_dvd (by omega : ¬ 2 ∣ Y), ← hPk, hP2, padicValNat.prime_pow]
    simp
  -- the rest
  set R := Finset.range (2 * P - 1 + 1) \ S with hR
  have hRval : ∀ i ∈ R, -((2 * j + 1 : ℕ) : ℤ) ≤ padicValRat 2 (1 / (d i : ℚ)) := by
    intro i hi
    simp only [hR, Finset.mem_sdiff, Finset.mem_range, hS, Finset.mem_insert,
      Finset.mem_singleton] at hi
    obtain ⟨hi1, hi2⟩ := hi
    push_neg at hi2
    have hnd : ¬ 2 ^ (2 * j + 2) ∣ d i := by
      intro hdv
      have hi3 : i + 1 ≤ 2 * P := by omega
      rcases split _ _ hdv with h | h
      · rw [← hP2] at h
        obtain ⟨u, hu⟩ := h
        have hu3 : u < 3 := by
          by_contra hc
          have := Nat.mul_le_mul_left P (not_lt.mp hc)
          omega
        interval_cases u <;> omega
      · rw [← hP2] at h
        obtain ⟨u, hu⟩ := h
        have hu6 : u < 6 := by
          by_contra hc
          have := Nat.mul_le_mul_left P (not_lt.mp hc)
          omega
        interval_cases u <;> omega
    have hlt := val_lt _ _ hnd
    rw [val_term]
    omega
  by_cases hRe : R = ∅
  · rw [hRe, Finset.sum_empty, zero_add, hvS]
  · have hRne : R.Nonempty := Finset.nonempty_iff_ne_empty.mpr hRe
    have hle := le_sum hRne hRval (fun i => term_pos i)
    rw [add_comm, padicValRat.add_eq_of_lt, hvS]
    · exact (add_pos (Finset.sum_pos (fun i _ => term_pos i) (Finset.nonempty_of_ne_empty
        (by rw [hS]; simp))) (Finset.sum_pos (fun i _ => term_pos i) hRne)).ne'
    · exact (Finset.sum_pos (fun i _ => term_pos i) (by rw [hS]; simp)).ne'
    · exact (Finset.sum_pos (fun i _ => term_pos i) hRne).ne'
    · rw [hvS]
      push_cast at hle ⊢
      linarith

/-- The 2-adic valuation of V(3,2;N-1) as a function of N >= 1, with a = floor(log2 N). -/
def f (N : ℕ) : ℤ :=
  if Nat.log 2 N % 2 = 0 then -((Nat.log 2 N : ℤ) + 1)
  else if 2 ^ (Nat.log 2 N + 2) + 1 ≤ 3 * N then -((Nat.log 2 N : ℤ) + 2)
  else -((Nat.log 2 N : ℤ) - 1)

theorem f_even {N : ℕ} (h : Nat.log 2 N % 2 = 0) : f N = -((Nat.log 2 N : ℤ) + 1) := by
  simp [f, h]

theorem f_hi {N : ℕ} (h : Nat.log 2 N % 2 = 1) (h2 : 2 ^ (Nat.log 2 N + 2) + 1 ≤ 3 * N) :
    f N = -((Nat.log 2 N : ℤ) + 2) := by
  simp [f, h, h2]

theorem f_lo {N : ℕ} (h : Nat.log 2 N % 2 = 1) (h2 : ¬ 2 ^ (Nat.log 2 N + 2) + 1 ≤ 3 * N) :
    f N = -((Nat.log 2 N : ℤ) - 1) := by
  simp [f, h, h2]

theorem V_succ (n : ℕ) : V (n + 1) = V n + 1 / (d (n + 1) : ℚ) := by
  rw [V_eq, V_eq, Finset.sum_range_succ]

theorem V_pos (n : ℕ) : 0 < V n := by
  rw [V_eq]
  exact Finset.sum_pos (fun i _ => term_pos i) ⟨0, by simp⟩

theorem padicValNat_two_two : padicValNat 2 2 = 1 := by
  simpa using padicValNat.prime_pow (p := 2) 1

theorem val_V (n : ℕ) : padicValRat 2 (V n) = f (n + 1) := by
  induction n with
  | zero =>
    have hV : V 0 = 1 / (d 0 : ℚ) := by rw [V_eq]; simp
    rw [hV, val_term, f_even (by simp)]
    have hd : d 0 = 2 := rfl
    rw [hd, padicValNat_two_two]
    simp
  | succ n ih =>
    set N := n + 1 with hN
    set a := Nat.log 2 N with ha
    have h1 : 2 ^ a ≤ N := Nat.pow_log_le_self 2 (by omega)
    have h2 : N < 2 ^ (a + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
    have hpow : 2 ^ (a + 1) = 2 * 2 ^ a := by rw [pow_succ]; ring
    have hpow2 : 2 ^ (a + 2) = 4 * 2 ^ a := by rw [pow_succ, pow_succ]; ring
    have hm3 := pow_two_mod_three a
    have hm3' := pow_two_mod_three (a + 1)
    have hm3'' := pow_two_mod_three (a + 2)
    have hne : V n + 1 / (d (n + 1) : ℚ) ≠ 0 := (add_pos (V_pos n) (term_pos _)).ne'
    have hV0 : V n ≠ 0 := (V_pos n).ne'
    have ht0 : (1 : ℚ) / (d (n + 1) : ℚ) ≠ 0 := (term_pos _).ne'
    have hdN : d (n + 1) = (N + 1) * (3 * N + 2) := rfl
    rcases Nat.lt_or_ge (N + 1) (2 ^ (a + 1)) with hlt | hge
    · have hlog : Nat.log 2 (N + 1) = a := Nat.log_eq_of_pow_le_of_lt_pow (by omega) hlt
      rw [V_succ]
      rcases Nat.mod_two_eq_zero_or_one a with hpar | hpar
      · -- a even: the term has valuation above -(a+1)
        have hnd : ¬ 2 ^ (a + 1) ∣ d (n + 1) := by
          intro hdv
          rcases split _ _ hdv with h | h
          · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
          · obtain ⟨u, hu⟩ := h
            have hu3 : u < 3 := by
              by_contra hc
              have := Nat.mul_le_mul_left (2 ^ (a + 1)) (not_lt.mp hc)
              omega
            have hpar' : (a + 1) % 2 = 1 := by omega
            simp only [hpar', if_neg (by norm_num : ¬ (1 = 0))] at hm3'
            interval_cases u <;> omega
        have hlt' := val_lt _ _ hnd
        rw [padicValRat.add_eq_of_lt hne hV0 ht0, ih, f_even (by rw [← ha]; exact hpar),
          f_even (by rw [hlog]; exact hpar), hlog]
        rw [ih, f_even (by rw [← ha]; exact hpar), val_term]
        omega
      · rcases Nat.lt_or_ge (3 * N) (2 ^ (a + 2) + 1) with hthr | hthr
        · rcases Nat.lt_or_ge (3 * (N + 1)) (2 ^ (a + 2) + 1) with hthr' | hthr'
          · -- a odd, below the threshold: valuation -(a-1), the term is above it
            have ha3 : 3 ≤ a := by
              by_contra hc
              have ha1 : a = 1 := by omega
              rw [ha1] at h1 h2 hthr'
              norm_num at h1 h2 hthr'
              omega
            obtain ⟨b, hb⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
            have hPa : 2 ^ a = 2 * 2 ^ b := by rw [hb, pow_succ]; ring
            have hmb := pow_two_mod_three b
            have hbpar : b % 2 = 0 := by omega
            simp only [hbpar, if_pos] at hmb
            have hnd : ¬ 2 ^ b ∣ d (n + 1) := by
              intro hdv
              rcases split _ _ hdv with h | h
              · obtain ⟨u, hu⟩ := h
                have hu3 : u < 3 := by
                  by_contra hc
                  have := Nat.mul_le_mul_left (2 ^ b) (not_lt.mp hc)
                  omega
                interval_cases u <;> omega
              · obtain ⟨u, hu⟩ := h
                have hu8 : u < 8 := by
                  by_contra hc
                  have := Nat.mul_le_mul_left (2 ^ b) (not_lt.mp hc)
                  omega
                interval_cases u <;> omega
            have hlt' := val_lt _ _ hnd
            have hf1 : f N = -((a : ℤ) - 1) := f_lo (by rw [← ha]; exact hpar) (by rw [← ha]; omega)
            have hf2 : f (N + 1) = -((a : ℤ) - 1) :=
              by rw [f_lo (by rw [hlog]; exact hpar) (by rw [hlog]; omega), hlog]
            rw [padicValRat.add_eq_of_lt hne hV0 ht0, ih, hf1, hf2]
            rw [ih, hf1, val_term]
            omega
          · -- a odd, the step to i = (2^(a+2)+1)/3: the new term dominates
            have hpar' : (a + 2) % 2 = 1 := by omega
            simp only [hpar', if_neg (by norm_num : ¬ (1 = 0))] at hm3''
            have h3 : 3 * N + 2 = 2 ^ (a + 2) := by omega
            have hodd : ¬ 2 ∣ N + 1 := by omega
            have hval : padicValNat 2 (d (n + 1)) = a + 2 := by
              rw [hdN, padicValNat.mul (by omega) (by omega), h3, padicValNat.prime_pow,
                padicValNat.eq_zero_of_not_dvd hodd]
              ring
            have hf1 : f N = -((a : ℤ) - 1) := f_lo (by rw [← ha]; exact hpar) (by rw [← ha]; omega)
            have hf2 : f (N + 1) = -((a : ℤ) + 2) :=
              by rw [f_hi (by rw [hlog]; exact hpar) (by rw [hlog]; omega), hlog]
            rw [add_comm, padicValRat.add_eq_of_lt (by rwa [add_comm]) ht0 hV0, val_term, hval, hf2]
            · push_cast; ring
            · rw [val_term, hval, ih, hf1]
              push_cast
              omega
        · -- a odd, above the threshold: valuation -(a+2)
          have hnd : ¬ 2 ^ (a + 2) ∣ d (n + 1) := by
            intro hdv
            rcases split _ _ hdv with h | h
            · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
            · obtain ⟨u, hu⟩ := h
              have hu2 : u < 2 := by
                by_contra hc
                have := Nat.mul_le_mul_left (2 ^ (a + 2)) (not_lt.mp hc)
                omega
              interval_cases u <;> omega
          have hlt' := val_lt _ _ hnd
          have hf1 : f N = -((a : ℤ) + 2) := f_hi (by rw [← ha]; exact hpar) (by rw [← ha]; omega)
          have hf2 : f (N + 1) = -((a : ℤ) + 2) :=
            by rw [f_hi (by rw [hlog]; exact hpar) (by rw [hlog]; omega), hlog]
          rw [padicValRat.add_eq_of_lt hne hV0 ht0, ih, hf1, hf2]
          rw [ih, hf1, val_term]
          omega
    · have heq : N + 1 = 2 ^ (a + 1) := by omega
      have hlog : Nat.log 2 (N + 1) = a + 1 := by
        rw [heq, Nat.log_pow (by norm_num)]
      rcases Nat.mod_two_eq_zero_or_one a with hpar | hpar
      · rcases Nat.eq_zero_or_pos a with ha0 | ha0
        · -- N = 1: V 1 = 3/5
          have hN1 : N = 1 := by rw [ha0] at heq; omega
          have hn0 : n = 0 := by omega
          subst hn0
          have hV : V 1 = (3 : ℚ) / 5 := by
            rw [V_eq]; simp [Finset.sum_range_succ, d]; norm_num
          have hf : f (0 + 1 + 1) = 0 := by
            have hl : Nat.log 2 2 = 1 :=
              Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
            rw [show (0 + 1 + 1 : ℕ) = 2 by rfl]
            simp [f, hl]
          rw [hV, hf, padicValRat.div (by norm_num) (by norm_num)]
          have e3 : padicValRat 2 (3 : ℚ) = 0 := by
            rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
              padicValNat.eq_zero_of_not_dvd (by norm_num)]
            simp
          have e5 : padicValRat 2 (5 : ℚ) = 0 := by
            rw [show (5 : ℚ) = ((5 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
              padicValNat.eq_zero_of_not_dvd (by norm_num)]
            simp
          rw [e3, e5]
          simp
        · -- a even, a >= 2: the special step
          obtain ⟨j, hj⟩ : ∃ j, a = 2 * j + 2 := ⟨(a - 2) / 2, by omega⟩
          have hNj : n + 1 = 2 * 4 ^ (j + 1) - 1 := by
            have : 2 ^ (a + 1) = 2 * 4 ^ (j + 1) := by
              rw [hj, show 2 * j + 2 + 1 = 2 * (j + 1) + 1 by ring, pow_succ, pow_mul]
              norm_num; ring
            omega
          have hV : V N = V (2 * 4 ^ (j + 1) - 1) := by
            congr 1
          rw [hV, val_special j]
          have hpar' : Nat.log 2 (N + 1) % 2 = 1 := by rw [hlog]; omega
          have hthr : ¬ 2 ^ (Nat.log 2 (N + 1) + 2) + 1 ≤ 3 * (N + 1) := by
            rw [hlog, heq, show a + 1 + 2 = (a + 1) + 2 by ring, pow_add]
            omega
          rw [f_lo hpar' hthr, hlog, hj]
          push_cast
          ring
      · -- a odd: the new term 1/(2^(a+1) (3 2^(a+1) - 1)) lies above -(a+2)
        have hodd : ¬ 2 ∣ 3 * N + 2 := by omega
        have hval : padicValNat 2 (d (n + 1)) = a + 1 := by
          rw [hdN, padicValNat.mul (by omega) (by omega), heq, padicValNat.prime_pow,
            padicValNat.eq_zero_of_not_dvd hodd]
        have h2a : 2 ≤ 2 ^ a := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hthr : 2 ^ (Nat.log 2 N + 2) + 1 ≤ 3 * N := by rw [← ha]; omega
        have hf1 : f N = -((a : ℤ) + 2) := f_hi (by rw [← ha]; exact hpar) hthr
        have hpar' : (a + 1) % 2 = 0 := by omega
        have hf2 : f (N + 1) = -((a : ℤ) + 2) := by
          rw [f_even (by rw [hlog]; exact hpar'), hlog]
          push_cast; ring
        rw [V_succ, padicValRat.add_eq_of_lt hne hV0 ht0, ih, hf1, hf2]
        rw [ih, hf1, val_term, hval]
        push_cast
        omega

/-- For q > 0, valuation at most 0 makes the numerator odd. -/
theorem num_odd_of_val {q : ℚ} (hq : 0 < q) (h : padicValRat 2 q ≤ 0) : Odd q.num.natAbs := by
  by_contra hc
  have h2 : 2 ∣ q.num.natAbs := by
    rcases Nat.even_or_odd q.num.natAbs with he | ho
    · exact even_iff_two_dvd.mp he
    · exact absurd ho hc
  have hn0 : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_pos.mpr hq).ne'
  have hd : ¬ 2 ∣ q.den := by
    intro hd
    have := Nat.dvd_gcd h2 hd
    rw [q.reduced] at this
    omega
  have h1 : 1 ≤ padicValNat 2 q.num.natAbs := one_le_padicValNat_of_dvd hn0 h2
  have hv : padicValRat 2 q = padicValNat 2 q.num.natAbs - padicValNat 2 q.den := rfl
  rw [hv, padicValNat.eq_zero_of_not_dvd hd] at h
  omega

/-- For q > 0, negative valuation makes the denominator even. -/
theorem den_even_of_val {q : ℚ} (h : padicValRat 2 q < 0) : 2 ∣ q.den := by
  by_contra hd
  have hv : padicValRat 2 q = padicValNat 2 q.num.natAbs - padicValNat 2 q.den := rfl
  rw [hv, padicValNat.eq_zero_of_not_dvd hd] at h
  omega

/-- The numerator of V(3,2;n) is odd. -/
theorem num_odd (n : ℕ) : Odd (V n).num.natAbs := by
  apply num_odd_of_val (V_pos n)
  rw [val_V]
  unfold f
  split_ifs with h1 h2 <;> omega

/-- (n+1) times the denominator of V(3,2;n) is even. -/
theorem two_dvd (n : ℕ) : 2 ∣ (n + 1) * (V n).den := by
  rcases Nat.even_or_odd (n + 1) with he | ho
  · exact Dvd.dvd.mul_right (even_iff_two_dvd.mp he) _
  · apply Dvd.dvd.mul_left
    apply den_even_of_val
    rw [val_V]
    have h1 : 2 ^ Nat.log 2 (n + 1) ≤ n + 1 := Nat.pow_log_le_self 2 (by omega)
    rw [Nat.odd_iff] at ho
    unfold f
    split_ifs with h2 h3
    · omega
    · omega
    · have : Nat.log 2 (n + 1) ≠ 1 := by
        intro h
        rw [h] at h1 h3
        norm_num at h1 h3
        omega
      omega



/-- The conjectured identity at one n. -/
def ConjAt (n : ℕ) : Prop := (a n : ℚ) = 2 * (b (n + 1) : ℚ) / ((n : ℚ) + 1)

/-- The conjecture stated in A294513. -/
def Conjecture : Prop := ∀ n : ℕ, (a n : ℚ) = 2 * (b (n + 1) : ℚ) / ((n : ℚ) + 1)

theorem harmonic_eq (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 (n + 1), (1 : ℚ) / ((k : ℚ) * (3 * k - 1) / 2) = 2 * V n := by
  rw [V, Finset.mul_sum]
  have hI : Finset.Icc 1 (n + 1) = Finset.Ico 1 (n + 1 + 1) := rfl
  rw [hI, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  have e : (3 * ((1 : ℚ) + k) - 1) = 3 * k + 2 := by ring
  rw [e, add_comm (1 : ℚ) (k : ℚ)]
  field_simp

/-- The criterion: the conjectured identity holds at n iff gcd(n+1, numerator of V(3,2;n)) = 1. -/
theorem conj_at_iff (n : ℕ) : ConjAt n ↔ Nat.Coprime (n + 1) (V n).num.natAbs := by
  have h := LangCriterion.hm_criterion_two (V n) (V_pos n) (n + 1) (Nat.succ_pos n) (num_odd n)
    (two_dvd n)
  rw [ConjAt, a, b, harmonic_eq]
  push_cast at h ⊢
  exact h

theorem conjecture_iff : Conjecture ↔ ∀ n : ℕ, Nat.Coprime (n + 1) (V n).num.natAbs :=
  forall_congr' conj_at_iff

theorem fails_iff (n : ℕ) :
    ¬ ConjAt n ↔ Nat.gcd (n + 1) (LangCriterion.pairs d (n + 1)).1 ≠ 1 := by
  rw [conj_at_iff, Nat.Coprime, V_eq, LangCriterion.num_eq d d_pos]

theorem chk_true : LangCriterion.chk d [1891] 30000 0 (LangCriterion.pairs d 0) = true := by
  decide +kernel

/-- For n < 30000 the conjecture fails exactly at n = 1891. -/
theorem failures_below : ∀ n : ℕ, n < 30000 → (¬ ConjAt n ↔ n ∈ [1891]) := by
  intro n hn
  have h := LangCriterion.chk_spec d [1891] 30000 0 chk_true n (Nat.zero_le n) (by omega)
  rw [fails_iff]
  tauto

/-- n = 1891 is the first counterexample. -/
theorem first_counterexample : ¬ ConjAt 1891 ∧ ∀ n < 1891, ConjAt n := by
  refine ⟨(failures_below 1891 (by norm_num)).mpr (by simp), fun n hn => ?_⟩
  by_contra h
  have := (failures_below n (by omega)).mp h
  simp at this
  omega


end OMA.S_oeis_a294513

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a294513.main) :=
  fun h => OMA.S_oeis_a294513.first_counterexample.1 (h 1891)
