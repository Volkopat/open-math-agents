import OMAStatements.S_oeis_a069517

namespace OMA.S_oeis_a069517

-- Helpers. The machine started on 2^v * m (m odd) walks left over v zero cells, turns at
-- the first one-cell, then runs a binary counter on the v cells below it until the carry
-- leaves the tape on the right. Block time: T 0 = 0, T (k+1) = 2 T k + k + 3.

def bcT : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 * bcT k + k + 3

theorem bc_T_int (k : ℕ) : (bcT k : ℤ) = 2 ^ (k + 2) - k - 4 := by
  induction k with
  | zero => norm_num [bcT]
  | succ k ih =>
    have h : bcT (k + 1) = 2 * bcT k + k + 3 := rfl
    rw [h]
    push_cast
    rw [ih]
    ring

theorem bc_it (k : ℕ) (c : Cfg) : step^[k + 1] c = step^[k] (step c) := rfl

theorem bc_add (m : ℕ) : ∀ (n : ℕ) (c : Cfg), step^[m + n] c = step^[m] (step^[n] c) := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ n ih => intro c; exact ih (step c)

theorem bc_upd_self (tp : ℤ → Bool) (p : ℤ) (x : Bool) (h : tp p = x) :
    Function.update tp p x = tp := by
  funext q
  rw [Function.update_apply]
  by_cases hq : q = p
  · rw [if_pos hq, hq, h]
  · rw [if_neg hq]

theorem bc_upd2 (tp : ℤ → Bool) (b : ℤ) (h : tp b = false) :
    Function.update (Function.update tp b true) b false = tp := by
  funext q
  rw [Function.update_apply, Function.update_apply]
  by_cases hq : q = b
  · rw [if_pos hq, hq, h]
  · rw [if_neg hq, if_neg hq]

theorem bc_raw0f (p : ℤ) (tp : ℤ → Bool) (h : tp p = false) :
    step ⟨0, p, tp⟩ = ⟨0, p + 1, Function.update tp p false⟩ := by
  first
  | (simp only [step, h]; done)
  | (unfold step; simp only [h]; rfl)

theorem bc_raw0t (p : ℤ) (tp : ℤ → Bool) (h : tp p = true) :
    step ⟨0, p, tp⟩ = ⟨1, p - 1, Function.update tp p true⟩ := by
  first
  | (simp only [step, h]; done)
  | (unfold step; simp only [h]; rfl)

theorem bc_s1f (p : ℤ) (tp : ℤ → Bool) (h : tp p = false) :
    step ⟨1, p, tp⟩ = ⟨0, p + 1, Function.update tp p true⟩ := by
  first
  | (simp only [step, h]; done)
  | (unfold step; simp only [h]; rfl)

theorem bc_s1t (p : ℤ) (tp : ℤ → Bool) (h : tp p = true) :
    step ⟨1, p, tp⟩ = ⟨1, p - 1, Function.update tp p false⟩ := by
  first
  | (simp only [step, h]; done)
  | (unfold step; simp only [h]; rfl)

theorem bc_s0f (p : ℤ) (tp : ℤ → Bool) (h : tp p = false) :
    step ⟨0, p, tp⟩ = ⟨0, p + 1, tp⟩ := by
  rw [bc_raw0f p tp h, bc_upd_self tp p false h]

theorem bc_s0t (p : ℤ) (tp : ℤ → Bool) (h : tp p = true) :
    step ⟨0, p, tp⟩ = ⟨1, p - 1, tp⟩ := by
  rw [bc_raw0t p tp h, bc_upd_self tp p true h]

theorem bc_walk (j : ℕ) : ∀ (b : ℤ) (tp : ℤ → Bool), (∀ i : ℕ, i < j → tp (b + i) = false) →
    step^[j] ⟨0, b, tp⟩ = ⟨0, b + j, tp⟩ ∧
      ∀ s : ℕ, s ≤ j → (step^[s] ⟨0, b, tp⟩).pos = b + s := by
  induction j with
  | zero =>
    intro b tp _
    refine ⟨?_, ?_⟩
    · simp
    · intro s hs
      have hs0 : s = 0 := by omega
      subst hs0
      simp
  | succ j ih =>
    intro b tp h
    have h0 : tp b = false := by
      have h1 := h 0 (by omega)
      simpa using h1
    have hs0 := bc_s0f b tp h0
    have h' : ∀ i : ℕ, i < j → tp (b + 1 + i) = false := by
      intro i hi
      have h1 := h (i + 1) (by omega)
      have e : b + ((i + 1 : ℕ) : ℤ) = b + 1 + (i : ℤ) := by push_cast; ring
      rw [e] at h1
      exact h1
    obtain ⟨ih1, ih2⟩ := ih (b + 1) tp h'
    refine ⟨?_, ?_⟩
    · rw [bc_it, hs0, ih1]
      congr 1
      push_cast
      ring
    · intro s hs
      rcases s with _ | s
      · simp
      · rw [bc_it, hs0, ih2 s (by omega)]
        push_cast
        ring

theorem bc_block (k : ℕ) : ∀ (b : ℤ) (tp : ℤ → Bool),
    (∀ i : ℕ, i < k → tp (b + i) = false) → tp (b + k) = true →
    step^[bcT k] ⟨1, b + k - 1, tp⟩ = ⟨1, b - 1, tp⟩ ∧
      ∀ s : ℕ, s < bcT k → b ≤ (step^[s] ⟨1, b + k - 1, tp⟩).pos := by
  induction k with
  | zero =>
    intro b tp _ _
    refine ⟨?_, ?_⟩
    · simp [bcT]
    · intro s hs
      simp [bcT] at hs
  | succ k ih =>
    intro b tp hz hw
    have hz' : ∀ i : ℕ, i < k → tp (b + 1 + i) = false := by
      intro i hi
      have h1 := hz (i + 1) (by omega)
      have e : b + ((i + 1 : ℕ) : ℤ) = b + 1 + (i : ℤ) := by push_cast; ring
      rw [e] at h1
      exact h1
    have hw' : tp (b + 1 + k) = true := by
      have e : b + ((k + 1 : ℕ) : ℤ) = b + 1 + (k : ℤ) := by push_cast; ring
      rw [e] at hw
      exact hw
    have hb : tp b = false := by
      have h1 := hz 0 (by omega)
      simpa using h1
    have hz2 : ∀ i : ℕ, i < k → (Function.update tp b true) (b + 1 + i) = false := by
      intro i hi
      have hne : b + 1 + (i : ℤ) ≠ b := by omega
      rw [Function.update_apply, if_neg hne]
      exact hz' i hi
    have hw2 : (Function.update tp b true) (b + 1 + k) = true := by
      have hne : b + 1 + (k : ℤ) ≠ b := by omega
      rw [Function.update_apply, if_neg hne]
      exact hw'
    have hb2 : (Function.update tp b true) b = true := by
      rw [Function.update_apply, if_pos (rfl : b = b)]
    obtain ⟨A1, A2⟩ := ih (b + 1) tp hz' hw'
    obtain ⟨B1, B2⟩ := ih (b + 1) (Function.update tp b true) hz2 hw2
    obtain ⟨W1, W2⟩ := bc_walk k (b + 1) (Function.update tp b true) hz2
    have hbb : b + 1 - 1 = b := by ring
    rw [hbb] at A1 B1
    have S1 : step ⟨1, b, tp⟩ = ⟨0, b + 1, Function.update tp b true⟩ := bc_s1f b tp hb
    have S2 : step ⟨0, b + 1 + k, Function.update tp b true⟩ =
        ⟨1, b + 1 + k - 1, Function.update tp b true⟩ := bc_s0t _ _ hw2
    have S3 : step ⟨1, b, Function.update tp b true⟩ = ⟨1, b - 1, tp⟩ := by
      rw [bc_s1t b _ hb2, bc_upd2 tp b hb]
    have hc0 : (⟨1, b + ((k + 1 : ℕ) : ℤ) - 1, tp⟩ : Cfg) = ⟨1, b + 1 + k - 1, tp⟩ := by
      congr 1
      push_cast
      ring
    rw [hc0]
    have hT : bcT (k + 1) = 1 + (bcT k + (1 + (k + (1 + bcT k)))) := by
      show 2 * bcT k + k + 3 = _
      omega
    refine ⟨?_, ?_⟩
    · rw [hT, bc_add, bc_add, bc_add, bc_add, bc_add]
      simp only [Function.iterate_one]
      rw [A1, S1, W1, S2, B1, S3]
    · intro s hs
      rw [hT] at hs
      rcases Nat.lt_or_ge s (bcT k) with h1 | h1
      · have h5 := A2 s h1
        linarith
      · rcases Nat.lt_or_ge s (1 + (k + (1 + bcT k))) with h2 | h2
        · obtain ⟨r, rfl⟩ : ∃ r, s = r + bcT k := ⟨s - bcT k, by omega⟩
          rw [bc_add, A1]
          rcases r with _ | r
          · simp
          · rw [bc_it, S1, W2 r (by omega)]
            omega
        · obtain ⟨r, rfl⟩ : ∃ r, s = r + (1 + (k + (1 + bcT k))) :=
            ⟨s - (1 + (k + (1 + bcT k))), by omega⟩
          rw [bc_add, bc_add, bc_add, bc_add]
          simp only [Function.iterate_one]
          rw [A1, S1, W1, S2]
          rcases Nat.lt_or_ge r (bcT k) with h3 | h3
          · have h5 := B2 r h3
            linarith
          · have hr : r = bcT k := by omega
            first
            | (rw [hr, B1]; done)
            | (rw [hr, B1]; exact le_refl _)

theorem bc_two_adic (N : ℕ) : ∀ n : ℕ, n ≤ N → 0 < n → ∃ v m : ℕ, m % 2 = 1 ∧ n = 2 ^ v * m := by
  induction N with
  | zero => intro n h1 h2; omega
  | succ N ih =>
    intro n hN hn
    rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
    · obtain ⟨v, m, hm, hnm⟩ := ih (n / 2) (by omega) (by omega)
      refine ⟨v + 1, m, hm, ?_⟩
      have e : n = 2 * (n / 2) := by omega
      rw [e, hnm]
      ring
    · exact ⟨0, n, h1, by ring⟩

theorem bc_bit_low (v m i : ℕ) (hi : i < v) : (2 ^ v * m).testBit i = false := by
  rw [Nat.testBit_two_pow_mul]
  simp
  omega

theorem bc_bit_v (v m : ℕ) (hm : m % 2 = 1) : (2 ^ v * m).testBit v = true := by
  rw [Nat.testBit_two_pow_mul]
  simp
  omega

theorem bc_mu (d : ℕ) :
    ∑ x ∈ d.divisors, (ArithmeticFunction.moebius x : ℤ) = if d = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f d)
    ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

theorem bc_filter (s e : ℕ) (he : e % 2 = 1) :
    (2 ^ s * e).divisors.filter (fun x => x % 2 = 1) = e.divisors := by
  ext x
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hx, -⟩, hodd⟩
    refine ⟨?_, by omega⟩
    have hc : Nat.Coprime x 2 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      omega
    exact (Nat.Coprime.pow_right s hc).dvd_of_dvd_mul_left hx
  · rintro ⟨hx, hne⟩
    refine ⟨⟨dvd_mul_of_dvd_right hx _, mul_ne_zero (pow_ne_zero _ (by norm_num)) hne⟩, ?_⟩
    exact Nat.odd_iff.mp (Odd.of_dvd_nat (Nat.odd_iff.mpr he) hx)

theorem bc_a_formula (s e : ℕ) (he : e % 2 = 1) :
    a (2 ^ s * e) = 2 * (if e = 1 then 1 else 0) - (if 2 ^ s * e = 1 then 1 else 0) := by
  have hterm : ∀ x : ℕ, (-1 : ℤ) ^ (x + 1) * ArithmeticFunction.moebius x =
      (if x % 2 = 1 then 2 * ArithmeticFunction.moebius x else 0) -
        ArithmeticFunction.moebius x := by
    intro x
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · have hx : Odd (x + 1) := Nat.odd_iff.mpr (by omega)
      have hc : ¬ (x % 2 = 1) := by omega
      rw [hx.neg_one_pow, if_neg hc]
      ring
    · have hx : Even (x + 1) := Nat.even_iff.mpr (by omega)
      rw [hx.neg_one_pow, if_pos h]
      ring
  have hf : ∑ x ∈ (2 ^ s * e).divisors.filter (fun x => x % 2 = 1),
      (2 : ℤ) * ArithmeticFunction.moebius x =
      ∑ x ∈ (2 ^ s * e).divisors,
        (if x % 2 = 1 then 2 * ArithmeticFunction.moebius x else 0) :=
    by rw [Finset.sum_filter]
  unfold a
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← hf, bc_filter s e he, ← Finset.mul_sum, bc_mu e,
    bc_mu (2 ^ s * e)]

theorem bc_a_pow (j : ℕ) : a (2 ^ j) = if j = 0 then 1 else 2 := by
  have h := bc_a_formula j 1 (by norm_num)
  rw [mul_one] at h
  rw [h]
  rcases j with _ | j
  · norm_num
  · have h2 : (2 : ℕ) ^ (j + 1) ≠ 1 := by
      simp
    have h4 : j + 1 ≠ 0 := by omega
    rw [if_neg h2, if_neg h4]
    norm_num

theorem bc_sum_pow (v : ℕ) : ∑ j ∈ Finset.range (v + 1),
    a (2 ^ j) ^ 2 * ((Nat.totient (2 ^ j) : ℕ) : ℤ) = 2 ^ (v + 2) - 3 := by
  induction v with
  | zero =>
    rw [Finset.sum_range_succ, Finset.sum_range_zero, bc_a_pow]
    norm_num
  | succ v ih =>
    rw [Finset.sum_range_succ, ih, bc_a_pow, Nat.totient_prime_pow_succ Nat.prime_two]
    have h4 : v + 1 ≠ 0 := by omega
    rw [if_neg h4, show (2 : ℕ) - 1 = 1 from rfl, mul_one]
    push_cast
    ring

theorem bc_sum (v m : ℕ) (hm : m % 2 = 1) :
    ∑ d ∈ (2 ^ v * m).divisors, a d ^ 2 * ((Nat.totient d : ℕ) : ℤ) = 2 ^ (v + 2) - 3 := by
  have hm0 : m ≠ 0 := by omega
  have hn0 : 2 ^ v * m ≠ 0 := mul_ne_zero (pow_ne_zero v (by norm_num)) hm0
  have hsub : (2 ^ v).divisors ⊆ (2 ^ v * m).divisors :=
    Nat.divisors_subset_of_dvd hn0 (dvd_mul_right _ _)
  have key : ∑ d ∈ (2 ^ v).divisors, a d ^ 2 * ((Nat.totient d : ℕ) : ℤ) =
      ∑ d ∈ (2 ^ v * m).divisors, a d ^ 2 * ((Nat.totient d : ℕ) : ℤ) := by
    apply Finset.sum_subset hsub
    intro x hx hx'
    have hx0 : 0 < x := Nat.pos_of_mem_divisors hx
    obtain ⟨s, e, he, rfl⟩ := bc_two_adic x x le_rfl hx0
    by_cases he1 : e = 1
    · exfalso
      apply hx'
      subst he1
      rw [Nat.mem_divisors] at hx ⊢
      rw [mul_one] at hx ⊢
      refine ⟨Nat.pow_dvd_pow 2 ?_, pow_ne_zero v (by norm_num)⟩
      by_contra hsv
      have hsv' : v + 1 ≤ s := by omega
      have h1 : 2 ^ (v + 1) ∣ 2 ^ v * m := (Nat.pow_dvd_pow 2 hsv').trans hx.1
      rw [pow_succ] at h1
      have h2 : 2 ∣ m := (mul_dvd_mul_iff_left (pow_ne_zero v (by norm_num))).mp h1
      omega
    · have hne : 2 ^ s * e ≠ 1 := by
        intro h
        apply he1
        exact Nat.eq_one_of_mul_eq_one_left h
      rw [bc_a_formula s e he, if_neg he1, if_neg hne]
      simp
  rw [← key, Nat.sum_divisors_prime_pow Nat.prime_two]
  exact bc_sum_pow v

end OMA.S_oeis_a069517

theorem OMA.solution : type_of% @OMA.S_oeis_a069517.main := by
  intro n hn
  obtain ⟨v, m, hm, rfl⟩ := OMA.S_oeis_a069517.bc_two_adic n n le_rfl (by omega)
  have hz : ∀ i : ℕ, i < v →
      (OMA.S_oeis_a069517.init (2 ^ v * m)).tape ((0 : ℤ) + i) = false := by
    intro i hi
    have hc : (0 : ℤ) ≤ (0 : ℤ) + (i : ℤ) := by omega
    have e1 : (OMA.S_oeis_a069517.init (2 ^ v * m)).tape ((0 : ℤ) + i) =
        (2 ^ v * m).testBit i := by
      show (if (0 : ℤ) ≤ (0 : ℤ) + (i : ℤ) then (2 ^ v * m).testBit ((0 : ℤ) + (i : ℤ)).toNat
        else false) = _
      rw [if_pos hc]
      congr 1
      omega
    rw [e1]
    exact OMA.S_oeis_a069517.bc_bit_low v m i hi
  have hw : (OMA.S_oeis_a069517.init (2 ^ v * m)).tape ((0 : ℤ) + v) = true := by
    have hc : (0 : ℤ) ≤ (0 : ℤ) + (v : ℤ) := by omega
    have e1 : (OMA.S_oeis_a069517.init (2 ^ v * m)).tape ((0 : ℤ) + v) =
        (2 ^ v * m).testBit v := by
      show (if (0 : ℤ) ≤ (0 : ℤ) + (v : ℤ) then (2 ^ v * m).testBit ((0 : ℤ) + (v : ℤ)).toNat
        else false) = _
      rw [if_pos hc]
      congr 1
      omega
    rw [e1]
    exact OMA.S_oeis_a069517.bc_bit_v v m hm
  have hc : OMA.S_oeis_a069517.init (2 ^ v * m) =
      ⟨0, 0, (OMA.S_oeis_a069517.init (2 ^ v * m)).tape⟩ := rfl
  obtain ⟨W1, W2⟩ := OMA.S_oeis_a069517.bc_walk v 0 (OMA.S_oeis_a069517.init (2 ^ v * m)).tape hz
  obtain ⟨B1, B2⟩ :=
    OMA.S_oeis_a069517.bc_block v 0 (OMA.S_oeis_a069517.init (2 ^ v * m)).tape hz hw
  have S := OMA.S_oeis_a069517.bc_s0t _ _ hw
  refine ⟨OMA.S_oeis_a069517.bcT v + (1 + v), ⟨?_, ?_⟩, ?_⟩
  · show (OMA.S_oeis_a069517.step^[OMA.S_oeis_a069517.bcT v + (1 + v)]
      (OMA.S_oeis_a069517.init (2 ^ v * m))).pos < 0
    rw [OMA.S_oeis_a069517.bc_add, OMA.S_oeis_a069517.bc_add, hc, W1]
    simp only [Function.iterate_one]
    rw [S, B1]
    show (0 : ℤ) - 1 < 0
    norm_num
  · intro s hs
    show 0 ≤ (OMA.S_oeis_a069517.step^[s] (OMA.S_oeis_a069517.init (2 ^ v * m))).pos
    rw [hc]
    rcases Nat.lt_or_ge s (v + 1) with h1 | h1
    · rw [W2 s (by omega)]
      omega
    · obtain ⟨r, rfl⟩ : ∃ r, s = r + (1 + v) := ⟨s - (1 + v), by omega⟩
      rw [OMA.S_oeis_a069517.bc_add, OMA.S_oeis_a069517.bc_add, W1]
      simp only [Function.iterate_one]
      rw [S]
      exact B2 r (by omega)
  · rw [OMA.S_oeis_a069517.bc_sum v m hm]
    push_cast
    rw [OMA.S_oeis_a069517.bc_T_int]
    ring
