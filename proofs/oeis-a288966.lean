import OMAStatements.S_oeis_a288966
import Mathlib

open OMA.S_oeis_a288966


def HInv (n : ℕ) (s : ℤ × ℤ × ℤ × ℤ) (i : ℕ) : Prop :=
  s.2.1 = (n : ℤ) - (s.2.2.1 + 1) * s.2.2.2 ∧ 1 ≤ s.2.2.1 ∧ 1 ≤ s.2.2.2 ∧
    (n : ℤ) < (s.2.2.1 + 1) * (s.2.2.2 + 1) ∧
    (∀ d : ℕ, 2 ≤ d → (d : ℤ) ≤ s.2.2.1 → ¬ d ∣ n) ∧
    s.2.2.1 + ((n : ℤ) - s.2.2.2) = (i : ℤ) + 1

theorem run_succ (n k : ℕ) (s : ℤ × ℤ × ℤ × ℤ) (h : run n k = some s) :
    run n (k + 1) = match body s with
      | none => none
      | some s' => if 0 < s'.2.2.2 then some s' else none := by
  simp only [run, h]
  try rfl

/-- p + 1 is at most the least prime factor. -/
theorem p_le (n : ℕ) (hn : 1 < n) (p : ℤ) (hp : 1 ≤ p) (hd : ∀ d : ℕ, 2 ≤ d → (d : ℤ) ≤ p → ¬ d ∣ n) :
    p + 1 ≤ (Nat.minFac n : ℤ) := by
  by_contra hc
  have h2 : 2 ≤ Nat.minFac n := (Nat.minFac_prime (by omega)).two_le
  exact hd (Nat.minFac n) h2 (by omega) (Nat.minFac_dvd n)

theorem base (n : ℕ) (hn : 1 < n) : ∃ s, run n 1 = some s ∧ HInv n s 1 := by
  refine ⟨(0, 0 + (0 + 1) - ((n : ℤ) - 1), 0 + 1, (n : ℤ) - 1), ?_, ?_⟩
  · have h1 : run n 1 = match body (0, 0, 0, (n : ℤ)) with
        | none => none
        | some s' => if 0 < s'.2.2.2 then some s' else none := run_succ n 0 _ rfl
    rw [h1]
    have hb : body (0, 0, 0, (n : ℤ)) = some (0, 0 + (0 + 1) - ((n : ℤ) - 1), 0 + 1, (n : ℤ) - 1) := by
      simp only [body]
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by simp; omega)]
    rw [hb]
    simp only
    rw [if_pos (by omega)]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only
    · ring
    · norm_num
    · omega
    · nlinarith
    · intro d hd1 hd2; omega
    · push_cast; ring

theorem step (n : ℕ) (hn : 1 < n) (s : ℤ × ℤ × ℤ × ℤ) (i : ℕ) (hI : HInv n s i) (hy : s.2.1 ≠ 0) :
    ∃ s', body s = some s' ∧ 0 < s'.2.2.2 ∧ HInv n s' (i + 1) := by
  obtain ⟨x, y, p, q⟩ := s
  obtain ⟨hy', hp, hq, hlt, hd, hphi⟩ := hI
  simp only at hy' hp hq hlt hd hphi hy
  have hpn := p_le n hn p hp hd
  have hmf : (Nat.minFac n : ℤ) ≤ n := by exact_mod_cast Nat.minFac_le (by omega)
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · refine ⟨(y + q, (y + q) + p - (q - 1), p, q - 1), ?_, ?_, ?_⟩
    · simp only [body]; rw [if_pos hneg]
    · simp only
      by_contra hc
      have : q = 1 := by omega
      subst this
      nlinarith
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only
      · rw [hy']; ring
      · exact hp
      · by_contra hc
        have : q = 1 := by omega
        subst this
        nlinarith
      · nlinarith
      · exact hd
      · push_cast; linarith
  · refine ⟨(y - (p + 1), (y - (p + 1)) + (p + 1) - q, p + 1, q), ?_, ?_, ?_⟩
    · simp only [body]; rw [if_neg (by omega), if_pos hpos]
    · simp only; omega
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only
      · rw [hy']; ring
      · omega
      · exact hq
      · nlinarith
      · intro d hd2 hdp hdiv
        rcases lt_or_eq_of_le hdp with hl | he
        · exact hd d hd2 (by omega) hdiv
        · obtain ⟨c, hc⟩ := hdiv
          have hcz : (n : ℤ) = (d : ℤ) * c := by exact_mod_cast hc
          rw [he] at hcz
          have h1 : (p + 1) * q < (p + 1) * c := by nlinarith
          have h2 : (p + 1) * c < (p + 1) * (q + 1) := by nlinarith
          have h3 : q < c := lt_of_mul_lt_mul_left h1 (by omega)
          have h4 : (c : ℤ) < q + 1 := lt_of_mul_lt_mul_left h2 (by omega)
          omega
      · push_cast; linarith

theorem brk (n : ℕ) (hn : 1 < n) (s : ℤ × ℤ × ℤ × ℤ) (i : ℕ) (hI : HInv n s i) (hy : s.2.1 = 0) :
    body s = none ∧ i + 1 = n + Nat.minFac n - n / Nat.minFac n - 1 := by
  obtain ⟨x, y, p, q⟩ := s
  obtain ⟨hy', hp, hq, hlt, hd, hphi⟩ := hI
  simp only at hy' hp hq hlt hd hphi hy
  subst hy
  refine ⟨?_, ?_⟩
  · simp only [body]
    rw [if_neg (lt_irrefl 0), if_neg (lt_irrefl 0), if_pos (Or.inl (by omega))]
  · have hpn := p_le n hn p hp hd
    have hnq : (n : ℤ) = (p + 1) * q := by linarith
    -- p + 1 is the least prime factor
    obtain ⟨pn, hpn'⟩ : ∃ m : ℕ, (m : ℤ) = p + 1 := ⟨(p + 1).toNat, by omega⟩
    obtain ⟨qn, hqn'⟩ : ∃ m : ℕ, (m : ℤ) = q := ⟨q.toNat, by omega⟩
    have hnat : n = pn * qn := by
      have : ((n : ℕ) : ℤ) = ((pn * qn : ℕ) : ℤ) := by push_cast; rw [hpn', hqn']; exact hnq
      exact_mod_cast this
    have hmin : Nat.minFac n = pn := by
      apply le_antisymm
      · exact Nat.minFac_le_of_dvd (by omega) ⟨qn, hnat⟩
      · have := hpn; rw [← hpn'] at this; exact_mod_cast this
    have hpos : 0 < pn := by omega
    have hdiv : n / Nat.minFac n = qn := by
      rw [hmin, hnat, Nat.mul_div_cancel_left _ hpos]
    rw [hdiv, hmin]
    have : ((i : ℕ) : ℤ) + 1 = (pn : ℤ) - 1 + ((n : ℤ) - qn) := by rw [hpn', hqn']; linarith
    have hqle : qn ≤ n := by rw [hnat]; exact Nat.le_mul_of_pos_left qn hpos
    omega

theorem alive (n : ℕ) (hn : 1 < n) :
    ∀ i, 1 ≤ i → i + 1 ≤ n + Nat.minFac n - n / Nat.minFac n - 1 →
      ∃ s, run n i = some s ∧ HInv n s i := by
  intro i hi
  induction i with
  | zero => omega
  | succ i ih =>
    intro hK
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact base n hn
    · obtain ⟨s, hs, hI⟩ := ih hi0 (by omega)
      by_cases hy : s.2.1 = 0
      · have := (brk n hn s i hI hy).2
        omega
      · obtain ⟨s', hb, hq, hI'⟩ := step n hn s i hI hy
        refine ⟨s', ?_, hI'⟩
        rw [run_succ n i s hs, hb]
        simp only
        rw [if_pos hq]

theorem phi_bound (n : ℕ) (hn : 1 < n) (s : ℤ × ℤ × ℤ × ℤ) (i : ℕ) (hI : HInv n s i) :
    i + 1 ≤ n + Nat.minFac n - n / Nat.minFac n - 1 := by
  obtain ⟨x, y, p, q⟩ := s
  obtain ⟨hy', hp, hq, hlt, hd, hphi⟩ := hI
  simp only at hy' hp hq hlt hd hphi
  have hpn := p_le n hn p hp hd
  set m := Nat.minFac n with hm
  have hm2 : 2 ≤ m := (Nat.minFac_prime (by omega)).two_le
  have hmd : m ∣ n := Nat.minFac_dvd n
  obtain ⟨Q, hQ⟩ := hmd
  have hdiv : n / m = Q := by rw [hQ, Nat.mul_div_cancel_left _ (by omega)]
  rw [hdiv]
  have hQz : (n : ℤ) = (m : ℤ) * Q := by exact_mod_cast hQ
  -- q >= Q
  have hqQ : (Q : ℤ) ≤ q := by
    by_contra hc
    have : q + 1 ≤ (Q : ℤ) := by omega
    have : (p + 1) * (q + 1) ≤ (m : ℤ) * Q := by
      apply mul_le_mul hpn this (by omega) (by omega)
    linarith
  have hQn : Q ≤ n := by rw [hQ]; exact Nat.le_mul_of_pos_left Q (by omega)
  have : ((i : ℕ) : ℤ) + 1 ≤ (m : ℤ) - 1 + ((n : ℤ) - Q) := by linarith
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a288966.main := by
  intro n hn
  suffices key : ∀ K, K = n + Nat.minFac n - n / Nat.minFac n - 1 → a n = K from key _ rfl
  intro K hK
  have hK2 : 2 ≤ K := by
    have hm2 : 2 ≤ Nat.minFac n := (Nat.minFac_prime (by omega)).two_le
    have : n / Nat.minFac n ≤ n / 2 := Nat.div_le_div_left hm2 (by norm_num)
    have : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
    omega
  -- K breaks
  have hbK : Breaks n K := by
    refine ⟨by omega, ?_⟩
    obtain ⟨s, hs, hI⟩ := alive n hn (K - 1) (by omega) (by omega)
    refine ⟨s, hs, ?_⟩
    by_cases hy : s.2.1 = 0
    · exact (brk n hn s (K - 1) hI hy).1
    · exfalso
      obtain ⟨s', hb, hq, hI'⟩ := step n hn s (K - 1) hI hy
      have := phi_bound n hn s' (K - 1 + 1) hI'
      omega
  have hlow : ∀ i, Breaks n i → K ≤ i := by
    rintro i ⟨hi, s, hs, hb⟩
    by_contra hc
    rcases Nat.lt_or_ge i 2 with h1 | h2
    · obtain rfl : i = 1 := by omega
      simp only [Nat.sub_self, run] at hs
      cases hs
      simp only [body] at hb
      rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by simp; omega)] at hb
      cases hb
    · obtain ⟨s', hs', hI⟩ := alive n hn (i - 1) (by omega) (by omega)
      rw [hs] at hs'
      cases hs'
      by_cases hy : s.2.1 = 0
      · have := (brk n hn s (i - 1) hI hy).2
        omega
      · obtain ⟨s'', hb', -⟩ := step n hn s (i - 1) hI hy
        rw [hb] at hb'
        cases hb'
  unfold a
  apply le_antisymm
  · exact Nat.sInf_le hbK
  · exact le_csInf ⟨K, hbK⟩ hlow
