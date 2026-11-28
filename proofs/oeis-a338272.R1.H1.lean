import OMAReductions.R_oeis_a338272_R1

/-!
# Proof of `oeis-a338272.R1.H1`

Write `n = d^2 * s` with `s` squarefree. Since `n ≡ 1 (mod 4)`, `d` is odd so `s ≡ 1 (mod 4)`.
If `n` is not a sum of two squares, Fermat's two-square theorem (`Nat.eq_sq_add_sq_iff`) gives a
prime `p ≡ 3 (mod 4)` with odd `p`-adic valuation in `n`, hence in `s`, so `p ∣ s`. The cofactor
`t = s / p` then satisfies `t ≡ 3 (mod 4)`, so it has a prime divisor `q ≡ 3 (mod 4)`. Since `s`
is squarefree, `p ≠ q` and `p * q ∣ s`.
-/

private lemma exists_sq_mul_squarefree :
    ∀ n : ℕ, 0 < n → ∃ s d : ℕ, 0 < s ∧ Squarefree s ∧ n = d ^ 2 * s := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hsq : Squarefree n
    · exact ⟨n, 1, hn, hsq, by ring⟩
    · rw [Squarefree] at hsq
      push Not at hsq
      obtain ⟨x, hx_dvd, hx_nu⟩ := hsq
      have hx1 : x ≠ 1 := by
        intro h1
        exact hx_nu (by rw [h1]; exact isUnit_one)
      have hx0 : x ≠ 0 := by
        intro h0
        rw [h0, zero_mul, zero_dvd_iff] at hx_dvd
        omega
      have hx2 : 2 ≤ x := by omega
      obtain ⟨m, rfl⟩ := hx_dvd
      have hm_pos : 0 < m := by
        by_contra h
        have : m = 0 := by omega
        subst this; simp at hn
      have hxsq : 4 ≤ x * x := by nlinarith
      have hm_lt : m < x * x * m := by nlinarith
      obtain ⟨s, d, hs_pos, hs_sq, hm_eq⟩ := ih m hm_lt hm_pos
      refine ⟨s, x * d, hs_pos, hs_sq, ?_⟩
      rw [hm_eq]; ring

private lemma exists_prime_mod4_eq3 :
    ∀ t : ℕ, t % 4 = 3 → ∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ q ∣ t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro ht
    have ht1 : t ≠ 1 := by omega
    set q := t.minFac
    have hqp : q.Prime := Nat.minFac_prime ht1
    have hqdvd : q ∣ t := Nat.minFac_dvd t
    have hq2 : q ≠ 2 := by
      intro h2
      rw [h2] at hqdvd
      omega
    have hq_odd : q % 2 = 1 := by
      rcases hqp.eq_two_or_odd with h2 | hodd
      · exact absurd h2 hq2
      · exact hodd
    by_cases hq3 : q % 4 = 3
    · exact ⟨q, hqp, hq3, hqdvd⟩
    · have hq1 : q % 4 = 1 := by omega
      obtain ⟨t', ht'⟩ := hqdvd
      have ht'_pos : 0 < t' := by
        by_contra h
        have : t' = 0 := by omega
        rw [this, mul_zero] at ht'
        omega
      have hq_ge2 : 2 ≤ q := hqp.two_le
      have ht'_lt : t' < t := by rw [ht']; nlinarith
      have ht'_mod : t' % 4 = 3 := by
        have : (q * t') % 4 = ((q % 4) * (t' % 4)) % 4 := Nat.mul_mod q t' 4
        rw [← ht', hq1, one_mul, Nat.mod_mod] at this
        omega
      obtain ⟨r, hrp, hr3, hrdvd⟩ := ih t' ht'_lt ht'_mod
      exact ⟨r, hrp, hr3, ht' ▸ dvd_mul_of_dvd_right hrdvd q⟩

theorem OMA.solution : OMA.R_oeis_a338272_R1.H1 := by
  intro n hn hn4
  by_cases hsum : ∃ x y : ℕ, n = x ^ 2 + y ^ 2
  · exact Or.inl hsum
  · right
    obtain ⟨s, d, hs_pos, hs_sq, hnds⟩ := exists_sq_mul_squarefree n hn
    have hd_pos : 0 < d := by
      by_contra h
      have : d = 0 := by omega
      subst this; simp at hnds; omega
    have hd_odd : d % 2 = 1 := by
      by_contra h
      have h2d : 2 ∣ d := by omega
      obtain ⟨k, rfl⟩ := h2d
      have h4n : 4 ∣ n := ⟨k ^ 2 * s, by rw [hnds]; ring⟩
      omega
    have hd2_mod : d ^ 2 % 4 = 1 := by
      have : d % 4 = 1 ∨ d % 4 = 3 := by omega
      rcases this with h1 | h3
      · rw [sq, Nat.mul_mod, h1]
      · rw [sq, Nat.mul_mod, h3]
    have hs4 : s % 4 = 1 := by
      have : (d ^ 2 * s) % 4 = ((d ^ 2 % 4) * (s % 4)) % 4 := Nat.mul_mod _ _ 4
      rw [← hnds, hd2_mod, one_mul, Nat.mod_mod] at this
      omega
    have hnot := (Nat.eq_sq_add_sq_iff (n := n)).not.mp hsum
    push Not at hnot
    obtain ⟨p, hp_mem, hp4, hp_nodd⟩ := hnot
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have : Fact p.Prime := ⟨hp⟩
    have hval_eq : padicValNat p n = 2 * padicValNat p d + padicValNat p s := by
      rw [hnds, padicValNat.mul (pow_ne_zero 2 hd_pos.ne') hs_pos.ne',
        sq, padicValNat.mul hd_pos.ne' hd_pos.ne']
      ring
    have hval_s_ne : padicValNat p s ≠ 0 := by
      intro h0
      rw [h0, add_zero] at hval_eq
      exact hp_nodd ⟨padicValNat p d, by omega⟩
    have hps : p ∣ s := by
      by_contra hndvd
      exact hval_s_ne (padicValNat.eq_zero_of_not_dvd hndvd)
    obtain ⟨t, ht⟩ := hps
    have ht4 : t % 4 = 3 := by
      have : (p * t) % 4 = ((p % 4) * (t % 4)) % 4 := Nat.mul_mod p t 4
      rw [← ht, hp4] at this
      omega
    obtain ⟨q, hq, hq4, hqt⟩ := exists_prime_mod4_eq3 t ht4
    have hpq_dvd : p * q ∣ s := by
      rw [ht]
      exact mul_dvd_mul_left p hqt
    have hpq_ne : p ≠ q := by
      intro heq
      subst heq
      have hunit : IsUnit p := hs_sq p hpq_dvd
      exact hp.ne_one (Nat.isUnit_iff.mp hunit)
    exact ⟨s, d, hs_pos, hs4, hs_sq, hnds, p, q, hp, hq, hpq_ne, hp4, hq4, hpq_dvd⟩
