import OMAStatements.S_oeis_a096126

-- Problem: A096126: a(n) is the least integer of the form (n^2)!/(n!)^k.
-- Upstream: formal-conjectures statements/oeis-a096126.lean:0 (declaration OMA.S_oeis_a096126.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: let s(m) be the base-q digit sum of m (q prime). Legendre: (q-1) v_q(m!) = m - s(m).
-- s(x+y) <= s(x) + s(y) (from x! y! | (x+y)!), s(q*x) = s(x), hence s(a*b) <= s(a) s(b) and
-- s(n^2) <= s(n)^2. If n is not a prime power then s(n) >= 2 for every prime q (s(n) = 1 forces
-- n = q^j), and with S = s(n) <= n: (n+2)(n - S) <= n^2 - S^2 <= n^2 - s(n^2), i.e.
-- (n+2) v_q(n!) <= v_q((n^2)!). So (n!)^(n+2) divides (n^2)!, and n+1 is not the largest k.

open OMA.S_oeis_a096126 in
theorem OMA.solution : type_of% @OMA.S_oeis_a096126.main := by
  have dsum_step : ∀ q n : ℕ, 1 < q → 0 < n →
      (Nat.digits q n).sum = n % q + (Nat.digits q (n / q)).sum := by
    intro q n hq hn
    rw [Nat.digits_def' hq hn, List.sum_cons]
  have spos : ∀ q m : ℕ, m ≠ 0 → 0 < (Nat.digits q m).sum := by
    intro q m hm
    have hnil : Nat.digits q m ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hm
    exact List.sum_pos_iff_exists_pos_nat.mpr
      ⟨_, List.getLast_mem hnil, Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero q hm)⟩
  have onepow : ∀ q : ℕ, 1 < q → ∀ n : ℕ, 0 < n → (Nat.digits q n).sum = 1 →
      ∃ k, n = q ^ k := by
    intro q hq n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn hs
      rw [dsum_step q n hq hn] at hs
      have hdm := Nat.div_add_mod n q
      rcases Nat.eq_zero_or_pos (n / q) with h0 | h0
      · refine ⟨0, ?_⟩
        rw [h0, Nat.digits_zero, List.sum_nil] at hs
        rw [h0] at hdm
        rw [pow_zero]
        omega
      · have hp := spos q (n / q) (by omega)
        have hmod : n % q = 0 := by omega
        have hs' : (Nat.digits q (n / q)).sum = 1 := by omega
        obtain ⟨k, hk⟩ := ih (n / q) (Nat.div_lt_self hn hq) h0 hs'
        refine ⟨k + 1, ?_⟩
        calc n = q * (n / q) + n % q := hdm.symm
          _ = q ^ (k + 1) := by
            rw [hmod, hk, pow_succ]
            ring
  have sadd : ∀ q : ℕ, q.Prime → ∀ x y : ℕ,
      (Nat.digits q (x + y)).sum ≤ (Nat.digits q x).sum + (Nat.digits q y).sum := by
    intro q hq x y
    have := Fact.mk hq
    have L := sub_one_mul_padicValNat_factorial (p := q) (x + y)
    have Lx := sub_one_mul_padicValNat_factorial (p := q) x
    have Ly := sub_one_mul_padicValNat_factorial (p := q) y
    have hdiv : Nat.factorial x * Nat.factorial y ∣ Nat.factorial (x + y) :=
      Nat.factorial_mul_factorial_dvd_factorial_add x y
    have hv : padicValNat q (Nat.factorial x * Nat.factorial y) ≤
        padicValNat q (Nat.factorial (x + y)) :=
      (padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)).mp (pow_padicValNat_dvd.trans hdiv)
    rw [padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)] at hv
    have hm : (q - 1) * (padicValNat q (Nat.factorial x) + padicValNat q (Nat.factorial y)) ≤
        (q - 1) * padicValNat q (Nat.factorial (x + y)) := Nat.mul_le_mul_left _ hv
    rw [mul_add] at hm
    have h1 := Nat.digit_sum_le q x
    have h2 := Nat.digit_sum_le q y
    have h3 := Nat.digit_sum_le q (x + y)
    omega
  have smul : ∀ q : ℕ, 1 < q → ∀ x : ℕ, (Nat.digits q (q * x)).sum = (Nat.digits q x).sum := by
    intro q hq x
    rcases Nat.eq_zero_or_pos x with h0 | h0
    · rw [h0, Nat.mul_zero]
    · rw [dsum_step q (q * x) hq (Nat.mul_pos (by omega) h0), Nat.mul_mod_right,
        Nat.mul_div_cancel_left x (by omega), Nat.zero_add]
  have sdmul : ∀ q : ℕ, q.Prime → ∀ d b : ℕ,
      (Nat.digits q (d * b)).sum ≤ d * (Nat.digits q b).sum := by
    intro q hq d b
    induction d with
    | zero => simp
    | succ d ih =>
      have e : (d + 1) * b = d * b + b := by ring
      rw [e]
      have h1 := sadd q hq (d * b) b
      have e2 : (d + 1) * (Nat.digits q b).sum = d * (Nat.digits q b).sum +
          (Nat.digits q b).sum := by ring
      rw [e2]
      omega
  have smult : ∀ q : ℕ, q.Prime → ∀ a b : ℕ,
      (Nat.digits q (a * b)).sum ≤ (Nat.digits q a).sum * (Nat.digits q b).sum := by
    intro q hq a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro b
      rcases Nat.eq_zero_or_pos a with h0 | ha
      · rw [h0, Nat.zero_mul]
        simp
      · have e : a * b = q * (a / q * b) + a % q * b := by
          have hdm := Nat.div_add_mod a q
          calc a * b = (q * (a / q) + a % q) * b := by rw [hdm]
            _ = q * (a / q * b) + a % q * b := by ring
        rw [e]
        have i1 := sadd q hq (q * (a / q * b)) (a % q * b)
        have i2 := smul q hq.one_lt (a / q * b)
        have i3 := ih (a / q) (Nat.div_lt_self ha hq.one_lt) b
        have i4 := sdmul q hq (a % q) b
        have i5 := dsum_step q a hq.one_lt ha
        have e3 : (Nat.digits q a).sum * (Nat.digits q b).sum =
            (Nat.digits q (a / q)).sum * (Nat.digits q b).sum +
            a % q * (Nat.digits q b).sum := by
          rw [i5]
          ring
        rw [e3]
        omega
  have arith : ∀ n S T V1 V2 c : ℕ, 2 ≤ S → S ≤ n → T ≤ S ^ 2 → T ≤ n ^ 2 →
      c * V1 = n - S → c * V2 = n ^ 2 - T → 0 < c → (n + 2) * V1 ≤ V2 := by
    intro n S T V1 V2 c hS2 hSn hT hTn h1 h2 hc
    apply Nat.le_of_mul_le_mul_left _ hc
    obtain ⟨d, rfl⟩ : ∃ d, n = S + d := ⟨n - S, by omega⟩
    have h1' : c * V1 = d := by omega
    have h2' : c * V2 + T = (S + d) ^ 2 := by omega
    have e1 : c * ((S + d + 2) * V1) = (S + d + 2) * (c * V1) := by ring
    rw [e1, h1']
    nlinarith [Nat.mul_le_mul_right d hS2]
  intro n hn hG
  by_contra hpp
  have hn0 : n ≠ 0 := by omega
  have hs2 : ∀ q : ℕ, q.Prime → 2 ≤ (Nat.digits q n).sum := by
    intro q hq
    by_contra hlt
    have hpos := spos q n hn0
    have h1 : (Nat.digits q n).sum = 1 := by omega
    obtain ⟨k, hk⟩ := onepow q hq.one_lt n (by omega) h1
    apply hpp
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero] at hk
      omega
    · exact ⟨q, k, hq.prime, h0, hk.symm⟩
  have hval : ∀ q : ℕ, q.Prime → (n + 2) * padicValNat q (Nat.factorial n) ≤
      padicValNat q (Nat.factorial (n ^ 2)) := by
    intro q hq
    have := Fact.mk hq
    have hsq : (Nat.digits q (n ^ 2)).sum ≤ (Nat.digits q n).sum ^ 2 := by
      rw [pow_two, pow_two]
      exact smult q hq n n
    exact arith n _ _ _ _ (q - 1) (hs2 q hq) (Nat.digit_sum_le q n) hsq
      (Nat.digit_sum_le q (n ^ 2)) (sub_one_mul_padicValNat_factorial (p := q) n)
      (sub_one_mul_padicValNat_factorial (p := q) (n ^ 2)) (by have := hq.two_le; omega)
  have hdvd : Nat.factorial n ^ (n + 2) ∣ Nat.factorial (n ^ 2) := by
    rw [← Nat.factorization_prime_le_iff_dvd (pow_ne_zero _ (Nat.factorial_ne_zero n))
      (Nat.factorial_ne_zero _)]
    intro q hq
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, Nat.factorization_def _ hq,
      Nat.factorization_def _ hq]
    exact hval q hq
  have hmem : n + 2 ∈ exps n := hdvd
  have hle : n + 2 ≤ n + 1 := hG.2 hmem
  omega
