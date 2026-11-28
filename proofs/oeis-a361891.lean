import OMAStatements.S_oeis_a361891

namespace OMA.S_oeis_a361891

open Polynomial Finset

noncomputable section

/-!
## Proof of OEIS A361891: `S 1 n ∣ S 7 n`

We prove a stronger general theorem: for all `n m : ℕ` with `m ≤ n` and all `a b : ℕ`
with `1 ≤ a` and `1 ≤ b`,
`(n.choose m : ℤ) ∣ ∑ k ∈ Icc 1 m, (C(n, k)^a * C(n, k - 1)^b - C(n, k)^b * C(n, k - 1)^a)`.

The proof lifts to `q`-binomial coefficients in `ℤ[X]`, where `qBinom n m` factors into a
squarefree product of cyclotomic polynomials `∏_{2 ≤ d ≤ n, n % d < m % d} Φ_d(X)`.
At any primitive `d`-th root of unity `ζ ∈ ℂ` with `n % d < m % d`, the `q`-Lucas theorem
splits the sequence `k ↦ qBinom n k (ζ)` into palindromic blocks separated by zeros, forcing
every antisymmetric adjacent-pair sum up to `m` to vanish at `ζ`. Thus `Φ_d(X)` divides the
polynomial sum in `ℚ[X]` for each such `d`; coprimality of distinct cyclotomic polynomials
and monicity of `qBinom n m` yield divisibility in `ℤ[X]`. Evaluating at `X = 1` gives the
integer divisibility, from which `S 1 n ∣ S r n` follows for every odd `r` (in particular `r = 7`).
-/

private def qBinom : ℕ → ℕ → ℤ[X]
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qBinom n (k + 1) + X ^ (n - k) * qBinom n k

private lemma qBinom_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → qBinom n k = 0
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
      have h1 : n < k := by omega
      have h2 : n < k + 1 := by omega
      simp [qBinom, qBinom_eq_zero_of_lt h1, qBinom_eq_zero_of_lt h2]

private lemma qBinom_self : ∀ n : ℕ, qBinom n n = 1
  | 0 => rfl
  | n + 1 => by
      simp [qBinom, qBinom_eq_zero_of_lt (Nat.lt_succ_self n), qBinom_self n]

private lemma eval_one_qBinom : ∀ n k : ℕ, (qBinom n k).eval 1 = (n.choose k : ℤ)
  | n, 0 => by simp [qBinom]
  | 0, k + 1 => by simp [qBinom]
  | n + 1, k + 1 => by
      simp only [qBinom, eval_add, eval_mul, eval_pow, eval_X, one_pow, one_mul,
        eval_one_qBinom n (k + 1), eval_one_qBinom n k, Nat.choose_succ_succ, Nat.cast_add]
      ring

private def qInt (n : ℕ) : ℤ[X] := ∑ i ∈ range n, X ^ i

private def qFact (n : ℕ) : ℤ[X] := ∏ i ∈ range n, qInt (i + 1)

private lemma qInt_add (a b : ℕ) : qInt (a + b) = qInt a + X ^ a * qInt b := by
  simp only [qInt, sum_range_add, Finset.mul_sum, pow_add]

private lemma eval_one_qInt (n : ℕ) : (qInt n).eval 1 = (n : ℤ) := by
  simp [qInt]

private lemma qFact_ne_zero (n : ℕ) : qFact n ≠ 0 := by
  intro h
  have h1 : (qFact n).eval 1 = 0 := by rw [h, eval_zero]
  have h2 : (qFact n).eval 1 = ∏ i ∈ range n, ((i + 1 : ℕ) : ℤ) := by
    simp [qFact, eval_prod, eval_one_qInt]
  rw [h2] at h1
  have hpos : (0 : ℤ) < ∏ i ∈ range n, ((i + 1 : ℕ) : ℤ) :=
    Finset.prod_pos fun i _ => by positivity
  omega

private lemma qFact_mul_qBinom :
    ∀ n k : ℕ, k ≤ n → qFact k * qFact (n - k) * qBinom n k = qFact n
  | n, 0, _ => by simp [qFact, qBinom]
  | 0, k + 1, hk => by omega
  | n + 1, k + 1, hk => by
      rcases eq_or_lt_of_le hk with heq | hlt
      · have hkn : k = n := by omega
        subst hkn
        simp [qBinom_self, qFact]
      · have hk1 : k + 1 ≤ n := by omega
        have hk0 : k ≤ n := by omega
        have hsub1 : n + 1 - (k + 1) = n - k := by omega
        have hsub2 : n - k = (n - (k + 1)) + 1 := by omega
        have ih1 := qFact_mul_qBinom n (k + 1) hk1
        have ih2 := qFact_mul_qBinom n k hk0
        rw [hsub1]
        have hfk : qFact (k + 1) = qFact k * qInt (k + 1) := by
          simp [qFact, prod_range_succ]
        have hfnk : qFact (n - k) = qFact (n - (k + 1)) * qInt (n - k) := by
          rw [hsub2, qFact, prod_range_succ, ← qFact]
        have hfn1 : qFact (n + 1) = qFact n * qInt (n + 1) := by
          simp [qFact, prod_range_succ]
        have hadd : qInt (n - k) + X ^ (n - k) * qInt (k + 1) = qInt (n + 1) := by
          rw [← qInt_add]
          congr 1
          omega
        calc qFact (k + 1) * qFact (n - k) * qBinom (n + 1) (k + 1)
            = qFact (k + 1) * qFact (n - k) * qBinom n (k + 1) +
                X ^ (n - k) * (qFact (k + 1) * qFact (n - k) * qBinom n k) := by
                  simp only [qBinom]; ring
          _ = qInt (n - k) * (qFact (k + 1) * qFact (n - (k + 1)) * qBinom n (k + 1)) +
                X ^ (n - k) * qInt (k + 1) * (qFact k * qFact (n - k) * qBinom n k) := by
                  conv_lhs =>
                    arg 1; rw [hfnk]
                  conv_lhs =>
                    arg 2; rw [hfk]
                  ring
          _ = (qInt (n - k) + X ^ (n - k) * qInt (k + 1)) * qFact n := by
                  rw [ih1, ih2]; ring
          _ = qFact (n + 1) := by rw [hadd, hfn1]; ring

private lemma qBinom_symm (n k : ℕ) (hk : k ≤ n) : qBinom n (n - k) = qBinom n k := by
  have h1 := qFact_mul_qBinom n (n - k) (Nat.sub_le n k)
  have h2 := qFact_mul_qBinom n k hk
  rw [Nat.sub_sub_self hk] at h1
  have h3 : (qFact k * qFact (n - k)) * qBinom n (n - k) =
      (qFact k * qFact (n - k)) * qBinom n k := by
    calc (qFact k * qFact (n - k)) * qBinom n (n - k)
        = qFact (n - k) * qFact k * qBinom n (n - k) := by ring
      _ = qFact n := h1
      _ = (qFact k * qFact (n - k)) * qBinom n k := h2.symm
  exact mul_left_cancel₀ (mul_ne_zero (qFact_ne_zero k) (qFact_ne_zero (n - k))) h3

private lemma qInt_eq_prod_cyclotomic (n : ℕ) (hn : 0 < n) :
    qInt n = ∏ d ∈ n.divisors.erase 1, cyclotomic d ℤ :=
  (prod_cyclotomic_eq_geom_sum hn ℤ).symm

private lemma div_succ_eq (N d : ℕ) (hd : 0 < d) :
    (N + 1) / d = N / d + if d ∣ N + 1 then 1 else 0 := by
  by_cases h : d ∣ N + 1
  · rw [if_pos h]
    rcases h with ⟨q, hq⟩
    rcases q with _ | q
    · simp at hq
    · have h1 : (N + 1) / d = q + 1 := by rw [hq, Nat.mul_div_cancel_left (q + 1) hd]
      have h2 : N = d * q + (d - 1) := by
        have : d * (q + 1) = d * q + d := by ring
        omega
      have h3 : N / d = q := by
        rw [h2, Nat.mul_add_div hd, Nat.div_eq_of_lt (by omega : d - 1 < d), add_zero]
      omega
  · rw [if_neg h]
    have hmod : (N + 1) % d ≠ 0 := fun hz => h (Nat.dvd_of_mod_eq_zero hz)
    have h1 := Nat.div_add_mod N d
    have h2 := Nat.div_add_mod (N + 1) d
    have hlt1 := Nat.mod_lt N hd
    have hlt2 := Nat.mod_lt (N + 1) hd
    have hdiv : N / d = (N + 1) / d := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : d * (N / d + 1) ≤ d * ((N + 1) / d) := Nat.mul_le_mul_left d hlt
        rw [mul_add, mul_one] at hle
        omega
      · have hle : d * ((N + 1) / d + 1) ≤ d * (N / d) := Nat.mul_le_mul_left d hgt
        rw [mul_add, mul_one] at hle
        omega
    omega

private lemma qFact_eq_prod_cyclotomic :
    ∀ N : ℕ, qFact N = ∏ d ∈ Icc 2 N, cyclotomic d ℤ ^ (N / d)
  | 0 => by simp [qFact]
  | N + 1 => by
      have ih := qFact_eq_prod_cyclotomic N
      rw [qFact, prod_range_succ, ← qFact, ih, qInt_eq_prod_cyclotomic (N + 1) (Nat.succ_pos N)]
      have hsub : (N + 1).divisors.erase 1 = (Icc 2 (N + 1)).filter (fun d => d ∣ N + 1) := by
        ext d
        simp only [mem_erase, Nat.mem_divisors, mem_filter, mem_Icc]
        constructor
        · rintro ⟨hd1, hdvd, _⟩
          have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.succ_pos N)
          have hdle : d ≤ N + 1 := Nat.le_of_dvd (Nat.succ_pos N) hdvd
          exact ⟨⟨by omega, hdle⟩, hdvd⟩
        · rintro ⟨⟨hd2, _⟩, hdvd⟩
          exact ⟨by omega, hdvd, Nat.succ_ne_zero N⟩
      rw [hsub]
      have hext : ∏ d ∈ Icc 2 N, cyclotomic d ℤ ^ (N / d) =
          ∏ d ∈ Icc 2 (N + 1), cyclotomic d ℤ ^ (N / d) := by
        refine Finset.prod_subset (Icc_subset_Icc_right (Nat.le_succ N)) ?_
        intro d hd hnot
        simp only [mem_Icc] at hd hnot
        have hd_eq : d = N + 1 := by omega
        subst hd_eq
        rw [Nat.div_eq_of_lt (Nat.lt_succ_self N), pow_zero]
      rw [hext]
      have hfilt : ∏ d ∈ (Icc 2 (N + 1)).filter (fun d => d ∣ N + 1), cyclotomic d ℤ =
          ∏ d ∈ Icc 2 (N + 1), cyclotomic d ℤ ^ (if d ∣ N + 1 then 1 else 0) := by
        rw [← Finset.prod_filter_mul_prod_filter_not (Icc 2 (N + 1)) (fun d => d ∣ N + 1)]
        have h1 : ∏ d ∈ (Icc 2 (N + 1)).filter (fun d => d ∣ N + 1),
            cyclotomic d ℤ ^ (if d ∣ N + 1 then 1 else 0) =
            ∏ d ∈ (Icc 2 (N + 1)).filter (fun d => d ∣ N + 1), cyclotomic d ℤ := by
          refine Finset.prod_congr rfl fun d hd => ?_
          simp [(mem_filter.mp hd).2]
        have h2 : ∏ d ∈ (Icc 2 (N + 1)).filter (fun d => ¬ d ∣ N + 1),
            cyclotomic d ℤ ^ (if d ∣ N + 1 then 1 else 0) = 1 := by
          refine Finset.prod_eq_one fun d hd => ?_
          simp [(mem_filter.mp hd).2]
        rw [h1, h2, mul_one]
      rw [hfilt, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun d hd => ?_
      rw [← pow_add, ← div_succ_eq N d (by have := (mem_Icc.mp hd).1; omega)]

private lemma div_sub_add_eq (n m d : ℕ) (hm : m ≤ n) (hd : 0 < d) :
    n / d = m / d + (n - m) / d + if n % d < m % d then 1 else 0 := by
  have hm1 := Nat.div_add_mod m d
  have hr1 := Nat.div_add_mod (n - m) d
  have hn1 := Nat.div_add_mod n d
  have hmlt := Nat.mod_lt m hd
  have hrlt := Nat.mod_lt (n - m) hd
  have hnlt := Nat.mod_lt n hd
  by_cases hlt : m % d + (n - m) % d < d
  · have hdiv : n / d = m / d + (n - m) / d := by
      have hsum : d * (m / d + (n - m) / d) + (m % d + (n - m) % d) = n := by
        rw [mul_add]; omega
      by_contra hne
      rcases lt_or_gt_of_ne hne with h1 | h2
      · have hle : d * (n / d + 1) ≤ d * (m / d + (n - m) / d) := Nat.mul_le_mul_left d h1
        rw [mul_add, mul_one] at hle
        omega
      · have hle : d * (m / d + (n - m) / d + 1) ≤ d * (n / d) := Nat.mul_le_mul_left d h2
        rw [mul_add, mul_one] at hle
        omega
    have hmod : n % d = m % d + (n - m) % d := by
      rw [hdiv, mul_add] at hn1; omega
    rw [if_neg (by omega), add_zero, hdiv]
  · have hdiv : n / d = m / d + (n - m) / d + 1 := by
      have hsum : d * (m / d + (n - m) / d + 1) + (m % d + (n - m) % d - d) = n := by
        rw [mul_add, mul_add, mul_one]; omega
      by_contra hne
      rcases lt_or_gt_of_ne hne with h1 | h2
      · have hle : d * (n / d + 1) ≤ d * (m / d + (n - m) / d + 1) := Nat.mul_le_mul_left d h1
        rw [mul_add, mul_one] at hle
        omega
      · have hle : d * (m / d + (n - m) / d + 1 + 1) ≤ d * (n / d) := Nat.mul_le_mul_left d h2
        rw [mul_add, mul_one] at hle
        omega
    have hmod : n % d = m % d + (n - m) % d - d := by
      rw [hdiv, mul_add, mul_add, mul_one] at hn1; omega
    rw [if_pos (by omega), hdiv]

private lemma qBinom_eq_prod_cyclotomic (n m : ℕ) (hm : m ≤ n) :
    qBinom n m = ∏ d ∈ (Icc 2 n).filter (fun d => n % d < m % d), cyclotomic d ℤ := by
  have hext : ∀ k : ℕ, k ≤ n →
      qFact k = ∏ d ∈ Icc 2 n, cyclotomic d ℤ ^ (k / d) := by
    intro k hk
    rw [qFact_eq_prod_cyclotomic k]
    refine Finset.prod_subset (Icc_subset_Icc_right hk) ?_
    intro d hd hnot
    simp only [mem_Icc] at hd hnot
    rw [Nat.div_eq_of_lt (by omega : k < d), pow_zero]
  have h1 : qFact m * qFact (n - m) *
      ∏ d ∈ (Icc 2 n).filter (fun d => n % d < m % d), cyclotomic d ℤ = qFact n := by
    rw [hext m hm, hext (n - m) (Nat.sub_le n m), qFact_eq_prod_cyclotomic n]
    have hfilt : ∏ d ∈ (Icc 2 n).filter (fun d => n % d < m % d), cyclotomic d ℤ =
        ∏ d ∈ Icc 2 n, cyclotomic d ℤ ^ (if n % d < m % d then 1 else 0) := by
      rw [← Finset.prod_filter_mul_prod_filter_not (Icc 2 n) (fun d => n % d < m % d)]
      have ha : ∏ d ∈ (Icc 2 n).filter (fun d => n % d < m % d),
          cyclotomic d ℤ ^ (if n % d < m % d then 1 else 0) =
          ∏ d ∈ (Icc 2 n).filter (fun d => n % d < m % d), cyclotomic d ℤ := by
        refine Finset.prod_congr rfl fun d hd => ?_
        simp [(mem_filter.mp hd).2]
      have hb : ∏ d ∈ (Icc 2 n).filter (fun d => ¬ n % d < m % d),
          cyclotomic d ℤ ^ (if n % d < m % d then 1 else 0) = 1 := by
        refine Finset.prod_eq_one fun d hd => ?_
        simp [(mem_filter.mp hd).2]
      rw [ha, hb, mul_one]
    rw [hfilt, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun d hd => ?_
    rw [← pow_add, ← pow_add, ← div_sub_add_eq n m d hm (by have := (mem_Icc.mp hd).1; omega)]
  have h2 := qFact_mul_qBinom n m hm
  exact mul_left_cancel₀ (mul_ne_zero (qFact_ne_zero m) (qFact_ne_zero (n - m))) (h2.trans h1.symm)

private lemma qBinom_monic (n m : ℕ) (hm : m ≤ n) : (qBinom n m).Monic := by
  rw [qBinom_eq_prod_cyclotomic n m hm]
  exact monic_prod_of_monic _ _ fun d _ => cyclotomic.monic d ℤ

private lemma nat_tri_succ (k : ℕ) : (k + 1) * k / 2 = k * (k - 1) / 2 + k := by
  rcases k with _ | k
  · simp
  · have h : (k + 1 + 1) * (k + 1) = (k + 1) * k + 2 * (k + 1) := by ring
    rw [Nat.add_sub_cancel, h, Nat.add_mul_div_left _ _ (by omega : 0 < 2)]

private lemma coeff_prod_qBinom (ζ : ℂ) :
    ∀ n k : ℕ,
      (∏ i ∈ range n, (1 + C (ζ ^ i) * (X : ℂ[X]))).coeff k =
        ζ ^ (k * (k - 1) / 2) * (qBinom n k).eval₂ (Int.castRingHom ℂ) ζ
  | 0, 0 => by simp [qBinom]
  | 0, k + 1 => by simp [qBinom, coeff_one]
  | n + 1, 0 => by
      rw [prod_range_succ, mul_add, mul_one, coeff_add, ← mul_assoc, coeff_mul_X_zero,
        add_zero, coeff_prod_qBinom ζ n 0]
      simp [qBinom]
  | n + 1, k + 1 => by
      rw [prod_range_succ, mul_add, mul_one, coeff_add, coeff_prod_qBinom ζ n (k + 1)]
      have hmul : ((∏ i ∈ range n, (1 + C (ζ ^ i) * (X : ℂ[X]))) * (C (ζ ^ n) * X)).coeff (k + 1) =
          ζ ^ n * (∏ i ∈ range n, (1 + C (ζ ^ i) * (X : ℂ[X]))).coeff k := by
        rw [← mul_assoc, coeff_mul_X, coeff_mul_C, mul_comm]
      rw [hmul, coeff_prod_qBinom ζ n k]
      simp only [qBinom, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X]
      by_cases hkn : k ≤ n
      · have htri : n + k * (k - 1) / 2 = (k + 1) * k / 2 + (n - k) := by
          have := nat_tri_succ k
          omega
        rw [Nat.add_sub_cancel]
        calc ζ ^ ((k + 1) * k / 2) * eval₂ (Int.castRingHom ℂ) ζ (qBinom n (k + 1)) +
              ζ ^ n * (ζ ^ (k * (k - 1) / 2) * eval₂ (Int.castRingHom ℂ) ζ (qBinom n k))
            = ζ ^ ((k + 1) * k / 2) * eval₂ (Int.castRingHom ℂ) ζ (qBinom n (k + 1)) +
              ζ ^ (n + k * (k - 1) / 2) * eval₂ (Int.castRingHom ℂ) ζ (qBinom n k) := by
                rw [pow_add]; ring
          _ = ζ ^ ((k + 1) * k / 2) * eval₂ (Int.castRingHom ℂ) ζ (qBinom n (k + 1)) +
              ζ ^ ((k + 1) * k / 2 + (n - k)) * eval₂ (Int.castRingHom ℂ) ζ (qBinom n k) := by
                rw [htri]
          _ = ζ ^ ((k + 1) * k / 2) *
                (eval₂ (Int.castRingHom ℂ) ζ (qBinom n (k + 1)) +
                  ζ ^ (n - k) * eval₂ (Int.castRingHom ℂ) ζ (qBinom n k)) := by
                rw [pow_add]; ring
      · have hlt1 : n < k := by omega
        have hlt2 : n < k + 1 := by omega
        simp [qBinom_eq_zero_of_lt hlt1, qBinom_eq_zero_of_lt hlt2]

private lemma prod_one_add_pow_X {ζ : ℂ} {d : ℕ} (hd : 0 < d) (hζ : IsPrimitiveRoot ζ d) :
    ∏ i ∈ range d, (1 + C (ζ ^ i) * (X : ℂ[X])) = 1 - (-X) ^ d := by
  apply Polynomial.funext
  intro z
  simp only [eval_prod, eval_add, eval_one, eval_mul, eval_C, eval_X, eval_sub, eval_pow, eval_neg]
  have h1 := hζ.pow_sub_pow_eq_prod_sub_mul (x := (1 : ℂ)) (y := -z) hd
  rw [one_pow] at h1
  rw [h1]
  refine Finset.prod_nbij (fun i => ζ ^ i) ?_ ?_ ?_ ?_
  · intro i _
    rw [mem_nthRootsFinset hd, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · intro i hi j hj hij
    exact hζ.injOn_pow hi hj hij
  · intro μ hμ
    rw [Finset.mem_coe, mem_nthRootsFinset hd] at hμ
    have : NeZero d := ⟨hd.ne'⟩
    obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
    exact ⟨i, Finset.mem_coe.mpr (mem_range.mpr hi), rfl⟩
  · intro i _
    ring

private lemma prod_blocks_eq {ζ : ℂ} {d : ℕ} (hd : 0 < d) (hζ : IsPrimitiveRoot ζ d) :
    ∀ q : ℕ, ∏ i ∈ range (q * d), (1 + C (ζ ^ i) * (X : ℂ[X])) = (1 - (-X) ^ d) ^ q
  | 0 => by simp
  | q + 1 => by
      rw [Nat.add_mul, one_mul, prod_range_add, prod_blocks_eq hd hζ q, pow_succ]
      congr 1
      have hshift : ∀ r : ℕ, ζ ^ (q * d + r) = ζ ^ r := by
        intro r
        rw [pow_add, mul_comm q d, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
      simp_rw [hshift]
      exact prod_one_add_pow_X hd hζ

private lemma two_dvd_mul_pred (m : ℕ) : 2 ∣ m * (m - 1) := by
  rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact ⟨t * (m - 1), by rw [ht]; ring⟩
  · rcases m with _ | m
    · simp
    · exact ⟨(m + 1) * t, by rw [Nat.add_sub_cancel]; nlinarith⟩

private lemma tri_add_eq (a b : ℕ) :
    (a + b) * (a + b - 1) / 2 = a * (a - 1) / 2 + a * b + b * (b - 1) / 2 := by
  obtain ⟨x, hx⟩ := two_dvd_mul_pred (a + b)
  obtain ⟨y, hy⟩ := two_dvd_mul_pred a
  obtain ⟨z, hz⟩ := two_dvd_mul_pred b
  have h1 : (a + b) * (a + b - 1) / 2 = x := by rw [hx, Nat.mul_div_cancel_left x (by omega)]
  have h2 : a * (a - 1) / 2 = y := by rw [hy, Nat.mul_div_cancel_left y (by omega)]
  have h3 : b * (b - 1) / 2 = z := by rw [hz, Nat.mul_div_cancel_left z (by omega)]
  rw [h1, h2, h3]
  rcases a with _ | a
  · simp at hx hy ⊢; omega
  · rcases b with _ | b
    · rw [add_zero] at hx; simp at hz ⊢; omega
    · have hprod : (a + 1 + (b + 1)) * (a + 1 + (b + 1) - 1) =
          (a + 1) * (a + 1 - 1) + 2 * ((a + 1) * (b + 1)) + (b + 1) * (b + 1 - 1) := by
        have hsub : a + 1 + (b + 1) - 1 = a + b + 1 := by omega
        rw [hsub, Nat.add_sub_cancel, Nat.add_sub_cancel]
        ring
      omega

private lemma tri_div_mod (k d : ℕ) :
    k * (k - 1) / 2 = (k / d * d) * (k / d * d - 1) / 2 + (k / d * d) * (k % d) +
      (k % d) * (k % d - 1) / 2 := by
  have hk : k / d * d + k % d = k := by
    rw [mul_comm, Nat.div_add_mod]
  conv_lhs => rw [← hk]
  exact tri_add_eq (k / d * d) (k % d)

private lemma pow_tri_div_mod {ζ : ℂ} {d : ℕ} (hd : 2 ≤ d) (hζ : IsPrimitiveRoot ζ d) (k : ℕ) :
    ζ ^ (k * (k - 1) / 2) =
      (-1 : ℂ) ^ ((d - 1) * (k / d)) * ζ ^ ((k % d) * (k % d - 1) / 2) := by
  rw [tri_div_mod k d, pow_add, pow_add]
  have hmid : ζ ^ (k / d * d * (k % d)) = 1 := by
    rw [show k / d * d * (k % d) = d * (k / d * (k % d)) by ring, pow_mul, hζ.pow_eq_one, one_pow]
  rw [hmid, mul_one]
  congr 1
  set q := k / d
  rcases Nat.even_or_odd d with ⟨t, ht⟩ | ⟨t, ht⟩
  · have htpos : 0 < t := by omega
    have hneg : ζ ^ t = -1 := by
      have hsq : (ζ ^ t) ^ 2 = 1 := by
        rw [← pow_mul, show t * 2 = d by omega, hζ.pow_eq_one]
      have hne : ζ ^ t ≠ 1 := hζ.pow_ne_one_of_pos_of_lt htpos.ne' (by omega)
      rcases sq_eq_one_iff.mp hsq with h | h
      · exact absurd h hne
      · exact h
    have hexp : q * d * (q * d - 1) / 2 = t * (q * (q * d - 1)) := by
      have : q * d * (q * d - 1) = 2 * (t * (q * (q * d - 1))) := by
        rw [show d = 2 * t by omega]; ring
      rw [this, Nat.mul_div_cancel_left _ (by omega)]
    rw [hexp, pow_mul, hneg]
    rcases eq_or_ne q 0 with hq0 | hq0
    · simp [hq0]
    · have hpar : Even (q * (q * d - 1)) ↔ Even ((d - 1) * q) := by
        have hodd1 : Odd (q * d - 1) := by
          refine ⟨q * t - 1, ?_⟩
          have h1 : 1 ≤ q * t := Nat.mul_pos (Nat.pos_of_ne_zero hq0) htpos
          have h2 : q * d = 2 * (q * t) := by rw [show d = 2 * t by omega]; ring
          omega
        have hodd2 : Odd (d - 1) := ⟨t - 1, by omega⟩
        simp [Nat.even_mul, Nat.not_even_iff_odd.mpr hodd1, Nat.not_even_iff_odd.mpr hodd2]
      by_cases hev : Even ((d - 1) * q)
      · rw [Even.neg_one_pow (hpar.mpr hev), Even.neg_one_pow hev]
      · rw [Odd.neg_one_pow (Nat.not_even_iff_odd.mp (fun h => hev (hpar.mp h))),
            Odd.neg_one_pow (Nat.not_even_iff_odd.mp hev)]
  · have h2 : 2 ∣ q * (q * d - 1) := by
      rcases Nat.even_or_odd q with ⟨s, hs⟩ | ⟨s, hs⟩
      · exact ⟨s * (q * d - 1), by rw [hs]; ring⟩
      · have hqd_odd : Odd (q * d) := Odd.mul ⟨s, hs⟩ ⟨t, ht⟩
        obtain ⟨u, hu⟩ := hqd_odd
        refine ⟨q * u, ?_⟩
        rw [hu, Nat.add_sub_cancel]
        ring
    obtain ⟨m, hm⟩ := h2
    have hexp : q * d * (q * d - 1) / 2 = d * m := by
      have : q * d * (q * d - 1) = 2 * (d * m) := by
        calc q * d * (q * d - 1) = d * (q * (q * d - 1)) := by ring
          _ = d * (2 * m) := by rw [hm]
          _ = 2 * (d * m) := by ring
      rw [this, Nat.mul_div_cancel_left _ (by omega)]
    rw [hexp, pow_mul, hζ.pow_eq_one, one_pow]
    have hev : Even ((d - 1) * q) := by
      refine ⟨t * q, ?_⟩
      rw [ht, Nat.add_sub_cancel]
      ring
    rw [Even.neg_one_pow hev]

private lemma qLucas {ζ : ℂ} {d : ℕ} (hd : 2 ≤ d) (hζ : IsPrimitiveRoot ζ d) (n k : ℕ) :
    (qBinom n k).eval₂ (Int.castRingHom ℂ) ζ =
      ((n / d).choose (k / d) : ℂ) * (qBinom (n % d) (k % d)).eval₂ (Int.castRingHom ℂ) ζ := by
  have hd0 : 0 < d := by omega
  set P := ∏ i ∈ range n, (1 + C (ζ ^ i) * (X : ℂ[X]))
  set Q := ∏ r ∈ range (n % d), (1 + C (ζ ^ r) * (X : ℂ[X]))
  have hP : P = (1 - (-X) ^ d) ^ (n / d) * Q := by
    have hn : n = n / d * d + n % d := by
      rw [mul_comm, Nat.div_add_mod]
    conv_lhs => rw [show P = ∏ i ∈ range (n / d * d + n % d), (1 + C (ζ ^ i) * (X : ℂ[X])) by
      rw [← hn]]
    rw [prod_range_add, prod_blocks_eq hd0 hζ (n / d)]
    congr 1
    refine Finset.prod_congr rfl fun r _ => ?_
    have : ζ ^ (n / d * d + r) = ζ ^ r := by
      rw [pow_add, mul_comm (n / d) d, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
    rw [this]
  have hpow : (1 - (-X : ℂ[X]) ^ d) ^ (n / d) =
      ∑ j ∈ range (n / d + 1),
        C (((n / d).choose j : ℂ) * (-1 : ℂ) ^ ((d - 1) * j)) * X ^ (j * d) := by
    have hbase : (1 - (-X : ℂ[X]) ^ d) = C ((-1 : ℂ) ^ (d - 1)) * X ^ d + 1 := by
      have hneg : (-X : ℂ[X]) ^ d = C ((-1 : ℂ) ^ d) * X ^ d := by
        rw [neg_eq_neg_one_mul, mul_pow, map_pow, map_neg, map_one]
      have hsign : -((-1 : ℂ) ^ d) = (-1 : ℂ) ^ (d - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ d by omega), pow_succ]
        ring
      rw [hneg, sub_eq_add_neg, add_comm, ← neg_mul, ← map_neg, hsign]
    rw [hbase, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_pow, mul_one, mul_pow, ← C_pow, ← pow_mul, ← pow_mul, mul_comm d j]
    rw [show C (((n / d).choose j : ℂ) * (-1 : ℂ) ^ ((d - 1) * j)) =
      C (((n / d).choose j : ℂ)) * C ((-1 : ℂ) ^ ((d - 1) * j)) by rw [map_mul]]
    simp only [C_eq_natCast]
    ring
  have hcoeff : P.coeff k =
      ((n / d).choose (k / d) : ℂ) * (-1 : ℂ) ^ ((d - 1) * (k / d)) * Q.coeff (k % d) := by
    rw [hP, hpow, Finset.sum_mul, finsetSum_coeff]
    have hterm : ∀ j ∈ range (n / d + 1),
        (C (((n / d).choose j : ℂ) * (-1 : ℂ) ^ ((d - 1) * j)) * X ^ (j * d) * Q).coeff k =
          if j = k / d then
            ((n / d).choose (k / d) : ℂ) * (-1 : ℂ) ^ ((d - 1) * (k / d)) * Q.coeff (k % d)
          else 0 := by
      intro j _
      rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
      have hkdm : k / d * d + k % d = k := by rw [mul_comm, Nat.div_add_mod]
      split_ifs with hle hjeq hjeq
      · subst hjeq
        have : k - k / d * d = k % d := by omega
        rw [this]
      · have hgt : n % d < k - j * d := by
          have hmlt := Nat.mod_lt k hd0
          have hnlt := Nat.mod_lt n hd0
          have hjlt : j < k / d := by
            by_contra hge
            have h1 : (k / d + 1) * d ≤ j * d := Nat.mul_le_mul_right d (by omega)
            rw [Nat.add_mul, one_mul] at h1
            omega
          have h2 : (j + 1) * d ≤ k / d * d := Nat.mul_le_mul_right d hjlt
          rw [Nat.add_mul, one_mul] at h2
          omega
        have hQ0 : Q.coeff (k - j * d) = 0 := by
          rw [coeff_prod_qBinom ζ (n % d) (k - j * d), qBinom_eq_zero_of_lt hgt, eval₂_zero,
            mul_zero]
        rw [hQ0, mul_zero]
      · subst hjeq
        omega
      · exact mul_zero _
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · have hgt : n / d < k / d := by
        simp only [mem_range] at hmem; omega
      rw [Nat.choose_eq_zero_of_lt hgt]
      simp
  rw [coeff_prod_qBinom ζ n k, coeff_prod_qBinom ζ (n % d) (k % d)] at hcoeff
  rw [pow_tri_div_mod hd hζ k] at hcoeff
  have hunit : (-1 : ℂ) ^ ((d - 1) * (k / d)) * ζ ^ ((k % d) * (k % d - 1) / 2) ≠ 0 := by
    apply mul_ne_zero
    · exact pow_ne_zero _ (by norm_num)
    · exact pow_ne_zero _ (hζ.ne_zero (by omega))
  have hcoeff' :
      ((-1 : ℂ) ^ ((d - 1) * (k / d)) * ζ ^ ((k % d) * (k % d - 1) / 2)) *
        eval₂ (Int.castRingHom ℂ) ζ (qBinom n k) =
      ((-1 : ℂ) ^ ((d - 1) * (k / d)) * ζ ^ ((k % d) * (k % d - 1) / 2)) *
        (((n / d).choose (k / d) : ℂ) * eval₂ (Int.castRingHom ℂ) ζ (qBinom (n % d) (k % d))) := by
    calc _ = ((n / d).choose (k / d) : ℂ) * (-1 : ℂ) ^ ((d - 1) * (k / d)) *
            (ζ ^ ((k % d) * (k % d - 1) / 2) * eval₂ (Int.castRingHom ℂ) ζ (qBinom (n % d) (k % d))) := hcoeff
      _ = _ := by ring
  exact mul_left_cancel₀ hunit hcoeff'

private def qAntiSum (n m a b : ℕ) : ℤ[X] :=
  ∑ k ∈ Icc 1 m, (qBinom n k ^ a * qBinom n (k - 1) ^ b - qBinom n k ^ b * qBinom n (k - 1) ^ a)

private lemma eval_qAntiSum_eq_zero {ζ : ℂ} {d n m a b : ℕ} (hd : 2 ≤ d)
    (hζ : IsPrimitiveRoot ζ d) (hmod : n % d < m % d) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (qAntiSum n m a b).eval₂ (Int.castRingHom ℂ) ζ = 0 := by
  have hd0 : 0 < d := by omega
  let c : ℕ → ℂ := fun k => (qBinom n k).eval₂ (Int.castRingHom ℂ) ζ
  let bb : ℕ → ℂ := fun r => (qBinom (n % d) r).eval₂ (Int.castRingHom ℂ) ζ
  let g : ℂ → ℂ → ℂ := fun x y => x ^ a * y ^ b - x ^ b * y ^ a
  have hg0l : ∀ y : ℂ, g 0 y = 0 := by
    intro y; simp [g, zero_pow (by omega : a ≠ 0), zero_pow (by omega : b ≠ 0)]
  have hg0r : ∀ x : ℂ, g x 0 = 0 := by
    intro x; simp [g, zero_pow (by omega : a ≠ 0), zero_pow (by omega : b ≠ 0)]
  have hgsym : ∀ x y : ℂ, g y x = -g x y := by intro x y; simp [g]; ring
  have hEval : (qAntiSum n m a b).eval₂ (Int.castRingHom ℂ) ζ =
      ∑ k ∈ Icc 1 m, g (c k) (c (k - 1)) := by
    simp only [qAntiSum, eval₂_finsetSum, eval₂_sub, eval₂_mul, eval₂_pow, c, g]
  rw [hEval]
  have hbb_zero : ∀ r : ℕ, n % d < r → bb r = 0 := fun r hr => by
    simp [bb, qBinom_eq_zero_of_lt hr]
  have hbb_symm : ∀ r : ℕ, r ≤ n % d → bb (n % d - r) = bb r := fun r hr => by
    simp [bb, qBinom_symm (n % d) r hr]
  have hc : ∀ k : ℕ, c k = ((n / d).choose (k / d) : ℂ) * bb (k % d) :=
    fun k => qLucas hd hζ n k
  have hterm_zero : ∀ k ∈ Icc 1 m, ¬ (1 ≤ k % d ∧ k % d ≤ n % d) → g (c k) (c (k - 1)) = 0 := by
    intro k hk hnot
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    by_cases h0 : k % d = 0
    · have hkm1 : (k - 1) % d = d - 1 := by
        have hkdiv : d ∣ k := Nat.dvd_of_mod_eq_zero h0
        rcases hkdiv with ⟨q, hq⟩
        rcases q with _ | q
        · omega
        · have hkm : k - 1 = d * q + (d - 1) := by
            have : d * (q + 1) = d * q + d := by ring
            omega
          rw [hkm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega : d - 1 < d)]
      have hlt : n % d < (k - 1) % d := by
        have := Nat.mod_lt m hd0
        omega
      rw [hc (k - 1), hbb_zero _ hlt, mul_zero, hg0r]
    · have hgt : n % d < k % d := by omega
      rw [hc k, hbb_zero _ hgt, mul_zero, hg0l]
  have hfilt : ∑ k ∈ Icc 1 m, g (c k) (c (k - 1)) =
      ∑ k ∈ (Icc 1 m).filter (fun k => 1 ≤ k % d ∧ k % d ≤ n % d), g (c k) (c (k - 1)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 m) (fun k => 1 ≤ k % d ∧ k % d ≤ n % d)]
    have hrest : ∑ k ∈ (Icc 1 m).filter (fun k => ¬ (1 ≤ k % d ∧ k % d ≤ n % d)),
        g (c k) (c (k - 1)) = 0 :=
      Finset.sum_eq_zero fun k hk => hterm_zero k (mem_filter.mp hk).1 (mem_filter.mp hk).2
    rw [hrest, add_zero]
  rw [hfilt]
  have hbij : ∑ k ∈ (Icc 1 m).filter (fun k => 1 ≤ k % d ∧ k % d ≤ n % d), g (c k) (c (k - 1)) =
      ∑ p ∈ (range (m / d + 1)) ×ˢ (Icc 1 (n % d)),
        g (c (p.1 * d + p.2)) (c (p.1 * d + p.2 - 1)) := by
    refine Finset.sum_nbij (fun k => (k / d, k % d)) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [mem_filter, mem_Icc] at hk
      simp only [mem_product, mem_range, mem_Icc]
      exact ⟨Nat.lt_succ_of_le (Nat.div_le_div_right hk.1.2), hk.2⟩
    · intro k₁ _ k₂ _ heq
      have hq : k₁ / d = k₂ / d := congr_arg Prod.fst heq
      have hr : k₁ % d = k₂ % d := congr_arg Prod.snd heq
      rw [← Nat.div_add_mod k₁ d, ← Nat.div_add_mod k₂ d, hq, hr]
    · rintro ⟨j, r⟩ hp
      simp only [Finset.mem_coe, mem_product, mem_range, mem_Icc] at hp
      refine ⟨j * d + r, ?_, ?_⟩
      · simp only [Finset.mem_coe, mem_filter, mem_Icc]
        have hrlt : r < d := by have := Nat.mod_lt n hd0; omega
        have hrmod : (j * d + r) % d = r := by
          rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hrlt]
        have hle : j * d + r ≤ m := by
          have hm1 : m / d * d + m % d = m := by rw [mul_comm, Nat.div_add_mod]
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hp.1) with hlt | rfl
          · have h1 : (j + 1) * d ≤ m / d * d := Nat.mul_le_mul_right d hlt
            rw [Nat.add_mul, one_mul] at h1
            omega
          · omega
        exact ⟨⟨by omega, hle⟩, by rw [hrmod]; exact hp.2⟩
      · have hrlt : r < d := by have := Nat.mod_lt n hd0; omega
        ext
        · simp [mul_comm, Nat.mul_add_div hd0, Nat.div_eq_of_lt hrlt]
        · simp [mul_comm, Nat.mod_eq_of_lt hrlt]
    · intro k _
      have hk : k / d * d + k % d = k := by rw [mul_comm, Nat.div_add_mod]
      simp [hk]
  rw [hbij, Finset.sum_product]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hinner : ∀ r ∈ Icc 1 (n % d),
      g (c (j * d + r)) (c (j * d + r - 1)) =
        g (((n / d).choose j : ℂ) * bb r) (((n / d).choose j : ℂ) * bb (r - 1)) := by
    intro r hr
    simp only [mem_Icc] at hr
    have hrlt : r < d := by have := Nat.mod_lt n hd0; omega
    have hrm1lt : r - 1 < d := by omega
    have h1 : (j * d + r) / d = j := by
      rw [mul_comm, Nat.mul_add_div hd0, Nat.div_eq_of_lt hrlt, add_zero]
    have h2 : (j * d + r) % d = r := by
      rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hrlt]
    have hsub : j * d + r - 1 = j * d + (r - 1) := by omega
    have h3 : (j * d + r - 1) / d = j := by
      rw [hsub, mul_comm, Nat.mul_add_div hd0, Nat.div_eq_of_lt hrm1lt, add_zero]
    have h4 : (j * d + r - 1) % d = r - 1 := by
      rw [hsub, mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hrm1lt]
    rw [hc, hc, h1, h2, h3, h4]
  rw [Finset.sum_congr rfl hinner]
  set S_in := ∑ r ∈ Icc 1 (n % d),
    g (((n / d).choose j : ℂ) * bb r) (((n / d).choose j : ℂ) * bb (r - 1))
  have hneg : S_in = -S_in := by
    have hrev : S_in = ∑ r ∈ Icc 1 (n % d),
        g (((n / d).choose j : ℂ) * bb (n % d + 1 - r))
          (((n / d).choose j : ℂ) * bb (n % d + 1 - r - 1)) := by
      symm
      refine Finset.sum_nbij (fun r => n % d + 1 - r) ?_ ?_ ?_ ?_
      · intro r hr; simp only [mem_Icc] at hr ⊢; omega
      · intro r₁ hr₁ r₂ hr₂ heq; simp only [Finset.mem_coe, mem_Icc] at hr₁ hr₂; dsimp only at heq; omega
      · intro r hr
        simp only [Finset.mem_coe, mem_Icc] at hr
        exact ⟨n % d + 1 - r, Finset.mem_coe.mpr (mem_Icc.mpr ⟨by omega, by omega⟩), by dsimp only; omega⟩
      · intro r _; rfl
    conv_lhs => rw [hrev]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    simp only [mem_Icc] at hr
    have h1 : bb (n % d + 1 - r) = bb (r - 1) := by
      have : n % d + 1 - r = n % d - (r - 1) := by omega
      rw [this, hbb_symm (r - 1) (by omega)]
    have h2 : bb (n % d + 1 - r - 1) = bb r := by
      have : n % d + 1 - r - 1 = n % d - r := by omega
      rw [this, hbb_symm r hr.2]
    rw [h1, h2, hgsym]
  have h2 : S_in + S_in = 0 := by
    calc S_in + S_in = S_in + (-S_in) := by rw [← hneg]
      _ = 0 := add_neg_cancel S_in
  have : (2 : ℂ) * S_in = 0 := by rw [two_mul]; exact h2
  exact (mul_eq_zero.mp this).resolve_left (by norm_num)

private lemma monic_dvd_of_map_rat_dvd {g f : ℤ[X]} (hg : g.Monic)
    (hdvd : g.map (Int.castRingHom ℚ) ∣ f.map (Int.castRingHom ℚ)) : g ∣ f := by
  set r := f %ₘ g
  have hdiv : r + g * (f /ₘ g) = f := modByMonic_add_div f g
  have hr0 : r = 0 := by
    by_contra hrne
    have hmap : r.map (Int.castRingHom ℚ) +
        g.map (Int.castRingHom ℚ) * (f /ₘ g).map (Int.castRingHom ℚ) =
        f.map (Int.castRingHom ℚ) := by
      simpa [Polynomial.map_add, Polynomial.map_mul] using
        congr_arg (Polynomial.map (Int.castRingHom ℚ)) hdiv
    have hrdvd : g.map (Int.castRingHom ℚ) ∣ r.map (Int.castRingHom ℚ) := by
      have : r.map (Int.castRingHom ℚ) =
          f.map (Int.castRingHom ℚ) -
            g.map (Int.castRingHom ℚ) * (f /ₘ g).map (Int.castRingHom ℚ) :=
        eq_sub_of_add_eq hmap
      rw [this]
      exact dvd_sub hdvd (dvd_mul_right _ _)
    have hrq0 : r.map (Int.castRingHom ℚ) ≠ 0 := by
      intro h
      exact hrne (Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective (by simpa using h))
    have hdeg_le : (g.map (Int.castRingHom ℚ)).natDegree ≤ (r.map (Int.castRingHom ℚ)).natDegree :=
      Polynomial.natDegree_le_of_dvd hrdvd hrq0
    have hdeg_g : (g.map (Int.castRingHom ℚ)).natDegree = g.natDegree :=
      Polynomial.natDegree_map_eq_of_injective Int.cast_injective g
    have hdeg_r : (r.map (Int.castRingHom ℚ)).natDegree = r.natDegree :=
      Polynomial.natDegree_map_eq_of_injective Int.cast_injective r
    by_cases hg1 : g = 1
    · subst hg1; simp [r] at hrne
    · have hlt : r.natDegree < g.natDegree := Polynomial.natDegree_modByMonic_lt f hg hg1
      omega
  refine ⟨f /ₘ g, ?_⟩
  rw [hr0, zero_add] at hdiv
  exact hdiv.symm

private lemma choose_dvd_antiSum (n m a b : ℕ) (hm : m ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (n.choose m : ℤ) ∣
      ∑ k ∈ Icc 1 m,
        ((n.choose k : ℤ) ^ a * (n.choose (k - 1) : ℤ) ^ b -
          (n.choose k : ℤ) ^ b * (n.choose (k - 1) : ℤ) ^ a) := by
  have hpoly : qBinom n m ∣ qAntiSum n m a b := by
    apply monic_dvd_of_map_rat_dvd (qBinom_monic n m hm)
    rw [qBinom_eq_prod_cyclotomic n m hm, Polynomial.map_prod]
    simp_rw [map_cyclotomic_int]
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro d₁ _ d₂ _ hne
      exact cyclotomic.isCoprime_rat hne
    · intro d hd
      simp only [mem_filter, mem_Icc] at hd
      have hd2 : 2 ≤ d := hd.1.1
      have hd0 : 0 < d := by omega
      have hζ := Complex.isPrimitiveRoot_exp d (by omega)
      rw [cyclotomic_eq_minpoly_rat hζ hd0]
      apply minpoly.dvd ℚ
      have hzero := eval_qAntiSum_eq_zero hd2 hζ hd.2 ha hb
      rw [aeval_def, eval₂_map]
      have hcomp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := by
        ext x; simp
      rw [hcomp]
      exact hzero
  obtain ⟨Q, hQ⟩ := hpoly
  refine ⟨Q.eval 1, ?_⟩
  have hev := congr_arg (Polynomial.eval 1) hQ
  simp only [eval_mul, eval_one_qBinom] at hev
  rw [← hev]
  simp only [qAntiSum, eval_finsetSum, eval_sub, eval_mul, eval_pow, eval_one_qBinom]

private lemma S_one_eq (n : ℕ) : S 1 n = (n.choose (n / 2) : ℤ) := by
  have hgen : ∀ m : ℕ,
      (∑ k ∈ range (m + 1),
        ((n.choose k : ℤ) - if k = 0 then 0 else (n.choose (k - 1) : ℤ))) =
      (n.choose m : ℤ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, ih]
      simp
  simpa [S] using hgen (n / 2)

private lemma sum_pow_telescope (n m r : ℕ) (hr : 1 ≤ r) :
    (∑ k ∈ range (m + 1),
      ((n.choose k : ℤ) ^ r - (if k = 0 then (0 : ℤ) else (n.choose (k - 1) : ℤ)) ^ r)) =
    (n.choose m : ℤ) ^ r := by
  induction m with
  | zero =>
    simp [zero_pow (by omega : r ≠ 0)]
  | succ m ih =>
    rw [sum_range_succ, ih]
    simp

private lemma main_proof : ∀ n : ℕ, S 1 n ∣ S 7 n := by
  intro n
  rw [S_one_eq n]
  set m := n / 2
  have hm : m ≤ n := Nat.div_le_self n 2
  let f : ℕ → ℤ := fun k => (n.choose k : ℤ)
  let g : ℕ → ℤ := fun k => if k = 0 then 0 else (n.choose (k - 1) : ℤ)
  have hexp : ∀ k : ℕ,
      (f k - g k) ^ 7 =
        (f k ^ 7 - g k ^ 7) - 7 * (f k ^ 6 * g k - f k * g k ^ 6) +
          21 * (f k ^ 5 * g k ^ 2 - f k ^ 2 * g k ^ 5) -
          35 * (f k ^ 4 * g k ^ 3 - f k ^ 3 * g k ^ 4) := by
    intro k; ring
  have hS7 : S 7 n =
      (∑ k ∈ range (m + 1), (f k ^ 7 - g k ^ 7)) -
        7 * (∑ k ∈ range (m + 1), (f k ^ 6 * g k - f k * g k ^ 6)) +
        21 * (∑ k ∈ range (m + 1), (f k ^ 5 * g k ^ 2 - f k ^ 2 * g k ^ 5)) -
        35 * (∑ k ∈ range (m + 1), (f k ^ 4 * g k ^ 3 - f k ^ 3 * g k ^ 4)) := by
    change ∑ k ∈ range (m + 1), (f k - g k) ^ 7 = _
    simp_rw [hexp]
    simp only [sum_add_distrib, sum_sub_distrib, ← Finset.mul_sum]
  rw [hS7]
  have hshift : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      (∑ k ∈ range (m + 1), (f k ^ a * g k ^ b - f k ^ b * g k ^ a)) =
        ∑ k ∈ Icc 1 m,
          ((n.choose k : ℤ) ^ a * (n.choose (k - 1) : ℤ) ^ b -
            (n.choose k : ℤ) ^ b * (n.choose (k - 1) : ℤ) ^ a) := by
    intro a b ha hb
    have hsplit : range (m + 1) = insert 0 (Icc 1 m) := by
      ext k; simp only [mem_range, mem_insert, mem_Icc]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    have h0 : f 0 ^ a * g 0 ^ b - f 0 ^ b * g 0 ^ a = 0 := by
      simp [g, zero_pow (by omega : a ≠ 0), zero_pow (by omega : b ≠ 0)]
    rw [h0, zero_add]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
    simp [f, g, hk0]
  have htel : (n.choose m : ℤ) ∣ ∑ k ∈ range (m + 1), (f k ^ 7 - g k ^ 7) := by
    rw [sum_pow_telescope n m 7 (by omega)]
    exact dvd_pow_self _ (by omega)
  have hd61 : (n.choose m : ℤ) ∣ ∑ k ∈ range (m + 1), (f k ^ 6 * g k - f k * g k ^ 6) := by
    have h61 := choose_dvd_antiSum n m 6 1 hm (by omega) (by omega)
    rw [← hshift 6 1 (by omega) (by omega)] at h61
    simpa only [pow_one] using h61
  have hd52 : (n.choose m : ℤ) ∣ ∑ k ∈ range (m + 1), (f k ^ 5 * g k ^ 2 - f k ^ 2 * g k ^ 5) := by
    rw [hshift 5 2 (by omega) (by omega)]
    exact choose_dvd_antiSum n m 5 2 hm (by omega) (by omega)
  have hd43 : (n.choose m : ℤ) ∣ ∑ k ∈ range (m + 1), (f k ^ 4 * g k ^ 3 - f k ^ 3 * g k ^ 4) := by
    rw [hshift 4 3 (by omega) (by omega)]
    exact choose_dvd_antiSum n m 4 3 hm (by omega) (by omega)
  exact dvd_sub
    (dvd_add (dvd_sub htel (dvd_mul_of_dvd_right hd61 7)) (dvd_mul_of_dvd_right hd52 21))
    (dvd_mul_of_dvd_right hd43 35)

end

end OMA.S_oeis_a361891

theorem OMA.solution : type_of% @OMA.S_oeis_a361891.main :=
  OMA.S_oeis_a361891.main_proof
