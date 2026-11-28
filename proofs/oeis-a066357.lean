import OMAStatements.S_oeis_a066357

/-!
Proof of Clément Garrot's 2-adic valuation identity for OEIS A066357:
Let S(n) = catalan (2*n + 1) + 2 * catalan (2*n) and T(n) = 2^(2*n + 1) * catalan n,
so a(n) = S(n) - T(n). Using (m + 1) * catalan m = m.centralBinom and
(2 * m)! = 2^m * m! * oddDouble m, we obtain
  (n + 1) * S(n) = 3 * (2*n).centralBinom
and
  (2*n).centralBinom * (oddDouble n)^2 = n.centralBinom * oddDouble (2*n),
whence v_2(S(n)) = v_2(catalan n). Since v_2(T(n)) = (2*n + 1) + v_2(catalan n) > v_2(S(n)),
S(n) != T(n) and v_2(|S(n) - T(n)|) = v_2(catalan n).
-/

namespace OMA.P_oeis_a066357

private def oddDouble : ℕ → ℕ
  | 0 => 1
  | m + 1 => (2 * m + 1) * oddDouble m

private lemma oddDouble_odd (m : ℕ) : Odd (oddDouble m) := by
  induction m with
  | zero => exact odd_one
  | succ m ih =>
    have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
    exact hodd.mul ih

private lemma oddDouble_pos (m : ℕ) : 0 < oddDouble m :=
  (oddDouble_odd m).pos

private lemma two_mul_factorial (m : ℕ) :
    (2 * m).factorial = 2 ^ m * m.factorial * oddDouble m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, Nat.factorial_succ,
      Nat.factorial_succ, ih]
    simp only [oddDouble, Nat.factorial_succ, pow_succ']
    ring

private lemma centralBinom_mul_factorial (m : ℕ) :
    m.centralBinom * m.factorial = 2 ^ m * oddDouble m := by
  have hch := Nat.choose_mul_factorial_mul_factorial (by omega : m ≤ 2 * m)
  rw [show 2 * m - m = m by omega, ← Nat.centralBinom_eq_two_mul_choose,
    two_mul_factorial] at hch
  have hfac : m.centralBinom * m.factorial * m.factorial =
      2 ^ m * oddDouble m * m.factorial := by
    linarith [hch]
  exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos m) hfac

private lemma centralBinom_two_mul_eq (n : ℕ) :
    (2 * n).centralBinom * oddDouble n ^ 2 = n.centralBinom * oddDouble (2 * n) := by
  have h1 := centralBinom_mul_factorial n
  have h2 := centralBinom_mul_factorial (2 * n)
  rw [two_mul_factorial] at h2
  have h2' : 2 ^ n * ((2 * n).centralBinom * n.factorial * oddDouble n) =
      2 ^ n * (2 ^ n * oddDouble (2 * n)) := by
    calc 2 ^ n * ((2 * n).centralBinom * n.factorial * oddDouble n)
        = (2 * n).centralBinom * (2 ^ n * n.factorial * oddDouble n) := by ring
      _ = 2 ^ (2 * n) * oddDouble (2 * n) := h2
      _ = 2 ^ n * (2 ^ n * oddDouble (2 * n)) := by rw [two_mul, pow_add, mul_assoc]
  have h3 : (2 * n).centralBinom * n.factorial * oddDouble n =
      2 ^ n * oddDouble (2 * n) :=
    Nat.eq_of_mul_eq_mul_left (by positivity) h2'
  have h4 : (2 * n).centralBinom * oddDouble n ^ 2 * n.factorial =
      n.centralBinom * oddDouble (2 * n) * n.factorial := by
    calc (2 * n).centralBinom * oddDouble n ^ 2 * n.factorial
        = ((2 * n).centralBinom * n.factorial * oddDouble n) * oddDouble n := by ring
      _ = (2 ^ n * oddDouble (2 * n)) * oddDouble n := by rw [h3]
      _ = (2 ^ n * oddDouble n) * oddDouble (2 * n) := by ring
      _ = (n.centralBinom * n.factorial) * oddDouble (2 * n) := by rw [← h1]
      _ = n.centralBinom * oddDouble (2 * n) * n.factorial := by ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos n) h4

private lemma succ_mul_catalan (m : ℕ) : (m + 1) * catalan m = m.centralBinom := by
  rw [catalan_eq_centralBinom_div, Nat.mul_div_cancel' (Nat.succ_dvd_centralBinom m)]

private lemma catalan_pos' (m : ℕ) : 0 < catalan m := by
  have hcb : 0 < m.centralBinom := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    exact Nat.choose_pos (by omega)
  by_contra h0
  have hc0 : catalan m = 0 := by omega
  have heq := succ_mul_catalan m
  rw [hc0, mul_zero] at heq
  omega

private lemma catalan_step_identity (n : ℕ) :
    (n + 1) * (catalan (2 * n + 1) + 2 * catalan (2 * n)) =
      3 * (2 * n).centralBinom := by
  have hc1 := succ_mul_catalan (2 * n)
  have hc2 := succ_mul_catalan (2 * n + 1)
  have hcb := Nat.succ_mul_centralBinom_succ (2 * n)
  have hstep : (2 * n + 1) * ((2 * n + 2) * catalan (2 * n + 1)) =
      (2 * n + 1) * ((4 * (2 * n) + 2) * catalan (2 * n)) := by
    calc (2 * n + 1) * ((2 * n + 2) * catalan (2 * n + 1))
        = (2 * n + 1) * (2 * n + 1).centralBinom := by rw [hc2]
      _ = 2 * (2 * (2 * n) + 1) * (2 * n).centralBinom := hcb
      _ = 2 * (2 * (2 * n) + 1) * ((2 * n + 1) * catalan (2 * n)) := by rw [← hc1]
      _ = (2 * n + 1) * ((4 * (2 * n) + 2) * catalan (2 * n)) := by ring
  have hstep1 : (2 * n + 2) * catalan (2 * n + 1) = (4 * (2 * n) + 2) * catalan (2 * n) :=
    Nat.eq_of_mul_eq_mul_left (by omega) hstep
  have hstep2 : 2 * ((n + 1) * catalan (2 * n + 1)) =
      2 * ((4 * n + 1) * catalan (2 * n)) := by
    linarith [hstep1]
  have hstep3 : (n + 1) * catalan (2 * n + 1) = (4 * n + 1) * catalan (2 * n) :=
    Nat.eq_of_mul_eq_mul_left (by omega) hstep2
  calc (n + 1) * (catalan (2 * n + 1) + 2 * catalan (2 * n))
      = (n + 1) * catalan (2 * n + 1) + 2 * (n + 1) * catalan (2 * n) := by ring
    _ = (4 * n + 1) * catalan (2 * n) + 2 * (n + 1) * catalan (2 * n) := by rw [hstep3]
    _ = 3 * ((2 * n + 1) * catalan (2 * n)) := by ring
    _ = 3 * (2 * n).centralBinom := by rw [hc1]

private lemma odd_fact_two {x : ℕ} (hx : Odd x) : x.factorization 2 = 0 := by
  have hndvd : ¬ 2 ∣ x := by
    rintro ⟨t, rfl⟩
    rcases hx with ⟨s, hs⟩
    omega
  by_contra hne
  have hle : 1 ≤ x.factorization 2 := Nat.pos_of_ne_zero hne
  exact hndvd ((Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hx.pos.ne').mpr hle)

private lemma two_pow_dvd_iff_le_fact {m x : ℕ} (hx : x ≠ 0) :
    2 ^ m ∣ x ↔ m ≤ x.factorization 2 := by
  rw [← Nat.factorization_le_iff_dvd (by positivity) hx, Nat.factorization_pow]
  constructor
  · intro hle
    have h2 := hle 2
    simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      Nat.Prime.factorization_self Nat.prime_two, mul_one] at h2
    exact h2
  · intro hm p
    simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hp : p = 2
    · subst hp
      rw [Nat.Prime.factorization_self Nat.prime_two, mul_one]
      exact hm
    · by_cases hp1 : p = 1
      · subst hp1; simp
      · have hnd : ¬ p ∣ 2 := fun hd =>
          hp ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hp1)
        simp [Nat.factorization_eq_zero_of_not_dvd hnd]

end OMA.P_oeis_a066357

theorem OMA.solution : type_of% @OMA.S_oeis_a066357.main := by
  intro n
  let S : ℕ := catalan (2 * n + 1) + 2 * catalan (2 * n)
  let T : ℕ := 2 ^ (2 * n + 1) * catalan n
  have hS_pos : 0 < S := by
    have h1 := OMA.P_oeis_a066357.catalan_pos' (2 * n + 1)
    have h2 := OMA.P_oeis_a066357.catalan_pos' (2 * n)
    dsimp [S]
    omega
  have hc_pos : 0 < catalan n := OMA.P_oeis_a066357.catalan_pos' n
  have hT_pos : 0 < T := by
    dsimp [T]
    positivity
  have hcb_pos : ∀ m : ℕ, 0 < m.centralBinom := fun m => by
    rw [Nat.centralBinom_eq_two_mul_choose]
    exact Nat.choose_pos (by omega)
  have hcb_eq := OMA.P_oeis_a066357.centralBinom_two_mul_eq n
  have hcb_fact : (2 * n).centralBinom.factorization 2 = n.centralBinom.factorization 2 := by
    have hlhs : ((2 * n).centralBinom * OMA.P_oeis_a066357.oddDouble n ^ 2).factorization 2 =
        (2 * n).centralBinom.factorization 2 := by
      rw [Nat.factorization_mul (hcb_pos (2 * n)).ne'
        (pow_ne_zero 2 (OMA.P_oeis_a066357.oddDouble_pos n).ne'),
        Nat.factorization_pow]
      have hof : (OMA.P_oeis_a066357.oddDouble n).factorization 2 = 0 :=
        OMA.P_oeis_a066357.odd_fact_two (OMA.P_oeis_a066357.oddDouble_odd n)
      simp [hof]
    have hrhs : (n.centralBinom * OMA.P_oeis_a066357.oddDouble (2 * n)).factorization 2 =
        n.centralBinom.factorization 2 := by
      rw [Nat.factorization_mul (hcb_pos n).ne' (OMA.P_oeis_a066357.oddDouble_pos (2 * n)).ne']
      have hof := OMA.P_oeis_a066357.odd_fact_two (OMA.P_oeis_a066357.oddDouble_odd (2 * n))
      rw [Finsupp.coe_add, Pi.add_apply, hof, add_zero]
    rw [← hlhs, ← hrhs, hcb_eq]
  have hS_fact : S.factorization 2 = (catalan n).factorization 2 := by
    have h1 := OMA.P_oeis_a066357.catalan_step_identity n
    have h2 := OMA.P_oeis_a066357.succ_mul_catalan n
    have hf1 : ((n + 1) * S).factorization 2 = (3 * (2 * n).centralBinom).factorization 2 :=
      congrArg (fun x : ℕ => x.factorization 2) h1
    have hf2 : ((n + 1) * catalan n).factorization 2 = n.centralBinom.factorization 2 :=
      congrArg (fun x : ℕ => x.factorization 2) h2
    rw [Nat.factorization_mul (by omega) hS_pos.ne',
      Nat.factorization_mul (by norm_num) (hcb_pos (2 * n)).ne'] at hf1
    rw [Nat.factorization_mul (by omega) hc_pos.ne'] at hf2
    have h3 : (3 : ℕ).factorization 2 = 0 := OMA.P_oeis_a066357.odd_fact_two ⟨1, rfl⟩
    simp only [Finsupp.coe_add, Pi.add_apply, h3, zero_add] at hf1 hf2
    omega
  set k := (catalan n).factorization 2
  have hS_dvd : 2 ^ k ∣ S :=
    (OMA.P_oeis_a066357.two_pow_dvd_iff_le_fact hS_pos.ne').mpr (by rw [hS_fact])
  have hS_ndvd : ¬ 2 ^ (k + 1) ∣ S := by
    rw [OMA.P_oeis_a066357.two_pow_dvd_iff_le_fact hS_pos.ne', hS_fact]
    omega
  have hT_fact : T.factorization 2 = (2 * n + 1) + k := by
    dsimp [T]
    rw [Nat.factorization_mul (by positivity) hc_pos.ne', Nat.factorization_pow]
    simp [Nat.Prime.factorization_self Nat.prime_two, k]
  have hT_dvd1 : 2 ^ (k + 1) ∣ T := by
    rw [OMA.P_oeis_a066357.two_pow_dvd_iff_le_fact hT_pos.ne', hT_fact]
    omega
  have hT_dvd0 : 2 ^ k ∣ T :=
    dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_succ k)) hT_dvd1
  have hST_ne : S ≠ T := by
    intro heq
    rw [← heq] at hT_dvd1
    exact hS_ndvd hT_dvd1
  have ha_eq : OMA.S_oeis_a066357.a n = (S : ℤ) - (T : ℤ) := rfl
  have ha_ne : OMA.S_oeis_a066357.a n ≠ 0 := by
    rw [ha_eq]
    omega
  refine ⟨ha_ne, ?_⟩
  set D := (OMA.S_oeis_a066357.a n).natAbs
  have hD_pos : 0 < D := Int.natAbs_pos.mpr ha_ne
  have hD_dvd0 : 2 ^ k ∣ D := by
    rcases le_total S T with hle | hle
    · have hD : D = T - S := by dsimp [D]; rw [ha_eq]; omega
      rw [hD]
      exact Nat.dvd_sub hT_dvd0 hS_dvd
    · have hD : D = S - T := by dsimp [D]; rw [ha_eq]; omega
      rw [hD]
      exact Nat.dvd_sub hS_dvd hT_dvd0
  have hD_ndvd1 : ¬ 2 ^ (k + 1) ∣ D := by
    intro hdvd
    rcases le_total S T with hle | hle
    · have hD : D = T - S := by dsimp [D]; rw [ha_eq]; omega
      have hS_eq : S = T - D := by omega
      rw [hS_eq] at hS_ndvd
      exact hS_ndvd (Nat.dvd_sub hT_dvd1 hdvd)
    · have hD : D = S - T := by dsimp [D]; rw [ha_eq]; omega
      have hS_eq : S = D + T := by omega
      rw [hS_eq] at hS_ndvd
      exact hS_ndvd (Nat.dvd_add hdvd hT_dvd1)
  have h1 : k ≤ D.factorization 2 :=
    (OMA.P_oeis_a066357.two_pow_dvd_iff_le_fact hD_pos.ne').mp hD_dvd0
  have h2 : ¬ k + 1 ≤ D.factorization 2 := by
    rwa [← OMA.P_oeis_a066357.two_pow_dvd_iff_le_fact hD_pos.ne']
  omega
