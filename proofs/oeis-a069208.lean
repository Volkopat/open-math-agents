import OMAStatements.S_oeis_a069208

-- Problem: OEIS A069208, Schulte's conjecture on sums over the powerful divisors
-- Statement: statements/oeis-a069208.lean (declaration OMA.S_oeis_a069208.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Part (2) is the definition: the sum of f(d) over the powerful divisors d of n is the
-- sum of chi(d) f(d) over all divisors. For part (1), a product of coprime numbers is powerful
-- exactly when the two factors are powerful, so chi is multiplicative, and chi * f is
-- multiplicative. Its Dirichlet convolution with the constant 1 is then multiplicative.

namespace OMA.A069208

open Finset ArithmeticFunction OMA.S_oeis_a069208

/-- For coprime factors, the product is powerful exactly when the two factors are powerful. -/
lemma powerful_mul (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    (∀ p ∈ (m * n).primeFactors, p ^ 2 ∣ m * n)
      ↔ (∀ p ∈ m.primeFactors, p ^ 2 ∣ m) ∧ (∀ p ∈ n.primeFactors, p ^ 2 ∣ n) := by
  constructor
  · intro H
    constructor
    · intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpm := Nat.dvd_of_mem_primeFactors hp
      have hmem : p ∈ (m * n).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpp, Dvd.dvd.mul_right hpm n, Nat.mul_ne_zero hm hn⟩
      have hc : Nat.Coprime (p ^ 2) n := (Nat.Coprime.coprime_dvd_left hpm h).pow_left 2
      exact hc.dvd_of_dvd_mul_right (H p hmem)
    · intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpn := Nat.dvd_of_mem_primeFactors hp
      have hmem : p ∈ (m * n).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpp, Dvd.dvd.mul_left hpn m, Nat.mul_ne_zero hm hn⟩
      have hc : Nat.Coprime (p ^ 2) m := (Nat.Coprime.coprime_dvd_left hpn h.symm).pow_left 2
      exact hc.dvd_of_dvd_mul_left (H p hmem)
  · rintro ⟨H1, H2⟩ p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    rcases (Nat.Prime.dvd_mul hpp).mp (Nat.dvd_of_mem_primeFactors hp) with hpm | hpn
    · exact Dvd.dvd.mul_right (H1 p (Nat.mem_primeFactors.mpr ⟨hpp, hpm, hm⟩)) n
    · exact Dvd.dvd.mul_left (H2 p (Nat.mem_primeFactors.mpr ⟨hpp, hpn, hn⟩)) m

lemma chi_mul (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    chi (m * n) = chi m * chi n := by
  unfold chi
  by_cases h1 : ∀ p ∈ m.primeFactors, p ^ 2 ∣ m
  · by_cases h2 : ∀ p ∈ n.primeFactors, p ^ 2 ∣ n
    · rw [if_pos h1, if_pos h2, if_pos ((powerful_mul m n hm hn h).mpr ⟨h1, h2⟩)]
      simp
    · rw [if_pos h1, if_neg h2, if_neg (fun H => h2 ((powerful_mul m n hm hn h).mp H).2)]
      simp
  · rw [if_neg h1, if_neg (fun H => h1 ((powerful_mul m n hm hn h).mp H).1)]
    simp

lemma chi_one : chi 1 = 1 := by
  simp [chi]

lemma P_eq (f : ℕ → ℤ) (n : ℕ) : P f n = ∑ d ∈ n.divisors, chi d * f d := by
  unfold P chi
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs <;> simp

theorem result (f : ℕ → ℤ) (h1 : f 1 = 1)
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) :
    (P f 1 = 1 ∧
      ∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n → P f (m * n) = P f m * P f n) ∧
    ∀ n : ℕ, 0 < n → P f n = ∑ d ∈ n.divisors, chi d * f d := by
  set g : ArithmeticFunction ℤ := ⟨fun d => if d = 0 then 0 else chi d * f d, by simp⟩ with hg
  have g_apply : ∀ d : ℕ, g d = if d = 0 then 0 else chi d * f d := fun d => rfl
  have g_mult : IsMultiplicative g := by
    refine ⟨by simp [g_apply, chi_one, h1], ?_⟩
    intro x y hxy
    rw [g_apply, g_apply, g_apply]
    by_cases hx : x = 0
    · simp [hx]
    · by_cases hy : y = 0
      · simp [hy]
      · rw [if_neg hx, if_neg hy, if_neg (Nat.mul_ne_zero hx hy), hmul x y hxy,
          chi_mul x y hx hy hxy]
        ring
  have hG : IsMultiplicative (g * ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)) :=
    g_mult.mul isMultiplicative_zeta.natCast
  have hP : ∀ n : ℕ, P f n = (g * ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)) n := by
    intro n
    rw [coe_mul_zeta_apply, P_eq]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [g_apply, if_neg (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))]
  refine ⟨⟨?_, ?_⟩, fun n _ => P_eq f n⟩
  · rw [hP]
    exact hG.1
  · intro m n _ _ hmn
    rw [hP, hP, hP]
    exact hG.2 hmn

end OMA.A069208

theorem OMA.solution : type_of% @OMA.S_oeis_a069208.main :=
  fun f h1 hmul => OMA.A069208.result f h1 hmul
