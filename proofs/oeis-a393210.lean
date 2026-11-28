import OMAStatements.S_oeis_a393210

namespace OMA.A393210
open OMA.S_oeis_a393210 ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

lemma runs_trans_aux {c : Config} {t₁ : ℕ} {y : Option Config} (h₁ : Runs c t₁ y) :
    ∀ (d : Config) (t₂ : ℕ) (z : Option Config), y = some d → Runs d t₂ z → Runs c (t₁ + t₂) z := by
  induction h₁ with
  | one c =>
    intro d t₂ z hy h₂
    rw [Nat.add_comm]
    exact Runs.more hy h₂
  | @more c' d' t z' hs _ ih =>
    intro d t₂ z hy h₂
    rw [show t + 1 + t₂ = (t + t₂) + 1 by omega]
    exact Runs.more hs (ih d t₂ z hy h₂)

lemma runs_trans {c d : Config} {t₁ t₂ : ℕ} {z : Option Config} (h₁ : Runs c t₁ (some d))
    (h₂ : Runs d t₂ z) : Runs c (t₁ + t₂) z :=
  runs_trans_aux h₁ d t₂ z rfl h₂

lemma runs_one {c d : Config} (h : step c = some d) : Runs c 1 (some d) := h ▸ Runs.one c

/-- Walking inward in state A over `j ≥ 1` blank cells. -/
lemma walk (j : ℕ) : ∀ (L : List Bool) (x : ℕ),
    Runs ⟨false, L, 2 ^ (j + 1) * x⟩ (j + 1) (some ⟨false, List.replicate (j + 1) false ++ L, x⟩) := by
  induction j with
  | zero =>
    intro L x
    apply runs_one
    simp [step, Nat.mul_mod_right]
  | succ j ih =>
    intro L x
    have h1 : step ⟨false, L, 2 ^ (j + 1 + 1) * x⟩ = some ⟨false, false :: L, 2 ^ (j + 1) * x⟩ := by
      rw [show 2 ^ (j + 1 + 1) * x = 2 * (2 ^ (j + 1) * x) by ring]
      simp [step, Nat.mul_mod_right]
    have := runs_trans (runs_one h1) (ih (false :: L) x)
    rw [show 1 + (j + 1) = j + 1 + 1 by omega] at this
    simpa [List.replicate_succ'] using this

def h : ℕ → ℕ
  | 0 => 0
  | j + 1 => 2 * h j + j + 3

lemma count (j : ℕ) : ∀ (L : List Bool) (R : ℕ),
    Runs ⟨false, List.replicate j false ++ L, 1 + 2 * R⟩ (h j + 1) (outward (2 ^ j * (1 + 2 * R)) L) := by
  induction j with
  | zero =>
    intro L R
    have : step ⟨false, L, 1 + 2 * R⟩ = outward (1 + 2 * R) L := by
      simp [step, Nat.add_mod]
    simp only [h, List.replicate_zero, List.nil_append, pow_zero, one_mul, zero_add]
    rw [← this]; exact Runs.one _
  | succ j ih =>
    intro L R
    set X := 2 ^ j * (1 + 2 * R) with hX
    -- first inner count, with `false :: L` below the block
    have e1 := ih (false :: L) R
    rw [← hX] at e1
    have o1 : outward X (false :: L) = some ⟨true, L, 2 * X⟩ := by simp [outward]
    rw [o1] at e1
    have l1 : List.replicate j false ++ false :: L = List.replicate (j + 1) false ++ L := by
      simp [List.replicate_succ']
    rw [l1] at e1
    -- write 1 at the bottom cell, move inward
    have s2 : step ⟨true, L, 2 * X⟩ = some ⟨false, true :: L, X⟩ := by
      simp [step, Nat.mul_mod_right]
    -- the second inner count, with `true :: L` below the block
    have e3 := ih (true :: L) R
    rw [← hX] at e3
    have o3 : outward X (true :: L) = some ⟨true, L, 2 * X + 1⟩ := by simp [outward]
    rw [o3] at e3
    have s4 : step ⟨true, L, 2 * X + 1⟩ = outward (2 ^ (j + 1) * (1 + 2 * R)) L := by
      simp only [step]
      rw [if_neg (by omega)]
      simp only [if_true, Nat.add_sub_cancel]
      rw [hX, pow_succ]; congr 1; ring
    -- assemble (the walk is empty when j = 0)
    have tail : Runs ⟨true, L, 2 * X + 1⟩ 1 (outward (2 ^ (j + 1) * (1 + 2 * R)) L) := by
      rw [← s4]; exact Runs.one _
    rcases j with _ | j
    · simp only [List.replicate_zero, List.nil_append, h, zero_add] at e3
      rw [show 1 + 2 * R = X by simp [hX]] at e3
      have := runs_trans e1 (runs_trans (runs_one s2) (runs_trans e3 tail))
      simpa [h] using this
    · have hw := walk j (true :: L) (1 + 2 * R)
      have hX' : X = 2 ^ (j + 1) * (1 + 2 * R) := hX
      rw [← hX'] at hw
      have := runs_trans e1 (runs_trans (runs_one s2) (runs_trans hw (runs_trans e3 tail)))
      have hh : h (j + 1 + 1) + 1 = h (j + 1) + 1 + (1 + (j + 1 + (h (j + 1) + 1 + 1))) := by
        simp only [h]; ring
      rw [hh]; simpa using this

lemma h_eq (j : ℕ) : h j + j + 4 = 2 ^ (j + 2) := by
  induction j with
  | zero => simp [h]
  | succ j ih => simp only [h, pow_succ] at ih ⊢; omega

lemma halt (e k : ℕ) (hk : Odd k) : Runs ⟨false, [], 2 ^ e * k⟩ (h e + 1 + e) none := by
  obtain ⟨R, rfl⟩ := hk
  have hc := count e [] R
  rw [show 2 * R + 1 = 1 + 2 * R by ring]
  have o : outward (2 ^ e * (1 + 2 * R)) [] = none := rfl
  rw [o] at hc
  rcases e with _ | e
  · simpa using hc
  · have hw := walk e [] (1 + 2 * R)
    simp only [List.append_nil] at hw hc
    have := runs_trans hw hc
    rw [show h (e + 1) + 1 + (e + 1) = e + 1 + (h (e + 1) + 1) by ring]
    exact this

/-- `c ↦ (-1)^(c+1)` as an arithmetic function. -/
def sgn : ArithmeticFunction ℤ := ⟨fun c => if c = 0 then 0 else (-1) ^ (c + 1), by simp⟩

lemma sgn_apply {c : ℕ} (hc : c ≠ 0) : sgn c = (-1) ^ (c + 1) := by
  simp [sgn, hc]

lemma sgn_mult : sgn.IsMultiplicative := by
  refine ⟨by simp [sgn], fun {m n} hmn => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [sgn]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sgn]
  rw [sgn_apply (by positivity), sgn_apply (by omega), sgn_apply (by omega)]
  rcases Nat.even_or_odd m with h1 | h1 <;> rcases Nat.even_or_odd n with h2 | h2
  · exfalso
    have h1' := even_iff_two_dvd.mp h1
    have h2' := even_iff_two_dvd.mp h2
    have := Nat.dvd_gcd h1' h2'
    rw [hmn] at this
    omega
  · rw [(h1.mul_right n).add_one.neg_one_pow, h1.add_one.neg_one_pow, h2.add_one.neg_one_pow]; simp
  · rw [(h2.mul_left m).add_one.neg_one_pow, h1.add_one.neg_one_pow, h2.add_one.neg_one_pow]; simp
  · rw [(h1.mul h2).add_one.neg_one_pow, h1.add_one.neg_one_pow, h2.add_one.neg_one_pow]; simp

/-- `A069517` as an arithmetic function. -/
def A : ArithmeticFunction ℤ := sgn.pmul μ * (ζ : ArithmeticFunction ℤ)

lemma A_apply (d : ℕ) : A d = m d := by
  rw [A, coe_mul_zeta_apply, m]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [pmul_apply, sgn_apply (Nat.ne_of_gt (Nat.pos_of_mem_divisors hc))]

lemma A_mult : A.IsMultiplicative :=
  (sgn_mult.pmul isMultiplicative_moebius).mul isMultiplicative_zeta.natCast

/-- The summand `a(d)^2 φ(d)`. -/
def F : ArithmeticFunction ℤ := ⟨fun d => A d ^ 2 * (d.totient : ℤ), by simp⟩

lemma F_apply (d : ℕ) : F d = A d ^ 2 * (d.totient : ℤ) := rfl

lemma F_mult : F.IsMultiplicative := by
  refine ⟨by simp [F_apply, A_mult.map_one], fun {m n} hmn => ?_⟩
  simp only [F_apply, A_mult.map_mul_of_coprime hmn, Nat.totient_mul hmn]
  push_cast; ring

def S : ArithmeticFunction ℤ := F * (ζ : ArithmeticFunction ℤ)

lemma S_mult : S.IsMultiplicative := F_mult.mul isMultiplicative_zeta.natCast

lemma A_prime_pow {p : ℕ} (hp : p.Prime) (x : ℕ) (hx : 1 ≤ x) : A (p ^ x) = 1 + sgn p * -1 := by
  rw [A, coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
  induction x with
  | zero => omega
  | succ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx'
    · rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, pmul_apply, pmul_apply,
        moebius_apply_prime hp, sgn_apply one_ne_zero]
      simp
    · rw [Finset.sum_range_succ, ih hx', pmul_apply, moebius_apply_prime_pow hp (by omega),
        if_neg (by omega)]
      ring

lemma S_odd_prime_pow {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (i : ℕ) : S (p ^ i) = 1 := by
  rw [S, coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
  induction i with
  | zero => simp [F_apply, A_mult.map_one]
  | succ i ih =>
    rw [Finset.sum_range_succ, ih, F_apply, A_prime_pow hp _ (by omega),
      sgn_apply hp.ne_zero, (hp.odd_of_ne_two h2).add_one.neg_one_pow]
    simp

lemma S_odd {k : ℕ} (hk : Odd k) : S k = 1 := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  rw [S_mult.multiplicative_factorization _ hk0]
  apply Finset.prod_eq_one
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization k ▸ hp)
  have hpd : p ∣ k := Nat.dvd_of_mem_primeFactors (Nat.support_factorization k ▸ hp)
  apply S_odd_prime_pow hpp
  rintro rfl
  exact (Nat.not_even_iff_odd.mpr hk) (even_iff_two_dvd.mpr hpd)

lemma S_two_pow (e : ℕ) : S (2 ^ e) + 3 = 2 ^ (e + 2) := by
  rw [S, coe_mul_zeta_apply, Nat.sum_divisors_prime_pow Nat.prime_two]
  induction e with
  | zero => simp [F_apply, A_mult.map_one]
  | succ e ih =>
    rw [Finset.sum_range_succ, F_apply, A_prime_pow Nat.prime_two _ (by omega),
      sgn_apply (by norm_num), Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp only [Nat.add_sub_cancel]
    push_cast
    norm_num
    linear_combination ih

lemma sum_eq (e k : ℕ) (hk : Odd k) :
    ∑ d ∈ (2 ^ e * k).divisors, (m d) ^ 2 * (Nat.totient d : ℤ) + 3 = 2 ^ (e + 2) := by
  have hc : Nat.Coprime (2 ^ e) k := (Nat.coprime_two_left.mpr hk).pow_left e
  have : ∑ d ∈ (2 ^ e * k).divisors, (m d) ^ 2 * (Nat.totient d : ℤ) = S (2 ^ e * k) := by
    rw [S, coe_mul_zeta_apply]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [F_apply, A_apply]
  rw [this, S_mult.map_mul_of_coprime hc, S_odd hk, mul_one, S_two_pow]

theorem solution_main : ∀ n : ℕ, 0 < n → ∃ t : ℕ,
    Runs ⟨false, [], n⟩ t none ∧
    (t : ℤ) = ∑ d ∈ n.divisors, (m d)^2 * (Nat.totient d : ℤ) := by
  intro n hn
  obtain ⟨e, k, hk, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (n := n) (by omega)
  refine ⟨h e + 1 + e, halt e k hk, ?_⟩
  have h1 := sum_eq e k hk
  have h2 : ((h e + e + 4 : ℕ) : ℤ) = ((2 ^ (e + 2) : ℕ) : ℤ) := congrArg _ (h_eq e)
  push_cast at h1 h2 ⊢
  linarith

end OMA.A393210

theorem OMA.solution : type_of% @OMA.S_oeis_a393210.main := OMA.A393210.solution_main
