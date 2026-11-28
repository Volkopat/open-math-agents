import FormalConjectures.Wikipedia.Mills

-- FULL THEOREM PROOF: mathematical subproofs reused verbatim from previously merged bank.

-- VERIFIED REDUCTION Mills.lower_bound_of_RH.R1

-- Reduction Mills.lower_bound_of_RH.R1 of Mills' constant lower bound
-- Credit: @senamakel
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- RH is already a premise of the target, so the hypotheses are the two explicit prime-counting
-- inputs that turn RH into primes between consecutive cubes.
--
-- H1: under RH, the explicit Chebyshev bound |psi(x) - x| < (1/8) sqrt(x) log(x)^2 for x >= 73.2
--     (Schoenfeld 1976, Theorem 10, has the constant 1/(8 pi); 1/8 is a weaker constant).
-- H2: unconditionally, psi(x) - theta(x) <= (1/8) sqrt(x) log(x)^2 for x >= 599
--     (from Costa Pereira's psi(x) - theta(x) <= psi(x^(1/2)) + psi(x^(1/3)) + psi(x^(1/5)),
--     in Mathlib, and Mathlib's psi(y) <= log 4 * y + 2 sqrt(y) log y).
--
-- main proves everything else:
-- 1. H1 and H2 give |theta(x) - x| < (1/4) sqrt(x) log(x)^2 for x >= 599.
-- 2. With a = x^3 and b = x^3 + 3x^2 + 3x, theta(b) > theta(a) once 3x^2 + 3x exceeds
--    (1/2) sqrt(b) log(b)^2, which holds for x >= 10^9: a prime lies strictly between x^3 and
--    (x+1)^3 for every x >= 10^9 (Caldwell and Cheng 2005 use Schoenfeld for x >= 2657).
-- 3. The greedy sequence g 0 = 2, g (n+1) = least prime >= (g n)^3 starts 2, 11, 1361,
--    2521008887 (primality of 2521008887 by a Lucas certificate, no native_decide). Every Mills
--    number A > 1 has g n <= floor(A^(3^(n+1))), so A^81 >= 2521008887 and A > 1.3063778838.
-- 4. Primes between cubes from g 3 = 2521008887 >= 10^9 on give g (n+1) + 1 < (g n + 1)^3, so
--    the limit of g(n)^(1/3^(n+1)) is a Mills number with A^81 <= 2521008888, hence the least
--    Mills number is < 1.3063778839.

namespace OMA.R_Mills_lower_bound_of_RH_R1

open Mills Chebyshev Real

/-- Under RH, `|ψ(x) − x| < √x log² x / 8` for `x ≥ 73.2`. -/
def H1 : Prop :=
  RiemannHypothesis → ∀ x : ℝ, 73.2 ≤ x →
    |Chebyshev.psi x - x| < 1 / 8 * (Real.sqrt x * Real.log x ^ 2)

/-- Unconditionally, `ψ(x) − θ(x) ≤ √x log² x / 8` for `x ≥ 599`. -/
def H2 : Prop :=
  ∀ x : ℝ, 599 ≤ x →
    Chebyshev.psi x - Chebyshev.theta x ≤ 1 / 8 * (Real.sqrt x * Real.log x ^ 2)

/-! ### Step 1: the θ bound -/

theorem theta_sub_lt_quarter (h1 : H1) (h2 : H2) (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 599 ≤ x) : |θ x - x| < 1 / 4 * (√x * Real.log x ^ 2) := by
  have hψ := h1 hRH x (by linarith)
  have hle := theta_le_psi x
  have hd := h2 x hx
  rw [abs_lt] at hψ ⊢
  constructor <;> linarith [hψ.1, hψ.2]

/-! ### Step 2: primes between consecutive cubes -/

/-- A strict increase of `θ` over `(a, b]` produces a prime there. -/
lemma exists_prime_of_theta_lt {a b : ℕ} (h : θ (a : ℝ) < θ (b : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ a < p ∧ p ≤ b := by
  by_contra hne
  push Not at hne
  refine absurd h (not_lt.mpr ?_)
  unfold Chebyshev.theta
  simp only [Nat.floor_natCast]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    obtain ⟨⟨h0, hpb⟩, hpp⟩ := hp
    refine ⟨⟨h0, ?_⟩, hpp⟩
    by_contra hlt
    push Not at hlt
    exact absurd hpb (not_le.mpr (hne p hpp hlt))
  · intro p hp _
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    exact Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)

lemma root_pow (x : ℝ) (hx : 0 ≤ x) (m : ℕ) (hm : m ≠ 0) : (x ^ ((1 : ℝ) / m)) ^ m = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  have : (1 : ℝ) / m * m = 1 := by field_simp
  rw [this, Real.rpow_one]

lemma cubes_inequality (X : ℝ) (hX : (10 : ℝ) ^ 9 ≤ X) :
    1 / 2 * (√(X ^ 3 + 3 * X ^ 2 + 3 * X) * Real.log (X ^ 3 + 3 * X ^ 2 + 3 * X) ^ 2)
      < 3 * X ^ 2 + 3 * X := by
  have hX0 : 0 < X := by linarith
  set b := X ^ 3 + 3 * X ^ 2 + 3 * X with hb
  have hu : 0 < X + 1 := by linarith
  set t : ℝ := (X + 1) ^ ((1 : ℝ) / ((8 : ℕ) : ℝ)) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hu _
  have ht8 : t ^ 8 = X + 1 := root_pow _ hu.le 8 (by norm_num)
  have ht13 : 13 ≤ t := by
    by_contra hlt
    push Not at hlt
    have : t ^ 8 < 13 ^ 8 := pow_lt_pow_left₀ hlt ht0.le (by norm_num)
    norm_num at this
    nlinarith
  have hbpos : 1 ≤ b := by rw [hb]; nlinarith
  have hbu : b ≤ (X + 1) ^ 3 := by rw [hb]; nlinarith
  have hu3 : (X + 1) ^ 3 = (t ^ 12) ^ 2 := by rw [← ht8]; ring
  have hsq : √b ≤ t ^ 12 := by
    calc √b ≤ √((t ^ 12) ^ 2) := Real.sqrt_le_sqrt (hu3 ▸ hbu)
      _ = t ^ 12 := Real.sqrt_sq (by positivity)
  have hlog : Real.log b ≤ 24 * t := by
    calc Real.log b ≤ Real.log ((X + 1) ^ 3) := Real.log_le_log (by linarith) hbu
      _ = 24 * Real.log t := by rw [Real.log_pow, ← ht8, Real.log_pow]; push_cast; ring
      _ ≤ 24 * t := by
        have := Real.log_le_sub_one_of_pos ht0
        linarith
  have hlog0 : 0 ≤ Real.log b := Real.log_nonneg hbpos
  have hK : √b * Real.log b ^ 2 ≤ t ^ 12 * (24 * t) ^ 2 :=
    mul_le_mul hsq (pow_le_pow_left₀ hlog0 hlog 2) (by positivity) (by positivity)
  have hX8 : X = t ^ 8 - 1 := by linarith
  have h100 : 100 ≤ t ^ 8 := by
    have : (13 : ℝ) ^ 8 ≤ t ^ 8 := pow_le_pow_left₀ (by norm_num) ht13 8
    norm_num at this; linarith
  have h169 : 169 * t ^ 14 ≤ t ^ 16 := by
    have : (169 : ℝ) ≤ t ^ 2 := by nlinarith
    calc 169 * t ^ 14 ≤ t ^ 2 * t ^ 14 := mul_le_mul_of_nonneg_right this (by positivity)
      _ = t ^ 16 := by ring
  have hX2 : (99 / 100 * t ^ 8) ^ 2 ≤ X ^ 2 := by
    apply pow_le_pow_left₀ (by positivity); rw [hX8]; linarith
  have h16 : (t ^ 8) ^ 2 = t ^ 16 := by ring
  have h14 : 0 < t ^ 14 := by positivity
  nlinarith [mul_pos h14 (by norm_num : (0:ℝ) < 1)]

/-- Under H1, H2 and RH: a prime strictly between `x³` and `(x+1)³` for every `x ≥ 10^9`. -/
theorem primeBetweenCubes (h1 : H1) (h2 : H2) (hRH : RiemannHypothesis) :
    ∀ x : ℕ, 10 ^ 9 ≤ x → ∃ p : ℕ, p.Prime ∧ x ^ 3 < p ∧ p < (x + 1) ^ 3 := by
  intro x hx
  have hX : (10 : ℝ) ^ 9 ≤ (x : ℝ) := by exact_mod_cast hx
  set A : ℕ := x ^ 3 with hA
  set B : ℕ := x ^ 3 + 3 * x ^ 2 + 3 * x with hB
  have hAr : (A : ℝ) = (x : ℝ) ^ 3 := by simp [hA]
  have hBr : (B : ℝ) = (x : ℝ) ^ 3 + 3 * (x : ℝ) ^ 2 + 3 * x := by simp [hB]
  have hx0 : (0 : ℝ) < x := by linarith
  have hA599 : (599 : ℝ) ≤ A := by
    rw [hAr]; nlinarith [mul_pos hx0 hx0]
  have hAB : (A : ℝ) ≤ B := by rw [hAr, hBr]; nlinarith [mul_pos hx0 hx0]
  have hA1 := theta_sub_lt_quarter h1 h2 hRH hA599
  have hB1 := theta_sub_lt_quarter h1 h2 hRH (le_trans hA599 hAB)
  have hlogA : 0 ≤ Real.log (A : ℝ) := Real.log_nonneg (by linarith)
  have hmono : √(A : ℝ) * Real.log (A : ℝ) ^ 2 ≤ √(B : ℝ) * Real.log (B : ℝ) ^ 2 :=
    mul_le_mul (Real.sqrt_le_sqrt hAB)
      (pow_le_pow_left₀ hlogA (Real.log_le_log (by linarith) hAB) 2) (by positivity)
      (Real.sqrt_nonneg _)
  have hkey := cubes_inequality (x : ℝ) hX
  rw [← hBr] at hkey
  rw [abs_lt] at hA1 hB1
  have hlt : θ (A : ℝ) < θ (B : ℝ) := by
    have : (B : ℝ) - A = 3 * (x : ℝ) ^ 2 + 3 * x := by rw [hAr, hBr]; ring
    nlinarith [hA1.1, hA1.2, hB1.1, hB1.2]
  obtain ⟨p, hp, hp1, hp2⟩ := exists_prime_of_theta_lt hlt
  refine ⟨p, hp, hp1, ?_⟩
  have : (x + 1) ^ 3 = B + 1 := by simp only [hB]; ring
  omega

/-! ### Step 3: the greedy sequence and the lower bound (no hypothesis)

A greedy sequence is any `g : ℕ → ℕ` with `g 0 = 2` such that `g (n+1)` is the least prime
`≥ (g n)^3`; the property is passed around as `hg`. -/

lemma exists_prime_ge (x : ℕ) : ∃ p, p.Prime ∧ x ≤ p := by
  obtain ⟨p, hp, hq⟩ := Nat.exists_infinite_primes x
  exact ⟨p, hq, hp⟩

lemma least_prime_eq {x p q : ℕ} (hq : q.Prime) (hxq : x ^ 3 ≤ q)
    (hmin : ∀ r, r.Prime → x ^ 3 ≤ r → q ≤ r) (hp : p.Prime) (h : x ^ 3 ≤ p)
    (hgap : ∀ r, x ^ 3 ≤ r → r < p → ¬ r.Prime) : q = p := by
  refine le_antisymm (hmin p hp h) ?_
  by_contra hlt
  exact hgap _ hxq (not_le.mp hlt) hq

/-- A Pratt/Lucas primality certificate: `5` is a primitive root mod `2521008887`, and
`2521008886 = 2 · 11 · 23 · 4982231` with `4982231` prime. -/
lemma prime_2521008887 : Nat.Prime 2521008887 := by
  have hp4 : Nat.Prime 4982231 := by norm_num
  have hfac : (2521008887 - 1 : ℕ) = 2 * 11 * 23 * 4982231 := by norm_num
  apply lucas_primality 2521008887 (5 : ZMod 2521008887)
  · show (5 : ZMod 2521008887) ^ 2521008886 = 1
    reduce_mod_char
  · intro q hq hdvd
    rw [hfac] at hdvd
    have key : q = 2 ∨ q = 11 ∨ q = 23 ∨ q = 4982231 := by
      rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
      · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
          · left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          · right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        · right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      · right; right; right; exact (Nat.prime_dvd_prime_iff_eq hq hp4).mp h
    rcases key with rfl | rfl | rfl | rfl
    · show (5 : ZMod 2521008887) ^ 1260504443 ≠ 1
      reduce_mod_char; decide
    · show (5 : ZMod 2521008887) ^ 229182626 ≠ 1
      reduce_mod_char; decide
    · show (5 : ZMod 2521008887) ^ 109609082 ≠ 1
      reduce_mod_char; decide
    · show (5 : ZMod 2521008887) ^ 506 ≠ 1
      reduce_mod_char; decide

section Greedy

variable {g : ℕ → ℕ}

lemma g_one (hg : g 0 = 2 ∧ ∀ n, (g (n + 1)).Prime ∧ g n ^ 3 ≤ g (n + 1) ∧
      ∀ p, p.Prime → g n ^ 3 ≤ p → g (n + 1) ≤ p) : g 1 = 11 := by
  obtain ⟨h0, hs⟩ := hg
  obtain ⟨hp, hc, hm⟩ := hs 0
  rw [h0] at hc hm
  refine least_prime_eq hp hc hm (by norm_num) (by norm_num) ?_
  intro q h1 h2
  have h1' : 8 ≤ q := by norm_num at h1; exact h1
  interval_cases q <;> norm_num

lemma g_two (hg : g 0 = 2 ∧ ∀ n, (g (n + 1)).Prime ∧ g n ^ 3 ≤ g (n + 1) ∧
      ∀ p, p.Prime → g n ^ 3 ≤ p → g (n + 1) ≤ p) : g 2 = 1361 := by
  have e1 := g_one hg
  obtain ⟨hp, hc, hm⟩ := hg.2 1
  rw [e1] at hc hm
  refine least_prime_eq hp hc hm (by norm_num) (by norm_num) ?_
  intro q h1 h2
  have h1' : 1331 ≤ q := by norm_num at h1; exact h1
  interval_cases q <;> norm_num

lemma g_three (hg : g 0 = 2 ∧ ∀ n, (g (n + 1)).Prime ∧ g n ^ 3 ≤ g (n + 1) ∧
      ∀ p, p.Prime → g n ^ 3 ≤ p → g (n + 1) ≤ p) : g 3 = 2521008887 := by
  have e2 := g_two hg
  obtain ⟨hp, hc, hm⟩ := hg.2 2
  rw [e2] at hc hm
  refine least_prime_eq hp hc hm prime_2521008887 (by norm_num) ?_
  intro q h1 h2
  have h1' : 2521008881 ≤ q := by norm_num at h1; exact h1
  interval_cases q <;> norm_num

lemma g_prime (hg : g 0 = 2 ∧ ∀ n, (g (n + 1)).Prime ∧ g n ^ 3 ≤ g (n + 1) ∧
      ∀ p, p.Prime → g n ^ 3 ≤ p → g (n + 1) ≤ p) (n : ℕ) : (g n).Prime := by
  cases n with
  | zero => rw [hg.1]; exact Nat.prime_two
  | succ n => exact (hg.2 n).1

lemma g_mono (hg : g 0 = 2 ∧ ∀ n, (g (n + 1)).Prime ∧ g n ^ 3 ≤ g (n + 1) ∧
      ∀ p, p.Prime → g n ^ 3 ≤ p → g (n + 1) ≤ p) : Monotone g := by
  refine monotone_nat_of_le_succ fun n => ?_
  have := (hg.2 n).2.1
  calc g n ≤ g n ^ 3 := Nat.le_self_pow (by norm_num) _
    _ ≤ _ := this

/-- Any Mills number `A > 1` has `g n ≤ ⌊A^(3^(n+1))⌋₊`: the greedy sequence is minimal. -/
theorem g_le_floor (hg : g 0 = 2 ∧ ∀ n, (g (n + 1)).Prime ∧ g n ^ 3 ≤ g (n + 1) ∧
      ∀ p, p.Prime → g n ^ 3 ≤ p → g (n + 1) ≤ p) {A : ℝ} (hA : 1 < A) (hM : IsMills A)
    (n : ℕ) : g n ≤ ⌊A ^ 3 ^ (n + 1)⌋₊ := by
  have hA0 : 0 ≤ A := by linarith
  have hprime : ∀ n : ℕ, (⌊A ^ 3 ^ (n + 1)⌋₊).Prime :=
    fun n => Nat.prime_iff.mpr (hM n.succPNat)
  induction n with
  | zero => rw [hg.1]; exact (hprime 0).two_le
  | succ n ih =>
    have hq : ⌊A ^ 3 ^ (n + 1)⌋₊ ^ 3 ≤ ⌊A ^ 3 ^ (n + 1 + 1)⌋₊ := by
      apply Nat.le_floor
      push_cast
      have h1 : ((⌊A ^ 3 ^ (n + 1)⌋₊ : ℕ) : ℝ) ≤ A ^ 3 ^ (n + 1) := Nat.floor_le (by positivity)
      calc ((⌊A ^ 3 ^ (n + 1)⌋₊ : ℕ) : ℝ) ^ 3 ≤ (A ^ 3 ^ (n + 1)) ^ 3 :=
            pow_le_pow_left₀ (by positivity) h1 3
        _ = A ^ 3 ^ (n + 1 + 1) := by rw [← pow_mul, ← pow_succ]
    exact (hg.2 n).2.2 _ (hprime (n + 1)) (le_trans (Nat.pow_le_pow_left ih 3) hq)

/-- **Lower bound, no hypotheses**: every Mills number `A > 1` exceeds `1.3063778838`. -/
theorem lower_bound (hg : g 0 = 2 ∧ ∀ n, (g (n + 1)).Prime ∧ g n ^ 3 ≤ g (n + 1) ∧
      ∀ p, p.Prime → g n ^ 3 ≤ p → g (n + 1) ≤ p) {A : ℝ} (hA : 1 < A) (hM : IsMills A) :
    (1.3063778838 : ℝ) < A := by
  have h := le_trans (Nat.cast_le.mpr (g_le_floor hg hA hM 3))
    (Nat.floor_le (by positivity : (0 : ℝ) ≤ A ^ 3 ^ (3 + 1)))
  rw [g_three hg] at h
  norm_num at h
  by_contra hle
  push Not at hle
  have : A ^ 81 ≤ (1.3063778838 : ℝ) ^ 81 := pow_le_pow_left₀ (by linarith) hle 81
  have h2 : (1.3063778838 : ℝ) ^ 81 < 2521008887 := by norm_num
  linarith

/-! ### Step 4: the greedy limit is a Mills number below `1.3063778839` -/

/-- The strict step: `g (n+1) + 1 < (g n + 1)^3`, given primes between cubes from `x₀` on. -/
theorem g_succ_add_one_lt (hg : g 0 = 2 ∧ ∀ n, (g (n + 1)).Prime ∧ g n ^ 3 ≤ g (n + 1) ∧
      ∀ p, p.Prime → g n ^ 3 ≤ p → g (n + 1) ≤ p) {x₀ : ℕ}
    (h : ∀ x : ℕ, x₀ ≤ x → ∃ p : ℕ, p.Prime ∧ x ^ 3 < p ∧ p < (x + 1) ^ 3)
    (hx : x₀ ≤ 2521008887) (n : ℕ) : g (n + 1) + 1 < (g n + 1) ^ 3 := by
  have hlt : g (n + 1) < (g n + 1) ^ 3 := by
    by_cases hn : 3 ≤ n
    · have h3 : x₀ ≤ g n := le_trans hx (by rw [← g_three hg]; exact g_mono hg hn)
      obtain ⟨p, hp, hp1, hp2⟩ := h (g n) h3
      exact lt_of_le_of_lt ((hg.2 n).2.2 p hp hp1.le) hp2
    · interval_cases n
      · rw [g_one hg, hg.1]; norm_num
      · rw [g_two hg, g_one hg]; norm_num
      · rw [g_three hg, g_two hg]; norm_num
  have hne : g (n + 1) + 1 ≠ (g n + 1) ^ 3 := by
    intro heq
    have hfac : g (n + 1) = g n * (g n ^ 2 + 3 * g n + 3) := by
      have : g (n + 1) + 1 = g n * (g n ^ 2 + 3 * g n + 3) + 1 := by rw [heq]; ring
      omega
    have hp := g_prime hg (n + 1)
    rw [hfac, Nat.prime_mul_iff] at hp
    have h2 := (g_prime hg n).two_le
    rcases hp with ⟨_, h1⟩ | ⟨_, h1⟩
    · nlinarith
    · omega
  omega

/-- The greedy limit `L = sup_n (g n)^(1/3^(n+1))` is a Mills number with `L^81 ≤ 2521008888`. -/
theorem exists_mills_lt (hg : g 0 = 2 ∧ ∀ n, (g (n + 1)).Prime ∧ g n ^ 3 ≤ g (n + 1) ∧
      ∀ p, p.Prime → g n ^ 3 ≤ p → g (n + 1) ≤ p) {x₀ : ℕ}
    (h : ∀ x : ℕ, x₀ ≤ x → ∃ p : ℕ, p.Prime ∧ x ^ 3 < p ∧ p < (x + 1) ^ 3)
    (hx : x₀ ≤ 2521008887) :
    ∃ A : ℝ, A > 1 ∧ IsMills A ∧ A < 1.3063778839 := by
  -- the lower and upper roots
  have hpos : ∀ n, (0 : ℝ) < g n := fun n => by exact_mod_cast (g_prime hg n).pos
  have lo_pos : ∀ n, 0 < (g n : ℝ) ^ ((1 : ℝ) / ((3 ^ (n + 1) : ℕ) : ℝ)) :=
    fun n => Real.rpow_pos_of_pos (hpos n) _
  have hi_pos : ∀ n, 0 < ((g n : ℝ) + 1) ^ ((1 : ℝ) / ((3 ^ (n + 1) : ℕ) : ℝ)) :=
    fun n => Real.rpow_pos_of_pos (by linarith [hpos n]) _
  have lo_pow : ∀ n, ((g n : ℝ) ^ ((1 : ℝ) / ((3 ^ (n + 1) : ℕ) : ℝ))) ^ 3 ^ (n + 1) = g n :=
    fun n => by
      have := root_pow (g n : ℝ) (hpos n).le (3 ^ (n + 1)) (by positivity)
      exact_mod_cast this
  have hi_pow : ∀ n, (((g n : ℝ) + 1) ^ ((1 : ℝ) / ((3 ^ (n + 1) : ℕ) : ℝ))) ^ 3 ^ (n + 1)
      = (g n : ℝ) + 1 :=
    fun n => by
      have := root_pow ((g n : ℝ) + 1) (by linarith [hpos n]) (3 ^ (n + 1)) (by positivity)
      exact_mod_cast this
  set lo : ℕ → ℝ := fun n => (g n : ℝ) ^ ((1 : ℝ) / ((3 ^ (n + 1) : ℕ) : ℝ)) with hlo
  set hi : ℕ → ℝ := fun n => ((g n : ℝ) + 1) ^ ((1 : ℝ) / ((3 ^ (n + 1) : ℕ) : ℝ)) with hhi
  have lo_le_hi : ∀ n, lo n ≤ hi n := fun n => by
    refine (pow_le_pow_iff_left₀ (lo_pos n).le (hi_pos n).le
      (by positivity : 3 ^ (n + 1) ≠ 0)).mp ?_
    rw [lo_pow, hi_pow]; linarith
  have lo_mono : Monotone lo := by
    refine monotone_nat_of_le_succ fun n => ?_
    refine (pow_le_pow_iff_left₀ (lo_pos n).le (lo_pos (n + 1)).le
      (by positivity : 3 ^ (n + 2) ≠ 0)).mp ?_
    have e1 : lo n ^ 3 ^ (n + 2) = (g n : ℝ) ^ 3 := by
      show ((g n : ℝ) ^ ((1 : ℝ) / ((3 ^ (n + 1) : ℕ) : ℝ))) ^ 3 ^ (n + 2) = _
      rw [pow_succ 3 (n + 1), pow_mul, lo_pow]
    have e2 : lo (n + 1) ^ 3 ^ (n + 2) = (g (n + 1) : ℝ) := lo_pow (n + 1)
    show lo n ^ 3 ^ (n + 2) ≤ lo (n + 1) ^ 3 ^ (n + 2)
    rw [e1, e2]
    exact_mod_cast (hg.2 n).2.1
  have hi_anti : Antitone hi := by
    refine antitone_nat_of_succ_le fun n => ?_
    refine (pow_le_pow_iff_left₀ (hi_pos (n + 1)).le (hi_pos n).le
      (by positivity : 3 ^ (n + 2) ≠ 0)).mp ?_
    have e1 : hi n ^ 3 ^ (n + 2) = ((g n : ℝ) + 1) ^ 3 := by
      show (((g n : ℝ) + 1) ^ ((1 : ℝ) / ((3 ^ (n + 1) : ℕ) : ℝ))) ^ 3 ^ (n + 2) = _
      rw [pow_succ 3 (n + 1), pow_mul, hi_pow]
    have e2 : hi (n + 1) ^ 3 ^ (n + 2) = (g (n + 1) : ℝ) + 1 := hi_pow (n + 1)
    show hi (n + 1) ^ 3 ^ (n + 2) ≤ hi n ^ 3 ^ (n + 2)
    rw [e1, e2]
    have := g_succ_add_one_lt hg h hx n
    have h2 : ((g (n + 1) : ℝ) + 1) < ((g n : ℝ) + 1) ^ 3 := by exact_mod_cast this
    exact h2.le
  have lo_le_hi' : ∀ n m, lo n ≤ hi m := fun n m =>
    calc lo n ≤ lo (max n m) := lo_mono (le_max_left _ _)
      _ ≤ hi (max n m) := lo_le_hi _
      _ ≤ hi m := hi_anti (le_max_right _ _)
  set L : ℝ := ⨆ n, lo n with hL
  have lo_le_L : ∀ n, lo n ≤ L := fun n =>
    le_ciSup ⟨hi 0, by rintro _ ⟨m, rfl⟩; exact lo_le_hi' m 0⟩ n
  have L_le_hi : ∀ m, L ≤ hi m := fun m => ciSup_le fun n => lo_le_hi' n m
  have L0 : 0 ≤ L := le_trans (lo_pos 0).le (lo_le_L 0)
  have hfloor : ∀ k, ⌊L ^ 3 ^ (k + 1)⌋₊ = g k := fun k => by
    rw [Nat.floor_eq_iff (pow_nonneg L0 _)]
    constructor
    · calc (g k : ℝ) = lo k ^ 3 ^ (k + 1) := (lo_pow k).symm
        _ ≤ _ := pow_le_pow_left₀ (lo_pos k).le (lo_le_L k) _
    · have h1 : L ^ 3 ^ (k + 1) ≤ hi (k + 1) ^ 3 ^ (k + 1) :=
        pow_le_pow_left₀ L0 (L_le_hi (k + 1)) _
      have h2 : (hi (k + 1) ^ 3 ^ (k + 1)) ^ 3 < ((g k : ℝ) + 1) ^ 3 := by
        rw [← pow_mul, ← pow_succ, hi_pow]
        have := g_succ_add_one_lt hg h hx k
        exact_mod_cast this
      have h3 : hi (k + 1) ^ 3 ^ (k + 1) < (g k : ℝ) + 1 :=
        lt_of_pow_lt_pow_left₀ 3 (by positivity) h2
      linarith
  have hL1 : 1 < L := by
    have h1 : 1 < lo 0 := by
      by_contra hle
      push Not at hle
      have : lo 0 ^ 3 ^ (0 + 1) ≤ 1 := pow_le_one₀ (lo_pos 0).le hle
      rw [lo_pow, hg.1] at this
      norm_num at this
    linarith [lo_le_L 0]
  have hMills : IsMills L := by
    intro n
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (n : ℕ) = k + 1 := ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
    rw [hk, hfloor k]
    exact Nat.prime_iff.mp (g_prime hg k)
  have hL81 : L ^ 81 ≤ 2521008888 := by
    have h1 : L ^ 3 ^ (3 + 1) ≤ hi 3 ^ 3 ^ (3 + 1) := pow_le_pow_left₀ L0 (L_le_hi 3) _
    rw [hi_pow, g_three hg] at h1
    norm_num at h1 ⊢
    linarith
  refine ⟨L, hL1, hMills, ?_⟩
  by_contra hle
  push Not at hle
  have h1 : (1.3063778839 : ℝ) ^ 81 ≤ L ^ 81 := pow_le_pow_left₀ (by norm_num) hle 81
  have h3 : (2521008888 : ℝ) < (1.3063778839 : ℝ) ^ 81 := by norm_num
  linarith

end Greedy

/-- A greedy sequence exists: `g 0 = 2`, `g (n+1)` the least prime `≥ (g n)^3`. -/
lemma exists_greedy : ∃ g : ℕ → ℕ, g 0 = 2 ∧ ∀ n, (g (n + 1)).Prime ∧ g n ^ 3 ≤ g (n + 1) ∧
    ∀ p, p.Prime → g n ^ 3 ≤ p → g (n + 1) ≤ p := by
  refine ⟨fun n => Nat.rec 2 (fun _ x => Nat.find (exists_prime_ge (x ^ 3))) n, rfl, ?_⟩
  intro n
  exact ⟨(Nat.find_spec (exists_prime_ge _)).1, (Nat.find_spec (exists_prime_ge _)).2,
    fun p hp h => Nat.find_min' (exists_prime_ge _) ⟨hp, h⟩⟩

theorem main : H1 → H2 → type_of% @Mills.lower_bound_of_RH := by
  intro h1 h2 hRH A hA
  obtain ⟨g, hg⟩ := exists_greedy
  refine ⟨lower_bound hg hA.1.1 hA.1.2, ?_⟩
  obtain ⟨B, hB1, hBM, hBlt⟩ :=
    exists_mills_lt hg (primeBetweenCubes h1 h2 hRH) (by norm_num)
  exact lt_of_le_of_lt (hA.2 ⟨hB1, hBM⟩) hBlt

end OMA.R_Mills_lower_bound_of_RH_R1


-- MERGED VERIFIED STEP Mills.lower_bound_of_RH.R1.H1

-- Step Mills.lower_bound_of_RH.R1.H1: hypothesis H1 of reduction Mills.lower_bound_of_RH.R1
-- Credit: @senamakel
-- Proof: the Schoenfeld-rh argument, pruned to what psiBound_of_RH uses. Under RH a second difference
-- of psi_1 through the explicit formula (Hadamard factorisation of xi, zero sums on the critical line)
-- gives |psi(x) - x| <= h/2 + 3.6 + 1.5/h + sqrt(x+h) F(2(x+h)/h); 15 intervals for x <= 2^18,
-- a quadratic inequality in log x beyond.

theorem Complex.digamma_apply_add_nat {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) (n : ℕ) :
    Complex.digamma (s + n) = Complex.digamma s + ∑ k ∈ Finset.range n, (s + k)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsn (m : ℕ) : s + (n : ℂ) ≠ -(m : ℂ) := fun h =>
      hs (m + n) (by push_cast at h ⊢; linear_combination h)
    rw [show s + ((n + 1 : ℕ) : ℂ) = (s + (n : ℂ)) + 1 by push_cast; ring,
      Complex.digamma_apply_add_one _ hsn, ih, Finset.sum_range_succ]
    ring
section
namespace Erdos985
end Erdos985
end
section
namespace Erdos985
open ArithmeticFunction Real
end Erdos985
end
section
open scoped BigOperators
namespace Real
lemma vfh {r : ℝ} (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (m : ℕ) :
    r ^ (m + 1) / (1 - r) ≤ 2 * r ^ (m + 1) := by
  have hpow : 0 ≤ r ^ (m + 1) := pow_nonneg hr _
  have hhalf' : (1 / 2 : ℝ) ≤ 1 - r := by linarith
  calc
    r ^ (m + 1) / (1 - r) ≤ r ^ (m + 1) / (1 / 2 : ℝ) := by
      exact div_le_div_of_nonneg_left hpow (by positivity) hhalf'
    _ = 2 * r ^ (m + 1) := by ring
end Real
namespace Complex
open scoped BigOperators in
lemma vfT {z : ℂ} (hz : ‖z‖ < 1) :
    -log (1 - z) = ∑' n : ℕ, z ^ (n + 1) / (n + 1) := by
  have h := hasSum_taylorSeries_neg_log hz
  rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
  simp only [pow_zero, Nat.cast_zero, div_zero, zero_add, Nat.cast_add, Nat.cast_one]
noncomputable
def vap (m : ℕ) (z : ℂ) : ℂ :=
  -logTaylor (m + 1) (-z)
@[simp]
lemma vhg (z : ℂ) : vap 0 z = 0 := by
  simp [vap, logTaylor_succ, logTaylor_zero]
@[simp]
lemma vgl (m : ℕ) : vap m 0 = 0 := by
  simp [vap, logTaylor_at_zero]
lemma vhi (n : ℕ) (z : ℂ) :
    logTaylor (n + 1) (-z) = logTaylor n (-z) - z ^ n / n := by
  rw [logTaylor_succ, Pi.add_apply]
  have hsign : (-1 : ℂ) ^ (n + 1) * (-z) ^ n = -z ^ n := by
    have hzpow : (-z) ^ n = (((-1 : ℂ) * z) ^ n) := by simp
    rw [hzpow, mul_pow, ← mul_assoc, ← pow_add]
    have hpow : (-1 : ℂ) ^ (n + 1 + n) = (-1 : ℂ) := by
      rw [show n + 1 + n = 2 * n + 1 by omega, pow_add, pow_mul]
      norm_num
    rw [hpow]
    ring
  rw [show (-1 : ℂ) ^ (n + 1) * (-z) ^ n / n = -(z ^ n / n) by
    rw [hsign]
    ring]
  abel
lemma vfy (m : ℕ) (z : ℂ) :
    logTaylor (m + 1) (-z) = -∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1) := by
  induction m with
  | zero =>
      simp [logTaylor_succ, logTaylor_zero]
  | succ m hm =>
      rw [vhi, hm, Finset.sum_range_succ]
      have hcast : ((m + 1 : ℕ) : ℂ) = (1 + (m : ℂ)) := by
        simp [Nat.cast_add, Nat.cast_one, add_comm]
      rw [hcast]
      ring_nf
lemma vdb (m : ℕ) (z : ℂ) :
    vap m z = ∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1) := by
  simpa [vap] using congrArg Neg.neg (vfy m z)
lemma vfA (m : ℕ) (z : ℂ) :
    HasDerivAt (vap m) (∑ j ∈ Finset.range m, z ^ j) z := by
  cases m with
  | zero =>
      have hzero : vap 0 = fun _ : ℂ ↦ (0 : ℂ) := by
        funext w
        exact vhg w
      simpa [hzero] using (hasDerivAt_const z (c := (0 : ℂ)))
  | succ m =>
      have hsum :
          (∑ j ∈ Finset.range (m + 1), z ^ j) =
            ∑ j ∈ Finset.range (m + 1), (-1) ^ j * (-z) ^ j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        symm
        calc
          (-1 : ℂ) ^ j * (-z) ^ j = (-1 : ℂ) ^ j * (((-1 : ℂ) * z) ^ j) := by simp
          _ = ((-1 : ℂ) ^ j * (-1 : ℂ) ^ j) * z ^ j := by rw [mul_pow]; ring
          _ = z ^ j := by
                rw [← pow_add, show j + j = 2 * j by omega, pow_mul]
                norm_num
      rw [hsum]
      simpa [vap] using!
        (((hasDerivAt_logTaylor (m + 1) (-z)).comp z (hasDerivAt_neg z)).neg)
lemma vcP (m : ℕ) :
    Differentiable ℂ (fun z : ℂ => vap m z) := by
  intro z
  exact (vfA m z).differentiableAt
noncomputable
def vaI (m : ℕ) (z : ℂ) : ℂ :=
  ∑' k, z ^ (m + 1 + k) / (m + 1 + k)
lemma vhH {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    Summable (fun k => z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)) := by
  have h_geom : Summable (fun k : ℕ => ‖z‖ ^ k) :=
    summable_geometric_of_lt_one (norm_nonneg z) hz
  refine Summable.of_norm_bounded (g := fun k => ‖z‖ ^ k) h_geom ?_
  intro k
  rw [norm_div, norm_pow]
  have h1 : (1 : ℝ) ≤ (m + 1 + k : ℝ) := by
    have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
    nlinarith
  have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (Complex.norm_natCast (m + 1 + k))
  rw [hnorm]
  calc
    ‖z‖ ^ (m + 1 + k) / (m + 1 + k : ℝ) ≤ ‖z‖ ^ (m + 1 + k) := by
      exact div_le_self (pow_nonneg (norm_nonneg z) _) h1
    _ = ‖z‖ ^ (m + 1) * ‖z‖ ^ k := by rw [pow_add]
    _ ≤ 1 * ‖z‖ ^ k := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg z) k)
          exact pow_le_one₀ (norm_nonneg z) (le_of_lt hz)
    _ = ‖z‖ ^ k := one_mul _
lemma vhX {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    ‖vaI m z‖ ≤ ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
  dsimp only [vaI]
  have h_rhs_summable : Summable (fun k => ‖z‖ ^ (m + 1 + k)) := by
    simpa [pow_add] using
      (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left (‖z‖ ^ (m + 1))
  have h_norm_summable : Summable (fun k => ‖z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ h_rhs_summable
    intro k
    rw [norm_div, norm_pow]
    have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
        (Complex.norm_natCast (m + 1 + k))
    rw [hnorm]
    have hm : 1 ≤ (m + 1 + k : ℝ) := by
      have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
      nlinarith
    exact div_le_self (pow_nonneg (norm_nonneg z) _) hm
  calc
    ‖∑' k, z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖
        ≤ ∑' k, ‖z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖ :=
          norm_tsum_le_tsum_norm h_norm_summable
    _ ≤ ∑' k, ‖z‖ ^ (m + 1 + k) := by
          refine h_norm_summable.tsum_le_tsum ?_ h_rhs_summable
          intro k
          rw [norm_div, norm_pow]
          have hm : 1 ≤ (m + 1 + k : ℝ) := by
            have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
            nlinarith
          have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
            simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
              (Complex.norm_natCast (m + 1 + k))
          rw [hnorm]
          exact div_le_self (pow_nonneg (norm_nonneg z) _) hm
    _ = ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
          have h_eq :
              (fun k => ‖z‖ ^ (m + 1 + k)) = fun k => ‖z‖ ^ (m + 1) * ‖z‖ ^ k := by
            ext k
            rw [pow_add]
          rw [h_eq, tsum_mul_left]
          have h_geom := hasSum_geometric_of_lt_one (norm_nonneg z) hz
          rw [h_geom.tsum_eq, div_eq_mul_inv]
lemma vcn {z : ℂ} (hz : ‖z‖ < 1) (hzhalf : ‖z‖ ≤ 1 / 2) (m : ℕ) :
    ‖vaI m z‖ ≤ 2 * ‖z‖ ^ (m + 1) :=
  (vhX hz m).trans (Real.vfh (norm_nonneg z) hzhalf m)
lemma vcw (m : ℕ) (z : ℂ) :
    ‖vap m z‖ ≤ (m : ℝ) * max 1 (‖z‖ ^ m) := by
  have hsum :
      ‖vap m z‖ ≤ ∑ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖ := by
    rw [vdb]
    exact norm_sum_le _ _
  have hterm : ∀ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖ ≤ max 1 (‖z‖ ^ m) := by
    intro k hk
    rw [norm_div, norm_pow]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have hk1_nat : (1 : ℕ) ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      exact_mod_cast hk1_nat
    have hdenom : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
        (Complex.norm_natCast (k + 1))
    have hk_le : k + 1 ≤ m := Nat.succ_le_iff.2 (Finset.mem_range.1 hk)
    have hpow_le : ‖z‖ ^ (k + 1) ≤ max 1 (‖z‖ ^ m) := by
      have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
      by_cases hz1 : ‖z‖ ≤ (1 : ℝ)
      · have : ‖z‖ ^ (k + 1) ≤ 1 := by exact pow_le_one₀ hz0 hz1
        exact this.trans (le_max_left _ _)
      · have hz1' : (1 : ℝ) ≤ ‖z‖ := le_of_lt (lt_of_not_ge hz1)
        have : ‖z‖ ^ (k + 1) ≤ ‖z‖ ^ m := pow_le_pow_right₀ hz1' hk_le
        exact this.trans (le_max_right _ _)
    calc
      ‖z‖ ^ (k + 1) / ‖((k : ℂ) + 1)‖ = ‖z‖ ^ (k + 1) / ((k : ℝ) + 1) := by simp [hdenom]
      _ ≤ ‖z‖ ^ (k + 1) := by
            exact div_le_self (pow_nonneg (norm_nonneg z) _) hk1
      _ ≤ max 1 (‖z‖ ^ m) := hpow_le
  have hsum_le :
      (∑ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖) ≤
        ∑ _k ∈ Finset.range m, max 1 (‖z‖ ^ m) :=
    Finset.sum_le_sum (fun k hk => hterm k hk)
  have hcard : ∑ _k ∈ Finset.range m, max 1 (‖z‖ ^ m) = (m : ℝ) * max 1 (‖z‖ ^ m) := by
    simp [Finset.sum_const]
  exact hsum.trans (hsum_le.trans_eq hcard)
lemma vcC {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    -log (1 - z) = vap m z + vaI m z := by
  let f : ℕ → ℂ := fun k ↦ z ^ (k + 1) / ((k : ℂ) + 1)
  have h_summable : Summable f := by
    simpa [f, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (vhH hz 0)
  have h_decomp := h_summable.sum_add_tsum_nat_add m
  rw [vfT hz, vdb, ← h_decomp]
  congr 1
  dsimp only [vaI]
  refine tsum_congr fun k ↦ ?_
  simp only [f, Nat.cast_add]
  ring_nf
end Complex
end
section
noncomputable section
namespace Complex
variable {z : ℂ}
theorem vgp (z : ℂ) : -‖z‖ ≤ z.re :=
  neg_le_of_abs_le (abs_re_le_norm z)
lemma vee (u : ℂ) (n : ℕ) (hu : (1 : ℝ) ≤ ‖u‖) :
    ‖(u ^ n)⁻¹‖ ≤ 1 := by
  have hge : (1 : ℝ) ≤ ‖u ^ n‖ := by
    rw [Complex.norm_pow]
    exact one_le_pow₀ hu
  calc ‖(u ^ n)⁻¹‖ = ‖(1 : ℂ) / u ^ n‖ := by rw [inv_eq_one_div]
    _ = 1 / ‖u ^ n‖ := by
        have hone : ‖(1 : ℂ)‖ = (1 : ℝ) := by simpa using Complex.norm_natCast 1
        rw [Complex.norm_div, hone]
    _ ≤ 1 := by simpa [one_div] using inv_le_one_of_one_le₀ hge
end Complex
end
end
section
noncomputable section
open scoped BigOperators
open Set
namespace Complex
def vae (m : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (vap m z)
lemma vep (m : ℕ) (z : ℂ) :
    vae m z = (1 - z) * exp (vap m z) := by
  simp [vae]
@[simp]
lemma viJ (m : ℕ) : vae m 0 = 1 := by
  simp [vae, vgl]
lemma vbb (m : ℕ) (z : ℂ) :
    vae m z = 0 ↔ z = 1 := by
  constructor
  · intro hz
    rw [vae] at hz
    rcases mul_eq_zero.mp hz with h1 | h2
    · exact (sub_eq_zero.mp h1).symm
    · exact absurd h2 (exp_ne_zero _)
  · rintro rfl
    simp [vae]
lemma vcH (m : ℕ) (z : ℂ) :
    vae m z ≠ 0 ↔ z ≠ 1 := by
  simpa [ne_eq] using (not_congr (vbb (m := m) (z := z)))
lemma vdV (m : ℕ) {z : ℂ} (hz : z ≠ 1) :
    vae m z ≠ 0 :=
  (vcH (m := m) (z := z)).2 hz
lemma vaB (m : ℕ) :
    Differentiable ℂ (fun z : ℂ => vae m z) := by
  simpa [vae] using!
    ((differentiable_const (c := (1 : ℂ))).sub differentiable_id).mul
      (differentiable_exp.comp (vcP m))
theorem vcR (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    analyticOrderAt (fun z : ℂ => vae m (z / a)) a = (1 : ℕ∞) := by
  set F : ℂ → ℂ := fun z => vae m (z / a)
  have hF : AnalyticAt ℂ F a := by
    have hdiv : Differentiable ℂ (fun z : ℂ => z / a) := by
      simp [div_eq_mul_inv]
    have hdiff : Differentiable ℂ F := (vaB m).comp hdiv
    exact Differentiable.analyticAt (f := F) hdiff a
  let g : ℂ → ℂ := fun z => (-a⁻¹) * Complex.exp (vap m (z / a))
  have hg : AnalyticAt ℂ g a := by
    have hdiv : Differentiable ℂ (fun z : ℂ => z / a) := by
      simp [div_eq_mul_inv]
    have hpls : Differentiable ℂ (fun z : ℂ => vap m (z / a)) :=
      (vcP m).comp hdiv
    have hexp : Differentiable ℂ (fun z : ℂ => Complex.exp (vap m (z / a))) :=
      (Complex.differentiable_exp).comp hpls
    have hdiffg : Differentiable ℂ g := by
      simpa [g] using hexp.const_mul (-a⁻¹ : ℂ)
    exact Differentiable.analyticAt (f := g) hdiffg a
  have hg0 : g a ≠ 0 := by
    have hconst : (-a⁻¹ : ℂ) ≠ 0 := by simp [ha]
    have hexp0 : Complex.exp (vap m (a / a)) ≠ 0 :=
      Complex.exp_ne_zero (vap m (a / a))
    simpa [g] using mul_ne_zero hconst hexp0
  refine (hF.analyticOrderAt_eq_natCast (n := 1)).2 ?_
  refine ⟨g, hg, hg0, ?_⟩
  refine Filter.Eventually.of_forall ?_
  intro z
  have hlin : (1 - z / a) = (z - a) * (-a⁻¹) := by
    have h1 : (1 : ℂ) = a * a⁻¹ := by simp [ha]
    simp [div_eq_mul_inv, h1]
    ring
  simp only [F, g, pow_one, smul_eq_mul]
  rw [vep]
  simp [hlin, mul_assoc]
lemma vci (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (hz1 : z ≠ 1) :
    vae m z = exp (-vaI m z) := by
  unfold vae
  have hz_ne_1 : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  rw [← exp_log hz_ne_1, ← Complex.exp_add]
  have hsum : log (1 - z) + vap m z = -vaI m z := by
    have hdecomp := vcC hz m
    calc
      log (1 - z) + vap m z
          = log (1 - z) + (vap m z + vaI m z) - vaI m z := by ring
      _ = log (1 - z) + (-log (1 - z)) - vaI m z := by rw [hdecomp]
      _ = -vaI m z := by ring
  simp [hsum]
theorem vbf {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖vae m z - 1‖ ≤ 4 * ‖z‖ ^ (m + 1) := by
  by_cases hm : m = 0
  · subst hm
    have hmain : ‖(1 - z) - 1‖ ≤ 4 * ‖z‖ ^ 1 := by
      have h : (1 - z) - 1 = -z := by ring
      calc
        ‖(1 - z) - 1‖ = ‖-z‖ := by simp [h]
        _ = ‖z‖ := norm_neg z
        _ = ‖z‖ ^ 1 := by simp
        _ ≤ 4 * ‖z‖ ^ 1 := by nlinarith [pow_nonneg (norm_nonneg z) 1]
    simpa [vae] using hmain
  · have hz_lt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
    by_cases hz1 : z = 1
    · exfalso; rw [hz1] at hz; norm_num at hz
    have h_eq : vae m z = exp (-vaI m z) :=
      vci m hz_lt hz1
    rw [h_eq]
    have h_tail_bound := vcn hz_lt hz m
    have hw_le_one : ‖-vaI m z‖ ≤ 1 := by
      simp only [norm_neg]
      have : ‖vaI m z‖ ≤ 1 := by
        have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
        have h2 : 2 ≤ m + 1 := by
          exact Nat.succ_le_succ (Nat.succ_le_iff.2 hm_pos)
        have hpow : (‖z‖ ^ (m + 1)) ≤ (‖z‖ ^ 2) := by
          have hz1' : ‖z‖ ≤ 1 := by nlinarith [hz]
          have hz0' : 0 ≤ ‖z‖ := norm_nonneg z
          exact pow_le_pow_of_le_one hz0' hz1' h2
        have hmul : 2 * ‖z‖ ^ (m + 1) ≤ 2 * ‖z‖ ^ 2 := by gcongr
        have hsq : 2 * ‖z‖ ^ 2 ≤ 1 := by
          have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
          have hz_sq : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hz0 hz 2
          nlinarith
        exact (h_tail_bound.trans hmul).trans hsq
      linarith
    have h_exp_sub_one : ‖exp (-vaI m z) - 1‖ ≤ 2 * ‖-vaI m z‖ :=
      Complex.norm_exp_sub_one_le hw_le_one
    simp only [norm_neg] at h_exp_sub_one
    calc
      ‖exp (-vaI m z) - 1‖ ≤ 2 * ‖vaI m z‖ := h_exp_sub_one
      _ ≤ 2 * (2 * ‖z‖ ^ (m + 1)) := by gcongr
      _ = 4 * ‖z‖ ^ (m + 1) := by ring
lemma vcc (m : ℕ) (z : ℂ) :
    Real.log ‖1 - z‖ - ‖vap m z‖ ≤ Real.log ‖vae m z‖ := by
  by_cases hz1 : z = (1 : ℂ)
  · subst hz1
    simp [vae]
  set S : ℂ := vap m z
  have hS : vae m z = (1 - z) * Complex.exp S := by
    simp [vae, S]
  have hnorm_pos : 0 < ‖(1 : ℂ) - z‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))
  have hlog :
      Real.log ‖vae m z‖ = Real.log ‖1 - z‖ + S.re := by
    have hne : ‖(1 : ℂ) - z‖ ≠ 0 := ne_of_gt hnorm_pos
    calc
      Real.log ‖vae m z‖
          = Real.log (‖(1 : ℂ) - z‖ * ‖Complex.exp S‖) := by
              simp [hS]
      _ = Real.log ‖(1 : ℂ) - z‖ + Real.log ‖Complex.exp S‖ := by
            simpa using (Real.log_mul hne (ne_of_gt (by simp)))
      _ = Real.log ‖(1 : ℂ) - z‖ + S.re := by
            simp [Complex.norm_exp, Real.log_exp]
      _ = Real.log ‖1 - z‖ + S.re := by simp [sub_eq_add_neg, add_comm]
  have hre : S.re ≥ -‖S‖ := Complex.vgp S
  have : Real.log ‖vae m z‖ ≥ Real.log ‖1 - z‖ - ‖S‖ := by
    linarith [hlog, hre]
  simpa [S] using this
lemma vcT {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    (-2 : ℝ) * ‖z‖ ^ (m + 1) ≤ Real.log ‖vae m z‖ := by
  have hz_lt : ‖z‖ < (1 : ℝ) := lt_of_le_of_lt hz (by norm_num)
  have hz1 : z ≠ (1 : ℂ) := by
    intro h
    have : (1 : ℝ) ≤ (1 / 2 : ℝ) := by
      simpa [h] using hz
    norm_num at this
  have hEq : vae m z = Complex.exp (-vaI m z) :=
    vci m hz_lt hz1
  have hlog :
      Real.log ‖vae m z‖ = (-vaI m z).re := by
    simp [hEq, Complex.norm_exp, Real.log_exp]
  have hre : (-vaI m z).re ≥ -‖vaI m z‖ := by
    simpa [norm_neg] using Complex.vgp (-vaI m z)
  have htail := vcn hz_lt hz m
  have : (-vaI m z).re ≥ (-2 : ℝ) * ‖z‖ ^ (m + 1) := by
    calc
      (-vaI m z).re ≥ -‖vaI m z‖ := hre
      _ ≥ (-2 : ℝ) * ‖z‖ ^ (m + 1) := by
            nlinarith [htail]
  simpa [hlog, mul_assoc, mul_left_comm, mul_comm] using this
end Complex
end
end
section
noncomputable section
open Filter Topology
namespace Complex
theorem vbY {a z : ℂ} (ha : a ≠ 0) (hz : z ≠ a) :
    logDeriv (fun w : ℂ => vae 1 (w / a)) z =
      1 / (z - a) + 1 / a := by
  have hE :
      (fun w : ℂ => vae 1 (w / a)) =
        fun w : ℂ => (1 - w / a) * exp (w / a) := by
    ext w
    simp [vep, vdb]
  have hf : (1 - z / a) ≠ 0 := by
    intro hzero
    have hdiv : z / a = 1 := by
      exact (sub_eq_zero.mp hzero).symm
    exact hz ((div_eq_one_iff_eq ha).1 hdiv)
  rw [hE,
    logDeriv_mul z hf (exp_ne_zero (z / a)) (by fun_prop) (by fun_prop)]
  have hleft : logDeriv (fun w : ℂ => 1 - w / a) z = 1 / (z - a) := by
    rw [logDeriv_apply]
    have hderiv : deriv (fun w : ℂ => 1 - w / a) z = -(1 / a) := by
      simp [one_div]
    rw [hderiv]
    have haz : -z + a ≠ 0 := by
      simpa [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr (Ne.symm hz)
    field_simp [ha, sub_ne_zero.mpr hz, haz]
    have haz' : a - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
    have hza : z - a = -(a - z) := by ring
    rw [hza]
    field_simp [haz']
  have hright : logDeriv (fun w : ℂ => exp (w / a)) z = 1 / a := by
    rw [logDeriv_apply]
    have hderiv : deriv (fun w : ℂ => exp (w / a)) z =
        exp (z / a) * (1 / a) := by
      simp [one_div]
    rw [hderiv]
    field_simp [exp_ne_zero (z / a)]
  rw [hleft, hright]
end Complex
end
end
section
open Filter Topology Set
namespace MeromorphicOn
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U K : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
lemma vdH (f : 𝕜 → E) {U K : Set 𝕜}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    (K ∩ (MeromorphicOn.divisor f U).support).Finite := by
  classical
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hloc :
      ∀ x ∈ K, ∃ V : Set 𝕜, V ∈ 𝓝 x ∧ Set.Finite (V ∩ D.support) := by
    intro x hxK
    rcases D.supportLocallyFiniteWithinDomain x (hKU hxK) with ⟨V, hV, hfin⟩
    exact ⟨V, hV, hfin⟩
  choose V hVnhds hVfin using hloc
  rcases hK.elim_nhds_subcover' (U := fun x hx => V x hx) (hU := fun x hx => hVnhds x hx) with
    ⟨t, ht⟩
  have hsub :
      K ∩ D.support ⊆ ⋃ x ∈ t, (V (x : 𝕜) x.2 ∩ D.support) := by
    intro y hy
    rcases hy with ⟨hyK, hyS⟩
    have hycov : y ∈ ⋃ x ∈ t, V (x : 𝕜) x.2 := ht hyK
    rcases Set.mem_iUnion.1 hycov with ⟨x, hycov'⟩
    rcases Set.mem_iUnion.1 hycov' with ⟨hxT, hyV⟩
    refine Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ?_⟩
    exact ⟨hxT, ⟨hyV, hyS⟩⟩
  have hfinU : Set.Finite (⋃ x ∈ t, (V (x : 𝕜) x.2 ∩ D.support)) := by
    classical
    refine (t.finite_toSet).biUnion ?_
    intro x hx
    simpa using (hVfin (x : 𝕜) x.2)
  exact hfinU.subset hsub
end MeromorphicOn
end
section
open Set
namespace Complex.Hadamard
def vhE (f : ℂ → ℂ) (U : Set ℂ) : Type :=
  Σ z : ℂ, Fin (Int.toNat (MeromorphicOn.divisor f U z))
abbrev vab (f : ℂ → ℂ) (U : Set ℂ) : Type :=
  {p : vhE f U // p.1 ≠ 0}
abbrev vaa {f : ℂ → ℂ} {U : Set ℂ} (p : vab f U) : ℂ :=
  p.1.1
@[simp]
lemma vao {f : ℂ → ℂ} {U : Set ℂ} (p : vab f U) :
    vaa p ≠ 0 := p.2
@[simp]
lemma vbm {f : ℂ → ℂ} {U : Set ℂ}
    (p : vab f U) :
    MeromorphicOn.divisor f U (vaa p) ≠ 0 := by
  have hn :
      Int.toNat (MeromorphicOn.divisor f U (vaa p)) ≠ 0 := by
    intro h0
    have q0 : Fin 0 := by
      simpa [vaa, h0] using p.1.2
    exact Fin.elim0 q0
  intro hdiv
  have : Int.toNat (MeromorphicOn.divisor f U (vaa p)) = 0 := by
    simp [hdiv]
  exact hn this
noncomputable def vac (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) (z : ℂ) : ℂ :=
  ∏' p : vab f U, vae m (z / vaa p)
@[simp]
lemma vaC (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) :
    vac m f U 0 = 1 := by
  simp [vac]
end Complex.Hadamard
end
section
namespace Complex
section UniformMul
theorem _root_.TendstoUniformlyOn.vhF {ι : Type*} {p : Filter ι} {K : Set ℂ}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {h : ℂ → ℂ}
    (hF : TendstoUniformlyOn F f p K) (hh : ∃ C, ∀ z ∈ K, ‖h z‖ ≤ C) :
    TendstoUniformlyOn (fun n z => h z * F n z) (fun z => h z * f z) p K := by
  intro u hu
  rcases Metric.mem_uniformity_dist.1 hu with ⟨ε, hεpos, hεu⟩
  rcases hh with ⟨C, hC⟩
  set C' : ℝ := max C 1
  have hC'pos : 0 < C' := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hC' : ∀ z ∈ K, ‖h z‖ ≤ C' := fun z hz => le_trans (hC z hz) (le_max_left _ _)
  have hv : {p : ℂ × ℂ | dist p.1 p.2 < ε / C'} ∈ uniformity ℂ :=
    Metric.mem_uniformity_dist.2 ⟨ε / C', div_pos hεpos hC'pos, fun _ _ hab => hab⟩
  have hF' : ∀ᶠ n in p, ∀ z : ℂ, z ∈ K → dist (f z) (F n z) < ε / C' := hF _ hv
  filter_upwards [hF'] with n hn z hzK
  have hn' : ‖f z - F n z‖ < ε / C' := by simpa [dist_eq_norm] using hn z hzK
  have hle : ‖h z‖ * ‖f z - F n z‖ ≤ C' * ‖f z - F n z‖ :=
    mul_le_mul_of_nonneg_right (hC' z hzK) (norm_nonneg _)
  have hlt : C' * ‖f z - F n z‖ < C' * (ε / C') := mul_lt_mul_of_pos_left hn' hC'pos
  have hnorm :
      ‖h z * f z - h z * F n z‖ = ‖h z‖ * ‖f z - F n z‖ := by
    calc
      ‖h z * f z - h z * F n z‖ = ‖h z * (f z - F n z)‖ := by simp [mul_sub]
      _ = ‖h z‖ * ‖f z - F n z‖ := by simp
  have hdist : dist (h z * f z) (h z * F n z) < ε := by
    rw [dist_eq_norm, hnorm]
    have hlt' : ‖h z‖ * ‖f z - F n z‖ < ε := by
      calc
        ‖h z‖ * ‖f z - F n z‖ ≤ C' * ‖f z - F n z‖ := hle
        _ < C' * (ε / C') := hlt
        _ = ε := by field_simp [hC'pos.ne']
    exact hlt'
  exact hεu hdist
end UniformMul
end Complex
end
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
lemma vaT {f : ℂ → ℂ} {U : Set ℂ} (B : ℝ)
    (hBU : Metric.closedBall (0 : ℂ) B ⊆ U) :
    Finite {p : vab f U // ‖vaa p‖ ≤ B} := by
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hK : IsCompact (Metric.closedBall (0 : ℂ) B) := isCompact_closedBall _ _
  have hpts0 : ((Metric.closedBall (0 : ℂ) B) ∩ D.support).Finite :=
    MeromorphicOn.vdH (f := f) (U := U)
      (K := Metric.closedBall (0 : ℂ) B) hK hBU
  set pts : Set ℂ := ((Metric.closedBall (0 : ℂ) B) ∩ D.support) \ {0}
  have hpts : pts.Finite := hpts0.sdiff
  let : Fintype pts := hpts.fintype
  let T : Type := Σ z : pts, Fin (Int.toNat (D z.1))
  have : Finite T := by infer_instance
  let F :
      {p : vab f U // ‖vaa p‖ ≤ B} → T := fun p =>
    ⟨⟨vaa p.1, by
        have hball : vaa p.1 ∈ Metric.closedBall (0 : ℂ) B := by
          simpa [Metric.mem_closedBall, dist_zero_right] using p.2
        have hsupport : vaa p.1 ∈ D.support := by
          have hne_toNat :
              Int.toNat (MeromorphicOn.divisor f U (vaa p.1)) ≠ 0 := by
            intro h0
            have hpfin :
                Fin (Int.toNat (MeromorphicOn.divisor f U (vaa p.1))) := by
              simpa [D] using p.1.1.2
            have : Fin 0 := by simpa [h0] using hpfin
            exact Fin.elim0 this
          have hne_D : D (vaa p.1) ≠ 0 := by
            intro hD0
            apply hne_toNat
            simp [D, hD0]
          simp [D, Function.locallyFinsuppWithin.support, Function.support]
        have hne0 : vaa p.1 ≠ 0 := vao p.1
        exact ⟨⟨hball, hsupport⟩, by simp [Set.mem_singleton_iff]⟩⟩,
      p.1.1.2⟩
  refine Finite.of_injective F ?_
  intro p q hpq
  apply Subtype.ext
  apply Subtype.ext
  have h' := (Sigma.mk.inj_iff.1 hpq)
  have hz : vaa p.1 = vaa q.1 := congrArg Subtype.val h'.1
  apply (Sigma.mk.inj_iff).2
  refine ⟨hz, ?_⟩
  exact h'.2
lemma vat {f : ℂ → ℂ} {U : Set ℂ} (B : ℝ)
    (hBU : Metric.closedBall (0 : ℂ) B ⊆ U) :
    ({p : vab f U | ‖vaa p‖ ≤ B} : Set _).Finite := by
  let s : Set (vab f U) := {p | ‖vaa p‖ ≤ B}
  have : Finite (↥s) :=
    vaT (f := f) (U := U) B hBU
  exact Set.toFinite s
lemma vbu {z a : ℂ} {R : ℝ}
    (hR : 0 < R) (hz : ‖z‖ ≤ R) (ha : (2 * R : ℝ) < ‖a‖) :
    ‖z / a‖ ≤ (1 / 2 : ℝ) := by
  have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hR]
  have hinv : ‖a‖⁻¹ < (2 * R)⁻¹ := by
    simpa [one_div] using one_div_lt_one_div_of_lt h2R_pos ha
  have hmul_le : ‖z‖ * ‖a‖⁻¹ ≤ R * ‖a‖⁻¹ :=
    mul_le_mul_of_nonneg_right hz (inv_nonneg.2 (norm_nonneg a))
  have hmul_lt : R * ‖a‖⁻¹ < R * (2 * R)⁻¹ :=
    mul_lt_mul_of_pos_left hinv hR
  have hRhalf : R * (2 * R)⁻¹ = (1 / 2 : ℝ) := by
    have hRne : (R : ℝ) ≠ 0 := hR.ne'
    rw [show R * (2 * R)⁻¹ = R / (2 * R) by simp [div_eq_mul_inv]]
    field_simp [hRne]
  have hnorm : ‖z / a‖ = ‖z‖ * ‖a‖⁻¹ := by
    simp [div_eq_mul_inv]
  exact le_of_lt <| by
    calc
      ‖z / a‖ = ‖z‖ * ‖a‖⁻¹ := hnorm
      _ ≤ R * ‖a‖⁻¹ := hmul_le
      _ < R * (2 * R)⁻¹ := hmul_lt
      _ = (1 / 2 : ℝ) := hRhalf
theorem vaM
    {f : ℂ → ℂ} {z : ℂ}
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (2 : ℕ)))
    (hz : ∀ p : vab f (Set.univ : Set ℂ), z ≠ vaa p) :
    Summable (fun p : vab f (Set.univ : Set ℂ) =>
      1 / (z - vaa p) + 1 / vaa p) := by
  let R : ℝ := max ‖z‖ 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hzle : ‖z‖ ≤ R := le_max_left _ _
  let u : vab f (Set.univ : Set ℂ) → ℝ :=
    fun p => (2 * R) * (‖vaa p‖⁻¹ ^ (2 : ℕ))
  have hu : Summable u := h_sum.mul_left (2 * R)
  refine hu.of_norm_bounded_eventually ?_
  have h_big :
      ∀ᶠ p : vab f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖vaa p‖ := by
    have hfin :
        ({p : vab f (Set.univ : Set ℂ) | ‖vaa p‖ ≤
          2 * R} : Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact vat
        (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖vaa p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this
  filter_upwards [h_big] with p hp
  let a : ℂ := vaa p
  have ha0 : a ≠ 0 := vao p
  have hza0 : z - a ≠ 0 := sub_ne_zero.mpr (hz p)
  have hterm : 1 / (z - a) + 1 / a = z / (a * (z - a)) := by
    field_simp [ha0, hza0]
    ring
  have htri : ‖a‖ ≤ ‖z‖ + ‖z - a‖ := by
    have hraw : ‖a‖ ≤ ‖z‖ + ‖a - z‖ := by
      have h := norm_add_le z (a - z)
      simpa [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
    simpa [norm_sub_rev] using hraw
  have hza_lower : ‖a‖ / 2 ≤ ‖z - a‖ := by
    nlinarith [htri, hzle, hp]
  have hnorm : ‖1 / (z - a) + 1 / a‖ ≤ (2 * R) * (‖a‖⁻¹ ^ (2 : ℕ)) := by
    rw [hterm, norm_div, norm_mul]
    have ha_norm_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    have hza_norm_pos : 0 < ‖z - a‖ := norm_pos_iff.mpr hza0
    rw [div_eq_mul_inv]
    calc
      ‖z‖ * (‖a‖ * ‖z - a‖)⁻¹
          = ‖z‖ * ‖a‖⁻¹ * ‖z - a‖⁻¹ := by
              field_simp [ha_norm_pos.ne', hza_norm_pos.ne']
      _ ≤ R * ‖a‖⁻¹ * ‖z - a‖⁻¹ := by
              gcongr
      _ ≤ R * ‖a‖⁻¹ * (2 * ‖a‖⁻¹) := by
              gcongr
              have hhalf_pos : 0 < ‖a‖ / 2 := by positivity
              have hinv : ‖z - a‖⁻¹ ≤ (‖a‖ / 2)⁻¹ := by
                simpa [one_div] using one_div_le_one_div_of_le hhalf_pos hza_lower
              have hhalf_inv : (‖a‖ / 2)⁻¹ = 2 * ‖a‖⁻¹ := by field_simp [ha_norm_pos.ne']
              simpa [hhalf_inv] using hinv
      _ = (2 * R) * (‖a‖⁻¹ ^ (2 : ℕ)) := by ring
  simpa [u, a] using hnorm
theorem vcq
    (m : ℕ) (f : ℂ → ℂ) {K : Set ℂ} (hK : IsCompact K)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1))) :
    HasProdUniformlyOn
      (fun (p : vab f (Set.univ : Set ℂ)) (z : ℂ) =>
        vae m (z / vaa p))
      (vac m f (Set.univ : Set ℂ)) K := by
  rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0, hR0⟩
  set R : ℝ := max R0 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hnormK : ∀ z ∈ K, ‖z‖ ≤ R := fun z hzK => le_trans (hR0 z hzK) (le_max_left _ _)
  let g : vab f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p z => vae m (z / vaa p) - 1
  let u : vab f (Set.univ : Set ℂ) → ℝ :=
    fun p => (4 * R ^ (m + 1)) * (‖vaa p‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * R ^ (m + 1))
  have h_big :
      ∀ᶠ p : vab f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖vaa p‖ := by
    have hfin :
        ({p : vab f (Set.univ : Set ℂ) | ‖vaa p‖ ≤ 2 * R} :
            Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact vat (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖vaa p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this
  have hBound :
      ∀ᶠ p in Filter.cofinite, ∀ z ∈ K, ‖g p z‖ ≤ u p := by
    filter_upwards [h_big] with p hp z hzK
    have hzle : ‖z‖ ≤ R := hnormK z hzK
    have hz_div : ‖z / vaa p‖ ≤ (1 / 2 : ℝ) := by
      exact vbu hRpos hzle hp
    have hE :
        ‖vae m (z / vaa p) - 1‖ ≤
          4 * ‖z / vaa p‖ ^ (m + 1) :=
      vbf (m := m) (z := z / vaa p) hz_div
    have hz_pow :
        ‖z / vaa p‖ ^ (m + 1) ≤
          (R ^ (m + 1)) * (‖vaa p‖⁻¹ ^ (m + 1)) := by
      have : ‖z / vaa p‖ = ‖z‖ * ‖vaa p‖⁻¹ := by
        simp [div_eq_mul_inv]
      rw [this]
      have : (‖z‖ * ‖vaa p‖⁻¹) ^ (m + 1) =
          ‖z‖ ^ (m + 1) * (‖vaa p‖⁻¹ ^ (m + 1)) := by
        simp [mul_pow]
      rw [this]
      have hzle_pow : ‖z‖ ^ (m + 1) ≤ R ^ (m + 1) :=
        pow_le_pow_left₀ (norm_nonneg z) hzle (m + 1)
      gcongr
    dsimp [g, u]
    nlinarith [hE, hz_pow]
  have hcts : ∀ p, ContinuousOn (g p) K := by
    intro p
    have hcontE : Continuous (fun z : ℂ => vae m z) :=
      (vaB m).continuous
    have hdiv : Continuous fun z : ℂ => z / vaa p := by
      simpa [div_eq_mul_inv] using! (continuous_id.mul continuous_const)
    have hcont : Continuous fun z : ℂ => vae m (z / vaa p) :=
      hcontE.comp hdiv
    simpa only [g] using hcont.continuousOn.fun_sub continuous_const.continuousOn
  have hprod :
      HasProdUniformlyOn (fun p z ↦ 1 + g p z) (fun z ↦ ∏' p, (1 + g p z)) K := by
    simpa using
      Summable.hasProdUniformlyOn_one_add (f := g) (u := u) (K := K) hK hu hBound hcts
  simpa [g, vac, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using! hprod
theorem vav
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1))) :
    HasProdLocallyUniformlyOn
      (fun (p : vab f (Set.univ : Set ℂ)) (z : ℂ) =>
        vae m (z / vaa p))
      (vac m f (Set.univ : Set ℂ))
      (Set.univ : Set ℂ) := by
  refine hasProdLocallyUniformlyOn_of_forall_compact
      (f := fun p z => vae m (z / vaa p))
      (g := vac m f (Set.univ : Set ℂ))
      (s := (Set.univ : Set ℂ)) isOpen_univ ?_
  intro K hKU hK
  simpa using
    (vcq (m := m) (f := f) (K := K) hK h_sum)
theorem vau
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1))) :
    DifferentiableOn ℂ (vac m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) := by
  have hloc :
      TendstoLocallyUniformlyOn
        (fun (s : Finset (vab f (Set.univ : Set ℂ))) (z : ℂ) =>
          ∏ p ∈ s, vae m (z / vaa p))
        (vac m f (Set.univ : Set ℂ))
        Filter.atTop (Set.univ : Set ℂ) := by
    simpa [HasProdLocallyUniformlyOn] using
      (vav (m := m) (f := f) h_sum)
  have hF :
      ∀ᶠ s : Finset (vab f (Set.univ : Set ℂ)) in Filter.atTop,
        DifferentiableOn ℂ
          (fun z : ℂ => ∏ p ∈ s, vae m (z / vaa p))
          (Set.univ : Set ℂ) := by
    refine Filter.Eventually.of_forall ?_
    intro s
    have hdiff :
        Differentiable ℂ
          (fun z : ℂ => ∏ p ∈ s, vae m (z / vaa p)) := by
      let F : vab f (Set.univ : Set ℂ) → ℂ → ℂ :=
        fun p z => vae m (z / vaa p)
      have hF' : ∀ p ∈ s, Differentiable ℂ (F p) := by
        intro p hp
        have hdiv : Differentiable ℂ (fun z : ℂ => z / vaa p) := by
          have : Differentiable ℂ (fun z : ℂ => z * ((vaa p)⁻¹)) :=
            (differentiable_id : Differentiable ℂ (fun z : ℂ => z)).mul_const
              ((vaa p)⁻¹)
          simp [div_eq_mul_inv]
        exact (vaB m).comp hdiv
      simpa [F] using (Differentiable.fun_finsetProd (𝕜 := ℂ) (f := F) (u := s) hF')
    simpa using hdiff.differentiableOn
  have : (Filter.atTop : Filter (Finset (vab f (Set.univ : Set ℂ)))).NeBot :=
    Filter.atTop_neBot
  exact hloc.differentiableOn hF isOpen_univ
theorem vcz
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1))) (z : ℂ) :
    DifferentiableAt ℂ (vac m f (Set.univ : Set ℂ)) z :=
  ((vau m f h_sum) z (by simp)).differentiableAt
    (by simp)
theorem vcB
    {f : ℂ → ℂ} {z : ℂ}
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (2 : ℕ)))
    (hz : ∀ p : vab f (Set.univ : Set ℂ), z ≠ vaa p)
    (hprod_ne : vac 1 f (Set.univ : Set ℂ) z ≠ 0) :
    logDeriv (vac 1 f (Set.univ : Set ℂ)) z =
      ∑' p : vab f (Set.univ : Set ℂ),
        (1 / (z - vaa p) + 1 / vaa p) := by
  let Φ : vab f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p w => vae 1 (w / vaa p)
  have hf : ∀ p, Φ p z ≠ 0 := by
    intro p
    have hp0 : vaa p ≠ 0 := vao p
    refine vdV 1 ?_
    intro h
    exact hz p ((div_eq_one_iff_eq hp0).1 h)
  have hd : ∀ p, DifferentiableOn ℂ (Φ p) (Set.univ : Set ℂ) := by
    intro p
    have hdiv : Differentiable ℂ (fun w : ℂ => w / vaa p) := by
      have : Differentiable ℂ (fun w : ℂ => w * ((vaa p)⁻¹)) :=
        (differentiable_id : Differentiable ℂ (fun w : ℂ => w)).mul_const
          ((vaa p)⁻¹)
      simp [div_eq_mul_inv]
    exact ((vaB 1).comp hdiv).differentiableOn
  have hm' : Summable fun p => logDeriv (Φ p) z := by
    have hm :
        Summable (fun p : vab f (Set.univ : Set ℂ) =>
          1 / (z - vaa p) + 1 / vaa p) :=
      vaM h_sum hz
    refine hm.congr ?_
    intro p
    have hp0 : vaa p ≠ 0 := vao p
    simpa [Φ] using
      (Complex.vbY
        (a := vaa p) (z := z) hp0 (hz p)).symm
  have htend : MultipliableLocallyUniformlyOn Φ (Set.univ : Set ℂ) := by
    have hprod := vav
      (m := 1) (f := f) h_sum
    simpa [Φ, vac] using hprod.multipliableLocallyUniformlyOn
  have hnez : (∏' p, Φ p z) ≠ 0 := by
    simpa [Φ, vac] using hprod_ne
  have hlog : logDeriv (∏' p, Φ p ·) z = ∑' p, logDeriv (Φ p) z :=
    logDeriv_tprod_eq_tsum (s := (Set.univ : Set ℂ)) isOpen_univ (by simp)
      hf hd hm' htend hnez
  calc
    logDeriv (vac 1 f (Set.univ : Set ℂ)) z
        = ∑' p, logDeriv (Φ p) z := by
          simpa [Φ, vac] using! hlog
    _ = ∑' p : vab f (Set.univ : Set ℂ),
          (1 / (z - vaa p) + 1 / vaa p) := by
          refine tsum_congr fun p => ?_
          have hp0 : vaa p ≠ 0 := vao p
          simpa [Φ] using
            Complex.vbY
              (a := vaa p) (z := z) hp0 (hz p)
end Complex.Hadamard
end
section
open Set
namespace Complex.Hadamard
end Complex.Hadamard
end
section
noncomputable section
open Set
open scoped Topology BigOperators
namespace Complex.Hadamard
lemma vaw {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    MeromorphicOn.divisor f (Set.univ : Set ℂ) z = (analyticOrderNatAt f z : ℤ) := by
  have hmero : MeromorphicOn f (Set.univ : Set ℂ) := by
    intro w hw
    exact (Differentiable.analyticAt (f := f) hf w).meromorphicAt
  simp only
    [MeromorphicOn.divisor_apply hmero (by simp : z ∈ (Set.univ : Set ℂ)), analyticOrderNatAt]
  have han : AnalyticAt ℂ f z := Differentiable.analyticAt (f := f) hf z
  cases h : analyticOrderAt f z with
  | top =>
      simp [han.meromorphicOrderAt_eq, h]
  | coe n =>
      simp [han.meromorphicOrderAt_eq, h]
theorem vcl (f : ℂ → ℂ) (z₀ : ℂ) :
    ({p : vab f (Set.univ : Set ℂ) | vaa p = z₀} :
      Set _).Finite := by
  have hsub :
      ({p : vab f (Set.univ : Set ℂ) | vaa p = z₀} : Set _)
        ⊆ ({p : vab f (Set.univ : Set ℂ) | ‖vaa p‖ ≤ ‖z₀‖} :
          Set _) := by
    intro p hp
    have : vaa p = z₀ := hp
    simp [this]
  have hfin :
      ({p : vab f (Set.univ : Set ℂ) | ‖vaa p‖ ≤ ‖z₀‖} :
        Set _).Finite := by
    have : Metric.closedBall (0 : ℂ) ‖z₀‖ ⊆ (Set.univ : Set ℂ) := by simp
    simpa using (vat (f := f) (U := (Set.univ : Set ℂ))
      (B := ‖z₀‖) this)
  exact hfin.subset hsub
def vad (f : ℂ → ℂ) (z₀ : ℂ) :
    Finset (vab f (Set.univ : Set ℂ)) :=
  (vcl (f := f) z₀).toFinset
@[simp]
lemma vai (f : ℂ → ℂ) (z₀ : ℂ)
    (p : vab f (Set.univ : Set ℂ)) :
    p ∈ vad (f := f) z₀ ↔ vaa p = z₀ := by
  simp [vad]
theorem vdS
    (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (vab f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      vad (f := f) z₀ ⊆ s := by
  refine (Filter.eventually_atTop.2 ?_)
  refine ⟨vad (f := f) z₀, ?_⟩
  intro s hs
  exact hs
lemma vbP (f : ℂ → ℂ) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    (vad (f := f) z₀).card =
      Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀) := by
  let S : Set (vab f (Set.univ : Set ℂ)) := {p | vaa p = z₀}
  have hS : S.Finite := vcl (f := f) z₀
  set n : ℕ := Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀)
  have hcard : Nat.card S = n := by
    classical
    have : Fintype S := hS.fintype
    let e : S ≃ Fin n :=
      { toFun := by
          intro x
          rcases x with ⟨p, hp⟩
          rcases p with ⟨⟨z, q⟩, hz⟩
          have hzEq : z = z₀ := by simpa [vaa] using! hp
          subst hzEq
          simpa [n] using q
        invFun := by
          intro q
          refine ⟨⟨⟨z₀, ?_⟩, hz₀⟩, ?_⟩
          · simpa [n] using q
          · simp [S, vaa]
        left_inv := by
          rintro ⟨p, hp⟩
          rcases p with ⟨⟨z, q⟩, hz⟩
          have hzEq : z = z₀ := by simpa [vaa] using! hp
          subst hzEq
          (ext; rfl)
        right_inv := by
          intro q
          rfl }
    have h := Nat.card_congr (α := S) (β := Fin n) e
    simpa using (h.trans (by simp))
  have hSncard : S.ncard = n := by
    simpa [Nat.card_coe_set_eq] using hcard
  have hto : hS.toFinset = vad (f := f) z₀ := by
    rfl
  have htoFinset : S.ncard = (vad (f := f) z₀).card := by
    have h' : S.ncard = hS.toFinset.card := Set.ncard_eq_toFinset_card S hS
    simpa [hto] using h'
  exact htoFinset.symm.trans hSncard
lemma vaA
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    (vad (f := f) z₀).card = analyticOrderNatAt f z₀ := by
  have hdiv :
      MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀ = (analyticOrderNatAt f z₀ : ℤ) :=
    vaw (f := f) hf z₀
  have htoNat : Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀) =
    analyticOrderNatAt f z₀ := by
    simp [hdiv]
  exact (vbP (f := f) (z₀ := z₀) hz₀).trans htoNat
lemma vcf
    {f : ℂ → ℂ} (z₀ : ℂ) (p : vab f (Set.univ : Set ℂ)) :
    p ∉ vad (f := f) z₀ ↔ vaa p ≠ z₀ := by
  simp [vai]
end Complex.Hadamard
end
end
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
noncomputable def vam
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : vab f (Set.univ : Set ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if p ∈ vad (f := f) z₀ then (1 : ℂ)
    else vae m (z / vaa p)
@[simp]
theorem vbF
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : vab f (Set.univ : Set ℂ)) (z : ℂ)
    (hp : p ∈ vad (f := f) z₀) :
    vam m f z₀ p z = 1 := by
  classical
  simp [vam, hp]
@[simp]
theorem vaV
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : vab f (Set.univ : Set ℂ)) (z : ℂ)
    (hp : p ∉ vad (f := f) z₀) :
    vam m f z₀ p z =
      vae m (z / vaa p) := by
  classical
  simp [vam, hp]
lemma vfa
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : vab f (Set.univ : Set ℂ)) (z : ℂ) :
    vam m f z₀ p z =
      if vaa p = z₀ then (1 : ℂ)
      else vae m (z / vaa p) := by
  classical
  by_cases h : vaa p = z₀
  · have hp : p ∈ vad (f := f) z₀ := by
      simpa [vai] using h
    simp [vbF, hp, h]
  · have hp : p ∉ vad (f := f) z₀ := by
      intro hmem
      exact h ((vai f z₀ p).1 hmem)
    simp [vaV, hp, h]
noncomputable def vag (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (vab f (Set.univ : Set ℂ))) (z : ℂ) : ℂ :=
  ∏ p ∈ s, vae m (z / vaa p)
theorem vax (m : ℕ) {f : ℂ → ℂ}
    (p : vab f (Set.univ : Set ℂ)) :
    Differentiable ℂ (fun z : ℂ => vae m (z / vaa p)) := by
  have hdiv : Differentiable ℂ (fun z : ℂ => z / vaa p) := by
    simp [div_eq_mul_inv]
  exact (vaB m).comp hdiv
theorem vbM (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (vab f (Set.univ : Set ℂ))) :
    Differentiable ℂ (vag m f s) := by
  let Φ : vab f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p z => vae m (z / vaa p)
  have hΦ : ∀ p ∈ s, Differentiable ℂ (Φ p) := by
    intro p _hp
    exact vax m p
  simpa [vag, Φ] using!
    (Differentiable.fun_finsetProd (𝕜 := ℂ) (f := Φ) (u := s) hΦ)
theorem vbo (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (vab f (Set.univ : Set ℂ))) (z₀ : ℂ) :
    AnalyticAt ℂ (vag m f s) z₀ :=
  (vbM m f s).analyticAt z₀
noncomputable def vah
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (vab f (Set.univ : Set ℂ))) (z : ℂ) : ℂ :=
  ∏ p ∈ s, vam m f z₀ p z
@[simp]
lemma vdQ
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (vab f (Set.univ : Set ℂ))) (z : ℂ) :
    vah m f z₀ s z =
      ∏ p ∈ s, if vaa p = z₀ then (1 : ℂ)
        else vae m (z / vaa p) := by
  simp [vah, vam,
    vai]
theorem vct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (vab f (Set.univ : Set ℂ))) :
    Differentiable ℂ (vah m f z₀ s) := by
  let Φ : vab f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p z => vam m f z₀ p z
  have hΦ : ∀ p ∈ s, Differentiable ℂ (Φ p) := by
    intro p _hp
    by_cases hpF : p ∈ vad (f := f) z₀
    · have hΦp : Φ p = fun _ => (1 : ℂ) := by
        ext z
        simp only [Φ, vbF m f z₀ p z hpF]
      rw [hΦp]
      exact differentiable_const (1 : ℂ)
    · have hΦp : Φ p = fun z => vae m (z / vaa p) := by
        ext z
        simp only [Φ, vaV m f z₀ p z hpF]
      rw [hΦp]
      exact vax m p
  have hEq : (fun z : ℂ => ∏ p ∈ s, Φ p z) =
      vah m f z₀ s := by
    ext z
    simp [Φ, vah]
  have : Differentiable ℂ (fun z : ℂ => ∏ p ∈ s, Φ p z) := by
    simpa using (Differentiable.fun_finsetProd (𝕜 := ℂ) (f := Φ) (u := s) hΦ)
  simpa [hEq] using this
noncomputable def vaf
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) (z : ℂ) : ℂ :=
  ∏' p : vab f (Set.univ : Set ℂ), vam m f z₀ p z
theorem vbz
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) {K : Set ℂ} (hK : IsCompact K)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1))) :
    HasProdUniformlyOn (fun (p : vab f (Set.univ : Set ℂ)) (z : ℂ) =>
        vam m f z₀ p z) (vaf m f z₀)
      K := by
  rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0, hR0⟩
  set R : ℝ := max R0 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hnormK : ∀ z ∈ K, ‖z‖ ≤ R := fun z hzK => le_trans (hR0 z hzK) (le_max_left _ _)
  let term : vab f (Set.univ : Set ℂ) → ℂ → ℂ := fun p z =>
    vam m f z₀ p z
  let g : vab f (Set.univ : Set ℂ) → ℂ → ℂ := fun p z => term p z - 1
  let u : vab f (Set.univ : Set ℂ) → ℝ :=
    fun p => (4 * R ^ (m + 1)) * (‖vaa p‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * R ^ (m + 1))
  have h_big :
      ∀ᶠ p : vab f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖vaa p‖ := by
    have hfin :
        ({p : vab f (Set.univ : Set ℂ) | ‖vaa p‖ ≤ 2 * R} :
          Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact vat (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖vaa p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this
  have hBound :
      ∀ᶠ p in Filter.cofinite, ∀ z ∈ K, ‖g p z‖ ≤ u p := by
    filter_upwards [h_big] with p hp z hzK
    by_cases hpF : p ∈ vad (f := f) z₀
    · have hval : vaa p = z₀ :=
        (vai (f := f) (z₀ := z₀) p).1 hpF
      have hu0 : 0 ≤ u p := by
        dsimp [u]
        refine mul_nonneg ?_ ?_
        · nlinarith [pow_nonneg (show 0 ≤ R from le_of_lt hRpos) (m + 1)]
        · exact pow_nonneg (inv_nonneg.2 (norm_nonneg _)) (m + 1)
      simp [g, term, vam, hval, hu0, sub_eq_add_neg]
    · have hzle : ‖z‖ ≤ R := hnormK z hzK
      have hz_div : ‖z / vaa p‖ ≤ (1 / 2 : ℝ) := by
        have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hRpos]
        have hinv : ‖vaa p‖⁻¹ < (2 * R)⁻¹ := by
          simpa [one_div] using (one_div_lt_one_div_of_lt h2R_pos hp)
        have hmul_le : ‖z‖ * ‖vaa p‖⁻¹ ≤ R * ‖vaa p‖⁻¹ := by
          refine mul_le_mul_of_nonneg_right hzle ?_
          exact inv_nonneg.2 (norm_nonneg _)
        have hmul_lt : R * ‖vaa p‖⁻¹ < R * (2 * R)⁻¹ :=
          mul_lt_mul_of_pos_left hinv hRpos
        have hlt : ‖z‖ * ‖vaa p‖⁻¹ < R * (2 * R)⁻¹ :=
          lt_of_le_of_lt hmul_le hmul_lt
        have hRhalf : R * (2 * R)⁻¹ = (1 / 2 : ℝ) := by
          have hRne : (R : ℝ) ≠ 0 := hRpos.ne'
          have : R * (2 * R)⁻¹ = R / (2 * R) := by simp [div_eq_mul_inv]
          rw [this]
          field_simp [hRne]
        have hnorm : ‖z / vaa p‖ = ‖z‖ * ‖vaa p‖⁻¹ := by
          simp [div_eq_mul_inv]
        have hzlt : ‖z / vaa p‖ < (1 / 2 : ℝ) := by
          calc
            ‖z / vaa p‖ = ‖z‖ * ‖vaa p‖⁻¹ := hnorm
            _ < R * (2 * R)⁻¹ := hlt
            _ = (1 / 2 : ℝ) := hRhalf
        exact le_of_lt hzlt
      have hE : ‖vae m (z / vaa p) - 1‖ ≤
            4 * ‖z / vaa p‖ ^ (m + 1) :=
        vbf (m := m) (z := z / vaa p) hz_div
      have hz_pow : ‖z / vaa p‖ ^ (m + 1) ≤
            (R ^ (m + 1)) * (‖vaa p‖⁻¹ ^ (m + 1)) := by
        have : ‖z / vaa p‖ = ‖z‖ * ‖vaa p‖⁻¹ := by
          simp [div_eq_mul_inv]
        rw [this]
        have : (‖z‖ * ‖vaa p‖⁻¹) ^ (m + 1) =
            ‖z‖ ^ (m + 1) * (‖vaa p‖⁻¹ ^ (m + 1)) := by
          simp [mul_pow]
        rw [this]
        have hzle_pow : ‖z‖ ^ (m + 1) ≤ R ^ (m + 1) :=
          pow_le_pow_left₀ (norm_nonneg z) hzle (m + 1)
        gcongr
      dsimp [g, term, u]
      simp [vam, hpF] at *
      nlinarith [hE, hz_pow]
  have hcts : ∀ p, ContinuousOn (g p) K := by
    intro p
    by_cases hpF : p ∈ vad (f := f) z₀
    · have hval : vaa p = z₀ :=
        (vai (f := f) (z₀ := z₀) p).1 hpF
      simpa [g, term, vam, hval, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] using
        (continuousOn_const : ContinuousOn (fun _ : ℂ => (0 : ℂ)) K)
    · have hvalne : vaa p ≠ z₀ :=
        (vcf (f := f) z₀ p).1 hpF
      have hcontE : Continuous (fun z : ℂ => vae m z) :=
        (vaB m).continuous
      have hdiv : Continuous fun z : ℂ => z / vaa p := by
        simpa [div_eq_mul_inv] using! (continuous_id.mul continuous_const)
      have hcont : Continuous fun z : ℂ => vae m (z / vaa p) :=
        hcontE.comp hdiv
      have : ContinuousOn (fun z : ℂ => vae m (z / vaa p) - 1) K :=
        (hcont.continuousOn.sub continuous_const.continuousOn)
      simpa [g, term, vam, vai, hvalne] using this
  have hprod :
      HasProdUniformlyOn (fun p z ↦ 1 + g p z) (fun z ↦ ∏' p, (1 + g p z)) K := by
    simpa using
      Summable.hasProdUniformlyOn_one_add (f := g) (u := u) (K := K) hK hu hBound hcts
  have hterm :
      HasProdUniformlyOn (fun p z ↦ term p z) (fun z ↦ ∏' p, term p z) K := by
    simpa [g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hprod
  refine hterm.congr_right ?_
  intro z hz
  simp [term, vaf, vam]
theorem vbq
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1))) :
    HasProdLocallyUniformlyOn
      (fun (p : vab f (Set.univ : Set ℂ)) (z : ℂ) =>
        vam m f z₀ p z)
      (vaf m f z₀)
      (Set.univ : Set ℂ) := by
  refine hasProdLocallyUniformlyOn_of_forall_compact
      (f := fun p z => vam m f z₀ p z)
      (g := vaf m f z₀) (s := (Set.univ : Set ℂ))
      isOpen_univ ?_
  intro K hKU hK
  simpa using
    (vbz (m := m) (f := f) (z₀ := z₀)
      (K := K) hK h_sum)
theorem vaK
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1))) :
    TendstoLocallyUniformlyOn
      (fun s : Finset (vab f (Set.univ : Set ℂ)) =>
        vah m f z₀ s)
      (vaf m f z₀)
      Filter.atTop
      (Set.univ : Set ℂ) := by
  have hprod :
      HasProdLocallyUniformlyOn
        (fun (p : vab f (Set.univ : Set ℂ)) (z : ℂ) =>
          vam m f z₀ p z)
        (vaf m f z₀)
        (Set.univ : Set ℂ) :=
    vbq (m := m) (f := f)
      (z₀ := z₀) h_sum
  have h :
      TendstoLocallyUniformlyOn
        (fun (s : Finset (vab f (Set.univ : Set ℂ))) (z : ℂ) =>
          ∏ p ∈ s,
            if vaa p = z₀ then (1 : ℂ)
            else vae m (z / vaa p))
        (vaf m f z₀)
        Filter.atTop
        (Set.univ : Set ℂ) := by
    simpa [HasProdLocallyUniformlyOn, vam, vai]
      using hprod
  refine h.congr (G := fun s z => vah m f z₀ s z) ?_
  intro s z hz
  simp [vdQ]
theorem vaW
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1))) :
    DifferentiableOn ℂ (vaf m f z₀) (Set.univ : Set ℂ) := by
  have hloc :
      TendstoLocallyUniformlyOn
        (fun s : Finset (vab f (Set.univ : Set ℂ)) =>
          vah m f z₀ s)
        (vaf m f z₀)
        Filter.atTop
        (Set.univ : Set ℂ) :=
    vaK (m := m) (f := f)
      (z₀ := z₀) h_sum
  have hF :
      ∀ᶠ s : Finset (vab f (Set.univ : Set ℂ)) in Filter.atTop,
        DifferentiableOn ℂ (vah m f z₀ s) (Set.univ : Set ℂ) := by
    refine Filter.Eventually.of_forall ?_
    intro s
    exact (vct m f z₀ s).differentiableOn
  have : (Filter.atTop : Filter (Finset (vab f (Set.univ : Set ℂ)))).NeBot :=
    Filter.atTop_neBot
  exact hloc.differentiableOn hF isOpen_univ
lemma vbH
    (m : ℕ) (f : ℂ → ℂ) (z₀ z : ℂ)
    (s : Finset (vab f (Set.univ : Set ℂ)))
    (hs : vad (f := f) z₀ ⊆ s) :
    vag m f s z =
      vag m f (vad (f := f) z₀) z *
        vah m f z₀ s z := by
  classical
  let fiber : Finset (vab f (Set.univ : Set ℂ)) :=
    vad (f := f) z₀
  let P : vab f (Set.univ : Set ℂ) → Prop := fun p => p ∈ fiber
  let term : vab f (Set.univ : Set ℂ) → ℂ :=
    fun p => vae m (z / vaa p)
  have hfilter : s.filter P = fiber := by
    ext p
    constructor
    · intro hp
      exact (Finset.mem_filter.mp hp).2
    · intro hp
      exact Finset.mem_filter.mpr ⟨hs hp, hp⟩
  have hsplit :
      (∏ p ∈ s with P p, term p) * (∏ p ∈ s with ¬ P p, term p) = ∏ p ∈ s, term p := by
    simpa [term] using
      (Finset.prod_filter_mul_prod_filter_not (s := s) (p := P) (f := term))
  have hP : (∏ p ∈ s with P p, term p) = vag m f fiber z := by
    have hg : ∀ x ∈ s \ fiber, (if x ∈ fiber then term x else (1 : ℂ)) = 1 := by
      intro x hx
      have hxnot : x ∉ fiber := (Finset.mem_sdiff.mp hx).2
      simp [hxnot]
    have hfg :
        ∀ x ∈ fiber, term x = (if x ∈ fiber then term x else (1 : ℂ)) := by
      intro x hx
      simp [hx]
    have hsub := (Finset.prod_subset_one_on_sdiff (s₁ := fiber) (s₂ := s)
        (f := term) (g := fun x => if x ∈ fiber then term x else (1 : ℂ)) hs hg hfg)
    simpa [vag, term, P, fiber, Finset.prod_filter] using hsub.symm
  have hnotP : (∏ p ∈ s with ¬ P p, term p) = vah m f z₀ s z := by
    simp [vah, vam, term, P, fiber,
      Finset.prod_filter, vai]
  have hsplit' : ∏ p ∈ s, term p = (∏ p ∈ s with P p, term p) * (∏ p ∈ s with ¬ P p, term p) :=
    hsplit.symm
  calc
    vag m f s z
        = ∏ p ∈ s, term p := by simp [vag, term]
    _ = (∏ p ∈ s with P p, term p) * (∏ p ∈ s with ¬ P p, term p) := hsplit'
    _ = vag m f fiber z * vah m f z₀ s z := by
      simp [hP, hnotP, fiber]
end Complex.Hadamard
end
section
noncomputable section
open Complex Filter Function Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
theorem vbl
    (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (vab f (Set.univ : Set ℂ))) (z₀ : ℂ) :
    analyticOrderAt (fun z : ℂ => ∏ p ∈ s, vae m (z / vaa p))
        z₀ = ((s.filter (fun p => vaa p = z₀)).card : ℕ∞) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp [analyticOrderAt_eq_zero]
  · intro p s hp hs
    by_cases hEq : vaa p = z₀
    · have hp0 : vaa p ≠ 0 := p.property
      have han_fac :
          AnalyticAt ℂ (fun z : ℂ => vae m (z / vaa p)) z₀ := by
        exact (vax m p).analyticAt z₀
      have han_rest : AnalyticAt ℂ (fun z : ℂ => ∏ q ∈ s, vae m
          (z / vaa q)) z₀ := by
        simpa [vag] using! vbo m f s z₀
      let fac : ℂ → ℂ := fun z : ℂ => vae m (z / vaa p)
      let rest : ℂ → ℂ := fun z : ℂ => ∏ q ∈ s, vae m (z / vaa q)
      have hmul :
          analyticOrderAt (fac * rest) z₀ =
            analyticOrderAt fac z₀ + analyticOrderAt rest z₀ := by
        simpa [fac, rest] using (analyticOrderAt_mul (z₀ := z₀) han_fac han_rest)
      have hcard :
          (Finset.filter (fun q => vaa q = z₀) (insert p s)).card =
            (Finset.filter (fun q => vaa q = z₀) s).card + 1 := by
        simp [hEq, hp, Finset.filter_insert]
      have hfac : analyticOrderAt fac z₀ = (1 : ℕ∞) := by
        simpa [fac, hEq] using
          (vcR (m := m) (a := vaa p) hp0)
      have hrest : analyticOrderAt rest z₀ = ((s.filter
          (fun q => vaa q = z₀)).card : ℕ∞) := by
        simpa [rest] using hs
      have hcongr :
          (fun z : ℂ => ∏ q ∈ insert p s, vae m (z / vaa q))
            =ᶠ[𝓝 z₀] (fac * rest) := by
        refine Filter.Eventually.of_forall ?_
        intro z
        simp [fac, rest, Finset.prod_insert, hp, Pi.mul_apply]
      calc
        analyticOrderAt (fun z : ℂ => ∏ q ∈ insert p s, vae m
            (z / vaa q)) z₀ = analyticOrderAt (fac * rest) z₀ := by
              simpa using (analyticOrderAt_congr hcongr)
        _ = analyticOrderAt fac z₀ + analyticOrderAt rest z₀ := hmul
        _ = (1 : ℕ∞) + ((s.filter (fun q => vaa q = z₀)).card : ℕ∞) := by
              simp [hfac, hrest]
        _ = (((insert p s).filter (fun q => vaa q = z₀)).card : ℕ∞) := by
              simp [hcard, Nat.add_comm]
    · have han_fac :
          AnalyticAt ℂ (fun z : ℂ => vae m (z / vaa p)) z₀ := by
        exact (vax m p).analyticAt z₀
      have hfac0 : analyticOrderAt (fun z : ℂ => vae m
          (z / vaa p)) z₀ = 0 := by
        have hp0 : vaa p ≠ 0 := p.property
        have hval : vae m (z₀ / vaa p) ≠ 0 := by
          have : (z₀ / vaa p) ≠ 1 := by
            intro h1
            have : z₀ = vaa p := by
              have : z₀ = (z₀ / vaa p) * (vaa p) := by
                simp [div_eq_mul_inv]
              simpa [h1, div_eq_mul_inv, hp0] using this
            exact hEq (this.symm)
          exact (vcH m (z₀ / vaa p)).2 this
        simpa using (han_fac.analyticOrderAt_eq_zero).2 (by simpa using hval)
      have hcard :
          (Finset.filter (fun q => vaa q = z₀) (insert p s)).card =
            (Finset.filter (fun q => vaa q = z₀) s).card := by
        simp [hEq, Finset.filter_insert]
      have han_rest : AnalyticAt ℂ (fun z : ℂ => ∏ q ∈ s, vae m
          (z / vaa q)) z₀ := by
        simpa [vag] using! vbo m f s z₀
      let fac : ℂ → ℂ := fun z : ℂ => vae m (z / vaa p)
      let rest : ℂ → ℂ := fun z : ℂ => ∏ q ∈ s, vae m (z / vaa q)
      have hmul :
          analyticOrderAt (fac * rest) z₀ =
            analyticOrderAt fac z₀ + analyticOrderAt rest z₀ := by
        simpa [fac, rest] using (analyticOrderAt_mul (z₀ := z₀) han_fac han_rest)
      have hcongr :
          (fun z : ℂ => ∏ q ∈ insert p s, vae m (z / vaa q))
            =ᶠ[𝓝 z₀] (fac * rest) := by
        refine Filter.Eventually.of_forall ?_
        intro z
        simp [fac, rest, Finset.prod_insert, hp, Pi.mul_apply]
      calc
        analyticOrderAt (fun z : ℂ => ∏ q ∈ insert p s, vae m
        (z / vaa q)) z₀
            = analyticOrderAt (fac * rest) z₀ := by
              simpa using (analyticOrderAt_congr hcongr)
        _ = analyticOrderAt rest z₀ := by
              calc
                analyticOrderAt (fac * rest) z₀ = analyticOrderAt fac z₀ +
                    analyticOrderAt rest z₀ := hmul
                _ = analyticOrderAt rest z₀ := by
                      have hfac0' : analyticOrderAt fac z₀ = 0 := by
                        simpa [fac] using hfac0
                      simp [hfac0']
        _ = ((s.filter (fun q => vaa q = z₀)).card : ℕ∞) := by
              simpa [rest] using hs
        _ = (((insert p s).filter (fun q => vaa q = z₀)).card : ℕ∞) := by
              simpa using congrArg (fun n : ℕ => (n : ℕ∞)) hcard.symm
theorem vbO
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (vab f (Set.univ : Set ℂ)))
    (hs : vad (f := f) z₀ ⊆ s) :
    analyticOrderAt
        (fun z : ℂ => ∏ p ∈ s, vae m (z / vaa p))
        z₀ = ((vad (f := f) z₀).card : ℕ∞) := by
  have h :=
    vbl
      (m := m) (f := f) (s := s) (z₀ := z₀)
  have hfilter :
      s.filter (fun p => vaa p = z₀) =
        vad (f := f) z₀ := by
    ext p
    constructor
    · intro hp'
      have hpv : vaa p = z₀ := (Finset.mem_filter.mp hp').2
      simpa [vai] using hpv
    · intro hp_fiber
      have hpv : vaa p = z₀ :=
        (vai (f := f) (z₀ := z₀) p).1 hp_fiber
      have hps : p ∈ s := hs (by simpa [vai] using hpv)
      exact Finset.mem_filter.2 ⟨hps, hpv⟩
  simpa [hfilter] using h
theorem vbt
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (vab f (Set.univ : Set ℂ)))
    (hs : vad (f := f) z₀ ⊆ s) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
        (fun z : ℂ => ∏ p ∈ s, vae m (z / vaa p))
          =ᶠ[𝓝 z₀]
          fun z : ℂ => (z - z₀) ^ (vad (f := f) z₀).card • g z := by
  let F : ℂ → ℂ := fun z : ℂ => ∏ p ∈ s, vae m (z / vaa p)
  have hF_ana : AnalyticAt ℂ F z₀ := by
    simpa [F, vag] using! vbo m f s z₀
  have hOrder :
      analyticOrderAt F z₀ =
        ((vad (f := f) z₀).card : ℕ∞) := by
    simpa [F] using
      (vbO (m := m)
      (f := f) (z₀ := z₀) (s := s) hs)
  refine (hF_ana.analyticOrderAt_eq_natCast (n := (vad
    (f := f) z₀).card)).1 ?_
  simp [hOrder]
end Complex.Hadamard
end
end
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
theorem vbU
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1))) :
    TendstoLocallyUniformlyOn
      (fun s : Finset (vab f (Set.univ : Set ℂ)) => vag m f s)
      (vac m f (Set.univ : Set ℂ))
      Filter.atTop
      (Set.univ : Set ℂ) := by
  have hprod :
      HasProdLocallyUniformlyOn
        (fun (p : vab f (Set.univ : Set ℂ)) (z : ℂ) =>
          vae m (z / vaa p))
        (vac m f (Set.univ : Set ℂ))
        (Set.univ : Set ℂ) :=
    vav (m := m) (f := f) h_sum
  simpa [HasProdLocallyUniformlyOn, vag] using! hprod
theorem vbS
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) {K : Set ℂ} (hK : IsCompact K) (hKz : ∀ z ∈ K, z ≠ z₀) :
    TendstoUniformlyOn
      (fun s z => (vag m f s z) / (z - z₀) ^ k)
      (fun z => (vac m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
      (Filter.atTop : Filter (Finset (vab f (Set.univ : Set ℂ))))
      K := by
  have hloc :
      TendstoLocallyUniformlyOn
        (fun s : Finset (vab f (Set.univ : Set ℂ)) => vag m f s)
        (vac m f (Set.univ : Set ℂ))
        Filter.atTop
        K :=
    (vbU (m := m) (f := f) h_sum).mono
      (by intro z hz; simp)
  have hunif :
      TendstoUniformlyOn
        (fun s : Finset (vab f (Set.univ : Set ℂ)) => vag m f s)
        (vac m f (Set.univ : Set ℂ))
        Filter.atTop
        K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1 hloc
  let h : ℂ → ℂ := fun z => ((z - z₀) ^ k)⁻¹
  have hh : ∃ C, ∀ z ∈ K, ‖h z‖ ≤ C := by
    have hcont : ContinuousOn h K := by
      have hpow : ContinuousOn (fun z : ℂ => (z - z₀) ^ k) K := by
        fun_prop
      refine hpow.inv₀ ?_
      intro z hz
      have hz0 : z - z₀ ≠ 0 := sub_ne_zero.mpr (hKz z hz)
      exact pow_ne_zero k hz0
    have hKimg : IsCompact (h '' K) := hK.image_of_continuousOn hcont
    rcases (isBounded_iff_forall_norm_le.1 hKimg.isBounded) with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro z hz
    exact hC (h z) ⟨z, hz, rfl⟩
  have hunif' :=
    (TendstoUniformlyOn.vhF (p := (Filter.atTop : Filter (Finset (vab f
    (Set.univ : Set ℂ)))))
        (K := K)
        (F := fun s z => vag m f s z)
        (f := fun z => vac m f (Set.univ : Set ℂ) z)
        (h := h)
        hunif hh)
  simpa [h, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hunif'
theorem vaN
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) :
    TendstoLocallyUniformlyOn
      (fun s z => (vag m f s z) / (z - z₀) ^ k)
      (fun z => (vac m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
      (Filter.atTop : Filter (Finset (vab f (Set.univ : Set ℂ))))
      ((Set.univ : Set ℂ) \ {z₀}) := by
  have hopen : IsOpen ((Set.univ : Set ℂ) \ {z₀}) := by
    have hset : ((Set.univ : Set ℂ) \ {z₀}) = ({z₀} : Set ℂ)ᶜ := by
      ext z
      simp
    simp [hset]
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).2 ?_
  intro K hKsub hK
  have hKz : ∀ z ∈ K, z ≠ z₀ := by
    intro z hzK
    have : z ∈ (Set.univ : Set ℂ) \ {z₀} := hKsub hzK
    exact by simpa [Set.mem_sdiff, Set.mem_singleton_iff] using this.2
  exact vbS
    (m := m) (f := f) h_sum (z₀ := z₀) (k := k) (hK := hK) hKz
open Filter
theorem vba
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    ∃ ε > 0, ∃ u : ℂ → ℂ, AnalyticAt ℂ u z₀ ∧
      u z₀ ≠ 0 ∧
        ∀ z : ℂ, z ∈ Metric.ball z₀ ε → z ≠ z₀ →
          (vac m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (vad (f := f) z₀).card =
            (vaf m f z₀ z) * u z := by
  let fiber : Finset (vab f (Set.univ : Set ℂ)) :=
    vad (f := f) z₀
  have hfib : ∃ u : ℂ → ℂ, AnalyticAt ℂ u z₀ ∧ u z₀ ≠ 0 ∧
          (fun z : ℂ => vag m f fiber z) =ᶠ[𝓝 z₀]
            fun z : ℂ => (z - z₀) ^ fiber.card • u z := by
    simpa [fiber, vag] using
      (vbt (m := m) (f := f) (z₀ := z₀)
        (s := fiber) (by rfl : fiber ⊆ fiber))
  rcases hfib with ⟨u, huA, hu0, huEq⟩
  have hmem : {z : ℂ | vag m f fiber z =
      (z - z₀) ^ fiber.card • u z} ∈ 𝓝 z₀ := huEq
  rcases Metric.mem_nhds_iff.1 hmem with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, u, huA, hu0, ?_⟩
  have hq :
      TendstoLocallyUniformlyOn (fun s z => (vag m f s z) / (z - z₀) ^ fiber.card)
        (fun z => (vac m f (Set.univ : Set ℂ) z) / (z - z₀) ^ fiber.card)
        (Filter.atTop : Filter (Finset (vab f (Set.univ : Set ℂ))))
        ((Set.univ : Set ℂ) \ {z₀}) :=
    vaN
      (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀) (k := fiber.card)
  have hcomp :
      TendstoLocallyUniformlyOn
        (fun s : Finset (vab f (Set.univ : Set ℂ)) =>
          vah m f z₀ s)
        (vaf m f z₀)
        Filter.atTop
        (Set.univ : Set ℂ) :=
    vaK (m := m) (f := f)
    (z₀ := z₀) h_sum
  intro z hz hzne
  have hz' : z ∈ ((Set.univ : Set ℂ) \ {z₀}) := by
    refine ⟨by simp, ?_⟩
    simpa [Set.mem_singleton_iff] using hzne
  have hF : Tendsto (fun s : Finset (vab f (Set.univ : Set ℂ)) =>
          (vag m f s z) / (z - z₀) ^ fiber.card) (Filter.atTop : Filter _)
        (𝓝 ((vac m f (Set.univ : Set ℂ) z) / (z - z₀) ^ fiber.card)) :=
    hq.tendsto_at hz'
  have hG0 : Tendsto  (fun s : Finset (vab f (Set.univ : Set ℂ)) =>
          vah m f z₀ s z) (Filter.atTop : Filter _)
        (𝓝 (vaf m f z₀ z)) :=
    hcomp.tendsto_at (by simp : z ∈ (Set.univ : Set ℂ))
  have hG : Tendsto (fun s : Finset (vab f (Set.univ : Set ℂ)) =>
          (vah m f z₀ s z) * u z) (Filter.atTop : Filter _)
        (𝓝 ((vaf m f z₀ z) * u z)) :=
    (hG0.mul tendsto_const_nhds)
  have hsub : ∀ᶠ s : Finset (vab f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      fiber ⊆ s := vdS (f := f) z₀
  have heq_eventually :
      ∀ᶠ s : Finset (vab f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
        (vag m f s z) / (z - z₀) ^ fiber.card
          = (vah m f z₀ s z) * u z := by
    filter_upwards [hsub] with s hs
    have hsplit :
        vag m f s z =
          vag m f fiber z * vah m f z₀ s z := by
      simpa [fiber] using
        (vbH (m := m) (f := f) (z₀ := z₀)
          (z := z) (s := s) hs)
    have hfibz :
        vag m f fiber z = (z - z₀) ^ fiber.card • u z := by
      exact hball hz
    have hzpow : (z - z₀) ^ fiber.card ≠ 0 :=
      pow_ne_zero _ (sub_ne_zero.mpr hzne)
    set a : ℂ := (z - z₀) ^ fiber.card
    have ha : a ≠ 0 := by simpa [a] using hzpow
    set c : ℂ := vah m f z₀ s z with hc
    rw [hsplit, hfibz, smul_eq_mul]
    calc
      ((a * u z) * c) / a
          = (a * (u z * c)) / a := by simp [mul_assoc]
      _ = u z * c := by
            simpa [mul_assoc] using (mul_div_cancel_left₀ (u z * c) ha)
      _ = c * u z := by ac_rfl
      _ = (vah m f z₀ s z) * u z := by
            simp [c]
  have hG' :
      Tendsto
        (fun s : Finset (vab f (Set.univ : Set ℂ)) =>
          (vag m f s z) / (z - z₀) ^ fiber.card)
        (Filter.atTop : Filter _)
        (𝓝 ((vaf m f z₀ z) * u z)) := by
    have heq' :
        ∀ᶠ s : Finset (vab f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
          (vah m f z₀ s z) * u z
            = (vag m f s z) / (z - z₀) ^ fiber.card := by
      filter_upwards [heq_eventually] with s hs
      exact hs.symm
    exact (hG.congr' heq')
  exact tendsto_nhds_unique hF hG'
theorem vbw
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) : ∃ r > 0, BddAbove (norm ∘ (fun z : ℂ =>
      (vac m f (Set.univ : Set ℂ) z) /
        (z - z₀) ^ (vad (f := f) z₀).card) ''
      ((Metric.ball z₀ r) \ {z₀})) := by
  rcases vba (m := m) (f := f) (h_sum := h_sum)
    (z₀ := z₀) with ⟨ε, hε, u, huA, hu0, hEq⟩
  have huC : ContinuousAt u z₀ := huA.continuousAt
  have hpre : {z : ℂ | ‖u z - u z₀‖ < 1} ∈ 𝓝 z₀ := by
    have : u ⁻¹' Metric.ball (u z₀) (1 : ℝ) ∈ 𝓝 z₀ :=
      huC.preimage_mem_nhds (Metric.ball_mem_nhds (u z₀) (by norm_num))
    simpa [Metric.ball, dist_eq_norm, Set.preimage] using this
  rcases Metric.mem_nhds_iff.1 hpre with ⟨r0, hr0pos, hr0sub⟩
  set r : ℝ := min (ε / 2) r0
  have hrpos : 0 < r := lt_min (by nlinarith [hε]) hr0pos
  have hr_lt_ε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by nlinarith [hε])
  have huBound : ∀ z ∈ Metric.ball z₀ r, ‖u z‖ ≤ ‖u z₀‖ + 1 := by
    intro z hz
    have hz0 : z ∈ Metric.ball z₀ r0 := by
      have : r ≤ r0 := min_le_right _ _
      exact Metric.ball_subset_ball this hz
    have hdiff : ‖u z - u z₀‖ < 1 := hr0sub hz0
    have htri : ‖u z‖ ≤ ‖u z - u z₀‖ + ‖u z₀‖ := by
      simpa [sub_eq_add_neg, add_assoc] using
        (norm_add_le (u z - u z₀) (u z₀))
    have : ‖u z‖ ≤ 1 + ‖u z₀‖ := le_trans htri (by nlinarith [le_of_lt hdiff])
    nlinarith [this]
  have hdiffC :
      DifferentiableOn ℂ (vaf m f z₀) (Set.univ : Set ℂ) :=
    vaW (m := m) (f := f) (z₀ := z₀) h_sum
  have hcontC : ContinuousOn (vaf m f z₀) (Metric.closedBall z₀ r) :=
    (hdiffC.continuousOn).mono (by intro z hz; simp)
  have hK : IsCompact (Metric.closedBall z₀ r) := isCompact_closedBall _ _
  rcases (isBounded_iff_forall_norm_le.1 (hK.image_of_continuousOn hcontC).isBounded) with ⟨C, hC⟩
  refine ⟨r, hrpos, ⟨C * (‖u z₀‖ + 1), ?_⟩⟩
  rintro _ ⟨z, hzset, rfl⟩
  rcases hzset with ⟨hzr, hzne⟩
  have hz_in_ε : z ∈ Metric.ball z₀ ε := Metric.ball_subset_ball hr_lt_ε.le hzr
  have hz_ne : z ≠ z₀ := by simpa [Set.mem_singleton_iff] using hzne
  have hq :
      (vac m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (vad (f := f) z₀).card
        = vaf m f z₀ z * u z :=
    hEq z hz_in_ε hz_ne
  have hCz : ‖vaf m f z₀ z‖ ≤ C := by
    have hzK : z ∈ Metric.closedBall z₀ r := Metric.mem_closedBall.2 (le_of_lt hzr)
    exact hC _ ⟨z, hzK, rfl⟩
  have huZ : ‖u z‖ ≤ ‖u z₀‖ + 1 := huBound z hzr
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) hCz
  have hmul : ‖vaf m f z₀ z * u z‖ ≤ C * (‖u z₀‖ + 1) := by
    calc
      ‖vaf m f z₀ z * u z‖
          = ‖vaf m f z₀ z‖ * ‖u z‖ := by simp
      _ ≤ C * (‖u z₀‖ + 1) := by
            exact mul_le_mul hCz huZ (norm_nonneg _) hCnonneg
  simpa [Function.comp, hq] using hmul
theorem vcG
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1))) :
    vaf m f z₀ z₀ ≠ 0 := by
  let Φ : vab f (Set.univ : Set ℂ) → ℂ :=
    fun p => if vaa p = z₀ then (1 : ℂ)
      else vae m (z₀ / vaa p)
  let a : vab f (Set.univ : Set ℂ) → ℂ := fun p => Φ p - 1
  have hΦ_ne : ∀ p, Φ p ≠ 0 := by
    intro p
    by_cases hp : vaa p = z₀
    · simp [Φ, hp]
    · have hval : vaa p ≠ z₀ := hp
      have hz : z₀ / vaa p ≠ (1 : ℂ) := by
        intro h
        by_cases hp0 : vaa p = 0
        · have : z₀ / vaa p = (0 : ℂ) := by simp [hp0]
          have h01 := h
          rw [this] at h01
          exact (show False from (by simpa using (show (0 : ℂ) ≠ (1 : ℂ) from by simp) h01))
        · have : z₀ = vaa p := (div_eq_one_iff_eq hp0).1 h
          exact hval this.symm
      have hE : vae m (z₀ / vaa p) ≠ 0 := by
        intro h0
        have : z₀ / vaa p = (1 : ℂ) :=
          (vbb (m := m) (z := z₀ / vaa p)).1 h0
        exact hz this
      simp [Φ, hp, hE]
  have hz0_le : ‖z₀‖ ≤ max ‖z₀‖ 1 := le_max_left _ _
  set R : ℝ := max ‖z₀‖ 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  let u : vab f (Set.univ : Set ℂ) → ℝ :=
    fun p => (4 * R ^ (m + 1)) * (‖vaa p‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * R ^ (m + 1))
  have h_big :
      ∀ᶠ p : vab f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖vaa p‖ := by
    have hfin : ({p : vab f (Set.univ : Set ℂ) | ‖vaa p‖ ≤
        2 * R} : Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact vat (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖vaa p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this
  have hBound :
      ∀ᶠ p in Filter.cofinite, ‖a p‖ ≤ u p := by
    filter_upwards [h_big] with p hp
    have ha_pos : 0 < ‖vaa p‖ := lt_trans (by nlinarith [hRpos]) hp
    have hz_div : ‖z₀ / vaa p‖ ≤ (1 / 2 : ℝ) := by
      have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hRpos]
      have hinv : ‖vaa p‖⁻¹ < (2 * R)⁻¹ := by
        simpa [one_div] using (one_div_lt_one_div_of_lt h2R_pos hp)
      have hmul_le : ‖z₀‖ * ‖vaa p‖⁻¹ ≤ R * ‖vaa p‖⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (norm_nonneg _))
        exact hz0_le
      have hmul_lt : R * ‖vaa p‖⁻¹ < R * (2 * R)⁻¹ :=
        mul_lt_mul_of_pos_left hinv hRpos
      have hlt : ‖z₀‖ * ‖vaa p‖⁻¹ < R * (2 * R)⁻¹ :=
        lt_of_le_of_lt hmul_le hmul_lt
      have hRhalf : R * (2 * R)⁻¹ = (1 / 2 : ℝ) := by
        have hRne : (R : ℝ) ≠ 0 := hRpos.ne'
        have : R * (2 * R)⁻¹ = R / (2 * R) := by simp [div_eq_mul_inv]
        rw [this]
        field_simp [hRne]
      have hnorm : ‖z₀ / vaa p‖ = ‖z₀‖ * ‖vaa p‖⁻¹ := by
        simp [div_eq_mul_inv]
      have hzlt : ‖z₀ / vaa p‖ < (1 / 2 : ℝ) := by
        calc
          ‖z₀ / vaa p‖ = ‖z₀‖ * ‖vaa p‖⁻¹ := hnorm
          _ < R * (2 * R)⁻¹ := hlt
          _ = (1 / 2 : ℝ) := hRhalf
      exact le_of_lt hzlt
    have hE :
        ‖vae m (z₀ / vaa p) - 1‖ ≤
          4 * ‖z₀ / vaa p‖ ^ (m + 1) :=
      vbf (m := m) (z := z₀ / vaa p) hz_div
    have hz_pow :
        ‖z₀ / vaa p‖ ^ (m + 1) ≤
          (R ^ (m + 1)) * (‖vaa p‖⁻¹ ^ (m + 1)) := by
      have : ‖z₀ / vaa p‖ = ‖z₀‖ * ‖vaa p‖⁻¹ := by
        simp [div_eq_mul_inv]
      rw [this]
      have : (‖z₀‖ * ‖vaa p‖⁻¹) ^ (m + 1) =
          ‖z₀‖ ^ (m + 1) * (‖vaa p‖⁻¹ ^ (m + 1)) := by
        simp [mul_pow]
      rw [this]
      have hzle_pow : ‖z₀‖ ^ (m + 1) ≤ R ^ (m + 1) :=
        pow_le_pow_left₀ (norm_nonneg z₀) hz0_le (m + 1)
      gcongr
    have hp_ne : vaa p ≠ z₀ := by
      intro h
      have : ‖vaa p‖ ≤ R := by
        simp [h, R]
      exact (not_lt_of_ge this) (lt_trans (by nlinarith [hRpos]) hp)
    have ha : ‖a p‖ = ‖vae m (z₀ / vaa p) - 1‖ := by
      simp [a, Φ, hp_ne, sub_eq_add_neg]
    calc
      ‖a p‖ = ‖vae m (z₀ / vaa p) - 1‖ := ha
      _ ≤ 4 * ‖z₀ / vaa p‖ ^ (m + 1) := by
            simpa [sub_eq_add_neg, add_comm] using hE
      _ ≤ 4 * (R ^ (m + 1) * (‖vaa p‖⁻¹ ^ (m + 1))) := by
            gcongr
      _ = u p := by
            simp [u, mul_assoc, mul_comm]
  have hsum_norm : Summable (fun p => ‖a p‖) := by
    refine (Summable.of_norm_bounded_eventually (E := ℝ) (f := fun p => ‖a p‖) (g := u) hu ?_)
    filter_upwards [hBound] with p hp
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (a p))] using hp
  have htprod_ne :
      (∏' p : vab f (Set.univ : Set ℂ), (1 + a p)) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable (R := ℂ) (f := a) (hf := fun p => by
      simpa [a, Φ, add_sub_cancel] using hΦ_ne p) hsum_norm
  have : (∏' p : vab f (Set.univ : Set ℂ), (1 + a p)) =
      vaf m f z₀ z₀ := by
    simp [a, Φ, vaf, vfa]
  exact by
    intro h0
    exact htprod_ne (by simpa [this] using h0)
end Complex.Hadamard
end
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
theorem vcg
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) (k : ℕ)
    (s : Finset (vab f (Set.univ : Set ℂ))) :
    DifferentiableOn ℂ (fun z : ℂ => (vag m f s z) / (z - z₀) ^ k)
      ((Set.univ : Set ℂ) \ {z₀}) := by
  have hdiff_prod : DifferentiableOn ℂ (vag m f s) (Set.univ : Set ℂ) := by
    exact (vbM m f s).differentiableOn
  have hdiff_den : DifferentiableOn ℂ (fun z : ℂ => (z - z₀) ^ k) ((Set.univ : Set ℂ) \ {z₀}) := by
    have : Differentiable ℂ (fun z : ℂ => (z - z₀) ^ k) := by
      fun_prop
    exact this.differentiableOn
  by_cases hk : k = 0
  · subst hk
    simpa [pow_zero] using! (hdiff_prod.mono (by intro z hz; exact hz.1))
  · have hne : ∀ z ∈ ((Set.univ : Set ℂ) \ {z₀}), (fun z : ℂ => (z - z₀) ^ k) z ≠ 0 := by
      intro z hz
      have hz' : z ≠ z₀ := by
        simpa [Set.mem_sdiff, Set.mem_singleton_iff] using hz.2
      exact pow_ne_zero _ (sub_ne_zero.mpr hz')
    have hdiff_inv :
        DifferentiableOn ℂ (fun z : ℂ => ((z - z₀) ^ k)⁻¹) ((Set.univ : Set ℂ) \ {z₀}) :=
      hdiff_den.inv hne
    simpa [div_eq_mul_inv] using! (hdiff_prod.mono (by intro z hz; exact hz.1)).mul hdiff_inv
theorem vbV
    (m : ℕ) (f : ℂ → ℂ) (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) : DifferentiableOn ℂ
      (fun z : ℂ => (vac m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
      ((Set.univ : Set ℂ) \ {z₀}) := by
  have hopen : IsOpen ((Set.univ : Set ℂ) \ {z₀}) := by
    have hset : ((Set.univ : Set ℂ) \ {z₀}) = ({z₀} : Set ℂ)ᶜ := by
      ext z; simp
    simp [hset]
  have hconv :=
    vaN
      (m := m) (f := f) h_sum (z₀ := z₀) (k := k)
  refine hconv.differentiableOn ?_ hopen
  refine Filter.Eventually.of_forall ?_
  intro s
  exact vcg (m := m) (f := f) (z₀ := z₀) (k := k) s
theorem vbr
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) : ∃ r > 0, DifferentiableOn ℂ (Function.update
          (fun z : ℂ => (vac m f (Set.univ : Set ℂ) z) /
            (z - z₀) ^ (vad (f := f) z₀).card) z₀
          (limUnder (𝓝[≠] z₀) (fun z : ℂ => (vac m f (Set.univ : Set ℂ) z) /
                (z - z₀) ^ (vad (f := f) z₀).card)))
        (Metric.ball z₀ r) := by
  rcases vbw (m := m) (f := f)
      (h_sum := h_sum) (z₀ := z₀) with ⟨r, hrpos, hbdd⟩
  refine ⟨r, hrpos, ?_⟩
  have hnhds : Metric.ball z₀ r ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hrpos
  have hdiff : DifferentiableOn ℂ (fun z : ℂ =>
        (vac m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (vad (f := f) z₀).card)
      ((Metric.ball z₀ r) \ {z₀}) := by
    have hglob :=
      vbV
        (m := m) (f := f) h_sum (z₀ := z₀)
        (k := (vad (f := f) z₀).card)
    refine hglob.mono ?_
    intro z hz
    exact ⟨by simp, hz.2⟩
  have hb : BddAbove (norm ∘ (fun z : ℂ => (vac m f (Set.univ : Set ℂ) z) /
      (z - z₀) ^ (vad (f := f) z₀).card) ''
    ((Metric.ball z₀ r) \ {z₀})) := hbdd
  simpa using
    (Complex.differentiableOn_update_limUnder_of_bddAbove (f := fun z : ℂ =>
        (vac m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (vad (f := f) z₀).card)
      (s := Metric.ball z₀ r) (c := z₀) hnhds hdiff hb)
theorem vbx
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) : AnalyticAt ℂ (Function.update (fun z : ℂ =>
          (vac m f (Set.univ : Set ℂ) z) /
        (z - z₀) ^ (vad (f := f) z₀).card) z₀
        (limUnder (𝓝[≠] z₀) (fun z : ℂ => (vac m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (vad (f := f) z₀).card)))
      z₀ := by
  rcases
      vbr
        (m := m) (f := f) h_sum (z₀ := z₀) with ⟨r, hrpos, hdiff⟩
  let g : ℂ → ℂ :=
    Function.update
      (fun z : ℂ =>
        (vac m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (vad (f := f) z₀).card)
      z₀
      (limUnder (𝓝[≠] z₀) fun z : ℂ =>
        (vac m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (vad (f := f) z₀).card)
  have hcont : ContinuousAt g z₀ :=
    (hdiff.differentiableAt (Metric.ball_mem_nhds z₀ hrpos)).continuousAt
  have hd :
      ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ g z := by
    have hballWithin : Metric.ball z₀ r ∈ 𝓝[≠] z₀ := by
      refine mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ?_
      refine ⟨Metric.ball z₀ r, Metric.ball_mem_nhds z₀ hrpos, ?_⟩
      intro z hz
      exact hz.1
    filter_upwards [hballWithin] with z hz
    exact (hdiff z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
  simpa [g] using Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd hcont
theorem vcb
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    ∃ q : ℂ → ℂ,
      AnalyticAt ℂ q z₀ ∧
        q z₀ =
          limUnder (𝓝[≠] z₀) (fun z : ℂ =>
            (vac m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (vad (f := f) z₀).card) ∧
        ∀ z : ℂ, z ≠ z₀ →
          q z =
            (vac m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (vad (f := f) z₀).card := by
  let q : ℂ → ℂ :=
    Function.update
      (fun z : ℂ =>
        (vac m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (vad (f := f) z₀).card)
      z₀
      (limUnder (𝓝[≠] z₀) fun z : ℂ =>
        (vac m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (vad (f := f) z₀).card)
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa [q] using
      vbx
        (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀)
  · simp [q]
  · intro z hz
    simp [q, Function.update_of_ne hz]
theorem vaU
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    analyticOrderNatAt (vac m f (Set.univ : Set ℂ)) z₀ =
      (vad (f := f) z₀).card := by
  set k : ℕ := (vad (f := f) z₀).card
  let F : ℂ → ℂ := vac m f (Set.univ : Set ℂ)
  let q0 : ℂ → ℂ := fun z => F z / (z - z₀) ^ k
  rcases vcb
      (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀) with
    ⟨q, hqA, hq_self, hq_ne⟩
  have hdiff_univ : DifferentiableOn ℂ F (Set.univ : Set ℂ) :=
    vau (m := m) (f := f) h_sum
  have han : AnalyticAt ℂ F z₀ := by
    refine (Complex.analyticAt_iff_eventually_differentiableAt).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro z
    have : DifferentiableWithinAt ℂ F (Set.univ : Set ℂ) z := hdiff_univ z (by simp)
    exact this.differentiableAt (by simp)
  rcases
      vba (m := m) (f := f) (h_sum := h_sum)
      (z₀ := z₀)
    with ⟨ε, hε, u, huA, hu0, hEq⟩
  let g : ℂ → ℂ := fun z => (vaf m f z₀ z) * u z
  have hcompDiff : DifferentiableOn ℂ (vaf m f z₀)
      (Set.univ : Set ℂ) :=
    vaW (m := m) (f := f) (z₀ := z₀) h_sum
  have hcompCont : ContinuousAt (vaf m f z₀) z₀ :=
    (hcompDiff z₀ (by simp)).differentiableAt (by simp) |>.continuousAt
  have hgCont : ContinuousAt g z₀ := (hcompCont.mul huA.continuousAt)
  have hg0 : g z₀ ≠ 0 := by
    have hcomp0 : vaf m f z₀ z₀ ≠ 0 :=
      vcG (m := m) (f := f) (z₀ := z₀) h_sum
    exact mul_ne_zero hcomp0 hu0
  have hne_mem : ∀ᶠ z in 𝓝[≠] z₀, z ∈ (({z₀} : Set ℂ)ᶜ) :=
    Filter.eventually_of_mem
      (self_mem_nhdsWithin : (({z₀} : Set ℂ)ᶜ) ∈ 𝓝[≠] z₀) (fun _ hz => hz)
  have hne : ∀ᶠ z in 𝓝[≠] z₀, z ≠ z₀ := by
    filter_upwards [hne_mem] with z hz
    simpa [Set.mem_compl_singleton_iff] using hz
  have ht_q0 : Tendsto q0 (𝓝[≠] z₀) (𝓝 (g z₀)) := by
    have hball : ∀ᶠ z in 𝓝[≠] z₀, z ∈ Metric.ball z₀ ε :=
      Filter.eventually_of_mem
        (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z₀ hε)) (fun _ hz => hz)
    have heq : q0 =ᶠ[𝓝[≠] z₀] g := by
      filter_upwards [hball, hne] with z hz hzne
      have hq := hEq z hz hzne
      simpa [q0, F, k, g, smul_eq_mul] using hq
    exact (hgCont.continuousWithinAt.tendsto.congr' heq.symm)
  have hlim : limUnder (𝓝[≠] z₀) q0 = g z₀ := ht_q0.limUnder_eq
  have hq0 : q z₀ ≠ 0 := by
    have hq_self' : q z₀ = limUnder (𝓝[≠] z₀) q0 := by
      simpa [q0, F, k] using hq_self
    have : q z₀ = g z₀ := hq_self'.trans hlim
    exact this.symm ▸ hg0
  have heq_punct : (fun z : ℂ => F z) =ᶠ[𝓝[≠] z₀] fun z : ℂ => (z - z₀) ^ k • q z := by
    filter_upwards [hne] with z hz
    have hzpow : (z - z₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz)
    have hq : q z = q0 z := by simpa [q0, F, k] using hq_ne z hz
    have hmul : (z - z₀) ^ k * q0 z = F z := by
      calc
        (z - z₀) ^ k * q0 z
            = (((z - z₀) ^ k) * F z) / ((z - z₀) ^ k) := by
                simp [q0, div_eq_mul_inv, mul_assoc]
        _ = F z := by
              simpa [mul_assoc] using (mul_div_cancel_left₀ (F z) hzpow)
    have : F z = (z - z₀) ^ k * q z := by
      calc
        F z = (z - z₀) ^ k * q0 z := hmul.symm
        _ = (z - z₀) ^ k * q z := by simp [hq]
    simpa [smul_eq_mul] using this
  have hcontF : ContinuousAt F z₀ :=
    (hdiff_univ z₀ (by simp)).differentiableAt (by simp) |>.continuousAt
  have hcontq : ContinuousAt q z₀ := hqA.continuousAt
  have h_at_z0 : F z₀ = (z₀ - z₀) ^ k • q z₀ := by
    have ht1 : Tendsto F (𝓝[≠] z₀) (𝓝 (F z₀)) := hcontF.continuousWithinAt.tendsto
    have hpow :
        Tendsto (fun z : ℂ => (z - z₀) ^ k) (𝓝[≠] z₀) (𝓝 ((z₀ - z₀) ^ k)) :=
      ((continuousAt_id.sub continuousAt_const).pow k).continuousWithinAt.tendsto
    have ht2 :
        Tendsto (fun z : ℂ => (z - z₀) ^ k • q z) (𝓝[≠] z₀)
          (𝓝 ((z₀ - z₀) ^ k • q z₀)) :=
      hpow.mul (hcontq.continuousWithinAt.tendsto)
    have ht2' : Tendsto F (𝓝[≠] z₀) (𝓝 ((z₀ - z₀) ^ k • q z₀)) :=
      ht2.congr' heq_punct.symm
    exact tendsto_nhds_unique ht1 ht2'
  have hfac : ∀ᶠ z in 𝓝 z₀, F z = (z - z₀) ^ k • q z := by
    have hball1 : Metric.ball z₀ 1 ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ (by norm_num)
    have hball1' : ∀ᶠ z in 𝓝 z₀, z ∈ Metric.ball z₀ 1 :=
      Filter.eventually_of_mem hball1 (fun _ hz => hz)
    filter_upwards [hball1'] with z _hz
    by_cases hz0 : z = z₀
    · subst hz0
      simpa using h_at_z0
    · have hzpow : (z - z₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz0)
      have hq : q z = q0 z := by simpa [q0, F, k] using hq_ne z hz0
      have hmul : (z - z₀) ^ k * q0 z = F z := by
        calc
          (z - z₀) ^ k * q0 z
              = (((z - z₀) ^ k) * F z) / ((z - z₀) ^ k) := by
                  simp [q0, div_eq_mul_inv, mul_assoc]
          _ = F z := by
                simpa [mul_assoc] using (mul_div_cancel_left₀ (F z) hzpow)
      have : F z = (z - z₀) ^ k * q z := by
        calc
          F z = (z - z₀) ^ k * q0 z := hmul.symm
          _ = (z - z₀) ^ k * q z := by simp [hq]
      simpa [smul_eq_mul] using this
  have hk' : analyticOrderAt F z₀ = k :=
    (han.analyticOrderAt_eq_natCast (n := k)).2 ⟨q, hqA, hq0, hfac⟩
  have hkNat : analyticOrderNatAt F z₀ = k := by
    simp [analyticOrderNatAt, hk']
  simpa [F, k] using hkNat
theorem vaH
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1)))
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    analyticOrderNatAt (vac m f (Set.univ : Set ℂ)) z₀ =
      analyticOrderNatAt f z₀ := by
  have hcp :
      analyticOrderNatAt (vac m f (Set.univ : Set ℂ)) z₀ =
        (vad (f := f) z₀).card :=
    vaU (m := m) (f := f) (h_sum := h_sum)
      (z₀ := z₀)
  have hfib :
      (vad (f := f) z₀).card = analyticOrderNatAt f z₀ :=
    vaA (hf := hf) (z₀ := z₀) hz₀
  simpa [hfib] using hcp
end Complex.Hadamard
end
section
namespace Complex.Hadamard
open scoped Topology
open Set
lemma vak {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0) :
    ∀ z : ℂ, analyticOrderAt f z ≠ ⊤ := by
  rcases hnot with ⟨z1, hz1⟩
  have hf_an : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) := by
    intro z hz
    exact (Differentiable.analyticAt (f := f) hf z)
  have hz1_not_top : analyticOrderAt f z1 ≠ ⊤ := by
    have : analyticOrderAt f z1 = 0 :=
      (hf.analyticAt z1).analyticOrderAt_eq_zero.2 hz1
    simp [this]
  intro z
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (hf := hf_an)
    (U := (Set.univ : Set ℂ)) (x := z1) (y := z) (by simpa using isPreconnected_univ)
    (by simp) (by simp) hz1_not_top
lemma vdk
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    {B r : ℝ} (hrpos : 0 < r) (hBr : r ≤ B) (hr_not : ∀ p : vab f (Set.univ : Set ℂ),
      ‖vaa p‖ ≤ B → r ≠ ‖vaa p‖) :
    ∀ u : ℂ, ‖u‖ = r → f u ≠ 0 := by
  intro u hur
  have hu0 : u ≠ 0 := by
    intro hu0
    subst hu0
    have : (0 : ℝ) = r := by simpa using hur
    exact (ne_of_gt hrpos) this.symm
  intro hfu0
  have hnotTop : analyticOrderAt f u ≠ ⊤ :=
    vak (f := f) hf hnot u
  have hord_ne0 : analyticOrderNatAt f u ≠ 0 := by
    intro h0
    have hEN : (analyticOrderNatAt f u : ENat) = 0 := by simp [h0]
    have hAt0 : analyticOrderAt f u = 0 := by
      have hcast : (analyticOrderNatAt f u : ENat) = analyticOrderAt f u :=
        Nat.cast_analyticOrderNatAt (f := f) (z₀ := u) hnotTop
      simpa [hcast] using hEN
    have han : AnalyticAt ℂ f u := Differentiable.analyticAt (f := f) hf u
    exact ((han.analyticOrderAt_eq_zero).1 hAt0) hfu0
  have hcard_pos : 0 < (vad (f := f) u).card := by
    have hcard :=
      vaA (hf := hf) (z₀ := u) hu0
    have : 0 < analyticOrderNatAt f u := Nat.pos_of_ne_zero hord_ne0
    simpa [hcard] using this
  rcases Finset.card_pos.mp hcard_pos with ⟨p, hp⟩
  have hpval : vaa p = u :=
    (vai (f := f) (z₀ := u) p).1 hp
  have hpB : ‖vaa p‖ ≤ B := by
    have : ‖vaa p‖ = r := by simp [hpval, hur]
    simpa [this] using hBr
  have : r ≠ ‖vaa p‖ := hr_not p hpB
  exact this (by simp [hpval, hur])
theorem vbN
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    analyticOrderAt (vac m f (Set.univ : Set ℂ)) z₀ =
      ((vad (f := f) z₀).card : ℕ∞) := by
  let F : ℂ → ℂ := vac m f (Set.univ : Set ℂ)
  have hNat :
      analyticOrderNatAt F z₀ = (vad (f := f) z₀).card := by
    simpa [F] using
      (vaU
        (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀))
  have hdiffOn : DifferentiableOn ℂ F (Set.univ : Set ℂ) := by
    simpa [F] using vau (m := m) (f := f) h_sum
  have hdiff : Differentiable ℂ F := by
    intro z
    exact (hdiffOn z (by simp)).differentiableAt (by simp)
  have hnotTop : analyticOrderAt F z₀ ≠ ⊤ :=
    vak (hf := hdiff)
      ⟨0, by simp [F, vaC]⟩ z₀
  have hcast : (analyticOrderNatAt F z₀ : ℕ∞) = analyticOrderAt F z₀ :=
    Nat.cast_analyticOrderNatAt (f := F) (z₀ := z₀) hnotTop
  have hNatCast :
      (analyticOrderNatAt F z₀ : ℕ∞) =
        ((vad (f := f) z₀).card : ℕ∞) := by
    simp [hNat]
  simpa [F, hcast] using hNatCast
theorem vbk
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1)))
    {z : ℂ} (hz : ∀ p : vab f (Set.univ : Set ℂ), z ≠ vaa p) :
    vac m f (Set.univ : Set ℂ) z ≠ 0 := by
  let F : ℂ → ℂ := vac m f (Set.univ : Set ℂ)
  have hfiber_empty : vad (f := f) z = ∅ := by
    ext p
    constructor
    · intro hp
      exact False.elim (hz p ((vai (f := f) (z₀ := z) p).1 hp).symm)
    · intro hp
      simp at hp
  have horder :
      analyticOrderAt F z = (0 : ℕ∞) := by
    have h :=
      vbN
        (m := m) (f := f) (h_sum := h_sum) (z₀ := z)
    simpa [F, hfiber_empty] using h
  have han : AnalyticAt ℂ F z := by
    refine (Complex.analyticAt_iff_eventually_differentiableAt).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro w
    exact (((vau m f h_sum) w
      (by simp)).differentiableAt (by simp))
  exact (han.analyticOrderAt_eq_zero).1 horder
theorem vbA
    {f : ℂ → ℂ} {z : ℂ}
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (2 : ℕ)))
    (hz : ∀ p : vab f (Set.univ : Set ℂ), z ≠ vaa p) :
    logDeriv (vac 1 f (Set.univ : Set ℂ)) z =
      ∑' p : vab f (Set.univ : Set ℂ),
        (1 / (z - vaa p) + 1 / vaa p) :=
  vcB h_sum hz
    (vbk 1 f h_sum hz)
end Hadamard
end Complex
end
section
open Set
open scoped ENNReal
namespace Metric
variable {X : Type*} [PseudoMetricSpace X]
variable {x : X} {r R : ℝ}
open scoped Function
variable {ι : Type*} [LinearOrder ι] [SuccOrder ι]
end Metric
namespace Metric
variable {X : Type*} [PseudoEMetricSpace X]
open scoped Function
variable {ι : Type*} [LinearOrder ι] [SuccOrder ι]
end Metric
namespace Metric
variable {X : Type*} [PseudoMetricSpace X]
variable {x : X} {r R : ℝ}
end Metric
end
section
namespace Complex.Hadamard
open Filter Topology Set Complex
open scoped BigOperators Topology
noncomputable def vaj (m : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z ^ (analyticOrderNatAt f 0) * vac m f (Set.univ : Set ℂ) z
theorem vas (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1))) :
    Differentiable ℂ (vac m f (Set.univ : Set ℂ)) := by
  intro z
  have hdiffOn :
      DifferentiableOn ℂ (vac m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
    vau (m := m) (f := f) h_sum
  exact (hdiffOn z (by simp)).differentiableAt (by simp)
theorem vaY (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1))) (z : ℂ) :
    AnalyticAt ℂ (vac m f (Set.univ : Set ℂ)) z :=
  (vas m f h_sum).analyticAt z
theorem vbD (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1))) :
    Differentiable ℂ (vaj m f) := by
  have hcprod : Differentiable ℂ (vac m f (Set.univ : Set ℂ)) := by
    exact vas m f h_sum
  simpa [vaj] using! (differentiable_id.pow (analyticOrderNatAt f 0)).mul hcprod
theorem vdJ {m : ℕ} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0) (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1))) {z : ℂ} (hz : f z ≠ 0) : vaj m f z ≠ 0 := by
  have hf_not_top : ∀ w : ℂ, analyticOrderAt f w ≠ ⊤ :=
    vak (hf := hf) hnot
  have han_f : AnalyticAt ℂ f z := hf.analyticAt z
  have horder_f : analyticOrderNatAt f z = 0 := by
    have : analyticOrderAt f z = 0 := (han_f.analyticOrderAt_eq_zero).2 hz
    have hcast : (analyticOrderNatAt f z : ℕ∞) = analyticOrderAt f z :=
      Nat.cast_analyticOrderNatAt (f := f) (z₀ := z) (hf_not_top z)
    have : (analyticOrderNatAt f z : ℕ∞) = 0 := by simp [hcast, this]
    exact_mod_cast this
  have han_cprod : AnalyticAt ℂ (vac m f (Set.univ : Set ℂ)) z := by
    exact vaY m f h_sum z
  by_cases hz0 : z = 0
  · subst hz0
    have hord0 : analyticOrderNatAt f 0 = 0 := by simpa using horder_f
    simp [vaj, hord0, vaC]
  · have hp : z ^ (analyticOrderNatAt f 0) ≠ 0 := pow_ne_zero _ hz0
    have hcprod_order :
        analyticOrderNatAt (vac m f (Set.univ : Set ℂ)) z = 0 := by
      simpa [horder_f] using
        (vaH (m := m) (hf := hf)
          (h_sum := h_sum) (z₀ := z) hz0)
    have hcprod_ne : vac m f (Set.univ : Set ℂ) z ≠ 0 := by
      have hcprod_entire :
          Differentiable ℂ (vac m f (Set.univ : Set ℂ)) := by
        exact vas m f h_sum
      have hcprod_not_top :
          analyticOrderAt (vac m f (Set.univ : Set ℂ)) z ≠ ⊤ :=
        vak (hf := hcprod_entire)
          ⟨0, by simp [vaC]⟩ z
      have hcprod_cast :
          (analyticOrderNatAt (vac m f (Set.univ : Set ℂ)) z : ℕ∞) =
            analyticOrderAt (vac m f (Set.univ : Set ℂ)) z :=
        Nat.cast_analyticOrderNatAt
          (f := vac m f (Set.univ : Set ℂ)) (z₀ := z) hcprod_not_top
      have : analyticOrderAt (vac m f (Set.univ : Set ℂ)) z = 0 := by
        have :
            (analyticOrderNatAt
              (vac m f (Set.univ : Set ℂ)) z : ℕ∞) = 0 := by
          exact_mod_cast hcprod_order
        simp [hcprod_cast] at this
        simpa using this
      exact (han_cprod.analyticOrderAt_eq_zero).1 this
    exact mul_ne_zero hp hcprod_ne
lemma vcr
    (m : ℕ) (f : ℂ → ℂ) (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1))) :
    analyticOrderNatAt (vac m f (Set.univ : Set ℂ)) 0 = 0 := by
  have hcprod_entire :
      Differentiable ℂ (vac m f (Set.univ : Set ℂ)) := by
    exact vas m f h_sum
  have hcprod_not_top :
      analyticOrderAt (vac m f (Set.univ : Set ℂ)) 0 ≠ ⊤ :=
    vak (hf := hcprod_entire)
      ⟨0, by simp [vaC]⟩ 0
  have hcprodA : AnalyticAt ℂ (vac m f (Set.univ : Set ℂ)) 0 :=
    hcprod_entire.analyticAt 0
  have hcprod0 : vac m f (Set.univ : Set ℂ) 0 ≠ 0 := by
    simp [vaC]
  have : analyticOrderAt (vac m f (Set.univ : Set ℂ)) 0 = 0 :=
    (hcprodA.analyticOrderAt_eq_zero).2 hcprod0
  have hcast :
      (analyticOrderNatAt (vac m f (Set.univ : Set ℂ)) 0 : ℕ∞) =
        analyticOrderAt (vac m f (Set.univ : Set ℂ)) 0 :=
    Nat.cast_analyticOrderNatAt
      (f := vac m f (Set.univ : Set ℂ)) (z₀ := (0 : ℂ)) hcprod_not_top
  have :
      (analyticOrderNatAt (vac m f (Set.univ : Set ℂ)) 0 : ℕ∞) =
        0 := by
    simp [hcast, this]
  exact_mod_cast this
theorem vdU
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1))) (z : ℂ) :
    analyticOrderNatAt (vaj m f) z = analyticOrderNatAt f z := by
  by_cases hz0 : z = 0
  · subst hz0
    have hpowA : AnalyticAt ℂ (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 := by
      simpa using! (analyticAt_id.pow (analyticOrderNatAt f 0))
    have hpow_not_top :
        analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 ≠ ⊤ :=
      vak
        (hf := (differentiable_id.pow (analyticOrderNatAt f 0)))
        ⟨1, by simp⟩ 0
    have hcprodA : AnalyticAt ℂ (vac m f (Set.univ : Set ℂ)) 0 := by
      exact vaY m f h_sum 0
    have hcprod0 :
        analyticOrderNatAt (vac m f (Set.univ : Set ℂ)) 0 = 0 :=
      vcr (m := m) (f := f) h_sum
    have hid0 : analyticOrderNatAt (fun z : ℂ => z) 0 = 1 := by
      have hid_entire : Differentiable ℂ (fun z : ℂ => z) := differentiable_id
      have hdiv :
          (MeromorphicOn.divisor (fun z : ℂ => z) (Set.univ : Set ℂ)) 0 =
            (analyticOrderNatAt (fun z : ℂ => z) 0 : ℤ) := by
        simpa using
          (vaw
            (f := fun z : ℂ => z) hid_entire 0)
      have hdiv1 : (MeromorphicOn.divisor (fun z : ℂ => z) (Set.univ : Set ℂ)) 0 = 1 := by
        simpa using
          (MeromorphicOn.divisor_sub_const_self (z₀ := (0 : ℂ))
            (U := (Set.univ : Set ℂ)) (by simp))
      have : (analyticOrderNatAt (fun z : ℂ => z) 0 : ℤ) = 1 := by
        simpa [hdiv] using hdiv1
      exact_mod_cast this
    have hpow0 :
        analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 =
          analyticOrderNatAt f 0 := by
      have hidA : AnalyticAt ℂ (fun z : ℂ => z) 0 := by
        simpa [id] using! (analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) 0)
      simpa [hid0] using! (analyticOrderNatAt_pow (hf := hidA) (n := analyticOrderNatAt f 0))
    have hmul :
        analyticOrderNatAt (vaj m f) 0 =
          analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 +
            analyticOrderNatAt (vac m f (Set.univ : Set ℂ)) 0 := by
      have hcprod_not_top' :
          analyticOrderAt (vac m f (Set.univ : Set ℂ)) 0 ≠ ⊤ :=
        vak
          (hf := vas m f h_sum)
          ⟨0, by simp [vaC]⟩ 0
      simpa [vaj] using!
        analyticOrderNatAt_mul (hf := hpowA) (hg := hcprodA)
          (hf' := hpow_not_top) (hg' := hcprod_not_top')
    simp [hmul, hpow0, hcprod0]
  · have hpowA : AnalyticAt ℂ (fun z : ℂ => z ^ analyticOrderNatAt f 0) z := by
      simpa using! (analyticAt_id.pow (analyticOrderNatAt f 0))
    have hpow_not_top :
        analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z ≠ ⊤ :=
      vak
        (hf := (differentiable_id.pow (analyticOrderNatAt f 0)))
        ⟨1, by simp⟩ z
    have hpow0 : analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z = 0 := by
      have hz' : (fun z : ℂ => z ^ analyticOrderNatAt f 0) z ≠ 0 := by
        simp [hz0]
      have : analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z = 0 :=
        ((hpowA).analyticOrderAt_eq_zero).2 hz'
      have hcast : (analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z : ℕ∞) =
          analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z :=
        Nat.cast_analyticOrderNatAt
          (f := fun z : ℂ => z ^ analyticOrderNatAt f 0) (z₀ := z) hpow_not_top
      have : (analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z : ℕ∞) = 0 := by
        simp [hcast, this]
      exact_mod_cast this
    have hcprod_eq :
        analyticOrderNatAt (vac m f (Set.univ : Set ℂ)) z =
          analyticOrderNatAt f z :=
      vaH
        (m := m) (hf := hf) (h_sum := h_sum) (z₀ := z) hz0
    have hcprodA : AnalyticAt ℂ (vac m f (Set.univ : Set ℂ)) z := by
      exact vaY m f h_sum z
    have hcprod_not_top :
        analyticOrderAt (vac m f (Set.univ : Set ℂ)) z ≠ ⊤ :=
      vak
        (hf := vas m f h_sum)
        ⟨0, by simp [vaC]⟩ z
    have hmul :
        analyticOrderNatAt (vaj m f) z =
          analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z +
            analyticOrderNatAt (vac m f (Set.univ : Set ℂ)) z := by
      simpa [vaj] using!
        analyticOrderNatAt_mul (hf := hpowA) (hg := hcprodA)
          (hf' := hpow_not_top) (hg' := hcprod_not_top)
    simp [hmul, hpow0, hcprod_eq]
theorem vfF
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1))) :
    MeromorphicOn.divisor (vaj m f) (Set.univ : Set ℂ) =
      MeromorphicOn.divisor f (Set.univ : Set ℂ) := by
  ext z
  have hden_entire : Differentiable ℂ (vaj m f) :=
    vbD (m := m) f h_sum
  have hf_entire : Differentiable ℂ f := hf
  have hden :
      (MeromorphicOn.divisor (vaj m f) (Set.univ : Set ℂ)) z =
        (analyticOrderNatAt (vaj m f) z : ℤ) := by
    simpa using (vaw (f := vaj m f) hden_entire z)
  have hfz :
      (MeromorphicOn.divisor f (Set.univ : Set ℂ)) z =
        (analyticOrderNatAt f z : ℤ) := by
    simpa using (vaw (f := f) hf_entire z)
  simp [hden, hfz, vdU (m := m) (hf := hf) (h_sum := h_sum) z]
theorem vel
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1))) :
    MeromorphicOn.divisor (fun z : ℂ => f z / vaj m f z) (Set.univ : Set ℂ) = 0 := by
  have hf_mero : MeromorphicOn f (Set.univ : Set ℂ) := by
    intro z hz
    exact (hf.analyticAt z).meromorphicAt
  have hden_entire : Differentiable ℂ (vaj m f) :=
    vbD (m := m) f h_sum
  have hden_mero : MeromorphicOn (vaj m f) (Set.univ : Set ℂ) := by
    intro z hz
    exact (hden_entire.analyticAt z).meromorphicAt
  rcases hnot with ⟨z1, hz1⟩
  have hden1 : vaj m f z1 ≠ 0 :=
    vdJ (m := m) (f := f) hf ⟨z1, hz1⟩ h_sum hz1
  have hf_order_ne_top : ∀ z ∈ (Set.univ : Set ℂ), meromorphicOrderAt f z ≠ ⊤ := by
    intro z hzU
    have hz1_ne_top : meromorphicOrderAt f z1 ≠ ⊤ := by
      have hfAt : MeromorphicAt f z1 := hf_mero z1 (by simp)
      have hcont : ContinuousAt f z1 := (hf.differentiableAt).continuousAt
      have hne_nhds : ∀ᶠ w in 𝓝 z1, f w ≠ 0 :=
        (hcont.ne_iff_eventually_ne continuousAt_const).1 hz1
      have hne_nhdsNE : ∀ᶠ w in 𝓝[≠] z1, f w ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds hne_nhds
      exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf := hfAt)).2 hne_nhdsNE
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf := hf_mero)
      (x := z1) (hU := isPreconnected_univ) (h₁x := by simp) (hy := by simp) hz1_ne_top
  have hden_order_ne_top :
      ∀ z ∈ (Set.univ : Set ℂ), meromorphicOrderAt (vaj m f) z ≠ ⊤ := by
    intro z hzU
    have hz1_ne_top : meromorphicOrderAt (vaj m f) z1 ≠ ⊤ := by
      have hdenAt : MeromorphicAt (vaj m f) z1 := hden_mero z1 (by simp)
      have hcont : ContinuousAt (vaj m f) z1 :=
        (hden_entire.differentiableAt).continuousAt
      have hne_nhds : ∀ᶠ w in 𝓝 z1, vaj m f w ≠ 0 :=
        (hcont.ne_iff_eventually_ne continuousAt_const).1 hden1
      have hne_nhdsNE : ∀ᶠ w in 𝓝[≠] z1, vaj m f w ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds hne_nhds
      exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf := hdenAt)).2 hne_nhdsNE
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf := hden_mero)
      (x := z1) (hU := isPreconnected_univ) (h₁x := by simp) (hy := by simp) hz1_ne_top
  have hinv_order_ne_top :
      ∀ z ∈ (Set.univ : Set ℂ),
        meromorphicOrderAt (fun z : ℂ => (vaj m f z)⁻¹) z ≠ ⊤ := by
    intro z hzU
    have hinv_mero :
        MeromorphicOn (fun z : ℂ => (vaj m f z)⁻¹) (Set.univ : Set ℂ) :=
      hden_mero.inv
    have hz1_ne_top :
        meromorphicOrderAt (fun z : ℂ => (vaj m f z)⁻¹) z1 ≠ ⊤ := by
      have hinvAt : MeromorphicAt (fun z : ℂ => (vaj m f z)⁻¹) z1 :=
        hinv_mero z1 (by simp)
      have hcont_denom : ContinuousAt (vaj m f) z1 :=
        (hden_entire.differentiableAt).continuousAt
      have hcont : ContinuousAt (fun z : ℂ => (vaj m f z)⁻¹) z1 :=
        hcont_denom.inv₀ hden1
      have hinv1 : (fun z : ℂ => (vaj m f z)⁻¹) z1 ≠ 0 := by
        simpa using inv_ne_zero hden1
      have hne_nhds :
          ∀ᶠ w in 𝓝 z1, (fun z : ℂ => (vaj m f z)⁻¹) w ≠ 0 :=
        (hcont.ne_iff_eventually_ne continuousAt_const).1 hinv1
      have hne_nhdsNE :
          ∀ᶠ w in 𝓝[≠] z1, (fun z : ℂ => (vaj m f z)⁻¹) w ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds hne_nhds
      exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf := hinvAt)).2 hne_nhdsNE
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf := hinv_mero)
      (x := z1) (hU := isPreconnected_univ) (h₁x := by simp) (hy := by simp) hz1_ne_top
  have hdiv_denom : MeromorphicOn.divisor (vaj m f) (Set.univ : Set ℂ) =
      MeromorphicOn.divisor f (Set.univ : Set ℂ) :=
    vfF (m := m) (hf := hf) (h_sum := h_sum)
  calc
    MeromorphicOn.divisor (fun z : ℂ => f z / vaj m f z) (Set.univ : Set ℂ)
        = MeromorphicOn.divisor
            (fun z : ℂ => f z * (vaj m f z)⁻¹) (Set.univ : Set ℂ) := by
            simp [div_eq_mul_inv]
    _ = MeromorphicOn.divisor f (Set.univ : Set ℂ) +
          MeromorphicOn.divisor (fun z : ℂ => (vaj m f z)⁻¹) (Set.univ : Set ℂ) := by
          simpa using (MeromorphicOn.divisor_fun_mul (U := (Set.univ : Set ℂ))
            (f₁ := f) (f₂ := fun z => (vaj m f z)⁻¹) hf_mero (hden_mero.inv)
            hf_order_ne_top hinv_order_ne_top)
    _ = MeromorphicOn.divisor f (Set.univ : Set ℂ) -
          MeromorphicOn.divisor (vaj m f) (Set.univ : Set ℂ) := by
          simp [sub_eq_add_neg]
    _ = 0 := by
          simp [hdiv_denom]
theorem vdu
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1))) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ (∀ z, H z ≠ 0) ∧ ∀ z : ℂ, f z =
      H z * z ^ (analyticOrderNatAt f 0) * vac m f (Set.univ : Set ℂ) z := by
  let denom : ℂ → ℂ := vaj m f
  let q : ℂ → ℂ := fun z => f z / denom z
  have hden_entire : Differentiable ℂ denom :=
    vbD (m := m) f h_sum
  have hq_mero : MeromorphicOn q (Set.univ : Set ℂ) := by
    intro z hzU
    have hf_m : MeromorphicAt f z := (hf.analyticAt z).meromorphicAt
    have hden_m : MeromorphicAt denom z := (hden_entire.analyticAt z).meromorphicAt
    simpa [q, denom, div_eq_mul_inv] using! (hf_m.mul hden_m.inv)
  let H : ℂ → ℂ := toMeromorphicNFOn q (Set.univ : Set ℂ)
  have hNF : MeromorphicNFOn H (Set.univ : Set ℂ) :=
    meromorphicNFOn_toMeromorphicNFOn q (Set.univ : Set ℂ)
  have hdivH : MeromorphicOn.divisor H (Set.univ : Set ℂ) = 0 := by
    have hdivq : MeromorphicOn.divisor q (Set.univ : Set ℂ) = 0 :=
      vel (m := m) (f := f) (hf := hf)
        (hnot := hnot) (h_sum := h_sum)
    simpa [H, hdivq] using
      (MeromorphicOn.divisor_of_toMeromorphicNFOn
        (f := q) (U := (Set.univ : Set ℂ)) hq_mero)
  have hA : AnalyticOnNhd ℂ H (Set.univ : Set ℂ) := by
    have :
        (0 : Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ) ≤
          MeromorphicOn.divisor H (Set.univ : Set ℂ) := by
      simp [hdivH]
    exact (MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd (h₁f := hNF)).1 (by simp [hdivH])
  have hH_entire : Differentiable ℂ H := by
    intro z
    exact (hA z (by simp)).differentiableAt
  rcases hnot with ⟨z1, hz1⟩
  have hden1 : denom z1 ≠ 0 :=
    vdJ (m := m) (f := f) hf ⟨z1, hz1⟩ h_sum hz1
  have hqA1 : AnalyticAt ℂ q z1 := by
    have hdenA1 : AnalyticAt ℂ denom z1 := hden_entire.analyticAt z1
    exact (hf.analyticAt z1).div hdenA1 hden1
  have hqNF1 : MeromorphicNFAt q z1 := hqA1.meromorphicNFAt
  have htoEq : toMeromorphicNFAt q z1 = q := (toMeromorphicNFAt_eq_self (f := q) (x := z1)).2 hqNF1
  have hH1 : H z1 = q z1 := by
    have hx : z1 ∈ (Set.univ : Set ℂ) := by simp
    have : toMeromorphicNFOn q (Set.univ : Set ℂ) z1 = toMeromorphicNFAt q z1 z1 :=
      (toMeromorphicNFOn_eq_toMeromorphicNFAt (f := q) (U := (Set.univ : Set ℂ)) hq_mero hx)
    simpa [H, htoEq] using this
  have hH1_ne : H z1 ≠ 0 := by
    have : q z1 ≠ 0 := div_ne_zero hz1 hden1
    simpa [hH1] using this
  have hH_not_top : ∀ z : ℂ, analyticOrderAt H z ≠ ⊤ := by
    exact vak (hf := hH_entire) ⟨z1, hH1_ne⟩
  have hH_orderNat_zero : ∀ z : ℂ, analyticOrderNatAt H z = 0 := by
    intro z
    have hzdiv :
        (MeromorphicOn.divisor H (Set.univ : Set ℂ)) z = (analyticOrderNatAt H z : ℤ) := by
      simpa using (vaw (f := H) hH_entire z)
    have : (MeromorphicOn.divisor H (Set.univ : Set ℂ)) z = 0 := by
      simp [hdivH]
    have : (analyticOrderNatAt H z : ℤ) = 0 := by simpa [hzdiv] using this
    exact_mod_cast this
  have hH_ne : ∀ z : ℂ, H z ≠ 0 := by
    intro z
    have hcast : (analyticOrderNatAt H z : ℕ∞) = analyticOrderAt H z :=
      Nat.cast_analyticOrderNatAt (f := H) (z₀ := z) (hH_not_top z)
    have : analyticOrderAt H z = 0 := by
      have : (analyticOrderNatAt H z : ℕ∞) = 0 := by exact_mod_cast (hH_orderNat_zero z)
      simpa [hcast] using this
    exact ((hA z (by simp)).analyticOrderAt_eq_zero).1 this
  have hfA : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) := fun z hzU => hf.analyticAt z
  have hdenA : AnalyticOnNhd ℂ denom (Set.univ : Set ℂ) := fun z hzU => hden_entire.analyticAt z
  have hprodA : AnalyticOnNhd ℂ (fun z => H z * denom z) (Set.univ : Set ℂ) :=
    (hA.mul hdenA)
  have hlocal : f =ᶠ[𝓝 z1] fun z => H z * denom z := by
    have hden_ne : ∀ᶠ z in 𝓝 z1, denom z ≠ 0 :=
      (hden_entire.differentiableAt.continuousAt.ne_iff_eventually_ne continuousAt_const).1 hden1
    have hH_eq_q : H =ᶠ[𝓝 z1] q := by
      have hx : z1 ∈ (Set.univ : Set ℂ) := by simp
      have hloc :
          toMeromorphicNFOn q (Set.univ : Set ℂ) =ᶠ[𝓝 z1] toMeromorphicNFAt q z1 := by
        simpa [H] using (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds (f := q)
          (U := (Set.univ : Set ℂ)) hq_mero hx)
      simpa [H, htoEq] using hloc
    filter_upwards [hden_ne, hH_eq_q] with z hzden hHz
    have hcancel : q z * denom z = f z := by
      dsimp [q]
      field_simp [hzden]
    calc
      f z = q z * denom z := hcancel.symm
      _ = H z * denom z := by simp [hHz]
  have hglob : f = fun z => H z * denom z :=
    AnalyticOnNhd.eq_of_eventuallyEq (hf := hfA) (hg := hprodA) hlocal
  refine ⟨H, hH_entire, hH_ne, ?_⟩
  intro z
  have hglobz : f z = H z * denom z := congrArg (fun g => g z) hglob
  simpa [denom, vaj, mul_assoc, mul_left_comm, mul_comm] using hglobz
end Complex.Hadamard
end
section
open Filter Function MeromorphicOn Metric Real Set
namespace Function.locallyFinsuppWithin
variable {E : Type*} [NormedAddCommGroup E]
lemma vaz {D : locallyFinsupp E ℤ} {r : ℝ} {z : E}
    (hz : z ∈ (toClosedBall r D).support) : ‖z‖ ≤ |r| := by
  have hz_ball : z ∈ closedBall (0 : E) |r| := (toClosedBall r D).supportWithinDomain hz
  simpa [mem_closedBall, dist_zero_right] using hz_ball
lemma vaO {D : locallyFinsupp E ℤ} {r : ℝ} {z : E}
    (hz : ‖z‖ ≤ |r|) : toClosedBall r D z = D z := by
  have hz_ball : z ∈ closedBall (0 : E) |r| := by
    simpa [mem_closedBall, dist_zero_right] using hz
  simpa using toClosedBall_eval_within (f := D) hz_ball
lemma vaX
    {D : locallyFinsupp E ℤ} {r : ℝ} {z : E} (hzD : z ∈ D.support) (hzR : ‖z‖ ≤ |r|) :
    z ∈ (toClosedBall r D).support := by
  rw [Function.mem_support]
  rw [vaO hzR]
  rwa [Function.mem_support] at hzD
lemma vdo {D : locallyFinsupp E ℤ} {r : ℝ} {z : E}
    (hz : z ∈ (toClosedBall r D).support) : z ∈ D.support := by
  have hnorm : ‖z‖ ≤ |r| := vaz hz
  rw [Function.mem_support] at hz ⊢
  rw [vaO hnorm] at hz
  exact hz
noncomputable def vbh {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (D : locallyFinsupp E ℤ) (R : ℝ) : ℝ := by
  classical
  exact
    (((finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).toFinset).filter
      (fun z => z ≠ (0 : E))).sum fun z => (D z : ℝ)
end Function.locallyFinsuppWithin
namespace Function.locallyFinsuppWithin
theorem vbp
    {R : ℝ} {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hR : R ≠ 0) :
    logCounting (divisor f ⊤) R =
      circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have hmero : Meromorphic f := fun z => (hf.analyticAt z).meromorphicAt
  simpa [top_eq_univ] using
    logCounting_divisor_eq_circleAverage_sub_const (f := f) hmero hR
end Function.locallyFinsuppWithin
end
section
namespace Real
theorem veA {x : ℝ} (hx : 0 ≤ x) :
    log (1 + exp x) ≤ x + log 2 := by
  have hexp_one : (1 : ℝ) ≤ exp x := by
    simpa using (one_le_exp_iff.2 hx)
  have hadd : 1 + exp x ≤ 2 * exp x := by linarith
  have hlog : log (1 + exp x) ≤ log (2 * exp x) :=
    log_le_log (by positivity) hadd
  calc
    log (1 + exp x) ≤ log (2 * exp x) := hlog
    _ = log 2 + x := by simp [log_mul, add_comm]
    _ = x + log 2 := by ring
theorem vdP {x y : ℝ} (hy : 0 ≤ y) (hx : 0 ≤ x)
    (hxy : y ≤ exp x) :
    log (1 + y) ≤ x + log 2 := by
  have hpos : 0 < (1 : ℝ) + y := by linarith
  have hle : (1 : ℝ) + y ≤ 1 + exp x := by linarith
  exact (log_le_log hpos hle).trans (veA hx)
theorem vfD {x y : ℝ} (hy : 0 ≤ y) (hxy : log (1 + y) ≤ x) :
    y ≤ exp x := by
  have hpos : 0 < (1 : ℝ) + y := by linarith
  have hone : 1 + y ≤ exp x := (log_le_iff_le_exp hpos).1 hxy
  linarith
theorem vgo (x : ℝ) : -log⁺ x⁻¹ ≤ log x := by
  linarith [posLog_sub_posLog_inv (x := x), posLog_nonneg (x := x)]
end Real
end
section
namespace Real
end Real
end
section
namespace Real
variable {α E : Type*} [SeminormedAddCommGroup E]
theorem veQ (w : E) :
    Real.log ‖w‖ ≤ Real.log (1 + ‖w‖) := by
  by_cases h0 : ‖w‖ = 0
  · simp [h0]
  · have hpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm h0)
    exact Real.log_le_log hpos (by linarith [norm_nonneg w])
variable {F : Type*} [NormedAddCommGroup F]
theorem veb {z : F} {r : ℝ} (hz : ‖z‖ ≤ r) :
    0 ≤ Real.log (r * ‖z‖⁻¹) := by
  by_cases hz0 : z = 0
  · simp [hz0]
  · have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have : (1 : ℝ) ≤ r * ‖z‖⁻¹ := by
      have : (1 : ℝ) ≤ r / ‖z‖ := (one_le_div hzpos).2 hz
      simpa [div_eq_mul_inv] using this
    exact Real.log_nonneg this
theorem vcu {z : F} {R : ℝ} (hz0 : z ≠ 0)
    (hz : ‖z‖ ≤ R) :
    Real.log 2 ≤ Real.log ((2 * R) * ‖z‖⁻¹) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hRdiv : (1 : ℝ) ≤ R / ‖z‖ := (one_le_div hzpos).2 hz
  have hle2 : (2 : ℝ) ≤ (2 * R) * ‖z‖⁻¹ := by
    have : (2 : ℝ) ≤ 2 * (R / ‖z‖) := by nlinarith
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  exact Real.log_le_log (by norm_num) hle2
theorem vdT
    {f : α → E} {r : α → ℝ} {C ρ τ : ℝ} (hC : 0 ≤ C) (hr : ∀ x, 1 ≤ r x) (hρτ : ρ ≤ τ)
    (hbound : ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ ρ)) : ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ τ) := by
  intro x
  refine (hbound x).trans (Real.exp_le_exp.2 ?_)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hr x) hρτ) hC
theorem ved
    {f : α → E} {r : α → ℝ} {C ρ τ : ℝ} (hC : 0 ≤ C) (hr : ∀ x, 1 ≤ r x) (hρτ : ρ ≤ τ)
    (hlog : ∀ x, Real.log (1 + ‖f x‖) ≤ C * (r x) ^ ρ) : ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ τ) := by
  intro x
  have hpow : (r x) ^ ρ ≤ (r x) ^ τ :=
    Real.rpow_le_rpow_of_exponent_le (hr x) hρτ
  have hlogτ : Real.log (1 + ‖f x‖) ≤ C * (r x) ^ τ :=
    (hlog x).trans (mul_le_mul_of_nonneg_left hpow hC)
  exact Real.vfD (norm_nonneg (f x)) hlogτ
theorem vca
    {f : α → E} {r : α → ℝ} {C τ : ℝ} (hC : 0 < C) (hτ : 0 ≤ τ)
    (hr : ∀ x, 1 ≤ r x) (hbound : ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ τ)) :
    ∃ C' > 0, ∀ x, Real.log (1 + ‖f x‖) ≤ C' * (r x) ^ τ := by
  refine ⟨C + Real.log 2, by
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith, ?_⟩
  intro x
  have hX : (1 : ℝ) ≤ (r x) ^ τ := Real.one_le_rpow (hr x) hτ
  have hB : 0 ≤ C * (r x) ^ τ :=
    mul_nonneg hC.le (Real.rpow_nonneg (le_trans zero_le_one (hr x)) _)
  have hlog :
      Real.log (1 + ‖f x‖) ≤ C * (r x) ^ τ + Real.log 2 :=
    Real.vdP (norm_nonneg _) hB (hbound x)
  have hlog2_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [hlog, hX, hlog2_nonneg]
theorem vdc
    {f : α → E} {r : α → ℝ} {τ : ℝ} {n : ℕ} (hr : ∀ x, 1 ≤ r x) (hτn : τ < (n : ℝ))
    (hbound : ∃ C > 0, ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ τ)) :
    ∃ C > 0, ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ n) := by
  rcases hbound with ⟨C, hCpos, hC⟩
  have hweak :
      ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ (n : ℝ)) :=
    vdT
      (f := f) (r := r) hCpos.le hr (le_of_lt hτn) hC
  refine ⟨C, hCpos, ?_⟩
  intro x
  have hpow : (r x) ^ (n : ℝ) = (r x) ^ n := Real.rpow_natCast (r x) n
  simpa [hpow] using hweak x
theorem vcx {x r : ℝ} (hx : 0 ≤ x)
    (hr : r ≤ 2 * max x 1) :  1 + r ≤ 3 * (1 + x) := by
  have hmax : max x 1 ≤ 1 + x := max_le_iff.2 ⟨by linarith, by linarith⟩
  nlinarith
theorem vdw
    {A B x y τ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hτ : 0 ≤ τ) (hxy : x ≤ B * y) : Real.exp (A * x ^ τ) ≤ Real.exp ((A * B ^ τ) * y ^ τ) := by
  refine Real.exp_le_exp.2 ?_
  have hpow : x ^ τ ≤ (B * y) ^ τ := Real.rpow_le_rpow hx hxy hτ
  have hsplit : (B * y) ^ τ = B ^ τ * y ^ τ := by
    simpa using (Real.mul_rpow (x := B) (y := y) (z := τ) hB hy)
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hpow.trans_eq hsplit) hA
theorem vaG {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ τ : ℝ, ρ < τ ∧ τ < (Nat.floor ρ + 1 : ℝ) ∧ 0 ≤ τ ∧ Nat.floor τ = Nat.floor ρ := by
  set m : ℕ := Nat.floor ρ
  set τ : ℝ := (ρ + (m + 1 : ℝ)) / 2
  have hm : ρ < (m + 1 : ℝ) := by simpa [m] using Nat.lt_floor_add_one (a := ρ)
  have hτ : ρ < τ := by dsimp [τ]; linarith
  have hτ_lt : τ < (m + 1 : ℝ) := by dsimp [τ]; linarith
  have hτ_nonneg : 0 ≤ τ := le_trans hρ (le_of_lt hτ)
  have hfloorτ : Nat.floor τ = m := by
    have hm_le_τ : (m : ℝ) ≤ τ := le_trans (Nat.floor_le hρ) (le_of_lt hτ)
    have hτ_lt_m1 : τ < (m : ℝ) + 1 := by simpa [add_assoc, add_comm, add_left_comm] using hτ_lt
    exact (Nat.floor_eq_iff hτ_nonneg).2 ⟨hm_le_τ, hτ_lt_m1⟩
  exact ⟨τ, hτ, by simpa [m] using hτ_lt, hτ_nonneg, by simpa [m] using hfloorτ⟩
open Metric Complex
theorem vcJ {f : ℂ → ℂ} {C ρ R : ℝ}
    (hC : ∀ z : ℂ, log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) |R|) : log ‖f z‖ ≤ C * (1 + |R|) ^ ρ := by
  have hz_norm : ‖z‖ = |R| := by
    simpa [mem_sphere, dist_zero_right] using hz
  simpa [hz_norm] using le_trans (veQ (f z)) (hC z)
end Real
end
section
open Filter Function MeromorphicOn Metric Real Set
namespace Function.locallyFinsuppWithin
theorem vdM {f : ℂ → ℂ} {ρ C : ℝ} (hf : Differentiable ℂ f)
    (hC : ∀ z : ℂ, log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) {R : ℝ} (hR0 : 0 < R) :
    logCounting (divisor f (Set.univ : Set ℂ)) R
      ≤ C * (1 + |R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
  have hR : R ≠ 0 := ne_of_gt hR0
  have hEq :=
    vbp (f := f) hf hR
  have hf_sphere : MeromorphicOn f (sphere (0 : ℂ) |R|) := by
    intro z hz
    exact (hf.analyticAt z).meromorphicAt
  have hInt : CircleIntegrable (fun z : ℂ => log ‖f z‖) 0 R :=
    MeromorphicOn.circleIntegrable_log_norm hf_sphere
  have hbound_circle : ∀ z ∈ sphere (0 : ℂ) |R|,
      log ‖f z‖ ≤ C * (1 + |R|) ^ ρ := by
    intro z hz
    exact vcJ hC hz
  have hCircleAvg_le :
      circleAverage (fun z : ℂ => log ‖f z‖) 0 R ≤ C * (1 + |R|) ^ ρ :=
    circleAverage_mono_on_of_le_circle (c := (0 : ℂ)) (R := R)
      (f := fun z => log ‖f z‖) hInt hbound_circle
  calc
    logCounting (divisor f (Set.univ : Set ℂ)) R
        = circleAverage (fun z : ℂ => log ‖f z‖) 0 R
            - log ‖meromorphicTrailingCoeffAt f 0‖ := by
            simpa [top_eq_univ] using hEq
    _ ≤ circleAverage (fun z : ℂ => log ‖f z‖) 0 R
          + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
          have :
              -log ‖meromorphicTrailingCoeffAt f 0‖
                ≤ |log ‖meromorphicTrailingCoeffAt f 0‖| :=
            neg_le_abs (log ‖meromorphicTrailingCoeffAt f 0‖)
          linarith
    _ ≤ C * (1 + |R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
          nlinarith [hCircleAvg_le]
variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
theorem vcF {D : locallyFinsupp E ℤ} (hDnonneg : 0 ≤ D)
    {R : ℝ} (hR : 1 ≤ R) :
    (log 2) * vbh D R ≤ logCounting D (2 * R) := by
  classical
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
  set r : ℝ := 2 * R
  have hrpos : 0 < r := by dsimp [r]; nlinarith
  let Dr := toClosedBall r D
  have hDr_fin : Set.Finite Dr.support := Dr.finiteSupport (isCompact_closedBall (0 : E) |r|)
  let F : Finset E := hDr_fin.toFinset
  let SR : Finset E :=
    (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).toFinset
  let S : Finset E := SR.filter fun z => z ≠ (0 : E)
  have hS_sub : S ⊆ F := by
    intro z hzS
    have hz_mem_SR : z ∈ SR := (Finset.mem_filter.1 hzS).1
    have hzR : z ∈ (toClosedBall R D).support := by
      exact (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).mem_toFinset.1
        hz_mem_SR
    have hz_norm_le_R : ‖z‖ ≤ R := by
      have := vaz hzR
      simpa [abs_of_pos hR0] using this
    have hz_norm_le_r : ‖z‖ ≤ |r| := by
      have : ‖z‖ ≤ r := le_trans hz_norm_le_R (by dsimp [r]; nlinarith)
      simpa [abs_of_pos hrpos] using this
    have hzD : z ∈ D.support := vdo hzR
    have : z ∈ Dr.support := by
      simpa [Dr] using
        vaX (D := D) (r := r) hzD hz_norm_le_r
    exact hDr_fin.mem_toFinset.2 this
  have hlogCounting :
      logCounting D r
        = (F.sum fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) + (D 0 : ℝ) * log r := by
    have hsupp : Function.support (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) ⊆ F := by
      intro z hz
      have : Dr z ≠ 0 := by
        by_contra h0
        simp [Function.mem_support, h0] at hz
      have : z ∈ Dr.support := by simpa [Function.mem_support] using this
      exact hDr_fin.mem_toFinset.2 this
    simp [logCounting, Dr, r,
      finsum_eq_sum_of_support_subset (f := fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) (s := F) hsupp]
  have hsum_le :
      (log 2) * (S.sum fun z => (D z : ℝ))
        ≤ F.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) := by
    have hterm_nonneg : ∀ z ∈ F, 0 ≤ (Dr z : ℝ) * log (r * ‖z‖⁻¹) := by
      intro z hzF
      have hz_sup : z ∈ Dr.support := hDr_fin.mem_toFinset.1 hzF
      have hDz : 0 ≤ Dr z := by
        have hDz' : 0 ≤ D z := hDnonneg z
        have hDrz : Dr z = D z :=
          vaO (vaz hz_sup)
        simpa [hDrz] using hDz'
      have hlog : 0 ≤ log (r * ‖z‖⁻¹) := by
        have hzle : ‖z‖ ≤ r := by
          have hnorm := vaz hz_sup
          simpa [abs_of_pos hrpos] using hnorm
        exact veb hzle
      exact mul_nonneg (by exact_mod_cast hDz) hlog
    have hsumSF :
        S.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹))
          ≤ F.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hS_sub (by
        intro z hzF _; exact hterm_nonneg z hzF)
    have hterm_ge : ∀ z ∈ S, (log 2) * (D z : ℝ) ≤ (Dr z : ℝ) * log (r * ‖z‖⁻¹) := by
      intro z hzS
      have hz0 : z ≠ (0 : E) := (Finset.mem_filter.1 hzS).2
      have hz_norm_le_R : ‖z‖ ≤ R := by
        have hz_mem_SR : z ∈ SR := (Finset.mem_filter.1 hzS).1
        have hzRsup : z ∈ (toClosedBall R D).support := by
          exact (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).mem_toFinset.1
            hz_mem_SR
        have hnorm := vaz hzRsup
        simpa [abs_of_pos hR0] using hnorm
      have hlog_le : log 2 ≤ log (r * ‖z‖⁻¹) := by
        simpa [r] using vcu hz0 hz_norm_le_R
      have hDz_nonneg : 0 ≤ D z := hDnonneg z
      have hz_in_ballr : z ∈ closedBall (0 : E) |r| := by
        have : ‖z‖ ≤ r := le_trans hz_norm_le_R (by dsimp [r]; nlinarith)
        simpa [mem_closedBall, dist_zero_right, abs_of_pos hrpos] using this
      have hDrz : Dr z = D z := by
        have hz_norm_le : ‖z‖ ≤ |r| := by
          simpa [mem_closedBall, dist_zero_right] using hz_in_ballr
        simpa [Dr] using vaO (D := D) (r := r) (z := z) hz_norm_le
      have : (log 2) * (D z : ℝ) ≤ (log (r * ‖z‖⁻¹)) * (D z : ℝ) :=
        mul_le_mul_of_nonneg_right hlog_le (by exact_mod_cast hDz_nonneg)
      simpa [hDrz, mul_assoc, mul_left_comm, mul_comm] using this
    calc
      (log 2) * (S.sum fun z => (D z : ℝ))
          = S.sum (fun z => (log 2) * (D z : ℝ)) := by simp [Finset.mul_sum]
      _ ≤ S.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) :=
        Finset.sum_le_sum fun z hz => hterm_ge z hz
      _ ≤ F.sum (fun z => (Dr z : ℝ) * log (r * ‖z‖⁻¹)) := hsumSF
  have hcenter_nonneg : 0 ≤ (D 0 : ℝ) * log r := by
    have hD0 : 0 ≤ D 0 := hDnonneg 0
    have hlogr : 0 ≤ log r := log_nonneg (by nlinarith [hR])
    exact mul_nonneg (by exact_mod_cast hD0) hlogr
  have : (log 2) * (S.sum fun z => (D z : ℝ)) ≤ logCounting D r := by
    rw [hlogCounting]
    nlinarith [hsum_le, hcenter_nonneg]
  simpa [vbh, r, S, SR] using this
theorem vcO {f : ℂ → ℂ} {ρ C : ℝ}
    (hf : Differentiable ℂ f)
    (hC : ∀ z : ℂ, log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) {R : ℝ} (hR : 1 ≤ R) :
    vbh (divisor f (Set.univ : Set ℂ)) R
      ≤ (C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖|) / log 2 := by
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
  have hlog2pos : 0 < log 2 := log_pos (by norm_num : (1 : ℝ) < 2)
  have hlow :
      (log 2) * vbh (divisor f (Set.univ : Set ℂ)) R
        ≤ logCounting (divisor f (Set.univ : Set ℂ)) (2 * R) :=
    vcF
      (D := divisor f (Set.univ : Set ℂ))
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg
        (hf.differentiableOn.analyticOnNhd isOpen_univ)) hR
  have hupp :
      logCounting (divisor f (Set.univ : Set ℂ)) (2 * R)
        ≤ C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
    have h2R0 : 0 < 2 * R := by nlinarith [hR0]
    simpa using vdM (f := f) (ρ := ρ) (C := C) hf hC
      (R := 2 * R) h2R0
  have hmul :
      (log 2) * vbh (divisor f (Set.univ : Set ℂ)) R
        ≤ C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| :=
    hlow.trans hupp
  have hmul' :
      vbh (divisor f (Set.univ : Set ℂ)) R * log 2
        ≤ C * (1 + |2 * R|) ^ ρ + |log ‖meromorphicTrailingCoeffAt f 0‖| := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  exact (le_div_iff₀ hlog2pos).2 hmul'
end Function.locallyFinsuppWithin
end
section
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
theorem Differentiable.divisor_nonneg {f : ℂ → E} (hf : Differentiable ℂ f) :
    0 ≤ MeromorphicOn.divisor f (univ : Set ℂ) :=
  MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hf.differentiableOn.analyticOnNhd isOpen_univ)
end
section
noncomputable section
open scoped BigOperators
open Filter
namespace Real
lemma vgi {x : ℝ} (hx : 1 ≤ x) :
    (2 : ℝ) ^ (⌊Real.logb 2 x⌋₊ : ℝ) ≤ x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
  have hlog_nonneg : 0 ≤ Real.logb 2 x :=
    Real.logb_nonneg (b := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2) hx
  have hfloor_le : (⌊Real.logb 2 x⌋₊ : ℝ) ≤ Real.logb 2 x := by
    simpa using (Nat.floor_le hlog_nonneg)
  exact (Real.le_logb_iff_rpow_le (b := (2 : ℝ))
    (x := (⌊Real.logb 2 x⌋₊ : ℝ)) (y := x)
    (by norm_num : (1 : ℝ) < 2) hx0).1 hfloor_le
lemma veH {x : ℝ} (hx : 1 ≤ x) :
    x < (2 : ℝ) ^ ((⌊Real.logb 2 x⌋₊ : ℝ) + 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
  have hlt : Real.logb 2 x < (⌊Real.logb 2 x⌋₊ : ℝ) + 1 := by
    simpa using (Nat.lt_floor_add_one (Real.logb 2 x))
  exact (Real.logb_lt_iff_lt_rpow (b := (2 : ℝ)) (x := x)
    (y := (⌊Real.logb 2 x⌋₊ : ℝ) + 1)
    (by norm_num : (1 : ℝ) < 2) hx0).1 hlt
lemma vfO {r0 x : ℝ} {k : ℕ} (hr0 : 0 < r0) (hx : r0 ≤ x)
    (hk : ⌊Real.logb 2 (x / r0)⌋₊ = k) :
    r0 * (2 : ℝ) ^ (k : ℝ) ≤ x := by
  have hr0ne : r0 ≠ 0 := ne_of_gt hr0
  have hx1 : (1 : ℝ) ≤ x / r0 := by
    have : r0 / r0 ≤ x / r0 := div_le_div_of_nonneg_right hx hr0.le
    simpa [hr0ne] using this
  have hle : (2 : ℝ) ^ (k : ℝ) ≤ x / r0 := by
    have := Real.vgi (x := x / r0) hx1
    simpa [hk] using this
  have := mul_le_mul_of_nonneg_left hle hr0.le
  have hxEq : r0 * (x / r0) = x := by
    field_simp [hr0ne]
  simpa [mul_assoc, hxEq] using this
lemma vfS {r0 x : ℝ} {k : ℕ} (hr0 : 0 < r0) (hx : r0 ≤ x)
    (hk : ⌊Real.logb 2 (x / r0)⌋₊ = k) :
    x ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by
  have hr0ne : r0 ≠ 0 := ne_of_gt hr0
  have hx1 : (1 : ℝ) ≤ x / r0 := by
    have : r0 / r0 ≤ x / r0 := div_le_div_of_nonneg_right hx hr0.le
    simpa [hr0ne] using this
  have hlt : x / r0 < (2 : ℝ) ^ ((k : ℝ) + 1) := by
    have := Real.veH (x := x / r0) hx1
    simpa [hk] using this
  have := mul_lt_mul_of_pos_left hlt hr0
  have hxEq : r0 * (x / r0) = x := by
    field_simp [hr0ne]
  exact le_of_lt (by simpa [mul_assoc, hxEq] using this)
lemma vgu (A : ℝ) :
    ∃ k0 : ℕ, ∀ n ≥ k0, A ≤ (2 : ℝ) ^ n := by
  have htend : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
  exact eventually_atTop.1 ((tendsto_atTop.1 htend) A)
lemma vcN
    {r0 : ℝ} {k0 kk : ℕ} (hr0 : 0 < r0)
    (hk0 : ∀ n ≥ k0, (1 / r0 : ℝ) ≤ (2 : ℝ) ^ n) (hkk : k0 ≤ kk + 1) :
    (1 : ℝ) ≤ r0 * (2 : ℝ) ^ ((kk : ℝ) + 1) := by
  have hr0ne : r0 ≠ 0 := ne_of_gt hr0
  have hpow_nat : (1 / r0 : ℝ) ≤ (2 : ℝ) ^ (kk + 1) := hk0 (kk + 1) hkk
  have hpow_rpow : (1 / r0 : ℝ) ≤ (2 : ℝ) ^ ((kk : ℝ) + 1) := by
    have hcast : (2 : ℝ) ^ ((kk : ℝ) + 1) = (2 : ℝ) ^ (kk + 1) := by
      calc
        (2 : ℝ) ^ ((kk : ℝ) + 1) = (2 : ℝ) ^ ((kk + 1 : ℕ) : ℝ) := by
          simp [Nat.cast_add, Nat.cast_one]
        _ = (2 : ℝ) ^ (kk + 1) := by
          simpa using (Real.rpow_natCast (2 : ℝ) (kk + 1))
    simpa [hcast] using hpow_nat
  have : (r0 * (1 / r0) : ℝ) ≤ r0 * (2 : ℝ) ^ ((kk : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hpow_rpow hr0.le
  simpa [one_div, hr0ne, mul_assoc] using this
lemma vcZ {r0 ρ : ℝ} (k : ℕ)
    (hr0 : 0 < r0) (hρ : 0 ≤ ρ) :
    (1 + |2 * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))|) ^ ρ
      ≤ (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ k := by
  let Rk : ℝ := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)
  have hRk' : |2 * Rk| = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := by
    have hnonneg : 0 ≤ (2 : ℝ) * Rk := by
      have : 0 ≤ Rk := by
        dsimp [Rk]
        exact mul_nonneg hr0.le (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
      nlinarith
    have hmul : (2 : ℝ) * Rk = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := by
      dsimp [Rk]
      calc
        (2 : ℝ) * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))
            = (2 * r0) * (2 : ℝ) ^ ((k : ℝ) + 1) := by ring
        _ = (2 * r0) * ((2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ (1 : ℝ)) := by
              simp [Real.rpow_add, mul_assoc]
        _ = (2 * r0) * ((2 : ℝ) ^ (k : ℝ) * 2) := by simp [Real.rpow_one]
        _ = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := by ring
    calc
      |2 * Rk| = 2 * Rk := abs_of_nonneg hnonneg
      _ = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := hmul
  have hbase :
      (1 + |2 * Rk|) ≤ (1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ) := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ (k : ℕ) := by
        simpa using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)))
      simpa [Real.rpow_natCast] using this
    have habs :
        1 + |2 * Rk| ≤ (2 : ℝ) ^ (k : ℝ) + (4 * r0) * (2 : ℝ) ^ (k : ℝ) := by
      rw [hRk']
      simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
        (add_le_add_right h1 ((4 * r0) * (2 : ℝ) ^ (k : ℝ)))
    have hfac :
        (2 : ℝ) ^ (k : ℝ) + (4 * r0) * (2 : ℝ) ^ (k : ℝ)
          = (1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ) := by
      ring
    exact habs.trans (le_of_eq hfac)
  have hRnonneg : 0 ≤ (1 + |2 * Rk|) := by linarith [abs_nonneg (2 * Rk)]
  have :
      (1 + |2 * Rk|) ^ ρ ≤ ((1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ)) ^ ρ :=
    Real.rpow_le_rpow hRnonneg hbase hρ
  have hsplit :
      ((1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ)) ^ ρ
        = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ (k : ℝ)) ^ ρ := by
    have h1 : 0 ≤ (1 + 4 * r0) := by nlinarith [hr0.le]
    have h2 : 0 ≤ (2 : ℝ) ^ (k : ℝ) :=
      le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
    simpa using (Real.mul_rpow h1 h2 (z := ρ))
  have hpow : ((2 : ℝ) ^ (k : ℝ)) ^ ρ = ((2 : ℝ) ^ ρ) ^ k := by
    have h2nonneg : (0 : ℝ) ≤ 2 := by norm_num
    calc
      ((2 : ℝ) ^ (k : ℝ)) ^ ρ = (2 : ℝ) ^ ((k : ℝ) * ρ) := by
        simp [Real.rpow_mul]
      _ = ((2 : ℝ) ^ ρ) ^ (k : ℝ) := by
        simpa [mul_comm] using
          (Real.rpow_mul (x := (2 : ℝ)) (y := ρ) (z := (k : ℝ)) h2nonneg)
      _ = ((2 : ℝ) ^ ρ) ^ k := by
        simp [Real.rpow_natCast]
  calc
    (1 + |2 * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))|) ^ ρ
        = (1 + |2 * Rk|) ^ ρ := by rfl
    _ ≤ ((1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ)) ^ ρ := this
    _ = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ (k : ℝ)) ^ ρ := hsplit
    _ = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ k := by
      simpa [mul_assoc] using congrArg (fun t => (1 + 4 * r0) ^ ρ * t) hpow
lemma vdg {α : Type*} [Fintype α] {a : α → ℝ}
    {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) (ha_nonneg : ∀ x, 0 ≤ a x)
    (ha_lower : ∀ x, R ≤ a x) :
    (∑' x : α, (a x)⁻¹ ^ τ) ≤ (Fintype.card α : ℝ) * (R⁻¹ ^ τ) := by
  have hsum_le :
      (∑ x : α, (a x)⁻¹ ^ τ) ≤ ∑ _x : α, R⁻¹ ^ τ := by
    refine Finset.sum_le_sum ?_
    intro x _hx
    have hinv : (a x)⁻¹ ≤ R⁻¹ := by
      simpa using (inv_anti₀ hR (ha_lower x))
    exact Real.rpow_le_rpow (inv_nonneg.2 (ha_nonneg x)) hinv hτ.le
  simpa [tsum_fintype, Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum_le
lemma vdN (r0 τ : ℝ) (k : ℕ) (hr0 : 0 ≤ r0) :
    (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ =
      (r0⁻¹ : ℝ) ^ τ * ((2 : ℝ) ^ (-τ)) ^ k := by
  have h2k_nonneg : 0 ≤ (2 : ℝ) ^ (k : ℝ) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
  calc
    (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ =
        (r0 * (2 : ℝ) ^ (k : ℝ)) ^ (-τ) := by
      simpa using (Real.rpow_neg_eq_inv_rpow (r0 * (2 : ℝ) ^ (k : ℝ)) τ).symm
    _ = r0 ^ (-τ) * (((2 : ℝ) ^ (k : ℝ)) ^ (-τ)) := by
      simpa using (Real.mul_rpow hr0 h2k_nonneg (z := -τ))
    _ = (r0⁻¹ : ℝ) ^ τ * ((2 : ℝ) ^ (-τ)) ^ k := by
      have hr0' : r0 ^ (-τ) = (r0⁻¹ : ℝ) ^ τ := by
        simp [Real.rpow_neg_eq_inv_rpow]
      have h2' : ((2 : ℝ) ^ (k : ℝ)) ^ (-τ) = ((2 : ℝ) ^ (-τ)) ^ k := by
        have h2nonneg : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
        calc
          ((2 : ℝ) ^ (k : ℝ)) ^ (-τ) = (2 : ℝ) ^ ((k : ℝ) * (-τ)) := by
            exact (Real.rpow_mul (x := (2 : ℝ)) (y := (k : ℝ)) (z := -τ)
              h2nonneg).symm
          _ = (2 : ℝ) ^ ((-τ) * (k : ℝ)) := by ring_nf
          _ = ((2 : ℝ) ^ (-τ)) ^ (k : ℝ) := by
            exact Real.rpow_mul (x := (2 : ℝ)) (y := -τ) (z := (k : ℝ)) h2nonneg
          _ = ((2 : ℝ) ^ (-τ)) ^ k := by
            simp [Real.rpow_natCast]
      calc
        r0 ^ (-τ) * (((2 : ℝ) ^ (k : ℝ)) ^ (-τ))
            = (r0⁻¹ : ℝ) ^ τ * (((2 : ℝ) ^ (k : ℝ)) ^ (-τ)) := by
              rw [hr0']
        _ = (r0⁻¹ : ℝ) ^ τ * ((2 : ℝ) ^ (-τ)) ^ k := by
              rw [h2']
lemma vfQ (ρ τ : ℝ) :
    (2 : ℝ) ^ (ρ - τ) = (2 : ℝ) ^ ρ * (2 : ℝ) ^ (-τ) := by
  have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
  calc
    (2 : ℝ) ^ (ρ - τ) = (2 : ℝ) ^ (ρ + (-τ)) := by ring_nf
    _ = (2 : ℝ) ^ ρ * (2 : ℝ) ^ (-τ) := by
      simp [Real.rpow_add h2pos]
lemma veW (ρ τ : ℝ) (k : ℕ) :
    ((2 : ℝ) ^ (ρ - τ)) ^ k =
      ((2 : ℝ) ^ ρ) ^ k * (((2 : ℝ) ^ (-τ)) ^ k) := by
  simp [vfQ, mul_pow]
lemma vfv (C L M r0 ρ τ : ℝ) (k : ℕ) (hr0 : 0 ≤ r0) :
    ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) *
        ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
      = (((C / L) * M) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (ρ - τ)) ^ k := by
  have hrk_inv :
      (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ =
        (r0⁻¹ : ℝ) ^ τ * (((2 : ℝ) ^ (-τ)) ^ k) :=
    vdN r0 τ k hr0
  rw [hrk_inv, veW]
  ac_rfl
lemma vfd (C L r0 τ : ℝ) (k : ℕ) (hr0 : 0 ≤ r0) :
    (C / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
      ≤ (((C / L) + 1) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (-τ)) ^ k := by
  rw [vdN r0 τ k hr0]
  have hcoeff : C / L ≤ C / L + 1 := by linarith
  have hr0Inv_nonneg : 0 ≤ (r0⁻¹ : ℝ) ^ τ :=
    Real.rpow_nonneg (inv_nonneg.2 hr0) _
  have hmul :
      (C / L) * ((r0⁻¹ : ℝ) ^ τ)
        ≤ ((C / L) + 1) * ((r0⁻¹ : ℝ) ^ τ) :=
    mul_le_mul_of_nonneg_right hcoeff hr0Inv_nonneg
  have hqpow_nonneg : 0 ≤ ((2 : ℝ) ^ (-τ)) ^ k :=
    pow_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)) _
  have := mul_le_mul_of_nonneg_right hmul hqpow_nonneg
  simpa [mul_assoc, mul_left_comm, mul_comm] using this
lemma vdp {C L M X T Ctrail r0 ρ τ : ℝ} {k : ℕ}
    (hL : 0 < L) (hC : 0 ≤ C) (hr0 : 0 ≤ r0)
    (hX : X ≤ M * ((2 : ℝ) ^ ρ) ^ k)
    (hT : T ≤ ((C * X + Ctrail) / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)) :
    T ≤ (((C / L) * M) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (ρ - τ)) ^ k
        + (((Ctrail / L) + 1) * (r0⁻¹ : ℝ) ^ τ) * ((2 : ℝ) ^ (-τ)) ^ k := by
  have hmul : C * X ≤ C * (M * ((2 : ℝ) ^ ρ) ^ k) :=
    mul_le_mul_of_nonneg_left hX hC
  have hnum : C * X + Ctrail ≤ C * (M * ((2 : ℝ) ^ ρ) ^ k) + Ctrail :=
    add_le_add hmul le_rfl
  have hdiv :
      (C * X + Ctrail) / L ≤ (C * (M * ((2 : ℝ) ^ ρ) ^ k) + Ctrail) / L :=
    div_le_div_of_nonneg_right hnum hL.le
  have h2k_nonneg : 0 ≤ (2 : ℝ) ^ (k : ℝ) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (k : ℝ))
  have hrk_nonneg : 0 ≤ r0 * (2 : ℝ) ^ (k : ℝ) :=
    mul_nonneg hr0 h2k_nonneg
  have hfactor_nonneg : 0 ≤ ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ) :=
    Real.rpow_nonneg (inv_nonneg.2 hrk_nonneg) τ
  have hmul' :=
    mul_le_mul_of_nonneg_right hdiv hfactor_nonneg
  have hdecomp :
      ((C * (M * ((2 : ℝ) ^ ρ) ^ k) + Ctrail) / L) *
          ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
        =
        ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) *
            ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
          + ((Ctrail / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)) := by
    let Y : ℝ := (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ
    have :
        ((C * (M * ((2 : ℝ) ^ ρ) ^ k) + Ctrail) / L) * Y
          = ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) * Y
            + ((Ctrail / L) * Y) := by
      ring
    simpa [Y]
  have hpre :
      T ≤ ((C / L) * (M * ((2 : ℝ) ^ ρ) ^ k)) *
            ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)
          + ((Ctrail / L) * ((r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ)) :=
    hT.trans (hmul'.trans_eq hdecomp)
  have hA := le_of_eq (vfv C L M r0 ρ τ k hr0)
  have hB := vfd Ctrail L r0 τ k hr0
  exact hpre.trans (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using add_le_add hA hB)
lemma vfU (A B q qσ : ℝ) (k k0 : ℕ) :
    A * q ^ (k + k0) + B * qσ ^ (k + k0)
      = (A * q ^ k0) * q ^ k + (B * qσ ^ k0) * qσ ^ k := by
  rw [pow_add, pow_add]
  ac_rfl
end Real
end
end
section
noncomputable section
open Filter Topology Set Complex
open scoped BigOperators Topology
namespace Complex.Hadamard
open scoped Real
noncomputable def vay (f : ℂ → ℂ) (R : ℝ) : ℝ :=
  Function.locallyFinsuppWithin.vbh (MeromorphicOn.divisor f (Set.univ : Set ℂ)) R
lemma vdE {f : ℂ → ℂ} {ρ C : ℝ}
    (hf : Differentiable ℂ f)
    (hC : ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ)
    {R : ℝ} (hR : 1 ≤ R) :
    vay f R
      ≤ (C * (1 + |2 * R|) ^ ρ + |Real.log ‖meromorphicTrailingCoeffAt f 0‖|) /
          Real.log 2 := by
  simpa [vay] using
    (Function.locallyFinsuppWithin.vcO
      (f := f) (ρ := ρ) (C := C) hf hC hR)
lemma vcV {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0) :
    ∃ r0 : ℝ, 0 < r0 ∧
      ∀ p : vab f (Set.univ : Set ℂ), r0 ≤ ‖vaa p‖ := by
  classical
  set U : Set ℂ := (Set.univ : Set ℂ)
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hDnonneg : 0 ≤ D := by
    simpa [D, U] using (Differentiable.divisor_nonneg (f := f) hf)
  have hzero : ∀ p : vab f U, f (vaa p) = 0 := by
    intro p
    set z : ℂ := vaa p
    have hneTop : meromorphicOrderAt f z ≠ ⊤ := by
      have hzAnal : AnalyticAt ℂ f z := hf.analyticAt z
      have hzA : analyticOrderAt f z ≠ ⊤ :=
        vak (f := f) (hf := hf) hnot (z := z)
      intro htop
      have hm : meromorphicOrderAt f z = (analyticOrderAt f z).map (↑) :=
        hzAnal.meromorphicOrderAt_eq (𝕜 := ℂ)
      cases h : analyticOrderAt f z with
      | top =>
          exact hzA (by simp [h])
      | coe n =>
          have : (analyticOrderAt f z).map (↑) ≠ (⊤ : WithTop ℤ) := by
            simp [h]
          exact this (by simpa [hm] using htop)
    have hmon : MeromorphicOn f U := by
      intro w hw; exact (hf.analyticAt w).meromorphicAt
    have hdiv : MeromorphicOn.divisor f U z = (meromorphicOrderAt f z).untop₀ := by
      simpa [U] using (MeromorphicOn.divisor_apply (f := f) (U := U) (z := z) hmon (by aesop))
    have hDz : MeromorphicOn.divisor f U z ≠ 0 := by
      have hzsup : z ∈ (MeromorphicOn.divisor f U).support := by
        simp [z]
      simpa [Function.mem_support] using hzsup
    have hposZ : (0 : ℤ) < (meromorphicOrderAt f z).untop₀ := by
      have hge0 : 0 ≤ (meromorphicOrderAt f z).untop₀ := by
        have : 0 ≤ MeromorphicOn.divisor f U z := by
          simpa [D, U, z] using hDnonneg z
        simpa [hdiv] using this
      have hne0 : (meromorphicOrderAt f z).untop₀ ≠ 0 := by
        simpa [hdiv] using hDz
      exact lt_of_le_of_ne hge0 (by simpa [eq_comm] using hne0)
    have hpos : (0 : WithTop ℤ) < meromorphicOrderAt f z := by
      have : (0 : WithTop ℤ) < ((meromorphicOrderAt f z).untop₀ : WithTop ℤ) :=
        WithTop.coe_lt_coe.2 hposZ
      simpa [WithTop.coe_untop₀_of_ne_top hneTop] using this
    have htend0 : Tendsto f (𝓝[≠] z) (𝓝 (0 : ℂ)) :=
      tendsto_zero_of_meromorphicOrderAt_pos (f := f) (x := z) hpos
    have hcontz : ContinuousAt f z := (hf z).continuousAt
    have htendz : Tendsto f (𝓝[≠] z) (𝓝 (f z)) :=
      (hcontz.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] z ≤ 𝓝 z))
    exact tendsto_nhds_unique htendz htend0
  by_cases h0 : f 0 = 0
  · have hD0 : D 0 ≠ 0 := by
      have hmero0 : MeromorphicAt f (0 : ℂ) := (hf.analyticAt 0).meromorphicAt
      have hneTop0 : meromorphicOrderAt f (0 : ℂ) ≠ ⊤ := by
        have hA0 : analyticOrderAt f (0 : ℂ) ≠ ⊤ :=
          vak (f := f) (hf := hf) hnot (z := 0)
        intro htop
        have hm : meromorphicOrderAt f (0 : ℂ) = (analyticOrderAt f (0 : ℂ)).map (↑) :=
          (hf.analyticAt 0).meromorphicOrderAt_eq (𝕜 := ℂ)
        cases h : analyticOrderAt f (0 : ℂ) with
        | top => exact absurd h hA0
        | coe n =>
            have : (analyticOrderAt f (0 : ℂ)).map (↑) ≠ (⊤ : WithTop ℤ) := by
              simp [h]
            exact this (by simpa [hm] using htop)
      have htend0 : Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
        have hcont0 : ContinuousAt f (0 : ℂ) := (hf 0).continuousAt
        have : Tendsto f (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by simpa [h0] using hcont0.tendsto
        exact this.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 (0 : ℂ))
      have hpos0 : (0 : WithTop ℤ) < meromorphicOrderAt f (0 : ℂ) :=
        (tendsto_zero_iff_meromorphicOrderAt_pos hmero0).1 htend0
      have hpos0' : (0 : ℤ) < (meromorphicOrderAt f (0 : ℂ)).untop₀ := by
        have : (0 : WithTop ℤ) < ((meromorphicOrderAt f (0 : ℂ)).untop₀ : WithTop ℤ) := by
          simpa [WithTop.coe_untop₀_of_ne_top hneTop0] using hpos0
        simpa using (WithTop.coe_lt_coe.1 this)
      have hdiv0 : D 0 = (meromorphicOrderAt f (0 : ℂ)).untop₀ := by
        have hmon : MeromorphicOn f U := by
          intro w hw; exact (hf.analyticAt w).meromorphicAt
        simpa [D, U] using
          (MeromorphicOn.divisor_apply (f := f) (U := U) (z := (0 : ℂ))
            hmon (by aesop))
      exact by
        have : (meromorphicOrderAt f (0 : ℂ)).untop₀ ≠ 0 := ne_of_gt hpos0'
        simpa [hdiv0] using this
    have hmem0 : (0 : ℂ) ∈ D.support := by
      simp [Function.mem_support, hD0]
    have hdisc : IsDiscrete D.support := by
      simpa [D] using (D.discreteSupport)
    rcases Metric.exists_ball_inter_eq_singleton_of_mem_discrete hdisc hmem0 with ⟨r0, hr0pos, hr0⟩
    refine ⟨r0, hr0pos, ?_⟩
    intro p
    have hp : vaa p ∈ D.support := by
      simp [D, vbm (f := f) (U := U) p]
    have hnotBall : vaa p ∉ Metric.ball (0 : ℂ) r0 := by
      intro hball
      have : vaa p ∈ Metric.ball (0 : ℂ) r0 ∩ D.support := ⟨hball, hp⟩
      have : vaa p ∈ ({(0 : ℂ)} : Set ℂ) := by simp [hr0] at this
      have : vaa p = 0 := by simp [Set.mem_singleton_iff] at this
      exact (vao p) this
    have : r0 ≤ ‖vaa p‖ := by
      have : ¬ ‖vaa p‖ < r0 := by
        intro hlt
        exact hnotBall (by simpa [Metric.mem_ball, dist_zero_right] using hlt)
      exact le_of_not_gt this
    exact this
  · have hcont0 : ContinuousAt f (0 : ℂ) := (hf 0).continuousAt
    have hne : ∀ᶠ z in 𝓝 (0 : ℂ), f z ≠ 0 := hcont0.eventually_ne h0
    rcases Metric.mem_nhds_iff.1 hne with ⟨r0, hr0pos, hr0⟩
    refine ⟨r0, hr0pos, ?_⟩
    intro p
    have : ¬ ‖vaa p‖ < r0 := by
      intro hlt
      have hzball : vaa p ∈ Metric.ball (0 : ℂ) r0 := by
        simpa [Metric.mem_ball, dist_zero_right] using hlt
      have : f (vaa p) ≠ 0 := hr0 hzball
      exact this (hzero p)
    exact le_of_not_gt this
open scoped BigOperators
lemma vdB
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {R : ℝ} (hR : 0 < R) :
    (Nat.card {p : vab f (Set.univ : Set ℂ) // ‖vaa p‖ ≤ R} : ℝ)
      ≤ vay f R := by
  set U : Set ℂ := (Set.univ : Set ℂ)
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have :
      Fintype {p : vab f U // ‖vaa p‖ ≤ R} := by
    have : Finite {p : vab f U // ‖vaa p‖ ≤ R} := by
      have : Metric.closedBall (0 : ℂ) R ⊆ U := by simp [U]
      simpa using (vaT (f := f) (U := U) (B := R) this)
    exact Fintype.ofFinite _
  have hDnonneg : 0 ≤ D := by
    simpa [D, U] using (Differentiable.divisor_nonneg (f := f) hf)
  let SR : Finset ℂ :=
    (Function.locallyFinsuppWithin.finiteSupport (Function.locallyFinsuppWithin.toClosedBall R D)
          (isCompact_closedBall (0 : ℂ) |R|)).toFinset
  let S : Finset ℂ := SR.filter fun z : ℂ => z ≠ 0
  let T : Type :=
    Σ z : S, Fin (Int.toNat (D z.1))
  let φ :
      {p : vab f U // ‖vaa p‖ ≤ R} → T := fun p =>
    let z0 : ℂ := vaa p.1
    have hz0_memSR : z0 ∈ SR := by
      have hz0_norm : ‖z0‖ ≤ |R| := by
        have : ‖z0‖ ≤ R := p.2
        simpa [abs_of_pos hR] using this
      have hz0_support : z0 ∈ (Function.locallyFinsuppWithin.toClosedBall R D).support := by
        have hz0_suppD : z0 ∈ D.support := by
          simp [z0, D]
        exact Function.locallyFinsuppWithin.vaX
          hz0_suppD hz0_norm
      exact (Set.Finite.mem_toFinset
        (Function.locallyFinsuppWithin.finiteSupport
          (Function.locallyFinsuppWithin.toClosedBall R D)
            (isCompact_closedBall (0 : ℂ) |R|))).2 hz0_support
    have hz0_ne0 : z0 ≠ 0 := vao p.1
    have hz0_memS : z0 ∈ S := Finset.mem_filter.2 ⟨hz0_memSR, hz0_ne0⟩
    ⟨⟨z0, hz0_memS⟩, by
        simpa [z0, vaa, D] using p.1.1.2⟩
  have hφ_inj : Function.Injective φ := by
    intro p q hpq
    have hσ := (Sigma.mk.inj_iff).1 hpq
    have hzS : (φ p).1 = (φ q).1 := hσ.1
    have hz : vaa p.1 = vaa q.1 := by
      simpa [φ] using congrArg Subtype.val hzS
    apply Subtype.ext
    apply Subtype.ext
    apply Sigma.ext
    · exact hz
    · simpa [φ] using hσ.2
  have hcard_le :
      Fintype.card {p : vab f U // ‖vaa p‖ ≤ R} ≤ Fintype.card T :=
    Fintype.card_le_of_injective φ hφ_inj
  have hT_card :
      (Fintype.card T : ℝ) =
        (S.sum fun z : ℂ => (Int.toNat (D z) : ℝ)) := by
    have hNat :
        Fintype.card T = ∑ z : S, Int.toNat (D z.1) := by
      have h1 :
          Fintype.card T = ∑ z : S, Fintype.card (Fin (Int.toNat (D z.1))) := by
        change Fintype.card (Sigma (fun z : S => Fin (Int.toNat (D z.1))))
            = ∑ z : S, Fintype.card (Fin (Int.toNat (D z.1)))
        exact (Fintype.card_sigma (ι := S) (α := fun z : S => Fin (Int.toNat (D z.1))))
      simpa using h1
    have hR :
        (Fintype.card T : ℝ) = ∑ z : S, (Int.toNat (D z.1) : ℝ) := by
      exact_mod_cast hNat
    have hR' :
        (Fintype.card T : ℝ) = S.attach.sum (fun z : S => (Int.toNat (D z.1) : ℝ)) := by
      simpa [Finset.univ_eq_attach] using hR
    calc
      (Fintype.card T : ℝ) = S.attach.sum (fun z : S => (Int.toNat (D z.1) : ℝ)) := hR'
      _ = S.sum (fun z : ℂ => (Int.toNat (D z) : ℝ)) := by
            simpa using (Finset.sum_attach (s := S) (f := fun z : ℂ => (Int.toNat (D z) : ℝ)))
  have htoNat_le : ∀ z ∈ S, (Int.toNat (D z) : ℝ) ≤ (D z : ℝ) := by
    intro z hz
    have hDz_nonneg : 0 ≤ D z := by simpa [D] using hDnonneg z
    have hEqZ : ((Int.toNat (D z) : ℕ) : ℤ) = D z := by
      simpa using (Int.toNat_of_nonneg hDz_nonneg)
    have hEqR : (Int.toNat (D z) : ℝ) = (D z : ℝ) := by
      exact_mod_cast hEqZ
    exact le_of_eq hEqR
  calc
    (Nat.card {p : vab f U // ‖vaa p‖ ≤ R} : ℝ)
        = (Fintype.card {p : vab f U // ‖vaa p‖ ≤ R} : ℝ) := by
          simp [Nat.card_eq_fintype_card]
    _ ≤ (Fintype.card T : ℝ) := by exact_mod_cast hcard_le
    _ = S.sum (fun z : ℂ => (Int.toNat (D z) : ℝ)) := hT_card
    _ ≤ S.sum (fun z : ℂ => (D z : ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro z hz
      exact htoNat_le z hz
    _ = vay f R := by
      rfl
lemma vbZ
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {s : Set (vab f (Set.univ : Set ℂ))} [Fintype s]
    {R : ℝ} (hR : 0 < R) (hs : ∀ p : s, ‖vaa p.1‖ ≤ R) :
    (Fintype.card s : ℝ) ≤ vay f R := by
  let Aball : Type :=
    {p : vab f (Set.univ : Set ℂ) // ‖vaa p‖ ≤ R}
  have : Fintype Aball := by
    have : Finite Aball := by
      have : Metric.closedBall (0 : ℂ) R ⊆ (Set.univ : Set ℂ) := by simp
      simpa [Aball] using
        (vaT (f := f) (U := (Set.univ : Set ℂ))
          (B := R) this)
    exact Fintype.ofFinite _
  have hinj : Function.Injective (fun p : s => (⟨p.1, hs p⟩ : Aball)) := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun x : Aball => x.1) hpq
  have hcard_le : Fintype.card s ≤ Fintype.card Aball :=
    Fintype.card_le_of_injective _ hinj
  have hAball : (Nat.card Aball : ℝ) ≤ vay f R := by
    simpa [Aball] using vdB (f := f) hf hR
  calc
    (Fintype.card s : ℝ) ≤ (Fintype.card Aball : ℝ) := by exact_mod_cast hcard_le
    _ = (Nat.card Aball : ℝ) := by simp [Nat.card_eq_fintype_card]
    _ ≤ vay f R := hAball
lemma vbn
    {f : ℂ → ℂ} {r0 : ℝ}
    (hr0pos : 0 < r0)
    (hr0 : ∀ p : vab f (Set.univ : Set ℂ), r0 ≤ ‖vaa p‖)
    {k : ℕ} {p : vab f (Set.univ : Set ℂ)}
    (hp : ⌊Real.logb 2 (‖vaa p‖ / r0)⌋₊ = k) :
    ‖vaa p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by
  exact Real.vfS (r0 := r0) (x := ‖vaa p‖)
    hr0pos (hr0 p) hp
lemma vcK
    {f : ℂ → ℂ} {r0 : ℝ}
    (hr0pos : 0 < r0)
    (hr0 : ∀ p : vab f (Set.univ : Set ℂ), r0 ≤ ‖vaa p‖)
    {k : ℕ} {p : vab f (Set.univ : Set ℂ)}
    (hp : ⌊Real.logb 2 (‖vaa p‖ / r0)⌋₊ = k) :
    r0 * (2 : ℝ) ^ (k : ℝ) ≤ ‖vaa p‖ := by
  exact Real.vfO (r0 := r0) (x := ‖vaa p‖)
    hr0pos (hr0 p) hp
lemma vbB
    {f : ℂ → ℂ} {r0 : ℝ}
    (hr0pos : 0 < r0)
    (hr0 : ∀ p : vab f (Set.univ : Set ℂ), r0 ≤ ‖vaa p‖)
    (k : ℕ) :
    ({p : vab f (Set.univ : Set ℂ) |
      ⌊Real.logb 2 (‖vaa p‖ / r0)⌋₊ = k} : Set _).Finite := by
  have hsub :
      {p : vab f (Set.univ : Set ℂ) |
        ⌊Real.logb 2 (‖vaa p‖ / r0)⌋₊ = k} ⊆
        {p : vab f (Set.univ : Set ℂ) |
          ‖vaa p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)} := by
    intro p hp
    exact vbn hr0pos hr0 hp
  have hfin :
      ({p : vab f (Set.univ : Set ℂ) |
        ‖vaa p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)} : Set _).Finite := by
    have :
        Metric.closedBall (0 : ℂ) (r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) ⊆
          (Set.univ : Set ℂ) := by
      simp
    simpa using
      (vat (f := f) (U := (Set.univ : Set ℂ))
        (B := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) this)
  exact hfin.subset hsub
lemma vbg
    {f : ℂ → ℂ} {ρ τ r0 Cgrow : ℝ}
    (hρ : 0 ≤ ρ) (hτpos : 0 < τ) (hf : Differentiable ℂ f)
    (hCgrow_pos : 0 < Cgrow)
    (hCgrow : ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ Cgrow * (1 + ‖z‖) ^ ρ)
    (hr0pos : 0 < r0)
    (hr0 : ∀ p : vab f (Set.univ : Set ℂ),
      r0 ≤ ‖vaa p‖)
    (k : ℕ) (hk_ge_one : 1 ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) :
    let kfun : vab f (Set.univ : Set ℂ) → ℕ :=
      fun p => ⌊Real.logb 2 (‖vaa p‖ / r0)⌋₊
    let S : Set (vab f (Set.univ : Set ℂ)) := {p | kfun p = k}
    let Ctrail : ℝ := |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
    let A : ℝ := ((Cgrow / Real.log 2) * (1 + 4 * r0) ^ ρ) * (r0⁻¹) ^ τ
    let B : ℝ := ((Ctrail / Real.log 2) + 1) * (r0⁻¹) ^ τ
    let q : ℝ := (2 : ℝ) ^ (ρ - τ)
    let qσ : ℝ := (2 : ℝ) ^ (-τ)
    (∑' p : S, ‖vaa p.1‖⁻¹ ^ τ) ≤ A * q ^ k + B * qσ ^ k := by
  classical
  intro kfun S Ctrail A B q qσ
  let rk : ℝ := r0 * (2 : ℝ) ^ (k : ℝ)
  let Rk : ℝ := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)
  have hrk_pos : 0 < rk := mul_pos hr0pos (Real.rpow_pos_of_pos (by norm_num) _)
  have hrk0 : 0 ≤ rk := le_of_lt hrk_pos
  have : Finite S := by
    simpa [S, kfun] using (vbB
      (f := f) hr0pos hr0 k).to_subtype
  have : Fintype S := Fintype.ofFinite S
  have hk_upper : ∀ p : S, ‖vaa p.1‖ ≤ Rk := by
    intro p
    have hk' : kfun p.1 = k := p.2
    simpa [Rk, kfun] using
      vbn (f := f) hr0pos hr0 hk'
  have hk_lower : ∀ p : S, rk ≤ ‖vaa p.1‖ := by
    intro p
    have hk' : kfun p.1 = k := p.2
    simpa [rk, kfun] using
      vcK (f := f) hr0pos hr0 hk'
  have htsum_le :
      (∑' p : S, ‖vaa p.1‖⁻¹ ^ τ)
        ≤ (Fintype.card S : ℝ) * (rk⁻¹ ^ τ) := by
    exact Real.vdg
      (a := fun p : S => ‖vaa p.1‖)
      hrk_pos hτpos (fun _ => norm_nonneg _) hk_lower
  have hmass_le_growth :
      vay f Rk
        ≤ (Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2) := by
    simpa [Ctrail, Rk] using
      (vdE (f := f) (ρ := ρ) (C := Cgrow) hf hCgrow
        (R := Rk) hk_ge_one)
  have hcard_le_mass :
      (Fintype.card S : ℝ) ≤ vay f Rk := by
    have hRk_pos : 0 < Rk := lt_of_lt_of_le (by norm_num) hk_ge_one
    exact vbZ (f := f) hf hRk_pos hk_upper
  have htsum' :
      (∑' p : S, ‖vaa p.1‖⁻¹ ^ τ)
        ≤ ((Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2)) * (rk⁻¹ ^ τ) := by
    have hcard_le_growth :
        (Fintype.card S : ℝ) ≤
          (Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2) :=
      le_trans hcard_le_mass hmass_le_growth
    exact le_trans htsum_le <|
      mul_le_mul_of_nonneg_right hcard_le_growth (Real.rpow_nonneg (inv_nonneg.2 hrk0) τ)
  have hpow_bound :
      (1 + |2 * Rk|) ^ ρ ≤ (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ k := by
    simpa [Rk] using
      Real.vcZ (r0 := r0) (ρ := ρ) k hr0pos hρ
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  simpa [A, B, q, qσ, rk, Ctrail, mul_assoc, mul_left_comm, mul_comm] using
    Real.vdp
      (C := Cgrow) (L := Real.log 2) (M := (1 + 4 * r0) ^ ρ)
      (X := (1 + |2 * Rk|) ^ ρ)
      (T := ∑' p : S, ‖vaa p.1‖⁻¹ ^ τ)
      (Ctrail := Ctrail) (r0 := r0) (ρ := ρ) (τ := τ) (k := k)
      hlog2pos hCgrow_pos.le hr0pos.le hpow_bound
      (by simpa [rk] using htsum')
theorem vaE {f : ℂ → ℂ} {ρ τ : ℝ}
    (hρ : 0 ≤ ρ) (hτ : ρ < τ) (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ τ) := by
  rcases hgrowth with ⟨Cgrow, hCgrow_pos, hCgrow⟩
  have hτpos : 0 < τ := lt_of_le_of_lt hρ hτ
  rcases vcV (f := f) hf hnot with ⟨r0, hr0pos, hr0⟩
  have hr0ne : (r0 : ℝ) ≠ 0 := ne_of_gt hr0pos
  let kfun : vab f (Set.univ : Set ℂ) → ℕ :=
    fun p => ⌊Real.logb 2 (‖vaa p‖ / r0)⌋₊
  let S : ℕ → Set (vab f (Set.univ : Set ℂ)) :=
    fun k => {p | kfun p = k}
  have hS : ∀ p : vab f (Set.univ : Set ℂ), ∃! k : ℕ, p ∈ S k := by
    intro p
    refine ⟨kfun p, ?_, ?_⟩
    · simp [S]
    · intro k hk
      simpa [S] using hk.symm
  have hnonneg : 0 ≤ fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ τ := by
    intro p
    exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
  have hSk_summable : ∀ k : ℕ, Summable fun p : S k => ‖vaa p.1‖⁻¹ ^ τ := by
    intro k
    have : Finite (S k) := by
      simpa [S, kfun] using (vbB
        (f := f) hr0pos hr0 k).to_subtype
    exact Summable.of_finite
  have hshell_summable :
      Summable fun k : ℕ => ∑' p : S k, ‖vaa p.1‖⁻¹ ^ τ := by
    let q : ℝ := (2 : ℝ) ^ (ρ - τ)
    let qσ : ℝ := (2 : ℝ) ^ (-τ)
    have hq_nonneg : 0 ≤ q := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    have hq_lt_one : q < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
        (sub_neg.2 hτ)
    have hqσ_nonneg : 0 ≤ qσ := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    have hqσ_lt_one : qσ < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
        (by simpa using (neg_neg_of_pos hτpos))
    have hgeom_q : Summable (fun k : ℕ => q ^ k) :=
      summable_geometric_of_lt_one hq_nonneg hq_lt_one
    have hgeom_qσ : Summable (fun k : ℕ => qσ ^ k) :=
      summable_geometric_of_lt_one hqσ_nonneg hqσ_lt_one
    let Ctrail : ℝ := |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
    let A : ℝ := ((Cgrow / Real.log 2) * (1 + 4 * r0) ^ ρ) * (r0⁻¹) ^ τ
    let B : ℝ := ((Ctrail / Real.log 2) + 1) * (r0⁻¹) ^ τ
    rcases Real.vgu (1 / r0) with ⟨k0, hk0⟩
    let A0 : ℝ := A * q ^ k0
    let B0 : ℝ := B * qσ ^ k0
    have hmajor : Summable (fun k : ℕ => A0 * q ^ k + B0 * qσ ^ k) :=
      (hgeom_q.mul_left A0).add (hgeom_qσ.mul_left B0)
    have hshell_summable_shift :
        Summable fun k : ℕ => ∑' p : S (k + k0), ‖vaa p.1‖⁻¹ ^ τ := by
      refine hmajor.of_nonneg_of_le
        (fun k => by
          have : ∀ p : S (k + k0), 0 ≤ ‖vaa p.1‖⁻¹ ^ τ := by
            intro p; exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
          exact tsum_nonneg this)
        (fun k => by
          let kk : ℕ := k + k0
          let Rk : ℝ := r0 * (2 : ℝ) ^ ((kk : ℝ) + 1)
          have hRk_ge_one : (1 : ℝ) ≤ Rk := by
            have hkk : k0 ≤ kk + 1 := by
              simp [kk, Nat.add_assoc, Nat.add_comm]
            simpa [Rk] using
              Real.vcN hr0pos hk0 hkk
          have hmain :
              (∑' p : S kk, ‖vaa p.1‖⁻¹ ^ τ) ≤ A * q ^ kk + B * qσ ^ kk := by
            simpa [S, kfun, Ctrail, A, B, q, qσ] using
              vbg
                (f := f) (ρ := ρ) (τ := τ) hρ hτpos hf hCgrow_pos hCgrow hr0pos hr0 kk hRk_ge_one
          have : A * q ^ kk + B * qσ ^ kk = A0 * q ^ k + B0 * qσ ^ k := by
            simpa [A0, B0, kk] using Real.vfU A B q qσ k k0
          simpa [kk] using (hmain.trans_eq this)
        )
    exact (summable_nat_add_iff k0).1 hshell_summable_shift
  have hpart :=
    (summable_partition (f := fun p : vab f (Set.univ : Set ℂ) =>
        ‖vaa p‖⁻¹ ^ τ) hnonneg (s := S) hS)
  exact (hpart.2 ⟨hSk_summable, hshell_summable⟩)
theorem vaZ {f : ℂ → ℂ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (Nat.floor ρ + 1)) := by
  have hτ : ρ < (Nat.floor ρ + 1 : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (a := ρ))
  have hs :=
    vaE (f := f) (ρ := ρ)
      (τ := (Nat.floor ρ + 1 : ℝ)) hρ hτ hf hnot hgrowth
  exact hs.congr fun p => by
    have hcast : ((Nat.floor ρ : ℝ) + 1) = ((Nat.floor ρ + 1 : ℕ) : ℝ) := by
      norm_num
    rw [hcast, Real.rpow_natCast]
end Complex.Hadamard
end
end
section
namespace Complex
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
theorem vcE {f : ℂ → F} {r C : ℝ} {z : ℂ}
    (hd : Differentiable ℂ f) (hrpos : 0 < r)
    (hz : z ∈ Metric.ball (0 : ℂ) r) (hsphere : ∀ u : ℂ, ‖u‖ = r → ‖f u‖ ≤ C) :
    ‖f z‖ ≤ C := by
  let U : Set ℂ := Metric.ball (0 : ℂ) r
  have hfront : ∀ u ∈ frontier U, ‖f u‖ ≤ C := by
    intro u hu
    have hur : ‖u‖ = r := by
      have hfront' : frontier (Metric.ball (0 : ℂ) r) = Metric.sphere (0 : ℂ) r := by
        simpa using (frontier_ball (x := (0 : ℂ)) (r := r) (ne_of_gt hrpos))
      have : u ∈ Metric.sphere (0 : ℂ) r := by simpa [U, hfront'] using hu
      simpa [Metric.mem_sphere, dist_zero_right] using this
    exact hsphere u hur
  exact norm_le_of_forall_mem_frontier_norm_le (f := f) (U := U) Metric.isBounded_ball
    hd.diffContOnCl hfront (subset_closure hz)
end Complex
end
section
namespace Complex
namespace CartanBound
open Real MeasureTheory intervalIntegral
open scoped Topology ENNReal
private lemma vfN {x : ℝ} (hx : 0 < x) (hxle : x ≤ 1) :
    -Real.log x ≤ Real.sqrt (2 / x) := by
  have hx0 : 0 ≤ x := le_of_lt hx
  have ht : 0 ≤ -Real.log x := by
    have : Real.log x ≤ 0 := Real.log_nonpos hx0 hxle
    linarith
  have hsq_div_two_le_exp : ∀ {t : ℝ}, 0 ≤ t → t ^ 2 / 2 ≤ Real.exp t := by
    intro t ht
    let g : ℝ → ℝ := fun u => Real.exp u - u ^ 2 / 2
    have hg_cont : ContinuousOn g (Set.Ici (0 : ℝ)) := by
      have : Continuous g := by fun_prop
      simpa using this.continuousOn
    have hg_diff : DifferentiableOn ℝ g (interior (Set.Ici (0 : ℝ))) := by
      intro u hu
      have : DifferentiableAt ℝ g u := by fun_prop
      exact this.differentiableWithinAt
    have hg'_nonneg : ∀ u ∈ interior (Set.Ici (0 : ℝ)), 0 ≤ deriv g u := by
      intro u hu
      have hu0 : 0 < u := by simpa [interior_Ici] using hu
      have hderiv : deriv g u = Real.exp u - u := by
        have hExp : HasDerivAt Real.exp (Real.exp u) u := Real.hasDerivAt_exp u
        have hpow2 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * u) u := by
          simpa using! ((hasDerivAt_id u).pow 2)
        have hpow2_div : HasDerivAt (fun z : ℝ => z ^ 2 / 2) u u := by
          simpa using (hpow2.div_const (2 : ℝ))
        have hG : HasDerivAt g (Real.exp u - u) u := by
          simpa [g] using! hExp.sub hpow2_div
        exact hG.deriv
      have hu_le : u ≤ Real.exp u := by
        have h1 : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
        exact (le_trans (le_add_of_nonneg_right (by norm_num)) h1)
      have : 0 ≤ Real.exp u - u := sub_nonneg.2 hu_le
      simpa [hderiv] using this
    have hg_mono : MonotoneOn g (Set.Ici (0 : ℝ)) :=
      monotoneOn_of_deriv_nonneg (D := Set.Ici (0 : ℝ)) (hD := convex_Ici 0)
        hg_cont hg_diff hg'_nonneg
    have hg0 : g 0 = 1 := by simp [g]
    have hle : g 0 ≤ g t := hg_mono (by simp) (by simpa [Set.mem_Ici] using ht) ht
    have : (1 : ℝ) ≤ Real.exp t - t ^ 2 / 2 := by simpa [g, hg0] using hle
    linarith
  have hmain : (-Real.log x) ^ 2 / 2 ≤ Real.exp (-Real.log x) := hsq_div_two_le_exp ht
  have hexp : Real.exp (-Real.log x) = x⁻¹ := by simp [Real.exp_neg, Real.exp_log hx]
  have hsq2 : (-Real.log x) ^ 2 ≤ 2 * Real.exp (-Real.log x) := by nlinarith [hmain]
  have hsq' : (-Real.log x) ^ 2 ≤ 2 / x := by simpa [hexp, div_eq_mul_inv, mul_assoc] using hsq2
  have hy : 0 ≤ 2 / x := div_nonneg (by norm_num) (le_of_lt hx)
  exact (Real.le_sqrt ht hy).2 hsq'
lemma vds {t : ℝ} :
    Real.posLog (1 / |1 - t|) ≤ Real.sqrt (2 / |1 - t|) := by
  by_cases ht : |1 - t| ≤ 1
  · by_cases h0 : |1 - t| = 0
    · have : t = 1 := by
        have : 1 - t = 0 := by simpa [abs_eq_zero] using h0
        linarith
      subst this
      simp
    · have hpos : 0 < |1 - t| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0)
      have hle : -Real.log |1 - t| ≤ Real.sqrt (2 / |1 - t|) :=
        vfN (x := |1 - t|) hpos ht
      have hlog : Real.log (1 / |1 - t|) = -Real.log |1 - t| := by simp [Real.log_inv]
      have hnonneg : 0 ≤ Real.log (1 / |1 - t|) := by
        exact Real.log_nonneg ((one_le_div hpos).2 ht)
      have hmax : Real.posLog (1 / |1 - t|) = Real.log (1 / |1 - t|) :=
        max_eq_right hnonneg
      calc
        Real.posLog (1 / |1 - t|) = Real.log (1 / |1 - t|) := hmax
        _ = -Real.log |1 - t| := hlog
        _ ≤ Real.sqrt (2 / |1 - t|) := hle
  · have hlt : 1 < |1 - t| := lt_of_not_ge ht
    have hle0 : Real.log (1 / |1 - t|) ≤ 0 := by
      have hpos : 0 < |1 - t| := lt_trans (by norm_num) hlt
      have : (1 / |1 - t| : ℝ) ≤ 1 := (div_le_one hpos).2 (le_of_lt hlt)
      exact le_trans (Real.log_le_log (by positivity) this) (by simp)
    have hmax : Real.posLog (1 / |1 - t|) = 0 := max_eq_left hle0
    have hrhs : 0 ≤ Real.sqrt (2 / |1 - t|) := by
      exact Real.sqrt_nonneg _
    rw [hmax]
    exact hrhs
noncomputable def φ (t : ℝ) : ℝ :=
  log⁺ (1 / |1 - t|)
lemma vgh : Measurable φ := by
  unfold φ
  simpa [Real.posLog_def, Real.posLog] using
    (by fun_prop : Measurable fun t : ℝ => max 0 (Real.log (1 / |1 - t|)))
lemma vfp {t : ℝ} (ht : t ≤ (1 / 2 : ℝ)) : φ t ≤ Real.log 2 := by
  have hnonneg : 0 ≤ (1 - t : ℝ) := by linarith
  have hden : (1 / 2 : ℝ) ≤ |1 - t| := by
    have : (1 / 2 : ℝ) ≤ (1 - t : ℝ) := by linarith
    simpa [abs_of_nonneg hnonneg] using this
  have hfrac : (1 / |1 - t| : ℝ) ≤ 2 := by
    have hhalfpos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
    have := one_div_le_one_div_of_le hhalfpos hden
    simpa [one_div, div_eq_mul_inv] using this
  have hposLog : log⁺ (1 / |1 - t|) ≤ log⁺ (2 : ℝ) :=
    Real.posLog_le_posLog (by positivity) hfrac
  have habs : (1 : ℝ) ≤ |(2 : ℝ)| := by
    simp
  have hposLog2 : (log⁺ (2 : ℝ)) = Real.log 2 := by
    simpa using (Real.posLog_eq_log habs)
  simpa [φ, hposLog2] using hposLog
lemma veg {t : ℝ} (ht : (1 : ℝ) ≤ |1 - t|) : φ t = 0 := by
  have hpos : 0 < |1 - t| := lt_of_lt_of_le (by norm_num) ht
  have hfrac : (1 / |1 - t| : ℝ) ≤ 1 := (div_le_one hpos).2 ht
  have habs : |(1 / |1 - t| : ℝ)| ≤ 1 := by
    have hnonneg : 0 ≤ (1 / |1 - t| : ℝ) := by positivity
    simpa [abs_of_nonneg hnonneg] using hfrac
  have : log⁺ (1 / |1 - t|) = 0 := (Real.posLog_eq_zero_iff _).2 habs
  simpa [φ] using this
lemma viw (t : ℝ) : 0 ≤ φ t := by
  simpa [φ] using (Real.posLog_nonneg (x := (1 / |1 - t|)))
lemma vhS (t : ℝ) : φ t ≤ Real.sqrt (2 / |1 - t|) := by
  simpa [φ, Real.posLog] using
    vds (t := t)
lemma vbE {A B : ℝ} (hAB : A ≤ B) {g : ℝ → ℝ}
    (hg : ∀ t, 0 ≤ g t) (h : ∀ t ∈ Set.Icc A B, φ t ≤ g t) :
    (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A B))] fun t => ‖g t‖ := by
  refine
    MeasureTheory.ae_restrict_of_forall_mem (μ := (volume : MeasureTheory.Measure ℝ))
    (s := Set.uIoc A B)
      (by simpa using (measurableSet_uIoc : MeasurableSet (Set.uIoc A B))) ?_
  intro t ht
  have htIoc : t ∈ Set.Ioc A B := by
    simpa [Set.uIoc_of_le hAB] using ht
  have htIcc : t ∈ Set.Icc A B := ⟨le_of_lt htIoc.1, htIoc.2⟩
  have hle : φ t ≤ g t := h t htIcc
  have hφ0 : 0 ≤ φ t := viw t
  have hg0 : 0 ≤ g t := hg t
  simpa [Real.norm_eq_abs, abs_of_nonneg hφ0, abs_of_nonneg hg0] using hle
lemma vev {u a : ℂ} {r : ℝ}
    (hur : ‖u‖ = r) (ha : a ≠ 0) (hr : r ≠ ‖a‖) :
    Real.log ‖(1 : ℂ) - u / a‖ ≥ -φ (r / ‖a‖) := by
  have ha_norm : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hnorm_eq : ‖(1 : ℂ) - u / a‖ = ‖a - u‖ / ‖a‖ := by
    have : (1 : ℂ) - u / a = (a - u) / a := by
      field_simp [ha]
    calc
      ‖(1 : ℂ) - u / a‖ = ‖(a - u) / a‖ := by simp [this]
      _ = ‖a - u‖ / ‖a‖ := by simp
  have hrev : |‖a‖ - ‖u‖| ≤ ‖a - u‖ := by
    simpa using (abs_norm_sub_norm_le a u)
  have hdiv : |‖a‖ - ‖u‖| / ‖a‖ ≤ ‖a - u‖ / ‖a‖ :=
    div_le_div_of_nonneg_right hrev (le_of_lt ha_norm)
  have habs : |1 - (r / ‖a‖)| = |‖a‖ - ‖u‖| / ‖a‖ := by
    have hu : ‖u‖ = r := hur
    have ha0 : (‖a‖ : ℝ) ≠ 0 := ha_norm.ne'
    have h1 : (1 : ℝ) - (r / ‖a‖) = (‖a‖ - r) / ‖a‖ := by
      field_simp [ha0]
    calc
      |1 - (r / ‖a‖)| = |(‖a‖ - r) / ‖a‖| := by simp [h1]
      _ = |‖a‖ - r| / ‖a‖ := by simp [abs_div, abs_of_pos ha_norm]
      _ = |‖a‖ - ‖u‖| / ‖a‖ := by simp [hu]
  have hnorm_ge : |1 - (r / ‖a‖)| ≤ ‖(1 : ℂ) - u / a‖ := by
    have : |1 - (r / ‖a‖)| ≤ ‖a - u‖ / ‖a‖ := by
      rw [habs]
      exact hdiv
    rwa [hnorm_eq]
  have hx0 : 0 < |1 - (r / ‖a‖)| := by
    have : (1 - (r / ‖a‖) : ℝ) ≠ 0 := by
      intro h0
      have : r = ‖a‖ := by
        have : r / ‖a‖ = (1 : ℝ) := by linarith
        simpa using (div_eq_iff ha_norm.ne').1 this
      exact hr this
    have : |1 - (r / ‖a‖)| ≠ 0 := by
      simpa [abs_eq_zero] using this
    exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm this)
  have hlogx :
      Real.log |1 - (r / ‖a‖)| ≥ -φ (r / ‖a‖) := by
    have := Real.vgo (x := |1 - (r / ‖a‖)|)
    simpa [φ, one_div, inv_inv, abs_sub_comm, sub_eq_add_neg] using this
  have hlog_mono :
      Real.log |1 - (r / ‖a‖)| ≤ Real.log ‖(1 : ℂ) - u / a‖ :=
    Real.log_le_log (by positivity) hnorm_ge
  linarith [hlog_mono, hlogx]
noncomputable def K : ℝ :=
  ∫ (t : ℝ) in (1 / 4 : ℝ)..(4 : ℝ), Real.sqrt (2 / |1 - t|) ∂volume
lemma vhC : 0 ≤ K := by
  have hle : (1 / 4 : ℝ) ≤ (4 : ℝ) := by norm_num
  have hnn : ∀ t ∈ Set.Icc (1 / 4 : ℝ) (4 : ℝ), 0 ≤ Real.sqrt (2 / |1 - t|) := by
    intro _t _ht
    exact Real.sqrt_nonneg _
  simpa [K] using (intervalIntegral.integral_nonneg
    (μ := (volume : MeasureTheory.Measure ℝ)) hle hnn)
noncomputable def Cφ : ℝ :=
  Real.log 2 + 4 * K + 1
lemma vij : 0 < Cφ := by
  have hlog : 0 < Real.log 2 := by
    simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hK : 0 ≤ K := vhC
  have : 0 < Real.log 2 + 4 * K := by nlinarith
  have : 0 < Real.log 2 + 4 * K + 1 := by linarith
  simpa [Cφ] using this
lemma vbd :
    IntervalIntegrable
      (fun t : ℝ => Real.sqrt (2 / |1 - t|))
      volume (1 / 4 : ℝ) (4 : ℝ) := by
  let f : ℝ → ℝ := fun u => Real.sqrt (2 / |u|)
  have hf0 : IntervalIntegrable f volume (0 : ℝ) (3 : ℝ) := by
    have hpow :
        IntervalIntegrable (fun u : ℝ => u ^ (- (2⁻¹ : ℝ))) volume (0 : ℝ) (3 : ℝ) := by
      simpa using
        (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := (3 : ℝ))
          (r := (- (2⁻¹ : ℝ))) (by linarith : (-1 : ℝ) < - (2⁻¹ : ℝ)))
    have hpow2 :
        IntervalIntegrable (fun u : ℝ => Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ))) volume (0 : ℝ) (3 : ℝ) :=
      hpow.const_mul (Real.sqrt 2)
    have hEq :
        Set.EqOn f (fun u : ℝ => Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ))) (Set.uIoc (0 : ℝ) (3 : ℝ)) := by
      intro u hu
      have hu' : u ∈ Set.Ioc (0 : ℝ) (3 : ℝ) := by
        simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 3 by norm_num)] using hu
      have hu0 : 0 < u := hu'.1
      have hu0' : 0 ≤ u := le_of_lt hu0
      have habs : |u| = u := abs_of_nonneg hu0'
      have : f u = Real.sqrt (2 / u) := by simp [f, habs]
      calc
        f u = Real.sqrt (2 / u) := this
        _ = Real.sqrt 2 / Real.sqrt u := by simp
        _ = Real.sqrt 2 * (Real.sqrt u)⁻¹ := by simp [div_eq_mul_inv]
        _ = Real.sqrt 2 * (u ^ (2⁻¹ : ℝ))⁻¹ := by simp [Real.sqrt_eq_rpow]
        _ = Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ)) := by
              have h : (u ^ (2⁻¹ : ℝ))⁻¹ = u ^ (- (2⁻¹ : ℝ)) := by
                simpa using (Real.rpow_neg hu0' (2⁻¹ : ℝ)).symm
              simp [h]
    exact
      (IntervalIntegrable.congr (a := (0 : ℝ)) (b := (3 : ℝ))
          (μ := (volume : MeasureTheory.Measure ℝ))
          (f := fun u : ℝ => Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ))) (g := f) hEq.symm)
        hpow2
  have hf0' : IntervalIntegrable f volume (0 : ℝ) (3 / 4 : ℝ) :=
    hf0.mono_set (by
      intro u hu
      have hsub : Set.uIcc (0 : ℝ) (3 / 4 : ℝ) ⊆ Set.uIcc (0 : ℝ) (3 : ℝ) := by
        refine Set.uIcc_subset_uIcc ?_ ?_
        · simp
        · have h0 : (0 : ℝ) ≤ (3 / 4 : ℝ) := by nlinarith
          have h1 : (3 / 4 : ℝ) ≤ (3 : ℝ) := by nlinarith
          exact (Set.mem_uIcc).2 (Or.inl ⟨h0, h1⟩)
      exact hsub hu)
  have hleft :
      IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume (1 / 4 : ℝ) (1 : ℝ) := by
    have htmp :
        IntervalIntegrable (fun t : ℝ => f (1 - t)) volume (1 : ℝ) ((1 : ℝ) - (3 / 4 : ℝ)) := by
      simpa using (hf0'.comp_sub_left (c := (1 : ℝ)))
    have htmp' :
        IntervalIntegrable (fun t : ℝ => f (1 - t)) volume ((1 : ℝ) - (3 / 4 : ℝ)) (1 : ℝ) :=
      htmp.symm
    have hsub : ((1 : ℝ) - (3 / 4 : ℝ)) = (1 / 4 : ℝ) := by norm_num
    have htmp'' : IntervalIntegrable (fun t : ℝ => f (1 - t)) volume (1 / 4 : ℝ) (1 : ℝ) := by
      simpa [hsub] using htmp'
    simpa [f] using htmp''
  have hright :
      IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume (1 : ℝ) (4 : ℝ) := by
    have htmp :
        IntervalIntegrable (fun t : ℝ => f (t - 1)) volume (1 : ℝ) ((3 : ℝ) + (1 : ℝ)) := by
      simpa using (hf0.comp_sub_right (c := (1 : ℝ)))
    have hsub : ((3 : ℝ) + (1 : ℝ)) = (4 : ℝ) := by norm_num
    have htmp' : IntervalIntegrable (fun t : ℝ => f (t - 1)) volume (1 : ℝ) (4 : ℝ) := by
      simpa [hsub] using htmp
    have hcongr :
        Set.EqOn (fun t : ℝ => f (t - 1)) (fun t : ℝ => Real.sqrt (2 / |1 - t|))
          (Set.uIoc (1 : ℝ) (4 : ℝ)) := by
      intro t _ht
      simp [f, abs_sub_comm]
    exact
      (IntervalIntegrable.congr (a := (1 : ℝ)) (b := (4 : ℝ))
          (μ := (volume : MeasureTheory.Measure ℝ))
          (f := fun t : ℝ => f (t - 1)) (g := fun t : ℝ => Real.sqrt (2 / |1 - t|)) hcongr)
        htmp'
  exact hleft.trans hright
lemma vby {A t : ℝ} (hA : A ≤ (1 / 4 : ℝ))
    (ht : t ∈ Set.Icc A (2 * A)) :
    φ t ≤ Real.log 2 := by
  have ht_le : t ≤ (1 / 2 : ℝ) := by
    exact ht.2.trans (by nlinarith [hA])
  exact vfp ht_le
lemma vet {t : ℝ} (ht : (2 : ℝ) ≤ t) : φ t = 0 := by
  have hden : (1 : ℝ) ≤ |1 - t| := by
    have : (1 : ℝ) ≤ t - 1 := by linarith
    have : (1 : ℝ) ≤ |t - 1| := by
      simpa [abs_of_nonneg (by linarith : 0 ≤ t - 1)] using this
    simpa [abs_sub_comm] using this
  exact veg hden
lemma vbR {A : ℝ} (hA0 : 0 ≤ A)
    (hA : A ≤ (1 / 4 : ℝ)) :
    IntervalIntegrable φ volume A (2 * A) := by
  have hA_le : A ≤ 2 * A := by nlinarith
  have hconst : IntervalIntegrable (fun _ : ℝ => (Real.log 2 : ℝ)) volume A (2 * A) :=
    intervalIntegrable_const
  have hmeas :
      AEStronglyMeasurable (fun t : ℝ => φ t) (volume.restrict (Set.uIoc A (2 * A))) :=
    (vgh.aestronglyMeasurable : _)
  have hdom :
      (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A (2 * A)))]
        fun _ => ‖(Real.log 2 : ℝ)‖ := by
    refine vbE (A := A) (B := 2 * A) hA_le
      (g := fun _ => (Real.log 2 : ℝ)) (hg := fun _ => ?_) ?_
    · simpa using (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
    · intro t ht
      exact vby hA ht
  exact IntervalIntegrable.mono_fun hconst hmeas hdom
lemma vdR {A : ℝ} (hA : (2 : ℝ) ≤ A) :
    IntervalIntegrable φ volume A (2 * A) := by
  have hA_le : A ≤ 2 * A := by nlinarith
  have hEq : Set.EqOn (fun t : ℝ => φ t) (fun _ => (0 : ℝ)) (Set.uIoc A (2 * A)) := by
    intro t ht
    have htIoc : t ∈ Set.Ioc A (2 * A) := by
      simpa [Set.uIoc_of_le hA_le] using ht
    exact vet (le_trans hA (le_of_lt htIoc.1))
  have hz : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume A (2 * A) :=
    intervalIntegrable_const
  exact (IntervalIntegrable.congr (a := A) (b := (2 * A))
    (μ := (volume : MeasureTheory.Measure ℝ))
    (f := fun _ => (0 : ℝ)) (g := fun t => φ t) (by
      intro t ht
      simpa using (hEq (x := t) ht).symm)) hz
lemma vaQ {A : ℝ}
    (hA_lower : (1 / 4 : ℝ) ≤ A) (hA_upper : A ≤ (2 : ℝ)) :
    IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume A (2 * A) := by
  have hsqrt_big :
      IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|))
        (volume : MeasureTheory.Measure ℝ) (1 / 4 : ℝ) (4 : ℝ) :=
    vbd
  refine hsqrt_big.mono_set ?_
  refine Set.uIcc_subset_uIcc ?_ ?_
  · exact (Set.mem_uIcc).2 (Or.inl ⟨hA_lower, by nlinarith [hA_upper]⟩)
  · exact (Set.mem_uIcc).2 (Or.inl ⟨by nlinarith [hA_lower], by nlinarith [hA_upper]⟩)
lemma vbI {A : ℝ}
    (hA_lower : (1 / 4 : ℝ) ≤ A) (hA_upper : A ≤ (2 : ℝ)) :
    IntervalIntegrable φ volume A (2 * A) := by
  have hA_le : A ≤ 2 * A := by nlinarith [hA_lower]
  have hsqrt :
      IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume A (2 * A) :=
    vaQ hA_lower hA_upper
  have hmeas :
      AEStronglyMeasurable (fun t : ℝ => φ t) (volume.restrict (Set.uIoc A (2 * A))) :=
    (vgh.aestronglyMeasurable : _)
  have hdom :
      (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A (2 * A)))]
        fun t => ‖Real.sqrt (2 / |1 - t|)‖ := by
    refine vbE (A := A) (B := 2 * A) hA_le
      (g := fun t => Real.sqrt (2 / |1 - t|)) (hg := fun _ => Real.sqrt_nonneg _) ?_
    intro t _ht
    exact vhS t
  exact IntervalIntegrable.mono_fun hsqrt hmeas hdom
lemma veI {A : ℝ} (hA : 0 ≤ A) :
    IntervalIntegrable φ volume A (2 * A) := by
  by_cases hA0 : A = 0
  · subst hA0
    simp
  cases le_total A (1 / 4 : ℝ) with
  | inl hsmall =>
      exact vbR hA hsmall
  | inr hge_quarter =>
      cases le_total (2 : ℝ) A with
      | inl hbig =>
          exact vdR hbig
      | inr hA_le_two =>
          exact vbI hge_quarter hA_le_two
lemma vdl {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    IntervalIntegrable (fun r : ℝ => φ (r / a)) volume R (2 * R) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hRa_nonneg : 0 ≤ R / a := by
    exact div_nonneg hR (le_of_lt ha)
  have hφ : IntervalIntegrable φ volume (R / a) (2 * (R / a)) :=
    veI (A := (R / a)) hRa_nonneg
  have := (hφ.comp_mul_right (c := (a⁻¹ : ℝ)))
  have hupper : a * (R * (a⁻¹ * 2)) = (2 * R) := by
    field_simp [ha0]
  simpa [div_eq_mul_inv, ha0, hupper, mul_assoc, mul_left_comm, mul_comm] using this
lemma vin : Real.log 2 ≤ Cφ := by
  dsimp [Cφ]
  have hK : 0 ≤ K := vhC
  linarith [hK]
lemma vfq : (4 * K + 1 : ℝ) ≤ Cφ := by
  dsimp [Cφ]
  have hlog_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith [hlog_nonneg]
lemma veF {A : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ (1 / 4 : ℝ)) :
    (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ Cφ * A := by
  have hA_le : A ≤ 2 * A := by nlinarith
  have hφ_int : IntervalIntegrable φ volume A (2 * A) :=
    vbR hA0 hA
  have hconst : IntervalIntegrable (fun _ : ℝ => (Real.log 2 : ℝ)) volume A (2 * A) :=
    intervalIntegrable_const
  have hle_int :
      (∫ (t : ℝ) in A..(2 * A), φ t ∂volume)
        ≤ ∫ (t : ℝ) in A..(2 * A), (Real.log 2 : ℝ) ∂volume := by
    refine intervalIntegral.integral_mono_on (μ := (volume : MeasureTheory.Measure ℝ))
      hA_le hφ_int hconst ?_
    intro t ht
    exact vby hA ht
  have hRHS :
      (∫ (t : ℝ) in A..(2 * A), (Real.log 2 : ℝ) ∂volume) = A * Real.log 2 := by
    simp [intervalIntegral.integral_const, sub_eq_add_neg, add_assoc, two_mul]
  have hcoef : A * Real.log 2 ≤ Cφ * A := by
    have := mul_le_mul_of_nonneg_left vin hA0
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  exact le_trans (by simpa [hRHS] using hle_int) hcoef
lemma veE {A : ℝ} (hA : (2 : ℝ) ≤ A) :
    (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ Cφ * A := by
  have hA_le : A ≤ 2 * A := by nlinarith
  have hφ0 : Set.EqOn (fun t : ℝ => φ t) (fun _ => (0 : ℝ)) (Set.uIcc A (2 * A)) := by
    intro t ht
    have ht' : t ∈ Set.Icc A (2 * A) := by
      simpa [Set.uIcc_of_le hA_le] using ht
    exact vet (le_trans hA ht'.1)
  have hzero : (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) = 0 := by
    simpa using intervalIntegral.integral_congr (μ := (volume : MeasureTheory.Measure ℝ)) hφ0
  have hnonneg : (0 : ℝ) ≤ Cφ * A := mul_nonneg (le_of_lt vij) (by linarith)
  simpa [hzero] using hnonneg
lemma vbT {A : ℝ}
    (hA_lower : (1 / 4 : ℝ) ≤ A) (hA_upper : A ≤ (2 : ℝ)) :
    (∫ (t : ℝ) in A..(2 * A), Real.sqrt (2 / |1 - t|) ∂volume) ≤ K := by
  let s (t : ℝ) : ℝ := Real.sqrt (2 / |1 - t|)
  have hA_le : A ≤ 2 * A := by nlinarith [hA_lower]
  have hA_upper' : (2 * A : ℝ) ≤ 4 := by nlinarith [hA_upper]
  have hsqrt_big : IntervalIntegrable s volume (1 / 4 : ℝ) (4 : ℝ) := by
    simpa [s] using vbd
  have hle_K :
      (∫ (t : ℝ) in A..(2 * A), s t ∂volume)
        ≤ ∫ (t : ℝ) in (1 / 4 : ℝ)..(4 : ℝ), s t ∂volume := by
    refine intervalIntegral.integral_mono_interval (μ := (volume : MeasureTheory.Measure ℝ))
      (c := (1 / 4 : ℝ)) (d := (4 : ℝ)) (a := A) (b := (2 * A))
      hA_lower hA_le hA_upper' ?_ hsqrt_big
    exact Filter.Eventually.of_forall (fun _t => Real.sqrt_nonneg _)
  simpa [K, s] using hle_K
lemma vcS {A : ℝ} (hA : (1 / 4 : ℝ) ≤ A) :
    K ≤ (4 * K + 1) * A := by
  have hcoef : 1 ≤ 4 * A := by nlinarith [hA]
  have hK : 0 ≤ K := vhC
  nlinarith [hK, hcoef]
lemma veD {A : ℝ}
    (hA_lower : (1 / 4 : ℝ) ≤ A) (hA_upper : A ≤ (2 : ℝ)) :
    (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ Cφ * A := by
  let s (t : ℝ) : ℝ := Real.sqrt (2 / |1 - t|)
  have hA_le : A ≤ 2 * A := by nlinarith [hA_lower]
  have hφ_int : IntervalIntegrable φ volume A (2 * A) :=
    vbI hA_lower hA_upper
  have hsqrt : IntervalIntegrable s volume A (2 * A) := by
    simpa [s] using
      vaQ hA_lower hA_upper
  have hle_int :
      (∫ (t : ℝ) in A..(2 * A), φ t ∂volume)
        ≤ ∫ (t : ℝ) in A..(2 * A), s t ∂volume := by
    refine intervalIntegral.integral_mono_on
      (μ := (volume : MeasureTheory.Measure ℝ)) hA_le hφ_int hsqrt ?_
    intro t _ht
    exact vhS t
  have hsqrt_le : (∫ (t : ℝ) in A..(2 * A), s t ∂volume) ≤ (4 * K + 1) * A := by
    have hK : (∫ (t : ℝ) in A..(2 * A), s t ∂volume) ≤ K := by
      simpa [s] using vbT hA_lower hA_upper
    exact le_trans hK (vcS hA_lower)
  have hcoef : (4 * K + 1 : ℝ) * A ≤ Cφ * A :=
    mul_le_mul_of_nonneg_right vfq (by nlinarith [hA_lower])
  exact le_trans hle_int (le_trans hsqrt_le hcoef)
lemma vfP {A : ℝ} (hA : 0 ≤ A) :
    (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ Cφ * A := by
  by_cases hA0 : A = 0
  · subst hA0
    simp [Cφ, φ, K]
  cases le_total A (1 / 4 : ℝ) with
  | inl hsmall =>
      exact veF hA hsmall
  | inr hge_quarter =>
      cases le_total (2 : ℝ) A with
      | inl hbig =>
          exact veE hbig
      | inr hA_le_two =>
          exact veD hge_quarter hA_le_two
open scoped BigOperators
lemma vff {R : ℝ} (hR : 0 < R) :
    (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2 * R)) ≠ 0 := by
  have hpos : (0 : ℝ) < 2 * R - R := by nlinarith [hR]
  simp [Real.volume_Ioc, ENNReal.ofReal_eq_zero, not_le_of_gt hpos]
lemma vdr (bad : Finset ℝ) {R : ℝ} (hR : 0 < R) :
    (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2 * R) \ (bad : Set ℝ)) ≠ 0 := by
  have hbad_meas : (volume : MeasureTheory.Measure ℝ) (bad : Set ℝ) = 0 := by
    simpa using (bad.measure_zero (μ := (volume : MeasureTheory.Measure ℝ)))
  have hdiff :
      (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2 * R) \ (bad : Set ℝ))
        = (volume : MeasureTheory.Measure ℝ) (Set.Ioc R (2 * R)) := by
    simpa [Set.sdiff_eq, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
      (MeasureTheory.measure_sdiff_null (s := Set.Ioc R (2 * R)) (t := (bad : Set ℝ))
        hbad_meas)
  simpa [hdiff] using vff hR
lemma vcp (bad : Finset ℝ) {R : ℝ} (hR : 0 < R) :
    (volume.restrict (Set.Ioc R (2 * R))) (Set.Ioc R (2 * R) \ (bad : Set ℝ)) ≠ 0 := by
  have hsubset : Set.Ioc R (2 * R) \ (bad : Set ℝ) ⊆ Set.Ioc R (2 * R) := by
    intro r hr
    exact hr.1
  have hinter :
      (Set.Ioc R (2 * R) \ (bad : Set ℝ)) ∩ Set.Ioc R (2 * R)
        = (Set.Ioc R (2 * R) \ (bad : Set ℝ)) := by
    exact Set.inter_eq_left.mpr hsubset
  simpa [MeasureTheory.Measure.restrict_apply, measurableSet_Ioc, hinter] using
    vdr bad hR
lemma vfb {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    (∫ (r : ℝ) in R..(2 * R), φ (r / a) ∂volume) ≤ Cφ * R := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hrew :
      (∫ (r : ℝ) in R..(2 * R), φ (r / a) ∂volume)
        = a * (∫ (t : ℝ) in (R / a)..(2 * R / a), φ t ∂volume) := by
    simp [smul_eq_mul, mul_left_comm, mul_comm, div_eq_mul_inv, ha0]
  rw [hrew]
  have hA : 0 ≤ R / a := by
    exact div_nonneg hR ha.le
  have hle : (∫ (t : ℝ) in (R / a)..(2 * (R / a)), φ t ∂volume) ≤ Cφ * (R / a) :=
    vfP (A := R / a) hA
  have hEq : (2 * R / a) = 2 * (R / a) := by ring
  have hle' :
      (∫ (t : ℝ) in (R / a)..(2 * R / a), φ t ∂volume) ≤ Cφ * (R / a) := by
    simpa [hEq] using hle
  have ha_nonneg : 0 ≤ a := ha.le
  have := mul_le_mul_of_nonneg_left hle' ha_nonneg
  have hRHS : a * (Cφ * (R / a)) = Cφ * R := by
    field_simp [ha0]
  simpa [hRHS, mul_assoc, mul_left_comm, mul_comm] using this
lemma vea
    {ι : Type} (s : Finset ι) (w : ι → ℝ) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (∑ i ∈ s, fun r : ℝ => w i * φ (r / a i))
      volume R (2 * R) := by
  refine IntervalIntegrable.sum (μ := volume) (a := R) (b := 2 * R)
    (s := s) (f := fun i : ι => fun r : ℝ => w i * φ (r / a i)) ?_
  intro i hi
  have hφi : IntervalIntegrable (fun r : ℝ => φ (r / a i)) volume R (2 * R) :=
    vdl (a := a i) (R := R) (ha i hi) hR
  simpa [mul_assoc] using hφi.const_mul (w i)
lemma vdm
    {ι : Type} (s : Finset ι) (w : ι → ℝ) (a : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (ha : ∀ i ∈ s, 0 < a i) {R : ℝ} (hR : 0 ≤ R) :
    (∫ r in R..(2 * R), (∑ i ∈ s, fun r : ℝ => w i * φ (r / a i)) r ∂volume)
      ≤ Cφ * (∑ i ∈ s, w i) * R := by
  have hint : ∀ i ∈ s, IntervalIntegrable (fun r : ℝ => w i * φ (r / a i))
      volume R (2 * R) := by
    intro i hi
    have hφi : IntervalIntegrable (fun r : ℝ => φ (r / a i)) volume R (2 * R) :=
      vdl (a := a i) (R := R) (ha i hi) hR
    simpa [mul_assoc] using hφi.const_mul (w i)
  have hsum_int :
      (∫ r in R..(2 * R), (∑ i ∈ s, fun r : ℝ => w i * φ (r / a i)) r ∂volume)
        = ∑ i ∈ s, ∫ r in R..(2 * R), (fun r : ℝ => w i * φ (r / a i)) r
            ∂volume := by
    simpa using
      (intervalIntegral.integral_finsetSum (μ := volume) (a := R) (b := 2 * R)
        (s := s) (f := fun i : ι => fun r : ℝ => w i * φ (r / a i)) hint)
  rw [hsum_int]
  have hsum_le :
      (∑ i ∈ s, ∫ r in R..(2 * R), (fun r : ℝ => w i * φ (r / a i)) r ∂volume)
        ≤ ∑ i ∈ s, w i * (Cφ * R) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hphi :
        (∫ r in R..(2 * R), φ (r / a i) ∂volume) ≤ Cφ * R :=
      vfb (a := a i) (R := R) (ha i hi) hR
    have := mul_le_mul_of_nonneg_left hphi (hw i hi)
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  refine le_trans hsum_le ?_
  have : (∑ i ∈ s, w i * (Cφ * R)) = Cφ * (∑ i ∈ s, w i) * R := by
    calc
      (∑ i ∈ s, w i * (Cφ * R)) = (∑ i ∈ s, w i) * (Cφ * R) := by
        simp [Finset.sum_mul]
      _ = Cφ * (∑ i ∈ s, w i) * R := by
        ac_rfl
  exact le_of_eq this
lemma vbL
    {ι : Type} (s : Finset ι) (w : ι → ℝ) (a : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (ha : ∀ i ∈ s, 0 < a i)
    (bad : Finset ℝ) {R : ℝ} (hR : 0 < R) :
    ∃ r ∈ Set.Ioc R (2 * R), r ∉ bad ∧
      (∑ i ∈ s, w i * φ (r / a i)) ≤ Cφ * (∑ i ∈ s, w i) := by
  by_contra hbad
  have hforall :
      ∀ r ∈ Set.Ioc R (2 * R), r ∉ bad →
        Cφ * (∑ i ∈ s, w i) < (∑ i ∈ s, w i * φ (r / a i)) := by
    intro r hr hrbad
    have : ¬(∑ i ∈ s, w i * φ (r / a i)) ≤ Cφ * (∑ i ∈ s, w i) := by
      intro hle
      exact hbad ⟨r, hr, hrbad, hle⟩
    exact lt_of_not_ge this
  let g : ℝ → ℝ := ∑ i ∈ s, fun r : ℝ => w i * φ (r / a i)
  have hg_int : IntervalIntegrable g volume R (2 * R) := by
    simpa [g] using vea s w a ha hR.le
  have hconst_int :
      IntervalIntegrable (fun _r : ℝ => Cφ * (∑ i ∈ s, w i)) volume R (2 * R) :=
    intervalIntegrable_const
  have hlt_meas :
      (volume.restrict (Set.Ioc R (2 * R)))
        {r | Cφ * (∑ i ∈ s, w i) < g r} ≠ 0 := by
    have hall : Set.Ioc R (2 * R) \ (bad : Set ℝ) ⊆ {r | Cφ * (∑ i ∈ s, w i) < g r} := by
      intro r hr
      have hrIoc : r ∈ Set.Ioc R (2 * R) := hr.1
      have hrbad : r ∉ bad := by simpa using hr.2
      simpa [g] using hforall r hrIoc hrbad
    have hle :
        (volume.restrict (Set.Ioc R (2 * R))) (Set.Ioc R (2 * R) \ (bad : Set ℝ))
          ≤ (volume.restrict (Set.Ioc R (2 * R))) {r | Cφ * (∑ i ∈ s, w i) < g r} :=
      MeasureTheory.measure_mono hall
    have hpos' :
        (volume.restrict (Set.Ioc R (2 * R))) (Set.Ioc R (2 * R) \ (bad : Set ℝ)) ≠ 0 := by
      exact vcp bad hR
    intro hzero
    have : (volume.restrict (Set.Ioc R (2 * R))) (Set.Ioc R (2 * R) \ (bad : Set ℝ)) = 0 :=
      le_antisymm (le_trans hle (le_of_eq hzero)) (by positivity)
    exact hpos' this
  have hlt_int :
      (∫ r in R..(2 * R), (Cφ * (∑ i ∈ s, w i)) ∂volume)
        < ∫ r in R..(2 * R), g r ∂volume := by
    have hab : R ≤ 2 * R := by nlinarith [hR.le]
    refine intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero (μ := volume)
      (a := R) (b := 2 * R) (f := fun _ => (Cφ * (∑ i ∈ s, w i))) (g := g)
      hab hconst_int hg_int ?_ hlt_meas
    have hmem : ∀ᵐ r ∂ (volume.restrict (Set.Ioc R (2 * R))), r ∈ Set.Ioc R (2 * R) :=
      MeasureTheory.ae_restrict_mem (by simp)
    have hnotBad :
        ∀ᵐ r ∂ (volume.restrict (Set.Ioc R (2 * R))), r ∉ (bad : Set ℝ) := by
      simpa using
        (bad.finite_toSet.countable.ae_notMem (μ := (volume.restrict (Set.Ioc R (2 * R)))))
    filter_upwards [hmem, hnotBad] with r hrIoc hrNotBad
    have hrNotBad' : r ∉ bad := by simpa using hrNotBad
    exact le_of_lt (by simpa [g] using hforall r hrIoc hrNotBad')
  have hconst_eval :
      (∫ r in R..(2 * R), (Cφ * (∑ i ∈ s, w i)) ∂volume) = Cφ * (∑ i ∈ s, w i) * R := by
    simp [intervalIntegral.integral_const, sub_eq_add_neg, mul_comm]
    ring
  have hg_le :
      (∫ r in R..(2 * R), g r ∂volume) ≤ Cφ * (∑ i ∈ s, w i) * R := by
    simpa [g] using vdm s w a hw ha hR.le
  have : ¬(Cφ * (∑ i ∈ s, w i) * R < Cφ * (∑ i ∈ s, w i) * R) := lt_irrefl _
  have hcontra : Cφ * (∑ i ∈ s, w i) * R < Cφ * (∑ i ∈ s, w i) * R := by
    have := hlt_int
    simpa [hconst_eval] using (this.trans_le hg_le)
  exact this hcontra
end CartanBound
end Complex
end
section
noncomputable section
namespace Complex.Hadamard
open Complex Real
lemma vdO
    {m : ℕ} {τ r : ℝ} {u a : ℂ}
    (hur : ‖u‖ = r)
    (hmτ : (m : ℝ) ≤ τ) :
    max 1 (‖u / a‖ ^ m) ≤ 1 + (r / ‖a‖) ^ τ := by
  by_cases hx : ‖u / a‖ ≤ 1
  · have hpowm_le1 : ‖u / a‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg (u / a)) hx
    have hr0 : 0 ≤ r := by simpa [hur] using (norm_nonneg u)
    have hbase : 0 ≤ r / ‖a‖ := div_nonneg hr0 (norm_nonneg a)
    have hnonneg : 0 ≤ (r / ‖a‖) ^ τ := Real.rpow_nonneg hbase τ
    have hle1 : (1 : ℝ) ≤ 1 + (r / ‖a‖) ^ τ := le_add_of_nonneg_right hnonneg
    have hle2 : ‖u / a‖ ^ m ≤ 1 + (r / ‖a‖) ^ τ := hpowm_le1.trans hle1
    exact (max_le_iff).2 ⟨hle1, hle2⟩
  · have hx1 : 1 < ‖u / a‖ := lt_of_not_ge hx
    have hpow :
        (‖u / a‖ : ℝ) ^ (m : ℝ) ≤ (‖u / a‖ : ℝ) ^ τ :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hx1) hmτ
    have hpow' : ‖u / a‖ ^ m ≤ (‖u / a‖ : ℝ) ^ τ := by
      simpa [Real.rpow_natCast] using hpow
    have hmax_add : max 1 (‖u / a‖ ^ m) ≤ 1 + ‖u / a‖ ^ m := by
      refine max_le (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left (by positivity))
    have : max 1 (‖u / a‖ ^ m) ≤ 1 + (‖u / a‖ : ℝ) ^ τ :=
      hmax_add.trans (by nlinarith [hpow'])
    simpa [norm_div, hur] using this
lemma vdt
    {m : ℕ} {τ r : ℝ} {u a : ℂ}
    (hur : ‖u‖ = r) (ha : a ≠ 0) (hr : r ≠ ‖a‖)
    (hmτ : (m : ℝ) ≤ τ) :
    ‖(vae m (u / a))⁻¹‖
      ≤ Real.exp (CartanBound.φ (r / ‖a‖) + (m : ℝ) * (1 + (r / ‖a‖) ^ τ)) := by
  have hlog_one :
      Real.log ‖(1 : ℂ) - u / a‖ ≥ -CartanBound.φ (r / ‖a‖) :=
    CartanBound.vev (hur := hur) (ha := ha) (hr := hr)
  have hbase :=
    vcc (m := m) (z := (u / a))
  have hlogE :
      Real.log ‖vae m (u / a)‖
        ≥ -CartanBound.φ (r / ‖a‖) - (m : ℝ) * max 1 (‖u / a‖ ^ m) := by
    have hpls :=
      vcw m (u / a)
    linarith [hbase, hlog_one, hpls]
  have hmax :
      max 1 (‖u / a‖ ^ m) ≤ 1 + (r / ‖a‖) ^ τ :=
    vdO (m := m) (τ := τ) (r := r) (u := u) (a := a) hur hmτ
  have hneglog :
      -Real.log ‖vae m (u / a)‖
        ≤ CartanBound.φ (r / ‖a‖) + (m : ℝ) * (1 + (r / ‖a‖) ^ τ) := by
    have : -Real.log ‖vae m (u / a)‖
        ≤ CartanBound.φ (r / ‖a‖) + (m : ℝ) * max 1 (‖u / a‖ ^ m) := by
      linarith [hlogE]
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    exact this.trans (by nlinarith [mul_le_mul_of_nonneg_left hmax hm0])
  have hpos : 0 < ‖vae m (u / a)‖ := by
    have : vae m (u / a) ≠ 0 := by
      intro h0
      have : u / a = (1 : ℂ) := (vbb m (u / a)).1 h0
      have : u = a := (div_eq_one_iff_eq ha).1 this
      have : r = ‖a‖ := by simpa [this] using hur.symm
      exact (hr this).elim
    exact norm_pos_iff.2 this
  have hEq :
      ‖(vae m (u / a))⁻¹‖ =
        Real.exp (-Real.log ‖vae m (u / a)‖) := by
    simp [norm_inv, Real.exp_neg, Real.exp_log hpos]
  have := Real.exp_le_exp.2 hneglog
  simpa [hEq] using this
lemma vdC
    {m : ℕ} {τ r : ℝ} {u a : ℂ}
    (hur : ‖u‖ = r) (ha : a ≠ 0)
    (hz : ‖u / a‖ ≤ (1 / 2 : ℝ)) (hτ_le : τ ≤ (m + 1 : ℝ)) :
    ‖(vae m (u / a))⁻¹‖ ≤ Real.exp ((2 : ℝ) * (r / ‖a‖) ^ τ) := by
  by_cases hu : u = 0
  · subst hu
    have hr0 : r = 0 := by simpa [hur] using (norm_zero : ‖(0 : ℂ)‖ = 0)
    subst hr0
    have h0 : 0 ≤ ((0 : ℝ) / ‖a‖) ^ τ := by
      exact Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 0 / ‖a‖) τ
    have h0' : 0 ≤ (2 : ℝ) * ((0 : ℝ) / ‖a‖) ^ τ := mul_nonneg (by norm_num) h0
    have hexp : (1 : ℝ) ≤ Real.exp ((2 : ℝ) * ((0 : ℝ) / ‖a‖) ^ τ) :=
      (Real.one_le_exp_iff).2 h0'
    simpa using hexp
  have hlogE :=
    vcT (m := m) (z := (u / a)) hz
  have hneglog : -Real.log ‖vae m (u / a)‖ ≤ (2 : ℝ) * (r / ‖a‖) ^ τ := by
    have h1 : -Real.log ‖vae m (u / a)‖ ≤ (2 : ℝ) * ‖u / a‖ ^ (m + 1) := by
      linarith [hlogE]
    set x : ℝ := ‖u / a‖
    have hx1 : x ≤ 1 := le_trans (by simpa [x] using hz) (by norm_num)
    have hxpos : 0 < x := by
      simpa [x] using (norm_pos_iff.2 (div_ne_zero hu ha))
    have hτ_le' : τ ≤ ((m + 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one] using hτ_le
    have hpow_rpow : x ^ ((m + 1 : ℕ) : ℝ) ≤ x ^ τ :=
      Real.rpow_le_rpow_of_exponent_ge hxpos hx1 hτ_le'
    have hpow : x ^ (m + 1) ≤ x ^ τ := by
      simpa [← Real.rpow_natCast] using hpow_rpow
    have h2x : (2 : ℝ) * x ^ (m + 1) ≤ (2 : ℝ) * x ^ τ :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    have h2 : (2 : ℝ) * ‖u / a‖ ^ (m + 1) ≤ (2 : ℝ) * (‖u / a‖ : ℝ) ^ τ := by
      simpa [x] using h2x
    have h3 : (‖u‖ / ‖a‖) ^ τ = (r / ‖a‖) ^ τ := by
      simp [hur]
    exact (h1.trans h2).trans_eq (by simp [h3])
  have hpos : 0 < ‖vae m (u / a)‖ := by
    have : vae m (u / a) ≠ 0 := by
      intro h0
      have : u / a = (1 : ℂ) := (vbb m (u / a)).1 h0
      have : u = a := (div_eq_one_iff_eq ha).1 this
      have : (‖u / a‖ : ℝ) = 1 := by simpa [this] using (by simp [ha])
      linarith [hz, this]
    exact norm_pos_iff.2 this
  have hEq :
      ‖(vae m (u / a))⁻¹‖ =
        Real.exp (-Real.log ‖vae m (u / a)‖) := by
    simp [norm_inv, Real.exp_neg, Real.exp_log hpos]
  have := Real.exp_le_exp.2 hneglog
  simpa [hEq] using this
end Complex.Hadamard
end
end
section
noncomputable section
namespace Complex.Hadamard
open scoped BigOperators
open Filter Finset Real Topology
section CartanFiniteSum
variable {α : Type*}
private lemma vaL [DecidableEq α] (s : Finset α) (u : α → ℝ) :
    Summable (fun a => if a ∈ s then u a else 0) :=
  summable_of_ne_finset_zero (s := s) fun a ha => by simp [ha]
private lemma vdv [DecidableEq α] (s : Finset α) (u : α → ℝ) :
    (∑' a, if a ∈ s then u a else 0) = ∑ a ∈ s, u a := by
  classical
  simpa [Finset.sum_ite] using
    (hasSum_sum_of_ne_finset_zero (s := s) (f := fun a => if a ∈ s then u a else 0)
      fun a ha => by simp [ha]).tsum_eq
private lemma viE (u₁ u₂ u₃ u₄ : α → ℝ)
    (h₁ : Summable u₁) (h₂ : Summable u₂) (h₃ : Summable u₃) (h₄ : Summable u₄) :
    tsum (fun a => ((u₁ a + u₂ a) + u₃ a) + u₄ a)
      = tsum u₁ + tsum u₂ + tsum u₃ + tsum u₄ := by
  calc
    tsum (fun a => ((u₁ a + u₂ a) + u₃ a) + u₄ a)
        = tsum (fun a => (u₁ a + u₂ a) + (u₃ a + u₄ a)) := by
          simp [add_comm, add_left_comm]
    _ = tsum (fun a => u₁ a + u₂ a) + tsum (fun a => u₃ a + u₄ a) :=
        Summable.tsum_add (h₁.add h₂) (h₃.add h₄)
    _ = tsum u₁ + tsum u₂ + tsum u₃ + tsum u₄ := by
        rw [Summable.tsum_add h₁ h₂, Summable.tsum_add h₃ h₄]
        ring
end CartanFiniteSum
noncomputable def vaS (m : ℕ) (τ Sτ : ℝ) : ℝ :=
  ((CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 3) * (Sτ + 1)
lemma veP {m : ℕ} {τ Sτ : ℝ} (hSτ : 0 ≤ Sτ) :
    0 ≤ vaS m τ Sτ := by
  have hS : 0 ≤ Sτ + 1 := by linarith
  have hA : 0 ≤ (CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 3 := by
    have hCφ : 0 ≤ CartanBound.Cφ := le_of_lt CartanBound.vij
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have h4τ : 0 ≤ (4 : ℝ) ^ τ := by positivity
    nlinarith [hCφ, hm0, h4τ]
  simpa [vaS] using mul_nonneg hA hS
lemma vaD
    {f : ℂ → ℂ} {r τ : ℝ} (hr : 0 ≤ r)
    (p : vab f (Set.univ : Set ℂ)) :
    (r / ‖vaa p‖) ^ τ =
      (r ^ τ) * ((‖vaa p‖⁻¹ : ℝ) ^ τ) := by
  have hp : 0 ≤ (‖vaa p‖⁻¹ : ℝ) := by positivity
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (Real.mul_rpow (x := r) (y := (‖vaa p‖⁻¹ : ℝ)) (z := τ) hr hp)
lemma vcX
    {f : ℂ → ℂ} {r τ : ℝ} (hr : 0 ≤ r) :
    (∑' p : vab f (Set.univ : Set ℂ),
        (r / ‖vaa p‖) ^ τ)
      = (r ^ τ) * ∑' p : vab f (Set.univ : Set ℂ),
          ‖vaa p‖⁻¹ ^ τ := by
  calc
    (∑' p : vab f (Set.univ : Set ℂ),
        (r / ‖vaa p‖) ^ τ)
        = ∑' p : vab f (Set.univ : Set ℂ),
            (r ^ τ) * (‖vaa p‖⁻¹ : ℝ) ^ τ := by
            refine tsum_congr ?_
            intro p
            exact vaD (f := f) (τ := τ) hr p
    _ = (r ^ τ) * ∑' p : vab f (Set.univ : Set ℂ),
          ‖vaa p‖⁻¹ ^ τ := by
        simp [tsum_mul_left]
lemma vck
    {f : ℂ → ℂ} {r τ : ℝ} (hr : 0 ≤ r) (hτ_nonneg : 0 ≤ τ) :
    (∑' p : vab f (Set.univ : Set ℂ),
        (2 : ℝ) * (r / ‖vaa p‖) ^ τ)
      ≤ (2 : ℝ) * ((∑' p : vab f (Set.univ : Set ℂ),
          ‖vaa p‖⁻¹ ^ τ) + 1) * (1 + r) ^ τ := by
  set Sτ : ℝ :=
    ∑' p : vab f (Set.univ : Set ℂ), ‖vaa p‖⁻¹ ^ τ
  have htsum :
      (∑' p : vab f (Set.univ : Set ℂ),
          (2 : ℝ) * (r / ‖vaa p‖) ^ τ)
        = (2 : ℝ) * (r ^ τ) * Sτ := by
    calc
      (∑' p : vab f (Set.univ : Set ℂ),
          (2 : ℝ) * (r / ‖vaa p‖) ^ τ)
          = (2 : ℝ) * ∑' p : vab f (Set.univ : Set ℂ),
              (r / ‖vaa p‖) ^ τ := by
              simp [tsum_mul_left]
      _ = (2 : ℝ) * ((r ^ τ) * Sτ) := by
              rw [vcX (f := f) (τ := τ) hr]
      _ = (2 : ℝ) * (r ^ τ) * Sτ := by ring
  have hSτ_nonneg : 0 ≤ Sτ :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _)
  have h1r : r ^ τ ≤ (1 + r) ^ τ :=
    Real.rpow_le_rpow (by positivity) (by linarith) hτ_nonneg
  have hS : Sτ ≤ Sτ + 1 := by linarith
  have hle : (r ^ τ) * Sτ ≤ (1 + r) ^ τ * (Sτ + 1) :=
    mul_le_mul h1r hS (by linarith) (by positivity)
  rw [htsum]
  have : (2 : ℝ) * (r ^ τ) * Sτ ≤ (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ := by
    nlinarith [hle]
  simpa [Sτ, mul_assoc, mul_left_comm, mul_comm] using this
lemma vdd
    {f : ℂ → ℂ} {r τ : ℝ} (small : Finset (vab f (Set.univ : Set ℂ)))
    (hr : 0 ≤ r) (hτ_nonneg : 0 ≤ τ)
    (hsumτ :
      Summable (fun p : vab f (Set.univ : Set ℂ) =>
        ‖vaa p‖⁻¹ ^ τ)) :
    (∑ p ∈ small, (r / ‖vaa p‖) ^ τ)
      ≤ ((∑' p : vab f (Set.univ : Set ℂ),
          ‖vaa p‖⁻¹ ^ τ) + 1) * (1 + r) ^ τ := by
  set Sτ : ℝ :=
    ∑' p : vab f (Set.univ : Set ℂ), ‖vaa p‖⁻¹ ^ τ
  have hsum_inv :
      (∑ p ∈ small, (‖vaa p‖⁻¹ : ℝ) ^ τ) ≤ Sτ := by
    have hnn : ∀ p : vab f (Set.univ : Set ℂ),
        0 ≤ (‖vaa p‖⁻¹ : ℝ) ^ τ := by
      intro p
      positivity
    simpa [Sτ] using
      (Summable.sum_le_tsum (s := small)
        (f := fun p : vab f (Set.univ : Set ℂ) =>
          (‖vaa p‖⁻¹ : ℝ) ^ τ)
        (fun p _ => hnn p) hsumτ)
  have hsum_eq :
      ∑ p ∈ small, (r / ‖vaa p‖) ^ τ =
        (r ^ τ) * ∑ p ∈ small, (‖vaa p‖⁻¹ : ℝ) ^ τ := by
    simp [vaD (f := f) (τ := τ) hr, Finset.mul_sum]
  have h1r : r ^ τ ≤ (1 + r) ^ τ :=
    Real.rpow_le_rpow (by positivity) (by linarith) hτ_nonneg
  have hS : (∑ p ∈ small, (‖vaa p‖⁻¹ : ℝ) ^ τ) ≤ Sτ + 1 := by
    linarith [hsum_inv]
  have hle :
      (r ^ τ) * (∑ p ∈ small, (‖vaa p‖⁻¹ : ℝ) ^ τ)
        ≤ (1 + r) ^ τ * (Sτ + 1) :=
    mul_le_mul h1r hS (by positivity) (by positivity)
  simpa [Sτ, hsum_eq, mul_assoc, mul_left_comm, mul_comm] using hle
lemma veG {x₁ x₂ x₃ x₄ A B C : ℝ}
    (h₁ : x₁ ≤ A) (h₂ : x₂ ≤ B) (h₃ : x₃ ≤ B) (h₄ : x₄ ≤ C) :
    x₁ + x₂ + x₃ + x₄ ≤ A + 2 * B + C := by
  nlinarith
lemma vew
    {xφ x0 xm xt Cφ m q Y T : ℝ}
    (hφ : xφ ≤ Cφ * q * Y * T)
    (h0 : x0 ≤ m * q * Y * T)
    (hm : xm ≤ m * q * Y * T)
    (ht : xt ≤ (2 : ℝ) * Y * T) :
    xφ + x0 + xm + xt ≤ (Cφ + (2 : ℝ) * m) * q * Y * T + (2 : ℝ) * Y * T := by
  have h :=
    veG hφ h0 hm ht
  have hring :
      Cφ * (q * (Y * T)) + 2 * (m * (q * (Y * T))) + 2 * (Y * T)
        = (Cφ + (2 : ℝ) * m) * (q * (Y * T)) + (2 : ℝ) * (Y * T) := by
    ring
  simpa [mul_assoc, hring] using h
lemma vex (A Y T : ℝ) :
    A * Y * T + (2 : ℝ) * Y * T = ((A + 2) * Y) * T := by
  ring
lemma ven {A S T : ℝ} (hS : 0 ≤ S + 1) (hT : 0 ≤ T) :
    ((A + 2) * (S + 1)) * T ≤ ((A + 3) * (S + 1)) * T := by
  have h : (A + 2) * (S + 1) ≤ (A + 3) * (S + 1) := by
    nlinarith
  exact mul_le_mul_of_nonneg_right h hT
lemma vgd
    {f : ℂ → ℂ} {m : ℕ} {τ r : ℝ} (hr : 0 ≤ r)
    (small : Finset (vab f (Set.univ : Set ℂ))) :
    letI : DecidableEq (vab f (Set.univ : Set ℂ)) := Classical.decEq _
    let ap : vab f (Set.univ : Set ℂ) → ℝ := fun p => ‖vaa p‖
    let b : vab f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else
          (2 : ℝ) * (r / ap p) ^ τ
    ∀ p, 0 ≤ b p := by
  classical
  dsimp
  intro p
  let ap : vab f (Set.univ : Set ℂ) → ℝ := fun q => ‖vaa q‖
  have hap : ap p = ‖vaa p‖ := rfl
  by_cases hp : p ∈ small
  · have hφ : 0 ≤ CartanBound.φ (r / ap p) := CartanBound.viw (t := r / ap p)
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have h1 : 0 ≤ (1 + (r / ap p) ^ τ) := by positivity
    have : 0 ≤ CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ) := by
      nlinarith [hφ, hm0, h1]
    simpa [hap, hp, ap] using this
  · have hbase : 0 ≤ r / ap p := div_nonneg hr (by positivity)
    have hpow : 0 ≤ (r / ap p) ^ τ := Real.rpow_nonneg hbase τ
    have : 0 ≤ (2 : ℝ) * (r / ap p) ^ τ := mul_nonneg (by norm_num) hpow
    simpa [hap, hp, ap] using this
lemma vfM
    {f : ℂ → ℂ} {m : ℕ} {τ r : ℝ} (hr : 0 ≤ r)
    (small : Finset (vab f (Set.univ : Set ℂ)))
    (hsumτ :
      Summable (fun p : vab f (Set.univ : Set ℂ) =>
        ‖vaa p‖⁻¹ ^ τ)) :
    letI : DecidableEq (vab f (Set.univ : Set ℂ)) := Classical.decEq _
    let ap : vab f (Set.univ : Set ℂ) → ℝ := fun p => ‖vaa p‖
    let b : vab f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else
          (2 : ℝ) * (r / ap p) ^ τ
    Summable b := by
  classical
  dsimp
  let ap : vab f (Set.univ : Set ℂ) → ℝ := fun q => ‖vaa q‖
  let b : vab f (Set.univ : Set ℂ) → ℝ :=
    fun p =>
      if p ∈ small then
        CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
      else
        (2 : ℝ) * (r / ap p) ^ τ
  have hb : Summable b := by
    let b₁ : vab f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else 0
    let b₂ : vab f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then 0 else (2 : ℝ) * (r / ap p) ^ τ
    have hb_decomp : b = fun p => b₁ p + b₂ p := by
      funext p
      by_cases hp : p ∈ small <;> simp [b, b₁, b₂, hp]
    have hb₁ : Summable b₁ := by
      simpa [b₁] using
        vaL small
          (fun p => CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ))
    have hb₂ : Summable b₂ := by
      have hconst :
          Summable (fun p =>
            (2 : ℝ) * (r ^ τ) * (‖vaa p‖⁻¹ ^ τ)) :=
        hsumτ.mul_left ((2 : ℝ) * (r ^ τ))
      refine Summable.of_nonneg_of_le
        (fun p => by
          by_cases hp : p ∈ small
          · simp [b₂, hp]
          · have : 0 ≤ (2 : ℝ) * (r / ap p) ^ τ := by positivity
            simpa [b₂, hp] using this)
        (fun p => ?_) hconst
      by_cases hp : p ∈ small
      · have : 0 ≤ (2 : ℝ) * (r ^ τ) * (‖vaa p‖⁻¹ ^ τ) := by positivity
        simpa [b₂, hp] using this
      · have hrpow : (r / ap p) ^ τ = (r ^ τ) * (‖vaa p‖⁻¹ ^ τ) := by
          simpa [ap] using vaD (f := f) (τ := τ) hr p
        simp [b₂, hp, hrpow, mul_assoc, mul_left_comm, mul_comm]
    simpa [hb_decomp] using hb₁.add hb₂
  refine hb.congr ?_
  intro p
  by_cases hp : p ∈ small <;> simp [b, ap, hp]
lemma vgy
    {f : ℂ → ℂ} {τ R : ℝ} (hRpos : 0 < R) (hτ_nonneg : 0 ≤ τ)
    (small : Finset (vab f (Set.univ : Set ℂ)))
    (hsmall : ∀ p ∈ small, ‖vaa p‖ ≤ 4 * R)
    (hsumτ :
      Summable
        (fun p : vab f (Set.univ : Set ℂ) =>
          ‖vaa p‖⁻¹ ^ τ)) :
    (small.card : ℝ)
      ≤ (4 * R) ^ τ
          * ((∑' p : vab f (Set.univ : Set ℂ),
                ‖vaa p‖⁻¹ ^ τ) + 1) := by
  classical
  set Sτ : ℝ :=
    ∑' p : vab f (Set.univ : Set ℂ), ‖vaa p‖⁻¹ ^ τ
  have hsum_le : (∑ p ∈ small, ‖vaa p‖⁻¹ ^ τ) ≤ Sτ := by
    have hnn :
        ∀ p : vab f (Set.univ : Set ℂ),
          0 ≤ ‖vaa p‖⁻¹ ^ τ := by
      intro p
      exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
    simpa [Sτ] using
      (Summable.sum_le_tsum (s := small)
        (f := fun p : vab f (Set.univ : Set ℂ) =>
          ‖vaa p‖⁻¹ ^ τ)
        (fun p _ => hnn p) hsumτ)
  have hgeom_sum :
      (small.card : ℝ) ≤ ∑ p ∈ small, (4 * R) ^ τ * ‖vaa p‖⁻¹ ^ τ := by
    have hcard_eq : (small.card : ℝ) = ∑ p ∈ small, (1 : ℝ) := by simp
    rw [hcard_eq]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hp_le : ‖vaa p‖ ≤ 4 * R := hsmall p hp
    have hap : 0 < ‖vaa p‖ :=
      norm_pos_iff.2 (vao p)
    have hbase : (1 : ℝ) ≤ (4 * R) / ‖vaa p‖ := by
      exact (le_div_iff₀ hap).2 (by simpa [mul_one] using hp_le)
    have : (1 : ℝ) ≤ ((4 * R) / ‖vaa p‖) ^ τ :=
      Real.one_le_rpow hbase hτ_nonneg
    have hdiv :
        ((4 * R) / ‖vaa p‖) ^ τ =
          (4 * R) ^ τ * (‖vaa p‖)⁻¹ ^ τ := by
      have h4 : 0 ≤ (4 * R : ℝ) := by nlinarith [le_of_lt hRpos]
      have ha : 0 ≤ (‖vaa p‖ : ℝ)⁻¹ := by positivity
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (Real.mul_rpow (x := (4 * R : ℝ))
          (y := (‖vaa p‖ : ℝ)⁻¹) (z := τ) h4 ha)
    have : (1 : ℝ) ≤ (4 * R) ^ τ * ‖vaa p‖⁻¹ ^ τ := by
      simpa [hdiv] using this
    exact this
  have hgeom :
      (small.card : ℝ) ≤ (4 * R) ^ τ * (∑ p ∈ small, ‖vaa p‖⁻¹ ^ τ) := by
    simpa [Finset.mul_sum] using hgeom_sum
  have hsmall_le : (small.card : ℝ) ≤ (4 * R) ^ τ * Sτ := by
    exact hgeom.trans (mul_le_mul_of_nonneg_left hsum_le (by positivity))
  have hS_le : (4 * R) ^ τ * Sτ ≤ (4 * R) ^ τ * (Sτ + 1) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  have : (small.card : ℝ) ≤ (4 * R) ^ τ * (Sτ + 1) := hsmall_le.trans hS_le
  simpa [Sτ, add_comm, add_left_comm, add_assoc, mul_assoc] using this
lemma vgW
    {τ R r : ℝ} (hRpos : 0 < R) (hrpos : 0 < r) (hR_le_r : R ≤ r) (hτ_nonneg : 0 ≤ τ) :
    (4 * R) ^ τ ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ := by
  have hR_le_1r : R ≤ 1 + r := by linarith [hR_le_r, le_of_lt hrpos]
  have hbase0 : 0 ≤ (4 * R : ℝ) := by nlinarith [le_of_lt hRpos]
  have : (4 * R) ^ τ ≤ (4 * (1 + r)) ^ τ := by
    refine Real.rpow_le_rpow hbase0 ?_ hτ_nonneg
    nlinarith [hR_le_1r]
  have hmul : (4 * (1 + r)) ^ τ = (4 : ℝ) ^ τ * (1 + r) ^ τ := by
    have h4 : 0 ≤ (4 : ℝ) := by norm_num
    have h1 : 0 ≤ (1 + r : ℝ) := by positivity
    simpa [mul_assoc] using
      (Real.mul_rpow (x := (4 : ℝ)) (y := (1 + r : ℝ)) (z := τ) h4 h1)
  simpa [hmul] using this
open scoped Classical in
theorem vgb
    {f : ℂ → ℂ} {m : ℕ} {τ R r : ℝ}
    (hRpos : 0 < R)
    (hrpos : 0 < r)
    (hR_le_r : R ≤ r)
    (hτ_nonneg : 0 ≤ τ)
    (smallSet : Set (vab f (Set.univ : Set ℂ)))
    (hsmall_fin : smallSet.Finite)
    (hsmallSet :
      smallSet = {p : vab f (Set.univ : Set ℂ) | ‖vaa p‖ ≤ 4 * R})
    (hsumτ :
      Summable (fun p : vab f (Set.univ : Set ℂ) => ‖vaa p‖⁻¹ ^ τ))
    (hr_phi :
      let small : Finset (vab f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
      let a : vab f (Set.univ : Set ℂ) → ℝ := fun p => ‖vaa p‖
      (∑ p ∈ small, CartanBound.φ (r / a p)) ≤ CartanBound.Cφ * (small.card : ℝ)) :
    let small : Finset (vab f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
    letI : DecidableEq (vab f (Set.univ : Set ℂ)) := Classical.decEq _
    let ap : vab f (Set.univ : Set ℂ) → ℝ := fun p => ‖vaa p‖
    let b : vab f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else
          (2 : ℝ) * (r / ap p) ^ τ
    let Sτ : ℝ := ∑' p : vab f (Set.univ : Set ℂ), ‖vaa p‖⁻¹ ^ τ
    let Cprod : ℝ := vaS m τ Sτ
    ∀ s : Finset (vab f (Set.univ : Set ℂ)),
      (∑ p ∈ s, b p) ≤ Cprod * (1 + r) ^ τ := by
  classical
  intro small ap b Sτ Cprod s
  have hr : 0 ≤ r := le_of_lt hrpos
  have hSτ_nonneg : 0 ≤ Sτ :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _)
  have hsmall_mem : ∀ p, p ∈ small ↔ p ∈ smallSet := by
    intro p
    simp [small, hsmall_fin.mem_toFinset]
  have hphi_sum :
      (∑ p ∈ small, CartanBound.φ (r / ap p)) ≤ CartanBound.Cφ * (small.card : ℝ) := by
    simpa [small, ap] using hr_phi
  have hb_nonneg : ∀ p, 0 ≤ b p := by
    simpa [ap, b] using (vgd (f := f) (m := m) (τ := τ) (r := r) hr small)
  have hb_summable : Summable b := by
    simpa [ap, b] using
      (vfM (f := f) (m := m) (τ := τ) (r := r) hr small hsumτ)
  have hsmall_norm : ∀ p ∈ small, ‖vaa p‖ ≤ 4 * R := by
    intro p hp
    have : p ∈ smallSet := (hsmall_mem p).1 hp
    simpa [hsmallSet] using this
  have hcard_le : (small.card : ℝ) ≤ (4 * R) ^ τ * (Sτ + 1) := by
    simpa [Sτ, mul_assoc, add_assoc, add_left_comm, add_comm] using
      (vgy (f := f) (τ := τ) (R := R) hRpos hτ_nonneg small hsmall_norm hsumτ)
  have hpowR : (4 * R) ^ τ ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ :=
    vgW (τ := τ) (R := R) (r := r) hRpos hrpos hR_le_r hτ_nonneg
  have hcard_le' : (small.card : ℝ) ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ * (Sτ + 1) := by
    have : (4 * R) ^ τ * (Sτ + 1) ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ * (Sτ + 1) := by
      exact mul_le_mul_of_nonneg_right hpowR (by linarith [hSτ_nonneg])
    exact le_trans hcard_le this
  have hb_tsum_le :
      (∑' p : vab f (Set.univ : Set ℂ), b p) ≤ Cprod * (1 + r) ^ τ := by
    let bφ : vab f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then CartanBound.φ (r / ap p) else 0
    let b0 : vab f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then (m : ℝ) else 0
    let bmτ : vab f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then (m : ℝ) * (r / ap p) ^ τ else 0
    let bt : vab f (Set.univ : Set ℂ) → ℝ :=
      fun p => (2 : ℝ) * (r / ap p) ^ τ
    have hb_pointwise : ∀ p, b p ≤ bφ p + b0 p + bmτ p + bt p := by
      intro p
      by_cases hp : p ∈ small
      · have hbase : 0 ≤ r / ap p := div_nonneg hr (by positivity)
        have hx : 0 ≤ (r / ap p) ^ τ := Real.rpow_nonneg hbase τ
        have hpos : 0 ≤ (2 : ℝ) * (r / ap p) ^ τ := mul_nonneg (by norm_num) hx
        simp [b, bφ, b0, bmτ, bt, hp]
        nlinarith
      · simp [b, bφ, b0, bmτ, bt, hp]
    have hmaj_summ : Summable (fun p => bφ p + b0 p + bmτ p + bt p) := by
      have hbφ_summ : Summable bφ := by
        simpa [bφ] using vaL small (fun p => CartanBound.φ (r / ap p))
      have hb0_summ : Summable b0 := by
        simpa [b0] using vaL small (fun _ => (m : ℝ))
      have hbmτ_summ : Summable bmτ := by
        simpa [bmτ] using vaL small (fun p => (m : ℝ) * (r / ap p) ^ τ)
      have hbt_summ : Summable bt := by
        have hconst : Summable (fun p =>
            (2 : ℝ) * (r ^ τ) * (‖vaa p‖⁻¹ ^ τ)) :=
          hsumτ.mul_left ((2 : ℝ) * (r ^ τ))
        refine hconst.congr ?_
        intro p
        simp [bt, ap, vaD (f := f) (τ := τ) hr p,
          mul_assoc, mul_left_comm, mul_comm]
      have h' : Summable (fun p => bφ p + b0 p + (bmτ p + bt p)) :=
        (hbφ_summ.add hb0_summ).add (hbmτ_summ.add hbt_summ)
      simpa [add_assoc] using h'
    have htsum_le :
        (∑' p : vab f (Set.univ : Set ℂ), b p)
          ≤ ∑' p : vab f (Set.univ : Set ℂ), (bφ p + b0 p + bmτ p + bt p) :=
      (hasSum_le hb_pointwise hb_summable.hasSum hmaj_summ.hasSum)
    have htsum_bφ :
        (∑' p : vab f (Set.univ : Set ℂ), bφ p)
          = ∑ p ∈ small, CartanBound.φ (r / ap p) := by
      classical
      simpa [bφ] using vdv small (fun p => CartanBound.φ (r / ap p))
    have htsum_b0 :
        (∑' p : vab f (Set.univ : Set ℂ), b0 p)
          = (m : ℝ) * (small.card : ℝ) := by
      classical
      have : (∑' p : vab f (Set.univ : Set ℂ), b0 p) = ∑ p ∈ small, (m : ℝ) := by
        simpa [b0] using vdv small (fun _ => (m : ℝ))
      simp [this, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have htsum_bmτ :
        (∑' p : vab f (Set.univ : Set ℂ), bmτ p)
          = (m : ℝ) * ∑ p ∈ small, (r / ap p) ^ τ := by
      classical
      have :
          (∑' p : vab f (Set.univ : Set ℂ), bmτ p)
            = ∑ p ∈ small, (m : ℝ) * (r / ap p) ^ τ := by
        simpa [bmτ] using vdv small (fun p => (m : ℝ) * (r / ap p) ^ τ)
      simp [this, Finset.mul_sum]
    have htsum_bt :
        (∑' p : vab f (Set.univ : Set ℂ), bt p)
          ≤ (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ := by
      simpa [bt, ap, Sτ] using
        vck (f := f) (τ := τ) hr hτ_nonneg
    have hsum_small_rpow_le :
        (∑ p ∈ small, (r / ap p) ^ τ) ≤ (Sτ + 1) * (1 + r) ^ τ := by
      simpa [ap, Sτ] using
        vdd (f := f) (τ := τ) small hr hτ_nonneg hsumτ
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have hCφ : 0 ≤ CartanBound.Cφ := le_of_lt CartanBound.vij
    have hS : 0 ≤ Sτ + 1 := by linarith [hSτ_nonneg]
    have htsum_majorant :
        (∑' p : vab f (Set.univ : Set ℂ), (bφ p + b0 p + bmτ p + bt p))
          ≤ (((CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 2) * (Sτ + 1))
              * (1 + r) ^ τ := by
      have hφ_le :
          (∑' p : vab f (Set.univ : Set ℂ), bφ p)
            ≤ CartanBound.Cφ * (small.card : ℝ) := by
        simpa [htsum_bφ] using hphi_sum
      have hb0_le :
          (∑' p : vab f (Set.univ : Set ℂ), b0 p)
            ≤ (m : ℝ) * (small.card : ℝ) := by
        simp [htsum_b0]
      have hbmτ_le :
          (∑' p : vab f (Set.univ : Set ℂ), bmτ p) ≤
            (m : ℝ) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
        have h0 :
            (∑' p : vab f (Set.univ : Set ℂ), bmτ p)
              ≤ (m : ℝ) * ((Sτ + 1) * (1 + r) ^ τ) := by
          have hmul := mul_le_mul_of_nonneg_left hsum_small_rpow_le hm0
          simpa [htsum_bmτ, mul_assoc, mul_left_comm, mul_comm] using hmul
        have h1 : (1 : ℝ) ≤ (4 : ℝ) ^ τ :=
          Real.one_le_rpow (by norm_num) hτ_nonneg
        have hscale :
            (m : ℝ) * ((Sτ + 1) * (1 + r) ^ τ)
              ≤ (m : ℝ) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
          have hnonneg : 0 ≤ (m : ℝ) * ((Sτ + 1) * (1 + r) ^ τ) := by
            have : 0 ≤ (Sτ + 1) * (1 + r) ^ τ := by positivity
            exact mul_nonneg hm0 this
          simpa [mul_assoc, mul_left_comm, mul_comm] using (mul_le_mul_of_nonneg_right h1 hnonneg)
        exact h0.trans hscale
      have hbt_le :
          (∑' p : vab f (Set.univ : Set ℂ), bt p)
            ≤ (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using htsum_bt
      have hsplit :
          (∑' p : vab f (Set.univ : Set ℂ), (bφ p + b0 p + bmτ p + bt p))
            = (∑' p, bφ p) + (∑' p, b0 p) + (∑' p, bmτ p) + (∑' p, bt p) := by
        classical
        have hbφ_summ : Summable bφ := by
          simpa [bφ] using vaL small (fun p => CartanBound.φ (r / ap p))
        have hb0_summ : Summable b0 := by
          simpa [b0] using vaL small (fun _ => (m : ℝ))
        have hbmτ_summ : Summable bmτ := by
          simpa [bmτ] using vaL small (fun p => (m : ℝ) * (r / ap p) ^ τ)
        have hbt_summ : Summable bt := by
          have hconst :
              Summable
                (fun p : vab f (Set.univ : Set ℂ) =>
                  (2 : ℝ) * (r ^ τ) * ((‖vaa p‖⁻¹ : ℝ) ^ τ)) :=
            hsumτ.mul_left ((2 : ℝ) * (r ^ τ))
          refine hconst.congr ?_
          intro p
          simp [bt, ap, vaD (f := f) (τ := τ) hr p,
            mul_assoc, mul_left_comm, mul_comm]
        exact viE bφ b0 bmτ bt hbφ_summ hb0_summ hbmτ_summ hbt_summ
      have hcard_le'' :
          (small.card : ℝ) ≤ (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hcard_le'
      have hφ_le' :
          (∑' p : vab f (Set.univ : Set ℂ), bφ p) ≤
            CartanBound.Cφ * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
        have : CartanBound.Cφ * (small.card : ℝ) ≤
            CartanBound.Cφ * ((4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ) :=
          mul_le_mul_of_nonneg_left hcard_le'' hCφ
        exact hφ_le.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using this)
      have hb0_le' :
          (∑' p : vab f (Set.univ : Set ℂ), b0 p) ≤
            (m : ℝ) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
        have : (m : ℝ) * (small.card : ℝ) ≤ (m : ℝ) * ((4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ) :=
          mul_le_mul_of_nonneg_left hcard_le'' hm0
        exact hb0_le.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using this)
      have htsum_majorant' :
          (∑' p : vab f (Set.univ : Set ℂ), (bφ p + b0 p + bmτ p + bt p))
            ≤ (CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ
              + (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ := by
        rw [hsplit]
        set Y : ℝ := Sτ + 1 with hY
        set T : ℝ := (1 + r) ^ τ with hT
        have hφ_leY :
            (∑' p : vab f (Set.univ : Set ℂ), bφ p)
              ≤ CartanBound.Cφ * (4 : ℝ) ^ τ * Y * T := by
          simpa [hY, hT, mul_assoc] using hφ_le'
        have hb0_leY :
            (∑' p : vab f (Set.univ : Set ℂ), b0 p)
              ≤ (m : ℝ) * (4 : ℝ) ^ τ * Y * T := by
          simpa [hY, hT, mul_assoc] using hb0_le'
        have hbmτ_leY :
            (∑' p : vab f (Set.univ : Set ℂ), bmτ p)
              ≤ (m : ℝ) * (4 : ℝ) ^ τ * Y * T := by
          simpa [hY, hT, mul_assoc] using hbmτ_le
        have hbt_leY :
            (∑' p : vab f (Set.univ : Set ℂ), bt p) ≤ (2 : ℝ) * Y * T := by
          simpa [hY, hT, mul_assoc] using hbt_le
        have hmain :=
          vew
            (q := (4 : ℝ) ^ τ) hφ_leY hb0_leY hbmτ_leY hbt_leY
        simpa [Y, T, add_assoc] using hmain
      have hring :
          (CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ
              + (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ
            = (((CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 2) * (Sτ + 1)) * (1 + r) ^ τ := by
        exact vex
          ((CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ) (Sτ + 1) ((1 + r) ^ τ)
      rw [← hring]
      exact htsum_majorant'
    have hCprod' :
        (((CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 2) * (Sτ + 1)) * (1 + r) ^ τ
          ≤ Cprod * (1 + r) ^ τ := by
      simpa [Cprod, vaS, mul_assoc, mul_left_comm, mul_comm] using
        ven
          (A := (CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ)
          (S := Sτ) (T := (1 + r) ^ τ) hS (by positivity)
    exact (le_trans (le_trans htsum_le htsum_majorant) hCprod')
  have hsum_fin_le :
      (∑ p ∈ s, b p) ≤ (∑' p : vab f (Set.univ : Set ℂ), b p) := by
    simpa using
      (Summable.sum_le_tsum (s := s) (f := b) (fun p _ => hb_nonneg p) hb_summable)
  exact hsum_fin_le.trans hb_tsum_le
end Complex.Hadamard
end
end
section
noncomputable section
open scoped BigOperators
open Filter Finset Real Topology
lemma Finset.vhY {α : Type} (s : Finset α) (a : α → ℝ) (b : α → ℝ)
    (ha : ∀ x ∈ s, 0 ≤ a x) (hab : ∀ x ∈ s, a x ≤ Real.exp (b x)) :
    (∏ x ∈ s, a x) ≤ Real.exp (∑ x ∈ s, b x) := by
  calc
    (∏ x ∈ s, a x) ≤ ∏ x ∈ s, Real.exp (b x) := Finset.prod_le_prod ha hab
    _ = Real.exp (∑ x ∈ s, b x) := by
      simpa using (Real.exp_sum (s := s) (f := b)).symm
lemma vft {α : Type} {f : α → ℝ} {a : ℝ}
    (hf : HasProd f a (SummationFilter.unconditional α))
    {B : ℝ} (hB : ∀ s : Finset α, (∏ x ∈ s, f x) ≤ Real.exp B) :
    a ≤ Real.exp B :=
  hasProd_le_of_prod_le (L := (SummationFilter.unconditional α)) hf hB
lemma vfr {α : Type} {fac : α → ℂ} {F : ℂ}
    (hfac : HasProd fac F (SummationFilter.unconditional α)) (hF : F ≠ 0) :
    HasProd (fun x => (fac x)⁻¹) (F⁻¹) (SummationFilter.unconditional α) := by
  change
    Tendsto (fun s : Finset α => ∏ x ∈ s, (fac x)⁻¹)
      (SummationFilter.unconditional α).filter (𝓝 (F⁻¹))
  have hprod :
      Tendsto (fun s : Finset α => ∏ x ∈ s, fac x)
        (SummationFilter.unconditional α).filter (𝓝 F) := by
    simpa [HasProd] using hfac
  have hinv :
      Tendsto (fun s : Finset α => (∏ x ∈ s, fac x)⁻¹)
        (SummationFilter.unconditional α).filter (𝓝 (F⁻¹)) :=
    hprod.inv₀ hF
  refine hinv.congr' (Filter.Eventually.of_forall ?_)
  intro s
  simp [Finset.prod_inv_distrib]
lemma vez {α : Type} {fac : α → ℂ} {F : ℂ}
    (hfac : HasProd fac F (SummationFilter.unconditional α)) (hF : F ≠ 0) :
    HasProd (fun x => ‖(fac x)⁻¹‖) ‖F⁻¹‖ (SummationFilter.unconditional α) := by
  change
    Tendsto (fun s : Finset α => ∏ x ∈ s, ‖(fac x)⁻¹‖)
      (SummationFilter.unconditional α).filter (𝓝 ‖F⁻¹‖)
  have hnorm := (vfr hfac hF).norm
  refine hnorm.congr' (Filter.Eventually.of_forall ?_)
  intro s
  simp [norm_inv, Finset.prod_inv_distrib]
lemma vcI {α : Type} {fac : α → ℂ} {F : ℂ}
    (hfac : HasProd fac F (SummationFilter.unconditional α))
    (b : α → ℝ) (B : ℝ)
    (hterm : ∀ x, ‖(fac x)⁻¹‖ ≤ Real.exp (b x))
    (hsum : ∀ s : Finset α, (∑ x ∈ s, b x) ≤ B) :
    ‖F⁻¹‖ ≤ Real.exp B := by
  by_cases hF : F = 0
  · subst hF
    simpa using exp_nonneg B
  have hnorm :
      HasProd (fun x => ‖(fac x)⁻¹‖) ‖F⁻¹‖ (SummationFilter.unconditional α) :=
    vez hfac hF
  have hprod : ∀ s : Finset α, (∏ x ∈ s, ‖(fac x)⁻¹‖) ≤ Real.exp B := by
    intro s
    have h0 : ∀ x ∈ s, 0 ≤ ‖(fac x)⁻¹‖ := by intro _ _; positivity
    have h1 : (∏ x ∈ s, ‖(fac x)⁻¹‖) ≤ Real.exp (∑ x ∈ s, b x) := by
      refine Finset.vhY s (a := fun x => ‖(fac x)⁻¹‖) (b := b) h0 ?_
      intro x hx
      simpa using hterm x
    have h2 : Real.exp (∑ x ∈ s, b x) ≤ Real.exp B :=
      Real.exp_le_exp.2 (hsum s)
    exact h1.trans h2
  exact vft hnorm hprod
end
end
section
open Metric
namespace Complex
theorem vef {f : ℂ → ℂ} {M r R : ℝ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    (hr : 0 < r) (hlt : r < R) (hM : 0 < M) (hf0 : f 0 = 0)
    (hf_re : ∀ w, ‖w‖ ≤ R → (f w).re ≤ M) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖f z‖ ≤ 2 * M * r / (R - r) := by
  have hR : 0 < R := lt_trans hr hlt
  have hz_ball : z ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hz.trans_lt hlt
  have hf_diff : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R) := by
    intro w hw
    have hw' : w ∈ Metric.closedBall (0 : ℂ) R := ball_subset_closedBall hw
    exact (hf w hw').differentiableAt.differentiableWithinAt
  have hf_map : Set.MapsTo f (Metric.ball (0 : ℂ) R) {w | w.re ≤ M} := by
    intro w hw
    simp only [Set.mem_ofPred_eq]
    have hw' : ‖w‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hw
    exact hf_re w hw'.le
  have hbc :=
    borelCaratheodory_zero hM hf_diff hf_map hR hz_ball hf0
  have hzR : ‖z‖ < R := by
    rw [Metric.mem_ball, dist_zero_right] at hz_ball
    exact hz_ball
  have hmono : ‖z‖ / (R - ‖z‖) ≤ r / (R - r) := by
    have hrden : 0 < R - r := sub_pos.mpr hlt
    have hden : 0 < R - ‖z‖ := sub_pos.mpr hzR
    rw [div_le_div_iff₀ hden hrden]
    nlinarith [hz, norm_nonneg z]
  have hM' : 0 ≤ 2 * M := mul_nonneg (by norm_num) (le_of_lt hM)
  calc ‖f z‖
      ≤ 2 * M * ‖z‖ / (R - ‖z‖) := hbc
    _ ≤ 2 * M * (r / (R - r)) := by
        simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hmono hM'
    _ = 2 * M * r / (R - r) := by ring
end Complex
end
section
noncomputable section
namespace Complex
namespace Hadamard
open Complex Real BigOperators Finset Set Filter Topology Metric
open scoped Topology
theorem vdq {H : ℂ → ℂ} {n : ℕ}
    (hH : Differentiable ℂ H)
    (h_nonzero : ∀ z, H z ≠ 0)
    (h_bound : ∃ C > 0, ∀ z, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ n)) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ n ∧ ∀ z, H z = Complex.exp (Polynomial.eval z P) := by
  classical
  rcases h_bound with ⟨C, hCpos, hC⟩
  let L : ℂ → ℂ := fun z => deriv H z / H z
  have hderivH : Differentiable ℂ (deriv H) := by
    intro z
    exact ((hH.analyticAt z).deriv).differentiableAt
  have hL : Differentiable ℂ L := by
    simpa [L] using! (hderivH.div hH h_nonzero)
  let h : ℂ → ℂ := fun z => Complex.wedgeIntegral (0 : ℂ) z L
  have hh_deriv : ∀ z, HasDerivAt h (L z) z := by
    intro z
    let r : ℝ := ‖z‖ + 1
    have hrpos : 0 < r := by
      dsimp [r]; linarith [norm_nonneg z]
    have hz_ball : z ∈ Metric.ball (0 : ℂ) r := by
      have : dist z (0 : ℂ) < r := by simp [r, dist_zero_right]
      simpa [Metric.mem_ball] using this
    have hconserv : Complex.IsConservativeOn L (Metric.ball (0 : ℂ) r) :=
      (hL.differentiableOn).isConservativeOn
    have hcont : ContinuousOn L (Metric.ball (0 : ℂ) r) :=
      hL.continuous.continuousOn
    simpa [h, r] using hconserv.hasDerivAt_wedgeIntegral (f_cont := hcont) (hz := hz_ball)
  have hh : Differentiable ℂ h := fun z => (hh_deriv z).differentiableAt
  have hderiv_h : ∀ z, deriv h z = L z := fun z => (hh_deriv z).deriv
  let k : ℂ → ℂ := fun z => h z + Complex.log (H 0)
  have hk : Differentiable ℂ k := hh.add_const (Complex.log (H 0))
  have hk_exp : ∀ z, H z = Complex.exp (k z) := by
    let F : ℂ → ℂ := fun z => Complex.exp (k z) / H z
    have hF_deriv : ∀ z, deriv F z = 0 := by
      intro z
      have hH_has : HasDerivAt H (deriv H z) z := (hH z).hasDerivAt
      have hk_has : HasDerivAt k (L z) z := by
        have hh_has : HasDerivAt h (L z) z := hh_deriv z
        simpa [k, L] using hh_has.add_const (Complex.log (H 0))
      have hExp : HasDerivAt (fun w => Complex.exp (k w)) (Complex.exp (k z) * L z) z :=
        (HasDerivAt.cexp hk_has)
      have hDiv := (HasDerivAt.div hExp hH_has (h_nonzero z))
      have :
          deriv F z =
            ((Complex.exp (k z) * L z) * H z - Complex.exp (k z) * deriv H z) / (H z) ^ 2 := by
        simpa [F] using! hDiv.deriv
      rw [this]
      have hnum :
          (Complex.exp (k z) * L z) * H z - Complex.exp (k z) * deriv H z = 0 := by
        dsimp [L]
        field_simp [h_nonzero z]
        ring
      simp [hnum]
    have hF_diff : Differentiable ℂ F := (hk.cexp).div hH h_nonzero
    have hF_const : ∀ z, F z = F 0 := by
      intro z
      exact is_const_of_deriv_eq_zero hF_diff hF_deriv z 0
    have hF0 : F 0 = 1 := by
      have hh0 : h 0 = 0 := by simp [h, Complex.wedgeIntegral]
      have hk0 : k 0 = Complex.log (H 0) := by simp [k, hh0]
      have hH0 : H 0 ≠ 0 := h_nonzero 0
      simp [F, hk0, Complex.exp_log hH0, hH0]
    intro z
    have : F z = 1 := by simpa [hF0] using (hF_const z)
    have hHz : H z ≠ 0 := h_nonzero z
    have : Complex.exp (k z) / H z = 1 := by simpa [F] using this
    have : Complex.exp (k z) = H z := by
      field_simp [hHz] at this
      simpa using this
    exact this.symm
  have hk_re_bound : ∀ z, (k z).re ≤ C * (1 + ‖z‖) ^ n := by
    intro z
    have hHz : H z ≠ 0 := h_nonzero z
    have hpos : 0 < ‖H z‖ := norm_pos_iff.mpr hHz
    have hlog_le : Real.log ‖H z‖ ≤ C * (1 + ‖z‖) ^ n := by
      have := Real.log_le_log hpos (hC z)
      simpa [Real.log_exp] using this
    have hlog_eq : Real.log ‖H z‖ = (k z).re := by
      have : ‖H z‖ = Real.exp (k z).re := by
        simpa [hk_exp z] using (Complex.norm_exp (k z))
      calc
        Real.log ‖H z‖ = Real.log (Real.exp (k z).re) := by simp [this]
        _ = (k z).re := by simp
    simpa [hlog_eq] using hlog_le
  have hk_iteratedDeriv_eq_zero : ∀ m : ℕ, n < m → iteratedDeriv m k 0 = 0 := by
    intro m hm
    have hm' : 0 < (m - n : ℕ) := Nat.sub_pos_of_lt hm
    have hmne : m - n ≠ 0 := (Nat.pos_iff_ne_zero.1 hm')
    let f : ℂ → ℂ := fun z => k z - k 0
    have hf : Differentiable ℂ f := hk.sub_const (k 0)
    have hf0 : f 0 = 0 := by simp [f]
    have hf_re_bound : ∀ R : ℝ, 0 < R →
        ∀ z, ‖z‖ ≤ R → (f z).re ≤ C * (1 + R) ^ n + ‖k 0‖ := by
      intro R hRpos z hzR
      have hkz : (k z).re ≤ C * (1 + ‖z‖) ^ n := hk_re_bound z
      have hkz' : (k z).re ≤ C * (1 + R) ^ n := by
        have h1 : (1 + ‖z‖ : ℝ) ≤ 1 + R := by linarith
        have hpow : (1 + ‖z‖ : ℝ) ^ n ≤ (1 + R) ^ n :=
          pow_le_pow_left₀ (by linarith [norm_nonneg z]) h1 n
        exact hkz.trans (mul_le_mul_of_nonneg_left hpow (le_of_lt hCpos))
      have hRe0 : -(k 0).re ≤ ‖k 0‖ := by
        have habs : |(k 0).re| ≤ ‖k 0‖ := Complex.abs_re_le_norm (k 0)
        have hneg : -(k 0).re ≤ |(k 0).re| := by simpa using (neg_le_abs (k 0).re)
        exact hneg.trans habs
      have : (f z).re ≤ C * (1 + R) ^ n + ‖k 0‖ := by
        have : (f z).re = (k z).re - (k 0).re := by simp [f, sub_eq_add_neg]
        nlinarith [this, hkz', hRe0]
      exact this
    have hf_bound_on_ball : ∀ R : ℝ, 0 < R →
        ∀ z, ‖z‖ ≤ R / 2 → ‖f z‖ ≤ 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
      intro R hRpos z hz
      have hR2pos : 0 < R / 2 := by nlinarith
      have hlt : R / 2 < R := by nlinarith
      have hMpos : 0 < (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        have : 0 ≤ C * (1 + R) ^ n := by
          refine mul_nonneg (le_of_lt hCpos) ?_
          exact pow_nonneg (by linarith) _
        nlinarith [this, norm_nonneg (k 0)]
      have hf_anal : AnalyticOnNhd ℂ f (Metric.closedBall 0 R) := by
        intro w _hw
        exact (hf.analyticAt w)
      have hf_re : ∀ w, ‖w‖ ≤ R → (f w).re ≤ (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        intro w hw
        have := hf_re_bound R hRpos w hw
        linarith
      have hf_bc :=
        vef (f := f) (r := R / 2) (R := R)
          (M := (C * (1 + R) ^ n + ‖k 0‖ + 1))
          hf_anal hR2pos hlt hMpos hf0 hf_re (z := z) hz
      have hconst :
          2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) * (R / 2) / (R - R / 2)
            = 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        field_simp [hRpos.ne'] ; ring
      simpa [hconst] using hf_bc
    have hCauchy : ∀ R : ℝ, 0 < R →
        ‖iteratedDeriv m f 0‖ ≤
          (m.factorial : ℝ) * (2 * (C * (1 + R) ^ n + ‖k 0‖ + 1)) / (R / 2) ^ m := by
      intro R hRpos
      have hR2pos : 0 < R / 2 := by nlinarith
      have hf_diffCont : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) (R / 2)) := hf.diffContOnCl
      have hbound_sphere :
          ∀ z ∈ Metric.sphere (0 : ℂ) (R / 2),
            ‖f z‖ ≤ 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        intro z hz
        have hz' : ‖z‖ ≤ R / 2 := by
          simpa [Metric.mem_sphere, dist_zero_right] using (le_of_eq hz)
        exact hf_bound_on_ball R hRpos z hz'
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n := m) (c := (0 : ℂ))
          (R := R / 2) (C := 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1))
          (hR := hR2pos) hf_diffCont hbound_sphere)
    have hf_iter_eq : iteratedDeriv m f 0 = 0 := by
      by_contra hne
      have ha : 0 < ‖iteratedDeriv m f 0‖ := norm_pos_iff.2 hne
      let RHS : ℝ → ℝ := fun R =>
        (m.factorial : ℝ) * (2 * (C * (1 + R) ^ n + ‖k 0‖ + 1)) / (R / 2) ^ m
      have hle_RHS : ∀ R : ℝ, 0 < R → ‖iteratedDeriv m f 0‖ ≤ RHS R := by
        intro R hRpos
        simpa [RHS] using hCauchy R hRpos
      have hRHS_tendsto : Tendsto RHS atTop (𝓝 0) := by
        let K : ℝ := ‖k 0‖ + 1
        have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hm
        have hm0 : m ≠ 0 := ne_of_gt hmpos
        have hratio : Tendsto (fun R : ℝ => R ^ n / (R / 2) ^ m) atTop (𝓝 0) := by
          have hident :
              (fun R : ℝ => R ^ n / (R / 2) ^ m) = fun R : ℝ => (2 : ℝ) ^ m * (R ^ n / R ^ m) := by
            funext R
            simp [div_eq_mul_inv, mul_pow, mul_assoc, mul_comm]
          have hmain : Tendsto (fun R : ℝ => R ^ n / R ^ m) atTop (𝓝 0) := by
            have hp : m - n ≠ 0 := (Nat.pos_iff_ne_zero.1 (Nat.sub_pos_of_lt hm))
            have hmain' : Tendsto (fun R : ℝ => (R ^ (m - n))⁻¹) atTop (𝓝 0) := by
              simpa using (tendsto_pow_neg_atTop (𝕜 := ℝ) (n := m - n) hp)
            have hEq : (fun R : ℝ => (R ^ (m - n))⁻¹) =ᶠ[atTop] fun R : ℝ => R ^ n / R ^ m := by
              have hEq' : (fun R : ℝ => R ^ n / R ^ m) =ᶠ[atTop] fun R : ℝ => (R ^ (m - n))⁻¹ := by
                filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
                have hle : n ≤ m := le_of_lt hm
                have hm_eq : n + (m - n) = m := Nat.add_sub_of_le hle
                have hn0 : R ^ n ≠ 0 := pow_ne_zero n hR
                calc
                  R ^ n / R ^ m = R ^ n / R ^ (n + (m - n)) := by simp [hm_eq]
                  _ = R ^ n * ((R ^ (m - n))⁻¹ * (R ^ n)⁻¹) := by
                        simp [pow_add, div_eq_mul_inv, mul_comm]
                  _ = (R ^ (m - n))⁻¹ := by
                        ring_nf
                        simp [hn0]
              exact hEq'.symm
            exact Filter.Tendsto.congr' hEq hmain'
          have : Tendsto (fun R : ℝ => (2 : ℝ) ^ m * (R ^ n / R ^ m)) atTop (𝓝 ((2 : ℝ) ^ m * 0)) :=
            tendsto_const_nhds.mul hmain
          simpa [hident] using this
        have hinv : Tendsto (fun R : ℝ => ((R / 2) ^ m)⁻¹) atTop (𝓝 0) := by
          have hdiv : Tendsto (fun R : ℝ => R / 2) atTop atTop :=
            (tendsto_id.atTop_div_const (r := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2))
          have hpow : Tendsto (fun R : ℝ => (R / 2) ^ m) atTop atTop :=
            (Filter.tendsto_pow_atTop (α := ℝ) (n := m) hm0).comp hdiv
          simpa using! hpow.inv_tendsto_atTop
        have hdiv : Tendsto (fun R : ℝ => (1 + R) / R) atTop (𝓝 (1 : ℝ)) := by
          have hinv' : Tendsto (fun R : ℝ => (R : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
          have hadd : Tendsto (fun R : ℝ => (1 : ℝ) + (R : ℝ)⁻¹) atTop (𝓝 (1 : ℝ)) := by
            simpa using (tendsto_const_nhds.add hinv')
          have hEq : (fun R : ℝ => (1 + R) / R) =ᶠ[atTop] fun R : ℝ => (1 : ℝ) + (R : ℝ)⁻¹ := by
            filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
            field_simp [hR]; ring
          exact Filter.Tendsto.congr' hEq.symm hadd
        have hdiv_pow : Tendsto (fun R : ℝ => ((1 + R) / R) ^ n) atTop (𝓝 (1 : ℝ)) := by
          simpa using (hdiv.pow n)
        have hone_add_ratio :
            Tendsto (fun R : ℝ => (1 + R) ^ n / (R / 2) ^ m) atTop (𝓝 (0 : ℝ)) := by
          have hEq :
              (fun R : ℝ => (1 + R) ^ n / (R / 2) ^ m)
                =ᶠ[atTop] fun R : ℝ => ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m) := by
            filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
            have hRpow : (R ^ n : ℝ) ≠ 0 := pow_ne_zero n hR
            have hident :
                ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m) = (1 + R) ^ n / (R / 2) ^ m := by
              calc
                ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m)
                    = ((1 + R) ^ n / R ^ n) * (R ^ n / (R / 2) ^ m) := by
                        simp [div_pow]
                _ = ((1 + R) ^ n * R ^ n) / (R ^ n * (R / 2) ^ m) := by
                        simp [div_mul_div_comm, mul_comm]
                _ = ((1 + R) ^ n * R ^ n) / ((R / 2) ^ m * R ^ n) := by
                        simp [mul_comm]
                _ = (1 + R) ^ n / (R / 2) ^ m := by
                        simpa [mul_assoc, mul_comm, mul_left_comm] using
                          (mul_div_mul_right (a := (1 + R) ^ n) (b := (R / 2) ^ m) hRpow)
            exact hident.symm
          have hmul :
              Tendsto
                (fun R : ℝ => ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m))
                atTop (𝓝 (0 : ℝ)) := by
            simpa [mul_zero] using (hdiv_pow.mul hratio)
          exact Filter.Tendsto.congr' hEq.symm hmul
        have h1 : Tendsto (fun R : ℝ => C * ((1 + R) ^ n / (R / 2) ^ m)) atTop (𝓝 0) := by
          simpa using (tendsto_const_nhds.mul hone_add_ratio)
        have h2 : Tendsto (fun R : ℝ => K * ((R / 2) ^ m)⁻¹) atTop (𝓝 0) := by
          simpa using (tendsto_const_nhds.mul hinv)
        have hsum :
            Tendsto
              (fun R : ℝ => C * ((1 + R) ^ n / (R / 2) ^ m) + K * ((R / 2) ^ m)⁻¹)
              atTop (𝓝 0) := by
          simpa using (h1.add h2)
        have hrew :
            (fun R : ℝ => (C * (1 + R) ^ n + K) / (R / 2) ^ m)
              = fun R : ℝ => C * ((1 + R) ^ n / (R / 2) ^ m) + K * ((R / 2) ^ m)⁻¹ := by
          funext R
          simp [div_eq_mul_inv, mul_add, mul_assoc, mul_comm]
        have hbase : Tendsto (fun R : ℝ => (C * (1 + R) ^ n + K) / (R / 2) ^ m) atTop (𝓝 0) := by
          simpa [hrew] using hsum
        have hconst :
            Tendsto (fun _ : ℝ => (m.factorial : ℝ) * (2 : ℝ)) atTop
              (𝓝 ((m.factorial : ℝ) * (2 : ℝ))) := tendsto_const_nhds
        have hmul : Tendsto (fun R : ℝ => ((m.factorial : ℝ) * (2 : ℝ)) *
              ((C * (1 + R) ^ n + K) / (R / 2) ^ m)) atTop (𝓝 0) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using (hconst.mul hbase)
        have hRHS_rw : RHS = fun R : ℝ => ((m.factorial : ℝ) * (2 : ℝ)) *
              ((C * (1 + R) ^ n + K) / (R / 2) ^ m) := by
          funext R
          dsimp [RHS, K]
          ring_nf
        simpa [hRHS_rw] using hmul
      have hsmall : ∀ᶠ R in atTop, RHS R < ‖iteratedDeriv m f 0‖ / 2 :=
        (tendsto_order.1 hRHS_tendsto).2 _ (half_pos ha)
      have hle_eventually : ∀ᶠ R in atTop, ‖iteratedDeriv m f 0‖ ≤ RHS R := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hRpos
        exact hle_RHS R hRpos
      rcases (hle_eventually.and hsmall).exists with ⟨R, hle, hlt⟩
      have : ‖iteratedDeriv m f 0‖ < ‖iteratedDeriv m f 0‖ :=
        (lt_of_le_of_lt hle hlt).trans (half_lt_self ha)
      exact lt_irrefl _ this
    have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hm
    have hm0 : m ≠ 0 := ne_of_gt hmpos
    have hkcd : ContDiffAt ℂ (↑m) k (0 : ℂ) := (hk.analyticAt 0).contDiffAt
    have hccd : ContDiffAt ℂ (↑m) (fun _ : ℂ => k 0) (0 : ℂ) := contDiffAt_const
    have hsub :
        iteratedDeriv m f 0 =
          iteratedDeriv m k 0 - iteratedDeriv m (fun _ : ℂ => k 0) 0 := by
      simpa [f] using! (iteratedDeriv_sub (n := m) (x := (0 : ℂ)) hkcd hccd)
    have hconst0 : iteratedDeriv m (fun _ : ℂ => k 0) 0 = 0 := by
      simp [iteratedDeriv_const, hm0]
    have hf_eq : iteratedDeriv m f 0 = iteratedDeriv m k 0 := by
      simp [hsub, hconst0]
    simpa [hf_eq] using hf_iter_eq
  let P : Polynomial ℂ :=
    ∑ m ∈ Finset.range (n + 1), Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)
  have hPdeg : P.natDegree ≤ n := by
    have hnat :
        P.natDegree ≤
          Finset.fold max 0
            (fun m : ℕ =>
              (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
            (Finset.range (n + 1)) := by
      simpa [P, Function.comp] using
        (Polynomial.natDegree_sum_le (s := Finset.range (n + 1))
          (f := fun m : ℕ =>
            Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)))
    have hfold :
        Finset.fold max 0
            (fun m : ℕ =>
              (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
            (Finset.range (n + 1)) ≤ n := by
      refine (Finset.fold_max_le (f := fun m : ℕ =>
        (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
        (b := 0) (s := Finset.range (n + 1)) (c := n)).2 ?_
      refine ⟨Nat.zero_le n, ?_⟩
      intro m hm
      have hmon :
          (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree ≤ m :=
        Polynomial.natDegree_monomial_le _
      have hm_le : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.1 hm)
      exact hmon.trans hm_le
    exact hnat.trans hfold
  have hk_poly : ∀ z, k z = Polynomial.eval z P := by
    intro z
    have htaylor := Complex.taylorSeries_eq_of_entire' (c := (0 : ℂ)) (z := z) hk
    have htail : ∀ m : ℕ, m ∉ Finset.range (n + 1) →
        ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * (z - 0) ^ m) = 0 := by
      intro m hm'
      have hmgt : n < m := by
        have : n + 1 ≤ m := Nat.le_of_not_lt (by simpa [Finset.mem_range] using hm')
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) this
      have hz : iteratedDeriv m k 0 = 0 := hk_iteratedDeriv_eq_zero m hmgt
      simp [hz]
    have htsum :
        (∑' m : ℕ, (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * (z - 0) ^ m)
          = ∑ m ∈ Finset.range (n + 1), (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * z ^ m := by
      simpa [sub_zero] using (tsum_eq_sum (s := Finset.range (n + 1)) htail)
    have hfinite :
        k z = ∑ m ∈ Finset.range (n + 1), (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * z ^ m := by
      calc
        k z = ∑' m : ℕ, (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * (z - 0) ^ m := by
          simpa using htaylor.symm
        _ = _ := htsum
    have hEval :
        Polynomial.eval z P =
          ∑ m ∈ Finset.range (n + 1), z ^ m * ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0) := by
      classical
      change Polynomial.eval₂ (RingHom.id ℂ) z P = _
      let φ : Polynomial ℂ →+* ℂ := Polynomial.eval₂RingHom (RingHom.id ℂ) z
      change φ P = _
      simp [P, φ, Polynomial.eval₂_monomial, mul_comm]
    have hfinite' :
        k z = ∑ m ∈ Finset.range (n + 1), z ^ m * ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hfinite
    simpa [hEval] using hfinite'
  refine ⟨P, hPdeg, ?_⟩
  intro z
  have : H z = Complex.exp (k z) := by simp [hk_exp z]
  simp [this, hk_poly z]
end Hadamard
end Complex
end
end
section
noncomputable section
namespace Complex
namespace Hadamard
open Complex Real BigOperators Finset Set Filter Topology Metric
open scoped Topology
open Polynomial
private lemma vgj {n : ℕ} (hn : 0 < n) (w : ℂ) : ∃ z : ℂ, z ^ n = w := by
  classical
  by_cases hw : w = 0
  · subst hw
    refine ⟨0, ?_⟩
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    simp [hn0]
  · refine ⟨Complex.exp (Complex.log w / n), ?_⟩
    have hn0 : (n : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    calc
      (Complex.exp (Complex.log w / n)) ^ n
          = Complex.exp ((n : ℂ) * (Complex.log w / n)) := by
              simpa using (Complex.exp_nat_mul (Complex.log w / n) n).symm
      _ = Complex.exp (Complex.log w) := by
            have : (n : ℂ) * (Complex.log w / n) = Complex.log w := by
              field_simp [hn0]
            simp [this]
      _ = w := by simpa using (Complex.exp_log hw)
private lemma vhr (a : ℂ) (ha : a ≠ 0) :
    a * ((starRingEnd ℂ) a / (‖a‖ : ℂ)) = (‖a‖ : ℂ) := by
  have hnorm_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hnorm_ne : (‖a‖ : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hnorm_pos)
  have hmul : a * (starRingEnd ℂ) a = (Complex.normSq a : ℂ) :=
    Complex.mul_conj a
  have hcast : (Complex.normSq a : ℂ) = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast (Complex.normSq_eq_norm_sq a)
  have hdiv : ((‖a‖ ^ 2 : ℝ) : ℂ) / (‖a‖ : ℂ) = (‖a‖ : ℂ) := by
    have : ((‖a‖ ^ 2 : ℝ) : ℂ) = (‖a‖ : ℂ) * (‖a‖ : ℂ) := by
      simp [pow_two]
    calc
      ((‖a‖ ^ 2 : ℝ) : ℂ) / (‖a‖ : ℂ)
          = ((‖a‖ : ℂ) * (‖a‖ : ℂ)) / (‖a‖ : ℂ) := by simp [this]
      _ = (‖a‖ : ℂ) := by
            field_simp [hnorm_ne]
  calc
    a * ((starRingEnd ℂ) a / (‖a‖ : ℂ))
        = (a * (starRingEnd ℂ) a) / (‖a‖ : ℂ) := by
            simp [div_eq_mul_inv, mul_assoc]
    _ = (Complex.normSq a : ℂ) / (‖a‖ : ℂ) := by simp [hmul]
    _ = ((‖a‖ ^ 2 : ℝ) : ℂ) / (‖a‖ : ℂ) := by simp [hcast]
    _ = (‖a‖ : ℂ) := hdiv
private lemma vfe
    (P : Polynomial ℂ) (hn : 0 < P.natDegree) :
    ∃ R0 : ℝ, 0 < R0 ∧
      ∀ R : ℝ, R0 ≤ R →
        ∃ z : ℂ, ‖z‖ = R ∧
          (‖P.leadingCoeff‖ / 2) * R ^ P.natDegree ≤ (P.eval z).re := by
  classical
  set n : ℕ := P.natDegree
  have hn0 : 0 < n := hn
  have hP0 : P ≠ 0 := by
    intro h0
    simp [n, h0] at hn0
  have hLC : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
  set a : ℂ := P.leadingCoeff
  have ha : a ≠ 0 := hLC
  have hnorm_a_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  set wtarget : ℂ := (starRingEnd ℂ) a / (‖a‖ : ℂ)
  have hwtarget_norm : ‖wtarget‖ = (1 : ℝ) := by
    calc
      ‖wtarget‖ = ‖(starRingEnd ℂ) a‖ / ‖(‖a‖ : ℂ)‖ := by
        simp [wtarget]
      _ = ‖a‖ / ‖a‖ := by simp
      _ = (1 : ℝ) := by
        field_simp [hnorm_a_pos.ne']
  rcases vgj (n := n) hn0 (w := wtarget) with ⟨w, hw⟩
  have hw_norm : ‖w‖ = (1 : ℝ) := by
    have hpow : (‖w‖ : ℝ) ^ n = 1 := by
      have := congrArg (fun z : ℂ => ‖z‖) hw
      simpa [norm_pow, hwtarget_norm] using this
    have hn0' : n ≠ 0 := Nat.ne_of_gt hn0
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg w) hn0').1 hpow
  set S : ℝ := ∑ i ∈ Finset.range n, ‖P.coeff i‖
  set R0 : ℝ := max 1 (2 * S / ‖a‖)
  refine ⟨R0, ?_, ?_⟩
  · have : (0 : ℝ) < (1 : ℝ) := by norm_num
    exact lt_of_lt_of_le this (le_max_left _ _)
  · intro R hR
    have hR_ge1 : (1 : ℝ) ≤ R := by
      exact le_trans (le_max_left _ _) hR
    have hR_nonneg : 0 ≤ R := le_trans (by norm_num) hR_ge1
    set z : ℂ := (R : ℂ) * w
    have hz_norm : ‖z‖ = R := by
      have : ‖z‖ = |R| * ‖w‖ := by
        simp [z]
      simp [this, hw_norm, abs_of_nonneg hR_nonneg]
    have h_eval : P.eval z =
        (∑ i ∈ Finset.range n, P.coeff i * z ^ i) + P.coeff n * z ^ n := by
      have hsum : P.eval z = ∑ i ∈ Finset.range (n + 1), P.coeff i * z ^ i := by
        have : P.natDegree + 1 = n + 1 := by simp [n]
        simpa [this] using (Polynomial.eval_eq_sum_range (p := P) z)
      have hsplit :
          (∑ i ∈ Finset.range (n + 1), P.coeff i * z ^ i)
            = (∑ i ∈ Finset.range n, P.coeff i * z ^ i) + P.coeff n * z ^ n := by
        simpa using (Finset.sum_range_succ (f := fun i => P.coeff i * z ^ i) n)
      exact hsum.trans hsplit
    have h_lower_norm :
        ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ ≤ S * R ^ (n - 1) := by
      have h1 :
          ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖
            ≤ ∑ i ∈ Finset.range n, ‖P.coeff i * z ^ i‖ := by
        simpa using (norm_sum_le (Finset.range n) (fun i => P.coeff i * z ^ i))
      have hterm : ∀ i ∈ Finset.range n, ‖P.coeff i * z ^ i‖ ≤ ‖P.coeff i‖ * R ^ (n - 1) := by
        intro i hi
        have hi_lt : i < n := Finset.mem_range.mp hi
        have hi_le : i ≤ n - 1 := Nat.le_pred_of_lt hi_lt
        have hzpow : ‖z‖ ^ i ≤ R ^ (n - 1) := by
          have hmono : ‖z‖ ^ i ≤ ‖z‖ ^ (n - 1) :=
            pow_le_pow_right₀ (by simpa [hz_norm] using hR_ge1) hi_le
          simpa [hz_norm] using hmono
        calc
          ‖P.coeff i * z ^ i‖ = ‖P.coeff i‖ * ‖z‖ ^ i := by
            simp [norm_pow]
          _ ≤ ‖P.coeff i‖ * R ^ (n - 1) := by
            exact mul_le_mul_of_nonneg_left hzpow (norm_nonneg _)
      have h2 :
          ∑ i ∈ Finset.range n, ‖P.coeff i * z ^ i‖
            ≤ ∑ i ∈ Finset.range n, ‖P.coeff i‖ * R ^ (n - 1) := by
        exact Finset.sum_le_sum (fun i hi => hterm i hi)
      have h3 :
          (∑ i ∈ Finset.range n, ‖P.coeff i‖ * R ^ (n - 1))
            = (∑ i ∈ Finset.range n, ‖P.coeff i‖) * R ^ (n - 1) := by
        simp [Finset.sum_mul]
      have hsum_le : (∑ i ∈ Finset.range n, ‖P.coeff i‖) ≤ S := by
        simp [S]
      calc
        ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖
            ≤ ∑ i ∈ Finset.range n, ‖P.coeff i * z ^ i‖ := h1
        _ ≤ ∑ i ∈ Finset.range n, ‖P.coeff i‖ * R ^ (n - 1) := h2
        _ = (∑ i ∈ Finset.range n, ‖P.coeff i‖) * R ^ (n - 1) := h3
        _ ≤ S * R ^ (n - 1) := by
              exact mul_le_mul_of_nonneg_right hsum_le (pow_nonneg hR_nonneg _)
    have h_lead_re : (P.coeff n * z ^ n).re = ‖a‖ * R ^ n := by
      have hw_pow : w ^ n = wtarget := hw
      have ha_mul : a * w ^ n = (‖a‖ : ℂ) := by
        have : a * w ^ n = a * wtarget := by simp [hw_pow]
        simpa [wtarget, a] using (this.trans (vhr a ha))
      have hz_pow : z ^ n = ((R : ℂ) ^ n) * (w ^ n) := by
        simp [z, mul_pow, mul_comm]
      have hcoeffn : P.coeff n = a := by simp [a, n, Polynomial.coeff_natDegree]
      have hreR : ∀ m : ℕ, (((R : ℂ) ^ m).re) = R ^ m := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
            simp [pow_succ, ih, mul_re]
      calc
        (P.coeff n * z ^ n).re
            = (a * z ^ n).re := by simp [hcoeffn]
        _ = (a * (((R : ℂ) ^ n) * (w ^ n))).re := by simp [hz_pow]
        _ = (((R : ℂ) ^ n) * (a * (w ^ n))).re := by
              ring_nf
        _ = (((R : ℂ) ^ n) * (‖a‖ : ℂ)).re := by simp [ha_mul]
        _ = (((R : ℂ) ^ n).re) * ‖a‖ := by
              simp [mul_re]
        _ = (R ^ n) * ‖a‖ := by simp [hreR n]
        _ = ‖a‖ * R ^ n := by ring
    refine ⟨z, hz_norm, ?_⟩
    have hre_lower : (∑ i ∈ Finset.range n, P.coeff i * z ^ i).re
        ≥ -‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ := by
      have habs : |(∑ i ∈ Finset.range n, P.coeff i * z ^ i).re|
          ≤ ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ :=
        Complex.abs_re_le_norm _
      have := neg_le_of_abs_le habs
      simpa using this
    have hre_main :
        (P.eval z).re ≥ (P.coeff n * z ^ n).re - ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ := by
      have : (P.eval z).re =
          (∑ i ∈ Finset.range n, P.coeff i * z ^ i).re + (P.coeff n * z ^ n).re := by
        simp [h_eval, add_comm]
      linarith [this, hre_lower]
    have hR_ge_R0 : R0 ≤ R := hR
    have hR_ge : 2 * S / ‖a‖ ≤ R := le_trans (le_max_right _ _) hR_ge_R0
    have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR_ge1
    have hR_nonneg' : 0 ≤ R := le_of_lt hRpos
    have hn_ge1 : 1 ≤ n := Nat.succ_le_of_lt hn0
    have hlower_le : S * R ^ (n - 1) ≤ (‖a‖ / 2) * R ^ n := by
      have ha_pos : 0 < ‖a‖ := hnorm_a_pos
      have hS_le : S ≤ (‖a‖ / 2) * R := by
        have : 2 * S ≤ ‖a‖ * R := by
          have := (mul_le_mul_of_nonneg_left hR_ge (by linarith [ha_pos.le] : (0 : ℝ) ≤ ‖a‖))
          have hne : (‖a‖ : ℝ) ≠ 0 := ne_of_gt ha_pos
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hne] using this
        have : S ≤ (‖a‖ * R) / 2 := by linarith
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
      have : S * R ^ (n - 1) ≤ (‖a‖ / 2) * R * R ^ (n - 1) := by
        have hpow_nonneg : 0 ≤ R ^ (n - 1) := pow_nonneg hR_nonneg' _
        exact mul_le_mul_of_nonneg_right hS_le hpow_nonneg
      have hRR : R * R ^ (n - 1) = R ^ n := by
        have : n = (n - 1) + 1 := by
          exact (Nat.sub_add_cancel hn_ge1).symm
        rw [this, pow_succ]
        ring_nf; grind
      simpa [mul_assoc, hRR] using this
    have hfinal_re :
        (‖a‖ / 2) * R ^ n ≤ (P.eval z).re := by
      have hlower' : ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ ≤ (‖a‖ / 2) * R ^ n := by
        exact h_lower_norm.trans hlower_le
      have hlead : (P.coeff n * z ^ n).re = ‖a‖ * R ^ n := by simpa [a] using h_lead_re
      have hre_main' :
          (‖a‖ * R ^ n) - ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ ≤ (P.eval z).re := by
        simpa [hlead] using hre_main
      have hsub :
          (‖a‖ * R ^ n) - (‖a‖ / 2) * R ^ n ≤
            (‖a‖ * R ^ n) - ‖∑ i ∈ Finset.range n, P.coeff i * z ^ i‖ :=
        sub_le_sub_left hlower' (‖a‖ * R ^ n)
      have hsim : (‖a‖ * R ^ n) - (‖a‖ / 2) * R ^ n = (‖a‖ / 2) * R ^ n := by ring
      have : (‖a‖ * R ^ n) - (‖a‖ / 2) * R ^ n ≤ (P.eval z).re :=
        hsub.trans hre_main'
      simpa [hsim] using this
    simpa [a, n] using hfinal_re
theorem vdD
    {ρ : ℝ} (hρ : 0 ≤ ρ) (P : Polynomial ℂ)
    (hgrowth :
      ∃ C > 0, ∀ z : ℂ,
        Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    P.natDegree ≤ Nat.floor ρ := by
  classical
  by_cases hdeg : P.natDegree = 0
  · simp [hdeg]
  · have hnpos : 0 < P.natDegree := Nat.pos_of_ne_zero hdeg
    rcases vfe (P := P) hnpos with ⟨R0, hR0pos, hray⟩
    rcases hgrowth with ⟨C, hCpos, hC⟩
    have hLCpos : 0 < ‖P.leadingCoeff‖ := by
      have hP0 : P ≠ 0 := by
        intro h0
        simp [h0] at hdeg
      have : P.leadingCoeff ≠ 0 := (Polynomial.leadingCoeff_ne_zero).2 hP0
      exact norm_pos_iff.2 this
    let c : ℝ := ‖P.leadingCoeff‖ / 2
    have hcpos : 0 < c := by
      have : (0 : ℝ) < (2 : ℝ) := by norm_num
      exact (div_pos hLCpos this)
    have hn_le_real : (P.natDegree : ℝ) ≤ ρ := by
      by_contra hnlt
      have hnlt' : ρ < (P.natDegree : ℝ) := lt_of_not_ge hnlt
      let δ : ℝ := (P.natDegree : ℝ) - ρ
      have hδ : 0 < δ := sub_pos.2 hnlt'
      let K0 : ℝ := (C * (2 : ℝ) ^ ρ) / c
      have hK0 : ∃ R1, ∀ R ≥ R1, K0 + 1 ≤ R ^ δ := by
        have h : ∀ᶠ R in (atTop : Filter ℝ), K0 + 1 ≤ R ^ δ :=
          (tendsto_atTop.mp (tendsto_rpow_atTop hδ)) (K0 + 1)
        rcases (eventually_atTop.1 h) with ⟨R1, hR1⟩
        exact ⟨R1, hR1⟩
      rcases hK0 with ⟨R1, hR1⟩
      set R : ℝ := max (max R0 1) R1
      have hR_ge_R0 : R0 ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
      have hR_ge1 : (1 : ℝ) ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
      have hR_ge_R1 : R1 ≤ R := le_max_right _ _
      have hR_pos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR_ge1
      have hRδ : K0 + 1 ≤ R ^ δ := hR1 R hR_ge_R1
      rcases hray R hR_ge_R0 with ⟨z, hz_norm, hz_re⟩
      have hlog_lower :
          (P.eval z).re ≤ Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) := by
        have hpos : 0 < ‖Complex.exp (Polynomial.eval z P)‖ := by
          simp
        have hle :
            ‖Complex.exp (Polynomial.eval z P)‖ ≤
              1 + ‖Complex.exp (Polynomial.eval z P)‖ := by
          linarith [norm_nonneg (Complex.exp (Polynomial.eval z P))]
        have hlog_le : Real.log ‖Complex.exp (Polynomial.eval z P)‖
            ≤ Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) :=
          Real.log_le_log hpos hle
        have hlog_eq : Real.log ‖Complex.exp (Polynomial.eval z P)‖ = (P.eval z).re := by
          simp [Complex.norm_exp]
        simpa [hlog_eq] using hlog_le
      have hlog_upper :
          Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) ≤ C * (1 + ‖z‖) ^ ρ :=
        hC z
      have hmain : c * R ^ (P.natDegree : ℝ) ≤ C * (1 + R) ^ ρ := by
        have hz_re' : c * R ^ P.natDegree ≤ (P.eval z).re := by
          simpa [c] using hz_re
        have hz_re'' : c * R ^ (P.natDegree : ℝ) ≤ (P.eval z).re := by
          simpa [Real.rpow_natCast, c] using hz_re'
        have : c * R ^ (P.natDegree : ℝ) ≤ Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) :=
          hz_re''.trans hlog_lower
        have : c * R ^ (P.natDegree : ℝ) ≤ C * (1 + ‖z‖) ^ ρ :=
          this.trans hlog_upper
        simpa [hz_norm] using this
      have h1R_le : (1 + R : ℝ) ≤ R * 2 := by linarith
      have hpow1 : (1 + R : ℝ) ^ ρ ≤ (R * 2) ^ ρ :=
        Real.rpow_le_rpow (by linarith [hR_pos.le]) h1R_le hρ
      have hR2 : (R * 2) ^ ρ = R ^ ρ * (2 : ℝ) ^ ρ := by
        have hRnonneg : 0 ≤ R := le_of_lt hR_pos
        have h2nonneg : 0 ≤ (2 : ℝ) := by norm_num
        simpa [mul_assoc] using (Real.mul_rpow hRnonneg h2nonneg (z := ρ))
      have hmain' : c * R ^ (P.natDegree : ℝ) ≤ C * (R ^ ρ * (2 : ℝ) ^ ρ) := by
        have := le_trans hmain (mul_le_mul_of_nonneg_left hpow1 (le_of_lt hCpos))
        simpa [hR2, mul_assoc, mul_left_comm, mul_comm] using this
      have hRρ_pos : 0 < R ^ ρ := Real.rpow_pos_of_pos hR_pos _
      have hRρ_ne : (R ^ ρ : ℝ) ≠ 0 := ne_of_gt hRρ_pos
      have hdiv :
          (c * R ^ (P.natDegree : ℝ)) / (R ^ ρ) ≤ C * (2 : ℝ) ^ ρ := by
        have h :=
            div_le_div_of_nonneg_right hmain' (le_of_lt hRρ_pos)
        have hRhs : (C * (R ^ ρ * (2 : ℝ) ^ ρ)) / (R ^ ρ) = C * (2 : ℝ) ^ ρ := by
          field_simp [hRρ_ne]
        simpa [hRhs, mul_assoc, mul_left_comm, mul_comm] using h
      have hRsub : R ^ δ = R ^ (P.natDegree : ℝ) / R ^ ρ := by
        simpa [δ] using (Real.rpow_sub hR_pos (P.natDegree : ℝ) ρ)
      have hRδ_le : c * (R ^ δ) ≤ C * (2 : ℝ) ^ ρ := by
        have hLhs : c * (R ^ δ) = (c * R ^ (P.natDegree : ℝ)) / (R ^ ρ) := by
          simp [hRsub, div_eq_mul_inv, mul_left_comm, mul_comm]
        simpa [hLhs] using hdiv
      have hRδ_le' : R ^ δ ≤ K0 := by
        have : R ^ δ ≤ (C * (2 : ℝ) ^ ρ) / c := by
          refine (le_div_iff₀ hcpos).2 ?_
          simpa [mul_assoc, mul_left_comm, mul_comm] using hRδ_le
        simpa [K0] using this
      have : K0 + 1 ≤ K0 := le_trans hRδ (le_trans hRδ_le' (le_rfl))
      exact (not_lt_of_ge this) (lt_add_of_pos_right _ (by norm_num : (0 : ℝ) < 1))
    exact (Nat.le_floor_iff hρ).2 hn_le_real
theorem vcU {τ : ℝ} (hτ : 0 ≤ τ) (P : Polynomial ℂ)
    (hbound :
      ∃ C > 0, ∀ z : ℂ,
        ‖Complex.exp (Polynomial.eval z P)‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ)) :
    P.natDegree ≤ Nat.floor τ := by
  rcases hbound with ⟨C, hCpos, hC⟩
  have hlog_growth :
      ∃ C > 0, ∀ z : ℂ,
        Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) ≤ C * (1 + ‖z‖) ^ τ :=
    Real.vca
      (f := fun z : ℂ => Complex.exp (Polynomial.eval z P))
      (r := fun z : ℂ => 1 + ‖z‖) hCpos hτ
      (fun z => by linarith [norm_nonneg z]) hC
  exact vdD (ρ := τ) hτ P hlog_growth
end Hadamard
end Complex
end
end
section
noncomputable section
open Set Filter Asymptotics
open scoped Topology BigOperators
namespace Complex.Hadamard
lemma vdF
    {f : ℂ → ℂ} (hentire : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    {B r : ℝ} (hrpos : 0 < r) (hr_le_B : r ≤ B)
    (smallSet : Set (vab f (Set.univ : Set ℂ))) (hsmall_fin : smallSet.Finite)
    (hsmallSet :
      smallSet = {p : vab f (Set.univ : Set ℂ) | ‖vaa p‖ ≤ B})
    (hr_not_bad :
      let small : Finset (vab f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
      let a : vab f (Set.univ : Set ℂ) → ℝ := fun p => ‖vaa p‖
      r ∉ small.image a) :
    ∀ u : ℂ, ‖u‖ = r → f u ≠ 0 := by
  classical
  let small : Finset (vab f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
  let a : vab f (Set.univ : Set ℂ) → ℝ := fun p => ‖vaa p‖
  let bad : Finset ℝ := small.image a
  have hr_not_bad' : r ∉ bad := by
    simpa [bad, small, a] using hr_not_bad
  have hr_not :
      ∀ p : vab f (Set.univ : Set ℂ),
        ‖vaa p‖ ≤ B → r ≠ ‖vaa p‖ := by
    intro p hpB hEq
    have hp_small : p ∈ small := by
      have hp_mem : p ∈ smallSet := by
        simpa [hsmallSet] using hpB
      simpa [small] using (hsmall_fin.mem_toFinset.2 hp_mem)
    have : r ∈ bad := Finset.mem_image.2 ⟨p, hp_small, by simpa [a] using hEq.symm⟩
    exact (hr_not_bad' this).elim
  exact vdk (f := f) hentire hnot
    (B := B) (r := r) hrpos hr_le_B hr_not
theorem vbW
    {f : ℂ → ℂ} {ρ τ : ℝ} {m : ℕ}
    (hmρ : (m : ℝ) ≤ ρ) (hτ : ρ < τ) (hτ_lt : τ < (m + 1 : ℝ))
    (hτ_nonneg : 0 ≤ τ)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1)))
    (hsumτ : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ τ)) :
    let Sτ : ℝ :=
      ∑' p : vab f (Set.univ : Set ℂ), ‖vaa p‖⁻¹ ^ τ
    let Cprod : ℝ := vaS m τ Sτ
    ∀ {R r : ℝ}, 0 < R → 1 ≤ R → R ≤ r → r ≤ 2 * R →
      ∀ (smallSet : Set (vab f (Set.univ : Set ℂ)))
        (hsmall_fin : smallSet.Finite),
        smallSet =
            {p : vab f (Set.univ : Set ℂ) |
              ‖vaa p‖ ≤ 4 * R} →
        (let small : Finset (vab f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
         let a : vab f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖vaa p‖
         r ∉ small.image a) →
        (let small : Finset (vab f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
         let a : vab f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖vaa p‖
         (∑ p ∈ small, (1 : ℝ) * CartanBound.φ (r / a p)) ≤
          CartanBound.Cφ * (small.card : ℝ)) →
        ∀ u : ℂ, ‖u‖ = r →
          ‖(u ^ analyticOrderNatAt f 0 *
              vac m f (Set.univ : Set ℂ) u)⁻¹‖
            ≤ Real.exp (Cprod * (1 + r) ^ τ) := by
  classical
  intro Sτ Cprod R r hRpos hRle hR_le_r hr_le_2R smallSet hsmall_fin
    hsmallSet hr_not_bad hr_phi u hur
  let small : Finset (vab f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
  let a : vab f (Set.univ : Set ℂ) → ℝ := fun p => ‖vaa p‖
  let bad : Finset ℝ := small.image a
  have hr_not_bad' : r ∉ bad := by
    simpa [bad, small, a] using hr_not_bad
  have hr1 : (1 : ℝ) ≤ r := le_trans hRle hR_le_r
  have hpow_inv_le1 : ‖(u ^ analyticOrderNatAt f 0)⁻¹‖ ≤ 1 :=
    Complex.vee u (analyticOrderNatAt f 0) (by simpa [hur] using hr1)
  let fac : vab f (Set.univ : Set ℂ) → ℂ :=
    fun p => vae m (u / vaa p)
  have hloc :
      HasProdLocallyUniformlyOn
        (fun (p : vab f (Set.univ : Set ℂ)) (w : ℂ) =>
          vae m (w / vaa p))
        (vac m f (Set.univ : Set ℂ))
        (Set.univ : Set ℂ) :=
    vav (m := m) (f := f) h_sum
  have hprod :
      HasProd fac (vac m f (Set.univ : Set ℂ) u) :=
    hloc.hasProd (by simp : u ∈ (Set.univ : Set ℂ))
  let ap : vab f (Set.univ : Set ℂ) → ℝ := fun p => ‖vaa p‖
  have : DecidablePred (fun p : vab f (Set.univ : Set ℂ) => p ∈ small) :=
    Classical.decPred _
  let b : vab f (Set.univ : Set ℂ) → ℝ :=
    fun p =>
      if hp : p ∈ small then
        CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
      else
        (2 : ℝ) * (r / ap p) ^ τ
  have hterm : ∀ p, ‖(fac p)⁻¹‖ ≤ Real.exp (b p) := by
    intro p
    by_cases hp : p ∈ small
    · have hval_ne : r ≠ ap p := by
        intro hEq
        have : r ∈ bad := by
          refine Finset.mem_image.2 ⟨p, hp, ?_⟩
          simp [ap, a, hEq]
        exact (hr_not_bad' this).elim
      have hval0 : vaa p ≠ 0 := vao p
      have hmτ : (m : ℝ) ≤ τ := le_trans hmρ (le_of_lt hτ)
      have hnear :
          ‖(vae m (u / vaa p))⁻¹‖
            ≤ Real.exp (CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)) := by
        simpa [ap] using
          (vdt (m := m) (τ := τ) (r := r)
              (u := u) (a := vaa p)
              (hur := hur) (ha := hval0) (hr := by simpa [ap] using hval_ne) hmτ)
      simpa [fac, b, hp] using hnear
    · have hlarge : (4 * R : ℝ) < ap p := by
        have : ¬ap p ≤ 4 * R := by
          intro hle
          have : p ∈ small := by
            have hp_mem : p ∈ smallSet := by
              simpa [hsmallSet, ap] using hle
            simpa [small] using (hsmall_fin.mem_toFinset.2 hp_mem)
          exact hp this
        exact lt_of_not_ge this
      have hz' : ‖u / vaa p‖ ≤ (1 / 2 : ℝ) :=
        vbu (z := u) (a := vaa p)
          (R := 2 * R) (by nlinarith [hRpos]) (by rw [hur]; exact hr_le_2R)
          (by nlinarith [hlarge])
      have hτ_le : τ ≤ (m + 1 : ℝ) := le_of_lt hτ_lt
      have hfar :
          ‖(vae m (u / vaa p))⁻¹‖ ≤
            Real.exp ((2 : ℝ) * (r / ap p) ^ τ) := by
        simpa [ap] using
          (vdC (m := m) (τ := τ) (r := r)
              (u := u) (a := vaa p)
              (hur := hur) (ha := vao p) (hz := hz') hτ_le)
      simpa [fac, b, hp] using hfar
  have hb_le :
      ∀ s : Finset (vab f (Set.univ : Set ℂ)),
        (∑ p ∈ s, b p) ≤ Cprod * (1 + r) ^ τ := by
    intro s
    simpa [small, ap, b, Sτ, Cprod, a, hsmallSet] using
      (Complex.Hadamard.vgb (f := f) (m := m) (τ := τ) (R := R) (r := r)
        (hRpos := hRpos) (hrpos := lt_of_lt_of_le hRpos hR_le_r)
        (hR_le_r := hR_le_r) (hτ_nonneg := hτ_nonneg)
        (smallSet := smallSet) (hsmall_fin := hsmall_fin) (hsmallSet := hsmallSet)
        (hsumτ := hsumτ)
        (hr_phi := by
          simpa [small, a, one_mul] using hr_phi)
        s)
  have hcprod_inv :
      ‖(vac m f (Set.univ : Set ℂ) u)⁻¹‖ ≤
        Real.exp (Cprod * (1 + r) ^ τ) := by
    refine vcI
      (α := vab f (Set.univ : Set ℂ)) (fac := fac)
      (F := vac m f (Set.univ : Set ℂ) u)
      hprod (b := b) (B := Cprod * (1 + r) ^ τ) ?_ ?_
    · exact hterm
    · intro s
      exact hb_le s
  have hmul :
      ‖(u ^ analyticOrderNatAt f 0 *
          vac m f (Set.univ : Set ℂ) u)⁻¹‖
        =
      ‖(u ^ analyticOrderNatAt f 0)⁻¹‖ *
        ‖(vac m f (Set.univ : Set ℂ) u)⁻¹‖ := by
    simp [mul_inv_rev, mul_comm]
  rw [hmul]
  have :
      ‖(u ^ analyticOrderNatAt f 0)⁻¹‖ *
          ‖(vac m f (Set.univ : Set ℂ) u)⁻¹‖
        ≤ 1 * Real.exp (Cprod * (1 + r) ^ τ) :=
    mul_le_mul hpow_inv_le1 hcprod_inv (by positivity) (by positivity)
  simpa using this
theorem vcA
    {f H : ℂ → ℂ} {ρ τ : ℝ} {m : ℕ} {Cf : ℝ}
    (hmρ : (m : ℝ) ≤ ρ) (hτ : ρ < τ) (hτ_lt : τ < (m + 1 : ℝ))
    (hτ_nonneg : 0 ≤ τ) (hentire : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1)))
    (hsumτ : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ τ))
    (hf_boundτ : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (Cf * (1 + ‖z‖) ^ τ))
    (hfactor : ∀ z : ℂ,
      f z =
        H z * z ^ analyticOrderNatAt f 0 *
          vac m f (Set.univ : Set ℂ) z) :
    let Sτ : ℝ :=
      ∑' p : vab f (Set.univ : Set ℂ), ‖vaa p‖⁻¹ ^ τ
    let Cprod : ℝ := vaS m τ Sτ
    ∀ {R r : ℝ}, 0 < R → 1 ≤ R → R ≤ r → r ≤ 2 * R → 0 < r →
      ∀ (smallSet : Set (vab f (Set.univ : Set ℂ)))
        (hsmall_fin : smallSet.Finite),
        smallSet =
            {p : vab f (Set.univ : Set ℂ) |
              ‖vaa p‖ ≤ 4 * R} →
        (let small : Finset (vab f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
         let a : vab f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖vaa p‖
         r ∉ small.image a) →
        (let small : Finset (vab f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
         let a : vab f (Set.univ : Set ℂ) → ℝ :=
          fun p => ‖vaa p‖
         (∑ p ∈ small, (1 : ℝ) * CartanBound.φ (r / a p)) ≤
          CartanBound.Cφ * (small.card : ℝ)) →
        ∀ u : ℂ, ‖u‖ = r → ‖H u‖ ≤ Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
  classical
  intro Sτ Cprod R r hRpos hRle hR_le_r hr_le_2R hrpos smallSet hsmall_fin
    hsmallSet hr_not_bad hr_phi u hur
  let small : Finset (vab f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
  let a : vab f (Set.univ : Set ℂ) → ℝ := fun p => ‖vaa p‖
  let bad : Finset ℝ := small.image a
  have hr_not_bad' : r ∉ bad := by
    simpa [bad, small, a] using hr_not_bad
  have hden_eq :
      f u =
        H u * (u ^ analyticOrderNatAt f 0 *
          vac m f (Set.univ : Set ℂ) u) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (hfactor u)
  have hfu_ne : f u ≠ 0 := by
    have hr_le_4R : r ≤ 4 * R := by nlinarith [hr_le_2R, hRpos]
    exact vdF (f := f) hentire hnot
      (B := 4 * R) (r := r) hrpos hr_le_4R smallSet hsmall_fin hsmallSet
      (by simpa [small, a] using hr_not_bad) u hur
  have hden_ne :
      (u ^ analyticOrderNatAt f 0 *
        vac m f (Set.univ : Set ℂ) u) ≠ 0 := by
    intro hden0
    have : f u = 0 := by simpa [hden0] using hden_eq
    exact hfu_ne this
  have hHu :
      H u =
        f u / (u ^ analyticOrderNatAt f 0 *
          vac m f (Set.univ : Set ℂ) u) := by
    exact eq_div_of_mul_eq hden_ne (Eq.symm hden_eq)
  have hf_u : ‖f u‖ ≤ Real.exp (Cf * (1 + r) ^ τ) := by
    simpa [hur] using hf_boundτ u
  have hden_inv :
      ‖(u ^ analyticOrderNatAt f 0 *
          vac m f (Set.univ : Set ℂ) u)⁻¹‖
        ≤ Real.exp (Cprod * (1 + r) ^ τ) := by
    simpa [Sτ, Cprod] using
      (vbW
        (f := f) (ρ := ρ) (τ := τ) (m := m)
        hmρ hτ hτ_lt hτ_nonneg h_sum hsumτ
        (R := R) (r := r) hRpos hRle hR_le_r hr_le_2R
        smallSet hsmall_fin hsmallSet
        (by simpa [small, a] using hr_not_bad)
        (by simpa [small, a, one_mul] using hr_phi)
        u hur)
  have :
      ‖H u‖ ≤
        ‖f u‖ *
          ‖(u ^ analyticOrderNatAt f 0 *
            vac m f (Set.univ : Set ℂ) u)⁻¹‖ := by
    have :
        ‖H u‖ =
          ‖f u /
            (u ^ analyticOrderNatAt f 0 *
              vac m f (Set.univ : Set ℂ) u)‖ := by
      simp [hHu]
    simp [div_eq_mul_inv, norm_inv, this]
  have hmul :
      ‖f u‖ *
          ‖(u ^ analyticOrderNatAt f 0 *
            vac m f (Set.univ : Set ℂ) u)⁻¹‖
        ≤ Real.exp (Cf * (1 + r) ^ τ) * Real.exp (Cprod * (1 + r) ^ τ) :=
    mul_le_mul hf_u hden_inv (by positivity) (by positivity)
  have hexp :
      Real.exp (Cf * (1 + r) ^ τ) * Real.exp (Cprod * (1 + r) ^ τ)
        = Real.exp ((Cf + Cprod) * (1 + r) ^ τ) := by
    simp [Real.exp_add, add_mul, add_comm]
  have : ‖H u‖ ≤ Real.exp ((Cf + Cprod) * (1 + r) ^ τ) :=
    (this.trans hmul).trans_eq hexp
  have hslack :
      Real.exp ((Cf + Cprod) * (1 + r) ^ τ) ≤
        Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
    refine Real.exp_le_exp.2 ?_
    have hnn : 0 ≤ (1 + r) ^ τ := by positivity
    nlinarith
  exact this.trans hslack
theorem vcL {f H : ℂ → ℂ} {ρ τ : ℝ} {m : ℕ}
    (hρ : 0 ≤ ρ) (hmρ : (m : ℝ) ≤ ρ) (hτ : ρ < τ) (hτ_lt : τ < (m + 1 : ℝ))
    (hτ_nonneg : 0 ≤ τ) (hentire : Differentiable ℂ f) (hH_entire : Differentiable ℂ H)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (m + 1)))
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ)
    (hfactor : ∀ z : ℂ,
      f z =
        H z * z ^ analyticOrderNatAt f 0 *
          vac m f (Set.univ : Set ℂ) z) :
    ∃ C > 0, ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := by
  rcases hgrowth with ⟨Cf, hCfpos, hCf⟩
  have hsumτ :
      Summable (fun p : vab f (Set.univ : Set ℂ) =>
        ‖vaa p‖⁻¹ ^ τ) :=
    vaE (f := f) (ρ := ρ) (τ := τ)
      hρ hτ hentire hnot ⟨Cf, hCfpos, hCf⟩
  let Sτ : ℝ := ∑' p : vab f (Set.univ : Set ℂ), ‖vaa p‖⁻¹ ^ τ
  have hSτ_nonneg : 0 ≤ Sτ := tsum_nonneg fun _ =>
    Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
  let Cprod : ℝ := vaS m τ Sτ
  have hCprod_nonneg : 0 ≤ Cprod := by
    simpa [Cprod] using veP (m := m) (τ := τ) hSτ_nonneg
  have hf_boundτ : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (Cf * (1 + ‖z‖) ^ τ) :=
    Real.ved
      (f := f) (r := fun z : ℂ => 1 + ‖z‖) (C := Cf) (ρ := ρ) (τ := τ)
      hCfpos.le (fun z => by linarith [norm_nonneg z]) (le_of_lt hτ) hCf
  refine ⟨(Cf + Cprod + 10) * (3 : ℝ) ^ τ, by
    have h3τ : 0 < (3 : ℝ) ^ τ := by positivity
    nlinarith [hCfpos, hCprod_nonneg, h3τ], ?_⟩
  intro z
  let R : ℝ := max ‖z‖ 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hRle : (1 : ℝ) ≤ R := le_max_right _ _
  let smallSet : Set (vab f (Set.univ : Set ℂ)) :=
    {p | ‖vaa p‖ ≤ 4 * R}
  have hsmall_fin : smallSet.Finite := by
    have : Metric.closedBall (0 : ℂ) (4 * R) ⊆ (Set.univ : Set ℂ) := by simp
    simpa [smallSet] using
      (vat (f := f) (U := (Set.univ : Set ℂ))
        (B := 4 * R) this)
  let small : Finset (vab f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
  let a : vab f (Set.univ : Set ℂ) → ℝ := fun p => ‖vaa p‖
  have ha_pos : ∀ p ∈ small, 0 < a p := by
    intro p hp
    exact norm_pos_iff.2 (vao p)
  let bad : Finset ℝ := small.image a
  rcases CartanBound.vbL
      (s := small) (w := fun _ => (1 : ℝ)) (a := a)
      (hw := by intro _ _; norm_num) (ha := ha_pos) (bad := bad) (R := R) hRpos with
    ⟨r, hr_mem, hr_not_bad, hr_phi⟩
  have hR_le_r : R ≤ r := le_of_lt hr_mem.1
  have hr_le_2R : r ≤ 2 * R := hr_mem.2
  have hrpos : 0 < r := lt_of_lt_of_le hRpos hR_le_r
  have hcircle :
      ∀ u : ℂ, ‖u‖ = r → ‖H u‖ ≤ Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
    simpa [Sτ, Cprod] using
      (vcA
        (f := f) (H := H) (ρ := ρ) (τ := τ) (m := m) (Cf := Cf)
        hmρ hτ hτ_lt hτ_nonneg hentire hnot h_sum hsumτ hf_boundτ hfactor
        (R := R) (r := r) hRpos hRle hR_le_r hr_le_2R hrpos
        smallSet hsmall_fin (by rfl)
        (by simpa [small, a, bad] using hr_not_bad)
        (by simpa [small, a, one_mul, Finset.sum_const, nsmul_eq_mul] using hr_phi))
  have hz_ball : z ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (le_max_left _ _) hr_mem.1
  have hball :
      ‖H z‖ ≤ Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
    exact Complex.vcE hH_entire hrpos hz_ball hcircle
  have hr_le_3 : 1 + r ≤ 3 * (1 + ‖z‖) := by
    exact Real.vcx (norm_nonneg z)
      (by simpa [R] using hr_le_2R)
  have hmain :
      Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ)
        ≤ Real.exp (((Cf + Cprod + 10) * (3 : ℝ) ^ τ) * (1 + ‖z‖) ^ τ) := by
    have hnn : 0 ≤ (Cf + Cprod + 10) := by nlinarith [le_of_lt hCfpos, hCprod_nonneg]
    exact Real.vdw hnn (by norm_num)
      (by linarith [le_of_lt hrpos]) (by positivity) hτ_nonneg hr_le_3
  simpa [mul_assoc] using hball.trans hmain
theorem vem {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hentire : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt f 0) *
            vac (Nat.floor ρ) f (Set.univ : Set ℂ) z := by
  set m : ℕ := Nat.floor ρ
  have h_sum :
      Summable (fun p : vab f (Set.univ : Set ℂ) =>
        ‖vaa p‖⁻¹ ^ (m + 1)) := by
    simpa [m] using
      (vaZ (f := f) (ρ := ρ)
        hρ hentire hnot hgrowth)
  rcases vdu (m := m) (f := f) hentire hnot h_sum with
    ⟨H, hH_entire, hH_ne, hfactor⟩
  rcases Real.vaG hρ with
    ⟨τ, hτ, hτ_lt, hτ_nonneg, hfloorτ'⟩
  have hfloorτ : Nat.floor τ = m := by
    simpa [m] using hfloorτ'
  have hτ_lt_m : τ < (m + 1 : ℝ) := by
    simpa [m] using hτ_lt
  have hτ_lt_nat : τ < ((m + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using hτ_lt_m
  have hmρ : (m : ℝ) ≤ ρ := by
    have := Nat.floor_le hρ
    simpa [m] using this
  have hH_bound_rpow :
      ∃ C > 0, ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) :=
    vcL (f := f) (H := H) (ρ := ρ) (τ := τ)
      (m := m) hρ hmρ hτ hτ_lt hτ_nonneg hentire hH_entire hnot h_sum hgrowth hfactor
  have hH_growth_nat :
      ∃ C > 0, ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (m + 1)) := by
    exact Real.vdc
      (f := H) (r := fun z : ℂ => 1 + ‖z‖)
      (fun z => by linarith [norm_nonneg z]) hτ_lt_nat hH_bound_rpow
  rcases vdq (H := H) (n := m + 1)
      hH_entire hH_ne hH_growth_nat with
    ⟨P, hPn, hHP⟩
  have hPnat : P.natDegree ≤ m := by
    have hbound :
        ∃ C > 0, ∀ z : ℂ,
          ‖Complex.exp (Polynomial.eval z P)‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := by
      rcases hH_bound_rpow with ⟨C, hCpos, hC⟩
      exact ⟨C, hCpos, fun z => by simpa [hHP z] using (hC z)⟩
    have := vcU hτ_nonneg P hbound
    simpa [hfloorτ] using this
  refine ⟨P, ?_, ?_⟩
  · have : P.degree ≤ m := Polynomial.degree_le_of_natDegree_le hPnat
    simpa [m] using this
  · intro z
    have hH' : H z = Complex.exp (Polynomial.eval z P) := by simpa using (hHP z)
    simpa [hH', mul_assoc, mul_left_comm, mul_comm, m] using (hfactor z)
end Complex.Hadamard
end
end
section
noncomputable section
open Set Filter Asymptotics
open scoped Topology BigOperators
namespace Complex.Hadamard
def vaP (ρ : ℝ) (f : ℂ → ℂ) : Prop :=
    Differentiable ℂ f ∧ ∀ ε : ℝ, 0 < ε →
  ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (ρ + ε))
namespace vaP
theorem differentiable {ρ : ℝ} {f : ℂ → ℂ} (h : vaP ρ f) :
    Differentiable ℂ f :=
  h.1
theorem exists_bound {ρ ε : ℝ} {f : ℂ → ℂ} (h : vaP ρ f)
    (hε : 0 < ε) :
    ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (ρ + ε)) :=
  h.2 ε hε
theorem vdZ {ρ τ : ℝ} {f : ℂ → ℂ} (h : vaP ρ f)
    (hτ : ρ < τ) (hτ_nonneg : 0 ≤ τ) :
    ∃ C' > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C' * (1 + ‖z‖) ^ τ := by
  rcases h.exists_bound (sub_pos.2 hτ) with ⟨C, hCpos, hC⟩
  have hnorm : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := by
    intro z
    simpa [sub_add_cancel] using (hC z)
  exact Real.vca (f := f)
    (r := fun z : ℂ => 1 + ‖z‖) hCpos hτ_nonneg
    (fun z => by linarith [norm_nonneg z]) hnorm
theorem vcW {ρ : ℝ} {f : ℂ → ℂ}
    (h : vaP ρ f) (hρ : 0 ≤ ρ) (hnot : ∃ z : ℂ, f z ≠ 0) :
    Summable (fun p : vab f (Set.univ : Set ℂ) =>
      ‖vaa p‖⁻¹ ^ (Nat.floor ρ + 1)) := by
  rcases Real.vaG hρ with
    ⟨τ, hτ, _hτ_lt, hτ_nonneg, hfloorτ⟩
  have hgrowthτ :
      ∃ C' > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C' * (1 + ‖z‖) ^ τ :=
    h.vdZ hτ hτ_nonneg
  have hsummable :=
    vaZ
      (f := f) (ρ := τ) hτ_nonneg h.differentiable hnot hgrowthτ
  simpa [hfloorτ] using hsummable
end vaP
theorem veu {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (horder : vaP ρ f) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt f 0) *
            vac (Nat.floor ρ) f (Set.univ : Set ℂ) z := by
  classical
  let hentire : Differentiable ℂ f := horder.differentiable
  set m : ℕ := Nat.floor ρ
  rcases Real.vaG hρ with
    ⟨τ, hτ, hτ_lt, hτ_nonneg, hfloorτ'⟩
  have hfloorτ : Nat.floor τ = m := by
    simpa [m] using hfloorτ'
  have hgrowthτ :
      ∃ C' > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C' * (1 + ‖z‖) ^ τ :=
    horder.vdZ hτ hτ_nonneg
  rcases vem (f := f) (ρ := τ) hτ_nonneg
      hentire hnot hgrowthτ with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, ?_, ?_⟩
  · simpa [m, hfloorτ] using hdeg
  · intro z
    simpa [m, hfloorτ] using hfac z
end Complex.Hadamard
end
end
section
namespace Polynomial
theorem vhn (P : ℂ[X]) (z : ℂ) :
    logDeriv (fun w : ℂ => Complex.exp (Polynomial.eval w P)) z =
      Polynomial.eval z P.derivative := by
  have hderiv :
      deriv (fun w : ℂ => Complex.exp (Polynomial.eval w P)) z =
        Complex.exp (Polynomial.eval z P) * Polynomial.eval z P.derivative := by
    simpa [Function.comp_def, mul_comm] using
      ((Complex.hasDerivAt_exp (Polynomial.eval z P)).comp z (P.hasDerivAt z)).deriv
  rw [logDeriv_apply, hderiv]
  field_simp [Complex.exp_ne_zero (Polynomial.eval z P)]
end Polynomial
end
section
namespace Erdos985.Analytic.HadamardAux
open Complex.Hadamard
variable {f : ℂ → ℂ}
lemma vhT (hf : Differentiable ℂ f) (p : vab f Set.univ) :
    f (vaa p) = 0 := by
  have h := vbm p
  rw [vaw hf] at h
  exact apply_eq_zero_of_analyticOrderNatAt_ne_zero (by exact_mod_cast h)
noncomputable def viL (hf : Differentiable ℂ f) (p : vab f Set.univ) :
    {ρ : ℂ // f ρ = 0} :=
  ⟨vaa p, vhT hf p⟩
lemma vfZ {E : Type*} [NormedAddCommGroup E]
    (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) (g : ℂ → E) {a : E}
    (h : HasSum (fun p : vab f Set.univ => g (vaa p)) a) :
    HasSum (fun ρ : {ρ : ℂ // f ρ = 0} => analyticOrderNatAt f ρ • g ρ) a := by
  classical
  set π := viL hf
  have h' := (Equiv.sigmaFiberEquiv π).hasSum_iff.mpr h
  refine h'.sigma fun ρ => ?_
  have hiff : ∀ p, π p = ρ ↔ p ∈ vad f (ρ : ℂ) := by
    intro p
    rw [vai]
    simp [π, viL, Subtype.ext_iff]
  let _ : Fintype {p // π p = ρ} :=
    Fintype.subtype (vad f (ρ : ℂ)) (fun p => (hiff p).symm)
  have hρ0 : (ρ : ℂ) ≠ 0 := fun h0 => hf0 (by simpa [h0] using ρ.2)
  have hcard : Fintype.card {p // π p = ρ} = analyticOrderNatAt f ρ := by
    rw [← vaA hf hρ0]
    exact Fintype.card_of_subtype _ (fun p => (hiff p).symm)
  have hc : ∀ c : {p // π p = ρ},
      g (vaa ((Equiv.sigmaFiberEquiv π) ⟨ρ, c⟩)) = g ρ := by
    intro c
    have : vaa c.1 = ρ := congrArg Subtype.val c.2
    simp [Equiv.sigmaFiberEquiv_apply, this]
  simp only [Function.comp_def, hc]
  rw [← hcard]
  convert hasSum_fintype (fun _ : {p // π p = ρ} => g ρ) using 1
  simp
lemma vfR (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hgrowth : ∃ C : ℝ, ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (C * ‖z‖ * Real.log (‖z‖ + 2))) :
    vaP 1 f := by
  obtain ⟨C, hC⟩ := hgrowth
  have hCpos : 0 < C := by
    have h0 := hC 0
    simp only [norm_zero, mul_zero, zero_mul, Real.exp_zero, mul_one] at h0
    exact lt_of_lt_of_le (norm_pos_iff.2 hf0) h0
  refine ⟨hf, fun ε hε => ?_⟩
  refine ⟨|Real.log C| + C * (1 + 1 / ε) + 1, by positivity, fun z => ?_⟩
  set r := ‖z‖
  have hr : 0 ≤ r := norm_nonneg z
  have h1 : 1 ≤ 1 + r := by linarith
  set Y := (1 + r) ^ ((1 : ℝ) + ε)
  have hA : 1 + r ≤ Y := Real.self_le_rpow_of_one_le h1 (by linarith)
  have hB : 1 ≤ Y := le_trans h1 hA
  have hlog : Real.log (r + 2) ≤ 1 + (1 + r) ^ ε / ε := by
    have h4 : Real.log (r + 2) ≤ Real.log 2 + Real.log (1 + r) := by
      rw [← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log (by linarith) (by nlinarith)
    have h2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    have h3 := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ 1 + r) hε
    linarith
  have hmul : (1 + r) * (1 + r) ^ ε = Y := by
    simp only [Y]
    rw [Real.rpow_add (by linarith), Real.rpow_one]
  have e1 : Real.log C ≤ |Real.log C| * Y :=
    le_trans (le_abs_self _) (le_mul_of_one_le_right (abs_nonneg _) hB)
  have e2 : C * r * Real.log (r + 2) ≤ C * (1 + 1 / ε) * Y := by
    calc C * r * Real.log (r + 2) ≤ C * (1 + r) * (1 + (1 + r) ^ ε / ε) := by
          gcongr
          · exact Real.log_nonneg (by linarith)
          · linarith
      _ = C * ((1 + r) + ((1 + r) * (1 + r) ^ ε) / ε) := by ring
      _ = C * ((1 + r) + Y / ε) := by rw [hmul]
      _ ≤ C * (Y + Y / ε) := by gcongr
      _ = C * (1 + 1 / ε) * Y := by ring
  calc ‖f z‖ ≤ C * Real.exp (C * r * Real.log (r + 2)) := hC z
    _ = Real.exp (Real.log C + C * r * Real.log (r + 2)) := by
      rw [Real.exp_add, Real.exp_log hCpos]
    _ ≤ Real.exp ((|Real.log C| + C * (1 + 1 / ε) + 1) * Y) := by
      gcongr
      have : (|Real.log C| + C * (1 + 1 / ε) + 1) * Y
          = |Real.log C| * Y + C * (1 + 1 / ε) * Y + Y := by ring
      rw [this]
      linarith
end Erdos985.Analytic.HadamardAux
end
section
namespace Erdos985.Analytic
open Complex.Hadamard HadamardAux
theorem vcM {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hgrowth : ∃ C : ℝ, ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (C * ‖z‖ * Real.log (‖z‖ + 2))) :
    (∀ ε : ℝ, 0 < ε → Summable fun ρ : {ρ : ℂ // f ρ = 0} =>
        (analyticOrderNatAt f ρ : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + ε)) ∧
    ∃ b : ℂ, ∀ z : ℂ, f z ≠ 0 →
      Summable (fun ρ : {ρ : ℂ // f ρ = 0} =>
        (analyticOrderNatAt f ρ : ℂ) * (1 / (z - ρ) + 1 / ρ)) ∧
      deriv f z / f z = b + ∑' ρ : {ρ : ℂ // f ρ = 0},
        (analyticOrderNatAt f ρ : ℂ) * (1 / (z - ρ) + 1 / ρ) := by
  have hord := vfR hf hf0 hgrowth
  have hnot : ∃ z, f z ≠ 0 := ⟨0, hf0⟩
  have hsum2 : Summable (fun p : vab f Set.univ =>
      ‖vaa p‖⁻¹ ^ (2 : ℕ)) := by
    simpa [Nat.floor_one] using hord.vcW (by norm_num) hnot
  constructor
  · intro ε hε
    obtain ⟨C', hC', hlog⟩ :=
      hord.vdZ (τ := 1 + ε / 2) (by linarith) (by linarith)
    have hs := vaE (τ := 1 + ε)
      (by linarith) (by linarith) hf hnot ⟨C', hC', hlog⟩
    have hW := vfZ hf hf0 (fun x : ℂ => ‖x‖⁻¹ ^ (1 + ε)) hs.hasSum
    refine hW.summable.congr fun ρ => ?_
    simp [nsmul_eq_mul, Real.inv_rpow (norm_nonneg _), div_eq_mul_inv]
  · obtain ⟨P, hdeg, hfac⟩ :=
      veu (by norm_num : (0 : ℝ) ≤ 1) hnot hord
    refine ⟨P.coeff 1, fun z hz => ?_⟩
    have hz' : ∀ p : vab f Set.univ, z ≠ vaa p :=
      fun p h => hz (h ▸ vhT hf p)
    have hS := vaM hsum2 hz'
    have hW := vfZ hf hf0 (fun x : ℂ => 1 / (z - x) + 1 / x) hS.hasSum
    simp only [nsmul_eq_mul] at hW
    refine ⟨hW.summable, ?_⟩
    rw [hW.tsum_eq]
    have h0 : analyticOrderNatAt f 0 = 0 := by
      by_contra h
      exact hf0 (apply_eq_zero_of_analyticOrderNatAt_ne_zero h)
    set G : ℂ → ℂ := vac 1 f Set.univ with hG
    have hfun : f = fun w => Complex.exp (Polynomial.eval w P) * G w := by
      funext w
      simpa [h0, G, Nat.floor_one] using hfac w
    have hdiff_exp : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (Polynomial.eval w P)) z :=
      (P.differentiable.differentiableAt (x := z)).cexp
    have hG0 : G z ≠ 0 := vbk 1 f hsum2 hz'
    have hGd : DifferentiableAt ℂ G z := vcz 1 f hsum2 z
    have hP1 : Polynomial.eval z P.derivative = P.coeff 1 := by
      have hdeg' : P.degree ≤ 1 := by simpa [Nat.floor_one] using hdeg
      rw [Polynomial.eq_X_add_C_of_degree_le_one hdeg']
      simp
    have hL : logDeriv f z = logDeriv (fun w : ℂ => Complex.exp (Polynomial.eval w P) * G w) z := by
      conv_lhs => rw [hfun]
    rw [← logDeriv_apply, hL, logDeriv_mul (f := fun w : ℂ => Complex.exp (Polynomial.eval w P)) (g := G) z
        (Complex.exp_ne_zero _) hG0 hdiff_exp hGd,
      Polynomial.vhn, hP1,
      vbA hsum2 hz']
end Erdos985.Analytic
end
section
open Complex MeasureTheory Set
namespace Erdos985.Analytic.PerronKernel
noncomputable def cesaro (t : ℝ) : ℂ := ((max 0 (1 - t) : ℝ) : ℂ)
lemma vhp : Continuous cesaro := by
  unfold cesaro; fun_prop
lemma vfJ {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    cesaro t = indicator (Ioc 0 1) (fun _ => 1 : ℝ → ℂ) t
      - indicator (Ioc 0 1) (fun t => (t : ℂ) ^ (1 : ℂ) : ℝ → ℂ) t := by
  simp only [mem_Ioi] at ht
  unfold cesaro
  by_cases h1 : t ≤ 1
  · have hm : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, h1⟩
    rw [indicator_of_mem hm, indicator_of_mem hm, cpow_one, max_eq_right (by linarith)]
    push_cast; ring
  · have hm : t ∉ Ioc (0 : ℝ) 1 := fun h => h1 h.2
    rw [indicator_of_notMem hm, indicator_of_notMem hm, max_eq_left (by linarith)]
    simp
lemma vfB {s : ℂ} (hs : 0 < s.re) : HasMellin cesaro s (1 / (s * (s + 1))) := by
  have h1 := hasMellin_one_Ioc hs
  have h2 := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by simp; linarith)
  have h := hasMellin_sub h1.1 h2.1
  rw [h1.2, h2.2] at h
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hval : 1 / s - 1 / (s + 1) = 1 / (s * (s + 1)) := by field_simp; ring
  rw [hval] at h
  refine ⟨?_, ?_⟩
  · have := h.1
    unfold MellinConvergent at this ⊢
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [vfJ ht]
  · rw [← h.2]
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [vfJ ht]
lemma denom_ne_zero (c : ℝ) (hc : 0 < c) (t : ℝ) :
    ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1) ≠ 0 := by
  have h0 : ((c : ℂ) + t * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h1 : ((c : ℂ) + t * I + 1) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  exact mul_ne_zero h0 h1
lemma viA (c : ℝ) (hc : 0 < c) (t : ℝ) :
    min (c ^ 2) 1 * (1 + t ^ 2) ≤ ‖((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)‖ := by
  have hs : ‖(c : ℂ) + t * I‖ ^ 2 = c ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have hs1 : ‖(c : ℂ) + t * I‖ ^ 2 ≤ ‖(c : ℂ) + t * I + 1‖ ^ 2 := by
    rw [hs, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; nlinarith
  have hn1 : ‖(c : ℂ) + t * I‖ ≤ ‖(c : ℂ) + t * I + 1‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hs1
  rw [norm_mul]
  calc min (c ^ 2) 1 * (1 + t ^ 2) ≤ c ^ 2 + t ^ 2 := by
        rcases le_total (c ^ 2) 1 with h | h
        · rw [min_eq_left h]; nlinarith [sq_nonneg t]
        · rw [min_eq_right h]; linarith
    _ = ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I‖ := by rw [← hs]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hn1 (norm_nonneg _)
lemma vgF (c : ℝ) (hc : 0 < c) :
    Continuous fun t : ℝ => 1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) :=
  by
  have h1 : Continuous fun t : ℝ => ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1) := by
    have h0 : Continuous fun t : ℝ => (c : ℂ) + t * I :=
      continuous_const.add (continuous_ofReal.mul continuous_const)
    exact h0.mul (h0.add continuous_const)
  exact Continuous.div (f := fun _ => (1:ℂ)) continuous_const h1 (denom_ne_zero c hc)
lemma vde (c : ℝ) (hc : 0 < c) :
    Integrable fun t : ℝ => 1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  have hm : 0 < min (c ^ 2) 1 := lt_min (by positivity) one_pos
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (min (c ^ 2) 1)⁻¹)
    (vgF c hc).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_div, norm_one]
  have h := viA c hc t
  have hpos : 0 < min (c ^ 2) 1 * (1 + t ^ 2) := by positivity
  calc 1 / ‖((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)‖ ≤ 1 / (min (c ^ 2) 1 * (1 + t ^ 2)) :=
        one_div_le_one_div_of_le hpos h
    _ = (min (c ^ 2) 1)⁻¹ * (1 + t ^ 2)⁻¹ := by rw [one_div, mul_inv]
theorem vfl (y c : ℝ) (hy : 0 < y) (hc : 0 < c) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = (max 0 (1 - 1 / y) : ℝ) := by
  have hmel : ∀ t : ℝ, mellin cesaro ((c : ℂ) + t * I)
      = 1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := fun t =>
    (vfB (s := (c : ℂ) + t * I) (by simpa using hc)).2
  have hconv : MellinConvergent cesaro (c : ℂ) := (vfB (by simpa using hc)).1
  have hvert : VerticalIntegrable (mellin cesaro) c := by
    unfold VerticalIntegrable
    simp_rw [hmel]
    exact vde c hc
  have hinv := mellinInv_mellin_eq (E := ℂ) c cesaro (x := 1 / y) (by positivity) hconv hvert
    vhp.continuousAt
  have hint : (∫ t : ℝ,
      (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)))
      = ∫ t : ℝ, (((1 / y : ℝ)) : ℂ) ^ (-((c : ℂ) + t * I)) • mellin cesaro ((c : ℂ) + t * I) := by
    congr 1
    funext t
    rw [hmel t, smul_eq_mul, ofReal_div, ofReal_one, one_div (y : ℂ),
      inv_cpow_ofReal_nonneg hy.le, cpow_neg, inv_inv]
    ring
  rw [hint]
  unfold mellinInv at hinv
  rw [Complex.real_smul] at hinv
  have h2 : ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 / (2 * (Real.pi : ℂ)) := by push_cast; ring
  rw [h2] at hinv
  exact hinv
end Erdos985.Analytic.PerronKernel
end
section
open Complex MeasureTheory Set Filter
namespace Erdos985.Analytic.PerronKernel
theorem vgL (y c : ℝ) (hy : 0 < y) (hc : 0 < c) :
    ∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = 2 * Real.pi * (if 1 ≤ y then 1 - 1 / y else 0) := by
  have h := vfl y c hy hc
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have := Real.pi_pos; exact mul_ne_zero two_ne_zero (ofReal_ne_zero.2 this.ne')
  have h' : (∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)))
      = 2 * Real.pi * ((max 0 (1 - 1 / y) : ℝ) : ℂ) := by
    rw [← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
  rw [h']
  congr 1
  split_ifs with h1
  · rw [max_eq_right (by rw [sub_nonneg, div_le_one hy]; exact h1)]
  · rw [max_eq_left (by
      rw [sub_nonpos, le_div_iff₀ hy]; linarith)]
noncomputable def K (c y t : ℝ) : ℂ :=
  (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
lemma vje (c y t : ℝ) (hy : 0 < y) :
    ‖K c y t‖ = y ^ c * ‖1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖ := by
  unfold K
  rw [div_eq_mul_one_div, norm_mul, norm_cpow_eq_rpow_re_of_pos hy]
  simp
lemma vhj (c y : ℝ) (hc : 0 < c) (hy : 0 < y) : Integrable (K c y) := by
  have hcont : Continuous (K c y) := by
    unfold K
    have h0 : Continuous fun t : ℝ => (c : ℂ) + t * I :=
      continuous_const.add (continuous_ofReal.mul continuous_const)
    have h1 : Continuous fun t : ℝ => ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1) :=
      h0.mul (h0.add continuous_const)
    exact (h0.const_cpow (Or.inl (ofReal_ne_zero.2 hy.ne'))).div h1 (denom_ne_zero c hc)
  refine Integrable.mono' ((vde c hc).norm.const_mul (y ^ c))
    hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [vje c y t hy]
lemma vie (c y : ℝ) (hy : 0 < y) :
    ∫ t : ℝ, ‖K c y t‖ = y ^ c * ∫ t : ℝ, ‖1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖ := by
  simp_rw [vje c y _ hy]
  rw [integral_const_mul]
lemma viQ (a : ℕ → ℂ) (c t : ℝ) (N n : ℕ) (hN : 1 ≤ N) :
    LSeries.term a ((c : ℂ) + t * I) n * ((N : ℂ) ^ ((c : ℂ) + t * I)
        / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)))
      = if n = 0 then 0 else a n * K c ((N : ℝ) / n) t := by
  rw [LSeries.term_def]
  split_ifs with hn
  · simp
  · unfold K
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
    have hnc : (n : ℂ) ^ ((c : ℂ) + t * I) ≠ 0 := by
      rw [cpow_ne_zero_iff]; left; exact_mod_cast hn
    rw [ofReal_div, div_eq_mul_inv ((N : ℝ) : ℂ), ← ofReal_inv, mul_cpow_ofReal_nonneg
      (by positivity) (by positivity), ofReal_inv, inv_cpow_ofReal_nonneg hn0.le, ofReal_natCast,
      ofReal_natCast]
    field_simp
theorem vhU (a : ℕ → ℂ) (c : ℝ) (hc : 0 < c)
    (ha : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioo 0 N, a n * (1 - (n : ℂ) / N)
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, LSeries a ((c : ℂ) + t * I) * (N : ℂ) ^ ((c : ℂ) + t * I)
          / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  set C := ∫ t : ℝ, ‖1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖ with hC
  have hC0 : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : ∀ n : ℕ, n ≠ 0 → (0 : ℝ) < (N : ℝ) / n := fun n hn =>
    div_pos hN0 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn))
  let G : ℕ → ℝ → ℂ := fun n t => if n = 0 then 0 else a n * K c ((N : ℝ) / n) t
  have hG_int : ∀ n, Integrable (G n) := by
    intro n
    by_cases hn : n = 0
    · simp only [G, hn, ↓reduceIte]; exact integrable_zero _ _ _
    · simp only [G, hn, ↓reduceIte]; exact (vhj c _ hc (hpos n hn)).const_mul _
  have hG_norm : ∀ n, ∫ t, ‖G n t‖ = if n = 0 then 0 else ‖a n‖ * (((N : ℝ) / n) ^ c * C) := by
    intro n
    by_cases hn : n = 0
    · simp [G, hn]
    · simp only [G, hn, ↓reduceIte, norm_mul]
      rw [integral_const_mul, vie c _ (hpos n hn)]
  have hsum : Summable fun n => ∫ t, ‖G n t‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) (ha.mul_left ((N : ℝ) ^ c * C))
    rw [hG_norm]
    split_ifs with hn
    · have : 0 ≤ ‖a n‖ / (n : ℝ) ^ c := div_nonneg (norm_nonneg _) (by positivity)
      positivity
    · rw [Real.div_rpow hN0.le (Nat.cast_nonneg n)]
      apply le_of_eq
      ring
  have hfun : (fun t : ℝ => LSeries a ((c : ℂ) + t * I) * (N : ℂ) ^ ((c : ℂ) + t * I)
        / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))) = fun t => ∑' n, G n t := by
    funext t
    rw [mul_div_assoc, LSeries, ← tsum_mul_right]
    congr 1
    funext n
    exact viQ a c t N n hN
  have hGint : ∀ n, ∫ t, G n t = if n = 0 then 0 else
      a n * (2 * Real.pi * ((if 1 ≤ (N : ℝ) / n then 1 - 1 / ((N : ℝ) / n) else 0 : ℝ) : ℂ)) := by
    intro n
    by_cases hn : n = 0
    · simp [G, hn]
    · simp only [G, hn, ↓reduceIte]
      rw [integral_const_mul]
      unfold K
      rw [vgL _ c (hpos n hn) hc]
  rw [hfun, ← integral_tsum_of_summable_integral_norm hG_int hsum]
  simp_rw [hGint]
  rw [tsum_eq_sum (s := Finset.Ioo 0 N), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Ioo] at hn
    have hn0 : n ≠ 0 := by omega
    have hle : 1 ≤ (N : ℝ) / n := by
      rw [one_le_div (Nat.cast_pos.2 (by omega))]; exact_mod_cast hn.2.le
    simp only [hn0, hle, ↓reduceIte]
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    push_cast
    field_simp
  · intro n hn
    rw [Finset.mem_Ioo] at hn
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, ↓reduceIte]
      have hnN : N ≤ n := by omega
      rcases eq_or_lt_of_le hnN with h | h
      · subst h
        have hNc : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0
        simp [div_self (show (N : ℝ) ≠ 0 by exact_mod_cast hn0)]
      · have hlt : ¬ 1 ≤ (N : ℝ) / n := by
          rw [not_le, div_lt_one (Nat.cast_pos.2 (by omega))]; exact_mod_cast h
        simp [hlt]
end Erdos985.Analytic.PerronKernel
end
section
open Complex MeasureTheory Set Filter Topology
namespace Erdos985.Analytic.PerronKernel
noncomputable def ver (w : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (-w) / (w * (w + 1)) - 1 / w + (t : ℂ) / (1 + w)
noncomputable def vdn (w : ℂ) (t : ℝ) : ℂ := if t ≤ 1 then ver w t else 0
lemma viU (w : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ -1) : ver w 1 = 0 := by
  have h1 : w + 1 ≠ 0 := fun h => hw1 (eq_neg_of_add_eq_zero_left h)
  have h2 : 1 + w ≠ 0 := by rwa [add_comm]
  unfold ver
  simp only [ofReal_one, one_cpow]
  field_simp
  ring
lemma vfI (w : ℂ) {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    vdn w t = (1 / (w * (w + 1))) • indicator (Ioc 0 1) (fun t => (t : ℂ) ^ (-w) : ℝ → ℂ) t
      - (1 / w) • indicator (Ioc 0 1) (fun _ => 1 : ℝ → ℂ) t
      + (1 / (1 + w)) • indicator (Ioc 0 1) (fun t => (t : ℂ) ^ (1 : ℂ) : ℝ → ℂ) t := by
  simp only [mem_Ioi] at ht
  unfold vdn ver
  by_cases h1 : t ≤ 1
  · have hm : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, h1⟩
    simp only [h1, ↓reduceIte]
    rw [indicator_of_mem hm, indicator_of_mem hm, indicator_of_mem hm, cpow_one]
    simp only [smul_eq_mul]
    ring
  · have hm : t ∉ Ioc (0 : ℝ) 1 := fun h => h1 h.2
    simp only [h1, ↓reduceIte]
    rw [indicator_of_notMem hm, indicator_of_notMem hm, indicator_of_notMem hm]
    simp
lemma vfE {s w : ℂ} (hs : 0 < s.re) (hsw : w.re < s.re) (hw0 : w ≠ 0)
    (hw1 : w ≠ -1) : HasMellin (vdn w) s (1 / ((s - w) * s * (s + 1))) := by
  have hA := hasMellin_cpow_Ioc (-w) (s := s) (by simp; linarith)
  have hB := hasMellin_one_Ioc hs
  have hC := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by simp; linarith)
  have hA' := hasMellin_const_smul hA.1 (1 / (w * (w + 1)))
  have hB' := hasMellin_const_smul hB.1 (1 / w)
  have hC' := hasMellin_const_smul hC.1 (1 / (1 + w))
  have hAB := hasMellin_sub hA'.1 hB'.1
  have h := hasMellin_add hAB.1 hC'.1
  rw [hAB.2, hA'.2, hB'.2, hC'.2, hA.2, hB.2, hC.2] at h
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hsw0 : s - w ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hsw0' : s + -w ≠ 0 := by rwa [← sub_eq_add_neg]
  have h1 : w + 1 ≠ 0 := fun h => hw1 (eq_neg_of_add_eq_zero_left h)
  have h2 : 1 + w ≠ 0 := by rwa [add_comm]
  have hval : (1 / (w * (w + 1))) • (1 / (s + -w)) - (1 / w) • (1 / s)
      + (1 / (1 + w)) • (1 / (s + 1)) = 1 / ((s - w) * s * (s + 1)) := by
    simp only [smul_eq_mul, ← sub_eq_add_neg]
    field_simp
    ring
  rw [hval] at h
  refine ⟨?_, ?_⟩
  · have := h.1
    unfold MellinConvergent at this ⊢
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [vfI w ht]
  · rw [← h.2]
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [vfI w ht]
lemma vgT (w : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ -1) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ContinuousAt (vdn w) x₀ := by
  set a := min (x₀ / 2) (1 / 2) with ha
  have ha0 : 0 < a := lt_min (by positivity) (by norm_num)
  have ha1 : a ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hax : a < x₀ := (min_le_left _ _).trans_lt (by linarith)
  let g : ℝ → ℂ := fun t => if t ≤ 1 then ver w (max t a) else 0
  have hE : Continuous fun t : ℝ => ver w (max t a) := by
    have hm : Continuous fun t : ℝ => max t a := continuous_id.max continuous_const
    have hpow : Continuous fun t : ℝ => ((max t a : ℝ) : ℂ) ^ (-w) := by
      refine continuous_iff_continuousAt.2 fun t => ?_
      refine ContinuousAt.cpow (continuous_ofReal.comp hm).continuousAt continuousAt_const ?_
      exact ofReal_mem_slitPlane.2 (lt_of_lt_of_le ha0 (le_max_right _ _))
    unfold ver
    exact ((hpow.div_const _).sub continuous_const).add
      ((continuous_ofReal.comp hm).div_const _)
  have hg : Continuous g := by
    refine continuous_if_le continuous_id continuous_const hE.continuousOn
      continuous_const.continuousOn (fun t ht => ?_)
    rw [ht, max_eq_left ha1]
    exact viU w hw0 hw1
  have hev : g =ᶠ[𝓝 x₀] vdn w := by
    filter_upwards [Ioi_mem_nhds hax] with t ht
    simp only [g, vdn, max_eq_left (le_of_lt (mem_Ioi.1 ht))]
  exact hg.continuousAt.congr hev
lemma vfw (c : ℝ) (hc : 0 < c) (w : ℂ) (hw : w.re < c) :
    Integrable fun t : ℝ =>
      1 / (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  have hδ : 0 < c - w.re := by linarith
  have hne : ∀ t : ℝ, ((c : ℂ) + t * I - w) ≠ 0 := by
    intro t h; have := congrArg Complex.re h; simp at this; linarith
  have hcont : Continuous fun t : ℝ =>
      1 / (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
    have h0 : Continuous fun t : ℝ => (c : ℂ) + t * I :=
      continuous_const.add (continuous_ofReal.mul continuous_const)
    have h1 : Continuous fun t : ℝ =>
        ((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1) :=
      ((h0.sub continuous_const).mul h0).mul (h0.add continuous_const)
    refine Continuous.div (f := fun _ => (1:ℂ)) continuous_const h1 (fun t => ?_)
    rw [mul_assoc]
    exact mul_ne_zero (hne t) (denom_ne_zero c hc t)
  refine Integrable.mono' ((vde c hc).norm.const_mul (c - w.re)⁻¹)
    hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have hge : c - w.re ≤ ‖(c : ℂ) + t * I - w‖ := by
    have := re_le_norm ((c : ℂ) + t * I - w); simpa using this
  rw [mul_assoc, norm_div, norm_div, norm_one, norm_mul]
  rw [← one_div_mul_one_div, ← one_div (c - w.re)]
  exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hδ hge)
    (one_div_nonneg.2 (norm_nonneg _))
theorem vgY (x c : ℝ) (hx : 1 ≤ x) (hc : 0 < c) (w : ℂ) (hw : w.re < c)
    (hw0 : w ≠ 0) (hw1 : w ≠ -1) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = (x : ℂ) ^ w / (w * (w + 1)) - 1 / w + (x : ℂ) ^ (-1 : ℂ) / (1 + w) := by
  have hx0 : 0 < x := by linarith
  have hmel : ∀ t : ℝ, mellin (vdn w) ((c : ℂ) + t * I)
      = 1 / (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := fun t =>
    (vfE (s := (c : ℂ) + t * I) (by simpa using hc) (by simpa using hw) hw0 hw1).2
  have hconv : MellinConvergent (vdn w) (c : ℂ) :=
    (vfE (by simpa using hc) (by simpa using hw) hw0 hw1).1
  have hvert : VerticalIntegrable (mellin (vdn w)) c := by
    unfold VerticalIntegrable
    simp_rw [hmel]
    exact vfw c hc w hw
  have hinv := mellinInv_mellin_eq (E := ℂ) c (vdn w) (x := 1 / x) (by positivity) hconv hvert
    (vgT w hw0 hw1 (by positivity))
  have hint : (∫ t : ℝ, (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)))
      = ∫ t : ℝ, (((1 / x : ℝ)) : ℂ) ^ (-((c : ℂ) + t * I)) • mellin (vdn w) ((c : ℂ) + t * I) := by
    congr 1
    funext t
    rw [hmel t, smul_eq_mul, ofReal_div, ofReal_one, one_div (x : ℂ),
      inv_cpow_ofReal_nonneg hx0.le, cpow_neg, inv_inv]
    ring
  rw [hint]
  unfold mellinInv at hinv
  rw [Complex.real_smul] at hinv
  have h2 : ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 / (2 * (Real.pi : ℂ)) := by push_cast; ring
  rw [h2] at hinv
  rw [hinv]
  have hle : 1 / x ≤ 1 := by rw [div_le_one hx0]; exact hx
  unfold vdn ver
  simp only [hle, ↓reduceIte]
  rw [ofReal_div, ofReal_one, one_div (x : ℂ), inv_cpow_ofReal_nonneg hx0.le, cpow_neg, inv_inv,
    cpow_neg_one]
end Erdos985.Analytic.PerronKernel
end
section
open Complex MeasureTheory Set Filter Topology
namespace Erdos985.Analytic.PerronAux
lemma vgP {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ((y⁻¹ : ℝ) : ℂ) ^ (-s) = (y : ℂ) ^ s := by
  rw [ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hy.le]; exact Real.pi_ne_zero.symm),
    cpow_neg, inv_inv]
theorem vhK {f : ℝ → ℂ} {F : ℂ → ℂ} {y c : ℝ} (hy : 0 < y)
    (hf : MellinConvergent f c) (hF : ∀ t : ℝ, mellin f (c + t * I) = F (c + t * I))
    (hFi : Integrable fun t : ℝ => F (c + t * I)) (hfc : ContinuousAt f y⁻¹) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + t * I) * F (c + t * I)
      = f y⁻¹ := by
  have hV : VerticalIntegrable (mellin f) c := by
    unfold VerticalIntegrable
    simp_rw [hF]; exact hFi
  have := mellinInv_mellin_eq c f (inv_pos.2 hy) hf hV hfc
  rw [← this, mellinInv]
  simp_rw [hF, vgP hy, smul_eq_mul]
  rw [Complex.real_smul]
  push_cast; ring
lemma vfi {h : ℝ → ℂ} {t : ℝ} (ht : 0 < t) (hh : ContinuousAt h t)
    (h1 : t = 1 → h 1 = 0) : ContinuousAt (indicator (Ioc 0 1) h) t := by
  rcases lt_trichotomy t 1 with h' | rfl | h'
  · refine hh.congr ?_
    filter_upwards [Ioo_mem_nhds ht h'] with u hu
    rw [indicator_of_mem (show u ∈ Ioc (0:ℝ) 1 from ⟨hu.1, hu.2.le⟩)]
  · rw [continuousAt_iff_continuous_left_right]
    constructor
    · refine (hh.continuousWithinAt).congr_of_eventuallyEq ?_ (by simp)
      filter_upwards [Ioc_mem_nhdsLE (show (0:ℝ) < 1 by norm_num)] with u hu
      rw [indicator_of_mem hu]
    · have : ContinuousWithinAt (fun _ : ℝ => (0 : ℂ)) (Ici 1) 1 := continuousWithinAt_const
      refine this.congr_of_eventuallyEq ?_ (by simp [h1 rfl])
      filter_upwards [self_mem_nhdsWithin] with u hu
      rcases eq_or_lt_of_le (show (1:ℝ) ≤ u from hu) with rfl | hu'
      · simp [h1 rfl]
      · rw [indicator_of_notMem (fun hm : u ∈ Ioc (0:ℝ) 1 => absurd hm.2 (not_le.2 hu'))]
  · refine continuousAt_const.congr (f := fun _ => (0:ℂ)) ?_
    filter_upwards [Ioi_mem_nhds h'] with u hu
    rw [indicator_of_notMem (fun hm : u ∈ Ioc (0:ℝ) 1 => absurd hm.2 (not_le.2 (show 1 < u from hu)))]
noncomputable def P (a : ℂ) : ℝ → ℂ := indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a)
lemma veh (a : ℂ) {s : ℂ} (hs : 0 < s.re + a.re) : HasMellin (P a) s (1 / (s + a)) :=
  hasMellin_cpow_Ioc a hs
lemma vhZ (α β γ a b d : ℂ) {s : ℂ} (ha : 0 < s.re + a.re) (hb : 0 < s.re + b.re)
    (hd : 0 < s.re + d.re) :
    HasMellin (indicator (Ioc 0 1) (fun t : ℝ => α * (t : ℂ) ^ a + β * (t : ℂ) ^ b +
      γ * (t : ℂ) ^ d)) s (α * (1 / (s + a)) + β * (1 / (s + b)) + γ * (1 / (s + d))) := by
  have e : indicator (Ioc 0 1) (fun t : ℝ => α * (t : ℂ) ^ a + β * (t : ℂ) ^ b +
      γ * (t : ℂ) ^ d) = fun t => (α • P a t + β • P b t) + γ • P d t := by
    funext t
    by_cases ht : t ∈ Ioc (0:ℝ) 1 <;> simp [P, ht]
  rw [e]
  have h1 := veh a ha
  have h2 := veh b hb
  have h3 := veh d hd
  have k1 := hasMellin_const_smul h1.1 α
  have k2 := hasMellin_const_smul h2.1 β
  have k3 := hasMellin_const_smul h3.1 γ
  have k12 := hasMellin_add k1.1 k2.1
  have k := hasMellin_add k12.1 k3.1
  refine ⟨k.1, ?_⟩
  rw [k.2, k12.2, k1.2, k2.2, k3.2, h1.2, h2.2, h3.2]
  simp [smul_eq_mul]
lemma viq (a : ℂ) (ha : -1 < a.re) : IntegrableOn (P a) (Ioi 0) := by
  have := (veh a (s := 1) (by simp; linarith)).1
  unfold MellinConvergent at this
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp
lemma vib (a : ℂ) {s : ℂ} (ha : -1 < a.re) (hs : 0 < s.re + a.re) :
    HasMellin (fun t : ℝ => (Real.log t : ℂ) * P a t) s (-1 / (s + a) ^ 2) := by
  have hloc : LocallyIntegrableOn (P a) (Ioi 0) := (viq a ha).locallyIntegrableOn
  have htop : P a =O[atTop] (· ^ (-(s.re + 1))) := by
    refine EventuallyEq.trans_isBigO ?_ (Asymptotics.isBigO_zero _ _)
    filter_upwards [eventually_gt_atTop 1] with t ht
    simp [P, indicator_of_notMem (fun hm : t ∈ Ioc (0:ℝ) 1 => absurd hm.2 (not_le.2 ht))]
  have hbot : P a =O[𝓝[>] 0] (· ^ (-(-a.re))) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    rw [P, indicator_of_mem (show t ∈ Ioc (0:ℝ) 1 from ⟨ht.1, ht.2.le⟩),
      norm_cpow_eq_rpow_re_of_pos ht.1, neg_neg, one_mul,
      Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)]
  obtain ⟨hconv, hder⟩ := mellin_hasDerivAt_of_isBigO_rpow hloc htop (by linarith) hbot
    (by linarith)
  have hne : s + a ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  have hev : mellin (P a) =ᶠ[𝓝 s] fun z => (z + a)⁻¹ := by
    have hopen : IsOpen {z : ℂ | 0 < z.re + a.re} :=
      isOpen_lt continuous_const (continuous_re.add continuous_const)
    filter_upwards [hopen.mem_nhds hs] with z hz
    rw [(veh a hz).2, one_div]
  have h2 : HasDerivAt (fun z => (z + a)⁻¹) (-1 / (s + a) ^ 2) s := by
    have := ((hasDerivAt_id s).add_const a).inv hne
    simp only [id] at this
    convert this using 1
    all_goals try with_reducible_and_instances rfl
  have h3 := (h2.congr_of_eventuallyEq hev).unique hder
  refine ⟨?_, ?_⟩
  · refine (hconv).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [Complex.real_smul]
  · rw [h3]; unfold mellin; congr 1
noncomputable def prof (κ a₀ α β γ a b d : ℂ) : ℝ → ℂ :=
  indicator (Ioc 0 1) (fun t : ℝ => κ * ((Real.log t : ℂ) * (t : ℂ) ^ a₀) +
    (α * (t : ℂ) ^ a + β * (t : ℂ) ^ b + γ * (t : ℂ) ^ d))
lemma vgg (κ a₀ α β γ a b d : ℂ) {s : ℂ} (ha₀ : -1 < a₀.re) (ha₀' : 0 < s.re + a₀.re)
    (ha : 0 < s.re + a.re) (hb : 0 < s.re + b.re) (hd : 0 < s.re + d.re) :
    HasMellin (prof κ a₀ α β γ a b d) s (κ * (-1 / (s + a₀) ^ 2) +
      (α * (1 / (s + a)) + β * (1 / (s + b)) + γ * (1 / (s + d)))) := by
  have e : prof κ a₀ α β γ a b d = fun t => κ • ((Real.log t : ℂ) * P a₀ t) +
      indicator (Ioc 0 1) (fun t : ℝ => α * (t : ℂ) ^ a + β * (t : ℂ) ^ b +
      γ * (t : ℂ) ^ d) t := by
    funext t
    by_cases ht : t ∈ Ioc (0:ℝ) 1 <;> simp [prof, P, ht]
  rw [e]
  have h1 := vib a₀ ha₀ ha₀'
  have k1 := hasMellin_const_smul h1.1 κ
  have h2 := vhZ α β γ a b d ha hb hd
  have k := hasMellin_add k1.1 h2.1
  refine ⟨k.1, ?_⟩
  rw [k.2, k1.2, h1.2, h2.2, smul_eq_mul]
lemma vht (κ a₀ α β γ a b d : ℂ) {t : ℝ} (ht : 0 < t)
    (h1 : t = 1 → α + β + γ = 0) : ContinuousAt (prof κ a₀ α β γ a b d) t := by
  refine vfi ht ?_ (fun h => by simp [h1 h])
  have hc : ∀ e : ℂ, ContinuousAt (fun u : ℝ => (u : ℂ) ^ e) t :=
    fun e => continuousAt_ofReal_cpow_const t e (Or.inr ht.ne')
  have hl : ContinuousAt (fun u : ℝ => (Real.log u : ℂ)) t :=
    continuous_ofReal.continuousAt.comp (Real.continuousAt_log ht.ne')
  exact (continuousAt_const.mul (hl.mul (hc a₀))).add
    (((continuousAt_const.mul (hc a)).add (continuousAt_const.mul (hc b))).add
      (continuousAt_const.mul (hc d)))
theorem vhA {y c : ℝ} (hy : 0 < y) (κ a₀ α β γ a b d : ℂ)
    (ha₀ : -1 < a₀.re) (ha₀' : 0 < c + a₀.re) (ha : 0 < c + a.re) (hb : 0 < c + b.re)
    (hd : 0 < c + d.re) (h1 : y⁻¹ = 1 → α + β + γ = 0) {F : ℂ → ℂ}
    (hF : ∀ t : ℝ, κ * (-1 / ((c : ℂ) + t * I + a₀) ^ 2) +
      (α * (1 / ((c : ℂ) + t * I + a)) + β * (1 / ((c : ℂ) + t * I + b)) +
        γ * (1 / ((c : ℂ) + t * I + d))) = F (c + t * I))
    (hFi : Integrable fun t : ℝ => F (c + t * I)) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + t * I) * F (c + t * I)
      = prof κ a₀ α β γ a b d y⁻¹ := by
  have hre : ∀ t : ℝ, ((c : ℂ) + t * I).re = c := by intro t; simp
  refine vhK hy ?_ ?_ hFi (vht _ _ _ _ _ _ _ _ (inv_pos.2 hy) h1)
  · exact (vgg κ a₀ α β γ a b d (s := (c : ℂ)) ha₀ (by simpa using ha₀')
      (by simpa using ha) (by simpa using hb) (by simpa using hd)).1
  · intro t
    rw [(vgg κ a₀ α β γ a b d (s := (c : ℂ) + t * I) ha₀ (by rw [hre]; exact ha₀')
      (by rw [hre]; exact ha) (by rw [hre]; exact hb) (by rw [hre]; exact hd)).2, hF]
end Erdos985.Analytic.PerronAux
end
section
open Complex MeasureTheory Set Filter Topology
namespace Erdos985.Analytic.PerronAux
lemma vfH (c t : ℝ) : ‖(c : ℂ) + t * I‖ ^ 2 = c ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm, normSq_add_mul_I]
lemma vfG (c t : ℝ) : (c : ℂ) + t * I + 1 = ((c + 1 : ℝ) : ℂ) + t * I := by
  push_cast; ring
lemma vgU (c t : ℝ) : |t| ≤ ‖(c : ℂ) + t * I‖ := by
  simpa using abs_im_le_norm ((c : ℂ) + t * I)
lemma vgn (c t : ℝ) (w : ℂ) : c - w.re ≤ ‖(c : ℂ) + t * I - w‖ := by
  have := re_le_norm ((c : ℂ) + t * I - w)
  simpa using this
lemma vgf (c t : ℝ) (w : ℂ) : |t - w.im| ≤ ‖(c : ℂ) + t * I - w‖ := by
  have := abs_im_le_norm ((c : ℂ) + t * I - w)
  simpa using this
lemma vis {c : ℝ} (_hc : 0 ≤ c) (t : ℝ) : c ≤ ‖(c : ℂ) + t * I‖ := by
  have := re_le_norm ((c : ℂ) + t * I)
  simpa using this
lemma vgB {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    ‖(c : ℂ) + t * I‖ ≤ ‖(c : ℂ) + t * I + 1‖ := by
  rw [vfG]
  have h1 := vfH c t
  have h2 := vfH (c + 1) t
  have := norm_nonneg ((c : ℂ) + t * I)
  have := norm_nonneg (((c + 1 : ℝ) : ℂ) + t * I)
  nlinarith
lemma vdG {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : 1 ≤ ‖(c : ℂ) + t * I + 1‖ := by
  rw [vfG]; have := vis (c := c + 1) (by linarith) t; linarith
lemma vfV (c t : ℝ) :
    min (c ^ 2) 1 * (1 + t ^ 2) ≤ ‖(c : ℂ) + t * I‖ ^ 2 := by
  rw [vfH]
  have h1 : min (c ^ 2) 1 ≤ c ^ 2 := min_le_left _ _
  have h2 : min (c ^ 2) 1 ≤ 1 := min_le_right _ _
  nlinarith [sq_nonneg t]
lemma veC {c : ℝ} (hc : 0 < c) (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
  intro h; have := congrArg re h; simp at this; linarith
lemma vbe {c : ℝ} (hc : 0 < c) (t : ℝ) : (c : ℂ) + t * I + 1 ≠ 0 := by
  intro h; have := congrArg re h; simp at this; linarith
lemma veo {c : ℝ} (t : ℝ) {w : ℂ} (hw : w.re < c) : (c : ℂ) + t * I - w ≠ 0 := by
  intro h; have := congrArg re h; simp at this; linarith
lemma vdY {c : ℝ} (hc : 0 < c) {G : ℝ → ℂ} (hG : Continuous G) {B : ℝ}
    (hB : ∀ t, ‖G t‖ ≤ B) :
    Integrable fun t : ℝ => G t / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  have hm : 0 < min (c ^ 2) 1 := lt_min (by positivity) one_pos
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine (integrable_inv_one_add_sq.const_mul (B / min (c ^ 2) 1)).mono' ?_ (ae_of_all _ ?_)
  · refine (hG.div (by fun_prop) fun t => ?_).aestronglyMeasurable
    exact mul_ne_zero (veC hc t) (vbe hc t)
  · intro t
    rw [norm_div, norm_mul]
    have hs := vfV c t
    have h1 := vgB hc.le t
    have hpos : 0 < ‖(c : ℂ) + t * I‖ := norm_pos_iff.2 (veC hc t)
    have hpos1 : 0 < ‖(c : ℂ) + t * I + 1‖ := norm_pos_iff.2 (vbe hc t)
    have key : min (c ^ 2) 1 * (1 + t ^ 2) ≤ ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I + 1‖ := by
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    calc ‖G t‖ ≤ B := hB t
      _ = B / min (c ^ 2) 1 * (1 + t ^ 2)⁻¹ * (min (c ^ 2) 1 * (1 + t ^ 2)) := by
          field_simp
      _ ≤ B / min (c ^ 2) 1 * (1 + t ^ 2)⁻¹ *
          (‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I + 1‖) := by
          gcongr
lemma vce {c : ℝ} (hc : 0 < c) {G : ℝ → ℂ} (hG : Continuous G) {B : ℝ}
    (hB : ∀ t, ‖G t‖ ≤ B) {w : ℂ} (hw : w.re < c) :
    Integrable fun t : ℝ =>
      G t / (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  have hδ : 0 < c - w.re := by linarith
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hG' : Continuous fun t : ℝ => G t / ((c : ℂ) + t * I - w) :=
    hG.div (by fun_prop) fun t => veo t hw
  have := vdY hc hG' (B := B / (c - w.re)) fun t => by
    rw [norm_div]
    exact div_le_div₀ hB0 (hB t) hδ (vgn c t w)
  refine this.congr (ae_of_all _ fun t => ?_)
  simp only
  rw [div_div, mul_assoc]
lemma veR {x : ℝ} (hx : 0 < x) (c t : ℝ) :
    ‖(x : ℂ) ^ ((c : ℂ) + t * I)‖ = x ^ c := by
  rw [norm_cpow_eq_rpow_re_of_pos hx]; simp
lemma vdi {x : ℝ} (hx : 0 < x) (c : ℝ) :
    Continuous fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) :=
  Continuous.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.2 hx.ne'))
lemma vcm {x c : ℝ} (hx : 0 < x) (hc : 0 < c) {w : ℂ} (hw : w.re < c) :
    Integrable fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) :=
  vce hc (vdi hx c) (B := x ^ c)
    (fun t => (veR hx c t).le) hw
lemma vdK {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    Integrable fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) :=
  vdY hc (vdi hx c) (B := x ^ c)
    (fun t => (veR hx c t).le)
lemma vgR {a b D θ : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 < D)
    (hab : D ≤ a + b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    1 / (a * b) ≤ (D / 2) ^ (-θ) * (a ^ (-(2 - θ)) + b ^ (-(2 - θ))) := by
  have key : ∀ a b : ℝ, 0 < a → 0 < b → a ≤ b → D ≤ a + b →
      1 / (a * b) ≤ (D / 2) ^ (-θ) * a ^ (-(2 - θ)) := by
    intro a b ha hb hle hab
    have hb2 : D / 2 ≤ b := by linarith
    have h1 : b ^ (-θ) ≤ (D / 2) ^ (-θ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hb2 (by linarith)
    have hp : (0 : ℝ) ≤ 1 - θ := by linarith
    have hap : a ^ (1 - θ) ≤ b ^ (1 - θ) := Real.rpow_le_rpow ha.le hle hp
    have hA : a ^ (-(2 - θ)) = (a * a ^ (1 - θ))⁻¹ := by
      rw [Real.rpow_neg ha.le, show 2 - θ = 1 + (1 - θ) by ring, Real.rpow_add ha, Real.rpow_one]
    have hB : b ^ (-θ) = b ^ (1 - θ) / b := by
      rw [Real.rpow_neg hb.le, show θ = 1 - (1 - θ) by ring, Real.rpow_sub hb, Real.rpow_one]
      field_simp
      rw [show 1 - (1 - (1 - θ)) = 1 - θ by ring]
    have hapos : 0 < a ^ (1 - θ) := Real.rpow_pos_of_pos ha _
    have hbpos : 0 < b ^ (1 - θ) := Real.rpow_pos_of_pos hb _
    calc 1 / (a * b) ≤ b ^ (-θ) * a ^ (-(2 - θ)) := by
          rw [hA, hB, div_le_iff₀ (by positivity)]
          field_simp
          exact hap
      _ ≤ (D / 2) ^ (-θ) * a ^ (-(2 - θ)) := by
          gcongr
  have hA0 : 0 ≤ a ^ (-(2 - θ)) := Real.rpow_nonneg ha.le _
  have hB0 : 0 ≤ b ^ (-(2 - θ)) := Real.rpow_nonneg hb.le _
  have hD0 : 0 ≤ (D / 2) ^ (-θ) := Real.rpow_nonneg (by positivity) _
  rcases le_total a b with h | h
  · calc 1 / (a * b) ≤ (D / 2) ^ (-θ) * a ^ (-(2 - θ)) := key a b ha hb h hab
      _ ≤ _ := by gcongr; linarith
  · calc 1 / (a * b) = 1 / (b * a) := by rw [mul_comm]
      _ ≤ (D / 2) ^ (-θ) * b ^ (-(2 - θ)) := key b a hb ha h (by linarith)
      _ ≤ _ := by gcongr; linarith
lemma viP {c δ : ℝ} (t : ℝ) {w : ℂ} (hw : w.re ≤ c - δ) :
    min δ 1 / 2 * (1 + |t - w.im|) ≤ ‖(c : ℂ) + t * I - w‖ := by
  have h1 := vgn c t w
  have h2 := vgf c t w
  have h3 : min δ 1 ≤ δ := min_le_left _ _
  have h4 : min δ 1 ≤ 1 := min_le_right _ _
  have h5 := abs_nonneg (t - w.im)
  nlinarith
lemma vhO {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    1 / 2 * (1 + |t|) ≤ ‖(c : ℂ) + t * I + 1‖ := by
  have h1 := vdG hc t
  have h2 : |t| ≤ ‖(c : ℂ) + t * I + 1‖ := by
    rw [vfG]; exact vgU _ t
  linarith
lemma vbj {r : ℝ} (hr : 1 < r) (v : ℝ) :
    Integrable fun t : ℝ => (1 + |t - v|) ^ (-r) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := r) (by simpa using hr)
  simpa [Real.norm_eq_abs] using h.comp_sub_right v
lemma vdz (r v : ℝ) :
    ∫ t : ℝ, (1 + |t - v|) ^ (-r) = ∫ t : ℝ, (1 + |t|) ^ (-r) :=
  integral_sub_right_eq_self (fun t : ℝ => (1 + |t|) ^ (-r)) v
theorem veZ {δ θ : ℝ} (hδ : 0 < δ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x c : ℝ, 0 < x → 0 < c → ∀ w : ℂ, w.re ≤ c - δ →
      Integrable (fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))) ∧
      ∫ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))‖
        ≤ K * x ^ c * (1 + ‖w‖) ^ (-θ) := by
  set r : ℝ := 2 - θ with hr_def
  have hr : 1 < r := by rw [hr_def]; linarith
  set m : ℝ := min δ 1 / 2 with hm_def
  have hm : 0 < m := by rw [hm_def]; exact half_pos (lt_min hδ one_pos)
  set J : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-r) with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun t => Real.rpow_nonneg (by positivity) _
  set A : ℝ := m ^ (-r) + (1 / 2 : ℝ) ^ (-r) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨(6⁻¹ : ℝ) ^ (-θ) * A * J, by positivity, ?_⟩
  intro x c hx hc w hw
  have hwc : w.re < c := by linarith
  set D : ℝ := max 1 ‖w + 1‖ with hD_def
  have hD : 0 < D := lt_of_lt_of_le one_pos (le_max_left _ _)
  set C : ℝ := x ^ c * (D / 2) ^ (-θ) with hC
  have hC0 : 0 ≤ C := by positivity
  set h : ℝ → ℝ := fun t => C * (m ^ (-r) * (1 + |t - w.im|) ^ (-r) +
    (1 / 2 : ℝ) ^ (-r) * (1 + |t - 0|) ^ (-r)) with hh
  have hint : Integrable h :=
    (((vbj hr w.im).const_mul _).add
      ((vbj hr 0).const_mul _)).const_mul _
  have hpt : ∀ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
      (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))‖ ≤ h t := by
    intro t
    set a := ‖(c : ℂ) + t * I - w‖
    set b := ‖(c : ℂ) + t * I + 1‖
    have ha : 0 < a := norm_pos_iff.2 (veo t hwc)
    have hb : 0 < b := norm_pos_iff.2 (vbe hc t)
    have hDab : D ≤ a + b := by
      refine max_le (by have := vdG hc.le t; linarith) ?_
      have : w + 1 = ((c : ℂ) + t * I + 1) - ((c : ℂ) + t * I - w) := by ring
      rw [this]
      exact (norm_sub_le _ _).trans (by linarith)
    have hab := vgR ha hb hD hDab hθ0 hθ1.le
    have hal : a ^ (-r) ≤ m ^ (-r) * (1 + |t - w.im|) ^ (-r) := by
      rw [← Real.mul_rpow hm.le (by positivity)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (viP t hw) (by linarith)
    have hbl : b ^ (-r) ≤ (1 / 2 : ℝ) ^ (-r) * (1 + |t - 0|) ^ (-r) := by
      rw [← Real.mul_rpow (by norm_num) (by positivity), sub_zero]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (vhO hc.le t) (by linarith)
    rw [norm_div, veR hx, norm_mul, div_eq_mul_one_div]
    simp only [hh, hC]
    rw [mul_assoc]
    gcongr
    refine hab.trans ?_
    rw [hr_def] at hal hbl
    gcongr
  refine ⟨?_, ?_⟩
  · refine hint.mono' ?_ (ae_of_all _ hpt)
    exact ((vdi hx c).div (by fun_prop) fun t =>
      mul_ne_zero (veo t hwc) (vbe hc t)).aestronglyMeasurable
  · calc _ ≤ ∫ t, h t := integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _) hint
          (ae_of_all _ hpt)
      _ = C * A * J := by
          simp only [hh]
          rw [integral_const_mul, integral_add ((vbj hr w.im).const_mul _)
            ((vbj hr 0).const_mul _), integral_const_mul,
            integral_const_mul, vdz, vdz]
          rw [hA]; ring
      _ ≤ _ := by
          rw [hC]
          have hw1 : (1 + ‖w‖) / 6 ≤ D / 2 := by
            have : ‖w‖ ≤ ‖w + 1‖ + 1 := by
              have := norm_sub_le (w + 1) 1; simpa using this
            have h1 : ‖w + 1‖ ≤ D := le_max_right _ _
            have h2 : (1 : ℝ) ≤ D := le_max_left _ _
            linarith
          have hθ' : (D / 2) ^ (-θ) ≤ (6⁻¹ : ℝ) ^ (-θ) * (1 + ‖w‖) ^ (-θ) := by
            rw [← Real.mul_rpow (by norm_num) (by positivity)]
            exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
          calc x ^ c * (D / 2) ^ (-θ) * A * J
              ≤ x ^ c * ((6⁻¹ : ℝ) ^ (-θ) * (1 + ‖w‖) ^ (-θ)) * A * J := by gcongr
            _ = _ := by ring
end Erdos985.Analytic.PerronAux
end
section
open Complex MeasureTheory Set
namespace Erdos985.Analytic
open PerronAux
theorem viI (y c : ℝ) (hy : 0 < y) (hc : 0 < c) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = (max 0 (1 - 1 / y) : ℝ) :=
  PerronKernel.vfl y c hy hc
theorem veO (x c : ℝ) (hx : 1 ≤ x) (hc : 0 < c) (w : ℂ) (hw : w.re < c)
    (hw0 : w ≠ 0) (hw1 : w ≠ -1) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = (x : ℂ) ^ w / (w * (w + 1)) - 1 / w + (x : ℂ) ^ (-1 : ℂ) / (1 + w) :=
  PerronKernel.vgY x c hx hc w hw hw0 hw1
theorem veJ (x c : ℝ) (hx : 1 ≤ x) (hc : 0 < c) (w : ℂ) (hw : w = 0) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = (Real.log x : ℂ) - 1 + (x : ℂ) ^ (-1 : ℂ) := by
  subst hw
  have hx0 : 0 < x := by linarith
  have key := vhA (c := c) hx0 (-1) 0 (-1) 0 1 0 0 1
    (by simp) (by simpa using hc) (by simpa using hc)
    (by simpa using hc) (by simpa using (show 0 < c + 1 by linarith))
    (fun _ => by ring) (F := fun s => 1 / ((s - 0) * s * (s + 1)))
    (fun t => by
      have h0 := veC hc t
      have h1 := vbe hc t
      simp only [add_zero, sub_zero]
      field_simp
      ring)
    (vce hc (G := fun _ => (1 : ℂ)) continuous_const (B := 1)
      (fun _ => by simp) (w := 0) (by simpa using hc))
  simp only [mul_one_div] at key
  rw [key, prof, indicator_of_mem (show x⁻¹ ∈ Ioc (0 : ℝ) 1 from
    ⟨inv_pos.2 hx0, inv_le_one_of_one_le₀ hx⟩), cpow_neg_one, Real.log_inv]
  push_cast
  simp only [cpow_one, cpow_zero]
  ring
theorem vga (x c : ℝ) (hx : 1 ≤ x) (hc : 0 < c) (w : ℂ) (hw : w = -1) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = 1 - (x : ℂ) ^ (-1 : ℂ) - (x : ℂ) ^ (-1 : ℂ) * (Real.log x : ℂ) := by
  subst hw
  have hx0 : 0 < x := by linarith
  have key := vhA (c := c) hx0 1 1 1 (-1) 0 0 1 0
    (by simp) (by simpa using (show 0 < c + 1 by linarith)) (by simpa using hc)
    (by simpa using (show 0 < c + 1 by linarith)) (by simpa using hc)
    (fun _ => by ring) (F := fun s => 1 / ((s - -1) * s * (s + 1)))
    (fun t => by
      have h0 := veC hc t
      have h1 := vbe hc t
      simp only [add_zero, sub_neg_eq_add]
      field_simp
      ring)
    (vce hc (G := fun _ => (1 : ℂ)) continuous_const (B := 1)
      (fun _ => by simp) (w := -1) (by simp; linarith))
  simp only [mul_one_div] at key
  rw [key, prof, indicator_of_mem (show x⁻¹ ∈ Ioc (0 : ℝ) 1 from
    ⟨inv_pos.2 hx0, inv_le_one_of_one_le₀ hx⟩), cpow_neg_one, Real.log_inv]
  push_cast
  simp only [cpow_one, cpow_zero]
  ring
theorem vdy (x c : ℝ) (hx : 0 < x) (hc : 0 < c) (w : ℂ) (hw : w.re < c) :
    Integrable fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) :=
  vcm hx hc hw
theorem vcQ {δ θ : ℝ} (hδ : 0 < δ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x c : ℝ, 0 < x → 0 < c → ∀ w : ℂ, w.re ≤ c - δ →
      Integrable (fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))) ∧
      ∫ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))‖
        ≤ K * x ^ c * (1 + ‖w‖) ^ (-θ) :=
  veZ hδ hθ0 hθ1
end Erdos985.Analytic
end
section
open Real Filter Topology
namespace Erdos985.Analytic.DigammaAux
lemma vhc {a : ℝ} (ha : 0 < a) :
    log (1 + a⁻¹) ≤ 1 / (2 * a) + 1 / (2 * (a + 1)) := by
  set y : ℝ := 1 / (2 * a + 1) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
  have hy2 : y ^ 2 < 1 := by nlinarith
  have hg : HasSum (fun k : ℕ => 2 * y * (y ^ 2) ^ k) (2 * y * (1 - y ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hy2).mul_left (2 * y)
  have hle := hasSum_le (fun k : ℕ => ?_) (hasSum_log_one_add_inv ha) hg
  · refine hle.trans (le_of_eq ?_)
    have h2a : (2 * a + 1) ≠ 0 := by positivity
    have e1 : 1 - y ^ 2 = 4 * a * (a + 1) / (2 * a + 1) ^ 2 := by
      rw [hy]; field_simp; ring
    rw [e1, hy]
    field_simp
    ring
  · rw [← hy, pow_succ, ← pow_mul]
    have h1 : (1 : ℝ) / (2 * k + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [k.cast_nonneg (α := ℝ)]
    have h2 : 0 ≤ y ^ (2 * k) * y := by positivity
    nlinarith
end Erdos985.Analytic.DigammaAux
end
section
namespace Erdos985.Analytic
open Complex
end Erdos985.Analytic
end
section
open Real ArithmeticFunction
namespace Erdos985.Analytic.ConstantsAux
lemma vco (m : ℝ) (hm : 0 < m) :
    Real.log (m + 1) ≤ Real.log m + (1 / (2 * m) + 1 / (2 * (m + 1))) := by
  have h := Erdos985.Analytic.DigammaAux.vhc hm
  have e : Real.log (m + 1) = Real.log m + Real.log (1 + m⁻¹) := by
    rw [← Real.log_mul hm.ne' (by positivity)]
    congr 1
    field_simp
  linarith
lemma viH :
    Real.log 2 ≤ 0.6931471808 ∧ Real.log 3 ≤ 1.098749 ∧ Real.log 5 ≤ 1.609512 ∧
    Real.log 7 ≤ 1.945980 ∧ Real.log 11 ≤ 2.398001 ∧ Real.log 13 ≤ 2.565052 ∧
    Real.log 17 ≤ 2.833350 ∧ Real.log 19 ≤ 2.944613 := by
  have p2 := Real.log_two_lt_d9.le
  have p3 : 2 * Real.log 3 ≤ 3 * Real.log 2 + (1 / (2 * 8) + 1 / (2 * (8 + 1))) := by
    have h := vco 8 (by norm_num)
    have e1 : Real.log (8 + 1) = 2 * Real.log 3 := by
      rw [show (8 : ℝ) + 1 = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
    have e2 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2^3 by norm_num]; simp [Real.log_mul, Real.log_pow]
    rw [e1, e2] at h; exact h
  have p5 : 2 * Real.log 5 ≤ 3 * Real.log 2 + Real.log 3 + (1 / (2 * 24) + 1 / (2 * (24 + 1))) := by
    have h := vco 24 (by norm_num)
    have e1 : Real.log (24 + 1) = 2 * Real.log 5 := by
      rw [show (24 : ℝ) + 1 = 5 ^ 2 by norm_num, Real.log_pow]; norm_num
    have e2 : Real.log 24 = 3 * Real.log 2 + Real.log 3 := by
      rw [show (24 : ℝ) = 2^3 * 3 by norm_num]; simp [Real.log_mul, Real.log_pow]
    rw [e1, e2] at h; exact h
  have p7 : 2 * Real.log 7 ≤ 4 * Real.log 2 + Real.log 3 + (1 / (2 * 48) + 1 / (2 * (48 + 1))) := by
    have h := vco 48 (by norm_num)
    have e1 : Real.log (48 + 1) = 2 * Real.log 7 := by
      rw [show (48 : ℝ) + 1 = 7 ^ 2 by norm_num, Real.log_pow]; norm_num
    have e2 : Real.log 48 = 4 * Real.log 2 + Real.log 3 := by
      rw [show (48 : ℝ) = 2^4 * 3 by norm_num]; simp [Real.log_mul, Real.log_pow]
    rw [e1, e2] at h; exact h
  have p11 : 2 * Real.log 11 ≤ 3 * Real.log 2 + Real.log 3 + Real.log 5 + (1 / (2 * 120) + 1 / (2 * (120 + 1))) := by
    have h := vco 120 (by norm_num)
    have e1 : Real.log (120 + 1) = 2 * Real.log 11 := by
      rw [show (120 : ℝ) + 1 = 11 ^ 2 by norm_num, Real.log_pow]; norm_num
    have e2 : Real.log 120 = 3 * Real.log 2 + Real.log 3 + Real.log 5 := by
      rw [show (120 : ℝ) = 2^3 * 3 * 5 by norm_num]; simp [Real.log_mul, Real.log_pow]
    rw [e1, e2] at h; exact h
  have p13 : 2 * Real.log 13 ≤ 3 * Real.log 2 + Real.log 3 + Real.log 7 + (1 / (2 * 168) + 1 / (2 * (168 + 1))) := by
    have h := vco 168 (by norm_num)
    have e1 : Real.log (168 + 1) = 2 * Real.log 13 := by
      rw [show (168 : ℝ) + 1 = 13 ^ 2 by norm_num, Real.log_pow]; norm_num
    have e2 : Real.log 168 = 3 * Real.log 2 + Real.log 3 + Real.log 7 := by
      rw [show (168 : ℝ) = 2^3 * 3 * 7 by norm_num]; simp [Real.log_mul, Real.log_pow]
    rw [e1, e2] at h; exact h
  have p17 : 2 * Real.log 17 ≤ 5 * Real.log 2 + 2 * Real.log 3 + (1 / (2 * 288) + 1 / (2 * (288 + 1))) := by
    have h := vco 288 (by norm_num)
    have e1 : Real.log (288 + 1) = 2 * Real.log 17 := by
      rw [show (288 : ℝ) + 1 = 17 ^ 2 by norm_num, Real.log_pow]; norm_num
    have e2 : Real.log 288 = 5 * Real.log 2 + 2 * Real.log 3 := by
      rw [show (288 : ℝ) = 2^5 * 3^2 by norm_num]; simp [Real.log_mul, Real.log_pow]
    rw [e1, e2] at h; exact h
  have p19 : 2 * Real.log 19 ≤ 3 * Real.log 2 + 2 * Real.log 3 + Real.log 5 + (1 / (2 * 360) + 1 / (2 * (360 + 1))) := by
    have h := vco 360 (by norm_num)
    have e1 : Real.log (360 + 1) = 2 * Real.log 19 := by
      rw [show (360 : ℝ) + 1 = 19 ^ 2 by norm_num, Real.log_pow]; norm_num
    have e2 : Real.log 360 = 3 * Real.log 2 + 2 * Real.log 3 + Real.log 5 := by
      rw [show (360 : ℝ) = 2^3 * 3^2 * 5 by norm_num]; simp [Real.log_mul, Real.log_pow]
    rw [e1, e2] at h; exact h
  norm_num at *
  refine ⟨p2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
end Erdos985.Analytic.ConstantsAux
end
section
open Complex ArithmeticFunction
namespace Erdos985.Analytic
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic
open Complex ArithmeticFunction MeasureTheory
open scoped Classical
variable {N : ℕ} [NeZero N]
noncomputable def vbK (χ : DirichletCharacter ℂ N) : ℕ := if χ.Even then 0 else 1
noncomputable def vaR (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + vbK χ) / 2)
noncomputable def vbi (χ : DirichletCharacter ℂ N) (x : ℕ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
    (vaR χ (2 + t * I) - vaR χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I)
      / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))
noncomputable def vcY (x : ℕ) (ρ : ℂ) : ℂ :=
  (1 - 1 / (x : ℂ)) / (2 - ρ)
    - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic.StepAAux
open Complex
theorem vfz {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt Gamma (Gamma w * digamma w) w := by
  have hd : DifferentiableAt ℂ Gamma w := differentiableAt_Gamma w fun m h => by
    rw [h] at hw; simp at hw; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  convert hd.hasDerivAt using 1
  all_goals try with_reducible_and_instances rfl
  rw [digamma_def, logDeriv_apply, mul_div_cancel₀ _ (Gamma_ne_zero_of_re_pos hw)]
theorem hasDerivAt_Gammaℝ {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt Gammaℝ (Gammaℝ w * (-(1 / 2) * (Real.log Real.pi : ℂ)
      + (1 / 2) * digamma (w / 2))) w := by
  have h1 : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2) w := by
    simpa using ((hasDerivAt_id w).neg.div_const 2)
  have h2 := h1.const_cpow (c := (Real.pi : ℂ)) (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  have h3 : HasDerivAt (fun z : ℂ => z / 2) (1 / 2) w := by
    simpa using (hasDerivAt_id w).div_const 2
  have hw2 : 0 < (w / 2).re := by simp; linarith
  have h4 := (vfz hw2).comp w h3
  have h5 := h2.mul h4
  have hlog : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) :=
    (ofReal_log Real.pi_pos.le).symm
  convert h5 using 1
  all_goals try with_reducible_and_instances rfl
  · rfl
  · rw [hlog, Gammaℝ_def]; simp only [Function.comp_apply]; ring
variable {N : ℕ}
end Erdos985.Analytic.StepAAux
end
section
namespace Erdos985.Analytic
open Complex ArithmeticFunction MeasureTheory
open scoped Classical
variable {N : ℕ} [NeZero N]
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic.XiOrderAux
open Real
def vaq (F : ℂ → ℂ) : Prop :=
  ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * exp (a * ((‖s‖ + b) * log (‖s‖ + b)))
lemma vcD {u : ℝ} (hu : 3 ≤ u) : 1 ≤ log u := by
  have h3 : exp 1 < 3 := lt_of_lt_of_le exp_one_lt_d9 (by norm_num)
  rw [le_log_iff_exp_le (by linarith)]
  linarith
lemma vhN {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) : u * log u ≤ v * log v :=
  mul_le_mul huv (log_le_log (by linarith) huv) (log_nonneg hu) (by linarith)
lemma viu {a a' b b' y y' : ℝ} (ha : 0 ≤ a) (haa : a ≤ a') (hb : 3 ≤ b) (hy : 0 ≤ y)
    (hle : y + b ≤ y' + b') :
    a * ((y + b) * log (y + b)) ≤ a' * ((y' + b') * log (y' + b')) := by
  have h1 : 1 ≤ log (y + b) := vcD (by linarith)
  have h2 : (y + b) * log (y + b) ≤ (y' + b') * log (y' + b') :=
    vhN (by linarith) hle
  have h3 : 0 ≤ (y' + b') * log (y' + b') := by nlinarith
  exact mul_le_mul haa h2 (by nlinarith) (ha.trans haa)
lemma vaq.vgA {F : ℂ → ℂ} {K a b : ℝ}
    (h : ∀ s, ‖F s‖ ≤ K * exp (a * ((‖s‖ + b) * log (‖s‖ + b)))) : 0 ≤ K :=
  nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (h 0)) (exp_pos _)
lemma vaq.mono {F : ℂ → ℂ} {K a b : ℝ} (ha : 0 ≤ a) (hb : 3 ≤ b)
    (h : ∀ s, ‖F s‖ ≤ K * exp (a * ((‖s‖ + b) * log (‖s‖ + b)))) {a' b' : ℝ} (haa : a ≤ a')
    (hbb : b ≤ b') : ∀ s, ‖F s‖ ≤ K * exp (a' * ((‖s‖ + b') * log (‖s‖ + b'))) := by
  intro s
  refine (h s).trans (mul_le_mul_of_nonneg_left ?_ (vaq.vgA h))
  exact exp_le_exp.2 (viu ha haa hb (norm_nonneg _) (by linarith))
lemma vaq.congr {F G : ℂ → ℂ} (hF : vaq F) (h : ∀ s, F s = G s) : vaq G := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  exact ⟨K, a, b, ha, hb, fun s => h s ▸ hK s⟩
lemma vaq.const (c : ℂ) : vaq (fun _ => c) :=
  ⟨‖c‖, 0, 3, le_rfl, le_rfl, fun s => by simp⟩
lemma vaq.add {F G : ℂ → ℂ} (hF : vaq F) (hG : vaq G) :
    vaq (fun s => F s + G s) := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  obtain ⟨K', a', b', ha', hb', hK'⟩ := hG
  refine ⟨K + K', max a a', max b b', le_max_of_le_left ha, le_max_of_le_left hb, fun s => ?_⟩
  have h1 := vaq.mono ha hb hK (le_max_left a a') (le_max_left b b') s
  have h2 := vaq.mono ha' hb' hK' (le_max_right a a') (le_max_right b b') s
  calc ‖F s + G s‖ ≤ ‖F s‖ + ‖G s‖ := norm_add_le _ _
    _ ≤ _ := by rw [add_mul]; exact add_le_add h1 h2
lemma vaq.mul {F G : ℂ → ℂ} (hF : vaq F) (hG : vaq G) :
    vaq (fun s => F s * G s) := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  obtain ⟨K', a', b', ha', hb', hK'⟩ := hG
  refine ⟨K * K', a + a', max b b', add_nonneg ha ha', le_max_of_le_left hb, fun s => ?_⟩
  have h1 := vaq.mono ha hb hK le_rfl (le_max_left b b') s
  have h2 := vaq.mono ha' hb' hK' le_rfl (le_max_right b b') s
  rw [norm_mul]
  calc ‖F s‖ * ‖G s‖ ≤ _ := mul_le_mul h1 h2 (norm_nonneg _)
        (mul_nonneg (vaq.vgA hK) (exp_pos _).le)
    _ = _ := by rw [add_mul a a', exp_add]; ring
lemma vaq.comp {F : ℂ → ℂ} (hF : vaq F) {g : ℂ → ℂ} {d : ℝ} (hd : 0 ≤ d)
    (hg : ∀ s, ‖g s‖ ≤ ‖s‖ + d) : vaq (fun s => F (g s)) := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  refine ⟨K, a, b + d, ha, by linarith, fun s => (hK (g s)).trans ?_⟩
  refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (vaq.vgA hK)
  exact viu ha le_rfl hb (norm_nonneg _) (by linarith [hg s])
end Erdos985.Analytic.XiOrderAux
end
section
namespace Erdos985.Analytic.XiOrderAux
open Real Set MeasureTheory
open scoped Nat
lemma vdL {y : ℝ} (hy : 0 < y) (m : ℕ) : exp (-y) ≤ m ! * y⁻¹ ^ m := by
  have h := pow_div_factorial_le_exp (x := y) (hx := hy.le) (n := m)
  have hpos : 0 < y ^ m / m ! := by positivity
  rw [exp_neg]
  calc (exp y)⁻¹ ≤ (y ^ m / m !)⁻¹ := inv_anti₀ hpos h
    _ = m ! * y⁻¹ ^ m := by rw [inv_div, inv_pow, div_eq_mul_inv]
noncomputable def vei : ℝ → ℝ :=
  (Ioc 0 1).indicator (fun _ => (1 : ℝ)) + (Ioi 1).indicator (fun t => t ^ (-2 : ℝ))
lemma vgO : IntegrableOn vei (Ioi 0) := by
  have h1 : Integrable ((Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Ioc
  have h2 : Integrable ((Ioi (1 : ℝ)).indicator (fun t : ℝ => t ^ (-2 : ℝ))) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).integrable_indicator measurableSet_Ioi
  exact (h1.add h2).integrableOn
lemma via (P : WeakFEPair ℂ) {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hf : ∀ t : ℝ, 1 < t → ‖P.f t - P.f₀‖ ≤ C * exp (-p * t))
    (hg : ∀ t : ℝ, 1 < t → ‖P.g t - P.g₀‖ ≤ C * exp (-p * t))
    (s : ℂ) (m : ℕ) (hm : ‖s‖ + P.k + 1 ≤ m) (t : ℝ) (ht : 0 < t) :
    ‖(t : ℂ) ^ (s - 1) • P.f_modif t‖ ≤ (C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m) * vei t := by
  have hsre : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
  have hk := P.hk
  have hA : 0 ≤ C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m := by positivity
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
  rcases lt_trichotomy t 1 with h1 | rfl | h1
  ·
    have hdom : vei t = 1 := by
      simp [vei, indicator, ht, h1.le, not_lt.2 h1.le]
    rw [hdom, mul_one]
    have hfm : P.f_modif t = (P.ε * ((1 / t) ^ P.k : ℝ)) • (P.g (1 / t) - P.g₀) := by
      have hfe := P.h_feq (1 / t) (by simpa using ht)
      rw [one_div_one_div] at hfe
      simp only [WeakFEPair.f_modif, Pi.add_apply, indicator, mem_Ioi, mem_Ioo, ht, h1,
        and_self, ite_true, not_lt.2 h1.le, ite_false, zero_add, hfe, smul_sub]
      congr 2
      rw [one_div, inv_rpow ht.le, rpow_neg ht.le]
    have h1t : 1 < 1 / t := by rw [lt_one_div one_pos ht, div_one]; exact h1
    rw [hfm, norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    have hgb := hg (1 / t) h1t
    have he := vdL (show 0 < p * (1 / t) by positivity) m
    rw [neg_mul] at hgb
    have hcalc : t ^ (s.re - 1) * (1 / t) ^ P.k * ((1 / t) ⁻¹ ^ m) ≤ 1 := by
      rw [one_div, inv_inv, inv_rpow ht.le, ← rpow_neg ht.le, ← rpow_natCast,
        ← rpow_add ht, ← rpow_add ht]
      apply rpow_le_one ht.le h1.le
      have := neg_abs_le s.re
      linarith
    calc t ^ (s.re - 1) * (‖P.ε‖ * (1 / t) ^ P.k * ‖P.g (1 / t) - P.g₀‖)
        ≤ t ^ (s.re - 1) * (‖P.ε‖ * (1 / t) ^ P.k * (C * (m ! * (p * (1 / t))⁻¹ ^ m))) := by
          gcongr
          exact hgb.trans (mul_le_mul_of_nonneg_left he hC)
      _ = C * ‖P.ε‖ * m ! * p⁻¹ ^ m * (t ^ (s.re - 1) * (1 / t) ^ P.k * ((1 / t) ⁻¹ ^ m)) := by
          rw [mul_inv, mul_pow]; ring
      _ ≤ C * ‖P.ε‖ * m ! * p⁻¹ ^ m * 1 := by gcongr
      _ ≤ C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m := by
          rw [mul_one]; gcongr; exact le_max_right _ _
  · have h0 : P.f_modif 1 = 0 := by simp [WeakFEPair.f_modif]
    rw [h0, norm_zero, mul_zero]
    exact mul_nonneg hA (by simp [vei])
  ·
    have hdom : vei t = t ^ (-2 : ℝ) := by
      simp [vei, indicator, h1, not_le.2 h1]
    rw [hdom]
    have hfm : P.f_modif t = P.f t - P.f₀ := by
      simp [WeakFEPair.f_modif, indicator, h1, not_lt.2 h1.le]
    rw [hfm]
    have he := vdL (show 0 < p * t by positivity) m
    have hfb := hf t h1
    rw [neg_mul] at hfb
    have ht0 : 0 < t := ht
    have hcalc : t ^ (s.re - 1) * t⁻¹ ^ m ≤ t ^ (-2 : ℝ) := by
      rw [inv_pow, ← rpow_natCast, ← rpow_neg ht.le, ← rpow_add ht]
      apply rpow_le_rpow_of_exponent_le h1.le
      have := le_abs_self s.re
      linarith
    calc t ^ (s.re - 1) * ‖P.f t - P.f₀‖
        ≤ t ^ (s.re - 1) * (C * (m ! * (p * t)⁻¹ ^ m)) := by
          gcongr
          exact hfb.trans (mul_le_mul_of_nonneg_left he hC)
      _ = C * 1 * m ! * p⁻¹ ^ m * (t ^ (s.re - 1) * t⁻¹ ^ m) := by
          rw [mul_inv, mul_pow]; ring
      _ ≤ C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m * t ^ (-2 : ℝ) := by
          gcongr
          exact le_max_left _ _
lemma viS (P : WeakFEPair ℂ) {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hf : ∀ t : ℝ, 1 < t → ‖P.f t - P.f₀‖ ≤ C * exp (-p * t))
    (hg : ∀ t : ℝ, 1 < t → ‖P.g t - P.g₀‖ ≤ C * exp (-p * t))
    (s : ℂ) (m : ℕ) (hm : ‖s‖ + P.k + 1 ≤ m) :
    ‖P.Λ₀ s‖ ≤ (C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m) * ∫ t in Ioi 0, vei t := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (vgO.const_mul _) ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioi
    (fun t ht => via P hp hC hf hg s m hm t ht)
theorem vhW (P : WeakFEPair ℂ) {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hf : ∀ t : ℝ, 1 < t → ‖P.f t - P.f₀‖ ≤ C * exp (-p * t))
    (hg : ∀ t : ℝ, 1 < t → ‖P.g t - P.g₀‖ ≤ C * exp (-p * t)) : vaq P.Λ₀ := by
  set I0 := ∫ t in Ioi 0, vei t
  set Q := max 1 p⁻¹
  have hQ : 1 ≤ Q := le_max_left _ _
  have hk := P.hk
  set b := P.k + 5
  refine ⟨C * max 1 ‖P.ε‖ * I0, 1 + log Q, b, by linarith [log_nonneg hQ], by linarith,
    fun s => ?_⟩
  set m := ⌈‖s‖ + P.k + 1⌉₊
  have hm : ‖s‖ + P.k + 1 ≤ m := Nat.le_ceil _
  have hm' : (m : ℝ) ≤ ‖s‖ + b := by
    have := Nat.ceil_lt_add_one (show 0 ≤ ‖s‖ + P.k + 1 by positivity)
    linarith
  have hm1 : (1 : ℝ) ≤ m := by linarith [norm_nonneg s]
  have hI0 : 0 ≤ I0 := setIntegral_nonneg measurableSet_Ioi (fun t _ => by
    simp only [vei, Pi.add_apply]
    exact add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
      (indicator_nonneg (fun t ht => rpow_nonneg (le_of_lt (lt_trans zero_lt_one ht)) _) _))
  refine (viS P hp hC hf hg s m hm).trans ?_
  have hfac : (m ! : ℝ) * p⁻¹ ^ m ≤ exp ((1 + log Q) * ((‖s‖ + b) * log (‖s‖ + b))) := by
    have h1 : (m ! : ℝ) * p⁻¹ ^ m ≤ ((m : ℝ) * Q) ^ m := by
      rw [mul_pow]
      gcongr
      · exact_mod_cast Nat.factorial_le_pow m
      · exact le_max_right _ _
    have h2 : ((m : ℝ) * Q) ^ m = exp (m * log (m * Q)) := by
      rw [← log_pow, exp_log (by positivity)]
    have hL : 1 ≤ log (‖s‖ + b) := vcD (by linarith [norm_nonneg s])
    have hlogQ : 0 ≤ log Q := log_nonneg hQ
    have h3 : (m : ℝ) * log (m * Q) ≤ (1 + log Q) * ((‖s‖ + b) * log (‖s‖ + b)) := by
      rw [log_mul (by positivity) (by positivity)]
      have e1 : (m : ℝ) * log m ≤ (‖s‖ + b) * log (‖s‖ + b) := vhN hm1 hm'
      have e2 : (m : ℝ) * log Q ≤ (‖s‖ + b) * log (‖s‖ + b) * log Q := by
        have : (m : ℝ) ≤ (‖s‖ + b) * log (‖s‖ + b) := by nlinarith
        exact mul_le_mul_of_nonneg_right this hlogQ
      nlinarith
    rw [h2] at h1
    exact h1.trans (exp_le_exp.2 h3)
  have hE : 0 ≤ C * max 1 ‖P.ε‖ := by positivity
  calc C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m * I0 = C * max 1 ‖P.ε‖ * I0 * (m ! * p⁻¹ ^ m) := by ring
    _ ≤ _ := by gcongr
end Erdos985.Analytic.XiOrderAux
end
section
namespace Erdos985.Analytic.XiOrderAux
open Real Set Filter Asymptotics HurwitzZeta
lemma veK {F : ℝ → ℝ} (hc : ContinuousOn F (Ioi 0)) {p : ℝ} (hp : 0 ≤ p)
    (h : F =O[atTop] fun x => exp (-p * x)) :
    ∃ C, 0 ≤ C ∧ ∀ t, 1 < t → |F t| ≤ C * exp (-p * t) := by
  obtain ⟨c, hc'⟩ := h.bound
  obtain ⟨T, hT⟩ := eventually_atTop.1 hc'
  set T' := max T 1
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := T')).exists_bound_of_continuousOn
    (hc.mono (fun x hx => lt_of_lt_of_le zero_lt_one hx.1))
  refine ⟨max (max c 0) (max M 0 * exp (p * T')), by positivity, fun t ht => ?_⟩
  rcases le_total T' t with h1 | h1
  · have := hT t ((le_max_left _ _).trans h1)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _)] at this
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (exp_pos _).le)
    exact (le_max_left _ _).trans (le_max_left _ _)
  · have h2 := hM t ⟨ht.le, h1⟩
    rw [Real.norm_eq_abs] at h2
    calc |F t| ≤ max M 0 := h2.trans (le_max_left _ _)
      _ ≤ max M 0 * (exp (p * T') * exp (-p * t)) := by
          refine le_mul_of_one_le_right (le_max_right _ _) ?_
          rw [← exp_add, one_le_exp_iff]
          nlinarith
      _ = (max M 0 * exp (p * T')) * exp (-p * t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (exp_pos _).le
lemma vir {f g : ℝ → ℝ} {p₁ p₂ C₁ C₂ : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂)
    (hf : ∀ t, 1 < t → f t ≤ C₁ * exp (-p₁ * t)) (hg : ∀ t, 1 < t → g t ≤ C₂ * exp (-p₂ * t)) :
    ∃ p C, 0 < p ∧ 0 ≤ C ∧ (∀ t, 1 < t → f t ≤ C * exp (-p * t)) ∧
      (∀ t, 1 < t → g t ≤ C * exp (-p * t)) := by
  refine ⟨min p₁ p₂, max C₁ C₂, lt_min hp₁ hp₂, le_max_of_le_left hC₁, fun t ht => ?_,
    fun t ht => ?_⟩
  · refine (hf t ht).trans (mul_le_mul (le_max_left _ _) (exp_le_exp.2 ?_) (exp_pos _).le
      (le_max_of_le_left hC₁))
    nlinarith [min_le_left p₁ p₂]
  · refine (hg t ht).trans (mul_le_mul (le_max_right _ _) (exp_le_exp.2 ?_) (exp_pos _).le
      (le_max_of_le_left hC₁))
    nlinarith [min_le_right p₁ p₂]
lemma vif (a : UnitAddCircle) : vaq (hurwitzEvenFEPair a).Λ₀ := by
  obtain ⟨p₁, hp₁, h₁⟩ := isBigO_atTop_evenKernel_sub a
  obtain ⟨p₂, hp₂, h₂⟩ := isBigO_atTop_cosKernel_sub a
  obtain ⟨C₁, hC₁, hb₁⟩ := veK
    ((continuousOn_evenKernel a).sub continuousOn_const) hp₁.le h₁
  obtain ⟨C₂, hC₂, hb₂⟩ := veK
    ((continuousOn_cosKernel a).sub continuousOn_const) hp₂.le h₂
  obtain ⟨p, C, hp, hC, hf, hg⟩ := vir hp₁ hp₂ hC₁ hC₂ hb₁ hb₂
  refine vhW _ hp hC (fun t ht => ?_) (fun t ht => ?_)
  · have : (hurwitzEvenFEPair a).f t - (hurwitzEvenFEPair a).f₀ =
        ((evenKernel a t - if a = 0 then 1 else 0 : ℝ) : ℂ) := by
      simp only [hurwitzEvenFEPair, Function.comp_apply]
      split_ifs <;> simp
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact hf t ht
  · have : (hurwitzEvenFEPair a).g t - (hurwitzEvenFEPair a).g₀ =
        ((cosKernel a t - 1 : ℝ) : ℂ) := by
      simp [hurwitzEvenFEPair]
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact hg t ht
lemma vdA (a : UnitAddCircle) :
    vaq (completedHurwitzZetaEven₀ a) := by
  refine (((vif a).comp (g := fun s => s / 2) le_rfl (fun s => ?_)).mul
    (vaq.const (1 / 2))).congr (fun s => ?_)
  · rw [norm_div, Complex.norm_two, add_zero]
    linarith [norm_nonneg s]
  · simp only [completedHurwitzZetaEven₀]; ring
end Erdos985.Analytic.XiOrderAux
end
section
open Complex
namespace Erdos985.Analytic
noncomputable def van (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta₀ s + 1
theorem vbs : Differentiable ℂ van := by
  unfold van
  have := differentiable_completedZeta₀
  fun_prop
theorem vgV {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    van s = s * (s - 1) * completedRiemannZeta s := by
  have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have h2 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [van, completedRiemannZeta_eq]
  field_simp
  ring
theorem vcj : van 0 = 1 := by simp [van]
open XiOrderAux in
theorem vgS {F : ℂ → ℂ} (hF : vaq F) :
    ∃ C : ℝ, ∀ s : ℂ, ‖F s‖ ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)) := by
  obtain ⟨K, a, b, ha, hb, h⟩ := hF
  have hK : 0 ≤ K := vaq.vgA h
  set lb := Real.log b
  have hlb : 0 ≤ lb := Real.log_nonneg (by linarith)
  set C₀ := a * (2 * lb + 1 + 2 * b)
  set D := a * (b * (lb + 1))
  refine ⟨max (K * Real.exp D) C₀, fun s => (h s).trans ?_⟩
  set u := ‖s‖
  have hu : 0 ≤ u := norm_nonneg s
  set ℓ := Real.log (u + 2)
  have hℓ2 : (1 / 2 : ℝ) ≤ ℓ := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hℓu : ℓ ≤ u + 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < u + 2 by linarith); linarith
  have hL : 0 ≤ u * ℓ := by positivity
  have h1 : Real.log (u + b) ≤ lb + ℓ := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have h2 : u ≤ 2 * (u * ℓ) := by nlinarith
  have key : a * ((u + b) * Real.log (u + b)) ≤ C₀ * (u * ℓ) + D := by
    have e : (u + b) * Real.log (u + b) ≤ (2 * lb + 1 + 2 * b) * (u * ℓ) + b * (lb + 1) := by
      calc (u + b) * Real.log (u + b) ≤ (u + b) * (lb + ℓ) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = lb * u + u * ℓ + b * lb + b * ℓ := by ring
        _ ≤ lb * (2 * (u * ℓ)) + u * ℓ + b * lb + b * (2 * (u * ℓ) + 1) := by
            gcongr; linarith
        _ = _ := by ring
    have := mul_le_mul_of_nonneg_left e ha
    simp only [C₀, D]; nlinarith
  calc K * Real.exp (a * ((u + b) * Real.log (u + b)))
      ≤ K * Real.exp (C₀ * (u * ℓ) + D) := by gcongr
    _ = K * Real.exp D * Real.exp (C₀ * (u * ℓ)) := by
        rw [Real.exp_add]; ring
    _ ≤ max (K * Real.exp D) C₀ * Real.exp (max (K * Real.exp D) C₀ * (u * ℓ)) :=
        mul_le_mul (le_max_left _ _)
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hL))
          (Real.exp_pos _).le (le_max_of_le_left (by positivity))
    _ = _ := by ring_nf
theorem vek :
    ∃ C : ℝ, ∀ s : ℂ, ‖van s‖ ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)) := by
  open XiOrderAux in
  have hid : vaq (fun s : ℂ => s) := by
    refine ⟨1, 1, 3, zero_le_one, le_rfl, fun s => ?_⟩
    have h3 : 1 ≤ Real.log (‖s‖ + 3) := vcD (by linarith [norm_nonneg s])
    have := Real.add_one_le_exp ‖s‖
    have : ‖s‖ ≤ (‖s‖ + 3) * Real.log (‖s‖ + 3) := by nlinarith [norm_nonneg s]
    have : Real.exp ‖s‖ ≤ Real.exp (1 * ((‖s‖ + 3) * Real.log (‖s‖ + 3))) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  open XiOrderAux in
  have h : vaq van :=
    (((hid.mul (hid.add (vaq.const (-1)))).mul
      (vdA 0)).add (vaq.const 1)).congr fun s => by
        simp only [van, completedRiemannZeta₀]; ring
  exact vgS h
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic.IdentityAux
open Complex MeasureTheory
theorem vgD {ι : Type*} [Countable ι] {F : ι → ℝ → ℂ} {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f) (hF_int : ∀ i, Integrable (F i))
    (hF_sum : Summable fun i => ∫ t, ‖F i t‖) (hsum : ∀ t, HasSum (fun i => F i t) (f t)) :
    Integrable f := by
  refine ⟨hf, ?_⟩
  have h1 : ∀ t, ‖f t‖ₑ ≤ ∑' i, ‖F i t‖ₑ := fun t => by
    rw [← (hsum t).tsum_eq]; exact enorm_tsum_le_tsum_enorm
  unfold HasFiniteIntegral
  calc ∫⁻ t, ‖f t‖ₑ ≤ ∫⁻ t, ∑' i, ‖F i t‖ₑ := lintegral_mono h1
    _ = ∑' i, ∫⁻ t, ‖F i t‖ₑ := lintegral_tsum fun i => (hF_int i).1.enorm
    _ = ∑' i, ENNReal.ofReal (∫ t, ‖F i t‖) := by
        congr 1; funext i; rw [ofReal_integral_norm_eq_lintegral_enorm (hF_int i)]
    _ = ENNReal.ofReal (∑' i, ∫ t, ‖F i t‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun _ => norm_nonneg _)
          hF_sum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top
variable {N : ℕ} [NeZero N]
end Erdos985.Analytic.IdentityAux
end
section
namespace Erdos985.Analytic.IdentityAux
open Complex MeasureTheory
noncomputable def kern (x t : ℝ) : ℂ :=
  (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))
noncomputable def vcy (x : ℝ) (ρ : ℂ) (t : ℝ) : ℂ :=
  (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))
noncomputable def vbC (x : ℝ) (ρ : ℂ) (t : ℝ) : ℂ :=
  (1 / ((2 : ℂ) + t * I - ρ) - 1 / (2 - ρ)) * kern x t
lemma vgM (t : ℝ) : (2 : ℂ) + t * I ≠ 0 := fun h => by
  have := congrArg re h; simp at this
lemma ves (t : ℝ) : (2 : ℂ) + t * I + 1 ≠ 0 := fun h => by
  have := congrArg re h; simp at this; norm_num at this
lemma vfj {ρ : ℂ} (hρ : ρ.re < 2) (t : ℝ) : (2 : ℂ) + t * I - ρ ≠ 0 := fun h => by
  have := congrArg re h; simp at this; linarith
lemma vhD {ρ : ℂ} (hρ : ρ.re < 2) : (2 : ℂ) - ρ ≠ 0 := fun h => by
  have := congrArg re h; simp at this; linarith
lemma vhv (x : ℝ) (ρ : ℂ) (t : ℝ) :
    vbC x ρ t = vcy x ρ t - (1 / (2 - ρ)) * kern x t := by
  unfold vbC vcy kern
  simp only [div_eq_mul_inv, mul_inv]
  ring
lemma vbQ {x : ℝ} (hx : 0 < x) : Integrable (kern x) := by
  have := PerronKernel.vhj 2 x two_pos hx
  unfold PerronKernel.K at this
  simp only [ofReal_ofNat] at this
  exact this
lemma vdI {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ : ρ.re < 2) :
    Integrable (vcy x ρ) := by
  have := vdy x 2 hx two_pos ρ (by simpa using hρ)
  simp only [ofReal_ofNat] at this
  exact this
lemma veL {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ : ρ.re < 2) :
    Integrable (vbC x ρ) := by
  have : vbC x ρ = fun t => vcy x ρ t - (1 / (2 - ρ)) * kern x t :=
    funext (vhv x ρ)
  rw [this]
  exact (vdI hx hρ).sub ((vbQ hx).const_mul _)
lemma vgI {x : ℝ} (hx : 1 ≤ x) :
    ∫ t, kern x t = 2 * Real.pi * (1 - 1 / (x : ℂ)) := by
  have h := PerronKernel.vgL x 2 (by linarith) two_pos
  simp only [ofReal_ofNat] at h
  rw [show (∫ t, kern x t) = _ from h, ite_eq_left_iff.2 (fun h => absurd hx h)]
  push_cast
  ring
lemma vho (x : ℕ) (hx : 1 ≤ x) {ρ : ℂ} (hρ : ρ.re < 2) (hρ0 : ρ ≠ 0)
    (hρ1 : ρ ≠ -1) :
    ∫ t, vbC (x : ℝ) ρ t = -(2 * Real.pi) * vcY x ρ := by
  have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have h := veO (x : ℝ) 2 hx' two_pos ρ (by simpa using hρ) hρ0 hρ1
  simp only [ofReal_ofNat, ofReal_natCast] at h
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_pos.ne')
  have hR : ∫ t, vcy (x : ℝ) ρ t = 2 * Real.pi * ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ
      + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ)) := by
    rw [← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
    simp [vcy]
  have hK := vgI hx'
  simp_rw [vhv]
  rw [integral_sub (vdI hx0 hρ) ((vbQ hx0).const_mul _),
    integral_const_mul, hR, hK]
  simp only [ofReal_natCast]
  unfold vcY
  ring
lemma vhI {x : ℝ} {ρ : ℂ} (hρ : ρ.re < 2) (t : ℝ) :
    ‖vbC x ρ t‖ ≤
      ‖(x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I + 1))‖
        / ‖(2 : ℂ) - ρ‖ := by
  have h0 := vgM t
  have h1 := ves t
  have h2 := vfj hρ t
  have h3 := vhD hρ
  have heq : vbC x ρ t = ((2 - ((2 : ℂ) + t * I)) / ((2 : ℂ) + t * I)) *
      ((x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I + 1)))
        / (2 - ρ) := by
    unfold vbC kern
    field_simp
    ring
  rw [heq, norm_div, norm_mul]
  gcongr
  calc ‖(2 - ((2 : ℂ) + t * I)) / ((2 : ℂ) + t * I)‖ * _ ≤ 1 * _ := by
        gcongr
        rw [norm_div, div_le_one (norm_pos_iff.2 h0)]
        have e : (2 : ℂ) - ((2 : ℂ) + t * I) = -(t * I) := by ring
        rw [e, norm_neg, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
        have := abs_im_le_norm ((2 : ℂ) + t * I)
        simpa using this
    _ = _ := one_mul _
theorem vfu :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ∀ ρ : ℂ, ρ.re < 1 → ρ ≠ 0 →
      ∫ t, ‖vbC x ρ t‖ ≤ C * x ^ (2 : ℝ) / ‖ρ‖ ^ (1 + 1 / 2 : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := vcQ (δ := 1) (θ := 1 / 2) one_pos
    (by norm_num) (by norm_num)
  refine ⟨3 * K, by positivity, fun x hx ρ hρ hρ0 => ?_⟩
  obtain ⟨hint, hbd⟩ := hK x 2 hx two_pos ρ (by norm_num; exact hρ.le)
  simp only [ofReal_ofNat] at hint hbd
  have hρ2 : ρ.re < 2 := by linarith
  have ha : 1 < ‖(2 : ℂ) - ρ‖ := by
    have := re_le_norm ((2 : ℂ) - ρ); simp at this; linarith
  have hr : 0 < ‖ρ‖ := norm_pos_iff.2 hρ0
  calc ∫ t, ‖vbC x ρ t‖
      ≤ ∫ t : ℝ, ‖(x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I + 1))‖
          / ‖(2 : ℂ) - ρ‖ :=
        integral_mono (veL hx hρ2).norm (hint.norm.div_const _)
          (vhI hρ2)
    _ = (∫ t : ℝ, ‖(x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - ρ) * ((2 : ℂ) + t * I + 1))‖)
          / ‖(2 : ℂ) - ρ‖ := integral_div _ _
    _ ≤ K * x ^ (2 : ℝ) * (1 + ‖ρ‖) ^ (-(1 / 2 : ℝ)) / ‖(2 : ℂ) - ρ‖ := by gcongr
    _ ≤ 3 * K * x ^ (2 : ℝ) / ‖ρ‖ ^ (1 + 1 / 2 : ℝ) := by
        have hle : ‖ρ‖ ≤ 3 * ‖(2 : ℂ) - ρ‖ := by
          have := norm_sub_le (2 : ℂ) ((2 : ℂ) - ρ)
          simp at this
          linarith
        have hsq : ‖ρ‖ ^ (1 / 2 : ℝ) ≤ (1 + ‖ρ‖) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hr.le (by linarith) (by norm_num)
        rw [Real.rpow_neg (by positivity), Real.rpow_add hr, Real.rpow_one]
        have hp1 : 0 < (1 + ‖ρ‖) ^ (1 / 2 : ℝ) := by positivity
        have hp2 : 0 < ‖ρ‖ ^ (1 / 2 : ℝ) := by positivity
        have hxk : 0 ≤ K * x ^ (2 : ℝ) := by positivity
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        calc K * x ^ (2 : ℝ) * ((1 + ‖ρ‖) ^ (1 / 2 : ℝ))⁻¹ * (‖ρ‖ * ‖ρ‖ ^ (1 / 2 : ℝ))
            ≤ K * x ^ (2 : ℝ) * ((1 + ‖ρ‖) ^ (1 / 2 : ℝ))⁻¹
                * (3 * ‖(2 : ℂ) - ρ‖ * (1 + ‖ρ‖) ^ (1 / 2 : ℝ)) := by
              gcongr
          _ = 3 * K * x ^ (2 : ℝ) * ‖(2 : ℂ) - ρ‖ := by
              field_simp
end Erdos985.Analytic.IdentityAux
end
section
namespace Erdos985.Analytic
open Complex ArithmeticFunction MeasureTheory IdentityAux
open scoped Classical
variable {N : ℕ} [NeZero N]
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic.BoundsAux
open Complex
lemma viR (x : ℕ) (hx : 1 ≤ x) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    vcY x ρ = 2 / (ρ * (2 - ρ)) - (3 / (x : ℂ)) / ((2 - ρ) * (1 + ρ))
      - (x : ℂ) ^ ρ / (ρ * (ρ + 1)) := by
  have h0 : ρ ≠ 0 := fun h => by rw [h] at hρ; norm_num at hρ
  have h2 : (2 : ℂ) - ρ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hρ] at this; norm_num at this
  have h1 : (1 : ℂ) + ρ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hρ] at this; norm_num at this
  have h1' : ρ + 1 ≠ 0 := by rwa [add_comm]
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  unfold vcY
  rw [cpow_neg_one]
  field_simp
  ring
lemma vic {ρ : ℂ} (hρ : ρ.re = 1 / 2) : ‖(2 : ℂ) - ρ‖ = ‖ρ + 1‖ := by
  rw [← Complex.norm_conj (ρ + 1)]
  congr 1
  apply Complex.ext <;> norm_num [hρ]
lemma vch {ρ : ℂ} (hρ : ρ.re = 1 / 2) : ‖ρ‖ ≤ ‖ρ + 1‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_le_sqrt
  simp [Complex.normSq_apply, hρ]
  norm_num
end Erdos985.Analytic.BoundsAux
namespace Erdos985.Analytic
open Complex BoundsAux
end Erdos985.Analytic
end
section
open Real ArithmeticFunction
namespace Erdos985.Analytic.BoundsAux
lemma viM (f : ℕ → ℝ) (n : ℕ) :
    LSeries.term (fun n => (f n : ℂ)) 2 n = ((f n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_ofNat]
    push_cast
    rfl
lemma veV (f : ℕ → ℝ) :
    LSeries (fun n => (f n : ℂ)) 2 = ((∑' n : ℕ, f n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  exact tsum_congr (viM f)
lemma vgz (f : ℕ → ℝ) (h : LSeriesSummable (fun n => (f n : ℂ)) 2) :
    Summable fun n : ℕ => f n / (n : ℝ) ^ 2 := by
  have : LSeries.term (fun n => (f n : ℂ)) 2 =
      fun n => ((f n / (n : ℝ) ^ 2 : ℝ) : ℂ) := funext (viM f)
  rw [LSeriesSummable, this] at h
  exact Complex.summable_ofReal.mp h
lemma re2 : 1 < (2 : ℂ).re := by norm_num
lemma viC : Summable fun n : ℕ => Real.log n / (n : ℝ) ^ 2 := by
  refine vgz (fun n => Real.log n) ?_
  have := (LSeriesSummable_vonMangoldt re2).convolution (LSeriesSummable_one_iff.mpr re2)
  rw [convolution_vonMangoldt_const_one] at this
  convert this using 2 with n
  simp [Complex.natCast_log]
lemma vjs :
    (∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2) * (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) =
      ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2 := by
  have h := LSeries_convolution' (LSeriesSummable_vonMangoldt re2)
    (LSeriesSummable_one_iff.mpr re2)
  rw [convolution_vonMangoldt_const_one] at h
  have e1 := veV (fun n => (Λ n : ℝ))
  have e2 := veV (fun _ => (1 : ℝ))
  have e3 := veV (fun n : ℕ => Real.log n)
  have h1 : (1 : ℕ → ℂ) = fun _ => ((1 : ℝ) : ℂ) := by ext; simp
  have h3 : (fun n : ℕ => Complex.log n) = fun n : ℕ => ((Real.log n : ℝ) : ℂ) := by
    ext n; simp [Complex.natCast_log]
  rw [h1, h3, e1, e2, e3] at h
  exact_mod_cast h.symm
lemma vjq {c y : ℝ} (hc : 2 ≤ c) (hcy : c ≤ y) :
    Real.log y / y ^ 2 ≤ Real.log c / c ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hy0 : 0 < y := by linarith
  have hL : 2 / 3 ≤ Real.log c := by
    have := Real.log_le_log (by norm_num) hc
    linarith [Real.log_two_gt_d9]
  have hlog : Real.log y - Real.log c ≤ y / c - 1 := by
    rw [← Real.log_div hy0.ne' hc0.ne']
    exact Real.log_le_sub_one_of_pos (by positivity)
  have hlog' : (Real.log y - Real.log c) * c ≤ y - c := by
    have : y / c - 1 = (y - c) / c := by field_simp
    rw [this, le_div_iff₀ hc0] at hlog; exact hlog
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 0 ≤ y - c := by linarith
  have : (y - c) * c ≤ Real.log c * (y - c) * (y + c) := by
    have : c ≤ Real.log c * (y + c) := by nlinarith
    nlinarith
  nlinarith
noncomputable def G2 (x : ℝ) : ℝ := (Real.log x + 1) / x
lemma vgH {t : ℝ} (ht : 0 < t) :
    HasDerivAt G2 (-(Real.log t / t ^ 2)) t := by
  have h1 : HasDerivAt (fun x => Real.log x + 1) (t⁻¹) t :=
    (Real.hasDerivAt_log ht.ne').add_const 1
  have := h1.div (hasDerivAt_id' t) ht.ne'
  unfold G2
  convert this using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
  ring
lemma vjr {x : ℝ} (hx : 2 ≤ x) :
    Real.log (x + 1) / (x + 1) ^ 2 ≤ G2 x - G2 (x + 1) := by
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope G2 (fun t => -(Real.log t / t ^ 2))
    (by linarith : x < x + 1)
    (fun t ht => (vgH (by linarith [ht.1])).continuousAt.continuousWithinAt)
    (fun t ht => vgH (by linarith [ht.1]))
  have : G2 x - G2 (x + 1) = Real.log c / c ^ 2 := by
    rw [show x + 1 - x = 1 by ring, div_one] at hcd
    linarith
  rw [this]
  exact vjq (by linarith [hc.1]) hc.2.le
lemma vjh {x : ℝ} (hx : 1 ≤ x) : 0 ≤ G2 x := by
  unfold G2
  have := Real.log_nonneg hx
  have : 0 < x := by linarith
  positivity
lemma vjn (K : ℕ) (hK : 3 ≤ K) :
    ∑' i : ℕ, Real.log ((i + K : ℕ) : ℝ) / (((i + K : ℕ) : ℝ)) ^ 2 ≤ G2 ((K : ℝ) - 1) := by
  have hK' : (3 : ℝ) ≤ K := by exact_mod_cast hK
  refine Real.tsum_le_of_sum_range_le (fun i => ?_) (fun M => ?_)
  · have : (1 : ℝ) ≤ ((i + K : ℕ) : ℝ) := by push_cast; linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
    have := Real.log_nonneg this
    positivity
  · have htel := Finset.sum_range_sub' (fun i : ℕ => G2 ((K : ℝ) - 1 + i)) M
    simp only [Nat.cast_zero, add_zero] at htel
    have hG : 0 ≤ G2 ((K : ℝ) - 1 + M) :=
      vjh (by linarith [(M.cast_nonneg : (0 : ℝ) ≤ M)])
    refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) (le_of_eq_of_le htel (by linarith))
    have hx : (2 : ℝ) ≤ (K : ℝ) - 1 + i := by linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
    have := vjr hx
    push_cast
    rw [show (K : ℝ) - 1 + ((i : ℝ) + 1) = (K : ℝ) - 1 + i + 1 by ring,
      show (i : ℝ) + K = (K : ℝ) - 1 + i + 1 by ring]
    exact this
lemma vjw : ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2 ≤ 0.962 := by
  obtain ⟨l2, l3, l5, -, -, -, -, -⟩ := ConstantsAux.viH
  have hD := (viC.sum_add_tsum_nat_add 7).symm
  have hdt := vjn 7 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hD
  norm_num at hD hdt
  unfold G2 at hdt
  have e4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num]; simp [Real.log_mul, Real.log_pow]
  rw [hD]
  norm_num [e4, e6] at hdt ⊢
  linarith
lemma vjv : ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2 ≤ 0.6 := by
  have hmul := vjs
  have hZ : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 = π ^ 2 / 6 := hasSum_zeta_two.tsum_eq
  have hD := vjw
  have hS : 0 ≤ ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2 :=
    tsum_nonneg fun n => div_nonneg vonMangoldt_nonneg (by positivity)
  rw [hZ] at hmul
  have hpi : (1.643 : ℝ) ≤ π ^ 2 / 6 := by
    nlinarith [Real.pi_gt_d2, mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 3.14) Real.pi_gt_d2.le]
  set S := ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2
  by_contra h
  have h' := (not_le.mp h).le
  nlinarith [mul_le_mul h' hpi (by norm_num) hS]
end Erdos985.Analytic.BoundsAux
namespace Erdos985.Analytic
open Complex BoundsAux
variable {N : ℕ} [NeZero N]
end Erdos985.Analytic
end
section
open Complex Filter Topology Set
namespace Erdos985.Analytic.BoundsAux
noncomputable def rD (x : ℝ) : ℝ := deriv (Real.log ∘ Real.Gamma) x
lemma veS {x : ℝ} (hx : 0 < x) : digamma (x : ℂ) = (rD x : ℂ) := by
  have hne : ∀ m : ℕ, (x : ℂ) ≠ -m := fun m h => by
    have := congrArg Complex.re h
    simp at this
    linarith [m.cast_nonneg (α := ℝ)]
  have hneR : ∀ m : ℕ, x ≠ -m := fun m h => by linarith [m.cast_nonneg (α := ℝ)]
  have h1 := ((Complex.differentiableAt_Gamma _ hne).hasDerivAt).comp_ofReal
  have h2 := ((Real.differentiableAt_Gamma hneR).hasDerivAt).ofReal_comp
  have heq : (fun t : ℝ => Complex.Gamma (t : ℂ)) = fun t => ((Real.Gamma t : ℝ) : ℂ) :=
    funext Complex.Gamma_ofReal
  rw [heq] at h1
  have hd := h1.unique h2
  rw [digamma_def, logDeriv_apply, hd, Complex.Gamma_ofReal, rD, Function.comp_def,
    deriv.log (Real.differentiableAt_Gamma hneR) (Real.Gamma_pos_of_pos hx).ne']
  push_cast
  rfl
lemma veX {x : ℝ} (hx : 1 < x) : Real.log (x - 1) ≤ rD x ∧ rD x ≤ Real.log x := by
  let f := Real.log ∘ Real.Gamma
  have hc : ConvexOn ℝ (Ioi 0) f := Real.convexOn_log_Gamma
  have h_rec (y : ℝ) (hy : 0 < y) : f (y + 1) = f y + Real.log y := by
    simp only [f, Function.comp_apply, Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne', add_comm]
  have hder {y : ℝ} (hy : 0 < y) : DifferentiableAt ℝ f y := by
    refine ((Real.differentiableAt_Gamma ?_).log (Real.Gamma_ne_zero ?_)) <;>
    exact fun m ↦ ne_of_gt (by linarith [m.cast_nonneg (α := ℝ)])
  constructor
  · refine (le_of_eq ?_).trans (hc.slope_le_deriv (mem_Ioi.mpr (by linarith : (0:ℝ) < x - 1))
      (mem_Ioi.mpr (by linarith : (0:ℝ) < x)) (by linarith) (hder (by linarith)))
    rw [slope_def_field, show x - (x - 1) = (1:ℝ) by ring, div_one]
    have := h_rec (x - 1) (by linarith)
    rw [show x - 1 + 1 = x by ring] at this
    linarith
  · refine (hc.deriv_le_slope (mem_Ioi.mpr (by linarith : (0:ℝ) < x))
      (mem_Ioi.mpr (by linarith : (0:ℝ) < x + 1)) (by linarith) (hder (by linarith))).trans
      (le_of_eq ?_)
    rw [slope_def_field, show x + 1 - x = (1:ℝ) by ring, div_one, h_rec x (by linarith)]
    ring
lemma vgk {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : Real.log a - Real.log b ≤ a / b - 1 := by
  rw [← Real.log_div ha.ne' hb.ne']
  exact Real.log_le_sub_one_of_pos (by positivity)
lemma vil {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => rD (x + n) - rD (1 + n)) atTop (𝓝 0) := by
  have hC := tendsto_const_div_atTop_nhds_zero_nat (x + 4)
  have hC' := hC.neg
  rw [neg_zero] at hC'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hC' hC ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    obtain ⟨l1, -⟩ := veX (x := x + n) (by linarith)
    obtain ⟨-, u2⟩ := veX (x := 1 + n) (by linarith)
    have := vgk (a := 1 + n) (b := x + n - 1) (by linarith) (by linarith)
    have hq : (1 + n) / (x + n - 1) - 1 ≤ (x + 4) / n := by
      rw [div_sub_one (by linarith), div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    linarith
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    obtain ⟨-, u1⟩ := veX (x := x + n) (by linarith)
    obtain ⟨l2, -⟩ := veX (x := 1 + n) (by linarith)
    rw [show 1 + (n : ℝ) - 1 = n by ring] at l2
    have := vgk (a := x + n) (b := n) (by linarith) (by linarith)
    have hq : (x + n) / n - 1 ≤ (x + 4) / n := by
      rw [div_sub_one (by linarith)]
      exact div_le_div_of_nonneg_right (by linarith) (by linarith)
    linarith
lemma norm_term_le {w : ℂ} (hw : 1 / 2 < w.re) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w)‖ ≤ 2 * (‖w‖ + 1) / ((k : ℝ) + 1) ^ 2 := by
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  have hre : ((k : ℝ) + 1) / 2 ≤ ‖(k : ℂ) + w‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp
    linarith [k.cast_nonneg (α := ℝ)]
  have hkw : ((k : ℂ) + w) ≠ 0 := by
    intro h; rw [h, norm_zero] at hre; linarith [k.cast_nonneg (α := ℝ)]
  rw [div_sub_div _ _ hk1 hkw, norm_div, norm_mul]
  have e1 : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by exact_mod_cast Complex.norm_natCast (k + 1)
  rw [e1]
  have hnum : ‖1 * ((k : ℂ) + w) - (k + 1) * 1‖ ≤ ‖w‖ + 1 := by
    rw [show 1 * ((k : ℂ) + w) - (k + 1) * 1 = w - 1 by ring]
    exact (norm_sub_le _ _).trans (by simp)
  have hk0 : (0 : ℝ) < k + 1 := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ ‖w‖ + 1 := by positivity
  calc ‖1 * ((k : ℂ) + w) - (k + 1) * 1‖ * ((k : ℝ) + 1) ^ 2
      ≤ (‖w‖ + 1) * ((k : ℝ) + 1) ^ 2 := by gcongr
    _ ≤ 2 * (‖w‖ + 1) * (((k : ℝ) + 1) * ‖(k : ℂ) + w‖) := by
      nlinarith [mul_le_mul_of_nonneg_left hre (by positivity : 0 ≤ 2 * (‖w‖ + 1) * ((k : ℝ) + 1))]
lemma vey : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa using this
lemma vgJ {w : ℂ} (hw : 1 / 2 < w.re) :
    Summable fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w) := by
  refine Summable.of_norm_bounded ?_ (norm_term_le hw)
  exact (vey.mul_left (2 * (‖w‖ + 1))).congr (fun k => by ring)
lemma vgQ {x : ℝ} (hx : 1 / 2 < x) :
    HasSum (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + x)) (digamma x - digamma 1) := by
  have hx0 : 0 < x := by linarith
  have hx' : ∀ m : ℕ, (x : ℂ) ≠ -m := fun m h => by
    have := congrArg Complex.re h
    simp at this
    linarith [m.cast_nonneg (α := ℝ)]
  have h1' : ∀ m : ℕ, (1 : ℂ) ≠ -m := fun m h => by
    have := congrArg Complex.re h
    simp at this
    linarith [m.cast_nonneg (α := ℝ)]
  have hpart : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + x)) =
      (digamma x - digamma 1) - (digamma ((x + n : ℝ) : ℂ) - digamma ((1 + n : ℝ) : ℂ)) := by
    intro n
    push_cast
    rw [digamma_apply_add_nat hx' n, digamma_apply_add_nat h1' n, Finset.sum_sub_distrib]
    simp only [one_div, add_comm (1 : ℂ), add_comm (x : ℂ)]
    ring
  have hs := vgJ (w := (x : ℂ)) (by simpa using hx)
  rw [hs.hasSum_iff_tendsto_nat]
  simp_rw [hpart]
  rw [show nhds (digamma (x : ℂ) - digamma 1) = nhds (digamma (x : ℂ) - digamma 1 - 0) by simp]
  refine tendsto_const_nhds.sub ?_
  have : (fun n : ℕ => digamma ((x + n : ℝ) : ℂ) - digamma ((1 + n : ℝ) : ℂ)) =
      fun n : ℕ => ((rD (x + n) - rD (1 + n) : ℝ) : ℂ) := by
    funext n
    rw [veS (by positivity), veS (by positivity)]
    push_cast; ring
  rw [this, show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp]
  exact (Complex.continuous_ofReal.tendsto _).comp (vil hx0)
lemma vfC :
    DifferentiableOn ℂ digamma {z : ℂ | 0 < z.re} := by
  have ho : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hne : ∀ z ∈ {z : ℂ | 0 < z.re}, ∀ m : ℕ, z ≠ -m := fun z hz m h => by
    rw [h] at hz; simp at hz; linarith [m.cast_nonneg (α := ℝ)]
  have hG : DifferentiableOn ℂ Gamma {z : ℂ | 0 < z.re} := fun z hz =>
    (Complex.differentiableAt_Gamma z (hne z hz)).differentiableWithinAt
  have : digamma = fun z => deriv Gamma z / Gamma z := by
    funext z; rw [digamma_def, logDeriv_apply]
  rw [this]
  exact (hG.deriv ho).div hG (fun z hz => Complex.Gamma_ne_zero_of_re_pos hz)
lemma vfg (R : ℝ) :
    DifferentiableOn ℂ (fun z => ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z)))
      ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 R) := by
  refine differentiableOn_tsum_of_summable_norm (u := fun k : ℕ => 2 * (R + 1) / ((k : ℝ) + 1) ^ 2)
    (F := fun (k : ℕ) (z : ℂ) => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z))
    ?_ (fun k => ?_) ((isOpen_lt continuous_const continuous_re).inter Metric.isOpen_ball)
    (fun k z hz => ?_)
  · exact (vey.mul_left (2 * (R + 1))).congr (fun k => by ring)
  · intro z hz
    have hkz : (k : ℂ) + z ≠ 0 := by
      intro h
      have h1 := congrArg Complex.re h
      have h2 : 1 / 2 < z.re := hz.1
      simp only [add_re, natCast_re, zero_re] at h1
      linarith [k.cast_nonneg (α := ℝ)]
    have : DifferentiableAt ℂ (fun z : ℂ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z)) z := by
      fun_prop (disch := exact hkz)
    exact this.differentiableWithinAt
  · refine (norm_term_le hz.1 k).trans ?_
    have hz2 : ‖z‖ < R := by simpa using hz.2
    gcongr
lemma vhm :
    ∃ᶠ z in 𝓝[≠] (1 : ℂ), (digamma z - digamma 1) =
      ∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z)) := by
  let u : ℕ → ℂ := fun n => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hu : Tendsto u atTop (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall (fun n => ?_)⟩
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ))
      rw [add_zero] at this
      have := (Complex.continuous_ofReal.tendsto _).comp this
      simpa [u, Function.comp_def] using this
    · simp only [mem_compl_iff, mem_singleton_iff, u]
      intro h
      have h1 := congrArg Complex.re h
      simp only [ofReal_re, one_re] at h1
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  refine hu.frequently (Frequently.of_forall (fun n => ?_))
  have hx : 1 / 2 < (1 + 1 / ((n : ℝ) + 1)) := by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  exact (vgQ hx).tsum_eq.symm
theorem vgs {w : ℂ} (hw : 1 / 2 < w.re) :
    HasSum (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + w)) (digamma w - digamma 1) := by
  have hUo : IsOpen ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 (‖w‖ + 2)) :=
    (isOpen_lt continuous_const continuous_re).inter Metric.isOpen_ball
  have hUc : IsPreconnected ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 (‖w‖ + 2)) :=
    ((convex_halfSpace_re_gt _).inter (convex_ball _ _)).isPreconnected
  have hF : DifferentiableOn ℂ (fun z => digamma z - digamma 1)
      ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 (‖w‖ + 2)) := by
    refine (vfC.mono (fun z hz => ?_)).sub_const _
    have h : 1 / 2 < z.re := hz.1
    show 0 < z.re
    linarith
  have h1U : (1 : ℂ) ∈ ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 (‖w‖ + 2)) :=
    ⟨by norm_num, by rw [Metric.mem_ball, dist_zero_right, norm_one]; linarith [norm_nonneg w]⟩
  have heq := (hF.analyticOnNhd hUo).eqOn_of_preconnected_of_frequently_eq
    ((vfg _).analyticOnNhd hUo) hUc h1U vhm
  have hwU : w ∈ ({z : ℂ | 1 / 2 < z.re} ∩ Metric.ball 0 (‖w‖ + 2)) := ⟨hw, by simp⟩
  have := heq hwU
  simp only at this
  rw [this]
  exact (vgJ hw).hasSum
end Erdos985.Analytic.BoundsAux
end
section
open Filter Topology
namespace Erdos985.Analytic.BoundsAux
noncomputable def tau (x : ℝ) (m : ℕ) : ℝ :=
  if m = 0 then (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x)
  else if m = 1 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * Real.log x)
  else (1 - 1 / x) / (2 + m) - ((1 / x) ^ m / (m * (m - 1)) + 1 / m - (1 / x) / (m - 1))
lemma vjo (y p M K : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ y) (hK : 0 ≤ K) (hM : 2 * (K + 1) ≤ M) :
    -(1 / 2) * (1 / ((K + 1) * (K + 2))) ≤
      (1 - y) / (2 + M) - (p / (M * (M - 1)) + 1 / M - y / (M - 1)) := by
  have h1 : M - 1 ≠ 0 := by intro h; linarith
  have h2 : M ≠ 0 := by intro h; linarith
  have h3 : 2 + M ≠ 0 := by intro h; linarith
  have h4 : K + 1 ≠ 0 := by intro h; linarith
  have h5 : K + 2 ≠ 0 := by intro h; linarith
  have e : (1 - y) / (2 + M) - (p / (M * (M - 1)) + 1 / M - y / (M - 1))
      - -(1 / 2) * (1 / ((K + 1) * (K + 2))) =
      ((M - 1) * (M ^ 2 + 2 * M - 8 - 4 * K ^ 2 - 12 * K) + (K + 1) * (K + 2) * (4 * M - 4) * y
        + 2 * (K + 1) * (K + 2) * (M + 2) * (y - p)) / (2 * M * (K + 1) * (K + 2) * (M - 1) * (2 + M)) := by
    field_simp
    ring
  rw [← sub_nonneg, e]
  have hy : 0 ≤ y := hp0.trans hp
  apply div_nonneg
  · have : 0 ≤ M ^ 2 + 2 * M - 8 - 4 * K ^ 2 - 12 * K := by nlinarith
    have : 0 ≤ (M - 1) * (M ^ 2 + 2 * M - 8 - 4 * K ^ 2 - 12 * K) := mul_nonneg (by linarith) this
    have : 0 ≤ (K + 1) * (K + 2) * (4 * M - 4) * y :=
      mul_nonneg (mul_nonneg (by positivity) (by linarith)) hy
    have : 0 ≤ 2 * (K + 1) * (K + 2) * (M + 2) * (y - p) :=
      mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
    linarith
  · have : 0 ≤ M - 1 := by linarith
    have : 0 ≤ M := by linarith
    positivity
lemma vji (y p K : ℝ) (hp0 : 0 ≤ p) (hy : 0 ≤ y) (hK : 0 ≤ K) :
    (1 - y) / (2 + 2 * (K + 1)) - (p / (2 * (K + 1) * (2 * (K + 1) - 1)) + 1 / (2 * (K + 1))
      - y / (2 * (K + 1) - 1)) ≤ (3 * y - 1) / 2 * (1 / ((K + 1) * (K + 2))) := by
  have h1 : 2 * K + 1 ≠ 0 := by intro h; linarith
  have h1' : 2 * (K + 1) - 1 ≠ 0 := by intro h; linarith
  have h4 : K + 1 ≠ 0 := by intro h; linarith
  have h5 : K + 2 ≠ 0 := by intro h; linarith
  have e : (3 * y - 1) / 2 * (1 / ((K + 1) * (K + 2))) - ((1 - y) / (2 + 2 * (K + 1)) -
      (p / (2 * (K + 1) * (2 * (K + 1) - 1)) + 1 / (2 * (K + 1)) - y / (2 * (K + 1) - 1))) =
      (K * p + 3 * K * y + 2 * p) / (2 * (K + 1) * (K + 2) * (2 * K + 1)) := by
    field_simp
    ring
  rw [← sub_nonneg, e]
  positivity
lemma vjj (y p K : ℝ) (hp0 : 0 ≤ p) (hy : 0 ≤ y) (hK : 0 ≤ K) :
    (1 - y) / (2 + (2 * (K + 1) + 1)) - (p / ((2 * (K + 1) + 1) * (2 * (K + 1) + 1 - 1))
      + 1 / (2 * (K + 1) + 1) - y / (2 * (K + 1) + 1 - 1))
      ≤ 3 * y / 4 * (1 / ((K + 1) * (K + 2))) := by
  have h1 : 2 * K + 3 ≠ 0 := by intro h; linarith
  have h2 : 2 * K + 5 ≠ 0 := by intro h; linarith
  have h4 : K + 1 ≠ 0 := by intro h; linarith
  have h5 : K + 2 ≠ 0 := by intro h; linarith
  have e : 3 * y / 4 * (1 / ((K + 1) * (K + 2))) - ((1 - y) / (2 + (2 * (K + 1) + 1)) -
      (p / ((2 * (K + 1) + 1) * (2 * (K + 1) + 1 - 1)) + 1 / (2 * (K + 1) + 1)
        - y / (2 * (K + 1) + 1 - 1))) =
      (4 * K ^ 2 * p + 8 * K ^ 2 + 18 * K * p + 6 * K * y + 24 * K + 20 * p + 9 * y + 16) /
        (4 * (K + 1) * (K + 2) * (2 * K + 3) * (2 * K + 5)) := by
    field_simp
    ring
  rw [← sub_nonneg, e]
  positivity
lemma vjg (x : ℝ) (hx : 1 ≤ x) (k : ℕ) (m : ℕ) (hm : 2 * (k + 1) ≤ m) :
    -(1 / 2) * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) ≤ tau x m := by
  have hm0 : m ≠ 0 := by omega
  have hm1 : m ≠ 1 := by omega
  simp only [tau, hm0, hm1, ite_false]
  have hy0 : 0 < 1 / x := by positivity
  have hy1 : 1 / x ≤ 1 := by rw [div_le_one (by linarith)]; exact hx
  exact vjo _ _ _ _ (by positivity) (pow_le_of_le_one hy0.le hy1 hm0) (Nat.cast_nonneg k)
    (by exact_mod_cast hm)
lemma vhB (x : ℝ) (hx : 1 ≤ x) (k : ℕ) :
    tau x (2 * (k + 1)) ≤ (3 * (1 / x) - 1) / 2 * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
  have hm0 : 2 * (k + 1) ≠ 0 := by omega
  have hm1 : 2 * (k + 1) ≠ 1 := by omega
  simp only [tau, hm0, hm1, ite_false]
  have hy0 : 0 < 1 / x := by positivity
  have := vji (1 / x) ((1 / x) ^ (2 * (k + 1))) k (by positivity) hy0.le (Nat.cast_nonneg k)
  push_cast
  exact this
lemma vja (x : ℝ) (hx : 1 ≤ x) (k : ℕ) :
    tau x (2 * (k + 1) + 1) ≤ 3 * (1 / x) / 4 * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
  have hm0 : 2 * (k + 1) + 1 ≠ 0 := by omega
  have hm1 : 2 * (k + 1) + 1 ≠ 1 := by omega
  simp only [tau, hm0, hm1, ite_false]
  have hy0 : 0 < 1 / x := by positivity
  have := vjj (1 / x) ((1 / x) ^ (2 * (k + 1) + 1)) k (by positivity) hy0.le
    (Nat.cast_nonneg k)
  push_cast
  exact this
lemma vdh : HasSum (fun k : ℕ => 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => by positivity)]
  have hps : ∀ n : ℕ, ∑ i ∈ Finset.range n, 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2)) =
      1 - 1 / ((n : ℝ) + 1) := by
    intro n
    have := Finset.sum_range_sub' (fun i : ℕ => 1 / ((i : ℝ) + 1)) n
    simp only [Nat.cast_zero, zero_add, div_one, Nat.cast_add, Nat.cast_one] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    field_simp
    ring
  simp_rw [hps]
  have := tendsto_one_div_add_atTop_nhds_zero_nat.const_sub (1 : ℝ)
  simpa using this
theorem vih (x : ℝ) (hx : 1 ≤ x) (a : ℕ) (ha : a ≤ 1) :
    Summable (fun k : ℕ => tau x (2 * k + a)) ∧
      |∑' k : ℕ, tau x (2 * k + a)| ≤ Real.log x + 1 := by
  set y := 1 / x with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 := by rw [hy, div_le_one (by linarith)]; exact hx
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have hL1 : 1 - y ≤ Real.log x := by
    have := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < x)
    rwa [hy, one_div]
  set u : ℕ → ℝ := fun k => 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) with hu
  have hu0 : ∀ k, 0 ≤ u k := fun k => by positivity
  set B : ℝ := if a = 0 then (3 * y - 1) / 2 else 3 * y / 4 with hB
  have hup : ∀ k : ℕ, tau x (2 * (k + 1) + a) ≤ B * u k := by
    intro k
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
    · simp only [hB, ↓reduceIte]; exact vhB x hx k
    · simp only [hB, one_ne_zero, ite_false]; exact vja x hx k
  have hlo : ∀ k : ℕ, -(1 / 2) * u k ≤ tau x (2 * (k + 1) + a) :=
    fun k => vjg x hx k _ (by omega)
  have hB1 : |B| ≤ 1 := by
    rw [hB]; split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have hg : Summable (fun k : ℕ => tau x (2 * (k + 1) + a)) := by
    refine Summable.of_norm_bounded vdh.summable (fun k => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have h1 := hup k
    have h2 := hlo k
    have h3 : B * u k ≤ u k := by
      have := (abs_le.mp hB1).2
      nlinarith [hu0 k]
    constructor <;> nlinarith [hu0 k]
  have hS : Summable (fun k : ℕ => tau x (2 * k + a)) := by
    exact (summable_nat_add_iff 1).mp hg
  refine ⟨hS, ?_⟩
  rw [hS.tsum_eq_zero_add]
  have e1 : (fun k : ℕ => tau x (2 * (k + 1) + a)) = fun k : ℕ => tau x (2 * (k + 1) + a) := rfl
  have hle : ∑' k : ℕ, tau x (2 * (k + 1) + a) ≤ B := by
    have := Summable.tsum_le_tsum hup hg (vdh.summable.mul_left B)
    rwa [tsum_mul_left, vdh.tsum_eq, mul_one] at this
  have hge : -(1 / 2) ≤ ∑' k : ℕ, tau x (2 * (k + 1) + a) := by
    have := Summable.tsum_le_tsum hlo (vdh.summable.mul_left _) hg
    rwa [tsum_mul_left, vdh.tsum_eq, mul_one] at this
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
  · simp only [hB, ite_true] at hle
    simp only [mul_zero, add_zero, tau, ite_true] at hle hge ⊢
    rw [← hy] at *
    rw [abs_le]; constructor <;> linarith
  · simp only [hB, one_ne_zero, ite_false] at hle
    simp only [mul_zero, zero_add, tau, ite_true, one_ne_zero, ite_false] at hle hge ⊢
    rw [← hy] at *
    have hyL : y * Real.log x ≤ Real.log x := by nlinarith
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg hy0.le hL]
end Erdos985.Analytic.BoundsAux
end
section
open Complex MeasureTheory Filter Topology
namespace Erdos985.Analytic.BoundsAux
lemma vgE {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun k : ℕ => 1 / (2 + ((2 * k + vbK χ : ℕ) : ℂ))
        - 1 / (s + ((2 * k + vbK χ : ℕ) : ℂ)))
      (vaR χ s - vaR χ 2) := by
  have ha0 : (0 : ℝ) ≤ (vbK χ : ℝ) := Nat.cast_nonneg _
  have hw : 1 / 2 < ((s + (vbK χ : ℂ)) / 2).re := by
    simp only [div_re, add_re, natCast_re, re_ofNat]
    norm_num
    linarith
  have hw2 : 1 / 2 < ((2 + (vbK χ : ℂ)) / 2).re := by
    simp only [div_re, add_re, natCast_re, re_ofNat]
    norm_num
    linarith
  have h := ((vgs hw).sub (vgs hw2)).mul_left (1 / 2)
  unfold vaR
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  · funext k
    have hh (u z : ℂ) : 1 / 2 * (1 / (u + z / 2)) = 1 / (2 * u + z) := by
      rw [one_div_mul_one_div]; congr 1; ring
    rw [show (1 / 2 : ℂ) * (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (s + (vbK χ : ℂ)) / 2)
        - (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (2 + (vbK χ : ℂ)) / 2)))
        = 1 / 2 * (1 / ((k : ℂ) + (2 + (vbK χ : ℂ)) / 2))
          - 1 / 2 * (1 / ((k : ℂ) + (s + (vbK χ : ℂ)) / 2)) by ring, hh, hh]
    push_cast
    congr 1 <;> congr 1 <;> ring
  · ring
noncomputable def vdx (x : ℕ) (m : ℕ) (t : ℝ) : ℂ :=
  (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * (x : ℂ) ^ ((2 : ℂ) + t * I)
    / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))
lemma viN (x m : ℕ) (t : ℝ) : vdx x m t =
    1 / (2 + (m : ℂ)) * ((x : ℂ) ^ ((2 : ℂ) + t * I) /
      (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)))
    - (x : ℂ) ^ ((2 : ℂ) + t * I) /
      (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) := by
  have hm : (0 : ℝ) ≤ m := m.cast_nonneg
  have h0 : (2 : ℂ) + t * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h1 : (2 : ℂ) + t * I + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : (2 : ℂ) + t * I + m ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h3 : (2 : ℂ) + m ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold vdx
  rw [sub_neg_eq_add]
  field_simp
lemma hw_m (m : ℕ) : (-(m : ℂ)).re < 2 := by
  simp only [neg_re, natCast_re]; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
lemma vfK (x : ℕ) (hx : 1 ≤ x) (m : ℕ) : Integrable (vdx x m) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hK := PerronAux.vdK (x := (x : ℝ)) (c := 2) hx0 two_pos
  have hP := PerronAux.vcm (x := (x : ℝ)) (c := 2) hx0 two_pos (hw_m m)
  simp only [ofReal_natCast, ofReal_ofNat] at hK hP
  rw [show vdx x m = _ from funext (viN x m)]
  exact (hK.const_mul _).sub hP
lemma vik (x : ℕ) (hx : 1 ≤ x) (m : ℕ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, vdx x m t = (tau x m : ℂ) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  have hK := PerronAux.vdK (x := (x : ℝ)) (c := 2) hx0 two_pos
  have hP := PerronAux.vcm (x := (x : ℝ)) (c := 2) hx0 two_pos (hw_m m)
  have hC := viI (x : ℝ) 2 hx0 two_pos
  simp only [ofReal_natCast, ofReal_ofNat] at hK hP hC
  rw [show vdx x m = _ from funext (viN x m), integral_sub (hK.const_mul _) hP,
    integral_const_mul, mul_sub, mul_left_comm, hC,
    max_eq_right (show (0 : ℝ) ≤ 1 - 1 / (x : ℝ) by
      rw [sub_nonneg, div_le_one hx0]; exact hx1)]
  rcases m with _ | _ | m
  · have hR := veJ (x : ℝ) 2 hx1 two_pos (-((0 : ℕ) : ℂ)) (by simp)
    simp only [ofReal_natCast, ofReal_ofNat] at hR
    rw [hR]
    simp only [tau, ↓reduceIte]
    push_cast
    rw [cpow_neg_one]
    ring
  · have hR := vga (x : ℝ) 2 hx1 two_pos (-((0 + 1 : ℕ) : ℂ)) (by simp)
    simp only [ofReal_natCast, ofReal_ofNat] at hR
    rw [hR]
    simp only [tau, ↓reduceIte, zero_add, one_ne_zero]
    push_cast
    rw [cpow_neg_one]
    ring
  · have hM : (2 : ℝ) ≤ ((m + 1 + 1 : ℕ) : ℝ) := by push_cast; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have hw0 : -((m + 1 + 1 : ℕ) : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hw1 : -((m + 1 + 1 : ℕ) : ℂ) ≠ -1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hR := veO (x : ℝ) 2 hx1 two_pos _ (hw_m (m + 1 + 1)) hw0 hw1
    simp only [ofReal_natCast, ofReal_ofNat] at hR
    rw [hR]
    have h0 : m + 1 + 1 ≠ 0 := by omega
    have h1 : m + 1 + 1 ≠ 1 := by omega
    simp only [tau, h0, h1, ↓reduceIte]
    rw [cpow_neg, cpow_natCast, cpow_neg_one]
    push_cast
    have e1 : (m : ℂ) + 1 + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have e2 : (m : ℂ) + 1 + 1 - 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have e3 : (2 : ℂ) + ((m : ℂ) + 1 + 1) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have e4 : -((m : ℂ) + 1 + 1) + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have e5 : 1 + -((m : ℂ) + 1 + 1) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have e6 : (x : ℂ) ^ (m + 1 + 1) ≠ 0 := pow_ne_zero _ hxC
    simp only [one_div, inv_pow]
    field_simp
    ring
lemma viG (x m : ℕ) (t : ℝ) :
    ‖vdx x m t‖ ≤ 1 / (2 + m) * ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
      (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ := by
  have hm : (0 : ℝ) ≤ m := m.cast_nonneg
  have h0 : (2 : ℂ) + t * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h1 : (2 : ℂ) + t * I + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : (2 : ℂ) + t * I + m ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h3 : (2 : ℂ) + m ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have e : vdx x m t = (((2 : ℂ) + t * I - 2) / ((2 : ℂ) + t * I)) * (1 / (2 + (m : ℂ))) *
      ((x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))) := by
    unfold vdx
    rw [sub_neg_eq_add]
    field_simp
    ring
  rw [e, norm_mul, norm_mul]
  have hq : ‖((2 : ℂ) + t * I - 2) / ((2 : ℂ) + t * I)‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.mpr h0)]
    have : (2 : ℂ) + t * I - 2 = t * I := by ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have := Complex.abs_im_le_norm ((2 : ℂ) + t * I)
    simpa using this
  have hn : ‖1 / (2 + (m : ℂ))‖ = 1 / (2 + m) := by
    rw [norm_div, norm_one]
    congr 1
    exact_mod_cast Complex.norm_natCast (2 + m)
  rw [hn]
  have := norm_nonneg ((x : ℂ) ^ ((2 : ℂ) + t * I) /
      (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1)))
  have : 0 ≤ 1 / (2 + (m : ℝ)) := by positivity
  calc _ ≤ 1 * (1 / (2 + (m : ℝ))) * ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
      (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ := by gcongr
    _ = _ := by ring
lemma viX (k m : ℕ) (hkm : k ≤ m) :
    (1 + (m : ℝ)) ^ (-(1 / 2 : ℝ)) / (2 + m) ≤ ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hkm' : (k : ℝ) ≤ m := by exact_mod_cast hkm
  have e : ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) = ((k : ℝ) + 1) ^ (-(1 / 2 : ℝ)) / ((k : ℝ) + 1) := by
    rw [show (-(3 / 2 : ℝ)) = -(1 / 2) + (-1) by norm_num, Real.rpow_add hk, Real.rpow_neg_one]
    ring
  rw [e]
  apply div_le_div₀ (by positivity) _ hk (by linarith)
  exact Real.rpow_le_rpow_of_nonpos hk (by linarith) (by norm_num)
lemma vhV : Summable fun k : ℕ => ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1))
  simpa using this
end Erdos985.Analytic.BoundsAux
namespace Erdos985.Analytic
open BoundsAux
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic
open Complex ArithmeticFunction MeasureTheory
open scoped Classical
variable {N : ℕ} [NeZero N]
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic.ZeroSumAux
open Complex ArithmeticFunction
open scoped Classical
variable {N : ℕ} [NeZero N]
end Erdos985.Analytic.ZeroSumAux
end
section
namespace Erdos985.Analytic.ZeroSumAux
open Complex
variable {N : ℕ} [NeZero N]
end Erdos985.Analytic.ZeroSumAux
end
section
namespace Erdos985.Analytic
open Complex ArithmeticFunction MeasureTheory
open scoped Classical
variable {N : ℕ} [NeZero N]
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic
open Complex ArithmeticFunction MeasureTheory
open scoped Classical
variable {N : ℕ} [NeZero N]
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic.PrincipalAux
open Complex
theorem vbv {s : ℂ} (hs : 1 ≤ s.re) :
    completedRiemannZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
  intro h
  apply riemannZeta_ne_zero_of_one_le_re hs
  rw [riemannZeta_def_of_ne_zero hs0, h, zero_div]
theorem vfo : van 1 = 1 := by simp [van]
theorem vbJ {ρ : ℂ} (hρ : van ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  have hρ0 : ρ ≠ 0 := fun h => by rw [h, vcj] at hρ; exact one_ne_zero hρ
  have hρ1 : ρ ≠ 1 := fun h => by rw [h, vfo] at hρ; exact one_ne_zero hρ
  have hΛ : completedRiemannZeta ρ = 0 := by
    rw [vgV hρ0 hρ1] at hρ
    rcases mul_eq_zero.mp hρ with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hρ0
      · exact absurd (sub_eq_zero.mp h) hρ1
    · exact h
  constructor
  · by_contra h
    push Not at h
    apply vbv (s := 1 - ρ) (by simp; linarith)
    rw [completedRiemannZeta_one_sub, hΛ]
  · by_contra h
    push Not at h
    exact vbv h hΛ
theorem veB {ρ : ℂ} (hρ : van ρ = 0) : analyticOrderNatAt van ρ ≠ 0 := by
  have han : AnalyticOnNhd ℂ van Set.univ :=
    vbs.differentiableOn.analyticOnNhd isOpen_univ
  have h0 : analyticOrderAt van 0 ≠ ⊤ := by
    rw [(analyticOrderAt_eq_zero.2 (Or.inr (by rw [vcj]; exact one_ne_zero)))]
    exact ENat.zero_ne_top
  have htop := han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ 0) (Set.mem_univ ρ) h0
  intro hm
  have := Nat.cast_analyticOrderNatAt htop
  rw [hm, Nat.cast_zero, eq_comm, analyticOrderAt_eq_zero] at this
  rcases this with h | h
  · exact h (han ρ (Set.mem_univ _))
  · exact h hρ
theorem vej : Countable {ρ : ℂ // van ρ = 0} := by
  have hs := (vcM vbs (by rw [vcj]; exact one_ne_zero)
    vek).1 1 one_pos
  rw [← Set.countable_univ_iff]
  convert hs.countable_support
  symm
  rw [Function.support_eq_univ]
  intro ρ
  have hm := veB ρ.2
  have hρ0 : (ρ : ℂ) ≠ 0 := fun h => (vbJ ρ.2).1.ne' (by simp [h])
  have : 0 < ‖(ρ : ℂ)‖ := norm_pos_iff.2 hρ0
  positivity
theorem vfk (s : ℂ) :
    vaR (1 : DirichletCharacter ℂ 1) s
      = -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma (s / 2) := by
  simp [vaR, vbK, DirichletCharacter.Even, MulChar.one_apply (isUnit_of_subsingleton _)]
theorem vcv {s : ℂ} (hs : 1 < s.re) :
    deriv riemannZeta s / riemannZeta s
      = deriv van s / van s - 1 / s - 1 / (s - 1)
          - vaR (1 : DirichletCharacter ℂ 1) s := by
  have hs0 : 0 < s.re := by linarith
  have hne0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
  have hne1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  have hne1' : s - 1 ≠ 0 := sub_ne_zero.mpr hne1
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hγ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs0
  have hev : van =ᶠ[nhds s] fun w => w * (w - 1) * (Gammaℝ w * riemannZeta w) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show s ∈ {w : ℂ | 1 < w.re} from hs)] with w hw
    have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw; linarith
    have hw1 : w ≠ 1 := fun h => by rw [h] at hw; simp at hw
    rw [vgV hw0 hw1, riemannZeta_def_of_ne_zero hw0,
      mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos (by linarith))]
  have hp : HasDerivAt (fun w : ℂ => w * (w - 1)) (1 * (s - 1) + s * 1) s :=
    (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)
  have hd := hp.fun_mul ((StepAAux.hasDerivAt_Gammaℝ hs0).fun_mul
    (differentiableAt_riemannZeta hne1).hasDerivAt)
  rw [hev.deriv_eq, hd.deriv, hev.eq_of_nhds, vfk]
  field_simp
  ring
end Erdos985.Analytic.PrincipalAux
end
section
namespace Erdos985.Analytic
open Complex ArithmeticFunction MeasureTheory IdentityAux
theorem vbJ {ρ : ℂ} (hρ : van ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 :=
  PrincipalAux.vbJ hρ
theorem vgr (x : ℕ) (hx : 1 ≤ x) :
    (((∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) : ℝ)) : ℂ)
      = (∑' ρ : {ρ : ℂ // van ρ = 0}, (analyticOrderNatAt van ρ : ℂ) * vcY x ρ)
        + vbi (1 : DirichletCharacter ℂ 1) x
        + ((x : ℂ) / 2 + (Real.log x : ℂ) - 7 / 2 + 3 / (x : ℂ))
        - (1 - 1 / (x : ℂ)) * (deriv riemannZeta 2 / riemannZeta 2) := by
  classical
  set G := vaR (1 : DirichletCharacter ℂ 1) with hG
  set D : ℂ → ℂ := fun z => deriv van z / van z with hD
  set m : {ρ : ℂ // van ρ = 0} → ℂ := fun ρ => (analyticOrderNatAt van ρ : ℂ) with hm
  set c2 : ℂ := deriv riemannZeta 2 / riemannZeta 2 with hc2
  have := PrincipalAux.vej
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_pos.ne')
  have hsre : ∀ t : ℝ, ((2 : ℂ) + t * I).re = 2 := fun t => by simp
  have hs_cont : Continuous fun t : ℝ => (2 : ℂ) + t * I :=
    continuous_const.add (continuous_ofReal.mul continuous_const)
  have hΛd : Differentiable ℂ van := vbs
  have hΛne : ∀ z : ℂ, 1 ≤ z.re → van z ≠ 0 := fun z hz h => by
    linarith [(vbJ h).2]
  obtain ⟨hsum_ε, b, hb⟩ := vcM hΛd (by rw [vcj]; exact one_ne_zero)
    vek
  have hzre : ∀ ρ : {ρ : ℂ // van ρ = 0}, 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 :=
    fun ρ => vbJ ρ.2
  let F : {ρ : ℂ // van ρ = 0} → ℝ → ℂ := fun ρ t => m ρ * vbC x ρ t
  have hF_int : ∀ ρ, Integrable (F ρ) := fun ρ =>
    (veL hx0 (by linarith [hzre ρ])).const_mul _
  obtain ⟨C, hC0, hC⟩ := vfu
  have hF_sum : Summable fun ρ => ∫ t, ‖F ρ t‖ := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun ρ => ?_) ((hsum_ε (1 / 2) (by norm_num)).mul_left (C * (x : ℝ) ^ (2 : ℝ)))
    have hρ0 : (ρ : ℂ) ≠ 0 := fun h => (hzre ρ).1.ne' (by simp [h])
    simp only [F, m, norm_mul, Complex.norm_natCast, integral_const_mul]
    calc (analyticOrderNatAt van ρ : ℝ) * ∫ t, ‖vbC x ρ t‖
        ≤ (analyticOrderNatAt van ρ : ℝ) *
            (C * (x : ℝ) ^ (2 : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hC x hx0 ρ (hzre ρ).2 hρ0) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hF_hasSum : ∀ t : ℝ, HasSum (fun ρ => F ρ t) ((D ((2 : ℂ) + t * I) - D 2) * kern x t) := by
    intro t
    obtain ⟨h1s, h1e⟩ := hb ((2 : ℂ) + t * I) (hΛne _ (by rw [hsre]; norm_num))
    obtain ⟨h2s, h2e⟩ := hb 2 (hΛne _ (by norm_num))
    have := (h1s.hasSum.sub h2s.hasSum).mul_right (kern x t)
    convert this using 1
    all_goals try with_reducible_and_instances rfl
    · funext ρ
      simp only [F, m, vbC]
      ring
    · simp only [hD]
      rw [h1e, h2e]
      ring
  have hD_cont : Continuous fun t : ℝ => D ((2 : ℂ) + t * I) := by
    have hcd : Continuous (deriv van) := (hΛd.contDiff (n := 1)).continuous_deriv le_rfl
    exact (hcd.comp hs_cont).div (hΛd.continuous.comp hs_cont)
      (fun t => hΛne _ (by simp))
  have hF1_int : Integrable fun t : ℝ => (D ((2 : ℂ) + t * I) - D 2) * kern x t :=
    vgD
      ((hD_cont.sub continuous_const).aestronglyMeasurable.mul (vbQ hx0).1)
      hF_int hF_sum hF_hasSum
  have hF1_integral : ∫ t : ℝ, (D ((2 : ℂ) + t * I) - D 2) * kern x t
      = ∑' ρ : {ρ : ℂ // van ρ = 0}, m ρ * (-(2 * Real.pi) * vcY x ρ) := by
    rw [show (fun t : ℝ => (D ((2 : ℂ) + t * I) - D 2) * kern x t)
        = fun t => ∑' ρ, F ρ t from funext fun t => (hF_hasSum t).tsum_eq.symm,
      ← integral_tsum_of_summable_integral_norm hF_int hF_sum]
    refine tsum_congr fun ρ => ?_
    have hρ0 : (ρ : ℂ) ≠ 0 := fun h => (hzre ρ).1.ne' (by simp [h])
    have hρ1 : (ρ : ℂ) ≠ -1 := fun h => by
      have := (hzre ρ).1; rw [h] at this; norm_num at this
    simp only [F]
    rw [integral_const_mul, vho x hx (by linarith [hzre ρ]) hρ0 hρ1]
  set a : ℕ → ℂ := fun n => ((Λ n : ℝ) : ℂ) with ha
  have ha_sum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ (2 : ℝ) := by
    have hs := (LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm
    refine hs.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn, a]
  have hP := PerronKernel.vhU a 2 two_pos ha_sum x hx
  simp only [ofReal_ofNat] at hP
  have hLS : ∀ z : ℂ, 1 < z.re → LSeries a z = -(D z - 1 / z - 1 / (z - 1) - G z) := fun z hz => by
    have h1 := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz
    change LSeries a z = _ at h1
    rw [h1, neg_div, PrincipalAux.vcv hz]
  have hc2' : c2 = D 2 - 1 / 2 - 1 / (2 - 1) - G 2 :=
    PrincipalAux.vcv (by norm_num)
  set H : ℝ → ℂ := fun t => LSeries a ((2 : ℂ) + t * I) * (x : ℂ) ^ ((2 : ℂ) + t * I)
    / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) with hH
  have hH_eq : ∀ t : ℝ, H t = LSeries a ((2 : ℂ) + t * I) * kern x t := fun t => by
    simp only [hH, kern, ofReal_natCast]
    ring
  have hH_int : Integrable H := by
    have hab : LSeries.abscissaOfAbsConv a < ((2 : ℝ) : EReal) := by
      refine lt_of_le_of_lt (LSeriesSummable.abscissaOfAbsConv_le
        (LSeriesSummable_vonMangoldt (s := (3 / 2 : ℂ)) (by norm_num))) ?_
      have : (3 / 2 : ℂ).re = 3 / 2 := by norm_num
      rw [this]
      exact EReal.coe_lt_coe_iff.2 (by norm_num)
    have hcont : Continuous fun t : ℝ => LSeries a ((2 : ℂ) + t * I) :=
      (LSeries_differentiableOn a).continuousOn.comp_continuous hs_cont
        (fun t => by simp only [Set.mem_ofPred_eq, hsre]; exact_mod_cast hab)
    set B := ∑' n, ‖LSeries.term a 2 n‖
    have hbd : ∀ t : ℝ, ‖LSeries a ((2 : ℂ) + t * I)‖ ≤ B := fun t => by
      have hs2 := (LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm
      have heq : (fun n => ‖LSeries.term a ((2 : ℂ) + t * I) n‖)
          = fun n => ‖LSeries.term a 2 n‖ := by
        funext n; rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hsre]; simp
      calc ‖LSeries a ((2 : ℂ) + t * I)‖ ≤ ∑' n, ‖LSeries.term a ((2 : ℂ) + t * I) n‖ :=
            norm_tsum_le_tsum_norm (by rw [heq]; exact hs2)
        _ = B := by rw [heq]
    have : H = fun t : ℝ => LSeries a ((2 : ℂ) + t * I) * kern x t := funext hH_eq
    rw [this]
    refine Integrable.mono' ((vbQ hx0).norm.const_mul B)
      (hcont.aestronglyMeasurable.mul (vbQ hx0).1)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbd t) (norm_nonneg _)
  set P0 : ℝ → ℂ := fun t => ((x : ℝ) : ℂ) ^ ((2 : ℂ) + t * I) /
    (((2 : ℂ) + t * I - 0) * ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) with hP0
  have hP0_int : Integrable P0 := by
    have := vdy (x : ℝ) 2 hx0 two_pos 0 (by simp)
    simp only [ofReal_ofNat] at this
    exact this
  have hP0_integral : ∫ t, P0 t = 2 * Real.pi * ((Real.log x : ℂ) - 1 + (x : ℂ) ^ (-1 : ℂ)) := by
    have h := veJ (x : ℝ) 2 hx1 two_pos 0 rfl
    simp only [ofReal_ofNat, ofReal_natCast] at h
    rw [← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
    simp [hP0]
  have hR1_int : Integrable (vcy x 1) := vdI hx0 (by norm_num)
  have hR1_integral : ∫ t, vcy x 1 t
      = 2 * Real.pi * ((x : ℂ) ^ (1 : ℂ) / (1 * (1 + 1)) - 1 / 1 + (x : ℂ) ^ (-1 : ℂ) / (1 + 1)) := by
    have h := veO (x : ℝ) 2 hx1 two_pos 1 (by norm_num) one_ne_zero (by norm_num)
    simp only [ofReal_ofNat, ofReal_natCast] at h
    rw [← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
    simp [vcy]
  have hF2 : (fun t : ℝ => (G ((2 : ℂ) + t * I) - G 2) * (x : ℂ) ^ ((2 : ℂ) + t * I)
      / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)))
      = fun t : ℝ => H t + (D ((2 : ℂ) + t * I) - D 2) * kern x t - P0 t - vcy x 1 t
          + (c2 + 3 / 2) * kern x t := by
    funext t
    have hz : 1 < ((2 : ℂ) + t * I).re := by rw [hsre]; norm_num
    have h0 := vgM t
    have h1 := ves t
    have h2 := vfj (ρ := 1) (by norm_num) t
    rw [hH_eq, hLS _ hz, hc2']
    simp only [kern, vcy, hP0, ofReal_natCast, sub_zero]
    field_simp
    ring
  have hgamma : vbi (1 : DirichletCharacter ℂ 1) x = (1 / (2 * Real.pi) : ℂ) *
      ((∫ t, H t) + (∫ t : ℝ, (D ((2 : ℂ) + t * I) - D 2) * kern x t)
        - (∫ t, P0 t) - (∫ t, vcy x 1 t) + (c2 + 3 / 2) * ∫ t, kern x t) := by
    unfold vbi
    rw [← hG, hF2, integral_add _ ((vbQ hx0).const_mul _),
      integral_sub _ hR1_int, integral_sub _ hP0_int, integral_add hH_int hF1_int,
      integral_const_mul]
    · exact hH_int.add hF1_int
    · exact (hH_int.add hF1_int).sub hP0_int
    · exact ((hH_int.add hF1_int).sub hP0_int).sub hR1_int
  have hbach : (((∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) : ℝ)) : ℂ)
      = ∑ n ∈ Finset.Ioo 0 x, a n * (1 - (n : ℂ) / x) := by
    push_cast
    symm
    refine Finset.sum_subset (fun n hn => ?_) fun n hn hn' => ?_
    · rw [Finset.mem_Ioo] at hn; rw [Finset.mem_range]; omega
    · have : n = 0 := by rw [Finset.mem_Ioo] at hn'; rw [Finset.mem_range] at hn; omega
      subst this
      simp [a]
  have hbach' : (((∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) : ℝ)) : ℂ)
      = (1 / (2 * Real.pi) : ℂ) * ∫ t, H t := by
    rw [hbach, hP]
  have hK := vgI hx1
  have htsum : ∑' ρ : {ρ : ℂ // van ρ = 0}, m ρ * (-(2 * Real.pi) * vcY x ρ)
      = -(2 * Real.pi) * ∑' ρ : {ρ : ℂ // van ρ = 0}, m ρ * vcY x ρ := by
    rw [← tsum_mul_left]
    exact tsum_congr fun ρ => by ring
  rw [hgamma, hbach', hF1_integral, htsum, hK, hP0_integral, hR1_integral]
  simp only [ofReal_natCast, cpow_one, cpow_neg_one]
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  field_simp
  ring
end Erdos985.Analytic
end
section
open Complex MeasureTheory Filter Topology ArithmeticFunction
namespace Erdos985.Analytic.PrincipalAux
open BoundsAux
theorem vgN (x : ℝ) (hx : 1 ≤ x) :
    Summable (fun k : ℕ => tau x (2 * k)) ∧
      1 - 3 / (2 * x) ≤ ∑' k : ℕ, tau x (2 * k) + Real.log x ∧
      ∑' k : ℕ, tau x (2 * k) + Real.log x ≤ 1 := by
  have hup : ∀ k : ℕ, tau x (2 * (k + 1)) ≤
      (3 * (1 / x) - 1) / 2 * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := fun k =>
    vhB x hx k
  have hlo : ∀ k : ℕ, -(1 / 2) * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) ≤ tau x (2 * (k + 1)) :=
    fun k => vjg x hx k (2 * (k + 1)) le_rfl
  have hS : Summable (fun k : ℕ => tau x (2 * k)) := by
    simpa using (vih x hx 0 (by norm_num)).1
  have hg : Summable (fun k : ℕ => tau x (2 * (k + 1))) :=
    (summable_nat_add_iff (f := fun k : ℕ => tau x (2 * k)) 1).mpr hS
  refine ⟨hS, ?_⟩
  rw [hS.tsum_eq_zero_add]
  have hle : ∑' k : ℕ, tau x (2 * (k + 1)) ≤ (3 * (1 / x) - 1) / 2 := by
    have := Summable.tsum_le_tsum hup hg (vdh.summable.mul_left _)
    rwa [tsum_mul_left, vdh.tsum_eq, mul_one] at this
  have hge : -(1 / 2) ≤ ∑' k : ℕ, tau x (2 * (k + 1)) := by
    have := Summable.tsum_le_tsum hlo (vdh.summable.mul_left _) hg
    rwa [tsum_mul_left, vdh.tsum_eq, mul_one] at this
  have h0 : tau x (2 * 0) = (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) := by simp [tau]
  rw [h0]
  have e : 3 / (2 * x) = 3 / 2 * (1 / x) := by field_simp
  rw [e]
  constructor <;> linarith
theorem vgx {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℕ)
    (hx : 1 ≤ x) :
    vbi χ x = ((∑' k : ℕ, tau x (2 * k + vbK χ) : ℝ) : ℂ) := by
  obtain ⟨C, hC0, hC⟩ := vcQ (δ := 1) (θ := 1 / 2) one_pos
    (by norm_num) (by norm_num)
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hsum : ∀ t : ℝ, (vaR χ (2 + t * I) - vaR χ 2) *
      (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) =
      ∑' k : ℕ, vdx x (2 * k + vbK χ) t := by
    intro t
    have hs : 1 < ((2 : ℂ) + t * I).re := by simp
    exact (((vgE χ hs).mul_right _).div_const _).tsum_eq.symm
  have hnorm : ∀ m : ℕ, ∫ t, ‖vdx x m t‖ ≤
      C * (x : ℝ) ^ (2 : ℝ) * ((1 + (m : ℝ)) ^ (-(1 / 2 : ℝ)) / (2 + m)) := by
    intro m
    obtain ⟨hQi, hQb⟩ := hC x 2 hx0 two_pos (-(m : ℂ)) (by
      simp only [neg_re, natCast_re]; norm_num; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
    simp only [ofReal_natCast, ofReal_ofNat, norm_neg, Complex.norm_natCast] at hQi hQb
    calc ∫ t : ℝ, ‖vdx x m t‖ ≤ ∫ t : ℝ, 1 / (2 + (m : ℝ)) * ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
          (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ :=
          integral_mono (vfK x hx m).norm (hQi.norm.const_mul _)
            (fun t => viG x m t)
      _ = 1 / (2 + (m : ℝ)) * ∫ t : ℝ, ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
          (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ := integral_const_mul _ _
      _ ≤ 1 / (2 + (m : ℝ)) * (C * (x : ℝ) ^ (2 : ℝ) * (1 + (m : ℝ)) ^ (-(1 / 2 : ℝ))) := by
          gcongr
      _ = _ := by ring
  have hsumm : Summable (fun k : ℕ => ∫ t, ‖vdx x (2 * k + vbK χ) t‖) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg (fun t => norm_nonneg _))
      (fun k => (hnorm _).trans ?_) (vhV.mul_left (C * (x : ℝ) ^ (2 : ℝ)))
    gcongr
    exact viX k _ (by omega)
  have hgp : vbi χ x = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, ∑' k : ℕ, vdx x (2 * k + vbK χ) t := by
    unfold vbi
    congr 1
    congr 1
    funext t
    exact hsum t
  rw [hgp, ← integral_tsum_of_summable_integral_norm (fun k => vfK x hx _) hsumm,
    ← tsum_mul_left]
  simp_rw [vik x hx]
  rw [← Complex.ofReal_tsum]
lemma viW : vbK (1 : DirichletCharacter ℂ 1) = 0 := by
  simp [vbK, DirichletCharacter.Even, MulChar.one_apply (isUnit_of_subsingleton _)]
theorem vgC (x : ℕ) (hx : 1 ≤ x) :
    (vbi (1 : DirichletCharacter ℂ 1) x).im = 0 ∧
    1 - 3 / (2 * (x : ℝ)) ≤ (vbi (1 : DirichletCharacter ℂ 1) x).re + Real.log x ∧
    (vbi (1 : DirichletCharacter ℂ 1) x).re + Real.log x ≤ 1 := by
  rw [vgx _ x hx, viW]
  simp only [add_zero, Complex.ofReal_im, Complex.ofReal_re, true_and]
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  exact (vgN x hx1).2
theorem vfL :
    (deriv riemannZeta 2 / riemannZeta 2).im = 0 ∧
    -0.6 ≤ (deriv riemannZeta 2 / riemannZeta 2).re ∧
      (deriv riemannZeta 2 / riemannZeta 2).re ≤ 0 := by
  have key := LSeries_vonMangoldt_eq_deriv_riemannZeta_div re2
  have e : deriv riemannZeta 2 / riemannZeta 2
      = -((∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
    rw [← veV (fun n => (Λ n : ℝ)), key]; ring
  rw [e]
  simp only [Complex.neg_im, Complex.ofReal_im, neg_zero, Complex.neg_re, Complex.ofReal_re,
    true_and]
  have hS := vjv
  have h0 : 0 ≤ ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2 :=
    tsum_nonneg fun n => div_nonneg vonMangoldt_nonneg (by positivity)
  constructor <;> linarith
end Erdos985.Analytic.PrincipalAux
end
section
open Real Filter Topology
namespace Erdos985.Analytic.PrincipalAux
lemma vhb {a : ℝ} (ha : 0 < a) :
    2 * (1 / (2 * a + 1)) + 2 / 3 * (1 / (2 * a + 1)) ^ 3 ≤ log (1 + a⁻¹) := by
  have h := hasSum_log_one_add_inv ha
  have hle := sum_le_hasSum (Finset.range 2) (fun k _ => by positivity) h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hle
  norm_num at hle
  simpa [one_div, inv_pow] using hle
lemma vjd {a : ℝ} (ha : 0 < a) :
    1 / (2 * a) + 1 / (2 * (a + 1)) + 1 / (8 * (a + 1) ^ 2) - 1 / (8 * a ^ 2)
      ≤ log (1 + a⁻¹) := by
  refine le_trans ?_ (vhb ha)
  rw [← sub_nonneg]
  have e : 2 * (1 / (2 * a + 1)) + 2 / 3 * (1 / (2 * a + 1)) ^ 3 -
      (1 / (2 * a) + 1 / (2 * (a + 1)) + 1 / (8 * (a + 1) ^ 2) - 1 / (8 * a ^ 2))
      = (4 * a ^ 2 + 2 * a + 1) * (4 * a ^ 2 + 6 * a + 3) /
        (24 * a ^ 2 * (a + 1) ^ 2 * (2 * a + 1) ^ 3) := by
    field_simp
    ring
  rw [e]
  positivity
noncomputable def vgZ (m : ℕ) : ℝ :=
  (harmonic (m + 1) : ℝ) - log ((m + 1 : ℕ) : ℝ) - (1 / 2) / ((m + 1 : ℕ) : ℝ)
    + (1 / 8) / ((m + 1 : ℕ) : ℝ) ^ 2
lemma viT : Antitone vgZ := by
  refine antitone_nat_of_succ_le (fun m => ?_)
  have ha : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have key := vjd ha
  have hlog : log (((m + 1 + 1 : ℕ) : ℝ)) =
      log ((m + 1 : ℕ) : ℝ) + log (1 + ((m + 1 : ℕ) : ℝ)⁻¹) := by
    rw [← log_mul ha.ne' (by positivity)]
    congr 1
    field_simp
    push_cast
    ring
  simp only [vgZ]
  rw [hlog, harmonic_succ (m + 1)]
  push_cast at key ⊢
  have : (1 : ℝ) / (2 * (m + 1)) + 1 / (2 * (m + 1 + 1)) + 1 / (8 * (m + 1 + 1) ^ 2)
      - 1 / (8 * (m + 1) ^ 2) =
      ((m : ℝ) + 1 + 1)⁻¹ + 1 / 2 / (m + 1) - 1 / 2 / (m + 1 + 1)
        + 1 / 8 / (m + 1 + 1) ^ 2 - 1 / 8 / (m + 1) ^ 2 := by
    field_simp; ring
  linarith
lemma vii : Tendsto vgZ atTop (𝓝 eulerMascheroniConstant) := by
  have h1 : Tendsto (fun n : ℕ => (harmonic n : ℝ) - log n - (1 / 2) / n + (1 / 8) / (n : ℝ) ^ 2)
      atTop (𝓝 (eulerMascheroniConstant - 0 + 0)) := by
    refine (tendsto_harmonic_sub_log.sub (tendsto_const_div_atTop_nhds_zero_nat _)).add ?_
    have := (tendsto_const_div_atTop_nhds_zero_nat (1 / 8 : ℝ)).comp
      (tendsto_pow_atTop (α := ℕ) (n := 2) (by norm_num))
    refine this.congr (fun n => ?_)
    simp
  rw [sub_zero, add_zero] at h1
  exact (tendsto_add_atTop_iff_nat 1).mpr h1
lemma vjf (m : ℕ) : eulerMascheroniConstant ≤ vgZ m :=
  viT.le_of_tendsto vii m
lemma vfc : eulerMascheroniConstant < 0.5774 := by
  refine lt_of_le_of_lt (vjf 15) ?_
  have hH : (harmonic 16 : ℝ) = 2436559 / 720720 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hl : log ((16 : ℕ) : ℝ) = 4 * log 2 := by
    rw [show ((16 : ℕ) : ℝ) = 2 ^ 4 by norm_num, log_pow]; norm_num
  simp only [vgZ]
  norm_num only [Nat.reduceAdd] at hH hl ⊢
  rw [hH, hl]
  linarith [log_two_gt_d9]
lemma vhQ : (1.144 : ℝ) < Real.log Real.pi := by
  rw [Real.lt_log_iff_exp_lt Real.pi_pos]
  have h1 : Real.exp 1.144 = Real.exp 1 * Real.exp 0.144 := by
    rw [← Real.exp_add]; norm_num
  have h2 := Real.exp_bound' (x := 0.144) (by norm_num) (by norm_num) (n := 4) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at h2
  rw [h1]
  have h3 := Real.exp_one_lt_d9
  have h4 := Real.pi_gt_d4
  have h5 : 0 < Real.exp 0.144 := Real.exp_pos _
  nlinarith
lemma vfx : 2 + eulerMascheroniConstant - Real.log (4 * Real.pi) < 1 / 20 := by
  rw [Real.log_mul (by norm_num) Real.pi_pos.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  have := vfc
  have := vhQ
  have := log_two_gt_d9
  push_cast
  linarith
end Erdos985.Analytic.PrincipalAux
end
section
open Complex
namespace Erdos985.Analytic.PrincipalAux
theorem vip (s : ℂ) : van (1 - s) = van s := by
  simp only [van, completedRiemannZeta₀_one_sub]
  ring
theorem vfm (s : ℂ) :
    HasDerivAt van ((1 * (s - 1) + s * 1) * completedRiemannZeta₀ s
      + s * (s - 1) * deriv completedRiemannZeta₀ s) s := by
  have h := (((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).mul
    (differentiable_completedZeta₀ s).hasDerivAt).add_const 1
  exact h
theorem vfn : deriv van 0 = -completedRiemannZeta₀ 0 := by
  rw [(vfm 0).deriv]; ring
theorem vhM : deriv van 1 = completedRiemannZeta₀ 1 := by
  rw [(vfm 1).deriv]; ring
theorem vbX :
    (2 * completedRiemannZeta₀ 1).re = 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) := by
  rw [completedRiemannZeta₀_one]
  have e : Complex.log (4 * (Real.pi : ℂ)) = ((Real.log (4 * Real.pi) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]; push_cast; rfl
  rw [e]
  simp
  ring
end Erdos985.Analytic.PrincipalAux
end
section
namespace Erdos985.Analytic
open Complex ArithmeticFunction
theorem veM (x : ℕ) (hx : 1 ≤ x) :
    (vbi (1 : DirichletCharacter ℂ 1) x).im = 0 ∧
    1 - 3 / (2 * (x : ℝ)) ≤ (vbi (1 : DirichletCharacter ℂ 1) x).re + Real.log x ∧
    (vbi (1 : DirichletCharacter ℂ 1) x).re + Real.log x ≤ 1 := by
  exact PrincipalAux.vgC x hx
theorem vdX :
    (deriv riemannZeta 2 / riemannZeta 2).im = 0 ∧
    -0.6 ≤ (deriv riemannZeta 2 / riemannZeta 2).re ∧ (deriv riemannZeta 2 / riemannZeta 2).re ≤ 0 := by
  exact PrincipalAux.vfL
end Erdos985.Analytic
end
section
namespace Erdos985.Analytic
open Complex ArithmeticFunction
end Erdos985.Analytic
end
section
namespace Schoenfeld
open Complex Erdos985.Analytic Erdos985.Analytic.PrincipalAux ArithmeticFunction
abbrev vaF := {ρ : ℂ // van ρ = 0}
instance : Countable vaF := vej
noncomputable def mult (ρ : vaF) : ℝ := (analyticOrderNatAt van (ρ : ℂ) : ℝ)
lemma vaJ (ρ : vaF) : 0 ≤ mult ρ := Nat.cast_nonneg _
lemma one_le_mult (ρ : vaF) : 1 ≤ mult ρ := by
  unfold mult
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (veB ρ.2)
theorem vcd (hRH : RiemannHypothesis) {s : ℂ}
    (hs : 1 / 2 < s.re) : van s ≠ 0 := by
  intro h
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hs1 : s ≠ 1 := by rintro rfl; rw [vfo] at h; norm_num at h
  rw [vgV hs0 hs1] at h
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hΛ : completedRiemannZeta s = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hs0
      · exact absurd h hs1'
    · exact h
  have hζ : riemannZeta s = 0 := by rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]
  have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at hs
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have := hRH s hζ htriv hs1
  linarith
theorem vbG (hRH : RiemannHypothesis) (ρ : vaF) : (ρ : ℂ).re = 1 / 2 := by
  have h1 : ¬ 1 / 2 < (ρ : ℂ).re := fun h => vcd hRH h ρ.2
  have h2 : ¬ 1 / 2 < (1 - (ρ : ℂ)).re := fun h =>
    vcd hRH h (by rw [vip]; exact ρ.2)
  simp only [sub_re, one_re] at h2
  linarith
lemma vhd {ρ : ℂ} (hρ : ρ.re = 1 / 2) : ‖ρ‖ ^ 2 = 1 / 4 + ρ.im ^ 2 := by
  rw [← normSq_eq_norm_sq, normSq_apply, hρ]; ring
lemma vgX {ρ : ℂ} (hρ : ρ.re = 1 / 2) : (1 / ρ).re = 1 / 2 / ‖ρ‖ ^ 2 := by
  rw [one_div, inv_re, normSq_eq_norm_sq, hρ]
theorem veN (hRH : RiemannHypothesis) :
    HasSum (fun ρ : vaF => mult ρ / ‖(ρ : ℂ)‖ ^ 2)
      (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) := by
  have hx0 : van 0 ≠ 0 := by rw [vcj]; norm_num
  have hx1 : van 1 ≠ 0 := by rw [vfo]; norm_num
  obtain ⟨-, b, H⟩ := vcM vbs hx0 vek
  obtain ⟨-, e0⟩ := H 0 hx0
  obtain ⟨s1, e1⟩ := H 1 hx1
  have hz : ∀ ρ : vaF, (analyticOrderNatAt van ρ : ℂ) * (1 / (0 - (ρ : ℂ)) + 1 / ρ) = 0 := by
    intro ρ; simp
  simp only [hz, tsum_zero, add_zero, vfn, vcj, div_one] at e0
  rw [vhM, vfo, div_one] at e1
  set T := ∑' ρ : vaF, (analyticOrderNatAt van ρ : ℂ) * (1 / (1 - (ρ : ℂ)) + 1 / ρ) with hT
  have hTv : T = 2 * completedRiemannZeta₀ 1 := by
    have h01 : completedRiemannZeta₀ 0 = completedRiemannZeta₀ 1 := by
      rw [← completedRiemannZeta₀_one_sub]; norm_num
    rw [h01] at e0
    linear_combination e0 - e1
  have hre := Complex.reCLM.hasSum s1.hasSum
  rw [← hT, hTv] at hre
  simp only [Complex.reCLM_apply, vbX] at hre
  refine hre.congr_fun fun ρ => ?_
  have hρ := vbG hRH ρ
  have h1 : (1 - (ρ : ℂ)) = (starRingEnd ℂ) ρ := by
    apply Complex.ext <;> simp [hρ]; norm_num
  rw [mul_re, natCast_re, natCast_im, zero_mul, sub_zero, add_re, h1, one_div,
    inv_re, normSq_conj, vgX hρ, conj_re, normSq_eq_norm_sq, hρ, mult]
  ring
theorem vbc (hRH : RiemannHypothesis) :
    Summable (fun ρ : vaF => mult ρ / ‖(ρ : ℂ)‖ ^ 2) := (veN hRH).summable
theorem vgG (hRH : RiemannHypothesis) :
    ∑' ρ : vaF, mult ρ / ‖(ρ : ℂ)‖ ^ 2 ≤ 1 / 20 := by
  rw [(veN hRH).tsum_eq]; exact vfx.le
theorem vda (hRH : RiemannHypothesis) (ρ : vaF) : 20 ≤ ‖(ρ : ℂ)‖ ^ 2 := by
  have hpos : 0 < ‖(ρ : ℂ)‖ ^ 2 := by
    have : (ρ : ℂ) ≠ 0 := fun h => by have := vbG hRH ρ; rw [h] at this; norm_num at this
    positivity
  have h1 : mult ρ / ‖(ρ : ℂ)‖ ^ 2 ≤ 1 / 20 :=
    ((vbc hRH).le_tsum ρ fun j _ => div_nonneg (vaJ j) (sq_nonneg _)).trans
      (vgG hRH)
  have h2 : 1 / ‖(ρ : ℂ)‖ ^ 2 ≤ 1 / 20 :=
    le_trans (div_le_div_of_nonneg_right (one_le_mult ρ) hpos.le) h1
  rw [div_le_div_iff₀ hpos (by norm_num)] at h2
  linarith
noncomputable def kern (a : ℝ) (ρ : vaF) : ℝ := mult ρ * (a / (a ^ 2 + (ρ : ℂ).im ^ 2))
lemma vhx {a : ℝ} (ha : 0 ≤ a) (ρ : vaF) : 0 ≤ kern a ρ :=
  mul_nonneg (vaJ ρ) (div_nonneg ha (by positivity))
theorem veU (hRH : RiemannHypothesis) {a : ℝ} (ha : 1 / 2 < a) :
    HasSum (kern a) (deriv van ((a + 1 / 2 : ℝ) : ℂ) / van ((a + 1 / 2 : ℝ) : ℂ)).re := by
  set s : ℂ := ((a + 1 / 2 : ℝ) : ℂ) with hs
  have hx0 : van 0 ≠ 0 := by rw [vcj]; norm_num
  have hxs : van s ≠ 0 := vcd hRH (by simp [hs]; linarith)
  obtain ⟨-, b, H⟩ := vcM vbs hx0 vek
  obtain ⟨-, e0⟩ := H 0 hx0
  obtain ⟨ss, es⟩ := H s hxs
  have hz : ∀ ρ : vaF, (analyticOrderNatAt van ρ : ℂ) * (1 / (0 - (ρ : ℂ)) + 1 / ρ) = 0 := by
    intro ρ; simp
  simp only [hz, tsum_zero, add_zero, vfn, vcj, div_one] at e0
  have hb : b.re = -((2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2) := by
    have h01 : completedRiemannZeta₀ 0 = completedRiemannZeta₀ 1 := by
      rw [← completedRiemannZeta₀_one_sub]; norm_num
    have := vbX
    rw [← e0, h01, neg_re]
    rw [show (2 * completedRiemannZeta₀ 1).re = 2 * (completedRiemannZeta₀ 1).re by
      simp [mul_re]] at this
    linarith
  have hre := Complex.reCLM.hasSum ss.hasSum
  simp only [Complex.reCLM_apply] at hre
  have hD : (deriv van s / van s).re - b.re
      = (∑' ρ : vaF, (analyticOrderNatAt van ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)).re := by
    rw [es, add_re]; ring
  have hhalf := (veN hRH).mul_left (1 / 2)
  have hsub := (hre.sub hhalf)
  rw [← hD, hb] at hsub
  convert hsub using 1
  all_goals try with_reducible_and_instances rfl
  · funext ρ
    have hρ := vbG hRH ρ
    have hsr : (s - (ρ : ℂ)).re = a := by simp [hs, hρ]
    have hsi : (s - (ρ : ℂ)).im = -(ρ : ℂ).im := by simp [hs]
    have hns : normSq (s - (ρ : ℂ)) = a ^ 2 + (ρ : ℂ).im ^ 2 := by
      rw [normSq_apply, hsr, hsi]; ring
    simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero, add_re]
    rw [vgX hρ, one_div (s - (ρ : ℂ)), inv_re, hns, hsr, kern, mult]
    ring
  · ring
theorem vfs {s : ℝ} (hs : 1 < s) :
    (deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).im = 0 ∧
      (deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).re ≤ 0 := by
  have hs' : 1 < (s : ℂ).re := by simpa using hs
  have key := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs'
  have hterm : ∀ n : ℕ, LSeries.term (fun n => (Λ n : ℂ)) (s : ℂ) n
      = (((Λ n : ℝ) / (n : ℝ) ^ s : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n)]
      push_cast; rfl
  have hL : LSeries (fun n => (Λ n : ℂ)) (s : ℂ)
      = ((∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ s : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]; exact tsum_congr hterm
  have e : deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)
      = -((∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ s : ℝ) : ℂ) := by
    rw [← hL, key]; ring
  rw [e]
  simp only [Complex.neg_im, Complex.ofReal_im, neg_zero, Complex.neg_re, Complex.ofReal_re,
    true_and, neg_nonpos]
  exact tsum_nonneg fun n => div_nonneg vonMangoldt_nonneg (by positivity)
theorem vig {a : ℝ} (ha : 2 ≤ a) :
    (deriv van ((a + 1 / 2 : ℝ) : ℂ) / van ((a + 1 / 2 : ℝ) : ℂ)).re
      ≤ Real.log a / 2 - Real.log (2 * Real.pi) / 2 + 12 / 5 / a := by
  set s : ℝ := a + 1 / 2 with hsdef
  have hs1 : 1 < s := by linarith
  have hs1' : 1 < (s : ℂ).re := by simpa using hs1
  have e := vcv hs1'
  have hD : deriv van (s : ℂ) / van (s : ℂ) = deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)
      + 1 / (s : ℂ) + 1 / ((s : ℂ) - 1) + vaR (1 : DirichletCharacter ℂ 1) (s : ℂ) := by
    rw [e]; ring
  rw [hD, vfk]
  have hdg : digamma ((s : ℂ) / 2) = ((BoundsAux.rD (s / 2) : ℝ) : ℂ) := by
    rw [show (s : ℂ) / 2 = ((s / 2 : ℝ) : ℂ) by push_cast; ring]
    exact BoundsAux.veS (by linarith)
  have hrD := (BoundsAux.veX (x := s / 2) (by linarith)).2
  obtain ⟨-, hz⟩ := vfs hs1
  rw [hdg]
  have e1 : (1 / (s : ℂ)).re = 1 / s := by
    rw [show (1 / (s : ℂ)) = ((1 / s : ℝ) : ℂ) by push_cast; ring, ofReal_re]
  have e2 : (1 / ((s : ℂ) - 1)).re = 1 / (s - 1) := by
    rw [show (1 / ((s : ℂ) - 1)) = ((1 / (s - 1) : ℝ) : ℂ) by push_cast; ring, ofReal_re]
  have e3 : (-(1 / 2) * ((Real.log Real.pi : ℝ) : ℂ) + 1 / 2 * ((BoundsAux.rD (s / 2) : ℝ) : ℂ)).re
      = -(1 / 2) * Real.log Real.pi + 1 / 2 * BoundsAux.rD (s / 2) := by
    rw [show (-(1 / 2) * ((Real.log Real.pi : ℝ) : ℂ) + 1 / 2 * ((BoundsAux.rD (s / 2) : ℝ) : ℂ))
      = (((-(1 / 2) * Real.log Real.pi + 1 / 2 * BoundsAux.rD (s / 2)) : ℝ) : ℂ) by push_cast; ring,
      ofReal_re]
  rw [add_re, add_re, add_re, e1, e2, e3]
  have ha0 : 0 < a := by linarith
  have hlog2 : Real.log (s / 2) = Real.log s - Real.log 2 :=
    Real.log_div (by linarith) (by norm_num)
  have hls : Real.log s ≤ Real.log a + 1 / (2 * a) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < s / a by positivity)
    rw [Real.log_div (by linarith) ha0.ne'] at h
    have : s / a - 1 = 1 / (2 * a) := by rw [hsdef]; field_simp; ring
    linarith
  have hpi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) Real.pi_pos.ne'
  have hfr : 1 / s + 1 / (s - 1) + 1 / (4 * a) ≤ 12 / 5 / a := by
    rw [hsdef, div_add_div _ _ (by linarith) (by linarith), div_add_div _ _ (by positivity)
      (by positivity), div_le_div_iff₀ (by positivity) ha0]
    nlinarith [mul_pos ha0 ha0, mul_pos (mul_pos ha0 ha0) ha0]
  have : 1 / (2 * a) / 2 = 1 / (4 * a) := by field_simp; ring
  nlinarith
theorem vit (hRH : RiemannHypothesis) {a : ℝ} (ha : 2 ≤ a) :
    ∑' ρ : vaF, kern a ρ ≤ Real.log a / 2 - Real.log (2 * Real.pi) / 2 + 12 / 5 / a := by
  rw [(veU hRH (by linarith)).tsum_eq]; exact vig ha
end Schoenfeld
end
section
namespace Schoenfeld
open Complex Real MeasureTheory
noncomputable def fmin (T : ℝ) (ρ : vaF) : ℝ :=
  mult ρ * min (1 / ‖(ρ : ℂ)‖) (T / ‖(ρ : ℂ)‖ ^ 2)
noncomputable def Vb (a : ℝ) : ℝ := Real.log a / 2 - Real.log (2 * π) / 2 + 12 / 5 / a
noncomputable def Jp (a : ℝ) : ℝ := Real.log a ^ 2 / 4 - Real.log (2 * π) / 2 * Real.log a - 12 / 5 / a
noncomputable def Jb (A : ℝ) : ℝ := Jp A - Jp 2
lemma veT {T : ℝ} (hT : 0 ≤ T) (ρ : vaF) : 0 ≤ fmin T ρ :=
  mul_nonneg (vaJ ρ) (le_min (by positivity) (by positivity))
lemma vhe {T : ℝ} (_hT : 0 ≤ T) (ρ : vaF) :
    fmin T ρ ≤ T * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) := by
  unfold fmin
  calc mult ρ * min (1 / ‖(ρ : ℂ)‖) (T / ‖(ρ : ℂ)‖ ^ 2) ≤ mult ρ * (T / ‖(ρ : ℂ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (vaJ ρ)
    _ = _ := by ring
theorem vdj (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) : Summable (fmin T) :=
  Summable.of_nonneg_of_le (veT hT) (vhe hT) ((vbc hRH).mul_left T)
theorem vhs (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) :
    ∑' ρ, fmin T ρ ≤ T / 20 := by
  calc ∑' ρ, fmin T ρ ≤ ∑' ρ, T * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) :=
        (vdj hRH hT).tsum_le_tsum (vhe hT) ((vbc hRH).mul_left T)
    _ = T * ∑' ρ, mult ρ / ‖(ρ : ℂ)‖ ^ 2 := tsum_mul_left
    _ ≤ T * (1 / 20) := mul_le_mul_of_nonneg_left (vgG hRH) hT
    _ = T / 20 := by ring
theorem vim (hRH : RiemannHypothesis) {T T' : ℝ} (hT : 0 ≤ T) (hTT : T ≤ T') :
    ∑' ρ, fmin T ρ ≤ ∑' ρ, fmin T' ρ := by
  refine (vdj hRH hT).tsum_le_tsum (fun ρ => ?_) (vdj hRH (hT.trans hTT))
  unfold fmin
  gcongr
  exact vaJ ρ
noncomputable def kint (ρ : vaF) (a : ℝ) : ℝ := mult ρ / (a ^ 2 + (ρ : ℂ).im ^ 2)
lemma viK (hRH : RiemannHypothesis) (ρ : vaF) :
    ‖(ρ : ℂ)‖ ^ 2 / 2 ≤ (ρ : ℂ).im ^ 2 := by
  have h1 := vhd (vbG hRH ρ)
  have h2 := vda hRH ρ
  linarith
lemma vfX (hRH : RiemannHypothesis) (ρ : vaF) : 0 < (ρ : ℂ).im ^ 2 := by
  have := viK hRH ρ; have := vda hRH ρ; linarith
lemma viD (hRH : RiemannHypothesis) (ρ : vaF) (A : ℝ) :
    ∫ a in (2 : ℝ)..A, kint ρ a
      = mult ρ * ((Real.arctan (A / |(ρ : ℂ).im|) - Real.arctan (2 / |(ρ : ℂ).im|)) / |(ρ : ℂ).im|) := by
  set g := |(ρ : ℂ).im| with hg
  have hg0 : 0 < g := by
    have := vfX hRH ρ
    rw [hg]; exact abs_pos.mpr (fun h => by rw [h] at this; norm_num at this)
  have hgg : (ρ : ℂ).im ^ 2 = g ^ 2 := by rw [hg, sq_abs]
  have e : ∀ a : ℝ, kint ρ a = mult ρ / g ^ 2 * (1 + (a / g) ^ 2)⁻¹ := by
    intro a; unfold kint; rw [hgg]; field_simp; ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div
    (fun x => (1 + x ^ 2)⁻¹) hg0.ne', integral_inv_one_add_sq, smul_eq_mul]
  field_simp
lemma vhh (hRH : RiemannHypothesis) (ρ : vaF) (a : ℝ) :
    ‖kint ρ a‖ ≤ 2 * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) := by
  have h1 := viK hRH ρ
  have h2 := vda hRH ρ
  have hp : 0 < (ρ : ℂ).im ^ 2 := vfX hRH ρ
  rw [Real.norm_eq_abs, kint, abs_of_nonneg (div_nonneg (vaJ ρ) (by positivity)),
    div_le_iff₀ (by positivity)]
  have hm := vaJ ρ
  rw [show 2 * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) * (a ^ 2 + (ρ : ℂ).im ^ 2)
      = mult ρ * (2 * (a ^ 2 + (ρ : ℂ).im ^ 2) / ‖(ρ : ℂ)‖ ^ 2) by ring]
  refine le_mul_of_one_le_right hm ?_
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg a]
lemma vju {a : ℝ} (ha : 2 ≤ a) : 0 < Vb a := by
  unfold Vb
  have ha0 : 0 < a := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < 2 * π / a by positivity)
  rw [Real.log_div (by positivity) ha0.ne'] at h
  have hpi := Real.pi_lt_d2
  have : 2 * π / a < 6.3 / a := div_lt_div_of_pos_right (by linarith) ha0
  have h2 : 6.3 / a / 2 ≤ 12 / 5 / a + 1 / 2 := by
    rw [div_div, div_add' _ _ _ ha0.ne', div_le_div_iff₀ (by positivity) ha0]; nlinarith
  linarith
lemma vix {a : ℝ} (ha : 0 < a) : HasDerivAt Jp (Vb a / a) a := by
  have hl := Real.hasDerivAt_log ha.ne'
  have h1 := (hl.pow 2).div_const 4
  have h2 := hl.const_mul (Real.log (2 * π) / 2)
  have h3 := (hasDerivAt_inv ha.ne').const_mul (12 / 5 : ℝ)
  have := (h1.sub h2).sub h3
  convert this using 1
  all_goals try with_reducible_and_instances rfl
  · funext x; simp [Jp, div_eq_mul_inv]
  · unfold Vb; field_simp; ring
theorem vhR (A : ℝ) (hA : 2 ≤ A) : ∫ a in (2 : ℝ)..A, Vb a / a = Jb A := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Jp)]
  · rfl
  · intro x hx
    rw [Set.uIcc_of_le hA] at hx
    exact vix (by linarith [hx.1])
  · refine ContinuousOn.intervalIntegrable fun x hx => ?_
    rw [Set.uIcc_of_le hA] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    unfold Vb
    exact ((((Real.continuousAt_log hx0).div_const _).sub continuousAt_const).add
      (continuousAt_const.div continuousAt_id hx0)).div continuousAt_id hx0 |>.continuousWithinAt
theorem vgq (hRH : RiemannHypothesis) {A : ℝ} (hA : 2 ≤ A) :
    Summable (fun ρ : vaF => ∫ a in (2 : ℝ)..A, kint ρ a) ∧
    ∑' ρ : vaF, ∫ a in (2 : ℝ)..A, kint ρ a ≤ Jb A := by
  set f : ℝ → ℝ := fun a => ∑' ρ : vaF, kint ρ a
  have hS := vbc hRH
  have hlim : ∀ a : ℝ, 0 < a → HasSum (fun ρ => kint ρ a) (f a) := by
    intro a ha
    refine Summable.hasSum ?_
    refine Summable.of_norm_bounded (hS.mul_left 2) (fun ρ => vhh hRH ρ a)
  have hsum : HasSum (fun ρ : vaF => ∫ a in (2 : ℝ)..A, kint ρ a) (∫ a in (2 : ℝ)..A, f a) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun ρ _ => 2 * (mult ρ / ‖(ρ : ℂ)‖ ^ 2)) (fun ρ => ?_) (fun ρ => ?_) ?_ ?_ ?_
    · have hd : Continuous fun a : ℝ => a ^ 2 + (ρ : ℂ).im ^ 2 := by fun_prop
      have hne : ∀ a : ℝ, a ^ 2 + (ρ : ℂ).im ^ 2 ≠ 0 := fun a => by
        have := vfX hRH ρ; have := sq_nonneg a; exact ne_of_gt (by linarith)
      have hc : Continuous fun a : ℝ => mult ρ / (a ^ 2 + (ρ : ℂ).im ^ 2) :=
        continuous_const.div hd hne
      exact hc.aestronglyMeasurable
    · exact ae_of_all _ fun a _ => vhh hRH ρ a
    · exact ae_of_all _ fun a _ => hS.mul_left 2
    · exact intervalIntegrable_const
    · refine ae_of_all _ fun a ha => hlim a ?_
      rw [Set.uIoc_of_le hA] at ha; linarith [ha.1]
  refine ⟨hsum.summable, ?_⟩
  rw [hsum.tsum_eq, ← vhR A hA]
  have hfle : ∀ a ∈ Set.Icc (2 : ℝ) A, f a ≤ Vb a / a := by
    intro a ha
    have ha0 : 0 < a := by linarith [ha.1]
    have hk := veU hRH (a := a) (by linarith [ha.1])
    have hk' : HasSum (fun ρ => kint ρ a) ((∑' ρ : vaF, kern a ρ) / a) := by
      rw [hk.tsum_eq]
      convert hk.div_const a using 1
      all_goals try with_reducible_and_instances rfl
      funext ρ; unfold kint kern; field_simp
    rw [(hlim a ha0).unique hk']
    exact div_le_div_of_nonneg_right (vit hRH ha.1) ha0.le
  by_cases hint : IntervalIntegrable f volume 2 A
  · refine intervalIntegral.integral_mono_on hA hint ?_ hfle
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    rw [Set.uIcc_of_le hA] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    unfold Vb
    exact ((((Real.continuousAt_log hx0).div_const _).sub continuousAt_const).add
      (continuousAt_const.div continuousAt_id hx0)).div continuousAt_id hx0 |>.continuousWithinAt
  · rw [intervalIntegral.integral_undef hint]
    refine intervalIntegral.integral_nonneg hA fun x hx => ?_
    exact div_nonneg (vju hx.1).le (by linarith [hx.1])
theorem arctan_le_self {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have h1 := Real.arctan_lt_pi_div_two x
  have h0 : 0 ≤ Real.arctan x := Real.arctan_nonneg.mpr hx
  have := Real.le_tan h0 h1
  rwa [Real.tan_arctan] at this
lemma vhP {x : ℝ} (hx : 10 ≤ x) : π / 2 - 1 / 10 ≤ Real.arctan x := by
  have h0 : 0 < x := by linarith
  have := arctan_inv_of_pos h0
  have h1 : Real.arctan x⁻¹ ≤ x⁻¹ := arctan_le_self (by positivity)
  have h2 : x⁻¹ ≤ 1 / 10 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hx
  linarith
theorem vhq (hRH : RiemannHypothesis) {T : ℝ} (hT : 2 ≤ T) (ρ : vaF) :
    fmin T ρ ≤ 0.9 * (∫ a in (2 : ℝ)..10 * T, kint ρ a) + 2 * kern T ρ + 2.75 * kern 5 ρ := by
  set g := |(ρ : ℂ).im| with hg
  have hp := vfX hRH ρ
  have hn20 := vda hRH ρ
  have hnorm := vhd (vbG hRH ρ)
  have hgg : (ρ : ℂ).im ^ 2 = g ^ 2 := by rw [hg, sq_abs]
  have hg0 : 0 < g := by
    rw [hg]; exact abs_pos.mpr (fun h => by rw [h] at hp; norm_num at hp)
  have hm := vaJ ρ
  have hN : 0 < ‖(ρ : ℂ)‖ := by nlinarith [norm_nonneg (ρ : ℂ)]
  have hgN : g ≤ ‖(ρ : ℂ)‖ := by
    have : g ^ 2 ≤ ‖(ρ : ℂ)‖ ^ 2 := by rw [hnorm, ← hgg]; linarith
    exact (pow_le_pow_iff_left₀ hg0.le hN.le two_ne_zero).mp this
  have hI : 0 ≤ ∫ a in (2 : ℝ)..10 * T, kint ρ a := by
    refine intervalIntegral.integral_nonneg (by linarith) fun a _ => ?_
    unfold kint; positivity
  have hkT : 0 ≤ kern T ρ := vhx (by linarith) ρ
  have hk5 : 0 ≤ kern 5 ρ := vhx (by norm_num) ρ
  unfold fmin
  rcases le_or_gt T g with h1 | h1
  ·
    have : mult ρ * min (1 / ‖(ρ : ℂ)‖) (T / ‖(ρ : ℂ)‖ ^ 2) ≤ 2 * kern T ρ := by
      refine (mul_le_mul_of_nonneg_left (min_le_right _ _) hm).trans ?_
      unfold kern
      rw [hgg]
      have hT0 : 0 < T := by linarith
      rw [show 2 * (mult ρ * (T / (T ^ 2 + g ^ 2))) = mult ρ * (2 * T / (T ^ 2 + g ^ 2)) by ring]
      refine mul_le_mul_of_nonneg_left ?_ hm
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : T ^ 2 + g ^ 2 ≤ 2 * g ^ 2 := by nlinarith
      nlinarith
    linarith
  rcases le_or_gt 6 g with h2 | h2
  ·
    have : mult ρ * min (1 / ‖(ρ : ℂ)‖) (T / ‖(ρ : ℂ)‖ ^ 2) ≤ 0.9 * ∫ a in (2 : ℝ)..10 * T, kint ρ a := by
      refine (mul_le_mul_of_nonneg_left (min_le_left _ _) hm).trans ?_
      rw [viD hRH ρ, ← hg]
      have ha1 : π / 2 - 1 / 10 ≤ Real.arctan (10 * T / g) := by
        apply vhP
        rw [le_div_iff₀ hg0]; nlinarith
      have ha2 : Real.arctan (2 / g) ≤ 1 / 3 := by
        refine (arctan_le_self (by positivity)).trans ?_
        rw [div_le_div_iff₀ hg0 (by norm_num)]; linarith
      have hpi := Real.pi_gt_d2
      have hkey : 1 / ‖(ρ : ℂ)‖ ≤ 0.9 * ((Real.arctan (10 * T / g) - Real.arctan (2 / g)) / g) := by
        rw [mul_div_assoc', le_div_iff₀ hg0, one_div, inv_mul_eq_div, div_le_iff₀ hN]
        nlinarith
      nlinarith
    linarith
  ·
    have : mult ρ * min (1 / ‖(ρ : ℂ)‖) (T / ‖(ρ : ℂ)‖ ^ 2) ≤ 2.75 * kern 5 ρ := by
      refine (mul_le_mul_of_nonneg_left (min_le_left _ _) hm).trans ?_
      unfold kern
      rw [show 2.75 * (mult ρ * (5 / (5 ^ 2 + (ρ : ℂ).im ^ 2)))
        = mult ρ * (2.75 * 5 / (5 ^ 2 + (ρ : ℂ).im ^ 2)) by ring]
      refine mul_le_mul_of_nonneg_left ?_ hm
      rw [div_le_div_iff₀ hN (by positivity), hgg]
      have hg6 : g ^ 2 < 36 := by nlinarith
      have h20 : (4.47 : ℝ) ≤ ‖(ρ : ℂ)‖ := by nlinarith
      nlinarith
    linarith
theorem viO (hRH : RiemannHypothesis) {T : ℝ} (hT : 2 ≤ T) :
    ∑' ρ, fmin T ρ ≤ 0.9 * Jb (10 * T) + 2 * Vb T + 2.75 * Vb 5 := by
  obtain ⟨hIs, hIle⟩ := vgq hRH (A := 10 * T) (by linarith)
  have hKT := (veU hRH (a := T) (by linarith)).summable
  have hK5 := (veU hRH (a := 5) (by norm_num)).summable
  have hsum := ((hIs.mul_left 0.9).add (hKT.mul_left 2)).add (hK5.mul_left 2.75)
  calc ∑' ρ, fmin T ρ
      ≤ ∑' ρ, (0.9 * (∫ a in (2 : ℝ)..10 * T, kint ρ a) + 2 * kern T ρ + 2.75 * kern 5 ρ) :=
        (vdj hRH (by linarith)).tsum_le_tsum (vhq hRH hT) hsum
    _ = 0.9 * (∑' ρ, ∫ a in (2 : ℝ)..10 * T, kint ρ a) + 2 * (∑' ρ, kern T ρ)
          + 2.75 * ∑' ρ, kern 5 ρ := by
        rw [Summable.tsum_add ((hIs.mul_left 0.9).add (hKT.mul_left 2)) (hK5.mul_left 2.75),
          Summable.tsum_add (hIs.mul_left 0.9) (hKT.mul_left 2), tsum_mul_left, tsum_mul_left,
          tsum_mul_left]
    _ ≤ 0.9 * Jb (10 * T) + 2 * Vb T + 2.75 * Vb 5 := by
        have := vit hRH (a := T) hT
        have := vit hRH (a := 5) (by norm_num)
        unfold Vb
        nlinarith
end Schoenfeld
end
section
namespace Schoenfeld
open ArithmeticFunction Real Chebyshev
noncomputable def psi1 (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊t⌋₊ + 1), (Λ n : ℝ) * (t - n)
lemma veY (s : ℝ) {N : ℕ} (hN : ⌊s⌋₊ ≤ N) (f g : ℕ → ℝ)
    (h0 : f 0 = g 0) (h1 : ∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ s → f n = g n)
    (h2 : ∀ n : ℕ, s < n → g n = 0) :
    ∑ n ∈ Finset.range (⌊s⌋₊ + 1), f n = ∑ n ∈ Finset.range (N + 1), g n := by
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega) :
    Finset.range (⌊s⌋₊ + 1) ⊆ Finset.range (N + 1))]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rcases eq_or_ne n 0 with rfl | hn0
    · exact h0
    · simp only [Finset.mem_range] at hn
      exact h1 n hn0 ((Nat.le_floor_iff' hn0).mp (by omega))
  · intro n _ hn
    simp only [Finset.mem_range, not_lt] at hn
    exact h2 n (Nat.lt_of_floor_lt (by omega))
lemma vfW {t : ℝ} {N : ℕ} (hN : ⌊t⌋₊ ≤ N) :
    psi1 t = ∑ n ∈ Finset.range (N + 1), (Λ n : ℝ) * max (t - n) 0 :=
  veY t hN _ _ (by simp)
    (fun n _ hn => by rw [max_eq_left (by linarith)])
    (fun n hn => by rw [max_eq_right (by linarith), mul_zero])
lemma vhG (t : ℝ) : ψ t = ∑ n ∈ Finset.range (⌊t⌋₊ + 1), (Λ n : ℝ) := by
  rw [psi_eq_sum_Icc, Nat.range_succ_eq_Icc_zero]
lemma vgw {t : ℝ} {N : ℕ} (hN : ⌊t⌋₊ ≤ N) :
    ψ t = ∑ n ∈ Finset.range (N + 1), if (n : ℝ) ≤ t then (Λ n : ℝ) else 0 := by
  rw [vhG]
  exact veY t hN _ _ (by simp) (fun n _ hn => by simp [hn])
    (fun n hn => by simp [not_le.mpr hn])
lemma viv (s h : ℝ) (hh : 0 ≤ h) :
    h * ψ s ≤ psi1 (s + h) - psi1 s ∧ psi1 (s + h) - psi1 s ≤ h * ψ (s + h) := by
  have hN : ⌊s⌋₊ ≤ ⌊s + h⌋₊ := Nat.floor_le_floor (by linarith)
  rw [vfW hN, vfW le_rfl, vgw hN, vgw le_rfl,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  constructor
  · refine Finset.sum_le_sum fun n _ => ?_
    have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    split_ifs with hn
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
      exact le_of_eq (by ring)
    · rw [mul_zero, ← mul_sub]
      exact mul_nonneg hΛ (sub_nonneg.mpr (max_le_max (by linarith) le_rfl))
  · refine Finset.sum_le_sum fun n _ => ?_
    have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    split_ifs with hn
    · rw [← mul_sub, mul_comm h]
      refine mul_le_mul_of_nonneg_left ?_ hΛ
      have := le_max_left (s - n) 0
      have := le_max_right (s - n) 0
      have : max (s + h - n) 0 ≤ max (s - n) 0 + h := max_le (by linarith) (by linarith)
      linarith
    · push Not at hn
      rw [max_eq_right (by linarith), max_eq_right (by linarith)]
      simp
lemma vjk (m : ℕ) (hm : 1 ≤ m) :
    psi1 m = m * ∑ n ∈ Finset.range m, (Λ n : ℝ) * (1 - (n : ℝ) / m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  unfold psi1
  rw [Nat.floor_natCast, Finset.sum_range_succ, sub_self, mul_zero, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  field_simp
end Schoenfeld
end
section
namespace Schoenfeld
open Complex Erdos985.Analytic ArithmeticFunction Chebyshev
noncomputable def tA (ρ : vaF) : ℂ := (mult ρ : ℂ) * (2 / ((ρ : ℂ) * (2 - ρ)))
noncomputable def tB (ρ : vaF) : ℂ := (mult ρ : ℂ) * (1 / ((2 - (ρ : ℂ)) * (1 + ρ)))
noncomputable def tW (x : ℕ) (ρ : vaF) : ℂ :=
  (mult ρ : ℂ) * ((x : ℂ) ^ (ρ : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1)))
section Norms
variable {ρ : ℂ}
lemma vdW (hρ : ρ.re = 1 / 2) : 0 < ‖ρ‖ :=
  norm_pos_iff.mpr fun h => by rw [h] at hρ; norm_num at hρ
lemma vgK (hρ : ρ.re = 1 / 2) : ‖ρ‖ ≤ ‖(2 : ℂ) - ρ‖ := by
  rw [BoundsAux.vic hρ]; exact BoundsAux.vch hρ
lemma viy (hρ : ρ.re = 1 / 2) : ‖ρ‖ ≤ ‖(1 : ℂ) + ρ‖ := by
  rw [add_comm]; exact BoundsAux.vch hρ
lemma norm_inv_mul_le {u v : ℂ} (hu : ‖ρ‖ ≤ ‖u‖) (hv : ‖ρ‖ ≤ ‖v‖) (h0 : 0 < ‖ρ‖) (c : ℝ)
    (hc : 0 ≤ c) {w : ℂ} (hw : ‖w‖ ≤ c) : ‖w / (u * v)‖ ≤ c / ‖ρ‖ ^ 2 := by
  rw [norm_div, norm_mul]
  have hu0 : 0 < ‖u‖ := h0.trans_le hu
  have hv0 : 0 < ‖v‖ := h0.trans_le hv
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc ‖w‖ * ‖ρ‖ ^ 2 ≤ c * (‖u‖ * ‖v‖) := by
        rw [sq]; exact mul_le_mul hw (mul_le_mul hu hv h0.le hu0.le) (by positivity) hc
    _ = _ := rfl
end Norms
lemma vid (hRH : RiemannHypothesis) (ρ : vaF) :
    ‖tA ρ‖ ≤ 2 * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) := by
  have hρ := vbG hRH ρ
  unfold tA
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (vaJ ρ)]
  have := norm_inv_mul_le le_rfl (vgK hρ) (vdW hρ) 2 (by norm_num)
    (w := 2) (by simp)
  calc mult ρ * ‖2 / ((ρ : ℂ) * (2 - ρ))‖ ≤ mult ρ * (2 / ‖(ρ : ℂ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left this (vaJ ρ)
    _ = _ := by ring
lemma viV (hRH : RiemannHypothesis) (ρ : vaF) :
    ‖tB ρ‖ ≤ mult ρ / ‖(ρ : ℂ)‖ ^ 2 := by
  have hρ := vbG hRH ρ
  unfold tB
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (vaJ ρ)]
  have := norm_inv_mul_le (vgK hρ) (viy hρ) (vdW hρ) 1
    (by norm_num) (w := 1) (by simp)
  calc mult ρ * ‖1 / ((2 - (ρ : ℂ)) * (1 + ρ))‖ ≤ mult ρ * (1 / ‖(ρ : ℂ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left this (vaJ ρ)
    _ = _ := by ring
lemma viB (x : ℕ) (hx : 1 ≤ x) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ‖(x : ℂ) ^ ρ‖ = √(x : ℝ) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  rw [show (x : ℂ) = ((x : ℝ) : ℂ) by push_cast; rfl, Complex.norm_cpow_eq_rpow_re_of_pos hx0, hρ,
    Real.sqrt_eq_rpow]
lemma viZ (hRH : RiemannHypothesis) (x : ℕ) (hx : 1 ≤ x) (ρ : vaF) :
    ‖tW x ρ‖ ≤ √(x : ℝ) * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) := by
  have hρ := vbG hRH ρ
  unfold tW
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (vaJ ρ)]
  have := norm_inv_mul_le le_rfl (BoundsAux.vch hρ) (vdW hρ) _
    (Real.sqrt_nonneg _) (w := (x : ℂ) ^ (ρ : ℂ)) (viB x hx hρ).le
  calc mult ρ * ‖(x : ℂ) ^ (ρ : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1))‖
      ≤ mult ρ * (√(x : ℝ) / ‖(ρ : ℂ)‖ ^ 2) := mul_le_mul_of_nonneg_left this (vaJ ρ)
    _ = _ := by ring
lemma vhy (hRH : RiemannHypothesis) : Summable tA :=
  Summable.of_norm_bounded ((vbc hRH).mul_left 2) (vid hRH)
lemma vhw (hRH : RiemannHypothesis) : Summable tB :=
  Summable.of_norm_bounded (vbc hRH) (viV hRH)
lemma vgc (hRH : RiemannHypothesis) (x : ℕ) (hx : 1 ≤ x) : Summable (tW x) :=
  Summable.of_norm_bounded ((vbc hRH).mul_left _) (viZ hRH x hx)
noncomputable def vhk : ℝ :=
  (∑' ρ, tA ρ).re - 7 / 2 - (deriv riemannZeta 2 / riemannZeta 2).re
noncomputable def delta : ℝ :=
  3 + (deriv riemannZeta 2 / riemannZeta 2).re - 3 * (∑' ρ, tB ρ).re
noncomputable def Efun (x : ℕ) : ℝ := (vbi (1 : DirichletCharacter ℂ 1) x).re + Real.log x
theorem vhu (hRH : RiemannHypothesis) (x : ℕ) (hx : 1 ≤ x) :
    psi1 x = (x : ℝ) ^ 2 / 2 - x * (∑' ρ, tW x ρ).re + vhk * x + x * Efun x + delta := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hid := vgr x hx
  have hzt : ∀ ρ : vaF, (analyticOrderNatAt van ρ : ℂ) * vcY x ρ
      = tA ρ - (3 / (x : ℂ)) * tB ρ - tW x ρ := by
    intro ρ
    rw [BoundsAux.viR x hx (vbG hRH ρ), tA, tB, tW, mult]
    push_cast
    ring
  simp_rw [hzt] at hid
  rw [Summable.tsum_sub ((vhy hRH).sub ((vhw hRH).mul_left _))
      (vgc hRH x hx), Summable.tsum_sub (vhy hRH) ((vhw hRH).mul_left _),
    tsum_mul_left] at hid
  have hre := congrArg Complex.re hid
  have hL2 : (deriv riemannZeta 2 / riemannZeta 2).im = 0 := (vdX).1
  have hΓ : (vbi (1 : DirichletCharacter ℂ 1) x).im = 0 := (veM x hx).1
  have e3 : (3 / (x : ℂ)) = ((3 / x : ℝ) : ℂ) := by push_cast; rfl
  have e1 : (1 - 1 / (x : ℂ)) = ((1 - 1 / x : ℝ) : ℂ) := by push_cast; rfl
  have e2 : ((x : ℂ) / 2 + (Real.log x : ℂ) - 7 / 2 + 3 / (x : ℂ))
      = (((x : ℝ) / 2 + Real.log x - 7 / 2 + 3 / x : ℝ) : ℂ) := by push_cast; rfl
  rw [e1, e2, e3] at hre
  simp only [Complex.ofReal_re, Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul] at hre
  rw [vjk x hx, hre, vhk, delta, Efun]
  field_simp
  ring
lemma vhf (hRH : RiemannHypothesis) : -2.6 ≤ vhk + 1 ∧ vhk + 1 ≤ -1.8 := by
  have hA : ‖∑' ρ, tA ρ‖ ≤ 2 * (1 / 20) := by
    calc ‖∑' ρ, tA ρ‖ ≤ ∑' ρ, 2 * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) :=
          tsum_of_norm_bounded ((vbc hRH).mul_left 2).hasSum (vid hRH)
      _ = 2 * ∑' ρ, mult ρ / ‖(ρ : ℂ)‖ ^ 2 := tsum_mul_left
      _ ≤ 2 * (1 / 20) := by linarith [vgG hRH]
  have hAr := (Complex.abs_re_le_norm (∑' ρ, tA ρ)).trans hA
  obtain ⟨-, hl1, hl2⟩ := vdX
  rw [abs_le] at hAr
  unfold vhk
  constructor <;> linarith [hAr.1, hAr.2]
lemma vhz (x : ℕ) (hx : 1 ≤ x) : (x : ℝ) - 3 / 2 ≤ x * Efun x ∧ x * Efun x ≤ x := by
  obtain ⟨-, h1, h2⟩ := veM x hx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  unfold Efun
  constructor
  · have := mul_le_mul_of_nonneg_left h1 hx0.le
    have e : (x : ℝ) * (1 - 3 / (2 * x)) = x - 3 / 2 := by field_simp
    linarith
  · nlinarith
lemma vhl {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ‖(b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)‖ ≤ ‖ρ + 1‖ * ((b - a) * √b) := by
  have hρ1 : ρ + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hρ] at this; norm_num at this
  have hI := integral_cpow (a := a) (b := b) (r := ρ) (Or.inl (by rw [hρ]; norm_num))
  have e : (b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1) = (ρ + 1) * ∫ x in a..b, (x : ℂ) ^ ρ := by
    rw [hI]; field_simp
  rw [e, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (f := fun x : ℝ => (x : ℂ) ^ ρ) (C := √b) (fun x hx => by
      rw [Set.uIoc_of_le hab] at hx
      have hx0 : 0 < x := ha.trans hx.1
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, hρ, ← Real.sqrt_eq_rpow]
      exact Real.sqrt_le_sqrt hx.2)
  rw [abs_of_nonneg (by linarith)] at hb
  linarith
lemma vgm {b : ℝ} (hb : 0 < b) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ‖(b : ℂ) ^ (ρ + 1)‖ = b * √b := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hb, add_re, hρ, one_re,
    show (1 / 2 + 1 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hb, Real.rpow_one,
    ← Real.sqrt_eq_rpow]
lemma vha (x : ℕ) (hx : 1 ≤ x) (ρ : ℂ) :
    (x : ℂ) * (x : ℂ) ^ ρ = ((x : ℝ) : ℂ) ^ (ρ + 1) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  rw [show ((x : ℝ) : ℂ) = (x : ℂ) by push_cast; rfl, cpow_add _ _ hx0, cpow_one, mul_comm]
lemma viY (hRH : RiemannHypothesis) (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) (ρ : vaF) :
    ‖((a + h : ℕ) : ℂ) * tW (a + h) ρ - (a : ℂ) * tW a ρ‖
      ≤ h * √((a + h : ℕ) : ℝ) * fmin (2 * ((a + h : ℕ) : ℝ) / h) ρ := by
  have hρ := vbG hRH ρ
  set b : ℕ := a + h with hbdef
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hbR : (b : ℝ) = a + h := by rw [hbdef]; push_cast; ring
  have hb0 : (0 : ℝ) < b := by rw [hbR]; linarith
  have hab : (a : ℝ) ≤ b := by rw [hbR]; linarith
  have hN := vdW hρ
  have hN1 := BoundsAux.vch hρ
  have e : ((b : ℕ) : ℂ) * tW b ρ - (a : ℂ) * tW a ρ
      = (mult ρ : ℂ) * ((((b : ℝ) : ℂ) ^ ((ρ : ℂ) + 1) - ((a : ℝ) : ℂ) ^ ((ρ : ℂ) + 1))
        / ((ρ : ℂ) * ((ρ : ℂ) + 1))) := by
    unfold tW
    rw [← vha b (by omega), ← vha a ha]
    ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (vaJ ρ), norm_div, norm_mul]
  set D := ‖((b : ℝ) : ℂ) ^ ((ρ : ℂ) + 1) - ((a : ℝ) : ℂ) ^ ((ρ : ℂ) + 1)‖
  have hD1 : D ≤ ‖(ρ : ℂ) + 1‖ * (h * √(b : ℝ)) := by
    have := vhl ha0 hab hρ
    rwa [show (b : ℝ) - a = h by rw [hbR]; ring] at this
  have hD2 : D ≤ 2 * (b * √(b : ℝ)) := by
    refine (norm_sub_le _ _).trans ?_
    rw [vgm hb0 hρ, vgm ha0 hρ]
    have : (a : ℝ) * √(a : ℝ) ≤ b * √(b : ℝ) :=
      mul_le_mul hab (Real.sqrt_le_sqrt hab) (Real.sqrt_nonneg _) hb0.le
    linarith
  have hN10 : 0 < ‖(ρ : ℂ) + 1‖ := hN.trans_le hN1
  unfold fmin
  rw [show (h : ℝ) * √(b : ℝ) * (mult ρ * min (1 / ‖(ρ : ℂ)‖) (2 * b / h / ‖(ρ : ℂ)‖ ^ 2))
      = mult ρ * (h * √(b : ℝ) * min (1 / ‖(ρ : ℂ)‖) (2 * b / h / ‖(ρ : ℂ)‖ ^ 2)) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (vaJ ρ)
  rw [mul_min_of_nonneg _ _ (by positivity), le_min_iff]
  constructor
  · rw [div_le_iff₀ (by positivity)]
    calc D ≤ ‖(ρ : ℂ) + 1‖ * (h * √(b : ℝ)) := hD1
      _ = h * √(b : ℝ) * (1 / ‖(ρ : ℂ)‖) * (‖(ρ : ℂ)‖ * ‖(ρ : ℂ) + 1‖) := by field_simp
  · rw [div_le_iff₀ (by positivity)]
    calc D ≤ 2 * (b * √(b : ℝ)) := hD2
      _ = h * √(b : ℝ) * (2 * b / h / ‖(ρ : ℂ)‖ ^ 2) * (‖(ρ : ℂ)‖ * ‖(ρ : ℂ)‖) := by
          field_simp
      _ ≤ h * √(b : ℝ) * (2 * b / h / ‖(ρ : ℂ)‖ ^ 2) * (‖(ρ : ℂ)‖ * ‖(ρ : ℂ) + 1‖) := by
          gcongr
theorem vhL (hRH : RiemannHypothesis) (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    |((a + h : ℕ) : ℝ) * (∑' ρ, tW (a + h) ρ).re - (a : ℝ) * (∑' ρ, tW a ρ).re|
      ≤ h * √((a + h : ℕ) : ℝ) * ∑' ρ, fmin (2 * ((a + h : ℕ) : ℝ) / h) ρ := by
  have hT : 0 ≤ 2 * ((a + h : ℕ) : ℝ) / h := by positivity
  have hsF := (vdj hRH hT).mul_left (h * √((a + h : ℕ) : ℝ))
  have e : ((a + h : ℕ) : ℝ) * (∑' ρ, tW (a + h) ρ).re - (a : ℝ) * (∑' ρ, tW a ρ).re
      = (∑' ρ, (((a + h : ℕ) : ℂ) * tW (a + h) ρ - (a : ℂ) * tW a ρ)).re := by
    rw [Summable.tsum_sub ((vgc hRH _ (by omega)).mul_left _)
      ((vgc hRH a ha).mul_left _), tsum_mul_left, tsum_mul_left, Complex.sub_re]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  rw [e]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [← tsum_mul_left]
  exact tsum_of_norm_bounded hsF.hasSum (viY hRH a h ha hh)
theorem vfY (hRH : RiemannHypothesis) (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    |psi1 ((a + h : ℕ) : ℝ) - psi1 a - ((((a + h : ℕ) : ℝ) ^ 2 - (a : ℝ) ^ 2) / 2
        + (vhk + 1) * h)|
      ≤ 3 / 2 + h * √((a + h : ℕ) : ℝ) * ∑' ρ, fmin (2 * ((a + h : ℕ) : ℝ) / h) ρ := by
  have hb := vhu hRH (a + h) (by omega)
  have ha' := vhu hRH a ha
  have hZ := vhL hRH a h ha hh
  obtain ⟨eb1, eb2⟩ := vhz (a + h) (by omega)
  obtain ⟨ea1, ea2⟩ := vhz a ha
  have hbR : ((a + h : ℕ) : ℝ) = a + h := by push_cast; ring
  rw [hb, ha']
  rw [abs_le] at hZ ⊢
  rw [hbR] at eb1 eb2 hZ ⊢
  constructor <;> nlinarith [hZ.1, hZ.2]
theorem viz (hRH : RiemannHypothesis) (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    ψ a - a ≤ h / 2 - 1.8 + 1.5 / h
      + √((a + h : ℕ) : ℝ) * ∑' ρ, fmin (2 * ((a + h : ℕ) : ℝ) / h) ρ := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hd := (viv (a : ℝ) h hh0.le).1
  have hbR : ((a + h : ℕ) : ℝ) = a + h := by push_cast; ring
  have hB := vfY hRH a h ha hh
  rw [hbR] at hB ⊢
  have hk := vhf hRH
  set F := √((a : ℝ) + h) * ∑' ρ, fmin (2 * ((a : ℝ) + h) / h) ρ
  have hB' := (abs_le.mp hB).2
  have key : (h : ℝ) * (ψ a - a) ≤ h * (h / 2 - 1.8 + 1.5 / h + F) := by
    have e : (h : ℝ) * (1.5 / h) = 3 / 2 := by field_simp; norm_num
    nlinarith
  exact le_of_mul_le_mul_left key hh0
theorem viF (hRH : RiemannHypothesis) (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    ((a + h : ℕ) : ℝ) - ψ ((a + h : ℕ) : ℝ) ≤ h / 2 + 2.6 + 1.5 / h
      + √((a + h : ℕ) : ℝ) * ∑' ρ, fmin (2 * ((a + h : ℕ) : ℝ) / h) ρ := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hd := (viv (a : ℝ) h hh0.le).2
  have hbR : ((a + h : ℕ) : ℝ) = a + h := by push_cast; ring
  have hB := vfY hRH a h ha hh
  rw [hbR] at hB ⊢
  have hk := vhf hRH
  set F := √((a : ℝ) + h) * ∑' ρ, fmin (2 * ((a : ℝ) + h) / h) ρ
  have hB' := (abs_le.mp hB).1
  have key : (h : ℝ) * ((a + h) - ψ (a + h)) ≤ h * (h / 2 + 2.6 + 1.5 / h + F) := by
    have e : (h : ℝ) * (1.5 / h) = 3 / 2 := by field_simp; norm_num
    nlinarith
  exact le_of_mul_le_mul_left key hh0
theorem vgv (hRH : RiemannHypothesis) (x : ℝ) (h : ℕ) (hh : 1 ≤ h)
    (hx : (h : ℝ) + 2 ≤ x) :
    |ψ x - x| ≤ h / 2 + 3.6 + 1.5 / h + √(x + h) * ∑' ρ, fmin (2 * (x + h) / h) ρ := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hx0 : 0 ≤ x := by linarith
  set n := ⌊x⌋₊ with hn
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  have hψ : ψ x = ψ n := by rw [psi_eq_psi_coe_floor]
  have hhn : h + 1 ≤ n := by
    have : ((h + 1 : ℕ) : ℝ) < (n : ℝ) + 1 := by push_cast; linarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  have hmono : ∀ y : ℝ, 0 ≤ y → y ≤ x + h →
      √y * ∑' ρ, fmin (2 * y / h) ρ ≤ √(x + h) * ∑' ρ, fmin (2 * (x + h) / h) ρ := by
    intro y hy hyx
    have hT : 0 ≤ 2 * y / h := by positivity
    exact mul_le_mul (Real.sqrt_le_sqrt hyx) (vim hRH hT (by gcongr))
      (tsum_nonneg (veT hT)) (Real.sqrt_nonneg _)
  rw [hψ, abs_le]
  constructor
  ·
    have hL := viF hRH (n - h) h (by omega) hh
    rw [show n - h + h = n by omega] at hL
    have := hmono n (by positivity) (by linarith)
    linarith
  · have hU := viz hRH n h (by omega) hh
    have := hmono ((n + h : ℕ) : ℝ) (by positivity) (by push_cast; linarith)
    linarith
end Schoenfeld
end
section
namespace Real
end Real
end
section
namespace Schoenfeld
open Chebyshev Real
def vjl (C x₀ : ℝ) : Prop :=
  ∀ x : ℝ, x₀ ≤ x → |ψ x - x| < C * (√x * Real.log x ^ 2)
end Schoenfeld
end
section
namespace Schoenfeld
open Real Chebyshev
lemma vgt : 0.6931471803 < Real.log 2 ∧ Real.log 2 < 0.6931471808 :=
  ⟨Real.log_two_gt_d9, Real.log_two_lt_d9⟩
lemma vhJ {a : ℝ} (k : ℕ) (hk : (2 : ℝ) ^ k ≤ a) :
    k * 0.6931471803 + (1 - 2 ^ k / a) ≤ Real.log a := by
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have ha : 0 < a := h2k.trans_le hk
  have e : Real.log a = Real.log (2 ^ k) + Real.log (a / 2 ^ k) := by
    rw [← Real.log_mul h2k.ne' (by positivity), mul_div_cancel₀ _ h2k.ne']
  have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < a / 2 ^ k by positivity)
  rw [inv_div] at h1
  rw [e, Real.log_pow]
  have := vgt.1
  have : (k : ℝ) * 0.6931471803 ≤ k * Real.log 2 :=
    mul_le_mul_of_nonneg_left this.le (Nat.cast_nonneg k)
  linarith
lemma vdf (hRH : RiemannHypothesis) {a b p q : ℝ} (h k : ℕ) (hh : 1 ≤ h)
    (hha : (h : ℝ) + 2 ≤ a) (_hp : 0 ≤ p) (hpa : p ^ 2 ≤ a) (hq : 0 ≤ q) (hqb : b + h ≤ q ^ 2)
    (hk : (2 : ℝ) ^ k ≤ a) (hl : 0 ≤ k * 0.6931471803 + (1 - 2 ^ k / a))
    (hnum : (h : ℝ) / 2 + 3.6 + 1.5 / h + q * (b + h) / (10 * h)
      < 1 / 8 * (p * (k * 0.6931471803 + (1 - 2 ^ k / a)) ^ 2))
    {x : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    |ψ x - x| < 1 / 8 * (√x * Real.log x ^ 2) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hB := vgv hRH x h hh (by linarith)
  have hT : 0 ≤ 2 * (x + h) / h := by
    have : 0 ≤ x := by linarith
    positivity
  have hF := vhs hRH hT
  have hsq : √(x + h) ≤ q := by
    rw [show q = √(q ^ 2) from (Real.sqrt_sq hq).symm]; exact Real.sqrt_le_sqrt (by linarith)
  have hz : √(x + h) * ∑' ρ, fmin (2 * (x + h) / h) ρ ≤ q * (b + h) / (10 * h) := by
    have hF0 : 0 ≤ ∑' ρ, fmin (2 * (x + h) / h) ρ := tsum_nonneg (veT hT)
    calc √(x + h) * ∑' ρ, fmin (2 * (x + h) / h) ρ ≤ q * (2 * (x + h) / h / 20) :=
          mul_le_mul hsq hF (by positivity) hq
      _ = q * ((x + h) / (10 * h)) := by ring
      _ ≤ q * ((b + h) / (10 * h)) := by gcongr
      _ = q * (b + h) / (10 * h) := by ring
  have hpx : p ≤ √x := Real.le_sqrt_of_sq_le (by linarith)
  have hlx : k * 0.6931471803 + (1 - 2 ^ k / a) ≤ Real.log x :=
    (vhJ k hk).trans (Real.log_le_log (by linarith [pow_pos (two_pos (α := ℝ)) k]) hax)
  have hR : 1 / 8 * (p * (k * 0.6931471803 + (1 - 2 ^ k / a)) ^ 2)
      ≤ 1 / 8 * (√x * Real.log x ^ 2) := by
    gcongr
  linarith
theorem vjp (hRH : RiemannHypothesis) {x : ℝ} (h1 : 73.2 ≤ x) (h2 : x ≤ 262144) :
    |ψ x - x| < 1 / 8 * (√x * Real.log x ^ 2) := by
  rcases le_or_gt x (476/5 : ℝ) with hb | hb
  · exact vdf hRH (a := (366/5 : ℝ)) (b := (476/5 : ℝ)) (p := (171/20 : ℝ)) (q := (1031/100 : ℝ)) 11 6 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (619/5 : ℝ) with hb | hb
  · exact vdf hRH (a := (476/5 : ℝ)) (b := (619/5 : ℝ)) (p := (39/4 : ℝ)) (q := (587/50 : ℝ)) 14 6 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (1857/10 : ℝ) with hb | hb
  · exact vdf hRH (a := (619/5 : ℝ)) (b := (1857/10 : ℝ)) (p := (278/25 : ℝ)) (q := (356/25 : ℝ)) 17 6 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (1393/5 : ℝ) with hb | hb
  · exact vdf hRH (a := (1857/10 : ℝ)) (b := (1393/5 : ℝ)) (p := (681/50 : ℝ)) (q := (867/50 : ℝ)) 22 7 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (4179/10 : ℝ) with hb | hb
  · exact vdf hRH (a := (1393/5 : ℝ)) (b := (4179/10 : ℝ)) (p := (1669/100 : ℝ)) (q := (2117/100 : ℝ)) 30 8 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (4179/5 : ℝ) with hb | hb
  · exact vdf hRH (a := (4179/10 : ℝ)) (b := (4179/5 : ℝ)) (p := (511/25 : ℝ)) (q := (1481/50 : ℝ)) 41 8 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (8358/5 : ℝ) with hb | hb
  · exact vdf hRH (a := (4179/5 : ℝ)) (b := (8358/5 : ℝ)) (p := (2891/100 : ℝ)) (q := (4173/100 : ℝ)) 69 9 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (16716/5 : ℝ) with hb | hb
  · exact vdf hRH (a := (8358/5 : ℝ)) (b := (16716/5 : ℝ)) (p := (1022/25 : ℝ)) (q := (5883/100 : ℝ)) 117 10 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (33432/5 : ℝ) with hb | hb
  · exact vdf hRH (a := (16716/5 : ℝ)) (b := (33432/5 : ℝ)) (p := (2891/50 : ℝ)) (q := (8297/100 : ℝ)) 197 11 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (66864/5 : ℝ) with hb | hb
  · exact vdf hRH (a := (33432/5 : ℝ)) (b := (66864/5 : ℝ)) (p := (8177/100 : ℝ)) (q := (11707/100 : ℝ)) 331 12 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (133728/5 : ℝ) with hb | hb
  · exact vdf hRH (a := (66864/5 : ℝ)) (b := (133728/5 : ℝ)) (p := (2891/25 : ℝ)) (q := (4131/25 : ℝ)) 556 13 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (267456/5 : ℝ) with hb | hb
  · exact vdf hRH (a := (133728/5 : ℝ)) (b := (267456/5 : ℝ)) (p := (8177/50 : ℝ)) (q := (2333/10 : ℝ)) 935 14 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (534912/5 : ℝ) with hb | hb
  · exact vdf hRH (a := (267456/5 : ℝ)) (b := (534912/5 : ℝ)) (p := (5782/25 : ℝ)) (q := (8237/25 : ℝ)) 1572 15 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (1069824/5 : ℝ) with hb | hb
  · exact vdf hRH (a := (534912/5 : ℝ)) (b := (1069824/5 : ℝ)) (p := (8177/25 : ℝ)) (q := (23271/50 : ℝ)) 2644 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  exact vdf hRH (a := (1069824/5 : ℝ)) (b := (262144 : ℝ)) (p := (11564/25 : ℝ)) (q := (51633/100 : ℝ)) 4447 17 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) (by norm_num at h1 ⊢; linarith)
lemma vjb {ℓ ℓp L : ℝ} (h1 : ℓ ≤ ℓp) (h2 : 2 * L ≤ ℓ + ℓp) :
    ℓ ^ 2 / 4 - L / 2 * ℓ ≤ ℓp ^ 2 / 4 - L / 2 * ℓp := by
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
lemma vjt {u l5 L l2 : ℝ} (hu : 12 ≤ u) (hl5 : 0 ≤ l5) (hl5' : l5 ≤ 2 * l2 + 1 / 4)
    (hl2 : 0.6931471803 < l2) (hl2' : l2 < 0.6931471808) (hL : l2 + 1.144 ≤ L) (hL' : L ≤ 3 * l2) :
    0.9 * ((u / 2 + l5 + 1 / 128) ^ 2 / 4 - L / 2 * (u / 2 + l5 + 1 / 128)
        - (l2 ^ 2 / 4 - L / 2 * l2 - 6 / 5))
      + 2 * ((u / 2 - l2 + 1 / 128) / 2 - L / 2 + 0.0141) + 2.75 * (l5 / 2 - L / 2 + 12 / 25)
      ≤ 0.05625 * u ^ 2 + 0.4566 * u + 0.887 := by
  have hA : 0 ≤ (L - (l2 + 1.144)) * (0.45 * (u / 2 + l5 + 1 / 128 - l2) + 2.375) :=
    mul_nonneg (by linarith) (by nlinarith)
  have hB : 0 ≤ u * (2 * l2 + 1 / 4 - l5) := mul_nonneg (by linarith) (by linarith)
  have hC : 0 ≤ (2 * l2 + 1 / 4 - l5) * (2 * l2 + 1 / 4 + l5 + 1 / 64) :=
    mul_nonneg (by linarith) (by linarith)
  have hD : 0 ≤ (3 * l2 - L) * l2 := mul_nonneg (by linarith) (by linarith)
  nlinarith
lemma vjm {s u hR : ℝ} (hs : 512 ≤ s) (hu : 12.47 ≤ u) (hh1 : 4 * s ≤ hR)
    (hh2 : hR < 4 * s + 1) :
    hR / 2 + 3.6 + 1.5 / hR + (s + 2.01) * (0.05625 * u ^ 2 + 0.4566 * u + 0.887)
      < 1 / 8 * (s * u ^ 2) := by
  have hR0 : 0 < hR := by linarith
  have h15 : 1.5 / hR ≤ 0.001 := by rw [div_le_iff₀ hR0]; linarith
  set P := 0.05625 * u ^ 2 + 0.4566 * u + 0.887 with hP
  set Q := u ^ 2 / 8 - P - 2 with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ, hP]; nlinarith
  have hPu : P ≤ 0.13 * u ^ 2 := by rw [hP]; nlinarith
  have hsQ : 512 * Q ≤ s * Q := mul_le_mul_of_nonneg_right hs hQ0
  have h512 : 2.01 * (0.13 * u ^ 2) + 4.101 < 512 * Q := by rw [hQ, hP]; nlinarith
  have : 1 / 8 * (s * u ^ 2) = s * Q + s * P + 2 * s := by rw [hQ]; ring
  nlinarith
set_option maxHeartbeats 1000000 in
theorem vjc (hRH : RiemannHypothesis) {x : ℝ} (hx : 262144 ≤ x) :
    |ψ x - x| < 1 / 8 * (√x * Real.log x ^ 2) := by
  obtain ⟨l2lo, l2hi⟩ := vgt
  have hx0 : 0 < x := by linarith
  set s := √x with hs
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx0.le
  have hs512 : 512 ≤ s := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hs0 : 0 < s := by linarith
  set u := Real.log x with hu
  have hus : Real.log s = u / 2 := by
    rw [hu, ← hs2, Real.log_pow]; push_cast; ring
  have hu0 : 18 * 0.6931471803 ≤ u := by
    have h1 := Real.log_le_log (by norm_num) hx
    have e : Real.log (262144 : ℝ) = 18 * Real.log 2 := by
      rw [show (262144 : ℝ) = 2 ^ 18 by norm_num, Real.log_pow]; norm_num
    linarith
  set h : ℕ := ⌈4 * s⌉₊ with hhdef
  have hh1 : 4 * s ≤ h := Nat.le_ceil _
  have hh2 : (h : ℝ) < 4 * s + 1 := Nat.ceil_lt_add_one (by positivity)
  have hh0 : (0 : ℝ) < h := by linarith
  have hh : 1 ≤ h := by exact_mod_cast (show (1 : ℝ) ≤ h by linarith)
  have hB := vgv hRH x h hh (by nlinarith)
  set T := 2 * (x + h) / h with hTdef
  have hTeq : T = 2 * x / h + 2 := by rw [hTdef]; field_simp
  have hT1 : T ≤ s / 2 + 2 := by
    have : 2 * x / h ≤ s / 2 := by
      rw [div_le_iff₀ hh0, ← hs2]; nlinarith
    linarith
  have hT2 : s / 3 ≤ T := by
    have : s / 3 ≤ 2 * x / h := by
      rw [le_div_iff₀ hh0, ← hs2]; nlinarith
    linarith
  have hT0 : 2 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hF := viO hRH hT0
  have hF0 : 0 ≤ ∑' ρ, fmin T ρ := tsum_nonneg (veT (by linarith))
  set L := Real.log (2 * π) with hL
  have hlpi_lo : (1.144 : ℝ) < Real.log π := Erdos985.Analytic.PrincipalAux.vhQ
  have hlpi_hi : Real.log π < 2 * Real.log 2 := by
    rw [show 2 * Real.log 2 = Real.log (2 ^ 2) by rw [Real.log_pow]; push_cast; ring]
    exact Real.log_lt_log Real.pi_pos (by nlinarith [Real.pi_lt_d2])
  have hLe : L = Real.log 2 + Real.log π := Real.log_mul (by norm_num) Real.pi_pos.ne'
  set l5 := Real.log 5 with hl5
  have hl5_hi : l5 ≤ 2 * Real.log 2 + 1 / 4 := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow] at h1
    norm_num at h1 ⊢; linarith
  have hl5_lo : 0 ≤ l5 := Real.log_nonneg (by norm_num)
  have hlT : Real.log T ≤ u / 2 - Real.log 2 + 1 / 128 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < T / (s / 2) by positivity)
    rw [Real.log_div hTpos.ne' (by positivity), Real.log_div hs0.ne' (by norm_num), hus] at h1
    have : T / (s / 2) - 1 ≤ 1 / 128 := by
      rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]; linarith
    linarith
  set ℓ := Real.log (10 * T) with hℓ
  have hℓe : ℓ = Real.log 2 + l5 + Real.log T := by
    rw [hℓ, Real.log_mul (by norm_num) hTpos.ne', show (10 : ℝ) = 2 * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  have hℓlo : 4 * Real.log 2 ≤ ℓ := by
    have := Real.log_le_log (by norm_num) (show (16 : ℝ) ≤ 10 * T by linarith)
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at this
    push_cast at this; linarith
  set ℓp := u / 2 + l5 + 1 / 128 with hℓpd
  have hℓp : ℓ ≤ ℓp := by rw [hℓe]; linarith
  have hJ : Jb (10 * T) ≤ ℓp ^ 2 / 4 - L / 2 * ℓp - (Real.log 2 ^ 2 / 4 - L / 2 * Real.log 2 - 6 / 5) := by
    unfold Jb Jp
    rw [← hℓ, ← hL]
    have h1 : 0 ≤ 12 / 5 / (10 * T) := by positivity
    have h2 := vjb (L := L) hℓp (by linarith)
    linarith
  have hVT : Vb T ≤ (u / 2 - Real.log 2 + 1 / 128) / 2 - L / 2 + 0.0141 := by
    unfold Vb
    have : 12 / 5 / T ≤ 0.0141 := by
      rw [div_le_iff₀ hTpos]; nlinarith
    linarith
  have hV5 : Vb 5 = l5 / 2 - L / 2 + 12 / 25 := by rw [hl5, hL]; unfold Vb; norm_num
  have hP : ∑' ρ, fmin T ρ ≤ 0.05625 * u ^ 2 + 0.4566 * u + 0.887 := by
    have := vjt (u := u) (l5 := l5) (L := L) (l2 := Real.log 2) (by linarith) hl5_lo hl5_hi
      l2lo l2hi (by linarith) (by linarith)
    rw [hV5] at hF
    rw [hℓpd] at hJ
    linarith
  have hsq : √(x + h) ≤ s + 2.01 := by
    rw [show s + 2.01 = √((s + 2.01) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    have e : (s + 2.01) ^ 2 = s ^ 2 + 4.02 * s + 4.0401 := by ring
    have hle : x + h ≤ (s + 2.01) ^ 2 := by rw [e, hs2]; linarith
    exact Real.sqrt_le_sqrt hle
  have hz : √(x + h) * ∑' ρ, fmin T ρ ≤ (s + 2.01) * (0.05625 * u ^ 2 + 0.4566 * u + 0.887) :=
    mul_le_mul hsq hP hF0 (by linarith)
  have hu1 : (12.47 : ℝ) ≤ u := by linarith
  have hfin := vjm (u := u) hs512 hu1 hh1 hh2
  calc |ψ x - x| ≤ h / 2 + 3.6 + 1.5 / h + √(x + h) * ∑' ρ, fmin T ρ := hB
    _ < 1 / 8 * (√x * u ^ 2) := by linarith
theorem vio (hRH : RiemannHypothesis) : vjl (1 / 8) 73.2 := by
  intro x hx
  rcases le_or_gt x 262144 with h | h
  · exact vjp hRH hx h
  · exact vjc hRH h.le
end Schoenfeld
end

theorem OMA.msl_closed_H1 : OMA.R_Mills_lower_bound_of_RH_R1.H1 :=
  fun hRH x hx => Schoenfeld.vio hRH x hx


-- MERGED VERIFIED STEP Mills.lower_bound_of_RH.R1.H2

-- Step Mills.lower_bound_of_RH.R1.H2: hypothesis H2 of reduction Mills.lower_bound_of_RH.R1
-- Credit: @senamakel
-- psi(x) - theta(x) <= psi(x^(1/2)) + psi(x^(1/3)) + psi(x^(1/5)) (Mathlib, Costa Pereira) and
-- psi(y) <= log 4 * y + 2 sqrt(y) log y (Mathlib), written with x = a^12.

namespace OMA.S_Mills_H2

open Real Chebyshev

/-- Twelfth roots: `x = a¹²`. -/
lemma twelfth_root {x : ℝ} (hx : 0 ≤ x) :
    ∃ a : ℝ, 0 ≤ a ∧ x = a ^ 12 ∧ x ^ (2 : ℝ)⁻¹ = a ^ 6 ∧ x ^ (3 : ℝ)⁻¹ = a ^ 4 := by
  refine ⟨x ^ ((1 : ℝ) / 12), by positivity, ?_, ?_, ?_⟩ <;>
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

/-- `ψ(x) − θ(x) ≤ ψ(x^{1/2}) + 2 ψ(x^{1/3})`, then Mathlib's `ψ(y) ≤ log 4 · y + 2 √y log y`:
for `x ≥ 599`, `ψ(x) − θ(x) ≤ (1/8) √x log² x`. -/
theorem psi_sub_theta_le_eighth {x : ℝ} (hx : 599 ≤ x) :
    ψ x - θ x ≤ 1 / 8 * (√x * Real.log x ^ 2) := by
  have hx0 : 0 ≤ x := by linarith
  have hCP := psi_sub_theta_le_psi_add_psi_add_psi x
  have h53 : ψ (x ^ (5 : ℝ)⁻¹) ≤ ψ (x ^ (3 : ℝ)⁻¹) :=
    psi_mono (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
  obtain ⟨a, ha0, hxa, h2, h3⟩ := twelfth_root hx0
  rw [h2, h3] at hCP
  rw [h3] at h53
  have ha : 1.7039 ≤ a := by
    by_contra h
    push Not at h
    have : a ^ 12 < 1.7039 ^ 12 := pow_lt_pow_left₀ h ha0 (by norm_num)
    norm_num at this; linarith
  have hlx : 6.38 ≤ Real.log x := by
    have hx512 : (0 : ℝ) < x / 512 := by positivity
    have e : Real.log x = 9 * Real.log 2 + Real.log (x / 512) := by
      rw [Real.log_div (by positivity) (by norm_num), show (512 : ℝ) = 2 ^ 9 by norm_num,
        Real.log_pow]; push_cast; ring
    have h1 := Real.one_sub_inv_le_log_of_pos hx512
    have h2 : (x / 512)⁻¹ ≤ 512 / 599 := by
      rw [inv_div, div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
    rw [e]; linarith [Real.log_two_gt_d9]
  set ℓ := Real.log a with hℓ
  have hL : Real.log x = 12 * ℓ := by rw [hxa, Real.log_pow]; push_cast; ring
  have hℓ0 : 0.5316 ≤ ℓ := by linarith
  have hsx : √x = a ^ 6 := by
    rw [hxa, show a ^ 12 = (a ^ 6) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hl4 : Real.log 4 ≤ 1.3863 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast
    linarith [Real.log_two_lt_d9]
  -- `ψ(a⁶) ≤ log 4 · a⁶ + 12 a³ ℓ` and `ψ(a⁴) ≤ log 4 · a⁴ + 8 a² ℓ`
  have hp6 := psi_le (x := a ^ 6) (one_le_pow₀ (by linarith))
  have hp4 := psi_le (x := a ^ 4) (one_le_pow₀ (by linarith))
  rw [show a ^ 6 = (a ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity), Real.log_pow] at hp6
  rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity), Real.log_pow] at hp4
  rw [show (a ^ 3) ^ 2 = a ^ 6 by ring] at hp6
  rw [show (a ^ 2) ^ 2 = a ^ 4 by ring] at hp4
  rw [Real.log_pow] at hp6 hp4
  push_cast at hp6 hp4
  rw [← hℓ] at hp6 hp4
  rw [hsx, hL]
  have ha2 : 2.9032 ≤ a ^ 2 := by nlinarith
  have ha3 : 4.9468 ≤ a ^ 3 := by nlinarith
  have ha4 : 8.4286 ≤ a ^ 4 := by nlinarith
  have ha6 : 0 < a ^ 6 := by positivity
  have e1 : 12 * a ^ 3 * ℓ ≤ 2.4259 * a ^ 6 * ℓ := by
    have : a ^ 6 = a ^ 3 * a ^ 3 := by ring
    rw [this]; nlinarith [mul_le_mul_of_nonneg_left ha3 (by positivity : (0 : ℝ) ≤ a ^ 3 * ℓ)]
  have e2 : 2 * (1.3863 * a ^ 4) ≤ 0.9551 * a ^ 6 := by
    have : a ^ 6 = a ^ 4 * a ^ 2 := by ring
    rw [this]; nlinarith [mul_le_mul_of_nonneg_left ha2 (by positivity : (0 : ℝ) ≤ a ^ 4)]
  have e3 : 16 * a ^ 2 * ℓ ≤ 1.8984 * a ^ 6 * ℓ := by
    have : a ^ 6 = a ^ 2 * a ^ 4 := by ring
    rw [this]; nlinarith [mul_le_mul_of_nonneg_left ha4 (by positivity : (0 : ℝ) ≤ a ^ 2 * ℓ)]
  have hq : 1.3863 + 0.9551 + (2.4259 + 1.8984) * ℓ ≤ 18 * ℓ ^ 2 := by nlinarith
  have hq' := mul_le_mul_of_nonneg_left hq ha6.le
  have hψ4 : 0 ≤ Real.log 4 * a ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hl4 ha6.le, mul_le_mul_of_nonneg_right hl4
    (by positivity : (0 : ℝ) ≤ a ^ 4)]


end OMA.S_Mills_H2

theorem OMA.msl_closed_H2 : OMA.R_Mills_lower_bound_of_RH_R1.H2 :=
  fun _ hx => OMA.S_Mills_H2.psi_sub_theta_le_eighth hx


theorem OMA.solution : type_of% @Mills.lower_bound_of_RH := by
  exact OMA.R_Mills_lower_bound_of_RH_R1.main OMA.msl_closed_H1 OMA.msl_closed_H2
