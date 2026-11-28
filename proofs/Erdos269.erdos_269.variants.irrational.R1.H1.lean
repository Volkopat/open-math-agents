import OMAReductions.R_Erdos269_erdos_269_variants_irrational_R1

/-!
# Step H1 of reduction Erdos269.erdos_269.variants.irrational.R1 (Erdős Problem 269)

Written with Claude Code (AI-assisted).

For primes p < q the series over the {p, q}-smooth numbers is irrational.

Paper proof.  Put e(j) = floor(j log_p q), f(i) = floor(i log_q p),
t_j = 1 / (q^j p^{e(j)}), S2 = sum of the t_j and S1 = sum of 1 / (p^i q^{f(i)}).
The lcm of the smooth numbers up to m = p^i q^j is p^{i + e(j)} q^{j + f(i)}, so the
series equals 1 + S1 * S2, and (p - 1) S1 + (q - 1) S2 = p + q - 1.  Hence
(p - 1) * series = (p - 1) + (p + q - 1) S2 - (q - 1) S2^2.

Let beta = log_p q, irrational because p^a = q^b forces a = b = 0.  For K >= 1 let Q be
the least index j >= 1 whose distance from j * beta to the nearest integer is below half
the minimum of those distances over 1 <= j <= K (Dirichlet).  Then either
e(j + Q) = e(j) + e(Q) for all j < Q + K (case U), or e(j + Q) = e(j) + e(Q) + 1 for all
1 <= j < Q + K (case L).  With T the sum of t_j over j < Q: in case U put D = q^Q p^{e(Q)}
and R = T D / (D - 1); in case L put D = q^Q p^{e(Q) + 1} and R = (T D + p - 1) / (D - 1).
In both cases R = c / (D - 1) with c a natural number, R differs from S2 (the carry pattern
is not periodic), and since the tail of S2 from J on is at most 2 p / q^{2 J},
(D - 1)^2 |R - S2| < 2 p^3 / q^{2 K} and |R - S2| < 1 / q^2.

If the series were a / b, then b (p - 1) (D - 1)^2 (a / b - rho(R)) is a nonzero integer,
where rho is the quadratic above, and it equals
b (D - 1)^2 (R - S2) ((q - 1) (S2 + R) - (p + q - 1)), whose last factor lies strictly
between 0 and 4 q.  With K = b + 3 this has absolute value below
8 p^3 q b / q^{2 b + 6} < 1, a contradiction.

Credit.  The factorisation S = S1 * S2 and the identity (p - 1) S1 + (q - 1) S2 = p + q - 1
are due to Steve Fan (erdosproblems.com forum thread 269, 26 June 2026), who proves that
the series is even transcendental for two primes via Hecke-Mahler series.  The elementary
Diophantine argument here generalises our proof for {2, 3} of the variant `rational`
(disproof), whose answer False was first recorded by wcook04 (formal-conjectures PR 6522).
-/

namespace E269

/-- e(j) = ⌊j log_p q⌋. -/
abbrev e (p q j : ℕ) : ℕ := Nat.log p (q ^ j)

/-- f(i) = ⌊i log_q p⌋. -/
abbrev f (p q i : ℕ) : ℕ := Nat.log q (p ^ i)

/-- t_j = 1 / (q^j p^{e(j)}). -/
noncomputable abbrev t (p q j : ℕ) : ℝ := 1 / ((q : ℝ) ^ j * (p : ℝ) ^ (e p q j))

/-- S1 = Σ_i 1 / (p^i q^{f(i)}). -/
noncomputable abbrev S1 (p q : ℕ) : ℝ := ∑' i : ℕ, 1 / ((p : ℝ) ^ i * (q : ℝ) ^ (f p q i))

/-- S2 = Σ_j t_j. -/
noncomputable abbrev S2 (p q : ℕ) : ℝ := ∑' j : ℕ, t p q j

open Erdos269 Filter
open scoped Topology

-- ## The {p, q}-smooth numbers

theorem pl_mem {p q x : ℕ} : x ∈ ({p, q} : Set ℕ) ↔ x = p ∨ x = q := by
  simp

theorem pl_smooth_of_pow {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (i j : ℕ) :
    HasPrimeFactorsIn ({p, q} : Set ℕ) (p ^ i * q ^ j) := by
  refine ⟨Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _), fun r hr hd => ?_⟩
  rw [pl_mem]
  rcases (Nat.Prime.dvd_mul hr).mp hd with h | h
  · left; exact (Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow h)
  · right; exact (Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow h)

theorem pl_pow_of_smooth {p q : ℕ} :
    ∀ n, HasPrimeFactorsIn ({p, q} : Set ℕ) n → ∃ i j, n = p ^ i * q ^ j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro ⟨hpos, hpr⟩
    rcases eq_or_ne n 1 with h1 | h1
    · exact ⟨0, 0, by simp [h1]⟩
    · obtain ⟨r, hr, k, rfl⟩ := Nat.exists_prime_and_dvd h1
      have hk : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h; simp at hpos
        · exact h
      have hlt : k < r * k := by nlinarith [hr.two_le]
      obtain ⟨i, j, hij⟩ :=
        ih k hlt ⟨hk, fun p' hp' hd => hpr p' hp' (Dvd.dvd.mul_left hd r)⟩
      rcases pl_mem.mp (hpr r hr (dvd_mul_right r _)) with h | h
      · exact ⟨i + 1, j, by rw [hij, h]; ring⟩
      · exact ⟨i, j + 1, by rw [hij, h]; ring⟩

theorem pl_pow_inj {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) {i j k l : ℕ}
    (h : p ^ i * q ^ j = p ^ k * q ^ l) : i = k ∧ j = l := by
  have cpq : ∀ a b : ℕ, Nat.Coprime (p ^ a) (q ^ b) := fun a b =>
    Nat.Coprime.pow a b ((Nat.coprime_primes hp hq).mpr hpq.ne)
  have cqp : ∀ a b : ℕ, Nat.Coprime (q ^ a) (p ^ b) := fun a b =>
    Nat.Coprime.pow a b ((Nat.coprime_primes hq hp).mpr hpq.ne')
  have h1 : i ≤ k := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp
    ((cpq i l).dvd_of_dvd_mul_right ⟨q ^ j, h.symm⟩)
  have h2 : k ≤ i := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp
    ((cpq k j).dvd_of_dvd_mul_right ⟨q ^ l, h⟩)
  have h3 : j ≤ l := (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp
    ((cqp j k).dvd_of_dvd_mul_left ⟨p ^ i, by rw [← h]; ring⟩)
  have h4 : l ≤ j := (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp
    ((cqp l i).dvd_of_dvd_mul_left ⟨p ^ k, by rw [h]; ring⟩)
  exact ⟨le_antisymm h1 h2, le_antisymm h3 h4⟩

theorem pl_smooth_infinite {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (Set.ofPred (HasPrimeFactorsIn ({p, q} : Set ℕ))).Infinite := by
  refine (Set.infinite_range_of_injective (f := fun k : ℕ => p ^ k)
    (Nat.pow_right_injective hp.two_le)).mono ?_
  rintro _ ⟨k, rfl⟩
  have h := pl_smooth_of_pow hp hq k 0
  rw [pow_zero, mul_one] at h
  exact h

-- ## Logarithms of smooth numbers

theorem pl_log_p {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (i j : ℕ) :
    Nat.log p (p ^ i * q ^ j) = i + e p q j := by
  induction i with
  | zero => rw [pow_zero, one_mul, zero_add]
  | succ n ih =>
    rw [show p ^ (n + 1) * q ^ j = p ^ n * q ^ j * p by ring,
      Nat.log_mul_base hp.one_lt (Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)).ne', ih]
    ring

theorem pl_log_q {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (i j : ℕ) :
    Nat.log q (p ^ i * q ^ j) = j + f p q i := by
  induction j with
  | zero => rw [pow_zero, mul_one, zero_add]
  | succ n ih =>
    rw [show p ^ i * q ^ (n + 1) = p ^ i * q ^ n * q by ring,
      Nat.log_mul_base hq.one_lt (Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)).ne', ih]
    ring

-- ## The partial lcm

theorem pl_partialLcm_zero (P : Set ℕ) : partialLcm P 0 = 1 := by
  simp [partialLcm]

theorem pl_partialLcm_succ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (n : ℕ) :
    partialLcm ({p, q} : Set ℕ) (n + 1) =
      p ^ (Nat.log p (a ({p, q} : Set ℕ) n)) * q ^ (Nat.log q (a ({p, q} : Set ℕ) n)) := by
  classical
  have hinf := pl_smooth_infinite hp hq
  have hmem : ∀ k, HasPrimeFactorsIn ({p, q} : Set ℕ) (a ({p, q} : Set ℕ) k) :=
    Nat.nth_mem_of_infinite hinf
  have hpos : 0 < a ({p, q} : Set ℕ) n := (hmem n).1
  have key : ∀ x, HasPrimeFactorsIn ({p, q} : Set ℕ) x → x ≤ a ({p, q} : Set ℕ) n →
      x ∣ partialLcm ({p, q} : Set ℕ) (n + 1) := by
    intro x hs hle
    have hc : a ({p, q} : Set ℕ) (Nat.count (HasPrimeFactorsIn ({p, q} : Set ℕ)) x) = x :=
      Nat.nth_count hs
    have hk : Nat.count (HasPrimeFactorsIn ({p, q} : Set ℕ)) x ≤ n := by
      have : a ({p, q} : Set ℕ) (Nat.count (HasPrimeFactorsIn ({p, q} : Set ℕ)) x) ≤
          a ({p, q} : Set ℕ) n := by rw [hc]; exact hle
      exact (Nat.nth_le_nth hinf).mp this
    have hd : a ({p, q} : Set ℕ) (Nat.count (HasPrimeFactorsIn ({p, q} : Set ℕ)) x) ∣
        partialLcm ({p, q} : Set ℕ) (n + 1) :=
      Finset.dvd_lcm (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    rwa [hc] at hd
  apply Nat.dvd_antisymm
  · unfold partialLcm
    rw [Finset.lcm_dvd_iff]
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hle : a ({p, q} : Set ℕ) k ≤ a ({p, q} : Set ℕ) n := (Nat.nth_le_nth hinf).mpr hk'
    obtain ⟨i', j', hk2⟩ := pl_pow_of_smooth _ (hmem k)
    rw [hk2] at hle ⊢
    apply Nat.mul_dvd_mul
    · apply Nat.pow_dvd_pow
      apply Nat.le_log_of_pow_le hp.one_lt
      exact le_trans (Nat.le_mul_of_pos_right _ (pow_pos hq.pos _)) hle
    · apply Nat.pow_dvd_pow
      apply Nat.le_log_of_pow_le hq.one_lt
      exact le_trans (Nat.le_mul_of_pos_left _ (pow_pos hp.pos _)) hle
  · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hpq.ne))
    · have hs := pl_smooth_of_pow hp hq (Nat.log p (a ({p, q} : Set ℕ) n)) 0
      rw [pow_zero, mul_one] at hs
      exact key _ hs (Nat.pow_log_le_self p hpos.ne')
    · have hs := pl_smooth_of_pow hp hq 0 (Nat.log q (a ({p, q} : Set ℕ) n))
      rw [pow_zero, one_mul] at hs
      exact key _ hs (Nat.pow_log_le_self q hpos.ne')

-- ## The exponent sequence

theorem pl_e_spec {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (j : ℕ) :
    p ^ e p q j ≤ q ^ j ∧ q ^ j < p ^ (e p q j + 1) :=
  ⟨Nat.pow_log_le_self p (pow_pos hq.pos _).ne', Nat.lt_pow_succ_log_self hp.one_lt _⟩

theorem pl_e_zero (p q : ℕ) : e p q 0 = 0 := by
  simp [e]

theorem pl_e_step {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (j : ℕ) :
    e p q j + 1 ≤ e p q (j + 1) := by
  have h1 := (pl_e_spec hp hq j).1
  have h2 := (pl_e_spec hp hq (j + 1)).2
  have h3 : p ^ (e p q j + 1) < p ^ (e p q (j + 1) + 1) := by
    calc p ^ (e p q j + 1) = p * p ^ e p q j := by ring
      _ ≤ p * q ^ j := Nat.mul_le_mul_left p h1
      _ ≤ q * q ^ j := Nat.mul_le_mul_right _ hpq.le
      _ = q ^ (j + 1) := by ring
      _ < _ := h2
  have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp h3
  omega

theorem pl_e_ge {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (j : ℕ) :
    j ≤ e p q j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ n ih => have := pl_e_step hp hq hpq n; omega

-- ## Summability

theorem pl_t_pos {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (j : ℕ) : 0 < t p q j := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  exact one_div_pos.mpr (mul_pos (pow_pos hq0 _) (pow_pos hp0 _))

theorem pl_t_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (j : ℕ) :
    t p q j ≤ (1 / (q : ℝ)) ^ j := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  rw [one_div_pow]
  apply one_div_le_one_div_of_le (pow_pos hq0 _)
  exact le_mul_of_one_le_right (pow_pos hq0 _).le (one_le_pow₀ hp1)

theorem pl_t_summable {p q : ℕ} (hp : p.Prime) (hq : q.Prime) : Summable (t p q) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  exact Summable.of_nonneg_of_le (fun j => (pl_t_pos hp hq j).le) (pl_t_le hp hq)
    (summable_geometric_of_lt_one (by positivity) (by rw [div_lt_one hq0]; exact hq1))

theorem pl_s1_term_nonneg (p q i : ℕ) :
    (0 : ℝ) ≤ 1 / ((p : ℝ) ^ i * (q : ℝ) ^ (f p q i)) := by
  positivity

theorem pl_s1_term_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (i : ℕ) :
    1 / ((p : ℝ) ^ i * (q : ℝ) ^ (f p q i)) ≤ (1 / (p : ℝ)) ^ i := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_lt.le
  rw [one_div_pow]
  apply one_div_le_one_div_of_le (pow_pos hp0 _)
  exact le_mul_of_one_le_right (pow_pos hp0 _).le (one_le_pow₀ hq1)

theorem pl_s1_summable {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    Summable (fun i : ℕ => 1 / ((p : ℝ) ^ i * (q : ℝ) ^ (f p q i))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact Summable.of_nonneg_of_le (pl_s1_term_nonneg p q) (pl_s1_term_le hp hq)
    (summable_geometric_of_lt_one (by positivity) (by rw [div_lt_one hp0]; exact hp1))

-- ## The series as a product

theorem pl_lcm_term {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (i j n : ℕ)
    (h : a ({p, q} : Set ℕ) n = p ^ i * q ^ j) :
    (1 : ℝ) / (partialLcm ({p, q} : Set ℕ) (n + 1)) =
      1 / ((p : ℝ) ^ i * (q : ℝ) ^ (f p q i)) * t p q j := by
  rw [pl_partialLcm_succ hp hq hpq, h, pl_log_p hp hq, pl_log_q hp hq]
  unfold t
  push_cast
  rw [pow_add, pow_add, one_div_mul_one_div]
  congr 1
  ring

theorem series_formula {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Summable (fun n => (1 : ℝ) / (Erdos269.partialLcm ({p, q} : Set ℕ) n)) ∧
      Erdos269.series ({p, q} : Set ℕ) = 1 + S1 p q * S2 p q := by
  classical
  have hinf := pl_smooth_infinite hp hq
  have hmem : ∀ k, HasPrimeFactorsIn ({p, q} : Set ℕ) (a ({p, q} : Set ℕ) k) :=
    Nat.nth_mem_of_infinite hinf
  let φ : ℕ × ℕ → ℕ := fun z =>
    Nat.count (HasPrimeFactorsIn ({p, q} : Set ℕ)) (p ^ z.1 * q ^ z.2)
  have hφ : ∀ z, a ({p, q} : Set ℕ) (φ z) = p ^ z.1 * q ^ z.2 :=
    fun z => Nat.nth_count (pl_smooth_of_pow hp hq z.1 z.2)
  have hbij : Function.Bijective φ := by
    constructor
    · intro z w h
      have h' : p ^ z.1 * q ^ z.2 = p ^ w.1 * q ^ w.2 := by rw [← hφ z, ← hφ w, h]
      exact Prod.ext (pl_pow_inj hp hq hpq h').1 (pl_pow_inj hp hq hpq h').2
    · intro n
      obtain ⟨i, j, hij⟩ := pl_pow_of_smooth _ (hmem n)
      refine ⟨(i, j), ?_⟩
      apply Nat.nth_injective hinf
      show a ({p, q} : Set ℕ) (φ (i, j)) = a ({p, q} : Set ℕ) n
      rw [hφ, hij]
  let E : ℕ × ℕ ≃ ℕ := Equiv.ofBijective φ hbij
  let F : ℕ × ℕ → ℝ := fun z => 1 / ((p : ℝ) ^ z.1 * (q : ℝ) ^ (f p q z.1)) * t p q z.2
  have hF : Summable F :=
    Summable.mul_of_nonneg (pl_s1_summable hp hq) (pl_t_summable hp hq)
      (pl_s1_term_nonneg p q) (fun j => (pl_t_pos hp hq j).le)
  have hterm : ∀ z, (1 : ℝ) / (partialLcm ({p, q} : Set ℕ) (E z + 1)) = F z :=
    fun z => pl_lcm_term hp hq hpq z.1 z.2 _ (hφ z)
  have hsum1 : Summable (fun n => (1 : ℝ) / (partialLcm ({p, q} : Set ℕ) (n + 1))) := by
    rw [← Equiv.summable_iff E]
    exact hF.congr (fun z => (hterm z).symm)
  have hsum : Summable (fun n => (1 : ℝ) / (partialLcm ({p, q} : Set ℕ) n)) :=
    (summable_nat_add_iff 1).mp hsum1
  refine ⟨hsum, ?_⟩
  have h1 : ∑' n, (1 : ℝ) / (partialLcm ({p, q} : Set ℕ) (n + 1)) = ∑' z, F z := by
    rw [← Equiv.tsum_eq E (fun n => (1 : ℝ) / (partialLcm ({p, q} : Set ℕ) (n + 1)))]
    exact tsum_congr hterm
  have h2 : S1 p q * S2 p q = ∑' z, F z :=
    Summable.tsum_mul_tsum (pl_s1_summable hp hq) (pl_t_summable hp hq) hF
  unfold series
  rw [hsum.tsum_eq_zero_add, h1, ← h2, pl_partialLcm_zero]
  norm_num

-- ## Fan's identity (p - 1) S1 + (q - 1) S2 = p + q - 1

theorem pl_geom_Ico {x : ℝ} (hx : x ≠ 0) (m n : ℕ) (hmn : m ≤ n) :
    (x - 1) * ∑ i ∈ Finset.Ico m n, (1 / x) ^ i = x * (1 / x) ^ m - x * (1 / x) ^ n := by
  have hx1 : x * (1 / x) = 1 := by field_simp
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, mul_add, ih, pow_succ]
    linear_combination ((1 / x) ^ n) * hx1

theorem pl_f_eq_of_mem {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (J i : ℕ)
    (h1 : e p q J < i) (h2 : i ≤ e p q (J + 1)) : f p q i = J := by
  unfold f
  rw [Nat.log_eq_iff (Or.inr ⟨hq.one_lt, (pow_pos hp.pos _).ne'⟩)]
  constructor
  · exact le_of_lt (lt_of_lt_of_le (pl_e_spec hp hq J).2 (Nat.pow_le_pow_right hp.pos h1))
  · have hle : p ^ i ≤ q ^ (J + 1) :=
      le_trans (Nat.pow_le_pow_right hp.pos h2) (pl_e_spec hp hq (J + 1)).1
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hd : p ∣ p ^ i := dvd_pow_self p (by omega)
    rw [heq] at hd
    have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hd)
    omega

theorem pl_s1_partial {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (J : ℕ) :
    ((p : ℝ) - 1) * ∑ i ∈ Finset.range (e p q J + 1), 1 / ((p : ℝ) ^ i * (q : ℝ) ^ (f p q i)) =
      ((p : ℝ) - 1) + ∑ j ∈ Finset.range J, (t p q j - q * t p q (j + 1)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.pos.ne'
  induction J with
  | zero =>
    rw [pl_e_zero]
    simp [f]
  | succ J ih =>
    rw [Finset.sum_range_succ _ J, ← add_assoc, ← ih]
    have hle : e p q J + 1 ≤ e p q (J + 1) + 1 := by
      have := pl_e_step hp hq hpq J; omega
    rw [← Finset.sum_range_add_sum_Ico _ hle, mul_add]
    congr 1
    have hc : ∀ i ∈ Finset.Ico (e p q J + 1) (e p q (J + 1) + 1),
        1 / ((p : ℝ) ^ i * (q : ℝ) ^ (f p q i)) = 1 / (q : ℝ) ^ J * (1 / (p : ℝ)) ^ i := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      rw [pl_f_eq_of_mem hp hq hpq J i (by omega) (by omega), one_div_pow,
        one_div_mul_one_div, mul_comm ((q : ℝ) ^ J)]
    have hg := pl_geom_Ico hp0 _ _ hle
    calc ((p : ℝ) - 1) * ∑ i ∈ Finset.Ico (e p q J + 1) (e p q (J + 1) + 1),
          1 / ((p : ℝ) ^ i * (q : ℝ) ^ (f p q i))
        = 1 / (q : ℝ) ^ J * (((p : ℝ) - 1) *
            ∑ i ∈ Finset.Ico (e p q J + 1) (e p q (J + 1) + 1), (1 / (p : ℝ)) ^ i) := by
          rw [Finset.sum_congr rfl hc, ← Finset.mul_sum]; ring
      _ = 1 / (q : ℝ) ^ J * ((p : ℝ) * (1 / (p : ℝ)) ^ (e p q J + 1) -
            (p : ℝ) * (1 / (p : ℝ)) ^ (e p q (J + 1) + 1)) := by rw [hg]
      _ = t p q J - q * t p q (J + 1) := by
          unfold t
          simp only [one_div, inv_pow, pow_succ]
          field_simp

theorem fan_identity {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    ((p : ℝ) - 1) * S1 p q + ((q : ℝ) - 1) * S2 p q = (p : ℝ) + q - 1 := by
  have hts := pl_t_summable hp hq
  have hA : Tendsto (fun J => ((p : ℝ) - 1) *
      ∑ i ∈ Finset.range (e p q J + 1), 1 / ((p : ℝ) ^ i * (q : ℝ) ^ (f p q i)))
      atTop (𝓝 (((p : ℝ) - 1) * S1 p q)) := by
    have h := (pl_s1_summable hp hq).hasSum.tendsto_sum_nat
    have hT : Tendsto (fun J => e p q J + 1) atTop atTop :=
      tendsto_atTop_mono
        (fun J => by have := pl_e_ge hp hq hpq J; show J ≤ e p q J + 1; omega) tendsto_id
    exact (h.comp hT).const_mul _
  have hs1 : Summable (fun j => (q : ℝ) * t p q (j + 1)) :=
    ((summable_nat_add_iff 1).mpr hts).mul_left _
  have hs3 : Summable (fun j => t p q j - (q : ℝ) * t p q (j + 1)) := hts.sub hs1
  have hB := (hs3.hasSum.tendsto_sum_nat).const_add ((p : ℝ) - 1)
  have heq : (fun J => ((p : ℝ) - 1) *
      ∑ i ∈ Finset.range (e p q J + 1), 1 / ((p : ℝ) ^ i * (q : ℝ) ^ (f p q i))) =
      fun J => ((p : ℝ) - 1) + ∑ j ∈ Finset.range J, (t p q j - q * t p q (j + 1)) :=
    funext (pl_s1_partial hp hq hpq)
  rw [heq] at hA
  have hu := tendsto_nhds_unique hA hB
  have ht0 : t p q 0 = 1 := by unfold t; rw [pl_e_zero]; norm_num
  have h0 : S2 p q = t p q 0 + ∑' j, t p q (j + 1) := hts.tsum_eq_zero_add
  have h1 : ∑' j, (t p q j - (q : ℝ) * t p q (j + 1)) =
      S2 p q - q * ∑' j, t p q (j + 1) := by
    rw [Summable.tsum_sub hts hs1, tsum_mul_left]
  have hX : ∑' j, t p q (j + 1) = S2 p q - 1 := by linarith
  rw [h1, hX] at hu
  linarith


-- ## The exponent sequence `e`

theorem e_spec {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) (j : ℕ) :
    p ^ e p q j ≤ q ^ j ∧ q ^ j < p ^ (e p q j + 1) :=
  ⟨Nat.pow_log_le_self p (pow_ne_zero j (by omega)), Nat.lt_pow_succ_log_self (by omega) _⟩

theorem e_step {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) (j : ℕ) : e p q j + 1 ≤ e p q (j + 1) := by
  have h1 := (e_spec hp hpq j).1
  have h2 := (e_spec hp hpq (j + 1)).2
  have h3 : p ^ (e p q j + 1) < p ^ (e p q (j + 1) + 1) := by
    calc p ^ (e p q j + 1) = p * p ^ e p q j := by ring
      _ ≤ p * q ^ j := Nat.mul_le_mul_left p h1
      _ ≤ q * q ^ j := Nat.mul_le_mul_right _ hpq.le
      _ = q ^ (j + 1) := by ring
      _ < _ := h2
  have := (Nat.pow_lt_pow_iff_right (by omega : 1 < p)).mp h3
  omega

theorem e_mono {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) : Monotone (e p q) :=
  monotone_nat_of_le_succ (fun j => by have := e_step hp hpq j; omega)

theorem e_add {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) (j Q : ℕ) :
    e p q (j + Q) = e p q j + e p q Q ∨ e p q (j + Q) = e p q j + e p q Q + 1 := by
  have h1 : p ^ (e p q j + e p q Q) < p ^ (e p q (j + Q) + 1) := by
    calc p ^ (e p q j + e p q Q) = p ^ e p q j * p ^ e p q Q := by ring
      _ ≤ q ^ j * q ^ Q := Nat.mul_le_mul (e_spec hp hpq j).1 (e_spec hp hpq Q).1
      _ = q ^ (j + Q) := by ring
      _ < _ := (e_spec hp hpq (j + Q)).2
  have h2 : p ^ e p q (j + Q) < p ^ (e p q j + e p q Q + 2) := by
    calc p ^ e p q (j + Q) ≤ q ^ (j + Q) := (e_spec hp hpq (j + Q)).1
      _ = q ^ j * q ^ Q := by ring
      _ < p ^ (e p q j + 1) * p ^ (e p q Q + 1) :=
        Nat.mul_lt_mul'' (e_spec hp hpq j).2 (e_spec hp hpq Q).2
      _ = p ^ (e p q j + e p q Q + 2) := by ring
  have := (Nat.pow_lt_pow_iff_right (by omega : 1 < p)).mp h1
  have := (Nat.pow_lt_pow_iff_right (by omega : 1 < p)).mp h2
  omega

theorem e_zero (p q : ℕ) : e p q 0 = 0 := by simp [e]

-- ## Size of the terms

theorem t_pos {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) (j : ℕ) : 0 < t p q j := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  exact div_pos one_pos (mul_pos (pow_pos hq0 _) (pow_pos hp0 _))

theorem t_zero (p q : ℕ) : t p q 0 = 1 := by
  simp [t, e]

theorem sq_pow_eq (x : ℝ) (j : ℕ) : (x ^ 2) ^ j = x ^ j * x ^ j := by
  rw [← pow_mul, mul_comm, pow_mul, sq]

theorem t_le {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) (j : ℕ) :
    t p q j ≤ (p : ℝ) / ((q : ℝ) ^ 2) ^ j := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have h2 : (q : ℝ) ^ j < (p : ℝ) ^ (e p q j + 1) := by exact_mod_cast (e_spec hp hpq j).2
  have hqj : (0 : ℝ) < (q : ℝ) ^ j := pow_pos hq0 _
  have hpe : (0 : ℝ) < (p : ℝ) ^ (e p q j) := pow_pos hp0 _
  unfold t
  rw [div_le_div_iff₀ (mul_pos hqj hpe) (pow_pos (pow_pos hq0 2) j), sq_pow_eq, one_mul]
  rw [pow_succ] at h2
  have := mul_le_mul_of_nonneg_left h2.le hqj.le
  linarith

theorem t_ge {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) (j : ℕ) :
    1 / ((q : ℝ) ^ 2) ^ j ≤ t p q j := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have h1 : (p : ℝ) ^ (e p q j) ≤ (q : ℝ) ^ j := by exact_mod_cast (e_spec hp hpq j).1
  have hqj : (0 : ℝ) < (q : ℝ) ^ j := pow_pos hq0 _
  have hpe : (0 : ℝ) < (p : ℝ) ^ (e p q j) := pow_pos hp0 _
  unfold t
  apply one_div_le_one_div_of_le (mul_pos hqj hpe)
  rw [sq_pow_eq]
  exact mul_le_mul_of_nonneg_left h1 hqj.le

theorem w_ge {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) : (9 : ℝ) ≤ (q : ℝ) ^ 2 := by
  have h3 : (3 : ℝ) ≤ q := by exact_mod_cast (by omega : 3 ≤ q)
  nlinarith

theorem geo_summable {w : ℝ} (hw : 9 ≤ w) : Summable (fun j : ℕ => (1 / w) ^ j) :=
  summable_geometric_of_lt_one (by positivity)
    (by rw [div_lt_one (by linarith)]; linarith)

theorem t_summable {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) : Summable (t p q) := by
  have hw := w_ge hp hpq
  refine Summable.of_nonneg_of_le (fun j => (t_pos hp hpq j).le) (fun j => t_le hp hpq j)
    (f := fun j : ℕ => (p : ℝ) / ((q : ℝ) ^ 2) ^ j) ?_
  refine ((geo_summable hw).mul_left (p : ℝ)).congr (fun j => ?_)
  rw [one_div, inv_pow]; rfl

theorem t_tail {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) (J : ℕ) :
    ∑' j, t p q (j + J) ≤ 2 * (p : ℝ) / ((q : ℝ) ^ 2) ^ J := by
  have hw := w_ge hp hpq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  generalize hwdef : (q : ℝ) ^ 2 = w at *
  have hw0 : (0 : ℝ) < w := by linarith
  have hs : Summable (fun j => t p q (j + J)) := (summable_nat_add_iff J).mpr (t_summable hp hpq)
  have hg : Summable (fun j : ℕ => (p : ℝ) / w ^ J * (1 / w) ^ j) :=
    (geo_summable hw).mul_left _
  have hle : ∀ j, t p q (j + J) ≤ (p : ℝ) / w ^ J * (1 / w) ^ j := by
    intro j
    have h := t_le hp hpq (j + J)
    rw [hwdef] at h
    refine le_of_le_of_eq h ?_
    rw [pow_add, one_div, inv_pow]; field_simp
  have h1 := hs.tsum_le_tsum hle hg
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity)
    (by rw [div_lt_one hw0]; linarith)] at h1
  have h2 : (1 - 1 / w)⁻¹ ≤ 2 := by
    have h3 : (1 / 2 : ℝ) ≤ 1 - 1 / w := by
      have : 1 / w ≤ 1 / 9 := one_div_le_one_div_of_le (by norm_num) hw
      linarith
    have h4 := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) h3
    norm_num at h4
    simpa using h4
  have h5 : (0 : ℝ) ≤ (p : ℝ) / w ^ J := by positivity
  calc ∑' j, t p q (j + J) ≤ (p : ℝ) / w ^ J * (1 - 1 / w)⁻¹ := h1
    _ ≤ (p : ℝ) / w ^ J * 2 := mul_le_mul_of_nonneg_left h2 h5
    _ = 2 * (p : ℝ) / w ^ J := by ring

theorem S2_bounds {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) :
    1 + 1 / (q : ℝ) ^ 2 ≤ S2 p q ∧ S2 p q ≤ 2 := by
  have hsum := t_summable hp hpq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hpq' : (p : ℝ) + 1 ≤ q := by exact_mod_cast hpq
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  constructor
  · have h2 := Summable.sum_add_tsum_nat_add 2 hsum
    have hpos : 0 ≤ ∑' j, t p q (j + 2) := tsum_nonneg (fun j => (t_pos hp hpq _).le)
    have ht1 := t_ge hp hpq 1
    rw [pow_one] at ht1
    rw [Finset.sum_range_succ, Finset.sum_range_one, t_zero] at h2
    have hS : S2 p q = 1 + t p q 1 + ∑' j, t p q (j + 2) := h2.symm
    rw [hS]; linarith
  · have h1 := Summable.sum_add_tsum_nat_add 1 hsum
    have htail := t_tail hp hpq 1
    rw [pow_one] at htail
    rw [Finset.sum_range_one, t_zero] at h1
    have hS : S2 p q = 1 + ∑' j, t p q (j + 1) := h1.symm
    have h3 : 2 * (p : ℝ) / (q : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (pow_pos (by linarith) 2)]
      nlinarith
    rw [hS]; linarith

-- ## Diophantine key lemma

/- ### Generic facts about `Int.floor` / `Int.fract` of a sum -/

theorem floor_add_eq_iff (x y : ℝ) :
    ⌊x + y⌋ = ⌊x⌋ + ⌊y⌋ ↔ Int.fract x + Int.fract y < 1 := by
  have hx := Int.floor_add_fract x
  have hy := Int.floor_add_fract y
  have hx0 := Int.fract_nonneg x
  have hy0 := Int.fract_nonneg y
  rw [Int.floor_eq_iff]
  push_cast
  constructor
  · rintro ⟨_, h⟩
    linarith
  · intro h
    constructor <;> linarith

theorem floor_add_eq_succ_iff (x y : ℝ) :
    ⌊x + y⌋ = ⌊x⌋ + ⌊y⌋ + 1 ↔ 1 ≤ Int.fract x + Int.fract y := by
  have hx := Int.floor_add_fract x
  have hy := Int.floor_add_fract y
  have hx1 := Int.fract_lt_one x
  have hy1 := Int.fract_lt_one y
  rw [Int.floor_eq_iff]
  push_cast
  constructor
  · rintro ⟨h, _⟩
    linarith
  · intro h
    constructor <;> linarith

theorem fract_add_of_lt (x y : ℝ) (h : Int.fract x + Int.fract y < 1) :
    Int.fract (x + y) = Int.fract x + Int.fract y := by
  have hx := Int.floor_add_fract x
  have hy := Int.floor_add_fract y
  have hx0 := Int.fract_nonneg x
  have hy0 := Int.fract_nonneg y
  rw [Int.fract_eq_iff]
  refine ⟨by linarith, h, ⌊x⌋ + ⌊y⌋, ?_⟩
  push_cast
  linarith

theorem fract_add_of_ge (x y : ℝ) (h : 1 ≤ Int.fract x + Int.fract y) :
    Int.fract (x + y) = Int.fract x + Int.fract y - 1 := by
  have hx := Int.floor_add_fract x
  have hy := Int.floor_add_fract y
  have hx1 := Int.fract_lt_one x
  have hy1 := Int.fract_lt_one y
  rw [Int.fract_eq_iff]
  refine ⟨by linarith, by linarith, ⌊x⌋ + ⌊y⌋ + 1, ?_⟩
  push_cast
  linarith

/- ### The exponent sequence as a floor -/

theorem logb_pos' {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) : 0 < Real.logb p q :=
  Real.logb_pos (by exact_mod_cast (by omega : 1 < p)) (by exact_mod_cast (by omega : 1 < q))

theorem e_cast_eq_floor {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) (j : ℕ) :
    ((e p q j : ℕ) : ℤ) = ⌊(j : ℝ) * Real.logb p q⌋ := by
  have h1 : (j : ℝ) * Real.logb p q = Real.logb ((p : ℕ) : ℝ) ((q ^ j : ℕ) : ℝ) := by
    push_cast
    rw [Real.logb_pow]
  have h2 : 0 ≤ (j : ℝ) * Real.logb p q :=
    mul_nonneg (Nat.cast_nonneg j) (logb_pos' hp hpq).le
  rw [← Int.natCast_floor_eq_floor h2, h1, Real.natFloor_logb_natCast]

theorem mul_logb_ne_int {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (i : ℕ) (hi : 1 ≤ i) (n : ℤ) : (i : ℝ) * Real.logb p q ≠ (n : ℝ) := by
  intro h
  have hp2 := hp.two_le
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hi' : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  have hpos : 0 < (i : ℝ) * Real.logb p q := mul_pos hi' (logb_pos' hp2 hpq)
  have hn : 0 < n := by
    have h0 : (0 : ℝ) < (n : ℝ) := by rw [← h]; exact hpos
    exact_mod_cast h0
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn.le
  have hm : 0 < m := by exact_mod_cast hn
  have h3 : (q : ℝ) ^ i = (p : ℝ) ^ m := by
    have h4 : Real.logb p ((q : ℝ) ^ i) = Real.logb p ((p : ℝ) ^ m) := by
      rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hp1, mul_one]
      exact_mod_cast h
    exact Real.logb_injOn_pos hp1 (Set.mem_Ioi.2 (pow_pos hq0 _))
      (Set.mem_Ioi.2 (pow_pos (by linarith) _)) h4
  have h5 : q ^ i = p ^ m := by exact_mod_cast h3
  have h6 : p ∣ q ^ i := by
    rw [h5]
    exact dvd_pow_self p hm.ne'
  have h7 : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h6)
  omega

theorem e_add_eq_iff {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) (j Q : ℕ) :
    e p q (j + Q) = e p q j + e p q Q ↔
      Int.fract ((j : ℝ) * Real.logb p q) + Int.fract ((Q : ℝ) * Real.logb p q) < 1 := by
  have h1 := e_cast_eq_floor hp hpq (j + Q)
  have h2 := e_cast_eq_floor hp hpq j
  have h3 := e_cast_eq_floor hp hpq Q
  rw [Nat.cast_add, add_mul] at h1
  rw [← floor_add_eq_iff, ← h1, ← h2, ← h3]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

theorem e_add_eq_succ_iff {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) (j Q : ℕ) :
    e p q (j + Q) = e p q j + e p q Q + 1 ↔
      1 ≤ Int.fract ((j : ℝ) * Real.logb p q) + Int.fract ((Q : ℝ) * Real.logb p q) := by
  have h1 := e_cast_eq_floor hp hpq (j + Q)
  have h2 := e_cast_eq_floor hp hpq j
  have h3 := e_cast_eq_floor hp hpq Q
  rw [Nat.cast_add, add_mul] at h1
  rw [← floor_add_eq_succ_iff, ← h1, ← h2, ← h3]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

/-- Real-variable core of L12. -/
theorem key_real (β : ℝ) (hβ : ∀ i : ℕ, 1 ≤ i → ∀ n : ℤ, (i : ℝ) * β ≠ (n : ℝ))
    (K : ℕ) (hK : 1 ≤ K) :
    ∃ Q : ℕ, 1 ≤ Q ∧
      ((∀ j : ℕ, j < Q + K →
          Int.fract ((j : ℝ) * β) + Int.fract ((Q : ℝ) * β) < 1) ∨
        (∀ j : ℕ, 1 ≤ j → j < Q + K →
          1 ≤ Int.fract ((j : ℝ) * β) + Int.fract ((Q : ℝ) * β))) := by
  classical
  obtain ⟨θ, hθ⟩ : ∃ θ : ℕ → ℝ, ∀ j, θ j = Int.fract ((j : ℝ) * β) := ⟨_, fun _ => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, ∀ j, D j = min (θ j) (1 - θ j) := ⟨_, fun _ => rfl⟩
  have hθ1 : ∀ j, θ j < 1 := fun j => by rw [hθ]; exact Int.fract_lt_one _
  have hθpos : ∀ j, 1 ≤ j → 0 < θ j := by
    intro j hj
    rw [hθ]
    rcases (Int.fract_nonneg ((j : ℝ) * β)).lt_or_eq with h | h
    · exact h
    · exfalso
      have h2 := Int.floor_add_fract ((j : ℝ) * β)
      rw [← h, add_zero] at h2
      exact hβ j hj _ h2.symm
  have hθ0 : θ 0 = 0 := by rw [hθ]; simp
  have hD1 : ∀ j, D j ≤ θ j := fun j => by rw [hD]; exact min_le_left _ _
  have hD2 : ∀ j, D j ≤ 1 - θ j := fun j => by rw [hD]; exact min_le_right _ _
  have hD3 : ∀ j, D j = θ j ∨ D j = 1 - θ j := fun j => by rw [hD]; exact min_choice _ _
  have hDpos : ∀ j, 1 ≤ j → 0 < D j := by
    intro j hj
    rw [hD]
    exact lt_min (hθpos j hj) (by linarith [hθ1 j])
  have hD4 : ∀ j : ℕ, |(j : ℝ) * β - round ((j : ℝ) * β)| = D j := by
    intro j
    rw [hD, hθ, abs_sub_round_eq_min]
  have hθadd1 : ∀ a b : ℕ, θ a + θ b < 1 → θ (a + b) = θ a + θ b := by
    intro a b h
    rw [hθ a, hθ b] at h
    rw [hθ (a + b), hθ a, hθ b, Nat.cast_add, add_mul]
    exact fract_add_of_lt _ _ h
  have hθadd2 : ∀ a b : ℕ, 1 ≤ θ a + θ b → θ (a + b) = θ a + θ b - 1 := by
    intro a b h
    rw [hθ a, hθ b] at h
    rw [hθ (a + b), hθ a, hθ b, Nat.cast_add, add_mul]
    exact fract_add_of_ge _ _ h
  -- the minimum over `1 ≤ i ≤ K`
  have hμ : ∀ K : ℕ, ∃ μ : ℝ, 0 < μ ∧ ∀ i : ℕ, 1 ≤ i → i ≤ K → μ ≤ D i := by
    intro K
    induction K with
    | zero => exact ⟨1, one_pos, fun i h1 h2 => by omega⟩
    | succ n ih =>
      obtain ⟨μ, hμ0, h⟩ := ih
      refine ⟨min μ (D (n + 1)), lt_min hμ0 (hDpos (n + 1) (by omega)), fun i h1 h2 => ?_⟩
      rcases Nat.lt_or_ge i (n + 1) with h3 | h3
      · exact (min_le_left _ _).trans (h i h1 (by omega))
      · have h4 : i = n + 1 := by omega
        rw [h4]
        exact min_le_right _ _
  obtain ⟨μ, hμ0, hμK⟩ := hμ K
  have hμhalf : μ ≤ 1 / 2 := by
    have h1 := hμK 1 le_rfl hK
    have h2 := hD1 1
    have h3 := hD2 1
    linarith
  -- Dirichlet
  have hex : ∃ k : ℕ, 1 ≤ k ∧ D k < μ / 2 := by
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / μ)
    have hNpos : 0 < N := by
      have h0 : (0 : ℝ) < 2 / μ := by positivity
      have h1 : (0 : ℝ) < (N : ℝ) := h0.trans hN
      exact_mod_cast h1
    obtain ⟨k, hk0, _, hk⟩ := Real.exists_nat_abs_mul_sub_round_le β hNpos
    refine ⟨k, hk0, ?_⟩
    rw [hD4] at hk
    refine lt_of_le_of_lt hk ?_
    rw [div_lt_iff₀ hμ0] at hN
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    rw [div_lt_iff₀ hN1]
    nlinarith
  have hQ := Nat.find_spec hex
  have hmin : ∀ j : ℕ, 1 ≤ j → j < Nat.find hex → μ / 2 ≤ D j := by
    intro j hj1 hj
    by_contra hc
    rw [not_le] at hc
    exact Nat.find_min hex hj ⟨hj1, hc⟩
  generalize Nat.find hex = Q at hQ hmin
  obtain ⟨hQ1, hQδ⟩ := hQ
  have hKQ : K < Q := by
    by_contra hc
    rw [not_lt] at hc
    have := hμK Q hQ1 hc
    linarith
  refine ⟨Q, hQ1, ?_⟩
  rcases hD3 Q with hcase | hcase
  · -- case U
    left
    intro j hj
    rw [← hθ j, ← hθ Q]
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · rw [hj0, hθ0]
      linarith [hθ1 Q]
    rcases Nat.lt_or_ge j Q with hjQ | hjQ
    · have h1 := hmin j hj0 hjQ
      have h2 := hD2 j
      linarith
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hjQ
      have hiK : i < K := by omega
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · rw [hi0, add_zero]
        linarith
      · have h1 := hμK i hi0 hiK.le
        have h2 := hD2 i
        have h3 := hθadd1 Q i (by linarith)
        rw [h3]
        linarith
  · -- case L
    right
    intro j hj0 hj
    rw [← hθ j, ← hθ Q]
    rcases Nat.lt_or_ge j Q with hjQ | hjQ
    · have h1 := hmin j hj0 hjQ
      have h2 := hD1 j
      linarith
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hjQ
      have hiK : i < K := by omega
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · rw [hi0, add_zero]
        linarith
      · have h1 := hμK i hi0 hiK.le
        have h2 := hD1 i
        have h3 := hθadd2 Q i (by linarith)
        rw [h3]
        linarith

/-- Real-variable non-periodicity, no-carry side: carries occur. -/
theorem exists_carry_real (β : ℝ) (hβ : ∀ i : ℕ, 1 ≤ i → ∀ n : ℤ, (i : ℝ) * β ≠ (n : ℝ))
    (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ j : ℕ, 1 ≤ Int.fract ((j : ℝ) * β) + Int.fract ((Q : ℝ) * β) := by
  by_contra hne
  have hall : ∀ j : ℕ, Int.fract ((j : ℝ) * β) + Int.fract ((Q : ℝ) * β) < 1 := by
    intro j
    by_contra h
    rw [not_lt] at h
    exact hne ⟨j, h⟩
  have hpos : 0 < Int.fract ((Q : ℝ) * β) := by
    rcases (Int.fract_nonneg ((Q : ℝ) * β)).lt_or_eq with h | h
    · exact h
    · exfalso
      have h2 := Int.floor_add_fract ((Q : ℝ) * β)
      rw [← h, add_zero] at h2
      exact hβ Q hQ _ h2.symm
  have hind : ∀ m : ℕ, Int.fract (((m * Q : ℕ) : ℝ) * β) =
      (m : ℝ) * Int.fract ((Q : ℝ) * β) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h := fract_add_of_lt _ _ (hall (m * Q))
      have hc : (((m + 1) * Q : ℕ) : ℝ) * β =
          ((m * Q : ℕ) : ℝ) * β + (Q : ℝ) * β := by
        push_cast
        ring
      rw [hc, h, ih]
      push_cast
      ring
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / Int.fract ((Q : ℝ) * β))
  rw [div_lt_iff₀ hpos] at hm
  have h1 := hind m
  have h2 := Int.fract_lt_one (((m * Q : ℕ) : ℝ) * β)
  linarith

/-- Real-variable non-periodicity, carry side: non-carries occur. -/
theorem exists_nocarry_real (β : ℝ) (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ j : ℕ, 1 ≤ j ∧ Int.fract ((j : ℝ) * β) + Int.fract ((Q : ℝ) * β) < 1 := by
  by_contra hne
  have hall : ∀ j : ℕ, 1 ≤ j →
      1 ≤ Int.fract ((j : ℝ) * β) + Int.fract ((Q : ℝ) * β) := by
    intro j hj
    by_contra h
    rw [not_le] at h
    exact hne ⟨j, hj, h⟩
  have hlt := Int.fract_lt_one ((Q : ℝ) * β)
  have hind : ∀ m : ℕ, Int.fract ((((m + 1) * Q : ℕ) : ℝ) * β) =
      1 - ((m : ℝ) + 1) * (1 - Int.fract ((Q : ℝ) * β)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hp : 1 ≤ (m + 1) * Q := Nat.mul_pos (Nat.succ_pos m) hQ
      have h := fract_add_of_ge _ _ (hall ((m + 1) * Q) hp)
      have hc : (((m + 1 + 1) * Q : ℕ) : ℝ) * β =
          (((m + 1) * Q : ℕ) : ℝ) * β + (Q : ℝ) * β := by
        push_cast
        ring
      rw [hc, h, ih]
      push_cast
      ring
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / (1 - Int.fract ((Q : ℝ) * β)))
  rw [div_lt_iff₀ (by linarith)] at hm
  have h1 := hind m
  have h2 := Int.fract_nonneg ((((m + 1) * Q : ℕ) : ℝ) * β)
  nlinarith

/-- KEY: for every `K ≥ 1` there is `Q ≥ 1` in case U or case L. -/
theorem key {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (K : ℕ) (hK : 1 ≤ K) :
    ∃ Q : ℕ, 1 ≤ Q ∧
      ((∀ j : ℕ, j < Q + K → e p q (j + Q) = e p q j + e p q Q) ∨
        (∀ j : ℕ, 1 ≤ j → j < Q + K → e p q (j + Q) = e p q j + e p q Q + 1)) := by
  obtain ⟨Q, hQ, h⟩ := key_real (Real.logb p q) (mul_logb_ne_int hp hq hpq) K hK
  refine ⟨Q, hQ, ?_⟩
  rcases h with h | h
  · exact Or.inl fun j hj => (e_add_eq_iff hp.two_le hpq j Q).2 (h j hj)
  · exact Or.inr fun j hj1 hj => (e_add_eq_succ_iff hp.two_le hpq j Q).2 (h j hj1 hj)

theorem exists_e_add_eq_succ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (Q : ℕ) (hQ : 1 ≤ Q) : ∃ j : ℕ, e p q (j + Q) = e p q j + e p q Q + 1 := by
  obtain ⟨j, hj⟩ := exists_carry_real (Real.logb p q) (mul_logb_ne_int hp hq hpq) Q hQ
  exact ⟨j, (e_add_eq_succ_iff hp.two_le hpq j Q).2 hj⟩

theorem exists_e_add_eq {p q : ℕ} (hp : p.Prime) (hpq : p < q)
    (Q : ℕ) (hQ : 1 ≤ Q) : ∃ j : ℕ, 1 ≤ j ∧ e p q (j + Q) = e p q j + e p q Q := by
  obtain ⟨j, hj1, hj⟩ := exists_nocarry_real (Real.logb p q) Q hQ
  exact ⟨j, hj1, (e_add_eq_iff hp.two_le hpq j Q).2 hj⟩

-- ## Approximation

lemma t_shift_eq {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) {j Q : ℕ}
    (h : e p q (j + Q) = e p q j + e p q Q) :
    t p q (j + Q) = t p q j / ((q : ℝ) ^ Q * (p : ℝ) ^ (e p q Q)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  unfold t
  rw [h, pow_add, pow_add]
  field_simp

lemma t_shift_succ {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) {j Q : ℕ}
    (h : e p q (j + Q) = e p q j + e p q Q + 1) :
    t p q (j + Q) = t p q j / ((q : ℝ) ^ Q * (p : ℝ) ^ (e p q Q)) / p := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  unfold t
  rw [h, pow_add, pow_add, pow_add]
  field_simp

lemma p_pow_e_le {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) (Q : ℕ) :
    (p : ℝ) ^ (e p q Q) ≤ (q : ℝ) ^ Q := by
  exact_mod_cast (e_spec hp hpq Q).1

/-- Tail estimate shared by both cases. -/
lemma tail_core {g u : ℕ → ℝ} (J : ℕ) (hu : Summable u)
    (hg0 : ∀ j, 0 ≤ g j) (hgle : ∀ j, g j ≤ u j) (hpos : ∃ j, J ≤ j ∧ 0 < g j) :
    Summable g ∧ 0 < ∑' j, g (j + J) ∧ ∑' j, g (j + J) ≤ ∑' j, u (j + J) := by
  have hg : Summable g := Summable.of_nonneg_of_le hg0 hgle hu
  have hgJ : Summable (fun j => g (j + J)) := (summable_nat_add_iff J).2 hg
  have huJ : Summable (fun j => u (j + J)) := (summable_nat_add_iff J).2 hu
  refine ⟨hg, ?_, ?_⟩
  · obtain ⟨j, hj, hjp⟩ := hpos
    refine hgJ.tsum_pos (fun i => hg0 _) (j - J) ?_
    simpa [Nat.sub_add_cancel hj] using hjp
  · exact hgJ.tsum_le_tsum (fun i => hgle _) huJ

/-- Final numeric step shared by both cases. -/
lemma approx_final {X D pr w : ℝ} {Q K : ℕ} (hK : 2 ≤ K) (hQ : 1 ≤ Q) (hp : 2 ≤ pr)
    (hw : 9 ≤ w) (hpw : 2 * pr ^ 2 < w ^ 2) (hD2 : 2 ≤ D) (hDle : D ≤ pr * w ^ Q)
    (hX0 : 0 < X) (hX : X ≤ 2 * pr ^ 2 / w ^ (Q + K)) :
    (D - 1) ^ 2 * (X / (D - 1)) < 2 * pr ^ 3 / w ^ K ∧ X / (D - 1) < 1 / w := by
  have hD1 : 0 < D - 1 := by linarith
  have hw0 : (0 : ℝ) < w := by linarith
  have hwK : (0 : ℝ) < w ^ K := pow_pos hw0 _
  have hwQ : (0 : ℝ) < w ^ Q := pow_pos hw0 _
  have hX' : X * (w ^ Q * w ^ K) ≤ 2 * pr ^ 2 := by
    rw [← pow_add]
    exact (le_div_iff₀ (pow_pos hw0 _)).1 hX
  constructor
  · have e1 : (D - 1) ^ 2 * (X / (D - 1)) = (D - 1) * X := by
      field_simp
    rw [e1, lt_div_iff₀ hwK]
    have hXw : 0 < X * w ^ K := mul_pos hX0 hwK
    have h1 := mul_le_mul_of_nonneg_right hDle hXw.le
    have h2 := mul_le_mul_of_nonneg_left hX' (by linarith : (0 : ℝ) ≤ pr)
    calc (D - 1) * X * w ^ K < D * (X * w ^ K) := by linarith
      _ ≤ pr * w ^ Q * (X * w ^ K) := h1
      _ = pr * (X * (w ^ Q * w ^ K)) := by ring
      _ ≤ pr * (2 * pr ^ 2) := h2
      _ = 2 * pr ^ 3 := by ring
  · have h3 : w ^ 3 ≤ w ^ (Q + K) := pow_le_pow_right₀ (by linarith) (by omega)
    have h4 : X / (D - 1) ≤ X := div_le_self hX0.le (by linarith)
    have h5 : 2 * pr ^ 2 / w ^ (Q + K) ≤ 2 * pr ^ 2 / w ^ 3 :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hw0 _) h3
    have h6 : 2 * pr ^ 2 / w ^ 3 < 1 / w := by
      rw [div_lt_div_iff₀ (pow_pos hw0 _) hw0]
      nlinarith [mul_pos hw0 (sub_pos.2 hpw)]
    linarith

/-- `T * D` is a natural number. -/
lemma cast_c {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) (Q m : ℕ) (hm : e p q Q ≤ m) :
    ((∑ j ∈ Finset.range Q, q ^ (Q - j) * p ^ (m - e p q j) : ℕ) : ℝ)
      = (∑ j ∈ Finset.range Q, t p q j) * ((q : ℝ) ^ Q * (p : ℝ) ^ m) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjQ : j ≤ Q := (Finset.mem_range.1 hj).le
  have hem : e p q j ≤ m := (e_mono hp hpq hjQ).trans hm
  have h3 : (q : ℝ) ^ Q = (q : ℝ) ^ (Q - j) * (q : ℝ) ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hjQ]
  have h2 : (p : ℝ) ^ m = (p : ℝ) ^ (m - e p q j) * (p : ℝ) ^ (e p q j) := by
    rw [← pow_add, Nat.sub_add_cancel hem]
  rw [h3, h2]
  unfold t
  field_simp

/-- Case U of the key lemma. -/
theorem approx_U {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q)
    (hnp : ∀ Q, 1 ≤ Q → ∃ j, e p q (j + Q) = e p q j + e p q Q + 1)
    {K Q : ℕ} (hK : 2 ≤ K) (hQ : 1 ≤ Q)
    (hU : ∀ j, j < Q + K → e p q (j + Q) = e p q j + e p q Q) :
    ∃ c D : ℕ, 2 ≤ D ∧ 0 < (c : ℝ) / ((D : ℝ) - 1) - S2 p q ∧
      ((D : ℝ) - 1) ^ 2 * ((c : ℝ) / ((D : ℝ) - 1) - S2 p q) <
        2 * (p : ℝ) ^ 3 / ((q : ℝ) ^ 2) ^ K ∧
      (c : ℝ) / ((D : ℝ) - 1) - S2 p q < 1 / (q : ℝ) ^ 2 := by
  have hsum := t_summable hp hpq
  have hstep := e_add hp hpq
  have hw := w_ge hp hpq
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hpq' : (p : ℝ) + 1 ≤ q := by exact_mod_cast hpq
  have hpw : 2 * (p : ℝ) ^ 2 < ((q : ℝ) ^ 2) ^ 2 := by nlinarith
  refine ⟨∑ j ∈ Finset.range Q, q ^ (Q - j) * p ^ (e p q Q - e p q j),
    q ^ Q * p ^ (e p q Q), ?_⟩
  have hc := cast_c hp hpq Q (e p q Q) le_rfl
  have hDn : 3 ≤ q ^ Q * p ^ (e p q Q) := by
    have h1 : q ^ 1 ≤ q ^ Q := Nat.pow_le_pow_right (by omega) hQ
    have h2 : 1 ≤ p ^ (e p q Q) := Nat.one_le_pow _ _ (by omega)
    calc 3 ≤ q ^ 1 * 1 := by rw [pow_one, mul_one]; omega
      _ ≤ q ^ Q * p ^ (e p q Q) := Nat.mul_le_mul h1 h2
  have hDcast : ((q ^ Q * p ^ (e p q Q) : ℕ) : ℝ) = (q : ℝ) ^ Q * (p : ℝ) ^ (e p q Q) := by
    simp only [Nat.cast_mul, Nat.cast_pow]
  rw [hDcast]
  have hD3' : (3 : ℝ) ≤ ((q ^ Q * p ^ (e p q Q) : ℕ) : ℝ) := by exact_mod_cast hDn
  rw [hDcast] at hD3'
  have hDle : (q : ℝ) ^ Q * (p : ℝ) ^ (e p q Q) ≤ (p : ℝ) * ((q : ℝ) ^ 2) ^ Q := by
    have h := p_pow_e_le hp hpq Q
    have h3 : (0 : ℝ) < (q : ℝ) ^ Q := pow_pos (by linarith) Q
    rw [sq_pow_eq]
    nlinarith [mul_le_mul_of_nonneg_left h h3.le, mul_pos h3 h3]
  generalize hDdef : (q : ℝ) ^ Q * (p : ℝ) ^ (e p q Q) = D at *
  have hD0 : 0 < D := by linarith
  have hD1 : 0 < D - 1 := by linarith
  -- the defect function
  set g : ℕ → ℝ := fun j => t p q j / D - t p q (j + Q) with hgdef
  have hgU : ∀ j, e p q (j + Q) = e p q j + e p q Q → g j = 0 := by
    intro j h
    simp only [hgdef, t_shift_eq hp hpq h, hDdef, sub_self]
  have hgS : ∀ j, e p q (j + Q) = e p q j + e p q Q + 1 →
      g j = t p q j / D - t p q j / D / p := by
    intro j h
    simp only [hgdef, t_shift_succ hp hpq h, hDdef]
  have htD : ∀ j, 0 < t p q j / D := fun j => div_pos (t_pos hp hpq j) hD0
  have hlt : ∀ j, t p q j / D / p < t p q j / D :=
    fun j => div_lt_self (htD j) (by linarith)
  have hg0 : ∀ j, 0 ≤ g j := by
    intro j
    rcases hstep j Q with h | h
    · rw [hgU j h]
    · rw [hgS j h]; linarith [hlt j]
  have hgle : ∀ j, g j ≤ (p : ℝ) * (t p q j / D) := by
    intro j
    have h1 : g j ≤ t p q j / D := by
      simp only [hgdef]
      linarith [t_pos hp hpq (j + Q)]
    nlinarith [htD j]
  have hpos : ∃ j, Q + K ≤ j ∧ 0 < g j := by
    obtain ⟨j, hj⟩ := hnp Q hQ
    refine ⟨j, ?_, ?_⟩
    · by_contra hlt'
      have := hU j (not_le.1 hlt')
      omega
    · rw [hgS j hj]; linarith [hlt j]
  have hu : Summable (fun j => (p : ℝ) * (t p q j / D)) := (hsum.div_const D).mul_left _
  obtain ⟨hg, hEpos, hEle⟩ := tail_core (Q + K) hu hg0 hgle hpos
  rw [tsum_mul_left, tsum_div_const] at hEle
  have htQ : Summable (fun j => t p q (j + Q)) := (summable_nat_add_iff Q).2 hsum
  have hsplit := hg.sum_add_tsum_nat_add (Q + K)
  have hfin : ∑ i ∈ Finset.range (Q + K), g i = 0 :=
    Finset.sum_eq_zero (fun i hi => hgU i (hU i (Finset.mem_range.1 hi)))
  have hgsum : ∑' j, g j = S2 p q / D - ∑' j, t p q (j + Q) := by
    simp only [hgdef]
    rw [(hsum.div_const D).tsum_sub htQ, tsum_div_const]
  have hS2 : S2 p q = ∑ j ∈ Finset.range Q, t p q j + ∑' j, t p q (j + Q) :=
    (hsum.sum_add_tsum_nat_add Q).symm
  have hE : ∑' j, g (j + (Q + K)) =
      S2 p q / D - (S2 p q - ∑ j ∈ Finset.range Q, t p q j) := by
    rw [hfin, zero_add] at hsplit
    rw [hsplit, hgsum, hS2]; ring
  have hXle : (∑' j, g (j + (Q + K))) * D ≤ 2 * (p : ℝ) ^ 2 / ((q : ℝ) ^ 2) ^ (Q + K) := by
    have h1 := mul_le_mul_of_nonneg_right hEle hD0.le
    have h2 : (p : ℝ) * ((∑' j, t p q (j + (Q + K))) / D) * D =
        (p : ℝ) * ∑' j, t p q (j + (Q + K)) := by
      field_simp
    have h3 := mul_le_mul_of_nonneg_left (t_tail hp hpq (Q + K)) (by linarith : (0 : ℝ) ≤ p)
    have h4 : (p : ℝ) * (2 * (p : ℝ) / ((q : ℝ) ^ 2) ^ (Q + K)) =
        2 * (p : ℝ) ^ 2 / ((q : ℝ) ^ 2) ^ (Q + K) := by ring
    linarith
  have key : ((∑ j ∈ Finset.range Q, q ^ (Q - j) * p ^ (e p q Q - e p q j) : ℕ) : ℝ) / (D - 1)
      - S2 p q = (∑' j, g (j + (Q + K))) * D / (D - 1) := by
    rw [hc, hE]
    field_simp
    ring
  rw [key]
  have hX0 : 0 < (∑' j, g (j + (Q + K))) * D := mul_pos hEpos hD0
  obtain ⟨h1, h2⟩ := approx_final hK hQ hpr hw hpw (by linarith) hDle hX0 hXle
  exact ⟨by omega, div_pos hX0 hD1, h1, h2⟩

/-- Case L of the key lemma. -/
theorem approx_L {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q)
    (hnp : ∀ Q, 1 ≤ Q → ∃ j, 1 ≤ j ∧ e p q (j + Q) = e p q j + e p q Q)
    {K Q : ℕ} (hK : 2 ≤ K) (hQ : 1 ≤ Q)
    (hL : ∀ j, 1 ≤ j → j < Q + K → e p q (j + Q) = e p q j + e p q Q + 1) :
    ∃ c D : ℕ, 2 ≤ D ∧ 0 < S2 p q - (c : ℝ) / ((D : ℝ) - 1) ∧
      ((D : ℝ) - 1) ^ 2 * (S2 p q - (c : ℝ) / ((D : ℝ) - 1)) <
        2 * (p : ℝ) ^ 3 / ((q : ℝ) ^ 2) ^ K ∧
      S2 p q - (c : ℝ) / ((D : ℝ) - 1) < 1 / (q : ℝ) ^ 2 := by
  have hsum := t_summable hp hpq
  have hstep := e_add hp hpq
  have hw := w_ge hp hpq
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hpq' : (p : ℝ) + 1 ≤ q := by exact_mod_cast hpq
  have hpw : 2 * (p : ℝ) ^ 2 < ((q : ℝ) ^ 2) ^ 2 := by nlinarith
  refine ⟨(∑ j ∈ Finset.range Q, q ^ (Q - j) * p ^ (e p q Q + 1 - e p q j)) + (p - 1),
    q ^ Q * p ^ (e p q Q + 1), ?_⟩
  have hc := cast_c hp hpq Q (e p q Q + 1) (Nat.le_succ _)
  have hDn : 3 ≤ q ^ Q * p ^ (e p q Q + 1) := by
    have h1 : q ^ 1 ≤ q ^ Q := Nat.pow_le_pow_right (by omega) hQ
    have h2 : 1 ≤ p ^ (e p q Q + 1) := Nat.one_le_pow _ _ (by omega)
    calc 3 ≤ q ^ 1 * 1 := by rw [pow_one, mul_one]; omega
      _ ≤ q ^ Q * p ^ (e p q Q + 1) := Nat.mul_le_mul h1 h2
  have hDcast : ((q ^ Q * p ^ (e p q Q + 1) : ℕ) : ℝ) =
      (q : ℝ) ^ Q * (p : ℝ) ^ (e p q Q + 1) := by
    simp only [Nat.cast_mul, Nat.cast_pow]
  rw [hDcast]
  have hD3' : (3 : ℝ) ≤ ((q ^ Q * p ^ (e p q Q + 1) : ℕ) : ℝ) := by exact_mod_cast hDn
  rw [hDcast] at hD3'
  have hDp : (q : ℝ) ^ Q * (p : ℝ) ^ (e p q Q) =
      (q : ℝ) ^ Q * (p : ℝ) ^ (e p q Q + 1) / p := by
    rw [pow_succ]; field_simp
  have hDle : (q : ℝ) ^ Q * (p : ℝ) ^ (e p q Q + 1) ≤ (p : ℝ) * ((q : ℝ) ^ 2) ^ Q := by
    have h := p_pow_e_le hp hpq Q
    have h3 : (0 : ℝ) < (q : ℝ) ^ Q := pow_pos (by linarith) Q
    have h4 := mul_le_mul_of_nonneg_left h h3.le
    have h5 := mul_le_mul_of_nonneg_left h4 (by linarith : (0 : ℝ) ≤ p)
    rw [sq_pow_eq, pow_succ]
    linarith
  have hpcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  generalize hDdef : (q : ℝ) ^ Q * (p : ℝ) ^ (e p q Q + 1) = D at *
  have hD0 : 0 < D := by linarith
  have hD1 : 0 < D - 1 := by linarith
  -- the defect function
  set g : ℕ → ℝ := fun j => t p q (j + Q) - t p q j / D with hgdef
  have hgU : ∀ j, e p q (j + Q) = e p q j + e p q Q →
      g j = (p : ℝ) * (t p q j / D) - t p q j / D := by
    intro j h
    simp only [hgdef, t_shift_eq hp hpq h, hDp]
    field_simp
  have hgS : ∀ j, e p q (j + Q) = e p q j + e p q Q + 1 → g j = 0 := by
    intro j h
    simp only [hgdef, t_shift_succ hp hpq h, hDp]
    field_simp
    ring
  have htD : ∀ j, 0 < t p q j / D := fun j => div_pos (t_pos hp hpq j) hD0
  have hg0 : ∀ j, 0 ≤ g j := by
    intro j
    rcases hstep j Q with h | h
    · rw [hgU j h]; nlinarith [htD j]
    · rw [hgS j h]
  have hgle : ∀ j, g j ≤ (p : ℝ) * (t p q j / D) := by
    intro j
    rcases hstep j Q with h | h
    · rw [hgU j h]; linarith [htD j]
    · rw [hgS j h]; nlinarith [htD j]
  have hpos : ∃ j, Q + K ≤ j ∧ 0 < g j := by
    obtain ⟨j, hj1, hj⟩ := hnp Q hQ
    refine ⟨j, ?_, ?_⟩
    · by_contra hlt
      have := hL j hj1 (not_le.1 hlt)
      omega
    · rw [hgU j hj]; nlinarith [htD j]
  have hu : Summable (fun j => (p : ℝ) * (t p q j / D)) := (hsum.div_const D).mul_left _
  obtain ⟨hg, hEpos, hEle⟩ := tail_core (Q + K) hu hg0 hgle hpos
  rw [tsum_mul_left, tsum_div_const] at hEle
  have htQ : Summable (fun j => t p q (j + Q)) := (summable_nat_add_iff Q).2 hsum
  have hsplit := hg.sum_add_tsum_nat_add (Q + K)
  have he0 : e p q (0 + Q) = e p q 0 + e p q Q := by simp [e]
  have hfin : ∑ i ∈ Finset.range (Q + K), g i = ((p : ℝ) - 1) / D := by
    rw [Finset.sum_eq_single 0]
    · rw [hgU 0 he0, t_zero]; ring
    · intro i hi hi0
      exact hgS i (hL i (Nat.pos_of_ne_zero hi0) (Finset.mem_range.1 hi))
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  have hgsum : ∑' j, g j = ∑' j, t p q (j + Q) - S2 p q / D := by
    simp only [hgdef]
    rw [htQ.tsum_sub (hsum.div_const D), tsum_div_const]
  have hS2 : S2 p q = ∑ j ∈ Finset.range Q, t p q j + ∑' j, t p q (j + Q) :=
    (hsum.sum_add_tsum_nat_add Q).symm
  have hE : ∑' j, g (j + (Q + K)) =
      (S2 p q - ∑ j ∈ Finset.range Q, t p q j) - S2 p q / D - ((p : ℝ) - 1) / D := by
    rw [hfin] at hsplit
    have h2 : ∑' j, g (j + (Q + K)) = ∑' j, g j - ((p : ℝ) - 1) / D := by linarith
    rw [h2, hgsum, hS2]; ring
  have hXle : (∑' j, g (j + (Q + K))) * D ≤ 2 * (p : ℝ) ^ 2 / ((q : ℝ) ^ 2) ^ (Q + K) := by
    have h1 := mul_le_mul_of_nonneg_right hEle hD0.le
    have h2 : (p : ℝ) * ((∑' j, t p q (j + (Q + K))) / D) * D =
        (p : ℝ) * ∑' j, t p q (j + (Q + K)) := by
      field_simp
    have h3 := mul_le_mul_of_nonneg_left (t_tail hp hpq (Q + K)) (by linarith : (0 : ℝ) ≤ p)
    have h4 : (p : ℝ) * (2 * (p : ℝ) / ((q : ℝ) ^ 2) ^ (Q + K)) =
        2 * (p : ℝ) ^ 2 / ((q : ℝ) ^ 2) ^ (Q + K) := by ring
    linarith
  have key : S2 p q -
      (((∑ j ∈ Finset.range Q, q ^ (Q - j) * p ^ (e p q Q + 1 - e p q j)) + (p - 1) : ℕ) : ℝ)
        / (D - 1) = (∑' j, g (j + (Q + K))) * D / (D - 1) := by
    rw [Nat.cast_add, hc, hE, hpcast]
    field_simp
    ring
  rw [key]
  have hX0 : 0 < (∑' j, g (j + (Q + K))) * D := mul_pos hEpos hD0
  obtain ⟨h1, h2⟩ := approx_final hK hQ hpr hw hpw (by linarith) hDle hX0 hXle
  exact ⟨by omega, div_pos hX0 hD1, h1, h2⟩

/-- For every `K ≥ 2` a good approximation exists. -/
theorem approx_exists {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (K : ℕ) (hK : 2 ≤ K) :
    ∃ c D : ℕ, 2 ≤ D ∧ (c : ℝ) / ((D : ℝ) - 1) - S2 p q ≠ 0 ∧
      ((D : ℝ) - 1) ^ 2 * |(c : ℝ) / ((D : ℝ) - 1) - S2 p q| <
        2 * (p : ℝ) ^ 3 / ((q : ℝ) ^ 2) ^ K ∧
      |(c : ℝ) / ((D : ℝ) - 1) - S2 p q| < 1 / (q : ℝ) ^ 2 := by
  obtain ⟨Q, hQ, hU | hL⟩ := key hp hq hpq K (by omega)
  · obtain ⟨c, D, hD, h0, h1, h2⟩ :=
      approx_U hp.two_le hpq (exists_e_add_eq_succ hp hq hpq) hK hQ hU
    refine ⟨c, D, hD, h0.ne', ?_, ?_⟩
    · rw [abs_of_pos h0]; exact h1
    · rw [abs_of_pos h0]; exact h2
  · obtain ⟨c, D, hD, h0, h1, h2⟩ :=
      approx_L hp.two_le hpq (exists_e_add_eq hp hpq) hK hQ hL
    refine ⟨c, D, hD, ?_, ?_, ?_⟩
    · intro h
      linarith
    · rw [abs_sub_comm, abs_of_pos h0]; exact h1
    · rw [abs_sub_comm, abs_of_pos h0]; exact h2

-- ## Final contradiction

theorem irrational_of {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) {x : ℝ}
    (hser : x = 1 + S1 p q * S2 p q)
    (hfan : ((p : ℝ) - 1) * S1 p q + ((q : ℝ) - 1) * S2 p q = (p : ℝ) + q - 1) :
    Irrational x := by
  rintro ⟨r, hr⟩
  have hp2 := hp.two_le
  obtain ⟨c, D, hD, hne, hsmall, heps⟩ := approx_exists hp hq hpq (r.den + 3) (by omega)
  obtain ⟨hlo, hhi⟩ := S2_bounds hp2 hpq
  have hw := w_ge hp2 hpq
  have hP2 : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hPQ : (p : ℝ) + 1 ≤ q := by exact_mod_cast hpq
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hd : (1 : ℝ) ≤ (D : ℝ) - 1 := by linarith
  have hd0 : (D : ℝ) - 1 ≠ 0 := by linarith
  have hb : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  generalize hRdef : (c : ℝ) / ((D : ℝ) - 1) = R at *
  generalize hwdef : (q : ℝ) ^ 2 = w at *
  have hw0 : (0 : ℝ) < w := by linarith
  have hquad : ((p : ℝ) - 1) * x =
      ((p : ℝ) - 1) + ((p : ℝ) + q - 1) * S2 p q - ((q : ℝ) - 1) * S2 p q ^ 2 := by
    have h1 : ((p : ℝ) - 1) * S1 p q = (p : ℝ) + q - 1 - ((q : ℝ) - 1) * S2 p q := by linarith
    rw [hser, mul_add, mul_one, ← mul_assoc, h1]; ring
  have hx : ((p : ℝ) - 1) * (r : ℝ) -
      (((p : ℝ) - 1) + ((p : ℝ) + q - 1) * R - ((q : ℝ) - 1) * R ^ 2) =
      (R - S2 p q) * (((q : ℝ) - 1) * (S2 p q + R) - ((p : ℝ) + q - 1)) := by
    rw [hr, hquad]; ring
  have hqr : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
    exact_mod_cast (Rat.num_div_den r).symm
  have hZ : (((r.num * ((p : ℤ) - 1) * ((D : ℤ) - 1) ^ 2 -
      r.den * (((p : ℤ) - 1) * ((D : ℤ) - 1) ^ 2 + ((p : ℤ) + q - 1) * c * ((D : ℤ) - 1)
        - ((q : ℤ) - 1) * c ^ 2) : ℤ)) : ℝ) =
      r.den * ((D : ℝ) - 1) ^ 2 * (((p : ℝ) - 1) * (r : ℝ) -
        (((p : ℝ) - 1) + ((p : ℝ) + q - 1) * R - ((q : ℝ) - 1) * R ^ 2)) := by
    rw [hqr, ← hRdef]; push_cast; field_simp
  rw [hx] at hZ
  rw [abs_lt] at heps
  have hw9 : 1 / w ≤ 1 / 9 := one_div_le_one_div_of_le (by norm_num) hw
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hG0 : 0 < ((q : ℝ) - 1) * (S2 p q + R) - ((p : ℝ) + q - 1) := by
    have h2 : 2 < S2 p q + R := by linarith
    nlinarith [mul_lt_mul_of_pos_left h2 hq1]
  have hG4 : ((q : ℝ) - 1) * (S2 p q + R) - ((p : ℝ) + q - 1) < 4 * q := by
    have h5 : S2 p q + R < 5 := by linarith
    nlinarith [mul_lt_mul_of_pos_left h5 hq1]
  generalize hGdef : ((q : ℝ) - 1) * (S2 p q + R) - ((p : ℝ) + q - 1) = G at *
  have hZne : (r.num * ((p : ℤ) - 1) * ((D : ℤ) - 1) ^ 2 -
      r.den * (((p : ℤ) - 1) * ((D : ℤ) - 1) ^ 2 + ((p : ℤ) + q - 1) * c * ((D : ℤ) - 1)
        - ((q : ℤ) - 1) * c ^ 2) : ℤ) ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at hZ
    have : r.den * ((D : ℝ) - 1) ^ 2 * ((R - S2 p q) * G) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hb.ne' (pow_ne_zero 2 hd0)) (mul_ne_zero hne hG0.ne')
    exact this hZ.symm
  have habs : (1 : ℝ) ≤ |(((r.num * ((p : ℤ) - 1) * ((D : ℤ) - 1) ^ 2 -
      r.den * (((p : ℤ) - 1) * ((D : ℤ) - 1) ^ 2 + ((p : ℤ) + q - 1) * c * ((D : ℤ) - 1)
        - ((q : ℤ) - 1) * c ^ 2) : ℤ)) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hZne
  rw [hZ, abs_mul, abs_mul, abs_mul, abs_of_pos hb,
    abs_of_pos (by positivity : (0 : ℝ) < ((D : ℝ) - 1) ^ 2), abs_of_pos hG0] at habs
  have hpos : 0 < |R - S2 p q| := abs_pos.mpr hne
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = ((D : ℝ) - 1) ^ 2 * |R - S2 p q| := ⟨_, rfl⟩
  rw [← hYdef] at hsmall
  have hY0 : 0 < Y := by rw [hYdef]; positivity
  have habs' : 1 ≤ (r.den : ℝ) * Y * G := by
    rw [hYdef, mul_assoc, mul_assoc]
    rw [mul_assoc] at habs
    exact habs
  have hwK : (0 : ℝ) < w ^ (r.den + 3) := pow_pos hw0 _
  have hYw : Y * w ^ (r.den + 3) < 2 * (p : ℝ) ^ 3 := (lt_div_iff₀ hwK).1 hsmall
  have hden : (r.den : ℝ) < w ^ r.den := by
    have h1 : r.den < (q ^ 2) ^ r.den :=
      Nat.lt_pow_self (by nlinarith [hq.two_le] : 1 < q ^ 2)
    have h2 : ((r.den : ℕ) : ℝ) < (((q ^ 2) ^ r.den : ℕ) : ℝ) := by exact_mod_cast h1
    rw [← hwdef]
    simpa using h2
  have hP0 : (0 : ℝ) < p := by linarith
  have hQ0 : (0 : ℝ) < q := by linarith
  have hP3 : (p : ℝ) ^ 3 ≤ (q : ℝ) ^ 3 := pow_le_pow_left₀ hP0.le (by linarith) 3
  have hw3 : 8 * (p : ℝ) ^ 3 * q ≤ w ^ 3 := by
    have h8 : (0 : ℝ) ≤ w ^ 2 * (w - 8) := mul_nonneg (by positivity) (by linarith)
    have h9 := mul_le_mul_of_nonneg_right hP3 hQ0.le
    have h10 : (q : ℝ) ^ 3 * q = w ^ 2 := by rw [← hwdef]; ring
    have h11 : w ^ 2 * (w - 8) = w ^ 3 - 8 * w ^ 2 := by ring
    linarith
  have hbY : 0 < (r.den : ℝ) * Y := mul_pos hb hY0
  have h1 : w ^ (r.den + 3) ≤ (r.den : ℝ) * Y * G * w ^ (r.den + 3) :=
    le_mul_of_one_le_left hwK.le habs'
  have h2 : (r.den : ℝ) * Y * G ≤ (r.den : ℝ) * Y * (4 * q) :=
    mul_le_mul_of_nonneg_left hG4.le hbY.le
  have h3 := mul_le_mul_of_nonneg_right h2 hwK.le
  have h4 : (r.den : ℝ) * (4 * q) * (Y * w ^ (r.den + 3)) <
      (r.den : ℝ) * (4 * q) * (2 * (p : ℝ) ^ 3) :=
    mul_lt_mul_of_pos_left hYw (by positivity)
  have h5 : (r.den : ℝ) * (8 * (p : ℝ) ^ 3 * q) ≤ (r.den : ℝ) * w ^ 3 :=
    mul_le_mul_of_nonneg_left hw3 hb.le
  have h6 : (r.den : ℝ) * w ^ 3 < w ^ r.den * w ^ 3 :=
    mul_lt_mul_of_pos_right hden (pow_pos hw0 3)
  have h7 : w ^ (r.den + 3) = w ^ r.den * w ^ 3 := pow_add _ _ _
  have h8 : (r.den : ℝ) * Y * (4 * q) * w ^ (r.den + 3) =
      (r.den : ℝ) * (4 * q) * (Y * w ^ (r.den + 3)) := by ring
  have h9 : (r.den : ℝ) * (4 * q) * (2 * (p : ℝ) ^ 3) = (r.den : ℝ) * (8 * (p : ℝ) ^ 3 * q) := by
    ring
  linarith

end E269

-- Step Erdos269.erdos_269.variants.irrational.R1.H1: hypothesis H1 of that reduction
-- Credit: @timlantin

theorem OMA.solution : OMA.R_Erdos269_erdos_269_variants_irrational_R1.H1 := by
  intro p q hp hq hpq
  exact E269.irrational_of hp hq hpq (E269.series_formula hp hq hpq).2
    (E269.fan_identity hp hq hpq)
