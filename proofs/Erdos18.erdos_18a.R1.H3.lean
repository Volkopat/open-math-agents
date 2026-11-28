import OMAReductions.R_Erdos18_erdos_18a_R1

/-!
# Proof of `Erdos18.erdos_18a.R1.H3`

Given short representations of all integers `< 2 ^ T` as sums of at most
`C * (Nat.log 2 T + 1) ^ 6` distinct divisors of `(4 * T)!` for all sufficiently
large `T`, we prove that for all sufficiently large `n`, every `1 ≤ R ≤ n!` is a
sum of at most `K < (Real.log (Real.log (n! : ℝ))) ^ (9 : ℝ)` distinct divisors
of `n!`.

Method:
1. For small `n`, every `R ≤ n!` is a sum of at most `n + 1` distinct divisors of `n!`
   by factorial-base induction.
2. For large `n`, set `T = n / 8` and `s = T / (Nat.log 2 n + 1)`. Partition the
   interval `(4 * T, n]` into `O(log n)` blocks of length at most `s`, giving
   strictly increasing radix bases `B_m = m! / (4 * T)!` whose consecutive ratios
   satisfy `m! / m'! ≤ n ^ s < 2 ^ T`. Peeling digits via the hypothesis on `T`
   writes any `r < n! / (4 * T)!` as a sum of `O(C * (log n)^7)` distinct divisors
   of `n!` all strictly less than `n! / (4 * T)!`.
3. Recursing on the quotient `q = R / (n! / (4 * T)!) ≤ (4 * T)!` halves `n` at
   each level (`O(log n)` levels total), giving `O(C * (log n)^8)` distinct divisors
   of `n!`, which is strictly less than `(log (log (n!))) ^ 9` for all large `n`.
-/

namespace OMA.P_Erdos18_erdos_18a_R1_H3

open Filter Finset

/-- Elementary base case: every `R ≤ m!` is a sum of at most `m + 1` distinct
divisors of `m!`. -/
private lemma rep_factorial_trivial : ∀ (m R : ℕ), R ≤ m.factorial →
    ∃ D : Finset ℕ, D ⊆ m.factorial.divisors ∧ D.sum id = R ∧ D.card ≤ m + 1
  | 0, R, hR => by
    have h01 : R = 0 ∨ R = 1 := by simp only [Nat.factorial_zero] at hR; omega
    rcases h01 with rfl | rfl
    · exact ⟨∅, by simp, by simp, by simp⟩
    · exact ⟨{1}, by simp, by simp, by simp⟩
  | m + 1, R, hR => by
    let q := R / (m + 1)
    let r := R % (m + 1)
    have hq_le : q ≤ m.factorial := by
      have hmul : q * (m + 1) ≤ m.factorial * (m + 1) := by
        calc q * (m + 1) ≤ R := Nat.div_mul_le_self R (m + 1)
          _ ≤ (m + 1).factorial := hR
          _ = m.factorial * (m + 1) := by rw [Nat.factorial_succ, mul_comm]
      exact Nat.le_of_mul_le_mul_right hmul (Nat.succ_pos m)
    obtain ⟨D', hD'sub, hD'sum, hD'card⟩ := rep_factorial_trivial m q hq_le
    let D₁ : Finset ℕ := D'.image (· * (m + 1))
    have hinj : Function.Injective (fun x : ℕ => x * (m + 1)) :=
      fun a b hab => Nat.eq_of_mul_eq_mul_right (Nat.succ_pos m) hab
    have hD₁_sub : D₁ ⊆ (m + 1).factorial.divisors := by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      have hd_dvd : d ∣ m.factorial := (Nat.mem_divisors.mp (hD'sub hd)).1
      refine Nat.mem_divisors.mpr ⟨?_, (Nat.factorial_pos (m + 1)).ne'⟩
      rw [Nat.factorial_succ, mul_comm (m + 1)]
      exact mul_dvd_mul_right hd_dvd (m + 1)
    have hD₁_sum : D₁.sum id = q * (m + 1) := by
      rw [Finset.sum_image (fun a _ b _ h => hinj h)]
      simp only [id_eq, ← Finset.sum_mul]
      rw [← hD'sum]
      simp only [id_eq]
    have hD₁_card : D₁.card ≤ m + 1 := by
      rw [Finset.card_image_of_injective _ hinj]
      exact hD'card
    have hR_eq : r + q * (m + 1) = R := by
      have := Nat.div_add_mod R (m + 1)
      dsimp only [q, r]
      linarith
    by_cases hr0 : r = 0
    · refine ⟨D₁, hD₁_sub, ?_, by omega⟩
      rw [hD₁_sum]; omega
    · have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
      have hr_lt : r < m + 1 := Nat.mod_lt R (Nat.succ_pos m)
      have hr_dvd : r ∣ (m + 1).factorial := Nat.dvd_factorial hr_pos (by omega)
      have hr_notMem : r ∉ D₁ := by
        intro hmem
        obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp hmem
        have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos
          (Nat.mem_divisors.mp (hD'sub hd)).1 (Nat.factorial_pos m)
        have hge : m + 1 ≤ d * (m + 1) := Nat.le_mul_of_pos_left (m + 1) hd_pos
        omega
      refine ⟨insert r D₁, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact Nat.mem_divisors.mpr ⟨hr_dvd, (Nat.factorial_pos (m + 1)).ne'⟩
        · exact hD₁_sub hx'
      · rw [Finset.sum_insert hr_notMem, id_eq, hD₁_sum, hR_eq]
      · rw [Finset.card_insert_of_notMem hr_notMem]
        omega

/-- Upper bound on the factorial quotient `m! / m'! ≤ m ^ (m - m')`. -/
private lemma factorial_div_le_pow : ∀ (k m' : ℕ),
    (m' + k).factorial / m'.factorial ≤ (m' + k) ^ k
  | 0, m' => by simp [Nat.div_self (Nat.factorial_pos m')]
  | k + 1, m' => by
    have hdvd : m'.factorial ∣ (m' + k).factorial := Nat.factorial_dvd_factorial (by omega)
    have hstep : (m' + (k + 1)).factorial / m'.factorial =
        (m' + k + 1) * ((m' + k).factorial / m'.factorial) := by
      rw [show m' + (k + 1) = (m' + k) + 1 by omega, Nat.factorial_succ,
        Nat.mul_div_assoc _ hdvd]
    rw [hstep]
    calc (m' + k + 1) * ((m' + k).factorial / m'.factorial)
        ≤ (m' + k + 1) * (m' + k) ^ k := Nat.mul_le_mul_left _ (factorial_div_le_pow k m')
      _ ≤ (m' + k + 1) * (m' + k + 1) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k)
      _ = (m' + (k + 1)) ^ (k + 1) := by
        rw [show m' + (k + 1) = m' + k + 1 by omega, pow_succ']

/-- Peeling lemma: for fixed `T, n, s` with `4 * T ≤ n`, `1 ≤ s`, and `n ^ s < 2 ^ T`,
any `R < m! / (4 * T)!` (with `4 * T ≤ m ≤ n`) is a sum of at most
`((m - 4 * T + s - 1) / s) * M` distinct divisors of `m!`, given that every `q < 2 ^ T`
is a sum of at most `M` distinct divisors of `(4 * T)!`. -/
private lemma peel_factorial {T n s M : ℕ} (hs : 1 ≤ s) (hpow : n ^ s < 2 ^ T)
    (hrep : ∀ q < 2 ^ T, ∃ D : Finset ℕ,
      D ⊆ (4 * T).factorial.divisors ∧ D.sum id = q ∧ D.card ≤ M) :
    ∀ (d m R : ℕ), m = 4 * T + d → m ≤ n → R < m.factorial / (4 * T).factorial →
      ∃ D : Finset ℕ, D ⊆ m.factorial.divisors ∧ D.sum id = R ∧
        D.card ≤ ((d + s - 1) / s) * M := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro m R hm hmn hR
    by_cases hd0 : d = 0
    · subst hd0
      have hm_eq : m = 4 * T := by omega
      subst hm_eq
      rw [Nat.div_self (Nat.factorial_pos (4 * T))] at hR
      have hR0 : R = 0 := by omega
      subst hR0
      exact ⟨∅, by simp, by simp, by simp⟩
    · let d' := d - s
      let m' := 4 * T + d'
      have hd'_lt : d' < d := by dsimp only [d']; omega
      have hm'_le : m' ≤ m := by dsimp only [m', d']; omega
      have hdiff_le : m - m' ≤ s := by dsimp only [m', d']; omega
      have hdvd_m' : (4 * T).factorial ∣ m'.factorial := Nat.factorial_dvd_factorial (by omega)
      have hdvd_mm' : m'.factorial ∣ m.factorial := Nat.factorial_dvd_factorial hm'_le
      let B' := m'.factorial / (4 * T).factorial
      let Q := m.factorial / m'.factorial
      have hB'_pos : 0 < B' :=
        Nat.div_pos (Nat.factorial_le (by omega)) (Nat.factorial_pos (4 * T))
      have hB_eq : m.factorial / (4 * T).factorial = B' * Q := by
        have h1 : (4 * T).factorial * (B' * Q) = m.factorial := by
          calc (4 * T).factorial * (B' * Q)
              = ((4 * T).factorial * B') * Q := by ring
            _ = m'.factorial * Q := by rw [Nat.mul_div_cancel' hdvd_m']
            _ = m.factorial := Nat.mul_div_cancel' hdvd_mm'
        exact Nat.div_eq_of_eq_mul_right (Nat.factorial_pos (4 * T)) h1.symm
      have hQ_lt : Q < 2 ^ T := by
        have h1 : Q ≤ m ^ (m - m') := by
          dsimp only [Q]
          have heq : m' + (m - m') = m := by omega
          simpa only [heq] using factorial_div_le_pow (m - m') m'
        calc Q ≤ m ^ (m - m') := h1
          _ ≤ n ^ (m - m') := Nat.pow_le_pow_left hmn _
          _ ≤ n ^ s := by
            have hn_pos : 1 ≤ n := by omega
            exact Nat.pow_le_pow_right hn_pos hdiff_le
          _ < 2 ^ T := hpow
      let q := R / B'
      let r := R % B'
      have hq_lt : q < 2 ^ T := by
        have hq_lt_Q : q < Q := by
          dsimp only [q]
          rw [Nat.div_lt_iff_lt_mul hB'_pos]
          rw [mul_comm, ← hB_eq]
          exact hR
        exact lt_trans hq_lt_Q hQ_lt
      have hr_lt : r < B' := Nat.mod_lt R hB'_pos
      obtain ⟨Dq, hDq_sub, hDq_sum, hDq_card⟩ := hrep q hq_lt
      obtain ⟨Dlo, hDlo_sub, hDlo_sum, hDlo_card⟩ :=
        ih d' hd'_lt m' r rfl (le_trans hm'_le hmn) hr_lt
      let Dhi : Finset ℕ := Dq.image (· * B')
      have hinj : Function.Injective (fun x : ℕ => x * B') :=
        fun a b hab => Nat.eq_of_mul_eq_mul_right hB'_pos hab
      have hDhi_sub : Dhi ⊆ m.factorial.divisors := by
        intro x hx
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
        have hu_dvd : u ∣ (4 * T).factorial := (Nat.mem_divisors.mp (hDq_sub hu)).1
        refine Nat.mem_divisors.mpr ⟨?_, (Nat.factorial_pos m).ne'⟩
        have h1 : u * B' ∣ (4 * T).factorial * B' := mul_dvd_mul_right hu_dvd B'
        rw [Nat.mul_div_cancel' hdvd_m'] at h1
        exact dvd_trans h1 hdvd_mm'
      have hDlo_sub' : Dlo ⊆ m.factorial.divisors := by
        intro y hy
        have hy_dvd : y ∣ m'.factorial := (Nat.mem_divisors.mp (hDlo_sub hy)).1
        exact Nat.mem_divisors.mpr ⟨dvd_trans hy_dvd hdvd_mm', (Nat.factorial_pos m).ne'⟩
      have hdisj : Disjoint Dlo Dhi := by
        rw [Finset.disjoint_left]
        intro y hy hy_hi
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy_hi
        have hu_pos : 1 ≤ u := Nat.pos_of_dvd_of_pos
          (Nat.mem_divisors.mp (hDq_sub hu)).1 (Nat.factorial_pos (4 * T))
        have hge : B' ≤ u * B' := Nat.le_mul_of_pos_left B' hu_pos
        have hle : u * B' ≤ r := by
          rw [← hDlo_sum]
          exact Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hy
        omega
      have hDhi_sum : Dhi.sum id = q * B' := by
        rw [Finset.sum_image (fun a _ b _ h => hinj h)]
        simp only [id_eq, ← Finset.sum_mul]
        rw [← hDq_sum]
        simp only [id_eq]
      have hDhi_card : Dhi.card ≤ M := by
        rw [Finset.card_image_of_injective _ hinj]
        exact hDq_card
      have hdiv_step : (d' + s - 1) / s + 1 ≤ (d + s - 1) / s := by
        by_cases hds : s ≤ d
        · have h1 : d' + s - 1 + s = d + s - 1 := by dsimp only [d']; omega
          rw [← h1, Nat.add_div_right _ (by omega : 0 < s)]
        · have hd'0 : d' = 0 := by dsimp only [d']; omega
          rw [hd'0, zero_add]
          have hzero : (s - 1) / s = 0 := Nat.div_eq_of_lt (by omega)
          have hone : 1 ≤ (d + s - 1) / s := (Nat.le_div_iff_mul_le (by omega : 0 < s)).mpr (by omega)
          omega
      refine ⟨Dlo ∪ Dhi, Finset.union_subset hDlo_sub' hDhi_sub, ?_, ?_⟩
      · rw [Finset.sum_union hdisj, hDlo_sum, hDhi_sum]
        have := Nat.div_add_mod R B'
        dsimp only [q, r]
        linarith
      · rw [Finset.card_union_of_disjoint hdisj]
        calc Dlo.card + Dhi.card
            ≤ ((d' + s - 1) / s) * M + M := Nat.add_le_add hDlo_card hDhi_card
          _ = ((d' + s - 1) / s + 1) * M := by ring
          _ ≤ ((d + s - 1) / s) * M := Nat.mul_le_mul_right M hdiv_step

/-- For `n ≥ 64`, `Nat.log 2 n + 1 ≤ n / 8`. -/
private lemma log2_succ_le_div_eight {n : ℕ} (hn : 64 ≤ n) : Nat.log 2 n + 1 ≤ n / 8 := by
  have hlt : ∀ k : ℕ, 6 ≤ k → 8 * (k + 1) ≤ 2 ^ k := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      by_cases h6 : 6 ≤ k
      · have hih := ih h6
        have hpow : 8 ≤ 2 ^ k := le_trans (by omega) hih
        rw [pow_succ]
        omega
      · have hk6 : k = 5 := by omega
        subst hk6
        norm_num
  have hlog_ge : 6 ≤ Nat.log 2 n := by
    rw [Nat.le_log_iff_pow_le (by norm_num) (by omega)]
    norm_num
    omega
  have h1 : 8 * (Nat.log 2 n + 1) ≤ 2 ^ Nat.log 2 n := hlt _ hlog_ge
  have h2 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  omega

/-- Combined recursive representation bound for all `n` and `R ≤ n!`. -/
private lemma rep_factorial_poly {C T₀ : ℕ} (hT₀ : 16 ≤ T₀)
    (hrep : ∀ T ≥ T₀, ∀ q < 2 ^ T, ∃ D : Finset ℕ,
      D ⊆ (4 * T).factorial.divisors ∧ D.sum id = q ∧ D.card ≤ C * (Nat.log 2 T + 1) ^ 6) :
    ∀ n : ℕ, ∀ R ≤ n.factorial, ∃ D : Finset ℕ,
      D ⊆ n.factorial.divisors ∧ D.sum id = R ∧
      D.card ≤ (8 * T₀ + 64) + 19 * C * (Nat.log 2 n + 1) ^ 8 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro R hR
    by_cases hsmall : n < max (8 * T₀) 64
    · obtain ⟨D, hsub, hsum, hcard⟩ := rep_factorial_trivial n R hR
      refine ⟨D, hsub, hsum, ?_⟩
      have : n + 1 ≤ 8 * T₀ + 64 := by omega
      omega
    · have hn64 : 64 ≤ n := by omega
      have hT_ge : T₀ ≤ n / 8 := by omega
      let T := n / 8
      let m₀ := 4 * T
      let s := T / (Nat.log 2 n + 1)
      have hlog_le : Nat.log 2 n + 1 ≤ T := log2_succ_le_div_eight hn64
      have hs_pos : 1 ≤ s :=
        (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr (by simpa only [one_mul] using hlog_le)
      have hpow : n ^ s < 2 ^ T := by
        have hn_lt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
        have hs_mul : s * (Nat.log 2 n + 1) ≤ T := Nat.div_mul_le_self T (Nat.log 2 n + 1)
        calc n ^ s < (2 ^ (Nat.log 2 n + 1)) ^ s := Nat.pow_lt_pow_left hn_lt (by omega)
          _ = 2 ^ ((Nat.log 2 n + 1) * s) := (pow_mul 2 _ _).symm
          _ = 2 ^ (s * (Nat.log 2 n + 1)) := by rw [mul_comm]
          _ ≤ 2 ^ T := Nat.pow_le_pow_right (by norm_num) hs_mul
      have hm₀_le_half : 2 * m₀ ≤ n := by dsimp only [m₀, T]; omega
      have hm₀_lt : m₀ < n := by omega
      have hm₀_pos : 0 < m₀ := by dsimp only [m₀, T]; omega
      have hlog_m₀ : Nat.log 2 m₀ + 1 ≤ Nat.log 2 n := by
        have h1 : 2 ^ (Nat.log 2 m₀ + 1) ≤ 2 * m₀ := by
          rw [pow_succ']
          exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))
        exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (le_trans h1 hm₀_le_half)
      have hdvd_m₀ : m₀.factorial ∣ n.factorial := Nat.factorial_dvd_factorial (by omega)
      let B := n.factorial / m₀.factorial
      have hB_pos : 0 < B :=
        Nat.div_pos (Nat.factorial_le (by omega)) (Nat.factorial_pos m₀)
      let q := R / B
      let r := R % B
      have hq_le : q ≤ m₀.factorial := by
        have hmul : q * B ≤ m₀.factorial * B := by
          calc q * B ≤ R := Nat.div_mul_le_self R B
            _ ≤ n.factorial := hR
            _ = m₀.factorial * B := (Nat.mul_div_cancel' hdvd_m₀).symm
        exact Nat.le_of_mul_le_mul_right hmul hB_pos
      have hr_lt : r < B := Nat.mod_lt R hB_pos
      obtain ⟨Dlo, hDlo_sub, hDlo_sum, hDlo_card⟩ :=
        peel_factorial hs_pos hpow (hrep T hT_ge) (n - m₀) n r (by omega) le_rfl hr_lt
      obtain ⟨Dq, hDq_sub, hDq_sum, hDq_card⟩ := ih m₀ hm₀_lt q hq_le
      let Dhi : Finset ℕ := Dq.image (· * B)
      have hinj : Function.Injective (fun x : ℕ => x * B) :=
        fun a b hab => Nat.eq_of_mul_eq_mul_right hB_pos hab
      have hDhi_sub : Dhi ⊆ n.factorial.divisors := by
        intro x hx
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
        have hu_dvd : u ∣ m₀.factorial := (Nat.mem_divisors.mp (hDq_sub hu)).1
        refine Nat.mem_divisors.mpr ⟨?_, (Nat.factorial_pos n).ne'⟩
        have h1 : u * B ∣ m₀.factorial * B := mul_dvd_mul_right hu_dvd B
        rwa [Nat.mul_div_cancel' hdvd_m₀] at h1
      have hdisj : Disjoint Dlo Dhi := by
        rw [Finset.disjoint_left]
        intro y hy hy_hi
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy_hi
        have hu_pos : 1 ≤ u := Nat.pos_of_dvd_of_pos
          (Nat.mem_divisors.mp (hDq_sub hu)).1 (Nat.factorial_pos m₀)
        have hge : B ≤ u * B := Nat.le_mul_of_pos_left B hu_pos
        have hle : u * B ≤ r := by
          rw [← hDlo_sum]
          exact Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hy
        omega
      have hDhi_sum : Dhi.sum id = q * B := by
        rw [Finset.sum_image (fun a _ b _ h => hinj h)]
        simp only [id_eq, ← Finset.sum_mul]
        rw [← hDq_sum]
        simp only [id_eq]
      have hDhi_card : Dhi.card ≤ (8 * T₀ + 64) + 19 * C * (Nat.log 2 m₀ + 1) ^ 8 := by
        rw [Finset.card_image_of_injective _ hinj]
        exact hDq_card
      -- Bound the number of peeling chunks: `(n - m₀ + s - 1) / s ≤ 19 * (Nat.log 2 n + 1)`
      have hchunks : (n - m₀ + s - 1) / s ≤ 19 * (Nat.log 2 n + 1) := by
        have hT_le_2s : T ≤ 2 * s * (Nat.log 2 n + 1) := by
          have hdiv := Nat.div_add_mod T (Nat.log 2 n + 1)
          have hmod : T % (Nat.log 2 n + 1) < Nat.log 2 n + 1 :=
            Nat.mod_lt T (Nat.succ_pos _)
          have hmul_le : 1 * (Nat.log 2 n + 1) ≤ s * (Nat.log 2 n + 1) :=
            Nat.mul_le_mul_right _ hs_pos
          dsimp only [s] at *
          nlinarith
        have hn_le_9T : n ≤ 9 * T := by dsimp only [T]; omega
        have hsub_lt : n - m₀ + s - 1 < n + s := by omega
        have hnum : n - m₀ + s - 1 < (19 * (Nat.log 2 n + 1) + 1) * s := by
          calc n - m₀ + s - 1 < n + s := hsub_lt
            _ ≤ 9 * T + s := by omega
            _ ≤ 9 * (2 * s * (Nat.log 2 n + 1)) + s := Nat.add_le_add_right (Nat.mul_le_mul_left 9 hT_le_2s) s
            _ ≤ (19 * (Nat.log 2 n + 1) + 1) * s := by
              have : 18 * (Nat.log 2 n + 1) * s + s ≤ (19 * (Nat.log 2 n + 1) + 1) * s := by nlinarith
              linarith
        exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega : 0 < s)).mpr hnum)
      have hlogT_le : Nat.log 2 T + 1 ≤ Nat.log 2 n + 1 :=
        Nat.add_le_add_right (Nat.log_mono_right (by dsimp only [T]; omega)) 1
      have hDlo_bound : Dlo.card ≤ 19 * C * (Nat.log 2 n + 1) ^ 7 := by
        calc Dlo.card
            ≤ ((n - m₀ + s - 1) / s) * (C * (Nat.log 2 T + 1) ^ 6) := hDlo_card
          _ ≤ (19 * (Nat.log 2 n + 1)) * (C * (Nat.log 2 n + 1) ^ 6) :=
              Nat.mul_le_mul hchunks
                (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hlogT_le 6))
          _ = 19 * C * (Nat.log 2 n + 1) ^ 7 := by ring
      -- Combine: `(Nat.log 2 m₀ + 1)^8 + (Nat.log 2 n + 1)^7 ≤ (Nat.log 2 n + 1)^8`
      have hpow_comb : (Nat.log 2 m₀ + 1) ^ 8 + (Nat.log 2 n + 1) ^ 7 ≤ (Nat.log 2 n + 1) ^ 8 := by
        have h1 : (Nat.log 2 m₀ + 1) ^ 8 ≤ (Nat.log 2 n) ^ 8 :=
          Nat.pow_le_pow_left hlog_m₀ 8
        have h2 : (Nat.log 2 n) ^ 8 ≤ (Nat.log 2 n) * (Nat.log 2 n + 1) ^ 7 := by
          calc (Nat.log 2 n) ^ 8
              = (Nat.log 2 n) * (Nat.log 2 n) ^ 7 := by ring
            _ ≤ (Nat.log 2 n) * (Nat.log 2 n + 1) ^ 7 :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ _) 7)
        calc (Nat.log 2 m₀ + 1) ^ 8 + (Nat.log 2 n + 1) ^ 7
            ≤ (Nat.log 2 n) * (Nat.log 2 n + 1) ^ 7 + 1 * (Nat.log 2 n + 1) ^ 7 := by linarith
          _ = (Nat.log 2 n + 1) ^ 8 := by ring
      have hR_eq : r + q * B = R := by
        have hmod := Nat.div_add_mod R B
        dsimp only [q, r]
        rw [add_comm, mul_comm]
        exact hmod
      refine ⟨Dlo ∪ Dhi, Finset.union_subset hDlo_sub hDhi_sub, ?_, ?_⟩
      · rw [Finset.sum_union hdisj, hDlo_sum, hDhi_sum, hR_eq]
      · rw [Finset.card_union_of_disjoint hdisj]
        calc Dlo.card + Dhi.card
            ≤ 19 * C * (Nat.log 2 n + 1) ^ 7 +
              ((8 * T₀ + 64) + 19 * C * (Nat.log 2 m₀ + 1) ^ 8) :=
              Nat.add_le_add hDlo_bound hDhi_card
          _ = (8 * T₀ + 64) + 19 * C * ((Nat.log 2 m₀ + 1) ^ 8 + (Nat.log 2 n + 1) ^ 7) := by ring
          _ ≤ (8 * T₀ + 64) + 19 * C * (Nat.log 2 n + 1) ^ 8 :=
              Nat.add_le_add_left (Nat.mul_le_mul_left _ hpow_comb) _

/-- Simple lower bound `2 ^ n ≤ n!` for `n ≥ 4`. -/
private lemma two_pow_le_factorial : ∀ n : ℕ, 4 ≤ n → 2 ^ n ≤ n.factorial
  | 0, h => by omega
  | 1, h => by omega
  | 2, h => by omega
  | 3, h => by omega
  | 4, _ => by decide
  | n + 5, _ => by
    have ih := two_pow_le_factorial (n + 4) (by omega)
    rw [pow_succ', Nat.factorial_succ]
    exact Nat.mul_le_mul (by omega) ih

/-- Asymptotic comparison: for any constants `A, B`, eventually
`A + B * (Nat.log 2 n + 1) ^ 8 < (Real.log (Real.log (n! : ℝ))) ^ (9 : ℝ)`. -/
private lemma poly_log_lt_log_log_factorial_pow_nine (A B : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ((A + B * (Nat.log 2 n + 1) ^ 8 : ℕ) : ℝ) <
        (Real.log (Real.log (n.factorial : ℝ))) ^ (9 : ℝ) := by
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  let M : ℝ := 512 * ((A : ℝ) + (B : ℝ) * 3 ^ 8) + 4
  have hten : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_ge_atTop 16, hten.eventually_gt_atTop M] with n hn hlogn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hlogn_ge2 : (2 : ℝ) ≤ Real.log (n : ℝ) := by
    have hnn : (0 : ℝ) ≤ 512 * ((A : ℝ) + (B : ℝ) * 3 ^ 8) := by positivity
    have hM_ge : (4 : ℝ) ≤ M := by dsimp only [M]; linarith
    linarith
  have hfac_ge : (2 : ℝ) ^ n ≤ (n.factorial : ℝ) := by
    exact_mod_cast two_pow_le_factorial n (by omega)
  have hlog_fac : (n : ℝ) / 2 ≤ Real.log (n.factorial : ℝ) := by
    have h1 : Real.log ((2 : ℝ) ^ n) ≤ Real.log (n.factorial : ℝ) :=
      Real.log_le_log (by positivity) hfac_ge
    rw [Real.log_pow] at h1
    nlinarith
  have hlog_log_fac : Real.log (n : ℝ) / 2 ≤ Real.log (Real.log (n.factorial : ℝ)) := by
    have h1 : Real.log ((n : ℝ) / 2) ≤ Real.log (Real.log (n.factorial : ℝ)) :=
      Real.log_le_log (by positivity) hlog_fac
    rw [Real.log_div hn_pos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h1
    have hlog2_lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    linarith
  have hnatlog : ((Nat.log 2 n : ℕ) : ℝ) + 1 ≤ 3 * Real.log (n : ℝ) := by
    have hpow_le : (2 : ℝ) ^ (Nat.log 2 n) ≤ (n : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have h1 : Real.log ((2 : ℝ) ^ (Nat.log 2 n)) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by positivity) hpow_le
    rw [Real.log_pow] at h1
    nlinarith
  have hlhs : ((A + B * (Nat.log 2 n + 1) ^ 8 : ℕ) : ℝ) ≤
      ((A : ℝ) + (B : ℝ) * 3 ^ 8) * (Real.log (n : ℝ)) ^ 8 := by
    push_cast
    have hpow8 : ((Nat.log 2 n : ℝ) + 1) ^ 8 ≤ (3 * Real.log (n : ℝ)) ^ 8 :=
      pow_le_pow_left₀ (by positivity) hnatlog 8
    have h1_le_pow8 : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 8 := by
      have : (1 : ℝ) ≤ Real.log (n : ℝ) := by linarith
      exact one_le_pow₀ this
    have hA_le : (A : ℝ) ≤ (A : ℝ) * (Real.log (n : ℝ)) ^ 8 :=
      le_mul_of_one_le_right (Nat.cast_nonneg A) h1_le_pow8
    have hB_le : (B : ℝ) * ((Nat.log 2 n : ℝ) + 1) ^ 8 ≤
        (B : ℝ) * (3 ^ 8 * (Real.log (n : ℝ)) ^ 8) := by
      rw [← mul_pow]
      exact mul_le_mul_of_nonneg_left hpow8 (Nat.cast_nonneg B)
    nlinarith
  have hrhs_ge : (Real.log (n : ℝ) / 2) ^ 9 ≤
      (Real.log (Real.log (n.factorial : ℝ))) ^ (9 : ℝ) := by
    rw [show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) hlog_log_fac 9
  have hstrict : ((A : ℝ) + (B : ℝ) * 3 ^ 8) * (Real.log (n : ℝ)) ^ 8 <
      (Real.log (n : ℝ) / 2) ^ 9 := by
    have hpow8_pos : (0 : ℝ) < (Real.log (n : ℝ)) ^ 8 := by positivity
    have hdiv : (Real.log (n : ℝ) / 2) ^ 9 =
        (Real.log (n : ℝ) / 512) * (Real.log (n : ℝ)) ^ 8 := by ring
    rw [hdiv]
    have hcoeff : (A : ℝ) + (B : ℝ) * 3 ^ 8 < Real.log (n : ℝ) / 512 := by
      dsimp only [M] at hlogn
      linarith
    exact mul_lt_mul_of_pos_right hcoeff hpow8_pos
  exact lt_of_le_of_lt hlhs (lt_of_lt_of_le hstrict hrhs_ge)

end OMA.P_Erdos18_erdos_18a_R1_H3

theorem OMA.solution : OMA.R_Erdos18_erdos_18a_R1.H3 := by
  rintro ⟨C, hT⟩
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp hT
  let T₀ := max T₁ 16
  have hrep : ∀ T ≥ T₀, ∀ q < 2 ^ T, ∃ D : Finset ℕ,
      D ⊆ (4 * T).factorial.divisors ∧ D.sum id = q ∧
      D.card ≤ C * (Nat.log 2 T + 1) ^ 6 :=
    fun T hT' => hT₁ T (le_trans (le_max_left _ _) hT')
  filter_upwards [OMA.P_Erdos18_erdos_18a_R1_H3.poly_log_lt_log_log_factorial_pow_nine
    (8 * T₀ + 64) (19 * C)] with n hn
  refine ⟨(8 * T₀ + 64) + 19 * C * (Nat.log 2 n + 1) ^ 8, hn, ?_⟩
  intro R _ hR
  exact OMA.P_Erdos18_erdos_18a_R1_H3.rep_factorial_poly (le_max_right T₁ 16) hrep n R hR
