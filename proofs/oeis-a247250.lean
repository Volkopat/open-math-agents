import OMAStatements.S_oeis_a247250

/-!
# Primitive prime divisors in the Pell sequence (OEIS A247250)

We prove Carmichael's theorem for Pell numbers: for every `n > 1`, `pell n` has a primitive prime
divisor `p` (a prime dividing `pell n` that divides no `pell m` for `0 < m < n`).
-/

namespace PellPrimDiv

open scoped BigOperators

abbrev P : ℕ → ℕ := OMA.S_oeis_a247250.pell

def pellQ : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * pellQ (n + 1) + pellQ n

lemma pell_step : ∀ n : ℕ, P (n + 1) = pellQ n + P n ∧ pellQ (n + 1) = pellQ n + 2 * P n
  | 0 => ⟨rfl, rfl⟩
  | 1 => ⟨rfl, rfl⟩
  | n + 2 => by
    obtain ⟨hp1, hq1⟩ := pell_step n
    obtain ⟨hp2, hq2⟩ := pell_step (n + 1)
    have h2 : n + 1 + 1 = n + 2 := rfl
    rw [h2] at hp2 hq2
    change 2 * P (n + 2) + P (n + 1) = (2 * pellQ (n + 1) + pellQ n) + P (n + 2) ∧
      2 * pellQ (n + 2) + pellQ (n + 1) = (2 * pellQ (n + 1) + pellQ n) + 2 * P (n + 2)
    omega

lemma pellQ_pos : ∀ n : ℕ, 0 < pellQ n
  | 0 => by decide
  | n + 1 => by
    have h := (pell_step n).2
    have ih := pellQ_pos n
    omega

lemma pell_pos : ∀ {n : ℕ}, 0 < n → 0 < P n
  | 0, h => by omega
  | n + 1, _ => by
    have h := (pell_step n).1
    have hq := pellQ_pos n
    omega

lemma pell_norm (n : ℕ) : (pellQ n : ℤ) ^ 2 - 2 * (P n : ℤ) ^ 2 = (-1 : ℤ) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨hp, hq⟩ := pell_step n
    rw [hp, hq]
    push_cast
    calc
      ((pellQ n : ℤ) + 2 * (P n : ℤ)) ^ 2 - 2 * ((pellQ n : ℤ) + (P n : ℤ)) ^ 2
        = -((pellQ n : ℤ) ^ 2 - 2 * (P n : ℤ) ^ 2) := by ring
      _ = -((-1 : ℤ) ^ n) := by rw [ih]
      _ = (-1 : ℤ) ^ (n + 1) := by rw [pow_succ]; ring

lemma coprime_pellQ_pell (n : ℕ) : Nat.Coprime (pellQ n) (P n) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  apply Nat.eq_one_of_dvd_one
  let g := Nat.gcd (pellQ n) (P n)
  have hgq : (g : ℤ) ∣ (pellQ n : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
  have hgp : (g : ℤ) ∣ (P n : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)
  have hgn : (g : ℤ) ∣ (pellQ n : ℤ) ^ 2 - 2 * (P n : ℤ) ^ 2 := by
    refine dvd_sub (dvd_pow hgq (by decide)) ?_
    exact dvd_mul_of_dvd_right (dvd_pow hgp (by decide)) 2
  rw [pell_norm] at hgn
  have h1 : (-1 : ℤ) ^ n ∣ 1 := ⟨(-1 : ℤ) ^ n, by rw [← mul_pow]; norm_num⟩
  have hg1 : (g : ℤ) ∣ (1 : ℤ) := dvd_trans hgn h1
  exact Int.natCast_dvd_natCast.mp hg1

lemma pell_add (m : ℕ) : ∀ n : ℕ,
    P (m + n) = pellQ m * P n + P m * pellQ n ∧
    pellQ (m + n) = pellQ m * pellQ n + 2 * P m * P n
  | 0 => by simp [P, OMA.S_oeis_a247250.pell, pellQ]
  | n + 1 => by
    obtain ⟨ihp, ihq⟩ := pell_add m n
    obtain ⟨hpmn, hqmn⟩ := pell_step (m + n)
    obtain ⟨hpn, hqn⟩ := pell_step n
    rw [← Nat.add_assoc, hpmn, hqmn, ihp, ihq, hpn, hqn]
    constructor <;> ring

lemma pell_dvd_pell {m n : ℕ} (h : m ∣ n) : P m ∣ P n := by
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => simp [P, OMA.S_oeis_a247250.pell]
  | succ k ih =>
    rw [Nat.mul_succ, (pell_add (m * k) m).1]
    exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_left ih _)

lemma gcd_pell_add (m n : ℕ) : Nat.gcd (P (m + n)) (P m) = Nat.gcd (P n) (P m) := by
  apply Nat.dvd_antisymm
  · refine Nat.dvd_gcd ?_ (Nat.gcd_dvd_right _ _)
    let g := Nat.gcd (P (m + n)) (P m)
    have h1 : g ∣ P (m + n) := Nat.gcd_dvd_left _ _
    have h2 : g ∣ P m * pellQ n :=
      dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) _
    rw [(pell_add m n).1] at h1
    have h3 : g ∣ pellQ m * P n :=
      (Nat.dvd_add_iff_left h2).mpr h1
    have hcop : Nat.Coprime g (pellQ m) :=
      (coprime_pellQ_pell m).symm.coprime_dvd_left (Nat.gcd_dvd_right _ _)
    exact hcop.dvd_of_dvd_mul_left h3
  · refine Nat.dvd_gcd ?_ (Nat.gcd_dvd_right _ _)
    rw [(pell_add m n).1]
    exact dvd_add (dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) _)
      (dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) _)

lemma gcd_pell_add_mul (m n : ℕ) : ∀ q : ℕ, Nat.gcd (P (n + m * q)) (P m) = Nat.gcd (P n) (P m)
  | 0 => by simp
  | q + 1 => by
    have heq : n + m * (q + 1) = m + (n + m * q) := by ring
    rw [heq, gcd_pell_add, gcd_pell_add_mul m n q]

lemma pell_gcd (m n : ℕ) : Nat.gcd (P m) (P n) = P (Nat.gcd m n) := by
  induction m, n using Nat.gcd.induction with
  | H0 n => simp [P, OMA.S_oeis_a247250.pell]
  | H1 m n _ ih =>
    rw [Nat.gcd_rec m n, ← ih, Nat.gcd_comm (P m) (P n)]
    conv_lhs => rw [← Nat.mod_add_div n m]
    rw [gcd_pell_add_mul m (n % m) (n / m), Nat.gcd_comm]

lemma pell_mul_expansion (k : ℕ) : ∀ u : ℕ, 0 < u → ∃ a b : ℕ,
    pellQ (u * k) = pellQ k ^ u + P k ^ 2 * a ∧
    P (u * k) = u * pellQ k ^ (u - 1) * P k + P k ^ 3 * b
  | 0, h => by omega
  | 1, _ => ⟨0, 0, by simp, by simp⟩
  | u + 2, _ => by
    obtain ⟨a, b, hq, hp⟩ := pell_mul_expansion k (u + 1) (by omega)
    have hmul : (u + 2) * k = (u + 1) * k + k := by ring
    obtain ⟨hp_add, hq_add⟩ := pell_add ((u + 1) * k) k
    refine ⟨a * pellQ k + 2 * (u + 1) * pellQ k ^ u + 2 * P k ^ 2 * b, a + b * pellQ k, ?_, ?_⟩
    · rw [hmul, hq_add, hq, hp]
      change (pellQ k ^ (u + 1) + P k ^ 2 * a) * pellQ k +
          2 * ((u + 1) * pellQ k ^ u * P k + P k ^ 3 * b) * P k =
        pellQ k ^ (u + 2) + P k ^ 2 * (a * pellQ k + 2 * (u + 1) * pellQ k ^ u + 2 * P k ^ 2 * b)
      ring
    · rw [hmul, hp_add, hq, hp]
      change (pellQ k ^ (u + 1) + P k ^ 2 * a) * P k +
          ((u + 1) * pellQ k ^ u * P k + P k ^ 3 * b) * pellQ k =
        (u + 2) * pellQ k ^ (u + 1) * P k + P k ^ 3 * (a + b * pellQ k)
      ring

lemma pell_factorization_mul_prime {k p q : ℕ} (hk : 0 < k) (hp : p.Prime) (hq : q.Prime)
    (hdiv : p ∣ P k) :
    (P (q * k)).factorization p = (P k).factorization p + if p = q then 1 else 0 := by
  obtain ⟨_, b, _, hexp⟩ := pell_mul_expansion k q hq.pos
  let M := q * pellQ k ^ (q - 1) + P k ^ 2 * b
  have hfac_eq : P (q * k) = P k * M := by
    rw [hexp]
    dsimp [M]
    ring
  have hPk_ne : P k ≠ 0 := (pell_pos hk).ne'
  have hM_pos : 0 < M := by
    have h1 : 0 < q * pellQ k ^ (q - 1) := Nat.mul_pos hq.pos (pow_pos (pellQ_pos k) _)
    dsimp [M]
    omega
  rw [hfac_eq, Nat.factorization_mul hPk_ne hM_pos.ne', Finsupp.add_apply]
  congr 1
  have hnot_q : ¬ (p ∣ pellQ k) := by
    intro hpq
    have hg : p ∣ Nat.gcd (pellQ k) (P k) := Nat.dvd_gcd hpq hdiv
    rw [coprime_pellQ_pell k] at hg
    exact hp.ne_one (Nat.eq_one_of_dvd_one hg)
  have hnot_qpow : ¬ (p ∣ pellQ k ^ (q - 1)) := fun h => hnot_q (hp.dvd_of_dvd_pow h)
  have hp_sq_b : p ^ 2 ∣ P k ^ 2 * b := dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hdiv 2) b
  have hp_b : p ∣ P k ^ 2 * b := dvd_trans (dvd_pow_self p (by decide)) hp_sq_b
  by_cases hpq : p = q
  · subst hpq
    rw [if_pos rfl]
    apply le_antisymm
    · by_contra hgt
      have hge2 : 2 ≤ M.factorization p := by omega
      have hp2M : p ^ 2 ∣ M := (hp.pow_dvd_iff_le_factorization hM_pos.ne').mpr hge2
      have hp2_term : p ^ 2 ∣ p * pellQ k ^ (p - 1) :=
        (Nat.dvd_add_iff_left hp_sq_b).mpr hp2M
      rw [sq] at hp2_term
      have hp_pow : p ∣ pellQ k ^ (p - 1) := Nat.dvd_of_mul_dvd_mul_left hp.pos hp2_term
      exact hnot_qpow hp_pow
    · have hp1M : p ^ 1 ∣ M := by
        rw [pow_one]
        exact dvd_add (dvd_mul_right p _) hp_b
      exact (hp.pow_dvd_iff_le_factorization hM_pos.ne').mp hp1M
  · rw [if_neg hpq]
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hpM
    have hp_term : p ∣ q * pellQ k ^ (q - 1) := (Nat.dvd_add_iff_left hp_b).mpr hpM
    rcases hp.dvd_mul.mp hp_term with hp_dvd_q | hp_pow
    · rcases (Nat.dvd_prime hq).mp hp_dvd_q with rfl | rfl
      · exact hp.ne_one rfl
      · exact hpq rfl
    · exact hnot_qpow hp_pow

lemma pell_factorization_mul {k p : ℕ} (hk : 0 < k) (hp : p.Prime) (hdiv : p ∣ P k) :
    ∀ u : ℕ, 0 < u → (P (k * u)).factorization p = (P k).factorization p + u.factorization p := by
  intro u
  induction u using Nat.strong_induction_on with
  | h u ih =>
    intro hu
    by_cases hu1 : u = 1
    · subst hu1
      simp
    · have hu2 : 2 ≤ u := by omega
      let q := u.minFac
      have hq : q.Prime := Nat.minFac_prime (by omega)
      obtain ⟨v, huv⟩ := Nat.minFac_dvd u
      have hv_pos : 0 < v := by
        rcases eq_or_lt_of_le (Nat.zero_le v) with rfl | hv
        · simp at huv; omega
        · exact hv
      have hv_lt : v < u := by
        have hq2 : 2 ≤ q := hq.two_le
        nlinarith
      have hmul : k * u = q * (k * v) := by rw [huv]; ring
      have hkv_pos : 0 < k * v := Nat.mul_pos hk hv_pos
      have hp_kv : p ∣ P (k * v) := dvd_trans hdiv (pell_dvd_pell ⟨v, rfl⟩)
      rw [hmul, pell_factorization_mul_prime hkv_pos hp hq hp_kv, ih v hv_lt hv_pos]
      rw [huv, Nat.factorization_mul hq.ne_zero hv_pos.ne', Finsupp.add_apply]
      have hq_fac : q.factorization p = if p = q then 1 else 0 := by
        by_cases hpq : p = q
        · subst hpq; simp [hp.factorization_self]
        · rw [if_neg hpq]
          apply Nat.factorization_eq_zero_of_not_dvd
          intro hd
          rcases (Nat.dvd_prime hq).mp hd with rfl | rfl
          · exact hp.ne_one rfl
          · exact hpq rfl
      rw [hq_fac]
      omega

def Dpos (n : ℕ) : Finset (ℕ × ℕ) :=
  n.divisorsAntidiagonal.filter (fun x => ArithmeticFunction.moebius x.1 = 1)

def Dneg (n : ℕ) : Finset (ℕ × ℕ) :=
  n.divisorsAntidiagonal.filter (fun x => ArithmeticFunction.moebius x.1 = -1)

def A (n : ℕ) : ℕ := ∏ x ∈ Dpos n, P x.2
def B (n : ℕ) : ℕ := ∏ x ∈ Dneg n, P x.2

lemma neg_one_pow_trichotomy : ∀ k : ℕ, (-1 : ℤ) ^ k = 1 ∨ (-1 : ℤ) ^ k = -1
  | 0 => Or.inl rfl
  | k + 1 => by
    rcases neg_one_pow_trichotomy k with h | h <;> rw [pow_succ, h] <;> simp

lemma moebius_trichotomy (m : ℕ) :
    ArithmeticFunction.moebius m = 1 ∨
    ArithmeticFunction.moebius m = -1 ∨
    ArithmeticFunction.moebius m = 0 := by
  by_cases h : Squarefree m
  · rw [ArithmeticFunction.moebius_apply_of_squarefree h]
    rcases neg_one_pow_trichotomy (ArithmeticFunction.cardFactors m) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (ArithmeticFunction.moebius_eq_zero_of_not_squarefree h))

lemma sum_moebius_antidiag (n : ℕ) (F : ℕ → ℤ) :
    ∑ x ∈ n.divisorsAntidiagonal, ArithmeticFunction.moebius x.1 * F x.2 =
      (∑ x ∈ Dpos n, F x.2) - (∑ x ∈ Dneg n, F x.2) := by
  rw [Dpos, Dneg, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _
  rcases moebius_trichotomy x.1 with h | h | h <;> simp [h]

lemma sum_moebius_const {n : ℕ} (hn : 2 ≤ n) :
    ∑ x ∈ n.divisorsAntidiagonal, ArithmeticFunction.moebius x.1 * (1 : ℤ) = 0 := by
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun i => if i = 1 then (1 : ℤ) else 0) (g := fun _ => (1 : ℤ))).mp
  have hsum : ∀ (m : ℕ), 0 < m → ∑ i ∈ m.divisors, (if i = 1 then (1 : ℤ) else 0) = 1 := by
    intro m hm
    rw [Finset.sum_ite_eq']
    have h1 : 1 ∈ m.divisors := Nat.mem_divisors.mpr ⟨one_dvd m, hm.ne'⟩
    simp [h1]
  have hn0 : 0 < n := by omega
  have hres := hinv hsum n hn0
  have hne1 : n ≠ 1 := by omega
  simp only [Int.cast_id, hne1, ↓reduceIte] at hres
  exact hres

lemma card_Dpos_eq_card_Dneg {n : ℕ} (hn : 2 ≤ n) : (Dpos n).card = (Dneg n).card := by
  have h := (sum_moebius_antidiag n (fun _ => (1 : ℤ))).symm.trans (sum_moebius_const hn)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  omega

lemma sum_Dpos_eq_sum_Dneg_add_totient {n : ℕ} (hn : 0 < n) :
    ∑ x ∈ Dpos n, x.2 = ∑ x ∈ Dneg n, x.2 + Nat.totient n := by
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun i => (Nat.totient i : ℤ)) (g := fun m => (m : ℤ))).mp
  have hsum : ∀ (m : ℕ), 0 < m → ∑ i ∈ m.divisors, (Nat.totient i : ℤ) = (m : ℤ) := by
    intro m _
    exact_mod_cast Nat.sum_totient m
  have hres := hinv hsum n hn
  simp only [Int.cast_id] at hres
  have hres' := (sum_moebius_antidiag n (fun d => (d : ℤ))).symm.trans hres
  have hcast1 : ∑ x ∈ Dpos n, (x.2 : ℤ) = ((∑ x ∈ Dpos n, x.2 : ℕ) : ℤ) := by push_cast; rfl
  have hcast2 : ∑ x ∈ Dneg n, (x.2 : ℤ) = ((∑ x ∈ Dneg n, x.2 : ℕ) : ℤ) := by push_cast; rfl
  rw [hcast1, hcast2] at hres'
  omega

open Classical in
lemma moebius_factorization_sum {t p : ℕ} (ht : 0 < t) (hp : p.Prime) :
    ∑ x ∈ t.divisorsAntidiagonal, ArithmeticFunction.moebius x.1 * (x.2.factorization p : ℤ) =
      if ∃ k ≥ 1, t = p ^ k then 1 else 0 := by
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun w => if ∃ k ≥ 1, w = p ^ k then (1 : ℤ) else 0)
    (g := fun u => (u.factorization p : ℤ))).mp
  have hres := hinv ?_ t ht
  · simpa only [Int.cast_id] using hres
  intro u hu
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  have hset : u.divisors.filter (fun w => ∃ k ≥ 1, w = p ^ k) =
      (Finset.Icc 1 (u.factorization p)).image (fun k => p ^ k) := by
    ext w
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hwu, _⟩, ⟨k, hk1, rfl⟩⟩
      refine ⟨k, ⟨hk1, ?_⟩, rfl⟩
      exact (hp.pow_dvd_iff_le_factorization hu.ne').mp hwu
    · rintro ⟨k, ⟨hk1, hkle⟩, rfl⟩
      refine ⟨⟨?_, hu.ne'⟩, ⟨k, hk1, rfl⟩⟩
      exact (hp.pow_dvd_iff_le_factorization hu.ne').mpr hkle
  rw [hset, Finset.card_image_of_injective _ (Nat.pow_right_injective hp.two_le), Nat.card_Icc]
  omega

lemma antidiag_snd_pos {n : ℕ} (hn : 0 < n) {x : ℕ × ℕ} (hx : x ∈ n.divisorsAntidiagonal) :
    0 < x.2 := by
  have hmul : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
  rcases eq_or_lt_of_le (Nat.zero_le x.2) with h0 | hpos
  · rw [← h0, mul_zero] at hmul; omega
  · exact hpos

lemma A_pos {n : ℕ} (hn : 0 < n) : 0 < A n := by
  apply Finset.prod_pos
  intro x hx
  exact pell_pos (antidiag_snd_pos hn (Finset.mem_of_mem_filter x hx))

lemma B_pos {n : ℕ} (hn : 0 < n) : 0 < B n := by
  apply Finset.prod_pos
  intro x hx
  exact pell_pos (antidiag_snd_pos hn (Finset.mem_of_mem_filter x hx))

lemma A_dvd_B_mul_of_no_prim {n : ℕ} (hn : 2 ≤ n)
    (hno : ∀ p : ℕ, p.Prime → p ∣ P n → ∃ m : ℕ, 0 < m ∧ m < n ∧ p ∣ P m) :
    A n ∣ B n * n := by
  classical
  have hn0 : 0 < n := by omega
  have hA0 : A n ≠ 0 := (A_pos hn0).ne'
  have hB0 : B n ≠ 0 := (B_pos hn0).ne'
  have hBn0 : B n * n ≠ 0 := mul_ne_zero hB0 hn0.ne'
  rw [← Nat.factorization_le_iff_dvd hA0 hBn0]
  intro p
  by_cases hp : p.Prime
  · have hA_fac : (A n).factorization p = ∑ x ∈ Dpos n, (P x.2).factorization p := by
      unfold A
      rw [Nat.factorization_prod, Finsupp.finsetSum_apply]
      intro x hx
      exact (pell_pos (antidiag_snd_pos hn0 (Finset.mem_of_mem_filter x hx))).ne'
    have hB_fac : (B n).factorization p = ∑ x ∈ Dneg n, (P x.2).factorization p := by
      unfold B
      rw [Nat.factorization_prod, Finsupp.finsetSum_apply]
      intro x hx
      exact (pell_pos (antidiag_snd_pos hn0 (Finset.mem_of_mem_filter x hx))).ne'
    have hBn_fac : (B n * n).factorization p = (B n).factorization p + n.factorization p := by
      rw [Nat.factorization_mul hB0 hn0.ne', Finsupp.add_apply]
    rw [hBn_fac]
    suffices hdiff : ((A n).factorization p : ℤ) - ((B n).factorization p : ℤ) ≤
        (n.factorization p : ℤ) by omega
    have hdiff_eq : ((A n).factorization p : ℤ) - ((B n).factorization p : ℤ) =
        ∑ x ∈ n.divisorsAntidiagonal,
          ArithmeticFunction.moebius x.1 * ((P x.2).factorization p : ℤ) := by
      refine Eq.trans ?_ (sum_moebius_antidiag n (fun d => ((P d).factorization p : ℤ))).symm
      rw [hA_fac, hB_fac]
      push_cast
      rfl
    rw [hdiff_eq]
    by_cases hpn : p ∣ P n
    · have hex : ∃ m : ℕ, 0 < m ∧ p ∣ P m := ⟨n, hn0, hpn⟩
      let m0 := Nat.find hex
      obtain ⟨hm0_pos, hm0_dvd⟩ := Nat.find_spec hex
      obtain ⟨m, hm_pos, hm_lt, hpm⟩ := hno p hp hpn
      have hm0_le : m0 ≤ m := Nat.find_min' hex ⟨hm_pos, hpm⟩
      have hm0_lt_n : m0 < n := lt_of_le_of_lt hm0_le hm_lt
      have hdvd_iff : ∀ d : ℕ, 0 < d → (p ∣ P d ↔ m0 ∣ d) := by
        intro d hd
        constructor
        · intro hpd
          have hpg : p ∣ Nat.gcd (P m0) (P d) := Nat.dvd_gcd hm0_dvd hpd
          rw [pell_gcd] at hpg
          have hg_pos : 0 < Nat.gcd m0 d := Nat.gcd_pos_of_pos_left d hm0_pos
          have hm0_le_g : m0 ≤ Nat.gcd m0 d := Nat.find_min' hex ⟨hg_pos, hpg⟩
          have hg_le_m0 : Nat.gcd m0 d ≤ m0 := Nat.le_of_dvd hm0_pos (Nat.gcd_dvd_left m0 d)
          have hg_eq : Nat.gcd m0 d = m0 := le_antisymm hg_le_m0 hm0_le_g
          have hgd : Nat.gcd m0 d ∣ d := Nat.gcd_dvd_right m0 d
          rwa [hg_eq] at hgd
        · intro hm0d
          exact dvd_trans hm0_dvd (pell_dvd_pell hm0d)
      have hm0_dvd_n : m0 ∣ n := (hdvd_iff n hn0).mp hpn
      let t := n / m0
      have hnt : m0 * t = n := Nat.mul_div_cancel' hm0_dvd_n
      have ht2 : 2 ≤ t := by
        by_contra hlt
        have ht1 : t ≤ 1 := by omega
        nlinarith
      have ht_pos : 0 < t := by omega
      have hfilter : ∑ x ∈ n.divisorsAntidiagonal,
            ArithmeticFunction.moebius x.1 * ((P x.2).factorization p : ℤ) =
          ∑ x ∈ n.divisorsAntidiagonal.filter (fun x => m0 ∣ x.2),
            ArithmeticFunction.moebius x.1 * ((P x.2).factorization p : ℤ) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro x hx
        by_cases hmd : m0 ∣ x.2
        · simp [hmd]
        · rw [if_neg hmd]
          have hx2 : 0 < x.2 := antidiag_snd_pos hn0 hx
          have hnot_p : ¬ (p ∣ P x.2) := fun hp_d => hmd ((hdvd_iff x.2 hx2).mp hp_d)
          rw [Nat.factorization_eq_zero_of_not_dvd hnot_p]
          simp
      have hbij : ∑ x ∈ n.divisorsAntidiagonal.filter (fun x => m0 ∣ x.2),
            ArithmeticFunction.moebius x.1 * ((P x.2).factorization p : ℤ) =
          ∑ y ∈ t.divisorsAntidiagonal,
            ArithmeticFunction.moebius y.1 * ((P (m0 * y.2)).factorization p : ℤ) := by
        symm
        refine Finset.sum_bij' (fun y _ => (y.1, m0 * y.2)) (fun x _ => (x.1, x.2 / m0))
          ?_ ?_ ?_ ?_ ?_
        · intro y hy
          rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
          have hyt : y.1 * y.2 = t := (Nat.mem_divisorsAntidiagonal.mp hy).1
          refine ⟨⟨?_, hn0.ne'⟩, dvd_mul_right m0 y.2⟩
          calc y.1 * (m0 * y.2) = m0 * (y.1 * y.2) := by ring
            _ = m0 * t := by rw [hyt]
            _ = n := hnt
        · intro x hx
          rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hx
          rw [Nat.mem_divisorsAntidiagonal]
          obtain ⟨u, hxu⟩ := hx.2
          have hu_div : x.2 / m0 = u := by rw [hxu, Nat.mul_div_cancel_left u hm0_pos]
          rw [hu_div]
          have hmul : m0 * (x.1 * u) = m0 * t := by
            calc m0 * (x.1 * u) = x.1 * (m0 * u) := by ring
              _ = x.1 * x.2 := by rw [← hxu]
              _ = n := hx.1.1
              _ = m0 * t := hnt.symm
          exact ⟨Nat.eq_of_mul_eq_mul_left hm0_pos hmul, ht_pos.ne'⟩
        · intro y _
          ext
          · rfl
          · exact Nat.mul_div_cancel_left y.2 hm0_pos
        · intro x hx
          rw [Finset.mem_filter] at hx
          ext
          · rfl
          · exact Nat.mul_div_cancel' hx.2
        · intro y _
          rfl
      rw [hfilter, hbij]
      have hlte_sum : ∑ y ∈ t.divisorsAntidiagonal,
            ArithmeticFunction.moebius y.1 * ((P (m0 * y.2)).factorization p : ℤ) =
          ((P m0).factorization p : ℤ) *
            (∑ y ∈ t.divisorsAntidiagonal, ArithmeticFunction.moebius y.1 * (1 : ℤ)) +
          ∑ y ∈ t.divisorsAntidiagonal,
            ArithmeticFunction.moebius y.1 * (y.2.factorization p : ℤ) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro y hy
        have hy2 : 0 < y.2 := antidiag_snd_pos ht_pos hy
        rw [pell_factorization_mul hm0_pos hp hm0_dvd y.2 hy2]
        push_cast
        ring
      rw [hlte_sum, sum_moebius_const ht2, mul_zero, zero_add]
      simp only [moebius_factorization_sum ht_pos hp]
      split_ifs with hpk
      · obtain ⟨k, hk1, htk⟩ := hpk
        have hp_dvd_t : p ∣ t := by
          rw [htk]
          exact dvd_pow_self p (by omega)
        have hp_dvd_n : p ^ 1 ∣ n := by
          rw [pow_one, ← hnt]
          exact dvd_mul_of_dvd_right hp_dvd_t m0
        have h1le : 1 ≤ n.factorization p :=
          (hp.pow_dvd_iff_le_factorization hn0.ne').mp hp_dvd_n
        omega
      · omega
    · have hzero : ∑ x ∈ n.divisorsAntidiagonal,
          ArithmeticFunction.moebius x.1 * ((P x.2).factorization p : ℤ) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        have hx_dvd : x.2 ∣ n := ⟨x.1, by rw [mul_comm, (Nat.mem_divisorsAntidiagonal.mp hx).1]⟩
        have hnot_px : ¬ (p ∣ P x.2) := fun hpx => hpn (dvd_trans hpx (pell_dvd_pell hx_dvd))
        rw [Nat.factorization_eq_zero_of_not_dvd hnot_px]
        simp
      rw [hzero]
      omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

noncomputable def alpha : ℝ := 1 + Real.sqrt 2
noncomputable def beta : ℝ := 1 - Real.sqrt 2
noncomputable def ratio : ℝ := 3 - 2 * Real.sqrt 2

lemma sqrt2_bounds : (7 : ℝ) / 5 < Real.sqrt 2 ∧ Real.sqrt 2 < 3 / 2 := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor <;> nlinarith

lemma alpha_gt : (12 : ℝ) / 5 < alpha := by
  unfold alpha
  linarith [sqrt2_bounds.1]

lemma ratio_bounds : 0 < ratio ∧ ratio < 1 / 5 := by
  unfold ratio
  obtain ⟨h1, h2⟩ := sqrt2_bounds
  constructor <;> linarith

lemma alpha_mul_ratio : alpha * ratio = -beta := by
  unfold alpha ratio beta
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith

lemma pell_real : ∀ d : ℕ, (P d : ℝ) * (2 * Real.sqrt 2) = alpha ^ d - beta ^ d
  | 0 => by simp [P, OMA.S_oeis_a247250.pell]
  | 1 => by
    unfold alpha beta
    simp [P, OMA.S_oeis_a247250.pell]
    ring
  | d + 2 => by
    have ih0 := pell_real d
    have ih1 := pell_real (d + 1)
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have ha2 : alpha ^ 2 = 2 * alpha + 1 := by unfold alpha; nlinarith
    have hb2 : beta ^ 2 = 2 * beta + 1 := by unfold beta; nlinarith
    have hap : alpha ^ (d + 2) = 2 * alpha ^ (d + 1) + alpha ^ d := by
      calc alpha ^ (d + 2) = alpha ^ d * alpha ^ 2 := by ring
        _ = alpha ^ d * (2 * alpha + 1) := by rw [ha2]
        _ = 2 * alpha ^ (d + 1) + alpha ^ d := by ring
    have hbp : beta ^ (d + 2) = 2 * beta ^ (d + 1) + beta ^ d := by
      calc beta ^ (d + 2) = beta ^ d * beta ^ 2 := by ring
        _ = beta ^ d * (2 * beta + 1) := by rw [hb2]
        _ = 2 * beta ^ (d + 1) + beta ^ d := by ring
    change ((2 * P (d + 1) + P d : ℕ) : ℝ) * (2 * Real.sqrt 2) = alpha ^ (d + 2) - beta ^ (d + 2)
    push_cast
    linarith

lemma neg_one_real_pow : ∀ d : ℕ, (-1 : ℝ) ^ d = 1 ∨ (-1 : ℝ) ^ d = -1
  | 0 => Or.inl rfl
  | d + 1 => by
    rcases neg_one_real_pow d with h | h <;> rw [pow_succ, h] <;> norm_num

lemma pell_real_bounds (d : ℕ) :
    alpha ^ d * (1 - ratio ^ d) ≤ (P d : ℝ) * (2 * Real.sqrt 2) ∧
    (P d : ℝ) * (2 * Real.sqrt 2) ≤ alpha ^ d * (1 + ratio ^ d) := by
  rw [pell_real]
  have hbr : beta = (-1 : ℝ) * (alpha * ratio) := by linarith [alpha_mul_ratio]
  have hbpow : beta ^ d = (-1 : ℝ) ^ d * (alpha ^ d * ratio ^ d) := by
    rw [hbr, mul_pow, mul_pow]
  have ha_pos : 0 ≤ alpha ^ d := pow_nonneg (by linarith [alpha_gt]) d
  have hr_pos : 0 ≤ ratio ^ d := pow_nonneg (le_of_lt ratio_bounds.1) d
  have har_pos : 0 ≤ alpha ^ d * ratio ^ d := mul_nonneg ha_pos hr_pos
  rw [hbpow]
  rcases neg_one_real_pow d with h | h <;> rw [h] <;> constructor <;> linarith

lemma prod_one_sub_ge {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf0 : ∀ x ∈ s, 0 ≤ f x) (hf1 : ∀ x ∈ s, f x ≤ 1) :
    1 - ∑ x ∈ s, f x ≤ ∏ x ∈ s, (1 - f x) := by
  induction s using Finset.cons_induction with
  | empty => norm_num
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.prod_cons]
    have ha0 : 0 ≤ f a := hf0 a (Finset.mem_cons_self a s)
    have ha1 : 0 ≤ 1 - f a := sub_nonneg.mpr (hf1 a (Finset.mem_cons_self a s))
    have hs0 : ∀ x ∈ s, 0 ≤ f x := fun x hx => hf0 x (Finset.mem_cons_of_mem hx)
    have hs1 : ∀ x ∈ s, f x ≤ 1 := fun x hx => hf1 x (Finset.mem_cons_of_mem hx)
    have ihs : 1 - ∑ x ∈ s, f x ≤ ∏ x ∈ s, (1 - f x) := ih hs0 hs1
    have hsum_nn : 0 ≤ ∑ x ∈ s, f x := Finset.sum_nonneg hs0
    have hmul : (1 - f a) * (1 - ∑ x ∈ s, f x) ≤ (1 - f a) * ∏ x ∈ s, (1 - f x) :=
      mul_le_mul_of_nonneg_left ihs ha1
    nlinarith

lemma geom_fifth_sum : ∀ n : ℕ,
    4 * (∑ d ∈ Finset.Icc 1 n, ((1 : ℝ) / 5) ^ d) = 1 - ((1 : ℝ) / 5) ^ n
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    have ih := geom_fifth_sum n
    rw [pow_succ]
    linarith

lemma sum_ratio_antidiag_lt {n : ℕ} (hn : 0 < n) {S : Finset (ℕ × ℕ)}
    (hS : S ⊆ n.divisorsAntidiagonal) :
    ∑ x ∈ S, ratio ^ x.2 < 1 / 4 := by
  have hinj : Set.InjOn Prod.snd (S : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    have hx_mem : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp (hS hx)).1
    have hy_mem : y.1 * y.2 = n := (Nat.mem_divisorsAntidiagonal.mp (hS hy)).1
    have hx2_pos : 0 < x.2 := antidiag_snd_pos hn (hS hx)
    rw [← hxy] at hy_mem
    have hx1 : x.1 = y.1 := Nat.eq_of_mul_eq_mul_right hx2_pos (hx_mem.trans hy_mem.symm)
    exact Prod.ext hx1 hxy
  have himg_sub : S.image Prod.snd ⊆ Finset.Icc 1 n := by
    intro d hd
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hd
    rw [Finset.mem_Icc]
    have hx2_pos : 0 < x.2 := antidiag_snd_pos hn (hS hxS)
    have hx2_dvd : x.2 ∣ n := ⟨x.1, by rw [mul_comm, (Nat.mem_divisorsAntidiagonal.mp (hS hxS)).1]⟩
    exact ⟨hx2_pos, Nat.le_of_dvd hn hx2_dvd⟩
  have h1 : ∑ x ∈ S, ratio ^ x.2 = ∑ d ∈ S.image Prod.snd, ratio ^ d :=
    (Finset.sum_image hinj).symm
  have h2 : ∑ d ∈ S.image Prod.snd, ratio ^ d ≤ ∑ d ∈ Finset.Icc 1 n, ratio ^ d :=
    Finset.sum_le_sum_of_subset_of_nonneg himg_sub
      (fun d _ _ => pow_nonneg (le_of_lt ratio_bounds.1) d)
  have h3 : ∑ d ∈ Finset.Icc 1 n, ratio ^ d ≤ ∑ d ∈ Finset.Icc 1 n, ((1 : ℝ) / 5) ^ d :=
    Finset.sum_le_sum (fun d _ => pow_le_pow_left₀ (le_of_lt ratio_bounds.1)
      (le_of_lt ratio_bounds.2) d)
  have h4 : 0 < ((1 : ℝ) / 5) ^ n := pow_pos (by norm_num) n
  have h5 := geom_fifth_sum n
  linarith

lemma analytic_bound {n : ℕ} (hn : 2 ≤ n) :
    (9 / 16 : ℝ) * alpha ^ (Nat.totient n) * (B n : ℝ) < (A n : ℝ) := by
  have hn0 : 0 < n := by omega
  let w : ℝ := 2 * Real.sqrt 2
  have hw_pos : 0 < w := by unfold w; linarith [sqrt2_bounds.1]
  have ha_pos : 0 < alpha := by linarith [alpha_gt]
  obtain ⟨hr0, hr1⟩ := ratio_bounds
  have hDpos_sub : Dpos n ⊆ n.divisorsAntidiagonal := Finset.filter_subset _ _
  have hDneg_sub : Dneg n ⊆ n.divisorsAntidiagonal := Finset.filter_subset _ _
  -- Lower bound on A n
  have hA_prod : (A n : ℝ) * w ^ (Dpos n).card =
      ∏ x ∈ Dpos n, ((P x.2 : ℝ) * w) := by
    unfold A
    rw [Nat.cast_prod, Finset.prod_mul_distrib, Finset.prod_const]
  have hA_ge1 : (∏ x ∈ Dpos n, (alpha ^ x.2 * (1 - ratio ^ x.2))) ≤
      (A n : ℝ) * w ^ (Dpos n).card := by
    rw [hA_prod]
    refine Finset.prod_le_prod (fun x _ => ?_) (fun x _ => (pell_real_bounds x.2).1)
    have hrd : ratio ^ x.2 ≤ 1 := pow_le_one₀ (le_of_lt hr0) (by linarith)
    exact mul_nonneg (pow_nonneg (le_of_lt ha_pos) _) (sub_nonneg.mpr hrd)
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum] at hA_ge1
  have hprod_pos_gt : (3 / 4 : ℝ) < ∏ x ∈ Dpos n, (1 - ratio ^ x.2) := by
    have hw_ineq := prod_one_sub_ge (Dpos n) (fun x => ratio ^ x.2)
      (fun x _ => pow_nonneg (le_of_lt hr0) _)
      (fun x _ => pow_le_one₀ (le_of_lt hr0) (by linarith))
    have hsum_lt := sum_ratio_antidiag_lt hn0 hDpos_sub
    linarith
  have hA_strict : alpha ^ (∑ x ∈ Dpos n, x.2) * (3 / 4 : ℝ) <
      (A n : ℝ) * w ^ (Dpos n).card := by
    have hlt : alpha ^ (∑ x ∈ Dpos n, x.2) * (3 / 4 : ℝ) <
        alpha ^ (∑ x ∈ Dpos n, x.2) * ∏ x ∈ Dpos n, (1 - ratio ^ x.2) :=
      mul_lt_mul_of_pos_left hprod_pos_gt (pow_pos ha_pos _)
    linarith
  -- Upper bound on B n
  have hB_prod : (B n : ℝ) * w ^ (Dneg n).card =
      ∏ x ∈ Dneg n, ((P x.2 : ℝ) * w) := by
    unfold B
    rw [Nat.cast_prod, Finset.prod_mul_distrib, Finset.prod_const]
  have hB_le1 : (B n : ℝ) * w ^ (Dneg n).card ≤
      ∏ x ∈ Dneg n, (alpha ^ x.2 * (1 + ratio ^ x.2)) := by
    rw [hB_prod]
    refine Finset.prod_le_prod (fun x _ => ?_) (fun x _ => (pell_real_bounds x.2).2)
    exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt hw_pos)
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum] at hB_le1
  have hprod_neg_sub_gt : (3 / 4 : ℝ) < ∏ x ∈ Dneg n, (1 - ratio ^ x.2) := by
    have hw_ineq := prod_one_sub_ge (Dneg n) (fun x => ratio ^ x.2)
      (fun x _ => pow_nonneg (le_of_lt hr0) _)
      (fun x _ => pow_le_one₀ (le_of_lt hr0) (by linarith))
    have hsum_lt := sum_ratio_antidiag_lt hn0 hDneg_sub
    linarith
  have hprod_sq_le1 : (∏ x ∈ Dneg n, (1 + ratio ^ x.2)) * (∏ x ∈ Dneg n, (1 - ratio ^ x.2)) ≤ 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_one (fun x _ => ?_) (fun x _ => ?_)
    · have hrd : ratio ^ x.2 ≤ 1 := pow_le_one₀ (le_of_lt hr0) (by linarith)
      nlinarith [pow_nonneg (le_of_lt hr0) x.2]
    · nlinarith [sq_nonneg (ratio ^ x.2)]
  have hprod_neg_nn : 0 ≤ ∏ x ∈ Dneg n, (1 + ratio ^ x.2) :=
    Finset.prod_nonneg (fun x _ => by linarith [pow_nonneg (le_of_lt hr0) x.2])
  have hprod_neg_le : ∏ x ∈ Dneg n, (1 + ratio ^ x.2) ≤ 4 / 3 := by
    nlinarith
  have hB_le2 : (B n : ℝ) * w ^ (Dneg n).card ≤ alpha ^ (∑ x ∈ Dneg n, x.2) * (4 / 3 : ℝ) := by
    have hle : alpha ^ (∑ x ∈ Dneg n, x.2) * ∏ x ∈ Dneg n, (1 + ratio ^ x.2) ≤
        alpha ^ (∑ x ∈ Dneg n, x.2) * (4 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left hprod_neg_le (pow_nonneg (le_of_lt ha_pos) _)
    linarith
  -- Combine using card equality and sum equality
  rw [ ← card_Dpos_eq_card_Dneg hn ] at hB_le2
  have hsum_eq := sum_Dpos_eq_sum_Dneg_add_totient hn0
  rw [hsum_eq, pow_add] at hA_strict
  have hcomb : (9 / 16 : ℝ) * alpha ^ (Nat.totient n) * ((B n : ℝ) * w ^ (Dpos n).card) <
      (A n : ℝ) * w ^ (Dpos n).card := by
    have hmul : (9 / 16 : ℝ) * alpha ^ (Nat.totient n) * ((B n : ℝ) * w ^ (Dpos n).card) ≤
        (9 / 16 : ℝ) * alpha ^ (Nat.totient n) * (alpha ^ (∑ x ∈ Dneg n, x.2) * (4 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hB_le2
        (mul_nonneg (by norm_num) (pow_nonneg (le_of_lt ha_pos) _))
    have hident : (9 / 16 : ℝ) * alpha ^ (Nat.totient n) *
          (alpha ^ (∑ x ∈ Dneg n, x.2) * (4 / 3 : ℝ)) =
        alpha ^ (∑ x ∈ Dneg n, x.2) * alpha ^ (Nat.totient n) * (3 / 4 : ℝ) := by ring
    linarith
  have hw_pow_pos : 0 < w ^ (Dpos n).card := pow_pos hw_pos _
  have hcomb' : ((9 / 16 : ℝ) * alpha ^ (Nat.totient n) * (B n : ℝ)) * w ^ (Dpos n).card <
      (A n : ℝ) * w ^ (Dpos n).card := by linarith
  exact lt_of_mul_lt_mul_right hcomb' (le_of_lt hw_pow_pos)

lemma odd_le_totient_sq : ∀ m : ℕ, Odd m → m ≤ (Nat.totient m) ^ 2 := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; simp at h
  | one => intro _; norm_num
  | prime_pow p k hp hk =>
    intro hodd
    have hp_odd : Odd p := Odd.of_dvd_nat hodd (dvd_pow_self p hk.ne')
    have hp_ne2 : p ≠ 2 := by
      rintro rfl
      rcases hp_odd with ⟨r, hr⟩
      omega
    have hp3 : 3 ≤ p := by
      have h2 := hp.two_le
      omega
    rw [Nat.totient_prime_pow hp hk]
    have hpk : p ^ k = p ^ (k - 1) * p := by
      conv_lhs => rw [← Nat.sub_add_cancel hk, pow_succ]
    rw [hpk]
    have hp_sq : p ≤ (p - 1) ^ 2 := by
      rcases p with _ | _ | _ | p'
      · omega
      · omega
      · omega
      · change p' + 3 ≤ (p' + 2) ^ 2
        nlinarith
    have hpk1_pos : 1 ≤ p ^ (k - 1) := Nat.one_le_pow _ _ hp.pos
    have hrhs : (p ^ (k - 1) * (p - 1)) ^ 2 = p ^ (k - 1) * (p ^ (k - 1) * (p - 1) ^ 2) := by ring
    rw [hrhs]
    refine Nat.mul_le_mul_left (p ^ (k - 1)) ?_
    calc p = 1 * p := (one_mul p).symm
      _ ≤ p ^ (k - 1) * (p - 1) ^ 2 := Nat.mul_le_mul hpk1_pos hp_sq
  | coprime a b _ _ hcop iha ihb =>
    intro hodd
    obtain ⟨hodda, hoddb⟩ := Nat.odd_mul.mp hodd
    rw [Nat.totient_mul hcop, mul_pow]
    exact Nat.mul_le_mul (iha hodda) (ihb hoddb)

lemma exists_two_pow_mul_odd : ∀ n : ℕ, 0 < n → ∃ k m : ℕ, Odd m ∧ n = 2 ^ k * m := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h2 : 2 ∣ n
    · obtain ⟨n', rfl⟩ := h2
      have hn' : 0 < n' := by omega
      have hlt : n' < 2 * n' := by omega
      obtain ⟨k, m, hm, rfl⟩ := ih n' hlt hn'
      exact ⟨k + 1, m, hm, by ring⟩
    · refine ⟨0, n, ?_, by simp⟩
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact h2

lemma two_pow_le_two_totient_sq : ∀ k : ℕ, 2 ^ k ≤ 2 * (Nat.totient (2 ^ k)) ^ 2
  | 0 => by norm_num
  | 1 => by norm_num
  | k + 2 => by
    rw [Nat.totient_prime_pow Nat.prime_two (by omega : 0 < k + 2)]
    change 2 ^ (k + 2) ≤ 2 * (2 ^ (k + 1) * 1) ^ 2
    have hpos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by decide)
    calc 2 ^ (k + 2) = 2 * (2 ^ (k + 1) * 1) := by ring
      _ ≤ 2 * (2 ^ (k + 1) * 2 ^ (k + 1)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hpos)
      _ = 2 * (2 ^ (k + 1) * 1) ^ 2 := by ring

lemma le_two_mul_totient_sq {n : ℕ} (hn : 0 < n) : n ≤ 2 * (Nat.totient n) ^ 2 := by
  obtain ⟨k, m, hm_odd, rfl⟩ := exists_two_pow_mul_odd n hn
  have hcop : Nat.Coprime (2 ^ k) m := by
    apply Nat.Coprime.pow_left k
    rw [Nat.prime_two.coprime_iff_not_dvd, ← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hm_odd
  rw [Nat.totient_mul hcop]
  have h1 := two_pow_le_two_totient_sq k
  have h2 := odd_le_totient_sq m hm_odd
  exact le_of_le_of_eq (Nat.mul_le_mul h1 h2) (by ring)

lemma totient_ge_six {n : ℕ} (hn : 13 ≤ n) : 6 ≤ Nat.totient n := by
  by_cases h33 : 33 ≤ n
  · have hbound := le_two_mul_totient_sq (by omega : 0 < n)
    have hsq : 17 ≤ (Nat.totient n) ^ 2 := by omega
    have h5 : 5 ≤ Nat.totient n := by nlinarith
    have heven : Even (Nat.totient n) := Nat.totient_even (by omega : 2 < n)
    rcases heven with ⟨r, hr⟩
    omega
  · interval_cases n <;> decide

lemma two_mul_sq_lt_exp : ∀ k : ℕ, 6 ≤ k →
    (2 * (k : ℝ) ^ 2) < (9 / 16 : ℝ) * ((12 : ℝ) / 5) ^ k := by
  intro k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction j with
  | zero => norm_num
  | succ j ih =>
    let m : ℝ := (6 + j : ℕ)
    have hm6 : 6 ≤ m := by
      dsimp [m]
      exact_mod_cast (by omega : 6 ≤ 6 + j)
    have hstep : 2 * (m + 1) ^ 2 < (12 / 5 : ℝ) * (2 * m ^ 2) := by nlinarith
    have hexp : (9 / 16 : ℝ) * ((12 : ℝ) / 5) ^ (6 + (j + 1)) =
        (12 / 5 : ℝ) * ((9 / 16 : ℝ) * ((12 : ℝ) / 5) ^ (6 + j)) := by
      have hadd : 6 + (j + 1) = (6 + j) + 1 := by omega
      rw [hadd, pow_succ]
      ring
    have hcast : (2 * ((6 + (j + 1) : ℕ) : ℝ) ^ 2) = 2 * (m + 1) ^ 2 := by
      dsimp [m]
      push_cast
      ring
    rw [hcast, hexp]
    have ih' : 2 * m ^ 2 < (9 / 16 : ℝ) * ((12 : ℝ) / 5) ^ (6 + j) := ih (by omega)
    linarith

lemma prim_prime_ge_13 {n : ℕ} (hn : 13 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ P n ∧ ∀ m : ℕ, 0 < m → m < n → ¬ p ∣ P m := by
  by_contra hnot
  have hno : ∀ p : ℕ, p.Prime → p ∣ P n → ∃ m : ℕ, 0 < m ∧ m < n ∧ p ∣ P m := by
    intro p hp hpn
    by_contra hnone
    apply hnot
    exact ⟨p, hp, hpn, fun m hm1 hm2 hpm => hnone ⟨m, hm1, hm2, hpm⟩⟩
  have hdvd : A n ∣ B n * n := A_dvd_B_mul_of_no_prim (by omega) hno
  have hBn_pos : 0 < B n * n := Nat.mul_pos (B_pos (by omega)) (by omega)
  have hle : A n ≤ B n * n := Nat.le_of_dvd hBn_pos hdvd
  have hk6 : 6 ≤ Nat.totient n := totient_ge_six hn
  have hn_le_sq : (n : ℝ) ≤ 2 * (Nat.totient n : ℝ) ^ 2 := by
    exact_mod_cast le_two_mul_totient_sq (by omega : 0 < n)
  have hsq_lt : 2 * (Nat.totient n : ℝ) ^ 2 < (9 / 16 : ℝ) * ((12 : ℝ) / 5) ^ (Nat.totient n) :=
    two_mul_sq_lt_exp (Nat.totient n) hk6
  have hpow_le : ((12 : ℝ) / 5) ^ (Nat.totient n) ≤ alpha ^ (Nat.totient n) :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt alpha_gt) _
  have hn_lt_coef : (n : ℝ) < (9 / 16 : ℝ) * alpha ^ (Nat.totient n) := by linarith
  have hB_pos_real : (0 : ℝ) < (B n : ℝ) := Nat.cast_pos.mpr (B_pos (by omega))
  have h1 : (B n : ℝ) * (n : ℝ) < (9 / 16 : ℝ) * alpha ^ (Nat.totient n) * (B n : ℝ) := by
    have := mul_lt_mul_of_pos_right hn_lt_coef hB_pos_real
    linarith
  have h2 := analytic_bound (by omega : 2 ≤ n)
  have hlt_real : ((B n * n : ℕ) : ℝ) < (A n : ℝ) := by
    push_cast
    linarith
  have hlt_nat : B n * n < A n := Nat.cast_lt.mp hlt_real
  omega

lemma pell_small_vals :
    P 1 = 1 ∧ P 2 = 2 ∧ P 3 = 5 ∧ P 4 = 12 ∧ P 5 = 29 ∧ P 6 = 70 ∧
    P 7 = 169 ∧ P 8 = 408 ∧ P 9 = 985 ∧ P 10 = 2378 ∧ P 11 = 5741 ∧ P 12 = 13860 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma prim_prime_small {n : ℕ} (hn1 : 1 < n) (hn12 : n ≤ 12) :
    ∃ p : ℕ, p.Prime ∧ p ∣ P n ∧ ∀ m : ℕ, 0 < m → m < n → ¬ p ∣ P m := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := pell_small_vals
  interval_cases n
  · refine ⟨2, by norm_num, by rw [h2], ?_⟩
    intro m hm1 hm2
    have hm : m = 1 := by omega
    subst hm
    omega
  · refine ⟨5, by norm_num, by rw [h3], ?_⟩
    intro m hm1 hm2; interval_cases m <;> omega
  · refine ⟨3, by norm_num, by rw [h4]; norm_num, ?_⟩
    intro m hm1 hm2; interval_cases m <;> omega
  · refine ⟨29, by norm_num, by rw [h5], ?_⟩
    intro m hm1 hm2; interval_cases m <;> omega
  · refine ⟨7, by norm_num, by rw [h6]; norm_num, ?_⟩
    intro m hm1 hm2; interval_cases m <;> omega
  · refine ⟨13, by norm_num, by rw [h7]; norm_num, ?_⟩
    intro m hm1 hm2; interval_cases m <;> omega
  · refine ⟨17, by norm_num, by rw [h8]; norm_num, ?_⟩
    intro m hm1 hm2; interval_cases m <;> omega
  · refine ⟨197, by norm_num, by rw [h9]; norm_num, ?_⟩
    intro m hm1 hm2; interval_cases m <;> omega
  · refine ⟨41, by norm_num, by rw [h10]; norm_num, ?_⟩
    intro m hm1 hm2; interval_cases m <;> omega
  · refine ⟨5741, by norm_num, by rw [h11], ?_⟩
    intro m hm1 hm2; interval_cases m <;> omega
  · refine ⟨11, by norm_num, by rw [h12]; norm_num, ?_⟩
    intro m hm1 hm2; interval_cases m <;> omega

end PellPrimDiv

theorem OMA.solution : type_of% @OMA.S_oeis_a247250.main := by
  intro n hn
  by_cases h13 : 13 ≤ n
  · exact PellPrimDiv.prim_prime_ge_13 h13
  · exact PellPrimDiv.prim_prime_small hn (by omega)
