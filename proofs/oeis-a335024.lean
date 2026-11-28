import OMAStatements.S_oeis_a335024

namespace OMA.S_oeis_a335024




/-! ## 27173 is in A136327 -/

/-- Lucas's theorem, one digit at a time, with the digits supplied as hypotheses. -/
lemma lucas_step (n k p a b c d : ℕ) [Fact p.Prime] (ha : n % p = a) (hb : k % p = b)
    (hc : n / p = c) (hd : k / p = d) : Nat.choose n k ≡ Nat.choose a b * Nat.choose c d [MOD p] := by
  subst ha hb hc hd
  exact Choose.choose_modEq_choose_mod_mul_choose_div_nat

lemma choose_mod29 : Nat.choose 54345 27172 ≡ 1 [MOD 29] := by
  haveI := Fact.mk (show Nat.Prime 29 by norm_num)
  have h1 := lucas_step 54345 27172 29 28 28 1873 936 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h2 := lucas_step 1873 936 29 17 8 64 32 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h3 := lucas_step 64 32 29 6 3 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e0 : Nat.choose 28 28 = 1 := Nat.choose_self 28
  have e1 : Nat.choose 17 8 = 24310 := by decide
  have e2 : Nat.choose 6 3 = 20 := by decide
  have e3 : Nat.choose 2 1 = 2 := by decide
  calc Nat.choose 54345 27172 ≡ Nat.choose 28 28 * Nat.choose 1873 936 [MOD 29] := h1
    _ = 1 * Nat.choose 1873 936 := by rw [e0]
    _ ≡ 1 * (Nat.choose 17 8 * Nat.choose 64 32) [MOD 29] := Nat.ModEq.mul_left _ h2
    _ ≡ 1 * (Nat.choose 17 8 * (Nat.choose 6 3 * Nat.choose 2 1)) [MOD 29] :=
        Nat.ModEq.mul_left _ (Nat.ModEq.mul_left _ h3)
    _ = 1 * (24310 * (20 * 2)) := by rw [e1, e2, e3]
    _ ≡ 1 [MOD 29] := by decide

lemma choose_mod937 : Nat.choose 54345 27172 ≡ 1 [MOD 937] := by
  haveI := Fact.mk (show Nat.Prime 937 by norm_num)
  have h1 := lucas_step 54345 27172 937 936 936 57 28 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have e0 : Nat.choose 936 936 = 1 := Nat.choose_self 936
  have e : Nat.choose 57 28 % 937 = 1 := by
    rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
    decide
  calc Nat.choose 54345 27172 ≡ Nat.choose 936 936 * Nat.choose 57 28 [MOD 937] := h1
    _ = Nat.choose 57 28 := by rw [e0, one_mul]
    _ ≡ 1 [MOD 937] := e

lemma crt_29_937 (x : ℕ) (h1 : x ≡ 1 [MOD 29]) (h2 : x ≡ 1 [MOD 937]) : x % 27173 = 1 :=
  (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 29 937)).mp ⟨h1, h2⟩

lemma mem_of (k m j : ℕ) (hk : 1 < k) (hm : 2 * k - 1 = m) (hj : k - 1 = j)
    (h : Nat.choose m j % k = 1) : InA136327 k := by
  subst hm hj
  exact ⟨hk, h⟩

lemma mem_A136327 : InA136327 27173 :=
  mem_of 27173 54345 27172 (by norm_num) (by norm_num) (by norm_num)
    (crt_29_937 _ choose_mod29 choose_mod937)

/-! ## a(27172) is a multiple of 29 -/

/-- The integer n! H_n. -/
def S (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 n, n.factorial / i

lemma S_cast (n : ℕ) : (S n : ℚ) = n.factorial * harmonic n := by
  rw [harmonic_eq_sum_Icc, Finset.mul_sum, S, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hin : i ≤ n := (Finset.mem_Icc.mp hi).2
  rw [Nat.cast_div (Nat.dvd_factorial hi1 hin) (by exact_mod_cast (by omega : i ≠ 0))]
  ring

lemma S_succ (n : ℕ) : S (n + 1) = (n + 1) * S n + n.factorial := by
  have h : (S (n + 1) : ℚ) = ((n + 1) * S n + n.factorial : ℕ) := by
    push_cast
    rw [S_cast, S_cast, harmonic_succ, Nat.factorial_succ]
    push_cast
    field_simp
  exact_mod_cast h

lemma g_dvd_succ (n : ℕ) : g n ∣ g (n + 1) := by
  apply Nat.dvd_gcd
  · exact (Nat.gcd_dvd_left _ _).trans (Nat.factorial_dvd_factorial (Nat.le_succ n))
  · show g n ∣ S (n + 1)
    rw [S_succ]
    exact dvd_add (dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _) (Nat.gcd_dvd_left _ _)

lemma harmonic_val (n : ℕ) (h1 : 24389 ≤ n) (h2 : n < 48778) :
    padicValRat 29 (harmonic n) = -3 := by
  haveI := Fact.mk (show Nat.Prime 29 by norm_num)
  set F : ℕ → ℚ := fun i => ((i + 1 : ℕ) : ℚ)⁻¹ with hF
  have hpos : ∀ i, 0 < F i := fun i => by simp only [hF]; positivity
  have hsplit : harmonic n = F 24388 + ∑ i ∈ (Finset.range n).erase 24388, F i := by
    rw [harmonic, Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega))]
  have hj : padicValRat 29 (F 24388) = -3 := by
    simp only [hF, padicValRat.inv, padicValRat.of_nat]
    have : padicValNat 29 (24388 + 1) = 3 := by
      rw [show 24388 + 1 = 29 ^ 3 by norm_num, padicValNat.prime_pow]
    rw [this]
    norm_num
  have hlt : padicValRat 29 (F 24388) < padicValRat 29 (∑ i ∈ (Finset.range n).erase 24388, F i) := by
    apply padicValRat.lt_sum_of_lt ⟨0, by simp; omega⟩ _ hpos
    intro i hi
    rw [Finset.mem_erase, Finset.mem_range] at hi
    rw [hj]
    simp only [hF, padicValRat.inv, padicValRat.of_nat]
    have hlt3 : padicValNat 29 (i + 1) < 3 := by
      by_contra hge
      push_neg at hge
      have hd : 29 ^ 3 ∣ i + 1 := by
        rw [padicValNat_dvd_iff_le (by omega)]
        exact hge
      obtain ⟨c, hc⟩ := hd
      have : c = 1 := by
        rcases c with _ | _ | c
        · omega
        · rfl
        · norm_num at hc; omega
      subst this
      norm_num at hc
      omega
    have : (padicValNat 29 (i + 1) : ℤ) < 3 := by exact_mod_cast hlt3
    omega
  have hne1 : F 24388 ≠ 0 := (hpos _).ne'
  have hne2 : ∑ i ∈ (Finset.range n).erase 24388, F i ≠ 0 :=
    (Finset.sum_pos (fun i _ => hpos i) ⟨0, by simp; omega⟩).ne'
  have hne3 : F 24388 + ∑ i ∈ (Finset.range n).erase 24388, F i ≠ 0 := by
    rw [← hsplit]; exact (harmonic_pos (by omega)).ne'
  rw [hsplit, padicValRat.add_eq_of_lt hne3 hne1 hne2 hlt, hj]

lemma val_S (n : ℕ) (h1 : 24389 ≤ n) (h2 : n < 48778) :
    (padicValNat 29 (S n) : ℤ) = padicValNat 29 n.factorial - 3 := by
  haveI := Fact.mk (show Nat.Prime 29 by norm_num)
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hh : harmonic n ≠ 0 := (harmonic_pos (by omega)).ne'
  have := congrArg (padicValRat 29) (S_cast n)
  rw [padicValRat.mul hf hh, harmonic_val n h1 h2, padicValRat.of_nat, padicValRat.of_nat] at this
  exact_mod_cast this

lemma S_ne_zero (n : ℕ) (hn : 1 ≤ n) : S n ≠ 0 := by
  intro h
  have := S_cast n
  rw [h] at this
  have hf : (0 : ℚ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hh := harmonic_pos (show n ≠ 0 by omega)
  push_cast at this
  nlinarith

lemma val_g (n : ℕ) (h1 : 24389 ≤ n) (h2 : n < 48778) :
    (padicValNat 29 (g n) : ℤ) = padicValNat 29 n.factorial - 3 := by
  have hp : Nat.Prime 29 := by norm_num
  have hS := S_ne_zero n (by omega)
  have hF := Nat.factorial_ne_zero n
  have hgcd := Nat.factorization_gcd hF hS
  have e : padicValNat 29 (g n) = min (padicValNat 29 n.factorial) (padicValNat 29 (S n)) := by
    rw [← Nat.factorization_def _ hp, ← Nat.factorization_def _ hp, ← Nat.factorization_def _ hp]
    show (Nat.gcd n.factorial (S n)).factorization 29 = _
    rw [hgcd, Finsupp.inf_apply]
  rw [e]
  have := val_S n h1 h2
  omega

lemma g_pos (n : ℕ) : 0 < g n := Nat.gcd_pos_of_pos_left _ (Nat.factorial_pos n)

lemma fact_val_27172 : padicValNat 29 (Nat.factorial 27172) = 969 := by
  haveI := Fact.mk (show Nat.Prime 29 by norm_num)
  rw [padicValNat_factorial (b := 4) (Nat.log_lt_of_lt_pow (by norm_num) (by norm_num))]
  decide

lemma fact_val_27173 : padicValNat 29 (Nat.factorial (27172 + 1)) = 970 := by
  haveI := Fact.mk (show Nat.Prime 29 by norm_num)
  rw [padicValNat_factorial (b := 4) (Nat.log_lt_of_lt_pow (by norm_num) (by norm_num))]
  decide

/-- If the 29-adic valuation of A056612 goes up by exactly one from n to n + 1, then a(n) is
not 1 (it is divisible by 29). -/
lemma a_ne_one_aux (n e : ℕ) (h1 : padicValNat 29 (g n) = e)
    (h2 : padicValNat 29 (g (n + 1)) = e + 1) : a n ≠ 1 := by
  obtain ⟨c, hc⟩ := g_dvd_succ n
  have ha : a n = c := by
    unfold a
    rw [hc, Nat.mul_div_cancel_left _ (g_pos n)]
  rw [ha]
  intro hc1
  rw [hc1, mul_one] at hc
  rw [hc, h1] at h2
  omega

lemma a_27172_ne_one : a 27172 ≠ 1 := by
  have v1 := val_g 27172 (by norm_num) (by norm_num)
  have v2 := val_g (27172 + 1) (by norm_num) (by norm_num)
  rw [fact_val_27172] at v1
  rw [fact_val_27173] at v2
  exact a_ne_one_aux 27172 966 (by omega) (by omega)

/-- The conjunction of the entry's two conjectures is false: Heinz's Conjecture 2 fails at
n = 27172, where n + 1 = 27173 is in A136327 but a(n) is not 1. -/
theorem disproof : ¬ ((∀ n : ℕ, 1 ≤ n →
      (a n = 1 ↔ ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ k < p ∧ n + 1 = p ^ k)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ InA136327 (n + 1)))) := by
  rintro ⟨-, h2⟩
  exact a_27172_ne_one ((h2 27172 (by norm_num)).mpr mem_A136327)

end OMA.S_oeis_a335024

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a335024.main) :=
  OMA.S_oeis_a335024.disproof
