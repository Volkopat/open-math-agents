import OMAStatements.S_oeis_a361713

-- Problem: A361713: a(n) = Sum_{k = 0..n-1} binomial(n,k)^2 * binomial(n+k-1,k)^2.
-- Upstream: formal-conjectures statements/oeis-a361713.lean:0 (declaration OMA.S_oeis_a361713.main)
-- Credit: @Dolcruz (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.A361713

lemma choose_p_div_mod (p m : ℕ) (hp : p.Prime) (hm : m + 1 < p) :
    p ∣ p.choose (m + 1) ∧
    (((m + 1 : ℕ) : ZMod p) ^ 2 * ((p.choose (m + 1) / p : ℕ) : ZMod p) ^ 2 = 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hdesc : (m + 1).factorial * p.choose (m + 1) = p * ∏ i ∈ Finset.range m, (p - 1 - i) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range,
      Finset.prod_range_succ']
    simp only [Nat.sub_zero, mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    omega
  have hndvd : ¬ p ∣ (m + 1).factorial := by
    rw [hp.dvd_factorial]
    omega
  have hdvd : p ∣ p.choose (m + 1) := by
    have h1 : p ∣ (m + 1).factorial * p.choose (m + 1) := ⟨∏ i ∈ Finset.range m, (p - 1 - i), hdesc⟩
    exact (hp.dvd_mul.mp h1).resolve_left hndvd
  refine ⟨hdvd, ?_⟩
  set u : ℕ := p.choose (m + 1) / p
  have hu : p * u = p.choose (m + 1) := Nat.mul_div_cancel' hdvd
  have hmul : (m + 1) * m.factorial * u = ∏ i ∈ Finset.range m, (p - 1 - i) := by
    have h1 : p * ((m + 1) * m.factorial * u) = p * ∏ i ∈ Finset.range m, (p - 1 - i) := by
      calc p * ((m + 1) * m.factorial * u)
          = (m + 1).factorial * (p * u) := by rw [Nat.factorial_succ]; ring
        _ = (m + 1).factorial * p.choose (m + 1) := by rw [hu]
        _ = p * ∏ i ∈ Finset.range m, (p - 1 - i) := hdesc
    exact Nat.eq_of_mul_eq_mul_left hp.pos h1
  have hprod_zmod :
      ((∏ i ∈ Finset.range m, (p - 1 - i) : ℕ) : ZMod p) =
      (-1 : ZMod p) ^ m * (m.factorial : ZMod p) := by
    rw [Nat.cast_prod]
    have hterm : ∀ i ∈ Finset.range m,
        ((p - 1 - i : ℕ) : ZMod p) = (-1 : ZMod p) * ((i + 1 : ℕ) : ZMod p) := by
      intro i hi
      have hi_lt : i < m := Finset.mem_range.mp hi
      have hsum : (p - 1 - i) + (i + 1) = p := by omega
      have hz : ((p - 1 - i : ℕ) : ZMod p) + ((i + 1 : ℕ) : ZMod p) = 0 := by
        exact_mod_cast (by rw [hsum]; exact ZMod.natCast_self p : (((p - 1 - i) + (i + 1) : ℕ) : ZMod p) = 0)
      linear_combination hz
    rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range]
    congr 1
    rw [← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
  have hcast :
      ((m + 1 : ℕ) : ZMod p) * (m.factorial : ZMod p) * (u : ZMod p) =
      (-1 : ZMod p) ^ m * (m.factorial : ZMod p) := by
    have h := congrArg (fun x : ℕ => (x : ZMod p)) hmul
    rw [hprod_zmod] at h
    simpa [Nat.cast_mul, mul_assoc] using h
  have hfac_ne : (m.factorial : ZMod p) ≠ 0 := by
    intro h0
    have h1 : p ∣ m.factorial := (ZMod.natCast_eq_zero_iff _ _).mp h0
    rw [hp.dvd_factorial] at h1
    omega
  have hcancel : ((m + 1 : ℕ) : ZMod p) * (u : ZMod p) = (-1 : ZMod p) ^ m := by
    apply mul_right_cancel₀ hfac_ne
    linear_combination hcast
  calc
    ((m + 1 : ℕ) : ZMod p) ^ 2 * (u : ZMod p) ^ 2
        = (((m + 1 : ℕ) : ZMod p) * (u : ZMod p)) ^ 2 := by ring
    _ = ((-1 : ZMod p) ^ m) ^ 2 := by rw [hcancel]
    _ = ((-1 : ZMod p) ^ 2) ^ m := by rw [← pow_mul, mul_comm, pow_mul]
    _ = 1 := by norm_num

lemma choose_add_div_mod (p m : ℕ) (hp : p.Prime) (hm : m + 1 < p) :
    p ∣ (p + m).choose (m + 1) ∧
    (((m + 1 : ℕ) : ZMod p) ^ 2 * (((p + m).choose (m + 1) / p : ℕ) : ZMod p) ^ 2 = 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hdesc : (m + 1).factorial * (p + m).choose (m + 1) = p * ∏ i ∈ Finset.range m, (p + m - i) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range,
      Finset.prod_range_succ]
    simp only [Nat.add_sub_cancel, mul_comm]
  have hndvd : ¬ p ∣ (m + 1).factorial := by
    rw [hp.dvd_factorial]
    omega
  have hdvd : p ∣ (p + m).choose (m + 1) := by
    have h1 : p ∣ (m + 1).factorial * (p + m).choose (m + 1) := ⟨∏ i ∈ Finset.range m, (p + m - i), hdesc⟩
    exact (hp.dvd_mul.mp h1).resolve_left hndvd
  refine ⟨hdvd, ?_⟩
  set v : ℕ := (p + m).choose (m + 1) / p
  have hv : p * v = (p + m).choose (m + 1) := Nat.mul_div_cancel' hdvd
  have hmul : (m + 1) * m.factorial * v = ∏ i ∈ Finset.range m, (p + m - i) := by
    have h1 : p * ((m + 1) * m.factorial * v) = p * ∏ i ∈ Finset.range m, (p + m - i) := by
      calc p * ((m + 1) * m.factorial * v)
          = (m + 1).factorial * (p * v) := by rw [Nat.factorial_succ]; ring
        _ = (m + 1).factorial * (p + m).choose (m + 1) := by rw [hv]
        _ = p * ∏ i ∈ Finset.range m, (p + m - i) := hdesc
    exact Nat.eq_of_mul_eq_mul_left hp.pos h1
  have hprod_zmod :
      ((∏ i ∈ Finset.range m, (p + m - i) : ℕ) : ZMod p) = (m.factorial : ZMod p) := by
    rw [Nat.cast_prod]
    have hterm : ∀ i ∈ Finset.range m, ((p + m - i : ℕ) : ZMod p) = ((m - i : ℕ) : ZMod p) := by
      intro i hi
      have hi_lt : i < m := Finset.mem_range.mp hi
      have heq : p + m - i = p + (m - i) := by omega
      rw [heq, Nat.cast_add, ZMod.natCast_self, zero_add]
    rw [Finset.prod_congr rfl hterm, ← Nat.cast_prod, ← Nat.descFactorial_eq_prod_range,
      Nat.descFactorial_self]
  have hcast :
      ((m + 1 : ℕ) : ZMod p) * (m.factorial : ZMod p) * (v : ZMod p) = (m.factorial : ZMod p) := by
    have h := congrArg (fun x : ℕ => (x : ZMod p)) hmul
    rw [hprod_zmod] at h
    simpa [Nat.cast_mul, mul_assoc] using h
  have hfac_ne : (m.factorial : ZMod p) ≠ 0 := by
    intro h0
    have h1 : p ∣ m.factorial := (ZMod.natCast_eq_zero_iff _ _).mp h0
    rw [hp.dvd_factorial] at h1
    omega
  have hcancel : ((m + 1 : ℕ) : ZMod p) * (v : ZMod p) = 1 := by
    apply mul_right_cancel₀ hfac_ne
    linear_combination hcast
  calc
    ((m + 1 : ℕ) : ZMod p) ^ 2 * (v : ZMod p) ^ 2
        = (((m + 1 : ℕ) : ZMod p) * (v : ZMod p)) ^ 2 := by ring
    _ = 1 ^ 2 := by rw [hcancel]
    _ = 1 := one_pow 2

lemma sum_pow_four_zmod_eq_zero (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) :
    ∑ x : ZMod p, x ^ 4 = 0 := by
  have hex : ∃ g : ZMod p, g ≠ 0 ∧ g ^ 4 ≠ 1 := by
    by_contra hall
    push Not at hall
    by_cases hsq : ∃ a : ZMod p, a ^ 2 = -1
    · rcases hsq with ⟨a, ha⟩
      have hsub : (Finset.univ : Finset (ZMod p)) ⊆ {0, 1, -1, a, -a} := by
        intro x _
        by_cases hx0 : x = 0
        · simp [hx0]
        · have hx4 : x ^ 4 = 1 := hall x hx0
          have hfac : (x - 1) * (x + 1) * (x - a) * (x + a) = 0 := by
            linear_combination hx4 - (x ^ 2 - 1) * ha
          simp only [mul_eq_zero] at hfac
          rcases hfac with ((h1 | h2) | h3) | h4
          · simp [sub_eq_zero.mp h1]
          · simp [eq_neg_of_add_eq_zero_left h2]
          · simp [sub_eq_zero.mp h3]
          · simp [eq_neg_of_add_eq_zero_left h4]
      have hcard : p ≤ ({0, 1, -1, a, -a} : Finset (ZMod p)).card := by
        simpa [ZMod.card] using Finset.card_le_card hsub
      have hle5 : ({0, 1, -1, a, -a} : Finset (ZMod p)).card ≤ 5 := by
        calc ({0, 1, -1, a, -a} : Finset (ZMod p)).card
            ≤ ({1, -1, a, -a} : Finset (ZMod p)).card + 1 := Finset.card_insert_le _ _
          _ ≤ ({-1, a, -a} : Finset (ZMod p)).card + 1 + 1 := by linarith [Finset.card_insert_le (1 : ZMod p) {-1, a, -a}]
          _ ≤ ({a, -a} : Finset (ZMod p)).card + 1 + 1 + 1 := by linarith [Finset.card_insert_le (-1 : ZMod p) {a, -a}]
          _ ≤ ({-a} : Finset (ZMod p)).card + 1 + 1 + 1 + 1 := by linarith [Finset.card_insert_le a {-a}]
          _ = 5 := by simp
      omega
    · push Not at hsq
      have hsub : (Finset.univ : Finset (ZMod p)) ⊆ {0, 1, -1} := by
        intro x _
        by_cases hx0 : x = 0
        · simp [hx0]
        · have hx4 : x ^ 4 = 1 := hall x hx0
          have hfac : (x - 1) * (x + 1) * (x ^ 2 + 1) = 0 := by linear_combination hx4
          simp only [mul_eq_zero] at hfac
          rcases hfac with (h1 | h2) | h3
          · simp [sub_eq_zero.mp h1]
          · simp [eq_neg_of_add_eq_zero_left h2]
          · exact False.elim (hsq x (eq_neg_of_add_eq_zero_left h3))
      have hcard : p ≤ ({0, 1, -1} : Finset (ZMod p)).card := by
        simpa [ZMod.card] using Finset.card_le_card hsub
      have hle3 : ({0, 1, -1} : Finset (ZMod p)).card ≤ 3 := by
        calc ({0, 1, -1} : Finset (ZMod p)).card
            ≤ ({1, -1} : Finset (ZMod p)).card + 1 := Finset.card_insert_le _ _
          _ ≤ ({-1} : Finset (ZMod p)).card + 1 + 1 := by linarith [Finset.card_insert_le (1 : ZMod p) {-1}]
          _ = 3 := by simp
      omega
  rcases hex with ⟨g, hg0, hg4⟩
  have hshift : g ^ 4 * ∑ x : ZMod p, x ^ 4 = ∑ x : ZMod p, x ^ 4 := by
    rw [Finset.mul_sum]
    have h1 : ∑ x : ZMod p, g ^ 4 * x ^ 4 = ∑ x : ZMod p, (g * x) ^ 4 := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [h1]
    exact Fintype.sum_equiv (Equiv.mulLeft₀ g hg0) (fun x => (g * x) ^ 4) (fun x => x ^ 4)
      (fun _ => rfl)
  have hmul0 : (g ^ 4 - 1) * ∑ x : ZMod p, x ^ 4 = 0 := by linear_combination hshift
  exact (mul_eq_zero.mp hmul0).resolve_left (sub_ne_zero.mpr hg4)

end OMA.A361713

theorem OMA.solution : type_of% @OMA.S_oeis_a361713.main := by
  intro p hp hp7
  have : Fact p.Prime := ⟨hp⟩
  have ha1 : OMA.S_oeis_a361713.a 1 = 1 := by
    simp [OMA.S_oeis_a361713.a]
  have hap : OMA.S_oeis_a361713.a p - OMA.S_oeis_a361713.a 1 =
      ∑ k ∈ Finset.Ico 1 p, (((p.choose k) ^ 2 * ((p + k - 1).choose k) ^ 2 : ℕ) : ℤ) := by
    rw [ha1, OMA.S_oeis_a361713.a, ← Nat.Ico_zero_eq_range,
      Finset.sum_eq_sum_Ico_succ_bot hp.pos]
    simp
  rw [hap]
  set S : ℕ := ∑ k ∈ Finset.Ico 1 p,
    (p.choose k / p) ^ 2 * ((p + k - 1).choose k / p) ^ 2
  have hfactor :
      (∑ k ∈ Finset.Ico 1 p, (((p.choose k) ^ 2 * ((p + k - 1).choose k) ^ 2 : ℕ) : ℤ)) =
      (p : ℤ) ^ 4 * (S : ℤ) := by
    rw [Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkp : k < p := (Finset.mem_Ico.mp hk).2
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have h1 : p ∣ p.choose (m + 1) := (OMA.A361713.choose_p_div_mod p m hp hkp).1
    have h2 : p ∣ (p + m).choose (m + 1) := (OMA.A361713.choose_add_div_mod p m hp hkp).1
    have heq : p + (m + 1) - 1 = p + m := by omega
    rw [heq]
    have hc1 : p.choose (m + 1) = p * (p.choose (m + 1) / p) := (Nat.mul_div_cancel' h1).symm
    have hc2 : (p + m).choose (m + 1) = p * ((p + m).choose (m + 1) / p) := (Nat.mul_div_cancel' h2).symm
    have hnat : (p.choose (m + 1)) ^ 2 * ((p + m).choose (m + 1)) ^ 2 =
        p ^ 4 * ((p.choose (m + 1) / p) ^ 2 * ((p + m).choose (m + 1) / p) ^ 2) := by
      conv_lhs => rw [hc1, hc2]
      ring
    exact_mod_cast hnat
  rw [hfactor]
  have hS_zmod : (S : ZMod p) = 0 := by
    have hterm : (S : ZMod p) = ∑ k ∈ Finset.Ico 1 p, ((k : ZMod p)⁻¹) ^ 4 := by
      dsimp only [S]
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
      have hkp : k < p := (Finset.mem_Ico.mp hk).2
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have heq : p + (m + 1) - 1 = p + m := by omega
      rw [heq]
      have h1 := (OMA.A361713.choose_p_div_mod p m hp hkp).2
      have h2 := (OMA.A361713.choose_add_div_mod p m hp hkp).2
      have hk_ne : ((m + 1 : ℕ) : ZMod p) ≠ 0 := by
        intro h0
        have hd : p ∣ m + 1 := (ZMod.natCast_eq_zero_iff _ _).mp h0
        have hle := Nat.le_of_dvd (by omega) hd
        omega
      have hu2 : ((p.choose (m + 1) / p : ℕ) : ZMod p) ^ 2 = (((m + 1 : ℕ) : ZMod p)⁻¹) ^ 2 := by
        have hmul_inv : (((m + 1 : ℕ) : ZMod p) ^ 2)⁻¹ * (((m + 1 : ℕ) : ZMod p) ^ 2 *
            ((p.choose (m + 1) / p : ℕ) : ZMod p) ^ 2) = (((m + 1 : ℕ) : ZMod p) ^ 2)⁻¹ * 1 :=
          congrArg ((((m + 1 : ℕ) : ZMod p) ^ 2)⁻¹ * ·) h1
        rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hk_ne), one_mul, mul_one, ← inv_pow] at hmul_inv
        exact hmul_inv
      have hv2 : (((p + m).choose (m + 1) / p : ℕ) : ZMod p) ^ 2 = (((m + 1 : ℕ) : ZMod p)⁻¹) ^ 2 := by
        have hmul_inv : (((m + 1 : ℕ) : ZMod p) ^ 2)⁻¹ * (((m + 1 : ℕ) : ZMod p) ^ 2 *
            (((p + m).choose (m + 1) / p : ℕ) : ZMod p) ^ 2) = (((m + 1 : ℕ) : ZMod p) ^ 2)⁻¹ * 1 :=
          congrArg ((((m + 1 : ℕ) : ZMod p) ^ 2)⁻¹ * ·) h2
        rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hk_ne), one_mul, mul_one, ← inv_pow] at hmul_inv
        exact hmul_inv
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, hu2, hv2]
      ring
    rw [hterm]
    have hrange : ∑ k ∈ Finset.Ico 1 p, ((k : ZMod p)⁻¹) ^ 4 =
        ∑ k ∈ Finset.range p, ((k : ZMod p)⁻¹) ^ 4 := by
      rw [← Nat.Ico_zero_eq_range, Finset.sum_eq_sum_Ico_succ_bot hp.pos]
      simp
    rw [hrange]
    have hfin : ∑ k ∈ Finset.range p, ((k : ZMod p)⁻¹) ^ 4 = ∑ x : ZMod p, (x⁻¹) ^ 4 := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => ((k : ZMod p)⁻¹) ^ 4) p]
      refine Finset.sum_bij (fun (i : Fin p) _ => (i.val : ZMod p))
        (fun _ _ => Finset.mem_univ _)
        (fun i _ j _ hij => Fin.ext (by
          have h := congrArg ZMod.val hij
          rw [ZMod.val_natCast_of_lt i.isLt, ZMod.val_natCast_of_lt j.isLt] at h
          exact h))
        (fun x _ => ⟨⟨x.val, x.val_lt⟩, Finset.mem_univ _, ZMod.natCast_zmod_val x⟩)
        (fun _ _ => rfl)
    rw [hfin]
    have hinv : ∑ x : ZMod p, (x⁻¹) ^ 4 = ∑ x : ZMod p, x ^ 4 :=
      Fintype.sum_equiv (Equiv.inv (ZMod p)) (fun x => (x⁻¹) ^ 4) (fun x => x ^ 4) (fun _ => rfl)
    rw [hinv]
    exact OMA.A361713.sum_pow_four_zmod_eq_zero p hp7
  have hpdvd : p ∣ S := (ZMod.natCast_eq_zero_iff S p).mp hS_zmod
  rcases hpdvd with ⟨q, hq⟩
  refine ⟨(q : ℤ), ?_⟩
  rw [hq]
  push_cast
  ring
