import OMAStatements.S_oeis_a356334
import Mathlib

open OMA.S_oeis_a356334

namespace OMA.P_oeis_a356334

lemma not_dvd_a {a b p : ℕ} (hab : Nat.Coprime a b) (hp : p.Prime) (hs : p ∣ a + b) : ¬ p ∣ a := by
  intro hpa
  have hpb : p ∣ b := (Nat.dvd_add_right hpa).mp hs
  have := Nat.dvd_gcd hpa hpb
  rw [hab] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

lemma two_pow_gt (n : ℕ) (hn : 4 ≤ n) : 2 * (n + 1) < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

lemma core_odd (a b g n : ℕ) (hab : Nat.Coprime a b) (ha1 : 1 ≤ a) (hlt : a < b) (hn : Odd n)
    (h : g * (a ^ (n + 1) + b ^ (n + 1)) = (a + b) ^ n) : False := by
  set S := a ^ (n + 1) + b ^ (n + 1) with hSdef
  have hSd : S ∣ (a + b) ^ n := ⟨g, by rw [← h]; ring⟩
  have hb2 : 2 ≤ b := by omega
  have hS4 : 4 ≤ S := by
    have : 2 ^ (n + 1) ≤ b ^ (n + 1) := Nat.pow_le_pow_left hb2 _
    have : 4 ≤ 2 ^ (n + 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by obtain ⟨k, rfl⟩ := hn; omega)
    omega
  have hS0 : S ≠ 0 := by omega
  obtain ⟨k, r, hr, hkr⟩ := Nat.exists_eq_two_pow_mul_odd hS0
  have hr1 : r = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpr⟩ := Nat.exists_prime_and_dvd hne
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hr) (even_iff_two_dvd.mpr hpr)
    have hpS : p ∣ S := by rw [hkr]; exact Dvd.dvd.mul_left hpr _
    have hps : p ∣ a + b := hp.dvd_of_dvd_pow (dvd_trans hpS hSd)
    have hpa := not_dvd_a hab hp hps
    have := Fact.mk hp
    have e1 : ((a + b : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hps
    have e2 : ((S : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpS
    push_cast at e1
    have hb : (b : ZMod p) = -a := by linear_combination e1
    have hev : Even (n + 1) := by obtain ⟨j, rfl⟩ := hn; exact ⟨j + 1, by ring⟩
    rw [hSdef] at e2
    push_cast at e2
    rw [hb, hev.neg_pow] at e2
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h20
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h20
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
    have : (2 : ZMod p) * (a : ZMod p) ^ (n + 1) = 0 := by linear_combination e2
    rcases mul_eq_zero.mp this with h | h
    · exact h2 h
    · have := pow_eq_zero_iff (n := n + 1) (by omega) |>.mp h
      exact hpa ((ZMod.natCast_eq_zero_iff _ _).mp this)
  subst hr1
  have h2S : 2 ∣ S := by
    rw [hkr]
    rcases k with _ | k
    · simp at hkr; omega
    · exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  have h4S : 4 ∣ S := by
    rw [hkr]
    rcases k with _ | _ | k
    · simp at hkr; omega
    · simp at hkr; omega
    · exact Dvd.dvd.mul_right ⟨2 ^ k, by ring⟩ _
  have hps : 2 ∣ a + b := Nat.prime_two.dvd_of_dvd_pow (dvd_trans h2S hSd)
  have ha : ¬ 2 ∣ a := not_dvd_a hab Nat.prime_two hps
  have hb : ¬ 2 ∣ b := by omega
  obtain ⟨j, hj⟩ := hn
  have hA : 8 ∣ (a ^ (j + 1)) ^ 2 - 1 :=
    Nat.eight_dvd_sq_sub_one_of_odd (Odd.pow (Nat.odd_iff.mpr (by omega)))
  have hB : 8 ∣ (b ^ (j + 1)) ^ 2 - 1 :=
    Nat.eight_dvd_sq_sub_one_of_odd (Odd.pow (Nat.odd_iff.mpr (by omega)))
  have hA1 : 1 ≤ (a ^ (j + 1)) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by
    apply pow_ne_zero; apply pow_ne_zero; omega)
  have hB1 : 1 ≤ (b ^ (j + 1)) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by
    apply pow_ne_zero; apply pow_ne_zero; omega)
  have hSe : S = (a ^ (j + 1)) ^ 2 + (b ^ (j + 1)) ^ 2 := by
    rw [hSdef, hj, ← pow_mul, ← pow_mul]; ring_nf
  omega


lemma core_even (a b g n : ℕ) (hab : Nat.Coprime a b) (ha1 : 1 ≤ a) (hlt : a < b) (hn : Even n)
    (hn4 : 4 ≤ n) (h : g * (a ^ (n + 1) + b ^ (n + 1)) = (a + b) ^ n) : False := by
  set S := a ^ (n + 1) + b ^ (n + 1) with hSdef
  have hSd : S ∣ (a + b) ^ n := ⟨g, by rw [← h]; ring⟩
  have hodd : Odd (n + 1) := hn.add_one
  obtain ⟨Φ, hΦ⟩ : a + b ∣ S := hodd.nat_add_dvd_pow_add_pow a b
  have hs0 : a + b ≠ 0 := by omega
  have hS0 : S ≠ 0 := by
    have : 0 < b ^ (n + 1) := pow_pos (by omega) _
    omega
  have hΦ0 : Φ ≠ 0 := by rintro rfl; simp at hΦ; exact hS0 hΦ
  have hΦdvd : Φ ∣ n + 1 := by
    rw [← Nat.factorization_prime_le_iff_dvd hΦ0 (by omega)]
    intro p hp
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
    by_cases hpΦ : p ∣ Φ
    · have hpS : p ∣ S := by rw [hΦ]; exact Dvd.dvd.mul_left hpΦ _
      have hps : p ∣ a + b := hp.dvd_of_dvd_pow (dvd_trans hpS hSd)
      have hpa := not_dvd_a hab hp hps
      have := Fact.mk hp
      rcases hp.eq_two_or_odd' with rfl | hpo
      · exfalso
        have hb : ¬ 2 ∣ b := by omega
        have key := not_dvd_geom_sum₂ (R := ℤ) (x := (a : ℤ)) (y := -(b : ℤ)) (n := n + 1)
          Int.prime_two (by rw [sub_neg_eq_add]; exact_mod_cast hps)
          (by exact_mod_cast hpa)
          (by
            intro h2
            have : (2 : ℕ) ∣ n + 1 := by exact_mod_cast h2
            exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this))
        have hg := geom_sum₂_mul (a : ℤ) (-(b : ℤ)) (n + 1)
        rw [hodd.neg_pow, sub_neg_eq_add, sub_neg_eq_add] at hg
        have hSZ : ((S : ℕ) : ℤ) = ((a : ℤ) + b) * Φ := by rw [hΦ]; push_cast; ring
        have hSZ' : ((S : ℕ) : ℤ) = (a : ℤ) ^ (n + 1) + (b : ℤ) ^ (n + 1) := by
          rw [hSdef]; push_cast; ring
        have hs0' : ((a : ℤ) + b) ≠ 0 := by positivity
        have heq : (∑ i ∈ Finset.range (n + 1), (a : ℤ) ^ i * (-(b : ℤ)) ^ (n + 1 - 1 - i)) =
            (Φ : ℤ) := by
          apply mul_right_cancel₀ hs0'
          rw [hg, ← hSZ', hSZ]; ring
        rw [heq] at key
        exact key (by exact_mod_cast hpΦ)
      · have h1 := padicValNat.pow_add_pow (p := p) (x := a) (y := b) hpo hps hpa hodd
        have h2 : padicValNat p S = padicValNat p (a + b) + padicValNat p Φ := by
          rw [hΦ]; exact padicValNat.mul hs0 hΦ0
        rw [← hSdef] at h1
        omega
    · rw [padicValNat.eq_zero_of_not_dvd hpΦ]; exact Nat.zero_le _
  have hΦle : Φ ≤ n + 1 := Nat.le_of_dvd (by omega) hΦdvd
  have h1 : b ^ (n + 1) ≤ S := Nat.le_add_left _ _
  have h2 : S ≤ (a + b) * (n + 1) := by rw [hΦ]; exact Nat.mul_le_mul_left _ hΦle
  have h3 : b * b ^ n ≤ b * (2 * (n + 1)) := by
    rw [← pow_succ']
    have : (a + b) * (n + 1) ≤ (2 * b) * (n + 1) := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  have h4 : b ^ n ≤ 2 * (n + 1) := Nat.le_of_mul_le_mul_left h3 (by omega)
  have h5 : 2 ^ n ≤ b ^ n := Nat.pow_le_pow_left (by omega) _
  have h6 := two_pow_gt n hn4
  omega

lemma core (a b g n : ℕ) (hab : Nat.Coprime a b) (ha1 : 1 ≤ a) (hlt : a < b) (hn : 1 ≤ n)
    (hn2 : n ≠ 2) (h : g * (a ^ (n + 1) + b ^ (n + 1)) = (a + b) ^ n) : False := by
  rcases Nat.even_or_odd n with he | ho
  · exact core_even a b g n hab ha1 hlt he (by obtain ⟨k, rfl⟩ := he; omega) h
  · exact core_odd a b g n hab ha1 hlt ho h

lemma classify (n : ℕ) (hn : 1 ≤ n) (hn2 : n ≠ 2) (x y : ℕ) :
    (x ≤ y ∧ x ^ (n + 1) + y ^ (n + 1) = (x + y) ^ n) ↔
      (x = 0 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 2 ^ (n - 1) ∧ y = 2 ^ (n - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  constructor
  · rintro ⟨hxy, he⟩
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
        zero_add] at he
      rcases Nat.lt_or_ge y 2 with hy | hy
      · interval_cases y <;> simp
      · exfalso
        have : y ^ (k + 1) < y ^ (k + 1 + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
        omega
    · right; right
      have hg : 0 < Nat.gcd x y := Nat.gcd_pos_of_pos_left _ hx
      obtain ⟨a, b, hab, hxa, hyb⟩ := Nat.exists_coprime x y
      set g := Nat.gcd x y
      have ha1 : 1 ≤ a := by
        rcases Nat.eq_zero_or_pos a with h0 | h0
        · rw [h0] at hxa; omega
        · exact h0
      have hab' : a ≤ b := by
        rw [hxa, hyb] at hxy; exact Nat.le_of_mul_le_mul_right hxy hg
      have key : g * (a ^ (k + 1 + 1) + b ^ (k + 1 + 1)) = (a + b) ^ (k + 1) := by
        apply Nat.eq_of_mul_eq_mul_left (pow_pos hg (k + 1))
        calc g ^ (k + 1) * (g * (a ^ (k + 1 + 1) + b ^ (k + 1 + 1)))
            = (a * g) ^ (k + 1 + 1) + (b * g) ^ (k + 1 + 1) := by ring
          _ = (a * g + b * g) ^ (k + 1) := by rw [← hxa, ← hyb]; exact he
          _ = g ^ (k + 1) * (a + b) ^ (k + 1) := by rw [← add_mul, mul_pow, mul_comm]
      rcases Nat.lt_or_ge a b with hlt | hge
      · exact (core a b g (k + 1) hab ha1 hlt (by omega) hn2 key).elim
      · have hba : a = b := by omega
        subst hba
        have ha : a = 1 := by simpa [Nat.Coprime] using hab
        subst ha
        have : g * 2 = 2 ^ k * 2 := by
          simp only [one_pow] at key; rw [pow_succ] at key; omega
        have hgk : g = 2 ^ k := by omega
        rw [hxa, hyb, hgk]; simp
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · simp
    · simp
    · refine ⟨le_rfl, ?_⟩
      have e1 : 2 * (2 ^ k) ^ (k + 1 + 1) = 2 ^ (k * (k + 2) + 1) := by
        rw [← pow_mul, pow_succ]; ring
      have e2 : (2 ^ k + 2 ^ k) ^ (k + 1) = 2 ^ ((k + 1) * (k + 1)) := by
        rw [pow_mul]; ring
      rw [← two_mul, e1, e2]
      congr 1
      ring

end OMA.P_oeis_a356334

open OMA.P_oeis_a356334 in
theorem OMA.solution : type_of% @OMA.S_oeis_a356334.main := by
  intro n hn0 hn2
  have hs : sols n = ↑({(0, 0), (0, 1), (2 ^ (n - 1), 2 ^ (n - 1))} : Finset (ℕ × ℕ)) := by
    ext ⟨x, y⟩
    simp only [sols, Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, Prod.mk.injEq]
    exact classify n (by omega) hn2 x y
  rw [a, hs, Set.ncard_coe_finset]
  have hp : (0 : ℕ) ≠ 2 ^ (n - 1) := (pow_pos (by norm_num) _).ne
  rw [Finset.card_insert_of_notMem, Finset.card_pair]
  · simp [hp]
  · simp [hp]

