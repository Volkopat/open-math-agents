import OMAStatements.S_oeis_a053031
import Mathlib

namespace OMA.P_oeis_a053031

open OMA.S_oeis_a053031

/-- Fibonacci Q-matrix over `ℤ`. -/
private def fibMat : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, 0]

private lemma fibMat_pow (n : ℕ) :
    fibMat ^ (n + 1) = !![(Nat.fib (n + 2) : ℤ), (Nat.fib (n + 1) : ℤ);
                          (Nat.fib (n + 1) : ℤ), (Nat.fib n : ℤ)] := by
  induction n with
  | zero =>
    ext i j; fin_cases i <;> fin_cases j <;> simp [fibMat]
  | succ k ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [fibMat, Matrix.mul_apply, Fin.sum_univ_two, Nat.fib_add_two] <;> ring

private lemma fib_add_mul (a b : ℕ) :
    Nat.fib (a + b + 1) = Nat.fib (a + 1) * Nat.fib (b + 1) + Nat.fib a * Nat.fib b := by
  have h11 := congr_arg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 1) (pow_add fibMat (a + 1) (b + 1))
  rw [show a + 1 + (b + 1) = (a + b + 1) + 1 by omega, fibMat_pow, fibMat_pow, fibMat_pow] at h11
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h11
  exact_mod_cast h11

private lemma cassini (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - (Nat.fib n : ℤ) * (Nat.fib (n + 2) : ℤ) = (-1 : ℤ) ^ n := by
  have hdet : (fibMat ^ (n + 1)).det = (-1 : ℤ) ^ (n + 1) := by
    rw [Matrix.det_pow]
    have hd : fibMat.det = -1 := by simp [fibMat, Matrix.det_fin_two]
    rw [hd]
  rw [fibMat_pow, Matrix.det_fin_two] at hdet
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hdet
  have h1 : (Nat.fib (n + 2) : ℤ) * (Nat.fib n : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2 = -((-1 : ℤ) ^ n) := by
    rw [pow_succ'] at hdet; linarith
  linarith

private lemma int_pow_emod (a : ℤ) (n : ℕ) (m : ℤ) :
    (a ^ n) % m = ((a % m) ^ n) % m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, Int.mul_emod, ih]
    conv_rhs => rw [Int.mul_emod, Int.emod_emod]

private lemma fib_coprime_succ (r : ℕ) : Nat.Coprime (Nat.fib r) (Nat.fib (r + 1)) := by
  rw [Nat.Coprime, ← Nat.fib_gcd]
  have hg : Nat.gcd r (r + 1) = 1 := by
    have h1 := Nat.gcd_dvd_left r (r + 1)
    have h2 := Nat.gcd_dvd_right r (r + 1)
    exact Nat.eq_one_of_dvd_one ((Nat.dvd_add_right h1).mp h2)
  rw [hg]
  rfl

/-- Lucas sequence `L(r) = 2 * F(r + 1) - F(r)`. -/
private def lucas (r : ℕ) : ℤ :=
  2 * (Nat.fib (r + 1) : ℤ) - (Nat.fib r : ℤ)

private lemma fib_two_mul_eq (r : ℕ) :
    (Nat.fib (2 * r) : ℤ) = (Nat.fib r : ℤ) * lucas r := by
  cases r with
  | zero => simp [lucas]
  | succ r' =>
    have h := fib_add_mul r' (r' + 1)
    rw [show r' + (r' + 1) + 1 = 2 * (r' + 1) by omega] at h
    have hcast : (Nat.fib (2 * (r' + 1)) : ℤ) =
        (Nat.fib (r' + 1) : ℤ) * (Nat.fib (r' + 2) : ℤ) + (Nat.fib r' : ℤ) * (Nat.fib (r' + 1) : ℤ) := by
      exact_mod_cast h
    have hrec : (Nat.fib (r' + 2) : ℤ) = (Nat.fib r' : ℤ) + (Nat.fib (r' + 1) : ℤ) := by
      exact_mod_cast Nat.fib_add_two
    have h11 : r' + 1 + 1 = r' + 2 := rfl
    unfold lucas
    rw [h11]
    nlinarith [hcast, hrec]

private lemma fib_two_mul_add_one_eq (r : ℕ) :
    (Nat.fib (2 * r + 1) : ℤ) = (Nat.fib (r + 1) : ℤ) * lucas r - (-1 : ℤ) ^ r := by
  have h := fib_add_mul r r
  rw [show r + r + 1 = 2 * r + 1 by omega] at h
  have hcast : (Nat.fib (2 * r + 1) : ℤ) = (Nat.fib (r + 1) : ℤ) ^ 2 + (Nat.fib r : ℤ) ^ 2 := by
    have : (Nat.fib (2 * r + 1) : ℤ) =
        (Nat.fib (r + 1) : ℤ) * (Nat.fib (r + 1) : ℤ) + (Nat.fib r : ℤ) * (Nat.fib r : ℤ) := by
      exact_mod_cast h
    linarith
  have hc := cassini r
  have hrec : (Nat.fib (r + 2) : ℤ) = (Nat.fib r : ℤ) + (Nat.fib (r + 1) : ℤ) := by
    exact_mod_cast Nat.fib_add_two
  unfold lucas
  nlinarith [hcast, hc, hrec]

private lemma lucas_sq_eq (r : ℕ) :
    (lucas r) ^ 2 - 5 * (Nat.fib r : ℤ) ^ 2 = 4 * (-1 : ℤ) ^ r := by
  have hc := cassini r
  have hrec : (Nat.fib (r + 2) : ℤ) = (Nat.fib r : ℤ) + (Nat.fib (r + 1) : ℤ) := by
    exact_mod_cast Nat.fib_add_two
  unfold lucas
  nlinarith [hc, hrec]

private lemma four_mul_fib_two_mul_add_one (r : ℕ) :
    4 * (Nat.fib (2 * r + 1) : ℤ) =
      4 * (-1 : ℤ) ^ r + 2 * lucas r * (Nat.fib r : ℤ) + 10 * (Nat.fib r : ℤ) ^ 2 := by
  have h1 := fib_two_mul_add_one_eq r
  have h2 := lucas_sq_eq r
  have h3 : 2 * (Nat.fib (r + 1) : ℤ) = lucas r + (Nat.fib r : ℤ) := by unfold lucas; ring
  nlinarith [h1, h2, h3]

private lemma exists_pisanoPeriod (m : ℕ) (hm : 1 ≤ m) :
    ∃ p : ℕ, IsPisanoPeriod m p := by
  let f : Fin (m * m + 1) → Fin m × Fin m := fun k =>
    (⟨Nat.fib k.val % m, Nat.mod_lt _ (by omega)⟩,
     ⟨Nat.fib (k.val + 1) % m, Nat.mod_lt _ (by omega)⟩)
  have hcard : Fintype.card (Fin m × Fin m) < Fintype.card (Fin (m * m + 1)) := by
    simp
  obtain ⟨i, j, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  wlog hlt : i.val < j.val generalizing i j
  · exact this j i hne.symm heq.symm (by have := Fin.val_ne_of_ne hne; omega)
  have hmod0 : Nat.fib i.val % m = Nat.fib j.val % m := congr_arg (fun p => p.1.val) heq
  have hmod1 : Nat.fib (i.val + 1) % m = Nat.fib (j.val + 1) % m := congr_arg (fun p => p.2.val) heq
  have hback : ∀ a b : ℕ, a ≤ b →
      Nat.fib a % m = Nat.fib b % m →
      Nat.fib (a + 1) % m = Nat.fib (b + 1) % m →
      Nat.fib (b - a) % m = 0 ∧ Nat.fib (b - a + 1) % m = 1 % m := by
    intro a
    induction a with
    | zero =>
      intro b _ h0 h1
      simpa using And.intro h0.symm h1.symm
    | succ a ih =>
      intro b hab h0 h1
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0) with ⟨b', rfl⟩
      have hprev : Nat.fib a % m = Nat.fib b' % m := by
        have hstep : (Nat.fib a + Nat.fib (a + 1)) % m = (Nat.fib b' + Nat.fib (b' + 1)) % m := by
          rw [← Nat.fib_add_two, ← Nat.fib_add_two]; exact h1
        have h1' : (Nat.fib a % m + Nat.fib (a + 1) % m) % m =
            (Nat.fib b' % m + Nat.fib (b' + 1) % m) % m := by
          simpa [Nat.add_mod] using hstep
        rw [h0] at h1'
        have hlt1 : Nat.fib a % m < m := Nat.mod_lt _ (by omega)
        have hlt2 : Nat.fib b' % m < m := Nat.mod_lt _ (by omega)
        by_contra hne_ab
        have hd : ((Nat.fib a % m : ℤ) - (Nat.fib b' % m : ℤ)) % (m : ℤ) = 0 := by
          have hz : ((Nat.fib a % m + Nat.fib (b' + 1) % m : ℕ) : ℤ) % (m : ℤ) =
              ((Nat.fib b' % m + Nat.fib (b' + 1) % m : ℕ) : ℤ) % (m : ℤ) := by
            exact_mod_cast h1'
          have hsub : (((Nat.fib a % m + Nat.fib (b' + 1) % m : ℕ) : ℤ) -
              ((Nat.fib b' % m + Nat.fib (b' + 1) % m : ℕ) : ℤ)) % (m : ℤ) = 0 := by
            rw [Int.sub_emod, hz, sub_self, Int.zero_emod]
          have hsimp : ((Nat.fib a % m + Nat.fib (b' + 1) % m : ℕ) : ℤ) -
              ((Nat.fib b' % m + Nat.fib (b' + 1) % m : ℕ) : ℤ) =
              (Nat.fib a % m : ℤ) - (Nat.fib b' % m : ℤ) := by push_cast; ring
          rwa [hsimp] at hsub
        obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero hd
        have hlt1z : (Nat.fib a : ℤ) % (m : ℤ) < (m : ℤ) := by
          have : ((Nat.fib a % m : ℕ) : ℤ) < (m : ℤ) := by exact_mod_cast hlt1
          simpa [Int.natCast_emod] using this
        have hlt2z : (Nat.fib b' : ℤ) % (m : ℤ) < (m : ℤ) := by
          have : ((Nat.fib b' % m : ℕ) : ℤ) < (m : ℤ) := by exact_mod_cast hlt2
          simpa [Int.natCast_emod] using this
        have h01 : (0 : ℤ) ≤ (Nat.fib a : ℤ) % (m : ℤ) := by
          have : (0 : ℤ) ≤ ((Nat.fib a % m : ℕ) : ℤ) := by positivity
          simpa [Int.natCast_emod] using this
        have h02 : (0 : ℤ) ≤ (Nat.fib b' : ℤ) % (m : ℤ) := by
          have : (0 : ℤ) ≤ ((Nat.fib b' % m : ℕ) : ℤ) := by positivity
          simpa [Int.natCast_emod] using this
        have hq0 : q = 0 := by nlinarith
        rw [hq0, mul_zero] at hq
        have heq_z : (Nat.fib a : ℤ) % (m : ℤ) = (Nat.fib b' : ℤ) % (m : ℤ) := by linarith
        have heq_nat : ((Nat.fib a % m : ℕ) : ℤ) = ((Nat.fib b' % m : ℕ) : ℤ) := by
          simpa [Int.natCast_emod] using heq_z
        exact hne_ab (by exact_mod_cast heq_nat)
      have hres := ih b' (by omega) hprev h0
      simpa [Nat.succ_sub_succ] using hres
  obtain ⟨h0, h1⟩ := hback i.val j.val (le_of_lt hlt) hmod0 hmod1
  exact ⟨j.val - i.val, by omega, h0, h1⟩

private lemma pisanoPeriod_spec (m : ℕ) (hm : 1 ≤ m) :
    IsPisanoPeriod m (pisanoPeriod m) :=
  Nat.sInf_mem (exists_pisanoPeriod m hm)

private lemma pisanoPeriod_le (m p : ℕ) (hp : IsPisanoPeriod m p) :
    pisanoPeriod m ≤ p :=
  Nat.sInf_le hp

private noncomputable def fibEntry (m : ℕ) : ℕ :=
  sInf { z : ℕ | 0 < z ∧ m ∣ Nat.fib z }

private lemma exists_fibEntry (m : ℕ) (hm : 1 ≤ m) :
    ∃ z : ℕ, 0 < z ∧ m ∣ Nat.fib z := by
  obtain ⟨p, hp0, hp1, _⟩ := exists_pisanoPeriod m hm
  exact ⟨p, hp0, Nat.dvd_of_mod_eq_zero hp1⟩

private lemma fibEntry_spec (m : ℕ) (hm : 1 ≤ m) :
    0 < fibEntry m ∧ m ∣ Nat.fib (fibEntry m) :=
  Nat.sInf_mem (exists_fibEntry m hm)

private lemma dvd_fib_iff_fibEntry_dvd (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    m ∣ Nat.fib k ↔ fibEntry m ∣ k := by
  constructor
  · intro hk
    have hz := fibEntry_spec m hm
    have hgcd : m ∣ Nat.fib (Nat.gcd k (fibEntry m)) := by
      rw [Nat.fib_gcd]; exact Nat.dvd_gcd hk hz.2
    have hpos : 0 < Nat.gcd k (fibEntry m) := Nat.gcd_pos_of_pos_right k hz.1
    have hle : fibEntry m ≤ Nat.gcd k (fibEntry m) := Nat.sInf_le ⟨hpos, hgcd⟩
    have hge : Nat.gcd k (fibEntry m) ≤ fibEntry m := Nat.gcd_le_right k hz.1
    have heq : Nat.gcd k (fibEntry m) = fibEntry m := le_antisymm hge hle
    rw [← heq]; exact Nat.gcd_dvd_left k (fibEntry m)
  · intro hk
    exact dvd_trans (fibEntry_spec m hm).2 (Nat.fib_dvd _ _ hk)

private lemma fib_mul_succ_mod (m z : ℕ) (hz : m ∣ Nat.fib z) (j : ℕ) :
    Nat.fib (j * z + 1) % m = (Nat.fib (z + 1) ^ j) % m := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hadd : (j + 1) * z + 1 = j * z + z + 1 := by ring
    rw [hadd, fib_add_mul]
    have h0 : Nat.fib z % m = 0 := Nat.mod_eq_zero_of_dvd hz
    rw [Nat.add_mod, Nat.mul_mod (Nat.fib (j * z + 1)), ih,
      Nat.mul_mod (Nat.fib (j * z)), h0, mul_zero, Nat.zero_mod, add_zero, Nat.mod_mod,
      ← Nat.mul_mod, pow_succ]

private lemma isPisanoPeriod_iff (m : ℕ) (hm : 1 ≤ m) (p : ℕ) :
    IsPisanoPeriod m p ↔
      ∃ j : ℕ, 0 < j ∧ p = j * fibEntry m ∧ Nat.fib (fibEntry m + 1) ^ j % m = 1 % m := by
  have hz := fibEntry_spec m hm
  constructor
  · rintro ⟨hp0, hpF, hpS⟩
    have hdvd : fibEntry m ∣ p := (dvd_fib_iff_fibEntry_dvd m hm p).mp (Nat.dvd_of_mod_eq_zero hpF)
    rcases hdvd with ⟨j, rfl⟩
    have hj0 : 0 < j := by
      rcases eq_or_ne j 0 with rfl | hne
      · simp at hp0
      · omega
    refine ⟨j, hj0, by ring, ?_⟩
    rw [mul_comm] at hpS
    rwa [← fib_mul_succ_mod m (fibEntry m) hz.2 j]
  · rintro ⟨j, hj0, rfl, hpow⟩
    refine ⟨Nat.mul_pos hj0 hz.1, ?_, ?_⟩
    · exact Nat.mod_eq_zero_of_dvd ((dvd_fib_iff_fibEntry_dvd m hm (j * fibEntry m)).mpr (dvd_mul_left _ _))
    · rw [fib_mul_succ_mod m (fibEntry m) hz.2 j, hpow]

private lemma fibZeros_eq_one_iff (m : ℕ) (hm : 1 ≤ m) :
    fibZeros m = 1 ↔ Nat.fib (fibEntry m + 1) % m = 1 % m := by
  have hz := fibEntry_spec m hm
  obtain ⟨r, hr0, hpeq, hrpow⟩ := (isPisanoPeriod_iff m hm (pisanoPeriod m)).mp (pisanoPeriod_spec m hm)
  have hzeros_eq : fibZeros m = r := by
    unfold fibZeros
    rw [hpeq]
    have hbij : ((Finset.range (r * fibEntry m)).filter (fun k => Nat.fib k % m = 0)).card =
        (Finset.range r).card := by
      refine Finset.card_bij (fun k _ => k / fibEntry m) ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
        exact Nat.div_lt_of_lt_mul (by linarith)
      · intro a ha b hb hab
        simp only [Finset.mem_filter] at ha hb
        have ha' : fibEntry m ∣ a := (dvd_fib_iff_fibEntry_dvd m hm a).mp (Nat.dvd_of_mod_eq_zero ha.2)
        have hb' : fibEntry m ∣ b := (dvd_fib_iff_fibEntry_dvd m hm b).mp (Nat.dvd_of_mod_eq_zero hb.2)
        rw [← Nat.mul_div_cancel' ha', ← Nat.mul_div_cancel' hb', hab]
      · intro j hj
        simp only [Finset.mem_range] at hj
        refine ⟨j * fibEntry m, ?_, Nat.mul_div_cancel j hz.1⟩
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by nlinarith [hz.1],
          Nat.mod_eq_zero_of_dvd ((dvd_fib_iff_fibEntry_dvd m hm _).mpr (dvd_mul_left _ _))⟩
    rw [hbij, Finset.card_range]
  rw [hzeros_eq]
  constructor
  · intro hr1
    rw [hr1, pow_one] at hrpow
    exact hrpow
  · intro h1
    have hper : IsPisanoPeriod m (1 * fibEntry m) :=
      (isPisanoPeriod_iff m hm _).mpr ⟨1, by omega, rfl, by simpa using h1⟩
    have hle := pisanoPeriod_le m (1 * fibEntry m) hper
    rw [hpeq] at hle
    have hrle : r ≤ 1 := Nat.le_of_mul_le_mul_right hle hz.1
    omega

private lemma fibEntry_dvd_of_dvd {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) (hdm : d ∣ m) :
    fibEntry d ∣ fibEntry m :=
  (dvd_fib_iff_fibEntry_dvd d hd (fibEntry m)).mp (dvd_trans hdm (fibEntry_spec m hm).2)

private lemma fibEntry_mul_coprime {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hcop : Nat.Coprime a b) :
    fibEntry (a * b) = Nat.lcm (fibEntry a) (fibEntry b) := by
  have hab : 1 ≤ a * b := Nat.mul_pos ha hb
  apply Nat.dvd_antisymm
  · apply (dvd_fib_iff_fibEntry_dvd (a * b) hab _).mp
    apply hcop.mul_dvd_of_dvd_of_dvd
    · exact (dvd_fib_iff_fibEntry_dvd a ha _).mpr (Nat.dvd_lcm_left _ _)
    · exact (dvd_fib_iff_fibEntry_dvd b hb _).mpr (Nat.dvd_lcm_right _ _)
  · exact Nat.lcm_dvd
      (fibEntry_dvd_of_dvd ha hab (dvd_mul_right a b))
      (fibEntry_dvd_of_dvd hb hab (dvd_mul_left b a))

private lemma fib_mul_prime_dvd (p r k : ℕ) (hp : p.Prime) (hr : 1 ≤ r) (hk : 1 ≤ k)
    (hdvd : p ^ r ∣ Nat.fib k) :
    p ^ (r + 1) ∣ Nat.fib (p * k) := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0) with ⟨k', rfl⟩
  have hFk : (p ^ r : ℤ) ∣ (Nat.fib (k' + 1) : ℤ) := Int.natCast_dvd_natCast.mpr hdvd
  rcases hFk with ⟨q, hq⟩
  let a : ℤ := (Nat.fib k' : ℤ)
  let B : Matrix (Fin 2) (Fin 2) ℤ := !![q, q; q, 0]
  have hMk : fibMat ^ (k' + 1) = a • (1 : Matrix (Fin 2) (Fin 2) ℤ) + ((p : ℤ) ^ r) • B := by
    rw [fibMat_pow]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, a, B, Fin.isValue, ite_true, ite_false,
        Fin.zero_eta, Fin.mk_one, Fin.reduceEq, Nat.fib_add_two] <;> push_cast <;> linarith [hq]
  have hcomm : Commute (((p : ℤ) ^ r) • B) (a • (1 : Matrix (Fin 2) (Fin 2) ℤ)) := by
    rw [Commute, SemiconjBy, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.smul_mul, mul_one, one_mul, smul_comm]
  have hpow : fibMat ^ (p * (k' + 1)) =
      (((p : ℤ) ^ r) • B + a • (1 : Matrix (Fin 2) (Fin 2) ℤ)) ^ p := by
    rw [mul_comm, pow_mul, hMk, add_comm]
  rw [hcomm.add_pow] at hpow
  have h01 := congr_arg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) hpow
  have hpk_pos : 1 ≤ p * (k' + 1) := Nat.mul_pos hp.pos (by omega)
  have hlhs : (fibMat ^ (p * (k' + 1))) 0 1 = (Nat.fib (p * (k' + 1)) : ℤ) := by
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : p * (k' + 1) ≠ 0) with ⟨m, hm⟩
    rw [hm, fibMat_pow]; simp
  rw [hlhs] at h01
  have hrhs_dvd : ((p : ℤ) ^ (r + 1)) ∣
      (∑ j ∈ Finset.range (p + 1),
        (((p : ℤ) ^ r) • B) ^ j *
        (a • (1 : Matrix (Fin 2) (Fin 2) ℤ)) ^ (p - j) *
        (p.choose j : Matrix (Fin 2) (Fin 2) ℤ)) 0 1 := by
    rw [Matrix.sum_apply]
    refine Finset.dvd_sum (fun j _ => ?_)
    have hnat : ∀ (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ),
        M * (n : Matrix (Fin 2) (Fin 2) ℤ) = (n : ℤ) • M := by
      intro M n
      induction n with
      | zero => simp
      | succ n ih =>
        push_cast
        rw [mul_add, mul_one, ih, add_smul, one_smul]
    have hterm : ((((p : ℤ) ^ r) • B) ^ j *
        (a • (1 : Matrix (Fin 2) (Fin 2) ℤ)) ^ (p - j) *
        (p.choose j : Matrix (Fin 2) (Fin 2) ℤ)) =
        (a ^ (p - j) * ((p : ℤ) ^ r) ^ j * (p.choose j : ℤ)) • (B ^ j) := by
      rw [smul_pow, smul_pow, one_pow, Matrix.smul_mul, Matrix.mul_smul, mul_one,
        hnat, smul_smul, smul_smul]
      congr 1; ring
    rw [hterm, Matrix.smul_apply, smul_eq_mul]
    by_cases hj0 : j = 0
    · subst hj0; simp
    · by_cases hj1 : j = 1
      · subst hj1
        rw [Nat.choose_one_right, pow_one]
        exact dvd_mul_of_dvd_left ⟨a ^ (p - 1), by rw [pow_succ]; ring⟩ _
      · have hj2 : 2 ≤ j := by omega
        have hle : r + 1 ≤ r * j := by nlinarith
        have hpow_dvd : ((p : ℤ) ^ (r + 1)) ∣ ((p : ℤ) ^ r) ^ j := by
          rw [← pow_mul]; exact pow_dvd_pow (p : ℤ) hle
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpow_dvd _) _) _
  rw [← h01] at hrhs_dvd
  exact Int.natCast_dvd_natCast.mp (by simpa using hrhs_dvd)

private lemma fibEntry_prime_pow_dvd (p : ℕ) (hp : p.Prime) (e : ℕ) (he : 1 ≤ e) :
    fibEntry (p ^ e) ∣ p ^ (e - 1) * fibEntry p := by
  induction e with
  | zero => omega
  | succ e ih =>
    cases e with
    | zero => simp
    | succ e' =>
      have hprev : p ^ (e' + 1) ∣ Nat.fib (p ^ e' * fibEntry p) :=
        (dvd_fib_iff_fibEntry_dvd (p ^ (e' + 1)) (pow_pos hp.pos _) _).mpr (ih (by omega))
      have hpos : 1 ≤ p ^ e' * fibEntry p :=
        Nat.mul_pos (pow_pos hp.pos _) (fibEntry_spec p hp.pos).1
      have hnext := fib_mul_prime_dvd p (e' + 1) (p ^ e' * fibEntry p) hp (by omega) hpos hprev
      have hmul : p * (p ^ e' * fibEntry p) = p ^ (e' + 1) * fibEntry p := by rw [pow_succ']; ring
      rw [hmul] at hnext
      exact (dvd_fib_iff_fibEntry_dvd (p ^ (e' + 2)) (pow_pos hp.pos _) _).mp hnext

/-- For any odd prime power `p^e`:
- If `z = fibEntry (p^e) = 2 * r` is even, then `F(z + 1) ≡ -(-1)^r (mod p^e)`.
- Hence `fibZeros (p^e) = 1 ↔ fibEntry (p^e) % 4 = 2`. -/
private lemma odd_prime_pow_fib_succ_mod (p e : ℕ) (hp : p.Prime) (hp_odd : Odd p) (_he : 1 ≤ e)
    (r : ℕ) (hz : fibEntry (p ^ e) = 2 * r) :
    ((Nat.fib (fibEntry (p ^ e) + 1) : ℤ) + (-1 : ℤ) ^ r) % ((p ^ e : ℕ) : ℤ) = 0 := by
  have hpe_pos : 1 ≤ p ^ e := pow_pos hp.pos _
  have hspec := fibEntry_spec (p ^ e) hpe_pos
  have hpe_dvd_F2r : ((p ^ e : ℕ) : ℤ) ∣ (Nat.fib r : ℤ) * lucas r := by
    rw [← fib_two_mul_eq r, ← hz]
    exact Int.natCast_dvd_natCast.mpr hspec.2
  have hnot_p_Fr : ¬ p ∣ Nat.fib r := by
    intro hpFr
    have hnot_p_L : ¬ (p : ℤ) ∣ lucas r := by
      intro hpL
      have hpFrZ : (p : ℤ) ∣ (Nat.fib r : ℤ) := Int.natCast_dvd_natCast.mpr hpFr
      have hp2F : (p : ℤ) ∣ 2 * (Nat.fib (r + 1) : ℤ) := by
        have : 2 * (Nat.fib (r + 1) : ℤ) = lucas r + (Nat.fib r : ℤ) := by unfold lucas; ring
        rw [this]; exact dvd_add hpL hpFrZ
      have hp2F' : p ∣ 2 * Nat.fib (r + 1) := Int.natCast_dvd_natCast.mp (by simpa using hp2F)
      have hcop2 : Nat.Coprime p 2 := by
        rw [Nat.coprime_two_right]; exact hp_odd
      have hpF1 : p ∣ Nat.fib (r + 1) := hcop2.dvd_of_dvd_mul_left hp2F'
      have hcopF : Nat.Coprime (Nat.fib r) (Nat.fib (r + 1)) := fib_coprime_succ r
      have hp1 : p ∣ 1 := hcopF ▸ Nat.dvd_gcd hpFr hpF1
      exact hp.not_dvd_one hp1
    have hcopL : IsCoprime ((p ^ e : ℕ) : ℤ) (lucas r) := by
      have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      have hcop1 : IsCoprime (p : ℤ) (lucas r) := hpZ.coprime_iff_not_dvd.mpr hnot_p_L
      simpa using hcop1.pow_left (m := e)
    have hpe_dvd_Fr : ((p ^ e : ℕ) : ℤ) ∣ (Nat.fib r : ℤ) :=
      hcopL.dvd_of_dvd_mul_right hpe_dvd_F2r
    have hpe_dvd_Fr' : p ^ e ∣ Nat.fib r := Int.natCast_dvd_natCast.mp hpe_dvd_Fr
    have hr_pos : 0 < r := by have := hspec.1; omega
    have hle : fibEntry (p ^ e) ≤ r := Nat.sInf_le ⟨hr_pos, hpe_dvd_Fr'⟩
    omega
  have hcopFr : IsCoprime ((p ^ e : ℕ) : ℤ) (Nat.fib r : ℤ) := by
    have hcop1 : Nat.Coprime p (Nat.fib r) := hp.coprime_iff_not_dvd.mpr hnot_p_Fr
    have hcope : Nat.Coprime (p ^ e) (Nat.fib r) := hcop1.pow_left e
    exact_mod_cast hcope.isCoprime
  have hpe_dvd_L : ((p ^ e : ℕ) : ℤ) ∣ lucas r :=
    hcopFr.dvd_of_dvd_mul_left hpe_dvd_F2r
  rw [hz, fib_two_mul_add_one_eq r]
  have heq : (Nat.fib (r + 1) : ℤ) * lucas r - (-1 : ℤ) ^ r + (-1 : ℤ) ^ r =
      (Nat.fib (r + 1) : ℤ) * lucas r := by ring
  rw [heq]
  exact Int.emod_eq_zero_of_dvd (dvd_mul_of_dvd_right hpe_dvd_L _)

private lemma odd_prime_pow_fibZeros_one_iff (p e : ℕ) (hp : p.Prime) (hp_odd : Odd p) (he : 1 ≤ e) :
    fibZeros (p ^ e) = 1 ↔ fibEntry (p ^ e) % 4 = 2 := by
  have hpe_pos : 1 ≤ p ^ e := pow_pos hp.pos _
  have hpe3 : 3 ≤ p ^ e := by
    have hp3 : 3 ≤ p := by rcases hp_odd with ⟨t, ht⟩; have := hp.two_le; omega
    calc 3 ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he
  rw [fibZeros_eq_one_iff (p ^ e) hpe_pos]
  constructor
  · intro h1
    have h1z : (Nat.fib (fibEntry (p ^ e) + 1) : ℤ) % ((p ^ e : ℕ) : ℤ) = 1 % ((p ^ e : ℕ) : ℤ) := by
      exact_mod_cast h1
    have heven_z : Even (fibEntry (p ^ e)) := by
      by_contra hnot
      have hodd : Odd (fibEntry (p ^ e)) := Nat.not_even_iff_odd.mp hnot
      have hc := cassini (fibEntry (p ^ e))
      rw [hodd.neg_one_pow] at hc
      have hzm : ((p ^ e : ℕ) : ℤ) ∣ (Nat.fib (fibEntry (p ^ e)) : ℤ) :=
        Int.natCast_dvd_natCast.mpr (fibEntry_spec (p ^ e) hpe_pos).2
      have hsq : ((Nat.fib (fibEntry (p ^ e) + 1) : ℤ) ^ 2 + 1) % ((p ^ e : ℕ) : ℤ) = 0 := by
        have heq : (Nat.fib (fibEntry (p ^ e) + 1) : ℤ) ^ 2 + 1 =
            (Nat.fib (fibEntry (p ^ e)) : ℤ) * (Nat.fib (fibEntry (p ^ e) + 2) : ℤ) := by linarith
        rw [heq]; exact Int.emod_eq_zero_of_dvd (dvd_mul_of_dvd_left hzm _)
      have h2m : (2 : ℤ) % ((p ^ e : ℕ) : ℤ) = 0 := by
        have : ((Nat.fib (fibEntry (p ^ e) + 1) : ℤ) ^ 2 + 1) % ((p ^ e : ℕ) : ℤ) =
            (1 ^ 2 + 1) % ((p ^ e : ℕ) : ℤ) := by
          rw [Int.add_emod, int_pow_emod, h1z, ← int_pow_emod, ← Int.add_emod]
        rw [hsq] at this; norm_num at this; exact this.symm
      have : ((p ^ e : ℕ) : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) (Int.dvd_of_emod_eq_zero h2m)
      omega
    rcases heven_z with ⟨r, hr⟩
    have hz2r : fibEntry (p ^ e) = 2 * r := by omega
    have hmod := odd_prime_pow_fib_succ_mod p e hp hp_odd he r hz2r
    have hodd_r : Odd r := by
      by_contra hnot
      have hev_r : Even r := Nat.not_odd_iff_even.mp hnot
      rw [hev_r.neg_one_pow] at hmod
      have h2m : (2 : ℤ) % ((p ^ e : ℕ) : ℤ) = 0 := by
        have : ((Nat.fib (fibEntry (p ^ e) + 1) : ℤ) + 1) % ((p ^ e : ℕ) : ℤ) =
            (1 + 1) % ((p ^ e : ℕ) : ℤ) := by
          rw [Int.add_emod, h1z, ← Int.add_emod]
        rw [hmod] at this; norm_num at this; exact this.symm
      have : ((p ^ e : ℕ) : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) (Int.dvd_of_emod_eq_zero h2m)
      omega
    rcases hodd_r with ⟨t, rfl⟩
    omega
  · intro hmod4
    have hz2r : fibEntry (p ^ e) = 2 * (fibEntry (p ^ e) / 2) := by omega
    have hodd_r : Odd (fibEntry (p ^ e) / 2) := by
      rw [Nat.odd_iff]; omega
    have hmod := odd_prime_pow_fib_succ_mod p e hp hp_odd he (fibEntry (p ^ e) / 2) hz2r
    rw [hodd_r.neg_one_pow] at hmod
    have hsub : ((Nat.fib (fibEntry (p ^ e) + 1) : ℤ) - 1) % ((p ^ e : ℕ) : ℤ) = 0 := by
      simpa [sub_eq_add_neg] using hmod
    have hz1 : ((Nat.fib (fibEntry (p ^ e) + 1) : ℕ) : ℤ) % ((p ^ e : ℕ) : ℤ) =
        (1 : ℤ) % ((p ^ e : ℕ) : ℤ) :=
      Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr hsub
    exact_mod_cast hz1

/-- Small powers of 2 entry points and zero counts. -/
private lemma fibEntry_two : fibEntry 2 = 3 := by
  have hz := fibEntry_spec 2 (by omega)
  have hle : fibEntry 2 ≤ 3 := Nat.sInf_le ⟨by omega, by decide⟩
  have h1 : fibEntry 2 ≠ 1 := fun h => by rw [h] at hz; norm_num at hz
  have h2 : fibEntry 2 ≠ 2 := fun h => by rw [h] at hz; norm_num at hz
  omega

private lemma fibEntry_four : fibEntry 4 = 6 := by
  have hz := fibEntry_spec 4 (by omega)
  have hle : fibEntry 4 ≤ 6 := Nat.sInf_le ⟨by omega, by decide⟩
  have h1 : fibEntry 4 ≠ 1 := fun h => by rw [h] at hz; norm_num at hz
  have h2 : fibEntry 4 ≠ 2 := fun h => by rw [h] at hz; norm_num at hz
  have h3 : fibEntry 4 ≠ 3 := fun h => by rw [h] at hz; norm_num at hz
  have h4 : fibEntry 4 ≠ 4 := fun h => by rw [h] at hz; norm_num at hz
  have h5 : fibEntry 4 ≠ 5 := fun h => by rw [h] at hz; norm_num at hz
  omega

private lemma fibEntry_eight : fibEntry 8 = 6 := by
  have hz := fibEntry_spec 8 (by omega)
  have hle : fibEntry 8 ≤ 6 := Nat.sInf_le ⟨by omega, by decide⟩
  have h1 : fibEntry 8 ≠ 1 := fun h => by rw [h] at hz; norm_num at hz
  have h2 : fibEntry 8 ≠ 2 := fun h => by rw [h] at hz; norm_num at hz
  have h3 : fibEntry 8 ≠ 3 := fun h => by rw [h] at hz; norm_num at hz
  have h4 : fibEntry 8 ≠ 4 := fun h => by rw [h] at hz; norm_num at hz
  have h5 : fibEntry 8 ≠ 5 := fun h => by rw [h] at hz; norm_num at hz
  omega

private lemma lucas_even_mod_four (s : ℕ) : lucas (2 * s) % 4 ≠ 0 := by
  have hper : ∀ n : ℕ, lucas (n + 6) % 4 = lucas n % 4 := by
    intro n
    have hstep : ∀ k : ℕ, lucas (k + 2) = lucas k + lucas (k + 1) := by
      intro k
      unfold lucas
      have h1 : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
        exact_mod_cast Nat.fib_add_two (n := k + 1)
      have h2 : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
        exact_mod_cast Nat.fib_add_two (n := k)
      linarith
    have h6 : lucas (n + 6) = 5 * lucas n + 8 * lucas (n + 1) := by
      have s0 := hstep n
      have s1 := hstep (n + 1)
      have s2 := hstep (n + 2)
      have s3 := hstep (n + 3)
      have s4 := hstep (n + 4)
      linarith
    rw [h6]
    omega
  have hmod3 : ∀ s : ℕ, lucas (2 * s) % 4 = lucas (2 * (s % 3)) % 4 := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      by_cases hs : s < 3
      · rw [Nat.mod_eq_of_lt hs]
      · have hsub : 2 * s = 2 * (s - 3) + 6 := by omega
        rw [hsub, hper, ih (s - 3) (by omega)]
        have hrem : (s - 3) % 3 = s % 3 := by omega
        rw [hrem]
  rw [hmod3 s]
  have hlt : s % 3 < 3 := Nat.mod_lt s (by omega)
  interval_cases (s % 3) <;> decide

/-- For `e ≥ 3` and `2^e` with `z = fibEntry (2^e)`: `F(z + 1) ≡ 1 + 2^(e - 1) (mod 2^e)`. -/
private lemma two_pow_fib_succ_mod (e : ℕ) (he : 3 ≤ e) :
    ((Nat.fib (fibEntry (2 ^ e) + 1) : ℤ) - (1 + (2 : ℤ) ^ (e - 1))) % ((2 ^ e : ℕ) : ℤ) = 0 := by
  by_cases he3 : e = 3
  · subst he3
    show ((Nat.fib (fibEntry 8 + 1) : ℤ) - (1 + (2 : ℤ) ^ 2)) % 8 = 0
    rw [fibEntry_eight]
    decide
  · have he4 : 4 ≤ e := by omega
    have h2e_pos : 1 ≤ 2 ^ e := pow_pos (by omega : 0 < 2) e
    have hspec := fibEntry_spec (2 ^ e) h2e_pos
    -- Since `16 ∣ 2^e`, `fibEntry 16 = 12 ∣ fibEntry (2^e)`, so `4 ∣ fibEntry (2^e)`!
    have h16_dvd : 16 ∣ 2 ^ e := by
      have : 2 ^ 4 ∣ 2 ^ e := pow_dvd_pow 2 he4
      simpa using this
    have hz16 : fibEntry 16 = 12 := by
      have h16 := fibEntry_spec 16 (by omega)
      have hle : fibEntry 16 ≤ 12 := Nat.sInf_le ⟨by omega, by decide⟩
      have hlt : ∀ k : ℕ, 1 ≤ k → k < 12 → ¬ 16 ∣ Nat.fib k := by
        intro k hk1 hk12; interval_cases k <;> decide
      by_contra hne
      exact hlt (fibEntry 16) h16.1 (by omega) h16.2
    have h4_dvd_z : 4 ∣ fibEntry (2 ^ e) := by
      have h1 := fibEntry_dvd_of_dvd (by omega : 1 ≤ 16) h2e_pos h16_dvd
      rw [hz16] at h1
      exact dvd_trans (by decide : 4 ∣ 12) h1
    rcases h4_dvd_z with ⟨s, hs⟩
    let r : ℕ := 2 * s
    have hz2r : fibEntry (2 ^ e) = 2 * r := by dsimp [r]; omega
    have hr_pos : 0 < r := by have := hspec.1; omega
    -- `2^e ∣ F(2r) = F(r) * lucas(r)`, and `4 ∤ lucas(2s)`, so `2^(e-1) ∣ F(r)` and `2 ∣ lucas(r)`!
    have h2e_dvd : ((2 : ℤ) ^ e) ∣ (Nat.fib r : ℤ) * lucas r := by
      rw [← fib_two_mul_eq r, ← hz2r]
      exact_mod_cast hspec.2
    have hnot_4_L : ¬ (4 : ℤ) ∣ lucas r := by
      intro h4L
      exact lucas_even_mod_four s (Int.emod_eq_zero_of_dvd h4L)
    have hnot_2e_Fr : ¬ 2 ^ e ∣ Nat.fib r := by
      intro hd
      have hle : fibEntry (2 ^ e) ≤ r := Nat.sInf_le ⟨hr_pos, hd⟩
      omega
    -- Write `lucas r` as `2 * B` with `B` odd, and `F r` as `2^(e - 1) * A` with `A` odd!
    have h2_dvd_L : (2 : ℤ) ∣ lucas r := by
      by_contra hnot2L
      have hcopL : IsCoprime ((2 : ℤ) ^ e) (lucas r) := by
        have h2p : Prime (2 : ℤ) := Nat.prime_iff_prime_int.mp Nat.prime_two
        exact (h2p.coprime_iff_not_dvd.mpr hnot2L).pow_left
      have h2e_Fr : ((2 : ℤ) ^ e) ∣ (Nat.fib r : ℤ) := hcopL.dvd_of_dvd_mul_right h2e_dvd
      exact hnot_2e_Fr (by exact_mod_cast h2e_Fr)
    rcases h2_dvd_L with ⟨B, hB⟩
    have hB_odd : B % 2 = 1 := by
      by_contra h
      have h2B : (2 : ℤ) ∣ B := Int.dvd_of_emod_eq_zero (by omega)
      rcases h2B with ⟨t, rfl⟩
      exact hnot_4_L ⟨t, by linarith⟩
    have h2em1_dvd_Fr : ((2 : ℤ) ^ (e - 1)) ∣ (Nat.fib r : ℤ) := by
      have hpow : (2 : ℤ) ^ e = 2 * (2 : ℤ) ^ (e - 1) := by
        rw [← pow_succ', show e - 1 + 1 = e by omega]
      rw [hpow, hB] at h2e_dvd
      have hmul : ((2 : ℤ) ^ (e - 1)) ∣ (Nat.fib r : ℤ) * B := by
        rcases h2e_dvd with ⟨q, hq⟩
        exact ⟨q, by linarith⟩
      have hcopB : IsCoprime ((2 : ℤ) ^ (e - 1)) B := by
        have h2p : Prime (2 : ℤ) := Nat.prime_iff_prime_int.mp Nat.prime_two
        have hnot2B : ¬ (2 : ℤ) ∣ B := fun ⟨t, ht⟩ => by omega
        exact (h2p.coprime_iff_not_dvd.mpr hnot2B).pow_left
      exact hcopB.dvd_of_dvd_mul_right hmul
    rcases h2em1_dvd_Fr with ⟨A, hA⟩
    have hA_odd : A % 2 = 1 := by
      by_contra h
      have h2A : (2 : ℤ) ∣ A := Int.dvd_of_emod_eq_zero (by omega)
      rcases h2A with ⟨t, rfl⟩
      have h2e_Fr : ((2 : ℤ) ^ e) ∣ (Nat.fib r : ℤ) := by
        refine ⟨t, ?_⟩
        rw [hA, show (2 : ℤ) ^ e = (2 : ℤ) ^ (e - 1) * 2 by
          rw [← pow_succ, show e - 1 + 1 = e by omega]]
        ring
      exact hnot_2e_Fr (by exact_mod_cast h2e_Fr)
    -- Now use `4 * F(2r + 1) = 4 * (-1)^r + 2 * lucas r * F r + 10 * (F r)^2`!
    have h4F := four_mul_fib_two_mul_add_one r
    have hneg1 : (-1 : ℤ) ^ r = 1 := Even.neg_one_pow ⟨s, by dsimp [r]; omega⟩
    rw [hneg1, hB, hA] at h4F
    -- Divide by `4`:
    -- `F(2r+1) = 1 + 2^(e-1) * A * B + 5 * 2^(2e - 3) * A^2`!
    have hpow2 : (2 : ℤ) ^ (e - 1) * (2 : ℤ) ^ (e - 1) = 2 * (2 : ℤ) ^ (2 * e - 3) := by
      rw [← pow_add, ← pow_succ', show (2 * e - 3) + 1 = (e - 1) + (e - 1) by omega]
    have hF_exact : (Nat.fib (2 * r + 1) : ℤ) =
        1 + (2 : ℤ) ^ (e - 1) * (A * B) + 5 * (2 : ℤ) ^ (2 * e - 3) * A ^ 2 := by
      have h4eq : 4 * (Nat.fib (2 * r + 1) : ℤ) =
          4 * (1 + (2 : ℤ) ^ (e - 1) * (A * B) + 5 * (2 : ℤ) ^ (2 * e - 3) * A ^ 2) := by
        rw [h4F, mul_pow, sq ((2 : ℤ) ^ (e - 1)), hpow2]; ring
      linarith
    rw [hz2r, hF_exact]
    have hAB_odd : (A * B - 1) % 2 = 0 := by
      rw [Int.sub_emod, Int.mul_emod, hA_odd, hB_odd]; norm_num
    obtain ⟨u, hu⟩ := Int.dvd_of_emod_eq_zero hAB_odd
    have hle_exp : e ≤ 2 * e - 3 := by omega
    have h2e_dvd_tail : ((2 : ℤ) ^ e) ∣ (2 : ℤ) ^ (2 * e - 3) := pow_dvd_pow 2 hle_exp
    have hdiff : 1 + (2 : ℤ) ^ (e - 1) * (A * B) + 5 * (2 : ℤ) ^ (2 * e - 3) * A ^ 2 -
        (1 + (2 : ℤ) ^ (e - 1)) =
        (2 : ℤ) ^ e * u + 5 * (2 : ℤ) ^ (2 * e - 3) * A ^ 2 := by
      have hpow_e : (2 : ℤ) ^ e = (2 : ℤ) ^ (e - 1) * 2 := by
        rw [← pow_succ, show e - 1 + 1 = e by omega]
      rw [hpow_e]
      linear_combination (2 : ℤ) ^ (e - 1) * hu
    rw [hdiff]
    have hdvd_tot : ((2 ^ e : ℕ) : ℤ) ∣
        (2 : ℤ) ^ e * u + 5 * (2 : ℤ) ^ (2 * e - 3) * A ^ 2 := by
      push_cast
      refine dvd_add (dvd_mul_right _ _) ?_
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h2e_dvd_tail _) _
    exact Int.emod_eq_zero_of_dvd hdvd_tot

/-- Raising `1 + 2^(e - 1)` to any odd power stays `≡ 1 + 2^(e - 1) (mod 2^e)` for `e ≥ 3`. -/
private lemma one_add_half_pow_odd (e u : ℕ) (he : 3 ≤ e) (hu : Odd u) :
    ((1 + (2 : ℤ) ^ (e - 1)) ^ u - (1 + (2 : ℤ) ^ (e - 1))) % ((2 ^ e : ℕ) : ℤ) = 0 := by
  have hsq : ((1 + (2 : ℤ) ^ (e - 1)) ^ 2 - 1) % ((2 ^ e : ℕ) : ℤ) = 0 := by
    have heq : (1 + (2 : ℤ) ^ (e - 1)) ^ 2 - 1 =
        (2 : ℤ) ^ e + (2 : ℤ) ^ (2 * e - 2) := by
      have h1 : 2 * (2 : ℤ) ^ (e - 1) = (2 : ℤ) ^ e := by
        rw [← pow_succ', show e - 1 + 1 = e by omega]
      have h2 : ((2 : ℤ) ^ (e - 1)) ^ 2 = (2 : ℤ) ^ (2 * e - 2) := by
        rw [← pow_mul, show (e - 1) * 2 = 2 * e - 2 by omega]
      linarith [h1, h2]
    rw [heq]
    have hd : ((2 ^ e : ℕ) : ℤ) ∣ (2 : ℤ) ^ e + (2 : ℤ) ^ (2 * e - 2) := by
      push_cast
      exact dvd_add (dvd_refl _) (pow_dvd_pow 2 (by omega))
    exact Int.emod_eq_zero_of_dvd hd
  rcases hu with ⟨t, rfl⟩
  have hmod_sq : ((1 + (2 : ℤ) ^ (e - 1)) ^ 2) % ((2 ^ e : ℕ) : ℤ) = 1 % ((2 ^ e : ℕ) : ℤ) :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr hsq
  have hmod_even : ((1 + (2 : ℤ) ^ (e - 1)) ^ (2 * t)) % ((2 ^ e : ℕ) : ℤ) = 1 % ((2 ^ e : ℕ) : ℤ) := by
    rw [pow_mul, int_pow_emod, hmod_sq, ← int_pow_emod, one_pow]
  have hmod_odd : ((1 + (2 : ℤ) ^ (e - 1)) ^ (2 * t + 1)) % ((2 ^ e : ℕ) : ℤ) =
      (1 + (2 : ℤ) ^ (e - 1)) % ((2 ^ e : ℕ) : ℤ) := by
    rw [pow_succ, Int.mul_emod, hmod_even, ← Int.mul_emod, one_mul]
  exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hmod_odd

/-- Helper: if `fibZeros m = 1`, then `¬ 4 ∣ fibEntry m`. -/
private lemma not_four_dvd_fibEntry_of_fibZeros_one (m : ℕ) (hm : 1 ≤ m) (h1 : fibZeros m = 1) :
    ¬ 4 ∣ fibEntry m := by
  intro h4z
  have hF1 : Nat.fib (fibEntry m + 1) % m = 1 % m := (fibZeros_eq_one_iff m hm).mp h1
  -- Find a prime power `p^e ∥ m` with `v_2(fibEntry (p^e)) = v_2(fibEntry m)`!
  let v := (fibEntry m).factorization 2
  have hv2 : 2 ≤ v := by
    have hzpos : fibEntry m ≠ 0 := (fibEntry_spec m hm).1.ne'
    have h22 : 2 ^ 2 ∣ fibEntry m := by simpa using h4z
    exact (Nat.prime_two.pow_dvd_iff_le_factorization hzpos).mp h22
  have hex : ∃ p : ℕ, p.Prime ∧ p ∣ m ∧
      v ≤ (fibEntry (p ^ (m.factorization p))).factorization 2 := by
    by_contra hall
    push Not at hall
    -- If every prime power `p^e ∥ m` had `v_2(fibEntry (p^e)) < v`, then `fibEntry m` would not be divisible by `2^v`!
    have hnot_pow : ∀ n : ℕ, 1 ≤ n →
        (∀ p : ℕ, p.Prime → p ∣ n → (fibEntry (p ^ (n.factorization p))).factorization 2 < v) →
        ¬ 2 ^ v ∣ fibEntry n := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro hn hlt
        by_cases hn1 : n = 1
        · subst hn1
          have h1e : fibEntry 1 = 1 := by
            have := fibEntry_spec 1 le_rfl
            have : fibEntry 1 ≤ 1 := Nat.sInf_le ⟨by omega, by simp⟩
            omega
          rw [h1e]
          have : 1 < 2 ^ v := one_lt_pow₀ (by norm_num) (by omega)
          intro hd; have := Nat.le_of_dvd (by omega) hd; omega
        · let p := n.minFac
          have hp : p.Prime := Nat.minFac_prime hn1
          have hpn : p ∣ n := Nat.minFac_dvd n
          let e := n.factorization p
          have he : 1 ≤ e := (hp.dvd_iff_one_le_factorization (by omega)).mp hpn
          rcases Nat.ordProj_dvd n p with ⟨r, hr⟩
          have hr_pos : 1 ≤ r := by rcases eq_or_ne r 0 with rfl | hne <;> omega
          have hcop : Nat.Coprime (p ^ e) r := by
            refine Nat.Coprime.pow_left e (hp.coprime_iff_not_dvd.mpr fun hpr => ?_)
            have hpe1 : p ^ (e + 1) ∣ n := by
              rcases hpr with ⟨t, rfl⟩; exact ⟨t, by rw [hr, pow_succ]; ring⟩
            have := (hp.pow_dvd_iff_le_factorization (by omega)).mp hpe1
            omega
          have hr_lt : r < n := by
            have : 1 < p ^ e := one_lt_pow₀ hp.one_lt (by omega)
            nlinarith
          have hnot_pe : ¬ 2 ^ v ∣ fibEntry (p ^ e) := by
            intro hd
            have hle := (Nat.prime_two.pow_dvd_iff_le_factorization
              (fibEntry_spec (p ^ e) (pow_pos hp.pos _)).1.ne').mp hd
            have hltp := hlt p hp hpn
            dsimp only [e] at hle
            omega
          have hnot_r : ¬ 2 ^ v ∣ fibEntry r := by
            refine ih r hr_lt hr_pos (fun q hq hqr => ?_)
            have hqne : q ≠ p := by
              rintro rfl
              have hcop1 := (Nat.coprime_pow_left_iff (by omega) p r).mp hcop
              exact hp.not_dvd_one (hcop1 ▸ Nat.dvd_gcd (dvd_refl p) hqr)
            have hqn : q ∣ n := dvd_trans hqr ⟨p ^ e, by rw [hr, mul_comm]⟩
            have hfac_eq : r.factorization q = n.factorization q := by
              rw [hr, Nat.factorization_mul (pow_pos hp.pos _).ne' (by omega),
                Finsupp.add_apply, hp.factorization_pow, Finsupp.single_eq_of_ne hqne,
                zero_add]
            rw [hfac_eq]
            exact hlt q hq hqn
          rw [hr, fibEntry_mul_coprime (pow_pos hp.pos _) hr_pos hcop]
          intro hd
          have hne_pe : fibEntry (p ^ e) ≠ 0 := (fibEntry_spec (p ^ e) (pow_pos hp.pos _)).1.ne'
          have hne_r : fibEntry r ≠ 0 := (fibEntry_spec r hr_pos).1.ne'
          have hne_lcm : Nat.lcm (fibEntry (p ^ e)) (fibEntry r) ≠ 0 := Nat.lcm_ne_zero hne_pe hne_r
          have hv_le_lcm := (Nat.prime_two.pow_dvd_iff_le_factorization hne_lcm).mp hd
          rw [Nat.factorization_lcm hne_pe hne_r, Finsupp.sup_apply, le_sup_iff] at hv_le_lcm
          rcases hv_le_lcm with h | h
          · exact hnot_pe ((Nat.prime_two.pow_dvd_iff_le_factorization hne_pe).mpr h)
          · exact hnot_r ((Nat.prime_two.pow_dvd_iff_le_factorization hne_r).mpr h)
    have h2v_dvd : 2 ^ v ∣ fibEntry m := Nat.ordProj_dvd (fibEntry m) 2
    exact hnot_pow m hm hall h2v_dvd
  obtain ⟨p, hp, hpm, hv_le⟩ := hex
  let e := m.factorization p
  have he_pos : 1 ≤ e := (hp.dvd_iff_one_le_factorization (by omega)).mp hpm
  have hpe_dvd_m : p ^ e ∣ m := Nat.ordProj_dvd m p
  have hpe_pos : 1 ≤ p ^ e := pow_pos hp.pos _
  have hzpe_dvd_zm : fibEntry (p ^ e) ∣ fibEntry m := fibEntry_dvd_of_dvd hpe_pos hm hpe_dvd_m
  rcases hzpe_dvd_zm with ⟨u, hu⟩
  have hu_odd : Odd u := by
    have hz_ne : fibEntry m ≠ 0 := (fibEntry_spec m hm).1.ne'
    have hzpe_ne : fibEntry (p ^ e) ≠ 0 := (fibEntry_spec (p ^ e) hpe_pos).1.ne'
    have hu_ne : u ≠ 0 := by rintro rfl; simp at hu; exact hz_ne hu
    have hfac := congr_arg (fun x => x.factorization 2) hu
    rw [Nat.factorization_mul hzpe_ne hu_ne, Finsupp.add_apply] at hfac
    have hu2 : u.factorization 2 = 0 := by dsimp only [e] at hfac; omega
    rw [Nat.odd_iff]
    by_contra h
    have h2u : 2 ∣ u := by omega
    have := (Nat.prime_two.dvd_iff_one_le_factorization hu_ne).mp h2u
    omega
  have hF1_pe : Nat.fib (fibEntry m + 1) % (p ^ e) = 1 % (p ^ e) := by
    have h1 := congr_arg (· % (p ^ e)) hF1
    rw [Nat.mod_mod_of_dvd _ hpe_dvd_m, Nat.mod_mod_of_dvd _ hpe_dvd_m] at h1
    exact h1
  have hpow_pe : Nat.fib (fibEntry (p ^ e) + 1) ^ u % (p ^ e) = 1 % (p ^ e) := by
    have hmul := fib_mul_succ_mod (p ^ e) (fibEntry (p ^ e)) (fibEntry_spec (p ^ e) hpe_pos).2 u
    rw [mul_comm, ← hu] at hmul
    rw [← hmul, hF1_pe]
  by_cases hp2 : p = 2
  · subst hp2
    have he3 : 3 ≤ e := by
      by_contra hlt
      have he12 : e = 1 ∨ e = 2 := by omega
      rcases he12 with he1 | he2
      · have hv1 : v ≤ (fibEntry (2 ^ 1)).factorization 2 := by
          have : m.factorization 2 = 1 := he1
          simpa only [this] using hv_le
        simp only [pow_one, fibEntry_two] at hv1
        have : (3 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
        omega
      · have hv2' : v ≤ (fibEntry (2 ^ 2)).factorization 2 := by
          have : m.factorization 2 = 2 := he2
          simpa only [this] using hv_le
        norm_num [fibEntry_four] at hv2'
        have : (6 : ℕ).factorization 2 = 1 := by
          rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.factorization_mul (by omega) (by omega),
            Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two,
            Nat.factorization_eq_zero_of_not_dvd (by decide)]
        omega
    have hbase := two_pow_fib_succ_mod e he3
    have hbase_eq : (Nat.fib (fibEntry (2 ^ e) + 1) : ℤ) % ((2 ^ e : ℕ) : ℤ) =
        (1 + (2 : ℤ) ^ (e - 1)) % ((2 ^ e : ℕ) : ℤ) :=
      Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr hbase
    have hpow_z : ((Nat.fib (fibEntry (2 ^ e) + 1) : ℤ) ^ u) % ((2 ^ e : ℕ) : ℤ) =
        1 % ((2 ^ e : ℕ) : ℤ) := by exact_mod_cast hpow_pe
    rw [int_pow_emod, hbase_eq, ← int_pow_emod] at hpow_z
    have hodd_mod := one_add_half_pow_odd e u he3 hu_odd
    have hodd_eq := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr hodd_mod
    rw [hpow_z] at hodd_eq
    have hsub : ((2 : ℤ) ^ (e - 1)) % ((2 ^ e : ℕ) : ℤ) = 0 := by
      have := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hodd_eq.symm
      simpa using this
    have hdvd : ((2 ^ e : ℕ) : ℤ) ∣ (2 : ℤ) ^ (e - 1) := Int.dvd_of_emod_eq_zero hsub
    have hle : ((2 ^ e : ℕ) : ℤ) ≤ (2 : ℤ) ^ (e - 1) := Int.le_of_dvd (by positivity) hdvd
    have hlt : (2 : ℤ) ^ (e - 1) < (2 : ℤ) ^ e := by
      have : (2 : ℤ) ^ e = 2 * (2 : ℤ) ^ (e - 1) := by
        rw [← pow_succ', show e - 1 + 1 = e by omega]
      have : (0 : ℤ) < (2 : ℤ) ^ (e - 1) := by positivity
      linarith
    push_cast at hle
    linarith
  · have hp_odd : Odd p := hp.odd_of_ne_two hp2
    have h4_dvd_zpe : 4 ∣ fibEntry (p ^ e) := by
      have h22 : 2 ^ 2 ∣ fibEntry (p ^ e) :=
        dvd_trans (pow_dvd_pow 2 hv2) (dvd_trans (pow_dvd_pow 2 hv_le) (Nat.ordProj_dvd _ 2))
      simpa using h22
    rcases h4_dvd_zpe with ⟨s, hs⟩
    have hmod := odd_prime_pow_fib_succ_mod p e hp hp_odd he_pos (2 * s) (by omega)
    have hneg1 : (-1 : ℤ) ^ (2 * s) = 1 := Even.neg_one_pow ⟨s, by omega⟩
    rw [hneg1] at hmod
    have hbase_eq : (Nat.fib (fibEntry (p ^ e) + 1) : ℤ) % ((p ^ e : ℕ) : ℤ) =
        (-1 : ℤ) % ((p ^ e : ℕ) : ℤ) :=
      Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (by simpa [sub_neg_eq_add] using hmod)
    have hpow_z : ((Nat.fib (fibEntry (p ^ e) + 1) : ℤ) ^ u) % ((p ^ e : ℕ) : ℤ) =
        1 % ((p ^ e : ℕ) : ℤ) := by exact_mod_cast hpow_pe
    rw [int_pow_emod, hbase_eq, ← int_pow_emod, hu_odd.neg_one_pow] at hpow_z
    have h2m : (2 : ℤ) % ((p ^ e : ℕ) : ℤ) = 0 := by
      have := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hpow_z.symm
      simpa using this
    have hpe3 : 3 ≤ p ^ e := by
      have hp3 : 3 ≤ p := by rcases hp_odd with ⟨t, ht⟩; have := hp.two_le; omega
      calc 3 ≤ p := hp3
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he_pos
    have hle : ((p ^ e : ℕ) : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) (Int.dvd_of_emod_eq_zero h2m)
    omega

/-- Helper: if `fibZeros m = 1`, then `¬ 8 ∣ m`. -/
private lemma not_eight_dvd_of_fibZeros_one (m : ℕ) (hm : 1 ≤ m) (h1 : fibZeros m = 1) :
    ¬ 8 ∣ m := by
  intro h8m
  have hnot4 := not_four_dvd_fibEntry_of_fibZeros_one m hm h1
  have h6_dvd : 6 ∣ fibEntry m := by
    rw [← fibEntry_eight]
    exact fibEntry_dvd_of_dvd (by omega) hm h8m
  rcases h6_dvd with ⟨u, hu⟩
  have hu_odd : Odd u := by
    rw [Nat.odd_iff]
    by_contra h
    have : 2 ∣ u := by omega
    rcases this with ⟨t, rfl⟩
    exact hnot4 ⟨3 * t, by omega⟩
  have hF1 : Nat.fib (fibEntry m + 1) % m = 1 % m := (fibZeros_eq_one_iff m hm).mp h1
  have hF1_8 : Nat.fib (fibEntry m + 1) % 8 = 1 := by
    have := congr_arg (· % 8) hF1
    rw [Nat.mod_mod_of_dvd _ h8m, Nat.mod_mod_of_dvd _ h8m] at this
    simpa using this
  have hpow8 : Nat.fib 7 ^ u % 8 = 1 := by
    have hmul := fib_mul_succ_mod 8 6 (by decide : 8 ∣ Nat.fib 6) u
    rw [mul_comm, ← hu] at hmul
    rw [← hmul, hF1_8]
  have h5u : 5 ^ u % 8 = 5 := by
    rcases hu_odd with ⟨t, rfl⟩
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hF7 : Nat.fib 7 % 8 = 5 := by decide
  rw [Nat.pow_mod, hF7, h5u] at hpow8
  omega

/-- Helper: if `fibZeros m = 1` and `p` is an odd prime dividing `m`, then `fibZeros p = 1`. -/
private lemma prime_fibZeros_one_of_dvd (m p : ℕ) (hm : 1 ≤ m) (h1 : fibZeros m = 1)
    (hp : p.Prime) (hp_odd : Odd p) (hpm : p ∣ m) :
    fibZeros p = 1 := by
  have hnot4 := not_four_dvd_fibEntry_of_fibZeros_one m hm h1
  have hzp_dvd : fibEntry p ∣ fibEntry m := fibEntry_dvd_of_dvd hp.pos hm hpm
  have hF1 : Nat.fib (fibEntry m + 1) % m = 1 % m := (fibZeros_eq_one_iff m hm).mp h1
  have hF1_p : Nat.fib (fibEntry m + 1) % p = 1 % p := by
    have := congr_arg (· % p) hF1
    rw [Nat.mod_mod_of_dvd _ hpm, Nat.mod_mod_of_dvd _ hpm] at this
    exact this
  have hzp_mod4 : fibEntry p % 4 = 2 := by
    have hnot4p : ¬ 4 ∣ fibEntry p := fun h => hnot4 (dvd_trans h hzp_dvd)
    have heven_p : Even (fibEntry p) := by
      by_contra hnot
      have hodd_p : Odd (fibEntry p) := Nat.not_even_iff_odd.mp hnot
      rcases hzp_dvd with ⟨u, hu⟩
      have hpow_p : Nat.fib (fibEntry p + 1) ^ u % p = 1 % p := by
        have hmul := fib_mul_succ_mod p (fibEntry p) (fibEntry_spec p hp.pos).2 u
        rw [mul_comm, ← hu] at hmul
        rw [← hmul, hF1_p]
      have hc := cassini (fibEntry p)
      rw [hodd_p.neg_one_pow] at hc
      have hzp_dvd_F : (p : ℤ) ∣ (Nat.fib (fibEntry p) : ℤ) :=
        Int.natCast_dvd_natCast.mpr (fibEntry_spec p hp.pos).2
      have hsq : ((Nat.fib (fibEntry p + 1) : ℤ) ^ 2) % (p : ℤ) = (-1 : ℤ) % (p : ℤ) := by
        apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
        have heq : (Nat.fib (fibEntry p + 1) : ℤ) ^ 2 - (-1 : ℤ) =
            (Nat.fib (fibEntry p) : ℤ) * (Nat.fib (fibEntry p + 2) : ℤ) := by linarith
        rw [heq]; exact Int.emod_eq_zero_of_dvd (dvd_mul_of_dvd_left hzp_dvd_F _)
      have hp3 : 3 ≤ p := by rcases hp_odd with ⟨t, ht⟩; have := hp.two_le; omega
      have hpow_z : ((Nat.fib (fibEntry p + 1) : ℤ) ^ u) % (p : ℤ) = 1 % (p : ℤ) := by
        exact_mod_cast hpow_p
      -- Since `4 ∤ fibEntry m` and `fibEntry p` is odd, `4 ∤ u`, so `u % 4 ∈ {1, 2, 3}`!
      have hnot4u : ¬ 4 ∣ u := fun h => hnot4 (hu ▸ dvd_mul_of_dvd_right h _)
      have hpow2_eq : ∀ q : ℕ, ((Nat.fib (fibEntry p + 1) : ℤ) ^ (2 * q)) % (p : ℤ) =
          ((-1 : ℤ) ^ q) % (p : ℤ) := by
        intro q; rw [pow_mul, int_pow_emod, hsq, ← int_pow_emod]
      by_cases hu2 : 2 ∣ u
      · rcases hu2 with ⟨q, rfl⟩
        have hq_odd : Odd q := by
          rw [Nat.odd_iff]
          by_contra h
          exact hnot4u ⟨q / 2, by omega⟩
        rw [hpow2_eq q, hq_odd.neg_one_pow] at hpow_z
        have h2p : (2 : ℤ) % (p : ℤ) = 0 := by
          have := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hpow_z.symm
          simpa using this
        have := Int.le_of_dvd (by norm_num) (Int.dvd_of_emod_eq_zero h2p)
        omega
      · -- `u` is odd, so `a^u = 1` and `a^2 = -1`, hence `a^(2u) = (-1)^u = -1`, contradicting `(a^u)^2 = 1`!
        have hu_odd : Odd u := by rw [Nat.odd_iff]; omega
        have h1sq : ((Nat.fib (fibEntry p + 1) : ℤ) ^ (2 * u)) % (p : ℤ) = 1 % (p : ℤ) := by
          rw [mul_comm, pow_mul, int_pow_emod, hpow_z, ← int_pow_emod, one_pow]
        rw [hpow2_eq u, hu_odd.neg_one_pow] at h1sq
        have h2p : (2 : ℤ) % (p : ℤ) = 0 := by
          have := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h1sq.symm
          simpa using this
        have := Int.le_of_dvd (by norm_num) (Int.dvd_of_emod_eq_zero h2p)
        omega
    rcases heven_p with ⟨r, hr⟩
    omega
  have hres := (odd_prime_pow_fibZeros_one_iff p 1 hp hp_odd le_rfl).mpr
  simpa only [pow_one] using hres (by simpa only [pow_one] using hzp_mod4)

/-- Backward helper: if `fibZeros a = 1`, `fibZeros b = 1`, and `Coprime a b`, then `fibZeros (a * b) = 1`. -/
private lemma fibZeros_one_mul_coprime {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hcop : Nat.Coprime a b) (hza : fibZeros a = 1) (hzb : fibZeros b = 1) :
    fibZeros (a * b) = 1 := by
  have hab : 1 ≤ a * b := Nat.mul_pos ha hb
  rw [fibZeros_eq_one_iff (a * b) hab]
  have ha1 : Nat.fib (fibEntry a + 1) % a = 1 % a := (fibZeros_eq_one_iff a ha).mp hza
  have hb1 : Nat.fib (fibEntry b + 1) % b = 1 % b := (fibZeros_eq_one_iff b hb).mp hzb
  have hda : fibEntry a ∣ fibEntry (a * b) := fibEntry_dvd_of_dvd ha hab (dvd_mul_right a b)
  have hdb : fibEntry b ∣ fibEntry (a * b) := fibEntry_dvd_of_dvd hb hab (dvd_mul_left b a)
  rcases hda with ⟨ua, hua⟩
  rcases hdb with ⟨ub, hub⟩
  have hmoda : Nat.fib (fibEntry (a * b) + 1) % a = 1 % a := by
    have hm := fib_mul_succ_mod a (fibEntry a) (fibEntry_spec a ha).2 ua
    rw [mul_comm, ← hua] at hm
    rw [hm, Nat.pow_mod, ha1, ← Nat.pow_mod, one_pow]
  have hmodb : Nat.fib (fibEntry (a * b) + 1) % b = 1 % b := by
    have hm := fib_mul_succ_mod b (fibEntry b) (fibEntry_spec b hb).2 ub
    rw [mul_comm, ← hub] at hm
    rw [hm, Nat.pow_mod, hb1, ← Nat.pow_mod, one_pow]
  have hcong : Nat.fib (fibEntry (a * b) + 1) ≡ 1 [MOD a * b] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hmoda, hmodb⟩
  exact hcong

private lemma fibZeros_one_of_odd_primes (k : ℕ) (hk : 1 ≤ k) (hk_odd : Odd k)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ k → fibZeros p = 1) :
    fibZeros k = 1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk1 : k = 1
    · subst hk1
      rw [fibZeros_eq_one_iff 1 le_rfl]; simp [Nat.mod_one]
    · let p := k.minFac
      have hp : p.Prime := Nat.minFac_prime hk1
      have hpk : p ∣ k := Nat.minFac_dvd k
      have hp_odd : Odd p := hk_odd.of_dvd_nat hpk
      let e := k.factorization p
      have he : 1 ≤ e := (hp.dvd_iff_one_le_factorization (by omega)).mp hpk
      rcases Nat.ordProj_dvd k p with ⟨r, hr⟩
      have hr_pos : 1 ≤ r := by rcases eq_or_ne r 0 with rfl | hne <;> omega
      have hcop : Nat.Coprime (p ^ e) r := by
        refine Nat.Coprime.pow_left e (hp.coprime_iff_not_dvd.mpr fun hpr => ?_)
        have hpe1 : p ^ (e + 1) ∣ k := by
          rcases hpr with ⟨t, rfl⟩; exact ⟨t, by rw [hr, pow_succ]; ring⟩
        have := (hp.pow_dvd_iff_le_factorization (by omega)).mp hpe1
        omega
      have hr_lt : r < k := by
        have : 1 < p ^ e := one_lt_pow₀ hp.one_lt (by omega)
        nlinarith
      have hr_odd : Odd r := hk_odd.of_dvd_nat ⟨p ^ e, by rw [hr, mul_comm]⟩
      have hzr : fibZeros r = 1 := ih r hr_lt hr_pos hr_odd (fun q hq hqr =>
        hprimes q hq (dvd_trans hqr ⟨p ^ e, by rw [hr, mul_comm]⟩))
      have hzpe : fibZeros (p ^ e) = 1 := by
        rw [odd_prime_pow_fibZeros_one_iff p e hp hp_odd he]
        have hzp : fibEntry p % 4 = 2 := by
          have := (odd_prime_pow_fibZeros_one_iff p 1 hp hp_odd le_rfl).mp
          simpa only [pow_one] using this (by simpa only [pow_one] using hprimes p hp hpk)
        have h1 : fibEntry p ∣ fibEntry (p ^ e) :=
          fibEntry_dvd_of_dvd hp.pos (pow_pos hp.pos _) (dvd_pow_self p (by omega))
        have h2 : fibEntry (p ^ e) ∣ p ^ (e - 1) * fibEntry p :=
          fibEntry_prime_pow_dvd p hp e he
        have hnot4 : ¬ 4 ∣ fibEntry (p ^ e) := by
          intro h4
          have h4' : 4 ∣ p ^ (e - 1) * fibEntry p := dvd_trans h4 h2
          have hcop4 : Nat.Coprime 4 (p ^ (e - 1)) := by
            have hcop2 : Nat.Coprime 2 p := by rw [Nat.coprime_two_left]; exact hp_odd
            have : Nat.Coprime (2 ^ 2) (p ^ (e - 1)) := (hcop2.pow_left 2).pow_right (e - 1)
            simpa using this
          have h4p : 4 ∣ fibEntry p := hcop4.dvd_of_dvd_mul_left h4'
          omega
        have h2_dvd : 2 ∣ fibEntry (p ^ e) := dvd_trans (by omega : 2 ∣ fibEntry p) h1
        omega
      rw [hr]
      exact fibZeros_one_mul_coprime (pow_pos hp.pos _) hr_pos hcop hzpe hzr

private lemma fibZeros_two : fibZeros 2 = 1 := by
  rw [fibZeros_eq_one_iff 2 (by omega), fibEntry_two]
  decide

private lemma fibZeros_four : fibZeros 4 = 1 := by
  rw [fibZeros_eq_one_iff 4 (by omega), fibEntry_four]
  decide

lemma solve_a053031 :
    ∀ m : ℕ, 1 ≤ m →
      (fibZeros m = 1 ↔
        (Odd m ∧ ∀ p : ℕ, p.Prime → p ∣ m → fibZeros p = 1) ∨
        (∃ k : ℕ, (m = 2 * k ∨ m = 4 * k) ∧ Odd k ∧
          ∀ p : ℕ, p.Prime → p ∣ k → fibZeros p = 1)) := by
  intro m hm
  constructor
  · intro h1
    have hnot8 := not_eight_dvd_of_fibZeros_one m hm h1
    by_cases h4m : 4 ∣ m
    · rcases h4m with ⟨k, rfl⟩
      have hk_odd : Odd k := by
        rw [Nat.odd_iff]
        by_contra h
        exact hnot8 ⟨k / 2, by omega⟩
      refine Or.inr ⟨k, Or.inr rfl, hk_odd, fun p hp hpk => ?_⟩
      exact prime_fibZeros_one_of_dvd (4 * k) p hm h1 hp (hk_odd.of_dvd_nat hpk)
        (dvd_trans hpk (dvd_mul_left k 4))
    · by_cases h2m : 2 ∣ m
      · rcases h2m with ⟨k, rfl⟩
        have hk_odd : Odd k := by
          rw [Nat.odd_iff]
          by_contra h
          exact h4m ⟨k / 2, by omega⟩
        refine Or.inr ⟨k, Or.inl rfl, hk_odd, fun p hp hpk => ?_⟩
        exact prime_fibZeros_one_of_dvd (2 * k) p hm h1 hp (hk_odd.of_dvd_nat hpk)
          (dvd_trans hpk (dvd_mul_left k 2))
      · have hm_odd : Odd m := by rw [Nat.odd_iff]; omega
        refine Or.inl ⟨hm_odd, fun p hp hpm => ?_⟩
        exact prime_fibZeros_one_of_dvd m p hm h1 hp (hm_odd.of_dvd_nat hpm) hpm
  · rintro (⟨hm_odd, hall⟩ | ⟨k, (rfl | rfl), hk_odd, hall⟩)
    · exact fibZeros_one_of_odd_primes m hm hm_odd hall
    · have hk1 : fibZeros k = 1 := fibZeros_one_of_odd_primes k (by omega) hk_odd hall
      have hcop : Nat.Coprime 2 k := by rw [Nat.coprime_two_left]; exact hk_odd
      exact fibZeros_one_mul_coprime (by omega) (by omega) hcop fibZeros_two hk1
    · have hk1 : fibZeros k = 1 := fibZeros_one_of_odd_primes k (by omega) hk_odd hall
      have hcop : Nat.Coprime 4 k := by
        have h2 : Nat.Coprime 2 k := by rw [Nat.coprime_two_left]; exact hk_odd
        simpa using h2.pow_left 2
      exact fibZeros_one_mul_coprime (by omega) (by omega) hcop fibZeros_four hk1

end OMA.P_oeis_a053031

theorem OMA.solution : type_of% @OMA.S_oeis_a053031.main :=
  OMA.P_oeis_a053031.solve_a053031
