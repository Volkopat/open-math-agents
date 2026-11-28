import OMAStatements.S_oeis_a185376

namespace OMA.S_oeis_a185376_Proof

open OMA.S_oeis_a185376

private def mkN {L : ℕ} (w : PalWord L) : Necklace L :=
  Quotient.mk (rotation L) w

private lemma emod_neg_sub_one (L : ℕ) (hL : 0 < L) (x : ℤ) :
    ((-1 - x) % (L : ℤ)) = (L : ℤ) - 1 - (x % (L : ℤ)) := by
  have hLpos : (0 : ℤ) < (L : ℤ) := by omega
  have hmod_ge : 0 ≤ x % (L : ℤ) := Int.emod_nonneg x (ne_of_gt hLpos)
  have hmod_lt : x % (L : ℤ) < (L : ℤ) := Int.emod_lt_of_pos x hLpos
  have hdiv : x = (L : ℤ) * (x / (L : ℤ)) + x % (L : ℤ) := (Int.mul_ediv_add_emod x (L : ℤ)).symm
  have hrew : -1 - x = (L : ℤ) * (-(x / (L : ℤ)) - 1) + ((L : ℤ) - 1 - x % (L : ℤ)) := by
    linarith
  rw [hrew, Int.mul_add_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]

private lemma periodic_int_mul {f : ℤ → Bool} {c : ℤ} (hf : Function.Periodic f c) (k x : ℤ) :
    f (x + k * c) = f x := by
  have h := hf.int_mul k x
  simpa using h

private lemma pal_eq_of_eq_on_range {L M : ℕ} (hL : 0 < L)
    {f g : ℤ → Bool}
    (hfP : Function.Periodic f (L : ℤ)) (hfR : ∀ i, f (-1 - i) = f i)
    (hgP : Function.Periodic g (L : ℤ)) (hgR : ∀ i, g (-1 - i) = g i)
    (hM : L ≤ 2 * M)
    (heq : ∀ k : ℕ, k < M → f (k : ℤ) = g (k : ℤ)) :
    f = g := by
  funext x
  have hLpos : (0 : ℤ) < (L : ℤ) := by omega
  have hper_mod : ∀ (h : ℤ → Bool), Function.Periodic h (L : ℤ) → ∀ y : ℤ, h y = h (y % (L : ℤ)) := by
    intro h hP y
    have hdiv : y = y % (L : ℤ) + (y / (L : ℤ)) * (L : ℤ) := by
      have := Int.mul_ediv_add_emod y (L : ℤ)
      linarith
    conv_lhs => rw [hdiv]
    exact periodic_int_mul hP (y / (L : ℤ)) (y % (L : ℤ))
  rw [hper_mod f hfP x, hper_mod g hgP x]
  set r : ℕ := (x % (L : ℤ)).toNat
  have hr_eq : (r : ℤ) = x % (L : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg x (ne_of_gt hLpos))
  have hr_lt : r < L := by
    have hlt := Int.emod_lt_of_pos x hLpos
    omega
  rw [← hr_eq]
  by_cases hrm : r < M
  · exact heq r hrm
  · have hcomp_lt : L - 1 - r < M := by omega
    have hf1 : f (r : ℤ) = f ((L - 1 - r : ℕ) : ℤ) := by
      have h1 : f ((L - 1 - r : ℕ) : ℤ) = f (-1 - (r : ℤ) + (L : ℤ)) := by
        congr 1; omega
      rw [h1, hfP (-1 - (r : ℤ)), hfR (r : ℤ)]
    have hg1 : g (r : ℤ) = g ((L - 1 - r : ℕ) : ℤ) := by
      have h1 : g ((L - 1 - r : ℕ) : ℤ) = g (-1 - (r : ℤ) + (L : ℤ)) := by
        congr 1; omega
      rw [h1, hgP (-1 - (r : ℤ)), hgR (r : ℤ)]
    rw [hf1, hg1]
    exact heq (L - 1 - r) hcomp_lt

private def mkEvenPal (n : ℕ) (hn : 0 < n) (g : Fin n → Bool) (x : ℤ) : Bool :=
  let r := (x % ((2 * n : ℕ) : ℤ)).toNat
  g ⟨min r (2 * n - 1 - r), by
    have hlt : x % ((2 * n : ℕ) : ℤ) < ((2 * n : ℕ) : ℤ) := Int.emod_lt_of_pos x (by omega)
    have hge : 0 ≤ x % ((2 * n : ℕ) : ℤ) := Int.emod_nonneg x (by omega)
    omega⟩

private lemma mkEvenPal_per (n : ℕ) (hn : 0 < n) (g : Fin n → Bool) :
    Function.Periodic (mkEvenPal n hn g) ((2 * n : ℕ) : ℤ) := fun x => by
  unfold mkEvenPal
  have hmod : (x + ((2 * n : ℕ) : ℤ)) % ((2 * n : ℕ) : ℤ) = x % ((2 * n : ℕ) : ℤ) :=
    Int.add_emod_right x ((2 * n : ℕ) : ℤ)
  simp only [hmod]

private lemma mkEvenPal_refl (n : ℕ) (hn : 0 < n) (g : Fin n → Bool) (x : ℤ) :
    mkEvenPal n hn g (-1 - x) = mkEvenPal n hn g x := by
  unfold mkEvenPal
  have hneg := emod_neg_sub_one (2 * n) (by omega) x
  have hge : 0 ≤ x % ((2 * n : ℕ) : ℤ) := Int.emod_nonneg x (by omega)
  have hlt : x % ((2 * n : ℕ) : ℤ) < ((2 * n : ℕ) : ℤ) := Int.emod_lt_of_pos x (by omega)
  have hr_neg : ((-1 - x) % ((2 * n : ℕ) : ℤ)).toNat =
      2 * n - 1 - (x % ((2 * n : ℕ) : ℤ)).toNat := by
    rw [hneg]; omega
  dsimp only
  congr 1
  apply Fin.ext
  dsimp only
  rw [hr_neg]
  omega

private def palWordEvenEquiv (n : ℕ) (hn : 0 < n) : PalWord (2 * n) ≃ (Fin n → Bool) where
  toFun w i := w.1 (i.1 : ℤ)
  invFun g := ⟨mkEvenPal n hn g, mkEvenPal_per n hn g, mkEvenPal_refl n hn g⟩
  left_inv w := by
    apply Subtype.ext
    dsimp only
    refine pal_eq_of_eq_on_range (L := 2 * n) (M := n) (by omega)
      (mkEvenPal_per n hn _) (mkEvenPal_refl n hn _) w.2.1 w.2.2 (by omega) ?_
    intro k hk
    unfold mkEvenPal
    dsimp only
    have hmod : ((k : ℤ) % ((2 * n : ℕ) : ℤ)).toNat = k := by
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      exact Int.toNat_natCast k
    exact congrArg (fun t : ℕ => w.1 (t : ℤ)) (by rw [hmod]; omega)
  right_inv g := by
    funext i
    unfold mkEvenPal
    dsimp only
    have hi := i.2
    have hmod : ((i.1 : ℤ) % ((2 * n : ℕ) : ℤ)).toNat = i.1 := by
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      exact Int.toNat_natCast i.1
    congr 1
    apply Fin.ext
    dsimp only
    rw [hmod]
    omega

private def mkOddPal (m q : ℕ) (hm : m = 2 * q + 1) (g : Fin (q + 1) → Bool) (x : ℤ) : Bool :=
  let r := (x % (m : ℤ)).toNat
  g ⟨min r (2 * q - r), by
    have hlt : x % (m : ℤ) < (m : ℤ) := Int.emod_lt_of_pos x (by omega)
    have hge : 0 ≤ x % (m : ℤ) := Int.emod_nonneg x (by omega)
    omega⟩

private lemma mkOddPal_per (m q : ℕ) (hm : m = 2 * q + 1) (g : Fin (q + 1) → Bool) :
    Function.Periodic (mkOddPal m q hm g) (m : ℤ) := fun x => by
  unfold mkOddPal
  have hmod : (x + (m : ℤ)) % (m : ℤ) = x % (m : ℤ) := Int.add_emod_right x (m : ℤ)
  simp only [hmod]

private lemma mkOddPal_refl (m q : ℕ) (hm : m = 2 * q + 1) (g : Fin (q + 1) → Bool) (x : ℤ) :
    mkOddPal m q hm g (-1 - x) = mkOddPal m q hm g x := by
  unfold mkOddPal
  have hneg := emod_neg_sub_one m (by omega) x
  have hge : 0 ≤ x % (m : ℤ) := Int.emod_nonneg x (by omega)
  have hlt : x % (m : ℤ) < (m : ℤ) := Int.emod_lt_of_pos x (by omega)
  have hr_neg : ((-1 - x) % (m : ℤ)).toNat = 2 * q - (x % (m : ℤ)).toNat := by
    rw [hneg]; omega
  dsimp only
  congr 1
  apply Fin.ext
  dsimp only
  rw [hr_neg]
  omega

private def palWordOddEquiv (n m q : ℕ) (hm : m = 2 * q + 1) (hdvd : m ∣ 2 * n) :
    {w : PalWord (2 * n) // Function.Periodic w.1 (m : ℤ)} ≃ (Fin (q + 1) → Bool) where
  toFun w i := w.1.1 (i.1 : ℤ)
  invFun g :=
    have hfP2n : Function.Periodic (mkOddPal m q hm g) ((2 * n : ℕ) : ℤ) := by
      rcases hdvd with ⟨c, hc⟩
      intro x
      have h1 : x + ((2 * n : ℕ) : ℤ) = x + (c : ℤ) * (m : ℤ) := by
        rw [hc]; push_cast; ring
      rw [h1]
      exact periodic_int_mul (mkOddPal_per m q hm g) (c : ℤ) x
    ⟨⟨mkOddPal m q hm g, hfP2n, mkOddPal_refl m q hm g⟩, mkOddPal_per m q hm g⟩
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp only
    refine pal_eq_of_eq_on_range (L := m) (M := q + 1) (by omega)
      (mkOddPal_per m q hm _) (mkOddPal_refl m q hm _) w.2 w.1.2.2 (by omega) ?_
    intro k hk
    unfold mkOddPal
    dsimp only
    have hmod : ((k : ℤ) % (m : ℤ)).toNat = k := by
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      exact Int.toNat_natCast k
    exact congrArg (fun t : ℕ => w.1.1 (t : ℤ)) (by rw [hmod]; omega)
  right_inv g := by
    funext i
    unfold mkOddPal
    dsimp only
    have hi := i.2
    have hmod : ((i.1 : ℤ) % (m : ℤ)).toNat = i.1 := by
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      exact Int.toNat_natCast i.1
    congr 1
    apply Fin.ext
    dsimp only
    rw [hmod]
    omega

private lemma minimal_period_exists {L : ℕ} (hL : 0 < L) (f : ℤ → Bool)
    (hf : Function.Periodic f (L : ℤ)) :
    ∃ d : ℕ, 0 < d ∧ ∀ p : ℤ, Function.Periodic f p ↔ (d : ℤ) ∣ p := by
  classical
  have hex : ∃ d : ℕ, 0 < d ∧ Function.Periodic f (d : ℤ) := ⟨L, hL, hf⟩
  let d := Nat.find hex
  have hd_spec : 0 < d ∧ Function.Periodic f (d : ℤ) := Nat.find_spec hex
  refine ⟨d, hd_spec.1, fun p => ?_⟩
  constructor
  · intro hp
    have hdpos : (0 : ℤ) < (d : ℤ) := by omega
    have hrem_per : Function.Periodic f (p % (d : ℤ)) := by
      intro x
      have h1 : x + p % (d : ℤ) = (x + p) + (-(p / (d : ℤ))) * (d : ℤ) := by
        have := Int.mul_ediv_add_emod p (d : ℤ)
        linarith
      rw [h1, periodic_int_mul hd_spec.2 (-(p / (d : ℤ))) (x + p), hp x]
    have hge : 0 ≤ p % (d : ℤ) := Int.emod_nonneg p (ne_of_gt hdpos)
    have hlt : p % (d : ℤ) < (d : ℤ) := Int.emod_lt_of_pos p hdpos
    set r := (p % (d : ℤ)).toNat
    have hr_eq : (r : ℤ) = p % (d : ℤ) := Int.toNat_of_nonneg hge
    have hr_lt : r < d := by omega
    have hr0 : r = 0 := by
      by_contra hne
      have hpos : 0 < r := by omega
      have hmin := Nat.find_min hex hr_lt
      exact hmin ⟨hpos, by rwa [hr_eq]⟩
    have hmod0 : p % (d : ℤ) = 0 := by omega
    exact Int.dvd_of_emod_eq_zero hmod0
  · rintro ⟨k, rfl⟩
    intro x
    have h := periodic_int_mul hd_spec.2 k x
    simpa [mul_comm] using h

private lemma shift_pal_iff {L : ℕ} (w : PalWord L) (k : ℤ) :
    (∀ i, w.1 (-1 - i + k) = w.1 (i + k)) ↔ Function.Periodic w.1 (2 * k) := by
  constructor
  · intro h j
    have h1 := h (j + k)
    have h2 : -1 - (j + k) + k = -1 - j := by omega
    have h3 : j + k + k = j + 2 * k := by omega
    rw [h2, h3, w.2.2 j] at h1
    exact h1.symm
  · intro h i
    have h1 : -1 - i + k = -1 - (i - k) := by omega
    rw [h1, w.2.2 (i - k)]
    have h2 : i + k = (i - k) + 2 * k := by omega
    rw [h2, h (i - k)]

private lemma main_proved : ∀ n : ℕ, 0 < n →
    Nat.card (Necklace (2 * n)) =
      2 ^ (n - 1) + 2 ^ ((n - 2 ^ (n.factorization 2)) / 2 ^ (n.factorization 2 + 1)) := by
  classical
  intro n hn
  let v : ℕ := n.factorization 2
  have h2dvd : 2 ^ v ∣ n := Nat.ordProj_dvd n 2
  let m : ℕ := n / 2 ^ v
  have hnm : n = 2 ^ v * m := (Nat.mul_div_cancel' h2dvd).symm
  have hm_pos : 0 < m := Nat.pos_of_ne_zero fun hm0 => by
    rw [hm0, mul_zero] at hnm
    omega
  have hm_odd : ¬ (2 ∣ m) := by
    intro h2m
    have h2succ : 2 ^ (v + 1) ∣ n := by
      rcases h2m with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [hnm, ht, pow_succ]
      ring
    have hle : v + 1 ≤ n.factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by omega)).1 h2succ
    dsimp only [v] at hle
    omega
  let q : ℕ := m / 2
  have hmq : m = 2 * q + 1 := by
    have hmod : m % 2 = 1 := by
      by_contra h
      exact hm_odd (Nat.dvd_of_mod_eq_zero (by omega))
    dsimp only [q]
    omega
  have hexp : (n - 2 ^ v) / 2 ^ (v + 1) = q := by
    have h1 : n - 2 ^ v = 2 ^ (v + 1) * q := by
      rw [hnm, hmq, pow_succ]
      have : 2 ^ v * (2 * q + 1) = 2 ^ v * 2 * q + 2 ^ v := by ring
      omega
    rw [h1, Nat.mul_div_cancel_left q (pow_pos (by norm_num) (v + 1))]
  rw [hexp]
  let : Fintype (PalWord (2 * n)) := Fintype.ofEquiv (Fin n → Bool) (palWordEvenEquiv n hn).symm
  let : Fintype (Necklace (2 * n)) := Quotient.fintype (S_oeis_a185376.rotation (2 * n))
  have hcardN : Nat.card (Necklace (2 * n)) = Fintype.card (Necklace (2 * n)) :=
    Nat.card_eq_fintype_card
  rw [hcardN]
  have hcardPal : Fintype.card (PalWord (2 * n)) = 2 ^ n := by
    rw [Fintype.card_congr (palWordEvenEquiv n hn)]
    simp
  have hm_dvd_2n : m ∣ 2 * n := ⟨2 * 2 ^ v, by rw [hnm]; ring⟩
  have hcardOdd :
      (Finset.univ.filter fun w : PalWord (2 * n) => Function.Periodic w.1 (m : ℤ)).card =
      2 ^ (q + 1) := by
    rw [← Fintype.card_subtype]
    rw [Fintype.card_congr (palWordOddEquiv n m q hmq hm_dvd_2n)]
    simp
  have hclass_card : ∀ w : PalWord (2 * n),
      (Finset.univ.filter fun u : PalWord (2 * n) => mkN u = mkN w).card =
      if Function.Periodic w.1 (m : ℤ) then 1 else 2 := by
    intro w
    obtain ⟨d, hd_pos, hd_iff⟩ := minimal_period_exists (by omega) w.1 w.2.1
    have hd_dvd_2n : d ∣ 2 * n := by
      have := (hd_iff ((2 * n : ℕ) : ℤ)).1 w.2.1
      exact Int.ofNat_dvd.1 this
    have hper_m_iff : Function.Periodic w.1 (m : ℤ) ↔ ¬ (2 ∣ d) := by
      constructor
      · intro hpm h2d
        have hdm : d ∣ m := Int.ofNat_dvd.1 ((hd_iff (m : ℤ)).1 hpm)
        exact hm_odd (dvd_trans h2d hdm)
      · intro hd_odd
        have hcop : Nat.Coprime d (2 ^ (v + 1)) := by
          refine Nat.Coprime.pow_right (v + 1) ?_
          exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hd_odd |>.symm
        have hd_dvd_prod : d ∣ 2 ^ (v + 1) * m := by
          have : 2 * n = 2 ^ (v + 1) * m := by rw [hnm, pow_succ]; ring
          rwa [← this]
        have hdm : d ∣ m := hcop.dvd_of_dvd_mul_left hd_dvd_prod
        exact (hd_iff (m : ℤ)).2 (Int.ofNat_dvd.2 hdm)
    by_cases hpm : Function.Periodic w.1 (m : ℤ)
    · simp only [hpm, ↓reduceIte]
      have hd_odd : ¬ (2 ∣ d) := hper_m_iff.1 hpm
      have hset : (Finset.univ.filter fun u : PalWord (2 * n) => mkN u = mkN w) = {w} := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hq
          have hrel : (S_oeis_a185376.rotation (2 * n)).r w u := Quotient.exact hq.symm
          obtain ⟨k, hk⟩ := hrel
          have huR : ∀ i, w.1 (-1 - i + k) = w.1 (i + k) := fun i => by
            rw [← hk (-1 - i), ← hk i, u.2.2 i]
          have h2k : Function.Periodic w.1 (2 * k) := (shift_pal_iff w k).1 huR
          have hd_dvd_2k : (d : ℤ) ∣ 2 * k := (hd_iff (2 * k)).1 h2k
          have hcop : IsCoprime (d : ℤ) 2 := by
            have hc : Nat.Coprime d 2 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hd_odd).symm
            exact Nat.isCoprime_iff_coprime.2 hc
          have hd_dvd_k : (d : ℤ) ∣ k := hcop.dvd_of_dvd_mul_left (by simpa [mul_comm] using hd_dvd_2k)
          have hpk : Function.Periodic w.1 k := (hd_iff k).2 hd_dvd_k
          apply Subtype.ext
          funext i
          rw [hk i, hpk i]
        · intro hu
          subst hu
          rfl
      rw [hset, Finset.card_singleton]
    · simp only [hpm, ↓reduceIte]
      have h2d : 2 ∣ d := by
        by_contra hnd
        exact hpm (hper_m_iff.2 hnd)
      rcases h2d with ⟨e, he⟩
      have he_pos : 0 < e := by omega
      have he_not_per : ¬ Function.Periodic w.1 (e : ℤ) := by
        intro hpe
        have hde : d ∣ e := Int.ofNat_dvd.1 ((hd_iff (e : ℤ)).1 hpe)
        have hle : d ≤ e := Nat.le_of_dvd he_pos hde
        omega
      let w' : PalWord (2 * n) :=
        ⟨fun i => w.1 (i + (e : ℤ)),
          ⟨fun i => by
              have h := w.2.1 (i + (e : ℤ))
              simpa [add_assoc, add_comm, add_left_comm] using h,
            fun i => by
              have h2e : Function.Periodic w.1 (2 * (e : ℤ)) := by
                have hde : (d : ℤ) ∣ 2 * (e : ℤ) := ⟨1, by rw [he]; push_cast; ring⟩
                exact (hd_iff (2 * (e : ℤ))).2 hde
              exact (shift_pal_iff w (e : ℤ)).2 h2e i⟩⟩
      have hw'_ne : w' ≠ w := by
        intro heq
        apply he_not_per
        intro i
        exact congrFun (congrArg Subtype.val heq) i
      have hset : (Finset.univ.filter fun u : PalWord (2 * n) => mkN u = mkN w) = {w, w'} := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · intro hq
          have hrel : (S_oeis_a185376.rotation (2 * n)).r w u := Quotient.exact hq.symm
          obtain ⟨k, hk⟩ := hrel
          have huR : ∀ i, w.1 (-1 - i + k) = w.1 (i + k) := fun i => by
            rw [← hk (-1 - i), ← hk i, u.2.2 i]
          have h2k : Function.Periodic w.1 (2 * k) := (shift_pal_iff w k).1 huR
          have hd_dvd_2k : (d : ℤ) ∣ 2 * k := (hd_iff (2 * k)).1 h2k
          have he_dvd_k : (e : ℤ) ∣ k := by
            rcases hd_dvd_2k with ⟨t, ht⟩
            refine ⟨t, ?_⟩
            have hde : (d : ℤ) = 2 * (e : ℤ) := by rw [he]; push_cast; ring
            rw [hde] at ht
            linarith
          rcases he_dvd_k with ⟨t, rfl⟩
          rcases Int.even_or_odd t with ⟨s, rfl⟩ | ⟨s, rfl⟩
          · left
            apply Subtype.ext
            funext i
            have hd_dvd : (d : ℤ) ∣ (e : ℤ) * (s + s) := ⟨s, by rw [he]; push_cast; ring⟩
            have hpk := (hd_iff ((e : ℤ) * (s + s))).2 hd_dvd
            rw [hk i, hpk i]
          · right
            apply Subtype.ext
            funext i
            have hd_dvd : (d : ℤ) ∣ (e : ℤ) * (2 * s) := ⟨s, by rw [he]; push_cast; ring⟩
            have hpk := (hd_iff ((e : ℤ) * (2 * s))).2 hd_dvd
            dsimp only [w']
            rw [hk i]
            have hrew : i + (e : ℤ) * (2 * s + 1) = (i + (e : ℤ)) + (e : ℤ) * (2 * s) := by ring
            rw [hrew, hpk (i + (e : ℤ))]
        · rintro (rfl | rfl)
          · rfl
          · symm
            exact Quotient.sound ⟨(e : ℤ), fun _ => rfl⟩
      rw [hset, Finset.card_pair hw'_ne.symm]
  have hpart : Fintype.card (PalWord (2 * n)) =
      ∑ c : Necklace (2 * n),
        (Finset.univ.filter fun u : PalWord (2 * n) => mkN u = c).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  have hodd_bij :
      (Finset.univ.filter fun w : PalWord (2 * n) => Function.Periodic w.1 (m : ℤ)).card =
      (Finset.univ.filter fun c : Necklace (2 * n) =>
        (Finset.univ.filter fun u : PalWord (2 * n) => mkN u = c).card = 1).card := by
    refine Finset.card_bij (fun w _ => mkN w)
      (fun w hw => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        rw [hclass_card w, if_pos hw])
      (fun w1 hw1 w2 hw2 h => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
        have hc1 := hclass_card w1
        rw [if_pos hw1] at hc1
        have hmem1 : w1 ∈ Finset.univ.filter fun u : PalWord (2 * n) => mkN u = mkN w1 := by simp
        have hmem2 : w2 ∈ Finset.univ.filter fun u : PalWord (2 * n) => mkN u = mkN w1 := by
          simp [h.symm]
        rw [Finset.card_eq_one] at hc1
        rcases hc1 with ⟨a, ha⟩
        rw [ha, Finset.mem_singleton] at hmem1 hmem2
        exact hmem1.trans hmem2.symm)
      (fun c hc => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        obtain ⟨w, rfl⟩ := Quotient.exists_rep c
        refine ⟨w, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hcw := hclass_card w
        change (Finset.univ.filter fun u : PalWord (2 * n) => mkN u = mkN w).card = 1 at hc
        rw [hc] at hcw
        by_contra hnot
        rw [if_neg hnot] at hcw
        omega)
  have hsum_eq :
      (∑ c : Necklace (2 * n),
        (Finset.univ.filter fun u : PalWord (2 * n) => mkN u = c).card) +
      (Finset.univ.filter fun c : Necklace (2 * n) =>
        (Finset.univ.filter fun u : PalWord (2 * n) => mkN u = c).card = 1).card =
      2 * Fintype.card (Necklace (2 * n)) := by
    have h2 : (Finset.univ.filter fun c : Necklace (2 * n) =>
        (Finset.univ.filter fun u : PalWord (2 * n) => mkN u = c).card = 1).card =
        ∑ c : Necklace (2 * n),
          if (Finset.univ.filter fun u : PalWord (2 * n) => mkN u = c).card = 1 then 1 else 0 := by
      rw [Finset.card_filter]
    rw [h2, ← Finset.sum_add_distrib]
    have hall2 : ∀ c : Necklace (2 * n),
        (Finset.univ.filter fun u : PalWord (2 * n) => mkN u = c).card +
        (if (Finset.univ.filter fun u : PalWord (2 * n) => mkN u = c).card = 1 then 1 else 0) = 2 := by
      intro c
      obtain ⟨w, rfl⟩ := Quotient.exists_rep c
      change (Finset.univ.filter fun u : PalWord (2 * n) => mkN u = mkN w).card +
        (if (Finset.univ.filter fun u : PalWord (2 * n) => mkN u = mkN w).card = 1 then 1 else 0) = 2
      rw [hclass_card w]
      split_ifs <;> omega
    rw [Finset.sum_congr rfl fun c _ => hall2 c, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  have htwo_pow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    cases n with
    | zero => omega
    | succ k => simp [pow_succ, mul_comm]
  have htwo_q : 2 ^ (q + 1) = 2 * 2 ^ q := by
    rw [pow_succ, mul_comm]
  omega

end OMA.S_oeis_a185376_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a185376.main :=
  OMA.S_oeis_a185376_Proof.main_proved
