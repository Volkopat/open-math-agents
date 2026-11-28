import OMAStatements.S_oeis_a289398
import Mathlib

/-!
# Proof of OEIS A289398 Conjecture

For `n ≥ 1`, `a(n) = 7 * n` iff every prime factor of `n` lies in A042999
(`p = 2` or `p ≡ 3, 5 (mod 8)`).

- (`←`) For any `p ∈ A042999` dividing `n`, `n^2 + m^2 = 2 * k^2` forces `p ∣ m` and `p ∣ k`
  (by parity for `p = 2`, and because `2` is a quadratic non-residue mod `p` for `p ≡ 3, 5 (mod 8)`).
  Strong induction on `n` reduces to the base case `n = 1`, where `a(1) = 7`.
- (`→`) If a prime `q ∣ n` satisfies `q ≡ ±1 (mod 8)`, then `2` is a square mod `q`.
  By Thue's pigeonhole lemma we obtain `0 < x < y` with `2 * y^2 - x^2 = q`, and then
  `m = x^2 + 4*x*y + 2*y^2`, `k = x^2 + 2*x*y + 2*y^2` satisfy `q^2 + m^2 = 2 * k^2`
  with `q < m < 7 * q`. Scaling by `n / q` shows `a(n) < 7 * n`.
-/

namespace OeisA289398Proof

private lemma isValid_seven (n : ℕ) (hn : 1 ≤ n) : OMA.S_oeis_a289398.IsValid n (7 * n) := by
  refine ⟨by omega, 5 * n, ?_⟩
  ring

private lemma a_le_seven (n : ℕ) (hn : 1 ≤ n) : OMA.S_oeis_a289398.a n ≤ 7 * n :=
  Nat.sInf_le (isValid_seven n hn)

private lemma a_isValid (n : ℕ) (hn : 1 ≤ n) :
    OMA.S_oeis_a289398.IsValid n (OMA.S_oeis_a289398.a n) :=
  Nat.sInf_mem (s := { m : ℕ | OMA.S_oeis_a289398.IsValid n m }) ⟨7 * n, isValid_seven n hn⟩

private lemma seven_le_of_one {m : ℕ} (hm : OMA.S_oeis_a289398.IsValid 1 m) : 7 ≤ m := by
  rcases hm with ⟨h1m, k, hk⟩
  by_contra hlt
  push Not at hlt
  have hk_lt : k < 6 := by nlinarith
  interval_cases m <;> interval_cases k <;> omega

private lemma prime_dvd_of_odd_mod8 {p n m k : ℕ} (hprime : p.Prime)
    (hmod : p % 8 = 3 ∨ p % 8 = 5) (hpn : p ∣ n) (heq : n ^ 2 + m ^ 2 = 2 * k ^ 2) :
    p ∣ m ∧ p ∣ k := by
  have hp_ne2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hprime⟩
  have hno2 : ¬ IsSquare (2 : ZMod p) := by
    rw [ZMod.exists_sq_eq_two_iff hp_ne2]; omega
  have hm : p ∣ m := by
    by_contra hpm
    have hmz : (m : ZMod p) ≠ 0 := by
      rwa [Ne, ZMod.natCast_eq_zero_iff]
    have hnz : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hpn
    have hzeq : (m : ZMod p) ^ 2 = 2 * (k : ZMod p) ^ 2 := by
      have hcast := congrArg (Nat.cast (R := ZMod p)) heq
      push_cast at hcast
      rw [hnz, zero_pow (by decide : 2 ≠ 0), zero_add] at hcast
      exact hcast
    have hkz : (k : ZMod p) ≠ 0 := by
      intro hk0
      rw [hk0, zero_pow (by decide : 2 ≠ 0), mul_zero] at hzeq
      exact hmz (sq_eq_zero_iff.mp hzeq)
    refine hno2 ⟨(m : ZMod p) * (k : ZMod p)⁻¹, ?_⟩
    have hsq : ((m : ZMod p) * (k : ZMod p)⁻¹) * ((m : ZMod p) * (k : ZMod p)⁻¹) = 2 := by
      calc ((m : ZMod p) * (k : ZMod p)⁻¹) * ((m : ZMod p) * (k : ZMod p)⁻¹)
          = (m : ZMod p) ^ 2 * ((k : ZMod p) ^ 2)⁻¹ := by rw [← inv_pow]; ring
        _ = (2 * (k : ZMod p) ^ 2) * ((k : ZMod p) ^ 2)⁻¹ := by rw [hzeq]
        _ = 2 * ((k : ZMod p) ^ 2 * ((k : ZMod p) ^ 2)⁻¹) := by ring
        _ = 2 := by rw [mul_inv_cancel₀ (pow_ne_zero 2 hkz), mul_one]
    exact hsq.symm
  have hk : p ∣ k := by
    rcases hpn with ⟨n', rfl⟩
    rcases hm with ⟨m', rfl⟩
    have h2k : p ^ 2 ∣ 2 * k ^ 2 := ⟨n' ^ 2 + m' ^ 2, by linarith⟩
    have hcop : Nat.Coprime (p ^ 2) 2 :=
      (hprime.coprime_iff_not_dvd.mpr
        (by intro h; have := Nat.le_of_dvd (by decide) h; omega)).pow_left 2
    have hk2 : p ^ 2 ∣ k ^ 2 := hcop.dvd_of_dvd_mul_left h2k
    exact hprime.dvd_of_dvd_pow (dvd_trans (dvd_pow_self p (by decide : 2 ≠ 0)) hk2)
  exact ⟨hm, hk⟩

private lemma prime_dvd_of_inA042999 {p n m k : ℕ} (hp : OMA.S_oeis_a289398.InA042999 p)
    (hpn : p ∣ n) (heq : n ^ 2 + m ^ 2 = 2 * k ^ 2) : p ∣ m ∧ p ∣ k := by
  rcases hp with ⟨hprime, hp2 | hp35⟩
  · subst hp2
    rcases hpn with ⟨n', rfl⟩
    have heq' : 4 * n' ^ 2 + m ^ 2 = 2 * k ^ 2 := by linarith
    have hm2 : 2 ∣ m ^ 2 := ⟨k ^ 2 - 2 * n' ^ 2, by omega⟩
    have hm : 2 ∣ m := hprime.dvd_of_dvd_pow hm2
    rcases hm with ⟨m', rfl⟩
    have heq'' : 4 * n' ^ 2 + 4 * m' ^ 2 = 2 * k ^ 2 := by linarith
    have hk2 : 2 ∣ k ^ 2 := ⟨n' ^ 2 + m' ^ 2, by omega⟩
    exact ⟨⟨m', rfl⟩, hprime.dvd_of_dvd_pow hk2⟩
  · exact prime_dvd_of_odd_mod8 hprime hp35 hpn heq

private lemma seven_mul_le_of_all_inA042999 :
    ∀ n : ℕ, 1 ≤ n →
      (∀ p : ℕ, p.Prime → p ∣ n → OMA.S_oeis_a289398.InA042999 p) →
      ∀ m : ℕ, OMA.S_oeis_a289398.IsValid n m → 7 * n ≤ m := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hall m hm
    by_cases hn1 : n = 1
    · subst hn1
      simpa using seven_le_of_one hm
    · have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
      have hpn : n.minFac ∣ n := Nat.minFac_dvd n
      have hpA : OMA.S_oeis_a289398.InA042999 n.minFac := hall n.minFac hp hpn
      rcases hm with ⟨hnm, k, heq⟩
      obtain ⟨hpm, hpk⟩ := prime_dvd_of_inA042999 hpA hpn heq
      rcases hpn with ⟨n', hn'⟩
      rcases hpm with ⟨m', hm'⟩
      rcases hpk with ⟨k', hk'⟩
      have hn'_pos : 1 ≤ n' := by
        rcases Nat.eq_zero_or_pos n' with rfl | hpos
        · simp at hn'; omega
        · exact hpos
      have hn'_lt : n' < n := by
        rw [hn']
        exact lt_mul_of_one_lt_left (by omega) hp.one_lt
      have hall' : ∀ q : ℕ, q.Prime → q ∣ n' → OMA.S_oeis_a289398.InA042999 q := by
        intro q hq hqn'
        exact hall q hq (by rw [hn']; exact dvd_mul_of_dvd_right hqn' n.minFac)
      have hm'_valid : OMA.S_oeis_a289398.IsValid n' m' := by
        refine ⟨?_, k', ?_⟩
        · rw [hn', hm'] at hnm
          exact Nat.lt_of_mul_lt_mul_left hnm
        · have hsq : n.minFac ^ 2 * (n' ^ 2 + m' ^ 2) = n.minFac ^ 2 * (2 * k' ^ 2) := by
            calc n.minFac ^ 2 * (n' ^ 2 + m' ^ 2)
                = (n.minFac * n') ^ 2 + (n.minFac * m') ^ 2 := by ring
              _ = n ^ 2 + m ^ 2 := by rw [← hn', ← hm']
              _ = 2 * k ^ 2 := heq
              _ = 2 * (n.minFac * k') ^ 2 := by rw [hk']
              _ = n.minFac ^ 2 * (2 * k' ^ 2) := by ring
          exact mul_left_cancel₀ (pow_ne_zero 2 hp.ne_zero) hsq
      have hle := ih n' hn'_lt hn'_pos hall' m' hm'_valid
      rw [hn', hm']
      calc 7 * (n.minFac * n') = n.minFac * (7 * n') := by ring
        _ ≤ n.minFac * m' := Nat.mul_le_mul_left n.minFac hle

private lemma not_two_mul_sq_eq_sq {x y : ℕ} (hxy : x ≠ 0 ∨ y ≠ 0) : 2 * y ^ 2 ≠ x ^ 2 := by
  intro h
  have hy : y ≠ 0 := by
    intro hy0
    rw [hy0] at h
    have hx0 : x = 0 := by
      have : x ^ 2 = 0 := by simpa using h.symm
      exact sq_eq_zero_iff.mp this
    rcases hxy with hx | hy'
    · exact hx hx0
    · exact hy' hy0
  have hx : x ≠ 0 := by
    intro hx0
    rw [hx0] at h
    have hy0 : y ^ 2 = 0 := by omega
    exact hy (sq_eq_zero_iff.mp hy0)
  have h1 := congrArg (fun n => Nat.factorization n 2) h
  simp only [Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) (pow_ne_zero 2 hy),
             Nat.factorization_pow, Finsupp.coe_add, Finsupp.coe_smul,
             Pi.add_apply, Pi.smul_apply, smul_eq_mul,
             Nat.Prime.factorization_self Nat.prime_two] at h1
  omega

private lemma exists_rep_of_prime_mod8 {q : ℕ} (hq : q.Prime) (hmod : q % 8 = 1 ∨ q % 8 = 7) :
    ∃ x y : ℕ, 0 < x ∧ x < y ∧ 2 * y ^ 2 = x ^ 2 + q := by
  have hq_ne2 : q ≠ 2 := by omega
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨t, ht⟩ := (ZMod.exists_sq_eq_two_iff hq_ne2).mpr hmod
  set B := Nat.sqrt q
  have hB2_lt : B ^ 2 < q := by
    have hle : B ^ 2 ≤ q := by simpa [sq] using Nat.sqrt_le q
    have hne : B ^ 2 ≠ q := by
      intro heq
      have hq_ge : 7 ≤ q := by have := hq.two_le; omega
      have hB1 : B ≠ 1 := by intro h1; rw [h1] at heq; norm_num at heq; omega
      have hB0 : B ≠ 0 := by intro h0; rw [h0] at heq; norm_num at heq; omega
      have hBdvd : B ∣ q := ⟨B, by linarith⟩
      rcases hq.eq_one_or_self_of_dvd B hBdvd with h1 | hself
      · exact hB1 h1
      · rw [hself] at heq; nlinarith
    omega
  have hq_lt : q < (B + 1) ^ 2 := by simpa [sq] using Nat.lt_succ_sqrt q
  let f : Fin (B + 1) × Fin (B + 1) → ZMod q :=
    fun p => (p.1.val : ZMod q) - t * (p.2.val : ZMod q)
  have hcard : Fintype.card (ZMod q) < Fintype.card (Fin (B + 1) × Fin (B + 1)) := by
    rw [ZMod.card, Fintype.card_prod, Fintype.card_fin, ← sq]
    exact hq_lt
  obtain ⟨⟨a₁, b₁⟩, ⟨a₂, b₂⟩, hne, hfeq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  set X : ℤ := (a₁.val : ℤ) - (a₂.val : ℤ)
  set Y : ℤ := (b₁.val : ℤ) - (b₂.val : ℤ)
  have hXY_ne : X ≠ 0 ∨ Y ≠ 0 := by
    by_contra hboth
    push Not at hboth
    dsimp only [X, Y] at hboth
    rcases hboth with ⟨hX, hY⟩
    apply hne
    exact Prod.ext (Fin.ext (by exact_mod_cast sub_eq_zero.mp hX))
                   (Fin.ext (by exact_mod_cast sub_eq_zero.mp hY))
  have hX_cast : (X : ZMod q) = t * (Y : ZMod q) := by
    have h1 : (a₁.val : ZMod q) - t * (b₁.val : ZMod q) =
              (a₂.val : ZMod q) - t * (b₂.val : ZMod q) := hfeq
    dsimp only [X, Y]
    push_cast
    linear_combination h1
  have hsq_zmod : (2 * Y ^ 2 - X ^ 2 : ZMod q) = 0 := by
    calc (2 * Y ^ 2 - X ^ 2 : ZMod q)
        = 2 * (Y : ZMod q) ^ 2 - (t * (Y : ZMod q)) ^ 2 := by rw [hX_cast]
      _ = (2 - t * t) * (Y : ZMod q) ^ 2 := by ring
      _ = (2 - 2) * (Y : ZMod q) ^ 2 := by rw [← ht]
      _ = 0 := by ring
  have hqdvd : (q : ℤ) ∣ (2 * Y ^ 2 - X ^ 2) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa using hsq_zmod
  set x := X.natAbs
  set y := Y.natAbs
  have hx_le : x ≤ B := by
    have ha1 := a₁.isLt; have ha2 := a₂.isLt
    dsimp only [x, X]; omega
  have hy_le : y ≤ B := by
    have hb1 := b₁.isLt; have hb2 := b₂.isLt
    dsimp only [y, Y]; omega
  have hx2_lt : x ^ 2 < q := lt_of_le_of_lt (Nat.pow_le_pow_left hx_le 2) hB2_lt
  have hy2_lt : y ^ 2 < q := lt_of_le_of_lt (Nat.pow_le_pow_left hy_le 2) hB2_lt
  have hX2 : X ^ 2 = (x : ℤ) ^ 2 := (Int.natAbs_sq X).symm
  have hY2 : Y ^ 2 = (y : ℤ) ^ 2 := (Int.natAbs_sq Y).symm
  have hxy_ne : x ≠ 0 ∨ y ≠ 0 := by
    rcases hXY_ne with hX | hY
    · exact Or.inl (Int.natAbs_ne_zero.mpr hX)
    · exact Or.inr (Int.natAbs_ne_zero.mpr hY)
  rcases hqdvd with ⟨c, hc⟩
  rw [hX2, hY2] at hc
  have hc_ge : 0 ≤ c := by
    by_contra hneg
    push Not at hneg
    have : (q : ℤ) * c ≤ -(q : ℤ) := by nlinarith
    nlinarith
  have hc_lt : c < 2 := by
    by_contra hge2
    push Not at hge2
    have : 2 * (q : ℤ) ≤ (q : ℤ) * c := by nlinarith
    nlinarith
  have hc_ne0 : c ≠ 0 := by
    intro hc0
    rw [hc0, mul_zero] at hc
    have hnat : 2 * y ^ 2 = x ^ 2 := by exact_mod_cast (sub_eq_zero.mp hc)
    exact not_two_mul_sq_eq_sq hxy_ne hnat
  have hc1 : c = 1 := by omega
  rw [hc1, mul_one] at hc
  have hrep : 2 * y ^ 2 = x ^ 2 + q := by
    have : (2 * y ^ 2 : ℤ) = (x ^ 2 + q : ℤ) := by linarith
    exact_mod_cast this
  have hx_pos : 0 < x := by
    by_contra hx0
    have hx0' : x = 0 := by omega
    rw [hx0'] at hrep
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at hrep
    omega
  have hx_lt_y : x < y := by
    by_contra hge
    push Not at hge
    have : y ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hge 2
    omega
  exact ⟨x, y, hx_pos, hx_lt_y, hrep⟩

private lemma exists_lt_seven_mul_of_prime {q : ℕ} (hq : q.Prime) (hmod : q % 8 = 1 ∨ q % 8 = 7) :
    ∃ m : ℕ, OMA.S_oeis_a289398.IsValid q m ∧ m < 7 * q := by
  obtain ⟨x, y, hx_pos, hx_lt_y, hrep⟩ := exists_rep_of_prime_mod8 hq hmod
  have hq_eq : (q : ℤ) = 2 * (y : ℤ) ^ 2 - (x : ℤ) ^ 2 := by
    have hrepZ : 2 * (y : ℤ) ^ 2 = (x : ℤ) ^ 2 + (q : ℤ) := by exact_mod_cast hrep
    linarith
  refine ⟨x ^ 2 + 4 * x * y + 2 * y ^ 2, ⟨?_, x ^ 2 + 2 * x * y + 2 * y ^ 2, ?_⟩, ?_⟩
  · nlinarith
  · have hZ : ((q ^ 2 + (x ^ 2 + 4 * x * y + 2 * y ^ 2) ^ 2 : ℕ) : ℤ) =
        ((2 * (x ^ 2 + 2 * x * y + 2 * y ^ 2) ^ 2 : ℕ) : ℤ) := by
      push_cast
      rw [hq_eq]
      ring
    exact_mod_cast hZ
  · have hdiff : (7 * (q : ℤ)) - ((x : ℤ) ^ 2 + 4 * (x : ℤ) * (y : ℤ) + 2 * (y : ℤ) ^ 2) =
        4 * (3 * (y : ℤ) + 2 * (x : ℤ)) * ((y : ℤ) - (x : ℤ)) := by
      rw [hq_eq]; ring
    have hpos : (0 : ℤ) < 4 * (3 * (y : ℤ) + 2 * (x : ℤ)) * ((y : ℤ) - (x : ℤ)) := by
      have : (0 : ℤ) < (y : ℤ) - (x : ℤ) := by omega
      positivity
    have hltZ : ((x ^ 2 + 4 * x * y + 2 * y ^ 2 : ℕ) : ℤ) < ((7 * q : ℕ) : ℤ) := by
      push_cast; linarith
    exact_mod_cast hltZ

end OeisA289398Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a289398.main := by
  intro n hn
  constructor
  · intro ha q hq hqn
    by_contra hnot
    have hq_ne2 : q ≠ 2 := fun h2 => hnot ⟨hq, Or.inl h2⟩
    have hq_odd : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with h2 | hodd
      · exact absurd h2 hq_ne2
      · exact hodd
    have hmod : q % 8 = 1 ∨ q % 8 = 7 := by
      have h3 : q % 8 ≠ 3 := fun h => hnot ⟨hq, Or.inr (Or.inl h)⟩
      have h5 : q % 8 ≠ 5 := fun h => hnot ⟨hq, Or.inr (Or.inr h)⟩
      omega
    obtain ⟨m, ⟨hqm, k, hkeq⟩, hm7⟩ := OeisA289398Proof.exists_lt_seven_mul_of_prime hq hmod
    rcases hqn with ⟨r, rfl⟩
    have hr_pos : 0 < r := by
      rcases Nat.eq_zero_or_pos r with rfl | hpos
      · simp at hn
      · exact hpos
    have hvalid : OMA.S_oeis_a289398.IsValid (q * r) (m * r) := by
      refine ⟨Nat.mul_lt_mul_of_pos_right hqm hr_pos, k * r, ?_⟩
      calc (q * r) ^ 2 + (m * r) ^ 2 = (q ^ 2 + m ^ 2) * r ^ 2 := by ring
        _ = (2 * k ^ 2) * r ^ 2 := by rw [hkeq]
        _ = 2 * (k * r) ^ 2 := by ring
    have hle : OMA.S_oeis_a289398.a (q * r) ≤ m * r := Nat.sInf_le hvalid
    have hlt : m * r < 7 * (q * r) := by
      calc m * r < (7 * q) * r := Nat.mul_lt_mul_of_pos_right hm7 hr_pos
        _ = 7 * (q * r) := by ring
    omega
  · intro hall
    exact le_antisymm (OeisA289398Proof.a_le_seven n hn)
      (OeisA289398Proof.seven_mul_le_of_all_inA042999 n hn hall _
        (OeisA289398Proof.a_isValid n hn))
