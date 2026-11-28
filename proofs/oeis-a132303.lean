import OMAStatements.S_oeis_a132303
import Mathlib

/-
  Proof of OEIS A132303 (Peter Bala supercongruence for sum of cubes of trinomial coefficients).
  We prove the term-by-term congruence trinomial (n * p ^ k) (p * m) == trinomial (n * p ^ (k - 1)) m [MOD p ^ (2 * k)]
  for every prime p >= 5, n >= 1, k >= 1, and p ^ k | trinomial (n * p ^ k) j when p does not divide j.
-/

namespace OeisA132303Proof

open Polynomial

private lemma hockey_stick (N m : ℕ) (hN : 1 ≤ N) :
    ∑ a ∈ Finset.range (m + 1), (N + a - 1).choose a = (N + m).choose m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : N + (m + 1) - 1 = N + m := by omega
    rw [h1, ← Nat.add_assoc, Nat.choose_succ_succ, add_comm]

private noncomputable def Qpoly (j : ℕ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range (j + 1), Polynomial.X ^ i

private lemma one_sub_X_mul_Qpoly (j : ℕ) :
    (1 - Polynomial.X) * Qpoly j = 1 - Polynomial.X ^ (j + 1) := by
  induction j with
  | zero => simp [Qpoly]
  | succ j ih =>
    unfold Qpoly at ih ⊢
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

private lemma coeff_Qpoly (j b : ℕ) :
    (Qpoly j).coeff b = if b ≤ j then 1 else 0 := by
  simp only [Qpoly, Polynomial.finsetSum_coeff, coeff_X_pow]
  by_cases hb : b ≤ j
  · rw [if_pos hb]
    have hmem : b ∈ Finset.range (j + 1) := Finset.mem_range.mpr (by omega)
    rw [Finset.sum_eq_single b]
    · simp
    · intro x _ hx
      simp [hx.symm]
    · intro h
      exact (h hmem).elim
  · rw [if_neg hb]
    apply Finset.sum_eq_zero
    intro x hx
    have hxlt : x < j + 1 := Finset.mem_range.mp hx
    have hne : b ≠ x := fun h => hb (h ▸ Nat.lt_succ_iff.mp hxlt)
    simp [hne]

private lemma coeff_Qpoly_pow (N j m : ℕ) (hN : 1 ≤ N) (hm : m ≤ j) :
    ((Qpoly j) ^ N).coeff m = (((N + m - 1).choose m : ℕ) : ℤ) := by
  induction N generalizing m with
  | zero => omega
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hNpos
    · simp [coeff_Qpoly, hm]
    · rw [pow_succ, Polynomial.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => ((Qpoly j) ^ N).coeff a * (Qpoly j).coeff b) m]
      have hsum :
          ∑ x ∈ Finset.range (m + 1), ((Qpoly j) ^ N).coeff x * (Qpoly j).coeff (m - x) =
            ∑ x ∈ Finset.range (m + 1), (((N + x - 1).choose x : ℕ) : ℤ) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hxm : x ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
        have hxj : x ≤ j := le_trans hxm hm
        have hsub : m - x ≤ j := le_trans (Nat.sub_le m x) hm
        rw [ih x hNpos hxj, coeff_Qpoly j (m - x), if_pos hsub, mul_one]
      rw [hsum]
      norm_cast
      have hhs := hockey_stick N m hNpos
      have hEq : N + 1 + m - 1 = N + m := by omega
      rw [hEq]
      exact hhs

private lemma coeff_one_sub_X_pow_mul (j N : ℕ) (F : Polynomial ℤ) :
    ((1 - Polynomial.X ^ (j + 1)) ^ N * F).coeff j = F.coeff j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ', mul_assoc, sub_mul, one_mul, coeff_sub]
    have hzero : (Polynomial.X ^ (j + 1) * ((1 - Polynomial.X ^ (j + 1)) ^ N * F)).coeff j = 0 := by
      rw [Polynomial.coeff_X_pow_mul']
      simp [Nat.not_le_of_lt (Nat.lt_succ_self j)]
    rw [hzero, sub_zero]
    exact ih

private lemma trinomial_eq_sum_choose (N j : ℕ) (hN : 1 ≤ N) :
    (((1 + Polynomial.X + Polynomial.X ^ 2 : ℕ[X]) ^ N).coeff j : ℤ) =
      ∑ r ∈ Finset.range (j / 3 + 1),
        (-1 : ℤ) ^ r * (N.choose r : ℤ) * ((N + (j - 3 * r) - 1).choose (j - 3 * r) : ℤ) := by
  let P0 : Polynomial ℤ := 1 + Polynomial.X + Polynomial.X ^ 2
  have hcast : (((1 + Polynomial.X + Polynomial.X ^ 2 : ℕ[X]) ^ N).coeff j : ℤ) = (P0 ^ N).coeff j := by
    have hmap : ((1 + Polynomial.X + Polynomial.X ^ 2 : ℕ[X]) ^ N).map (Nat.castRingHom ℤ) = P0 ^ N := by
      simp [P0]
    have hcoe : (((1 + Polynomial.X + Polynomial.X ^ 2 : ℕ[X]) ^ N).coeff j : ℤ) =
        (Nat.castRingHom ℤ) (((1 + Polynomial.X + Polynomial.X ^ 2 : ℕ[X]) ^ N).coeff j) := rfl
    rw [hcoe, ← Polynomial.coeff_map, hmap]
  rw [hcast]
  have hid1 : (1 - Polynomial.X) * P0 = 1 - Polynomial.X ^ 3 := by
    simp only [P0]
    ring
  have hpoly :
      (1 - Polynomial.X ^ (j + 1)) ^ N * P0 ^ N = (1 - Polynomial.X ^ 3) ^ N * (Qpoly j) ^ N := by
    calc
      (1 - Polynomial.X ^ (j + 1)) ^ N * P0 ^ N
          = ((1 - Polynomial.X) * Qpoly j) ^ N * P0 ^ N := by rw [one_sub_X_mul_Qpoly]
      _ = ((1 - Polynomial.X) * P0) ^ N * (Qpoly j) ^ N := by simp only [mul_pow]; ring
      _ = (1 - Polynomial.X ^ 3) ^ N * (Qpoly j) ^ N := by rw [hid1]
  have hcoeff := congrArg (fun p : Polynomial ℤ => p.coeff j) hpoly
  rw [coeff_one_sub_X_pow_mul] at hcoeff
  rw [hcoeff]
  have hpow :
      (1 - Polynomial.X ^ 3 : Polynomial ℤ) ^ N =
        ∑ r ∈ Finset.range (N + 1), Polynomial.C ((-1 : ℤ) ^ r * (N.choose r : ℤ)) * (Polynomial.X ^ (3 * r) : Polynomial ℤ) := by
    rw [sub_eq_add_neg, add_comm 1 (-Polynomial.X ^ 3), add_pow]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [one_pow, mul_one, neg_pow, ← pow_mul, mul_comm 3 r, map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  rw [hpow, Finset.sum_mul, Polynomial.finsetSum_coeff]
  have hterm :
      ∀ r : ℕ,
        ((Polynomial.C ((-1 : ℤ) ^ r * (N.choose r : ℤ)) * (Polynomial.X ^ (3 * r) : Polynomial ℤ)) * (Qpoly j) ^ N).coeff j =
          if 3 * r ≤ j then
            (-1 : ℤ) ^ r * (N.choose r : ℤ) * ((N + (j - 3 * r) - 1).choose (j - 3 * r) : ℤ)
          else 0 := by
    intro r
    rw [mul_assoc, Polynomial.coeff_C_mul, coeff_X_pow_mul']
    split_ifs with hle
    · rw [coeff_Qpoly_pow N j (j - 3 * r) hN (Nat.sub_le j (3 * r))]
    · simp
  simp_rw [hterm]
  let M := max N (j / 3)
  have hM1 : N ≤ M := le_max_left _ _
  have hM2 : j / 3 ≤ M := le_max_right _ _
  have h1 :
      ∑ r ∈ Finset.range (N + 1),
          (if 3 * r ≤ j then (-1 : ℤ) ^ r * (N.choose r : ℤ) * ((N + (j - 3 * r) - 1).choose (j - 3 * r) : ℤ) else 0) =
        ∑ r ∈ Finset.range (M + 1),
          (if 3 * r ≤ j then (-1 : ℤ) ^ r * (N.choose r : ℤ) * ((N + (j - 3 * r) - 1).choose (j - 3 * r) : ℤ) else 0) := by
    refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hM1)) fun r _ hr => ?_
    have hrgt : N < r := Nat.lt_of_not_le (fun hle => hr (Finset.mem_range.mpr (Nat.lt_succ_of_le hle)))
    rw [Nat.choose_eq_zero_of_lt hrgt]
    simp
  have h2 :
      ∑ r ∈ Finset.range (j / 3 + 1),
          (-1 : ℤ) ^ r * (N.choose r : ℤ) * ((N + (j - 3 * r) - 1).choose (j - 3 * r) : ℤ) =
        ∑ r ∈ Finset.range (M + 1),
          (if 3 * r ≤ j then (-1 : ℤ) ^ r * (N.choose r : ℤ) * ((N + (j - 3 * r) - 1).choose (j - 3 * r) : ℤ) else 0) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext r
    simp only [Finset.mem_range, Finset.mem_filter]
    constructor
    · intro hr
      have hrle : r ≤ j / 3 := Nat.lt_succ_iff.mp hr
      refine ⟨Nat.lt_succ_of_le (le_trans hrle hM2), ?_⟩
      exact (Nat.le_div_iff_mul_le (by omega)).mp hrle |> fun h => by linarith
    · rintro ⟨_, hrle⟩
      exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le (by omega)).mpr (by linarith))
  rw [h1, ← h2]

private lemma dvd_choose_of_not_dvd {p n k r : ℕ} (hp : p.Prime) (_hk : 0 < k) (hpr : ¬ p ∣ r) :
    p ^ k ∣ (n * p ^ k).choose r := by
  rcases Nat.eq_zero_or_pos r with rfl | hrpos
  · exfalso; exact hpr (dvd_zero p)
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · rw [zero_mul, Nat.choose_eq_zero_of_lt hrpos]
    exact dvd_zero _
  have hrec : r * (n * p ^ k).choose r = (n * p ^ k) * (n * p ^ k - 1).choose (r - 1) := by
    have hs := Nat.add_one_mul_choose_eq (n * p ^ k - 1) (r - 1)
    have h1 : n * p ^ k - 1 + 1 = n * p ^ k := Nat.sub_add_cancel (Nat.mul_pos hnpos (pow_pos hp.pos k))
    have h2 : r - 1 + 1 = r := Nat.sub_add_cancel hrpos
    rw [h1, h2] at hs
    linarith
  have hcop : Nat.Coprime (p ^ k) r := (hp.coprime_iff_not_dvd.mpr hpr).pow_left k
  have hdvd : p ^ k ∣ r * (n * p ^ k).choose r := by
    rw [hrec]
    exact dvd_mul_of_dvd_left (dvd_mul_left (p ^ k) n) _
  exact hcop.dvd_of_dvd_mul_left hdvd

private lemma dvd_choose_add_sub_one_of_not_dvd {p n k L : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hn : 0 < n) (hpL : ¬ p ∣ L) :
    p ^ k ∣ (n * p ^ k + L - 1).choose L := by
  have hNpos : 0 < n * p ^ k := Nat.mul_pos hn (pow_pos hp.pos k)
  have hadd : n * p ^ k + L - 1 + 1 = n * p ^ k + L := by omega
  have hrec : (n * p ^ k + L) * (n * p ^ k + L - 1).choose L =
      (n * p ^ k) * (n * p ^ k + L).choose L := by
    have h1 := Nat.choose_succ_right_eq (n * p ^ k + L) L
    have h2 := Nat.add_one_mul_choose_eq (n * p ^ k + L - 1) L
    rw [hadd] at h2
    rw [Nat.add_sub_cancel] at h1
    linarith
  have hpnot : ¬ p ∣ n * p ^ k + L := by
    intro hd
    have hpk : p ∣ n * p ^ k := dvd_mul_of_dvd_right (dvd_pow_self p hk.ne') n
    exact hpL ((Nat.dvd_add_right hpk).mp hd)
  have hcop : Nat.Coprime (p ^ k) (n * p ^ k + L) := (hp.coprime_iff_not_dvd.mpr hpnot).pow_left k
  have hdvd : p ^ k ∣ (n * p ^ k + L) * (n * p ^ k + L - 1).choose L := by
    rw [hrec]
    exact dvd_mul_of_dvd_left (dvd_mul_left (p ^ k) n) _
  exact hcop.dvd_of_dvd_mul_left hdvd

private lemma dvd_trinomial_of_not_dvd {p n k j : ℕ} (hp : p.Prime)
    (hn : 0 < n) (hk : 0 < k) (hpj : ¬ p ∣ j) :
    p ^ k ∣ OMA.S_oeis_a132303.trinomial (n * p ^ k) j := by
  unfold OMA.S_oeis_a132303.trinomial
  have hN : 1 ≤ n * p ^ k := Nat.mul_pos hn (pow_pos hp.pos k)
  rw [← Int.natCast_dvd_natCast, trinomial_eq_sum_choose (n * p ^ k) j hN]
  apply Finset.dvd_sum
  intro r hr
  by_cases hpr : p ∣ r
  · have hpL : ¬ p ∣ j - 3 * r := by
      intro hd
      have hle : 3 * r ≤ j := (Nat.le_div_iff_mul_le (by omega)).mp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)) |> fun h => by linarith
      have hj : j = 3 * r + (j - 3 * r) := (Nat.add_sub_of_le hle).symm
      rw [hj] at hpj
      exact hpj (dvd_add (dvd_mul_of_dvd_right hpr 3) hd)
    have h2 : (p ^ k : ℤ) ∣ ((n * p ^ k + (j - 3 * r) - 1).choose (j - 3 * r) : ℤ) :=
      Int.natCast_dvd_natCast.mpr (dvd_choose_add_sub_one_of_not_dvd hp hk hn hpL)
    exact dvd_mul_of_dvd_right h2 _
  · have h1 : (p ^ k : ℤ) ∣ ((n * p ^ k).choose r : ℤ) :=
      Int.natCast_dvd_natCast.mpr (dvd_choose_of_not_dvd hp hk hpr)
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h1 _) _

private def blockSet (p d : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (p * d)).filter (fun t => ¬ p ∣ t)

private def blockProd (p d : ℕ) : ℕ :=
  ∏ t ∈ blockSet p d, t

private lemma blockSet_bijective (p d : ℕ) :
    ∀ x ∈ Finset.range d ×ˢ Finset.Ico 1 p, x.1 * p + x.2 ∈ blockSet p d := by
  intro x hx
  rcases Finset.mem_product.mp hx with ⟨hx1, hx2⟩
  have hj : x.1 < d := Finset.mem_range.mp hx1
  have hr1 : 1 ≤ x.2 := (Finset.mem_Ico.mp hx2).1
  have hr2 : x.2 < p := (Finset.mem_Ico.mp hx2).2
  simp only [blockSet, Finset.mem_filter, Finset.mem_Ico]
  refine ⟨⟨by nlinarith, ?_⟩, ?_⟩
  · calc
      x.1 * p + x.2 < x.1 * p + p := by omega
      _ = (x.1 + 1) * p := by ring
      _ ≤ d * p := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hj)
      _ = p * d := mul_comm d p
  · intro hd
    have hd2 : p ∣ x.2 := (Nat.dvd_add_right (dvd_mul_left p x.1)).mp hd
    have hzero : x.2 = 0 := Nat.eq_zero_of_dvd_of_lt hd2 hr2
    omega

private lemma sum_blockSet {α : Type*} [AddCommMonoid α] (p d : ℕ) (f : ℕ → α) :
    ∑ t ∈ blockSet p d, f t = ∑ j ∈ Finset.range d, ∑ r ∈ Finset.Ico 1 p, f (j * p + r) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun x _ => x.1 * p + x.2) (blockSet_bijective p d) ?_ ?_ (fun _ _ => rfl)
  · intro x hx y hy heq
    rcases Finset.mem_product.mp hx with ⟨_, hx2⟩
    rcases Finset.mem_product.mp hy with ⟨_, hy2⟩
    have hxp : x.2 < p := (Finset.mem_Ico.mp hx2).2
    have hyp : y.2 < p := (Finset.mem_Ico.mp hy2).2
    have hdiv := congrArg (· / p) heq
    have hmod := congrArg (· % p) heq
    have hdx : (x.1 * p + x.2) / p = x.1 := by
      rw [add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hxp, zero_add]
    have hdy : (y.1 * p + y.2) / p = y.1 := by
      rw [add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hyp, zero_add]
    have hmx : (x.1 * p + x.2) % p = x.2 := by
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hxp]
    have hmy : (y.1 * p + y.2) % p = y.2 := by
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hyp]
    ext
    · rw [← hdx, ← hdy, hdiv]
    · rw [← hmx, ← hmy, hmod]
  · intro t ht
    simp only [blockSet, Finset.mem_filter, Finset.mem_Ico] at ht
    rcases ht with ⟨⟨ht1, ht2⟩, hndvd⟩
    have hppos : 0 < p := by
      rcases Nat.eq_zero_or_pos p with rfl | h
      · simp at ht2
      · exact h
    refine ⟨(t / p, t % p), Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_Ico.mpr ⟨?_, Nat.mod_lt t hppos⟩⟩, ?_⟩
    · exact Nat.div_lt_of_lt_mul ht2
    · have hm : t % p ≠ 0 := fun h => hndvd (Nat.dvd_of_mod_eq_zero h)
      omega
    · have := Nat.div_add_mod t p
      linarith

private lemma card_blockSet_even {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (d : ℕ) :
    Even (blockSet p d).card := by
  have hcard : (blockSet p d).card = ∑ j ∈ Finset.range d, ∑ _r ∈ Finset.Ico 1 p, 1 := by
    simpa using sum_blockSet p d (fun _ => (1 : ℕ))
  rw [hcard]
  simp only [Finset.sum_const, Nat.card_Ico, Finset.card_range, smul_eq_mul, mul_one]
  have hodd : p % 2 = 1 := by
    rcases Nat.Prime.eq_two_or_odd hp with h2 | h
    · omega
    · exact h
  have hev : Even (p - 1) := Nat.even_iff.mpr (by omega)
  exact hev.mul_left d

private lemma coprime_blockProd {p d : ℕ} (hp : p.Prime) : Nat.Coprime (blockProd p d) p := by
  unfold blockProd
  refine Nat.Coprime.prod_left fun t ht => ?_
  have hnd : ¬ p ∣ t := (Finset.mem_filter.mp ht).2
  exact (hp.coprime_iff_not_dvd.mpr hnd).symm

private lemma prod_Ico_add_one (M m : ℕ) :
    ∏ i ∈ Finset.range m, (M + i) = (M + m - 1).choose m * m.factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    have h2 : (M + m) * (M + m - 1).choose m = (M + m).choose (m + 1) * (m + 1) := by
      rcases Nat.eq_zero_or_pos (M + m) with h0 | hpos
      · have hM0 : M = 0 := by omega
        have hm0 : m = 0 := by omega
        subst hM0 hm0; simp
      · have hs := Nat.add_one_mul_choose_eq (M + m - 1) m
        have hsub : M + m - 1 + 1 = M + m := by omega
        rw [hsub] at hs
        exact hs
    have h3 : M + (m + 1) - 1 = M + m := by omega
    rw [h3]
    calc
      (M + m - 1).choose m * m.factorial * (M + m)
          = ((M + m) * (M + m - 1).choose m) * m.factorial := by ring
      _ = ((M + m).choose (m + 1) * (m + 1)) * m.factorial := by rw [h2]
      _ = (M + m).choose (m + 1) * ((m + 1) * m.factorial) := by ring

private lemma prod_range_sub (N m : ℕ) (hm : m ≤ N) :
    ∏ i ∈ Finset.range m, (N - i) = N.choose m * m.factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm' : m ≤ N := Nat.le_of_succ_le hm
    rw [Finset.prod_range_succ, ih hm', Nat.factorial_succ]
    have hs := Nat.choose_succ_right_eq N m
    calc
      N.choose m * m.factorial * (N - m)
          = (N.choose m * (N - m)) * m.factorial := by ring
      _ = (N.choose (m + 1) * (m + 1)) * m.factorial := by rw [hs]
      _ = N.choose (m + 1) * ((m + 1) * m.factorial) := by ring

private lemma factorial_mul_split (p d : ℕ) (hp : 0 < p) :
    (p * d).factorial = p ^ d * d.factorial * blockProd p d := by
  by_cases hd : d = 0
  · subst hd; simp [blockProd, blockSet]
  have hpdpos : 1 ≤ p * d := Nat.mul_pos hp (Nat.pos_of_ne_zero hd)
  rw [← Finset.prod_Ico_id_eq_factorial (p * d)]
  have hsplit : Finset.Ico 1 (p * d + 1) = insert (p * d) (Finset.Ico 1 (p * d)) := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega
  rw [hsplit, Finset.prod_insert (by simp)]
  have hpart := Finset.prod_filter_mul_prod_filter_not (Finset.Ico 1 (p * d)) (fun t => p ∣ t) (fun t => t)
  have hdiv : (p * d) * ∏ t ∈ (Finset.Ico 1 (p * d)).filter (fun t => p ∣ t), t = p ^ d * d.factorial := by
    have hbij : ∏ j ∈ Finset.Ico 1 d, (p * j) =
        ∏ t ∈ (Finset.Ico 1 (p * d)).filter (fun t => p ∣ t), t := by
      refine Finset.prod_bij (fun j _ => p * j) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro j hj
        rcases Finset.mem_Ico.mp hj with ⟨hj1, hjd⟩
        simp only [Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨Nat.mul_pos hp hj1, Nat.mul_lt_mul_of_pos_left hjd hp⟩, dvd_mul_right p j⟩
      · intro a _ b _ h
        exact Nat.eq_of_mul_eq_mul_left hp h
      · intro t ht
        simp only [Finset.mem_filter, Finset.mem_Ico] at ht
        rcases ht with ⟨⟨ht1, ht2⟩, ⟨j, rfl⟩⟩
        refine ⟨j, Finset.mem_Ico.mpr ⟨?_, ?_⟩, rfl⟩
        · by_contra h
          have hj0 : j = 0 := by omega
          subst hj0
          simp at ht1
        · exact Nat.lt_of_mul_lt_mul_left ht2
    rw [← hbij]
    have hmerge : (p * d) * ∏ j ∈ Finset.Ico 1 d, (p * j) = ∏ j ∈ Finset.Ico 1 (d + 1), (p * j) := by
      have hs : Finset.Ico 1 (d + 1) = insert d (Finset.Ico 1 d) := by
        ext x; simp [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [hs, Finset.prod_insert (by simp)]
    rw [hmerge, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico, Nat.add_sub_cancel,
      Finset.prod_Ico_id_eq_factorial]
  calc
    p * d * ∏ x ∈ Finset.Ico 1 (p * d), x
        = p * d * ((∏ x ∈ (Finset.Ico 1 (p * d)).filter (fun t => p ∣ t), x) *
            ∏ x ∈ (Finset.Ico 1 (p * d)).filter (fun t => ¬ p ∣ t), x) := by rw [← hpart]
    _ = (p * d * ∏ x ∈ (Finset.Ico 1 (p * d)).filter (fun t => p ∣ t), x) * blockProd p d := by
          unfold blockProd blockSet; ring
    _ = p ^ d * d.factorial * blockProd p d := by rw [hdiv]

private lemma prod_Ico_add_one_split (p A d : ℕ) (hp : 0 < p) (_hA : 0 < A) :
    (blockProd p d : ℤ) * ((p * A + p * d - 1).choose (p * d) : ℤ) =
      ((A + d - 1).choose d : ℤ) * ∏ t ∈ blockSet p d, ((t : ℤ) + (p * A : ℤ)) := by
  have htot := prod_Ico_add_one (p * A) (p * d)
  have hpart := Finset.prod_filter_mul_prod_filter_not (Finset.range (p * d)) (fun i => p ∣ i) (fun i => p * A + i)
  have hdiv : ∏ i ∈ (Finset.range (p * d)).filter (fun i => p ∣ i), (p * A + i) =
      p ^ d * ((A + d - 1).choose d * d.factorial) := by
    have hbij : ∏ j ∈ Finset.range d, (p * (A + j)) =
        ∏ i ∈ (Finset.range (p * d)).filter (fun i => p ∣ i), (p * A + i) := by
      refine Finset.prod_bij (fun j _ => p * j) ?_ ?_ ?_ (fun j _ => by ring)
      · intro j hj
        have hjd : j < d := Finset.mem_range.mp hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mul_lt_mul_of_pos_left hjd hp), dvd_mul_right p j⟩
      · intro a _ b _ h
        exact Nat.eq_of_mul_eq_mul_left hp h
      · intro i hi
        rcases Finset.mem_filter.mp hi with ⟨hir, ⟨j, rfl⟩⟩
        exact ⟨j, Finset.mem_range.mpr (Nat.lt_of_mul_lt_mul_left (Finset.mem_range.mp hir)), rfl⟩
    rw [← hbij, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, prod_Ico_add_one A d]
  have hndiv : ∏ i ∈ (Finset.range (p * d)).filter (fun i => ¬ p ∣ i), (p * A + i) =
      ∏ t ∈ blockSet p d, (p * A + t) := by
    refine Finset.prod_congr ?_ (fun _ _ => rfl)
    ext x
    simp only [blockSet, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hx, hnd⟩
      have hx0 : x ≠ 0 := fun h => hnd (h ▸ dvd_zero p)
      exact ⟨⟨Nat.pos_of_ne_zero hx0, hx⟩, hnd⟩
    · rintro ⟨⟨_, hx2⟩, hnd⟩
      exact ⟨hx2, hnd⟩
  rw [← hpart, hdiv, hndiv, factorial_mul_split p d hp] at htot
  have hcancel :
      (p ^ d * d.factorial) * ((p * A + p * d - 1).choose (p * d) * blockProd p d) =
        (p ^ d * d.factorial) * ((A + d - 1).choose d * ∏ t ∈ blockSet p d, (p * A + t)) := by
    calc
      (p ^ d * d.factorial) * ((p * A + p * d - 1).choose (p * d) * blockProd p d)
          = (p * A + p * d - 1).choose (p * d) * (p ^ d * d.factorial * blockProd p d) := by ring
      _ = (p ^ d * ((A + d - 1).choose d * d.factorial)) * ∏ t ∈ blockSet p d, (p * A + t) := htot.symm
      _ = (p ^ d * d.factorial) * ((A + d - 1).choose d * ∏ t ∈ blockSet p d, (p * A + t)) := by ring
  have hpos : 0 < p ^ d * d.factorial := Nat.mul_pos (pow_pos hp d) (Nat.factorial_pos d)
  have hnat := Nat.eq_of_mul_eq_mul_left hpos hcancel
  have hz := congrArg (Nat.cast : ℕ → ℤ) hnat
  push_cast at hz
  rw [mul_comm (blockProd p d : ℤ), hz]
  congr 1
  refine Finset.prod_congr rfl fun t _ => by ring

private lemma prod_range_sub_split {p A s : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hs : s ≤ A) :
    (blockProd p s : ℤ) * ((p * A).choose (p * s) : ℤ) =
      (A.choose s : ℤ) * ∏ t ∈ blockSet p s, ((t : ℤ) - (p * A : ℤ)) := by
  have hppos : 0 < p := hp.pos
  have hps : p * s ≤ p * A := Nat.mul_le_mul_left p hs
  have htot := prod_range_sub (p * A) (p * s) hps
  have hpart := Finset.prod_filter_mul_prod_filter_not (Finset.range (p * s)) (fun i => p ∣ i) (fun i => p * A - i)
  have hdiv : ∏ i ∈ (Finset.range (p * s)).filter (fun i => p ∣ i), (p * A - i) =
      p ^ s * (A.choose s * s.factorial) := by
    have hbij : ∏ j ∈ Finset.range s, (p * (A - j)) =
        ∏ i ∈ (Finset.range (p * s)).filter (fun i => p ∣ i), (p * A - i) := by
      refine Finset.prod_bij (fun j _ => p * j) ?_ ?_ ?_ (fun j _ => by rw [Nat.mul_sub_left_distrib])
      · intro j hj
        have hjs : j < s := Finset.mem_range.mp hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mul_lt_mul_of_pos_left hjs hppos), dvd_mul_right p j⟩
      · intro a _ b _ h
        exact Nat.eq_of_mul_eq_mul_left hppos h
      · intro i hi
        rcases Finset.mem_filter.mp hi with ⟨hir, ⟨j, rfl⟩⟩
        exact ⟨j, Finset.mem_range.mpr (Nat.lt_of_mul_lt_mul_left (Finset.mem_range.mp hir)), rfl⟩
    rw [← hbij, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, prod_range_sub A s hs]
  have hndiv : ∏ i ∈ (Finset.range (p * s)).filter (fun i => ¬ p ∣ i), (p * A - i) =
      ∏ t ∈ blockSet p s, (p * A - t) := by
    refine Finset.prod_congr ?_ (fun _ _ => rfl)
    ext x
    simp only [blockSet, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hx, hnd⟩
      have hx0 : x ≠ 0 := fun h => hnd (h ▸ dvd_zero p)
      exact ⟨⟨Nat.pos_of_ne_zero hx0, hx⟩, hnd⟩
    · rintro ⟨⟨_, hx2⟩, hnd⟩
      exact ⟨hx2, hnd⟩
  rw [← hpart, hdiv, hndiv, factorial_mul_split p s hppos] at htot
  have hcancel :
      (p ^ s * s.factorial) * ((p * A).choose (p * s) * blockProd p s) =
        (p ^ s * s.factorial) * (A.choose s * ∏ t ∈ blockSet p s, (p * A - t)) := by
    calc
      (p ^ s * s.factorial) * ((p * A).choose (p * s) * blockProd p s)
          = (p * A).choose (p * s) * (p ^ s * s.factorial * blockProd p s) := by ring
      _ = (p ^ s * (A.choose s * s.factorial)) * ∏ t ∈ blockSet p s, (p * A - t) := htot.symm
      _ = (p ^ s * s.factorial) * (A.choose s * ∏ t ∈ blockSet p s, (p * A - t)) := by ring
  have hpos : 0 < p ^ s * s.factorial := Nat.mul_pos (pow_pos hppos s) (Nat.factorial_pos s)
  have hnat := Nat.eq_of_mul_eq_mul_left hpos hcancel
  have hz := congrArg (Nat.cast : ℕ → ℤ) hnat
  push_cast at hz
  have hneg :
      (∏ t ∈ blockSet p s, ((p * A - t : ℕ) : ℤ)) =
        ∏ t ∈ blockSet p s, ((t : ℤ) - (p * A : ℤ)) := by
    have hsub : ∀ t ∈ blockSet p s, ((p * A - t : ℕ) : ℤ) = -((t : ℤ) - (p * A : ℤ)) := by
      intro t ht
      have htlt : t < p * s := (Finset.mem_Ico.mp (Finset.mem_filter.mp ht).1).2
      have htle : t ≤ p * A := le_trans (le_of_lt htlt) hps
      rw [Nat.cast_sub htle]
      push_cast
      ring
    rw [Finset.prod_congr rfl hsub, Finset.prod_neg]
    have hev := card_blockSet_even hp hp3 s
    rw [Even.neg_one_pow hev, one_mul]
  rw [hneg] at hz
  rw [mul_comm (blockProd p s : ℤ)]
  exact hz

private noncomputable def Bpoly (p d : ℕ) : Polynomial ℤ :=
  ∏ t ∈ blockSet p d, (Polynomial.C (t : ℤ) + Polynomial.X)

private lemma eval_Bpoly (p d : ℕ) (z : ℤ) :
    (Bpoly p d).eval z = ∏ t ∈ blockSet p d, ((t : ℤ) + z) := by
  simp [Bpoly, Polynomial.eval_prod]

private lemma prod_add_X_coeff_zero (s : Finset ℕ) :
    (∏ t ∈ s, (Polynomial.C (t : ℤ) + Polynomial.X)).coeff 0 = ∏ t ∈ s, (t : ℤ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Polynomial.mul_coeff_zero,
      coeff_add, coeff_C_zero, coeff_X_zero, add_zero, ih]

private lemma prod_add_X_coeff_one (s : Finset ℕ) :
    (∏ t ∈ s, (Polynomial.C (t : ℤ) + Polynomial.X)).coeff 1 =
      ∑ t ∈ s, ∏ u ∈ s.erase t, (u : ℤ) := by
  induction s using Finset.induction_on with
  | empty => simp [coeff_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hmul : ((Polynomial.C (a : ℤ) + Polynomial.X) * ∏ t ∈ s, (Polynomial.C (t : ℤ) + Polynomial.X)).coeff 1 =
        (a : ℤ) * (∏ t ∈ s, (Polynomial.C (t : ℤ) + Polynomial.X)).coeff 1 +
          (∏ t ∈ s, (Polynomial.C (t : ℤ) + Polynomial.X)).coeff 0 := by
      rw [add_mul, Polynomial.C_mul', coeff_add, coeff_smul, coeff_X_mul, smul_eq_mul, add_comm]
    rw [hmul, ih, prod_add_X_coeff_zero]
    symm
    rw [Finset.sum_insert ha, Finset.erase_insert ha]
    have hsum :
        ∑ t ∈ s, (∏ u ∈ (insert a s).erase t, (u : ℤ)) =
          (a : ℤ) * ∑ t ∈ s, ∏ u ∈ s.erase t, (u : ℤ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      have hne : t ≠ a := fun h => ha (h ▸ ht)
      rw [Finset.erase_insert_of_ne hne.symm, Finset.prod_insert (fun h => ha (Finset.erase_subset t s h))]
    rw [hsum, add_comm]

private lemma prod_add_X_coeff_two (s : Finset ℕ) :
    2 * (∏ t ∈ s, (Polynomial.C (t : ℤ) + Polynomial.X)).coeff 2 =
      ∑ t ∈ s, ∑ u ∈ s.erase t, ∏ v ∈ (s.erase t).erase u, (v : ℤ) := by
  induction s using Finset.induction_on with
  | empty => simp [coeff_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hmul : ((Polynomial.C (a : ℤ) + Polynomial.X) * ∏ t ∈ s, (Polynomial.C (t : ℤ) + Polynomial.X)).coeff 2 =
        (a : ℤ) * (∏ t ∈ s, (Polynomial.C (t : ℤ) + Polynomial.X)).coeff 2 +
          (∏ t ∈ s, (Polynomial.C (t : ℤ) + Polynomial.X)).coeff 1 := by
      rw [add_mul, Polynomial.C_mul', coeff_add, coeff_smul, coeff_X_mul, smul_eq_mul, add_comm]
    rw [hmul]
    have hlin :
        2 * ((a : ℤ) * (∏ t ∈ s, (Polynomial.C (t : ℤ) + Polynomial.X)).coeff 2 +
          (∏ t ∈ s, (Polynomial.C (t : ℤ) + Polynomial.X)).coeff 1) =
          (a : ℤ) * (2 * (∏ t ∈ s, (Polynomial.C (t : ℤ) + Polynomial.X)).coeff 2) +
            2 * (∏ t ∈ s, (Polynomial.C (t : ℤ) + Polynomial.X)).coeff 1 := by ring
    rw [hlin, ih, prod_add_X_coeff_one]
    symm
    rw [Finset.sum_insert ha, Finset.erase_insert ha]
    have hsum :
        ∑ t ∈ s, ∑ u ∈ (insert a s).erase t, ∏ v ∈ ((insert a s).erase t).erase u, (v : ℤ) =
          (a : ℤ) * ∑ t ∈ s, ∑ u ∈ s.erase t, ∏ v ∈ (s.erase t).erase u, (v : ℤ) +
            ∑ t ∈ s, ∏ v ∈ s.erase t, (v : ℤ) := by
      have hinner :
          ∀ t ∈ s,
            (∑ u ∈ (insert a s).erase t, ∏ v ∈ ((insert a s).erase t).erase u, (v : ℤ)) =
              (∏ v ∈ s.erase t, (v : ℤ)) +
                (a : ℤ) * ∑ u ∈ s.erase t, ∏ v ∈ (s.erase t).erase u, (v : ℤ) := by
        intro t ht
        have hne : t ≠ a := fun h => ha (h ▸ ht)
        have ha_not : a ∉ s.erase t := fun h => ha (Finset.erase_subset t s h)
        rw [Finset.erase_insert_of_ne hne.symm, Finset.sum_insert ha_not, Finset.erase_insert ha_not]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u hu => ?_
        have huna : u ≠ a := fun h => ha_not (h ▸ hu)
        rw [Finset.erase_insert_of_ne huna.symm, Finset.prod_insert]
        exact fun h => ha_not (Finset.erase_subset u (s.erase t) h)
      rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, ← Finset.mul_sum, add_comm]
    rw [hsum]
    ring

private lemma coeff_zero_Bpoly (p d : ℕ) : (Bpoly p d).coeff 0 = (blockProd p d : ℤ) := by
  unfold Bpoly blockProd
  rw [prod_add_X_coeff_zero, Nat.cast_prod]

private lemma sum_zmod_inv_pow {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (_hm1 : 1 ≤ m) (hm2 : 2 ^ m % p ≠ 1) :
    ∑ r ∈ Finset.Ico 1 p, ((r : ZMod p)⁻¹) ^ m = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hbi :
      ∑ r ∈ Finset.Ico 1 p, ((r : ZMod p)⁻¹) ^ m =
        ∑ u : (ZMod p)ˣ, ((u : ZMod p)⁻¹) ^ m := by
    have hcop_fn : ∀ r ∈ Finset.Ico 1 p, Nat.Coprime r p := by
      intro r hr
      have hr0 : 1 ≤ r := (Finset.mem_Ico.mp hr).1
      have hrp : r < p := (Finset.mem_Ico.mp hr).2
      exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hr0 hrp)).symm
    refine Finset.sum_bij (fun r hr => ZMod.unitOfCoprime r (hcop_fn r hr)) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a ha b hb h
      have ha1 : ((ZMod.unitOfCoprime a (hcop_fn a ha) : (ZMod p)ˣ) : ZMod p) = (a : ZMod p) :=
        ZMod.coe_unitOfCoprime a (hcop_fn a ha)
      have hb1 : ((ZMod.unitOfCoprime b (hcop_fn b hb) : (ZMod p)ˣ) : ZMod p) = (b : ZMod p) :=
        ZMod.coe_unitOfCoprime b (hcop_fn b hb)
      have hZ : (a : ZMod p) = (b : ZMod p) := by
        rw [← ha1, ← hb1, h]
      have hap : a < p := (Finset.mem_Ico.mp ha).2
      have hbp : b < p := (Finset.mem_Ico.mp hb).2
      have := congrArg ZMod.val hZ
      rwa [ZMod.val_natCast_of_lt hap, ZMod.val_natCast_of_lt hbp] at this
    · intro u _
      have hval : (u : ZMod p).val ∈ Finset.Ico 1 p := by
        refine Finset.mem_Ico.mpr ⟨?_, ZMod.val_lt _⟩
        have hne : (u : ZMod p) ≠ 0 := u.ne_zero
        have hv : (u : ZMod p).val ≠ 0 := by
          intro hz
          exact hne ((ZMod.val_eq_zero _).mp hz)
        omega
      refine ⟨(u : ZMod p).val, hval, ?_⟩
      ext
      rw [ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val]
    · intro r hr
      rw [ZMod.coe_unitOfCoprime]
  rw [hbi]
  have hpnot2 : ¬ p ∣ 2 := by
    intro hd
    have hle := Nat.le_of_dvd (by omega) hd
    have := hp.two_le
    omega
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hz
    exact hpnot2 ((ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hz))
  have hcop2 : Nat.Coprime 2 p := (hp.coprime_iff_not_dvd.mpr hpnot2).symm
  let a : (ZMod p)ˣ := ZMod.unitOfCoprime 2 hcop2
  let S : ZMod p := ∑ u : (ZMod p)ˣ, ((u : ZMod p)⁻¹) ^ m
  have hscale : ((2 : ZMod p)⁻¹) ^ m * S = S := by
    simp only [S, Finset.mul_sum]
    have hreindex := Fintype.sum_bijective (fun u : (ZMod p)ˣ => a * u)
      (Group.mulLeft_bijective a) _ (fun u : (ZMod p)ˣ => ((u : ZMod p)⁻¹) ^ m) (fun _ => rfl)
    calc
      ∑ u : (ZMod p)ˣ, ((2 : ZMod p)⁻¹) ^ m * ((u : ZMod p)⁻¹) ^ m
          = ∑ u : (ZMod p)ˣ, (((a * u : (ZMod p)ˣ) : ZMod p)⁻¹) ^ m := by
              refine Finset.sum_congr rfl fun u _ => ?_
              have ha2 : (a : ZMod p) = (2 : ZMod p) := ZMod.coe_unitOfCoprime 2 hcop2
              rw [Units.val_mul, ha2, mul_inv, mul_pow]
      _ = S := hreindex
  have hmul : (1 - (2 : ZMod p) ^ m) * S = 0 := by
    have hinv : (2 : ZMod p) ^ m * ((2 : ZMod p)⁻¹) ^ m = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ h2ne, one_pow]
    calc
      (1 - (2 : ZMod p) ^ m) * S = S - (2 : ZMod p) ^ m * S := by ring
      _ = S - (2 : ZMod p) ^ m * (((2 : ZMod p)⁻¹) ^ m * S) := by rw [hscale]
      _ = S - ((2 : ZMod p) ^ m * ((2 : ZMod p)⁻¹) ^ m) * S := by ring
      _ = S - 1 * S := by rw [hinv]
      _ = 0 := by ring
  have h1ne : (1 - (2 : ZMod p) ^ m : ZMod p) ≠ 0 := by
    intro hz
    have heq : ((2 ^ m : ℕ) : ZMod p) = (1 : ZMod p) := by
      push_cast
      exact (sub_eq_zero.mp hz).symm
    have hval := congrArg ZMod.val heq
    rw [ZMod.val_natCast, ZMod.val_one] at hval
    exact hm2 hval
  exact (mul_eq_zero.mp hmul).resolve_left h1ne

private lemma dvd_coeff_one {p d e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hed : p ^ e ∣ d) :
    (p ^ (e + 2) : ℤ) ∣ (Bpoly p d).coeff 1 := by
  let M := p ^ (e + 2)
  have : NeZero M := ⟨pow_ne_zero _ hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  have hpcast : (p : ℤ) ^ (e + 2) = ((M : ℕ) : ℤ) := by
    simp only [M]; push_cast; rfl
  rw [hpcast, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  unfold Bpoly
  rw [prod_add_X_coeff_one]
  push_cast
  have hcop_t : ∀ t ∈ blockSet p d, Nat.Coprime t M := by
    intro t ht
    have hnd : ¬ p ∣ t := (Finset.mem_filter.mp ht).2
    exact (hp.coprime_iff_not_dvd.mpr hnd).symm.pow_right (e + 2)
  let invR : ℕ → ZMod M := fun t => if h : t ∈ blockSet p d then ↑((ZMod.unitOfCoprime t (hcop_t t h))⁻¹) else 0
  have hinv_mul : ∀ t ∈ blockSet p d, (t : ZMod M) * invR t = 1 := by
    intro t ht
    simp only [invR, dif_pos ht]
    have hc : ((ZMod.unitOfCoprime t (hcop_t t ht) : (ZMod M)ˣ) : ZMod M) = (t : ZMod M) :=
      ZMod.coe_unitOfCoprime t (hcop_t t ht)
    calc
      (t : ZMod M) * ↑((ZMod.unitOfCoprime t (hcop_t t ht))⁻¹)
          = ↑(ZMod.unitOfCoprime t (hcop_t t ht)) * ↑((ZMod.unitOfCoprime t (hcop_t t ht))⁻¹) := by rw [hc]
      _ = ↑(ZMod.unitOfCoprime t (hcop_t t ht) * (ZMod.unitOfCoprime t (hcop_t t ht))⁻¹) := by rw [Units.val_mul]
      _ = 1 := by simp
  have hterm :
      ∀ t ∈ blockSet p d,
        (∏ u ∈ (blockSet p d).erase t, (u : ZMod M)) = (blockProd p d : ZMod M) * invR t := by
    intro t ht
    have hprod : (t : ZMod M) * ∏ u ∈ (blockSet p d).erase t, (u : ZMod M) = (blockProd p d : ZMod M) := by
      rw [Finset.mul_prod_erase (blockSet p d) (fun u => (u : ZMod M)) ht]
      simp [blockProd]
    calc
      ∏ u ∈ (blockSet p d).erase t, (u : ZMod M)
          = (invR t * (t : ZMod M)) * ∏ u ∈ (blockSet p d).erase t, (u : ZMod M) := by
              rw [mul_comm (invR t), hinv_mul t ht, one_mul]
      _ = invR t * ((t : ZMod M) * ∏ u ∈ (blockSet p d).erase t, (u : ZMod M)) := by ring
      _ = invR t * (blockProd p d : ZMod M) := by rw [hprod]
      _ = (blockProd p d : ZMod M) * invR t := by ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  suffices hsum0 : ∑ t ∈ blockSet p d, invR t = 0 by
    rw [hsum0, mul_zero]
  have hinv_symm : ∀ t ∈ blockSet p d, p * d - t ∈ blockSet p d := by
    intro t ht
    simp only [blockSet, Finset.mem_filter, Finset.mem_Ico] at ht ⊢
    rcases ht with ⟨⟨ht1, ht2⟩, hnd⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro hd
    have hpd : p ∣ p * d := dvd_mul_right p d
    have : p ∣ t := by
      have heq : t = p * d - (p * d - t) := by omega
      rw [heq]
      exact Nat.dvd_sub hpd hd
    exact hnd this
  have hsum_eq :
      ∑ t ∈ blockSet p d, invR t = ∑ t ∈ blockSet p d, invR (p * d - t) := by
    symm
    refine Finset.sum_bij (fun t _ => p * d - t) hinv_symm ?_ ?_ (fun _ _ => rfl)
    · intro a ha b hb h
      have ha2 : a < p * d := (Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1).2
      have hb2 : b < p * d := (Finset.mem_Ico.mp (Finset.mem_filter.mp hb).1).2
      omega
    · intro t ht
      have ht2 : t < p * d := (Finset.mem_Ico.mp (Finset.mem_filter.mp ht).1).2
      exact ⟨p * d - t, hinv_symm t ht, by omega⟩
  have h2sum :
      (2 : ZMod M) * ∑ t ∈ blockSet p d, invR t =
        (p * d : ZMod M) * ∑ t ∈ blockSet p d, invR t * invR (p * d - t) := by
    calc
      (2 : ZMod M) * ∑ t ∈ blockSet p d, invR t
          = ∑ t ∈ blockSet p d, invR t + ∑ t ∈ blockSet p d, invR (p * d - t) := by
              rw [two_mul, ← hsum_eq]
      _ = ∑ t ∈ blockSet p d, (invR t + invR (p * d - t)) := (Finset.sum_add_distrib).symm
      _ = ∑ t ∈ blockSet p d, (p * d : ZMod M) * (invR t * invR (p * d - t)) := by
            refine Finset.sum_congr rfl fun t ht => ?_
            have ht_sub := hinv_symm t ht
            have ht2 : t < p * d := (Finset.mem_Ico.mp (Finset.mem_filter.mp ht).1).2
            have hadd : (t : ZMod M) + (p * d - t : ℕ) = (p * d : ZMod M) := by
              rw [Nat.cast_sub (le_of_lt ht2)]
              push_cast
              ring
            calc
              invR t + invR (p * d - t)
                  = invR t * ((p * d - t : ℕ) * invR (p * d - t)) +
                      ((t : ZMod M) * invR t) * invR (p * d - t) := by
                        rw [hinv_mul (p * d - t) ht_sub, hinv_mul t ht, mul_one, one_mul]
              _ = ((t : ZMod M) + (p * d - t : ℕ)) * (invR t * invR (p * d - t)) := by ring
              _ = (p * d : ZMod M) * (invR t * invR (p * d - t)) := by rw [hadd]
      _ = (p * d : ZMod M) * ∑ t ∈ blockSet p d, invR t * invR (p * d - t) := (Finset.mul_sum _ _ _).symm
  let W : ℕ := (∑ t ∈ blockSet p d, invR t * invR (p * d - t)).val
  have hW_cast : (W : ZMod M) = ∑ t ∈ blockSet p d, invR t * invR (p * d - t) := ZMod.natCast_zmod_val _
  have hW_mod_p : (W : ZMod p) = 0 := by
    have hpM : p ∣ M := dvd_pow_self p (Nat.succ_ne_zero (e + 1))
    let φ : ZMod M →+* ZMod p := ZMod.castHom hpM (ZMod p)
    have hφW : φ (W : ZMod M) = (W : ZMod p) := map_natCast φ W
    rw [← hφW, hW_cast, map_sum]
    have hφ_inv : ∀ t ∈ blockSet p d, φ (invR t) = (t : ZMod p)⁻¹ := by
      intro t ht
      have hnd : ¬ p ∣ t := (Finset.mem_filter.mp ht).2
      have htne : (t : ZMod p) ≠ 0 := by
        intro hz
        exact hnd ((ZMod.natCast_eq_zero_iff t p).mp hz)
      have h1 : φ ((t : ZMod M) * invR t) = φ 1 := by rw [hinv_mul t ht]
      rw [map_mul, map_natCast, map_one] at h1
      exact mul_left_cancel₀ htne (by rw [h1, mul_inv_cancel₀ htne])
    have hφ_neg : ∀ t ∈ blockSet p d, φ (invR (p * d - t)) = -((t : ZMod p)⁻¹) := by
      intro t ht
      rw [hφ_inv (p * d - t) (hinv_symm t ht)]
      have ht2 : t < p * d := (Finset.mem_Ico.mp (Finset.mem_filter.mp ht).1).2
      have hcast_sub : ((p * d - t : ℕ) : ZMod p) = -(t : ZMod p) := by
        rw [Nat.cast_sub (le_of_lt ht2)]
        push_cast
        simp
      rw [hcast_sub, inv_neg]
    have hsum_p :
        ∑ t ∈ blockSet p d, φ (invR t * invR (p * d - t)) =
          - ∑ t ∈ blockSet p d, ((t : ZMod p)⁻¹) ^ 2 := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [map_mul, hφ_inv t ht, hφ_neg t ht]
      ring
    rw [hsum_p, sum_blockSet]
    have hblk :
        ∑ j ∈ Finset.range d, ∑ r ∈ Finset.Ico 1 p, (((j * p + r : ℕ) : ZMod p)⁻¹) ^ 2 =
          (d : ZMod p) * ∑ r ∈ Finset.Ico 1 p, ((r : ZMod p)⁻¹) ^ 2 := by
      have hinner : ∀ j : ℕ,
          ∑ r ∈ Finset.Ico 1 p, (((j * p + r : ℕ) : ZMod p)⁻¹) ^ 2 =
            ∑ r ∈ Finset.Ico 1 p, ((r : ZMod p)⁻¹) ^ 2 := by
        intro j
        refine Finset.sum_congr rfl fun r _ => ?_
        have hper : ((j * p + r : ℕ) : ZMod p) = (r : ZMod p) := by
          push_cast; simp
        rw [hper]
      simp_rw [hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hblk, sum_zmod_inv_pow hp (by omega) (by omega) (by
      have : 2 ^ 2 = 4 := rfl
      rw [this, Nat.mod_eq_of_lt (by omega)]
      omega), mul_zero, neg_zero]
  have hpW : p ∣ W := (ZMod.natCast_eq_zero_iff W p).mp hW_mod_p
  have hM_dvd : M ∣ p * d * W := by
    have h1 : p ^ (e + 1) ∣ p * d := by
      rw [pow_succ']
      exact Nat.mul_dvd_mul_left p hed
    have h2 : p ^ (e + 1) * p ∣ p * d * W := Nat.mul_dvd_mul h1 hpW
    simpa [M, pow_succ] using h2
  have hrhs0 : (p * d : ZMod M) * ∑ t ∈ blockSet p d, invR t * invR (p * d - t) = 0 := by
    rw [← hW_cast, ← Nat.cast_mul, ← Nat.cast_mul]
    exact (ZMod.natCast_eq_zero_iff (p * d * W) M).mpr hM_dvd
  rw [hrhs0] at h2sum
  have hcop2 : Nat.Coprime 2 M := by
    have hp2 : ¬ p ∣ 2 := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
    exact (hp.coprime_iff_not_dvd.mpr hp2).symm.pow_right (e + 2)
  have hu2 : (2 : ZMod M) = ((ZMod.unitOfCoprime 2 hcop2 : (ZMod M)ˣ) : ZMod M) :=
    (ZMod.coe_unitOfCoprime 2 hcop2).symm
  let u2 := ZMod.unitOfCoprime 2 hcop2
  have hleft : (↑(u2⁻¹) : ZMod M) * ((2 : ZMod M) * ∑ t ∈ blockSet p d, invR t) = ∑ t ∈ blockSet p d, invR t := by
    rw [hu2, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  rw [← hleft, h2sum, mul_zero]

private lemma dvd_coeff_two {p d : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p : ℤ) ∣ (Bpoly p d).coeff 2 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h2nz : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hz)
    have := Nat.le_of_dvd (by omega) hd
    omega
  apply mul_left_cancel₀ h2nz
  rw [mul_zero]
  have h2eq : (2 : ZMod p) * (((Bpoly p d).coeff 2 : ℤ) : ZMod p) =
      (((2 * (Bpoly p d).coeff 2 : ℤ) : ℤ) : ZMod p) := by push_cast; ring
  rw [h2eq]
  unfold Bpoly
  rw [prod_add_X_coeff_two]
  push_cast
  have hterm :
      ∀ t ∈ blockSet p d, ∀ u ∈ (blockSet p d).erase t,
        (∏ v ∈ ((blockSet p d).erase t).erase u, (v : ZMod p)) =
          (blockProd p d : ZMod p) * (t : ZMod p)⁻¹ * (u : ZMod p)⁻¹ := by
    intro t ht u hu
    have hu_mem : u ∈ blockSet p d := Finset.erase_subset t (blockSet p d) hu
    have htne : (t : ZMod p) ≠ 0 := by
      intro hz
      exact (Finset.mem_filter.mp ht).2 ((ZMod.natCast_eq_zero_iff t p).mp hz)
    have hune : (u : ZMod p) ≠ 0 := by
      intro hz
      exact (Finset.mem_filter.mp hu_mem).2 ((ZMod.natCast_eq_zero_iff u p).mp hz)
    have hprod1 : (t : ZMod p) * ∏ w ∈ (blockSet p d).erase t, (w : ZMod p) = (blockProd p d : ZMod p) := by
      rw [Finset.mul_prod_erase (blockSet p d) (fun w => (w : ZMod p)) ht]
      simp [blockProd]
    have hprod2 : (u : ZMod p) * ∏ v ∈ ((blockSet p d).erase t).erase u, (v : ZMod p) =
        ∏ w ∈ (blockSet p d).erase t, (w : ZMod p) :=
      Finset.mul_prod_erase ((blockSet p d).erase t) (fun w => (w : ZMod p)) hu
    calc
      ∏ v ∈ ((blockSet p d).erase t).erase u, (v : ZMod p)
          = (u : ZMod p)⁻¹ * ((u : ZMod p) * ∏ v ∈ ((blockSet p d).erase t).erase u, (v : ZMod p)) := by
              rw [← mul_assoc, inv_mul_cancel₀ hune, one_mul]
      _ = (u : ZMod p)⁻¹ * ((t : ZMod p)⁻¹ * ((t : ZMod p) * ∏ w ∈ (blockSet p d).erase t, (w : ZMod p))) := by
              rw [hprod2]
              congr 1
              rw [← mul_assoc, inv_mul_cancel₀ htne, one_mul]
      _ = (blockProd p d : ZMod p) * (t : ZMod p)⁻¹ * (u : ZMod p)⁻¹ := by
              rw [hprod1]; ring
  have hsum :
      (∑ t ∈ blockSet p d, ∑ u ∈ (blockSet p d).erase t, ∏ v ∈ ((blockSet p d).erase t).erase u, (v : ZMod p)) =
        (blockProd p d : ZMod p) *
          ((∑ t ∈ blockSet p d, (t : ZMod p)⁻¹) ^ 2 - ∑ t ∈ blockSet p d, ((t : ZMod p)⁻¹) ^ 2) := by
    have h1 :
        ∑ t ∈ blockSet p d, ∑ u ∈ (blockSet p d).erase t, ∏ v ∈ ((blockSet p d).erase t).erase u, (v : ZMod p) =
          ∑ t ∈ blockSet p d, ∑ u ∈ (blockSet p d).erase t,
            (blockProd p d : ZMod p) * (t : ZMod p)⁻¹ * (u : ZMod p)⁻¹ :=
      Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun u hu => hterm t ht u hu
    rw [h1]
    have h2 :
        ∑ t ∈ blockSet p d, ∑ u ∈ (blockSet p d).erase t,
            (blockProd p d : ZMod p) * (t : ZMod p)⁻¹ * (u : ZMod p)⁻¹ =
          (blockProd p d : ZMod p) *
            ∑ t ∈ blockSet p d, (t : ZMod p)⁻¹ * ((∑ u ∈ blockSet p d, (u : ZMod p)⁻¹) - (t : ZMod p)⁻¹) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      simp_rw [mul_assoc, ← Finset.mul_sum]
      rw [Finset.sum_erase_eq_sub ht]
    rw [h2]
    congr 1
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sq]
  rw [hsum]
  have hs1 : ∑ t ∈ blockSet p d, (t : ZMod p)⁻¹ = 0 := by
    rw [sum_blockSet]
    have hinner : ∀ j : ℕ,
        ∑ r ∈ Finset.Ico 1 p, ((j * p + r : ℕ) : ZMod p)⁻¹ =
          ∑ r ∈ Finset.Ico 1 p, (r : ZMod p)⁻¹ := by
      intro j
      refine Finset.sum_congr rfl fun r _ => ?_
      have hper : ((j * p + r : ℕ) : ZMod p) = (r : ZMod p) := by
        push_cast; simp
      rw [hper]
    simp_rw [hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hpow1 : ∑ r ∈ Finset.Ico 1 p, (r : ZMod p)⁻¹ = 0 := by
      have h := sum_zmod_inv_pow hp (by omega : p ≠ 2) (le_refl 1) (by
        rw [pow_one, Nat.mod_eq_of_lt (by omega : 2 < p)]
        omega)
      simpa only [pow_one] using h
    rw [hpow1, mul_zero]
  have hs2 : ∑ t ∈ blockSet p d, ((t : ZMod p)⁻¹) ^ 2 = 0 := by
    rw [sum_blockSet]
    have hinner : ∀ j : ℕ,
        ∑ r ∈ Finset.Ico 1 p, (((j * p + r : ℕ) : ZMod p)⁻¹) ^ 2 =
          ∑ r ∈ Finset.Ico 1 p, ((r : ZMod p)⁻¹) ^ 2 := by
      intro j
      refine Finset.sum_congr rfl fun r _ => ?_
      have hper : ((j * p + r : ℕ) : ZMod p) = (r : ZMod p) := by
        push_cast; simp
      rw [hper]
    simp_rw [hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [sum_zmod_inv_pow hp (by omega) (by omega) (by
      have : 2 ^ 2 = 4 := rfl
      rw [this, Nat.mod_eq_of_lt (by omega)]
      omega), mul_zero]
  rw [hs1, hs2]
  simp

private lemma eval_sub_quad_dvd (f : Polynomial ℤ) (z : ℤ) :
    z ^ 3 ∣ f.eval z - f.coeff 0 - f.coeff 1 * z - f.coeff 2 * z ^ 2 := by
  induction f using Polynomial.induction_on' with
  | add f g ihf ihg =>
    have heq :
        (f + g).eval z - (f + g).coeff 0 - (f + g).coeff 1 * z - (f + g).coeff 2 * z ^ 2 =
          (f.eval z - f.coeff 0 - f.coeff 1 * z - f.coeff 2 * z ^ 2) +
            (g.eval z - g.coeff 0 - g.coeff 1 * z - g.coeff 2 * z ^ 2) := by
      simp only [eval_add, coeff_add]
      ring
    rw [heq]
    exact dvd_add ihf ihg
  | monomial n a =>
    by_cases h0 : n = 0
    · subst h0
      rw [monomial_zero_left, eval_C, coeff_C, coeff_C, coeff_C]
      norm_num
    by_cases h1 : n = 1
    · subst h1; simp [eval_monomial, coeff_monomial]
    by_cases h2 : n = 2
    · subst h2; simp [eval_monomial, coeff_monomial]
    have h3 : 3 ≤ n := by omega
    rw [eval_monomial, coeff_monomial, coeff_monomial, coeff_monomial]
    split_ifs <;> first | omega | (
      simp only [zero_mul, sub_zero]
      refine ⟨a * z ^ (n - 3), ?_⟩
      have hz : z ^ n = z ^ 3 * z ^ (n - 3) := by rw [← pow_add, Nat.add_sub_of_le h3]
      rw [hz]; ring)

private lemma dvd_eval_Bpoly_sub {p d k e : ℕ} {z : ℤ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hk : 0 < k) (hed : p ^ e ∣ d) (hz : (p ^ k : ℤ) ∣ z) :
    (p ^ min (k + e + 2) (2 * k + 1) : ℤ) ∣ (Bpoly p d).eval z - (blockProd p d : ℤ) := by
  set E := min (k + e + 2) (2 * k + 1)
  have h1 : (p ^ E : ℤ) ∣ (Bpoly p d).coeff 1 * z := by
    have hE1 : E ≤ k + e + 2 := min_le_left _ _
    have hc1 : (p ^ (e + 2) : ℤ) ∣ (Bpoly p d).coeff 1 := dvd_coeff_one hp hp5 hed
    have hmul : (p ^ (k + e + 2) : ℤ) ∣ (Bpoly p d).coeff 1 * z := by
      rw [show k + e + 2 = (e + 2) + k by omega, pow_add]
      exact mul_dvd_mul hc1 hz
    exact dvd_trans (pow_dvd_pow (p : ℤ) hE1) hmul
  have h2 : (p ^ E : ℤ) ∣ (Bpoly p d).coeff 2 * z ^ 2 := by
    have hE2 : E ≤ 2 * k + 1 := min_le_right _ _
    have hc2 : (p : ℤ) ∣ (Bpoly p d).coeff 2 := dvd_coeff_two hp hp5
    have hz2 : (p ^ (2 * k) : ℤ) ∣ z ^ 2 := by
      simpa [← pow_mul, mul_comm k 2] using pow_dvd_pow_of_dvd hz 2
    have hmul : (p ^ (2 * k + 1) : ℤ) ∣ (Bpoly p d).coeff 2 * z ^ 2 := by
      rw [show 2 * k + 1 = 1 + 2 * k by omega, pow_add, pow_one]
      exact mul_dvd_mul hc2 hz2
    exact dvd_trans (pow_dvd_pow (p : ℤ) hE2) hmul
  have h3 : (p ^ E : ℤ) ∣
      (Bpoly p d).eval z - (Bpoly p d).coeff 0 - (Bpoly p d).coeff 1 * z - (Bpoly p d).coeff 2 * z ^ 2 := by
    have hz3 : (p ^ (3 * k) : ℤ) ∣ z ^ 3 := by
      simpa [← pow_mul, mul_comm k 3] using pow_dvd_pow_of_dvd hz 3
    have hE3 : E ≤ 3 * k := le_trans (min_le_right _ _) (by omega)
    exact dvd_trans (pow_dvd_pow (p : ℤ) hE3) (dvd_trans hz3 (eval_sub_quad_dvd (Bpoly p d) z))
  have hid :
      (Bpoly p d).eval z - (blockProd p d : ℤ) =
        ((Bpoly p d).eval z - (Bpoly p d).coeff 0 - (Bpoly p d).coeff 1 * z - (Bpoly p d).coeff 2 * z ^ 2) +
          (Bpoly p d).coeff 1 * z + (Bpoly p d).coeff 2 * z ^ 2 := by
    rw [coeff_zero_Bpoly]
    ring
  rw [hid]
  exact dvd_add (dvd_add h3 h1) h2

private lemma master_choose_congr {p k d C L : ℕ} {z : ℤ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) (hd : 0 < d)
    (hz : (p ^ k : ℤ) ∣ z) (hdC : p ^ (k - 1) ∣ d * C)
    (hEq : (blockProd p d : ℤ) * (L : ℤ) = (C : ℤ) * (Bpoly p d).eval z) :
    L ≡ C [MOD p ^ (2 * k)] := by
  have hmul : (blockProd p d : ℤ) * ((L : ℤ) - (C : ℤ)) = (C : ℤ) * ((Bpoly p d).eval z - (blockProd p d : ℤ)) := by
    calc
      (blockProd p d : ℤ) * ((L : ℤ) - (C : ℤ))
          = (blockProd p d : ℤ) * (L : ℤ) - (C : ℤ) * (blockProd p d : ℤ) := by ring
      _ = (C : ℤ) * (Bpoly p d).eval z - (C : ℤ) * (blockProd p d : ℤ) := by rw [hEq]
      _ = (C : ℤ) * ((Bpoly p d).eval z - (blockProd p d : ℤ)) := by ring
  let e := d.factorization p
  have he_dvd : p ^ e ∣ d := by
    rw [← Nat.factorization_le_iff_dvd (pow_ne_zero e hp.ne_zero) hd.ne']
    intro q
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hp.factorization]
    by_cases hq : q = p
    · subst hq; simp [e]
    · simp [hq]
  rcases he_dvd with ⟨d0, hd_split⟩
  have hndvd_d0 : ¬ p ∣ d0 := by
    intro hdvd0
    have hpe1 : p ^ (e + 1) ∣ d := by
      rcases hdvd0 with ⟨m, rfl⟩
      exact ⟨m, by rw [hd_split, pow_succ]; ring⟩
    have hle := (Nat.factorization_le_iff_dvd (pow_ne_zero (e + 1) hp.ne_zero) hd.ne').mpr hpe1 p
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hp.factorization, Finsupp.single_eq_same, mul_one] at hle
    omega
  have hcop_compl : Nat.Coprime p d0 := hp.coprime_iff_not_dvd.mpr hndvd_d0
  have heval : (p ^ min (k + e + 2) (2 * k + 1) : ℤ) ∣ (Bpoly p d).eval z - (blockProd p d : ℤ) :=
    dvd_eval_Bpoly_sub hp hp5 hk ⟨d0, hd_split⟩ hz
  have hrhs : (p ^ (2 * k) : ℤ) ∣ (C : ℤ) * ((Bpoly p d).eval z - (blockProd p d : ℤ)) := by
    by_cases hke : k - 1 ≤ e
    · have h2k : 2 * k ≤ min (k + e + 2) (2 * k + 1) := le_min (by omega) (by omega)
      exact dvd_mul_of_dvd_right (dvd_trans (pow_dvd_pow (p : ℤ) h2k) heval) _
    · have he_lt : e < k - 1 := Nat.lt_of_not_le hke
      have hdC' : p ^ ((k - 1 - e) + e) ∣ p ^ e * (d0 * C) := by
        rw [Nat.sub_add_cancel (le_of_lt he_lt), ← mul_assoc, ← hd_split]
        exact hdC
      rw [pow_add, mul_comm (p ^ (k - 1 - e))] at hdC'
      have hdvdC' : p ^ (k - 1 - e) ∣ d0 * C :=
        Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos e) hdC'
      have hcop_pow : Nat.Coprime (p ^ (k - 1 - e)) d0 :=
        hcop_compl.pow_left (k - 1 - e)
      have hC_nat : p ^ (k - 1 - e) ∣ C := hcop_pow.dvd_of_dvd_mul_left hdvdC'
      have hC_int : (p ^ (k - 1 - e) : ℤ) ∣ (C : ℤ) := Int.natCast_dvd_natCast.mpr hC_nat
      have hmul_div : (p ^ ((k - 1 - e) + min (k + e + 2) (2 * k + 1)) : ℤ) ∣
          (C : ℤ) * ((Bpoly p d).eval z - (blockProd p d : ℤ)) := by
        rw [pow_add]
        exact mul_dvd_mul hC_int heval
      have hexp : 2 * k ≤ (k - 1 - e) + min (k + e + 2) (2 * k + 1) := by omega
      exact dvd_trans (pow_dvd_pow (p : ℤ) hexp) hmul_div
  rw [← hmul] at hrhs
  have hcopZ : IsCoprime (p ^ (2 * k) : ℤ) (blockProd p d : ℤ) :=
    ((coprime_blockProd hp).symm.pow_left (2 * k)).isCoprime
  have hzdvd : (p ^ (2 * k) : ℤ) ∣ (L : ℤ) - (C : ℤ) := hcopZ.dvd_of_dvd_mul_left hrhs
  exact Int.natCast_modEq_iff.mp ((Int.modEq_iff_dvd).mpr hzdvd).symm

private lemma choose_mul_modEq {p k A s : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hk : 0 < k) (hA : p ^ (k - 1) ∣ A) :
    (p * A).choose (p * s) ≡ A.choose s [MOD p ^ (2 * k)] := by
  by_cases hs : s ≤ A
  · rcases Nat.eq_zero_or_pos s with rfl | hspos
    · simp [Nat.ModEq]
    rcases Nat.eq_zero_or_pos A with rfl | hApos
    · omega
    have hEq : (blockProd p s : ℤ) * ((p * A).choose (p * s) : ℤ) =
        (A.choose s : ℤ) * (Bpoly p s).eval (-(p * A : ℤ)) := by
      rw [eval_Bpoly]
      convert prod_range_sub_split hp (by omega) hs using 3
      ring
    have hsC : p ^ (k - 1) ∣ s * A.choose s := by
      have hrec := Nat.add_one_mul_choose_eq (A - 1) (s - 1)
      rw [Nat.sub_add_cancel hApos, Nat.sub_add_cancel hspos] at hrec
      rw [mul_comm s, ← hrec]
      exact dvd_mul_of_dvd_left hA _
    have hz : (p ^ k : ℤ) ∣ -(p * A : ℤ) := by
      rcases hA with ⟨q, hq⟩
      refine ⟨-(q : ℤ), ?_⟩
      have hk1 : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
      rw [hq]
      nth_rw 2 [hk1]
      rw [pow_succ']
      push_cast
      ring
    exact master_choose_congr hp hp5 hk hspos hz hsC hEq
  · have hlt1 : A < s := Nat.lt_of_not_le hs
    have hlt2 : p * A < p * s := Nat.mul_lt_mul_of_pos_left hlt1 hp.pos
    rw [Nat.choose_eq_zero_of_lt hlt1, Nat.choose_eq_zero_of_lt hlt2]

private lemma choose_add_sub_one_modEq {p k A d : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hk : 0 < k) (hApos : 0 < A) (hA : p ^ (k - 1) ∣ A) :
    (p * A + p * d - 1).choose (p * d) ≡ (A + d - 1).choose d [MOD p ^ (2 * k)] := by
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · simp [Nat.ModEq]
  have hEq : (blockProd p d : ℤ) * ((p * A + p * d - 1).choose (p * d) : ℤ) =
      ((A + d - 1).choose d : ℤ) * (Bpoly p d).eval (p * A : ℤ) := by
    rw [eval_Bpoly]
    exact prod_Ico_add_one_split p A d hp.pos hApos
  have hdC : p ^ (k - 1) ∣ d * (A + d - 1).choose d := by
    have hrec := Nat.choose_succ_right_eq (A + d - 1) (d - 1)
    have hd1 : d - 1 + 1 = d := Nat.sub_add_cancel hdpos
    have had : A + d - 1 - (d - 1) = A := by omega
    rw [hd1, had] at hrec
    rw [mul_comm d, hrec]
    exact dvd_mul_of_dvd_right hA _
  have hz : (p ^ k : ℤ) ∣ (p * A : ℤ) := by
    rcases hA with ⟨q, hq⟩
    refine ⟨(q : ℤ), ?_⟩
    have hk1 : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
    rw [hq]
    nth_rw 2 [hk1]
    rw [pow_succ']
    push_cast
    ring
  exact master_choose_congr hp hp5 hk hdpos hz hdC hEq

private lemma trinomial_mul_modEq {p n k m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : 0 < n) (hk : 0 < k) :
    OMA.S_oeis_a132303.trinomial (n * p ^ k) (p * m) ≡
      OMA.S_oeis_a132303.trinomial (n * p ^ (k - 1)) m [MOD p ^ (2 * k)] := by
  let A := n * p ^ (k - 1)
  have hApos : 0 < A := Nat.mul_pos hn (pow_pos hp.pos (k - 1))
  have hA_dvd : p ^ (k - 1) ∣ A := dvd_mul_left _ n
  have hN_eq : n * p ^ k = p * A := by
    have hk1 : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
    nth_rw 1 [hk1, pow_succ]
    simp only [A]
    ring
  have hNpos : 1 ≤ n * p ^ k := Nat.mul_pos hn (pow_pos hp.pos k)
  rw [← Int.natCast_modEq_iff]
  unfold OMA.S_oeis_a132303.trinomial
  rw [trinomial_eq_sum_choose (n * p ^ k) (p * m) hNpos,
    trinomial_eq_sum_choose A m hApos]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (p * m / 3 + 1)) (fun r => p ∣ r)]
  have hndiv :
      (p ^ (2 * k) : ℤ) ∣
        ∑ r ∈ (Finset.range (p * m / 3 + 1)).filter (fun r => ¬ p ∣ r),
          (-1 : ℤ) ^ r * ((n * p ^ k).choose r : ℤ) *
            ((n * p ^ k + (p * m - 3 * r) - 1).choose (p * m - 3 * r) : ℤ) := by
    apply Finset.dvd_sum
    intro r hr
    rcases Finset.mem_filter.mp hr with ⟨hrr, hpr⟩
    have hle : 3 * r ≤ p * m :=
      (Nat.le_div_iff_mul_le (by omega)).mp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hrr)) |> fun h => by linarith
    have hpL : ¬ p ∣ p * m - 3 * r := by
      intro hd
      have hpm : p * m = 3 * r + (p * m - 3 * r) := (Nat.add_sub_of_le hle).symm
      have hd3r : p ∣ 3 * r := (Nat.dvd_add_left hd).mp (by rw [← hpm]; exact dvd_mul_right p m)
      have hp3 : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
      exact hpr (hp.dvd_mul.mp hd3r |>.resolve_left hp3)
    have h1 : (p ^ k : ℤ) ∣ ((n * p ^ k).choose r : ℤ) :=
      Int.natCast_dvd_natCast.mpr (dvd_choose_of_not_dvd hp hk hpr)
    have h2 : (p ^ k : ℤ) ∣ ((n * p ^ k + (p * m - 3 * r) - 1).choose (p * m - 3 * r) : ℤ) :=
      Int.natCast_dvd_natCast.mpr (dvd_choose_add_sub_one_of_not_dvd hp hk hn hpL)
    have hmul : (p ^ (2 * k) : ℤ) ∣
        ((n * p ^ k).choose r : ℤ) * ((n * p ^ k + (p * m - 3 * r) - 1).choose (p * m - 3 * r) : ℤ) := by
      rw [show 2 * k = k + k by omega, pow_add]
      exact mul_dvd_mul h1 h2
    calc
      (p ^ (2 * k) : ℤ) ∣ (-1 : ℤ) ^ r *
          (((n * p ^ k).choose r : ℤ) * ((n * p ^ k + (p * m - 3 * r) - 1).choose (p * m - 3 * r) : ℤ)) :=
        dvd_mul_of_dvd_right hmul _
      _ = (-1 : ℤ) ^ r * ((n * p ^ k).choose r : ℤ) *
          ((n * p ^ k + (p * m - 3 * r) - 1).choose (p * m - 3 * r) : ℤ) := by ring
  have hcong_ndiv :
      (∑ r ∈ (Finset.range (p * m / 3 + 1)).filter (fun r => ¬ p ∣ r),
          (-1 : ℤ) ^ r * ((n * p ^ k).choose r : ℤ) *
            ((n * p ^ k + (p * m - 3 * r) - 1).choose (p * m - 3 * r) : ℤ)) ≡ 0 [ZMOD (p ^ (2 * k) : ℤ)] :=
    Int.modEq_zero_iff_dvd.mpr hndiv
  have hdiv :
      (∑ r ∈ (Finset.range (p * m / 3 + 1)).filter (fun r => p ∣ r),
          (-1 : ℤ) ^ r * ((n * p ^ k).choose r : ℤ) *
            ((n * p ^ k + (p * m - 3 * r) - 1).choose (p * m - 3 * r) : ℤ)) =
        ∑ s ∈ Finset.range (m / 3 + 1),
          (-1 : ℤ) ^ s * ((p * A).choose (p * s) : ℤ) *
            ((p * A + p * (m - 3 * s) - 1).choose (p * (m - 3 * s)) : ℤ) := by
    symm
    refine Finset.sum_bij (fun s _ => p * s) ?_ ?_ ?_ ?_
    · intro s hs
      have hsl : s ≤ m / 3 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      have h3s : 3 * s ≤ m := (Nat.le_div_iff_mul_le (by omega)).mp hsl |> fun h => by linarith
      have hps : p * s ≤ p * m / 3 := (Nat.le_div_iff_mul_le (by omega)).mpr (by nlinarith)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hps), dvd_mul_right p s⟩
    · intro a _ b _ h
      exact Nat.eq_of_mul_eq_mul_left hp.pos h
    · intro r hr
      rcases Finset.mem_filter.mp hr with ⟨hrr, ⟨s, rfl⟩⟩
      have hps : p * s ≤ p * m / 3 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hrr)
      have h3ps : 3 * (p * s) ≤ p * m := (Nat.le_div_iff_mul_le (by omega)).mp hps |> fun h => by linarith
      have h3s : 3 * s ≤ m := Nat.le_of_mul_le_mul_left (by nlinarith) hp.pos
      exact ⟨s, Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le (by omega)).mpr (by linarith))), rfl⟩
    · intro s _
      have hpodd : p % 2 = 1 := by
        rcases hp.eq_two_or_odd with h2 | h
        · omega
        · exact h
      have hsgn : (-1 : ℤ) ^ (p * s) = (-1 : ℤ) ^ s := by
        rw [pow_mul]
        have hneg1 : (-1 : ℤ) ^ p = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr hpodd)
        rw [hneg1]
      have hsub : p * m - 3 * (p * s) = p * (m - 3 * s) := by
        rw [show 3 * (p * s) = p * (3 * s) by ring, Nat.mul_sub_left_distrib]
      rw [hsgn, hN_eq, hsub]
  have hcong_div :
      (∑ s ∈ Finset.range (m / 3 + 1),
          (-1 : ℤ) ^ s * ((p * A).choose (p * s) : ℤ) *
            ((p * A + p * (m - 3 * s) - 1).choose (p * (m - 3 * s)) : ℤ)) ≡
        ∑ s ∈ Finset.range (m / 3 + 1),
          (-1 : ℤ) ^ s * (A.choose s : ℤ) * ((A + (m - 3 * s) - 1).choose (m - 3 * s) : ℤ)
          [ZMOD (p ^ (2 * k) : ℤ)] := by
    refine Int.ModEq.sum fun s _ => ?_
    have hc1 : ((p * A).choose (p * s) : ℤ) ≡ (A.choose s : ℤ) [ZMOD (p ^ (2 * k) : ℤ)] :=
      Int.natCast_modEq_iff.mpr (choose_mul_modEq hp hp5 hk hA_dvd)
    have hc2 : ((p * A + p * (m - 3 * s) - 1).choose (p * (m - 3 * s)) : ℤ) ≡
        ((A + (m - 3 * s) - 1).choose (m - 3 * s) : ℤ) [ZMOD (p ^ (2 * k) : ℤ)] :=
      Int.natCast_modEq_iff.mpr (choose_add_sub_one_modEq hp hp5 hk hApos hA_dvd)
    exact (Int.ModEq.refl _ |>.mul hc1).mul hc2
  rw [hdiv]
  simpa using hcong_div.add hcong_ndiv

end OeisA132303Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a132303.main := by
  intro p n k hp hp5 hn hk
  unfold OMA.S_oeis_a132303.a
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (2 * (n * p ^ k) + 1)) (fun j => p ∣ j)]
  have hndiv :
      p ^ (2 * k) ∣
        ∑ j ∈ (Finset.range (2 * (n * p ^ k) + 1)).filter (fun j => ¬ p ∣ j),
          OMA.S_oeis_a132303.trinomial (n * p ^ k) j ^ 3 := by
    apply Finset.dvd_sum
    intro j hj
    have hpj : ¬ p ∣ j := (Finset.mem_filter.mp hj).2
    have hpk : p ^ k ∣ OMA.S_oeis_a132303.trinomial (n * p ^ k) j :=
      OeisA132303Proof.dvd_trinomial_of_not_dvd hp hn hk hpj
    have h3k : p ^ (3 * k) ∣ OMA.S_oeis_a132303.trinomial (n * p ^ k) j ^ 3 := by
      simpa [← pow_mul, mul_comm k 3] using pow_dvd_pow_of_dvd hpk 3
    exact dvd_trans (pow_dvd_pow p (by omega)) h3k
  have hdiv :
      ∑ j ∈ (Finset.range (2 * (n * p ^ k) + 1)).filter (fun j => p ∣ j),
          OMA.S_oeis_a132303.trinomial (n * p ^ k) j ^ 3 =
        ∑ m ∈ Finset.range (2 * (n * p ^ (k - 1)) + 1),
          OMA.S_oeis_a132303.trinomial (n * p ^ k) (p * m) ^ 3 := by
    symm
    refine Finset.sum_bij (fun m _ => p * m) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro m hm
      have hmlt : m < 2 * (n * p ^ (k - 1)) + 1 := Finset.mem_range.mp hm
      have hk1 : n * p ^ k = p * (n * p ^ (k - 1)) := by
        have h : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
        nth_rw 1 [h, pow_succ]
        ring
      have hlt : p * m < 2 * (n * p ^ k) + 1 := by
        rw [hk1]
        nlinarith
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, dvd_mul_right p m⟩
    · intro a _ b _ h
      exact Nat.eq_of_mul_eq_mul_left hp.pos h
    · intro j hj
      rcases Finset.mem_filter.mp hj with ⟨hjr, ⟨m, rfl⟩⟩
      have hk1 : n * p ^ k = p * (n * p ^ (k - 1)) := by
        have h : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
        nth_rw 1 [h, pow_succ]
        ring
      have hpm : p * m ≤ 2 * (n * p ^ k) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjr)
      rw [hk1] at hpm
      have hm : m ≤ 2 * (n * p ^ (k - 1)) := Nat.le_of_mul_le_mul_left (by linarith) hp.pos
      exact ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_le hm), rfl⟩
  have hcong_div :
      (∑ m ∈ Finset.range (2 * (n * p ^ (k - 1)) + 1),
          OMA.S_oeis_a132303.trinomial (n * p ^ k) (p * m) ^ 3) ≡
        ∑ m ∈ Finset.range (2 * (n * p ^ (k - 1)) + 1),
          OMA.S_oeis_a132303.trinomial (n * p ^ (k - 1)) m ^ 3 [MOD p ^ (2 * k)] := by
    refine Nat.ModEq.sum fun m _ => ?_
    exact (OeisA132303Proof.trinomial_mul_modEq hp hp5 hn hk).pow 3
  have hcong_ndiv :
      (∑ j ∈ (Finset.range (2 * (n * p ^ k) + 1)).filter (fun j => ¬ p ∣ j),
          OMA.S_oeis_a132303.trinomial (n * p ^ k) j ^ 3) ≡ 0 [MOD p ^ (2 * k)] :=
    Nat.modEq_zero_iff_dvd.mpr hndiv
  rw [hdiv]
  simpa using hcong_div.add hcong_ndiv
