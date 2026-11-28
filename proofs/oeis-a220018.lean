import OMAStatements.S_oeis_a220018
import Mathlib


namespace OMA.A220018Proof
open OMA.S_oeis_a220018 Finset

def c (m r k : ℕ) : ℕ := 3 ^ k * r % m
def D (m r : ℕ) : ℕ := m / Nat.gcd m r
noncomputable def ord (d : ℕ) : ℕ := orderOf (3 : ZMod d)
noncomputable def s (m r : ℕ) : ℕ := ord (D m r)

lemma c_zero {m r : ℕ} (hr : r < m) : c m r 0 = r := by simp [c, Nat.mod_eq_of_lt hr]

lemma c_c (m r i j : ℕ) : c m (c m r i) j = c m r (i + j) := by
  unfold c; rw [Nat.mul_mod_mod, ← mul_assoc, ← pow_add, add_comm]

lemma c_lt {m : ℕ} (hm : 0 < m) (r k : ℕ) : c m r k < m := Nat.mod_lt _ hm

lemma step (m r j : ℕ) : 3 * c m r j % m = c m r (j+1) := by
  unfold c; rw [Nat.mul_mod_mod]; congr 1; ring

lemma ord_dvd_iff (d k : ℕ) : ord d ∣ k ↔ d ∣ 3 ^ k - 1 := by
  rw [ord, orderOf_dvd_iff_pow_eq_one, ← ZMod.natCast_eq_zero_iff,
    Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]
  push_cast
  rw [sub_eq_zero]

lemma c_eq_iff {m r : ℕ} (hm : 0 < m) (hr : r < m) (k : ℕ) :
    c m r k = r ↔ D m r ∣ 3 ^ k - 1 := by
  have hg : 0 < Nat.gcd m r := Nat.gcd_pos_of_pos_left _ hm
  have hcop := Nat.coprime_div_gcd_div_gcd hg
  have h1 : c m r k = r ↔ m ∣ 3 ^ k * r - r := by
    unfold c
    rw [← Nat.modEq_iff_dvd' (Nat.le_mul_of_pos_left r (Nat.one_le_pow _ _ (by norm_num)))]
    unfold Nat.ModEq; rw [Nat.mod_eq_of_lt hr]; exact eq_comm
  rw [h1]
  have hm' : m = Nat.gcd m r * (m / Nat.gcd m r) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_left m r)).symm
  have hr'' : r = Nat.gcd m r * (r / Nat.gcd m r) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_right m r)).symm
  have he : 3 ^ k * r - r = Nat.gcd m r * ((r / Nat.gcd m r) * (3 ^ k - 1)) := by
    rw [Nat.mul_sub_one, Nat.mul_sub, ← mul_assoc, ← hr'', mul_comm r]
  rw [he]
  nth_rewrite 1 [hm']
  rw [Nat.mul_dvd_mul_iff_left hg, hcop.dvd_mul_left]
  rfl

lemma D_dvd (m r : ℕ) : D m r ∣ m := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m r)

lemma s_props {m : ℕ} (r : ℕ) (hm : 0 < m) (h3 : Nat.Coprime 3 m) :
    0 < s m r ∧ s m r ≤ m := by
  have hDd : D m r ∣ m := D_dvd m r
  have hDpos : 0 < D m r := Nat.pos_of_dvd_of_pos hDd hm
  have hc : Nat.Coprime 3 (D m r) := Nat.Coprime.coprime_dvd_right hDd h3
  have he : D m r ∣ 3 ^ (D m r).totient - 1 := by
    have := Nat.ModEq.pow_totient hc
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).1 this.symm
  have hdvd : s m r ∣ (D m r).totient := (ord_dvd_iff _ _).2 he
  have htp : 0 < (D m r).totient := Nat.totient_pos.2 hDpos
  refine ⟨Nat.pos_of_dvd_of_pos hdvd htp, ?_⟩
  calc s m r ≤ (D m r).totient := Nat.le_of_dvd htp hdvd
    _ ≤ D m r := Nat.totient_le _
    _ ≤ m := Nat.le_of_dvd hm hDd

lemma c_iff_s {m r : ℕ} (hm : 0 < m) (hr : r < m) (k : ℕ) : c m r k = r ↔ s m r ∣ k := by
  rw [c_eq_iff hm hr, s, ord_dvd_iff]

lemma D_c {m : ℕ} (h3 : Nat.Coprime 3 m) (r k : ℕ) : D m (c m r k) = D m r := by
  unfold D c
  congr 1
  rw [Nat.gcd_comm, ← Nat.gcd_rec]
  exact Nat.Coprime.gcd_mul_left_cancel_right r (Nat.Coprime.pow_left k h3)

lemma s_c {m : ℕ} (h3 : Nat.Coprime 3 m) (r k : ℕ) : s m (c m r k) = s m r := by
  unfold s; rw [D_c h3]

lemma c_mod {m r : ℕ} (hm : 0 < m) (hr : r < m) (k : ℕ) : c m r k = c m r (k % s m r) := by
  conv_lhs => rw [← Nat.div_add_mod k (s m r)]
  rw [← c_c, (c_iff_s hm hr _).2 (dvd_mul_right _ _)]

lemma cancel {m r : ℕ} (h3 : Nat.Coprime 3 m) (hr : r < m) {i j : ℕ} (hij : i ≤ j)
    (h : c m r i = c m r j) : c m r (j - i) = r := by
  have hg : Nat.gcd m (3 ^ i) = 1 := Nat.Coprime.symm (Nat.Coprime.pow_left _ h3)
  have h' : 3 ^ i * r ≡ 3 ^ i * (3 ^ (j - i) * r) [MOD m] := by
    unfold Nat.ModEq; rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hij]; exact h
  have := Nat.ModEq.cancel_left_of_coprime hg h'
  unfold c; unfold Nat.ModEq at this; rw [← this, Nat.mod_eq_of_lt hr]

lemma c_symm {m r : ℕ} (hm : 0 < m) (h3 : Nat.Coprime 3 m) (hr : r < m) (k : ℕ) :
    c m (c m r k) (s m r * (k + 1) - k) = r := by
  have hs := (s_props r hm h3).1
  rw [c_c]
  have : k + (s m r * (k + 1) - k) = s m r * (k + 1) := by
    have : k ≤ s m r * (k + 1) := by nlinarith
    omega
  rw [this]
  exact (c_iff_s hm hr _).2 (dvd_mul_right _ _)

/-! orbitMin -/

lemma om_le (m r f x : ℕ) : orbitMin m r f x ≤ x := by
  cases f with
  | zero => simp [orbitMin]
  | succ f =>
    simp only [orbitMin]
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _

lemma om_ge {m r : ℕ} (hm : 0 < m) (hr : r < m) (h3 : Nat.Coprime 3 m) (t : ℕ) :
    ∀ f j, j < s m r → s m r ≤ j + f →
      (t ≤ orbitMin m r f (c m r j) ↔ ∀ i, j ≤ i → i < s m r → t ≤ c m r i) := by
  intro f
  induction f with
  | zero => intro j hj hjf; omega
  | succ f ih =>
    intro j hj hjf
    simp only [orbitMin]
    rw [step]
    by_cases hj1 : j + 1 = s m r
    · have : c m r (j+1) = r := (c_iff_s hm hr _).2 (hj1 ▸ dvd_refl _)
      rw [if_pos this]
      constructor
      · intro h i hi1 hi2
        have : i = j := by omega
        subst this; exact h
      · intro h; exact h j le_rfl hj
    · have hne : c m r (j+1) ≠ r := by
        intro h
        have := (c_iff_s hm hr _).1 h
        have := Nat.le_of_dvd (by omega) this
        omega
      rw [if_neg hne, le_min_iff, ih (j+1) (by omega) (by omega)]
      constructor
      · rintro ⟨h1, h2⟩ i hi1 hi2
        rcases Nat.eq_or_lt_of_le hi1 with h | h
        · subst h; exact h1
        · exact h2 i h hi2
      · intro h; exact ⟨h j le_rfl hj, fun i hi1 hi2 => h i (by omega) hi2⟩

def Good (m r : ℕ) : Prop := ∀ i, r ≤ c m r i

lemma om_iff {m r : ℕ} (hm : 0 < m) (hr : r < m) (h3 : Nat.Coprime 3 m) :
    orbitMin m r m r = r ↔ Good m r := by
  obtain ⟨hs0, hsm⟩ := s_props r hm h3
  have h := om_ge hm hr h3 r m 0 hs0 (by omega)
  rw [c_zero hr] at h
  constructor
  · intro he i
    have h2 := h.1 (le_of_eq he.symm)
    rw [c_mod hm hr]
    exact h2 _ (Nat.zero_le _) (Nat.mod_lt _ hs0)
  · intro hi
    exact le_antisymm (om_le _ _ _ _) (h.2 (fun i _ _ => hi i))

/-! orbits -/

noncomputable def O (m r : ℕ) : Finset ℕ := (range (s m r)).image (c m r)

lemma mem_O {m r : ℕ} (hm : 0 < m) (hr : r < m) (h3 : Nat.Coprime 3 m) (x : ℕ) :
    x ∈ O m r ↔ ∃ k, c m r k = x := by
  unfold O
  rw [mem_image]
  constructor
  · rintro ⟨k, _, hk⟩; exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k % s m r, mem_range.2 (Nat.mod_lt _ (s_props r hm h3).1), by rw [← c_mod hm hr, hk]⟩

lemma card_O {m r : ℕ} (hm : 0 < m) (hr : r < m) (h3 : Nat.Coprime 3 m) :
    (O m r).card = s m r := by
  unfold O
  rw [card_image_of_injOn, card_range]
  intro i hi j hj hij
  simp only [coe_range, Set.mem_Iio] at hi hj
  rcases le_total i j with h | h
  · have := (c_iff_s hm hr _).1 (cancel h3 hr h hij)
    have := Nat.eq_zero_of_dvd_of_lt this (by omega)
    omega
  · have := (c_iff_s hm hr _).1 (cancel h3 hr h hij.symm)
    have := Nat.eq_zero_of_dvd_of_lt this (by omega)
    omega

lemma O_eq {m r : ℕ} (hm : 0 < m) (hr : r < m) (h3 : Nat.Coprime 3 m) (k : ℕ) :
    O m (c m r k) = O m r := by
  ext x
  rw [mem_O hm (c_lt hm r k) h3, mem_O hm hr h3]
  constructor
  · rintro ⟨j, hj⟩; exact ⟨k + j, by rw [← c_c, hj]⟩
  · rintro ⟨j, hj⟩
    refine ⟨(s m r * (k + 1) - k) + j, ?_⟩
    rw [← c_c, c_symm hm h3 hr, hj]

lemma O_nonempty {m r : ℕ} (hm : 0 < m) (hr : r < m) (h3 : Nat.Coprime 3 m) :
    (O m r).Nonempty := ⟨r, (mem_O hm hr h3 r).2 ⟨0, c_zero hr⟩⟩

noncomputable def pi (m r : ℕ) : ℕ := if h : (O m r).Nonempty then (O m r).min' h else 0

lemma pi_mem {m r : ℕ} (hm : 0 < m) (hr : r < m) (h3 : Nat.Coprime 3 m) :
    ∃ i, c m r i = pi m r := by
  unfold pi
  rw [dif_pos (O_nonempty hm hr h3)]
  exact (mem_O hm hr h3 _).1 (min'_mem _ _)

lemma pi_le {m r : ℕ} (hm : 0 < m) (hr : r < m) (h3 : Nat.Coprime 3 m) (k : ℕ) :
    pi m r ≤ c m r k := by
  unfold pi
  rw [dif_pos (O_nonempty hm hr h3)]
  exact min'_le _ _ ((mem_O hm hr h3 _).2 ⟨k, rfl⟩)

lemma pi_c {m r : ℕ} (hm : 0 < m) (hr : r < m) (h3 : Nat.Coprime 3 m) (k : ℕ) :
    pi m (c m r k) = pi m r := by
  unfold pi; rw [O_eq hm hr h3]

lemma pi_good {m r : ℕ} (hm : 0 < m) (hr : r < m) (h3 : Nat.Coprime 3 m) :
    Good m (pi m r) := by
  obtain ⟨i, hi⟩ := pi_mem hm hr h3
  intro k
  calc pi m r ≤ c m r (i + k) := pi_le hm hr h3 _
    _ = c m (pi m r) k := by rw [← hi, c_c]

lemma pi_of_good {m μ : ℕ} (hm : 0 < m) (hμ : μ < m) (h3 : Nat.Coprime 3 m) (hg : Good m μ) :
    pi m μ = μ := by
  apply le_antisymm
  · have := pi_le hm hμ h3 0; rwa [c_zero hμ] at this
  · obtain ⟨i, hi⟩ := pi_mem hm hμ h3
    rw [← hi]; exact hg i

lemma fiber_eq {m μ : ℕ} (hm : 0 < m) (hμ : μ < m) (h3 : Nat.Coprime 3 m) (hg : Good m μ) :
    (range m).filter (fun r => pi m r = μ) = O m μ := by
  ext r
  rw [mem_filter, mem_range]
  constructor
  · rintro ⟨hr, hp⟩
    obtain ⟨i, hi⟩ := pi_mem hm hr h3
    rw [hp] at hi
    rw [mem_O hm hμ h3]
    refine ⟨s m r * (i + 1) - i, ?_⟩
    rw [← hi, c_symm hm h3 hr]
  · intro h
    obtain ⟨k, hk⟩ := (mem_O hm hμ h3 r).1 h
    subst hk
    exact ⟨c_lt hm _ _, by rw [pi_c hm hμ h3, pi_of_good hm hμ h3 hg]⟩

lemma count_eq_sum {m : ℕ} (hm : 0 < m) (h3 : Nat.Coprime 3 m) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ r < m, P r ↔ Good m r) :
    (((range m).filter P).card : ℚ) = ∑ r ∈ range m, (1 : ℚ) / s m r := by
  rw [← sum_fiberwise_of_maps_to (g := pi m) (t := (range m).filter P)]
  · rw [card_eq_sum_ones, Nat.cast_sum]
    apply sum_congr rfl
    intro μ hμ
    rw [mem_filter, mem_range] at hμ
    have hg := (hP μ hμ.1).1 hμ.2
    rw [fiber_eq hm hμ.1 h3 hg]
    have : ∀ r ∈ O m μ, (1 : ℚ) / s m r = 1 / s m μ := by
      intro r hr
      obtain ⟨k, hk⟩ := (mem_O hm hμ.1 h3 r).1 hr
      rw [← hk, s_c h3]
    rw [sum_congr rfl this, sum_const, card_O hm hμ.1 h3, nsmul_eq_mul]
    have := (s_props μ hm h3).1
    field_simp
    simp
  · intro r hr
    rw [mem_range] at hr
    rw [mem_filter, mem_range]
    obtain ⟨i, hi⟩ := pi_mem hm hr h3
    refine ⟨?_, (hP _ ?_).2 (pi_good hm hr h3)⟩
    · rw [← hi]; exact c_lt hm _ _
    · rw [← hi]; exact c_lt hm _ _

lemma sum_eq_divisors {m : ℕ} (hm : 0 < m) :
    ∑ r ∈ range m, (1 : ℚ) / s m r = ∑ d ∈ m.divisors, (d.totient : ℚ) / ord d := by
  rw [← sum_fiberwise_of_maps_to (g := fun r => Nat.gcd m r) (t := m.divisors)]
  · rw [← Nat.sum_div_divisors m (fun d => (d.totient : ℚ) / ord d)]
    apply sum_congr rfl
    intro g hg
    have hgd : g ∣ m := Nat.dvd_of_mem_divisors hg
    have : ∀ r ∈ (range m).filter (fun r => Nat.gcd m r = g), (1 : ℚ) / s m r = 1 / ord (m / g) := by
      intro r hr
      rw [mem_filter] at hr
      simp only [s, D, hr.2]
    rw [sum_congr rfl this, sum_const, ← Nat.totient_div_of_dvd hgd, nsmul_eq_mul]
    ring
  · intro r _
    exact Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left m r, by omega⟩

/-! orders -/

def o2 (i : ℕ) : ℕ := if i ≤ 1 then 1 else if i = 2 then 2 else 2 ^ (i - 2)
def o5 (j : ℕ) : ℕ := if j = 0 then 1 else 4 * 5 ^ (j - 1)
def ordv (i j : ℕ) : ℕ :=
  if j = 0 then o2 i else (if i ≤ 3 then 4 else 2 ^ (i - 2)) * 5 ^ (j - 1)

lemma pow3_mod4 (k : ℕ) : 3 ^ k % 4 = if k % 2 = 0 then 1 else 3 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    split_ifs at ih ⊢ <;> omega

lemma pow3_mod5 (k : ℕ) : (k % 4 = 0 ∧ 3^k % 5 = 1) ∨ (k % 4 = 1 ∧ 3^k % 5 = 3) ∨
    (k % 4 = 2 ∧ 3^k % 5 = 4) ∨ (k % 4 = 3 ∧ 3^k % 5 = 2) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

lemma dvd4 (k : ℕ) : 4 ∣ 3 ^ k - 1 ↔ 2 ∣ k := by
  have h1 := pow3_mod4 k
  have h2 : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
  split_ifs at h1 <;> omega

lemma dvd5 (k : ℕ) : 5 ∣ 3 ^ k - 1 ↔ 4 ∣ k := by
  have h1 := pow3_mod5 k
  have h2 : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
  omega

lemma v2_eq (k : ℕ) (hk : k ≠ 0) (he : Even k) :
    padicValNat 2 (3 ^ k - 1) = padicValNat 2 k + 2 := by
  have := padicValNat.pow_two_sub_one (x := 3) (n := k) (by norm_num) (by norm_num) hk he
  have h4 : padicValNat 2 (3 + 1) = 2 := by
    rw [show 3 + 1 = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  have h2 : padicValNat 2 (3 - 1) = 1 := by
    rw [show 3 - 1 = 2 by norm_num]; exact padicValNat_self
  omega

lemma char2 (i k : ℕ) : 2 ^ i ∣ 3 ^ k - 1 ↔ o2 i ∣ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rcases (show i ≤ 1 ∨ i = 2 ∨ 3 ≤ i by omega) with hi | hi | hi
  · simp only [o2, if_pos hi, one_dvd, iff_true]
    have h1 := pow3_mod4 k
    interval_cases i
    · simp
    · have h2 : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
      simp only [pow_one]
      split_ifs at h1 <;> omega
  · subst hi; simp only [o2]; norm_num; exact dvd4 k
  · obtain ⟨t, rfl⟩ : ∃ t, i = t + 3 := ⟨i - 3, by omega⟩
    simp only [o2, show ¬ (t + 3 ≤ 1) by omega, show t + 3 ≠ 2 by omega, if_false,
      show t + 3 - 2 = t + 1 by omega]
    have hX : 3 ^ k - 1 ≠ 0 := by
      have : 3 ≤ 3 ^ k := by
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      omega
    by_cases he : Even k
    · rw [padicValNat_dvd_iff_le hX, padicValNat_dvd_iff_le (by omega), v2_eq k (by omega) he]
      omega
    · have hodd : ¬ 2 ∣ k := by rwa [even_iff_two_dvd] at he
      have h4 : 4 ∣ 2 ^ (t + 3) := ⟨2 ^ t * 2, by ring⟩
      constructor
      · intro h
        exact absurd ((dvd4 k).1 (dvd_trans h4 h)) hodd
      · intro h
        exact absurd (dvd_trans (dvd_pow_self 2 (by omega)) h) hodd

lemma v5_eq (q : ℕ) (hq : q ≠ 0) : padicValNat 5 (81 ^ q - 1) = padicValNat 5 q + 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have := padicValNat.pow_sub_pow (p := 5) (x := 81) (y := 1) ⟨2, rfl⟩ (by norm_num)
    (by norm_num) (by norm_num) hq
  rw [one_pow] at this
  rw [this]
  have : padicValNat 5 (81 - 1) = 1 := by
    rw [show 81 - 1 = 5 * 16 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat_self, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  omega

lemma char5 (j k : ℕ) : 5 ^ j ∣ 3 ^ k - 1 ↔ o5 j ∣ k := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [o5]
  obtain ⟨l, rfl⟩ : ∃ l, j = l + 1 := ⟨j - 1, by omega⟩
  simp only [o5, show l + 1 ≠ 0 by omega, if_false, Nat.add_sub_cancel]
  by_cases h4 : 4 ∣ k
  · obtain ⟨q, rfl⟩ := h4
    have hq : q ≠ 0 := by omega
    have hpow : 3 ^ (4 * q) = 81 ^ q := by rw [pow_mul]; norm_num
    have hX : 81 ^ q - 1 ≠ 0 := by
      have : 81 ≤ 81 ^ q := by
        calc 81 = 81 ^ 1 := by norm_num
          _ ≤ 81 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hpow, padicValNat_dvd_iff_le hX, v5_eq q hq, Nat.mul_dvd_mul_iff_left (by norm_num),
      padicValNat_dvd_iff_le hq]
    omega
  · constructor
    · intro h
      exact absurd ((dvd5 k).1 (dvd_trans (dvd_pow_self 5 (by omega)) h)) h4
    · intro h
      exact absurd (dvd_trans (dvd_mul_right 4 _) h) h4

lemma cop_dvd_iff {x y k : ℕ} (h : Nat.Coprime x y) : x * y ∣ k ↔ x ∣ k ∧ y ∣ k :=
  ⟨fun hk => ⟨dvd_trans (dvd_mul_right _ _) hk, dvd_trans (dvd_mul_left _ _) hk⟩,
   fun ⟨h1, h2⟩ => h.mul_dvd_of_dvd_of_dvd h1 h2⟩

lemma charv (i j k : ℕ) : 2 ^ i * 5 ^ j ∣ 3 ^ k - 1 ↔ ordv i j ∣ k := by
  have hc : Nat.Coprime (2 ^ i) (5 ^ j) := Nat.Coprime.pow _ _ (by norm_num)
  rw [cop_dvd_iff hc, char2, char5]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [o5, ordv]
  obtain ⟨l, rfl⟩ : ∃ l, j = l + 1 := ⟨j - 1, by omega⟩
  simp only [o5, ordv, show l + 1 ≠ 0 by omega, if_false, Nat.add_sub_cancel]
  rw [cop_dvd_iff (Nat.Coprime.pow_right _ (by norm_num : Nat.Coprime 4 5))]
  by_cases hi : i ≤ 3
  · rw [if_pos hi, cop_dvd_iff (Nat.Coprime.pow_right _ (by norm_num : Nat.Coprime 4 5))]
    have : o2 i ∣ 4 := by interval_cases i <;> decide
    constructor
    · rintro ⟨_, h4, h5⟩; exact ⟨h4, h5⟩
    · rintro ⟨h4, h5⟩; exact ⟨dvd_trans this h4, h4, h5⟩
  · rw [if_neg hi, cop_dvd_iff (Nat.Coprime.pow _ _ (by norm_num : Nat.Coprime 2 5))]
    have ho : o2 i = 2 ^ (i - 2) := by
      unfold o2; rw [if_neg (by omega), if_neg (by omega)]
    rw [ho]
    have : 4 ∣ 2 ^ (i - 2) := by
      obtain ⟨t, rfl⟩ : ∃ t, i = t + 4 := ⟨i - 4, by omega⟩
      rw [show t + 4 - 2 = t + 2 by omega]
      exact ⟨2 ^ t, by ring⟩
    constructor
    · rintro ⟨h2, _, h5⟩; exact ⟨h2, h5⟩
    · rintro ⟨h2, h5⟩; exact ⟨h2, dvd_trans this h2, h5⟩

lemma ord_val (i j : ℕ) : ord (2 ^ i * 5 ^ j) = ordv i j :=
  Nat.dvd_antisymm ((ord_dvd_iff _ _).2 ((charv _ _ _).2 dvd_rfl))
    ((charv _ _ _).1 ((ord_dvd_iff _ _).1 dvd_rfl))

def tv (i j : ℕ) : ℚ := if j = 0 then (if i ≤ 2 then 1 else 2) else
  (if i = 0 then 1 else if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 4 else 8)

lemma phi2 (t : ℕ) : (2 ^ (t+1)).totient = 2 ^ t := by
  rw [Nat.totient_prime_pow_succ Nat.prime_two]; simp

lemma phi5 (l : ℕ) : (5 ^ (l+1)).totient = 5 ^ l * 4 := by
  rw [Nat.totient_prime_pow_succ (by norm_num)]

lemma term_val (i j : ℕ) :
    ((2 ^ i * 5 ^ j).totient : ℚ) / ord (2 ^ i * 5 ^ j) = tv i j := by
  rw [ord_val, Nat.totient_mul (Nat.Coprime.pow _ _ (by norm_num))]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero, Nat.totient_one, mul_one]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [ordv, o2, tv]
    obtain ⟨t, rfl⟩ : ∃ t, i = t + 1 := ⟨i - 1, by omega⟩
    rw [phi2]
    rcases (show t = 0 ∨ t = 1 ∨ 2 ≤ t by omega) with h | h | h
    · subst h; simp [ordv, o2, tv]
    · subst h; norm_num [ordv, o2, tv]
    · obtain ⟨u, rfl⟩ : ∃ u, t = u + 2 := ⟨t - 2, by omega⟩
      have h1 : ordv (u + 2 + 1) 0 = 2 ^ (u + 1) := by
        unfold ordv o2; rw [if_pos rfl, if_neg (by omega), if_neg (by omega)]; congr 1
      have h2 : tv (u + 2 + 1) 0 = 2 := by unfold tv; rw [if_pos rfl, if_neg (by omega)]
      rw [h1, h2]; push_cast; rw [pow_succ 2 (u+1)]; field_simp
  · obtain ⟨l, rfl⟩ : ∃ l, j = l + 1 := ⟨j - 1, by omega⟩
    rw [phi5]
    have hv : ordv i (l+1) = (if i ≤ 3 then 4 else 2 ^ (i - 2)) * 5 ^ l := by
      unfold ordv; rw [if_neg (by omega)]; rfl
    rw [hv]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [tv]; field_simp
    obtain ⟨t, rfl⟩ : ∃ t, i = t + 1 := ⟨i - 1, by omega⟩
    rw [phi2]
    rcases (show t ≤ 2 ∨ 3 ≤ t by omega) with h | h
    · interval_cases t <;> simp [tv] <;> field_simp <;> ring
    · obtain ⟨u, rfl⟩ : ∃ u, t = u + 3 := ⟨t - 3, by omega⟩
      have h2 : tv (u + 3 + 1) (l + 1) = 8 := by
        unfold tv; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [if_neg (by omega), h2, show u + 3 + 1 - 2 = u + 2 by omega]
      push_cast; rw [pow_succ 2 (u+2)]; field_simp; ring

/-! divisor sum -/

lemma v2_of (i j : ℕ) : padicValNat 2 (2 ^ i * 5 ^ j) = i := by
  rw [padicValNat.mul (by positivity) (by positivity), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd]
  · simp
  · intro h; have := (Nat.prime_two.dvd_of_dvd_pow h); norm_num at this

lemma v5_of (i j : ℕ) : padicValNat 5 (2 ^ i * 5 ^ j) = j := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [padicValNat.mul (by positivity) (by positivity), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd]
  · simp
  · intro h; have := ((Fact.out : Nat.Prime 5).dvd_of_dvd_pow h); norm_num at this

lemma ten_pow (n : ℕ) : (10 : ℕ) ^ n = 2 ^ n * 5 ^ n := by rw [← mul_pow]; norm_num

lemma divisors_sum (n : ℕ) (F : ℕ → ℚ) :
    ∑ d ∈ (10 ^ n).divisors, F d =
      ∑ i ∈ range (n+1), ∑ j ∈ range (n+1), F (2 ^ i * 5 ^ j) := by
  rw [show (∑ i ∈ range (n+1), ∑ j ∈ range (n+1), F (2 ^ i * 5 ^ j)) =
    ∑ p ∈ range (n+1) ×ˢ range (n+1), F (2 ^ p.1 * 5 ^ p.2) from
      (Finset.sum_product' _ _ _).symm]
  symm
  apply sum_bij (fun p _ => 2 ^ p.1 * 5 ^ p.2)
  · intro p hp
    rw [mem_product, mem_range, mem_range] at hp
    rw [Nat.mem_divisors]
    refine ⟨?_, by positivity⟩
    rw [ten_pow]
    exact mul_dvd_mul (pow_dvd_pow 2 (by omega)) (pow_dvd_pow 5 (by omega))
  · intro p _ q _ h
    have h1 := congrArg (padicValNat 2) h
    have h2 := congrArg (padicValNat 5) h
    simp only [v2_of] at h1
    simp only [v5_of] at h2
    exact Prod.ext h1 h2
  · intro d hd
    rw [Nat.mem_divisors, ten_pow] at hd
    obtain ⟨d1, d2, h1, h2, rfl⟩ := Nat.dvd_mul.1 hd.1
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow (by norm_num)).1 h2
    exact ⟨(i, j), by simp only [mem_product, mem_range]; omega, rfl⟩
  · intro p hp; rfl

lemma sum0 (k : ℕ) : ∑ i ∈ range (k + 3 + 1), tv i 0 = 2 * k + 5 := by
  induction k with
  | zero => simp [sum_range_succ, tv]; norm_num
  | succ k ih =>
    rw [show k + 1 + 3 + 1 = (k + 3 + 1) + 1 by ring, sum_range_succ, ih]
    have : tv (k + 3 + 1) 0 = 2 := by unfold tv; rw [if_pos rfl, if_neg (by omega)]
    rw [this]; push_cast; ring

lemma sum1 (k l : ℕ) : ∑ i ∈ range (k + 3 + 1), tv i (l + 1) = 8 * k + 8 := by
  induction k with
  | zero => simp [sum_range_succ, tv]; norm_num
  | succ k ih =>
    rw [show k + 1 + 3 + 1 = (k + 3 + 1) + 1 by ring, sum_range_succ, ih]
    have : tv (k + 3 + 1) (l + 1) = 8 := by
      unfold tv; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [this]; push_cast; ring

lemma total (k : ℕ) : ∑ i ∈ range (k + 3 + 1), ∑ j ∈ range (k + 3 + 1), tv i j =
    8 * ((k:ℚ) + 3) ^ 2 - 14 * ((k:ℚ) + 3) - 1 := by
  rw [sum_comm, sum_range_succ']
  have : ∀ j ∈ range (k + 3), ∑ i ∈ range (k + 3 + 1), tv i (j + 1) = 8 * k + 8 :=
    fun j _ => sum1 k j
  rw [sum_congr rfl this, sum0 k, sum_const, card_range, nsmul_eq_mul]
  push_cast; ring

theorem closed (n : ℕ) (hn : 2 < n) : (a n : ℚ) = 8 * (n : ℚ) ^ 2 - 14 * n - 1 := by
  have hm : 0 < 10 ^ n := by positivity
  have h3 : Nat.Coprime 3 (10 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
  have ha : a n = ((range (10 ^ n)).filter (fun r => orbitMin (10 ^ n) r (10 ^ n) r = r)).card :=
    rfl
  rw [ha, count_eq_sum hm h3 _ (fun r hr => om_iff hm hr h3), sum_eq_divisors hm, divisors_sum]
  simp only [term_val]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [total]; push_cast; ring

theorem main_proof :
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 8 * (n : ℤ) ^ 2 - 14 * (n : ℤ) - 1) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) =
      3 * (a (n - 1) : ℤ) - 3 * (a (n - 2) : ℤ) + (a (n - 3) : ℤ)) := by
  have hc : ∀ n : ℕ, 2 < n → (a n : ℤ) = 8 * (n : ℤ) ^ 2 - 14 * (n : ℤ) - 1 := by
    intro n hn
    have := closed n hn
    exact_mod_cast this
  refine ⟨hc, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  rw [hc _ (by omega), hc (k + 6 - 1) (by omega), hc (k + 6 - 2) (by omega),
    hc (k + 6 - 3) (by omega)]
  rw [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
    show k + 6 - 3 = k + 3 by omega]
  push_cast; ring

end OMA.A220018Proof


open OMA.A220018Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a220018.main := main_proof
