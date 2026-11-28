import OMAStatements.S_mse_3286093
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
Normalize the two representations to nested pairs. Comparison of the two
individual powers forces the outer exponent to be the next integer above
the base-a logarithm of the inner leading power. The two smaller inputs
must be multiplicatively independent. A two-adic descent shows that a diagonal
inner pair forces both outer inputs to be odd. The remaining cases concern a diagonal
inner pair and a strictly increasing inner pair.
-/

namespace OMA.R_mse_3286093_R1

open OMA.S_mse_3286093

/-- An inner diagonal pair cannot coincide with an odd forced outer pair. -/
def H1 : Prop :=
  ∀ a m : ℕ, 2 ≤ a → a < m → Odd a → Odd (Nat.log a (m ^ m) + 1) →
    (∀ k l : ℕ, k ≠ 0 ∨ l ≠ 0 → a ^ k ≠ m ^ l) →
    L a (Nat.log a (m ^ m) + 1) ≠ L m m

/-- A strictly increasing inner pair cannot coincide with the forced outer candidate. -/
def H2 : Prop :=
  ∀ a m n : ℕ, 2 ≤ a → a < m → m < n →
    (∀ k l : ℕ, k ≠ 0 ∨ l ≠ 0 → a ^ k ≠ m ^ l) →
    L a (Nat.log a (m ^ n) + 1) ≠ L m n

section Assembly

-- For 1 < x < y, the tangent to log at x gives x * log(y/x) < y-x.
private theorem tangent (x y : ℝ) (hx : 0 < x) (hxy : x < y) :
    x * (Real.log y - Real.log x) < y - x := by
  have hy := hx.trans hxy
  have h := Real.log_lt_sub_one_of_pos (div_pos hy hx)
    (ne_of_gt ((one_lt_div hx).2 hxy))
  rw [Real.log_div hy.ne' hx.ne'] at h
  have h' := mul_lt_mul_of_pos_left h hx
  calc
    x * (Real.log y - Real.log x) < x * (y / x - 1) := h'
    _ = y - x := by field_simp

private theorem log_bound (a b m n : ℕ) (ha : 2 ≤ a) (hn : 2 ≤ n)
    (ham : a < m) (hnb : n < b) (hp : a ^ b ≤ m ^ n) (hq : n ^ m ≤ b ^ a) :
    Real.log a * Real.log n < 1 := by
  have ha' : 0 < (a : ℝ) := by positivity
  have hn' : 0 < (n : ℝ) := by positivity
  have ham' : (a : ℝ) < m := by exact_mod_cast ham
  have hnb' : (n : ℝ) < b := by exact_mod_cast hnb
  have hp' : (a : ℝ) ^ b ≤ (m : ℝ) ^ n := by exact_mod_cast hp
  have hq' : (n : ℝ) ^ m ≤ (b : ℝ) ^ a := by exact_mod_cast hq
  have hpl := Real.log_le_log (pow_pos ha' _) hp'
  have hql := Real.log_le_log (pow_pos hn' _) hq'
  rw [Real.log_pow, Real.log_pow] at hpl hql
  have h₁ : a * ((b : ℝ) - n) * Real.log a < n * ((m : ℝ) - a) := by
    have hl := mul_lt_mul_of_pos_left (tangent a m ha' ham') hn'
    have hr := mul_le_mul_of_nonneg_left hpl ha'.le
    linarith
  have h₂ : n * ((m : ℝ) - a) * Real.log n < a * ((b : ℝ) - n) := by
    have hl := mul_lt_mul_of_pos_left (tangent n b hn' hnb') ha'
    have hr := mul_le_mul_of_nonneg_left hql hn'.le
    linarith
  have hloga : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hprod := mul_lt_mul_of_pos_right h₁ hlogn
  have hfactor : 0 < (a : ℝ) * ((b : ℝ) - n) := mul_pos ha' (sub_pos.mpr hnb')
  apply (mul_lt_mul_iff_right₀ hfactor).mp
  linarith [hprod.trans h₂]

private theorem small_table :
    ∀ (a m n : Fin 8) (b : Fin 21),
      2 ≤ a.val → a.val < m.val → m.val ≤ n.val → n.val < b.val →
      a.val ^ b.val ≤ m.val ^ n.val → n.val ^ m.val ≤ b.val ^ a.val → False := by
  decide +kernel

/-- On strictly nested pairs, the outer pair cannot have both its first
power at most the inner first power and its second power at least the inner
second power. -/
private theorem not_reverse_dominance (a b m n : ℕ) (ha : 2 ≤ a)
    (ham : a < m) (hmn : m ≤ n) (hnb : n < b)
    (hp : a ^ b ≤ m ^ n) (hq : n ^ m ≤ b ^ a) : False := by
  by_cases hn : 8 ≤ n
  · have bound := log_bound a b m n ha (by omega) ham hnb hp hq
    have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      convert Real.log_pow (2 : ℝ) 3 using 1 <;> norm_num
    have hla := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
        (show (2 : ℝ) ≤ a by exact_mod_cast ha)
    have hln := Real.log_le_log (by norm_num : (0 : ℝ) < 8)
        (show (8 : ℝ) ≤ n by exact_mod_cast hn)
    rw [h8] at hln
    have hl2 := Real.log_two_gt_d9
    have ha₁ : (2 : ℝ) / 3 < Real.log (a : ℝ) := by linarith
    have hn₁ : (2 : ℝ) < Real.log (n : ℝ) := by linarith
    nlinarith [mul_lt_mul_of_pos_right ha₁ (show 0 < Real.log (n : ℝ) by linarith)]
  · have hb : b < 21 := by
      by_contra! hb
      have h1 := Nat.pow_le_pow_right (show 0 < 2 by decide) hb
      have h2 := Nat.pow_le_pow_left ha b
      have h3 := Nat.pow_le_pow_left (show m ≤ 7 by omega) n
      have h4 := Nat.pow_le_pow_right (show 0 < 7 by decide) (show n ≤ 7 by omega)
      omega
    exact small_table ⟨a, by omega⟩ ⟨m, by omega⟩ ⟨n, by omega⟩ ⟨b, hb⟩ ha ham hmn hnb hp hq

private theorem collision_term_order (a b m n : ℕ) (ha : 2 ≤ a)
    (ham : a < m) (hmn : m ≤ n) (hnb : n < b)
    (heq : a ^ b + b ^ a = m ^ n + n ^ m) :
    m ^ n < a ^ b ∧ b ^ a < n ^ m := by
  have hmain : m ^ n < a ^ b := by
    by_contra! hp
    exact not_reverse_dominance a b m n ha ham hmn hnb hp (by omega)
  omega

private theorem inner_power_order (m n : ℕ) (hm : 3 ≤ m) (hmn : m ≤ n) :
    n ^ m ≤ m ^ n := by
  have hm' : 3 ≤ (m : ℝ) := by exact_mod_cast hm
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have he : Real.exp 1 ≤ (m : ℝ) := by linarith [Real.exp_one_lt_d9]
  have h := Real.log_div_self_antitoneOn (a := (m : ℝ)) (b := (n : ℝ)) he (he.trans hmn') hmn'
  have hlog := (div_le_div_iff₀ (by linarith : 0 < (n : ℝ)) (by linarith : 0 < (m : ℝ))).mp h
  have hp : (n : ℝ) ^ m ≤ (m : ℝ) ^ n := by
    apply (Real.log_le_log_iff (pow_pos (by linarith) _) (pow_pos (by linarith) _)).mp
    rw [Real.log_pow, Real.log_pow]
    linarith
  exact_mod_cast hp

/-- Three entries pin down the fourth by an exact integer logarithm. -/
private theorem collision_forced_exponent (a b m n : ℕ) (ha : 2 ≤ a)
    (ham : a < m) (hmn : m ≤ n) (hnb : n < b)
    (heq : OMA.S_mse_3286093.L a b = OMA.S_mse_3286093.L m n) :
    b = Nat.log a (m ^ n) + 1 := by
  change a ^ b + b ^ a = m ^ n + n ^ m at heq
  have h1 := (collision_term_order a b m n ha ham hmn hnb heq).1
  have h2 := inner_power_order m n (by omega) hmn
  have hpos : 0 < b ^ a := Nat.pow_pos (by omega)
  have h3 : a ^ b < (m ^ n) * a :=
    calc
      a ^ b < (m ^ n) * 2 := by omega
      _ ≤ (m ^ n) * a := Nat.mul_le_mul_left _ ha
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show b ≠ 0 by omega)
  rw [pow_succ] at h3
  have hk : a ^ k < m ^ n := Nat.lt_of_mul_lt_mul_right h3
  rw [Nat.log_eq_of_pow_le_of_lt_pow hk.le h1]

/-- In every hypothetical collision of distinct sorted pairs, the two smaller
entries are multiplicatively independent. The larger entries have no
factorization restrictions. -/
private theorem collision_smaller_independent (a b m n : ℕ) (ha : 2 ≤ a)
    (ham : a < m) (hmn : m ≤ n) (hnb : n < b)
    (heq : OMA.S_mse_3286093.L a b = OMA.S_mse_3286093.L m n) :
    ∀ k l : ℕ, k ≠ 0 ∨ l ≠ 0 → a ^ k ≠ m ^ l := by
  intro k l hkl hpow
  change a ^ b + b ^ a = m ^ n + n ^ m at heq
  have h1 := (collision_term_order a b m n ha ham hmn hnb heq).1
  have h2 := inner_power_order m n (by omega) hmn
  have hpos : 0 < b ^ a := Nat.pow_pos (by omega)
  obtain ⟨B, haB, hmB⟩ := Nat.exists_eq_pow_of_pow_eq_pow hkl hpow
  let r := l / Nat.gcd k l
  let u := k / Nat.gcd k l
  change a = B ^ r at haB
  change m = B ^ u at hmB
  have hB : 2 ≤ B := by
    by_contra! hsmall
    have hle := Nat.pow_le_pow_left (show B ≤ 1 by omega) r
    simp only [one_pow] at hle
    omega
  have h1' : B ^ (u * n) < B ^ (r * b) := by simpa only [haB, hmB, pow_mul] using h1
  have hex : u * n < r * b := by
    by_contra! hle
    exact (not_lt_of_ge (Nat.pow_le_pow_right (by omega : 0 < B) hle)) h1'
  have h3 : 2 * m ^ n ≤ a ^ b := by
    calc
      2 * m ^ n ≤ B * m ^ n := Nat.mul_le_mul_right _ hB
      _ = B ^ (u * n + 1) := by rw [hmB, pow_succ, pow_mul, Nat.mul_comm]
      _ ≤ B ^ (r * b) := Nat.pow_le_pow_right (by omega) hex
      _ = a ^ b := by rw [haB, pow_mul]
  omega


private theorem val_add_min {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hne : padicValNat 2 x ≠ padicValNat 2 y) :
    padicValNat 2 (x+y) = min (padicValNat 2 x) (padicValNat 2 y) := by
  have h : padicValRat 2 (x : ℚ) ≠ padicValRat 2 (y : ℚ) := by
    rw [padicValRat.of_nat, padicValRat.of_nat]
    exact_mod_cast hne
  have hr := padicValRat.add_eq_min (p := 2) (q := (x : ℚ)) (r := (y : ℚ))
    (by positivity) (by positivity) (by positivity) h
  rw [← Nat.cast_add, padicValRat.of_nat, padicValRat.of_nat, padicValRat.of_nat] at hr
  exact_mod_cast hr

private theorem odd_unit_square {x k : ℕ} (hx : Odd x) (hk : Even k) :
    ∃ j : ℕ, x^k = 4*j+1 := by
  obtain ⟨e, rfl⟩ := hk
  obtain ⟨u, hu⟩ := hx.pow (n := e)
  refine ⟨u*u+u, ?_⟩
  rw [pow_add,hu]
  ring

private theorem split_pow (a b : ℕ) :
    a^b = 2^(b * padicValNat 2 a) * (a.divMaxPow 2)^b := by
  calc
    a^b = (2^(padicValNat 2 a) * a.divMaxPow 2)^b :=
      congrArg (fun x : ℕ => x^b) (Nat.pow_padicValNat_mul_divMaxPow 2 a).symm
    _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_comm b]

private theorem even_diag_absurd {a b m : ℕ} (ha : 2 ≤ a) (ham : a < m) (hmb : m < b)
    (ea : Even a) (eb : Even b) (h : a^b+b^a = 2*m^m) : False := by
  let r := padicValNat 2 a
  let s := padicValNat 2 b
  let t := padicValNat 2 m
  have hr : 0 < r := by
    have := (padicValNat_dvd_iff_le (p:=2) (n:=1) (a:=a) (by omega)).mp
      (by simpa using even_iff_two_dvd.mp ea)
    exact this
  have hs : 0 < s := by
    have := (padicValNat_dvd_iff_le (p:=2) (n:=1) (a:=b) (by omega)).mp
      (by simpa using even_iff_two_dvd.mp eb)
    exact this
  have hmval : padicValNat 2 (a^b+b^a) = 1+m*t := by
    rw [h,padicValNat.mul (by decide) (pow_ne_zero _ (by omega)), padicValNat_self, padicValNat.pow]
  have emt : Even (m*t) := by
    by_cases em : Even m
    · exact em.mul_right _
    · have ht : t = 0 := padicValNat.eq_zero_of_not_dvd (by simpa [← even_iff_two_dvd] using em)
      simp [ht]
  have hsame : b*r = a*s := by
    by_contra hdiff
    have hne : padicValNat 2 (a^b) ≠ padicValNat 2 (b^a) := by simpa only [padicValNat.pow] using hdiff
    have hmin := val_add_min (pow_ne_zero _ (by omega)) (pow_ne_zero _ (by omega)) hne
    simp only [padicValNat.pow] at hmin
    change padicValNat 2 (a^b+b^a) = min (b*r) (a*s) at hmin
    have hEven : Even (min (b*r) (a*s)) := by
      rcases le_total (b*r) (a*s) with hh | hh
      · rw [min_eq_left hh]
        exact eb.mul_right _
      · rw [min_eq_right hh]
        exact ea.mul_right _
    rw [← hmin, hmval, Nat.add_comm] at hEven
    exact Nat.even_add_one.mp hEven emt
  have hoA : Odd (a.divMaxPow 2) := Nat.not_even_iff_odd.mp <| by
    rw [even_iff_two_dvd]; exact Nat.not_dvd_divMaxPow (by decide) (by omega)
  have hoB : Odd (b.divMaxPow 2) := Nat.not_even_iff_odd.mp <| by
    rw [even_iff_two_dvd]; exact Nat.not_dvd_divMaxPow (by decide) (by omega)
  obtain ⟨u, hu⟩ := odd_unit_square hoA eb
  obtain ⟨v, hv⟩ := odd_unit_square hoB ea
  have hsplit : a^b+b^a = 2^(b*r)*2*(2*(u+v)+1) := by
    rw [split_pow a b, split_pow b a, hu, hv]
    change 2^(b*r)*(4*u+1)+2^(a*s)*(4*v+1) = _
    rw [← hsame]
    ring
  have hvalodd : padicValNat 2 (2*(u+v)+1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
  have hbr : b*r = m*t := by
    rw [hsplit, padicValNat.mul (by positivity) (by positivity), padicValNat.mul (by positivity) (by decide),
      padicValNat.prime_pow, padicValNat_self, hvalodd] at hmval
    omega
  have ht : 0 < t := by
    have := Nat.mul_pos (show 0 < b by omega) hr
    by_contra! hz
    have z : t=0 := by omega
    simp [z] at hbr
    omega
  have hrt : r < t := by
    by_contra! htr
    have hlt := Nat.mul_lt_mul_of_pos_right hmb hr
    have hle := Nat.mul_le_mul_left m htr
    omega
  have hts : t < s := by
    by_contra! hst
    have hlt := Nat.mul_lt_mul_of_pos_right ham ht
    have hle := Nat.mul_le_mul_left a hst
    omega
  have veq₁ := congrArg (padicValNat 2) hsame
  have veq₂ := congrArg (padicValNat 2) hbr
  rw [padicValNat.mul (by omega) (by omega), padicValNat.mul (by omega) (by omega)] at veq₁ veq₂
  change s + padicValNat 2 r = r + padicValNat 2 s at veq₁
  change s + padicValNat 2 r = t + padicValNat 2 t at veq₂
  let d := s-t
  have hd : 0 < d := by dsimp [d]; omega
  have hsd : 2^d ∣ s := (padicValNat_dvd_iff_le (by omega)).mpr (by dsimp [d]; omega)
  have htd : 2^d ∣ t := (padicValNat_dvd_iff_le (by omega)).mpr (by dsimp [d]; omega)
  have hdd : 2^d ∣ d := Nat.dvd_sub hsd htd
  have hle := Nat.le_of_dvd hd hdd
  exact (Nat.not_lt_of_ge hle) (Nat.lt_pow_self (by decide))

private theorem odd_outer_of_diagonal {a b m : ℕ} (ha : 2 ≤ a) (ham : a < m) (hmb : m < b)
    (h : OMA.S_mse_3286093.L a b = OMA.S_mse_3286093.L m m) : Odd a ∧ Odd b := by
  have eqn : a^b+b^a = 2*m^m := by simpa only [OMA.S_mse_3286093.L, two_mul] using h
  have eSum : Even (a^b+b^a) := by rw [eqn]; exact even_two.mul_right _
  have ee := Nat.even_add.mp eSum
  rw [Nat.even_pow' (by omega), Nat.even_pow' (by omega)] at ee
  have na : ¬ Even a := fun ea => even_diag_absurd ha ham hmb ea (ee.mp ea) eqn
  exact ⟨Nat.not_even_iff_odd.mp na, Nat.not_even_iff_odd.mp (fun eb => na (ee.mpr eb))⟩

private theorem exclude_nested (h₁ : H1) (h₂ : H2) {a b m n : ℕ}
    (ha : 2 ≤ a) (hab : a ≤ b) (ham : a < m) (hmn : m ≤ n)
    (heq : L a b = L m n) : False := by
  have hnb : n < b := by
    by_contra! hbn
    have h₃ : a ^ b < m ^ n :=
      (Nat.pow_lt_pow_left ham (by omega : b ≠ 0)).trans_le
        (Nat.pow_le_pow_right (by omega : 0 < m) hbn)
    have h₄ : b ^ a ≤ n ^ m :=
      (Nat.pow_le_pow_left hbn a).trans
        (Nat.pow_le_pow_right (by omega : 0 < n) ham.le)
    unfold L at heq
    omega
  have hi := collision_smaller_independent a b m n ha ham hmn hnb heq
  have hlog := collision_forced_exponent a b m n ha ham hmn hnb heq
  subst b
  rcases eq_or_lt_of_le hmn with rfl | hmn'
  · obtain ⟨hoa, hob⟩ := odd_outer_of_diagonal ha ham hnb heq
    exact h₁ a m ha ham hoa hob hi heq
  · exact h₂ a m n ha ham hmn' hi heq

private theorem sorted_unique (h₁ : H1) (h₂ : H2) {a b m n : ℕ}
    (ha : 2 ≤ a) (hab : a ≤ b) (hm : 2 ≤ m) (hmn : m ≤ n)
    (heq : L a b = L m n) : a = m ∧ b = n := by
  rcases lt_trichotomy a m with ham | rfl | hma
  · exact (exclude_nested h₁ h₂ ha hab ham hmn heq).elim
  · have strict : StrictMono (L a) := by
      intro x y hxy
      apply Nat.add_lt_add_of_lt_of_le
      · exact Nat.pow_lt_pow_right (by omega) hxy
      · exact Nat.pow_le_pow_left hxy.le a
    exact ⟨rfl, strict.injective heq⟩
  · exact (exclude_nested h₁ h₂ hm hmn hma hab heq.symm).elim

private theorem normalize (a b : ℕ) : L (min a b) (max a b) = L a b := by
  rcases le_total a b with hab | hba
  · simp [min_eq_left hab, max_eq_right hab]
  · simp [min_eq_right hba, max_eq_left hba, L, Nat.add_comm]

theorem main : H1 → H2 → type_of% @OMA.S_mse_3286093.main := by
  intro h₁ h₂ a b m n ha hb hm hn heq
  have eqn := (normalize a b).trans (heq.trans (normalize m n).symm)
  obtain ⟨hmin, hmax⟩ := sorted_unique h₁ h₂ (by omega) (by omega) (by omega) (by omega) eqn
  omega

end Assembly

end OMA.R_mse_3286093_R1
