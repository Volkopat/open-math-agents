import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R2

/-!
Crystal uniqueness when the successor has at most one odd prime divisor.
Shorter proof of a step first solved in pull request 7234 (by ivillar).

Source: Marco Abrate, Stefano Barbero, Umberto Cerruti, Nadir Murru,
The biharmonic mean, Mathematical Reports 18(68) (2016), 483–495.
https://imar.ro/journals/Mathematical_Reports/Pdfs/2016/4/5.pdf
Refereed journal article; preprint https://arxiv.org/abs/1601.03081.

Route (odd cofactor r in n+1 = (a+b)r with r+1 dividing a+b, then r = p^i
and the prime-power lemma forcing i = 1): laid out by the author of the R2
reduction (pull request 6383, senamakel) in its description and plan note.
The proved upstream form of Proposition 1 converts the crystal condition
into a conic equation; a direct Vieta descent proves the divisibility
invariant without assuming the article's recurrence classification.
The unrestricted uniqueness conjecture is not proved by this file.
-/

open Arxiv.«1601.03081»

lemma conic_parameter_dvd (u v k : ℕ) (hu : 0 < u) (hv : 0 < v)
    (heq : (u + v - 1)^2 = k * u * v) : k ∣ u + v - 1 := by
  generalize hn : u + v = n
  induction n using Nat.strong_induction_on generalizing u v with
  | h n ih =>
    have ordered (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (huv : u ≤ v)
        (heq : (u + v - 1)^2 = k * u * v) (hn : u + v = n) :
        k ∣ u + v - 1 := by
      by_cases hu1 : u = 1
      · subst u
        simp only [Nat.add_sub_cancel_left] at heq ⊢
        have hvk : v = k := by nlinarith
        exact hvk ▸ dvd_rfl
      have hu2 : 2 ≤ u := by omega
      have hs : u + v - 1 = (u - 1) + v := by omega
      have heq' : ((u - 1) + v)^2 = k * u * v := by rwa [hs] at heq
      have hd : v ∣ (u - 1)^2 := by
        have hsum : v ∣ (u - 1)^2 + v * (2 * (u - 1) + v) := by
          have hid : (u - 1)^2 + v * (2 * (u - 1) + v) = ((u - 1) + v)^2 := by ring
          rw [hid, heq']
          exact dvd_mul_left _ _
        exact (Nat.dvd_add_iff_left (dvd_mul_right v (2 * (u - 1) + v))).mpr hsum
      let w := (u - 1)^2 / v
      have hwv : w * v = (u - 1)^2 := Nat.div_mul_cancel hd
      have hw : 0 < w := by
        have hpos : 0 < (u - 1)^2 := pow_pos (by omega) 2
        nlinarith
      have hwlt : w < u := by
        have hu0 : u - 1 + 1 = u := by omega
        nlinarith
      have hroot : w + v + 2 * (u - 1) = k * u := by
        apply Nat.eq_of_mul_eq_mul_right hv
        nlinarith [heq', hwv]
      have hnew : (u + w - 1)^2 = k * u * w := by
        have hs' : u + w - 1 = (u - 1) + w := by omega
        rw [hs', ← hroot]
        nlinarith [hwv]
      have hdiv : k ∣ u + w - 1 := ih (u + w) (by omega) u w hu hw hnew rfl
      have hsum : (u + w - 1) + (u + v - 1) = k * u := by omega
      apply (Nat.dvd_add_iff_right hdiv).mpr
      rw [hsum]
      exact dvd_mul_right _ _
    rcases le_total u v with huv | hvu
    · simpa only [hn] using ordered u v hu hv huv heq hn
    · have heq' : (v + u - 1)^2 = k * v * u := by simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm] using heq
      simpa only [Nat.add_comm v u, hn] using ordered v u hv hu hvu heq' (by omega)

lemma crystal_cofactor (a b : ℕ) (ha : 1 < a) (hb : 1 < b)
    (hao : Odd a) (hbo : Odd b)
    (hd : (a+1)*(b+1) ∣ (a+b)^2) :
    ∃ r : ℕ, 1 < r ∧ Odd r ∧ a*b+1 = r*(a+b) ∧ r+1 ∣ a+b := by
  obtain ⟨α, rfl⟩ := hao
  obtain ⟨β, rfl⟩ := hbo
  obtain ⟨k, hk⟩ := hd
  have hα : 1 ≤ α := by omega
  have hβ : 1 ≤ β := by omega
  have hc : (α+β+1)^2 = k*(α+1)*(β+1) := by nlinarith [hk]
  have hkpos : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hc)
  have hdk : k ∣ α+β+1 := by
    have h := conic_parameter_dvd (α+1) (β+1) k (by omega) (by omega)
      (by convert hc using 1 <;> congr 1 <;> omega)
    convert h using 1 <;> omega
  obtain ⟨e, he⟩ := hdk
  have huv : (α+1)*(β+1) = k*e^2 := by
    apply Nat.eq_of_mul_eq_mul_left hkpos
    calc
      k*((α+1)*(β+1)) = (α+β+1)^2 := by nlinarith [hc]
      _ = (k*e)^2 := by rw [he]
      _ = k*(k*e^2) := by ring
  have he2 : 2 ≤ e := by
    by_contra h
    have he1 : e ≤ 1 := by omega
    interval_cases e
    · norm_num at he
    · norm_num at he huv
      nlinarith
  let r := 2*e-1
  have hr : r+1 = 2*e := by dsimp [r]; omega
  have hs : (2*α+1)+(2*β+1) = 2*k*e := by nlinarith [he]
  refine ⟨r, by dsimp [r]; omega, ⟨e-1, by dsimp [r]; omega⟩, ?_, ?_⟩
  · apply Nat.add_right_cancel (m := (2*α+1)+(2*β+1))
    calc
      (2*α+1)*(2*β+1)+1+((2*α+1)+(2*β+1)) = 4*((α+1)*(β+1)) := by ring
      _ = 4*(k*e^2) := by rw [huv]
      _ = (r+1)*(2*k*e) := by rw [hr]; ring
      _ = r*((2*α+1)+(2*β+1))+((2*α+1)+(2*β+1)) := by rw [hs]; ring
  · refine ⟨k, ?_⟩
    rw [hs, hr]
    ring

lemma odd_pow_add_one_eq_two_pow {p i j : ℕ} (hp : 1 < p) (ho : Odd p)
    (hi : 0 < i) (heq : p^i + 1 = 2^j) : i = 1 := by
  have hpwi : 1 < p^i := Nat.one_lt_pow hi.ne' hp
  have hj : 2 ≤ j := by
    by_contra h
    have hj1 : j ≤ 1 := by omega
    interval_cases j <;> norm_num at heq <;> omega
  rcases Nat.even_or_odd i with he | hodd
  · obtain ⟨h, hh⟩ := he
    obtain ⟨t, ht⟩ := (ho.pow : Odd (p^h))
    have hid : p^i + 1 = 4 * (t*t+t) + 2 := by
      rw [hh, pow_add, ht]
      ring
    have hfour : 4 ∣ 2^j := by
      exact_mod_cast (Nat.pow_dvd_pow 2 hj : 2^2 ∣ 2^j)
    rw [← heq, hid] at hfour
    omega
  · have hdiv : p + 1 ∣ 2^j := by
      rw [← heq]
      simpa using hodd.nat_add_dvd_pow_add_pow p 1
    obtain ⟨l, hlj, hl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
    have hsq : p^2 ≡ 1 [MOD 2*(p+1)] := by
      obtain ⟨t, ht⟩ := ho
      have hid : p^2 = (2*(p+1))*t + 1 := by rw [ht]; ring
      rw [hid]
      exact Nat.ModEq.modulus_mul_add
    have hcong : p^i + 1 ≡ p+1 [MOD 2*(p+1)] := by
      obtain ⟨h, hh⟩ := hodd
      rw [hh, pow_add, pow_mul, pow_one]
      simpa using ((hsq.pow h).mul_right p).add_right 1
    have hjl : j ≤ l := by
      by_contra h
      have hpow : 2^(l+1) ∣ 2^j := Nat.pow_dvd_pow 2 (by omega)
      have hmod : 2*(p+1) ∣ p^i+1 := by
        rw [heq, hl]
        simpa [pow_succ, Nat.mul_comm] using hpow
      have := Nat.le_of_dvd (by omega : 0 < p+1) ((hcong.dvd_iff dvd_rfl).mp hmod)
      omega
    have hjl' : j = l := by omega
    have hpi : p^i+1 = p+1 := by rw [heq, hjl', ← hl]
    have hpow : p^i = p^1 := by simpa only [pow_one] using Nat.add_right_cancel hpi
    exact Nat.pow_right_injective (by omega : 2 ≤ p) hpow

lemma cofactor_eq_prime {n s r p A B : ℕ} (hp : p.Prime) (ho : Odd p)
    (hr : 1 < r) (hro : Odd r) (ht : n+1 = r*s)
    (hdiv : r+1 ∣ s) (hn : n+1 = 2^A*p^B) : r = p := by
  have hr2 : r.Coprime 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr hro.not_two_dvd_nat).symm
  have hrpow : r ∣ p^B := by
    apply (hr2.pow_right A).dvd_of_dvd_mul_left
    rw [← hn, ht]
    exact dvd_mul_right _ _
  obtain ⟨i, hiB, hri⟩ := (Nat.dvd_prime_pow hp).mp hrpow
  have hi : 0 < i := by
    by_contra h
    have hi0 : i = 0 := by omega
    simp [hi0] at hri
    omega
  have hpr : p ∣ r := by rw [hri]; exact dvd_pow_self p hi.ne'
  have hpnot : ¬ p ∣ r+1 := fun h => hp.not_dvd_one ((Nat.dvd_add_iff_right hpr).mpr h)
  have hd : r+1 ∣ 2^A := by
    apply ((hp.coprime_iff_not_dvd.mpr hpnot).symm.pow_right B).dvd_of_dvd_mul_right
    rw [← hn, ht]
    exact hdiv.trans (dvd_mul_left s r)
  obtain ⟨j, hjA, hrj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hi1 : i = 1 := odd_pow_add_one_eq_two_pow hp.one_lt ho hi (by simpa [hri] using hrj)
  simpa [hi1] using hri

lemma unordered_pair_of_sum_product {a b c d : ℕ}
    (hs : a+b = c+d) (hp : a*b = c*d) :
    ({a,b} : Finset ℕ) = {c,d} := by
  have hzero : ((a : ℤ)-c)*((a : ℤ)-d) = 0 := by
    have hs' : (a : ℤ)+b = c+d := by exact_mod_cast hs
    have hp' : (a : ℤ)*b = c*d := by exact_mod_cast hp
    nlinarith
  rcases mul_eq_zero.mp hzero with h | h
  · obtain rfl : a = c := by omega
    obtain rfl : b = d := by omega
    rfl
  · obtain rfl : a = d := by omega
    obtain rfl : b = c := by omega
    exact Finset.pair_comm _ _

theorem OMA.solution : OMA.R_Arxiv_1601_03081_crystals_components_unique_R2.H1 := by
  intro n a b c d hab hcd h
  obtain ⟨p, A, B, hp, ho, hn⟩ := h
  have hsum : ∀ x y, IsCrystalWithComponents n x y → n+1 = p*(x+y) := by
    intro x y hxy
    obtain ⟨hno, hx, hy, hprod, hdiv⟩ := (isCrystalWithComponents_iff_sum_sq_dvd n x y).mp hxy
    rw [hprod] at hno
    obtain ⟨r, hr, hro, heq, hd⟩ :=
      crystal_cofactor x y hx hy (Nat.Odd.of_mul_left hno) (Nat.Odd.of_mul_right hno) hdiv
    have ht : n+1 = r*(x+y) := by simpa only [hprod] using heq
    have hrp : r = p := cofactor_eq_prime hp ho hr hro ht hd hn
    simpa only [hrp] using ht
  exact unordered_pair_of_sum_product
    (Nat.eq_of_mul_eq_mul_left hp.pos ((hsum a b hab).symm.trans (hsum c d hcd)))
    (hab.2.2.2.1.symm.trans hcd.2.2.2.1)
