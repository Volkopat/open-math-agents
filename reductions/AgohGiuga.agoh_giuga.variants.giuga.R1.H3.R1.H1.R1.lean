import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R1_H3_R1
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith

-- Reduction AgohGiuga.agoh_giuga.variants.giuga.R1.H3.R1.H1.R1 of step AgohGiuga.agoh_giuga.variants.giuga.R1.H3.R1.H1
-- Credit: @Alewawa

namespace OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1_H3_R1_H1_R1

open scoped BigOperators

private theorem card_even_of_numerator {n : ℕ} (ho : Odd n)
    (hs : ∑ r ∈ n.primeFactors, n / r = n + 1) :
    Even n.primeFactors.card := by
  have hn : n % 2 = 1 := Nat.odd_iff.mp ho
  have hterm (r : ℕ) (hr : r ∈ n.primeFactors) : (↑(n / r) : ZMod 2) = 1 := by
    have hd := Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hr)
    rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff']
    have hnd : ¬ 2 ∣ n := by omega
    have hrd : ¬ 2 ∣ n / r := fun h => hnd (h.trans hd)
    omega
  have hc := congrArg (fun x : ℕ => (x : ZMod 2)) hs
  push_cast at hc
  have hsum : ∑ r ∈ n.primeFactors, (↑(n / r) : ZMod 2) =
      ∑ _r ∈ n.primeFactors, (1 : ZMod 2) := Finset.sum_congr rfl hterm
  rw [hsum, Finset.sum_const, nsmul_one] at hc
  have hn' : (n : ZMod 2) = 1 := by
    rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff']
    exact hn
  rw [hn'] at hc
  norm_num at hc
  exact Nat.even_iff.mpr ((ZMod.natCast_eq_zero_iff _ _).mp hc |> Nat.dvd_iff_mod_eq_zero.mp)

private theorem product_all_neg_one {k : ℕ} {s : Finset ℕ}
    (hall : ∀ r ∈ s, (r : ZMod k) = -1) (he : Even s.card) :
    (∏ r ∈ s, (r : ZMod k)) = 1 := by
  rw [Finset.prod_congr rfl hall, Finset.prod_const, he.neg_one_pow]

private theorem three_not_dvd {n : ℕ} (hn : 0 < n) (ho : Odd n) (hf : Squarefree n)
    (hs : ∑ r ∈ n.primeFactors, n / r = n + 1)
    (hk : ∀ r ∈ n.primeFactors, (r - 1) ∣ n - 1) : ¬ 3 ∣ n := by
  intro h3
  have hmem := (Nat.mem_primeFactors_of_ne_zero hn.ne').mpr ⟨by decide, h3⟩
  let s := n.primeFactors.erase 3
  have hrmod : ∀ r ∈ s, r % 3 = 2 := by
    intro r hr
    obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hr
    have hp := Nat.prime_of_mem_primeFactors hm
    have hnot0 : ¬ 3 ∣ r := by
      intro hd
      exact hne ((hp.eq_one_or_self_of_dvd 3 hd).resolve_left (by decide)).symm
    have hnot1 : ¬ 3 ∣ r - 1 := by
      intro hd
      have hh := hd.trans (hk r hm)
      omega
    have := hp.two_le
    omega
  have hprod : ∏ r ∈ s, r = n / 3 := by
    have h := Finset.mul_prod_erase n.primeFactors (fun r => r) hmem
    change 3 * ∏ r ∈ s, r = ∏ r ∈ n.primeFactors, r at h
    rw [Nat.prod_primeFactors_of_squarefree hf] at h
    omega
  have hsum : ∑ r ∈ s, n / r + n / 3 = n + 1 := by
    rw [Finset.sum_erase_add _ _ hmem, hs]
  have hdiv (r : ℕ) (hr : r ∈ s) : 3 ∣ n / r := by
    obtain ⟨_, hm⟩ := Finset.mem_erase.mp hr
    apply (Nat.dvd_div_iff_mul_dvd (Nat.dvd_of_mem_primeFactors hm)).mpr
    have hcop : Nat.Coprime 3 r := by
      apply Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3) |>.mpr
      have := hrmod r hr
      omega
    exact hcop.symm.mul_dvd_of_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hm) h3
  have hcof : (↑(n / 3) : ZMod 3) = 1 := by
    have hsumCast := congrArg (fun x : ℕ => (x : ZMod 3)) hsum
    push_cast at hsumCast
    have h0 : ∑ r ∈ s, (↑(n / r) : ZMod 3) = 0 :=
      Finset.sum_eq_zero fun r hr => (ZMod.natCast_eq_zero_iff _ _).mpr (hdiv r hr)
    rw [h0, zero_add, (ZMod.natCast_eq_zero_iff _ _).mpr h3, zero_add] at hsumCast
    exact hsumCast
  have hcard := card_even_of_numerator ho hs
  have hcard' : Odd s.card := by
    have hh := Finset.card_erase_of_mem hmem
    rw [Nat.odd_iff]
    change (n.primeFactors.erase 3).card % 2 = 1
    have hpos := Finset.card_pos.mpr ⟨3, hmem⟩
    have he := Nat.even_iff.mp hcard
    omega
  have hneg (r : ℕ) (hr : r ∈ s) : (r : ZMod 3) = -1 := by
    calc
      (r : ZMod 3) = (2 : ℕ) := (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (hrmod r hr)
      _ = -1 := by decide
  have hh : (↑(n / 3) : ZMod 3) = -1 := by
    rw [← hprod, Nat.cast_prod, Finset.prod_congr rfl hneg, Finset.prod_const, hcard'.neg_one_pow]
  exact (by decide : (1 : ZMod 3) ≠ -1) (hcof.symm.trans hh)

private theorem product_mod_twelve {n : ℕ} (hn : 0 < n) (ho : Odd n) (hf : Squarefree n)
    (hs : ∑ r ∈ n.primeFactors, n / r = n + 1)
    (hk : ∀ r ∈ n.primeFactors, (r - 1) ∣ n - 1) : n % 12 = 1 := by
  have hcard := card_even_of_numerator ho hs
  have hthree := three_not_dvd hn ho hf hs hk
  have mod3 : n % 3 = 1 := by
    by_cases hex : ∃ r ∈ n.primeFactors, r % 3 = 1
    · obtain ⟨r, hr, hmod⟩ := hex
      have h := Nat.prime_of_mem_primeFactors hr |>.two_le
      have hd : 3 ∣ r - 1 := by omega
      have h := hd.trans (hk r hr)
      omega
    · have hneg (r : ℕ) (hr : r ∈ n.primeFactors) : (r : ZMod 3) = -1 := by
        have hn0 : ¬ 3 ∣ r := fun h => hthree (h.trans (Nat.dvd_of_mem_primeFactors hr))
        have hn1 : r % 3 ≠ 1 := fun h => hex ⟨r, hr, h⟩
        have hmod : r % 3 = 2 := by omega
        calc
          (r : ZMod 3) = (2 : ℕ) := (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hmod
          _ = -1 := by decide
      have hc := product_all_neg_one hneg hcard
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hf, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff'] at hc
      exact hc
  have mod4 : n % 4 = 1 := by
    by_cases hex : ∃ r ∈ n.primeFactors, r % 4 = 1
    · obtain ⟨r, hr, hmod⟩ := hex
      have h := Nat.prime_of_mem_primeFactors hr |>.two_le
      have hd : 4 ∣ r - 1 := by omega
      have h := hd.trans (hk r hr)
      omega
    · have hneg (r : ℕ) (hr : r ∈ n.primeFactors) : (r : ZMod 4) = -1 := by
        have hn0 : ¬ 2 ∣ r := by
          intro h
          have hd := h.trans (Nat.dvd_of_mem_primeFactors hr)
          have hn2 := Nat.odd_iff.mp ho
          omega
        have hn1 : r % 4 ≠ 1 := fun h => hex ⟨r, hr, h⟩
        have hmod : r % 4 = 3 := by omega
        calc
          (r : ZMod 4) = (3 : ℕ) := (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hmod
          _ = -1 := by decide
      have hc := product_all_neg_one hneg hcard
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hf, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff'] at hc
      exact hc
  omega

private theorem square_residue_table : ∀ r : Fin 24,
    r.val % 2 = 1 → r.val % 3 ≠ 0 → (r.val : ZMod 24)^2 = 1 := by decide

private theorem square_mod_twentyfour {r : ℕ} (ho : Odd r) (h3 : ¬ 3 ∣ r) :
    (r : ZMod 24)^2 = 1 := by
  have hmod : (r : ZMod 24) = (↑(r % 24) : ZMod 24) :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (by simp)
  rw [hmod]
  apply square_residue_table ⟨r % 24, Nat.mod_lt _ (by decide)⟩
  · have := Nat.odd_iff.mp ho
    dsimp
    omega
  · dsimp
    omega

private theorem completion_gap_mod_twentyfour {m p q g : ℕ} (hp : Odd p) (hq : Odd q)
    (hp3 : ¬ 3 ∣ p) (hq3 : ¬ 3 ∣ q) (hn : 0 < m*p*q)
    (hn12 : (m*p*q) % 12 = 1) (heq : g*p*q + 1 = m*(p+q)) :
    (g + (p-1)*(q-1)) % 24 = 1 := by
  have hp2 := square_mod_twentyfour hp hp3
  have hq2 := square_mod_twentyfour hq hq3
  have h12 : 12 ∣ m*p*q - 1 := by omega
  have h2 : 2 ∣ p+q := by
    have := Nat.odd_iff.mp hp
    have := Nat.odd_iff.mp hq
    omega
  have h24 : 24 ∣ (m*p*q-1)*(p+q) := mul_dvd_mul h12 h2
  have h24cast := (ZMod.natCast_eq_zero_iff _ _).mpr h24
  push_cast [Nat.cast_sub (show 1 ≤ m*p*q by omega)] at h24cast
  have hN : (m : ZMod 24)*p*q*((p : ZMod 24)+q) = p+q := by
    calc
      _ = ((m : ZMod 24)*p*q-1)*((p : ZMod 24)+q)+(p+q) := by ring
      _ = _ := by rw [h24cast, zero_add]
  have h := congrArg (fun x : ℕ => (x : ZMod 24)) heq
  push_cast at h
  have hG : (g : ZMod 24) = (p : ZMod 24)+q-p*q := by
    calc
      _ = (g*p*q : ZMod 24)*(p*q) := by
        calc
          _ = g*((p : ZMod 24)^2)*((q : ZMod 24)^2) := by rw [hp2, hq2]; ring
          _ = _ := by ring
      _ = ((m : ZMod 24)*(p+q)-1)*(p*q) := by rw [eq_sub_of_add_eq h]
      _ = (m : ZMod 24)*p*q*(p+q)-p*q := by ring
      _ = _ := by rw [hN]
  have hh : (↑(g + (p-1)*(q-1)) : ZMod 24) = 1 := by
    push_cast [Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_sub (show 1 ≤ q by omega)]
    rw [hG]
    ring
  exact (ZMod.natCast_eq_natCast_iff' _ 1 24).mp hh

private theorem prefix_discriminant {m p q g L : ℕ} (hn : 0 < m*p*q)
    (hk : L ∣ m*p*q - 1) (heq : g*p*q + 1 = m*(p+q)) :
    ∃ x : ZMod L, x^2 = ((g : ZMod L)+m)^2 - 4*(m : ZMod L)^3 := by
  have hN := (ZMod.natCast_eq_zero_iff _ _).mpr hk
  push_cast [Nat.cast_sub (show 1 ≤ m*p*q by omega)] at hN
  have hN' := sub_eq_zero.mp hN
  have he := congrArg (fun x : ℕ => (x : ZMod L)) heq
  push_cast at he
  have hS : (m : ZMod L)^2*(p+q) = g+m := by
    calc
      _ = (m : ZMod L)*((m : ZMod L)*(p+q)) := by ring
      _ = (g : ZMod L)*((m : ZMod L)*p*q)+m := by rw [← he]; ring
      _ = _ := by rw [hN', mul_one]
  refine ⟨(m : ZMod L)^2*(q-p), ?_⟩
  calc
    _ = ((m : ZMod L)^2*(p+q))^2 - 4*(m : ZMod L)^3*((m : ZMod L)*p*q) := by ring
    _ = _ := by rw [hS, hN', mul_one]

private theorem completion_product_congruences {m p q g K : ℕ} (hm : 0 < m)
    (hn : 0 < m*p*q) (hk : K ∣ m*p*q - 1)
    (heq : g*p*q + 1 = m*(p+q)) :
    Nat.ModEq m (g*(p*q)) (m-1) ∧ Nat.ModEq K (m*(p*q)) 1 := by
  constructor
  · apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    have he := congrArg (fun x : ℕ => (x : ZMod m)) heq
    push_cast at he
    rw [ZMod.natCast_self, zero_mul] at he
    push_cast [Nat.cast_sub (show 1 ≤ m by omega)]
    rw [ZMod.natCast_self, zero_sub, ← mul_assoc]
    exact eq_neg_of_add_eq_zero_left he
  · apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    have h := (ZMod.natCast_eq_zero_iff _ _).mpr hk
    push_cast [Nat.cast_sub (show 1 ≤ m*p*q by omega)] at h
    push_cast
    rw [← mul_assoc]
    exact sub_eq_zero.mp h

private theorem completion_product_lt {m p q g : ℕ} (hm : 0 < m)
    (hpq : p < q) (hqm : q < m)
    (heq : g*p*q + 1 = m*(p+q)) : g*(p*q) < 2*m^2 := by
  have h := Nat.mul_lt_mul_of_pos_left (show p+q < 2*m by omega) hm
  nlinarith only [h, heq]

private theorem terminal_cofactor_bound {a b c g u v : ℕ}
    (ha : 0 < a) (ha2 : 2 ∣ a) (hb2 : 2 ∣ b)
    (hg : 2 ≤ g) (hu : 0 < u) (hv : 0 < v)
    (hleft : g*a = c+u*b) (hright : g*b = c+v*a)
    (heq : g*(a+1)*(b+1)+1 = (g+c)*(a+b+2)) :
    2*(g+c) < g^3 := by
  let t := a.gcd b
  have hta : t ∣ a := Nat.gcd_dvd_left _ _
  have htb : t ∣ b := Nat.gcd_dvd_right _ _
  have ht : 0 < t := Nat.gcd_pos_of_pos_left _ ha
  have htc : t ∣ c := by
    have hd : t ∣ c+u*b := hleft ▸ dvd_mul_of_dvd_right hta g
    exact (Nat.dvd_add_left (dvd_mul_of_dvd_right htb u)).mp hd
  have ht2 : 2 ∣ t := Nat.dvd_gcd ha2 hb2
  have htSum : t^2 ∣ (g-1)+2*c := by
    have hprod : t^2 ∣ g*(a*b) := by
      rw [pow_two]
      exact dvd_mul_of_dvd_right (mul_dvd_mul hta htb) g
    have htcs : t^2 ∣ c*(a+b) := by
      rw [pow_two]
      exact mul_dvd_mul htc (Nat.dvd_add hta htb)
    have hEq : g*(a*b) = c*(a+b)+((g-1)+2*c) := by
      nlinarith only [heq, Nat.sub_add_cancel (show 1 ≤ g by omega)]
    rw [hEq] at hprod
    exact (Nat.dvd_add_right htcs).mp hprod
  have h2tDvd : 2*t ∣ g-1 := by
    have htSquare : 2*t ∣ t^2 := by
      rw [pow_two]
      exact mul_dvd_mul ht2 (dvd_refl _)
    exact (Nat.dvd_add_left (Nat.mul_dvd_mul_left 2 htc)).mp (htSquare.trans htSum)
  have h2t := Nat.le_of_dvd (show 0 < g-1 by omega) h2tDvd
  have hratio : (g+u)*b = a*(g+v) := by nlinarith only [hleft, hright]
  have hadd : a ∣ (g+u)*t := Nat.dvd_mul_gcd_iff_dvd_mul.mpr ⟨g+v, hratio⟩
  have haLe := Nat.le_of_dvd (Nat.mul_pos (by omega : 0 < g+u) ht) hadd
  have hcore : (g+u)*c < g^2*a := by
    have huv := Nat.mul_pos (Nat.mul_pos hu hv) ha
    nlinarith only [congrArg (g*·) hleft, congrArg (u*·) hright, huv]
  have hc : c < t*g^2 := by
    apply Nat.lt_of_mul_lt_mul_left (a := g+u)
    calc
      (g+u)*c < g^2*a := hcore
      _ ≤ g^2*((g+u)*t) := Nat.mul_le_mul_left _ haLe
      _ = (g+u)*(t*g^2) := by ring
  have h2c : 2*c < (g-1)*g^2 := by
    calc
      2*c < 2*(t*g^2) := Nat.mul_lt_mul_of_pos_left hc (by decide)
      _ = (2*t)*g^2 := by ring
      _ ≤ (g-1)*g^2 := Nat.mul_le_mul_right _ h2t
  have h2g : 2*g ≤ g^2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right g hg
  have hBalance := congrArg (· * g^2) (Nat.sub_add_cancel (show 1 ≤ g by omega))
  nlinarith only [h2c, h2g, hBalance]

private theorem terminal_product_bound {m p q g u : ℕ} (hm : 0 < m) (hp : 2 ≤ p) (hpq : p < q)
    (hu : 0 < u) (hgap : g*p*q+1 = m*(p+q))
    (hpoly : u*(q-1)*(p+q)+1 = g*p^2) (hmBound : 2*m < g^3) :
    4*(m*p*q)^2 < g^15 := by
  have hq : 0 < q := by omega
  have hg : 0 < g := by
    by_contra! h
    simp [Nat.eq_zero_of_le_zero h] at hmBound
  have hp' : 0 < p := by omega
  have hgp : g*p < 2*m := by
    by_contra! h
    have hh := Nat.mul_le_mul_right q h
    nlinarith only [hh, hgap, Nat.mul_lt_mul_of_pos_left hpq hm]
  have hgp' : g*p < g*g^2 := hgp.trans (by simpa only [pow_succ', pow_zero, mul_one] using hmBound)
  have hpBound : p < g^2 := (Nat.mul_lt_mul_left hg).mp hgp'
  have hqq : q^2 ≤ (q-1)*(p+q) := by
    have hqEq := congrArg (· * q) (Nat.sub_add_cancel (show 1 ≤ q by omega))
    have hqp : q ≤ p*(q-1) :=
      (show q ≤ 2*(q-1) by omega).trans (Nat.mul_le_mul_right _ hp)
    calc
      q^2 = (q-1)*q+q := by nlinarith only [hqEq]
      _ ≤ (q-1)*q+p*(q-1) := Nat.add_le_add_left hqp _
      _ = _ := by ring
  have hqBound : q^2 < g*p^2 := by
    calc
      q^2 ≤ (q-1)*(p+q) := hqq
      _ ≤ u*((q-1)*(p+q)) := Nat.le_mul_of_pos_left _ hu
      _ < g*p^2 := by
        have hpoly' : u*((q-1)*(p+q))+1 = g*p^2 := by simpa only [mul_assoc] using hpoly
        omega
  have hp2 : p^2 < (g^2)^2 := Nat.pow_lt_pow_left hpBound (by decide)
  have hq2 : q^2 < g*(g^2)^2 := hqBound.trans (Nat.mul_lt_mul_of_pos_left hp2 hg)
  have hm2 : (2*m)^2 < (g^3)^2 := Nat.pow_lt_pow_left hmBound (by decide)
  calc
    4*(m*p*q)^2 = (2*m)^2*p^2*q^2 := by ring
    _ < (g^3)^2*((g^2)^2)*(g*((g^2)^2)) := by
      have hleft : (2*m)^2*p^2 < (g^3)^2*((g^2)^2) :=
        (Nat.mul_lt_mul_of_pos_right hm2 (Nat.pow_pos hp')).trans_le
          (Nat.mul_le_mul_left _ hp2.le)
      exact (Nat.mul_lt_mul_of_pos_right hleft (Nat.pow_pos hq)).trans_le
        (Nat.mul_le_mul_left _ hq2.le)
    _ = g^15 := by ring

open scoped BigOperators

private theorem numerator_mul_prime {m p : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hc : m.Coprime p) :
    (∑ r ∈ (m*p).primeFactors, m*p/r) =
      p*(∑ r ∈ m.primeFactors, m/r)+m := by
  have hpNot : p ∉ m.primeFactors := fun h =>
    (hp.coprime_iff_not_dvd.mp hc.symm) (Nat.dvd_of_mem_primeFactors h)
  rw [Nat.primeFactors_mul hm.ne' hp.ne_zero, hp.primeFactors, Finset.union_comm]
  simp only [Finset.singleton_union, Finset.sum_insert hpNot, Nat.mul_div_cancel _ hp.pos,
    Finset.mul_sum]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [mul_comm m p, Nat.mul_div_assoc p (Nat.dvd_of_mem_primeFactors hr)]

private theorem terminal_korselt {p k h : ℕ} (hp : 0 < p) (hk : h*p+1 = k)
    (hd : (p-1) ∣ h) : (p-1) ∣ k*p-1 := by
  have hEq : k*p-1 = (p-1)*k + h*p := by
    have he := congrArg (· * k) (Nat.sub_add_cancel (show 1 ≤ p by omega))
    have hkp : 1 ≤ k*p := Nat.mul_pos (by omega) hp
    have hsub := Nat.sub_add_cancel hkp
    nlinarith only [he, hsub, hk]
  rw [hEq]
  exact Nat.dvd_add (Nat.dvd_mul_right _ _) (dvd_mul_of_dvd_left hd _)

private theorem terminal_gap_identity {m p q g d e : ℕ} (hg : 0 < g)
    (hd : m+d = g*p) (he : m+e = g*q) (hde : d*e+g = m*m) :
    g*p*q+1 = m*(p+q) := by
  apply Nat.eq_of_mul_eq_mul_left hg
  nlinarith only [congrArg₂ (· * ·) hd he, congrArg (m * ·) hd,
    congrArg (m * ·) he, hde]

private theorem restrictions_of_candidate {m d : ℕ} (hm : 1 < m) (ho : Odd m) (hf : Squarefree m)
    (hD : (∑ r ∈ m.primeFactors, m/r) < m)
    (hgap : 13 ≤ m - (∑ r ∈ m.primeFactors, m/r))
    (hd0 : 0 < d)
    (hdd : d ∣ m*m - (m - (∑ r ∈ m.primeFactors, m/r))) :
    let g := m - (∑ r ∈ m.primeFactors, m/r)
    let e := (m*m-g)/d
    let p := (m+d)/g
    let q := (m+e)/g
    d < e → g ∣ m+d → g ∣ m+e → p.Prime → q.Prime → p < q →
    (∀ r ∈ m.primeFactors, r < p) →
    (q-1) ∣ d → (p-1) ∣ e →
    (∀ r ∈ m.primeFactors, (r-1) ∣ m*p*q-1) →
    ((m*p*q)%12=1 ∧ (g+(p-1)*(q-1))%24=1 ∧ 4*(m*p*q)^2 < g^15 ∧
      g*p*q+1=m*(p+q)) ∧
    (∀ r ∈ m.primeFactors, ∃ x : ZMod (r-1),
      x^2 = ((g : ZMod (r-1))+m)^2-4*(m : ZMod (r-1))^3) := by
  dsimp only
  set D := ∑ r ∈ m.primeFactors, m/r
  set g := m-D
  set e := (m*m-g)/d
  set p := (m+d)/g
  set q := (m+e)/g
  intro hdeOrd hgp hgq hp hq hpq hord hdK heK hK
  have hm0 : 0 < m := by omega
  have hmd := (Nat.mul_div_cancel' hgp).symm
  have hme := (Nat.mul_div_cancel' hgq).symm
  change m+d=g*p at hmd
  change m+e=g*q at hme
  have hde : d*e+g = m*m := by
    have hd' := Nat.mul_div_cancel' hdd
    change d*e = m*m-g at hd'
    have hle : g ≤ m*m :=
      (Nat.sub_le _ _).trans (Nat.le_mul_of_pos_right m hm0)
    omega
  have hEq := terminal_gap_identity (show 0 < g by omega) hmd hme hde
  have hpC : m.Coprime p := hp.coprime_iff_not_dvd.mpr (fun hd =>
    (Nat.lt_irrefl p) (hord p ((Nat.mem_primeFactors_of_ne_zero hm0.ne').mpr ⟨hp, hd⟩))) |>.symm
  have hqC : m.Coprime q := hq.coprime_iff_not_dvd.mpr (fun hd =>
    (not_lt_of_ge hpq.le) (hord q ((Nat.mem_primeFactors_of_ne_zero hm0.ne').mpr ⟨hq, hd⟩))) |>.symm
  have hpqC : p.Coprime q := hq.coprime_iff_not_dvd.mpr
    (fun hd => (not_le_of_gt hpq) (Nat.le_of_dvd hp.pos hd)) |>.symm
  have hqmp : (m*p).Coprime q := hqC.mul_left hpqC
  have hn : 0 < m*p*q := Nat.mul_pos (Nat.mul_pos hm0 hp.pos) hq.pos
  have hsf : Squarefree (m*p*q) :=
    (Nat.squarefree_mul hqmp).mpr ⟨(Nat.squarefree_mul hpC).mpr ⟨hf, hp.squarefree⟩, hq.squarefree⟩
  obtain ⟨r, hr⟩ := Nat.nonempty_primeFactors.mpr hm
  have hr2 := (Nat.prime_of_mem_primeFactors hr).two_le
  have hp2 : p ≠ 2 := by have := hord r hr; omega
  have hq2 : q ≠ 2 := by have := hp.two_le; omega
  have hpo := hp.odd_of_ne_two hp2
  have hqo := hq.odd_of_ne_two hq2
  have hno : Odd (m*p*q) := (ho.mul hpo).mul hqo
  have hnum : ∑ r ∈ (m*p*q).primeFactors, m*p*q/r = m*p*q+1 := by
    rw [numerator_mul_prime (Nat.mul_pos hm0 hp.pos) hq hqmp, numerator_mul_prime hm0 hp hpC]
    change q*(p*D+m)+m*p = m*p*q+1
    have hsum : D+g=m := by omega
    nlinarith only [hEq, congrArg (· * (p*q)) hsum]
  have hpK : (p-1) ∣ m*p*q-1 := by
    have hh : e*p+1=m*q := by
      nlinarith only [hEq, congrArg (p*·) hme]
    simpa only [mul_right_comm m q p] using terminal_korselt hp.pos hh heK
  have hqK : (q-1) ∣ m*p*q-1 := by
    have hh : d*q+1=m*p := by
      nlinarith only [hEq, congrArg (q*·) hmd]
    exact terminal_korselt hq.pos hh hdK
  have hk : ∀ r ∈ (m*p*q).primeFactors, (r-1) ∣ m*p*q-1 := by
    rw [Nat.primeFactors_mul (Nat.mul_pos hm0 hp.pos).ne' hq.ne_zero,
      Nat.primeFactors_mul hm0.ne' hp.ne_zero, hp.primeFactors, hq.primeFactors]
    intro r hr
    simp only [Finset.mem_union, Finset.mem_singleton] at hr
    rcases hr with (hr | rfl) | rfl
    · exact hK r hr
    · exact hpK
    · exact hqK
  have hn12 := product_mod_twelve hn hno hsf hnum hk
  have h3 := three_not_dvd hn hno hsf hnum hk
  have hp3 : ¬ 3 ∣ p := fun h => h3 (h.trans (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_refl p) m) q))
  have hq3 : ¬ 3 ∣ q := fun h => h3 (dvd_mul_of_dvd_right h (m*p))
  obtain ⟨u, hu⟩ := hdK
  obtain ⟨v, hv⟩ := heK
  have hu0 : 0 < u := Nat.pos_of_ne_zero (by intro h; simp [h] at hu; omega)
  have hv0 : 0 < v := Nat.pos_of_ne_zero (by intro h; simp [h] at hv; omega)
  let c := m-g
  have hc : g+c=m := by
    have hg_le : g ≤ m := Nat.sub_le _ _
    dsimp [c]
    omega
  have hp1 := Nat.sub_add_cancel hp.one_le
  have hq1 := Nat.sub_add_cancel hq.one_le
  have hleft : g*(p-1)=c+u*(q-1) := by
    nlinarith only [hmd, hu, hc, congrArg (g*·) hp1]
  have hright : g*(q-1)=c+v*(p-1) := by
    nlinarith only [hme, hv, hc, congrArg (g*·) hq1]
  have hcof_eq : g*((p-1)+1)*((q-1)+1)+1=(g+c)*((p-1)+(q-1)+2) := by
    rw [hp1, hq1, hc, show (p-1)+(q-1)+2=p+q by omega]
    exact hEq
  have hpEven : 2 ∣ p-1 := by have h := Nat.odd_iff.mp hpo; omega
  have hqEven : 2 ∣ q-1 := by have h := Nat.odd_iff.mp hqo; omega
  have hmBound : 2*m < g^3 := hc ▸ terminal_cofactor_bound
    (by have h := hp.two_le; omega) hpEven hqEven
    (by omega) hu0 hv0 hleft hright hcof_eq
  have hpoly : u*(q-1)*(p+q)+1 = g*p^2 := by
    nlinarith only [hEq, congrArg (·*(p+q)) hmd, congrArg (·*(p+q)) hu]
  have hnBound := terminal_product_bound hm0 hp.two_le hpq hu0 hEq hpoly hmBound
  exact ⟨⟨hn12, completion_gap_mod_twentyfour hpo hqo hp3 hq3 hn hn12 hEq, hnBound, hEq⟩,
    fun r hr => prefix_discriminant hn (hK r hr) hEq⟩

open scoped BigOperators

private theorem completion_product_crt {m g K x : ℕ} (hm : m ≠ 0) (hK : K ≠ 0)
    (hg : g.Coprime m) (hmK : m.Coprime K) (hx : x < m*K)
    (h1 : Nat.ModEq m (g*x) (m-1)) (h2 : Nat.ModEq K (m*x) 1) :
    x = (Nat.chineseRemainder hmK (-((g : ZMod m)⁻¹)).val
      ((m : ZMod K)⁻¹).val).val := by
  let _ : NeZero m := ⟨hm⟩
  let _ : NeZero K := ⟨hK⟩
  have hr1 : Nat.ModEq m (g*(-((g : ZMod m)⁻¹)).val) (m-1) := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    push_cast [Nat.cast_sub (show 1 ≤ m by omega)]
    rw [ZMod.natCast_self, zero_sub, ZMod.natCast_val, ZMod.cast_id, mul_neg]
    have hInv : (g : ZMod m)*((g : ZMod m)⁻¹) = 1 := by
      simpa [ZMod.natCast_val, ZMod.cast_id, mul_comm] using ZMod.val_inv_mul hg
    rw [hInv]
  have hr2 : Nat.ModEq K (m*((m : ZMod K)⁻¹).val) 1 := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa [mul_comm] using ZMod.val_inv_mul hmK
  have hCong := Nat.chineseRemainder_modEq_unique hmK
    ((h1.trans hr1.symm).cancel_left_of_coprime hg.symm)
    ((h2.trans hr2.symm).cancel_left_of_coprime hmK.symm)
  have hLt := Nat.chineseRemainder_lt_mul hmK (-((g : ZMod m)⁻¹)).val
    ((m : ZMod K)⁻¹).val hm hK
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hLt] using hCong

/-- When the prefix modulus is large, its unique product in the admissible
range comes directly from the Chinese remainder theorem. -/
def H1 : Prop :=
  ∀ m : ℕ, 1 < m → Odd m → Squarefree m →
    let D := ∑ r ∈ m.primeFactors, m/r
    D < m →
    let g := m-D
    13 ≤ g → g.Coprime m →
    let K := m.primeFactors.lcm (fun r => r-1)
    ∀ hmK : m.Coprime K, 2*m ≤ g*K →
      ∀ x p q : ℕ,
        x = (Nat.chineseRemainder hmK (-((g : ZMod m)⁻¹)).val
          ((m : ZMod K)⁻¹).val).val →
        p*q = x → p+q = (g*x+1)/m →
        p.Prime → q.Prime → p < q → q < m →
        (∀ r ∈ m.primeFactors, r < p) →
        (q-1) ∣ g*p-m → (p-1) ∣ g*q-m →
        (m*x)%12 = 1 → (g+(p-1)*(q-1))%24 = 1 → 4*(m*x)^2 < g^15 →
        (∃ y : ZMod K, y^2 = ((g : ZMod K)+m)^2-4*(m : ZMod K)^3) →
        False

/-- With a smaller prefix modulus, test products in a bounded arithmetic
progression. Their sums and hence their ordered endpoints are fixed. -/
def H2 : Prop :=
  ∀ m : ℕ, 1 < m → Odd m → Squarefree m →
    let D := ∑ r ∈ m.primeFactors, m/r
    D < m →
    let g := m-D
    13 ≤ g → g.Coprime m →
    let K := m.primeFactors.lcm (fun r => r-1)
    m.Coprime K → g*K < 2*m →
    ∀ x p q : ℕ,
      0 < x → g*x < 2*m^2 →
      Nat.ModEq m (g*x) (m-1) → Nat.ModEq K (m*x) 1 →
      p*q = x → p+q = (g*x+1)/m →
      p.Prime → q.Prime → p < q → q < m →
      (∀ r ∈ m.primeFactors, r < p) →
      (q-1) ∣ g*p-m → (p-1) ∣ g*q-m →
      (m*x)%12 = 1 → (g+(p-1)*(q-1))%24 = 1 → 4*(m*x)^2 < g^15 →
      (∃ y : ZMod K, y^2 = ((g : ZMod K)+m)^2-4*(m : ZMod K)^3) →
      False

theorem main : H1 → H2 → OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1_H3_R1.H1 := by
  intro hLarge hSmall
  unfold OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1_H3_R1.H1
  intro m hm ho hf
  dsimp only
  set D := ∑ r ∈ m.primeFactors, m/r
  set g := m-D
  intro hD hg _ hgc d hd0 hdd
  set e := (m*m-g)/d
  set p := (m+d)/g
  set q := (m+e)/g
  intro hde hgd hge hp hq hpq hqm hOrder hdK heK hK
  have hBase := restrictions_of_candidate hm ho hf hD hg hd0 hdd
    hde hgd hge hp hq hpq hOrder hdK heK hK
  obtain ⟨⟨hn12, hgap24, hHeight, hEq⟩, _⟩ := hBase
  change (m*p*q)%12=1 at hn12
  change (g+(p-1)*(q-1))%24=1 at hgap24
  change 4*(m*p*q)^2 < g^15 at hHeight
  change g*p*q+1=m*(p+q) at hEq
  let K := m.primeFactors.lcm (fun r => r-1)
  have hKd : K ∣ m*p*q-1 := Finset.lcm_dvd hK
  have hm0 : 0 < m := by omega
  have hn : 0 < m*p*q := Nat.mul_pos (Nat.mul_pos hm0 hp.pos) hq.pos
  have hK0 : K ≠ 0 := by
    intro h
    rw [h] at hKd
    obtain ⟨w, hw⟩ := hKd
    rw [zero_mul] at hw
    have hm_le : m ≤ m*p*q :=
      (Nat.le_mul_of_pos_right m hp.pos).trans (Nat.le_mul_of_pos_right _ hq.pos)
    omega
  have hDelta := prefix_discriminant hn hKd hEq
  obtain ⟨hResM, hResK⟩ := completion_product_congruences hm0 hn hKd hEq
  have hmK := Nat.coprime_of_mul_modEq_one (p*q) hResK
  have hBound := completion_product_lt hm0 hpq hqm hEq
  have hSum : p+q = (g*(p*q)+1)/m := by
    rw [← mul_assoc, hEq, Nat.mul_div_cancel_left _ hm0]
  have hd' : (q-1) ∣ g*p-m := by
    have h := Nat.mul_div_cancel' hgd
    change g*p=m+d at h
    simpa [h] using hdK
  have he' : (p-1) ∣ g*q-m := by
    have h := Nat.mul_div_cancel' hge
    change g*q=m+e at h
    simpa [h] using heK
  have hx12 : (m*(p*q))%12=1 := by simpa only [mul_assoc] using hn12
  have hxHeight : 4*(m*(p*q))^2 < g^15 := by simpa only [mul_assoc] using hHeight
  by_cases hBig : 2*m ≤ g*K
  · have hCap : 2*m^2 ≤ g*(m*K) := by
      have := Nat.mul_le_mul_left m hBig
      nlinarith only [this]
    have hSmallProduct : p*q < m*K :=
      Nat.lt_of_mul_lt_mul_left (hBound.trans_le hCap)
    have hX := completion_product_crt hm0.ne' hK0 hgc hmK hSmallProduct hResM hResK
    exact hLarge m hm ho hf hD hg hgc hmK hBig (p*q) p q
      hX rfl hSum hp hq hpq hqm hOrder hd' he' hx12 hgap24 hxHeight hDelta
  · exact hSmall m hm ho hf hD hg hgc hmK (Nat.lt_of_not_ge hBig) (p*q) p q
      (Nat.mul_pos hp.pos hq.pos) hBound hResM hResK rfl hSum hp hq hpq hqm hOrder
      hd' he' hx12 hgap24 hxHeight hDelta

end OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1_H3_R1_H1_R1
