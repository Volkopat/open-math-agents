import OMAStatements.S_oeis_a123722
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The multiples of three in Layman's square-residue sequence

Write S(m) for the number of distinct squares modulo m. CRT makes S
multiplicative. The half-interval bound for S is sharp on odd moduli
precisely for primes (apart from 1). When 3 divides q, count separately
the classes coprime to three and control the remaining factors.

Sources: https://oeis.org/A123722 and https://oeis.org/A000224.
Credit: @Solitude1312
-/

open OMA.S_oeis_a123722

namespace OMA.A123722

private abbrev S (m : ℕ) := (squares m).card

private lemma residue_lt {m r : ℕ} (hm : 0 < m) (hr : r ∈ squares m) : r < m := by
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hr
  exact Nat.mod_lt _ hm

private lemma project {m a r : ℕ} (ha : 0 < a) (had : a ∣ m) (hr : r ∈ squares m) :
    r % a ∈ squares a := by
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hr
  exact Finset.mem_image.mpr ⟨k % a, Finset.mem_range.mpr (Nat.mod_lt _ ha),
    by rw [Nat.mod_mod_of_dvd _ had, ← Nat.pow_mod]⟩

private lemma crt_count (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (h : m.Coprime n) :
    S (m*n) = S m * S n := by
  change _ = (squares m).card * (squares n).card
  rw [← Finset.card_product]
  apply Finset.card_bij (fun r _ => (r % m, r % n))
  · intro r hr
    exact Finset.mem_product.mpr ⟨project hm (dvd_mul_right _ _) hr, project hn (dvd_mul_left _ _) hr⟩
  · intro r hr s hs he
    have hg : r ≡ s [MOD m*n] := (Nat.modEq_and_modEq_iff_modEq_mul h).mp
      ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
    exact hg.eq_of_lt_of_lt (residue_lt (Nat.mul_pos hm hn) hr) (residue_lt (Nat.mul_pos hm hn) hs)
  · rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp ha
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hb
    let z := Nat.chineseRemainder h x y
    have hz : z.val < m*n := Nat.chineseRemainder_lt_mul h x y hm.ne' hn.ne'
    refine ⟨z.val ^ 2 % (m*n), Finset.mem_image.mpr ⟨z.val, Finset.mem_range.mpr hz, rfl⟩, ?_⟩
    apply Prod.ext
    · change (z.val ^ 2 % (m * n)) % m = a
      rw [Nat.mod_mod_of_dvd _ (dvd_mul_right m n)]
      exact Eq.trans (z.property.1.pow 2) hx
    · change (z.val ^ 2 % (m * n)) % n = b
      rw [Nat.mod_mod_of_dvd _ (dvd_mul_left n m)]
      exact Eq.trans (z.property.2.pow 2) hy

private lemma coarse_bound (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : S (a*b) ≤ b * S a := by
  let f (r : ℕ) := (r / a, r % a)
  have h : (squares (a*b)).card ≤ ((Finset.range b) ×ˢ squares a).card := by
    apply Finset.card_le_card_of_injOn f
    · intro r hr
      have hlt := residue_lt (Nat.mul_pos ha hb) hr
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul ha).mpr
        (by simpa [Nat.mul_comm] using hlt)), project ha (dvd_mul_right _ _) hr⟩
    · intro r _ s _ he
      have hd : r / a = s / a := congrArg Prod.fst he
      have hm : r % a = s % a := congrArg Prod.snd he
      calc
        r = r % a + a*(r/a) := (Nat.mod_add_div _ _).symm
        _ = s % a + a*(s/a) := by rw [hd, hm]
        _ = s := Nat.mod_add_div _ _
  simpa using h

private lemma half_image (m : ℕ) (hm : 0 < m) :
    squares m = (Finset.range (m / 2 + 1)).image (fun k => k ^ 2 % m) := by
  ext r
  unfold squares
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    by_cases h : k ≤ m / 2
    · exact ⟨k, by omega, rfl⟩
    · refine ⟨m-k, by omega, ?_⟩
      change (m-k)^2 ≡ k^2 [MOD m]
      apply Nat.modEq_iff_dvd.mpr
      refine ⟨2*(k:ℤ) - m, ?_⟩
      push_cast [hk.le]
      ring
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, by omega, rfl⟩

private lemma half_bound (m : ℕ) (hm : 0 < m) : S m ≤ m/2+1 := by
  change (squares m).card ≤ _
  rw [half_image m hm]
  exact (Finset.card_image_le).trans_eq (Finset.card_range _)

private lemma diff_squares (x y : ℕ) (h : x ≤ y) :
    y^2 - x^2 = (y-x)*(y+x) := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
  rw [hd, Nat.add_sub_cancel_left]
  apply Nat.sub_eq_of_eq_add
  ring

private lemma prime_count (p : ℕ) (hp : p.Prime) : S p = p/2+1 := by
  change (squares p).card = _
  rw [half_image p hp.pos]
  refine (Finset.card_image_of_injOn ?_).trans (Finset.card_range _)
  have distinct (x y : ℕ) (hxy : x<y) (hy : y ≤ p/2) (he : x^2 ≡ y^2 [MOD p]) : False := by
    have hd := (Nat.modEq_iff_dvd' (Nat.pow_le_pow_left hxy.le 2)).mp he
    rw [diff_squares x y hxy.le] at hd
    rcases hp.dvd_mul.mp hd with h | h
    · have := Nat.le_of_dvd (show 0 < y-x by omega) h
      omega
    · have := Nat.le_of_dvd (show 0 < y+x by omega) h
      omega
  intro x hx y hy he
  have hx' := Finset.mem_range.mp hx
  have hy' := Finset.mem_range.mp hy
  by_contra hn
  rcases lt_or_gt_of_ne hn with h | h
  · exact distinct x y h (by omega) he
  · exact distinct y x h (by omega) he.symm

private lemma odd_collision (u v q : ℕ) (hv : 0 < v) (hvu : v ≤ u)
    (h : (2*u+1)*(2*v+1)=q) :
    ¬ Set.InjOn (fun k : ℕ => k ^ 2 % q) (Finset.range (q/2+1)) := by
  intro hinj
  have hcalc : q = 2*(2*(u*v)+u+v)+1 := by rw [← h]; ring
  have hprod : 0 < u*v := Nat.mul_pos (by omega) hv
  have he : (u-v)^2 ≡ (u+v+1)^2 [MOD q] := by
    apply Nat.modEq_iff_dvd.mpr
    refine ⟨1, ?_⟩
    rw [← h]
    push_cast [hvu]
    ring
  have hc := hinj (x₁ := u-v) (x₂ := u+v+1)
    (Finset.mem_range.mpr (by omega)) (Finset.mem_range.mpr (by omega)) he
  omega

private lemma odd_maximal (q : ℕ) (hq : 1 < q) (ho : Odd q) (hc : 2 * S q = q+1) : q.Prime := by
  obtain ⟨t, ht⟩ := ho
  have hcard : (squares q).card = q/2+1 := by change 2*(squares q).card = _ at hc; omega
  rw [half_image q (by omega)] at hcard
  have hi := Finset.card_image_iff.mp (hcard.trans (Finset.card_range _).symm)
  by_contra hnp
  obtain ⟨a,b,ha,hb,he⟩ := (Nat.not_prime_iff_exists_mul_eq hq).mp hnp
  have habodd : Odd (a*b) := he ▸ ⟨t, ht⟩
  obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := Nat.odd_mul.mp habodd
  have upos : 0<u := by
    by_contra! h
    have h1 : a=1 := by omega
    simp_all
  have vpos : 0<v := by
    by_contra! h
    have h1 : b=1 := by omega
    simp_all
  rw [hu, hv] at he
  rcases le_total v u with huv | hvu
  · exact odd_collision u v q vpos huv he hi
  · exact odd_collision v u q upos hvu ((Nat.mul_comm _ _).trans he) hi

private lemma higher_power_lower (e : ℕ) (he : 2 ≤ e) : 3^e + 2 ≤ S (3 * 3^e) := by
  let q := 3^e
  let m := 3*q
  let f (k : ℕ) := (3*k+1)^2 % m
  let units := (Finset.range q).image f
  have h9 : 9 ≤ q := Nat.pow_le_pow_right (by decide : 0 < 3) he
  have hm : m = 3^(e+1) := by simp [m, q, pow_succ, Nat.mul_comm]
  have hmgt : 9 < m := by dsimp [m]; omega
  have fmod (k : ℕ) : f k % 3 = 1 := by
    dsimp [f]
    rw [Nat.mod_mod_of_dvd _ (show 3 ∣ m from ⟨q, rfl⟩),
      show (3*k+1)^2 = 3*(3*k^2+2*k)+1 by ring]
    simp
  have is_unit_class (r : ℕ) (hr : r ∈ units) : r % 3 = 1 := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hr
    exact fmod k
  have hz : 0 ∉ units := fun h => by have := is_unit_class _ h; omega
  have hn : 9 ∉ units := fun h => by have := is_unit_class _ h; omega
  have card : units.card = q := by
    refine (Finset.card_image_of_injOn ?_).trans (Finset.card_range _)
    have sep (x y : ℕ) (hxy : x<y) (hy : y<q) (hval : f x = f y) : False := by
      have hxy' : 3*x+1 ≤ 3*y+1 := by omega
      have hd := (Nat.modEq_iff_dvd' (Nat.pow_le_pow_left hxy' 2)).mp hval
      rw [diff_squares _ _ hxy'] at hd
      have cop : m.Coprime (3*y+1+(3*x+1)) := by
        rw [hm]
        apply Nat.Coprime.pow_left
        exact Nat.prime_three.coprime_iff_not_dvd.mpr (by omega)
      have := Nat.le_of_dvd (show 0 < 3*y+1-(3*x+1) by omega) (cop.dvd_of_dvd_mul_right hd)
      dsimp [m] at this
      omega
    intro x hx y hy hxy
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · exact sep x y h (Finset.mem_range.mp hy) hxy
    · exact sep y x h (Finset.mem_range.mp hx) hxy.symm
  have sub : insert 0 (insert 9 units) ⊆ squares m := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), by simp⟩
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact Finset.mem_image.mpr ⟨3, Finset.mem_range.mpr (by omega), Nat.mod_eq_of_lt hmgt⟩
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
      have hlt := Finset.mem_range.mp hk
      exact Finset.mem_image.mpr ⟨3*k+1, Finset.mem_range.mpr (by dsimp [m]; omega), rfl⟩
  have hc := Finset.card_le_card sub
  rw [Finset.card_insert_of_notMem (by simp [hz]), Finset.card_insert_of_notMem hn, card] at hc
  exact hc

private lemma even_excluded (q : ℕ) (hq : 0 < q) (he : Even q) : S (3*q) ≠ q+1 := by
  intro hc
  by_cases h8 : 8 ∣ q
  · obtain ⟨t, ht⟩ := h8
    have h := coarse_bound 24 t (by decide) (by omega)
    rw [show S 24 = 6 by decide, show 24*t = 3*q by omega, hc] at h
    omega
  by_cases h4 : 4 ∣ q
  · obtain ⟨t, ht⟩ := h4
    have cp : Nat.Coprime 2 (3*t) := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
    have cp4 : Nat.Coprime 4 (3*t) := cp.pow_left 2
    rw [show 3*q = 4*(3*t) by omega, crt_count 4 (3*t) (by decide) (by omega) cp4,
      show S 4 = 2 by decide] at hc
    omega
  · obtain ⟨t, ht⟩ := he
    have cp : Nat.Coprime 2 (3*t) := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
    rw [show 3*q = 2*(3*t) by omega, crt_count 2 (3*t) (by decide) (by omega) cp,
      show S 2 = 2 by decide] at hc
    omega

private lemma mixed_bound (t r : ℕ) (ht : 3 ≤ t) (hr : 5 ≤ r)
    (hto : Odd t) (hro : Odd r) (hcop : (3*t).Coprime r) : S (3*t*r) ≤ t*r := by
  rw [crt_count (3*t) r (by omega) (by omega) hcop]
  have hprod := Nat.mul_le_mul (half_bound (3*t) (by omega)) (half_bound r (by omega))
  have h1 : 2*((3*t)/2+1)=3*t+1 := by obtain ⟨j, hj⟩ := hto; omega
  have h2 : 2*(r/2+1)=r+1 := by obtain ⟨j, hj⟩ := hro; omega
  have hscaled : 4*(((3*t)/2+1)*(r/2+1))=(3*t+1)*(r+1) := by
    rw [← h1, ← h2]
    ring
  have hineq : (3*t+1)*(r+1) ≤ 4*(t*r) := by
    obtain ⟨a, ha⟩ : ∃ a, t=a+3 := ⟨t-3,by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, r=b+5 := ⟨r-5,by omega⟩
    rw [ha,hb]
    nlinarith
  omega

theorem classification (q : ℕ) (hq : 1 < q) : S (3*q) = q+1 ↔ Odd q ∧ q.Prime := by
  constructor
  · intro hc
    have ho : Odd q := Nat.not_even_iff_odd.mp (fun he => even_excluded q (by omega) he hc)
    refine ⟨ho, ?_⟩
    by_cases h3 : 3 ∣ q
    · let e := q.factorization 3
      let r := q / 3^e
      have he : 0 < e := Nat.Prime.factorization_pos_of_dvd Nat.prime_three (by omega) h3
      have hs : 3^e*r=q := Nat.ordProj_mul_ordCompl_eq_self q 3
      have hr : 0 < r := Nat.ordCompl_pos 3 (by omega : q ≠ 0)
      have hnd : ¬ 3 ∣ r := Nat.not_dvd_ordCompl Nat.prime_three (by omega : q ≠ 0)
      have cp : Nat.Coprime 3 r := Nat.prime_three.coprime_iff_not_dvd.mpr hnd
      by_cases h1 : r=1
      · have hqeq : 3^e=q := by simpa [h1] using hs
        by_cases he1 : e=1
        · have : q=3 := by simpa [he1] using hqeq.symm
          simpa [this] using Nat.prime_three
        · have bad := higher_power_lower e (by omega)
          rw [hqeq, hc] at bad
          omega
      · have hro : Odd r := (Nat.odd_mul.mp (hs ▸ ho)).2
        have h5 : 5 ≤ r := by
          obtain ⟨j, hj⟩ := hro
          omega
        have hcp : (3*3^e).Coprime r := by
          rw [← pow_succ']
          exact cp.pow_left _
        have hge : 3 ≤ 3^e := Nat.pow_le_pow_right (by decide : 0<3) he
        have hto : Odd (3^e) := (show Odd (3:ℕ) from ⟨1,rfl⟩).pow
        have bad := mixed_bound (3^e) r hge h5 hto hro hcp
        rw [Nat.mul_assoc, hs, hc] at bad
        omega
    · rw [crt_count 3 q (by decide) (by omega) (Nat.prime_three.coprime_iff_not_dvd.mpr h3),
        show S 3 = 2 by decide] at hc
      exact odd_maximal q hq ho hc
  · rintro ⟨ho, hp⟩
    by_cases h3 : q=3
    · subst q
      decide
    have hnd : ¬ 3 ∣ q := by
      intro hd
      rcases (Nat.dvd_prime hp).mp hd with h | h <;> omega
    rw [crt_count 3 q (by decide) (by omega) (Nat.prime_three.coprime_iff_not_dvd.mpr hnd),
      show S 3 = 2 by decide, prime_count q hp]
    obtain ⟨t, ht⟩ := ho
    omega

private lemma before_three : preceding 3 ≤ 1 := by
  classical
  have h2 : ¬ qualifies 2 := by unfold qualifies squares; decide
  have hsub : (Finset.Ico 1 3).filter qualifies ⊆ ({1} : Finset ℕ) := by
    intro k hk
    obtain ⟨hi, hv⟩ := Finset.mem_filter.mp hk
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hi
    rcases (show k=1 ∨ k=2 by omega) with rfl | rfl
    · simp
    · exact (h2 hv).elim
  simpa [preceding] using Finset.card_le_card hsub

end OMA.A123722

theorem OMA.solution : type_of% @OMA.S_oeis_a123722.main := by
  constructor
  · intro m hm hi hd
    obtain ⟨q,hq⟩ := hd
    have hmpos := hm.1
    have hq1 : 1<q := by
      by_contra! h
      have hm3 : m=3 := by omega
      have := OMA.A123722.before_three
      rw [hm3] at hi
      omega
    have hc := hm.2
    rw [hq, show (3*q+3)/3=q+1 by omega] at hc
    rw [hq, Nat.mul_div_cancel_left _ (by decide)]
    exact ((OMA.A123722.classification q hq1).mp hc).2
  · intro p hp ho
    refine ⟨Nat.mul_pos (by decide) hp.pos, ?_⟩
    rw [show (3*p+3)/3=p+1 by omega]
    exact (OMA.A123722.classification p hp.one_lt).mpr ⟨ho,hp⟩
