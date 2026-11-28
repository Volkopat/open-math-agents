import FormalConjectures.ErdosProblems.«889»

/-!
A reduction of the lowercase Erdős 889 finiteness problem. The odd case has
also been settled in the earlier R1 reduction. Here the new restriction on
even solutions comes from factoring an odd power plus one at offset two
and applying the lifting-the-exponent lemma to its odd cofactor. Fourth powers
and prime squares admit additional restrictions by elementary Pell descents
and quadratic reciprocity. The final steps also use factorizations in the
Eisenstein integers, modular certificates, and classifications of higher powers.
-/

namespace OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

open Erdos889

open Finset

lemma fresh_iff {n k p : ℕ} (hp : 0 < p) (hd : p ∣ n+k) :
    (∀ i ∈ range k, ¬p ∣ n+i) ↔ k < p := by
  constructor
  · intro h
    by_contra! hle
    have hdiff : n + (k-p) = n+k-p := by omega
    exact h (k-p) (mem_range.mpr (by omega)) (hdiff ▸ Nat.dvd_sub hd (dvd_refl p))
  · intro h i hi hdiv
    have hi' := mem_range.mp hi
    have hsub : n+k-(n+i) = k-i := by omega
    have hd' : p ∣ k-i := hsub ▸ Nat.dvd_sub hd hdiv
    have := Nat.le_of_dvd (by omega : 0 < k-i) hd'
    omega

theorem v_as_card (n k : ℕ) :
    v n k = ((n+k).primeFactors.filter (k < ·)).card := by
  unfold v
  congr 1
  ext p
  simp only [mem_filter]
  exact and_congr_right fun h => fresh_iff (Nat.prime_of_mem_primeFactors h).pos
    (Nat.dvd_of_mem_primeFactors h)

lemma offset_le {n k : ℕ} (hk : 1 ≤ k) :
    (v n k : ℕ∞) ≤ v_l 1 n :=
  le_iSup_of_le k (le_iSup_of_le hk le_rfl)

lemma offset_le_one {n k : ℕ} (h : v_l 1 n = 1) (hk : 1 ≤ k) : v n k ≤ 1 := by
  have hh := offset_le (n := n) hk
  rw [h] at hh
  exact_mod_cast hh

lemma two_primes {n k p q : ℕ} (hk : 0 < k)
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hkp : k < p) (hkq : k < q) (dp : p ∣ n+k) (dq : q ∣ n+k) : v_l 1 n ≠ 1 := by
  intro h
  have hh := offset_le_one h hk
  rw [v_as_card, Finset.card_le_one] at hh
  exact hne (hh p (mem_filter.mpr ⟨hp.mem_primeFactors dp (by omega), hkp⟩)
    q (mem_filter.mpr ⟨hq.mem_primeFactors dq (by omega), hkq⟩))

lemma prime_power_at {n k : ℕ} (h : v_l 1 n = 1) (hk : 0 < k)
    (hn : 2 ≤ n+k) (eligible : ∀ p, p.Prime → p ∣ n+k → k < p) :
    IsPrimePow (n+k) := by
  by_contra bad
  obtain ⟨p, hp, q, hq, hpq⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le hn).mp bad
  obtain ⟨pp, dp, _⟩ := Nat.mem_primeFactors.mp hp
  obtain ⟨pq, dq, _⟩ := Nat.mem_primeFactors.mp hq
  exact two_primes hk pp pq hpq (eligible p pp dp) (eligible q pq dq) dp dq h

theorem prime_power_succ {n : ℕ} (hn : 0 < n) (h : v_l 1 n = 1) : IsPrimePow (n+1) :=
  prime_power_at h (by decide) (by omega) (fun _ hp _ => hp.one_lt)

lemma square_power_neighbor {y a : ℕ} (hy : 2 ≤ y) (he : y^2 = 2^a+1) :
    a = 3 := by
  have fac : (y-1)*(y+1) = 2^a := by
    have : y-1+1=y := by omega
    nlinarith
  obtain ⟨u, _, hu⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (fac ▸ dvd_mul_right (y-1) (y+1))
  obtain ⟨w, _, hw⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (fac ▸ dvd_mul_left (y+1) (y-1))
  have small : y ≤ 3 := by
    by_contra! large
    have hu2 : 2 ≤ u := by by_contra! z; interval_cases u <;> omega
    have hw2 : 2 ≤ w := by by_contra! z; interval_cases w <;> omega
    have du : 4 ∣ y-1 := hu ▸ (pow_dvd_pow (2 : ℕ) hu2)
    have dw : 4 ∣ y+1 := hw ▸ (pow_dvd_pow (2 : ℕ) hw2)
    omega
  have yy : y = 3 := by
    interval_cases y
    · have h3 : 3 ∣ 2^a := by norm_num at he; exact ⟨1, by omega⟩
      have := Nat.prime_three.dvd_of_dvd_pow h3
      omega
    · rfl
  subst y
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  norm_num at he ⊢
  omega

lemma prime_power_neighbor {a : ℕ} (ha : a ≠ 0) (h : IsPrimePow (2^a+1)) :
    a = 3 ∨ ∃ t : ℕ, a = 2^t := by
  obtain ⟨p, b, pp, hb, he⟩ := (isPrimePow_nat_iff _).mp h
  by_cases even : Even b
  · obtain ⟨j, rfl⟩ := even
    left
    apply square_power_neighbor (y := p^j)
    · have := pp.two_le
      exact Nat.succ_le_of_lt (Nat.one_lt_pow (by omega : j ≠ 0) pp.one_lt)
    · rw [pow_two, ← pow_add, he]
  · have ob := Nat.not_even_iff_odd.mp even
    have op : Odd p := pp.odd_of_ne_two (by
      rintro rfl
      have d₁ := dvd_pow_self (2 : ℕ) ha
      have d₂ := dvd_pow_self (2 : ℕ) hb.ne'
      omega)
    let s := ∑ i ∈ range b, p^i
    have os : Odd s := by
      dsimp [s]
      rw [Finset.odd_sum_iff_odd_card_odd]
      simpa [op.pow] using ob
    have prod : s*(p-1) = 2^a := by
      simpa [s, he] using geom_sum_mul_of_one_le pp.one_le b
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (prod ▸ dvd_mul_right s (p-1))
    have j0 : j = 0 := by
      by_contra bad
      have d := dvd_pow_self (2 : ℕ) bad
      rw [← hj] at d
      obtain ⟨w, hw⟩ := os
      omega
    have s1 : s = 1 := by simp [hj, j0]
    have peq : p = 2^a+1 := by rw [s1, one_mul] at prod; have := pp.two_le; omega
    exact Or.inr (Nat.pow_of_pow_add_prime (by decide) ha (peq ▸ pp))

/-- Six modular orbits rule out every exponent index at least three. -/
lemma orbit {s m r : ℕ} (base : Nat.ModEq m (2^(2^s)) r)
    (step : Nat.ModEq m (r^64) r) (j : ℕ) : Nat.ModEq m (2^(2^(s+6*j))) r := by
  induction j with
  | zero => simpa using base
  | succ j ih =>
    rw [show s+6*(j+1) = (s+6*j)+6 by omega, pow_add, pow_mul]
    exact (ih.pow 64).trans step

lemma orbit_witness {n t s k p q r : ℕ} (hn : n+1 = 2^(2^t))
    (j : ℕ) (ht : t = s+6*j) (hk : 0 < k)
    (pp : p.Prime) (pq : q.Prime) (hne : p ≠ q) (hp : k < p) (hq : k < q)
    (base : Nat.ModEq (p*q) (2^(2^s)) r) (step : Nat.ModEq (p*q) (r^64) r)
    (hit : Nat.ModEq (p*q) (r+(k-1)) 0) : v_l 1 n ≠ 1 := by
  have hh := (orbit base step j).add_right (k-1)
  rw [← ht, ← hn, show n+1+(k-1) = n+k by omega] at hh
  have d := Nat.modEq_zero_iff_dvd.mp (hh.trans hit)
  exact two_primes hk pp pq hne hp hq ((dvd_mul_right p q).trans d) ((dvd_mul_left q p).trans d)

set_option maxRecDepth 8192 in
lemma orbit_excluded {n t : ℕ} (hn : n+1 = 2^(2^t)) (ht : 3 ≤ t) : v_l 1 n ≠ 1 := by
  let j := (t-3)/6
  have cases : t=3+6*j ∨ t=4+6*j ∨ t=5+6*j ∨ t=6+6*j ∨ t=7+6*j ∨ t=8+6*j := by
    dsimp [j]; omega
  rcases cases with h|h|h|h|h|h
  · apply orbit_witness (k:=4) (p:=7) (q:=37) (r:=256) hn j h <;> decide
  · apply orbit_witness (k:=5) (p:=29) (q:=113) (r:=3273) hn j h <;> decide
  · apply orbit_witness (k:=14) (p:=19) (q:=29) (r:=538) hn j h <;> decide
  · apply orbit_witness (k:=6) (p:=7) (q:=29) (r:=198) hn j h <;> decide
  · apply orbit_witness (k:=5) (p:=13) (q:=29) (r:=373) hn j h <;> decide
  · apply orbit_witness (k:=17) (p:=241) (q:=433) (r:=104337) hn j h <;> decide

lemma odd_forward {n : ℕ} (odd : Odd n) (h : v_l 1 n = 1) :
    n = 1 ∨ n = 3 ∨ n = 7 ∨ n = 15 := by
  obtain ⟨w, hw⟩ := odd
  have hp := prime_power_succ (by omega : 0 < n) h
  have h2 : (n+1).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr (by omega)
  obtain ⟨a, ha⟩ : ∃ a : ℕ, n+1 = 2^a := ⟨_, by simpa [h2] using hp.minFac_pow_factorization_eq.symm⟩
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha; omega
  have hnext : IsPrimePow (n+2) := prime_power_at h (by decide) (by omega) (by
    intro p pp dp
    have := pp.two_le
    by_contra! hh
    have : p=2 := by omega
    subst p
    omega)
  rw [show n+2=2^a+1 by omega] at hnext
  rcases prime_power_neighbor ha0 hnext with rfl | ⟨t, rfl⟩
  · norm_num at ha; omega
  · have ht : t < 3 := by by_contra! ht; exact orbit_excluded ha ht h
    interval_cases t <;> norm_num at ha <;> omega

lemma square_bound {n k : ℕ} (hk : 0 < k) (h : 1 < v n k) : k*k < n+k := by
  rw [v_as_card, Finset.one_lt_card_iff_nontrivial] at h
  obtain ⟨p, hp, q, hq, hne⟩ := h
  obtain ⟨pm, pk⟩ := mem_filter.mp hp
  obtain ⟨qm, qk⟩ := mem_filter.mp hq
  obtain ⟨pp, dp, _⟩ := Nat.mem_primeFactors.mp pm
  obtain ⟨pq, dq, _⟩ := Nat.mem_primeFactors.mp qm
  exact (Nat.mul_lt_mul_of_lt_of_le (by omega) (by omega) (by omega)).trans_le
    (Nat.le_of_dvd (by omega) (Nat.Prime.dvd_mul_of_dvd_ne hne pp pq dp dq))

lemma small_solution {n : ℕ} (hn : n ≤ 26) (lo : 1 ≤ v n 1)
    (vals : ∀ k : Fin 7, 0 < k.val → v n k.val ≤ 1) : v_l 1 n = 1 := by
  apply le_antisymm
  · apply iSup_le; intro k; apply iSup_le; intro hk
    have hv : v n k ≤ 1 := by
      by_cases small : k < 7
      · exact vals ⟨k, small⟩ hk
      · by_contra! hh
        have := square_bound hk hh
        nlinarith [show 7 ≤ k by omega, Nat.zero_le ((k-7)*(k-7))]
    exact_mod_cast hv
  · exact (by exact_mod_cast lo : (1 : ℕ∞) ≤ (v n 1 : ℕ∞)).trans (offset_le (by decide))

theorem odd_classification {n : ℕ} (h : Odd n) :
    v_l 1 n = 1 ↔ n = 1 ∨ n = 3 ∨ n = 7 ∨ n = 15 := by
  refine ⟨odd_forward h, ?_⟩
  rintro (rfl|rfl|rfl|rfl) <;> apply small_solution <;> decide +kernel


/-- If a solution is one less than an odd cube, its cube root is one
less than a power of two. -/
theorem cube_root_neighbor {n u : ℕ} (hu : Odd u) (large : 1 < u)
    (hn : n+1 = u^3) (h : v_l 1 n = 1) : ∃ b : ℕ, u+1 = 2^b := by
  obtain ⟨w, hw⟩ := hu
  have wpos : 0 < w := by omega
  let y := 4*w^2 + 2*w + 1
  have ybig : 3 < y := by dsimp [y]; nlinarith [Nat.mul_self_le_mul_self wpos]
  have yodd : y = 2*(2*w^2+w)+1 := by dsimp [y]; ring
  have no9 : ¬9 ∣ y := by
    change ¬9 ∣ 4*w^2+2*w+1
    rw [Nat.dvd_iff_mod_eq_zero]
    have z := Nat.mod_lt w (by decide : 0 < 9)
    have reduce : (4*w^2+2*w+1)%9 = (4*(w%9)^2+2*(w%9)+1)%9 := by
      have m := (Nat.mod_modEq w 9).symm
      exact (((m.pow 2).mul_left 4).add (m.mul_left 2)).add_right 1
    rw [reduce]
    interval_cases hmod : w%9 <;> decide
  have other : ∃ q : ℕ, q.Prime ∧ q ∣ y ∧ q ≠ 3 := by
    by_contra! none
    have eq := Nat.eq_prime_pow_of_unique_prime_dvd (n := y) (p := 3) (by omega)
      (fun {q} => none q)
    let e := y.primeFactorsList.length
    change y = 3^e at eq
    have e2 : 2 ≤ e := by
      by_contra! small
      interval_cases e <;> simp_all
    exact no9 (eq ▸ pow_dvd_pow (3 : ℕ) e2)
  obtain ⟨q, pq, dy, q3⟩ := other
  have qbig : 2 < q := by
    have := pq.two_le
    by_contra! small
    have eq : q=2 := by omega
    rw [eq, yodd] at dy
    omega
  have fac : n+2 = (u+1)*y := by
    rw [hw] at hn ⊢
    dsimp [y]
    nlinarith
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) ?_⟩
  intro p pp dp
  by_contra p2
  have pbig := lt_of_le_of_ne pp.two_le (Ne.symm p2)
  have neq : p ≠ q := by
    rintro rfl
    have eq : y + 3*(u+1) = (u+1)^2+3 := by dsimp [y]; rw [hw]; ring
    have dl := dvd_add dy (dvd_mul_of_dvd_right dp 3)
    rw [eq] at dl
    have ds : p ∣ (u+1)^2 := dp.trans (dvd_pow_self _ (by decide : 2 ≠ 0))
    exact q3 ((Nat.prime_dvd_prime_iff_eq pp Nat.prime_three).mp ((Nat.dvd_add_iff_right ds).mpr dl))
  apply two_primes (k := 2) (by decide) pp pq neq pbig qbig _ _ h
  · rw [fac]; exact dvd_mul_of_dvd_left dp _
  · rw [fac]; exact dvd_mul_of_dvd_right dy _


/-- Reduce an exponent modulo a verified multiplicative period. -/
lemma pow_cycle {a d m : ℕ} (period : Nat.ModEq m (a^d) 1) (j : ℕ) :
    Nat.ModEq m (a^j) (a^(j%d)) := by
  calc
    a^j = a^(j%d) * (a^d)^(j/d) := by rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    _ ≡ a^(j%d) * 1^(j/d) [MOD m] := (period.pow _).mul_left _
    _ = _ := by simp

lemma small_prime {p : ℕ} (hp : p.Prime) (le : p ≤ 9) :
    p=2 ∨ p=3 ∨ p=5 ∨ p=7 := by
  interval_cases p <;> norm_num at *

lemma large_factor {m p : ℕ} (hm : 0 < m)
    (small : ∀ q : ℕ, q.Prime → q ∣ m → q ≤ 9 → q=p)
    (exclude : ∀ e : ℕ, m ≠ p^e) : ∃ q : ℕ, q.Prime ∧ 9 < q ∧ q ∣ m := by
  by_contra! none
  exact exclude _ (Nat.eq_prime_pow_of_unique_prime_dvd hm.ne'
    (fun {q} hq dq => small q hq dq (by by_contra! z; exact none q hq z dq)))

lemma seven_pow_mod_eight (b : ℕ) : 7^b%8=1 ∨ 7^b%8=7 := by
  have h := pow_cycle (a:=7) (d:=2) (m:=8) (by decide) b
  change 7^b%8 = 7^(b%2)%8 at h
  have bound := Nat.mod_lt b (by decide : 0<2)
  interval_cases z : b%2 <;> simp_all

lemma three_pow_mod_eight (b : ℕ) : 3^b%8=1 ∨ 3^b%8=3 := by
  have h := pow_cycle (a:=3) (d:=2) (m:=8) (by decide) b
  change 3^b%8 = 3^(b%2)%8 at h
  have bound := Nat.mod_lt b (by decide : 0<2)
  interval_cases z : b%2 <;> simp_all

lemma odd_index_offsets {j : ℕ} (hj : Odd j) :
    2^j%3=2 ∧ ¬5 ∣ 2^j+1 ∧ ¬7 ∣ 2^j+1 := by
  have h3 := pow_cycle (a:=2) (d:=2) (m:=3) (by decide) j
  have h5 := pow_cycle (a:=2) (d:=4) (m:=5) (by decide) j
  have h7 := pow_cycle (a:=2) (d:=3) (m:=7) (by decide) j
  change 2^j%3=2^(j%2)%3 at h3
  change 2^j%5=2^(j%4)%5 at h5
  change 2^j%7=2^(j%3)%7 at h7
  obtain ⟨w, hw⟩ := hj
  have odd : j%2=1 := by omega
  rw [odd] at h3
  refine ⟨h3, ?_, ?_⟩
  · have cases : j%4=1 ∨ j%4=3 := by omega
    rcases cases with e|e <;> rw [e] at h5 <;> norm_num at h5 <;> omega
  · have bound := Nat.mod_lt j (by decide : 0<3)
    interval_cases e : j%3 <;> norm_num at h7 <;> omega

/-- Offset nine supplies two large primes when the cube root is
one less than two to an odd exponent of at least five. -/
lemma cube_offset_nine {n u j : ℕ} (hn : n+1=u^3) (hu : u+1=2^j)
    (hj : 5 ≤ j) (oj : Odd j) : v_l 1 n ≠ 1 := by
  obtain ⟨m3, m5, m7⟩ := odd_index_offsets oj
  have d8 : 8 ∣ 2^j := pow_dvd_pow (2 : ℕ) (by omega : 3 ≤ j)
  have u8 : u%8=7 := by omega
  obtain ⟨p, pp, pbig, dp⟩ : ∃ p : ℕ, p.Prime ∧ 9 < p ∧ p ∣ u+2 := by
    apply large_factor (p:=3) (by omega)
    · intro q pq dq lq
      rcases small_prime pq lq with rfl|rfl|rfl|rfl <;> omega
    · intro e eq
      have epos : 0 < e := by
        by_contra! z
        have e0 : e=0 := by omega
        rw [e0, pow_zero] at eq
        omega
      have hprime : IsPrimePow (2^j+1) := (isPrimePow_nat_iff _).mpr
        ⟨3, e, Nat.prime_three, epos, by omega⟩
      rcases prime_power_neighbor (by omega) hprime with z|⟨t, ht⟩
      · omega
      · by_cases t0 : t=0
        · simp [t0] at ht; omega
        · have d2 := dvd_pow_self (2 : ℕ) t0
          obtain ⟨w, hw⟩ := oj
          omega
  let z := (u-1)/3
  have uz : u=3*z+1 := by dsimp [z]; omega
  let y := 3*z^2+1
  have z8 : z%8=2 := by omega
  have y8 : y%8=5 := by
    have m : Nat.ModEq 8 z 2 := z8
    exact ((m.pow 2).mul_left 3).add_right 1
  have no5 : ¬5 ∣ y := by
    have m := (Nat.mod_modEq z 5).symm
    have v := ((m.pow 2).mul_left 3).add_right 1
    change y%5 = (3*(z%5)^2+1)%5 at v
    have bound := Nat.mod_lt z (by decide : 0<5)
    interval_cases e : z%5 <;> norm_num at v <;> omega
  obtain ⟨q, pq, qbig, dq⟩ : ∃ q : ℕ, q.Prime ∧ 9 < q ∧ q ∣ y := by
    apply large_factor (p:=7) (by dsimp [y]; omega)
    · intro q pq dq lq
      have y3 : y%3=1 := by simp [y]
      rcases small_prime pq lq with rfl|rfl|rfl|rfl <;> omega
    · intro e eq
      have := seven_pow_mod_eight e
      omega
  have neq : p ≠ q := by
    rintro rfl
    have eq : 3*y+6*(u+2)=(u+2)^2+12 := by dsimp [y]; rw [uz]; ring
    have dl := dvd_add (dvd_mul_of_dvd_right dq 3) (dvd_mul_of_dvd_right dp 6)
    rw [eq] at dl
    have ds := dp.trans (dvd_pow_self (u+2) (by decide : 2 ≠ 0))
    have d12 := (Nat.dvd_add_iff_right ds).mpr dl
    have := Nat.le_of_dvd (by decide : 0<12) d12
    interval_cases p <;> norm_num at *
  have fac : n+9 = (u+2)*(3*y) := by dsimp [y]; rw [uz] at hn ⊢; nlinarith
  apply two_primes (k:=9) (by decide) pp pq neq pbig qbig
  · rw [fac]; exact dvd_mul_of_dvd_left dp _
  · rw [fac]; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right dq _) _

/-- The only solution immediately below an odd cube greater than one is 26. -/
theorem cube_classification {n u : ℕ} (hu : Odd u) (large : 1 < u) (hn : n+1=u^3) :
    v_l 1 n = 1 ↔ n=26 := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := cube_root_neighbor hu large hn h
    by_cases small : j < 4
    · interval_cases j
      · norm_num at hj
        omega
      · norm_num at hj
        omega
      · have u3 : u=3 := by norm_num at hj; omega
        norm_num [u3] at hn
        omega
      · have u7 : u=7 := by norm_num at hj; omega
        have n342 : n=342 := by norm_num [u7] at hn; omega
        subst n
        exact False.elim (two_primes (n:=342) (k:=3) (p:=5) (q:=23)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) h)
    · have d8 : 8 ∣ 2^j := pow_dvd_pow (2 : ℕ) (by omega : 3 ≤ j)
      by_cases oj : Odd j
      · have j5 : 5≤j := by obtain ⟨w, hw⟩ := oj; omega
        exact False.elim (cube_offset_nine hn hj j5 oj h)
      · have j2 : j%2=0 := by rw [Nat.odd_iff] at oj; omega
        have m := pow_cycle (a:=2) (d:=2) (m:=3) (by decide) j
        change 2^j%3=2^(j%2)%3 at m
        rw [j2] at m
        norm_num at m
        have du : 3 ∣ u := by omega
        have nl : 0 < n := by have := Nat.one_lt_pow (by decide : 3 ≠ 0) large; omega
        have hp := prime_power_succ nl h
        rw [hn, isPrimePow_pow_iff (by decide : 3 ≠ 0)] at hp
        obtain ⟨p, e, pp, _, he⟩ := (isPrimePow_nat_iff _).mp hp
        have d : 3 ∣ p^e := he ▸ du
        have p3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pp).mp (Nat.prime_three.dvd_of_dvd_pow d)
        rw [← p3] at he
        have := three_pow_mod_eight e
        omega
  · rintro rfl
    apply small_solution <;> decide +kernel

/-- Apart from 26, a positive even solution must precede an odd prime
power whose exponent is not divisible by three. -/
theorem even_solution_shape {n : ℕ} (hn : 0 < n) (ev : Even n) (h26 : n ≠ 26)
    (h : v_l 1 n = 1) :
    ∃ p a : ℕ, p.Prime ∧ Odd p ∧ 0 < a ∧ ¬3 ∣ a ∧ n+1 = p^a := by
  obtain ⟨p, a, pp, ha, he⟩ := (isPrimePow_nat_iff _).mp (prime_power_succ hn h)
  have op : Odd p := pp.odd_of_ne_two (by
    rintro rfl
    have d := dvd_pow_self (2 : ℕ) ha.ne'
    rw [he] at d
    obtain ⟨w, hw⟩ := ev
    omega)
  refine ⟨p, a, pp, op, ha, ?_, he.symm⟩
  rintro ⟨b, rfl⟩
  have bpos : b ≠ 0 := by omega
  have cube : n+1=(p^b)^3 := by rw [← he, ← pow_mul, Nat.mul_comm]
  exact h26 ((cube_classification op.pow (Nat.one_lt_pow bpos pp.one_lt) cube).mp h)

/-- The cofactor of x+1 in an odd power plus one is odd and grows
faster than the exponent for every odd x greater than one. -/
lemma odd_cofactor {x r : ℕ} (ox : Odd x) (hx : 1 < x) (orr : Odd r) (hr : 1 < r) :
    ∃ c : ℕ, Odd c ∧ r < c ∧ x^r+1 = (x+1)*c := by
  obtain ⟨w, hw⟩ := ox
  obtain ⟨j, rfl⟩ := orr
  have wp : 0 < w := by omega
  have hx3 : 3 ≤ x := by omega
  have aux (i : ℕ) : ∃ z : ℕ, 2*i ≤ z ∧ x^(2*i+1)+1 = (x+1)*(2*z+1) := by
    induction i with
    | zero => exact ⟨0, by decide, by simp⟩
    | succ i ih =>
      obtain ⟨z, hz, he⟩ := ih
      refine ⟨x^2*z+w*x, ?_, ?_⟩
      · have mulz : z ≤ x^2*z := by
          simpa using Nat.mul_le_mul_right z (show 1 ≤ x^2 by exact Nat.one_le_pow _ _ (by omega))
        have mulw : 3 ≤ w*x := by simpa using Nat.mul_le_mul wp hx3
        omega
      · rw [show 2*(i+1)+1 = (2*i+1)+2 by omega, pow_add]
        have scaled := congrArg (fun m : ℕ => m*x^2) he
        rw [hw] at scaled ⊢
        nlinarith only [scaled]
  obtain ⟨z, hz, he⟩ := aux j
  exact ⟨2*z+1, ⟨z,rfl⟩, by omega, he⟩

/-- If an odd power plus one has at most one odd prime divisor, its base
is one below a power of two. -/
theorem odd_root_with_unique_odd_prime {x r : ℕ} (ox : Odd x) (hx : 1 < x)
    (orr : Odd r) (hr : 1 < r)
    (unique : ∀ p q : ℕ, p.Prime → q.Prime → 2<p → 2<q →
      p ∣ x^r+1 → q ∣ x^r+1 → p=q) : ∃ b : ℕ, x+1=2^b := by
  obtain ⟨c, oc, hc, fac⟩ := odd_cofactor ox hx orr hr
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) ?_⟩
  intro p pp dp
  by_contra p2
  have pbig := lt_of_le_of_ne pp.two_le (Ne.symm p2)
  have pure : c=p^c.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
    intro q pq dq
    by_contra different
    have qbig : 2 < q := by
      have := pq.two_le
      obtain ⟨w, hw⟩ := oc
      by_contra! z
      have q2 : q=2 := by omega
      rw [q2] at dq
      omega
    exact different (unique q p pq pp qbig pbig (fac ▸ dvd_mul_of_dvd_right dq _)
      (fac ▸ dvd_mul_of_dvd_left dp _)))
  let _ : Fact p.Prime := ⟨pp⟩
  have nd : ¬p ∣ x := by
    intro d
    have d1 := (Nat.dvd_add_iff_right d).mpr dp
    have := Nat.le_of_dvd Nat.one_pos d1
    omega
  have v := padicValNat.pow_add_pow (x:=x) (y:=1) (pp.odd_of_ne_two p2) dp nd orr
  rw [one_pow, fac, padicValNat.mul (by omega) (by omega)] at v
  have eq : padicValNat p c = padicValNat p r := by omega
  have power : p^(padicValNat p c) = c := by
    conv_lhs => arg 2; rw [pure, padicValNat.prime_pow]
    exact pure.symm
  have cd : c ∣ r := by rw [← power, eq]; exact pow_padicValNat_dvd
  exact (Nat.not_le_of_gt hc) (Nat.le_of_dvd (by omega) cd)

/-- When an even solution precedes a nontrivial odd power, the base
of that power is one less than a power of two. -/
theorem odd_power_root_neighbor {n x r : ℕ} (ox : Odd x) (hx : 1 < x)
    (orr : Odd r) (hr : 1 < r) (hn : n+1=x^r) (h : v_l 1 n=1) :
    ∃ b : ℕ, x+1=2^b := by
  apply odd_root_with_unique_odd_prime ox hx orr hr
  intro p q pp pq hp hq dp dq
  by_contra ne
  have shift : n+2=x^r+1 := by omega
  exact two_primes (k:=2) (by decide) pp pq ne hp hq (shift ▸ dp) (shift ▸ dq) h

lemma mersenne_power_exponent {p s b : ℕ} (op : Odd p) (hp : 1 < p)
    (hs : 0 < s) (eq : p^s+1=2^b) : s=1 := by
  by_contra bad
  rcases Nat.even_or_odd s with ⟨j, hj⟩|os
  · have hjp : j ≠ 0 := by omega
    have ob : Odd (p^j) := op.pow
    obtain ⟨w, hw⟩ := ob
    have large := Nat.one_lt_pow hjp hp
    have q : p^s = (2*w+1)^2 := by rw [hj, pow_add, hw, pow_two]
    have b2 : 2 ≤ b := by
      by_contra! z
      interval_cases b <;> norm_num at eq <;> have := Nat.one_lt_pow hs.ne' hp <;> omega
    have d4 : 4 ∣ 2^b := pow_dvd_pow (2 : ℕ) b2
    have sq : (2*w+1)^2+1 = 4*(w^2+w)+2 := by ring
    omega
  · obtain ⟨c, oc, hc, f⟩ := odd_cofactor op hp os (by omega)
    have dc : c ∣ 2^b := (f.symm.trans eq) ▸ dvd_mul_left c (p+1)
    obtain ⟨t, _, ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp dc
    have tpos : t ≠ 0 := by rintro rfl; simp at ht; omega
    have d := dvd_pow_self (2 : ℕ) tpos
    rw [← ht] at d
    obtain ⟨w, hw⟩ := oc
    omega

/-- Every odd prime divisor of the successor exponent must be the entire
exponent. In that case the prime base is a Mersenne prime. -/
theorem successor_exponent {n p a : ℕ} (pp : p.Prime) (op : Odd p) (ha : 0<a)
    (hn : n+1=p^a) (h : v_l 1 n=1) :
    (∃ t : ℕ, a=2^t) ∨ (a.Prime ∧ Odd a ∧ ∃ b : ℕ, p+1=2^b) := by
  by_cases ex : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ a
  · obtain ⟨r, pr, r2, s, hs⟩ := ex
    have spos : 0 < s := by
      by_contra! z
      have s0 : s=0 := by omega
      rw [s0, Nat.mul_zero] at hs
      omega
    have hx : n+1 = (p^s)^r := by rw [hn, hs, ← pow_mul, Nat.mul_comm]
    obtain ⟨b, hb⟩ := odd_power_root_neighbor op.pow (Nat.one_lt_pow spos.ne' pp.one_lt)
      (pr.odd_of_ne_two r2) pr.one_lt hx h
    have one := mersenne_power_exponent op pp.one_lt spos hb
    rw [one, mul_one] at hs
    exact Or.inr ⟨hs ▸ pr, hs ▸ pr.odd_of_ne_two r2, b, by simpa [one] using hb⟩
  · left
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd ha.ne' ?_⟩
    intro r pr dr
    by_contra nr
    exact ex ⟨r, pr, nr, dr⟩

lemma pell_divisibility {x y : ℕ} (he : x^2+1=5*y^2) (hd : 5 ∣ y) : 61 ∣ y := by
  let states : List (ℕ × ℕ) := [(2,1),(38,17),(72,0),(38,288),(2,304),
    (303,304),(267,288),(233,0),(267,17),(303,1)]
  have closed : ∀ z ∈ states, ((9*z.1+20*z.2)%305,(4*z.1+9*z.2)%305) ∈ states := by
    decide +kernel
  have sieve : ∀ z ∈ states, 5 ∣ z.2 → 61 ∣ z.2 := by decide +kernel
  have orbit (b a : ℕ) (eqn : a^2+1=5*b^2) : (a%305,b%305) ∈ states := by
    induction b using Nat.strong_induction_on generalizing a with
    | h b ih =>
      by_cases small : b < 5
      · have ab : a ≤ 8 := by nlinarith [Nat.mul_self_le_mul_self (show b ≤ 4 by omega)]
        interval_cases b <;> interval_cases a <;> norm_num at eqn
        all_goals decide +kernel
      · have lb : 5 ≤ b := by omega
        have low : 20*b ≤ 9*a := by
          by_contra! bad
          nlinarith only [eqn, Nat.mul_self_le_mul_self bad.le, Nat.mul_self_le_mul_self lb]
        have high : 4*a ≤ 9*b := by
          by_contra! bad
          nlinarith only [eqn, Nat.mul_self_le_mul_self bad.le, Nat.zero_le (b*b)]
        have strict : 2*b < a := by
          by_contra! bad
          nlinarith only [eqn, Nat.mul_self_le_mul_self bad, Nat.mul_self_le_mul_self lb]
        let u := 9*a-20*b
        let v := 9*b-4*a
        have eu : u+20*b=9*a := Nat.sub_add_cancel low
        have ev : v+4*a=9*b := Nat.sub_add_cancel high
        have evsmall : v<b := by omega
        have norm : u^2+1=5*v^2 := by
          have az : (a:ℤ)^2+1=5*(b:ℤ)^2 := by exact_mod_cast eqn
          have uz : (u:ℤ)=9*(a:ℤ)-20*(b:ℤ) := by dsimp [u]; push_cast [Nat.cast_sub low]; ring
          have vz : (v:ℤ)=9*(b:ℤ)-4*(a:ℤ) := by dsimp [v]; push_cast [Nat.cast_sub high]; ring
          have nz : (u:ℤ)^2+1=5*(v:ℤ)^2 := by rw [uz,vz]; linear_combination az
          exact_mod_cast nz
        have prev := closed _ (ih v evsmall u norm)
        have m := (Nat.mod_modEq u 305).symm
        have n := (Nat.mod_modEq v 305).symm
        have ax := (m.mul_left 9).add (n.mul_left 20)
        have by' := (m.mul_left 4).add (n.mul_left 9)
        change (9*u+20*v)%305=_ at ax
        change (4*u+9*v)%305=_ at by'
        rwa [show a=9*u+20*v by omega, show b=4*u+9*v by omega, ax, by']
  have d5 : 5 ∣ y%305 := by omega
  have d61 := sieve (x%305,y%305) (orbit y x he) d5
  change 61 ∣ y%305 at d61
  omega

/-- The only possible positive square root of a power of five minus one is two. -/
theorem square_plus_one_five {z e : ℕ} (h : z^2+1=5^e) : z ≤ 2 := by
  rcases Nat.even_or_odd e with ⟨b, rfl⟩|⟨b, rfl⟩
  · have eq : z^2+1=(5^b)^2 := by simpa [pow_add,pow_two] using h
    by_contra! big
    by_cases le : 5^b ≤ z
    · nlinarith [Nat.mul_self_le_mul_self le]
    · have l : z+1 ≤ 5^b := by omega
      nlinarith [Nat.mul_self_le_mul_self l]
  · have eq : z^2+1=5*(5^b)^2 := by
      rw [h, pow_succ, mul_comm 2 b, pow_mul, mul_comm]
    by_cases b0 : b=0
    · simp [b0] at eq
      nlinarith
    · have d := pell_divisibility eq (dvd_pow_self (5:ℕ) b0)
      have pr : Nat.Prime 61 := by decide
      have bad := pr.dvd_of_dvd_pow d
      omega

lemma large_prime_of_square {u : ℕ} (ev : Even u) (hu : 2<u) :
    ∃ p : ℕ, p.Prime ∧ 5<p ∧ p ∣ u^2+1 := by
  by_contra! none
  have no3 : ¬3 ∣ u^2+1 := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, pow_two, Nat.mul_mod]
    have bound := Nat.mod_lt u (by decide : 0<3)
    interval_cases r : u%3 <;> decide
  obtain ⟨w, hw⟩ := ev
  have no2 : ¬2 ∣ u^2+1 := by
    have form : u^2+1 = 2*(2*w^2)+1 := by rw [hw]; ring
    omega
  have pure : u^2+1 = 5^(u^2+1).primeFactorsList.length := by
    apply Nat.eq_prime_pow_of_unique_prime_dvd (by omega)
    intro p pp dp
    have le : p≤5 := by by_contra! big; exact none p pp big dp
    have choices : p=2 ∨ p=3 ∨ p=5 := by interval_cases p <;> norm_num at *
    rcases choices with rfl|rfl|rfl
    · exact False.elim (no2 dp)
    · exact False.elim (no3 dp)
    · rfl
  exact (Nat.not_le_of_gt hu) (square_plus_one_five pure)

/-- At offset five, the two Sophie Germain factors each supply a prime
above five, for every odd fourth root greater than three. -/
theorem fourth_power_witness {x : ℕ} (ox : Odd x) (hx : 3<x) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≠q ∧ 5<p ∧ 5<q ∧ p ∣ x^4+4 ∧ q ∣ x^4+4 := by
  obtain ⟨w, hw⟩ := ox
  let L := (2*w)^2+1
  let R := (2*w+2)^2+1
  obtain ⟨p, pp, pbig, dp⟩ := large_prime_of_square (u:=2*w) ⟨w,by omega⟩ (by omega)
  obtain ⟨q, pq, qbig, dq⟩ := large_prime_of_square (u:=2*w+2) ⟨w+1,by omega⟩ (by omega)
  change p ∣ L at dp
  change q ∣ R at dq
  have fac : x^4+4=L*R := by dsimp [L,R]; rw [hw]; ring
  refine ⟨p,q,pp,pq,?_,pbig,qbig,fac ▸ dvd_mul_of_dvd_left dp _,fac ▸ dvd_mul_of_dvd_right dq _⟩
  rintro rfl
  have diff : R=L+4*x := by dsimp [L,R]; rw [hw]; ring
  rw [diff] at dq
  have d4x := (Nat.dvd_add_iff_right dp).mpr dq
  have dx : p ∣ x := pp.dvd_mul.mp d4x |>.resolve_left (by
    intro d
    have := Nat.le_of_dvd (by decide : 0<4) d
    omega)
  have eq : L+2*x=x^2+2 := by dsimp [L]; rw [hw]; ring
  have dl := dvd_add dp (dvd_mul_of_dvd_right dx 2)
  rw [eq] at dl
  have ds : p ∣ x^2 := dx.trans (dvd_pow_self x (by decide : 2≠0))
  have bad := (Nat.dvd_add_iff_right ds).mpr dl
  have := Nat.le_of_dvd (by decide : 0<2) bad
  omega

/-- A uniform witness for successors that are prime squares suffices for
all proper powers of odd primes with power-of-two exponent. -/
theorem dyadic_of_prime_squares
    (squares : ∃ B : ℕ, ∀ p : ℕ, p.Prime → Odd p → B < p^2 →
      ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
        q ∣ p^2+d ∧ s ∣ p^2+d) :
    ∃ B : ℕ, ∀ p t : ℕ, p.Prime → Odd p → 0<t → B < p^(2^t) →
      ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
        q ∣ p^(2^t)+d ∧ s ∣ p^(2^t)+d := by
  obtain ⟨B, hB⟩ := squares
  refine ⟨B+81, ?_⟩
  intro p t pp op ht big
  cases t with
  | zero => omega
  | succ j =>
    cases j with
    | zero =>
      change B+81 < p^2 at big
      exact hB p pp op (by omega)
    | succ j =>
      let x := p^(2^j)
      have eq : p^(2^(j+1+1))=x^4 := by
        dsimp [x]
        rw [← pow_mul, show j+1+1=j+2 by omega, pow_add]
        rfl
      rw [eq] at big ⊢
      have xbig : 3<x := by
        by_contra! small
        have bound := Nat.pow_le_pow_left small 4
        norm_num at bound
        omega
      obtain ⟨q,s,pq,ps,ne,hq,hs,dq,ds⟩ := fourth_power_witness (x:=x) op.pow xbig
      exact ⟨4,q,s,pq,ps,ne,hq,hs,dq,ds⟩

private theorem cofactor_power {N d m : ℕ} (hm : 2 ≤ m) (dm : m ∣ N+d)
    (eligible : ∀ q : ℕ, q.Prime → q ∣ m → d+1<q)
    (nohit : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ N+d ∧ s ∣ N+d) : IsPrimePow m := by
  by_contra bad
  obtain ⟨q, hq, s, hs, ne⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le hm).mp bad
  obtain ⟨pq,dq,_⟩ := Nat.mem_primeFactors.mp hq
  obtain ⟨ps,ds,_⟩ := Nat.mem_primeFactors.mp hs
  exact nohit ⟨d,q,s,pq,ps,ne,eligible q pq dq,eligible s ps ds,dq.trans dm,ds.trans dm⟩

private theorem square_mod_three {x : ℕ} (h : ¬3 ∣ x) : x^2%3=1 := by
  have b := Nat.mod_lt x (by decide : 0<3)
  rw [pow_two, Nat.mul_mod]
  interval_cases e : x%3 <;> first | decide | omega

private theorem odd_power_mod_three {x b : ℕ} (ob : Odd b) (h : ¬3 ∣ x) :
    x^b%3 = x%3 := by
  obtain ⟨j,hj⟩ := ob
  have one : Nat.ModEq 3 (x^2) 1 := square_mod_three h
  have m := (one.pow j).mul_right x
  change Nat.ModEq 3 (x^b) x
  rw [hj, pow_succ, pow_mul]
  simpa only [one_pow, one_mul] using m

/-- Offsets 2 and 4 force simultaneous prime powers. Offset 10 removes
every multiple of four from the exponent of the first cofactor. -/
theorem square_survivor {p : ℕ} (pp : p.Prime) (op : Odd p) (hp : 3<p)
    (nohit : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p^2+d ∧ s ∣ p^2+d) :
    ∃ q r a b : ℕ, q.Prime ∧ r.Prime ∧ q≠r ∧ q%4=1 ∧ r%3=1 ∧
      0<a ∧ ¬4 ∣ a ∧ 0<b ∧ Odd b ∧ p^2+1=2*q^a ∧ p^2+3=4*r^b := by
  obtain ⟨w,hw⟩ := op
  let A := 2*w*(w+1)+1
  let B := w*(w+1)+1
  have hA : p^2+1=2*A := by dsimp [A]; rw [hw]; ring
  have hB : p^2+3=4*B := by dsimp [B]; rw [hw]; ring
  have abig : 2≤A := by nlinarith [Nat.mul_self_le_mul_self hp.le]
  have bbig : 2≤B := by nlinarith [Nat.mul_self_le_mul_self hp.le]
  have aodd : ¬2 ∣ A := by
    have e : A=2*(w*(w+1))+1 := by dsimp [A]; ring
    omega
  have bodd : ¬2 ∣ B := by
    rcases Nat.even_or_odd w with ⟨i,hi⟩|⟨i,hi⟩
    · have e : B=2*(i*(w+1))+1 := by dsimp [B]; rw [hi]; ring
      omega
    · have e : B=2*(w*(i+1))+1 := by dsimp [B]; rw [hi]; ring
      omega
  have p3 : ¬3 ∣ p := by
    intro d
    have e := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pp).mp d
    omega
  have pmod := square_mod_three p3
  have modB : B%3=1 := by omega
  have pureA : IsPrimePow A := cofactor_power (d:=1) abig (hA ▸ dvd_mul_left A 2) (by
    intro q pq dq
    have := pq.two_le
    by_contra! bad
    have eq : q=2 := by omega
    exact aodd (eq ▸ dq)) nohit
  have pureB : IsPrimePow B := cofactor_power (d:=3) bbig (hB ▸ dvd_mul_left B 4) (by
    intro q pq dq
    by_contra! bad
    have e : q=2 ∨ q=3 := by interval_cases q <;> norm_num at *
    rcases e with rfl|rfl
    · exact bodd dq
    · omega) nohit
  obtain ⟨q,a,pq,apos,eqA⟩ := (isPrimePow_nat_iff _).mp pureA
  obtain ⟨r,b,pr,bpos,eqB⟩ := (isPrimePow_nat_iff _).mp pureB
  have dq : q ∣ A := eqA ▸ dvd_pow_self q apos.ne'
  have dr : r ∣ B := eqB ▸ dvd_pow_self r bpos.ne'
  have q2 : q ≠ 2 := by rintro rfl; exact aodd dq
  have qs : q ∣ p^2+1 := hA ▸ dvd_mul_of_dvd_right dq 2
  obtain ⟨j,hj⟩ := Nat.pow_pow_add_primeFactors_one_lt (a:=p) (n:=1) pq q2 (by simpa using qs)
  norm_num at hj
  have q4 : q%4=1 := by omega
  have qbig : 3<q := by have := pq.two_le; omega
  have ne : q ≠ r := by
    rintro rfl
    have d := hB ▸ (dvd_mul_of_dvd_right dr 4 : q ∣ 4*B)
    have dd := Nat.dvd_sub d qs
    have e : p^2+3-(p^2+1)=2 := by omega
    rw [e] at dd
    have := Nat.le_of_dvd (by decide) dd
    omega
  have ob : Odd b := by
    apply Nat.not_even_iff_odd.mp
    rintro ⟨i,hi⟩
    have sq : p^2+3=(2*r^i)^2 := by rw [hB, ← eqB, hi, pow_add]; ring
    by_cases le : 2*r^i ≤ p
    · nlinarith [Nat.mul_self_le_mul_self le]
    · nlinarith [Nat.mul_self_le_mul_self (show p+1 ≤ 2*r^i by omega)]
  have r3 : ¬3 ∣ r := by intro d; have dB := d.trans dr; omega
  have rmod := odd_power_mod_three ob r3
  have no4 : ¬4 ∣ a := by
    rintro ⟨i,hi⟩
    have ip : 0 < i := by omega
    let x := q^i
    have xb : 3<x := (lt_of_lt_of_le qbig (Nat.le_self_pow ip.ne' q))
    have ox : Odd x := (pq.odd_of_ne_two q2).pow
    have f : p^2+9=2*(x^4+4) := by
      have aa : A=x^4 := by dsimp [x]; rw [←eqA, hi, ←pow_mul, Nat.mul_comm]
      omega
    obtain ⟨l,s,pl,ps,nls,hl,hs,dl,ds⟩ := fourth_power_witness ox xb
    have no7 : ¬7 ∣ x^4+4 := by
      have mx := (Nat.mod_modEq x 7).symm
      have red := (mx.pow 4).add_right 4
      change (x^4+4)%7=((x%7)^4+4)%7 at red
      rw [Nat.dvd_iff_mod_eq_zero, red]
      have bound := Nat.mod_lt x (by decide : 0<7)
      interval_cases e : x%7 <;> decide
    have big (t : ℕ) (pt : t.Prime) (dt : t ∣ x^4+4) (ht : 5<t) : 10<t := by
      by_contra! small
      have et : t=7 := by interval_cases t <;> norm_num at *
      exact no7 (et ▸ dt)
    exact nohit ⟨9,l,s,pl,ps,nls,big l pl dl hl,big s ps ds hs,
      f ▸ dvd_mul_of_dvd_right dl 2,f ▸ dvd_mul_of_dvd_right ds 2⟩
  exact ⟨q,r,a,b,pq,pr,ne,q4,by omega,apos,no4,bpos,ob,by omega,by omega⟩

private theorem pell_three_divisibility {x y : ℕ} (he : x^2+2=3*y^2) (hd : 9 ∣ y) :
    17 ∣ y := by
  let states : List (ℕ × ℕ) := [(1,1),(5,3),(19,11),(71,41),(112,0),(71,112),
    (19,142),(5,150),(1,152),(152,152),(148,150),(134,142),(82,112),(41,0),
    (82,41),(134,11),(148,3),(152,1)]
  have closed : ∀ z ∈ states, ((2*z.1+3*z.2)%153,(z.1+2*z.2)%153) ∈ states := by
    decide +kernel
  have sieve : ∀ z ∈ states, 9 ∣ z.2 → 17 ∣ z.2 := by decide +kernel
  have orbit (b a : ℕ) (eqn : a^2+2=3*b^2) : (a%153,b%153) ∈ states := by
    induction b using Nat.strong_induction_on generalizing a with
    | h b ih =>
      by_cases small : b < 2
      · have ab : a ≤ 1 := by nlinarith [Nat.mul_self_le_mul_self (show b ≤ 1 by omega)]
        interval_cases b <;> interval_cases a <;> norm_num at eqn
        all_goals decide +kernel
      · have lb : 2 ≤ b := by omega
        have low : 3*b ≤ 2*a := by
          by_contra! bad
          nlinarith only [eqn, Nat.mul_self_le_mul_self bad.le, Nat.mul_self_le_mul_self lb]
        have high : a ≤ 2*b := by
          by_contra! bad
          nlinarith only [eqn, Nat.mul_self_le_mul_self bad.le, Nat.zero_le (b*b)]
        have strict : b < a := by
          by_contra! bad
          nlinarith only [eqn, Nat.mul_self_le_mul_self bad, Nat.mul_self_le_mul_self lb]
        let u := 2*a-3*b
        let v := 2*b-a
        have eu : u+3*b=2*a := Nat.sub_add_cancel low
        have ev : v+a=2*b := Nat.sub_add_cancel high
        have evsmall : v<b := by omega
        have norm : u^2+2=3*v^2 := by
          have az : (a:ℤ)^2+2=3*(b:ℤ)^2 := by exact_mod_cast eqn
          have uz : (u:ℤ)=2*(a:ℤ)-3*(b:ℤ) := by dsimp [u]; push_cast [Nat.cast_sub low]; ring
          have vz : (v:ℤ)=2*(b:ℤ)-(a:ℤ) := by dsimp [v]; push_cast [Nat.cast_sub high]; ring
          have nz : (u:ℤ)^2+2=3*(v:ℤ)^2 := by rw [uz,vz]; linear_combination az
          exact_mod_cast nz
        have prev := closed _ (ih v evsmall u norm)
        have m := (Nat.mod_modEq u 153).symm
        have n := (Nat.mod_modEq v 153).symm
        have ax := (m.mul_left 2).add (n.mul_left 3)
        have by' := m.add (n.mul_left 2)
        change (2*u+3*v)%153=_ at ax
        change (u+2*v)%153=_ at by'
        rwa [show a=2*u+3*v by omega, show b=u+2*v by omega, ax, by']
  have d9 : 9 ∣ y%153 := by omega
  have d17 := sieve (x%153,y%153) (orbit y x he) d9
  change 17 ∣ y%153 at d17
  omega

/-- The only possible natural roots of a power of three minus two are at most five. -/
theorem square_plus_two_three {z e : ℕ} (h : z^2+2=3^e) : z ≤ 5 := by
  rcases Nat.even_or_odd e with ⟨b, rfl⟩|⟨b, rfl⟩
  · have eq : z^2+2=(3^b)^2 := by simpa [pow_add,pow_two] using h
    by_contra! big
    by_cases le : 3^b ≤ z
    · nlinarith [Nat.mul_self_le_mul_self le]
    · nlinarith [Nat.mul_self_le_mul_self (show z+1 ≤ 3^b by omega)]
  · have eq : z^2+2=3*(3^b)^2 := by
      rw [h, pow_succ, mul_comm 2 b, pow_mul, mul_comm]
    by_cases lb : 2 ≤ b
    · have d9 : 9 ∣ 3^b := pow_dvd_pow (3 : ℕ) lb
      have d17 := pell_three_divisibility eq d9
      have pr : Nat.Prime 17 := by decide
      have bad := pr.dvd_of_dvd_pow d17
      omega
    · have ub : b ≤ 1 := by omega
      interval_cases b <;> norm_num at eq <;> nlinarith

/-- Offset three forces exactly one prime other than three to divide the middle term. -/
theorem square_middle {p : ℕ} (pp : p.Prime) (op : Odd p) (hp : 5 < p)
    (nohit : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p^2+d ∧ s ∣ p^2+d) :
    ∃ t c e : ℕ, t.Prime ∧ 3 < t ∧ (t%8=1 ∨ t%8=3) ∧
      0 < c ∧ 0 < e ∧ p^2+2=3^c*t^e := by
  let n := p^2+2
  let c := n.factorization 3
  let m := n / 3^c
  have nz : n ≠ 0 := by dsimp [n]; omega
  have form : 3^c*m=n := Nat.ordProj_mul_ordCompl_eq_self n 3
  have dm : m ∣ n := Nat.ordCompl_dvd n 3
  have pos : 0 < m := Nat.ordCompl_pos 3 nz
  have no3 : ¬3 ∣ m := Nat.not_dvd_ordCompl Nat.prime_three nz
  have oddn : Odd n := (op.pow (n:=2)).add_even (by decide : Even 2)
  have no2 : ¬2 ∣ m := by intro div; exact (Nat.not_even_iff_odd.mpr oddn) (even_iff_two_dvd.mpr (div.trans dm))
  have div3 : 3 ∣ n := by
    have p3 : ¬3 ∣ p := by
      intro h
      have eq := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pp).mp h
      omega
    have residue := square_mod_three p3
    dsimp [n]; omega
  have cp : 0 < c := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three nz).mp div3
  have big : 2 ≤ m := by
    by_contra! small
    have m1 : m=1 := by omega
    have eq : p^2+2=3^c := by simpa [m1,n] using form.symm
    have bound := square_plus_two_three eq
    omega
  have pure : IsPrimePow m := cofactor_power (d:=2) big dm (by
    intro t pt dt
    have lb := pt.two_le
    by_contra! small
    rcases (show t=2 ∨ t=3 by omega) with rfl|rfl
    · exact no2 dt
    · exact no3 dt) nohit
  obtain ⟨t,e,pt,ep,eq⟩ := (isPrimePow_nat_iff _).mp pure
  have dt : t ∣ m := eq ▸ dvd_pow_self t ep.ne'
  have tb : 3 < t := by
    have lb := pt.two_le
    by_contra! small
    rcases (show t=2 ∨ t=3 by omega) with rfl|rfl
    · exact no2 dt
    · exact no3 dt
  have residue : t%8=1 ∨ t%8=3 := by
    let _ : Fact t.Prime := ⟨pt⟩
    apply (ZMod.exists_sq_eq_neg_two_iff (p:=t) (by omega)).mp
    refine ⟨(p : ZMod t), ?_⟩
    have zero := (ZMod.natCast_eq_zero_iff (p^2+2) t).mpr (dt.trans dm)
    push_cast at zero
    linear_combination -zero
  exact ⟨t,c,e,pt,tb,residue,cp,ep,by rw [eq]; exact form.symm⟩

/-- Each of the four surviving prime-square examples attains supremum one. -/
theorem square_examples {n : ℕ} (cases : n=8 ∨ n=24 ∨ n=48 ∨ n=120) : v_l 1 n = 1 := by
  have size : n ≤ 120 := by omega
  have lo : 1 ≤ v n 1 := by rcases cases with rfl|rfl|rfl|rfl <;> decide +kernel
  have vals : ∀ k : Fin 12, 0 < k.val → v n k.val ≤ 1 := by
    rcases cases with rfl|rfl|rfl|rfl <;> decide +kernel
  apply le_antisymm
  · apply iSup_le; intro k; apply iSup_le; intro hk
    have hv : v n k ≤ 1 := by
      by_cases small : k < 12
      · exact vals ⟨k, small⟩ hk
      · by_contra! hh
        have bound := square_bound hk hh
        have large : 12 ≤ k := by omega
        nlinarith [Nat.mul_le_mul_right k large]
    exact_mod_cast hv
  · exact (by exact_mod_cast lo : (1 : ℕ∞) ≤ (v n 1 : ℕ∞)).trans (offset_le (by decide))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
/-- Exact classification of positive solutions through the largest survivor in the finite search. -/
theorem solutions_through_330 {n : ℕ} (hn : 0 < n) (size : n ≤ 330) :
    v_l 1 n = 1 ↔ n ∈ [1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,30,36,42,46,
      48,60,70,78,80,96,120,190,222,330] := by
  let xs : List ℕ := [1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,30,36,42,46,
      48,60,70,78,80,96,120,190,222,330]
  change v_l 1 n = 1 ↔ n ∈ xs
  constructor
  · intro sol
    by_contra missing
    have excluded : ∀ m : Fin 331, 0 < m.val → m.val ∉ xs → ∃ k : Fin 12,
        0 < k.val ∧ 1 < ((m.val+k.val).primeFactors.filter (k.val < ·)).card := by
      decide +kernel
    obtain ⟨k,hk,hh⟩ := excluded ⟨n, by omega⟩ hn missing
    have bound := offset_le_one (k:=k.val) sol hk
    rw [v_as_card] at bound
    exact (Nat.not_lt_of_ge bound) hh
  · intro member
    have vals : ∀ m ∈ xs, ∀ k : Fin 20, 0 < k.val →
        ((m+k.val).primeFactors.filter (k.val < ·)).card ≤ 1 := by decide +kernel
    have first : ∀ m ∈ xs, 1 ≤ ((m+1).primeFactors.filter (1 < ·)).card := by decide +kernel
    have lo : 1 ≤ v n 1 := by rw [v_as_card]; exact first n member
    apply le_antisymm
    · apply iSup_le; intro k; apply iSup_le; intro hk
      have hv : v n k ≤ 1 := by
        by_cases small : k < 20
        · rw [v_as_card]; exact vals n member ⟨k,small⟩ hk
        · by_contra! hh
          have b := square_bound hk hh
          have large : 20 ≤ k := by omega
          nlinarith [Nat.mul_le_mul_right k large]
      exact_mod_cast hv
    · exact (by exact_mod_cast lo : (1 : ℕ∞) ≤ (v n 1 : ℕ∞)).trans (offset_le (by decide))

private theorem fifth_order {b q : ℕ} (pb : b.Prime) (ob : Odd b) (pq : q.Prime)
    (dq : q ∣ 2^b+1) (small : q < b) : q=3 := by
  -- The order of -2 divides both the prime b and q-1. It must be one.
  let _ : Fact q.Prime := ⟨pq⟩
  have zero := (ZMod.natCast_eq_zero_iff (2^b+1) q).mpr dq
  push_cast at zero
  have eq : (-2 : ZMod q)^b=1 := by rw [ob.neg_pow]; linear_combination -zero
  have ne : (-2 : ZMod q) ≠ 0 := by
    intro h
    rw [h,zero_pow pb.ne_zero] at eq
    exact zero_ne_one eq
  have cases := (Nat.dvd_prime pb).mp (orderOf_dvd_of_pow_eq_one eq)
  have one : orderOf (-2 : ZMod q)=1 := cases.resolve_right (by
    intro same
    have dd := ZMod.orderOf_dvd_card_sub_one ne
    rw [same] at dd
    have := Nat.le_of_dvd (show 0 < q-1 by have := pq.two_le; omega) dd
    omega)
  have nz := orderOf_eq_one_iff.mp one
  have z : ((3 : ℕ) : ZMod q)=0 := by push_cast; linear_combination -nz
  exact (Nat.prime_dvd_prime_iff_eq pq Nat.prime_three).mp ((ZMod.natCast_eq_zero_iff _ _).mp z)

private theorem mersenne_left_factor {b L : ℕ} (pb : b.Prime) (lb : L < b) (hb : 3 < b) :
    ∃ q : ℕ, q.Prime ∧ L < q ∧ q ∣ 2^b+1 := by
  have ob := pb.odd_of_ne_two (by omega)
  have no9 : ¬9 ∣ 2^b+1 := by
    have b3 : ¬3 ∣ b := by
      intro h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pb).mp h
      omega
    obtain ⟨w,hw⟩ := ob
    have rem : b%6=1 ∨ b%6=5 := by omega
    have pow : Nat.ModEq 9 (2^b) (2^(b%6)) := by
      have h : Nat.ModEq 9 (2^6) 1 := by decide
      calc
        2^b = 2^(b%6)*(2^6)^(b/6) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
        _ ≡ 2^(b%6)*1^(b/6) [MOD 9] := (h.pow _).mul_left _
        _ = _ := by simp
    change 2^b%9=2^(b%6)%9 at pow
    rcases rem with h|h <;> rw [h] at pow <;> norm_num at pow <;> omega
  by_contra! none
  have big := Nat.pow_le_pow_right (by decide : 0<2) (show 3 ≤ b by omega)
  norm_num at big
  have eq : 2^b+1=3^(2^b+1).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
      intro q pq dq
      have upper : q ≤ L := by by_contra! high; exact none q pq high dq
      exact fifth_order pb ob pq dq (by omega))
  generalize (2^b+1).primeFactorsList.length = e at eq
  have e2 : 2 ≤ e := by
    by_contra! bad
    interval_cases e <;> norm_num at eq
    all_goals omega
  exact no9 (eq ▸ (pow_dvd_pow (3 : ℕ) e2))

private theorem fifth_power_residue (a e : ℕ) (sq : a^2%8=1) :
    a^e%8=1 ∨ a^e%8=a%8 := by
  have m : Nat.ModEq 8 (a^2) 1 := sq
  rcases Nat.even_or_odd e with ⟨j,hj⟩|⟨j,hj⟩
  · left
    change Nat.ModEq 8 (a^e) 1
    rw [hj, ←two_mul, pow_mul]
    simpa only [one_pow] using m.pow j
  · right
    change Nat.ModEq 8 (a^e) a
    rw [hj, pow_succ, pow_mul]
    simpa only [one_pow,one_mul] using (m.pow j).mul_right a

/-- Every fifth power of a Mersenne prime provides a two-prime witness. -/
theorem mersenne_fifth_witness {p b : ℕ} (pp : p.Prime) (base : p+1=2^b) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
    q ∣ p^5+d ∧ s ∣ p^5+d := by
  have ep : p=2^b-1 := by omega
  have b1 : b ≠ 1 := by rintro rfl; norm_num at base; have := pp.two_le; omega
  have pb : b.Prime := (Nat.prime_of_pow_sub_one_prime b1 (ep ▸ pp)).2
  by_cases small : b ≤ 33
  · have primes : b ∈ [2,3,5,7,11,13,17,19,23,29,31] := by
      have tab : ∀ k : Fin 34, k.val.Prime → k.val ∈ [2,3,5,7,11,13,17,19,23,29,31] := by decide +kernel
      exact tab ⟨b,by omega⟩ pb
    subst p
    simp only [List.mem_cons,List.not_mem_nil,or_false] at primes
    rcases primes with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨2,5,7,by decide +kernel⟩
    · exact ⟨1,11,191,by decide +kernel⟩
    · exact ⟨6,37,47,by decide +kernel⟩
    · exact ⟨1,11,41,by decide +kernel⟩
    · exact ⟨0,23,89,by decide +kernel⟩
    · exact ⟨1,11,181,by decide +kernel⟩
    · exact ⟨2,7,23,by decide +kernel⟩
    · exact ⟨1,31,421,by decide +kernel⟩
    · exact ⟨1,11,281,by decide +kernel⟩
    · exact ⟨0,233,1103,by decide +kernel⟩
    · exact ⟨3,5,23,by decide +kernel⟩
  by_contra missing
  have d8 : 8 ∣ 2^b := pow_dvd_pow (2 : ℕ) (show 3 ≤ b by omega)
  let x := p-2
  have xp : p=x+2 := by dsimp [x]; have := pp.two_le; omega
  have xm : Nat.ModEq 8 x 5 := by change x%8=5; omega
  let F (y : ℕ) := (((y+6)*y+16)*y+16)*y+16
  let C (y : ℕ) := (((y+7)*y+19)*y+23)*y+11
  have fc {m i j : ℕ} (h : Nat.ModEq m i j) : Nat.ModEq m (F i) (F j) :=
    ((((((h.add_right 6).mul h).add_right 16).mul h).add_right 16).mul h).add_right 16
  have cc {m i j : ℕ} (h : Nat.ModEq m i j) : Nat.ModEq m (C i) (C j) :=
    ((((((h.add_right 7).mul h).add_right 19).mul h).add_right 23).mul h).add_right 11
  have f8 : F x%8=7 := (fc xm).trans (by decide +kernel : Nat.ModEq 8 (F 5) 7)
  have c8 : C x%8=5 := (cc xm).trans (by decide +kernel : Nat.ModEq 8 (C 5) 5)
  have fac : p^5+32=(p+2)*F x := by rw [xp]; dsimp [F]; ring
  have first : p^5+1=(p+1)*C x := by rw [xp]; dsimp [C]; ring
  -- The two shifted powers differ by 31. A divisor 31 at offset 33
  -- gives a divisor at offset two, where C cannot be a power of 31.
  have no31 : ¬31 ∣ F x := by
    intro d
    have d32 : 31 ∣ p^5+32 := fac ▸ dvd_mul_of_dvd_right d _
    have d1 : 31 ∣ p^5+1 := by omega
    have pr : Nat.Prime 31 := by decide
    have eq : C x = 31^(C x).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
        intro q pq dq
        by_contra neq
        have lq : 2 < q := by
          have := pq.two_le
          by_contra! low
          have q2 : q=2 := by omega
          rw [q2] at dq
          omega
        exact missing ⟨1,q,31,pq,pr,neq,lq,by decide,first ▸ dvd_mul_of_dvd_right dq _,d1⟩)
    have res := fifth_power_residue 31 (C x).primeFactorsList.length (by decide)
    rw [←eq] at res
    norm_num at res
    omega
  obtain ⟨q,pq,hq,dq⟩ := mersenne_left_factor pb (show 33 < b by omega) (by omega)
  have dl : q ∣ p+2 := by convert dq using 1; omega
  obtain ⟨s,ps,hs,ds⟩ : ∃ s : ℕ, s.Prime ∧ 33 < s ∧ s ∣ F x := by
    by_contra! none
    have eq : F x = 11^(F x).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
        intro s ps ds
        have le : s ≤ 33 := by by_contra! big; exact none s ps big ds
        have tab : ∀ i : Fin 34, i.val.Prime → ∀ j : Fin i.val, F j.val%i.val=0 →
            i.val=2 ∨ (i.val=5 ∧ (j.val+4)%5=0) ∨ i.val=11 ∨ i.val=31 := by decide +kernel
        have cong := fc (Nat.mod_modEq x s).symm
        change F x%s=F (x%s)%s at cong
        have opts := tab ⟨s,by omega⟩ ps ⟨x%s,Nat.mod_lt _ ps.pos⟩ (cong ▸ Nat.mod_eq_zero_of_dvd ds)
        change s=2 ∨ (s=5 ∧ (x%s+4)%5=0) ∨ s=11 ∨ s=31 at opts
        rcases opts with rfl|⟨rfl,h⟩|ok|rfl
        · omega
        · have d5 : 5 ∣ 2^b+1 := by omega
          have bad := fifth_order pb (pb.odd_of_ne_two (by omega)) (by decide : Nat.Prime 5) d5 (by omega)
          contradiction
        · exact ok
        · exact False.elim (no31 ds))
    have res := fifth_power_residue 11 (F x).primeFactorsList.length (by decide)
    rw [←eq] at res
    norm_num at res
    omega
  have ne : q≠s := by
    rintro rfl
    have ident : F x+16*(p+2)=80+(p+2)*(x^3+2*x^2+8*x) := by rw [xp]; dsimp [F]; ring
    have dd := dvd_add ds (dvd_mul_of_dvd_right dl 16)
    rw [ident] at dd
    have d80 := (Nat.dvd_add_iff_left (dvd_mul_of_dvd_left dl _)).mpr dd
    have mem := pq.mem_primeFactors d80 (by decide)
    have list : (80:ℕ).primeFactors={2,5} := by decide +kernel
    rw [list] at mem
    simp only [Finset.mem_insert,Finset.mem_singleton] at mem
    omega
  exact missing ⟨32,q,s,pq,ps,ne,hq,hs,fac ▸ dvd_mul_of_dvd_left dl _,fac ▸ dvd_mul_of_dvd_right ds _⟩


private theorem seventh_residue_product {v : ℕ} (hv : v ≠ 0)
    (h : ∀ q : ℕ, q.Prime → q ∣ v → q%24 ∈ [1,5,19,23]) : v%24 ∈ [1,5,19,23] := by
  let G : List ℕ := [1,5,19,23]
  -- These four residues form a subgroup of the units modulo 24.
  have closed : ∀ a ∈ G, ∀ b ∈ G, a*b%24 ∈ G := by decide +kernel
  have aux (l : List ℕ) (hl : ∀ q ∈ l, q%24 ∈ G) : l.prod%24 ∈ G := by
    induction l with
    | nil => decide +kernel
    | cons a t ih =>
      rw [List.prod_cons,Nat.mul_mod]
      exact closed _ (hl a (List.mem_cons_self ..)) _ (ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)))
  have res := aux v.primeFactorsList (fun q hq => h q (Nat.prime_of_mem_primeFactorsList hq)
    (Nat.dvd_of_mem_primeFactorsList hq))
  rwa [Nat.prod_primeFactorsList hv] at res

set_option maxRecDepth 16384 in
private theorem seventh_small {b : ℕ} (small : b≤129) (pb : b.Prime) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^7+d ∧ s ∣ (2^b-1)^7+d := by
  let certs : List (ℕ × ℕ × ℕ × ℕ) := [(2,2,11,199),(3,1,113,911),(5,4,7,397),(7,1,673,757),(11,0,23,89),(13,1,29,71),(17,3,11,23),(19,1,71,281),(23,2,5,17),(29,0,233,1103),(31,1,71,113),(37,1,673,3067),(41,1,29,127),(43,3,13,31),(47,0,2351,4513),(53,4,7,73),(59,1,113,701),(61,3,23,157),(67,2,5,353),(71,2,5,17),(73,5,11,1487),(79,2,5,17),(83,1,71,127),(89,1,71,281),(97,1,29,127),(101,2,179,199),(103,1,239,673),(107,4,7,73),(109,3,349,557),(113,2,419,3583),(127,2,5,17)]
  have covers : ∀ k : Fin 130, k.val.Prime → ∃ z ∈ certs, z.1=k.val := by decide +kernel
  have valid : ∀ z ∈ certs, z.2.2.1.Prime ∧ z.2.2.2.Prime ∧ z.2.2.1≠z.2.2.2 ∧
      z.2.1+1<z.2.2.1 ∧ z.2.1+1<z.2.2.2 ∧ z.2.2.1 ∣ (2^z.1-1)^7+z.2.1 ∧
        z.2.2.2 ∣ (2^z.1-1)^7+z.2.1 := by decide +kernel
  obtain ⟨⟨j,d,q,s⟩,mem,eq⟩ := covers ⟨b,by omega⟩ pb
  change j=b at eq
  subst j
  exact ⟨d,q,s,valid _ mem⟩

set_option maxRecDepth 16384 in
set_option synthInstance.maxSize 512 in
set_option maxHeartbeats 2000000 in
/-- Every seventh power of a Mersenne prime provides a two-prime witness. -/
theorem mersenne_seventh_witness {p b : ℕ} (pp : p.Prime) (base : p+1=2^b) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
    q ∣ p^7+d ∧ s ∣ p^7+d := by
  have ep : p=2^b-1 := by omega
  have b1 : b ≠ 1 := by rintro rfl; norm_num at base; have := pp.two_le; omega
  have pb : b.Prime := (Nat.prime_of_pow_sub_one_prime b1 (ep ▸ pp)).2
  by_cases small : b ≤ 129
  · exact ep ▸ seventh_small small pb
  by_contra missing
  have ob := pb.odd_of_ne_two (by omega)
  have d16 : 16 ∣ 2^b := pow_dvd_pow (2 : ℕ) (show 4 ≤ b by omega)
  let x := p-2
  have xp : p=x+2 := by dsimp [x]; have := pp.two_le; omega
  have p3 : Nat.ModEq 3 (2^b) 2 := by
    obtain ⟨j,hj⟩ := ob
    rw [hj,pow_succ,pow_mul]
    have h : Nat.ModEq 3 (2^2) 1 := by decide
    simpa only [one_pow,one_mul] using (h.pow j).mul_right 2
  change 2^b%3=2 at p3
  have xm : Nat.ModEq 24 x 5 := by change x%24=5; omega
  have xn : Nat.ModEq 16 x 13 := by change x%16=13; omega
  let F (y : ℕ) := (((((y+10)*y+44)*y+104)*y+144)*y+96)*y+64
  let C (y : ℕ) := (((((y+11)*y+51)*y+127)*y+179)*y+135)*y+43
  have fc {m i j : ℕ} (h : Nat.ModEq m i j) : Nat.ModEq m (F i) (F j) :=
    ((((((((((h.add_right 10).mul h).add_right 44).mul h).add_right 104).mul h).add_right 144).mul h).add_right 96).mul h).add_right 64
  have cc {m i j : ℕ} (h : Nat.ModEq m i j) : Nat.ModEq m (C i) (C j) :=
    ((((((((((h.add_right 11).mul h).add_right 51).mul h).add_right 127).mul h).add_right 179).mul h).add_right 135).mul h).add_right 43
  have f24 : F x%24=7 := (fc xm).trans (by decide +kernel : Nat.ModEq 24 (F 5) 7)
  have c16 : C x%16=7 := (cc xn).trans (by decide +kernel : Nat.ModEq 16 (C 13) 7)
  have fac : p^7+128=(p+2)*F x := by rw [xp]; dsimp [F]; ring
  have first : p^7+1=(p+1)*C x := by rw [xp]; dsimp [C]; ring
  have no127 : ¬127 ∣ F x := by
    intro d
    have d128 : 127 ∣ p^7+128 := fac ▸ dvd_mul_of_dvd_right d _
    have d1 : 127 ∣ p^7+1 := by omega
    have pr : Nat.Prime 127 := by decide
    have eq : C x = 127^(C x).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
        intro q pq dq
        by_contra neq
        have lq : 2 < q := by
          have := pq.two_le
          by_contra! low
          have q2 : q=2 := by omega
          rw [q2] at dq
          omega
        exact missing ⟨1,q,127,pq,pr,neq,lq,by decide,first ▸ dvd_mul_of_dvd_right dq _,d1⟩)
    have res (e : ℕ) : 127^e%16=1 ∨ 127^e%16=15 := by
      induction e with
      | zero => decide
      | succ e ih =>
        rw [pow_succ,Nat.mul_mod]
        rcases ih with h|h <;> rw [h] <;> decide
    have rr := res (C x).primeFactorsList.length
    rw [←eq] at rr
    omega
  have no113 : ¬113 ∣ F x := by
    -- The period of 2 modulo 113 is 28. The prime exponent b is coprime to 28.
    have period : Nat.ModEq 113 (2^28) 1 := by decide
    have red : Nat.ModEq 113 (2^b) (2^(b%28)) := by
      calc
        2^b = 2^(b%28)*(2^28)^(b/28) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
        _ ≡ 2^(b%28)*1^(b/28) [MOD 113] := (period.pow _).mul_left _
        _ = _ := by simp
    have b7 : ¬7 ∣ b := by
      intro h
      have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 7) pb).mp h
      omega
    have trans := (Nat.mod_modEq x 113).add_right 3
    change (x%113+3)%113=(x+3)%113 at trans
    change 2^b%113=2^(b%28)%113 at red
    have g := fc (Nat.mod_modEq x 113).symm
    change F x%113=F (x%113)%113 at g
    have tab : ∀ k : Fin 28, k.val%2=1 → k.val%7≠0 → ∀ z : Fin 113,
        (z.val+3)%113=2^k.val%113 → F z.val%113≠0 := by decide +kernel
    obtain ⟨w,ow⟩ := ob
    have rr := tab ⟨b%28,Nat.mod_lt _ (by decide)⟩ (by dsimp; omega) (by dsimp; omega)
      ⟨x%113,Nat.mod_lt _ (by decide)⟩ (by dsimp; omega)
    rw [Nat.dvd_iff_mod_eq_zero,g]
    exact rr
  obtain ⟨q,pq,hq,dq⟩ := mersenne_left_factor pb (show 129 < b by omega) (by omega)
  have dl : q ∣ p+2 := by convert dq using 1; omega
  obtain ⟨s,ps,hs,ds⟩ : ∃ s : ℕ, s.Prime ∧ 129 < s ∧ s ∣ F x := by
    by_contra! none
    have res := seventh_residue_product (v:=F x) (by omega) (by
      intro s ps ds
      have le : s ≤ 129 := by by_contra! big; exact none s ps big ds
      have tab : ∀ i : Fin 130, i.val.Prime → ∀ j : Fin i.val, F j.val%i.val=0 →
          i.val=2 ∨ (i.val=7 ∧ (j.val+4)%7=0) ∨ i.val=113 ∨ i.val=127 ∨
            i.val%24 ∈ [1,5,19,23] := by decide +kernel
      have cong := fc (Nat.mod_modEq x s).symm
      change F x%s=F (x%s)%s at cong
      have opts := tab ⟨s,by omega⟩ ps ⟨x%s,Nat.mod_lt _ ps.pos⟩ (cong ▸ Nat.mod_eq_zero_of_dvd ds)
      change s=2 ∨ (s=7 ∧ (x%s+4)%7=0) ∨ s=113 ∨ s=127 ∨ s%24 ∈ [1,5,19,23] at opts
      rcases opts with rfl|⟨rfl,h⟩|rfl|rfl|ok
      · omega
      · have d7 : 7 ∣ 2^b+1 := by omega
        have bad := fifth_order pb ob (by decide : Nat.Prime 7) d7 (by omega)
        contradiction
      · exact False.elim (no113 ds)
      · exact False.elim (no127 ds)
      · exact ok)
    rw [f24] at res
    norm_num at res
  have ne : q≠s := by
    rintro rfl
    have ident : F x+96*(p+2)=448+(p+2)*(x^5+6*x^4+20*x^3+24*x^2+48*x) := by rw [xp]; dsimp [F]; ring
    have dd := dvd_add ds (dvd_mul_of_dvd_right dl 96)
    rw [ident] at dd
    have d448 := (Nat.dvd_add_iff_left (dvd_mul_of_dvd_left dl _)).mpr dd
    have mem := pq.mem_primeFactors d448 (by decide)
    have list : (448:ℕ).primeFactors={2,7} := by decide +kernel
    rw [list] at mem
    simp only [Finset.mem_insert,Finset.mem_singleton] at mem
    omega
  exact missing ⟨128,q,s,pq,ps,ne,hq,hs,fac ▸ dvd_mul_of_dvd_left dl _,fac ▸ dvd_mul_of_dvd_right ds _⟩


-- Each entry records (b,d,q,s). The modular tests use the small exponents
-- b modulo q−1 and b modulo s−1. The second test covers the prime indices
-- in one interval of length 64.
private theorem eleventh_witness_prime {q : ℕ} (mem : q ∈ [5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,127,131,149,151,167]) : q.Prime := by
  have table : ∀ t ∈ ([5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,127,131,149,151,167] : List ℕ), t.Prime := by decide +kernel
  exact table q mem

private theorem eleventh_small_block {b start : ℕ} (small : b≤2049) (pb : b.Prime)
    (lower : start≤b) (upper : b<start+64) (certs : List (ℕ × ℕ × ℕ × ℕ))
    (valid : certs.all (fun z => decide (
      z.2.2.1 ∈ [5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,127,131,149,151,167] ∧ z.2.2.2 ∈ [5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,127,131,149,151,167] ∧
      z.2.2.1≠z.2.2.2 ∧ z.2.1+1<z.2.2.1 ∧ z.2.1+1<z.2.2.2 ∧
      (2^(z.2.2.1-1)%z.2.2.1=1 ∧ (((2^(z.1%(z.2.2.1-1))-1)%z.2.2.1)^11+z.2.1)%z.2.2.1=0) ∧
      (2^(z.2.2.2-1)%z.2.2.2=1 ∧ (((2^(z.1%(z.2.2.2-1))-1)%z.2.2.2)^11+z.2.1)%z.2.2.2=0))) = true)
    (covers : (List.range 64).all (fun i => decide (2049<start+i) ||
      certs.any (fun z => z.1 == start+i) || decide (start+i<2) ||
      ([2,3,5,7,11,13,17,19,23,29,31,37,41,43] : List ℕ).any (fun d => decide (1<d ∧ d<start+i ∧ (start+i)%d=0))) = true) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  let v := b-start
  have index : start+v=b := by dsimp [v]; omega
  have hit := List.all_eq_true.mp covers v (List.mem_range.mpr (show v<64 by dsimp [v]; omega))
  simp only [index, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq, beq_iff_eq] at hit
  have high : ¬2049<b := by omega
  have low : ¬b<2 := by have := pb.two_le; omega
  have noDiv : ¬∃ d ∈ ([2,3,5,7,11,13,17,19,23,29,31,37,41,43] : List ℕ), 1<d ∧ d<b ∧ b%d=0 := by
    rintro ⟨d,_,hd,lt,div⟩
    have bad := (Nat.dvd_prime pb).mp (Nat.dvd_iff_mod_eq_zero.mpr div)
    omega
  have good : ∃ z ∈ certs, z.1=b := ((hit.resolve_right noDiv).resolve_right low).resolve_left high
  obtain ⟨⟨j,d,q,s⟩,mem,ej⟩ := good
  change j=b at ej
  subst j
  have facts := of_decide_eq_true (List.all_eq_true.mp valid _ mem)
  obtain ⟨qp,sp,ne,hq,hs,tq,ts⟩ := facts
  have pq := eleventh_witness_prime qp
  have ps := eleventh_witness_prime sp
  have lift (t : ℕ) (pt : t.Prime) (per : 2^(t-1)%t=1)
      (hit : (((2^(b%(t-1))-1)%t)^11+d)%t=0) : t ∣ (2^b-1)^11+d := by
    have m : Nat.ModEq t (2^(t-1)) 1 := by
      change 2^(t-1)%t=1%t
      rwa [Nat.mod_eq_of_lt pt.one_lt]
    have red : Nat.ModEq t (2^b) (2^(b%(t-1))) := by
      calc
        2^b = 2^(b%(t-1))*(2^(t-1))^(b/(t-1)) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
        _ ≡ 2^(b%(t-1))*1^(b/(t-1)) [MOD t] := (m.pow _).mul_left _
        _ = _ := by simp
    have pm : Nat.ModEq t (2^b-1) ((2^(b%(t-1))-1)%t) := by
      apply Nat.ModEq.trans _ (Nat.mod_modEq _ _).symm
      apply Nat.ModEq.add_right_cancel' 1
      rw [Nat.sub_add_cancel (Nat.one_le_pow b 2 (by decide)),
        Nat.sub_add_cancel (Nat.one_le_pow (b%(t-1)) 2 (by decide))]
      exact red
    exact Nat.dvd_iff_mod_eq_zero.mpr (((pm.pow 11).add_right d).trans (show Nat.ModEq t _ 0 from hit))
  exact ⟨d,q,s,pq,ps,ne,hq,hs,lift q pq tq.1 tq.2,lift s ps ts.1 ts.2⟩

set_option maxRecDepth 8192 in
private theorem eleventh_block_0 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=0) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=0) small pb (by omega) (by omega)
    [(2,9,19,37),(3,11,13,31),(5,2,7,11),(7,77,89,131),(11,2,5,7),(13,4,11,19),(17,5,11,13),(19,20,41,47),(23,2,5,7),(29,6,11,19),(31,6,29,43),(37,5,11,53),(41,45,61,73),(43,3,17,37),(47,2,5,7),(53,5,13,37),(59,2,5,7),(61,17,19,37)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_1 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=1) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=64) small pb (by omega) (by omega)
    [(67,37,41,53),(71,2,5,7),(73,11,31,59),(79,53,59,61),(83,2,5,7),(89,5,13,37),(97,17,19,37),(101,6,19,43),(103,4,11,19),(107,2,5,7),(109,7,17,41),(113,11,19,31),(127,15,17,29)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_2 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=2) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=128) small pb (by omega) (by omega)
    [(131,2,5,7),(137,5,11,13),(139,8,43,127),(149,7,17,41),(151,17,19,29),(157,1,23,67),(163,43,47,59),(167,2,5,7),(173,11,29,31),(179,2,5,7),(181,8,43,127),(191,2,5,7)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_3 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=3) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=192) small pb (by omega) (by omega)
    [(193,4,11,19),(197,5,11,13),(199,6,11,29),(211,3,17,61),(223,1,23,67),(227,2,5,7),(229,7,17,41),(233,5,13,37),(239,2,5,7),(241,17,19,37),(251,2,5,7)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_4 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=4) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=256) small pb (by omega) (by omega)
    [(257,5,11,13),(263,2,5,7),(269,5,13,37),(271,3,61,79),(277,17,19,37),(281,90,101,167),(283,4,11,19),(293,11,19,31),(307,18,31,79),(311,2,5,7),(313,11,29,31),(317,5,11,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_5 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=5) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=320) small pb (by omega) (by omega)
    [(331,3,17,37),(337,77,79,89),(347,2,5,7),(349,17,19,37),(353,6,19,43),(359,2,5,7),(367,6,29,43),(373,4,11,19),(379,3,17,47),(383,2,5,7)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_6 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=6) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=384) small pb (by omega) (by omega)
    [(389,6,11,19),(397,7,17,59),(401,5,13,53),(409,6,11,43),(419,2,5,7),(421,17,19,37),(431,2,5,7),(433,20,47,71),(439,30,67,71),(443,2,5,7)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_7 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=7) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=448) small pb (by omega) (by omega)
    [(449,5,13,37),(457,17,19,37),(461,8,37,43),(463,4,11,19),(467,2,5,7),(479,2,5,7),(487,1,23,67),(491,2,5,7),(499,34,37,43),(503,2,5,7),(509,11,19,29)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_8 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=8) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=512) small pb (by omega) (by omega)
    [(521,5,13,37),(523,2,5,47),(541,18,79,127),(547,3,17,37),(557,5,11,13),(563,2,5,7),(569,6,11,19),(571,3,17,61)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_9 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=9) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=576) small pb (by omega) (by omega)
    [(577,31,59,61),(587,2,5,7),(593,11,29,31),(599,2,5,7),(601,17,19,37),(607,5,11,29),(613,27,29,59),(617,5,11,13),(619,6,11,29),(631,15,17,29)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_10 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=10) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=640) small pb (by omega) (by omega)
    [(641,24,43,59),(643,4,11,19),(647,2,5,7),(653,11,19,31),(659,2,5,7),(661,2,47,101),(673,17,19,37),(677,5,11,13),(683,2,5,7),(691,3,17,37),(701,5,13,37)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_11 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=11) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=704) small pb (by omega) (by omega)
    [(709,17,19,37),(719,2,5,7),(727,39,53,101),(733,4,11,19),(739,3,17,79),(743,2,5,7),(751,34,37,43),(757,28,41,103),(761,11,19,29)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_12 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=12) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=768) small pb (by omega) (by omega)
    [(769,1,23,89),(773,5,13,37),(787,6,29,43),(797,5,11,13),(809,5,13,37),(811,3,17,61),(821,5,13,107),(823,4,11,19),(827,2,5,7),(829,7,17,41)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_13 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=13) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=832) small pb (by omega) (by omega)
    [(839,2,5,7),(853,17,19,37),(857,5,11,13),(859,20,41,83),(863,2,5,7),(877,37,67,89),(881,5,13,37),(883,14,47,59),(887,2,5,7)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_14 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=14) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=896) small pb (by omega) (by omega)
    [(907,17,19,29),(911,2,5,7),(919,7,29,47),(929,6,11,19),(937,25,29,97),(941,45,61,73),(947,2,5,7),(953,5,13,37)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_15 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=15) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=960) small pb (by omega) (by omega)
    [(967,15,17,29),(971,2,5,7),(977,5,11,13),(983,2,5,7),(991,29,71,103),(997,17,19,37),(1009,37,67,89),(1013,11,19,29),(1019,2,5,7),(1021,38,59,67)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_16 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=16) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=1024) small pb (by omega) (by omega)
    [(1031,2,5,7),(1033,17,19,37),(1039,6,11,29),(1049,25,29,101),(1051,3,17,37),(1061,5,13,37),(1063,4,11,59),(1069,17,19,37),(1087,35,47,73)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_17 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=17) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=1088) small pb (by omega) (by omega)
    [(1091,2,5,7),(1093,4,11,19),(1097,5,11,13),(1103,2,5,7),(1109,6,11,19),(1117,24,43,53),(1123,3,17,37),(1129,57,71,107),(1151,2,5,7)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_18 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=18) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=1152) small pb (by omega) (by omega)
    [(1153,11,29,31),(1163,2,5,7),(1171,3,17,61),(1181,5,13,53),(1187,2,5,7),(1193,11,19,31),(1201,29,37,71),(1213,17,19,37)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_19 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=19) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=1216) small pb (by omega) (by omega)
    [(1217,5,11,13),(1223,2,5,7),(1229,7,17,41),(1231,3,37,61),(1237,4,19,59),(1249,17,19,37),(1259,2,5,7),(1277,5,11,13),(1279,1,23,67)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_20 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=20) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=1280) small pb (by omega) (by omega)
    [(1283,2,5,7),(1289,6,11,19),(1291,6,29,43),(1297,1,23,89),(1301,45,59,61),(1303,15,17,29),(1307,2,5,7),(1319,2,5,7),(1321,17,19,37),(1327,57,61,83)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_21 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=21) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=1344) small pb (by omega) (by omega)
    [(1361,6,19,43),(1367,2,5,7),(1373,11,19,31),(1381,1,23,67),(1399,20,41,47)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_22 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=22) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=1408) small pb (by omega) (by omega)
    [(1409,57,71,83),(1423,34,43,47),(1427,2,5,7),(1429,17,19,37),(1433,11,29,31),(1439,2,5,7),(1447,5,11,29),(1451,2,5,7),(1453,4,11,19),(1459,6,11,29),(1471,15,17,29)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_23 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=23) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=1472) small pb (by omega) (by omega)
    [(1481,24,43,53),(1483,3,17,37),(1487,2,5,7),(1489,29,37,67),(1493,5,13,37),(1499,2,5,7),(1511,2,5,7),(1523,2,5,7),(1531,3,17,61)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_24 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=24) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=1536) small pb (by omega) (by omega)
    [(1543,4,11,19),(1549,7,17,41),(1553,11,19,31),(1559,2,5,7),(1567,8,43,53),(1571,2,5,7),(1579,1,23,67),(1583,2,5,7),(1597,5,11,53)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_25 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=25) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=1600) small pb (by omega) (by omega)
    [(1601,5,13,37),(1607,2,5,7),(1609,17,19,37),(1613,6,19,43),(1619,2,5,7),(1621,29,67,71),(1627,3,17,37),(1637,5,11,13),(1657,41,71,151),(1663,17,19,29)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_26 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=26) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=1664) small pb (by omega) (by omega)
    [(1667,2,5,7),(1669,7,17,41),(1693,30,47,67),(1697,5,11,13),(1699,3,17,37),(1709,5,13,37),(1721,8,37,43),(1723,4,11,19)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_27 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=27) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=1728) small pb (by omega) (by omega)
    [(1733,11,19,31),(1741,1,23,67),(1747,37,41,89),(1753,17,19,37),(1759,34,37,43),(1777,1,23,67),(1783,9,13,149),(1787,2,5,7),(1789,17,19,37)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_28 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=28) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=1792) small pb (by omega) (by omega)
    [(1801,37,67,89),(1811,2,5,7),(1823,2,5,7),(1831,27,41,59),(1847,2,5,7)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_29 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=29) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=1856) small pb (by omega) (by omega)
    [(1861,17,19,37),(1867,5,11,29),(1871,2,5,7),(1873,1,23,67),(1877,5,11,13),(1879,6,11,29),(1889,5,13,37),(1901,24,43,73),(1907,2,5,7),(1913,11,19,31)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_30 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=30) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=1920) small pb (by omega) (by omega)
    [(1931,2,5,7),(1933,17,19,37),(1949,7,17,41),(1951,3,37,61),(1973,8,37,43),(1979,2,5,7)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_31 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=31) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=1984) small pb (by omega) (by omega)
    [(1987,3,17,37),(1993,4,11,19),(1997,5,11,13),(1999,36,59,79),(2003,2,5,7),(2011,34,37,43),(2017,41,47,151),(2027,2,5,7),(2029,7,17,41),(2039,2,5,7)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem eleventh_block_32 {b : ℕ} (small : b≤2049) (pb : b.Prime) (index : b/64=32) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  apply eleventh_small_block (start:=2048) small pb (by omega) (by omega)
    []
  · decide +kernel
  · decide +kernel

private theorem eleventh_small {b : ℕ} (small : b≤2049) (pb : b.Prime) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^11+d ∧ s ∣ (2^b-1)^11+d := by
  have bound : b/64≤32 := by omega
  interval_cases h : b/64
  · exact eleventh_block_0 small pb h
  · exact eleventh_block_1 small pb h
  · exact eleventh_block_2 small pb h
  · exact eleventh_block_3 small pb h
  · exact eleventh_block_4 small pb h
  · exact eleventh_block_5 small pb h
  · exact eleventh_block_6 small pb h
  · exact eleventh_block_7 small pb h
  · exact eleventh_block_8 small pb h
  · exact eleventh_block_9 small pb h
  · exact eleventh_block_10 small pb h
  · exact eleventh_block_11 small pb h
  · exact eleventh_block_12 small pb h
  · exact eleventh_block_13 small pb h
  · exact eleventh_block_14 small pb h
  · exact eleventh_block_15 small pb h
  · exact eleventh_block_16 small pb h
  · exact eleventh_block_17 small pb h
  · exact eleventh_block_18 small pb h
  · exact eleventh_block_19 small pb h
  · exact eleventh_block_20 small pb h
  · exact eleventh_block_21 small pb h
  · exact eleventh_block_22 small pb h
  · exact eleventh_block_23 small pb h
  · exact eleventh_block_24 small pb h
  · exact eleventh_block_25 small pb h
  · exact eleventh_block_26 small pb h
  · exact eleventh_block_27 small pb h
  · exact eleventh_block_28 small pb h
  · exact eleventh_block_29 small pb h
  · exact eleventh_block_30 small pb h
  · exact eleventh_block_31 small pb h
  · exact eleventh_block_32 small pb h


-- BEGIN ELEVEN
private theorem eleven_period {b m o : ℕ} (hm : Nat.ModEq m (2^o) 1) :
    Nat.ModEq m (2^b) (2^(b%o)) := by
  calc
    2^b = 2^(b%o)*(2^o)^(b/o) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
    _ ≡ 2^(b%o)*1^(b/o) [MOD m] := (hm.pow _).mul_left _
    _ = _ := by simp

private theorem eleven_order {q p : ℕ} (pq : q.Prime) (q2 : q≠2)
    (d : q ∣ p^11+2048) (nd : ¬q ∣ p+2) : 11 ∣ q-1 := by
  let _ : Fact q.Prime := ⟨pq⟩
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro h
    have eq := (Nat.prime_dvd_prime_iff_eq pq Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 q).mp h)
    exact q2 eq
  let t : ZMod q := -(p:ZMod q)/2
  have zero := (ZMod.natCast_eq_zero_iff _ _).mpr d
  push_cast at zero
  have eq : t^11=1 := by
    dsimp [t]
    rw [div_pow,div_eq_iff (pow_ne_zero _ h2)]
    linear_combination -zero
  have t1 : t≠1 := by
    intro h
    dsimp [t] at h
    rw [div_eq_iff h2] at h
    apply nd
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    linear_combination -h
  have t0 : t≠0 := by rintro h; rw [h] at eq; simp at eq
  have ord : orderOf t = 11 := ((Nat.dvd_prime (by decide : Nat.Prime 11)).mp
    (orderOf_dvd_of_pow_eq_one eq)).resolve_left (fun h => t1 (orderOf_eq_one_iff.mp h))
  exact ord ▸ ZMod.orderOf_dvd_card_sub_one t0

set_option maxRecDepth 32768 in
set_option synthInstance.maxSize 512 in
set_option maxHeartbeats 10000000 in
/-- At a Mersenne-prime eleventh power, the shifts by one and 2048 force a witness
when the Mersenne index exceeds 2049. -/
theorem mersenne_eleven_large_witness {p b : ℕ} (pp : p.Prime) (base : p+1=2^b)
    (hb : 2049 < b) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
    q ∣ p^11+d ∧ s ∣ p^11+d := by
  by_contra missing
  have ep : p=2^b-1 := by omega
  have pb : b.Prime := (Nat.prime_of_pow_sub_one_prime (by omega) (ep ▸ pp)).2
  let x := p-2
  have xp : p=x+2 := by dsimp [x]; have := pp.two_le; omega
  have bx : x+3=2^b := by omega
  have d8 : 8 ∣ 2^b := pow_dvd_pow (2:ℕ) (show 3≤b by omega)
  have xm : Nat.ModEq 8 x 5 := by change x%8=5; omega
  let F (y : ℕ) := ((((((((((1*y+18)*y+148)*y+728)*y+2368)*y+5312)*y+8320)*y+8960)*y+6400)*y+2560)*y+1024)
  let C (y : ℕ) := ((((((((((1*y+19)*y+163)*y+831)*y+2787)*y+6423)*y+10299)*y+11343)*y+8211)*y+3527)*y+683)
  have fc {m i j : ℕ} (h : Nat.ModEq m i j) : Nat.ModEq m (F i) (F j) := (((((((((((((((((((((Nat.ModEq.refl 1).mul h).add_right 18).mul h).add_right 148).mul h).add_right 728).mul h).add_right 2368).mul h).add_right 5312).mul h).add_right 8320).mul h).add_right 8960).mul h).add_right 6400).mul h).add_right 2560).mul h).add_right 1024)
  have cc {m i j : ℕ} (h : Nat.ModEq m i j) : Nat.ModEq m (C i) (C j) := (((((((((((((((((((((Nat.ModEq.refl 1).mul h).add_right 19).mul h).add_right 163).mul h).add_right 831).mul h).add_right 2787).mul h).add_right 6423).mul h).add_right 10299).mul h).add_right 11343).mul h).add_right 8211).mul h).add_right 3527).mul h).add_right 683)
  have f8 : F x%8=7 := (fc xm).trans (by decide +kernel : Nat.ModEq 8 (F 5) 7)
  have c8 : C x%8=3 := (cc xm).trans (by decide +kernel : Nat.ModEq 8 (C 5) 3)
  have fac : p^11+2048=(p+2)*F x := by rw [xp]; dsimp [F]; ring
  have first : p^11+1=(p+1)*C x := by rw [xp]; dsimp [C]; ring
  have excl : b%11 ∉ [3,4,6,9,10] := by
    intro mem
    have red := eleven_period (b:=b) (by decide : Nat.ModEq 23 (2^11) 1)
    have pmod : Nat.ModEq 23 p (2^(b%11)-1) := by
      apply Nat.ModEq.add_right_cancel' 1
      rw [base,Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide : 0<2))]
      exact red
    have tab : ∀ i : Fin 11, i.val ∈ [3,4,6,9,10] → ((2^i.val-1)^11+1)%23=0 := by decide +kernel
    have rd := (pmod.pow 11).add_right 1
    have div : 23 ∣ p^11+1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      exact Eq.trans rd (tab ⟨b%11,Nat.mod_lt _ (by decide)⟩ mem)
    have eq : C x=23^(C x).primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
      intro q pq dq
      by_contra ne
      have qbig : 2 < q := by
        by_contra! small
        have := pq.two_le
        have q2 : q=2 := by omega
        rw [q2] at dq
        omega
      exact missing ⟨1,q,23,pq,by decide,ne,qbig,by decide,first ▸ dvd_mul_of_dvd_right dq _, div⟩)
    have rem (j : ℕ) : 23^j%8=1 ∨ 23^j%8=7 := by
      induction j with
      | zero => decide
      | succ j ih => rw [pow_succ,Nat.mul_mod]; rcases ih with h|h <;> rw [h] <;> decide
    have zz := rem (C x).primeFactorsList.length
    rw [←eq] at zz
    omega
  obtain ⟨q,pq,hq,dq⟩ := mersenne_left_factor pb (show 2049 < b by omega) (by omega)
  have dl : q ∣ p+2 := by convert dq using 1; omega
  have common {s : ℕ} (d1 : s ∣ p+2) (d2 : s ∣ F x) : s ∣ 11264 := by
    have ident : F x+2560*(p+2)=11264+(p+2)*(x^9+14*x^8+92*x^7+360*x^6+928*x^5+1600*x^4+1920*x^3+1280*x^2+1280*x) := by
      rw [xp]; dsimp [F]; ring
    have both := dvd_add d2 (dvd_mul_of_dvd_right d1 2560)
    rw [ident] at both
    exact (Nat.dvd_add_iff_left (dvd_mul_of_dvd_left d1 _)).mpr both
  have only (s : ℕ) (ps : s.Prime) (ds : s ∣ F x) : s ≤ 2049 := by
    by_contra! high
    have diff : q≠s := by
      rintro rfl
      have mem := pq.mem_primeFactors (common dl ds) (by decide)
      have tab : (11264:ℕ).primeFactors={2,11} := by decide +kernel
      rw [tab] at mem; simp only [Finset.mem_insert,Finset.mem_singleton] at mem; omega
    exact missing ⟨2048,q,s,pq,ps,diff,hq,high,fac ▸ dvd_mul_of_dvd_left dl _,fac ▸ dvd_mul_of_dvd_right ds _⟩
  -- A triple gives a possible small prime, the order of two, and the
  -- compatible exponent residues modulo the gcd of that order with 132.
  let catalog : List (ℕ × ℕ × List ℕ) := [(23,11,[3,4,6,9,10]),
    (67,66,[13,17,23,31,59]),
    (89,11,[10]),
    (199,99,[31,20]),
    (331,30,[]),
    (353,88,[]),
    (397,44,[]),
    (419,418,[5,19,1,9,17,13]),
    (463,231,[16]),
    (617,154,[17]),
    (661,660,[89]),
    (683,22,[1,21]),
    (727,121,[2]),
    (859,858,[5,31]),
    (881,55,[]),
    (947,946,[1,21,13,5,3]),
    (991,495,[28,32,4]),
    (1013,92,[]),
    (1123,1122,[13]),
    (1277,1276,[3,35,31,25,9]),
    (1321,60,[]),
    (1409,704,[13,23,7]),
    (1453,1452,[85,119,79,25]),
    (1607,803,[4,6]),
    (1783,891,[1,4,20,31,26]),
    (1871,935,[4,8,6]),
    (2003,286,[21])]
  let rows : List (ℕ × List ℕ) := [(1,[419,683,947,1783]),
    (5,[419,859,947]),
    (7,[1409]),
    (13,[67,419,727,947,1123,1409]),
    (19,[419,1871]),
    (23,[67,419,683,947,1409]),
    (29,[]),
    (35,[419,727,947,1277]),
    (41,[419,1871]),
    (49,[419,463,947]),
    (67,[419,683,947,1409,1783]),
    (71,[419,859,947]),
    (73,[]),
    (79,[67,419,727,947,1123,1277,1453]),
    (85,[419,1453,1871]),
    (89,[67,419,661,683,947]),
    (95,[1409]),
    (101,[419,727,947,1409]),
    (107,[419,1871]),
    (115,[419,463,947])]
  have idx : ∀ k : Fin 132, k.val.Coprime 132 → k.val%11 ∉ [3,4,6,9,10] →
      ∃ row ∈ rows, row.1=k.val := by decide +kernel
  have co (o : ℕ) (ho : 0 < o) (ob : o < b) : (b%o).Coprime o := by
    have h := pb.coprime_iff_not_dvd.mpr (show ¬b ∣ o by intro d; have := Nat.le_of_dvd ho d; omega)
    change Nat.gcd (b%o) o=1
    rw [←Nat.gcd_rec o b,Nat.gcd_comm]
    exact h
  obtain ⟨row,hr,rb⟩ := idx ⟨_,Nat.mod_lt b (by decide)⟩ (co 132 (by decide) (by omega)) (by
    change (b%132)%11 ∉ [3,4,6,9,10]
    rwa [Nat.mod_mod_of_dvd _ (by decide : 11 ∣ 132)])
  change row.1=b%132 at rb
  have sup (s : ℕ) (ps : s.Prime) (ds : s ∣ F x) : s ∈ row.2 := by
    have le := only s ps ds
    have nd : ¬s ∣ p+2 := by
      intro dd
      have dL : s ∣ 2^b+1 := by convert dd using 1; omega
      have three := fifth_order pb (pb.odd_of_ne_two (by omega)) ps dL (by omega)
      subst s
      have mem := (by decide : Nat.Prime 3).mem_primeFactors (common dd ds) (by decide)
      have tab : (11264:ℕ).primeFactors={2,11} := by decide +kernel
      rw [tab] at mem; simp at mem
    have s2 : s≠2 := by rintro rfl; omega
    have mult : s ∣ p^11+2048 := fac ▸ dvd_mul_of_dvd_right ds _
    have ord := eleven_order ps s2 mult nd
    obtain ⟨j,hj⟩ := ord
    have sj : s=11*j+1 := by have := ps.two_le; omega
    have lst : ∀ i : Fin 187, (11*i.val+1).Prime → ∃ e ∈ catalog, e.1=11*i.val+1 := by decide +kernel
    obtain ⟨⟨s',o,R⟩,hm,es⟩ : ∃ e ∈ catalog,e.1=s := by
      rw [sj]; exact lst ⟨j,by omega⟩ (sj ▸ ps)
    change s'=s at es
    subst s'
    have periods : ∀ e ∈ catalog, 0 < e.2.1 ∧ e.2.1 ≤ 2049 ∧
        2^e.2.1%e.1=1 ∧ ∀ i : Fin e.2.1, i.val.Coprime e.2.1 →
          (((2^i.val-1)%e.1)^11+2048)%e.1=0 → i.val%(Nat.gcd e.2.1 132) ∈ e.2.2 := by decide +kernel
    obtain ⟨op,ou,per,hit⟩ := periods _ hm
    change 0<o at op
    change o≤2049 at ou
    change 2^o%s=1 at per
    have mo : Nat.ModEq s (2^o) 1 := by change 2^o%s=1%s; rw [Nat.mod_eq_of_lt ps.one_lt]; exact per
    have red := eleven_period (b:=b) mo
    have pm : Nat.ModEq s p ((2^(b%o)-1)%s) := by
      apply Nat.ModEq.trans _ (Nat.mod_modEq _ _).symm
      apply Nat.ModEq.add_right_cancel' 1
      rw [base,Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide : 0<2))]
      exact red
    have rr := (pm.pow 11).add_right 2048
    have z := Nat.mod_eq_zero_of_dvd mult
    have com := hit ⟨b%o,Nat.mod_lt b op⟩ (co o op (by omega)) (rr ▸ z)
    change (b%o)%(Nat.gcd o 132) ∈ R at com
    have rowsOk : ∀ r ∈ rows, ∀ t ∈ catalog, r.1%(Nat.gcd t.2.1 132) ∈ t.2.2 → t.1 ∈ r.2 := by decide +kernel
    apply rowsOk _ hr _ hm
    change row.1%(Nat.gcd o 132) ∈ R
    rw [rb,Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_right _ _)]
    rwa [Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_left _ _)] at com
  obtain ⟨D,t,dt,sf⟩ := Nat.sq_mul_squarefree (F x)
  let T := D.primeFactors
  have sub : T ∈ row.2.toFinset.powerset := Finset.mem_powerset.mpr (by
    intro s hs
    obtain ⟨ps,ds,_⟩ := Nat.mem_primeFactors.mp hs
    exact List.mem_toFinset.mpr (sup s ps (dt ▸ dvd_mul_of_dvd_right ds _)))
  have prod : (∏ a ∈ T, a)=D := Nat.prod_primeFactors_of_squarefree sf
  have dmod : D%8=7 := by
    have mm := (Nat.mod_modEq t 8).symm.pow 2
    have dd := mm.mul (Nat.mod_modEq D 8).symm
    change (t^2*D)%8=((t%8)^2*(D%8))%8 at dd
    rw [dt,f8] at dd
    have check : ∀ u v : Fin 8, (u.val^2*v.val)%8=7 → v.val=7 := by decide
    exact check ⟨_,Nat.mod_lt t (by decide)⟩ ⟨_,Nat.mod_lt D (by decide)⟩ dd.symm
  -- For each possible squarefree part D of F, one of these moduli shows
  -- that D times a square cannot be F in the prescribed exponent class.
  let mods : List ℕ := [3,5,7,13,23,89,397]
  have cover : ∀ r ∈ rows, ∀ U ∈ r.2.toFinset.powerset,
      (∏ a ∈ U,a)%8=7 → ∃ m ∈ mods,
        (((F ((2^(r.1+132)-3)%m)*(∏ a ∈ U,a))%m)^((m-1)/2))%m=m-1 := by decide +kernel
  obtain ⟨m,hm,test⟩ := cover row hr T sub (prod ▸ dmod)
  have squares : ∀ m ∈ mods, ∀ w : Fin m, ((w.val^2%m)^((m-1)/2))%m ≠ m-1 := by decide +kernel
  have tab : ∀ m ∈ mods, 1 < m ∧ 2^132%m=1 := by decide +kernel
  obtain ⟨mb,per⟩ := tab _ hm
  have mo : Nat.ModEq m (2^132) 1 := by change 2^132%m=1%m; rwa [Nat.mod_eq_of_lt mb]
  have red := eleven_period (b:=b) mo
  have large : 3≤2^(row.1+132) := by
    have zz := Nat.pow_le_pow_right (by decide : 0<2) (show 2≤row.1+132 by omega)
    norm_num at zz; omega
  have xa : Nat.ModEq m x ((2^(row.1+132)-3)%m) := by
    apply Nat.ModEq.trans _ (Nat.mod_modEq _ _).symm
    apply Nat.ModEq.add_right_cancel' 3
    rw [bx,Nat.sub_add_cancel large,pow_add,rb]
    have lift := mo.mul_left (2^(b%132))
    rw [mul_one] at lift
    exact red.trans lift.symm
  have left := (Nat.mod_modEq (t*D) m).pow 2
  have right := (fc xa).mul_right D
  have ident : (t*D)^2=F x*D := by rw [←dt]; ring
  have both := (ident ▸ left).trans right
  change (((t*D)%m)^2)%m=(F ((2^(row.1+132)-3)%m)*D)%m at both
  apply squares m hm ⟨(t*D)%m,Nat.mod_lt _ (by omega)⟩
  dsimp only
  rw [both]
  rwa [prod] at test

/-- Two-prime witnesses cover both the bounded and unbounded Mersenne indices. -/
theorem mersenne_eleventh_witness {p b : ℕ} (pp : p.Prime) (base : p+1=2^b) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p^11+d ∧ s ∣ p^11+d := by
  by_cases small : b≤2049
  · have ep : p=2^b-1 := by omega
    have b1 : b≠1 := by rintro rfl; norm_num at base; have := pp.two_le; omega
    have pb : b.Prime := (Nat.prime_of_pow_sub_one_prime b1 (ep ▸ pp)).2
    exact ep ▸ eleventh_small small pb
  · exact mersenne_eleven_large_witness pp base (by omega)

-- Each entry records (b,d,q,s). The modular tests use the small exponents
-- b modulo q−1 and b modulo s−1. The second test covers the prime indices
-- in one interval of length 64.
private theorem thirteenth_witness_prime {q : ℕ} (mem : q ∈ [5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,113,127,131,137,139,149,163,167,197,227,233]) : q.Prime := by
  have table : ∀ t ∈ ([5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,113,127,131,137,139,149,163,167,197,227,233] : List ℕ), t.Prime := by decide +kernel
  exact table q mem

private theorem thirteenth_small_block {b start : ℕ} (small : b≤8193) (pb : b.Prime)
    (lower : start≤b) (upper : b<start+64) (certs : List (ℕ × ℕ × ℕ × ℕ))
    (valid : certs.all (fun z => decide (
      z.2.2.1 ∈ [5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,113,127,131,137,139,149,163,167,197,227,233] ∧ z.2.2.2 ∈ [5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,113,127,131,137,139,149,163,167,197,227,233] ∧
      z.2.2.1≠z.2.2.2 ∧ z.2.1+1<z.2.2.1 ∧ z.2.1+1<z.2.2.2 ∧
      (2^(z.2.2.1-1)%z.2.2.1=1 ∧ (((2^(z.1%(z.2.2.1-1))-1)%z.2.2.1)^13+z.2.1)%z.2.2.1=0) ∧
      (2^(z.2.2.2-1)%z.2.2.2=1 ∧ (((2^(z.1%(z.2.2.2-1))-1)%z.2.2.2)^13+z.2.1)%z.2.2.2=0))) = true)
    (covers : (List.range 64).all (fun i => decide (8193<start+i) ||
      certs.any (fun z => z.1 == start+i) || decide (start+i<2) ||
      ([2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89] : List ℕ).any (fun d => decide (1<d ∧ d<start+i ∧ (start+i)%d=0))) = true) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  let v := b-start
  have index : start+v=b := by dsimp [v]; omega
  have hit := List.all_eq_true.mp covers v (List.mem_range.mpr (show v<64 by dsimp [v]; omega))
  simp only [index, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq, beq_iff_eq] at hit
  have high : ¬8193<b := by omega
  have low : ¬b<2 := by have := pb.two_le; omega
  have noDiv : ¬∃ d ∈ ([2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89] : List ℕ), 1<d ∧ d<b ∧ b%d=0 := by
    rintro ⟨d,_,hd,lt,div⟩
    have bad := (Nat.dvd_prime pb).mp (Nat.dvd_iff_mod_eq_zero.mpr div)
    omega
  have good : ∃ z ∈ certs, z.1=b := ((hit.resolve_right noDiv).resolve_right low).resolve_left high
  obtain ⟨⟨j,d,q,s⟩,mem,ej⟩ := good
  change j=b at ej
  subst j
  have facts := of_decide_eq_true (List.all_eq_true.mp valid _ mem)
  obtain ⟨qp,sp,ne,hq,hs,tq,ts⟩ := facts
  have pq := thirteenth_witness_prime qp
  have ps := thirteenth_witness_prime sp
  have lift (t : ℕ) (pt : t.Prime) (per : 2^(t-1)%t=1)
      (hit : (((2^(b%(t-1))-1)%t)^13+d)%t=0) : t ∣ (2^b-1)^13+d := by
    have m : Nat.ModEq t (2^(t-1)) 1 := by
      change 2^(t-1)%t=1%t
      rwa [Nat.mod_eq_of_lt pt.one_lt]
    have red : Nat.ModEq t (2^b) (2^(b%(t-1))) := by
      calc
        2^b = 2^(b%(t-1))*(2^(t-1))^(b/(t-1)) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
        _ ≡ 2^(b%(t-1))*1^(b/(t-1)) [MOD t] := (m.pow _).mul_left _
        _ = _ := by simp
    have pm : Nat.ModEq t (2^b-1) ((2^(b%(t-1))-1)%t) := by
      apply Nat.ModEq.trans _ (Nat.mod_modEq _ _).symm
      apply Nat.ModEq.add_right_cancel' 1
      rw [Nat.sub_add_cancel (Nat.one_le_pow b 2 (by decide)),
        Nat.sub_add_cancel (Nat.one_le_pow (b%(t-1)) 2 (by decide))]
      exact red
    exact Nat.dvd_iff_mod_eq_zero.mpr (((pm.pow 13).add_right d).trans (show Nat.ModEq t _ 0 from hit))
  exact ⟨d,q,s,pq,ps,ne,hq,hs,lift q pq tq.1 tq.2,lift s ps ts.1 ts.2⟩

set_option maxRecDepth 8192 in
private theorem thirteenth_block_0 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=0) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=0) small pb (by omega) (by omega)
    [(2,5,17,19),(3,3,5,23),(5,8,11,13),(7,3,5,13),(11,7,13,47),(13,12,17,31),(17,4,7,11),(19,3,5,13),(23,7,13,19),(29,17,19,23),(31,3,5,13),(37,30,53,89),(41,7,19,59),(43,3,5,13),(47,4,7,11),(53,12,17,31),(59,7,11,13),(61,55,59,79)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_1 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=1) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=64) small pb (by omega) (by omega)
    [(67,3,5,13),(71,5,23,37),(73,9,11,41),(79,3,5,13),(83,3,5,61),(89,4,7,31),(97,4,11,19),(101,14,23,37),(103,3,5,13),(107,4,7,11),(109,6,23,47),(113,9,11,41),(127,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_2 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=2) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=128) small pb (by omega) (by omega)
    [(131,7,13,19),(137,4,7,11),(139,3,5,13),(149,7,11,19),(151,3,5,13),(157,7,31,59),(163,3,5,13),(167,4,7,11),(173,12,17,31),(179,7,11,13),(181,12,17,67),(191,21,37,47)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_3 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=3) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=192) small pb (by omega) (by omega)
    [(193,9,11,41),(197,4,7,11),(199,3,5,13),(211,3,5,13),(223,3,5,13),(227,4,7,11),(229,2,23,61),(233,9,11,41),(239,7,11,13),(241,7,47,67),(251,2,23,43)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_4 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=4) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=256) small pb (by omega) (by omega)
    [(257,4,7,11),(263,12,29,31),(269,13,19,29),(271,3,5,13),(277,4,11,19),(281,17,19,47),(283,3,5,13),(293,12,17,31),(307,3,5,13),(311,7,13,19),(313,9,11,41),(317,4,7,11)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_5 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=5) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=320) small pb (by omega) (by omega)
    [(331,3,5,13),(337,68,71,83),(347,4,7,11),(349,4,19,31),(353,9,11,41),(359,7,11,13),(367,3,5,13),(373,12,17,31),(379,3,5,13),(383,7,13,19)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_6 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=6) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=384) small pb (by omega) (by omega)
    [(389,4,7,31),(397,23,53,79),(401,4,7,61),(409,55,59,79),(419,7,11,13),(421,20,137,149),(431,13,19,43),(433,9,11,41),(439,3,5,13),(443,3,5,23)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_7 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=7) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=448) small pb (by omega) (by omega)
    [(449,4,7,31),(457,4,11,19),(461,4,7,61),(463,3,5,13),(467,4,7,11),(479,7,11,13),(487,3,5,13),(491,7,13,19),(499,3,5,13),(503,4,7,47),(509,7,11,19)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_8 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=8) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=512) small pb (by omega) (by omega)
    [(521,13,19,29),(523,3,5,13),(541,43,97,149),(547,3,5,13),(557,4,7,11),(563,7,13,19),(569,4,7,31),(571,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_9 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=9) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=576) small pb (by omega) (by omega)
    [(577,55,61,79),(587,4,7,11),(593,9,11,41),(599,7,11,13),(601,22,47,59),(607,3,5,13),(613,12,17,31),(617,4,7,11),(619,3,5,13),(631,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_10 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=10) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=640) small pb (by omega) (by omega)
    [(641,3,23,29),(643,3,5,13),(647,4,7,11),(653,12,17,31),(659,7,11,13),(661,30,53,97),(673,9,11,41),(677,4,7,11),(683,12,29,31),(691,3,5,13),(701,4,7,61)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_11 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=11) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=704) small pb (by omega) (by omega)
    [(709,4,19,31),(719,7,11,13),(727,3,5,13),(733,12,17,31),(739,3,5,13),(743,7,13,19),(751,3,5,13),(757,55,59,61),(761,4,7,61)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_12 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=12) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=768) small pb (by omega) (by omega)
    [(769,2,43,61),(773,13,19,29),(787,3,5,13),(797,4,7,11),(809,13,19,23),(811,3,5,13),(821,17,19,23),(823,3,5,13),(827,4,7,11),(829,23,53,79)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_13 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=13) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=832) small pb (by omega) (by omega)
    [(839,7,11,13),(853,12,17,31),(857,4,7,11),(859,3,5,13),(863,5,23,37),(877,24,41,59),(881,2,37,43),(883,3,5,13),(887,4,7,11)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_14 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=14) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=896) small pb (by omega) (by omega)
    [(907,3,5,13),(911,7,13,59),(919,3,5,13),(929,4,7,31),(937,23,71,89),(941,13,23,29),(947,4,7,11),(953,9,11,41)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_15 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=15) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=960) small pb (by omega) (by omega)
    [(967,3,5,13),(971,3,5,23),(977,4,7,11),(983,4,7,29),(991,3,5,13),(997,4,11,19),(1009,4,31,47),(1013,12,17,31),(1019,7,11,13),(1021,2,23,43)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_16 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=16) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=1024) small pb (by omega) (by omega)
    [(1031,7,13,19),(1033,9,11,41),(1039,3,5,13),(1049,7,11,19),(1051,3,5,13),(1061,13,19,43),(1063,3,5,13),(1069,4,19,31),(1087,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_17 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=17) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=1088) small pb (by omega) (by omega)
    [(1091,38,41,59),(1093,12,17,31),(1097,4,7,11),(1103,7,13,19),(1109,4,7,31),(1117,13,23,43),(1123,3,5,13),(1129,11,47,73),(1151,4,7,29)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_18 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=18) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=1152) small pb (by omega) (by omega)
    [(1153,9,11,41),(1163,19,23,29),(1171,3,5,13),(1181,4,7,61),(1187,4,7,11),(1193,9,11,41),(1201,23,37,53),(1213,12,17,31)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_19 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=19) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=1216) small pb (by omega) (by omega)
    [(1217,4,7,11),(1223,3,5,43),(1229,7,11,19),(1231,3,5,13),(1237,12,17,67),(1249,13,23,29),(1259,7,11,13),(1277,4,7,11),(1279,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_20 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=20) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=1280) small pb (by omega) (by omega)
    [(1283,7,13,19),(1289,4,7,31),(1291,3,5,13),(1297,7,31,67),(1301,4,7,61),(1303,3,5,13),(1307,4,7,11),(1319,7,11,13),(1321,47,101,197),(1327,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_21 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=21) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=1344) small pb (by omega) (by omega)
    [(1361,4,7,61),(1367,4,7,11),(1373,12,17,31),(1381,11,73,103),(1399,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_22 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=22) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=1408) small pb (by omega) (by omega)
    [(1409,7,11,19),(1423,3,5,13),(1427,4,7,11),(1429,4,19,31),(1433,9,11,41),(1439,7,11,13),(1447,3,5,13),(1451,11,17,47),(1453,12,17,31),(1459,3,5,13),(1471,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_23 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=23) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=1472) small pb (by omega) (by omega)
    [(1481,4,7,61),(1483,3,5,13),(1487,4,7,11),(1489,23,37,53),(1493,12,17,31),(1499,7,11,13),(1511,5,37,47),(1523,12,29,31),(1531,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_24 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=24) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=1536) small pb (by omega) (by omega)
    [(1543,3,5,13),(1549,7,11,59),(1553,9,11,41),(1559,7,11,13),(1567,3,5,13),(1571,7,13,19),(1579,3,5,13),(1583,3,5,61),(1597,23,37,89)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_25 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=25) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=1600) small pb (by omega) (by omega)
    [(1601,13,19,23),(1607,4,7,11),(1609,4,19,31),(1613,17,19,23),(1619,7,11,13),(1621,30,53,89),(1627,3,5,13),(1637,4,7,11),(1657,15,29,59),(1663,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_26 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=26) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=1664) small pb (by omega) (by omega)
    [(1667,4,7,11),(1669,23,37,53),(1693,12,17,31),(1697,4,7,11),(1699,3,5,13),(1709,4,7,31),(1721,4,7,61),(1723,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_27 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=27) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=1728) small pb (by omega) (by omega)
    [(1733,12,17,31),(1741,3,23,43),(1747,3,5,13),(1753,9,11,41),(1759,3,5,13),(1777,30,47,53),(1783,3,5,13),(1787,4,7,11),(1789,4,19,31)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_28 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=28) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=1792) small pb (by omega) (by omega)
    [(1801,21,29,47),(1811,17,19,23),(1823,7,13,19),(1831,3,5,13),(1847,4,7,11)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_29 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=29) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=1856) small pb (by omega) (by omega)
    [(1861,1,53,79),(1867,3,5,13),(1871,32,47,73),(1873,3,23,29),(1877,4,7,11),(1879,3,5,13),(1889,4,7,31),(1901,4,7,61),(1907,4,7,11),(1913,6,23,37)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_30 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=30) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=1920) small pb (by omega) (by omega)
    [(1931,7,13,19),(1933,12,17,31),(1949,7,11,19),(1951,3,5,13),(1973,12,17,31),(1979,7,11,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_31 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=31) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=1984) small pb (by omega) (by omega)
    [(1987,3,5,13),(1993,9,11,41),(1997,4,7,11),(1999,3,5,13),(2003,7,13,19),(2011,3,5,13),(2017,1,53,79),(2027,4,7,11),(2029,2,43,61),(2039,7,11,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_32 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=32) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=2048) small pb (by omega) (by omega)
    [(2053,12,17,31),(2063,3,5,43),(2069,4,7,31),(2081,14,23,37),(2083,3,5,13),(2087,4,7,11),(2089,7,11,67),(2099,7,11,13),(2111,7,13,19)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_33 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=33) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=2112) small pb (by omega) (by omega)
    [(2113,9,11,41),(2129,7,11,19),(2131,3,5,13),(2137,23,37,53),(2141,2,37,43),(2143,3,5,13),(2153,9,11,41),(2161,26,83,113)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_34 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=34) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=2176) small pb (by omega) (by omega)
    [(2179,3,5,13),(2203,3,5,13),(2207,4,7,11),(2213,12,17,31),(2221,6,23,73),(2237,4,7,11),(2239,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_35 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=35) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=2240) small pb (by omega) (by omega)
    [(2243,4,7,29),(2251,3,5,13),(2267,4,7,11),(2269,23,53,79),(2273,9,11,41),(2281,16,19,71),(2287,3,5,13),(2293,12,17,31),(2297,4,7,11)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_36 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=36) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=2304) small pb (by omega) (by omega)
    [(2309,7,11,19),(2311,3,5,13),(2333,12,17,31),(2339,7,11,13),(2341,36,43,113),(2347,3,5,13),(2351,17,19,47),(2357,4,7,11)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_37 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=37) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=2368) small pb (by omega) (by omega)
    [(2371,3,5,13),(2377,13,43,59),(2381,4,7,61),(2383,3,5,13),(2389,4,31,47),(2393,13,19,23),(2399,7,11,13),(2411,4,7,29),(2417,4,7,11),(2423,3,5,23)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_38 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=38) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=2432) small pb (by omega) (by omega)
    [(2437,4,11,19),(2441,4,7,61),(2447,4,7,11),(2459,7,11,13),(2467,3,5,13),(2473,9,11,41),(2477,4,7,11)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_39 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=39) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=2496) small pb (by omega) (by omega)
    [(2503,3,5,13),(2521,56,79,197),(2531,41,59,61),(2539,3,5,13),(2543,7,13,19),(2549,4,7,31),(2551,3,5,13),(2557,12,17,67)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_40 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=40) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=2560) small pb (by omega) (by omega)
    [(2579,7,11,13),(2591,13,19,23),(2593,9,11,41),(2609,4,7,31),(2617,4,11,19),(2621,4,7,61)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_41 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=41) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=2624) small pb (by omega) (by omega)
    [(2633,9,11,41),(2647,3,5,13),(2657,4,7,11),(2659,3,5,13),(2663,4,7,29),(2671,3,5,13),(2677,30,89,97),(2683,3,5,13),(2687,4,7,11)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_42 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=42) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=2688) small pb (by omega) (by omega)
    [(2689,4,19,31),(2693,12,17,31),(2699,7,11,13),(2707,3,5,13),(2711,4,7,47),(2713,9,11,41),(2719,3,5,13),(2729,4,7,31),(2731,3,5,13),(2741,3,29,47),(2749,7,11,67)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_43 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=43) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=2752) small pb (by omega) (by omega)
    [(2753,9,11,41),(2767,3,5,13),(2777,4,7,11),(2789,13,19,23),(2791,3,5,13),(2797,4,11,19),(2801,17,19,23),(2803,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_44 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=44) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=2816) small pb (by omega) (by omega)
    [(2819,7,11,13),(2833,9,11,41),(2837,4,7,11),(2843,5,23,37),(2851,3,5,13),(2857,23,37,53),(2861,4,7,61),(2879,7,11,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_45 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=45) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=2880) small pb (by omega) (by omega)
    [(2887,3,5,13),(2897,4,7,11),(2903,7,13,19),(2909,4,7,31),(2917,55,61,79),(2927,4,7,11),(2939,7,11,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_46 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=46) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=2944) small pb (by omega) (by omega)
    [(2953,9,11,41),(2957,4,7,11),(2963,33,43,47),(2969,4,7,31),(2971,3,5,13),(2999,7,11,13),(3001,56,71,79)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_47 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=47) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=3008) small pb (by omega) (by omega)
    [(3011,7,13,19),(3019,3,5,13),(3023,2,23,43),(3037,23,37,71),(3041,13,19,29),(3049,4,19,31),(3061,58,131,163),(3067,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_48 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=48) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=3072) small pb (by omega) (by omega)
    [(3079,3,5,13),(3083,7,13,19),(3089,4,7,31),(3109,11,59,73),(3119,7,11,13),(3121,38,59,107)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_49 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=49) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=3136) small pb (by omega) (by omega)
    [(3137,4,7,11),(3163,3,5,13),(3167,4,7,11),(3169,23,53,79),(3181,23,37,83),(3187,3,5,13),(3191,7,13,19)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_50 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=50) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=3200) small pb (by omega) (by omega)
    [(3203,12,29,31),(3209,7,11,19),(3217,4,11,47),(3221,2,23,37),(3229,4,19,31),(3251,4,7,29),(3253,12,17,31),(3257,4,7,11),(3259,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_51 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=51) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=3264) small pb (by omega) (by omega)
    [(3271,3,5,13),(3299,7,11,13),(3301,13,43,47),(3307,3,5,13),(3313,9,11,41),(3319,3,5,13),(3323,3,5,43)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_52 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=52) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=3328) small pb (by omega) (by omega)
    [(3329,4,7,31),(3331,3,5,13),(3343,3,5,13),(3347,4,7,11),(3359,7,11,13),(3361,23,37,53),(3371,7,13,19),(3373,12,17,31),(3389,7,11,19),(3391,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_53 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=53) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=3392) small pb (by omega) (by omega)
    [(3407,4,7,11),(3413,3,23,29),(3433,9,11,41),(3449,4,7,31)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_54 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=54) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=3456) small pb (by omega) (by omega)
    [(3457,56,79,89),(3461,7,19,47),(3463,3,5,13),(3467,4,7,11),(3469,30,53,89),(3491,3,5,43),(3499,3,5,13),(3511,3,5,13),(3517,4,11,19)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_55 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=55) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=3520) small pb (by omega) (by omega)
    [(3527,4,7,11),(3529,2,23,61),(3533,12,17,31),(3539,7,11,13),(3541,23,37,53),(3547,3,5,13),(3557,4,7,11),(3559,3,5,13),(3571,3,5,13),(3581,13,19,23),(3583,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_56 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=56) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=3584) small pb (by omega) (by omega)
    [(3593,17,19,23),(3607,3,5,13),(3613,12,17,31),(3617,4,7,11),(3623,7,13,19),(3631,3,5,13),(3637,7,31,59),(3643,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_57 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=57) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=3648) small pb (by omega) (by omega)
    [(3659,7,11,13),(3671,4,7,29),(3673,9,11,41),(3677,4,7,11),(3691,3,5,13),(3697,4,11,19),(3701,4,7,61),(3709,2,43,61)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_58 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=58) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=3712) small pb (by omega) (by omega)
    [(3719,7,11,13),(3727,3,5,13),(3733,12,17,31),(3739,3,5,13),(3761,13,19,47),(3767,4,7,11),(3769,4,19,31)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_59 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=59) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=3776) small pb (by omega) (by omega)
    [(3779,7,11,13),(3793,9,11,41),(3797,4,7,11),(3803,7,13,19),(3821,4,7,61),(3823,3,5,13),(3833,9,11,41)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_60 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=60) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=3840) small pb (by omega) (by omega)
    [(3847,3,5,13),(3851,19,29,47),(3853,12,17,31),(3863,3,5,61),(3877,4,11,19),(3881,4,7,61),(3889,13,23,43)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_61 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=61) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=3904) small pb (by omega) (by omega)
    [(3907,3,5,13),(3911,7,13,19),(3917,4,7,11),(3919,3,5,13),(3923,4,7,29),(3929,7,11,19),(3931,3,5,13),(3943,3,5,13),(3947,4,7,11),(3967,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_62 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=62) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=3968) small pb (by omega) (by omega)
    [(3989,17,19,23),(4001,13,43,59),(4003,3,5,13),(4007,4,7,11),(4013,12,17,31),(4019,7,11,13),(4021,13,23,29),(4027,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_63 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=63) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=4032) small pb (by omega) (by omega)
    [(4049,13,19,29),(4051,3,5,13),(4057,4,11,19),(4073,9,11,41),(4079,7,11,13),(4091,7,13,19),(4093,12,17,31)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_64 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=64) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=4096) small pb (by omega) (by omega)
    [(4099,3,5,13),(4111,3,5,13),(4127,4,7,11),(4129,4,19,31),(4133,12,17,31),(4139,7,11,13),(4153,9,11,41),(4157,4,7,11),(4159,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_65 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=65) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=4160) small pb (by omega) (by omega)
    [(4177,15,29,47),(4201,6,23,73),(4211,13,19,43),(4217,4,7,11),(4219,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_66 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=66) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=4224) small pb (by omega) (by omega)
    [(4229,4,7,31),(4231,3,5,13),(4241,4,7,61),(4243,3,5,13),(4253,12,17,31),(4259,7,11,13),(4261,23,37,53),(4271,7,13,19),(4273,9,11,41),(4283,3,5,61)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_67 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=67) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=4288) small pb (by omega) (by omega)
    [(4289,7,11,19),(4297,23,37,53),(4327,3,5,13),(4337,4,7,11),(4339,3,5,13),(4349,4,7,31)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_68 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=68) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=4352) small pb (by omega) (by omega)
    [(4357,24,41,59),(4363,3,5,13),(4373,13,19,23),(4391,7,13,59),(4397,4,7,11),(4409,4,7,31)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_69 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=69) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=4416) small pb (by omega) (by omega)
    [(4421,17,19,47),(4423,3,5,13),(4441,11,47,73),(4447,3,5,13),(4451,7,13,19),(4457,4,7,11),(4463,12,29,31)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_70 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=70) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=4480) small pb (by omega) (by omega)
    [(4481,4,7,61),(4483,3,5,13),(4493,12,17,31),(4507,3,5,13),(4513,9,11,41),(4517,4,7,11),(4519,3,5,13),(4523,7,13,19)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_71 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=71) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=4544) small pb (by omega) (by omega)
    [(4547,4,7,11),(4549,16,19,59),(4561,6,73,127),(4567,3,5,13),(4583,17,19,23),(4591,3,5,13),(4597,4,11,19),(4603,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_72 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=72) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=4608) small pb (by omega) (by omega)
    [(4621,12,17,149),(4637,4,7,11),(4639,3,5,13),(4643,4,7,47),(4649,7,11,19),(4651,3,5,13),(4657,7,31,47),(4663,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_73 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=73) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=4672) small pb (by omega) (by omega)
    [(4673,9,11,41),(4679,7,11,13),(4691,70,73,97),(4703,7,13,19),(4721,4,7,61),(4723,3,5,13),(4729,23,37,53),(4733,12,17,31)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_74 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=74) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=4736) small pb (by omega) (by omega)
    [(4751,3,5,43),(4759,3,5,13),(4783,3,5,13),(4787,4,7,11),(4789,15,59,83),(4793,9,11,41),(4799,7,11,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_75 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=75) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=4800) small pb (by omega) (by omega)
    [(4801,23,37,53),(4813,12,17,31),(4817,4,7,11),(4831,3,5,13),(4861,66,101,103)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_76 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=76) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=4864) small pb (by omega) (by omega)
    [(4871,2,23,43),(4877,4,7,11),(4889,4,7,31),(4903,3,5,13),(4909,25,71,103),(4919,7,11,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_77 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=77) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=4928) small pb (by omega) (by omega)
    [(4931,3,5,23),(4933,12,17,31),(4937,4,7,11),(4943,3,5,61),(4951,3,5,13),(4957,4,11,19),(4967,4,7,11),(4969,2,43,61),(4973,12,17,31),(4987,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_78 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=78) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=4992) small pb (by omega) (by omega)
    [(4993,9,11,41),(4999,3,5,13),(5003,3,5,43),(5009,7,11,19),(5011,3,5,13),(5021,21,29,47),(5023,3,5,13),(5039,7,11,13),(5051,38,41,101)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_79 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=79) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=5056) small pb (by omega) (by omega)
    [(5059,3,5,13),(5077,23,53,79),(5081,6,23,37),(5087,4,7,11),(5099,7,11,13),(5101,56,59,71),(5107,3,5,13),(5113,9,11,41),(5119,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_80 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=80) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=5120) small pb (by omega) (by omega)
    [(5147,4,7,11),(5153,9,11,41),(5167,3,5,13),(5171,7,13,19),(5179,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_81 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=81) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=5184) small pb (by omega) (by omega)
    [(5189,7,11,19),(5197,23,37,53),(5209,4,19,31),(5227,3,5,13),(5231,23,53,83),(5233,9,11,41),(5237,4,7,11)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_82 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=82) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=5248) small pb (by omega) (by omega)
    [(5261,3,23,29),(5273,9,11,41),(5279,7,11,13),(5281,15,47,83),(5297,4,7,11),(5303,12,29,31),(5309,13,19,29)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_83 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=83) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=5312) small pb (by omega) (by omega)
    [(5323,3,5,13),(5333,12,17,31),(5347,3,5,13),(5351,7,13,19)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_84 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=84) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=5376) small pb (by omega) (by omega)
    [(5381,4,7,61),(5387,4,7,11),(5393,9,11,41),(5399,7,11,13),(5407,3,5,13),(5413,12,17,31),(5417,4,7,11),(5419,3,5,13),(5431,3,5,13),(5437,3,23,43)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_85 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=85) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=5440) small pb (by omega) (by omega)
    [(5441,4,7,61),(5443,3,5,13),(5449,1,53,79),(5471,13,19,43),(5477,4,7,11),(5479,3,5,13),(5483,3,5,61),(5501,4,7,61),(5503,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_86 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=86) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=5504) small pb (by omega) (by omega)
    [(5507,4,7,11),(5519,7,11,13),(5521,39,59,83),(5527,3,5,13),(5531,7,13,19),(5557,23,37,71),(5563,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_87 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=87) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=5568) small pb (by omega) (by omega)
    [(5569,3,23,29),(5573,17,19,23),(5581,43,59,97),(5591,3,5,23),(5623,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_88 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=88) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=5632) small pb (by omega) (by omega)
    [(5639,7,11,13),(5641,2,23,43),(5647,3,5,13),(5651,5,37,47),(5653,12,17,31),(5657,4,7,11),(5659,3,5,13),(5669,4,7,31),(5683,3,5,13),(5689,26,41,113),(5693,12,17,31)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_89 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=89) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=5696) small pb (by omega) (by omega)
    [(5701,23,37,53),(5711,7,13,19),(5717,4,7,11),(5737,13,23,43),(5741,13,19,59),(5743,3,5,13),(5749,4,19,31)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_90 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=90) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=5760) small pb (by omega) (by omega)
    [(5779,3,5,13),(5783,7,13,19),(5791,3,5,13),(5801,4,7,61),(5807,4,7,11),(5813,13,19,29),(5821,23,53,79)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_91 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=91) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=5824) small pb (by omega) (by omega)
    [(5827,3,5,13),(5839,3,5,13),(5843,3,5,43),(5849,4,7,31),(5851,3,5,13),(5857,4,11,19),(5861,33,43,47),(5867,4,7,11),(5869,13,23,29),(5879,7,11,13),(5881,23,37,53)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_92 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=92) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=5888) small pb (by omega) (by omega)
    [(5897,4,7,11),(5903,29,41,47),(5923,3,5,13),(5927,4,7,11),(5939,7,11,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_93 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=93) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=5952) small pb (by omega) (by omega)
    [(5953,9,11,41),(5981,4,7,61),(5987,4,7,11),(6007,3,5,13),(6011,5,23,37)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_94 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=94) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=6016) small pb (by omega) (by omega)
    [(6029,4,7,31),(6037,4,11,19),(6043,3,5,13),(6047,4,7,11),(6053,12,17,31),(6067,3,5,13),(6073,9,11,41),(6079,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_95 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=95) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=6080) small pb (by omega) (by omega)
    [(6089,7,11,19),(6091,3,5,13),(6101,13,19,43),(6113,9,11,41),(6121,36,43,113),(6131,7,13,59),(6133,12,17,31),(6143,7,13,19)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_96 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=96) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=6144) small pb (by omega) (by omega)
    [(6151,3,5,13),(6163,3,5,13),(6173,12,17,31),(6197,4,7,11),(6199,3,5,13),(6203,3,5,61)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_97 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=97) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=6208) small pb (by omega) (by omega)
    [(6211,3,5,13),(6217,4,11,19),(6221,14,37,59),(6229,2,43,61),(6247,3,5,13),(6257,4,7,11),(6263,3,5,43),(6269,7,11,19),(6271,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_98 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=98) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=6272) small pb (by omega) (by omega)
    [(6277,3,43,83),(6287,4,7,11),(6299,7,11,13),(6301,12,17,167),(6311,38,41,59),(6317,4,7,11),(6323,7,13,19),(6329,4,7,31)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_99 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=99) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=6336) small pb (by omega) (by omega)
    [(6337,55,61,79),(6343,3,5,13),(6353,13,19,23),(6359,7,11,13),(6361,3,23,43),(6367,3,5,13),(6373,12,17,31),(6379,3,5,13),(6389,4,7,31),(6397,4,11,19)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_100 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=100) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=6400) small pb (by omega) (by omega)
    [(6421,35,67,127),(6427,3,5,13),(6449,7,11,19),(6451,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_101 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=101) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=6464) small pb (by omega) (by omega)
    [(6469,4,19,31),(6473,9,11,41),(6481,23,53,79),(6491,17,19,47),(6521,13,43,47)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_102 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=102) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=6528) small pb (by omega) (by omega)
    [(6529,4,31,47),(6547,3,5,13),(6551,13,19,23),(6553,9,11,41),(6563,17,19,23),(6569,13,19,29),(6571,3,5,13),(6577,4,11,19),(6581,12,17,59)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_103 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=103) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=6592) small pb (by omega) (by omega)
    [(6599,7,11,13),(6607,3,5,13),(6619,3,5,13),(6637,24,41,47),(6653,12,17,31)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_104 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=104) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=6656) small pb (by omega) (by omega)
    [(6659,7,11,13),(6661,13,23,43),(6673,9,11,41),(6679,3,5,13),(6689,4,7,31),(6691,3,5,13),(6701,4,7,61),(6703,3,5,13),(6709,7,11,67),(6719,7,11,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_105 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=105) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=6720) small pb (by omega) (by omega)
    [(6733,12,17,31),(6737,4,7,11),(6761,17,19,23),(6763,3,5,13),(6779,7,11,13),(6781,3,43,59)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_106 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=106) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=6784) small pb (by omega) (by omega)
    [(6791,7,13,19),(6793,13,23,29),(6803,5,23,37),(6823,3,5,13),(6827,4,7,11),(6829,4,19,31),(6833,14,23,37),(6841,60,227,233)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_107 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=107) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=6848) small pb (by omega) (by omega)
    [(6857,4,7,11),(6863,7,13,19),(6869,4,7,31),(6871,3,5,13),(6883,3,5,13),(6899,7,11,13),(6907,3,5,13),(6911,3,5,23)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_108 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=108) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=6912) small pb (by omega) (by omega)
    [(6917,4,7,11),(6947,4,7,11),(6949,23,53,79),(6959,7,11,13),(6961,36,43,83),(6967,3,5,13),(6971,7,13,19)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_109 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=109) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=6976) small pb (by omega) (by omega)
    [(6977,4,7,11),(6983,12,29,31),(6991,3,5,13),(6997,55,61,71),(7001,4,7,61),(7013,12,17,31),(7019,7,11,13),(7027,3,5,13),(7039,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_110 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=110) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=7040) small pb (by omega) (by omega)
    [(7043,7,13,19),(7057,88,107,139),(7069,23,37,53),(7079,7,11,13),(7103,3,5,43)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_111 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=111) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=7104) small pb (by omega) (by omega)
    [(7109,3,23,29),(7121,4,7,61),(7127,4,7,11),(7129,36,43,113),(7151,7,13,19),(7159,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_112 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=112) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=7168) small pb (by omega) (by omega)
    [(7177,51,89,103),(7187,4,7,11),(7193,9,11,41),(7207,3,5,13),(7211,13,23,47),(7213,12,17,31),(7219,3,5,13),(7229,4,7,31)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_113 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=113) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=7232) small pb (by omega) (by omega)
    [(7237,7,31,67),(7243,3,5,13),(7247,4,7,11),(7253,12,17,31),(7283,4,7,29)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_114 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=114) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=7296) small pb (by omega) (by omega)
    [(7297,4,11,19),(7307,4,7,11),(7309,12,17,67),(7321,16,19,71),(7331,7,13,19),(7333,12,17,31),(7349,7,11,19),(7351,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_115 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=115) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=7360) small pb (by omega) (by omega)
    [(7369,4,19,31),(7393,9,11,41),(7411,3,5,13),(7417,3,23,29)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_116 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=116) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=7424) small pb (by omega) (by omega)
    [(7433,9,11,41),(7451,4,7,29),(7457,4,7,11),(7459,3,5,13),(7477,4,11,19),(7481,4,7,61),(7487,4,7,11)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_117 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=117) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=7488) small pb (by omega) (by omega)
    [(7489,2,23,43),(7499,7,11,13),(7507,3,5,13),(7517,4,7,11),(7523,3,5,43),(7529,7,11,19),(7537,23,37,53),(7541,13,19,23),(7547,4,7,11),(7549,4,19,31)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_118 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=118) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=7552) small pb (by omega) (by omega)
    [(7559,7,11,13),(7561,6,47,67),(7573,12,17,31),(7577,4,7,11),(7583,7,13,19),(7589,4,7,31),(7591,3,5,13),(7603,3,5,13),(7607,4,7,11)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_119 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=119) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=7616) small pb (by omega) (by omega)
    [(7621,32,37,47),(7639,3,5,13),(7643,2,23,43),(7649,4,7,31),(7669,14,23,107),(7673,9,11,41)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_120 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=120) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=7680) small pb (by omega) (by omega)
    [(7681,16,19,59),(7687,3,5,13),(7691,7,13,19),(7699,3,5,13),(7703,3,5,23),(7717,13,23,29),(7723,3,5,13),(7727,4,7,11),(7741,12,17,59)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_121 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=121) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=7744) small pb (by omega) (by omega)
    [(7753,9,11,41),(7757,4,7,11),(7759,3,5,13),(7789,1,53,79),(7793,9,11,41)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_122 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=122) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=7808) small pb (by omega) (by omega)
    [(7817,4,7,11),(7823,12,29,31),(7829,13,19,29),(7841,4,7,61),(7853,12,17,31),(7867,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_123 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=123) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=7872) small pb (by omega) (by omega)
    [(7873,9,11,41),(7877,4,7,11),(7879,3,5,13),(7883,3,5,59),(7901,3,23,43),(7907,4,7,11),(7919,7,11,13),(7927,3,5,13),(7933,12,17,31)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_124 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=124) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=7936) small pb (by omega) (by omega)
    [(7937,4,7,11),(7949,17,19,23),(7951,3,5,13),(7963,3,5,13),(7993,9,11,41)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_125 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=125) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=8000) small pb (by omega) (by omega)
    [(8009,4,7,31),(8011,3,5,13),(8017,4,11,19),(8039,7,11,13),(8053,12,17,31),(8059,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_126 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=126) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=8064) small pb (by omega) (by omega)
    [(8069,7,11,19),(8081,13,19,29),(8087,4,7,11),(8089,4,19,31),(8093,12,17,31),(8101,12,17,67),(8111,3,5,43),(8117,4,7,11),(8123,7,13,19)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_127 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=127) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=8128) small pb (by omega) (by omega)
    [(8147,4,7,11),(8161,7,59,67),(8167,3,5,13),(8171,30,47,53),(8179,3,5,13),(8191,3,5,13)]
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
private theorem thirteenth_block_128 {b : ℕ} (small : b≤8193) (pb : b.Prime) (index : b/64=128) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  apply thirteenth_small_block (start:=8192) small pb (by omega) (by omega)
    []
  · decide +kernel
  · decide +kernel

set_option maxHeartbeats 1000000 in
private theorem thirteenth_small {b : ℕ} (small : b≤8193) (pb : b.Prime) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^13+d ∧ s ∣ (2^b-1)^13+d := by
  have bound : b/64≤128 := by omega
  interval_cases h : b/64
  · exact thirteenth_block_0 small pb h
  · exact thirteenth_block_1 small pb h
  · exact thirteenth_block_2 small pb h
  · exact thirteenth_block_3 small pb h
  · exact thirteenth_block_4 small pb h
  · exact thirteenth_block_5 small pb h
  · exact thirteenth_block_6 small pb h
  · exact thirteenth_block_7 small pb h
  · exact thirteenth_block_8 small pb h
  · exact thirteenth_block_9 small pb h
  · exact thirteenth_block_10 small pb h
  · exact thirteenth_block_11 small pb h
  · exact thirteenth_block_12 small pb h
  · exact thirteenth_block_13 small pb h
  · exact thirteenth_block_14 small pb h
  · exact thirteenth_block_15 small pb h
  · exact thirteenth_block_16 small pb h
  · exact thirteenth_block_17 small pb h
  · exact thirteenth_block_18 small pb h
  · exact thirteenth_block_19 small pb h
  · exact thirteenth_block_20 small pb h
  · exact thirteenth_block_21 small pb h
  · exact thirteenth_block_22 small pb h
  · exact thirteenth_block_23 small pb h
  · exact thirteenth_block_24 small pb h
  · exact thirteenth_block_25 small pb h
  · exact thirteenth_block_26 small pb h
  · exact thirteenth_block_27 small pb h
  · exact thirteenth_block_28 small pb h
  · exact thirteenth_block_29 small pb h
  · exact thirteenth_block_30 small pb h
  · exact thirteenth_block_31 small pb h
  · exact thirteenth_block_32 small pb h
  · exact thirteenth_block_33 small pb h
  · exact thirteenth_block_34 small pb h
  · exact thirteenth_block_35 small pb h
  · exact thirteenth_block_36 small pb h
  · exact thirteenth_block_37 small pb h
  · exact thirteenth_block_38 small pb h
  · exact thirteenth_block_39 small pb h
  · exact thirteenth_block_40 small pb h
  · exact thirteenth_block_41 small pb h
  · exact thirteenth_block_42 small pb h
  · exact thirteenth_block_43 small pb h
  · exact thirteenth_block_44 small pb h
  · exact thirteenth_block_45 small pb h
  · exact thirteenth_block_46 small pb h
  · exact thirteenth_block_47 small pb h
  · exact thirteenth_block_48 small pb h
  · exact thirteenth_block_49 small pb h
  · exact thirteenth_block_50 small pb h
  · exact thirteenth_block_51 small pb h
  · exact thirteenth_block_52 small pb h
  · exact thirteenth_block_53 small pb h
  · exact thirteenth_block_54 small pb h
  · exact thirteenth_block_55 small pb h
  · exact thirteenth_block_56 small pb h
  · exact thirteenth_block_57 small pb h
  · exact thirteenth_block_58 small pb h
  · exact thirteenth_block_59 small pb h
  · exact thirteenth_block_60 small pb h
  · exact thirteenth_block_61 small pb h
  · exact thirteenth_block_62 small pb h
  · exact thirteenth_block_63 small pb h
  · exact thirteenth_block_64 small pb h
  · exact thirteenth_block_65 small pb h
  · exact thirteenth_block_66 small pb h
  · exact thirteenth_block_67 small pb h
  · exact thirteenth_block_68 small pb h
  · exact thirteenth_block_69 small pb h
  · exact thirteenth_block_70 small pb h
  · exact thirteenth_block_71 small pb h
  · exact thirteenth_block_72 small pb h
  · exact thirteenth_block_73 small pb h
  · exact thirteenth_block_74 small pb h
  · exact thirteenth_block_75 small pb h
  · exact thirteenth_block_76 small pb h
  · exact thirteenth_block_77 small pb h
  · exact thirteenth_block_78 small pb h
  · exact thirteenth_block_79 small pb h
  · exact thirteenth_block_80 small pb h
  · exact thirteenth_block_81 small pb h
  · exact thirteenth_block_82 small pb h
  · exact thirteenth_block_83 small pb h
  · exact thirteenth_block_84 small pb h
  · exact thirteenth_block_85 small pb h
  · exact thirteenth_block_86 small pb h
  · exact thirteenth_block_87 small pb h
  · exact thirteenth_block_88 small pb h
  · exact thirteenth_block_89 small pb h
  · exact thirteenth_block_90 small pb h
  · exact thirteenth_block_91 small pb h
  · exact thirteenth_block_92 small pb h
  · exact thirteenth_block_93 small pb h
  · exact thirteenth_block_94 small pb h
  · exact thirteenth_block_95 small pb h
  · exact thirteenth_block_96 small pb h
  · exact thirteenth_block_97 small pb h
  · exact thirteenth_block_98 small pb h
  · exact thirteenth_block_99 small pb h
  · exact thirteenth_block_100 small pb h
  · exact thirteenth_block_101 small pb h
  · exact thirteenth_block_102 small pb h
  · exact thirteenth_block_103 small pb h
  · exact thirteenth_block_104 small pb h
  · exact thirteenth_block_105 small pb h
  · exact thirteenth_block_106 small pb h
  · exact thirteenth_block_107 small pb h
  · exact thirteenth_block_108 small pb h
  · exact thirteenth_block_109 small pb h
  · exact thirteenth_block_110 small pb h
  · exact thirteenth_block_111 small pb h
  · exact thirteenth_block_112 small pb h
  · exact thirteenth_block_113 small pb h
  · exact thirteenth_block_114 small pb h
  · exact thirteenth_block_115 small pb h
  · exact thirteenth_block_116 small pb h
  · exact thirteenth_block_117 small pb h
  · exact thirteenth_block_118 small pb h
  · exact thirteenth_block_119 small pb h
  · exact thirteenth_block_120 small pb h
  · exact thirteenth_block_121 small pb h
  · exact thirteenth_block_122 small pb h
  · exact thirteenth_block_123 small pb h
  · exact thirteenth_block_124 small pb h
  · exact thirteenth_block_125 small pb h
  · exact thirteenth_block_126 small pb h
  · exact thirteenth_block_127 small pb h
  · exact thirteenth_block_128 small pb h

-- BEGIN THIRTEEN
private theorem thirteen_index_check {α β : Type*} {L : ℕ}
    (a : List α) (b : List β) (x : α → ℕ) (y : β → ℕ)
    (ok : (List.range L).all (fun k =>
      !decide (k.Coprime L) || (a.any (fun z => x z == k) || b.any (fun z => y z == k))) = true) :
    ∀ k ∈ List.range L, k.Coprime L → (∃ z ∈ a, x z = k) ∨ ∃ z ∈ b, y z = k := by
  intro k hk hc
  simpa [hc, List.any_eq_true] using List.all_eq_true.mp ok k hk

private theorem thirteen_prime_check {α : Type*} (a : List α) (x : α → ℕ) (tiny : List ℕ)
    (ok : (List.range 631).all (fun i =>
      let n := 13*i+1
      decide (n < 2) || (tiny.any (fun d => decide (1 < d ∧ d < n ∧ n % d = 0))
        || a.any (fun z => x z == n))) = true) :
    ∀ i ∈ List.range 631, (13*i+1).Prime → ∃ z ∈ a, x z = 13*i+1 := by
  intro i hi pri
  have cases : 13*i+1 < 2 ∨ (∃ d ∈ tiny, 1 < d ∧ d < 13*i+1 ∧ (13*i+1) % d = 0)
      ∨ (∃ z ∈ a, x z = 13*i+1) := by
    simpa [List.any_eq_true] using List.all_eq_true.mp ok i hi
  rcases cases with low | ⟨d, _, dl, du, dv⟩ | found
  · have := pri.two_le
    omega
  · have := (Nat.dvd_prime pri).mp (Nat.dvd_iff_mod_eq_zero.mpr dv)
    omega
  · exact found

private theorem thirteen_row_check {α β : Type*} (a : List α) (b : List β)
    (p q : α → β → Prop) [∀ r, DecidablePred (p r)] [∀ r, DecidablePred (q r)]
    (ok : a.all (fun r => b.all (fun t => !decide (p r t) || decide (q r t))) = true) :
    ∀ r ∈ a, ∀ t ∈ b, p r t → q r t := by
  intro r hr t ht hp
  simpa [hp] using List.all_eq_true.mp (List.all_eq_true.mp ok r hr) t ht

private theorem thirteen_order {q p : ℕ} (pq : q.Prime) (q2 : q≠2)
    (d : q ∣ p^13+8192) (nd : ¬q ∣ p+2) : 13 ∣ q-1 := by
  let _ : Fact q.Prime := ⟨pq⟩
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro h
    have eq := (Nat.prime_dvd_prime_iff_eq pq Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 q).mp h)
    exact q2 eq
  let t : ZMod q := -(p:ZMod q)/2
  have zero := (ZMod.natCast_eq_zero_iff _ _).mpr d
  push_cast at zero
  have eq : t^13=1 := by
    dsimp [t]
    rw [div_pow,div_eq_iff (pow_ne_zero _ h2)]
    linear_combination -zero
  have t1 : t≠1 := by
    intro h
    dsimp [t] at h
    rw [div_eq_iff h2] at h
    apply nd
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    linear_combination -h
  have t0 : t≠0 := by rintro h; rw [h] at eq; simp at eq
  have ord : orderOf t = 13 := ((Nat.dvd_prime (by decide : Nat.Prime 13)).mp
    (orderOf_dvd_of_pow_eq_one eq)).resolve_left (fun h => t1 (orderOf_eq_one_iff.mp h))
  exact ord ▸ ZMod.orderOf_dvd_card_sub_one t0


private theorem thirteen_legendre (m n : ℕ) [Fact m.Prime] (hm : 2 < m) :
    legendreSym m (n:ℤ) = if n%m=0 then 0 else if ((n%m)^(m/2))%m=1 then 1 else -1 := by
  have cast : ((n:ℤ):ZMod m)=(n:ZMod m) := by simp
  by_cases z : n%m=0
  · rw [if_pos z,legendreSym.eq_zero_iff,cast,ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero z
  rw [if_neg z]
  have nz : ((n:ℤ):ZMod m)≠0 := by
    intro h
    rw [cast] at h
    exact z (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff n m).mp h))
  have power : ((n%m)^(m/2))%m=1 ↔ (n:ZMod m)^(m/2)=1 := by
    have eq := ZMod.natCast_eq_natCast_iff' ((n%m)^(m/2)) 1 m
    rw [Nat.mod_eq_of_lt (by omega : 1 < m)] at eq
    simpa only [Nat.cast_pow,ZMod.natCast_mod,Nat.cast_one] using eq.symm
  have sign := legendreSym.eq_pow m (n:ℤ)
  rw [cast] at sign
  rcases legendreSym.eq_one_or_neg_one m nz with h|h
  · rw [h,Int.cast_one] at sign
    rw [h,if_pos (power.mpr sign.symm)]
  · rw [h,Int.cast_neg,Int.cast_one] at sign
    rw [h,if_neg]
    intro bad
    have eq : (-1:ZMod m)=1 := sign.trans (power.mp bad)
    have zero : ((2:ℕ):ZMod m)=0 := by push_cast; linear_combination -eq
    have dd := (ZMod.natCast_eq_zero_iff _ _).mp zero
    have le := Nat.le_of_dvd (by decide) dd
    omega

private theorem thirteen_character_mul (m : ℕ) (ok : m=4 ∨ m=8 ∨ (m.Prime ∧ 2 < m)) :
    let char (n : ℕ) : ℤ := if m=4 then (if n%2=0 then 0 else if n%4=1 then 1 else -1)
    else if m=8 then (if n%2=0 then 0 else if n%8=1 ∨ n%8=7 then 1 else -1)
    else if n%m=0 then 0 else if ((n%m)^(m/2))%m=1 then 1 else -1
    ∀ u v, char (u*v)=char u*char v := by
  dsimp only
  rcases ok with rfl|rfl|⟨pm,hm⟩
  · intro u v
    simp only [if_true]
    simpa only [ZMod.χ₄_nat_eq_if_mod_four] using
      (show ZMod.χ₄ ((u*v:ℕ):ZMod 4)=ZMod.χ₄ (u:ZMod 4)*ZMod.χ₄ (v:ZMod 4) by rw [Nat.cast_mul,map_mul])
  · intro u v
    simp only [show (8:ℕ)≠4 by decide,if_false,if_true]
    simpa only [ZMod.χ₈_nat_eq_if_mod_eight] using
      (show ZMod.χ₈ ((u*v:ℕ):ZMod 8)=ZMod.χ₈ (u:ZMod 8)*ZMod.χ₈ (v:ZMod 8) by rw [Nat.cast_mul,map_mul])
  · intro u v
    let _ : Fact m.Prime := ⟨pm⟩
    have n4 : m≠4 := by rintro rfl; norm_num at pm
    have n8 : m≠8 := by rintro rfl; norm_num at pm
    simp only [n4,n8,if_false,←thirteen_legendre m _ hm,Nat.cast_mul,legendreSym.mul]

set_option maxRecDepth 32768 in
set_option synthInstance.maxSize 512 in
set_option maxHeartbeats 20000000 in
/-- Every thirteenth power with Mersenne index greater than 8193 has a two-prime witness. -/
theorem mersenne_thirteen_large_witness {p b : ℕ} (pp : p.Prime) (base : p+1=2^b)
    (hb : 8193 < b) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
    q ∣ p^13+d ∧ s ∣ p^13+d := by
  by_contra missing
  have ep : p=2^b-1 := by omega
  have pb : b.Prime := (Nat.prime_of_pow_sub_one_prime (by omega) (ep ▸ pp)).2
  let x := p-2
  have xp : p=x+2 := by dsimp [x]; have := pp.two_le; omega
  have bx : x+3=2^b := by omega
  let F (y : ℕ) := ((((((((((((1*y+22)*y+224)*y+1392)*y+5872)*y+17696)*y+39040)*y+63488)*y+75520)*y+64000)*y+36864)*y+12288)*y+4096)
  have fc {m i j : ℕ} (h : Nat.ModEq m i j) : Nat.ModEq m (F i) (F j) := (((((((((((((((((((((((((Nat.ModEq.refl 1).mul h).add_right 22).mul h).add_right 224).mul h).add_right 1392).mul h).add_right 5872).mul h).add_right 17696).mul h).add_right 39040).mul h).add_right 63488).mul h).add_right 75520).mul h).add_right 64000).mul h).add_right 36864).mul h).add_right 12288).mul h).add_right 4096)
  have fac : p^13+8192=(p+2)*F x := by rw [xp]; dsimp [F]; ring
  have d8 : 8 ∣ 2^b := pow_dvd_pow (2:ℕ) (show 3≤b by omega)
  have xm : Nat.ModEq 8 x 5 := by change x%8=5; omega
  have f8 : F x%8=7 := (fc xm).trans (by decide +kernel : Nat.ModEq 8 (F 5) 7)
  obtain ⟨q,pq,hq,dq⟩ := mersenne_left_factor pb (show 8193 < b by omega) (by omega)
  have dl : q ∣ p+2 := by convert dq using 1; omega
  have common {s : ℕ} (d1 : s ∣ p+2) (d2 : s ∣ F x) : s ∣ 53248 := by
    have ident : F x+12288*(p+2)=53248+(p+2)*(6144*x^1+7680*x^2+14080*x^3+15360*x^4+12032*x^5+6752*x^6+2736*x^7+784*x^8+152*x^9+18*x^10+1*x^11) := by rw [xp]; dsimp [F]; ring
    have both := dvd_add d2 (dvd_mul_of_dvd_right d1 12288)
    rw [ident] at both
    exact (Nat.dvd_add_iff_left (dvd_mul_of_dvd_left d1 _)).mpr both
  have only (s : ℕ) (ps : s.Prime) (ds : s ∣ F x) : s ≤ 8193 := by
    by_contra! high
    have diff : q≠s := by
      rintro rfl
      have mem := pq.mem_primeFactors (common dl ds) (by decide)
      have tab : (53248:ℕ).primeFactors={2,13} := by decide +kernel
      rw [tab] at mem; simp only [Finset.mem_insert,Finset.mem_singleton] at mem; omega
    exact missing ⟨8192,q,s,pq,ps,diff,hq,high,fac ▸ dvd_mul_of_dvd_left dl _,fac ▸ dvd_mul_of_dvd_right ds _⟩
  let catalog : List (ℕ × ℕ × List ℕ × ℕ × List ℕ) := [(53,52,[7,9,11,27,37],10,[26,11,24,12,9,39,34,16,18,27,20,37,7]),
    (79,39,[2,14,19,22,31],8,[39,6,14,2,31,39,22,19,39,12,13,9,39]),
    (131,130,[3,33,41,73,81,87],39,[65,87,33,62,90,39,98,73,64,3,74,41,81]),
    (157,52,[3],14,[26,20,52,3,8,52,52,39,52,52,52,52,52]),
    (313,156,[73,121],27,[78,156,14,156,156,156,121,156,156,75,73,156,27]),
    (443,442,[9,7,11,15,25,19],35,[221,230,260,61,409,226,275,219,378,386,148,337,137]),
    (521,260,[227],18,[130,260,260,240,260,117,260,260,110,260,150,227,124]),
    (547,546,[55,35,17,1,43],46,[273,116,497,235,287,113,55,355,504,506,488,173,324]),
    (599,299,[7,10,12],19,[299,299,72,88,299,161,299,299,299,299,114,299,142]),
    (677,676,[33,7,43],40,[338,68,189,238,38,508,420,371,325,667,22,481,244]),
    (859,858,[17,7,49],100,[429,12,346,182,638,78,616,753,673,251,553,658,543]),
    (911,91,[2],30,[91,91,91,91,91,91,91,91,91,91,80,91,91]),
    (937,117,[],36,[117,117,117,117,117,117,117,117,117,117,117,117,117]),
    (1093,364,[35,45],11,[182,364,364,364,364,206,243,364,364,364,305,195,324]),
    (1171,1170,[187,257,1,79,137],86,[585,627,469,633,147,391,527,187,38,651,257,82,242]),
    (1223,611,[2,12,8,3,9],117,[611,611,611,325,611,510,611,611,106,581,294,377,142]),
    (1249,156,[],68,[78,156,156,141,156,156,156,156,156,156,156,156,156]),
    (1301,1300,[249,3,251],78,[650,1291,996,515,784,762,249,1005,914,292,783,842,364]),
    (1327,221,[5,6],257,[221,221,221,221,221,221,221,221,221,221,221,214,213]),
    (1483,1482,[31,61,23,55],132,[741,959,187,350,604,400,356,838,936,1381,516,919,582]),
    (1613,52,[],16,[26,52,52,46,52,52,52,52,52,52,52,6,52]),
    (1847,923,[4,7,10,11],123,[923,442,923,923,7,923,108,923,923,310,65,101,4]),
    (1873,936,[35,61],96,[468,916,936,936,936,936,685,347,936,129,936,936,936]),
    (1951,975,[137,181,136],113,[975,975,975,975,975,137,376,975,526,80,975,910,975]),
    (2003,286,[],22,[143,286,286,286,286,286,286,121,165,286,286,286,286]),
    (2029,2028,[55,97,137],56,[1014,597,886,1006,1474,1292,1612,409,951,367,372,1073,1261]),
    (2081,1040,[211,63],104,[520,1040,430,1040,471,285,84,1040,560,1040,1040,843,180]),
    (2237,2236,[15,27,51,3,31],47,[1118,79,586,1492,1308,2215,43,675,1510,1726,67,235,783]),
    (2341,780,[269],65,[390,261,780,357,468,780,369,780,780,780,780,269,780]),
    (2393,598,[19],135,[299,598,194,598,598,598,598,19,598,598,598,598,598]),
    (2549,2548,[11,23,7],325,[1274,1939,2347,1800,2278,780,1011,8,352,424,2142,271,923]),
    (2731,26,[1,25],4,[13,26,26,26,26,26,1,26,26,26,26,26,25]),
    (2861,2860,[129,7,171],559,[1430,248,1469,2358,630,496,995,1047,366,1211,909,1226,1736]),
    (2887,1443,[7,10,14,37,1],233,[1443,319,586,1443,1119,1443,1443,443,400,1443,505,1401,622]),
    (2939,2938,[7,17,23,3,9],176,[1469,1491,1365,345,1884,953,1245,68,1355,2646,195,2550,1282]),
    (3121,156,[],20,[78,58,156,156,156,156,156,156,156,156,156,156,156]),
    (3251,650,[83],93,[325,650,464,650,650,426,246,650,650,650,213,650,650]),
    (3329,1664,[25],102,[832,266,1664,1664,1664,1664,1664,337,1558,1498,1664,580,1052]),
    (3407,1703,[10,2,1],713,[1703,1417,1479,1703,1250,1703,88,288,729,1703,626,1703,1703]),
    (3433,1716,[73,1,149],6,[858,894,1694,1716,1716,242,1553,1165,1249,1716,324,1570,1190]),
    (3511,1755,[152,23],88,[1755,294,1098,1388,1430,1755,1755,1365,1755,1755,208,1299,542]),
    (3719,1859,[10,1,9],200,[1859,361,1859,1859,1859,378,1859,1569,1859,1101,1859,1534,1859]),
    (3797,3796,[33,17,23,5,9],347,[1898,208,1162,2122,1461,381,2762,293,1280,2557,2484,1167,2934]),
    (3823,637,[],93,[637,637,637,104,637,637,637,637,637,637,637,637,637]),
    (4057,169,[2,4,11],78,[169,95,2,169,169,169,169,169,169,115,169,169,169]),
    (4421,340,[9,11],616,[170,340,340,340,29,340,251,314,340,116,340,340,340]),
    (4447,2223,[11,4,7],732,[2223,979,2223,1746,1908,206,2223,1060,2223,2223,2223,1851,2223]),
    (4603,4602,[19,23,53,47],571,[2301,2783,1350,460,606,1358,4370,2972,643,4181,2786,752,647]),
    (4733,364,[49],295,[182,364,364,364,364,364,361,364,364,364,364,158,364]),
    (4759,793,[3],44,[793,793,393,793,793,793,793,793,793,793,793,793,793]),
    (4889,2444,[27],217,[1222,2444,2093,858,2444,2444,2444,443,1402,2444,366,2444,2444]),
    (4967,2483,[12,1,9,8],307,[2483,2483,2483,2483,2483,2023,2483,685,2483,129,2483,1067,352]),
    (4993,624,[67],492,[312,624,624,624,624,624,624,624,67,624,624,624,624]),
    (5227,5226,[11,41,31,71],25,[2613,3411,1747,869,2723,3921,1203,1440,1133,10,980,2763,2119]),
    (5279,377,[12,11],67,[377,377,377,377,377,377,155,377,377,180,377,377,377]),
    (5591,2795,[21,23,54,53,19],208,[2795,281,868,1549,2795,2795,2684,2670,2795,2393,2795,2795,2795]),
    (5669,436,[3,1],817,[218,436,436,343,436,436,436,436,436,436,425,436,436]),
    (5851,5850,[271,77,199,239],66,[2925,755,3679,1852,5309,3638,4171,470,4367,4489,3854,4228,906]),
    (5903,2951,[3,1,8,7],590,[2951,2951,783,2951,2951,1444,2951,2951,2951,1866,2951,2951,1724]),
    (5981,460,[],227,[230,460,460,460,460,460,460,460,85,460,460,460,460]),
    (6007,1001,[12],454,[1001,1001,1001,1001,1001,1001,1001,1001,1001,974,1001,1001,1001]),
    (6163,2054,[3,5],250,[1027,2054,2054,2054,2054,887,2054,1331,2054,2054,1676,2054,2054]),
    (6397,6396,[79,61,41],224,[3198,1617,5365,387,360,1251,3744,4112,2961,2282,2731,4974,6281]),
    (6449,806,[],139,[403,806,806,806,806,806,806,806,588,806,806,598,806]),
    (6553,117,[],24,[117,117,117,117,117,117,117,117,117,117,117,117,117]),
    (6709,6708,[47,107,31],747,[3354,1827,2812,5959,6565,1199,671,4601,6573,3104,2469,5068,4244]),
    (6761,1690,[113],119,[845,1690,1690,1690,1690,1690,893,1690,1690,1690,1690,1690,1690]),
    (6917,6916,[25,33,49],40,[3458,428,701,5789,3342,1146,1470,5717,3408,2564,448,1687,1021]),
    (7151,325,[],185,[325,325,325,325,325,325,325,325,325,325,325,325,325]),
    (7177,3588,[73,83],368,[1794,3588,3588,3588,3588,3588,1321,3588,345,3588,2891,310,3588]),
    (7229,7228,[19,29,31,3],320,[3614,4360,539,5437,5905,1381,3714,1580,4694,5678,1903,1166,4215]),
    (7307,7306,[1,5,15,23,21],196,[3653,3895,5200,920,2662,690,847,3534,681,34,469,2690,3637]),
    (7333,2444,[11],27,[1222,1623,2444,1450,2444,2030,2444,2444,858,2444,2444,1244,1166]),
    (7411,7410,[367,223,287],176,[3705,7018,7307,5683,464,4954,6639,4985,4267,6552,3000,3938,1150]),
    (7489,468,[],841,[234,468,468,468,468,468,468,468,468,468,468,468,468]),
    (7541,7540,[47,3,87,23,253,137],501,[3770,7417,6493,5494,3663,3048,7000,2083,5935,1760,47,3467,4658]),
    (7723,2574,[53],1144,[1287,1437,2574,2574,2574,2574,2574,1262,871,2574,770,2574,365]),
    (7853,7852,[43,33,3,9,11],1709,[3926,3575,563,4059,6306,3257,2124,5261,5919,4336,2460,4870,7187]),
    (7879,3939,[2],635,[3939,2873,3852,3939,1125,2537,3939,3939,3939,3094,3939,3939,3939]),
    (8009,4004,[7,25,31],753,[2002,631,4004,1851,2737,4004,4004,1585,1494,4004,4004,4004,1188]),
    (8087,4043,[6,8,11],618,[4043,1891,1971,4043,4041,4043,4043,4043,2990,4043,4043,4043,4043]),
    (8191,13,[12],2,[13,13,13,13,13,13,13,13,13,13,13,12,13])]
  let direct : List (ℕ × ℕ × ℕ × ℕ) := [(7,3,5,13),
    (17,4,7,11),
    (19,3,5,13),
    (23,3,5,61),
    (29,4,7,31),
    (31,3,5,13),
    (41,4,7,61),
    (43,3,5,13),
    (47,4,7,11),
    (49,23,53,79),
    (53,9,11,41),
    (59,7,11,13),
    (67,3,5,13),
    (71,1,53,157),
    (73,9,11,41),
    (77,4,7,11),
    (79,3,5,13),
    (83,3,5,61),
    (89,4,7,31),
    (97,55,61,79),
    (101,4,7,61),
    (103,3,5,13),
    (107,4,7,11),
    (113,9,11,41),
    (119,7,11,13),
    (127,3,5,13),
    (133,9,11,41),
    (137,4,7,11),
    (139,3,5,13),
    (149,4,7,31),
    (151,3,5,13),
    (161,4,7,61),
    (163,3,5,13),
    (167,4,7,11),
    (173,9,11,41),
    (179,7,11,13),
    (187,3,5,13),
    (193,9,11,41),
    (197,4,7,11),
    (199,3,5,13),
    (203,3,5,61),
    (209,4,7,31),
    (211,3,5,13),
    (217,55,61,79),
    (223,3,5,13),
    (227,4,7,11),
    (233,9,11,41),
    (239,7,11,13),
    (241,23,53,79),
    (253,9,11,41),
    (257,4,7,11),
    (259,3,5,13),
    (263,3,5,61),
    (269,4,7,31),
    (271,3,5,13),
    (277,1,79,131),
    (281,4,7,61),
    (283,3,5,13),
    (287,4,7,11),
    (289,58,131,151),
    (293,9,11,41),
    (301,1,53,79),
    (307,3,5,13),
    (311,23,53,79),
    (313,9,11,41),
    (317,4,7,11),
    (319,3,5,13),
    (323,3,5,61),
    (329,4,7,31),
    (331,3,5,13),
    (341,4,7,61),
    (343,3,5,13),
    (347,4,7,11),
    (353,9,11,41),
    (359,7,11,13),
    (361,23,53,79),
    (367,3,5,13),
    (373,9,11,41),
    (379,3,5,13),
    (383,3,5,61),
    (389,4,7,31),
    (391,3,5,13),
    (397,23,53,79),
    (401,4,7,61),
    (407,4,7,11),
    (413,9,11,41),
    (419,7,11,13),
    (427,3,5,13),
    (433,9,11,41),
    (437,4,7,11),
    (439,3,5,13),
    (443,3,5,61),
    (449,4,7,31),
    (451,3,5,13),
    (457,1,53,79),
    (461,4,7,61),
    (463,3,5,13),
    (467,4,7,11),
    (473,9,11,41),
    (479,7,11,13),
    (487,3,5,13),
    (491,1,79,131),
    (493,9,11,41),
    (497,4,7,11),
    (499,3,5,13),
    (503,3,5,61),
    (509,4,7,31),
    (511,3,5,13),
    (517,23,53,79),
    (521,4,7,61),
    (523,3,5,13),
    (527,4,7,11),
    (539,7,11,13),
    (547,3,5,13),
    (553,9,11,41),
    (557,4,7,11),
    (563,3,5,61),
    (569,4,7,31),
    (571,3,5,13),
    (577,55,61,79),
    (581,4,7,61),
    (583,3,5,13),
    (587,4,7,11),
    (593,9,11,41),
    (599,7,11,13),
    (607,3,5,13),
    (613,9,11,41),
    (617,4,7,11),
    (619,3,5,13),
    (623,3,5,61),
    (629,4,7,31),
    (631,3,5,13),
    (641,4,7,61),
    (643,3,5,13),
    (647,4,7,11),
    (653,9,11,41),
    (659,7,11,13),
    (667,3,5,13),
    (673,9,11,41),
    (677,4,7,11),
    (679,3,5,13),
    (683,3,5,61),
    (691,3,5,13),
    (701,4,7,61),
    (703,3,5,13),
    (707,4,7,11),
    (709,23,53,79),
    (713,9,11,41),
    (719,7,11,13),
    (727,3,5,13),
    (733,9,11,41),
    (737,4,7,11),
    (739,3,5,13),
    (743,3,5,61),
    (749,4,7,31),
    (751,3,5,13),
    (757,24,41,79),
    (761,4,7,61),
    (763,3,5,13),
    (769,1,53,79),
    (773,9,11,41),
    (779,7,11,13)]
  let hard : List (ℕ × List ℕ × List ℕ) := [(1,[547,1171,2731,2887,3407,3433,3719,4967,5669,5903,7307],[4,8,3,5,7,31,41,53,61,131]),
    (11,[53,443,1847,2549,4057,4421,4447,5227,5279,5669,7333,7853,8087],[4,3,5,11,31,41,61,151]),
    (37,[53,443,1847,2887,4057,5279,5669,8087],[8,3,11]),
    (61,[53,79,443,1223,1483,1873,2939,3719,3797,4967,5669,6397,7853],[4,8,31,61,151,331]),
    (109,[79,1327,1483,3797,4421,5227,5669,6163,7307],[4,8,11,41,131]),
    (121,[313,547,1847,2939,3797,4057,4447,5669],[4,8,3,7,11,41]),
    (131,[53,79,2237,2731,2887,3407,3719,4421,4603,4889,4967,5669,5903,7307,7723],[4,11,31,41,61,131,313]),
    (157,[547,2731,2887,3407,3433,3719,4967,5669,5903,7307],[4,8,3,5,7,31,41,53,61,131]),
    (181,[443,599,1223,1951,2731,3329,4967,5279,5669,6007,6917,8009,8191],[41,61,151,313]),
    (191,[443,547,1093,1223,1873,2939,3719,4421,4967,5669],[8,61,79]),
    (229,[313,1223,3433,4421,4967,5669,5903,7177,7307,8087],[8,3,5,7,11,31,53,79]),
    (251,[547,677,859,1301,1847,2939,4057,4421,5669,7853],[3,5,11,41,61]),
    (337,[443,599,1223,2731,3329,4967,5279,5669,6007,6917,8009,8191],[4,8,3,11,41,53]),
    (349,[53,443,1847,2887,4057,4421,5279,5669,8087],[8,31,131]),
    (371,[53,443,599,677,1847,2549,2939,4421,5669,5903,8009],[8,3,5,7,11,31,61,313]),
    (409,[79,443,1093,1327,2029,2393,4421,4603,5591,5669,8087],[4,3,5,11,53,61]),
    (421,[79,1327,1483,3797,5227,5669,6163,7307],[4,31,53,61]),
    (431,[79,131,443,911,1223,2237,2861,3407,4057,4421,5227,5669,7307,7879],[4,8,3,157]),
    (469,[547,1171,2731,2887,3407,3433,3719,4421,4967,5669,5903,7307],[3,5,7,11,41,61,79]),
    (529,[53,79,443,1223,1483,1873,2939,3719,3797,4421,4967,5669,6397,7853],[4,8,31,61,151,331]),
    (541,[313,1223,3433,4967,5591,5669,5903,7177,7307,8087],[4,8,3,5,53,61,131,151]),
    (551,[1327,2237,4421,5669,6163,7177,7229,7307,8009],[8,3,7,31]),
    (589,[313,547,1847,2939,3797,4057,4421,4447,5669,5851],[4,5,7,79]),
    (601,[131,547,1223,1483,2939,4759,5669,5903,6163,7229],[3,151]),
    (649,[443,599,1223,2731,2861,3329,4421,4967,5279,5669,6007,6917,8009,8191],[41,61,151,313]),
    (661,[53,443,1847,2887,4057,5279,5669,5851,8087],[4,3,41]),
    (671,[1223,4421,4603,4967,5591,5669,5903,6709,7307,8087],[3,5,7,11,31,53,131]),
    (697,[313,1223,3433,4967,5669,5903,7177,7307,8087],[8,3,11]),
    (721,[79,443,1093,1327,1951,2029,2393,4603,5669,8087],[8,7,11,31,53,61]),
    (731,[131,157,1223,2081,2237,2939,4421,4759,5669,5903,6163,6709,7229,7853],[3,5,7,11,31,41,61,151,1321])]
  let char (m n : ℕ) : ℤ := if m=4 then (if n%2=0 then 0 else if n%4=1 then 1 else -1)
    else if m=8 then (if n%2=0 then 0 else if n%8=1 ∨ n%8=7 then 1 else -1)
    else if n%m=0 then 0 else if ((n%m)^(m/2))%m=1 then 1 else -1
  have co (o : ℕ) (ho : 0 < o) (ob : o < b) : (b%o).Coprime o := by
    have h := pb.coprime_iff_not_dvd.mpr (show ¬b ∣ o by intro d; have := Nat.le_of_dvd ho d; omega)
    change Nat.gcd (b%o) o=1
    rw [←Nat.gcd_rec o b,Nat.gcd_comm]
    exact h
  have idx : ∀ k ∈ List.range 780, k.Coprime 780 →
      (∃ row ∈ direct,row.1=k) ∨ (∃ row ∈ hard,row.1=k) :=
    thirteen_index_check direct hard Prod.fst Prod.fst (by decide +kernel)
  rcases idx _ (List.mem_range.mpr (Nat.mod_lt b (by decide))) (co 780 (by decide) (by omega)) with h|⟨row,hr,rb⟩
  · obtain ⟨⟨k,d,q₁,q₂⟩,mem,ek⟩ := h
    change k=b%780 at ek
    have good : ∀ z ∈ direct, z.2.2.1.Prime ∧ z.2.2.2.Prime ∧ z.2.2.1≠z.2.2.2 ∧
        z.2.1+1<z.2.2.1 ∧ z.2.1+1<z.2.2.2 ∧ ∀ m ∈ [z.2.2.1,z.2.2.2],
        2^780%m=1 ∧ (((2^z.1-1)%m)^13+z.2.1)%m=0 := by decide +kernel
    obtain ⟨p₁,p₂,ne,b₁,b₂,rest⟩ := good _ mem
    have div {m : ℕ} (pr : m.Prime) (dm : m ∈ [q₁,q₂]) : m ∣ p^13+d := by
      obtain ⟨per,hit⟩ := rest m dm
      have red := eleven_period (b:=b) (show Nat.ModEq m (2^780) 1 by
        change 2^780%m=1%m; rw [Nat.mod_eq_of_lt pr.one_lt]; exact per)
      have pm : Nat.ModEq m p ((2^k-1)%m) := by
        apply Nat.ModEq.trans _ (Nat.mod_modEq _ _).symm
        apply Nat.ModEq.add_right_cancel' 1
        rw [base,Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide : 0<2)),ek]; exact red
      exact Nat.dvd_iff_mod_eq_zero.mpr (Eq.trans ((pm.pow 13).add_right d) hit)
    exact missing ⟨d,q₁,q₂,p₁,p₂,ne,b₁,b₂,div p₁ (by simp),div p₂ (by simp)⟩
  change row.1=b%780 at rb
  have sup (s : ℕ) (ps : s.Prime) (ds : s ∣ F x) : s ∈ row.2.1 := by
    have le := only s ps ds
    have nd : ¬s ∣ p+2 := by
      intro dd
      have dL : s ∣ 2^b+1 := by convert dd using 1; omega
      have three := fifth_order pb (pb.odd_of_ne_two (by omega)) ps dL (by omega)
      subst s
      have mem := (by decide : Nat.Prime 3).mem_primeFactors (common dd ds) (by decide)
      have tab : (53248:ℕ).primeFactors={2,13} := by decide +kernel
      rw [tab] at mem; simp at mem
    have s2 : s≠2 := by rintro rfl; omega
    have mult : s ∣ p^13+8192 := fac ▸ dvd_mul_of_dvd_right ds _
    obtain ⟨j,hj⟩ := thirteen_order ps s2 mult nd
    have sj : s=13*j+1 := by have := ps.two_le; omega
    have lst : ∀ i ∈ List.range 631, (13*i+1).Prime → ∃ e ∈ catalog,e.1=13*i+1 :=
      thirteen_prime_check catalog Prod.fst
        [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89]
        (by decide +kernel)
    obtain ⟨⟨s',o,R,w,logs⟩,hm,es⟩ : ∃ e ∈ catalog,e.1=s := by rw [sj]; exact lst _ (List.mem_range.mpr (by omega)) (sj ▸ ps)
    change s'=s at es
    subst s'
    have periods : ∀ e ∈ catalog, 0 < e.2.1 ∧ e.2.1 ≤ 8193 ∧
        2^e.2.1%e.1=1 ∧ (∀ j ∈ e.2.1.primeFactors, 2^(e.2.1/j)%e.1≠1) ∧
        e.2.2.2.1^13%e.1=1 ∧ e.2.2.2.1%e.1≠1 ∧
        ∀ i : Fin 13, let t := e.2.2.2.2.getD i.val e.2.1
          let Y := (e.1+1-(2*e.2.2.2.1^i.val)%e.1)%e.1
          if t < e.2.1 then 2^t%e.1=Y ∧ (t.Coprime e.2.1 → t%(Nat.gcd e.2.1 780)∈e.2.2.1)
          else Y^e.2.1%e.1≠1 := by decide +kernel
    obtain ⟨op,ou,per,proper,wt,w1,cases⟩ := periods _ hm
    change 0<o at op
    change o≤8193 at ou
    change 2^o%s=1 at per
    let _ : Fact s.Prime := ⟨ps⟩
    let _ : Fact (Nat.Prime 13) := ⟨by decide⟩
    have mod1 (u : ℕ) : (u:ZMod s)=1 ↔ u%s=1 := by
      simpa only [Nat.cast_one,Nat.mod_eq_of_lt ps.one_lt] using ZMod.natCast_eq_natCast_iff' u 1 s
    have aone : (2:ZMod s)^o=1 := by simpa only [Nat.cast_pow,Nat.cast_ofNat] using (mod1 _).mpr per
    have aord : orderOf (2:ZMod s)=o := orderOf_eq_of_pow_and_pow_div_prime op aone (by
      intro j pj dj h
      have ng := proper j (pj.mem_primeFactors dj op.ne')
      exact ng ((mod1 _).mp (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using h)))
    have h2 : (2:ZMod s) ≠ 0 := by
      intro h
      exact s2 ((Nat.prime_dvd_prime_iff_eq ps Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 s).mp h))
    let z : ZMod s := -(p:ZMod s)/2
    have zero := (ZMod.natCast_eq_zero_iff _ _).mpr mult
    push_cast at zero
    have z13 : z^13=1 := by dsimp [z]; rw [div_pow,div_eq_iff (pow_ne_zero _ h2)]; linear_combination -zero
    have primitive : IsPrimitiveRoot (w:ZMod s) 13 := IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime
      (by simpa only [Nat.cast_pow] using (mod1 _).mpr wt) (fun h => w1 ((mod1 _).mp h)))
    obtain ⟨i,hi,iw⟩ := primitive.eq_pow_of_pow_eq_one z13
    let Y := (s+1-(2*w^i)%s)%s
    have min : (2*w^i)%s ≤ s+1 := by have := Nat.mod_lt (2*w^i) ps.pos; omega
    have Yeq : (Y:ZMod s)=(2:ZMod s)^b := by
      dsimp only [Y]
      rw [ZMod.natCast_mod,Nat.cast_sub min,Nat.cast_add,ZMod.natCast_self,Nat.cast_one,ZMod.natCast_mod,Nat.cast_mul,Nat.cast_pow]
      have bp := congrArg (fun n : ℕ => (n:ZMod s)) base
      push_cast at bp
      have iw' : (w:ZMod s)^i*2= -(p:ZMod s) := (eq_div_iff h2).mp iw
      push_cast
      linear_combination bp - iw'
    let t := logs.getD i o
    have c := cases ⟨i,hi⟩
    change (if t<o then 2^t%s=Y ∧ (t.Coprime o → t%(Nat.gcd o 780)∈R) else Y^o%s≠1) at c
    have com : (b%o)%(Nat.gcd o 780)∈R := by
      by_cases lt : t<o
      · rw [if_pos lt] at c
        obtain ⟨logt,accept⟩ := c
        have ylt : Y<s := Nat.mod_lt _ ps.pos
        have cast : ((2^t:ℕ):ZMod s)=(Y:ZMod s) := (ZMod.natCast_eq_natCast_iff' _ _ s).mpr (by rwa [Nat.mod_eq_of_lt ylt])
        push_cast at cast
        have fin : IsOfFinOrder (2:ZMod s) := isOfFinOrder_iff_pow_eq_one.mpr ⟨o,op,aone⟩
        have same := fin.pow_eq_pow_iff_modEq.mp (cast.trans Yeq)
        rw [aord] at same
        change t%o=b%o at same
        rw [Nat.mod_eq_of_lt lt] at same
        rw [←same]
        exact accept (same ▸ co o op (by omega))
      · rw [if_neg lt] at c
        exfalso
        apply c
        apply (mod1 _).mp
        rw [Nat.cast_pow,Yeq,←pow_mul,Nat.mul_comm,pow_mul,aone,one_pow]
    have rowsOk : ∀ r ∈ hard, ∀ t ∈ catalog, r.1%(Nat.gcd t.2.1 780) ∈ t.2.2.1 → t.1 ∈ r.2.1 :=
      thirteen_row_check hard catalog (fun r t => r.1%(Nat.gcd t.2.1 780) ∈ t.2.2.1)
        (fun r t => t.1 ∈ r.2.1) (by decide +kernel)
    apply rowsOk _ hr _ hm
    change row.1%(Nat.gcd o 780) ∈ R
    rw [rb,Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_right _ _)]
    rwa [Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_left _ _)] at com
  have valid : ∀ r ∈ hard,
      (∀ m ∈ r.2.2, m=4 ∨ m=8 ∨ (m.Prime ∧ 2 < m ∧ 2^780%m=1)) ∧
      (∀ s ∈ r.2.1, (r.2.2.map (fun m => char m s)).prod=1) ∧
      (r.2.2.map (fun m => char m (F ((2^(r.1+780)-3)%m)))).prod= -1 := by decide +kernel
  obtain ⟨mods,good,bad⟩ := valid _ hr
  let chi (n : ℕ) := (row.2.2.map (fun m => char m n)).prod
  have mul (u v : ℕ) : chi (u*v)=chi u*chi v := by
    have gen (l : List ℕ) (hl : ∀ m ∈ l, m=4 ∨ m=8 ∨ (m.Prime ∧ 2 < m)) :
        (l.map (fun m => char m (u*v))).prod=(l.map (fun m => char m u)).prod*(l.map (fun m => char m v)).prod := by
      induction l with
      | nil => simp
      | cons m tail ih =>
        simp only [List.map_cons,List.prod_cons]
        rw [show char m (u*v)=char m u*char m v from thirteen_character_mul m (hl _ (by simp)) u v,
          ih (fun s hs => hl s (by simp [hs]))]
        ring
    exact gen _ (by intro m hm; rcases mods m hm with h|h|⟨a,b,_⟩; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr ⟨a,b⟩))
  have one : chi 1=1 := by
    have h : ∀ r ∈ hard,(r.2.2.map (fun m => char m 1)).prod=1 := by decide +kernel
    exact h _ hr
  have pos : chi (F x)=1 := by
    have gen (l : List ℕ) (hl : ∀ s ∈ l,s ∈ row.2.1) : chi l.prod=1 := by
      induction l with
      | nil => exact one
      | cons s t ih =>
        rw [List.prod_cons,mul,show chi s=1 from good s (hl s (by simp)),one_mul]
        exact ih (fun u hu => hl u (by simp [hu]))
    have h := gen (F x).primeFactorsList (fun s hs => sup s (Nat.prime_of_mem_primeFactorsList hs) (Nat.dvd_of_mem_primeFactorsList hs))
    rwa [Nat.prod_primeFactorsList (show F x≠0 by omega)] at h
  have same (m : ℕ) (hm : m ∈ row.2.2) : char m (F x)=char m (F ((2^(row.1+780)-3)%m)) := by
    have large : 3≤2^(row.1+780) := by
      have zz := Nat.pow_le_pow_right (by decide : 0<2) (show 2≤row.1+780 by omega)
      norm_num at zz; omega
    have congrX : Nat.ModEq m x ((2^(row.1+780)-3)%m) := by
      apply Nat.ModEq.trans _ (Nat.mod_modEq _ _).symm
      apply Nat.ModEq.add_right_cancel' 3
      rw [bx,Nat.sub_add_cancel large]
      rcases mods m hm with rfl|rfl|⟨pm,mb,per⟩
      · have d : 4 ∣ 2^b := pow_dvd_pow (2:ℕ) (show 2≤b by omega)
        have d' : 4 ∣ 2^(row.1+780) := pow_dvd_pow (2:ℕ) (show 2≤row.1+780 by omega)
        change 2^b%4=2^(row.1+780)%4; omega
      · have d' : 8 ∣ 2^(row.1+780) := pow_dvd_pow (2:ℕ) (show 3≤row.1+780 by omega)
        change 2^b%8=2^(row.1+780)%8; omega
      · have mo : Nat.ModEq m (2^780) 1 := by change 2^780%m=1%m; rwa [Nat.mod_eq_of_lt (by omega : 1 < m)]
        have red := eleven_period (b:=b) mo
        rw [pow_add,rb]
        have lift := mo.mul_left (2^(b%780))
        rw [mul_one] at lift
        exact red.trans lift.symm
    have reduced := fc congrX
    change F x%m=F ((2^(row.1+780)-3)%m)%m at reduced
    by_cases m4 : m=4
    · subst m
      dsimp [char]
      split_ifs <;> omega
    by_cases m8 : m=8
    · subst m
      dsimp [char]
      split_ifs <;> omega
    simp only [char,m4,m8,if_false,reduced]
  have eq : (row.2.2.map (fun m => char m (F x)))=(row.2.2.map (fun m => char m (F ((2^(row.1+780)-3)%m)))) :=
    List.map_congr_left (fun m hm => same m hm)
  change (row.2.2.map (fun m => char m (F x))).prod=1 at pos
  rw [eq,bad] at pos
  contradiction

/-- Two-prime witnesses cover both the bounded and unbounded Mersenne indices. -/
theorem mersenne_thirteenth_witness {p b : ℕ} (pp : p.Prime) (base : p+1=2^b) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p^13+d ∧ s ∣ p^13+d := by
  by_cases small : b≤8193
  · have ep : p=2^b-1 := by omega
    have b1 : b≠1 := by rintro rfl; norm_num at base; have := pp.two_le; omega
    have pb : b.Prime := (Nat.prime_of_pow_sub_one_prime b1 (ep ▸ pp)).2
    exact ep ▸ thirteenth_small small pb
  · exact mersenne_thirteen_large_witness pp base (by omega)

-- BEGIN SEVENTEEN BOUNDED
private theorem seventeen_prime_data {t : ℕ} (mem : t ∈ [5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,257,263,269,281,283,293,307,311,337,347,367,383,401,421,467,1321]) : t.Prime ∧ 2^(t-1)%t=1 := by
  have good : ∀ q ∈ ([5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,257,263,269,281,283,293,307,311,337,347,367,383,401,421,467,1321] : List ℕ), q.Prime ∧ 2^(q-1)%q=1 := by decide +kernel
  exact good t mem

private theorem seventeen_index_divisor {b o t d : ℕ} (pt : t.Prime) (period : 2^o%t=1)
    (hit : (((2^(b%o)-1)%t)^17+d)%t=0) : t ∣ (2^b-1)^17+d := by
  have m : Nat.ModEq t (2^o) 1 := by
    change 2^o%t=1%t
    rwa [Nat.mod_eq_of_lt pt.one_lt]
  have red : Nat.ModEq t (2^b) (2^(b%o)) := by
    calc
      2^b = 2^(b%o)*(2^o)^(b/o) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
      _ ≡ 2^(b%o)*1^(b/o) [MOD t] := (m.pow _).mul_left _
      _ = _ := by simp
  have pm : Nat.ModEq t (2^b-1) ((2^(b%o)-1)%t) := by
    apply Nat.ModEq.trans _ (Nat.mod_modEq _ _).symm
    apply Nat.ModEq.add_right_cancel' 1
    rw [Nat.sub_add_cancel (Nat.one_le_pow b 2 (by decide)),
      Nat.sub_add_cancel (Nat.one_le_pow (b%o) 2 (by decide))]
    exact red
  exact Nat.dvd_iff_mod_eq_zero.mpr (((pm.pow 17).add_right d).trans (show Nat.ModEq t _ 0 from hit))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- After the periodic checks, just 36 index classes require individual certificates. -/
private theorem seventeen_periodic_or_ray {b : ℕ} (pb : b.Prime) :
    (∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d) ∨ b%2520 ∈ [1,61,121,241,253,361,401,421,613,673,841,901,937,961,1081,1177,1201,1261,1321,1441,1501,1513,1621,1681,1793,1801,1873,1933,2017,2081,2101,2161,2281,2341,2377,2461] := by
  let rules : List (ℕ × ℕ × ℕ × ℕ × ℕ) := [(10,9,8,11,31),(20,7,3,5,11),(20,11,3,5,41),(18,17,2,7,19),(60,43,5,11,61),(40,37,3,11,17),(60,23,11,13,41),(180,13,9,19,41),(60,17,26,41,61),(180,113,11,19,61),(56,37,3,17,29),(84,5,8,13,29),(35,3,9,71,127),(90,67,9,19,31),(21,20,16,127,337),(126,25,23,43,73),(126,97,16,19,127),(70,33,5,11,71),(420,281,333,421,1321),(140,37,3,11,29),(252,101,4,19,29),(252,229,8,29,37),(252,185,6,37,43),(420,13,7,29,61),(140,117,26,41,71),(280,181,3,17,71),(315,263,49,71,73),(140,17,26,41,113),(252,221,15,73,113),(126,31,9,19,127),(1260,641,12,109,211),(420,373,41,127,421),(12,2,2,5,7),(420,233,9,41,211),(120,53,13,31,241)]
  have eligible : (b%2520).Coprime 2520 ∨ b%2520 ∈ [2,3,5,7] := by
    by_cases co : b.Coprime 2520
    · left
      change Nat.gcd (b%2520) 2520=1
      rw [←Nat.gcd_rec 2520 b,Nat.gcd_comm]
      exact co
    · right
      have dv : b ∣ 2520 := by by_contra h; exact co (pb.coprime_iff_not_dvd.mpr h)
      have mem := pb.mem_primeFactors dv (by decide)
      have tab : (2520:ℕ).primeFactors={2,3,5,7} := by decide +kernel
      rw [tab] at mem
      simp only [Finset.mem_insert,Finset.mem_singleton] at mem
      rcases mem with rfl|rfl|rfl|rfl <;> decide
  have cover : (List.range 2520).all (fun i =>
      decide (¬i.Coprime 2520 ∧ i ∉ ([2,3,5,7] : List ℕ)) ||
      decide (i ∈ ([1,61,121,241,253,361,401,421,613,673,841,901,937,961,1081,1177,1201,1261,1321,1441,1501,1513,1621,1681,1793,1801,1873,1933,2017,2081,2101,2161,2281,2341,2377,2461] : List ℕ)) || rules.any (fun z => i%z.1 == z.2.1)) = true := by decide +kernel
  have h := List.all_eq_true.mp cover (b%2520) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  simp only [Bool.or_eq_true,decide_eq_true_eq,List.any_eq_true,beq_iff_eq] at h
  rcases h with (notCo|rem)|good
  · tauto
  · exact Or.inr rem
  left
  obtain ⟨⟨o,j,d,q,s⟩,mem,hit⟩ := good
  have checked : ∀ z ∈ rules, z.1 ∣ 2520 ∧ z.2.2.2.1 ∈ [5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,257,263,269,281,283,293,307,311,337,347,367,383,401,421,467,1321] ∧ z.2.2.2.2 ∈ [5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,257,263,269,281,283,293,307,311,337,347,367,383,401,421,467,1321] ∧
      z.2.2.2.1≠z.2.2.2.2 ∧ z.2.2.1+1<z.2.2.2.1 ∧ z.2.2.1+1<z.2.2.2.2 ∧
      2^z.1%z.2.2.2.1=1 ∧ 2^z.1%z.2.2.2.2=1 ∧
      (((2^z.2.1-1)%z.2.2.2.1)^17+z.2.2.1)%z.2.2.2.1=0 ∧
      (((2^z.2.1-1)%z.2.2.2.2)^17+z.2.2.1)%z.2.2.2.2=0 := by decide +kernel
  obtain ⟨od,mq,ms,ne,hq,hs,tq,ts,zq,zs⟩ := checked _ mem
  change (b%2520)%o=j at hit
  rw [Nat.mod_mod_of_dvd _ od] at hit
  have pq := (seventeen_prime_data mq).1
  have ps := (seventeen_prime_data ms).1
  exact ⟨d,q,s,pq,ps,ne,hq,hs,seventeen_index_divisor pq tq (hit ▸ zq),
    seventeen_index_divisor ps ts (hit ▸ zs)⟩

private theorem seventeen_ray_check {b i : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=i)
    (row : List (ℕ × ℕ × ℕ))
    (ok : (List.range 53).all (fun j =>
      let n := 2520*j+i
      let z := row.getD j (0,0,0)
      decide (n<2 ∨ 131073<n) ||
      decide (z.2.1 ∈ [5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,257,263,269,281,283,293,307,311,337,347,367,383,401,421,467,1321] ∧ z.2.2 ∈ [5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,257,263,269,281,283,293,307,311,337,347,367,383,401,421,467,1321] ∧ z.2.1≠z.2.2 ∧ z.1+1<z.2.1 ∧ z.1+1<z.2.2 ∧
        (((2^(n%(z.2.1-1))-1)%z.2.1)^17+z.1)%z.2.1=0 ∧
        (((2^(n%(z.2.2-1))-1)%z.2.2)^17+z.1)%z.2.2=0)) = true) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  have h := List.all_eq_true.mp ok (b/2520) (List.mem_range.mpr (by omega))
  dsimp only at h
  have id : 2520*(b/2520)+i=b := by omega
  rw [id] at h
  simp only [Bool.or_eq_true,decide_eq_true_eq] at h
  obtain ⟨mq,ms,ne,hq,hs,zq,zs⟩ := h.resolve_left (by omega)
  have pq := seventeen_prime_data mq
  have ps := seventeen_prime_data ms
  exact ⟨_,_,_,pq.1,ps.1,ne,hq,hs,seventeen_index_divisor pq.1 pq.2 zq,
    seventeen_index_divisor ps.1 ps.2 zs⟩

set_option maxRecDepth 8192 in
private theorem seventeen_ray_1 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=1) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(0,0,0),(39,47,163),(66,83,89),(34,157,223),(73,83,101),(10,59,137),(77,101,149),(42,227,269),(37,59,163),(32,53,89),(0,23,89),(23,47,79),(11,47,53),(25,47,59),(15,53,59),(18,67,107),(155,347,367),(274,401,467),(3,59,193),(87,223,233),(9,23,79),(0,23,89),(57,103,107),(49,149,269),(24,67,163),(46,149,307),(37,149,163),(15,53,67),(9,47,59),(11,197,199),(8,23,83),(71,83,107),(0,23,89),(33,83,167),(7,23,83),(66,89,149),(37,83,137),(17,47,157),(46,103,199),(69,83,107),(15,47,53),(42,59,79),(174,199,227),(0,23,89),(50,53,59),(10,53,149),(47,103,149),(188,199,229),(18,47,67),(46,103,199),(14,23,53),(24,83,163),(80,83,197)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_61 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=61) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(15,47,67),(23,53,73),(30,43,47),(8,23,29),(16,19,107),(15,53,59),(93,97,157),(10,79,137),(47,53,103),(3,17,59),(10,23,53),(9,47,79),(84,109,149),(16,19,67),(8,23,29),(23,73,79),(8,29,59),(23,47,73),(84,109,193),(23,73,83),(63,101,113),(8,29,167),(12,23,59),(49,107,139),(16,19,67),(8,23,29),(8,29,47),(30,43,67),(23,73,79),(8,29,83),(56,103,107),(47,59,103),(42,59,79),(3,17,139),(56,173,179),(50,53,59),(8,23,29),(16,19,47),(3,17,59),(26,197,199),(23,47,53),(23,73,79),(23,59,73),(17,47,59),(15,53,67),(8,29,59),(16,19,67),(8,23,29),(30,43,47),(8,29,47),(63,101,113),(12,47,59),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_121 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=121) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(3,29,59),(47,103,113),(34,59,67),(9,19,131),(70,107,131),(10,23,137),(15,47,67),(8,37,59),(1,137,239),(8,23,37),(9,19,23),(0,23,89),(47,53,113),(65,71,79),(3,29,83),(9,19,79),(28,43,47),(9,19,47),(28,43,59),(8,37,167),(8,23,37),(9,19,23),(0,23,89),(42,59,79),(34,67,109),(47,53,113),(50,53,59),(10,23,53),(9,19,79),(3,29,59),(133,167,197),(8,23,37),(9,19,23),(0,23,89),(98,107,167),(47,103,107),(8,37,59),(34,109,157),(47,53,113),(28,43,47),(9,19,47),(9,19,79),(8,23,37),(9,19,23),(0,23,89),(10,47,59),(34,67,109),(28,43,59),(37,59,131),(41,127,137),(47,103,113),(47,53,59),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_241 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=241) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(28,59,67),(37,59,71),(6,43,79),(37,71,149),(4,23,29),(42,59,79),(10,23,79),(15,59,67),(50,53,59),(16,19,47),(9,79,127),(56,103,107),(23,47,73),(23,53,73),(23,73,79),(4,23,29),(23,73,83),(18,59,67),(15,47,67),(14,23,107),(16,19,67),(8,23,47),(4,29,107),(0,23,89),(9,127,131),(33,157,167),(4,23,29),(23,73,79),(6,43,79),(9,47,127),(37,59,71),(16,19,67),(16,19,47),(47,53,59),(0,23,89),(23,47,73),(9,79,127),(4,23,29),(54,59,89),(23,53,73),(23,73,79),(6,43,79),(16,19,67),(37,71,131),(23,59,73),(0,23,89),(6,43,107),(64,107,191),(4,23,29),(9,79,127),(76,83,101),(139,179,211),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_253 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=253) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(0,23,47),(57,83,103),(10,53,59),(9,41,79),(13,23,31),(52,97,173),(13,31,59),(14,23,53),(5,11,23),(7,61,67),(9,23,41),(64,71,83),(127,131,137),(7,23,61),(24,67,83),(13,23,31),(9,41,79),(112,139,151),(6,167,199),(5,11,23),(7,61,67),(9,23,41),(0,23,89),(13,31,83),(7,23,61),(9,41,59),(13,23,31),(21,59,83),(12,23,59),(9,41,79),(5,11,23),(7,61,67),(9,23,41),(0,23,89),(5,11,107),(13,31,59),(5,11,179),(13,23,31),(10,23,79),(5,11,149),(112,139,151),(5,11,23),(7,47,61),(9,23,41),(9,41,47),(129,139,157),(7,23,61),(66,83,89),(13,23,31),(10,23,47),(37,107,139),(52,83,97),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_361 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=361) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(8,23,59),(23,43,47),(11,47,83),(46,307,311),(146,167,199),(22,47,227),(86,97,197),(15,47,113),(23,43,53),(14,23,29),(12,89,139),(14,29,47),(32,83,89),(13,59,83),(23,43,83),(47,53,59),(56,107,163),(10,53,137),(9,47,79),(15,67,113),(14,23,29),(23,43,53),(14,29,53),(10,47,131),(23,43,47),(15,53,113),(23,43,59),(17,47,59),(72,79,149),(10,23,149),(15,47,67),(14,23,29),(9,59,107),(8,23,47),(14,29,47),(14,29,53),(93,127,283),(6,59,149),(15,53,113),(93,127,157),(28,47,59),(47,53,103),(14,23,29),(16,67,107),(49,53,149),(9,23,131),(0,23,89),(23,43,47),(14,29,53),(66,89,197),(23,43,223),(3,59,83),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_401 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=401) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(6,37,67),(32,53,67),(6,37,59),(6,37,83),(8,13,23),(28,43,59),(11,19,47),(41,67,127),(15,73,79),(47,53,59),(46,61,103),(10,23,53),(15,59,73),(41,127,137),(8,13,47),(8,13,23),(3,29,59),(11,19,53),(41,67,127),(15,53,73),(28,43,107),(28,43,47),(6,37,67),(8,13,59),(31,79,89),(49,53,67),(8,13,23),(32,53,89),(23,47,53),(11,19,47),(11,19,53),(6,37,59),(15,53,73),(6,37,67),(28,43,59),(15,73,83),(5,23,109),(8,13,23),(47,59,113),(0,23,89),(47,103,113),(15,59,73),(47,103,113),(11,19,53),(28,43,47),(3,29,59),(47,103,113),(15,73,79),(8,13,23),(5,107,109),(10,47,53),(41,67,127),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_421 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=421) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(23,73,79),(11,53,83),(10,23,137),(15,53,67),(16,19,47),(16,19,67),(47,53,59),(23,47,73),(0,23,89),(3,17,83),(2,37,197),(32,53,83),(23,53,73),(3,17,59),(10,131,149),(31,83,89),(16,19,67),(23,59,73),(2,37,139),(0,23,89),(112,139,233),(47,103,107),(52,59,97),(9,59,131),(2,37,197),(23,53,73),(14,23,53),(16,19,47),(41,47,83),(10,47,59),(23,47,73),(84,109,193),(63,101,139),(84,109,149),(33,59,67),(26,83,173),(15,47,67),(63,101,229),(16,19,67),(8,23,47),(52,83,97),(0,23,89),(3,17,59),(112,131,139),(24,67,83),(47,53,103),(23,59,73),(96,131,149),(129,139,233),(16,19,67),(16,19,47),(23,53,73),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_613 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=613) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(5,11,23),(7,61,67),(9,23,41),(0,23,89),(14,29,47),(14,29,53),(11,53,83),(13,23,31),(18,47,67),(7,47,61),(14,23,29),(5,11,23),(7,61,67),(9,23,41),(49,53,71),(7,61,107),(7,23,61),(23,43,47),(13,23,31),(3,17,59),(15,67,113),(14,23,29),(5,11,23),(23,43,59),(9,23,41),(30,47,67),(8,47,59),(14,29,47),(52,59,97),(13,23,31),(23,43,53),(14,29,53),(14,23,29),(5,11,23),(9,41,47),(9,23,41),(0,23,47),(93,97,127),(7,23,61),(10,47,53),(13,23,31),(47,59,103),(15,67,113),(14,23,29),(5,11,23),(7,61,67),(9,23,41),(0,23,89),(3,17,59),(7,23,61),(14,29,47),(13,23,31),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_673 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=673) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(7,23,61),(13,31,59),(13,23,31),(16,19,107),(64,71,83),(9,41,79),(5,11,23),(7,61,67),(9,23,41),(23,73,79),(3,59,193),(7,23,61),(64,71,107),(13,23,31),(18,47,67),(7,47,61),(13,31,83),(5,11,23),(49,53,59),(9,23,41),(16,19,47),(23,53,73),(7,23,61),(23,47,73),(13,23,31),(15,53,83),(2,37,107),(29,53,59),(5,11,23),(7,61,67),(9,23,41),(30,47,67),(13,31,167),(7,23,61),(23,53,73),(13,23,31),(39,47,107),(7,61,263),(7,47,61),(5,11,23),(9,41,47),(9,23,41),(0,23,47),(16,19,47),(7,23,61),(64,71,83),(13,23,31),(23,53,73),(23,73,79),(9,41,59),(5,11,23),(7,61,67),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_841 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=841) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(33,59,157),(47,59,103),(14,23,53),(5,23,149),(8,23,37),(9,19,23),(0,23,89),(34,109,139),(31,73,83),(46,103,223),(34,59,109),(9,19,79),(8,37,47),(14,23,47),(16,67,79),(8,23,37),(9,19,23),(0,23,89),(9,19,59),(34,67,109),(9,19,47),(33,47,67),(65,79,179),(6,59,83),(9,19,79),(9,19,131),(8,23,37),(9,19,23),(0,23,89),(10,131,137),(34,67,109),(45,47,107),(15,47,163),(10,23,79),(47,53,103),(8,37,47),(106,139,157),(8,23,37),(9,19,23),(0,23,89),(76,83,101),(7,23,47),(31,73,293),(9,19,47),(8,37,59),(12,23,167),(31,73,89),(9,19,59),(8,23,37),(9,19,23),(9,19,79),(9,19,131),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_901 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=901) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(69,71,149),(30,43,67),(3,17,139),(63,101,113),(73,79,101),(23,53,83),(8,29,59),(45,107,127),(52,59,97),(37,131,139),(8,23,29),(63,113,139),(30,43,67),(63,101,113),(52,97,107),(8,29,83),(26,211,227),(30,43,47),(8,29,47),(14,23,47),(12,47,89),(8,23,29),(9,23,163),(30,43,67),(69,71,83),(47,53,103),(142,149,157),(33,47,67),(3,17,59),(8,29,163),(73,79,83),(16,67,79),(8,23,29),(11,47,53),(30,43,67),(8,29,59),(34,67,139),(45,47,127),(63,101,113),(63,113,173),(30,43,47),(8,29,47),(3,17,83),(8,23,29),(32,83,89),(30,43,67),(72,241,257),(7,23,47),(63,101,113),(33,59,67),(10,23,79),(45,83,127),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_937 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=937) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(7,23,29),(24,67,113),(9,31,47),(33,47,59),(47,53,59),(16,47,127),(41,47,71),(7,29,67),(9,23,31),(0,23,89),(26,41,83),(7,23,29),(24,67,113),(98,131,239),(15,47,53),(23,59,101),(47,103,107),(57,101,103),(8,23,59),(9,23,31),(9,31,79),(9,31,59),(7,23,29),(7,29,47),(3,11,139),(9,31,47),(46,101,199),(41,71,137),(16,47,67),(7,29,67),(9,23,31),(0,23,89),(41,71,137),(7,23,29),(24,67,113),(73,79,131),(46,101,103),(15,47,67),(24,47,113),(16,67,127),(8,23,47),(9,23,31),(0,23,89),(51,59,61),(7,23,29),(24,67,113),(7,29,47),(57,83,101),(9,31,47),(16,79,127),(9,31,59),(7,29,67),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_961 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=961) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(3,29,83),(112,131,149),(65,71,163),(12,47,59),(16,19,67),(3,29,89),(28,43,67),(0,23,89),(28,43,47),(23,53,73),(23,73,79),(33,59,67),(16,19,47),(15,53,67),(31,89,167),(16,19,67),(3,29,89),(28,43,67),(0,23,89),(3,29,59),(35,79,149),(73,79,101),(23,53,73),(23,59,73),(12,23,139),(14,23,47),(16,19,67),(3,29,89),(28,43,67),(0,23,89),(65,71,79),(28,43,47),(9,47,79),(33,47,67),(3,29,193),(16,19,47),(14,23,53),(28,43,59),(23,47,73),(28,43,67),(0,23,89),(3,29,83),(47,53,113),(65,71,79),(15,47,59),(23,73,83),(47,103,113),(31,83,89),(3,29,59),(23,73,79),(28,43,67),(0,23,89),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_1081 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=1081) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(4,23,29),(13,23,83),(9,127,131),(10,47,137),(23,47,53),(23,59,79),(6,43,79),(18,59,107),(0,23,89),(9,107,127),(15,47,83),(4,23,29),(112,263,383),(10,23,53),(12,23,59),(9,127,131),(6,43,59),(3,89,193),(37,71,83),(6,43,79),(37,59,71),(9,47,127),(4,23,29),(37,71,163),(72,79,107),(41,47,137),(10,47,53),(9,79,127),(6,43,107),(32,53,89),(0,23,89),(69,107,283),(34,59,67),(4,23,29),(37,71,131),(10,23,83),(12,23,139),(14,23,47),(12,47,89),(3,83,89),(9,23,59),(0,23,89),(26,113,139),(23,53,83),(4,23,29),(6,43,59),(10,23,59),(15,53,67),(6,43,199),(37,59,71),(47,53,103),(9,23,127),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_1177 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=1177) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(23,53,73),(23,73,79),(3,11,139),(9,31,47),(3,11,59),(3,11,193),(16,19,47),(51,59,61),(16,19,67),(23,47,73),(9,23,31),(0,23,89),(73,79,131),(23,53,73),(9,31,59),(75,107,173),(51,61,139),(12,23,59),(23,73,101),(16,19,67),(72,79,83),(9,23,31),(0,23,89),(9,31,79),(7,23,47),(23,73,83),(9,31,47),(23,73,79),(23,73,101),(16,19,47),(16,19,67),(3,11,89),(9,23,31),(3,11,59),(25,47,107),(34,59,67),(51,59,61),(23,59,73),(23,73,101),(23,53,73),(14,23,53),(16,19,67),(3,11,89),(9,23,31),(0,23,89),(29,53,83),(72,79,149),(26,41,83),(23,73,101),(9,31,47),(79,151,157),(73,79,107),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_1201 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=1201) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(14,29,53),(15,113,163),(8,37,47),(14,29,47),(12,23,47),(14,23,29),(14,29,107),(8,23,37),(9,19,23),(9,19,79),(9,19,47),(34,67,109),(23,43,53),(14,29,53),(9,19,107),(19,71,107),(14,23,29),(93,127,157),(8,23,37),(9,19,23),(0,23,89),(96,131,137),(9,19,59),(24,47,67),(73,79,101),(8,37,47),(14,29,47),(14,23,29),(10,59,137),(8,23,37),(9,19,23),(0,23,89),(14,29,149),(9,19,47),(154,173,181),(9,19,79),(9,19,131),(15,59,67),(14,23,29),(23,43,47),(8,23,37),(9,19,23),(59,79,83),(31,73,83),(34,67,109),(23,43,59),(45,83,107),(10,23,53),(8,37,47),(14,23,29),(12,47,89),(8,23,37),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_1261 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=1261) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(9,79,163),(16,67,107),(3,17,89),(3,17,59),(45,47,83),(63,101,229),(51,59,139),(15,53,83),(93,97,157),(18,59,67),(12,23,47),(44,67,83),(69,107,167),(9,59,79),(9,23,131),(0,23,89),(9,47,223),(57,83,103),(6,59,79),(35,149,167),(59,79,89),(72,241,257),(37,59,139),(5,23,107),(3,17,89),(63,101,167),(0,23,89),(9,131,163),(15,47,59),(24,47,67),(54,59,89),(10,23,131),(3,17,59),(2,139,197),(93,97,157),(3,17,89),(3,17,83),(0,23,89),(3,17,139),(9,47,79),(112,257,263),(52,59,97),(16,47,79),(46,103,149),(10,47,131),(12,59,89),(3,17,89),(28,67,107),(10,59,79),(47,53,103),(86,167,227),(146,173,179),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_1321 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=1321) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(2,37,107),(8,29,59),(16,19,47),(45,83,127),(10,23,47),(23,47,73),(69,71,149),(16,19,67),(8,23,29),(6,59,79),(30,43,67),(15,47,53),(7,23,83),(30,43,47),(8,29,47),(10,23,137),(12,23,47),(69,71,83),(16,19,67),(8,23,29),(23,53,73),(30,43,67),(63,101,113),(73,83,101),(68,163,181),(16,19,47),(10,23,79),(23,59,73),(23,47,73),(16,19,67),(8,23,29),(9,23,131),(30,43,67),(23,53,73),(23,73,79),(24,47,67),(30,43,47),(8,29,47),(6,59,107),(10,59,79),(16,19,67),(8,23,29),(63,101,113),(30,43,67),(45,83,127),(132,139,149),(23,53,73),(23,73,79),(16,19,47),(8,29,83),(26,173,179),(16,19,67),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_1441 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=1441) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(0,23,89),(24,47,113),(7,23,29),(14,53,83),(16,127,269),(3,59,71),(15,53,67),(112,131,139),(56,103,107),(7,29,47),(28,47,67),(0,23,89),(33,47,191),(7,23,29),(24,67,113),(16,79,127),(10,23,47),(24,113,163),(3,71,193),(27,43,59),(7,29,67),(10,59,79),(0,23,89),(7,29,107),(7,23,29),(24,67,113),(33,59,67),(73,79,101),(12,23,47),(14,23,53),(76,83,101),(7,29,67),(7,29,47),(3,71,83),(3,59,71),(7,23,29),(24,67,113),(47,103,107),(59,83,89),(15,67,229),(70,131,269),(16,67,79),(7,29,67),(6,79,107),(0,23,89),(15,53,83),(7,23,29),(24,47,67),(27,43,59),(10,23,137),(10,53,59),(7,29,83),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_1501 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=1501) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(23,47,59),(37,71,137),(14,23,83),(16,19,67),(3,17,89),(32,53,89),(23,53,73),(23,73,79),(6,43,79),(4,23,29),(37,71,131),(6,43,59),(10,59,79),(47,53,103),(16,19,67),(7,47,67),(28,47,67),(0,23,89),(37,71,137),(23,53,73),(4,23,29),(6,43,79),(10,23,47),(15,53,67),(11,47,83),(3,17,59),(3,17,89),(9,23,127),(10,53,83),(23,59,73),(9,127,131),(4,23,29),(8,47,59),(14,47,53),(12,23,47),(9,59,127),(16,19,67),(21,53,59),(9,23,127),(0,23,89),(6,43,59),(10,53,59),(4,23,29),(16,19,47),(37,59,71),(23,53,73),(14,23,53),(11,47,53),(3,17,89),(37,71,107),(0,23,89),(10,79,137),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_1513 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=1513) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(46,103,199),(115,157,167),(5,11,23),(7,61,67),(9,23,41),(0,23,89),(18,47,59),(7,23,47),(9,41,163),(13,23,31),(9,41,59),(15,67,83),(16,47,79),(5,11,23),(7,61,67),(9,23,41),(0,23,89),(7,61,83),(7,23,61),(37,59,83),(13,23,31),(10,23,53),(9,41,79),(30,47,167),(5,11,23),(7,61,67),(9,23,41),(0,23,89),(112,139,151),(7,23,61),(7,47,61),(13,23,31),(9,41,47),(96,137,149),(24,83,191),(5,11,23),(8,23,59),(9,23,41),(23,47,53),(9,41,59),(7,23,61),(56,103,163),(13,23,31),(13,31,83),(15,47,67),(96,107,137),(5,11,23),(8,23,47),(9,23,41),(13,31,59),(33,59,157),(7,23,61),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_1621 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=1621) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(14,29,83),(23,43,53),(14,29,53),(14,23,29),(7,47,107),(3,17,89),(9,23,47),(3,17,59),(87,157,167),(34,59,67),(10,53,149),(23,43,59),(23,43,47),(73,79,101),(14,23,29),(14,29,53),(3,17,89),(9,23,59),(15,47,53),(21,53,59),(52,83,97),(93,97,127),(14,29,47),(10,23,53),(15,67,113),(14,23,29),(37,59,163),(23,43,53),(14,29,53),(0,23,89),(3,17,83),(15,53,113),(15,59,113),(13,23,83),(10,23,47),(23,43,47),(14,23,29),(93,97,127),(3,17,89),(32,53,89),(23,43,53),(14,29,53),(15,83,113),(73,101,107),(8,47,83),(14,29,47),(12,23,47),(14,23,29),(72,241,257),(3,17,89),(9,23,79),(6,59,83),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_1681 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=1681) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(3,89,193),(32,89,269),(23,59,73),(69,107,227),(70,131,311),(23,53,73),(23,73,79),(10,23,131),(39,47,223),(63,101,173),(21,53,59),(3,89,139),(9,23,47),(0,23,89),(10,53,59),(16,19,47),(41,47,137),(73,79,83),(23,47,53),(23,73,79),(68,163,181),(16,19,67),(34,107,139),(21,53,191),(0,23,89),(24,47,239),(84,109,223),(10,53,137),(14,47,227),(2,37,139),(73,79,101),(23,53,59),(16,19,67),(7,47,67),(28,47,67),(0,23,89),(21,53,83),(34,67,157),(16,19,47),(65,79,163),(10,23,47),(23,47,73),(154,163,173),(16,19,67),(23,53,73),(28,59,67),(0,23,89),(49,139,149),(37,131,167),(47,59,167),(8,47,167),(47,53,103),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_1793 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=1793) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(11,61,83),(5,11,107),(29,37,53),(4,19,23),(13,23,31),(10,23,53),(8,13,47),(14,23,47),(5,11,23),(8,13,23),(9,23,41),(11,53,61),(4,19,79),(94,149,163),(4,19,23),(13,23,31),(4,19,107),(12,23,109),(31,79,89),(5,11,23),(8,13,23),(9,23,41),(8,13,83),(8,13,59),(11,53,61),(4,19,23),(13,23,31),(4,19,149),(29,37,53),(8,13,47),(5,11,23),(8,13,23),(9,23,41),(29,37,59),(47,103,107),(7,23,47),(4,19,23),(13,23,31),(4,19,79),(12,23,109),(25,59,67),(5,11,23),(8,13,23),(9,23,41),(11,47,61),(49,53,73),(63,167,191),(4,19,23),(13,23,31),(6,67,149),(11,53,61),(4,19,79),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_1801 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=1801) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(28,43,47),(3,29,89),(28,43,67),(0,23,47),(47,103,113),(41,47,83),(10,47,79),(54,59,89),(65,71,79),(3,29,59),(153,157,193),(34,59,139),(3,29,89),(23,53,59),(0,23,89),(47,103,113),(8,47,59),(65,71,107),(57,103,167),(10,23,79),(47,53,113),(65,71,79),(12,59,89),(28,43,47),(9,23,47),(0,23,89),(43,107,139),(28,43,59),(36,83,107),(13,23,59),(59,79,89),(47,59,113),(47,103,113),(47,53,103),(65,71,79),(28,43,67),(0,23,89),(41,127,137),(3,29,59),(9,107,163),(14,47,53),(10,23,131),(147,173,263),(44,67,83),(18,47,59),(8,23,59),(28,43,47),(65,71,79),(33,47,107),(47,103,113),(16,47,107),(41,47,127),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_1873 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=1873) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(15,59,113),(13,23,31),(93,127,157),(15,67,113),(14,23,29),(5,11,23),(7,61,67),(9,23,41),(23,43,59),(39,163,179),(23,43,53),(14,29,53),(13,23,31),(10,23,137),(9,41,59),(14,23,29),(5,11,23),(7,61,67),(9,23,41),(0,23,89),(7,47,61),(7,23,61),(9,41,47),(13,23,31),(14,29,53),(15,67,113),(14,23,29),(5,11,23),(23,43,47),(9,23,41),(0,23,89),(9,41,163),(7,23,61),(49,53,71),(13,23,31),(100,137,227),(23,43,53),(14,23,29),(5,11,23),(7,61,67),(9,23,41),(49,59,71),(9,41,107),(7,23,47),(4,23,149),(13,23,31),(49,53,71),(57,103,107),(14,23,29),(5,11,23),(14,29,53),(9,23,41),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_1933 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=1933) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(5,11,23),(7,61,67),(9,23,41),(7,47,61),(52,59,107),(9,41,47),(93,97,157),(13,23,31),(16,19,47),(72,241,257),(10,47,53),(5,11,23),(7,61,67),(9,23,41),(23,53,73),(13,31,59),(7,23,61),(47,59,103),(13,23,31),(61,191,193),(15,59,67),(14,23,47),(5,11,23),(7,61,67),(9,23,41),(0,23,89),(7,47,61),(7,23,61),(9,41,47),(13,23,31),(18,59,67),(16,19,47),(93,97,157),(5,11,23),(9,41,59),(9,23,41),(13,31,83),(9,41,79),(7,23,61),(96,137,149),(13,23,31),(23,73,79),(7,61,191),(2,37,197),(5,11,23),(7,61,67),(9,23,41),(0,23,89),(84,109,193),(7,23,47),(9,41,79),(13,23,31),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_2017 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=2017) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(10,47,53),(9,31,79),(20,53,107),(73,79,131),(9,31,59),(61,71,83),(9,23,31),(3,11,83),(51,61,139),(6,59,167),(10,59,79),(23,83,101),(59,83,89),(37,59,281),(9,31,79),(51,61,83),(7,47,67),(9,23,31),(9,31,47),(15,59,83),(98,101,131),(26,41,107),(3,11,193),(10,23,47),(9,31,163),(65,79,229),(51,59,61),(9,31,79),(9,23,31),(0,23,89),(3,11,193),(23,79,101),(45,149,211),(9,31,59),(59,79,89),(12,23,47),(34,107,157),(39,47,83),(3,11,89),(9,23,31),(9,31,79),(9,31,47),(46,101,103),(4,23,107),(33,59,67),(61,71,107),(61,71,83),(72,83,179),(3,11,83),(3,11,89),(9,23,31),(0,23,89),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_2081 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=2081) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(4,19,79),(4,19,23),(21,53,83),(29,37,53),(49,59,73),(28,43,47),(9,47,59),(8,13,23),(9,23,131),(8,13,83),(41,47,67),(65,71,107),(4,19,23),(29,37,59),(28,43,59),(37,59,83),(29,37,53),(49,67,73),(8,13,23),(29,37,83),(49,53,73),(8,13,47),(57,103,151),(4,19,23),(63,79,101),(3,29,59),(4,19,79),(4,19,163),(28,43,47),(8,13,23),(47,53,103),(0,23,47),(8,13,59),(49,53,59),(4,19,23),(12,67,109),(3,29,83),(28,43,107),(12,59,109),(49,67,73),(8,13,23),(57,67,103),(29,37,53),(28,43,59),(8,13,47),(4,19,23),(12,47,67),(77,79,101),(32,53,67),(25,59,67),(49,67,73),(8,13,23),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_2101 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=2101) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(8,37,47),(57,103,179),(52,59,97),(9,19,59),(9,19,79),(18,47,67),(12,23,59),(31,73,89),(9,19,47),(8,23,37),(9,19,23),(0,23,89),(52,83,97),(10,47,79),(47,53,103),(8,37,149),(10,23,53),(9,19,79),(31,73,89),(73,79,101),(8,23,37),(9,19,23),(3,17,59),(8,37,47),(34,59,67),(9,19,107),(23,59,83),(59,83,89),(18,47,59),(8,37,59),(49,53,59),(8,23,37),(9,19,23),(0,23,47),(96,137,149),(34,67,109),(8,37,83),(37,131,139),(10,23,59),(29,53,59),(31,73,89),(34,109,139),(8,23,37),(9,19,23),(0,23,89),(15,163,179),(8,37,47),(14,47,53),(99,107,173),(54,59,107),(15,53,67),(3,17,59),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_2161 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=2161) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(10,23,59),(12,23,167),(45,47,127),(69,71,83),(8,23,29),(30,43,47),(8,29,47),(96,131,137),(40,83,131),(4,23,149),(39,47,83),(18,47,67),(26,139,211),(11,53,83),(12,89,191),(8,23,29),(43,139,191),(30,43,67),(47,53,103),(96,107,137),(8,29,59),(49,53,59),(25,47,107),(32,53,83),(8,29,163),(23,79,83),(8,23,29),(24,47,163),(30,43,47),(8,29,47),(29,53,59),(153,193,197),(65,79,107),(10,23,53),(8,29,167),(8,29,83),(73,79,101),(8,23,29),(33,47,83),(0,23,47),(63,101,113),(37,83,131),(8,29,163),(57,83,103),(69,71,83),(63,101,113),(14,23,107),(153,157,193),(8,23,29),(8,29,59),(30,43,67),(30,43,47),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_2281 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=2281) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(57,83,103),(7,29,47),(8,37,59),(9,19,47),(16,67,127),(8,23,37),(9,19,23),(0,23,89),(10,47,131),(7,23,29),(24,67,113),(21,53,191),(29,53,59),(24,83,113),(31,73,89),(10,53,83),(8,23,37),(9,19,23),(8,37,47),(3,71,83),(7,23,29),(24,67,113),(13,23,83),(18,47,67),(7,29,47),(31,73,83),(9,19,47),(8,23,37),(9,19,23),(9,19,79),(9,19,131),(7,23,29),(23,47,53),(8,37,83),(9,19,59),(53,107,139),(31,73,89),(7,29,83),(8,23,37),(9,19,23),(30,47,67),(8,37,47),(7,23,29),(24,67,113),(13,23,59),(16,79,127),(62,89,149),(7,29,47),(16,67,127),(8,23,37),(9,19,23),(0,23,47),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_2341 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=2341) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(3,17,89),(6,43,59),(0,23,89),(29,53,59),(72,79,241),(4,23,29),(13,23,59),(9,79,127),(52,83,97),(9,47,127),(16,67,79),(3,17,89),(6,43,79),(0,23,89),(10,47,83),(3,17,59),(4,23,29),(72,79,83),(3,17,83),(46,167,199),(9,79,127),(9,127,131),(8,23,59),(9,23,127),(0,23,89),(6,43,79),(37,71,167),(4,23,29),(46,103,107),(18,47,67),(6,43,59),(37,71,107),(9,47,127),(3,17,89),(37,59,71),(0,23,89),(37,71,163),(23,79,167),(4,23,29),(6,43,83),(15,53,59),(93,97,157),(29,53,83),(98,167,197),(3,17,59),(9,23,127),(30,47,67),(73,83,101),(6,43,167),(4,23,29),(72,107,241),(6,43,79),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_2377 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=2377) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(57,101,103),(14,29,47),(23,43,53),(14,29,53),(18,59,67),(23,43,83),(14,23,29),(3,11,139),(9,31,47),(9,23,31),(0,23,47),(4,101,131),(9,31,79),(23,43,101),(23,43,47),(23,43,53),(14,29,53),(14,23,29),(23,43,101),(7,67,83),(9,23,31),(0,23,89),(98,101,107),(23,43,101),(14,29,47),(9,31,79),(79,151,157),(3,11,59),(14,23,29),(14,29,53),(51,59,61),(9,23,31),(0,23,89),(23,43,101),(14,29,149),(51,61,179),(26,41,107),(23,43,47),(9,31,79),(14,23,29),(12,59,89),(23,43,53),(9,23,31),(0,23,89),(51,61,139),(15,53,113),(23,43,83),(14,29,47),(23,43,101),(47,59,103),(14,23,29),(9,31,79),(0,0,0)]
  decide +kernel

set_option maxRecDepth 8192 in
private theorem seventeen_ray_2461 {b : ℕ} (lo : 2≤b) (hi : b≤131073) (index : b%2520=2461) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  apply seventeen_ray_check lo hi index [(93,97,127),(8,23,37),(9,19,23),(0,23,89),(23,43,47),(23,43,53),(14,29,53),(9,19,59),(93,97,127),(15,53,67),(14,23,29),(34,109,157),(8,23,37),(9,19,23),(14,29,47),(9,19,79),(3,17,83),(34,109,223),(23,43,53),(14,29,53),(23,43,83),(14,23,29),(15,53,59),(8,23,37),(9,19,23),(0,23,89),(3,17,59),(23,43,47),(9,19,79),(9,19,131),(23,43,59),(23,43,53),(14,23,29),(8,37,59),(8,23,37),(9,19,23),(8,37,47),(14,29,47),(47,53,103),(12,59,199),(9,19,107),(18,47,67),(15,67,113),(14,23,29),(9,19,47),(8,23,37),(9,19,23),(0,23,89),(15,53,113),(42,59,79),(23,43,47),(15,59,113),(0,0,0)]
  decide +kernel

/-- Two different primes exceeding the offset exist for every prime index up through 131073. -/
theorem seventeen_bounded_witness {b : ℕ} (pb : b.Prime) (hi : b≤131073) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d := by
  rcases seventeen_periodic_or_ray pb with direct|remaining
  · exact direct
  simp only [List.mem_cons,List.not_mem_nil,or_false] at remaining
  rcases remaining with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact seventeen_ray_1 pb.two_le hi h
  · exact seventeen_ray_61 pb.two_le hi h
  · exact seventeen_ray_121 pb.two_le hi h
  · exact seventeen_ray_241 pb.two_le hi h
  · exact seventeen_ray_253 pb.two_le hi h
  · exact seventeen_ray_361 pb.two_le hi h
  · exact seventeen_ray_401 pb.two_le hi h
  · exact seventeen_ray_421 pb.two_le hi h
  · exact seventeen_ray_613 pb.two_le hi h
  · exact seventeen_ray_673 pb.two_le hi h
  · exact seventeen_ray_841 pb.two_le hi h
  · exact seventeen_ray_901 pb.two_le hi h
  · exact seventeen_ray_937 pb.two_le hi h
  · exact seventeen_ray_961 pb.two_le hi h
  · exact seventeen_ray_1081 pb.two_le hi h
  · exact seventeen_ray_1177 pb.two_le hi h
  · exact seventeen_ray_1201 pb.two_le hi h
  · exact seventeen_ray_1261 pb.two_le hi h
  · exact seventeen_ray_1321 pb.two_le hi h
  · exact seventeen_ray_1441 pb.two_le hi h
  · exact seventeen_ray_1501 pb.two_le hi h
  · exact seventeen_ray_1513 pb.two_le hi h
  · exact seventeen_ray_1621 pb.two_le hi h
  · exact seventeen_ray_1681 pb.two_le hi h
  · exact seventeen_ray_1793 pb.two_le hi h
  · exact seventeen_ray_1801 pb.two_le hi h
  · exact seventeen_ray_1873 pb.two_le hi h
  · exact seventeen_ray_1933 pb.two_le hi h
  · exact seventeen_ray_2017 pb.two_le hi h
  · exact seventeen_ray_2081 pb.two_le hi h
  · exact seventeen_ray_2101 pb.two_le hi h
  · exact seventeen_ray_2161 pb.two_le hi h
  · exact seventeen_ray_2281 pb.two_le hi h
  · exact seventeen_ray_2341 pb.two_le hi h
  · exact seventeen_ray_2377 pb.two_le hi h
  · exact seventeen_ray_2461 pb.two_le hi h

/-- The cofactor lies strictly between consecutive scaled squares. -/
theorem seventeen_cofactor_not_square_large {p t : ℕ} (large : 8192≤p) :
    p^17+1 ≠ (p+1)*t^2 := by
  intro contra
  have h : (p:ℤ)^17+1=((p:ℤ)+1)*(t:ℤ)^2 := by exact_mod_cast contra
  let x : ℤ := (p:ℤ)-8192
  have hx : 0≤x := by
    dsimp [x]
    have hl : (8192:ℤ)≤p := by exact_mod_cast large
    omega
  have ep : (p:ℤ)=x+8192 := by dsimp [x]; ring
  let s := 32768*(p:ℤ)^8-16384*(p:ℤ)^7+12288*(p:ℤ)^6-10240*(p:ℤ)^5+
    8960*(p:ℤ)^4-8064*(p:ℤ)^3+7392*(p:ℤ)^2-6864*(p:ℤ)+6435
  have hs : 0<s := by
    dsimp only [s]
    rw [ep]
    ring_nf
    positivity
  have below : 0 < 32768^2*((p:ℤ)^17+1) - ((p:ℤ)+1)*(s-1)^2 := by
    dsimp only [s]
    rw [ep]
    ring_nf
    positivity
  have above : 0 < ((p:ℤ)+1)*s^2 - 32768^2*((p:ℤ)^17+1) := by
    dsimp only [s]
    rw [ep]
    ring_nf
    positivity
  have hpos : 0 < (p:ℤ)+1 := by positivity
  have left : ((p:ℤ)+1)*(s-1)^2 < ((p:ℤ)+1)*(32768*(t:ℤ))^2 := by
    calc
      _ < 32768^2*((p:ℤ)^17+1) := by linarith only [below]
      _ = _ := by rw [h]; ring
  have right : ((p:ℤ)+1)*(32768*(t:ℤ))^2 < ((p:ℤ)+1)*s^2 := by
    calc
      _ = 32768^2*((p:ℤ)^17+1) := by rw [h]; ring
      _ < _ := by linarith only [above]
  have hleft := lt_of_mul_lt_mul_left left (le_of_lt hpos)
  have hright := lt_of_mul_lt_mul_left right (le_of_lt hpos)
  have lt1 : s-1 < 32768*(t:ℤ) := by
    by_contra! hn
    have := mul_self_le_mul_self (show 0≤32768*(t:ℤ) by positivity) hn
    nlinarith
  have lt2 : 32768*(t:ℤ) < s := by
    by_contra! hn
    have := mul_self_le_mul_self hs.le hn
    nlinarith
  omega

theorem seventeen_cofactor_not_square {p b t : ℕ} (hb : 2≤b) (hm : p+1=2^b) :
    p^17+1 ≠ (p+1)*t^2 := by
  by_cases large : 8192≤p
  · exact seventeen_cofactor_not_square_large large
  have small : b<14 := by
    by_contra! big
    have low := Nat.pow_le_pow_right (by decide : 0<2) big
    omega
  have table : ∀ j ∈ List.range 12,
      let m := 2^(j+2)-1
      let c := (m^17+1)/(m+1)
      Nat.sqrt c * Nat.sqrt c ≠ c := by decide +kernel
  have mem : b-2 ∈ List.range 12 := List.mem_range.mpr (by omega)
  have obs := table (b-2) mem
  have hb' : b-2+2=b := by omega
  have hp : 2^b-1=p := by omega
  dsimp only at obs
  rw [hb',hp] at obs
  intro con
  rw [con,Nat.mul_div_cancel_left _ (by omega : 0<p+1),pow_two,Nat.sqrt_eq] at obs
  exact obs rfl

theorem seventeen_cofactor_odd_exponent {p b q a : ℕ} (hb : 2≤b) (hm : p+1=2^b)
    (h : p^17+1=(p+1)*q^a) : Odd a := by
  rcases Nat.even_or_odd a with ⟨k,hk⟩ | odd
  · have e : a=k*2 := by omega
    rw [e,pow_mul] at h
    exact (seventeen_cofactor_not_square hb hm h).elim
  · exact odd

theorem seventeen_cofactor_base_mod {p b q a : ℕ} (hb : 5≤b) (hm : p+1=2^b)
    (h : p^17+1=(p+1)*q^a) : q%32=17 := by
  have d : 32∣p+1 := hm ▸ (pow_dvd_pow 2 hb : 2^5∣2^b)
  obtain ⟨k,hk⟩ := d
  have hp : p ≡ 31 [MOD 32] := by change p%32=31%32; omega
  let F (z : ℕ) := 1+(z-1)*(z+z^3+z^5+z^7+z^9+z^11+z^13+z^15)
  have ep : q^a = F p := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0<p+1)
    rw [←h]
    cases p with
    | zero => omega
    | succ p => try dsimp [F]
                ring
  have hF : F p ≡ F 31 [MOD 32] := by
    dsimp only [F]
    gcongr <;> omega
  have target : q^a ≡ 17 [MOD 32] := ep ▸ hF.trans (by decide +kernel)
  have odd := seventeen_cofactor_odd_exponent (by omega) hm h
  obtain ⟨j,hj⟩ := odd
  have ho : Odd (q^a) := by
    apply Nat.odd_iff.mpr
    change q^a%32=17%32 at target
    omega
  have hq : (q%32)%2=1 := by
    have he := Nat.odd_iff.mp ((Nat.odd_pow_iff (by omega : a ≠ 0)).mp ho)
    omega
  have table : ∀ t ∈ List.range 32, t%2=1 → t^8%32=1 ∧
      ∀ i ∈ List.range 8, i%2=1 → t^i%32=17 → t=17 := by decide +kernel
  obtain ⟨cycle,get⟩ := table (q%32) (List.mem_range.mpr (by omega)) hq
  have per : q^8 ≡ 1 [MOD 32] := ((Nat.mod_modEq q 32).symm.pow 8).trans cycle
  have red : q^a ≡ (q%32)^(a%8) [MOD 32] := by
    calc
      q^a = q^(a%8)*(q^8)^(a/8) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
      _ ≡ (q%32)^(a%8)*1^(a/8) [MOD 32] := ((Nat.mod_modEq q 32).symm.pow _).mul (per.pow _)
      _ = _ := by simp
  exact get (a%8) (List.mem_range.mpr (by omega)) (by omega) (red.symm.trans target)

private theorem seventeen_cycle {x t m : ℕ} (h : Nat.ModEq m (x^t) 1) (b : ℕ) :
    Nat.ModEq m (x^b) (x^(b%t)) := by
  calc
    x^b = x^(b%t)*(x^t)^(b/t) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
    _ ≡ x^(b%t)*1^(b/t) [MOD m] := (h.pow _).mul_left _
    _ = _ := by simp

/-- For a Mersenne base with index b, every prime above four at offset
four is one modulo 2^(b-1) if there is no two-prime witness. -/
theorem mersenne_four_prime_congruence {p b r q : ℕ} (base : p+1=2^b) (ob : Odd b)
    (hb : 3 ≤ b) (ro : Odd r) (pq : q.Prime) (qb : 4 < q) (dq : q ∣ p^r+3)
    (missing : ¬∃ d l s : ℕ, l.Prime ∧ s.Prime ∧ l≠s ∧ d+1 < l ∧ d+1 < s ∧
      l ∣ p^r+d ∧ s ∣ p^r+d) : 2^(b-1) ∣ q-1 := by
  let D := (p^r+3)/2
  have dbase : 2^b ∣ p^r+1 := by
    rw [←base]
    simpa using ro.nat_add_dvd_pow_add_pow p 1
  have d4 : 4 ∣ p^r+1 := (pow_dvd_pow (2:ℕ) (show 2≤b by omega)).trans dbase
  have fac : 2*D=p^r+3 := by dsimp [D]; omega
  have oddD : ¬2 ∣ D := by omega
  have mod3 : D%3=2 := by
    obtain ⟨j,hj⟩ := ob
    have bpow : Nat.ModEq 3 (2^b) 2 := by
      rw [hj,pow_succ,pow_mul]
      have sq : Nat.ModEq 3 (2^2) 1 := by decide
      simpa only [one_pow,one_mul] using (sq.pow j).mul_right 2
    change 2^b%3=2 at bpow
    have z : Nat.ModEq 3 p 1 := by change p%3=1; omega
    have zr : Nat.ModEq 3 (p^r) 1 := by simpa only [one_pow] using z.pow r
    change p^r%3=1 at zr
    omega
  have pure : D=q^D.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
      intro s ps ds
      by_contra neq
      have big : 4<s := by
        by_contra! upper
        have choices : s=2 ∨ s=3 := by
          have s4 : s≠4 := by rintro rfl; exact (by decide : ¬Nat.Prime 4) ps
          have := ps.two_le
          omega
        rcases choices with rfl|rfl <;> omega
      exact missing ⟨3,s,q,ps,pq,neq,big,qb,fac ▸ dvd_mul_of_dvd_right ds _,dq⟩)
  let e := D.primeFactorsList.length
  change D=q^e at pure
  have oe : Odd e := by
    apply Nat.not_even_iff_odd.mp
    rintro ⟨j,hj⟩
    have sq : D=(q^j)^2 := by rw [pure,hj,pow_add,pow_two]
    have rem := Nat.mod_lt (q^j) (by decide : 0<3)
    rw [sq,pow_two,Nat.mul_mod] at mod3
    interval_cases h : q^j%3 <;> norm_num [h] at mod3
  let S := ∑ i ∈ Finset.range e, q^i
  have oq := pq.odd_of_ne_two (by omega)
  have os : Odd S := by
    dsimp [S]
    rw [Finset.odd_sum_iff_odd_card_odd]
    simpa [oq.pow] using oe
  have geom : S*(q-1)=D-1 := by
    simpa [S,pure] using geom_sum_mul_of_one_le pq.one_le e
  have halve : 2^(b-1) ∣ D-1 := by
    have bp : 2^b=2*2^(b-1) := by
      conv_lhs => rw [show b=(b-1)+1 by omega,pow_succ,Nat.mul_comm]
    rw [bp,show p^r+1=2*(D-1) by omega] at dbase
    exact Nat.dvd_of_mul_dvd_mul_left (by decide) dbase
  have cop : Nat.Coprime (2^(b-1)) S := by
    apply Nat.Coprime.pow_left
    exact Nat.prime_two.coprime_iff_not_dvd.mpr
      (fun d => (Nat.not_even_iff_odd.mpr os) (even_iff_two_dvd.mpr d))
  exact cop.dvd_of_dvd_mul_left (geom ▸ halve)

private theorem seventeen_offset_mod {p b m u q d : ℕ} (base : p+1=2^b)
    (rem : b%m=u) (period : 2^m%q=1) (large : 1<q)
    (hit : (((2^u-1)%q)^17+d)%q=0) : q ∣ p^17+d := by
  have period' : Nat.ModEq q (2^m) 1 := by change 2^m%q=1%q; rwa [Nat.mod_eq_of_lt large]
  have cyc := seventeen_cycle period' b
  rw [rem,←base] at cyc
  have right : 2^u-1+1=2^u := by have := @Nat.one_le_two_pow u; omega
  have lhs : Nat.ModEq q p (2^u-1) := Nat.ModEq.add_right_cancel' 1 (right ▸ cyc)
  have canonical := lhs.trans (Nat.mod_modEq _ q).symm
  have finish := (canonical.pow 17).add_right d
  exact Nat.modEq_zero_iff_dvd.mp (finish.trans hit)

private theorem seventeen_small_offset_prime {v : ℕ} (h : v ∈ [5,7,11,13,17,19,29,31,37,41,43,61,71,73,109,113,127,211,337,421,1321,14449]) : v.Prime := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num1

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
/-- Twenty-two small-offset tests leave eleven of the 576 reduced
residue classes modulo 2520 for a prime Mersenne index greater than seven. -/
theorem seventeen_coarse_from_eight {p b : ℕ} (pb : b.Prime) (_pp : p.Prime)
    (base : p+1=2^b) (hb : 7<b)
    (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧
      q ∣ p^17+d ∧ s ∣ p^17+d) :
    b%2520 ∈ ([1,361,673,841,1201,1321,1513,1681,1793,1873,2161] : List ℕ) := by
  let rows : List (ℕ × ℕ × ℕ × ℕ × ℕ) := [(4,3,3,5,0),(8,5,3,17,0),(10,9,8,11,31),(10,7,3,11,0),(18,17,2,7,19),(28,9,3,29,0),(84,73,4,29,14449),(70,33,5,11,71),(35,6,3,71,0),(180,113,11,19,61),(180,13,9,19,41),(84,5,8,13,29),(252,101,4,19,29),(420,13,7,29,61),(126,25,23,43,73),(420,281,333,421,1321),(252,229,8,29,37),(252,185,6,37,43),(315,263,49,71,73),(252,221,15,73,113),(1260,641,12,109,211),(21,20,16,127,337)]
  let rems : List ℕ := [1,361,673,841,1201,1321,1513,1681,1793,1873,2161]
  change b%2520 ∈ rems
  have tests : (List.range 2520).all (fun i => decide (i%2=0 ∨ i%3=0 ∨ i%5=0 ∨ i%7=0 ∨ i ∈ rems) ||
      rows.any (fun z => i%z.1 == z.2.1)) = true := by decide +kernel
  have test (i : Fin 2520) (h2 : i.val%2≠0) (h3 : i.val%3≠0) (h5 : i.val%5≠0)
      (h7 : i.val%7≠0) (hm : i.val ∉ rems) : ∃ z ∈ rows, i.val%z.1=z.2.1 := by
    have obs := List.all_eq_true.mp tests i.val (List.mem_range.mpr i.isLt)
    simp only [Bool.or_eq_true,decide_eq_true_eq,List.any_eq_true,beq_iff_eq] at obs
    exact obs.resolve_left (fun t => t.elim h2 (fun t => t.elim h3 (fun t => t.elim h5 (fun t => t.elim h7 hm))))
  have data : ∀ z ∈ rows,
      z.1 ∣ 2520 ∧ z.2.2.2.1 ∈ [5,7,11,13,17,19,29,31,37,41,43,61,71,73,109,113,127,211,337,421,1321,14449] ∧ z.2.2.1+1 < z.2.2.2.1 ∧ 2^z.1%z.2.2.2.1=1 ∧ (((2^z.2.1-1)%z.2.2.2.1)^17+z.2.2.1)%z.2.2.2.1=0 ∧
      ((z.2.2.2.2=0 ∧ z.2.2.1=3 ∧ z.2.2.2.1 ≤ 71) ∨ (z.2.2.2.2 ∈ [5,7,11,13,17,19,29,31,37,41,43,61,71,73,109,113,127,211,337,421,1321,14449] ∧ z.2.2.1+1 < z.2.2.2.2 ∧ z.2.2.2.1≠z.2.2.2.2 ∧ 2^z.1%z.2.2.2.2=1 ∧ (((2^z.2.1-1)%z.2.2.2.2)^17+z.2.2.1)%z.2.2.2.2=0)) := by
    decide +kernel
  by_contra bad
  have ndiv (z : ℕ) (pz : z.Prime) (hz : z≤7) : b%z≠0 := by
    intro h
    have eq := (Nat.prime_dvd_prime_iff_eq pz pb).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  have n2 := ndiv 2 (by decide) (by decide)
  have n3 := ndiv 3 (by decide) (by decide)
  have n5 := ndiv 5 (by decide) (by decide)
  have n7 := ndiv 7 (by decide) (by decide)
  obtain ⟨⟨t,u,d,q,s⟩,mem,rule⟩ := test ⟨b%2520,Nat.mod_lt _ (by decide)⟩
    (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) bad
  obtain ⟨dt,qmem,qb,qo,qHit,rest⟩ := data _ mem
  have pq := seventeen_small_offset_prime qmem
  change b%2520%t=u at rule
  rw [Nat.mod_mod_of_dvd _ dt] at rule
  have dq := seventeen_offset_mod base rule qo pq.one_lt qHit
  rcases rest with ⟨_,rfl,small⟩|⟨smem,sb,ne,so,sHit⟩
  · change q ≤ 71 at small
    change 3+1 < q at qb
    have congr : 2^(b-1) ∣ q-1 := mersenne_four_prime_congruence base (pb.odd_of_ne_two (by omega)) (by omega)
      (by decide : Odd 17) pq qb dq missing
    have low := Nat.le_of_dvd (show 0<q-1 by omega) congr
    have lb := Nat.pow_le_pow_right (by decide : 0<2) (show 7≤b-1 by omega)
    norm_num at lb
    omega
  · have ps := seventeen_small_offset_prime smem
    exact missing ⟨d,q,s,pq,ps,ne,qb,sb,dq,seventeen_offset_mod base rule so ps.one_lt sHit⟩

theorem seventeen_coarse {p b : ℕ} (pb : b.Prime) (pp : p.Prime) (base : p+1=2^b)
    (hb : 131073 < b) (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧
      d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d) :
    b%2520 ∈ ([1,361,673,841,1201,1321,1513,1681,1793,1873,2161] : List ℕ) :=
  seventeen_coarse_from_eight pb pp base (by omega) missing

-- BEGIN SEVENTEEN DIRECT
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem seventeen_direct_prime_list {v : ℕ} (h : v ∈ [61,71,97,103,137,151,193,211,239,281,307,409,433,449,577,613,631,673,919,953,1009,1021,1153,1361,1531,2017,2521,2689,2857,3571,4421,4999,5441,6121,6337,6427,8161,12853,16831,17137,34273,131071]) : v.Prime := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num1

private theorem seventeen_direct_prime {v : ℕ × ℕ} (h : v ∈ [(61,60),(71,35),(97,48),(103,51),(137,68),(151,15),(193,96),(211,210),(239,119),(281,70),(307,102),(409,204),(433,72),(449,224),(577,144),(613,612),(631,45),(673,48),(919,153),(953,68),(1009,504),(1021,340),(1153,288),(1361,680),(1531,1530),(2017,336),(2521,1260),(2689,224),(2857,102),(3571,3570),(4421,340),(4999,357),(5441,544),(6121,1530),(6337,288),(6427,2142),(8161,408),(12853,1428),(16831,765),(17137,2142),(34273,1008),(131071,17)]) :
    v.1.Prime ∧ v.2 ∣ 171360 ∧ 2^v.2%v.1=1 := by
  have t : ∀ z ∈ ([(61,60),(71,35),(97,48),(103,51),(137,68),(151,15),(193,96),(211,210),(239,119),(281,70),(307,102),(409,204),(433,72),(449,224),(577,144),(613,612),(631,45),(673,48),(919,153),(953,68),(1009,504),(1021,340),(1153,288),(1361,680),(1531,1530),(2017,336),(2521,1260),(2689,224),(2857,102),(3571,3570),(4421,340),(4999,357),(5441,544),(6121,1530),(6337,288),(6427,2142),(8161,408),(12853,1428),(16831,765),(17137,2142),(34273,1008),(131071,17)] : List (ℕ × ℕ)), z.1 ∈ [61,71,97,103,137,151,193,211,239,281,307,409,433,449,577,613,631,673,919,953,1009,1021,1153,1361,1531,2017,2521,2689,2857,3571,4421,4999,5441,6121,6337,6427,8161,12853,16831,17137,34273,131071] ∧ z.2 ∣ 171360 ∧ 2^z.2%z.1=1 := by decide +kernel
  obtain ⟨mem,cycle,val⟩ := t _ h
  exact ⟨seventeen_direct_prime_list mem,cycle,val⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem seventeen_direct_or_remaining {b : ℕ} (pb : b.Prime) (hb : 131073 < b)
    (hc : b%2520 ∈ [1,361,673,841,1201,1321,1513,1681,1793,1873,2161]) : (∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ (2^b-1)^17+d ∧ s ∣ (2^b-1)^17+d) ∨ b%171360 ∈ [1,1201,1681,1793,3361,3721,4033,4313,5041,5713,6241,6553,6721,7201,8401,8761,8881,9073,9353,9721,10441,10753,10921,11281,11761,11873,12241,12961,13441,13801,14761,15481,15961,16321,16633,16993,17281,17641,18001,18481,18841,19801,20833,21001,21841,21953,22033,22681,23521,23881,24001,24473,25201,25561,26041,26713,26881,28081,28561,29881,30241,30601,30913,31081,31921,33121,34081,34273,35641,35953,36121,36961,37441,38161,39001,39121,39313,39961,40321,40993,41521,42001,42113,42841,43201,44041,44161,44633,46033,46201,46561,47041,47233,47881,49081,49201,49393,49673,50041,50401,51601,51913,52081,52193,52273,52561,53281,53761,54121,54241,54713,55081,55441,55801,56113,56281,56641,57121,57313,57601,58321,58801,59161,59281,59473,60121,60481,61153,61321,61681,62161,62273,62641,63841,64201,64321,64513,64793,65521,66193,66361,66721,67393,67681,68041,68401,68881,69361,69553,69833,70921,71401,71761,72353,72433,72721,73081,73441,74401,75961,76273,77113,77473,77761,78481,78961,80281,80641,81313,81841,82153,82321,82513,82801,83161,84001,84361,84673,84953,85681,87361,89041,89401,89713,89993,90721,91393,91921,92233,92401,92513,92881,93241,94081,94441,94561,94753,95033,95401,96121,96433,96601,96961,97441,97921,98641,99121,99481,100441,101161,101641,102313,102593,102673,102961,103321,103681,104161,104521,106513,106681,107353,107521,107713,109201,109561,109681,110153,110881,111721,112393,112561,113761,114241,114913,115561,115921,116281,116593,116761,117601,118801,119761,119953,120601,121321,121633,121801,122641,122753,122833,123121,123481,123841,124681,124801,124993,126001,127201,127513,127681,128521,128881,129721,129841,130313,131713,131881,132241,132721,132833,132913,133561,134761,134881,135073,135353,136081,136921,137281,137593,137761,137953,138241,138961,139441,139801,139921,140393,140761,141121,141481,141793,141961,142321,142801,142993,143281,144481,144841,144961,145153,145433,145801,146161,146521,146833,147001,147841,148321,149521,149881,150001,150193,150473,151201,151873,152041,152401,152993,153073,153361,153721,154081,154561,155041,155233,155513,156601,157081,157441,157753,158113,158401,159121,159601,160081,161641,161953,162793,163153,163441,164161,164641,165961,166681,166993,167521,167833,168001,168193,168481,168841,169681,170041,170353,170633] := by
  let coarse : List ℕ := [1,361,673,841,1201,1321,1513,1681,1793,1873,2161]
  let direct : List (ℕ × ℕ × (ℕ × ℕ) × (ℕ × ℕ)) := [(361,86,(97,48),(953,68)),(673,647,(953,68),(1531,1530)),(841,356,(409,204),(1021,340)),(1321,212,(577,144),(673,48)),(1873,7,(61,60),(409,204)),(2161,57,(103,51),(919,153)),(2521,35,(613,612),(17137,2142)),(2881,41,(137,68),(449,224)),(3193,212,(577,144),(673,48)),(3841,1,(103,51),(131071,17)),(4201,212,(577,144),(673,48)),(4393,62,(211,210),(577,144)),(4681,17,(307,102),(449,224)),(5401,169,(211,210),(2857,102)),(5881,1,(103,51),(131071,17)),(6361,212,(577,144),(673,48)),(6833,24,(193,96),(1153,288)),(6913,41,(137,68),(449,224)),(7561,96,(137,68),(1153,288)),(7921,1,(103,51),(131071,17)),(8233,212,(577,144),(673,48)),(9241,212,(577,144),(673,48)),(9433,62,(211,210),(577,144)),(11401,212,(577,144),(673,48)),(11593,112,(151,15),(4421,340)),(11953,57,(103,51),(919,153)),(12601,86,(97,48),(953,68)),(13273,212,(577,144),(673,48)),(13921,266,(281,70),(4421,340)),(14113,7,(61,60),(409,204)),(14281,212,(577,144),(673,48)),(14393,1,(103,51),(307,102)),(14473,62,(211,210),(577,144)),(15121,356,(409,204),(1021,340)),(16441,212,(577,144),(673,48)),(16801,152,(577,144),(1021,340)),(16913,24,(193,96),(1153,288)),(18313,212,(577,144),(673,48)),(18961,213,(433,72),(3571,3570)),(19153,1,(613,612),(1021,340)),(19321,212,(577,144),(673,48)),(19433,441,(577,144),(613,612)),(19513,62,(211,210),(577,144)),(20161,1,(103,51),(131071,17)),(20521,57,(103,51),(919,153)),(21361,442,(577,144),(953,68)),(21481,212,(577,144),(673,48)),(21673,96,(137,68),(1153,288)),(23041,1810,(2857,102),(6121,1530)),(23353,212,(577,144),(673,48)),(24193,57,(103,51),(919,153)),(24553,62,(211,210),(577,144)),(24841,86,(97,48),(953,68)),(25873,112,(151,15),(4421,340)),(26521,212,(577,144),(673,48)),(26993,24,(193,96),(1153,288)),(27073,49,(71,35),(409,204)),(27361,356,(409,204),(1021,340)),(27721,1,(613,612),(3571,3570)),(28393,7,(61,60),(409,204)),(28921,86,(97,48),(953,68)),(29041,152,(577,144),(1021,340)),(29233,704,(1153,288),(4999,357)),(29401,212,(577,144),(673,48)),(29513,10481,(12853,1428),(34273,1008)),(29593,62,(211,210),(577,144)),(31441,356,(409,204),(1021,340)),(31561,212,(577,144),(673,48)),(31753,402,(409,204),(631,45)),(32033,436,(613,612),(1361,680)),(32401,1,(103,51),(131071,17)),(32761,57,(103,51),(919,153)),(33433,212,(577,144),(673,48)),(33601,442,(577,144),(953,68)),(33961,169,(211,210),(2857,102)),(34441,212,(577,144),(673,48)),(34553,701,(919,153),(2857,102)),(34633,62,(211,210),(577,144)),(34921,17,(307,102),(449,224)),(35281,1810,(2857,102),(6121,1530)),(36481,41,(137,68),(449,224)),(36793,436,(449,224),(1361,680)),(37073,24,(193,96),(239,119)),(37153,41,(137,68),(449,224)),(37801,96,(137,68),(1153,288)),(38473,212,(577,144),(673,48)),(39481,212,(577,144),(673,48)),(39673,62,(211,210),(577,144)),(41161,86,(97,48),(953,68)),(41641,212,(577,144),(673,48)),(41833,96,(137,68),(1153,288)),(42193,112,(151,15),(4421,340)),(42481,266,(281,70),(4421,340)),(43513,212,(577,144),(673,48)),(43681,356,(409,204),(1021,340)),(44521,212,(577,144),(673,48)),(44713,7,(61,60),(409,204)),(45001,57,(103,51),(919,153)),(45361,35,(613,612),(17137,2142)),(45721,356,(409,204),(1021,340)),(46681,212,(577,144),(673,48)),(46873,86,(97,48),(953,68)),(47153,24,(193,96),(1153,288)),(47521,1810,(2857,102),(6121,1530)),(48241,169,(211,210),(2857,102)),(48553,212,(577,144),(673,48)),(48721,1,(103,51),(131071,17)),(49561,212,(577,144),(673,48)),(49753,62,(211,210),(577,144)),(50761,1,(103,51),(131071,17)),(51073,389,(2521,1260),(16831,765)),(51241,917,(2689,224),(4421,340)),(51721,212,(577,144),(673,48)),(53593,212,(577,144),(673,48)),(54433,112,(151,15),(4421,340)),(54601,212,(577,144),(673,48)),(54793,62,(211,210),(577,144)),(56761,212,(577,144),(673,48)),(56953,7,(61,60),(409,204)),(57233,1,(103,51),(307,102)),(57961,356,(409,204),(1021,340)),(59641,212,(577,144),(673,48)),(59753,54,(193,96),(409,204)),(59833,62,(211,210),(577,144)),(60841,96,(137,68),(1153,288)),(61801,17,(307,102),(449,224)),(61993,1,(613,612),(1021,340)),(62353,402,(409,204),(631,45)),(63001,1,(103,51),(131071,17)),(63361,57,(103,51),(919,153)),(63673,212,(577,144),(673,48)),(64681,212,(577,144),(673,48)),(64873,62,(211,210),(577,144)),(65881,1810,(2857,102),(6121,1530)),(66841,212,(577,144),(673,48)),(67033,57,(103,51),(919,153)),(67313,24,(193,96),(1153,288)),(68713,212,(577,144),(673,48)),(69721,212,(577,144),(673,48)),(69913,49,(71,35),(409,204)),(70201,356,(409,204),(1021,340)),(70561,1,(613,612),(3571,3570)),(71233,7,(61,60),(409,204)),(71881,212,(577,144),(673,48)),(72073,96,(137,68),(1153,288)),(72241,356,(409,204),(1021,340)),(73753,212,(577,144),(673,48)),(73921,3562,(6337,288),(8161,408)),(74281,356,(409,204),(1021,340)),(74593,402,(409,204),(631,45)),(74761,212,(577,144),(673,48)),(74873,436,(449,224),(613,612)),(75241,1,(103,51),(131071,17)),(75601,57,(103,51),(919,153)),(76441,445,(919,153),(1009,504)),(76801,169,(211,210),(2857,102)),(76921,212,(577,144),(673,48)),(77281,1,(103,51),(131071,17)),(77393,24,(193,96),(1153,288)),(78121,1810,(2857,102),(6121,1530)),(78793,212,(577,144),(673,48)),(79321,1,(103,51),(131071,17)),(79633,35,(613,612),(17137,2142)),(79801,212,(577,144),(673,48)),(79913,143,(409,204),(2017,336)),(79993,62,(211,210),(577,144)),(81001,96,(137,68),(1153,288)),(81961,212,(577,144),(673,48)),(83833,212,(577,144),(673,48)),(84481,356,(409,204),(1021,340)),(84841,212,(577,144),(673,48)),(85033,62,(211,210),(577,144)),(85321,96,(137,68),(1153,288)),(86041,86,(97,48),(953,68)),(86353,647,(953,68),(1531,1530)),(86521,356,(409,204),(1021,340)),(86881,41,(137,68),(449,224)),(87001,212,(577,144),(673,48)),(87473,24,(193,96),(1153,288)),(87553,7,(61,60),(409,204)),(87841,57,(103,51),(919,153)),(88201,35,(613,612),(17137,2142)),(88561,356,(409,204),(1021,340)),(88873,212,(577,144),(673,48)),(89521,1,(103,51),(131071,17)),(89881,212,(577,144),(673,48)),(90073,62,(211,210),(577,144)),(90361,1810,(2857,102),(6121,1530)),(91081,169,(211,210),(2857,102)),(91561,1,(103,51),(131071,17)),(92041,17,(307,102),(449,224)),(92593,1,(613,612),(1021,340)),(93601,41,(137,68),(449,224)),(93913,212,(577,144),(673,48)),(94921,212,(577,144),(673,48)),(95113,62,(211,210),(577,144)),(97081,212,(577,144),(673,48)),(97273,112,(151,15),(4421,340)),(97553,24,(193,96),(1153,288)),(97633,57,(103,51),(919,153)),(98281,86,(97,48),(953,68)),(98953,212,(577,144),(673,48)),(99601,266,(281,70),(4421,340)),(99793,7,(61,60),(409,204)),(99961,212,(577,144),(673,48)),(100073,1,(103,51),(307,102)),(100153,62,(211,210),(577,144)),(100801,356,(409,204),(1021,340)),(102001,2372,(2689,224),(17137,2142)),(102121,212,(577,144),(673,48)),(102481,152,(577,144),(1021,340)),(103993,212,(577,144),(673,48)),(104641,213,(433,72),(3571,3570)),(104833,1,(613,612),(1021,340)),(105001,212,(577,144),(673,48)),(105113,441,(577,144),(613,612)),(105193,62,(211,210),(577,144)),(105481,96,(137,68),(1153,288)),(105841,1,(103,51),(131071,17)),(106201,57,(103,51),(919,153)),(107041,442,(577,144),(953,68)),(107161,212,(577,144),(673,48)),(107633,24,(193,96),(1153,288)),(108361,917,(2689,224),(4421,340)),(108721,1810,(2857,102),(6121,1530)),(109033,212,(577,144),(673,48)),(109873,57,(103,51),(919,153)),(110233,62,(211,210),(577,144)),(110521,86,(97,48),(953,68)),(111241,96,(137,68),(1153,288)),(111553,112,(151,15),(4421,340)),(112201,212,(577,144),(673,48)),(112673,503,(613,612),(5441,544)),(112753,49,(71,35),(409,204)),(113041,356,(409,204),(1021,340)),(113401,1,(613,612),(3571,3570)),(114073,7,(61,60),(409,204)),(114601,86,(97,48),(953,68)),(114721,152,(577,144),(1021,340)),(115081,212,(577,144),(673,48)),(115193,10481,(12853,1428),(34273,1008)),(115273,62,(211,210),(577,144)),(117121,41,(137,68),(449,224)),(117241,212,(577,144),(673,48)),(117433,402,(409,204),(631,45)),(117713,24,(193,96),(1153,288)),(118081,1,(103,51),(131071,17)),(118441,57,(103,51),(919,153)),(119113,212,(577,144),(673,48)),(119281,442,(577,144),(953,68)),(119641,169,(211,210),(2857,102)),(120121,212,(577,144),(673,48)),(120233,701,(919,153),(2857,102)),(120313,62,(211,210),(577,144)),(120961,1810,(2857,102),(6121,1530)),(122161,1,(103,51),(131071,17)),(122473,35,(613,612),(17137,2142)),(124153,212,(577,144),(673,48)),(125161,212,(577,144),(673,48)),(125353,62,(211,210),(577,144)),(125641,481,(2689,224),(6427,2142)),(126673,130,(449,224),(1531,1530)),(126841,86,(97,48),(953,68)),(127321,212,(577,144),(673,48)),(127793,24,(193,96),(1153,288)),(127873,41,(137,68),(449,224)),(128161,266,(281,70),(4421,340)),(129193,212,(577,144),(673,48)),(129361,356,(409,204),(1021,340)),(130201,212,(577,144),(673,48)),(130393,7,(61,60),(409,204)),(130681,57,(103,51),(919,153)),(131041,35,(613,612),(17137,2142)),(131401,356,(409,204),(1021,340)),(132361,212,(577,144),(673,48)),(132553,86,(97,48),(953,68)),(133201,1810,(2857,102),(6121,1530)),(133921,169,(211,210),(2857,102)),(134233,212,(577,144),(673,48)),(134401,1,(103,51),(131071,17)),(135241,212,(577,144),(673,48)),(135433,62,(211,210),(577,144)),(135721,96,(137,68),(1153,288)),(136441,1,(103,51),(131071,17)),(136753,389,(2521,1260),(16831,765)),(137401,212,(577,144),(673,48)),(137873,24,(193,96),(1153,288)),(139273,212,(577,144),(673,48)),(140113,112,(151,15),(4421,340)),(140281,212,(577,144),(673,48)),(140473,62,(211,210),(577,144)),(142441,212,(577,144),(673,48)),(142633,7,(61,60),(409,204)),(142913,1,(103,51),(307,102)),(143641,356,(409,204),(1021,340)),(144001,41,(137,68),(449,224)),(145321,212,(577,144),(673,48)),(145513,62,(211,210),(577,144)),(147361,3562,(6337,288),(8161,408)),(147481,212,(577,144),(673,48)),(147673,1,(613,612),(1021,340)),(147953,24,(193,96),(1153,288)),(148033,402,(409,204),(631,45)),(148681,1,(103,51),(131071,17)),(149041,57,(103,51),(919,153)),(149353,212,(577,144),(673,48)),(150361,212,(577,144),(673,48)),(150553,62,(211,210),(577,144)),(151561,1810,(2857,102),(6121,1530)),(152521,212,(577,144),(673,48)),(152713,57,(103,51),(919,153)),(154393,212,(577,144),(673,48)),(155401,212,(577,144),(673,48)),(155593,49,(71,35),(409,204)),(155881,356,(409,204),(1021,340)),(156241,1,(613,612),(3571,3570)),(156913,7,(61,60),(409,204)),(157561,212,(577,144),(673,48)),(157921,356,(409,204),(1021,340)),(158033,24,(193,96),(1153,288)),(158761,96,(137,68),(1153,288)),(159433,212,(577,144),(673,48)),(159961,356,(409,204),(1021,340)),(160273,402,(409,204),(631,45)),(160441,212,(577,144),(673,48)),(160553,436,(613,612),(1361,680)),(160921,1,(103,51),(131071,17)),(161281,57,(103,51),(919,153)),(162121,445,(919,153),(1009,504)),(162481,169,(211,210),(2857,102)),(162601,212,(577,144),(673,48)),(162961,1,(103,51),(131071,17)),(163073,701,(919,153),(2857,102)),(163801,1810,(2857,102),(6121,1530)),(164473,212,(577,144),(673,48)),(165001,1,(103,51),(131071,17)),(165313,35,(613,612),(17137,2142)),(165481,212,(577,144),(673,48)),(165593,143,(409,204),(2017,336)),(165673,62,(211,210),(577,144)),(166321,704,(1153,288),(4999,357)),(167641,212,(577,144),(673,48)),(169513,212,(577,144),(673,48)),(170161,356,(409,204),(1021,340)),(170521,212,(577,144),(673,48)),(170713,62,(211,210),(577,144)),(171001,266,(281,70),(4421,340))]
  let hard : List ℕ := [1,1201,1681,1793,3361,3721,4033,4313,5041,5713,6241,6553,6721,7201,8401,8761,8881,9073,9353,9721,10441,10753,10921,11281,11761,11873,12241,12961,13441,13801,14761,15481,15961,16321,16633,16993,17281,17641,18001,18481,18841,19801,20833,21001,21841,21953,22033,22681,23521,23881,24001,24473,25201,25561,26041,26713,26881,28081,28561,29881,30241,30601,30913,31081,31921,33121,34081,34273,35641,35953,36121,36961,37441,38161,39001,39121,39313,39961,40321,40993,41521,42001,42113,42841,43201,44041,44161,44633,46033,46201,46561,47041,47233,47881,49081,49201,49393,49673,50041,50401,51601,51913,52081,52193,52273,52561,53281,53761,54121,54241,54713,55081,55441,55801,56113,56281,56641,57121,57313,57601,58321,58801,59161,59281,59473,60121,60481,61153,61321,61681,62161,62273,62641,63841,64201,64321,64513,64793,65521,66193,66361,66721,67393,67681,68041,68401,68881,69361,69553,69833,70921,71401,71761,72353,72433,72721,73081,73441,74401,75961,76273,77113,77473,77761,78481,78961,80281,80641,81313,81841,82153,82321,82513,82801,83161,84001,84361,84673,84953,85681,87361,89041,89401,89713,89993,90721,91393,91921,92233,92401,92513,92881,93241,94081,94441,94561,94753,95033,95401,96121,96433,96601,96961,97441,97921,98641,99121,99481,100441,101161,101641,102313,102593,102673,102961,103321,103681,104161,104521,106513,106681,107353,107521,107713,109201,109561,109681,110153,110881,111721,112393,112561,113761,114241,114913,115561,115921,116281,116593,116761,117601,118801,119761,119953,120601,121321,121633,121801,122641,122753,122833,123121,123481,123841,124681,124801,124993,126001,127201,127513,127681,128521,128881,129721,129841,130313,131713,131881,132241,132721,132833,132913,133561,134761,134881,135073,135353,136081,136921,137281,137593,137761,137953,138241,138961,139441,139801,139921,140393,140761,141121,141481,141793,141961,142321,142801,142993,143281,144481,144841,144961,145153,145433,145801,146161,146521,146833,147001,147841,148321,149521,149881,150001,150193,150473,151201,151873,152041,152401,152993,153073,153361,153721,154081,154561,155041,155233,155513,156601,157081,157441,157753,158113,158401,159121,159601,160081,161641,161953,162793,163153,163441,164161,164641,165961,166681,166993,167521,167833,168001,168193,168481,168841,169681,170041,170353,170633]
  change _ ∨ b%171360 ∈ hard
  have cb : (b%171360).Coprime 171360 := by
    change Nat.gcd (b%171360) 171360=1
    rw [←Nat.gcd_rec 171360 b,Nat.gcd_comm]
    apply pb.coprime_iff_not_dvd.mpr
    intro bad
    have mem := pb.mem_primeFactors bad (by decide)
    have tab : (171360:ℕ).primeFactors = {2,3,5,7,17} := by decide +kernel
    rw [tab] at mem
    simp only [Finset.mem_insert,Finset.mem_singleton] at mem
    omega
  have ck : (b%171360)%2520 ∈ coarse := by rw [Nat.mod_mod_of_dvd _ (by decide : 2520 ∣ 171360)]; exact hc
  have test : coarse.all (fun k => (List.range 68).all (fun u =>
      let i := k+2520*u
      !decide (i.Coprime 171360) || direct.any (fun row => row.1 == i) || decide (i ∈ hard))) = true := by decide +kernel
  have idx (k : ℕ) (hk : k ∈ coarse) (u : ℕ) (hu : u ∈ List.range 68)
      (co : (k+2520*u).Coprime 171360) : (∃ row ∈ direct, row.1=k+2520*u) ∨ k+2520*u ∈ hard := by
    have t := List.all_eq_true.mp (List.all_eq_true.mp test k hk) u hu
    simp only [Bool.or_eq_true,List.any_eq_true,decide_eq_true_eq,beq_iff_eq] at t
    rcases t with (bad|good)|remaining
    · rw [decide_eq_true co] at bad
      contradiction
    · exact Or.inl good
    · exact Or.inr remaining
  have lift : (b%171360)%2520+2520*((b%171360)/2520)=b%171360 := Nat.mod_add_div _ _
  have hits := idx _ ck _ (List.mem_range.mpr (show (b%171360)/2520 < 68 by omega)) (lift.symm ▸ cb)
  rw [lift] at hits
  rcases hits with ⟨⟨k,d,x,y⟩,mem,ek⟩ | hv
  · left
    change k=b%171360 at ek
    have data : ∀ z ∈ direct,
        z.2.2.1 ∈ [(61,60),(71,35),(97,48),(103,51),(137,68),(151,15),(193,96),(211,210),(239,119),(281,70),(307,102),(409,204),(433,72),(449,224),(577,144),(613,612),(631,45),(673,48),(919,153),(953,68),(1009,504),(1021,340),(1153,288),(1361,680),(1531,1530),(2017,336),(2521,1260),(2689,224),(2857,102),(3571,3570),(4421,340),(4999,357),(5441,544),(6121,1530),(6337,288),(6427,2142),(8161,408),(12853,1428),(16831,765),(17137,2142),(34273,1008),(131071,17)] ∧ z.2.2.2 ∈ [(61,60),(71,35),(97,48),(103,51),(137,68),(151,15),(193,96),(211,210),(239,119),(281,70),(307,102),(409,204),(433,72),(449,224),(577,144),(613,612),(631,45),(673,48),(919,153),(953,68),(1009,504),(1021,340),(1153,288),(1361,680),(1531,1530),(2017,336),(2521,1260),(2689,224),(2857,102),(3571,3570),(4421,340),(4999,357),(5441,544),(6121,1530),(6337,288),(6427,2142),(8161,408),(12853,1428),(16831,765),(17137,2142),(34273,1008),(131071,17)] ∧ z.2.2.1.1≠z.2.2.2.1 ∧ z.2.1+1 < z.2.2.1.1 ∧ z.2.1+1 < z.2.2.2.1 ∧
        (((2^(z.1%z.2.2.1.2)-1)%z.2.2.1.1)^17+z.2.1)%z.2.2.1.1=0 ∧ (((2^(z.1%z.2.2.2.2)-1)%z.2.2.2.1)^17+z.2.1)%z.2.2.2.1=0 := by decide +kernel
    obtain ⟨px,py,ne,hx,hy,dx,dy⟩ := data _ mem
    have div (v : ℕ × ℕ) (hv : v ∈ [(61,60),(71,35),(97,48),(103,51),(137,68),(151,15),(193,96),(211,210),(239,119),(281,70),(307,102),(409,204),(433,72),(449,224),(577,144),(613,612),(631,45),(673,48),(919,153),(953,68),(1009,504),(1021,340),(1153,288),(1361,680),(1531,1530),(2017,336),(2521,1260),(2689,224),(2857,102),(3571,3570),(4421,340),(4999,357),(5441,544),(6121,1530),(6337,288),(6427,2142),(8161,408),(12853,1428),(16831,765),(17137,2142),(34273,1008),(131071,17)]) (h : (((2^(k%v.2)-1)%v.1)^17+d)%v.1=0) :
        v.1 ∣ (2^b-1)^17+d := by
      have ⟨pr,period,pow⟩ := seventeen_direct_prime hv
      rw [ek,Nat.mod_mod_of_dvd _ period] at h
      exact seventeen_index_divisor pr pow h
    exact ⟨d,x.1,y.1,(seventeen_direct_prime px).1,(seventeen_direct_prime py).1,ne,hx,hy,div x px dx,div y py dy⟩
  · right
    exact hv

private theorem seventeen_index_prime {p b : ℕ} (pp : p.Prime) (base : p+1=2^b) : b.Prime := by
  have ep : p=2^b-1 := by omega
  have b1 : b≠1 := by rintro rfl; norm_num at base; have := pp.two_le; omega
  exact (Nat.prime_of_pow_sub_one_prime b1 (ep ▸ pp)).2

/-- A surviving seventeenth-power case has a large index in one of eleven residue classes. -/
theorem seventeen_surviving_index {p b : ℕ} (pp : p.Prime) (base : p+1=2^b)
    (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p^17+d ∧ s ∣ p^17+d) : 131073 < b ∧ b%2520 ∈ [1,361,673,841,1201,1321,1513,1681,1793,1873,2161] := by
  have pb := seventeen_index_prime pp base
  have hi : 131073 < b := by
    by_contra! small
    have ep : p=2^b-1 := by omega
    exact missing (ep ▸ seventeen_bounded_witness pb small)
  exact ⟨hi,seventeen_coarse pb pp base hi missing⟩

/-- Direct witnesses eliminate 347 of the 704 possible lifts of the eleven index classes. -/
theorem seventeen_surviving_lift {p b : ℕ} (pp : p.Prime) (base : p+1=2^b)
    (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p^17+d ∧ s ∣ p^17+d) : 131073 < b ∧ (∃ z ∈ ([(1,151424057718062388869),(361,145667772990363991280),(673,93751790033793536276),(841,202901096132581285882),(1201,227989676659606258431),(1321,12297791404224717320),(1513,247474687640128234574),(1681,74171282362119574805),(1793,151805376059737309979),(1873,98093190462001381696),(2161,135450721927820790012)] : List (ℕ × ℕ)), b%2520=z.1 ∧ z.2.testBit (b%171360/2520)=true) := by
  obtain ⟨hi,co⟩ := seventeen_surviving_index pp base missing
  have pb := seventeen_index_prime pp base
  rcases seventeen_direct_or_remaining pb hi co with w|rem
  · have ep : p=2^b-1 := by omega
    exact (missing (ep ▸ w)).elim
  · have cert : ∀ k ∈ ([1,1201,1681,1793,3361,3721,4033,4313,5041,5713,6241,6553,6721,7201,8401,8761,8881,9073,9353,9721,10441,10753,10921,11281,11761,11873,12241,12961,13441,13801,14761,15481,15961,16321,16633,16993,17281,17641,18001,18481,18841,19801,20833,21001,21841,21953,22033,22681,23521,23881,24001,24473,25201,25561,26041,26713,26881,28081,28561,29881,30241,30601,30913,31081,31921,33121,34081,34273,35641,35953,36121,36961,37441,38161,39001,39121,39313,39961,40321,40993,41521,42001,42113,42841,43201,44041,44161,44633,46033,46201,46561,47041,47233,47881,49081,49201,49393,49673,50041,50401,51601,51913,52081,52193,52273,52561,53281,53761,54121,54241,54713,55081,55441,55801,56113,56281,56641,57121,57313,57601,58321,58801,59161,59281,59473,60121,60481,61153,61321,61681,62161,62273,62641,63841,64201,64321,64513,64793,65521,66193,66361,66721,67393,67681,68041,68401,68881,69361,69553,69833,70921,71401,71761,72353,72433,72721,73081,73441,74401,75961,76273,77113,77473,77761,78481,78961,80281,80641,81313,81841,82153,82321,82513,82801,83161,84001,84361,84673,84953,85681,87361,89041,89401,89713,89993,90721,91393,91921,92233,92401,92513,92881,93241,94081,94441,94561,94753,95033,95401,96121,96433,96601,96961,97441,97921,98641,99121,99481,100441,101161,101641,102313,102593,102673,102961,103321,103681,104161,104521,106513,106681,107353,107521,107713,109201,109561,109681,110153,110881,111721,112393,112561,113761,114241,114913,115561,115921,116281,116593,116761,117601,118801,119761,119953,120601,121321,121633,121801,122641,122753,122833,123121,123481,123841,124681,124801,124993,126001,127201,127513,127681,128521,128881,129721,129841,130313,131713,131881,132241,132721,132833,132913,133561,134761,134881,135073,135353,136081,136921,137281,137593,137761,137953,138241,138961,139441,139801,139921,140393,140761,141121,141481,141793,141961,142321,142801,142993,143281,144481,144841,144961,145153,145433,145801,146161,146521,146833,147001,147841,148321,149521,149881,150001,150193,150473,151201,151873,152041,152401,152993,153073,153361,153721,154081,154561,155041,155233,155513,156601,157081,157441,157753,158113,158401,159121,159601,160081,161641,161953,162793,163153,163441,164161,164641,165961,166681,166993,167521,167833,168001,168193,168481,168841,169681,170041,170353,170633] : List ℕ), ∃ z ∈ ([(1,151424057718062388869),(361,145667772990363991280),(673,93751790033793536276),(841,202901096132581285882),(1201,227989676659606258431),(1321,12297791404224717320),(1513,247474687640128234574),(1681,74171282362119574805),(1793,151805376059737309979),(1873,98093190462001381696),(2161,135450721927820790012)] : List (ℕ × ℕ)),
        k%2520=z.1 ∧ z.2.testBit (k/2520)=true := by decide +kernel
    have h := cert _ rem
    rw [Nat.mod_mod_of_dvd _ (by decide : 2520 ∣ 171360)] at h
    exact ⟨hi,h⟩

/-- A solution cannot immediately precede any nontrivial fifth, seventh, eleventh or thirteenth power. -/
theorem fifth_seventh_eleventh_thirteenth_exclusion {n x r : ℕ} (hx : 1 < x) (hr : r=5 ∨ r=7 ∨ r=11 ∨ r=13)
    (eq : n+1=x^r) : v_l 1 n ≠ 1 := by
  intro sol
  have rp : 1 < r := by omega
  have ro : Odd r := by rcases hr with rfl|rfl|rfl|rfl <;> decide
  have bound : 32 ≤ x^r := by
    have a := Nat.pow_le_pow_left (show 2 ≤ x by omega) r
    rcases hr with rfl|rfl|rfl|rfl <;> norm_num at a <;> omega
  have ox : Odd x := by
    apply Nat.not_even_iff_odd.mp
    intro ex
    have dd : 2 ∣ x^r := (even_iff_two_dvd.mp ex).trans (dvd_pow_self x (by omega))
    have on : Odd n := by rw [Nat.odd_iff]; omega
    rcases (odd_classification on).mp sol with h|h|h|h <;> omega
  obtain ⟨b,base⟩ := odd_power_root_neighbor ox hx ro rp eq sol
  have pure := prime_power_succ (n:=n) (by omega) sol
  rw [eq,isPrimePow_pow_iff (by omega : r≠0)] at pure
  obtain ⟨p,e,pp,pe,he⟩ := (isPrimePow_nat_iff _).mp pure
  have op := pp.odd_of_ne_two (by
    rintro rfl
    have div := dvd_pow_self (2:ℕ) pe.ne'
    rw [he] at div
    exact (Nat.not_even_iff_odd.mpr ox) (even_iff_two_dvd.mpr div))
  have one := mersenne_power_exponent op pp.one_lt pe (he.symm ▸ base)
  rw [one,pow_one] at he
  subst x
  have hit : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p^r+d ∧ s ∣ p^r+d := by
    rcases hr with rfl|rfl|rfl|rfl
    · exact mersenne_fifth_witness pp base
    · exact mersenne_seventh_witness pp base
    · exact mersenne_eleventh_witness pp base
    · exact mersenne_thirteenth_witness pp base
  obtain ⟨d,q,s,pq,ps,ne,hq,hs,dq,ds⟩ := hit
  have rearr : n+(d+1)=p^r+d := by omega
  exact two_primes (k:=d+1) (by omega) pq ps ne hq hs (rearr ▸ dq) (rearr ▸ ds) sol

theorem fifth_seventh_eleventh_exclusion {n x r : ℕ} (hx : 1 < x) (hr : r=5 ∨ r=7 ∨ r=11)
    (eq : n+1=x^r) : v_l 1 n ≠ 1 :=
  fifth_seventh_eleventh_thirteenth_exclusion hx (by omega) eq

theorem fifth_seventh_exclusion {n x r : ℕ} (hx : 1 < x) (hr : r=5 ∨ r=7)
    (eq : n+1=x^r) : v_l 1 n ≠ 1 :=
  fifth_seventh_eleventh_exclusion hx (hr.elim Or.inl (fun h => Or.inr (Or.inl h))) eq

private theorem odd_power_cannot_precede_prime_power {x r : ℕ} (hx : 3 ≤ x)
    (ex : Even x) (ro : Odd r) (hr : 3 ≤ r) : ¬IsPrimePow (x^r+1) := by
  intro pure
  have grow (j : ℕ) : (j+2)*(x+1) ≤ x^(j+2) := by
    induction j with
    | zero =>
      change 2*(x+1) ≤ x^2
      nlinarith [Nat.mul_le_mul_right x hx]
    | succ j ih =>
      have le : j+3 ≤ (j+2)*x := by
        have hb := Nat.mul_le_mul_left (j+2) hx
        omega
      have a := Nat.mul_le_mul_right (x+1) le
      have b := Nat.mul_le_mul_right x ih
      rw [show j+1+2=(j+2)+1 by omega,pow_succ]
      nlinarith only [a,b]
  have g := grow (r-2)
  rw [show r-2+2=r by omega] at g
  have d : x+1 ∣ x^r+1 := by simpa using (ro.nat_add_dvd_pow_add_pow (x:=x) (y:=1))
  obtain ⟨c,fac⟩ := d
  have hc : r < c := by
    by_contra! small
    have h := Nat.mul_le_mul_left (x+1) small
    nlinarith only [h,g,fac]
  obtain ⟨q,e,pq,_,eq⟩ := (isPrimePow_nat_iff _).mp pure
  have facq : (x+1)*c=q^e := fac.symm.trans eq.symm
  obtain ⟨a,_,ea⟩ := (Nat.dvd_prime_pow pq).mp (facq ▸ dvd_mul_right (x+1) c)
  obtain ⟨b,_,eb⟩ := (Nat.dvd_prime_pow pq).mp (facq ▸ dvd_mul_left c (x+1))
  have ap : a ≠ 0 := by rintro rfl; simp at ea; omega
  have dq : q ∣ x+1 := ea ▸ dvd_pow_self q ap
  have oq := pq.odd_of_ne_two (by
    rintro rfl
    obtain ⟨t,ht⟩ := ex
    omega)
  have nx : ¬q ∣ x := by
    intro dx
    have d1 := (Nat.dvd_add_iff_right dx).mpr dq
    have := Nat.le_of_dvd Nat.one_pos d1
    have := pq.two_le
    omega
  let _ : Fact q.Prime := ⟨pq⟩
  have v := padicValNat.pow_add_pow (x:=x) (y:=1) oq dq nx ro
  rw [one_pow,fac,padicValNat.mul (by omega) (by omega)] at v
  have val : padicValNat q c=padicValNat q r := by omega
  have power : q^(padicValNat q c)=c := by
    conv_lhs => arg 2; rw [eb,padicValNat.prime_pow]
    exact eb.symm
  have cd : c ∣ r := by rw [←power,val]; exact pow_padicValNat_dvd
  exact (Nat.not_le_of_gt hc) (Nat.le_of_dvd (by omega) cd)

private theorem even_fourth_power_excluded {x : ℕ} (hx : 2 < x) (ex : Even x) :
    v_l 1 (x^4) ≠ 1 := by
  obtain ⟨u,hu⟩ := ex
  let z := u-1
  have xz : x=2*(z+1) := by dsimp [z]; omega
  let L := 2*z^2+2*z+1
  let R := 2*z^2+6*z+5
  have zl : 1 ≤ z := by omega
  have f : x^4+4=4*L*R := by rw [xz]; dsimp [L,R]; ring
  have lb : 2 ≤ L := by dsimp [L]; omega
  have rb : 2 ≤ R := by dsimp [R]; omega
  obtain ⟨p,pp,dp⟩ := Nat.exists_prime_and_dvd (show L ≠ 1 by omega)
  obtain ⟨q,pq,dq⟩ := Nat.exists_prime_and_dvd (show R ≠ 1 by omega)
  have no3 : ¬3 ∣ L ∧ ¬3 ∣ R := by
    have m := (Nat.mod_modEq z 3).symm
    have ml := (((m.pow 2).mul_left 2).add (m.mul_left 2)).add_right 1
    have mr := (((m.pow 2).mul_left 2).add (m.mul_left 6)).add_right 5
    change L%3=_ at ml
    change R%3=_ at mr
    have h := Nat.mod_lt z (by decide : 0<3)
    simp only [Nat.dvd_iff_mod_eq_zero,ml,mr]
    interval_cases e : z%3 <;> decide
  have high (t : ℕ) (pt : t.Prime) (dv : t ∣ L ∨ t ∣ R) : 4<t := by
    by_contra! small
    have choices : t=2 ∨ t=3 := by interval_cases t <;> norm_num at *
    rcases choices with rfl|rfl
    · rcases dv with h|h <;> dsimp [L,R] at h <;> omega
    · tauto
  have ph := high p pp (Or.inl dp)
  have qh := high q pq (Or.inr dq)
  have diff : R=L+4*(z+1) := by dsimp [R,L]; ring
  have ne : p≠q := by
    rintro rfl
    rw [diff] at dq
    have dd := (Nat.dvd_add_iff_right dp).mpr dq
    have dz := pp.dvd_mul.mp dd |>.resolve_left (by
      intro bad
      have := Nat.le_of_dvd (by decide : 0<4) bad
      omega)
    have ll : L=2*z*(z+1)+1 := by dsimp [L]; ring
    rw [ll] at dp
    have d1 := (Nat.dvd_add_iff_right (dvd_mul_of_dvd_right dz (2*z))).mpr dp
    have := Nat.le_of_dvd Nat.one_pos d1
    omega
  exact two_primes (k:=4) (by decide) pp pq ne ph qh
    (f ▸ dvd_mul_of_dvd_left (dvd_mul_of_dvd_right dp 4) _) (f ▸ dvd_mul_of_dvd_right dq _)

private theorem odd_actual_power {x r : ℕ} (hx : 1<x) (hr : 3≤r) (ro : Odd r)
    (sol : v_l 1 (x^r)=1) : x^r=8 := by
  have pos : 0 < x^r := Nat.pow_pos (by omega)
  have pure := prime_power_succ pos sol
  rcases Nat.even_or_odd x with ex|ox
  · by_cases eq : x=2
    · subst x
      rcases prime_power_neighbor (by omega) pure with h|⟨t,ht⟩
      · simp [h]
      · have t0 : t≠0 := by rintro rfl; norm_num at ht; omega
        have d2 := dvd_pow_self (2:ℕ) t0
        obtain ⟨w,hw⟩ := ro
        omega
    · exact False.elim (odd_power_cannot_precede_prime_power (by omega) ex ro hr pure)
  · have high : 27 ≤ x^r := by
      have three : 3 ≤ x := by obtain ⟨t,ht⟩ := ox; omega
      exact (Nat.pow_le_pow_left three 3).trans (Nat.pow_le_pow_right (by omega) hr)
    rcases (odd_classification ox.pow).mp sol with h|h|h|h <;> omega

/-- The only positive solutions that are perfect powers of exponent at least three are 8 and 16. -/
theorem higher_perfect_power {x r : ℕ} (hx : 1<x) (hr : 3≤r) :
    v_l 1 (x^r)=1 ↔ x^r=8 ∨ x^r=16 := by
  constructor
  · intro sol
    by_cases four : 4 ∣ r
    · obtain ⟨j,hj⟩ := four
      let y := x^j
      have eq : x^r=y^4 := by dsimp [y]; rw [hj,←pow_mul,Nat.mul_comm]
      rw [eq] at sol ⊢
      have hy : 1<y := Nat.one_lt_pow (by omega : j ≠ 0) hx
      rcases Nat.even_or_odd y with ev|od
      · have small : y≤2 := by by_contra! large; exact even_fourth_power_excluded large ev sol
        right
        rw [show y=2 by omega]
        decide
      · have large : 81 ≤ y^4 := Nat.pow_le_pow_left (show 3≤y by obtain ⟨t,ht⟩ := od; omega) 4
        rcases (odd_classification od.pow).mp sol with h|h|h|h <;> omega
    · left
      rcases Nat.even_or_odd r with ⟨j,hj⟩|ro
      · have oj : Odd j := by rw [Nat.odd_iff]; omega
        have eq : x^r=(x^2)^j := by rw [hj,←pow_mul,two_mul]
        rw [eq] at sol ⊢
        exact odd_actual_power (Nat.one_lt_pow (by decide : 2≠0) hx) (by omega) oj sol
      · exact odd_actual_power hx hr ro sol
  · rintro (h|h) <;> rw [h] <;> apply (solutions_through_330 (by decide) (by decide)).mpr <;> decide +kernel


private theorem solution_prime_power_factor {n k c : ℕ} (sol : v_l 1 n = 1)
    (hk : 0 < k) (hc : 2 ≤ c) (div : c ∣ n+k)
    (eligible : ∀ p : ℕ, p.Prime → p ∣ c → k < p) : IsPrimePow c := by
  by_contra bad
  obtain ⟨p, hp, q, hq, different⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le hc).mp bad
  obtain ⟨pp, dp, _⟩ := Nat.mem_primeFactors.mp hp
  obtain ⟨pq, dq, _⟩ := Nat.mem_primeFactors.mp hq
  exact two_primes hk pp pq different (eligible p pp dp) (eligible q pq dq)
    (dp.trans div) (dq.trans div) sol

/-- All powers of two which attain the lowercase supremum one. -/
theorem power_two_solution {n b : ℕ} (hn : n=2^b) :
    v_l 1 n = 1 ↔ n=1 ∨ n=2 ∨ n=4 ∨ n=8 ∨ n=16 := by
  constructor
  · intro sol
    have bound : b ≤ 4 := by
      by_contra! eb
      have pp := prime_power_succ (n:=n) (by rw [hn]; positivity) sol
      rw [hn] at pp
      obtain ⟨t,ht⟩ := (prime_power_neighbor (by omega) pp).resolve_left (by omega)
      have tp : t≠0 := by rintro rfl; simp at ht; omega
      have evenb : 2 ∣ b := ht ▸ dvd_pow_self 2 tp
      let a := b-1
      have ha : b=a+1 := by dsimp [a]; omega
      have ea : 2 ∣ 2^a := dvd_pow_self _ (by omega)
      have mid : n+2=2*(2^a+1) := by rw [hn,ha,pow_succ]; ring
      have pp2 : IsPrimePow (2^a+1) :=
        solution_prime_power_factor sol (k:=2) (by decide) (by have := @Nat.one_le_two_pow a; omega)
          (mid ▸ dvd_mul_left _ _) (by
            intro q pq dq
            have := pq.two_le
            by_contra! low
            have eq : q=2 := by omega
            rw [eq] at dq
            omega)
      obtain ⟨u,hu⟩ := (prime_power_neighbor (by omega) pp2).resolve_left (by omega)
      have up : u≠0 := by rintro rfl; simp at hu; omega
      have evena : 2 ∣ a := hu ▸ dvd_pow_self 2 up
      omega
    interval_cases b <;> norm_num at hn <;> omega
  · rintro (rfl|rfl|rfl|rfl|rfl) <;> apply (solutions_through_330 (by decide) (by decide)).mpr <;> decide

private theorem shifted_double_orbit {n t s k p q r : ℕ} (hn : n+2=2*2^(2^t))
    (j : ℕ) (ht : t=s+12*j) (hk : 0<k)
    (pp : p.Prime) (pq : q.Prime) (ne : p≠q) (hp : k<p) (hq : k<q)
    (base : Nat.ModEq (p*q) (2^(2^s)) r) (period : Nat.ModEq (p*q) (r^4096) r)
    (hit : Nat.ModEq (p*q) (2*r+k) 2) : v_l 1 n ≠ 1 := by
  have orbit (i : ℕ) : Nat.ModEq (p*q) (2^(2^(s+12*i))) r := by
    induction i with
    | zero => simpa using base
    | succ i ih =>
      rw [show s+12*(i+1)=(s+12*i)+12 by omega,pow_add,pow_mul]
      calc
        _ ≡ r^(2^12) [MOD p*q] := ih.pow (2^12)
        _ ≡ r [MOD p*q] := by rw [show (2:ℕ)^12=4096 by decide]; exact period
  have cover := (((orbit j).mul_left 2).add_right k).trans hit
  rw [←ht,←hn,show n+2+k=(n+k)+2 by omega] at cover
  have d := Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_right_cancel' 2 (b:=0) cover)
  exact two_primes hk pp pq ne hp hq ((dvd_mul_right p q).trans d) ((dvd_mul_left q p).trans d)

set_option maxRecDepth 16384 in
private theorem shifted_double_exclusion {n t : ℕ} (hn : n+2=2*2^(2^t)) (ht : 3≤t) :
    v_l 1 n ≠ 1 := by
  let j := (t-3)/12
  have classes : t=3+12*j ∨ t=4+12*j ∨ t=5+12*j ∨ t=6+12*j ∨ t=7+12*j ∨ t=8+12*j ∨ t=9+12*j ∨ t=10+12*j ∨ t=11+12*j ∨ t=12+12*j ∨ t=13+12*j ∨ t=14+12*j := by
    dsimp [j]; omega
  rcases classes with h|h|h|h|h|h|h|h|h|h|h|h
  · apply shifted_double_orbit (k:=1) (p:=7) (q:=73) (r:=256) hn j h <;> decide +kernel
  · apply shifted_double_orbit (k:=10) (p:=29) (q:=113) (r:=3273) hn j h <;> decide +kernel
  · apply shifted_double_orbit (k:=10) (p:=13) (q:=41) (r:=529) hn j h <;> decide +kernel
  · apply shifted_double_orbit (k:=6) (p:=19) (q:=43) (r:=815) hn j h <;> decide +kernel
  · apply shifted_double_orbit (k:=10) (p:=13) (q:=29) (r:=373) hn j h <;> decide +kernel
  · apply shifted_double_orbit (k:=9) (p:=13) (q:=79) (r:=510) hn j h <;> decide +kernel
  · apply shifted_double_orbit (k:=1) (p:=7) (q:=73) (r:=256) hn j h <;> decide +kernel
  · apply shifted_double_orbit (k:=11) (p:=19) (q:=41) (r:=385) hn j h <;> decide +kernel
  · apply shifted_double_orbit (k:=7) (p:=11) (q:=53) (r:=289) hn j h <;> decide +kernel
  · apply shifted_double_orbit (k:=6) (p:=11) (q:=19) (r:=207) hn j h <;> decide +kernel
  · apply shifted_double_orbit (k:=10) (p:=13) (q:=29) (r:=373) hn j h <;> decide +kernel
  · apply shifted_double_orbit (k:=34) (p:=241) (q:=433) (r:=104337) hn j h <;> decide +kernel

private theorem shifted_even_exclusion {n j : ℕ} (hn : n+2=2^(j+j)) (hj : 2 ≤ j) :
    v_l 1 n ≠ 1 := by
  let x := 2^j
  have large : 4≤x := Nat.pow_le_pow_right (by decide : 0 < 2) hj
  have evenx : 2 ∣ x := dvd_pow_self 2 (by omega)
  have sq : n+2=x*x := by simpa [x,pow_add] using hn
  have fac : n+1=(x-1)*(x+1) := by
    have u : x-1+1=x := by omega
    nlinarith
  let p := (x-1).minFac
  let q := (x+1).minFac
  have pp : p.Prime := Nat.minFac_prime (by omega)
  have pq : q.Prime := Nat.minFac_prime (by omega)
  have dp : p ∣ x-1 := Nat.minFac_dvd _
  have dq : q ∣ x+1 := Nat.minFac_dvd _
  have ne : p≠q := by
    intro e
    rw [←e] at dq
    have diff := Nat.dvd_sub dq dp
    rw [show x+1-(x-1)=2 by omega] at diff
    have := Nat.le_of_dvd (by decide) diff
    have := pp.two_le
    have eq : p=2 := by omega
    rw [eq] at dq
    omega
  exact two_primes (k:=1) (by decide) pp pq ne pp.one_lt pq.one_lt
    (fac ▸ dvd_mul_of_dvd_left dp _) (fac ▸ dvd_mul_of_dvd_right dq _)

/-- All positive solutions two below a power of two. -/
theorem two_below_power_two_solution {n b : ℕ} (pos : 0<n) (hn : n+2=2^b) :
    v_l 1 n=1 ↔ n=2 ∨ n=6 ∨ n=30 := by
  constructor
  · intro sol
    have b2 : 2≤b := by by_contra! low; interval_cases b <;> norm_num at hn <;> omega
    rcases Nat.even_or_odd b with ⟨j,hj⟩ | ⟨j,hj⟩
    · by_cases large : 2 ≤ j
      · exact False.elim (shifted_even_exclusion (hj ▸ hn) large sol)
      · have j1 : j=1 := by omega
        rw [hj,j1] at hn
        norm_num at hn
        omega
    · let a := 2*j
      have ha : b=a+1 := hj
      have ea : 2 ∣ 2^a := dvd_pow_self _ (by omega)
      have m3 : 2^a%3=1 := by
        change Nat.ModEq 3 (2^a) 1
        have c : Nat.ModEq 3 (2^2) 1 := by decide
        have u := c.pow j
        simpa only [a,pow_mul,one_pow] using u
      have adj : n+4=2*(2^a+1) := by rw [ha,pow_succ] at hn; omega
      have pp : IsPrimePow (2^a+1) :=
        solution_prime_power_factor sol (k:=4) (by decide) (by have := @Nat.one_le_two_pow a; omega)
          (adj ▸ dvd_mul_left _ _) (by
            intro q pq dq
            by_contra! lq
            have choices : q=2 ∨ q=3 := by interval_cases q <;> norm_num at *
            rcases choices with rfl|rfl <;> omega)
      obtain ⟨t,ht⟩ := (prime_power_neighbor (by omega) pp).resolve_left (by dsimp [a]; omega)
      have expr : n+2=2*2^(2^t) := by rw [ha,pow_succ,ht] at hn; simpa [Nat.mul_comm] using hn
      have small : t≤2 := by by_contra! large; exact shifted_double_exclusion expr large sol
      interval_cases t <;> norm_num at expr <;> omega
  · rintro (rfl|rfl|rfl) <;> apply (solutions_through_330 (by decide) (by decide)).mpr <;> decide

private theorem shifted_prime_above_three {m : ℕ} (hm : 1 < m) (oddm : ¬2 ∣ m)
    (ex : ∀ e : ℕ, m≠3^e) : ∃ p : ℕ, p.Prime ∧ 3<p ∧ p ∣ m := by
  by_contra! none
  exact ex _ (Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
    intro p pp dp
    have low : p ≤ 3 := by by_contra! big; exact none p pp big dp
    have := pp.two_le
    by_contra different
    have e : p=2 := by omega
    exact oddm (e ▸ dp)))

private theorem shifted_plus_not_three {j e : ℕ} (hj : 4≤j) : 2^j+1≠3^e := by
  intro eq
  have ep : e≠0 := by
    rintro rfl
    have := @Nat.one_le_two_pow j
    simp at eq
  have primepower : IsPrimePow (2^j+1) := (isPrimePow_nat_iff _).mpr
    ⟨3,e,Nat.prime_three,Nat.pos_of_ne_zero ep,eq.symm⟩
  obtain ⟨t,ht⟩ := (prime_power_neighbor (by omega) primepower).resolve_left (by omega)
  have tn : t≠0 := by rintro rfl; simp at ht; omega
  obtain ⟨u,hu⟩ : 2 ∣ j := ht ▸ dvd_pow_self 2 tn
  have red : Nat.ModEq 3 (2^j) 1 := by
    rw [hu,pow_mul]
    have m : Nat.ModEq 3 (2^2) 1 := by decide
    simpa only [one_pow] using m.pow u
  change 2^j%3=1 at red
  have d : 3 ∣ 2^j+1 := eq ▸ dvd_pow_self _ ep
  omega

/-- All positive solutions four below a power of two. -/
theorem four_below_power_two_solution {n b : ℕ} (pos : 0<n) (hn : n+4=2^b) :
    v_l 1 n=1 ↔ n=4 ∨ n=12 ∨ n=60 := by
  constructor
  · intro sol
    have bound : b≤6 := by
      by_contra! large
      let j := b/2
      let x := 2^j
      have j3 : 3≤j := by dsimp [j]; omega
      have xl : 8≤x := Nat.pow_le_pow_right (by decide : 0 < 2) j3
      have xe : 8 ∣ x := pow_dvd_pow (2:ℕ) j3
      have e0 : ¬2 ∣ x-1 := by omega
      have e1 : ¬2 ∣ x+1 := by omega
      have disjoint {p q : ℕ} (hp : 2<p) (dp : p ∣ x-1) (dq : q ∣ x+1) : p≠q := by
        rintro rfl
        have d := Nat.dvd_sub dq dp
        rw [show x+1-(x-1)=2 by omega] at d
        have := Nat.le_of_dvd (by decide) d
        omega
      have fac : x*x=(x-1)*(x+1)+1 := by
        have h : x-1+1=x := by omega
        nlinarith
      by_cases evenb : b=2*j
      · have j4 : 4≤j := by omega
        have shifted : n+3=(x-1)*(x+1) := by
          rw [evenb,Nat.mul_comm 2 j,pow_mul,pow_two] at hn
          change n+4=x*x at hn
          omega
        obtain ⟨p,pp,hp,dp⟩ := shifted_prime_above_three (m:=x-1) (by omega) e0 (by
          intro e eq
          have rr : 3^e%8=1 ∨ 3^e%8=3 := three_pow_mod_eight e
          omega)
        obtain ⟨q,pq,hq,dq⟩ := shifted_prime_above_three (m:=x+1) (by omega) e1
          (fun _ => shifted_plus_not_three j4)
        exact two_primes (k:=3) (by decide) pp pq (disjoint (by omega) dp dq) hp hq
          (shifted ▸ dvd_mul_of_dvd_left dp _) (shifted ▸ dvd_mul_of_dvd_right dq _) sol
      · have oddb : b=2*j+1 := by dsimp [j] at *; omega
        have shifted : n+2=2*((x-1)*(x+1)) := by
          rw [oddb,pow_succ,Nat.mul_comm 2 j,pow_mul,pow_two] at hn
          change n+4=x*x*2 at hn
          omega
        let p := (x-1).minFac
        let q := (x+1).minFac
        have pp : p.Prime := Nat.minFac_prime (by omega)
        have pq : q.Prime := Nat.minFac_prime (by omega)
        have dp : p ∣ x-1 := Nat.minFac_dvd _
        have dq : q ∣ x+1 := Nat.minFac_dvd _
        have hp : 2<p := by
          have := pp.two_le
          by_contra! low
          have eq : p=2 := by omega
          exact e0 (eq ▸ dp)
        have hq : 2<q := by
          have := pq.two_le
          by_contra! low
          have eq : q=2 := by omega
          exact e1 (eq ▸ dq)
        exact two_primes (k:=2) (by decide) pp pq (disjoint hp dp dq) hp hq
          (shifted ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_left dp _) _)
          (shifted ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_right dq _) _) sol
    have bad : n≠28 := by
      rintro rfl
      have m := (solutions_through_330 (n:=28) (by decide) (by decide)).mp sol
      exact (by decide : 28 ∉ ([1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,30,36,42,46,
        48,60,70,78,80,96,120,190,222,330] : List ℕ)) m
    interval_cases b <;> norm_num at hn <;> omega
  · rintro (rfl|rfl|rfl) <;> apply (solutions_through_330 (by decide) (by decide)).mpr <;> decide

private theorem binary_cofactor_at {n k : ℕ} (hk : 0<k) (ev : 2 ∣ n+k)
    (notpure : ∀ e : ℕ, n+k≠2^e) (sol : v_l 1 n=1)
    (eligible : ∀ q : ℕ, q.Prime → q≠2 → q ∣ n+k → k<q) :
    ∃ q a b : ℕ, q.Prime ∧ k<q ∧ 0<a ∧ 0<b ∧ n+k=2^a*q^b := by
  let N := n+k
  let a := N.factorization 2
  let m := N/2^a
  have nz : N≠0 := by dsimp [N]; omega
  have fac : 2^a*m=N := Nat.ordProj_mul_ordCompl_eq_self N 2
  have dm : m ∣ n+k := Nat.ordCompl_dvd N 2
  have pos : 0 < m := Nat.ordCompl_pos 2 nz
  have oddm : ¬2 ∣ m := Nat.not_dvd_ordCompl Nat.prime_two nz
  have ap : 0<a := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two nz).mp ev
  have m2 : 2 ≤ m := by
    by_contra! small
    have one : m=1 := by omega
    exact notpure a (by simpa only [one,mul_one] using fac.symm)
  have ok (q : ℕ) (pq : q.Prime) (dq : q ∣ m) : k<q :=
    eligible q pq (by rintro rfl; exact oddm dq) (dq.trans dm)
  have pure := solution_prime_power_factor sol hk m2 dm ok
  obtain ⟨q,b,pq,bp,rep⟩ := (isPrimePow_nat_iff _).mp pure
  have dq : q ∣ m := rep ▸ dvd_pow_self q bp.ne'
  exact ⟨q,a,b,pq,ok q pq dq,ap,bp,by rw [rep]; exact fac.symm⟩

/-- The odd parts of both even neighbors p+1 and p+3 are nontrivial prime powers. -/
theorem prime_successor_survivor {n p : ℕ} (pp : p.Prime) (eq : n+1=p)
    (large : 60<n) (sol : v_l 1 n=1) :
    (∀ e : ℕ, p ≠ 2^e+1) ∧ ∃ q r a b c d : ℕ,
      q.Prime ∧ r.Prime ∧ 2<q ∧ 3<r ∧ q≠r ∧ 0<a ∧ 0<b ∧ 0<c ∧ 0<d ∧
      (a=1 ∨ c=1) ∧ p+1=2^a*q^b ∧ p+3=2^c*r^d := by
  have oddp := pp.odd_of_ne_two (by omega)
  obtain ⟨u,hu⟩ := oddp
  constructor
  · intro e he
    have claim := (power_two_solution (n:=n) (b:=e) (by omega)).mp sol
    omega
  · have no2 (e : ℕ) : n+2≠2^e := by
      intro he
      have small := (two_below_power_two_solution (by omega) he).mp sol
      omega
    have no4 (e : ℕ) : n+4≠2^e := by
      intro he
      have small := (four_below_power_two_solution (by omega) he).mp sol
      omega
    obtain ⟨q,a,b,pq,qbig,ap,bp,fa⟩ := binary_cofactor_at (by decide : 0<2)
      (by omega) no2 sol (by intro z pz nz _; have := pz.two_le; omega)
    obtain ⟨r,c,d,pr,rbig,cp,dp,fc⟩ := binary_cofactor_at (by decide : 0<4)
      (by omega) no4 sol (by
        intro z pz nz dz
        by_contra! small
        have z3 : z=3 := by interval_cases z <;> norm_num at *
        rw [z3] at dz
        have d3 : 3 ∣ p := by omega
        have bad := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pp).mp d3
        omega)
    have neq : q≠r := by
      rintro rfl
      have d2 : q ∣ n+2 := fa ▸ dvd_mul_of_dvd_right (dvd_pow_self q bp.ne') _
      have d4 : q ∣ n+4 := fc ▸ dvd_mul_of_dvd_right (dvd_pow_self q dp.ne') _
      have diff := Nat.dvd_sub d4 d2
      rw [show n+4-(n+2)=2 by omega] at diff
      have := Nat.le_of_dvd (by decide) diff
      omega
    have one : a=1 ∨ c=1 := by
      by_contra! bad
      have da : 4 ∣ n+2 := fa ▸ dvd_mul_of_dvd_left (pow_dvd_pow (2:ℕ) (show 2≤a by omega)) _
      have dc : 4 ∣ n+4 := fc ▸ dvd_mul_of_dvd_left (pow_dvd_pow (2:ℕ) (show 2≤c by omega)) _
      omega
    exact ⟨q,r,a,b,c,d,pq,pr,qbig,by omega,neq,ap,bp,cp,dp,one,by omega,by omega⟩


open NumberField


private theorem eisenstein_model : Nonempty ((QuadraticAlgebra ℤ (-1) (-1)) ≃ₐ[ℤ] 𝓞 (CyclotomicField 3 ℚ)) := by
  let _ : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) := CyclotomicField.isCyclotomicExtension 3 ℚ
  let z := IsCyclotomicExtension.zeta 3 ℚ (CyclotomicField 3 ℚ)
  have hz : IsPrimitiveRoot z 3 := IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ)
  let w := hz.toInteger
  have sq : w*w=(-1:ℤ) • (1:𝓞 (CyclotomicField 3 ℚ))+(-1:ℤ) • w := by
    have h := IsCyclotomicExtension.Rat.Three.eta_sq hz
    change w^2 = -w-1 at h
    simp only [neg_smul,one_smul]
    linear_combination h
  let f : (QuadraticAlgebra ℤ (-1) (-1)) →ₐ[ℤ] 𝓞 (CyclotomicField 3 ℚ) := QuadraticAlgebra.lift ⟨w,sq⟩
  have inj : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).2
    intro x hx
    have e := congrArg f (QuadraticAlgebra.algebraMap_norm_eq_mul_star x)
    rw [AlgHom.commutes,map_mul,hx,zero_mul] at e
    have en : x.norm=0 := by
      change (x.norm : 𝓞 (CyclotomicField 3 ℚ))=0 at e
      exact_mod_cast e
    change x.re*x.re+(-1)*x.re*x.im-(-1)*x.im*x.im=0 at en
    ext
    · change x.re=0
      nlinarith [sq_nonneg (x.re-2*x.im),sq_nonneg x.re, sq_nonneg x.im]
    · change x.im=0
      nlinarith [sq_nonneg (2*x.re-x.im),sq_nonneg x.re,sq_nonneg x.im]
  have surj : Function.Surjective f := by
    let _ : IsCyclotomicExtension {3^1} ℚ (CyclotomicField 3 ℚ) := by norm_num; infer_instance
    let B := (show IsPrimitiveRoot z (3^1) from hz).integralPowerBasisOfPrimePow
    have hg : B.gen=w := IsPrimitiveRoot.integralPowerBasisOfPrimePow_gen _
    have incl : Algebra.adjoin ℤ ({B.gen} : Set (𝓞 (CyclotomicField 3 ℚ))) ≤ f.range := by
      apply Algebra.adjoin_le
      intro v hv
      obtain rfl := Set.mem_singleton_iff.mp hv
      exact ⟨QuadraticAlgebra.omega,by simp [f,QuadraticAlgebra.lift,hg]⟩
    rw [B.adjoin_gen_eq_top] at incl
    exact fun t => incl (show t ∈ (⊤ : Subalgebra ℤ (𝓞 (CyclotomicField 3 ℚ))) by trivial)
  exact ⟨AlgEquiv.ofBijective f ⟨inj,surj⟩⟩

private theorem eisenstein_unit_six (u : (𝓞 (CyclotomicField 3 ℚ))ˣ) : (u : 𝓞 (CyclotomicField 3 ℚ))^6=1 := by
  let _ : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) := CyclotomicField.isCyclotomicExtension 3 ℚ
  let z := IsCyclotomicExtension.zeta 3 ℚ (CyclotomicField 3 ℚ)
  have hz : IsPrimitiveRoot z 3 := IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ)
  have mem := IsCyclotomicExtension.Rat.Three.Units.mem hz u
  let w := hz.toInteger
  have h3 : w^3=1 := hz.toInteger_cube_eq_one
  have h6 : w^6=1 := by rw [show 6=3*2 by decide,pow_mul,h3,one_pow]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [Units.val_one,Units.val_neg,Units.val_pow_eq_pow_val,IsUnit.unit_spec,one_pow,Even.neg_pow (by decide : Even 6)]
  all_goals first | exact h6 | change (w^2)^6=1; rw [←pow_mul, Nat.mul_comm, pow_mul,h6,one_pow]

private theorem eisenstein_extract {x y z : (QuadraticAlgebra ℤ (-1) (-1))} {d : ℕ} (pd : d.Prime) (hd : 3 < d)
    (cop : IsCoprime x y) (prod : x*y=z^d) : ∃ a : (QuadraticAlgebra ℤ (-1) (-1)), a^d=x := by
  obtain ⟨f⟩ := eisenstein_model
  let _ : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) := CyclotomicField.isCyclotomicExtension 3 ℚ
  let _ : IsPrincipalIdealRing (𝓞 (CyclotomicField 3 ℚ)) := IsCyclotomicExtension.Rat.three_pid (CyclotomicField 3 ℚ)
  obtain ⟨a,u,hu⟩ := exists_associated_pow_of_mul_eq_pow' (cop.map f.toRingHom)
    (show f x*f y=(f z)^d by rw [←map_mul,prod,map_pow])
  have h6 := eisenstein_unit_six u
  have od := pd.odd_of_ne_two (by omega)
  have nd3 : ¬3 ∣ d := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pd).mp h
    omega
  obtain ⟨j,hj⟩ := od
  have key (e : ℕ) (he : e%6=1) : (u : 𝓞 (CyclotomicField 3 ℚ))^e=u := by
    have rep : e=e%6+6*(e/6) := (Nat.mod_add_div _ _).symm
    conv_lhs => rw [rep,pow_add,pow_mul,he,h6,one_pow,mul_one,pow_one]
  have root : ∃ v : 𝓞 (CyclotomicField 3 ℚ), v^d=u := by
    rcases (show d%6=1 ∨ d%6=5 by omega) with h|h
    · exact ⟨u,key d h⟩
    · exact ⟨(u : 𝓞 (CyclotomicField 3 ℚ))^5,by rw [←pow_mul]; exact key _ (by omega)⟩
  obtain ⟨v,hv⟩ := root
  refine ⟨f.symm (a*v),f.injective ?_⟩
  rw [map_pow,AlgEquiv.apply_symm_apply,mul_pow,hv,hu]
  rfl

private theorem eisenstein_im_dvd (v : (QuadraticAlgebra ℤ (-1) (-1))) (n : ℕ) : v.im ∣ (v^n).im := by
  induction n with
  | zero => simp [QuadraticAlgebra.im_one]
  | succ n ih =>
    rw [pow_succ,QuadraticAlgebra.im_mul]
    exact dvd_add (dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_left ih _)) (dvd_mul_left _ _)

/-- A prime square plus three cannot be four times a nontrivial power
with prime exponent larger than three. -/
theorem square_plus_three_exclusion {p y d : ℕ} (pp : p.Prime) (hp : 3 < p)
    (pd : d.Prime) (hd : 3 < d) (hy : 1 < y) (eq : p^2+3=4*y^d) : False := by
  obtain ⟨w,hw⟩ := pp.odd_of_ne_two (by omega)
  let α : (QuadraticAlgebra ℤ (-1) (-1)) := ⟨(w:ℤ)+1,1⟩
  have pw : (p:ℤ)=2*(w:ℤ)+1 := by exact_mod_cast hw
  have ppow : (p:ℤ)^2+3=4*(y:ℤ)^d := by exact_mod_cast eq
  have tr : α+star α=(p:(QuadraticAlgebra ℤ (-1) (-1))) := by
    ext <;> simp [α]
    omega
  have diff : (α-star α)^2=(-3:(QuadraticAlgebra ℤ (-1) (-1))) := by
    ext <;> simp [α,pow_two,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]
  have normα : α.norm=(y:ℤ)^d := by
    simp [α,QuadraticAlgebra.norm_def]
    rw [pw] at ppow
    nlinarith
  have copZ : IsCoprime (p:ℤ) 3 := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    change p.Coprime 3
    exact pp.coprime_iff_not_dvd.mpr (by intro h; have := Nat.le_of_dvd (by decide : 0<3) h; omega)
  obtain ⟨u,v,uv⟩ := copZ
  have cop : IsCoprime α (star α) := by
    refine ⟨(u:(QuadraticAlgebra ℤ (-1) (-1)))-v*(α-star α),(u:(QuadraticAlgebra ℤ (-1) (-1)))+v*(α-star α),?_⟩
    calc
      _ = (u:(QuadraticAlgebra ℤ (-1) (-1)))*(α+star α)-v*(α-star α)^2 := by ring
      _ = 1 := by rw [tr,diff]; simpa using (show (u:(QuadraticAlgebra ℤ (-1) (-1)))*(p:(QuadraticAlgebra ℤ (-1) (-1)))+(v:(QuadraticAlgebra ℤ (-1) (-1)))*3=1 by exact_mod_cast uv)
  have prod : α*star α=(y:(QuadraticAlgebra ℤ (-1) (-1)))^d := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star,normα,map_pow]
    rfl
  obtain ⟨a,ha⟩ := eisenstein_extract pd hd cop prod
  have idiv := eisenstein_im_dvd a d
  rw [ha] at idiv
  change a.im ∣ 1 at idiv
  have absim : a.im.natAbs=1 := by
    obtain ⟨k,hk⟩ := idiv
    apply Nat.dvd_one.mp
    exact ⟨k.natAbs,by simpa [Int.natAbs_mul] using congrArg Int.natAbs hk⟩
  have ims : a.im^2=1 := by
    have hh := congrArg (fun t : ℕ => (t:ℤ)^2) absim
    simpa [Int.natCast_natAbs,sq_abs] using hh
  let S : ℤ := 2*a.re-a.im
  have ts : a+star a=(S:(QuadraticAlgebra ℤ (-1) (-1))) := by
    ext
    · change a.re+(a.re+(-1)*a.im)=2*a.re-a.im
      ring
    · change a.im+ -a.im=0
      omega
  have ad := (pd.odd_of_ne_two (by omega)).add_dvd_pow_add_pow a (star a)
  rw [ts,←star_pow,ha,tr] at ad
  obtain ⟨k,hk⟩ := ad
  have div : S ∣ (p:ℤ) := ⟨k.re,by simpa using congrArg QuadraticAlgebra.re hk⟩
  have absdiv : S.natAbs ∣ p := by
    obtain ⟨b,hb⟩ := div
    exact ⟨b.natAbs,by simpa [Int.natAbs_mul] using congrArg Int.natAbs hb⟩
  have nform : 4*a.norm=S^2+3 := by
    simp only [QuadraticAlgebra.norm_def,S]
    linear_combination 3*ims
  have hn : a.norm^d=(y:ℤ)^d := by rw [←map_pow,ha,normα]
  have ybig : (1:ℤ)<(y:ℤ)^d := one_lt_pow₀ (by exact_mod_cast hy) pd.ne_zero
  have big : 1 < a.norm := by
    by_contra! le
    have pos : 0 < a.norm := by nlinarith [sq_nonneg S]
    have one : a.norm=1 := by omega
    rw [one,one_pow] at hn
    omega
  have gt : a.norm < a.norm^d := by simpa using pow_lt_pow_right₀ big (show 1 < d by omega)
  have hs : (S.natAbs:ℤ)^2=S^2 := by rw [Int.natCast_natAbs,sq_abs]
  rcases (Nat.dvd_prime pp).mp absdiv with one|same
  · rw [one] at hs
    norm_num at hs
    omega
  · rw [same] at hs
    nlinarith

/-- For a surviving prime square, the third cofactor's odd exponent must be a power of three. -/
theorem square_third_exponent {p r b : ℕ} (pp : p.Prime) (hp : 3 < p)
    (hr : 1 < r) (ob : Odd b) (eq : p^2+3=4*r^b) :
    ∃ k : ℕ, b=3^k := by
  obtain ⟨w,hw⟩ := ob
  refine ⟨_,Nat.eq_prime_pow_of_unique_prime_dvd (by omega) ?_⟩
  intro d pd dd
  by_contra ne
  have d2 : d≠2 := by rintro rfl; omega
  have big : 3 < d := by have := pd.two_le; omega
  obtain ⟨j,hj⟩ := dd
  have jp : j ≠ 0 := by rintro rfl; simp at hj; omega
  apply square_plus_three_exclusion pp hp pd big (Nat.one_lt_pow jp hr)
  rw [←pow_mul,Nat.mul_comm j d,←hj,eq]


private theorem gaussian_unit_four (u : GaussianIntˣ) : (u:GaussianInt)^4=1 := by
  have un := (Zsqrtd.norm_eq_one_iff' (by decide : (-1:ℤ)≤0) (u:GaussianInt)).mpr u.isUnit
  generalize (u:GaussianInt)=v at un ⊢
  obtain ⟨a,b⟩ := v
  change a*a-(-1)*b*b=1 at un
  have a₁ : -1 ≤ a := by nlinarith [sq_nonneg b]
  have a₂ : a ≤ 1 := by nlinarith [sq_nonneg b]
  have b₁ : -1 ≤ b := by nlinarith [sq_nonneg a]
  have b₂ : b ≤ 1 := by nlinarith [sq_nonneg a]
  interval_cases a <;> interval_cases b <;> norm_num at un
  all_goals decide +kernel

private theorem gaussian_odd_root {u : GaussianInt} (hu : u^4=1) {d : ℕ} (od : Odd d) :
    ∃ v : GaussianInt, v^d=u := by
  obtain ⟨w,hw⟩ := od
  have key (e : ℕ) (he : e%4=1) : u^e=u := by
    have rep : e=e%4+4*(e/4) := (Nat.mod_add_div _ _).symm
    conv_lhs => rw [rep,pow_add,pow_mul,he,hu,one_pow,mul_one,pow_one]
  rcases (show d%4=1 ∨ d%4=3 by omega) with h|h
  · exact ⟨u,key _ h⟩
  · exact ⟨u^3,by rw [←pow_mul]; exact key _ (by omega)⟩

private theorem gaussian_primitive_divisor {t : ℤ} {p k : ℕ} (ht : ¬2 ∣ t)
    (div : t ∣ (2:ℤ)^k*p) : t.natAbs ∣ p := by
  obtain ⟨h,hh⟩ := div
  have dn : t.natAbs ∣ 2^k*p := ⟨h.natAbs,by simpa [Int.natAbs_mul,Int.natAbs_pow] using congrArg Int.natAbs hh⟩
  have odd : Odd t.natAbs := by rw [Nat.odd_iff]; omega
  exact ((Nat.coprime_two_right.mpr odd).pow_right k).dvd_of_dvd_mul_left dn

private theorem gaussian_im_dvd (v : GaussianInt) (n : ℕ) : v.im ∣ (v^n).im := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,Zsqrtd.im_mul]
    exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_left ih _)

/-- A prime square plus one cannot be twice a nontrivial odd power of an odd number. -/
theorem square_plus_one_odd_exclusion {p y d : ℕ} (pp : p.Prime) (hp : 2 < p)
    (hy : 1 < y) (oy : Odd y) (hd : 1 < d) (od : Odd d) (eq : p^2+1=2*y^d) : False := by
  obtain ⟨w,hw⟩ := pp.odd_of_ne_two (by omega)
  obtain ⟨k,hk⟩ := od
  let I : GaussianInt := ⟨0,1⟩
  let A : GaussianInt := ⟨(w:ℤ)+1,-(w:ℤ)⟩
  have I2 : I^2=-1 := by decide +kernel
  have pair : A+I*star A=1+I := by ext <;> simp [I,A]
  have pcast : (p:ℤ)=2*(w:ℤ)+1 := by exact_mod_cast hw
  have eqZ : (p:ℤ)^2+1=2*(y:ℤ)^d := by exact_mod_cast eq
  have An : A.norm=(y:ℤ)^d := by
    rw [pcast] at eqZ
    simp [A,Zsqrtd.norm_def]
    nlinarith
  have prod : A*star A=(y:GaussianInt)^d := by rw [←Zsqrtd.norm_eq_mul_conj,An]; push_cast; rfl
  have Iprod : (1+I)*(1-I)=2 := by linear_combination -I2
  have cop : IsCoprime A (star A) := by
    obtain ⟨l,hl⟩ : Odd (y^d) := oy.pow
    have oddZ : (y:GaussianInt)^d = 2*(l:GaussianInt)+1 := by exact_mod_cast hl
    refine ⟨star A-(l:GaussianInt)*(1-I),-(l:GaussianInt)*(1-I)*I,?_⟩
    calc
      _ = A*star A-(l:GaussianInt)*((A+I*star A)*(1-I)) := by ring
      _ = 1 := by rw [prod,oddZ,pair,Iprod]; ring
  obtain ⟨z,u,hu⟩ := exists_associated_pow_of_mul_eq_pow' cop prod
  have ii : (-I)^4=1 := by decide +kernel
  have ui : ((u:GaussianInt)*(-I)^k)^4=1 := by
    rw [mul_pow,gaussian_unit_four,one_mul,←pow_mul,Nat.mul_comm,pow_mul,ii,one_pow]
  obtain ⟨v,hv⟩ := gaussian_odd_root ui (show Odd d from ⟨k,hk⟩)
  let h := z*v
  have hpow : h^d=(-I)^k*A := by dsimp [h]; rw [mul_pow,hv,←hu]; ring
  let θ := (1+I)*h
  have prodA : (1+I)*A=(p:GaussianInt)+I := by
    ext <;> simp [I,A]
    all_goals omega
  have scale : ((1+I)^2)*(-I)=2 := by decide +kernel
  have θpow : θ^d=(((2:ℤ)^k : ℤ):GaussianInt)*((p:GaussianInt)+I) := by
    dsimp [θ]
    rw [mul_pow,hpow,hk,pow_succ,pow_mul]
    push_cast
    calc
      _ = (((1+I)^2)*(-I))^k*((1+I)*A) := by rw [mul_pow]; ring
      _ = _ := by rw [scale,prodA]
  have hnorm : h.norm=(y:ℤ) := by
    apply (show Odd d from ⟨k,hk⟩).pow_injective
    change Zsqrtd.normMonoidHom h ^ d = _
    rw [←map_pow,hpow,map_mul,map_pow]
    change (-I).norm^k*A.norm=_
    rw [show (-I).norm=1 by decide +kernel,one_pow,one_mul,An]
  have θnorm : θ.norm=2*(y:ℤ) := by
    dsimp [θ]
    rw [Zsqrtd.norm_mul,hnorm,show (1+I).norm=2 by decide +kernel]
  have sumsq : θ.re^2+θ.im^2=2*(y:ℤ) := by
    rw [←θnorm,Zsqrtd.norm_def]; ring
  have par : θ.re=h.re-h.im ∧ θ.im=h.re+h.im := by
    constructor
    · simp [θ,I,sub_eq_add_neg]
    · simp [θ,I,add_comm]
  have notboth : ¬(2 ∣ θ.re ∧ 2 ∣ θ.im) := by
    rintro ⟨⟨a,ha⟩,b,hb⟩
    have div : (4:ℤ) ∣ 2*(y:ℤ) := ⟨a^2+b^2,by rw [←sumsq,ha,hb]; ring⟩
    obtain ⟨m,hm⟩ := oy
    omega
  have oi : ¬2 ∣ θ.im := by omega
  have or' : ¬2 ∣ θ.re := by omega
  have imag := gaussian_im_dvd θ d
  have rpow : (θ^d).re=(2:ℤ)^k*p := by
    rw [θpow,Zsqrtd.re_mul,Zsqrtd.re_intCast,Zsqrtd.im_intCast]
    simp [I]
  have ipow : (θ^d).im=(2:ℤ)^k := by
    rw [θpow,Zsqrtd.im_mul,Zsqrtd.re_intCast,Zsqrtd.im_intCast]
    simp [I]
  rw [ipow] at imag
  have imag' : θ.im ∣ (2:ℤ)^k*1 := by simpa using imag
  have absI : θ.im.natAbs=1 := Nat.dvd_one.mp (gaussian_primitive_divisor (p:=1) oi imag')
  have real : θ.re ∣ (2:ℤ)^k*p := by
    have dv := (show Odd d from ⟨k,hk⟩).add_dvd_pow_add_pow θ (star θ)
    obtain ⟨s,hs⟩ := dv
    rw [←star_pow] at hs
    refine ⟨s.re,?_⟩
    have cc := congrArg Zsqrtd.re hs
    simp only [Zsqrtd.re_mul,Zsqrtd.re_add,Zsqrtd.im_add,Zsqrtd.re_star,Zsqrtd.im_star,rpow] at cc
    nlinarith only [cc]
  have absR := gaussian_primitive_divisor or' real
  have isq : θ.im^2=1 := by
    have he := congrArg (fun t:ℕ => (t:ℤ)^2) absI
    simpa [Int.natCast_natAbs,sq_abs] using he
  have hs : (θ.re.natAbs:ℤ)^2=θ.re^2 := by rw [Int.natCast_natAbs,sq_abs]
  rcases (Nat.dvd_prime pp).mp absR with one|same
  · rw [one] at hs
    norm_num at hs
    omega
  · rw [same] at hs
    have gt : (y:ℤ) < (y:ℤ)^d := by simpa using pow_lt_pow_right₀ (show (1:ℤ)<y by exact_mod_cast hy) hd
    nlinarith

/-- In the surviving square branch the first prime cofactor has exponent one or two. -/
theorem square_first_exponent {p q a : ℕ} (pp : p.Prime) (hp : 2 < p) (oq : Odd q)
    (hq : 1 < q) (ap : 0 < a) (no4 : ¬4 ∣ a) (eq : p^2+1=2*q^a) : a=1 ∨ a=2 := by
  have pure : a=2^a.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd ap.ne' (by
    intro d pd dd
    by_contra ne
    obtain ⟨j,hj⟩ := dd
    have jpos : j ≠ 0 := by rintro rfl; simp at hj; omega
    apply square_plus_one_odd_exclusion pp hp (Nat.one_lt_pow jpos hq) oq.pow pd.one_lt (pd.odd_of_ne_two ne)
    rw [←pow_mul,Nat.mul_comm j d,←hj,eq])
  generalize a.primeFactorsList.length=e at pure
  have low : e < 2 := by
    by_contra! he
    exact no4 (pure ▸ pow_dvd_pow (2:ℕ) he)
  interval_cases e <;> simp_all


private theorem square_cube_mersenne {p x : ℕ} (pp : p.Prime) (large : 7 ≤ x)
    (residue : x%3=1) (eqn : p^2+3=4*x^3)
    (none : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p^2+d ∧ s ∣ p^2+d) : ∃ j : ℕ, x+1=2^j := by
  have high : 7 < p := by
    by_contra! low
    have hp := Nat.pow_le_pow_left low 2
    have hx := Nat.pow_le_pow_left large 3
    norm_num at hp hx
    omega
  have no7 : ¬7 ∣ p^2+7 := by
    intro h
    have dv := (by decide : Nat.Prime 7).dvd_of_dvd_pow (show 7 ∣ p^2 by omega)
    have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 7) pp).mp dv
    omega
  let t := x-1
  have xt : x=t+1 := by dsimp [t]; omega
  let F (z : ℕ) := z^2+z+1
  have fc {m i j : ℕ} (h : Nat.ModEq m i j) : Nat.ModEq m (F i) (F j) :=
    ((h.pow 2).add h).add_right 1
  have fac : p^2+7=4*((x+1)*F t) := by
    have h : x^3+1=(x+1)*F t := by rw [xt]; dsimp [F]; ring
    omega
  have dm : F t ∣ p^2+7 := fac ▸ (dvd_mul_left _ _).trans (dvd_mul_left _ 4)
  have dl : x+1 ∣ p^2+7 := fac ▸ (dvd_mul_right _ _).trans (dvd_mul_left _ 4)
  have fpos : 1 < F t := by dsimp [F]; omega
  obtain ⟨s,ps,ds⟩ := Nat.exists_prime_and_dvd fpos.ne'
  have sb : 8 < s := by
    by_contra! low
    have tab : ∀ i : Fin 9, i.val.Prime → ∀ z : Fin i.val,
        F z.val%i.val=0 → i.val=3 ∨ i.val=7 := by decide +kernel
    have c := fc (Nat.mod_modEq t s)
    change F (t%s)%s=F t%s at c
    have cases := tab ⟨s,by omega⟩ ps ⟨t%s,Nat.mod_lt _ ps.pos⟩ (c.trans (Nat.mod_eq_zero_of_dvd ds))
    rcases cases with h|h
    · change s=3 at h
      subst s
      have tt : Nat.ModEq 3 t 0 := by change t%3=0; omega
      have cm := fc tt
      change F t%3=1 at cm
      omega
    · change s=7 at h
      subst s
      exact no7 (ds.trans dm)
  have sep : ¬s ∣ x+1 := by
    intro d
    have ident : F t+3*(x+1)=3+(x+1)*(x+1) := by rw [xt]; dsimp [F]; ring
    have h := dvd_add ds (dvd_mul_of_dvd_right d 3)
    rw [ident] at h
    have d3 := (Nat.dvd_add_iff_left (dvd_mul_of_dvd_left d _)).mpr h
    have := Nat.le_of_dvd (by decide : 0<3) d3
    omega
  have no5 : ¬5 ∣ x+1 := by
    have tab : ∀ a b : Fin 5, (a.val^2+3)%5=(4*b.val^3)%5 → (b.val+1)%5≠0 := by decide +kernel
    have a := ((Nat.mod_modEq p 5).pow 2).add_right 3
    have b := ((Nat.mod_modEq x 5).pow 3).mul_left 4
    have e := (Nat.mod_modEq x 5).add_right 1
    change ((p%5)^2+3)%5=(p^2+3)%5 at a
    change (4*(x%5)^3)%5=(4*x^3)%5 at b
    change (x%5+1)%5=(x+1)%5 at e
    rw [eqn] at a
    have hit := tab ⟨p%5,Nat.mod_lt _ (by decide)⟩ ⟨x%5,Nat.mod_lt _ (by decide)⟩ (a.trans b.symm)
    change (x%5+1)%5≠0 at hit
    omega
  refine ⟨_,Nat.eq_prime_pow_of_unique_prime_dvd (by omega) ?_⟩
  intro q pq dq
  have lq : q≤8 := by
    by_contra! big
    have ne : q≠s := by rintro rfl; exact sep dq
    exact none ⟨7,q,s,pq,ps,ne,big,sb,dq.trans dl,ds.trans dm⟩
  have opts : q=2 ∨ q=3 ∨ q=5 ∨ q=7 := by interval_cases q <;> norm_num at *
  rcases opts with ok|rfl|rfl|rfl
  · exact ok
  · omega
  · exact False.elim (no5 dq)
  · exact False.elim (no7 (dq.trans dl))


private theorem square_cube_small {j : ℕ} (pj : j.Prime) (small : j≤36) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (4*(2^j-1)^3-3)+d ∧ s ∣ (4*(2^j-1)^3-3)+d := by
  let certs : List (ℕ × ℕ × ℕ × ℕ) := [(2,0,3,5),(3,1,5,137),(5,0,7,29),(7,1,5,109),(11,0,7,181),(13,1,293,739),(17,0,7,71),(19,8,17,2027),(23,0,7,53),(29,3,233,1103),(31,1,5,1051)]
  have cover : ∀ a : Fin 37, a.val.Prime → ∃ z ∈ certs, z.1=a.val := by decide +kernel
  have valid : ∀ z ∈ certs, z.2.2.1.Prime ∧ z.2.2.2.Prime ∧ z.2.2.1≠z.2.2.2 ∧
      z.2.1+1<z.2.2.1 ∧ z.2.1+1<z.2.2.2 ∧ z.2.2.1 ∣ (4*(2^z.1-1)^3-3)+z.2.1 ∧
      z.2.2.2 ∣ (4*(2^z.1-1)^3-3)+z.2.1 := by decide +kernel
  obtain ⟨⟨k,d,q,s⟩,mem,e⟩ := cover ⟨j,by omega⟩ pj
  change k=j at e
  subst k
  exact ⟨d,q,s,valid _ mem⟩

set_option maxRecDepth 16384 in
set_option synthInstance.maxSize 512 in
set_option maxHeartbeats 2000000 in
private theorem square_cube_mersenne_exclusion
    (leftFactor : ∀ {b L : ℕ}, b.Prime → L < b → 3 < b →
      ∃ q : ℕ, q.Prime ∧ L < q ∧ q ∣ 2^b+1)
    {p r j : ℕ} (pp : p.Prime) (pr : r.Prime) (lb : 7≤r) (residue : r%3=1)
    (base : r+1=2^j) (eqn : p^2+3=4*r^3)
    (none : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p^2+d ∧ s ∣ p^2+d) : False := by
  have er : r=2^j-1 := by omega
  have j1 : j≠1 := by rintro rfl; norm_num at base; omega
  have pj : j.Prime := (Nat.prime_of_pow_sub_one_prime j1 (er ▸ pr)).2
  by_cases small : j≤36
  · have h := square_cube_small pj small
    rw [←er] at h
    have en : 4*r^3-3=p^2 := by omega
    rw [en] at h
    exact none h
  let z := (r-1)/3
  have rz : r=3*z+1 := by dsimp [z]; omega
  have high : 7 < p := by
    by_contra! low
    have hp := Nat.pow_le_pow_left low 2
    have hr := Nat.pow_le_pow_left lb 3
    norm_num at hp hr
    omega
  let G (w : ℕ) := 3*w^2+1
  have gc {m i k : ℕ} (h : Nat.ModEq m i k) : Nat.ModEq m (G i) (G k) :=
    ((h.pow 2).mul_left 3).add_right 1
  have fac : p^2+35=12*((r+2)*G z) := by
    have h : r^3+8=3*((r+2)*G z) := by rw [rz]; dsimp [G]; ring
    omega
  have dg : G z ∣ p^2+35 := fac ▸ (dvd_mul_left _ _).trans (dvd_mul_left _ 12)
  have dl : r+2 ∣ p^2+35 := fac ▸ (dvd_mul_right _ _).trans (dvd_mul_left _ 12)
  have gz : 1 < G z := by
    have pos : 0 < z := by omega
    dsimp [G]
    nlinarith [Nat.mul_self_le_mul_self (show 1 ≤ z by omega)]
  obtain ⟨s,ps,ds⟩ := Nat.exists_prime_and_dvd gz.ne'
  have sb : 36 < s := by
    by_contra! low
    let T : List ℕ := [13,19,31]
    have tab : ∀ i : Fin 37, i.val.Prime → ∀ w : Fin i.val,
        G w.val%i.val=0 → i.val=2 ∨ i.val=7 ∨ i.val ∈ T := by decide +kernel
    have c := gc (Nat.mod_modEq z s)
    change G (z%s)%s=G z%s at c
    have opts := tab ⟨s,by omega⟩ ps ⟨z%s,Nat.mod_lt _ ps.pos⟩ (c.trans (Nat.mod_eq_zero_of_dvd ds))
    change s=2 ∨ s=7 ∨ s∈T at opts
    rcases opts with rfl|rfl|mem
    · obtain ⟨w,hw⟩ := pr.odd_of_ne_two (by omega)
      have zm : Nat.ModEq 2 z 0 := by change z%2=0; omega
      have cm := gc zm
      change G z%2=1 at cm
      omega
    · have dv := ds.trans dg
      have d7 := (by decide : Nat.Prime 7).dvd_of_dvd_pow (show 7 ∣ p^2 by omega)
      have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 7) pp).mp d7
      omega
    · have periods : ∀ i ∈ T, Nat.ModEq i (2^180) 1 := by decide +kernel
      have sim (n : ℕ) : Nat.ModEq s (2^n) (2^(n%180)) := by
        calc
          2^n=2^(n%180)*(2^180)^(n/180) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
          _ ≡ 2^(n%180)*1^(n/180) [MOD s] := ((periods s mem).pow _).mul_left _
          _ = _ := by simp
      have cop : j.Coprime 180 := pj.coprime_iff_not_dvd.mpr (by
        intro d
        have h := pj.mem_primeFactors d (by decide)
        have pf : (180:ℕ).primeFactors={2,3,5} := by decide +kernel
        rw [pf] at h
        simp only [Finset.mem_insert,Finset.mem_singleton] at h
        omega)
      have cop' : (j%180).Coprime 180 := by simpa using cop
      have filters : ∀ i ∈ T, ∀ k : Fin 180, k.val.Coprime 180 → ∀ w : Fin i,
          (3*w.val+2)%i=2^k.val%i → G w.val%i≠0 := by decide +kernel
      have m := ((Nat.mod_modEq z s).mul_left 3).add_right 2
      change (3*(z%s)+2)%s=(3*z+2)%s at m
      have jred := sim j
      change 2^j%s=2^(j%180)%s at jred
      have rr := filters s mem ⟨j%180,Nat.mod_lt _ (by decide)⟩ cop' ⟨z%s,Nat.mod_lt _ ps.pos⟩
        (show (3*(z%s)+2)%s=2^(j%180)%s by rw [m,show 3*z+2=2^j by omega,jred])
      exact rr (c.trans (Nat.mod_eq_zero_of_dvd ds))
  obtain ⟨q,pq,qb,dq⟩ := leftFactor pj (show 36 < j by omega) (by omega)
  have dr : q ∣ r+2 := by convert dq using 1; omega
  have ne : q≠s := by
    rintro rfl
    have d3 : q ∣ 3*(z+1) := (show r+2=3*(z+1) by omega) ▸ dr
    have dz := (pq.dvd_mul.mp d3).resolve_left (by
      intro h
      have := Nat.le_of_dvd (by decide : 0<3) h
      omega)
    have ident : G z+6*(z+1)=4+3*(z+1)^2 := by dsimp [G]; ring
    have all := dvd_add ds (dvd_mul_of_dvd_right dz 6)
    rw [ident] at all
    have d4 := (Nat.dvd_add_iff_left (dvd_mul_of_dvd_right (dz.trans (dvd_pow_self _ (by decide : 2≠0))) 3)).mpr all
    have := Nat.le_of_dvd (by decide : 0<4) d4
    omega
  exact none ⟨35,q,s,pq,ps,ne,qb,sb,dr.trans dl,ds.trans dg⟩

/-- If the exponent of the third cofactor is a power of three, it is one. -/
theorem square_third_exponent_one
    (splitPow : ∀ {p s b : ℕ}, Odd p → 1<p → 0<s → p^s+1=2^b → s=1)
    (leftFactor : ∀ {b L : ℕ}, b.Prime → L < b → 3 < b →
      ∃ q : ℕ, q.Prime ∧ L < q ∧ q ∣ 2^b+1)
    {p r b : ℕ} (pp : p.Prime) (pr : r.Prime) (r3 : r%3=1) (eqn : p^2+3=4*r^b)
    (shape : ∃ k : ℕ, b=3^k)
    (none : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p^2+d ∧ s ∣ p^2+d) : b=1 := by
  obtain ⟨k,rfl⟩ := shape
  cases k with
  | zero => rfl
  | succ k =>
    exfalso
    let m := 3^k
    have mp : 0 < m := pow_pos (by decide) _
    let x := r^m
    have cube : p^2+3=4*x^3 := by
      change p^2+3=4*(r^(3^k))^3
      rw [←pow_mul]
      simpa only [pow_succ (3:ℕ) k] using eqn
    have rm : Nat.ModEq 3 r 1 := r3
    have one : x%3=1 := by
      change Nat.ModEq 3 (r^m) 1
      simpa only [one_pow] using rm.pow m
    have rr : 7≤r := by
      by_contra! low
      interval_cases r <;> norm_num at *
    have xr : 7 ≤ x := rr.trans (Nat.le_self_pow mp.ne' r)
    obtain ⟨j,hj⟩ := square_cube_mersenne pp xr one cube none
    have mono := splitPow (pr.odd_of_ne_two (by omega)) pr.one_lt mp hj
    have eqx : x=r := by dsimp [x]; rw [mono,pow_one]
    rw [eqx] at hj cube
    exact square_cube_mersenne_exclusion leftFactor pp pr rr r3 hj cube none

private theorem three_power_pell {t w e : ℕ} (hi : 3 < t) (power : t = 3^e)
    (pell : t^2 = 2*w^2+1) : False := by
  have pos : 0 < e := by
    by_contra! h
    have ze : e=0 := by omega
    rw [ze,pow_zero] at power
    omega
  have three : 3 ∣ t := power ▸ dvd_pow_self _ pos.ne'
  have oddt : Odd t := power ▸ (show Odd (3:ℕ) by decide).pow
  obtain ⟨u,tu⟩ := oddt
  let v := u+1
  have uv : u.Coprime v := by simp [v]
  have eq : v*(2*u)=w^2 := by dsimp [v]; nlinarith [pell,tu]
  have extract {x y : ℕ} (h : x.Coprime y) (e' : x*y=w^2) : ∃ s : ℕ, x=s^2 := by
    apply exists_eq_pow_of_mul_eq_pow _ e'
    change IsUnit (Nat.gcd x y)
    rw [show Nat.gcd x y = 1 from h]
    exact isUnit_one
  have sq : ∃ s : ℕ, t+1=s^2 := by
    rcases Nat.even_or_odd v with ev|ov
    · have ou : Odd u := by rw [Nat.odd_iff]; dsimp [v] at ev; obtain ⟨k,hk⟩ := ev; omega
      obtain ⟨s,hs⟩ := extract (ou.coprime_two_left.mul_left uv.symm) (show (2*v)*u=w^2 by nlinarith [eq])
      exact ⟨s,by dsimp [v] at hs; omega⟩
    · obtain ⟨s,hs⟩ := extract (ov.coprime_two_right.mul_right uv.symm) eq
      have mm := congrArg (· % 3) hs
      rw [Nat.pow_mod] at mm
      have modv : v%3=2 := by dsimp [v]; omega
      rw [modv] at mm
      have tab : ∀ i : Fin 3, i.val^2%3≠2 := by decide
      exact False.elim (tab ⟨s%3,Nat.mod_lt _ (by decide)⟩ mm.symm)
  obtain ⟨s,hs⟩ := sq
  have sl : 2 < s := by by_contra! h; interval_cases s <;> norm_num at hs <;> omega
  obtain ⟨j,rfl⟩ : ∃ j : ℕ, s=j+1 := ⟨s-1,by omega⟩
  have prod : j*(j+2)=3^e := by nlinarith [hs,power]
  have both {z : ℕ} (hz : 1 < z) (dz : z ∣ 3^e) : 3 ∣ z := by
    have hit := (Nat.dvd_prime_pow Nat.prime_three).mp dz
    obtain ⟨k,_,rfl⟩ := hit
    cases k with
    | zero => simp at hz
    | succ k => exact dvd_pow_self _ (by omega)
  have da := both (show 1 < j by omega) (prod ▸ dvd_mul_right j (j+2))
  have db := both (show 1 < j+2 by omega) (prod ▸ dvd_mul_left (j+2) j)
  omega

/-- For a nontrivial prime-square survivor beyond root seven, the odd cofactor
of p²+1 cannot itself be a square. Offset three supplies two distinct primes. -/
theorem square_first_not_square {p q : ℕ} (op : Odd p) (hp : 7 < p)
    (first : p^2+1=2*q^2) : ∃ a b : ℕ, a.Prime ∧ b.Prime ∧ a≠b ∧ 3<a ∧ 3<b ∧
      a ∣ p^2+2 ∧ b ∣ p^2+2 := by
  have qp : q ≤ p := by by_contra! h; nlinarith [Nat.pow_le_pow_left h 2]
  have large : p+3 < 2*q := by
    by_contra! le
    have h := Nat.pow_le_pow_left le 2
    obtain ⟨j,hj⟩ : ∃ j : ℕ, p=j+8 := ⟨p-8,by omega⟩
    rw [hj] at h first
    nlinarith
  let L := 2*q-p
  let R := 2*q+p
  have hL : L+p=2*q := Nat.sub_add_cancel (by omega)
  have hR : R=2*q+p := rfl
  have posL : 3 < L := by omega
  have posR : 3 < R := by omega
  obtain ⟨i,pi⟩ := op
  have fac : L*R=p^2+2 := by nlinarith [hL,hR,first]
  have pellL : L^2=2*(p-q)^2+1 := by
    have h := Nat.sub_add_cancel qp
    nlinarith [first,hL,h]
  have pellR : R^2=2*(p+q)^2+1 := by rw [hR]; nlinarith [first]
  have factor {t w : ℕ} (ht : 3 < t) (ot : t%2=1) (pw : t^2=2*w^2+1) :
      ∃ a : ℕ, a.Prime ∧ 3<a ∧ a ∣ t := by
    by_contra! none
    have power : t=3^t.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
      intro a ha da
      have al : a≤3 := by by_contra! h; exact none a ha h da
      have a2 := ha.two_le
      rcases (show a=2 ∨ a=3 by omega) with rfl|three
      · omega
      · exact three)
    exact three_power_pell ht power pw
  obtain ⟨a,pa,ha,da⟩ := factor posL (by omega) pellL
  obtain ⟨b,pb,hb,db⟩ := factor posR (by omega) pellR
  have left : a ∣ p^2+2 := fac ▸ dvd_mul_of_dvd_left da R
  have right : b ∣ p^2+2 := fac ▸ dvd_mul_of_dvd_right db L
  refine ⟨a,b,pa,pb,?_,ha,hb,left,right⟩
  rintro rfl
  have diff : R-L=2*p := by omega
  have d := diff ▸ Nat.dvd_sub db da
  rcases pa.dvd_mul.mp d with small|ap
  · have := Nat.le_of_dvd (by decide : 0 < 2) small; omega
  · have p2 : a ∣ p^2 := ap.trans (dvd_pow_self p (by decide : 2≠0))
    have div : a ∣ 2 := (Nat.dvd_add_iff_right p2).mpr left
    have := Nat.le_of_dvd (by decide : 0 < 2) div
    omega


/-- Of the positive numbers one below a square and two below twice a square,
only 48 is a solution. -/
theorem adjacent_square_twice_square {n p q : ℕ} (hn : 0 < n)
    (left : n+1=p^2) (right : n+2=2*q^2) : v_l 1 n=1 ↔ n=48 := by
  constructor
  · intro sol
    have first : p^2+1=2*q^2 := by omega
    by_cases small : p≤7
    · have qq : q≤7 := by
        by_contra! h
        have a := Nat.pow_le_pow_left small 2
        have b := Nat.pow_le_pow_left (show 8≤q by omega) 2
        norm_num at a b
        omega
      have tab : ∀ x y : Fin 8, 1 < x.val^2 → x.val^2+1=2*y.val^2 → x.val=7 := by decide
      have eq := tab ⟨p,by omega⟩ ⟨q,by omega⟩ (by simpa using (show 1 < p^2 by omega)) first
      change p=7 at eq
      norm_num [eq] at left
      omega
    · have op : Odd p := by
        rw [Nat.odd_iff]
        have one : p^2%2=1 := by omega
        rw [Nat.pow_mod] at one
        by_contra! bad
        have z : p%2=0 := by omega
        simp [z] at one
      obtain ⟨a,b,pa,pb,ne,ha,hb,da,db⟩ := square_first_not_square op (by omega) first
      have id : n+3=p^2+2 := by omega
      exact False.elim (two_primes (k:=3) (by decide) pa pb ne ha hb (id ▸ da) (id ▸ db) sol)
  · rintro rfl
    exact square_examples (by decide)

/-- An exponent divisible by the entire power of two in q-1 cannot
send a nonzero residue to minus one modulo an odd prime q. -/
private theorem no_small_prime_in_even_power {p q a b : ℕ}
    (pq : q.Prime) (lo : 2<q) (hi : q≤2^b) (apos : 0<a)
    (align : 2^(b-1) ∣ a) : ¬ q ∣ p^a+1 := by
  intro div
  let t := (q-1).factorization 2
  let w := (q-1)/2^t
  have nz : q-1≠0 := by omega
  have fac : 2^t*w=q-1 := Nat.ordProj_mul_ordCompl_eq_self (q-1) 2
  have oddw : Odd w := Nat.not_even_iff_odd.mp
    (fun even => Nat.not_dvd_ordCompl Nat.prime_two nz (even_iff_two_dvd.mp even))
  have size : 2^t ≤ q-1 := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd (q-1) 2)
  have tb : t < b := by
    by_contra! bad
    have := Nat.pow_le_pow_right (by decide : 0<2) bad
    omega
  obtain ⟨k,hk⟩ : 2^t ∣ a := (pow_dvd_pow (2:ℕ) (by omega : t≤b-1)).trans align
  let _ : Fact q.Prime := ⟨pq⟩
  have zero := (ZMod.natCast_eq_zero_iff (p^a+1) q).mpr div
  push_cast at zero
  have neg : (p : ZMod q)^a = -1 := by linear_combination zero
  have ne : (p : ZMod q)≠0 := by
    intro h
    rw [h,zero_pow apos.ne'] at zero
    simp at zero
  have group := ZMod.pow_card_sub_one_eq_one ne
  have aw : a*w=(q-1)*k := by rw [hk,←fac]; ring
  have one : ((p : ZMod q)^a)^w=1 := by rw [←pow_mul,aw,pow_mul,group,one_pow]
  rw [neg,oddw.neg_one_pow] at one
  have cast : ((2 : ℕ) : ZMod q)=0 := by push_cast; linear_combination -one
  have d2 := (ZMod.natCast_eq_zero_iff 2 q).mp cast
  have := Nat.le_of_dvd (by decide) d2
  omega

/-- For a surviving Mersenne successor p^r, a sufficiently divisible
even exponent r-1 must itself be a power of two. -/
theorem mersenne_exponent_alignment {n p r b : ℕ} (pp : p.Prime) (op : Odd p)
    (base : p+1=2^b) (ro : Odd r) (rp : 1<r) (hn : n+1=p^r)
    (sol : v_l 1 n=1) (align : 2^(b-1) ∣ r-1) : ∃ t : ℕ, r-1=2^t := by
  let a := r-1
  have apos : 0<a := by dsimp [a]; omega
  have ra : r=a+1 := by dsimp [a]; omega
  refine ⟨_,Nat.eq_prime_pow_of_unique_prime_dvd apos.ne' ?_⟩
  intro l pl dl
  by_contra l2
  obtain ⟨s,hs⟩ := dl
  change a=l*s at hs
  have sp : 0<s := by
    by_contra! bad
    have s0 : s=0 := by omega
    simp [s0] at hs
    omega
  have form : (p^s)^l=p^a := by rw [←pow_mul,hs,Nat.mul_comm s l]
  have raised : n+(p+1)=p*((p^s)^l+1) := by
    rw [form]
    rw [ra,pow_succ] at hn
    nlinarith
  have eligible (q : ℕ) (pq : q.Prime) (lo : 2<q) (div : q ∣ (p^s)^l+1) : p+1<q := by
    by_contra! small
    rw [form] at div
    exact no_small_prime_in_even_power pq lo (base ▸ small) apos align div
  obtain ⟨e,power⟩ := odd_root_with_unique_odd_prime op.pow (Nat.one_lt_pow sp.ne' pp.one_lt)
    (pl.odd_of_ne_two l2) pl.one_lt (by
      intro q z pq pz hq hz dq dz
      by_contra neq
      exact two_primes (k:=p+1) (by omega) pq pz neq (eligible q pq hq dq) (eligible z pz hz dz)
        (raised ▸ dvd_mul_of_dvd_right dq p) (raised ▸ dvd_mul_of_dvd_right dz p) sol)
  have one := mersenne_power_exponent op pp.one_lt sp power
  rw [one,mul_one] at hs
  obtain ⟨u,hu⟩ := ro
  obtain ⟨v,hv⟩ := pl.odd_of_ne_two l2
  omega

private theorem three_large_prime_exponent {n r : ℕ} (pr : r.Prime) (rb : 5≤r)
    (hn : n+1=3^r) : v_l 1 n≠1 := by
  intro sol
  have ro := pr.odd_of_ne_two (by omega)
  obtain ⟨w,hw⟩ := ro
  obtain ⟨t,ht⟩ := mersenne_exponent_alignment (p:=3) (b:=2) Nat.prime_three (by decide)
    (by decide) ⟨w,hw⟩ (by omega) hn sol (by norm_num; omega)
  have t2 : 2≤t := by by_contra! small; interval_cases t <;> norm_num at ht <;> omega
  have d4 : 4 ∣ r-1 := ht ▸ (pow_dvd_pow (2:ℕ) t2)
  have not3 : ¬3 ∣ r := by
    intro d
    have e := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pr).mp d
    omega
  have pair : 2^t%3=1 ∨ 2^t%3=2 := by
    have period := pow_cycle (a:=2) (d:=2) (m:=3) (by decide) t
    change 2^t%3=2^(t%2)%3 at period
    rcases Nat.mod_two_eq_zero_or_one t with e|e <;> rw [e] at period <;> norm_num at period <;> omega
  have r4 : r%4=1 := by omega
  have r6 : r%6=5 := by omega
  have d5 := pow_cycle (a:=3) (d:=4) (m:=5) (by decide) r
  have d7 := pow_cycle (a:=3) (d:=6) (m:=7) (by decide) r
  change 3^r%5=3^(r%4)%5 at d5
  change 3^r%7=3^(r%6)%7 at d7
  rw [r4] at d5
  rw [r6] at d7
  norm_num at d5 d7
  exact two_primes (k:=3) (p:=5) (q:=7) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega) sol

/-- These four positive solutions are exactly the ones below a power of three. -/
theorem three_successor_solution {n e : ℕ} (pos : 0<n) (hn : n+1=3^e) :
    v_l 1 n=1 ↔ n=2 ∨ n=8 ∨ n=26 ∨ n=80 := by
  constructor
  · intro sol
    have ep : 0<e := by
      by_contra! bad
      have e0 : e=0 := by omega
      rw [e0,pow_zero] at hn
      omega
    have bound : e≤4 := by
      by_contra! large
      rcases successor_exponent Nat.prime_three (by decide) ep hn sol with ⟨t,ht⟩|⟨pr,_,_⟩
      · have t2 : 2≤t := by by_contra! bad; interval_cases t <;> norm_num at ht <;> omega
        obtain ⟨j,hj⟩ : 4 ∣ e := ht ▸ (pow_dvd_pow (2:ℕ) t2)
        have j2 : 2≤j := by omega
        have pow : 3^e=(3^j)^4 := by rw [hj,←pow_mul,Nat.mul_comm]
        have lb := Nat.pow_le_pow_right (by decide : 0<3) j2
        norm_num at lb
        obtain ⟨p,q,pp,pq,ne,hp,hq,dp,dq⟩ := fourth_power_witness (x:=3^j)
          ((by decide : Odd 3).pow) (by omega)
        have sh : n+5=(3^j)^4+4 := by omega
        exact two_primes (k:=5) (by decide) pp pq ne hp hq (sh ▸ dp) (sh ▸ dq) sol
      · exact three_large_prime_exponent pr large hn sol
    interval_cases e <;> norm_num at hn <;> omega
  · rintro (rfl|rfl|rfl|rfl) <;> apply (solutions_through_330 (by decide) (by decide)).mpr <;> decide

/-- An odd power of a nontrivial odd base introduces an odd prime
dividing x^d+1 that did not already divide x+1. -/
private theorem odd_step_new_prime {x d : ℕ} (ox : Odd x) (hx : 1 < x)
    (od : Odd d) (hd : 1 < d) :
    ∃ q : ℕ, q.Prime ∧ 2<q ∧ q ∣ x^d+1 ∧ ¬ q ∣ x+1 := by
  obtain ⟨c,oc,hc,fac⟩ := odd_cofactor ox hx od hd
  by_contra missing
  have cd : c ∣ d := by
    apply (Nat.factorization_le_iff_dvd (by omega : c≠0) (by omega : d≠0)).mp
    intro q
    by_cases pq : q.Prime
    · by_cases dq : q ∣ c
      · have big : 2 < q := by
          have lb := pq.two_le
          by_contra! small
          have qt : q=2 := by omega
          obtain ⟨u,hu⟩ := oc
          rw [qt] at dq
          omega
        have dx : q ∣ x+1 := by
          by_contra bad
          exact missing ⟨q,pq,big,fac ▸ dvd_mul_of_dvd_right dq _,bad⟩
        let _ : Fact q.Prime := ⟨pq⟩
        have nd : ¬q ∣ x := by
          intro div
          have one := (Nat.dvd_add_iff_right div).mpr dx
          have := Nat.le_of_dvd Nat.one_pos one
          omega
        have v := padicValNat.pow_add_pow (x:=x) (y:=1) (pq.odd_of_ne_two (by omega)) dx nd od
        rw [one_pow,fac,padicValNat.mul (by omega) (by omega)] at v
        change c.factorization q ≤ d.factorization q
        rw [Nat.factorization_def _ pq,Nat.factorization_def _ pq]
        omega
      · exact (Nat.factorization_eq_zero_of_not_dvd dq).trans_le (Nat.zero_le _)
    · exact (Nat.factorization_eq_zero_of_not_prime c pq).trans_le (Nat.zero_le _)
  exact (Nat.not_le_of_gt hc) (Nat.le_of_dvd (by omega) cd)

private theorem seven_orbit_hit {n t s k p q z : ℕ} (hn : n+1=7*7^(2^t))
    (j : ℕ) (ht : t=s+4*j) (hk : 0<k)
    (pp : p.Prime) (pq : q.Prime) (ne : p≠q) (kp : k<p) (kq : k<q)
    (base : Nat.ModEq (p*q) (7^(2^s)) z) (step : Nat.ModEq (p*q) (z^16) z)
    (hit : Nat.ModEq (p*q) (7*z+k) 1) : v_l 1 n≠1 := by
  have orbit (i : ℕ) : Nat.ModEq (p*q) (7^(2^(s+4*i))) z := by
    induction i with
    | zero => simpa using base
    | succ i ih =>
      rw [show s+4*(i+1)=s+4*i+4 by omega,pow_add,pow_mul]
      exact (ih.pow 16).trans step
  have d := (((orbit j).mul_left 7).add_right k).trans hit
  rw [←ht,←hn,show n+1+k=(n+k)+1 by omega] at d
  have div := Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_right_cancel' 1 (b:=0) d)
  exact two_primes hk pp pq ne kp kq ((dvd_mul_right p q).trans div) ((dvd_mul_left q p).trans div)

set_option maxRecDepth 8192 in
/-- A surviving prime exponent for base seven must be twice another
prime plus one. -/
theorem seven_safe_prime_exponent {n r : ℕ} (pr : r.Prime) (lo : 5≤r)
    (hn : n+1=7^r) (sol : v_l 1 n=1) : ∃ m : ℕ, m.Prime ∧ r=2*m+1 := by
  have ro := pr.odd_of_ne_two (by omega)
  have not3 : ¬3 ∣ r := by
    intro h
    have err := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pr).mp h
    omega
  have rmod : r%4=3 := by
    by_contra miss
    have div : 4 ∣ r-1 := by obtain ⟨w,hw⟩ := ro; omega
    obtain ⟨t,ht⟩ := mersenne_exponent_alignment (p:=7) (b:=3) (by decide) (by decide)
      (by decide) ro (by omega) hn sol div
    have tb : 2≤t := by by_contra! low; interval_cases t <;> norm_num at ht <;> omega
    have pm := pow_cycle (a:=2) (d:=2) (m:=3) (by decide) t
    change 2^t%3=2^(t%2)%3 at pm
    have tmod : t%2=0 := by
      by_contra bad
      have e : t%2=1 := by omega
      rw [e] at pm
      norm_num at pm
      omega
    have shift : n+1=7*7^(2^t) := by
      rw [show r=2^t+1 by omega,pow_succ] at hn
      simpa [Nat.mul_comm] using hn
    let j := (t-2)/4
    rcases (show t=2+4*j ∨ t=4+4*j by dsimp [j]; omega) with h|h
    · apply seven_orbit_hit (k:=2) (p:=11) (q:=191) (z:=300) shift j h <;> first | exact sol | decide +kernel
    · apply seven_orbit_hit (k:=11) (p:=17) (q:=61) (z:=443) shift j h <;> first | exact sol | decide +kernel
  let m := r/2
  have rm : r=2*m+1 := by dsimp [m]; omega
  have mo : Odd m := by rw [Nat.odd_iff]; omega
  refine ⟨m,?_,rm⟩
  by_contra mp
  obtain ⟨u,v,us,vs,uv⟩ := (Nat.not_prime_iff_exists_mul_eq (n:=m) (by omega)).mp mp
  have ub : 1<u := by by_contra! bad; interval_cases u <;> simp_all
  have vb : 1<v := by by_contra! bad; interval_cases v <;> simp_all
  rw [←uv,Nat.odd_mul] at mo
  obtain ⟨q,pq,hq,dq,nq⟩ := odd_step_new_prime (x:=49) (by decide) (by decide) mo.1 ub
  obtain ⟨s,ps,hs,ds,ns⟩ := odd_step_new_prime (x:=49^u) ((by decide : Odd 49).pow)
    (Nat.one_lt_pow (by omega) (by decide)) mo.2 vb
  have enters : 49^u+1 ∣ (49^u)^v+1 := by simpa using mo.2.nat_add_dvd_pow_add_pow (49^u) 1
  have five : 5 ∣ 49^u+1 := by
    have lift : 49+1 ∣ 49^u+1 := by simpa using mo.1.nat_add_dvd_pow_add_pow 49 1
    exact (by decide : 5 ∣ 49+1).trans lift
  have ne : q≠s := by rintro rfl; exact ns dq
  have enlarged : (49^u)^v=49^m := by rw [←pow_mul,uv]
  have qdiv := dq.trans enters
  rw [enlarged] at qdiv ds
  have big (z : ℕ) (pz : z.Prime) (hz : 2<z) (nz : z≠5) (dz : z ∣ 49^m+1) : 8<z := by
    by_contra! small
    have cases : z=3 ∨ z=7 := by interval_cases z <;> norm_num at *
    rcases cases with rfl|rfl
    · have h : Nat.ModEq 3 49 1 := by decide
      have red : Nat.ModEq 3 (49^m) 1 := by simpa only [one_pow] using h.pow m
      change 49^m%3=1 at red
      omega
    · have div := (by decide : 7 ∣ 49).trans (dvd_pow_self 49 (by omega : m≠0))
      omega
  have qb := big q pq hq (by rintro rfl; exact nq (by decide)) qdiv
  have sb := big s ps hs (by rintro rfl; exact ns five) ds
  have shift : n+8=7*(49^m+1) := by
    rw [rm,pow_succ,pow_mul,show (7:ℕ)^2=49 by decide] at hn
    omega
  exact two_primes (k:=8) (by decide) pq ps ne qb sb
    (shift ▸ dvd_mul_of_dvd_right qdiv 7) (shift ▸ dvd_mul_of_dvd_right ds 7) sol

private theorem middle_norm_pos {b : Zsqrtd (-2)} (hb : b≠0) : 0 < b.norm := by
  have nn := Zsqrtd.norm_nonneg (by decide : (-2:ℤ)≤0) b
  by_contra! le
  have hz : b.norm=0 := by omega
  rw [Zsqrtd.norm_def] at hz
  apply hb
  ext
  · change b.re=0
    nlinarith [sq_nonneg b.im]
  · change b.im=0
    nlinarith [sq_nonneg b.re]

private theorem middle_euclidean : IsPrincipalIdealRing (Zsqrtd (-2)) ∧ IsDomain (Zsqrtd (-2)) := by
  let Q (a b : Zsqrtd (-2)) : Zsqrtd (-2) :=
    ⟨(a*star b).re.bdiv b.norm.natAbs,(a*star b).im.bdiv b.norm.natAbs⟩
  let R (a b : Zsqrtd (-2)) := a-b*Q a b
  have divide (a b : Zsqrtd (-2)) (hb : b≠0) : (R a b).norm.natAbs < b.norm.natAbs := by
    let n := b.norm.natAbs
    have bp := middle_norm_pos hb
    have en : (n:ℤ)=b.norm := Int.natAbs_of_nonneg bp.le
    have np : 0<n := by omega
    let u := (a*star b).re
    let v := (a*star b).im
    let U := u.bmod n
    let V := v.bmod n
    have rel : R a b*star b=a*star b-(b.norm:Zsqrtd (-2))*Q a b := by
      dsimp [R]; rw [Zsqrtd.norm_eq_mul_conj]; ring
    have coords : R a b*star b=(⟨U,V⟩:Zsqrtd (-2)) := by
      rw [rel]
      ext
      · change u-((b.norm:Zsqrtd (-2))*Q a b).re=U
        simp only [Zsqrtd.re_mul,Zsqrtd.re_intCast,Zsqrtd.im_intCast,mul_zero,zero_mul,add_zero]
        change u-b.norm*u.bdiv n=u.bmod n
        rw [←en,Int.bmod_eq_self_sub_mul_bdiv]
      · change v-((b.norm:Zsqrtd (-2))*Q a b).im=V
        simp only [Zsqrtd.im_mul,Zsqrtd.re_intCast,Zsqrtd.im_intCast,zero_mul,add_zero]
        change v-b.norm*v.bdiv n=v.bmod n
        rw [←en,Int.bmod_eq_self_sub_mul_bdiv]
    have bound (x : ℤ) : 4*(x.bmod n)^2 ≤ b.norm^2 := by
      have lo := Int.le_bmod (x:=x) np
      have hi := Int.bmod_lt (x:=x) np
      have h₁ : 0 ≤ b.norm-2*x.bmod n := by omega
      have h₂ : 0 ≤ b.norm+2*x.bmod n := by omega
      nlinarith only [mul_nonneg h₁ h₂]
    have ee := congrArg Zsqrtd.norm coords
    rw [Zsqrtd.norm_mul,Zsqrtd.norm_conj] at ee
    change (R a b).norm*b.norm=U*U-(-2)*V*V at ee
    have u2 := bound u
    have v2 := bound v
    change 4*U^2≤b.norm^2 at u2
    change 4*V^2≤b.norm^2 at v2
    have lt : (R a b).norm < b.norm := by
      by_contra! bad
      nlinarith only [ee,u2,v2,mul_le_mul_of_nonneg_right bad bp.le,mul_pos bp bp]
    have nonneg := Zsqrtd.norm_nonneg (by decide : (-2:ℤ)≤0) (R a b)
    omega
  let nt : Nontrivial (Zsqrtd (-2)) := ⟨⟨0,1,by decide⟩⟩
  let _ : EuclideanDomain (Zsqrtd (-2)) :=
    { Zsqrtd.commRing, nt with
      quotient := Q
      quotient_zero := by intro a; dsimp [Q]; simp; rfl
      remainder := R
      quotient_mul_add_remainder_eq := by intro a b; dsimp [R]; ring
      r := fun a b => a.norm.natAbs < b.norm.natAbs
      r_wellFounded := (measure (fun a : Zsqrtd (-2) => a.norm.natAbs)).wf
      remainder_lt := by intro a b hb; exact divide a b hb
      mul_left_not_lt := by
        intro a b hb
        have bp := middle_norm_pos hb
        rw [Zsqrtd.norm_mul,Int.natAbs_mul]
        have bn : 1≤b.norm.natAbs := by omega
        exact not_lt_of_ge (Nat.le_mul_of_pos_right _ bn) }
  exact ⟨inferInstance,inferInstance⟩

private theorem middle_unit_sq (u : (Zsqrtd (-2))ˣ) : (u:Zsqrtd (-2))^2=1 := by
  have un := (Zsqrtd.norm_eq_one_iff' (by decide : (-2:ℤ)≤0) (u:Zsqrtd (-2))).mpr u.isUnit
  generalize (u:Zsqrtd (-2))=v at un ⊢
  obtain ⟨a,b⟩ := v
  change a*a-(-2)*b*b=1 at un
  have bi : b=0 := by nlinarith [sq_nonneg a]
  subst b
  have opts : a=-1 ∨ a=1 := by
    have h1 : -1≤a := by nlinarith
    have h2 : a≤1 := by nlinarith
    interval_cases a <;> norm_num at *
  rcases opts with rfl|rfl <;> decide

private theorem middle_im_dvd (a : Zsqrtd (-2)) (n : ℕ) : a.im ∣ (a^n).im := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,Zsqrtd.im_mul]
    exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_left ih _)

/-- For an odd prime p, p²+2 is not a proper power with base greater than three. -/
theorem square_middle_power_exclusion {p y d : ℕ} (pp : p.Prime) (op : Odd p)
    (hy : 3<y) (hd : 1<d) (he : p^2+2=y^d) : False := by
  rcases Nat.even_or_odd d with ⟨j,hj⟩|od
  · have eq : p^2+2=(y^j)^2 := by rw [he,hj,pow_add,pow_two]
    have hp := pp.two_le
    by_cases h : y^j≤p
    · nlinarith [Nat.mul_self_le_mul_self h]
    · nlinarith [Nat.mul_self_le_mul_self (show p+1≤y^j by omega)]
  have structures := middle_euclidean
  let _ : IsDomain (Zsqrtd (-2)) := structures.2
  let _ : IsPrincipalIdealRing (Zsqrtd (-2)) := structures.1
  let A : Zsqrtd (-2) := ⟨(p:ℤ),1⟩
  have zhe : (p:ℤ)^2+2=(y:ℤ)^d := by exact_mod_cast he
  have An : A.norm=(y:ℤ)^d := by change (p:ℤ)*p-(-2)*1*1=(y:ℤ)^d; nlinarith
  have prod : A*star A=(y:Zsqrtd (-2))^d := by
    rw [←Zsqrtd.norm_eq_mul_conj,An]; push_cast; rfl
  have diff : (A-star A)^2=(-8:Zsqrtd (-2)) := by
    ext <;> simp [A,pow_two]
  have tr : A+star A=((2*(p:ℤ):ℤ):Zsqrtd (-2)) := by
    ext <;> simp [A]
    ring
  have oddn : Odd (p^2+2) := (op.pow (n:=2)).add_even (by decide : Even 2)
  have copZ : IsCoprime (((p^2+2:ℕ):ℤ)) 8 := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    change (p^2+2).Coprime (2^3)
    exact (Nat.coprime_two_right.mpr oddn).pow_right _
  obtain ⟨u,v,huv⟩ := copZ
  have cop : IsCoprime A (star A) := by
    refine ⟨(u:Zsqrtd (-2))*star A-v*(A-star A),(v:Zsqrtd (-2))*(A-star A),?_⟩
    calc
      _ = (u:Zsqrtd (-2))*(A*star A)-v*(A-star A)^2 := by ring
      _ = 1 := by
        rw [prod,diff,←Nat.cast_pow,←he]
        simpa using (show (u:Zsqrtd (-2))*((p^2+2:ℕ):Zsqrtd (-2))+(v:Zsqrtd (-2))*8=1 by exact_mod_cast huv)
  obtain ⟨z,u,hu⟩ := exists_associated_pow_of_mul_eq_pow' cop prod
  have ud : (u:Zsqrtd (-2))^d=u := by
    obtain ⟨j,hj⟩ := od
    rw [hj,pow_succ,pow_mul,middle_unit_sq,one_pow,one_mul]
  let a := z*(u:Zsqrtd (-2))
  have eq : a^d=A := by dsimp [a]; rw [mul_pow,ud,hu]
  have di := middle_im_dvd a d
  rw [eq] at di
  change a.im ∣ 1 at di
  have ia : a.im.natAbs=1 := by
    obtain ⟨t,ht⟩ := di
    apply Nat.dvd_one.mp
    exact ⟨t.natAbs,by simpa [Int.natAbs_mul] using congrArg Int.natAbs ht⟩
  have sqi : a.im^2=1 := by
    have h := congrArg (fun t : ℕ => (t:ℤ)^2) ia
    simpa [Int.natCast_natAbs,sq_abs] using h
  have dr : a.re ∣ (p:ℤ) := by
    obtain ⟨w,hw⟩ := od.add_dvd_pow_add_pow a (star a)
    rw [←star_pow,eq,tr] at hw
    have cv := congrArg Zsqrtd.re hw
    simp only [Zsqrtd.re_intCast,Zsqrtd.re_mul,Zsqrtd.re_add,Zsqrtd.re_star,Zsqrtd.im_add,Zsqrtd.im_star] at cv
    exact ⟨w.re,by nlinarith only [cv]⟩
  have ra : a.re.natAbs ∣ p := by
    obtain ⟨t,ht⟩ := dr
    exact ⟨t.natAbs,by simpa [Int.natAbs_mul] using congrArg Int.natAbs ht⟩
  have an : a.norm=(y:ℤ) := by
    apply od.pow_injective
    change Zsqrtd.normMonoidHom a ^ d = _
    rw [←map_pow,eq]
    exact An
  rw [Zsqrtd.norm_def] at an
  have sqr : (a.re.natAbs:ℤ)^2=a.re^2 := by rw [Int.natCast_natAbs,sq_abs]
  rcases (Nat.dvd_prime pp).mp ra with one|same
  · rw [one] at sqr
    norm_num at sqr
    have yb : (3:ℤ)<y := by exact_mod_cast hy
    nlinarith
  · rw [same] at sqr
    have gt : (y:ℤ)<(y:ℤ)^d := by simpa using pow_lt_pow_right₀ (show (1:ℤ)<y by omega) hd
    nlinarith

/-- The positive exponents of the two distinct primes in p²+2 are coprime. -/
theorem square_middle_exponents_coprime {p t c e : ℕ} (pp : p.Prime) (op : Odd p)
    (ht : 3<t) (ep : 0<e) (eq : p^2+2=3^c*t^e) : c.Coprime e := by
  by_contra bad
  obtain ⟨d,pd,dc,de⟩ := Nat.Prime.not_coprime_iff_dvd.mp bad
  obtain ⟨u,hu⟩ := dc
  obtain ⟨v,hv⟩ := de
  have vp : v≠0 := by rintro rfl; simp at hv; omega
  have lb := Nat.le_self_pow vp t
  have yb : 3 < 3^u*t^v := by
    have pos : 0<3^u := pow_pos (by decide) _
    have := Nat.mul_le_mul_right (t^v) pos
    omega
  apply square_middle_power_exclusion pp op yb pd.one_lt
  rw [mul_pow,←pow_mul,←pow_mul,Nat.mul_comm u d,Nat.mul_comm v d,←hu,←hv,eq]

private theorem middle_pell_divisibility {x y : ℕ} (he : x^2+2=3*y^2) (hd : 3 ∣ y) :
    5 ∣ x := by
  let states : List (ℕ × ℕ) := [(1,1),(5,3),(4,11),(11,11),(10,3),(14,1)]
  have closed : ∀ z ∈ states, ((2*z.1+3*z.2)%15,(z.1+2*z.2)%15) ∈ states := by
    decide +kernel
  have sieve : ∀ z ∈ states, 3 ∣ z.2 → 5 ∣ z.1 := by decide +kernel
  have orbit (b a : ℕ) (eqn : a^2+2=3*b^2) : (a%15,b%15) ∈ states := by
    induction b using Nat.strong_induction_on generalizing a with
    | h b ih =>
      by_cases small : b < 2
      · have ab : a ≤ 1 := by nlinarith [Nat.mul_self_le_mul_self (show b ≤ 1 by omega)]
        interval_cases b <;> interval_cases a <;> norm_num at eqn
        all_goals decide +kernel
      · have lb : 2 ≤ b := by omega
        have low : 3*b ≤ 2*a := by
          by_contra! bad
          nlinarith only [eqn, Nat.mul_self_le_mul_self bad.le, Nat.mul_self_le_mul_self lb]
        have high : a ≤ 2*b := by
          by_contra! bad
          nlinarith only [eqn, Nat.mul_self_le_mul_self bad.le, Nat.zero_le (b*b)]
        have strict : b < a := by
          by_contra! bad
          nlinarith only [eqn, Nat.mul_self_le_mul_self bad, Nat.mul_self_le_mul_self lb]
        let u := 2*a-3*b
        let v := 2*b-a
        have eu : u+3*b=2*a := Nat.sub_add_cancel low
        have ev : v+a=2*b := Nat.sub_add_cancel high
        have evsmall : v<b := by omega
        have norm : u^2+2=3*v^2 := by
          have az : (a:ℤ)^2+2=3*(b:ℤ)^2 := by exact_mod_cast eqn
          have uz : (u:ℤ)=2*(a:ℤ)-3*(b:ℤ) := by dsimp [u]; push_cast [Nat.cast_sub low]; ring
          have vz : (v:ℤ)=2*(b:ℤ)-(a:ℤ) := by dsimp [v]; push_cast [Nat.cast_sub high]; ring
          have nz : (u:ℤ)^2+2=3*(v:ℤ)^2 := by rw [uz,vz]; linear_combination az
          exact_mod_cast nz
        have prev := closed _ (ih v evsmall u norm)
        have m := (Nat.mod_modEq u 15).symm
        have n := (Nat.mod_modEq v 15).symm
        have ax := (m.mul_left 2).add (n.mul_left 3)
        have by' := m.add (n.mul_left 2)
        change (2*u+3*v)%15=_ at ax
        change (u+2*v)%15=_ at by'
        rwa [show a=2*u+3*v by omega, show b=u+2*v by omega, ax, by']
  have d9 : 3 ∣ y%15 := by omega
  have d17 := sieve (x%15,y%15) (orbit y x he) d9
  change 5 ∣ x%15 at d17
  omega

/-- When the exponent of the large prime is even, three divides the middle term exactly once. -/
theorem square_middle_even_exponent {p t c e : ℕ} (pp : p.Prime) (hp : 5<p) (co : c.Coprime e)
    (eq : p^2+2=3^c*t^e) (ev : Even e) : c=1 := by
  obtain ⟨v,hv⟩ := ev
  have odd : Odd c := by
    apply Nat.not_even_iff_odd.mp
    intro ec
    have cc := Nat.dvd_gcd (even_iff_two_dvd.mp ec) (even_iff_two_dvd.mp (show Even e from ⟨v,hv⟩))
    rw [Nat.coprime_iff_gcd_eq_one.mp co] at cc
    omega
  obtain ⟨u,hu⟩ := odd
  by_contra ne
  have up : u≠0 := by omega
  let y := 3^u*t^v
  have fact : p^2+2=3*y^2 := by
    rw [eq,hu,hv,pow_succ,Nat.mul_comm 2 u,pow_mul,pow_add]
    dsimp [y]; ring
  have hit := middle_pell_divisibility fact (dvd_mul_of_dvd_left (dvd_pow_self (3:ℕ) up) (t^v))
  have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 5) pp).mp hit
  omega

/-- A fourth power in the middle cofactor would supply a witness at offset fifteen. -/
theorem square_middle_exponent_not_four
    (fourth : ∀ {x : ℕ}, Odd x → 3<x →
      ∃ q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ 5<q ∧ 5<s ∧ q ∣ x^4+4 ∧ s ∣ x^4+4)
    {p q t c e : ℕ} (pp : p.Prime) (hp : 5<p) (pq : q.Prime) (first : p^2+1=2*q)
    (ot : Odd t) (ht : 3<t) (ep : 0<e) (co : c.Coprime e) (eq : p^2+2=3^c*t^e)
    (none : ¬∃ d l s : ℕ, l.Prime ∧ s.Prime ∧ l≠s ∧ d+1<l ∧ d+1<s ∧
      l ∣ p^2+d ∧ s ∣ p^2+d) : ¬4 ∣ e := by
  rintro ⟨u,hu⟩
  have up : u≠0 := by omega
  have even : Even e := ⟨2*u,by omega⟩
  have c1 := square_middle_even_exponent pp hp co eq even
  let x := t^u
  have fac : p^2+14=3*(x^4+4) := by
    have eq' : p^2+2=3*x^4 := by
      rw [eq,c1,pow_one,hu,Nat.mul_comm 4 u,pow_mul]
    omega
  have no13 : ¬13 ∣ x^4+4 := by
    intro dv
    have da : 13 ∣ p^2+14 := fac ▸ dvd_mul_of_dvd_right dv 3
    have db : 13 ∣ 2*q := by omega
    have pr : Nat.Prime 13 := by decide
    have d := (pr.dvd_mul.mp db).resolve_left (by decide)
    have same := (Nat.prime_dvd_prime_iff_eq pr pq).mp d
    have lim := Nat.pow_le_pow_left (show 6≤p by omega) 2
    norm_num at lim
    omega
  have big (l : ℕ) (pl : l.Prime) (hl : 5<l) (dv : l ∣ x^4+4) : 15<l := by
    by_contra! low
    have opt : l=7 ∨ l=11 ∨ l=13 := by interval_cases l <;> norm_num at *
    have tab : ∀ i ∈ ([7,11] : List ℕ), ∀ z : Fin i, (z.val^4+4)%i≠0 := by decide +kernel
    have cm := ((Nat.mod_modEq x l).pow 4).add_right 4
    change ((x%l)^4+4)%l=(x^4+4)%l at cm
    have val := cm.trans (Nat.mod_eq_zero_of_dvd dv)
    rcases opt with rfl|rfl|rfl
    · exact tab 7 (by decide) ⟨x%7,Nat.mod_lt _ (by decide)⟩ val
    · exact tab 11 (by decide) ⟨x%11,Nat.mod_lt _ (by decide)⟩ val
    · exact no13 dv
  obtain ⟨l,s,pl,ps,ne,hl,hs,dl,ds⟩ := fourth (x:=x) ot.pow (lt_of_lt_of_le ht (Nat.le_self_pow up t))
  exact none ⟨14,l,s,pl,ps,ne,big l pl hl dl,big s ps hs ds,
    fac ▸ dvd_mul_of_dvd_right dl 3,fac ▸ dvd_mul_of_dvd_right ds 3⟩

/-- With only one factor of three in the middle term, every even exponent is two. -/
theorem square_middle_even_exponent_two
    (uniqueRoot : ∀ {x r : ℕ}, Odd x → 1<x → Odd r → 1<r →
      (∀ l s : ℕ, l.Prime → s.Prime → 2<l → 2<s → l ∣ x^r+1 → s ∣ x^r+1 → l=s) →
      ∃ b : ℕ, x+1=2^b)
    {p t e : ℕ} (pp : p.Prime) (hp : 5<p) (ot : Odd t) (ht : 3<t)
    (ep : 0<e) (ev : Even e) (no4 : ¬4 ∣ e) (eq : p^2+2=3*t^e)
    (none : ¬∃ d l s : ℕ, l.Prime ∧ s.Prime ∧ l≠s ∧ d+1<l ∧ d+1<s ∧
      l ∣ p^2+d ∧ s ∣ p^2+d) : e=2 := by
  by_contra ne
  obtain ⟨u,hu⟩ := ev
  have ou : Odd u := by rw [Nat.odd_iff]; omega
  have pow : (t^2)^u=t^e := by rw [←pow_mul]; congr 1; omega
  have fac : p^2+5=3*((t^2)^u+1) := by rw [pow]; omega
  have no5 : ¬5 ∣ (t^2)^u+1 := by
    intro dv
    have d5 : 5 ∣ p^2+5 := fac ▸ dvd_mul_of_dvd_right dv 3
    have hit := (by decide : Nat.Prime 5).dvd_of_dvd_pow (show 5 ∣ p^2 by omega)
    have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 5) pp).mp hit
    omega
  have no3 : ¬3 ∣ (t^2)^u+1 := by
    have swap : (t^2)^u=(t^u)^2 := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
    rw [swap,Nat.dvd_iff_mod_eq_zero]
    have cm := ((Nat.mod_modEq (t^u) 3).pow 2).add_right 1
    change ((t^u%3)^2+1)%3=((t^u)^2+1)%3 at cm
    have bad : ∀ z : Fin 3, (z.val^2+1)%3≠0 := by decide +kernel
    exact cm ▸ bad ⟨t^u%3,Nat.mod_lt _ (by decide)⟩
  have eligible {l : ℕ} (pl : l.Prime) (low : 2<l) (div : l ∣ (t^2)^u+1) : 6<l := by
    by_contra! small
    have cases : l=3 ∨ l=5 := by interval_cases l <;> norm_num at *
    rcases cases with rfl|rfl
    · exact no3 div
    · exact no5 div
  obtain ⟨j,hj⟩ := uniqueRoot (x:=t^2) (r:=u) ot.pow (by nlinarith) ou (by omega) (by
    intro l s pl ps hl hs dl ds
    by_contra diff
    exact none ⟨5,l,s,pl,ps,diff,eligible pl hl dl,eligible ps hs ds,
      fac ▸ dvd_mul_of_dvd_right dl 3,fac ▸ dvd_mul_of_dvd_right ds 3⟩)
  have big : 2≤j := by by_contra! small; interval_cases j <;> norm_num at hj <;> nlinarith
  have h4 : 4 ∣ t^2+1 := hj ▸ pow_dvd_pow (2:ℕ) big
  obtain ⟨w,hw⟩ := ot
  have form : t^2+1=4*(w^2+w)+2 := by rw [hw]; ring
  omega

/-- At every sufficiently large odd prime, find a later or equal integer
with two distinct prime factors larger than the offset from its predecessor. -/
def H1 : Prop := ∃ B : ℕ, ∀ p : ℕ, p.Prime → Odd p → B < p →
    (∀ x : ℕ, 1<x → p≠x^4+1) →
    ((∀ e : ℕ, p ≠ 2^e+1) ∧ ∃ q r a b c d : ℕ, q.Prime ∧ r.Prime ∧ 2<q ∧ 3<r ∧
      q≠r ∧ 0<a ∧ 0<b ∧ 0<c ∧ 0<d ∧ (a=1 ∨ c=1) ∧ p+1=2^a*q^b ∧ p+3=2^c*r^d) →
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
      q ∣ p+d ∧ s ∣ p+d

/-- A prime square needs a witness only if three successive values have the prescribed factorizations
with the specified residues and exponents. -/
def H2 : Prop := ∃ B : ℕ, ∀ p : ℕ, p.Prime → Odd p → B < p^2 →
    (∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q≠r ∧ q%4=1 ∧ r%3=1 ∧
      p^2+1=2*q ∧ p^2+3=4*r) →
    (∃ t c e : ℕ, t.Prime ∧ 3 < t ∧ (t%8=1 ∨ t%8=3) ∧
      0 < c ∧ 0 < e ∧ c.Coprime e ∧ (Even e → c=1 ∧ e=2) ∧ p^2+2=3^c*t^e) →
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
      q ∣ p^2+d ∧ s ∣ p^2+d

/-- Only odd Mersenne primes above three and prime exponents at least seventeen remain.
When the Mersenne index and exponent satisfy the divisibility condition, r−1 is a power of two. -/
def H3 : Prop := ∃ B : ℕ, ∀ p r : ℕ, p.Prime → Odd p → 3 < p → r.Prime → 17 ≤ r →
    (∃ b : ℕ, p+1=2^b ∧ (2^(b-1) ∣ r-1 → ∃ t : ℕ, r-1=2^t) ∧
      (r=17 → 131073 < b ∧ (∃ z ∈ ([(1,151424057718062388869),(361,145667772990363991280),(673,93751790033793536276),(841,202901096132581285882),(1201,227989676659606258431),(1321,12297791404224717320),(1513,247474687640128234574),(1681,74171282362119574805),(1793,151805376059737309979),(1873,98093190462001381696),(2161,135450721927820790012)] : List (ℕ × ℕ)), b%2520=z.1 ∧ z.2.testBit (b%171360/2520)=true))) →
    (p=7 → ∃ m : ℕ, m.Prime ∧ r=2*m+1) → B < p^r →
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
      q ∣ p^r+d ∧ s ∣ p^r+d

theorem main : H1 → H2 → H3 → type_of% @Erdos889.erdos_889.variants.v1_eq_1_finite := by
  rintro ⟨A, primeCase⟩ ⟨B0, narrowSquares⟩ ⟨C, mersenneCase⟩
  have squares : ∃ B : ℕ, ∀ p : ℕ, p.Prime → Odd p → B < p^2 →
      ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
        q ∣ p^2+d ∧ s ∣ p^2+d := by
    refine ⟨B0+49, ?_⟩
    intro p pp op large
    by_contra missing
    have greater : 7 < p := by
      by_contra! small
      have lim := Nat.pow_le_pow_left small 2
      norm_num at lim
      omega
    obtain ⟨q,r,a,b,pq,pr,ne,rq,rr,ap,no4,bp,ob,f1,f3⟩ :=
      square_survivor pp op (by omega) missing
    have cb := square_third_exponent pp (by omega) pr.one_lt ob f3
    have qlarge : 3 < q := by have := pq.two_le; omega
    have qo := pq.odd_of_ne_two (by omega)
    have b1 := square_third_exponent_one mersenne_power_exponent mersenne_left_factor pp pr rr f3 cb missing
    have third : p^2+3=4*r := by simpa only [b1,pow_one] using f3
    have first : p^2+1=2*q := by
      rcases square_first_exponent pp (by omega) qo pq.one_lt ap no4 f1 with one|two
      · simpa only [one,pow_one] using f1
      · rw [two] at f1
        obtain ⟨u,v,pu,pv,ne',hu,hv,du,dv⟩ := square_first_not_square op greater f1
        exact False.elim (missing ⟨2,u,v,pu,pv,ne',hu,hv,du,dv⟩)
    obtain ⟨t,c,e,pt,lt,tm,cp,ep,mid⟩ := square_middle pp op (by omega) missing
    have cop := square_middle_exponents_coprime pp op lt ep mid
    have ev := square_middle_even_exponent pp (by omega) cop mid
    have nf := square_middle_exponent_not_four fourth_power_witness pp (by omega) pq first
      (pt.odd_of_ne_two (by omega)) lt ep cop mid missing
    have evenCase (h : Even e) : c=1 ∧ e=2 := by
      have one := ev h
      have eq1 : p^2+2=3*t^e := by simpa only [one,pow_one] using mid
      exact ⟨one,square_middle_even_exponent_two odd_root_with_unique_odd_prime pp (by omega)
        (pt.odd_of_ne_two (by omega)) lt ep h nf eq1 missing⟩
    exact missing (narrowSquares p pp op (by omega)
      ⟨q,r,pq,pr,ne,rq,rr,first,third⟩
      ⟨t,c,e,pt,lt,tm,cp,ep,cop,evenCase,mid⟩)
  obtain ⟨B, dyadicCase⟩ := dyadic_of_prime_squares squares
  refine (Set.finite_le_nat (A+B+C+60)).subset ?_
  intro n hn
  change v_l 1 n = 1 at hn
  change n ≤ A+B+C+60
  by_contra! big
  rcases Nat.even_or_odd n with ev|od
  · obtain ⟨p, a, pp, op, apos, no3, he⟩ := even_solution_shape (by omega) ev (by omega) hn
    have witness : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
        q ∣ p^a+d ∧ s ∣ p^a+d := by
      rcases successor_exponent pp op apos he hn with ⟨t, ht⟩ | ⟨pr, oa, base⟩
      · subst a
        cases t with
        | zero =>
          simp only [pow_zero, pow_one] at he ⊢
          apply primeCase p pp op (by omega)
          · intro x hx eq
            have nx : n=x^4 := by omega
            have sol : v_l 1 (x^4)=1 := nx ▸ hn
            rcases (higher_perfect_power hx (by decide : 3≤4)).mp sol with h|h <;> omega
          · exact prime_successor_survivor pp he (by omega) hn
        | succ t => exact dyadicCase p (t+1) pp op (by omega) (by omega)
      · have exc : ¬(a=5 ∨ a=7 ∨ a=11 ∨ a=13) := fun h => fifth_seventh_eleventh_thirteenth_exclusion pp.one_lt h he hn
        have a17 : 17 ≤ a := by
          obtain ⟨w, hw⟩ := oa
          have := pr.two_le
          omega
        have p3 : 3 < p := by
          by_contra! lim
          have p2 := pp.two_le
          obtain ⟨z,hz⟩ := op
          have equal : p=3 := by omega
          rw [equal] at he
          exact three_large_prime_exponent pr (by omega) he hn
        obtain ⟨j,hj⟩ := base
        by_cases witness17 : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
            q ∣ p^a+d ∧ s ∣ p^a+d
        · exact witness17
        have rem17 (h : a=17) := seventeen_surviving_lift pp hj (by simpa only [h] using witness17)
        exact mersenneCase p a pp op p3 pr a17
          ⟨j,hj,mersenne_exponent_alignment pp op hj oa (by omega) he hn,rem17⟩
          (by rintro rfl; exact seven_safe_prime_exponent pr (by omega) he hn) (by omega)
    obtain ⟨d,q,s,pq,ps,ne,hq,hs,dq,ds⟩ := witness
    have equal : n+(d+1)=p^a+d := by omega
    exact two_primes (k:=d+1) (by omega) pq ps ne hq hs (equal ▸ dq) (equal ▸ ds) hn
  · rcases (odd_classification od).mp hn with h|h|h|h <;> omega

end OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

