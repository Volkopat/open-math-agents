import OMAReductions.R_WeakTiling_problem_4_2_R1_H2_R1
import Mathlib

/-! For three points, the weak tiling equation forces a subgroup of unit weights. -/

open Finset
open scoped ENNReal

private theorem window {d q j v k : ℤ} (hd : 0 < d) (hq : 0 < q) (hk : 0 ≤ k)
    (hkd : k + q ≤ d) (hv : v % d = k) :
    (j - v) % d < q ↔ k ≤ j % d ∧ j % d < k + q := by
  have hj0 := Int.emod_nonneg j hd.ne'
  have hjd := Int.emod_lt_of_pos j hd
  rw [Int.sub_emod, hv]
  by_cases h : k ≤ j % d
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  · rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
    omega

private theorem add_eq_one_zero {x y : ℝ≥0∞} (h : 1 + x + y = 1) : x = 0 ∧ y = 0 := by
  have h' : 1 + (x + y) = 1 + 0 := by simpa [← add_assoc] using h
  have he : x + y = 0 := (ENNReal.add_right_inj (by simp)).mp h'
  exact add_eq_zero.mp he

private theorem pairTile {x y : ℤ} (hxy : x < y) :
    ∃ C : Set ℤ, 0 ∈ C ∧ ∀ j : ℤ, ∃! t : ℤ, t ∈ C ∧ j - t ∈ ({x,y} : Finset ℤ) := by
  let q := y - x
  let d := 2 * q
  have hq : 0 < q := by dsimp [q]; omega
  have hd : 0 < d := by dsimp [d]; omega
  let C : Set ℤ := {t | t % d < q}
  refine ⟨C, by simpa [C] using hq, fun j => ?_⟩
  have h0 : j - x ∈ C ↔ (j-x)%d < q := Iff.rfl
  have h1 : j - y ∈ C ↔ q ≤ (j-x)%d := by
    change (j-y)%d < q ↔ _
    rw [show j-y = (j-x)-q by dsimp [q]; ring]
    rw [window hd hq (le_of_lt hq) (by dsimp [d]; omega)
      (Int.emod_eq_of_lt hq.le (by dsimp [d]; omega))]
    have := Int.emod_lt_of_pos (j-x) hd
    have hupper : (j-x)%d < 2*q := this
    omega
  have hj (t : ℤ) : j - t ∈ ({x,y} : Finset ℤ) ↔ t = j-x ∨ t = j-y := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  by_cases hr : (j-x)%d < q
  · refine ⟨j-x, ⟨h0.mpr hr, (hj _).2 (.inl rfl)⟩, ?_⟩
    intro t ht
    rcases (hj _).mp ht.2 with rfl | rfl
    · rfl
    · exact (not_le_of_gt hr (h1.mp ht.1)).elim
  · refine ⟨j-y, ⟨h1.mpr (le_of_not_gt hr), (hj _).2 (.inr rfl)⟩, ?_⟩
    intro t ht
    rcases (hj _).mp ht.2 with rfl | rfl
    · exact (hr (h0.mp ht.1)).elim
    · rfl

private theorem unitWeights {a b : ℤ} (w : ℤ → ℝ≥0∞) (w0 : w 0 = 1)
    (row : ∀ j : ℤ, w j + w (j-a) + w (j-b) = 1) :
    ∀ (u v : ℤ), w ((a+b)*u + (3*a)*v) = 1 := by
  have step (t : ℤ) (ht : w t = 1) :
      w (t+(a+b)) = 1 ∧ w (t+(b-2*a)) = 1 ∧ w (t+(a-2*b)) = 1 := by
    have h0 := add_eq_one_zero (by simpa only [ht] using row t)
    have ha' := row (t+a)
    rw [show t+a-a=t by ring, ht, add_comm (w (t+a)) 1] at ha'
    have ha := add_eq_one_zero ha'
    have hb' := row (t+b)
    rw [show t+b-b=t by ring, ht, add_comm (w (t+b) + w (t+b-a)) 1, ← add_assoc] at hb'
    have hb := add_eq_one_zero hb'
    refine ⟨?_, ?_, ?_⟩
    · simpa only [show t+(a+b)-a=t+b by ring, show t+(a+b)-b=t+a by ring,
        ha.1, hb.1, add_zero] using row (t+(a+b))
    · have h := row (t+(b-a))
      rw [show t+(b-a)-a=t+(b-2*a) by ring, show t+(b-a)-b=t-a by ring,
        show t+(b-a)=t+b-a by ring, hb.2, h0.1, zero_add, add_zero] at h
      exact h
    · have h := row (t+(a-b))
      rw [show t+(a-b)-a=t-b by ring, show t+(a-b)-b=t+(a-2*b) by ring,
        show t+(a-b)=t+a-b by ring, ha.2, h0.2, zero_add, zero_add] at h
      exact h
  have back (t : ℤ) (ht : w t = 1) :
      w (t-(a+b)) = 1 ∧ w (t-(b-2*a)) = 1 := by
    constructor
    · simpa only [show t+(b-2*a)+(a-2*b)=t-(a+b) by ring] using
        (step _ (step t ht).2.1).2.2
    · simpa only [show t+(a+b)+(a-2*b)=t-(b-2*a) by ring] using
        (step _ (step t ht).1).2.2
  have triple (t : ℤ) (ht : w t = 1) : w (t+3*a) = 1 ∧ w (t-3*a) = 1 := by
    constructor
    · simpa only [show t+(a+b)-(b-2*a)=t+3*a by ring] using
        (back _ (step t ht).1).2
    · simpa only [show t+(b-2*a)-(a+b)=t-3*a by ring] using
        (back _ (step t ht).2.1).1
  have first (u : ℤ) : w ((a+b)*u) = 1 := by
    refine Int.inductionOn' u 0 ?_ ?_ ?_
    · simpa using w0
    · intro k _ ih
      simpa only [show (a+b)*k+(a+b)=(a+b)*(k+1) by ring] using (step _ ih).1
    · intro k _ ih
      simpa only [show (a+b)*k-(a+b)=(a+b)*(k-1) by ring] using (back _ ih).1
  intro u v
  refine Int.inductionOn' v 0 ?_ ?_ ?_
  · simpa using first u
  · intro k _ ih
    simpa only [show (a+b)*u+3*a*k+3*a=(a+b)*u+3*a*(k+1) by ring] using
      (triple _ ih).1
  · intro k _ ih
    simpa only [show (a+b)*u+3*a*k-3*a=(a+b)*u+3*a*(k-1) by ring] using
      (triple _ ih).2

private theorem residueBands {a b d : ℤ} (hd : 0 < d) (ha : ¬ d ∣ a)
    (hd1 : d ∣ a+b) (hd3 : d ∣ 3*a) :
    ∃ q : ℤ, 0 < q ∧ d = 3*q ∧
      ((a%d=q ∧ b%d=2*q) ∨ (a%d=2*q ∧ b%d=q)) := by
  let r := a % d
  let s := b % d
  have hr : 0 < r := lt_of_le_of_ne (Int.emod_nonneg a hd.ne')
    (Ne.symm (mt Int.dvd_of_emod_eq_zero ha))
  have hrd : r < d := Int.emod_lt_of_pos a hd
  have hs0 : 0 ≤ s := Int.emod_nonneg b hd.ne'
  have hsd : s < d := Int.emod_lt_of_pos b hd
  have hsumMod : (r+s)%d=0 := by
    dsimp [r,s]
    rw [← Int.add_emod, Int.emod_eq_zero_of_dvd hd1]
  have hsum : r+s=d := by
    by_cases hh : r+s<d
    · rw [Int.emod_eq_of_lt (by omega) hh] at hsumMod
      omega
    · rw [← Int.sub_emod_right, Int.emod_eq_of_lt (by omega) (by omega)] at hsumMod
      omega
  obtain ⟨m, hm⟩ := hd3
  have hra : r + d*(a/d) = a := Int.emod_add_mul_ediv a d
  let k := m - 3*(a/d)
  have hk : 3*r = d*k := by
    dsimp [k]
    linear_combination hm + 3*hra
  have hlo : 1 ≤ k := by
    by_contra! h
    have := mul_nonpos_of_nonneg_of_nonpos hd.le (show k ≤ 0 by omega)
    omega
  have hhi : k ≤ 2 := by
    by_contra! h
    have := mul_le_mul_of_nonneg_left (show 3 ≤ k by omega) hd.le
    omega
  interval_cases k
  · simp only [mul_one] at hk
    exact ⟨r, hr, by omega, .inl ⟨rfl, by change s = 2*r; omega⟩⟩
  · refine ⟨s, by omega, by omega, .inr ⟨?_, rfl⟩⟩
    change r = 2*s
    linarith

private theorem threeTile {x y z : ℤ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (w : ℤ → ℝ≥0∞) (w0 : w 0 = 1)
    (cover : ∀ j : ℤ, ∑ t ∈ ({x,y,z} : Finset ℤ), w (j-t) = 1) :
    ∃ C : Set ℤ, 0 ∈ C ∧ ∀ j : ℤ, ∃! t : ℤ, t ∈ C ∧ j-t ∈ ({x,y,z} : Finset ℤ) := by
  let a := y-x
  let b := z-x
  have ha0 : a ≠ 0 := by dsimp [a]; omega
  have row (j : ℤ) : w j + w (j-a) + w (j-b) = 1 := by
    have h := cover (j+x)
    rw [Finset.sum_insert (by simp [hxy,hxz]), Finset.sum_insert (by simp [hyz]),
      Finset.sum_singleton] at h
    simpa only [show j+x-x=j by ring, show j+x-y=j-a by dsimp [a]; ring,
      show j+x-z=j-b by dsimp [b]; ring, add_assoc] using h
  let d : ℤ := Int.gcd (a+b) (3*a)
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast Int.gcd_pos_of_ne_zero_right (a+b) (by omega : 3*a ≠ 0)
  have hunit : ∀ k : ℤ, w (d*k) = 1 := by
    intro k
    rw [show d = (a+b)*Int.gcdA (a+b) (3*a) + (3*a)*Int.gcdB (a+b) (3*a) from
      Int.gcd_eq_gcd_ab ..]
    rw [add_mul, mul_assoc, mul_assoc]
    exact unitWeights w w0 row _ _
  have hnd : ¬ d ∣ a := by
    rintro ⟨k, hk⟩
    have h1 : w a = 1 := hk ▸ hunit k
    have ha := row a
    rw [sub_self, w0, h1] at ha
    have bad := add_eq_one_zero ha
    simp at bad
  obtain ⟨q,hq,hdq,hab⟩ := residueBands hd hnd (Int.gcd_dvd_left ..) (Int.gcd_dvd_right ..)
  let C : Set ℤ := {t | t%d<q}
  refine ⟨C, by simpa [C] using hq, fun j => ?_⟩
  let r := (j-x)%d
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hd.ne'
  have hrd : r < d := Int.emod_lt_of_pos _ hd
  have hx : j-x ∈ C ↔ r<q := Iff.rfl
  have hw (v k : ℤ) (hk : 0 ≤ k) (hkd : k+q ≤ d) (hv : v%d=k) :
      j-x-v ∈ C ↔ k ≤ r ∧ r < k+q := window hd hq hk hkd hv
  have hy (k : ℤ) (hk : 0 ≤ k) (hkd : k+q ≤ d) (hv : a%d=k) :
      j-y ∈ C ↔ k ≤ r ∧ r < k+q := by
    rw [show j-y=j-x-a by dsimp [a]; ring]
    exact hw a k hk hkd hv
  have hz (k : ℤ) (hk : 0 ≤ k) (hkd : k+q ≤ d) (hv : b%d=k) :
      j-z ∈ C ↔ k ≤ r ∧ r < k+q := by
    rw [show j-z=j-x-b by dsimp [b]; ring]
    exact hw b k hk hkd hv
  have candidate (t : ℤ) : j-t ∈ ({x,y,z} : Finset ℤ) ↔ t=j-x ∨ t=j-y ∨ t=j-z := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have finish (u v : ℤ) (hs : ∀ t, t = j-x ∨ t = u ∨ t = v ↔
      j-t ∈ ({x,y,z} : Finset ℤ))
      (hu : u ∈ C ↔ q≤r ∧ r<q+q)
      (hv : v ∈ C ↔ 2*q≤r ∧ r<2*q+q) :
      ∃! t, t ∈ C ∧ j-t ∈ ({x,y,z} : Finset ℤ) := by
    by_cases h : r < q
    · refine ⟨j-x, ⟨hx.mpr h, (hs _).mp (.inl rfl)⟩, ?_⟩
      intro t ht
      rcases (hs _).mpr ht.2 with rfl | rfl | rfl
      · rfl
      · have := (hu.mp ht.1).1
        omega
      · have := (hv.mp ht.1).1
        omega
    · by_cases h' : r < 2*q
      · refine ⟨u, ⟨hu.mpr ⟨by omega, by omega⟩, (hs _).mp (.inr (.inl rfl))⟩, ?_⟩
        intro t ht
        rcases (hs _).mpr ht.2 with rfl | rfl | rfl
        · exact (h (hx.mp ht.1)).elim
        · rfl
        · have := (hv.mp ht.1).1
          omega
      · refine ⟨v, ⟨hv.mpr ⟨by omega, by omega⟩, (hs _).mp (.inr (.inr rfl))⟩, ?_⟩
        intro t ht
        rcases (hs _).mpr ht.2 with rfl | rfl | rfl
        · exact (h (hx.mp ht.1)).elim
        · have := (hu.mp ht.1).2
          omega
        · rfl
  rcases hab with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact finish (j-y) (j-z) (fun t => (candidate t).symm)
      (hy q (by omega) (by omega) ha) (hz (2*q) (by omega) (by omega) hb)
  · exact finish (j-z) (j-y) (fun t => by rw [candidate, or_comm (a := t=j-z)])
      (hz q (by omega) (by omega) hb) (hy (2*q) (by omega) (by omega) ha)

private theorem smallTile (A : Finset ℤ) (hA : A.Nonempty) (hc : A.card ≤ 3)
    (weak : ∃ w : ℤ → ℝ≥0∞, w 0 = 1 ∧ ∀ j, ∑ a ∈ A, w (j-a) = 1) :
    ∃ C : Set ℤ, 0 ∈ C ∧ ∀ j : ℤ, ∃! t : ℤ, t ∈ C ∧ j-t ∈ A := by
  have hp := Finset.card_pos.mpr hA
  have hc' : A.card = 1 ∨ A.card = 2 ∨ A.card = 3 := by omega
  rcases hc' with hc' | hc' | hc'
  · obtain ⟨x,rfl⟩ := Finset.card_eq_one.mp hc'
    refine ⟨Set.univ, trivial, fun j => ⟨j-x, by simp, ?_⟩⟩
    intro t ht
    have := Finset.mem_singleton.mp ht.2
    omega
  · obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hc'
    rcases lt_or_gt_of_ne hxy with h | h
    · exact pairTile h
    · simpa only [Finset.pair_comm x y] using pairTile h
  · obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩ := Finset.card_eq_three.mp hc'
    obtain ⟨w,w0,cover⟩ := weak
    exact threeTile hxy hxz hyz w w0 cover

theorem OMA.solution : OMA.R_WeakTiling_problem_4_2_R1_H2_R1.H1 := smallTile