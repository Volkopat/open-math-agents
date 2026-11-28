import OMAStatements.S_mo_109343
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Optimal Gear Trains

Source: Joseph O'Rourke, https://mathoverflow.net/questions/109343
Credit: @LDJAI

The first part proves the finite dynamic program correct. The second derives
sharp multiplicative certificates for the two concrete optimization questions.
-/

namespace OMA.S_mo_109343

lemma weight_mono (m : Cost) {x y : ℕ} (h : x ≤ y) : weight m x ≤ weight m y := by
  cases m with
  | teeth => exact h
  | metal => exact Nat.mul_le_mul h h

lemma le_weight (m : Cost) (x : ℕ) : x ≤ weight m x := by
  cases m with
  | teeth => exact le_rfl
  | metal => exact Nat.le_mul_self x

lemma side_step (m : Cost) (x : ℕ) (xs : List ℕ) :
    sideCost m (x :: xs) = weight m x + sideCost m xs := by
  simp [sideCost]

lemma side_floor (m : Cost) {t : ℕ} {xs : List ℕ} (hx : ∀ x ∈ xs, t ≤ x) :
    xs.length * weight m t ≤ sideCost m xs := by
  induction xs with
  | nil => simp [sideCost]
  | cons x xs ih =>
    simp only [List.forall_mem_cons] at hx
    simpa [side_step, Nat.succ_mul, Nat.add_comm] using
      Nat.add_le_add (weight_mono m hx.1) (ih hx.2)

lemma side_sound (m : Cost) (t cap k : ℕ) {s : ℕ × ℕ}
    (hs : s ∈ sideTable m t cap k) :
    ∃ xs : List ℕ, xs.length = k ∧ (∀ x ∈ xs, t ≤ x) ∧
      xs.prod = s.1 ∧ sideCost m xs = s.2 := by
  induction k generalizing s with
  | zero =>
    have h : s = (1, 0) := by simpa [sideTable] using hs
    subst s
    exact ⟨[], by simp [sideCost]⟩
  | succ k ih =>
    rw [sideTable, Finset.mem_filter] at hs
    obtain ⟨⟨u, x⟩, hux, rfl⟩ := Finset.mem_image.mp hs.1
    obtain ⟨hu, hx⟩ := Finset.mem_product.mp hux
    have htx := (Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1).1
    obtain ⟨xs, hk, hall, hp, hc⟩ := ih hu
    exact ⟨x :: xs, by simp [hk], List.forall_mem_cons.mpr ⟨htx, hall⟩,
      by simp [hp, Nat.mul_comm], by simp [side_step, hc, Nat.add_comm]⟩

lemma side_complete (m : Cost) {t cap : ℕ} {xs : List ℕ}
    (hx : ∀ x ∈ xs, t ≤ x) (hc : sideCost m xs ≤ cap) :
    (xs.prod, sideCost m xs) ∈ sideTable m t cap xs.length := by
  induction xs with
  | nil => simp [sideTable, sideCost]
  | cons x xs ih =>
    rw [List.forall_mem_cons] at hx
    rw [side_step] at hc
    have hw : weight m x ≤ cap := by omega
    have ht : sideCost m xs ≤ cap := by omega
    rw [List.length_cons, sideTable, Finset.mem_filter]
    refine ⟨Finset.mem_image.mpr ⟨((xs.prod, sideCost m xs), x), ?_, ?_⟩, ?_⟩
    · exact Finset.mem_product.mpr ⟨ih hx.2 ht, Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hx.1, (le_weight m x).trans hw⟩, hw⟩⟩
    · simp [side_step, Nat.mul_comm, Nat.add_comm]
    · simpa only [side_step] using hc

lemma join_sound (m : Cost) {t a b cap k c : ℕ} (hc : c ∈ costsAt m t a b cap k) :
    ∃ g : Train, feasible t a b g ∧ cost m g = c := by
  obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨hmem, hratio, _⟩ := Finset.mem_filter.mp huv
  obtain ⟨hu, hv⟩ := Finset.mem_product.mp hmem
  obtain ⟨xs, hk, hx, hp, hw⟩ := side_sound m t cap k hu
  obtain ⟨ys, hl, hy, hq, hz⟩ := side_sound m t cap k hv
  exact ⟨(xs, ys), ⟨hk.trans hl.symm, hx, hy, by simpa only [hp, hq] using hratio⟩,
    by simp [cost, hw, hz]⟩

lemma join_complete (m : Cost) {t a b cap : ℕ} {g : Train} (hg : feasible t a b g)
    (hc : cost m g ≤ cap) : cost m g ∈ costsAt m t a b cap g.1.length := by
  obtain ⟨hlen, hx, hy, hr⟩ := hg
  change sideCost m g.1 + sideCost m g.2 ≤ cap at hc
  have h₁ := side_complete m hx (show sideCost m g.1 ≤ cap by omega)
  have h₂ := side_complete m hy (show sideCost m g.2 ≤ cap by omega)
  rw [← hlen] at h₂
  exact Finset.mem_image.mpr ⟨((g.1.prod, sideCost m g.1), (g.2.prod, sideCost m g.2)),
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h₁, h₂⟩, hr, hc⟩, rfl⟩

lemma stage_bound (m : Cost) {t a b cap : ℕ} (ht : 0 < t) {g : Train}
    (hg : feasible t a b g) (hc : cost m g ≤ cap) : g.1.length ≤ cap / (2 * weight m t) := by
  obtain ⟨hlen, hx, hy, _⟩ := hg
  have h₁ := side_floor m hx
  have h₂ := side_floor m hy
  rw [← hlen] at h₂
  have hw := le_weight m t
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2 * weight m t)).mpr
  calc g.1.length * (2 * weight m t) = g.1.length * weight m t + g.1.length * weight m t := by ring
       _ ≤ cost m g := Nat.add_le_add h₁ h₂
       _ ≤ cap := hc

lemma direct_feasible {t a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    feasible t a b ([t * a], [t * b]) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simpa using Nat.le_mul_of_pos_right t ha
  · simpa using Nat.le_mul_of_pos_right t hb
  · simp
    ring

lemma solve_general (m : Cost) {t a b : ℕ} (ht : 0 < t) {seed : Train}
    (hs : feasible t a b seed) :
    (∃ g, optimal m t a b g) ∧ ∀ g, optimal m t a b g ↔
      feasible t a b g ∧ cost m g = bestCost m t a b (cost m seed) := by
  let cap := cost m seed
  let values := (Finset.range (cap / (2 * weight m t) + 1)).biUnion (costsAt m t a b cap)
  let entries := insert cap values
  have hne : entries.Nonempty := Finset.insert_nonempty _ _
  let best := entries.min' hne
  have hbest : best ∈ entries := Finset.min'_mem _ _
  have hex : ∃ g, feasible t a b g ∧ cost m g = best := by
    rcases Finset.mem_insert.mp hbest with h | h
    · exact ⟨seed, hs, h.symm⟩
    · obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp h
      exact join_sound m hk
  obtain ⟨winner, hwin, heq⟩ := hex
  have lower : ∀ g, feasible t a b g → best ≤ cost m g := by
    intro g hg
    by_cases hc : cost m g ≤ cap
    · apply Finset.min'_le
      apply Finset.mem_insert_of_mem
      exact Finset.mem_biUnion.mpr ⟨g.1.length, Finset.mem_range.mpr
        (Nat.lt_succ_of_le (stage_bound m ht hg hc)), join_complete m hg hc⟩
    · have h := Finset.min'_le entries cap (Finset.mem_insert_self ..)
      exact h.trans (by omega)
  refine ⟨⟨winner, hwin, fun g hg => heq.le.trans (lower g hg)⟩, ?_⟩
  intro g
  constructor
  · rintro ⟨hg, hmin⟩
    exact ⟨hg, le_antisymm ((hmin winner hwin).trans_eq heq) (lower g hg)⟩
  · rintro ⟨hg, he⟩
    exact ⟨hg, fun h hh => he.le.trans (lower h hh)⟩


/-- An integer-valued multiplicative potential for the eight-tooth minimum. -/
def potential (n : ℕ) : ℕ := n ^ 19 * 2 ^ n.factorization 2

lemma potential_mul {x y : ℕ} (hx : 0 < x) (hy : 0 < y) :
    potential (x * y) = potential x * potential y := by
  simp only [potential, mul_pow, Nat.factorization_mul hx.ne' hy.ne', Finsupp.add_apply, pow_add]
  ring

lemma potential_two_pow (j : ℕ) : potential (2 ^ j) = 2 ^ (20 * j) := by
  rw [potential, Nat.factorization_pow_self Nat.prime_two, ← pow_mul, ← pow_add]
  congr 1
  omega

lemma potential_pos {n : ℕ} (hn : 0 < n) : 0 < potential n :=
  Nat.mul_pos (Nat.pow_pos hn) (Nat.pow_pos (by decide))

lemma potential_input {x : ℕ} (hx : 8 ≤ x) : 2 ^ 68 ≤ 2 ^ x * potential x := by
  rcases hx.eq_or_lt with h | h
  · subst x
    change 2 ^ 68 ≤ 2 ^ 8 * potential (2 ^ 3)
    rw [potential_two_pow]
    decide
  · calc (2 : ℕ) ^ 68 ≤ 2 ^ 9 * 9 ^ 19 := by decide
         _ ≤ 2 ^ x * x ^ 19 :=
           Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) h) (Nat.pow_le_pow_left h 19)
         _ ≤ 2 ^ x * potential x := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _
           (Nat.pow_pos (by decide : 0 < 2)))

lemma power_step {n : ℕ} (hn : 32 ≤ n) : (n + 1) ^ 20 ≤ 2 * n ^ 20 := by
  have hr : 32 * (n + 1) ≤ 33 * n := by omega
  have hp := Nat.pow_le_pow_left hr 20
  rw [mul_pow, mul_pow] at hp
  have hsmall : (33 : ℕ) ^ 20 ≤ 32 ^ 20 * 2 := by decide
  apply Nat.le_of_mul_le_mul_left (c := 32 ^ 20) _ (by decide)
  calc (32 : ℕ) ^ 20 * (n + 1) ^ 20 ≤ 33 ^ 20 * n ^ 20 := hp
       _ ≤ (32 ^ 20 * 2) * n ^ 20 := Nat.mul_le_mul_right _ hsmall
       _ = 32 ^ 20 * (2 * n ^ 20) := Nat.mul_assoc ..

lemma power_tail {n : ℕ} (hn : 32 ≤ n) : n ^ 20 ≤ 2 ^ (n + 68) := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    calc (n + 1) ^ 20 ≤ 2 * n ^ 20 := power_step hn
         _ ≤ 2 * 2 ^ (n + 68) := Nat.mul_le_mul_left 2 ih
         _ = 2 ^ ((n + 68) + 1) := (pow_succ' 2 (n + 68)).symm
         _ = 2 ^ (n + 1 + 68) := by rw [show n + 1 + 68 = (n + 68) + 1 by omega]

lemma potential_output {y : ℕ} (hy : 8 ≤ y) : potential y ≤ 2 ^ (y + 68) := by
  by_cases h : y < 32
  · have hd := Nat.ordProj_dvd y 2
    have hpos : 0 < y := by omega
    have hle := Nat.le_of_dvd hpos hd
    have hv : y.factorization 2 ≤ 5 :=
      (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hle.trans (by omega : y ≤ 2 ^ 5))
    have hg : 2 ^ y.factorization 2 ≤ y.gcd 32 :=
      Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hpos) (Nat.dvd_gcd hd (Nat.pow_dvd_pow 2 hv))
    calc potential y ≤ y ^ 19 * y.gcd 32 := Nat.mul_le_mul_left _ hg
         _ ≤ 2 ^ (y + 68) := by interval_cases y <;> decide
  · calc potential y ≤ y ^ 19 * y :=
           Nat.mul_le_mul_left _ (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd y 2))
         _ = y ^ 20 := (pow_succ y 19).symm
         _ ≤ 2 ^ (y + 68) := power_tail (by omega)

lemma product_positive {t : ℕ} (ht : 0 < t) {xs : List ℕ} (hx : ∀ x ∈ xs, t ≤ x) :
    0 < xs.prod := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    rw [List.forall_mem_cons] at hx
    exact Nat.mul_pos (ht.trans_le hx.1) (ih hx.2)

/-- A per-gear bound telescopes through arbitrary cancellations in a train. -/
lemma certificate (m : Cost) (t q : ℕ) (f : ℕ → ℕ) (ht : 0 < t)
    (hmul : ∀ x y, 0 < x → 0 < y → f (x * y) = f x * f y)
    (hin : ∀ x, t ≤ x → 2 ^ q ≤ 2 ^ weight m x * f x)
    (hout : ∀ y, t ≤ y → f y ≤ 2 ^ (weight m y + q))
    (xs ys : List ℕ) (hlen : xs.length = ys.length)
    (hx : ∀ x ∈ xs, t ≤ x) (hy : ∀ y ∈ ys, t ≤ y) :
    f ys.prod ≤ 2 ^ (sideCost m xs + sideCost m ys) * f xs.prod := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp [sideCost]
    | cons y ys => simp at hlen
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      rw [List.forall_mem_cons] at hx hy
      have hh := ih ys (by simpa using hlen) hx.2 hy.2
      have hxy : f y ≤ 2 ^ (weight m x + weight m y) * f x := by
        calc f y ≤ 2 ^ (weight m y + q) := hout y hy.1
             _ = 2 ^ weight m y * 2 ^ q := pow_add ..
             _ ≤ 2 ^ weight m y * (2 ^ weight m x * f x) := Nat.mul_le_mul_left _ (hin x hx.1)
             _ = _ := by rw [pow_add]; ring
      rw [List.prod_cons, List.prod_cons, hmul y _ (ht.trans_le hy.1) (product_positive ht hy.2),
        hmul x _ (ht.trans_le hx.1) (product_positive ht hx.2)]
      apply (Nat.mul_le_mul hxy hh).trans_eq
      simp only [sideCost, List.map_cons, List.sum_cons, pow_add]
      ring

lemma dyadic_bound (m : Cost) (t q : ℕ) (f : ℕ → ℕ) (ht : 0 < t)
    (hmul : ∀ x y, 0 < x → 0 < y → f (x * y) = f x * f y)
    (hpow : ∀ j, f (2 ^ j) = 2 ^ (20 * j)) (hpos : ∀ n, 0 < n → 0 < f n)
    (hin : ∀ x, t ≤ x → 2 ^ q ≤ 2 ^ weight m x * f x)
    (hout : ∀ y, t ≤ y → f y ≤ 2 ^ (weight m y + q))
    {j : ℕ} {g : Train} (hg : feasible t 1 (2 ^ j) g) : 20 * j ≤ cost m g := by
  obtain ⟨hlen, hx, hy, hr⟩ := hg
  have h := certificate m t q f ht hmul hin hout _ _ hlen hx hy
  have hp := product_positive ht hx
  simp only [one_mul] at hr
  rw [← hr, hmul _ _ (Nat.pow_pos (by decide)) hp, hpow] at h
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (Nat.le_of_mul_le_mul_right h (hpos _ hp))

lemma eight_tooth_bound {j : ℕ} {g : Train} (hg : feasible 8 1 (2 ^ j) g) :
    20 * j ≤ cost .teeth g := by
  exact dyadic_bound .teeth 8 68 potential (by decide) (fun _ _ => potential_mul)
    potential_two_pow (fun _ => potential_pos) (fun _ => potential_input) (fun _ => potential_output) hg

lemma metal_output (y : ℕ) : y ^ 20 ≤ 2 ^ (y * y + 24) := by
  by_cases hsmall : y < 10
  · interval_cases y <;> decide
  by_cases hy : y < 20
  · have hs := Nat.mul_le_mul (by omega : 10 ≤ y) (by omega : 10 ≤ y)
    calc y ^ 20 ≤ 32 ^ 20 := Nat.pow_le_pow_left (by omega) 20
         _ = 2 ^ 100 := by decide
         _ ≤ 2 ^ (y * y + 24) := Nat.pow_le_pow_right (by decide) (by omega)
  · calc y ^ 20 ≤ (2 ^ y) ^ 20 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 20
         _ = 2 ^ (y * 20) := (pow_mul ..).symm
         _ ≤ 2 ^ (y * y + 24) := Nat.pow_le_pow_right (by decide)
             (Nat.le_trans (Nat.mul_le_mul_left y (by omega : 20 ≤ y)) (by omega))

lemma two_metal_bound {j : ℕ} {g : Train} (hg : feasible 2 1 (2 ^ j) g) :
    20 * j ≤ cost .metal g := by
  apply dyadic_bound .metal 2 24 (fun n => n ^ 20) (by decide)
      (fun x y _ _ => mul_pow x y 20) _ (fun _ h => Nat.pow_pos h) _ (fun y _ => metal_output y) hg
  · intro j
    rw [← pow_mul, Nat.mul_comm]
  · intro x hx
    calc (2 : ℕ) ^ 24 = 2 ^ (2 * 2) * 2 ^ 20 := by decide
         _ ≤ 2 ^ (x * x) * x ^ 20 := Nat.mul_le_mul
           (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul hx hx)) (Nat.pow_le_pow_left hx 20)


/-- This includes every even power of two in Q1a. -/
lemma quarters_optimal (k : ℕ) : optimal .teeth 8 1 (4 ^ k) (quarters k) ∧
    cost .teeth (quarters k) = 40 * k := by
  have hratio : 4 ^ k * 8 ^ k = 32 ^ k := by rw [← mul_pow]; rfl
  have hfeas : feasible 8 1 (4 ^ k) (quarters k) := by
    refine ⟨by simp [quarters], ?_, ?_, ?_⟩
    · intro x hx
      have h := List.eq_of_mem_replicate hx
      omega
    · intro x hx
      have h := List.eq_of_mem_replicate hx
      omega
    · simpa [quarters, List.prod_replicate] using hratio
  have hc : cost .teeth (quarters k) = 40 * k := by
    simp [cost, sideCost, quarters, weight]
    omega
  refine ⟨⟨hfeas, ?_⟩, hc⟩
  intro g hg
  have he : (2 : ℕ) ^ (2 * k) = 4 ^ k := by rw [pow_mul]; rfl
  rw [← he] at hg
  have hl := eight_tooth_bound hg
  omega

/-- Classify every feasible 1/4 train having at most ten teeth in total. -/
lemma small_teeth {g : Train} (hg : feasible 2 1 4 g) (hc : cost .teeth g ≤ 10) :
    g = ([2], [8]) := by
  obtain ⟨xs, ys⟩ := g
  have hk := stage_bound .teeth (by decide : 0 < 2) hg hc
  change xs.length ≤ 2 at hk
  obtain ⟨hlen, hx, hy, hr⟩ := hg
  change xs.length = ys.length at hlen
  change 4 * xs.prod = 1 * ys.prod at hr
  change ∀ x ∈ xs, 2 ≤ x at hx
  change ∀ y ∈ ys, 2 ≤ y at hy
  cases xs with
  | nil =>
    have h : ys = [] := List.length_eq_zero_iff.mp hlen.symm
    subst ys
    simp at hr
  | cons x xs =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      cases xs with
      | nil =>
        have h : ys = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
        subst ys
        simp [cost, sideCost, weight] at hc
        simp at hr
        have hx₂ : 2 ≤ x := hx x (by simp)
        have ex : x = 2 := by omega
        have ey : y = 8 := by omega
        simp [ex, ey]
      | cons x' xs =>
        have exs : xs = [] := List.length_eq_zero_iff.mp (by
          change xs.length + 1 + 1 ≤ 2 at hk
          omega)
        subst xs
        cases ys with
        | nil => simp at hlen
        | cons y' ys =>
          have eys : ys = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
          subst ys
          simp [cost, sideCost, weight] at hc
          simp at hr
          have hx₁ : 2 ≤ x := hx x (by simp)
          have hx₂ : 2 ≤ x' := hx x' (by simp)
          have hy₁ : 2 ≤ y := hy y (by simp)
          have hy₂ : 2 ≤ y' := hy y' (by simp)
          have hu : 16 ≤ 4 * (x * x') :=
            Nat.mul_le_mul_left 4 (Nat.mul_le_mul hx₁ hx₂)
          have hs : y + y' ≤ 6 := by omega
          have hprod : y * y' ≤ 12 := by
            by_cases h : y ≤ 3
            · exact Nat.mul_le_mul h (by omega : y' ≤ 4)
            · exact (Nat.mul_le_mul (by omega : y ≤ 4) (by omega : y' ≤ 2)).trans (by decide)
          omega

lemma differing_objectives : optimal .teeth 2 1 4 ([2], [8]) ∧
    optimal .metal 2 1 4 ([2, 2], [4, 4]) ∧
    ¬ ∃ g, optimal .teeth 2 1 4 g ∧ optimal .metal 2 1 4 g := by
  have h₁ : feasible 2 1 4 ([2], [8]) := by norm_num [feasible]
  have h₂ : feasible 2 1 4 ([2, 2], [4, 4]) := by norm_num [feasible]
  have hcost : cost .teeth ([2], [8]) = 10 := by decide
  refine ⟨⟨h₁, ?_⟩, ⟨h₂, ?_⟩, ?_⟩
  · intro g hg
    by_cases h : cost .teeth g ≤ 10
    · rw [small_teeth hg h]
    · omega
  · intro g hg
    exact two_metal_bound (j := 2) hg
  · rintro ⟨g, ht, hm⟩
    have he := small_teeth ht.1 ((ht.2 _ h₁).trans_eq hcost)
    have h := hm.2 _ h₂
    rw [he] at h
    exact (by decide : ¬ cost .metal ([2], [8]) ≤ cost .metal ([2, 2], [4, 4])) h

end OMA.S_mo_109343

open OMA.S_mo_109343

theorem OMA.solution : type_of% @OMA.S_mo_109343.main := by
  refine ⟨fun _ _ _ _ ha hb => direct_feasible ha hb, ?_, ?_, ?_, differing_objectives⟩
  · exact fun m _ _ _ ht _ _ _ hs => solve_general m ht hs
  · exact quarters_optimal 4
  · exact quarters_optimal 8
