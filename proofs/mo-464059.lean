import OMAStatements.S_mo_464059
import Mathlib

namespace OMA.S_mo_464059

open Matrix
open scoped BigOperators

private theorem ip_symm (u v : Plane) : ip u v = ip v u := by
  unfold ip
  ring

private def area (u v : Plane) : ℝ := u.1 * v.2 - u.2 * v.1

private theorem area_identity (u v w : Plane) :
    ip u v * ip u w + area u v * area u w = ip u u * ip v w := by
  unfold ip area
  ring

private theorem area_sq {u v : Plane} (hu : unit u) (hv : unit v) :
    area u v ^ 2 = 1 - ip u v ^ 2 := by
  have h := area_identity u v v
  change ip u u = 1 at hu
  change ip v v = 1 at hv
  rw [hu, hv] at h
  nlinarith

private theorem ip_bound {u v : Plane} (hu : unit u) (hv : unit v) : ip u v ^ 2 ≤ 1 := by
  nlinarith [area_sq hu hv, sq_nonneg (area u v)]

private theorem det_factor (a b t : ℝ) :
    determinant a b t = (1 - a^2) * (1 - t^2) - (b - a*t)^2 := by
  unfold determinant
  ring

private theorem det_vanishes {u v w : Plane} (hu : unit u) (hv : unit v) (hw : unit w) :
    determinant (ip u v) (ip v w) (ip u w) = 0 := by
  have h := area_identity u v w
  change ip u u = 1 at hu
  rw [hu, one_mul] at h
  have hdiff : ip v w - ip u v * ip u w = area u v * area u w := by linarith
  rw [det_factor, ← area_sq hu hv, ← area_sq hu hw, hdiff, mul_pow, sub_self]

/-- A common pair of unit vectors realizes one prescribed triple of products. -/
private theorem planar_pair {a b t : ℝ} (ha : a^2 ≤ 1) (ht : t^2 ≤ 1)
    (hdet : determinant a b t = 0) :
    ∃ v : Plane, unit v ∧ ip (1, 0) v = a ∧ ip v (t, Real.sqrt (1-t^2)) = b := by
  let s := Real.sqrt (1 - t^2)
  have hs : s^2 = 1 - t^2 := Real.sq_sqrt (by linarith)
  rw [det_factor] at hdet
  have hpro : (b - a*t)^2 = (1 - a^2) * s^2 := by rw [hs]; linarith
  by_cases hz : s = 0
  · have hb : b - a*t = 0 := by
      rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] at hpro
      exact sq_eq_zero_iff.mp hpro
    have hc := Real.sq_sqrt (show 0 ≤ 1 - a^2 by linarith)
    refine ⟨(a, Real.sqrt (1-a^2)), ?_, ?_, ?_⟩
    · dsimp [unit, ip]
      nlinarith
    · simp [ip]
    · change a*t + Real.sqrt (1-a^2)*s = b
      rw [hz, mul_zero, add_zero]
      linarith
  · let q := (b - a*t) / s
    have hqs : q * s = b - a*t := div_mul_cancel₀ _ hz
    have hq : q^2 = 1 - a^2 := by
      apply mul_right_cancel₀ (pow_ne_zero 2 hz)
      rw [← mul_pow, hqs, hpro]
    refine ⟨(a, q), ?_, ?_, ?_⟩
    · dsimp [unit, ip]
      nlinarith
    · simp [ip]
    · change a*t + q*s = b
      rw [hqs]
      ring

private theorem plane_criterion (a b c d t : ℝ) :
    possible a b c d t ↔
      a^2 ≤ 1 ∧ d^2 ≤ 1 ∧ t^2 ≤ 1 ∧ determinant a b t = 0 ∧ determinant d c t = 0 := by
  constructor
  · rintro ⟨u, v, w, z, hu, hv, hw, hz, ha, hb, hc, hd, ht⟩
    have hdu : ip u z = d := (ip_symm u z).trans hd
    have hcz : ip z w = c := (ip_symm z w).trans hc
    exact ⟨ha ▸ ip_bound hu hv, hdu ▸ ip_bound hu hz, ht ▸ ip_bound hu hw,
      ha ▸ hb ▸ ht ▸ det_vanishes hu hv hw,
      hdu ▸ hcz ▸ ht ▸ det_vanishes hu hz hw⟩
  · rintro ⟨ha, hd, ht, h1, h2⟩
    obtain ⟨v, hv, hva, hvb⟩ := planar_pair ha ht h1
    obtain ⟨z, hz, hzd, hzc⟩ := planar_pair hd ht h2
    let w : Plane := (t, Real.sqrt (1-t^2))
    have hw : unit w := by
      have hs := Real.sq_sqrt (show 0 ≤ 1 - t^2 by linarith)
      dsimp [w, unit, ip]
      nlinarith
    exact ⟨(1, 0), v, w, z, by norm_num [unit, ip], hv, hw, hz, hva, hvb,
      (ip_symm w z).trans hzc, (ip_symm z (1, 0)).trans hzd, by simp [w, ip]⟩

private def planeVector (d : ℕ) (u : Plane) : Fin (d+2) → ℝ :=
  Pi.single 0 u.1 + Pi.single 1 u.2

private theorem plane_dot (d : ℕ) (u v : Plane) :
    dotProduct (planeVector d u) (planeVector d v) = ip u v := by
  have h01 : (0 : Fin (d+2)) ≠ 1 := by
    intro h
    have := congrArg Fin.val h
    simp at this
  unfold planeVector
  simp [h01, Ne.symm h01, ip]

private theorem planeVector_ne_zero (d : ℕ) (u : Plane) (hu : u.1 ≠ 0) :
    planeVector d u ≠ 0 := by
  intro h
  have h01 : (0 : Fin (d+2)) ≠ 1 := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have h0 := congrFun h 0
  exact hu (by simpa [planeVector, h01, Ne.symm h01] using h0)

private theorem complete_for_units (n d : ℕ) (G : SimpleGraph (Fin n)) :
    determines G (d+2) isUnit ↔ G = ⊤ := by
  classical
  constructor
  · intro h
    apply le_antisymm le_top
    intro i j hij
    have hij' := (SimpleGraph.top_adj i j).mp hij
    by_contra hnon
    let x (v : Fin n) : Plane := if v = i ∨ v = j then (0, 1) else (1, 0)
    let y (v : Fin n) : Plane := if v = i then (0, -1) else x v
    have hxu (v : Fin n) : isUnit (planeVector d (x v)) := by
      unfold isUnit
      rw [plane_dot]
      dsimp [x]
      split_ifs <;> norm_num [ip]
    have hyu (v : Fin n) : isUnit (planeVector d (y v)) := by
      by_cases hi : v = i
      · simp [isUnit, y, hi, plane_dot, ip]
      · simpa [y, hi] using hxu v
    have he (v w : Fin n) (ha : G.Adj v w) : ip (x v) (x w) = ip (y v) (y w) := by
      by_cases hv : v = i
      · subst v
        have hwi : w ≠ i := ha.ne.symm
        have hwj : w ≠ j := fun h => hnon (h ▸ ha)
        simp [x, y, hwi, hwj, ip]
      · by_cases hw : w = i
        · subst w
          have hvj : v ≠ j := fun h => hnon (h ▸ ha.symm)
          simp [x, y, hv, hvj, ip]
        · simp [y, hv, hw]
    have hall := h (fun v => planeVector d (x v)) (fun v => planeVector d (y v))
      hxu hyu (fun v w ha => by simpa only [plane_dot] using he v w ha) i j
    norm_num [plane_dot, x, y, hij', Ne.symm hij', ip] at hall
  · rintro rfl x y hx hy h i j
    by_cases hij : i = j
    · subst j
      exact (hx i).trans (hy i).symm
    · exact h i j ((SimpleGraph.top_adj i j).mpr hij)

private theorem unknown_planes (n d : ℕ) (G : SimpleGraph (Fin (n+1))) :
    ¬ determines G (d+2) (fun x => x ≠ 0) := by
  classical
  intro h
  let x (_ : Fin (n+1)) : Plane := (1, 0)
  let y (v : Fin (n+1)) : Plane := if v = 0 then (1, 1) else (1, 0)
  have hxu (v : Fin (n+1)) : planeVector d (x v) ≠ 0 := planeVector_ne_zero d _ one_ne_zero
  have hyu (v : Fin (n+1)) : planeVector d (y v) ≠ 0 := by
    apply planeVector_ne_zero
    dsimp [y]
    split_ifs <;> exact one_ne_zero
  have he (v w : Fin (n+1)) (ha : G.Adj v w) : ip (x v) (x w) = ip (y v) (y w) := by
    by_cases hv : v = 0
    · have hw : w ≠ 0 := fun e => ha.ne (hv.trans e.symm)
      simp [ip, x, y, hv, hw]
    · by_cases hw : w = 0 <;> simp [ip, x, y, hv, hw]
  have hall := h (fun v => planeVector d (x v)) (fun v => planeVector d (y v)) hxu hyu
    (fun v w ha => by simpa only [plane_dot] using he v w ha) 0 0
  norm_num [plane_dot, x, y, ip] at hall

private theorem dot_one (u v : Fin 1 → ℝ) : dotProduct u v = u 0 * v 0 := by
  rw [dotProduct, Fin.sum_univ_one]

private theorem const_nonzero {a : ℝ} (ha : a ≠ 0) : (fun _ : Fin 1 => a) ≠ 0 :=
  fun h => ha (congrFun h 0)

private theorem propagate {V : Type*} {G : SimpleGraph V} {i j : V}
    (h : G.Reachable i j) {P : V → Prop} (hi : P i)
    (hstep : ∀ {u v}, G.Adj u v → P u → P v) : P j := by
  rw [G.reachable_eq_reflTransGen] at h
  induction h with
  | refl => exact hi
  | tail _ hEdge ih => exact hstep hEdge ih

private theorem connected_of_determines {V : Type*} (G : SimpleGraph V)
    (P : (Fin 1 → ℝ) → Prop) (hplus : P (fun _ => 1)) (hminus : P (fun _ => -1))
    (h : determines G 1 P) : G.Preconnected := by
  classical
  intro i j
  by_contra hij
  let y (v : V) (_ : Fin 1) : ℝ := if G.Reachable i v then 1 else -1
  have hy (v : V) : P (y v) := by
    by_cases hv : G.Reachable i v
    · simpa [y, hv] using hplus
    · simpa [y, hv] using hminus
  have he (v w : V) (ha : G.Adj v w) :
      dotProduct (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 1) = dotProduct (y v) (y w) := by
    have hh : G.Reachable i v ↔ G.Reachable i w :=
      ⟨fun hv => hv.trans ha.reachable, fun hw => hw.trans ha.symm.reachable⟩
    by_cases hv : G.Reachable i v
    · simp [dot_one, y, hv, hh.mp hv]
    · have hw : ¬G.Reachable i w := fun hw => hv (hh.mpr hw)
      norm_num [dot_one, y, hv, hw]
  have hbad := h (fun _ _ => 1) y (fun _ => hplus) hy he i j
  norm_num [dot_one, y, hij, SimpleGraph.Reachable.refl] at hbad

private theorem ratio_edges {V : Type*} (G : SimpleGraph V) (x y : V → Fin 1 → ℝ)
    (hx : ∀ i, x i 0 ≠ 0)
    (h : ∀ i j, G.Adj i j → dotProduct (x i) (x j) = dotProduct (y i) (y j)) :
    ∀ i j, G.Adj i j → (y i 0 / x i 0) * (y j 0 / x j 0) = 1 := by
  intro i j hij
  have he := h i j hij
  simp only [dot_one] at he
  rw [div_mul_div_comm, ← he, div_self (mul_ne_zero (hx i) (hx j))]

private theorem recover_ratios {V : Type*} {G : SimpleGraph V} (hc : G.Preconnected)
    (x y : V → Fin 1 → ℝ) (hx : ∀ i, x i 0 ≠ 0)
    (h : ∀ i j, G.Adj i j → dotProduct (x i) (x j) = dotProduct (y i) (y j))
    (hs : ∀ i, (y i 0 / x i 0)^2 = 1) :
    ∀ i j, dotProduct (x i) (x j) = dotProduct (y i) (y j) := by
  let r (i : V) := y i 0 / x i 0
  have hr := ratio_edges G x y hx h
  have hsame {u v : V} (ha : G.Adj u v) : r u = r v := by
    calc
      r u = r u * (r u * r v) := by rw [hr u v ha, mul_one]
      _ = r v := by rw [← mul_assoc, ← pow_two, hs u, one_mul]
  intro i j
  have hrj : r i = r j :=
    propagate (hc i j) (P := fun v => r i = r v) rfl (fun he hv => hv.trans (hsame he))
  have hh : r i * r j = 1 := by rw [← hrj, ← pow_two, hs i]
  have hhx (v : V) : r v * x v 0 = y v 0 := div_mul_cancel₀ _ (hx v)
  rw [dot_one, dot_one, ← hhx i, ← hhx j]
  calc
    _ = (r i * r j) * (x i 0 * x j 0) := by rw [hh, one_mul]
    _ = _ := by ring

private theorem units_on_line (n : ℕ) (G : SimpleGraph (Fin n)) :
    determines G 1 isUnit ↔ G.Preconnected := by
  constructor
  · exact connected_of_determines G isUnit
      (by norm_num [isUnit, dot_one]) (by norm_num [isUnit, dot_one])
  · intro hc x y hx hy he
    have hsx (i : Fin n) : (x i 0)^2 = 1 := by
      simpa only [isUnit, dot_one, pow_two] using hx i
    have hsy (i : Fin n) : (y i 0)^2 = 1 := by
      simpa only [isUnit, dot_one, pow_two] using hy i
    have hnx (i : Fin n) : x i 0 ≠ 0 := by
      intro h
      have hz := hsx i
      norm_num [h] at hz
    apply recover_ratios hc x y hnx he
    intro i
    rw [div_pow, hsx, hsy, div_one]

/-- Ratios on a connected graph alternate between a value and its reciprocal. -/
private theorem ratios_or_coloring {V : Type*} {G : SimpleGraph V} (hc : G.Preconnected)
    (r : V → ℝ) (he : ∀ i j, G.Adj i j → r i * r j = 1) (i : V) :
    (r i)^2 = 1 ∨ G.Colorable 2 := by
  classical
  by_cases hi : (r i)^2 = 1
  · exact Or.inl hi
  · right
    have hclass (j : V) : r j = r i ∨ r j * r i = 1 := by
      apply propagate (hc i j) (Or.inl rfl)
      intro u v huv hu
      rcases hu with hu | hu
      · right
        simpa [hu, mul_comm] using he u v huv
      · left
        have hn : r u ≠ 0 := by
          intro hz
          simp [hz] at hu
        exact mul_left_cancel₀ hn ((he u v huv).trans hu.symm)
    refine ⟨SimpleGraph.Coloring.mk (fun j => if r j = r i then (0 : Fin 2) else 1) ?_⟩
    intro u v huv
    by_cases hU : r u = r i <;> by_cases hV : r v = r i
    · exfalso
      apply hi
      simpa [hU, hV, pow_two] using he u v huv
    · simp [hU, hV]
    · simp [hU, hV]
    · exfalso
      apply hi
      have h1 := (hclass u).resolve_left hU
      have h2 := (hclass v).resolve_left hV
      calc
        (r i)^2 = (r u * r v) * (r i)^2 := by rw [he u v huv, one_mul]
        _ = (r u * r i) * (r v * r i) := by ring
        _ = 1 := by rw [h1, h2, one_mul]

private theorem nonzero_on_line (n : ℕ) (G : SimpleGraph (Fin (n+1))) :
    determines G 1 (fun x => x ≠ 0) ↔ G.Preconnected ∧ ¬ G.Colorable 2 := by
  classical
  constructor
  · intro h
    refine ⟨connected_of_determines G _ (const_nonzero one_ne_zero)
      (const_nonzero (by norm_num)) h, ?_⟩
    rintro ⟨col⟩
    let y (v : Fin (n+1)) (_ : Fin 1) : ℝ := if col v = 0 then 2 else 1/2
    have hy (v : Fin (n+1)) : y v ≠ 0 := by
      apply const_nonzero
      split_ifs <;> norm_num
    have he (v w : Fin (n+1)) (ha : G.Adj v w) :
        dotProduct (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 1) = dotProduct (y v) (y w) := by
      have hne := col.map_rel ha
      change col v ≠ col w at hne
      have ht (j : Fin 2) : j = 0 ∨ j = 1 := by fin_cases j <;> simp
      rcases ht (col v) with hv | hv <;> rcases ht (col w) with hw | hw
      · exact False.elim (hne (hv.trans hw.symm))
      · norm_num [dot_one, y, hv, hw]
      · norm_num [dot_one, y, hv, hw]
      · exact False.elim (hne (hv.trans hw.symm))
    have hbad := h (fun _ _ => 1) y (fun _ => const_nonzero one_ne_zero) hy he 0 0
    by_cases h0 : col 0 = 0 <;> norm_num [dot_one, y, h0] at hbad
  · rintro ⟨hc, hb⟩ x y hx _ he
    have hnx (v : Fin (n+1)) : x v 0 ≠ 0 := by
      intro hz
      apply hx v
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa [hi] using hz
    apply recover_ratios hc x y hnx he
    intro i
    exact (ratios_or_coloring hc _ (ratio_edges G x y hnx he) i).resolve_right hb

end OMA.S_mo_464059

open OMA.S_mo_464059 in
theorem OMA.solution : type_of% @OMA.S_mo_464059.main := by
  refine ⟨plane_criterion, ?_, ?_, complete_for_units, units_on_line, unknown_planes, nonzero_on_line⟩
  · intro a b c d t h hne
    obtain ⟨_, _, _, h1, h2⟩ := (plane_criterion a b c d t).mp h
    unfold determinant at h1 h2
    have hden : 2 * (a*b-c*d) ≠ 0 := mul_ne_zero (by norm_num) (sub_ne_zero.mpr hne)
    apply (eq_div_iff hden).mpr
    nlinarith
  · constructor
    · apply (plane_criterion _ _ _ _ _).mpr
      norm_num [determinant]
    · apply (plane_criterion _ _ _ _ _).mpr
      norm_num [determinant]