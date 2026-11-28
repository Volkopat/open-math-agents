import OMAStatements.S_opg_a_conjecture_on_iterated_circumcentres
import Mathlib.Tactic

/- Luis Goddyn's iterated circumcentres conjecture.
   Roger Lidón Ardanuy, On Goddyn's iterated circumcenters conjecture, Theorem 1.
   An independent proof was given by Shuho Kanda and Junnosuke Koizumi. -/

namespace Goddyn

open scoped RealInnerProductSpace

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def step {d : ℕ} (p : ℕ → E d) (i : ℕ) : E d := p (i+1) - p i

structure Local (d : ℕ) (v : ℕ → E d) : Prop where
  nonzero : ∀ i, v i ≠ 0
  adjacent : ∀ i, ⟪v i, v (i+1)⟫ = -(‖v i‖ ^ 2) / 2
  apart : ∀ i k, 2 ≤ k → k ≤ d → ⟪v i, v (i+k)⟫ = 0
  total : ∀ (i : ℕ) (u : E d), (∀ j : ℕ, j < d → ⟪u, v (i+j)⟫ = 0) → u = 0

end Goddyn

open OMA.S_opg_a_conjecture_on_iterated_circumcentres
open scoped RealInnerProductSpace

namespace Goddyn

private theorem next_ne {d : ℕ} {p : ℕ → E d}
    (hd : 0 < d) (h : IsCircumcentreSequence d p) (i : ℕ) : p (i+1) ≠ p i := by
  intro he
  let a : Fin (d+1) := ⟨1, by omega⟩
  let b : Fin (d+1) := ⟨0, by omega⟩
  have e : a = b := (h i).1 (show p (i+a.val) = p (i+b.val) by simpa [a, b] using he)
  have := congrArg Fin.val e
  simp [a, b] at this

-- Shift past any initial block so that the centre rule applies to every local pair.
private theorem sees {d : ℕ} {p : ℕ → E d} (h : IsCircumcentreSequence d p)
    {k : ℕ} (hk : 0 < k) (per : Function.Periodic p k) {i m : ℕ}
    (hlo : i+2 ≤ m) (hhi : m ≤ i+d+1) : dist (p i) (p m) = dist (p (i+1)) (p m) := by
  let t := (d+1)*k
  have ht : d+1 ≤ t := Nat.le_mul_of_pos_right _ hk
  let b := m+t-(d+1)
  have hbt : b+(d+1) = m+t := by dsimp [b]; omega
  have hbi : b ≤ i+t := by dsimp [b]; omega
  let j : Fin (d+1) := ⟨i+t-b, by omega⟩
  let j' : Fin (d+1) := ⟨i+1+t-b, by omega⟩
  have hj : b+j.val = i+t := by dsimp [j]; omega
  have hj' : b+j'.val = i+1+t := by dsimp [j']; omega
  obtain ⟨r, _, hr, _⟩ := (h b).2
  have hh := (hr j).trans (hr j').symm
  rw [hj, hj', show b+d+1 = m+t by omega] at hh
  have shift : Function.Periodic p t := per.nat_mul (d+1)
  simpa only [shift i, shift (i+1), shift m] using hh

private theorem inner_to_center {d : ℕ} {x y c : E d} (h : dist x c = dist y c) :
    2 * ⟪y-x, c-y⟫ = -(‖y-x‖^2) := by
  have hh : ‖(y-x)+(c-y)‖ = ‖c-y‖ := by
    rw [show (y-x)+(c-y)=c-x by abel, ← dist_eq_norm, ← dist_eq_norm, dist_comm c x, dist_comm c y]
    exact h
  have he := norm_add_sq_real (y-x) (c-y)
  rw [hh] at he
  linarith

private theorem move_center {d : ℕ} {x y c u : E d}
    (h : dist x c = dist y c) (hor : ⟪u,y-x⟫=0) :
    dist x (c+u) = dist y (c+u) := by
  have hs (v : E d) : dist v (c+u)^2 =
      dist v c^2 - 2*⟪v-c,u⟫ + ‖u‖^2 := by
    rw [dist_eq_norm, dist_eq_norm, show v-(c+u)=(v-c)-u by abel, norm_sub_sq_real]
  have he : ⟪x-c,u⟫ = ⟪y-c,u⟫ := by
    rw [inner_sub_right] at hor
    simp only [inner_sub_left]
    rw [real_inner_comm u x, real_inner_comm u y]
    linarith
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [hs, hs, h, he]

private theorem local_total {d : ℕ} {p : ℕ → E d} (hd : 0 < d)
    (h : IsCircumcentreSequence d p) (i : ℕ) (u : E d)
    (hor : ∀ j : ℕ, j < d → ⟪u, step p (i+j)⟫ = 0) : u = 0 := by
  obtain ⟨r, hr, sphere, uniq⟩ := (h i).2
  let c := p (i+d+1)
  have equ (j : ℕ) (hj : j ≤ d) : dist (p (i+j)) (c+u) = dist (p i) (c+u) := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hj' : j < d := by omega
      have hs := (sphere (⟨j, by omega⟩ : Fin (d+1))).trans
        (sphere (⟨j+1, by omega⟩ : Fin (d+1))).symm
      have hb : ⟪u, p (i+(j+1))-p (i+j)⟫ = 0 := by
        simpa only [step, Nat.add_assoc] using hor j hj'
      exact (move_center (u := u) hs hb).symm.trans (ih (by omega))
  have hpos : 0 < dist (p i) (c+u) := by
    by_contra! hh
    have h0 := le_antisymm hh dist_nonneg
    have h1 := (equ 1 (by omega)).trans h0
    exact next_ne hd h i ((dist_eq_zero.mp h1).trans (dist_eq_zero.mp h0).symm)
  have hC : c+u = c := (uniq (c+u) _ hpos (fun j => equ j.val (by omega))).1
  exact add_left_cancel (hC.trans (add_zero c).symm)

theorem local_of_sequence {d : ℕ} {p : ℕ → E d} (hd : 0 < d)
    (h : IsCircumcentreSequence d p) (per : ∃ k, 0 < k ∧ Function.Periodic p k) :
    Local d (step p) := by
  obtain ⟨k, hk, hp⟩ := per
  refine ⟨fun i => sub_ne_zero.mpr (next_ne hd h i), ?_, ?_, local_total hd h⟩
  · intro i
    have hh := inner_to_center (sees h hk hp (i := i) (m := i+2) (by omega) (by omega))
    unfold step
    linarith
  · intro i t ht htd
    have h₁ := inner_to_center (sees h hk hp (i := i) (m := i+t) (by omega) (by omega))
    have h₂ := inner_to_center (sees h hk hp (i := i) (m := i+t+1) (by omega) (by omega))
    unfold step
    rw [show p (i+t+1)-p (i+t) = (p (i+t+1)-p (i+1))-(p (i+t)-p (i+1)) by abel, inner_sub_right]
    linarith

end Goddyn

open scoped RealInnerProductSpace

namespace Goddyn

/-- Orthogonality to a whole block forces a scalar shift by d+2.
Periodicity then forces its real scalar to have square one. -/
theorem step_period {d : ℕ} {v : ℕ → E d} (h : Local d v)
    (per : ∃ k, 0 < k ∧ Function.Periodic v k) :
    Function.Periodic v (2*(d+2)) := by
  obtain ⟨K, hK, hper⟩ := per
  let L := d+2
  let r (i : ℕ) := ⟪v (i+L), v (i+1)⟫ / ⟪v i, v (i+1)⟫
  have hn (i : ℕ) : ⟪v i, v (i+1)⟫ ≠ 0 := by
    rw [h.adjacent]
    exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr (h.nonzero i)))) (by norm_num)
  have shift (i : ℕ) : v (i+L) = r i • v i := by
    apply sub_eq_zero.mp
    apply h.total (i+1)
    intro j hj
    rw [inner_sub_left, real_inner_smul_left]
    by_cases hz : j = 0
    · subst j
      simp only [Nat.add_zero, r, div_mul_cancel₀ _ (hn i), sub_self]
    · have he : 2 ≤ j+1 := by omega
      have hf : j+1 ≤ d := by omega
      have e₁ := h.apart i (j+1) he hf
      rw [show i+(j+1) = i+1+j by omega] at e₁
      have g₁ : 2 ≤ L-(j+1) := by dsimp [L]; omega
      have g₂ : L-(j+1) ≤ d := by dsimp [L]; omega
      have e₂ := h.apart (i+1+j) (L-(j+1)) g₁ g₂
      rw [show (i+1+j)+(L-(j+1)) = i+L by dsimp [L]; omega] at e₂
      rw [real_inner_comm (v (i+1+j)) (v (i+L)), e₂, e₁, mul_zero, sub_zero]
  have rn (i : ℕ) : r i ≠ 0 := by
    intro hz
    exact h.nonzero (i+L) (by rw [shift i, hz, zero_smul])
  have inc (i : ℕ) : r (i+1) = r i := by
    have coeff : (r i * r (i+1)) * ⟪v i, v (i+1)⟫ = (r i * r i) * ⟪v i, v (i+1)⟫ := by
      calc
        _ = ⟪v (i+L), v ((i+L)+1)⟫ := by
          rw [show (i+L)+1 = (i+1)+L by omega, shift i, shift (i+1),
            real_inner_smul_left, real_inner_smul_right]
          ring
        _ = _ := by
          rw [h.adjacent (i+L), h.adjacent i, shift i, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
          ring
    exact mul_left_cancel₀ (rn i) (mul_right_cancel₀ (hn i) coeff)
  have constant (i : ℕ) : r i = r 0 := by
    induction i with
    | zero => rfl
    | succ i ih => exact (inc i).trans ih
  have iter (m i : ℕ) : v (i+m*L) = (r 0)^m • v i := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.succ_mul, ← Nat.add_assoc, shift, constant, ih, smul_smul, pow_succ']
  have hk : v (0+K*L) = v 0 := by
    rw [zero_add, Nat.mul_comm]
    exact hper.nat_mul_eq L
  have hr : (r 0)^K = 1 := smul_left_injective ℝ (h.nonzero 0) (by
    simpa only [one_smul] using (iter K 0).symm.trans hk)
  have h2 : (r 0)^2 = 1 := by
    rcases (pow_eq_one_iff_of_ne_zero hK.ne').mp hr with h | ⟨h,_⟩ <;> rw [h] <;> norm_num
  intro i
  simpa only [h2, one_smul] using iter 2 i

end Goddyn

open OMA.S_opg_a_conjecture_on_iterated_circumcentres
open scoped BigOperators RealInnerProductSpace

namespace Goddyn

/-- Equal distances between all the vertices and the centre force a second
sphere through the vertices, contradicting uniqueness. -/
private theorem secondSphere {d : ℕ} (hd : 0 < d) (q : Fin (d+1) → E d)
    (c : E d) (r : ℝ) (hr : 0 < r)
    (rad : ∀ i, dist (q i) c = r)
    (pair : ∀ i j, i ≠ j → dist (q i) (q j) = r)
    (uniq : ∀ z : E d, ∀ s : ℝ, 0 < s → (∀ i, dist (q i) z = s) → z = c) : False := by
  let u (i : Fin (d+1)) := q i - c
  let v := ∑ i, u i
  have hnorm (i) : ‖u i‖ = r := by simpa only [u, dist_eq_norm] using rad i
  have hdif (i j) (hij : i ≠ j) : ‖u i-u j‖ = r := by
    rw [show u i - u j = q i-q j by dsimp [u]; abel, ← dist_eq_norm]
    exact pair i j hij
  have gram (i j) : ⟪u i, u j⟫ = r^2/2 + if j=i then r^2/2 else 0 := by
    by_cases hij : j=i
    · subst j
      simp only [if_true, real_inner_self_eq_norm_sq, hnorm]
      ring
    · rw [if_neg hij, add_zero,
        real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
        hnorm i, hnorm j, hdif i j (Ne.symm hij)]
      ring
  have row (i) : ⟪u i,v⟫ = ((d:ℝ)+2)*r^2/2 := by
    simp [v, inner_sum, gram, Finset.sum_add_distrib]
    ring
  have hv : v ≠ 0 := by
    intro he
    have hh := row (0 : Fin (d+1))
    rw [he, inner_zero_right] at hh
    have hp : 0 < ((d:ℝ)+2)*r^2/2 := by positivity
    linarith
  let z := c+v
  have sqdist (i) : dist (q i) z ^ 2 = r^2 - 2*(((d:ℝ)+2)*r^2/2) + ‖v‖^2 := by
    rw [dist_eq_norm, show q i-z=u i-v by dsimp [z,u]; abel,
      norm_sub_sq_real, hnorm, row]
  have allDist (i) : dist (q i) z = dist (q 0) z :=
    (sq_eq_sq₀ dist_nonneg dist_nonneg).mp ((sqdist i).trans (sqdist 0).symm)
  have hs : 0 < dist (q 0) z := by
    apply dist_pos.mpr
    intro h0
    let j : Fin (d+1) := ⟨1, by omega⟩
    have hj : q j = z := dist_eq_zero.mp (by rw [allDist j, h0, dist_self])
    have hdj := pair 0 j (by intro he; have := congrArg Fin.val he; simp [j] at this)
    rw [h0, hj, dist_self] at hdj
    linarith
  have hz := uniq z _ hs allDist
  exact hv (add_left_cancel (show c+v=c+0 by simpa [z] using hz))

theorem noShort {d : ℕ} {p : ℕ → E d} (hd : 0 < d) (h : IsCircumcentreSequence d p) :
    ¬ Function.Periodic p (d+2) := by
  intro hp
  have radial (j : Fin (d+2)) : ∃ r : ℝ, 0 < r ∧
      ∀ k : Fin (d+2), k ≠ j → dist (p k.val) (p j.val) = r := by
    obtain ⟨_, r, hr, hs, _⟩ := h (j.val+1)
    refine ⟨r,hr,?_⟩
    intro k hkj
    have hn : k.val ≠ j.val := fun he => hkj (Fin.ext he)
    have hc : p ((j.val+1)+d+1) = p j.val := by
      rw [show (j.val+1)+d+1=j.val+(d+2) by omega]
      exact hp j.val
    by_cases hlt : j.val < k.val
    · let t : Fin (d+1) := ⟨k.val-j.val-1, by omega⟩
      have hz := hs t
      rwa [hc,show j.val+1+t.val=k.val by dsimp [t]; omega] at hz
    · let t : Fin (d+1) := ⟨k.val+d+2-j.val-1, by omega⟩
      have hz := hs t
      rwa [hc,show j.val+1+t.val=k.val+(d+2) by dsimp [t]; omega, hp k.val] at hz
  let m := Fin.last (d+1)
  obtain ⟨r,hr,hm⟩ := radial m
  let q (i : Fin (d+1)) := p i.val
  have hq (i : Fin (d+1)) : dist (q i) (p (d+1)) = r :=
    hm i.castSucc (ne_of_lt i.castSucc_lt_last)
  have pairs (i j : Fin (d+1)) (hij : i ≠ j) : dist (q i) (q j) = r := by
    obtain ⟨s,_,hs⟩ := radial j.castSucc
    have hn : i.castSucc ≠ j.castSucc := fun he => hij (Fin.castSucc_injective _ he)
    have h1 := hs i.castSucc hn
    have h2 := hs m (ne_of_gt j.castSucc_lt_last)
    exact h1.trans (h2.symm.trans ((dist_comm _ _).trans (hq j)))
  obtain ⟨_, _, _, _, hu⟩ := h 0
  apply secondSphere hd q (p (d+1)) r hr hq pairs
  intro z s hs hzs
  simpa using (hu z s hs (by simpa [q] using hzs)).1

end Goddyn

namespace Goddyn

open OMA.S_opg_a_conjecture_on_iterated_circumcentres

theorem step_of_period {d k : ℕ} {p : ℕ → E d} (hk : Function.Periodic p k) :
    Function.Periodic (step p) k := by
  intro i
  simp only [step, show i+k+1 = i+1+k by omega, hk i, hk (i+1)]

/-- A periodic polygonal path cannot acquire a nonzero translation over a period of its steps. -/
theorem period_of_step {d t : ℕ} {p : ℕ → E d}
    (per : ∃ k, 0 < k ∧ Function.Periodic p k) (ht : Function.Periodic (step p) t) :
    Function.Periodic p t := by
  obtain ⟨k, hk, hpk⟩ := per
  let u := p t - p 0
  have shift (i : ℕ) : p (i+t) = p i + u := by
    induction i with
    | zero => simp [u]
    | succ i ih =>
      have he := ht i
      change p (i+t+1) - p (i+t) = p (i+1) - p i at he
      rw [ih] at he
      rw [show i.succ+t = i+t+1 by omega]
      abel_nf at he ⊢
      linear_combination (norm := abel) he
  have iter (m : ℕ) : p (m*t) = p 0 + m • u := by
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.succ_mul, shift, ih, succ_nsmul, add_assoc]
  have cyc : p (k*t) = p 0 := by simpa [Nat.mul_comm] using hpk.nat_mul_eq t
  have hu : k • u = 0 := by simpa only [cyc, left_eq_add] using (iter k)
  have hu' : (k : ℝ) • u = 0 := by simpa only [Nat.cast_smul_eq_nsmul] using hu
  have hz : u = 0 := (smul_eq_zero.mp hu').resolve_left (by exact_mod_cast hk.ne')
  intro i
  simpa only [hz, add_zero] using shift i

theorem period_lower {d k : ℕ} {p : ℕ → E d} (h : IsCircumcentreSequence d p)
    (hk : 0 < k) (per : Function.Periodic p k) : d+2 ≤ k := by
  by_contra! hsmall
  have eq0 : p k = p 0 := by simpa using per 0
  by_cases hkd : k ≤ d
  · let j : Fin (d+1) := ⟨k, by omega⟩
    have he : j = 0 := (h 0).1 (show p (0+j.val) = p (0+(0 : Fin (d+1)).val) by
      simpa [j] using eq0)
    have : k = 0 := congrArg Fin.val he
    omega
  · have he : k = d+1 := by omega
    obtain ⟨r, hr, hball, _⟩ := (h 0).2
    have hd := hball (0 : Fin (d+1))
    rw [he] at eq0
    simp [eq0] at hd
    linarith

theorem period_minimal {d : ℕ} {p : ℕ → E d} (h : IsCircumcentreSequence d p)
    (half : ¬ Function.Periodic p (d+2)) (full : Function.Periodic p (2*d+4)) :
    ∀ k, 0 < k → Function.Periodic p k → 2*d+4 ≤ k := by
  intro k hk hp
  by_contra! hlt
  have lower := period_lower h hk hp
  have ne : k ≠ d+2 := fun he => half (he ▸ hp)
  have hdiff : Function.Periodic p (2*d+4-k) := by
    intro i
    calc
      p (i+(2*d+4-k)) = p (i+(2*d+4-k)+k) := (hp _).symm
      _ = p (i+(2*d+4)) := by congr 1; omega
      _ = p i := full i
  have := period_lower h (by omega : 0 < 2*d+4-k) hdiff
  omega

end Goddyn

theorem OMA.solution : type_of% @OMA.S_opg_a_conjecture_on_iterated_circumcentres.main := by
  intro d hd p h per
  obtain ⟨k, hk, hpk⟩ := per
  have hlocal := Goddyn.local_of_sequence hd h ⟨k, hk, hpk⟩
  have hsteps := Goddyn.step_period hlocal ⟨k, hk, Goddyn.step_of_period hpk⟩
  have full : Function.Periodic p (2*d+4) := by
    rw [show 2*d+4 = 2*(d+2) by omega]
    exact Goddyn.period_of_step ⟨k, hk, hpk⟩ hsteps
  exact ⟨full, Goddyn.period_minimal h (Goddyn.noShort hd h) full⟩
