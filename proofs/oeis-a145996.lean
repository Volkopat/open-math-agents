import OMAStatements.S_oeis_a145996
import Mathlib

namespace QuinticRoots

private lemma five_nonsquare (q : ℚ) : q^2 ≠ 5 := by
  intro h
  have hs : IsSquare ((5:ℕ):ℚ) := ⟨q, by norm_cast; simpa only [pow_two] using h.symm⟩
  exact (by decide : Nat.Prime 5).not_isSquare (Rat.isSquare_natCast_iff.mp hs)

set_option maxHeartbeats 2000000 in
private lemma parameter_identity (k t : ℚ) (h5 : 5-t^2≠0)
    (h : let x := (2*t+2)/(5-t^2)
         4*(x^2-x-1)*(1+t*x)=2*((x-1)*(4*x^2+2*x-1)^2)*k+(-32*x^5+20*x^3+4)) :
    (t-1)*(t^2+8*t+11)^2*(k*(t+3)*(t^2-4*t-1)^2-128)=0 := by
  dsimp only at h
  field_simp [h5] at h
  linear_combination -h/2

/-- A nontrivial rational root gives a rational parameter with constant
numerator 128. The only exceptional fibres used in the proof are at x=0,1. -/
theorem parameter_of_root {k x : ℚ}
    (h : 4*k-k^2+5*k^2*x+(20*k-20*k^2)*x^3+(16-32*k+16*k^2)*x^5=0) :
    k=0 ∨ k=2 ∨ k=4 ∨ ∃ t : ℚ, k*(t+3)*(t^2-4*t-1)^2=128 := by
  by_cases h0 : x=0
  · subst x
    have hz : k*(k-4)=0 := by linear_combination -h
    rcases mul_eq_zero.mp hz with he|he
    · exact Or.inl he
    · exact Or.inr (Or.inr (Or.inl (by linarith)))
  by_cases h1 : x=1
  · subst x
    exact Or.inr (Or.inl (by linarith [show 16-8*k=0 by linear_combination h]))
  right; right; right
  let A := (x-1)*(4*x^2+2*x-1)^2
  let B := -32*x^5+20*x^3+4
  let d := x^2-x-1
  have hd : d≠0 := by
    intro he
    apply five_nonsquare (2*x-1)
    dsimp [d] at he
    linear_combination 4*he
  let y := (2*A*k+B)/(4*d)
  have hy : 4*d*y = 2*A*k+B := by dsimp [y]; field_simp
  have hy2 : y^2=5*x^2-2*x+1 := by
    apply (mul_left_cancel₀ (show (4*d)^2 ≠ 0 by positivity))
    calc
      (4*d)^2*y^2 = (2*A*k+B)^2 := by rw [←mul_pow,hy]
      _ = (4*d)^2*(5*x^2-2*x+1) := by
        dsimp [A,B,d]
        linear_combination 4*((x-1)*(4*x^2+2*x-1)^2)*h
  let t := (y-1)/x
  have hyt : y=1+t*x := by dsimp [t]; field_simp; ring
  have hxrel : x*(5-t^2)=2*t+2 := by
    apply mul_left_cancel₀ h0
    rw [hyt] at hy2
    linear_combination -hy2
  have h5 : 5-t^2≠0 := fun he => five_nonsquare t (by linarith)
  have hx : x=(2*t+2)/(5-t^2) := (eq_div_iff h5).mpr hxrel
  have hn1 : t≠1 := by
    intro ht
    apply h1
    rw [hx,ht]
    norm_num
  have hn2 : t^2+8*t+11≠0 := by
    intro he
    apply five_nonsquare (t+4)
    linear_combination he
  refine ⟨t, ?_⟩
  have key := hy
  dsimp only [A,B,d] at key
  rw [hyt,hx] at key
  have hf := parameter_identity k t h5 key
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left
    (mul_ne_zero (sub_ne_zero.mpr hn1) (pow_ne_zero _ hn2)))

end QuinticRoots

namespace QuinticRoots

private def form (u b : ℤ) := u^2 - 10*u*b + 20*b^2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem possibilities : ∀ i j : Fin 129, 0 < i.val → 0 < j.val →
    (i.val : ℤ) * (form i.val j.val)^2 ∣ (128 : ℤ) →
    (i.val = 2 ∧ j.val = 1) ∨ (i.val = 4 ∧ j.val = 1) ∨
      (i.val = 8 ∧ j.val = 1) ∨ (i.val = 8 ∧ j.val = 3) := by
  decide +kernel

private theorem classify_integers {k b : ℕ} {u : ℤ} (hb : 0 < b)
    (hc : IsCoprime u (b : ℤ))
    (he : (k : ℤ) * (u * (form u b)^2) = 128 * (b : ℤ)^5) :
    k=1 ∨ k=2 ∨ k=4 ∨ k=243 := by
  let v := form u b
  change (k : ℤ) * (u * v^2) = 128 * (b : ℤ)^5 at he
  have hvC : IsCoprime v (b : ℤ) := by
    have h0 : IsCoprime (u^2) (b : ℤ) := hc.pow_left
    have hv : v = u^2 + (20*(b:ℤ)-10*u)*b := by dsimp [v, form]; ring
    rw [hv]
    exact h0.add_mul_right_left _
  have hC : IsCoprime (u*v^2) ((b:ℤ)^5) := (hc.mul_left hvC.pow_left).pow_right
  have hd : u*v^2 ∣ (128:ℤ) := hC.dvd_of_dvd_mul_right ⟨k, by simpa [mul_comm] using he.symm⟩
  have hbz : 0 < (b : ℤ) := by exact_mod_cast hb
  have hpr : 0 < (k:ℤ)*(u*v^2) := by rw [he]; positivity
  have hw : 0 < u*v^2 := (mul_pos_iff.mp hpr).resolve_right (by
    intro hh
    exact (by positivity : (0:ℤ)≤k).not_gt hh.1) |>.2
  have hu : 0 < u := (mul_pos_iff.mp hw).resolve_right (fun hh => (sq_nonneg v).not_gt hh.2) |>.1
  have hval : 0 < v^2 := (mul_pos_iff.mp hw).resolve_right (fun hh => (sq_nonneg v).not_gt hh.2) |>.2
  have hbound : u*v^2 ≤ 128 := Int.le_of_dvd (by decide) hd
  have hu128 : u ≤ 128 := by nlinarith [mul_nonneg hu.le (show 0 ≤ v^2-1 by omega)]
  have hv128 : v^2 ≤ 128 := by nlinarith [mul_nonneg (show 0≤u-1 by omega) (sq_nonneg v)]
  have hb128 : b ≤ 128 := by
    by_contra! hlarge
    have hgap : 0 ≤ (b:ℤ)-u := by omega
    have hlow : (b:ℤ)^2 ≤ v := by
      dsimp [v,form]
      nlinarith [sq_nonneg u, sq_nonneg (b:ℤ), mul_nonneg hbz.le hgap]
    have hlow' : (b:ℤ) ≤ (b:ℤ)^2 := by nlinarith [sq_nonneg ((b:ℤ)-1)]
    nlinarith [sq_nonneg (v-12)]
  lift u to ℕ using hu.le
  have hu' : 0 < u := by omega
  have hcases := possibilities ⟨u,by omega⟩ ⟨b,by omega⟩ hu' hb hd
  change (u=2 ∧ b=1) ∨ (u=4 ∧ b=1) ∨ (u=8 ∧ b=1) ∨ (u=8 ∧ b=3) at hcases
  rcases hcases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    norm_num [v,form] at he <;> omega

/-- Integer values of the parameter obtained from the rational parametrization. -/
theorem classify_parameter {k : ℕ} {t : ℚ}
    (h : (k:ℚ)*(t+3)*(t^2-4*t-1)^2=128) : k=1 ∨ k=2 ∨ k=4 ∨ k=243 := by
  let r := t+3
  have hr : (k:ℚ)*r*(r^2-10*r+20)^2=128 := by
    dsimp [r]
    linear_combination h
  apply classify_integers (u:=r.num) (b:=r.den) r.den_pos r.isCoprime_num_den
  have hden : (r.den:ℚ) ≠ 0 := by exact_mod_cast r.den_nz
  rw [← r.num_div_den] at hr
  field_simp [hden] at hr
  dsimp [form]
  exact_mod_cast (show (k:ℚ)*((r.num:ℚ)*((r.num:ℚ)^2-10*r.num*r.den+20*r.den^2)^2)=128*(r.den:ℚ)^5 by
    linear_combination hr)

end QuinticRoots

theorem OMA.solution : type_of% @OMA.S_oeis_a145996.main := by
  intro k
  constructor
  · rintro ⟨x,hx⟩
    obtain h|h|h|⟨t,ht⟩ := QuinticRoots.parameter_of_root hx
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (Or.inr (Or.inl (by exact_mod_cast h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by exact_mod_cast h))))
    · exact Or.inr (QuinticRoots.classify_parameter ht)
  · rintro (rfl|rfl|rfl|rfl|rfl)
    · exact ⟨0, by norm_num [OMA.S_oeis_a145996.polynomialValue]⟩
    · exact ⟨-3/5, by norm_num [OMA.S_oeis_a145996.polynomialValue]⟩
    · exact ⟨1, by norm_num [OMA.S_oeis_a145996.polynomialValue]⟩
    · exact ⟨0, by norm_num [OMA.S_oeis_a145996.polynomialValue]⟩
    · exact ⟨3/11, by norm_num [OMA.S_oeis_a145996.polynomialValue]⟩
