import OMAStatements.S_oeis_a361716

/-!
# The arbitrary-index supercongruence for OEIS A361716

Write M=floor(N/2). Reflection and Dixon's alternating cubic binomial
identity give a(N)=(-1)^M choose(N-1,M) choose(N+M,M) for positive N.
A polynomial telescoping certificate proves the Dixon identity here.
The two binomial factors give the product of 1−N²/j² for 1≤j≤M.

At N=n p^r, the factors indexed by multiples of p reproduce a(N/p).
The other denominators are units modulo p^(3r). Their quadratic and
higher cross terms vanish, leaving a sum of reciprocal squares.
Reflection gives half the complete unit sum modulo p^r, and doubling
permutes these units. Since 2 and 3 are invertible for p≥5, the sum
vanishes. Clearing denominators gives the native integer congruence.

Source: https://oeis.org/A361716
-/

namespace Dixon716

open Finset OMA.S_oeis_a361716

private theorem multiples_half (p M : ℕ) (hp : 0 < p) :
    ((Icc 1 (p*M/2)).filter (fun j => p ∣ j)) = (Icc 1 (M/2)).image (p*·) := by
  have aux (j : ℕ) : p*j ≤ p*M / 2 ↔ j ≤ M/2 := by
    rw [Nat.le_div_iff_mul_le (by decide : 0<2),Nat.le_div_iff_mul_le (by decide : 0<2),
      Nat.mul_assoc,mul_le_mul_iff_right₀ hp]
  ext j
  simp only [mem_filter,mem_Icc,mem_image]
  constructor
  · rintro ⟨⟨hj,hm⟩,⟨k,rfl⟩⟩
    refine ⟨k,⟨?_,(aux k).1 hm⟩,rfl⟩
    by_contra! h
    obtain rfl := Nat.eq_zero_of_le_zero (by omega : k ≤ 0)
    simp at hj
  · rintro ⟨k,⟨hk,hm⟩,rfl⟩
    exact ⟨⟨Nat.mul_pos hp hk,(aux k).2 hm⟩,dvd_mul_right ..⟩

private theorem ratio_step
    (eval : ∀ N : ℕ, 0 < N → (a N:ℚ) = ∏ j ∈ Icc 1 (N/2), (1-(N:ℚ)^2/(j:ℚ)^2))
    (p M : ℕ) (hp : 0<p) (hM : 0<M) :
    (a (p*M):ℚ) = (a M:ℚ) * ∏ j ∈ (Icc 1 (p*M/2)).filter (fun j => ¬p∣j),
      (1-((p*M:ℕ):ℚ)^2/(j:ℚ)^2) := by
  rw [eval (p*M) (Nat.mul_pos hp hM),eval M hM,
    ← prod_filter_mul_prod_filter_not (Icc 1 (p*M/2)) (fun j => p∣j)]
  congr 1
  rw [multiples_half p M hp,prod_image (fun i _ j _ h => Nat.eq_of_mul_eq_mul_left hp h)]
  apply prod_congr rfl
  intro j hj
  have hpq : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hjq : (j:ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp hj).1)
  push_cast
  field_simp

private theorem cross_step
    (eval : ∀ N : ℕ, 0 < N → (a N:ℚ) = ∏ j ∈ Icc 1 (N/2), (1-(N:ℚ)^2/(j:ℚ)^2))
    (p M : ℕ) (hp : 0<p) (hM : 0<M) :
    a (p*M) * (∏ j ∈ (Icc 1 (p*M/2)).filter (fun j => ¬p∣j), (j:ℤ)^2) =
      a M * ∏ j ∈ (Icc 1 (p*M/2)).filter (fun j => ¬p∣j), ((j:ℤ)^2-((p*M:ℕ):ℤ)^2) := by
  let S := (Icc 1 (p*M/2)).filter (fun j => ¬p∣j)
  have hr : (a (p*M):ℚ) = (a M:ℚ) * ∏ j ∈ S, (1-((p*M:ℕ):ℚ)^2/(j:ℚ)^2) :=
    ratio_step eval p M hp hM
  have hc : (a (p*M):ℚ) * (∏ j ∈ S, (j:ℚ)^2) =
      (a M:ℚ) * ∏ j ∈ S, ((j:ℚ)^2-((p*M:ℕ):ℚ)^2) := by
    rw [hr, mul_assoc, ← prod_mul_distrib]
    congr 1
    apply prod_congr rfl
    intro j hj
    have hjn : 0 < j := (mem_Icc.mp (mem_filter.mp hj).1).1
    have hj' : (j:ℚ) ≠ 0 := by exact_mod_cast hjn.ne'
    field_simp
  exact_mod_cast hc

private theorem prod_linear {R : Type*} [CommRing R] (x : R) (hx : x*x=0)
    (g : ℕ → R) (s : Finset ℕ) :
    (∏ j ∈ s, (1-x*g j)) = 1-x*(∑ j ∈ s,g j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [prod_insert hj,sum_insert hj,ih]
    linear_combination (g j * ∑ i ∈ s, g i) * hx

private theorem normalized_product (q N : ℕ) (hq : 0<q) (hN : q ∣ N) (s : Finset ℕ)
    (hu : ∀ j ∈ s, j.Coprime q)
    (hs : ∑ j ∈ s, ((j : ZMod q)⁻¹)^2 = 0) :
    (∏ j ∈ s, ((j : ZMod (q^3))^2 - (N:ZMod (q^3))^2)) =
      ∏ j ∈ s, (j : ZMod (q^3))^2 := by
  have : NeZero (q^3) := ⟨pow_ne_zero _ hq.ne'⟩
  let red := ZMod.castHom (show q ∣ q^3 by exact dvd_pow_self _ (by decide)) (ZMod q)
  have hred (j : ℕ) (hj : j ∈ s) :
      red ((j : ZMod (q^3))⁻¹) = (j : ZMod q)⁻¹ := by
    apply (ZMod.inv_eq_of_mul_eq_one q _ _ ?_).symm
    have h := congrArg red (ZMod.coe_mul_inv_eq_one j ((hu j hj).pow_right 3))
    simpa only [map_mul,map_one,map_natCast] using h
  let u : ZMod (q^3) := ∑ j ∈ s, ((j : ZMod (q^3))⁻¹)^2
  have hz : red u = 0 := by
    rw [show red u = ∑ j ∈ s, (red ((j : ZMod (q^3))⁻¹))^2 by simp [u]]
    exact (sum_congr rfl (fun j hj => by rw [hred j hj])).trans hs
  have hdiv : q ∣ u.val := by
    apply (ZMod.natCast_eq_zero_iff _ _).1
    have h := congrArg red (ZMod.natCast_zmod_val u)
    simpa only [map_natCast,hz] using h
  have cube : (q : ZMod (q^3))^3 = 0 := by
    rw [← Nat.cast_pow,ZMod.natCast_eq_zero_iff]
  obtain ⟨v,hv⟩ := hN
  obtain ⟨d,hd⟩ := hdiv
  have ue : u = (q:ZMod (q^3))*d := by
    rw [← Nat.cast_mul, ← hd,ZMod.natCast_zmod_val]
  have hnz : (N : ZMod (q^3))^2*u = 0 := by
    rw [hv,Nat.cast_mul,ue]
    linear_combination (v:ZMod (q^3))^2 * d * cube
  have hsq : (N : ZMod (q^3))^2 * (N : ZMod (q^3))^2 = 0 := by
    rw [hv,Nat.cast_mul]
    linear_combination (q:ZMod (q^3))*(v:ZMod (q^3))^4 * cube
  have unitprod : (∏ j ∈ s, (1-(N:ZMod (q^3))^2*((j:ZMod (q^3))⁻¹)^2)) = 1 := by
    rw [prod_linear _ hsq]
    change 1 - (N:ZMod (q^3))^2*u = 1
    rw [hnz,sub_zero]
  calc
    _ = ∏ j ∈ s, ((j:ZMod (q^3))^2*(1-(N:ZMod (q^3))^2*((j:ZMod (q^3))⁻¹)^2)) := by
      apply prod_congr rfl
      intro j hj
      have inv := ZMod.coe_mul_inv_eq_one j ((hu j hj).pow_right 3)
      linear_combination (N:ZMod (q^3))^2 * (((j:ZMod (q^3))*(j:ZMod (q^3))⁻¹)+1) * inv
    _ = _ := by rw [prod_mul_distrib,unitprod,mul_one]

theorem super_of_product_aux
    (eval : ∀ N : ℕ, 0 < N → (a N:ℚ) = ∏ j ∈ Icc 1 (N/2), (1-(N:ℚ)^2/(j:ℚ)^2))
    (harm : ∀ p r n : ℕ, p.Prime → 5≤p → 0<r →
      ∑ j ∈ (Icc 1 (n*p^r/2)).filter (fun j => ¬p∣j), ((j : ZMod (p^r))⁻¹)^2 = 0) :
    type_of% @OMA.S_oeis_a361716.main := by
  intro p n r hp h5 hn hr
  let M := n*p^(r-1)
  let N := n*p^r
  let q := p^r
  let S := (Icc 1 (N/2)).filter (fun j => ¬p∣j)
  have hN : p*M = N := by
    dsimp [M,N]
    rw [show r = r-1+1 by omega] at ⊢
    simp only [Nat.add_sub_cancel,pow_succ]
    ring
  have hu (j : ℕ) (hj : j ∈ S) : j.Coprime q :=
    (hp.coprime_iff_not_dvd.mpr (mem_filter.mp hj).2).symm.pow_right r
  have modEq := normalized_product q N (pow_pos hp.pos _) (dvd_mul_left _ _) S hu (harm p r n hp h5 hr)
  have cross := cross_step eval p M hp.pos (Nat.mul_pos hn (pow_pos hp.pos _))
  rw [hN] at cross
  change a N * (∏ j ∈ S, (j:ℤ)^2) = a M * ∏ j ∈ S, ((j:ℤ)^2-(N:ℤ)^2) at cross
  have castCross := congrArg (Int.castRingHom (ZMod (q^3))) cross
  simp only [map_mul,map_prod,map_pow,map_sub,map_natCast,Int.coe_castRingHom] at castCross
  rw [modEq] at castCross
  have units : IsUnit (∏ j ∈ S, (j:ZMod (q^3))^2) := by
    apply prod_induction _ _ (fun _ _ => IsUnit.mul) isUnit_one
    exact fun j hj => ((ZMod.isUnit_iff_coprime _ _).2 ((hu j hj).pow_right 3)).pow 2
  have hres := units.mul_right_cancel castCross
  have out := (ZMod.intCast_eq_intCast_iff (a N) (a M) (q^3)).1 hres
  convert out using 1
  simp [q,←pow_mul,Nat.mul_comm]

end Dixon716

open Finset
namespace Dixon716

private theorem small_unit {p r a : ℕ} (hp : p.Prime) (hr : 0 < r) (ha : 0 < a) (hap : a < p) :
    IsUnit (a : ZMod (p^r)) :=
  (ZMod.isUnit_natCast_iff_not_dvd_pow hp hr).2 (fun h => (not_le_of_gt hap) (Nat.le_of_dvd ha h))

private theorem all_unit_squares {p r : ℕ} [NeZero (p^r)] (hp : p.Prime) (h5 : 5 ≤ p) (hr : 0 < r) :
    ∑ u : (ZMod (p^r))ˣ, ((u : ZMod (p^r))^2) = 0 := by
  classical
  have h₂ : IsUnit (2 : ZMod (p^r)) := by exact_mod_cast small_unit (a:=2) hp hr (by decide) (by omega)
  have h₃ : IsUnit (3 : ZMod (p^r)) := by exact_mod_cast small_unit (a:=3) hp hr (by decide) (by omega)
  let S : ZMod (p^r) := ∑ u : (ZMod (p^r))ˣ, (u : ZMod (p^r))^2
  have he : 4 * S = S := calc
    4 * S = ∑ u : (ZMod (p^r))ˣ, (↑(h₂.unit*u) : ZMod (p^r))^2 := by
      dsimp [S]; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro u _
      ring
    _ = S := Equiv.sum_comp (Equiv.mulLeft h₂.unit) (fun u : (ZMod (p^r))ˣ => (u : ZMod (p^r))^2)
  have hz : 3*S = 0 := by linear_combination he
  exact h₃.mul_right_inj.mp (show 3*S = 3*0 by simpa using hz)

private theorem full_harmonic {p r : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hr : 0 < r) :
    ∑ j ∈ (range (p^r)).filter (fun j => ¬ p ∣ j), ((j : ZMod (p^r))⁻¹)^2 = 0 := by
  classical
  let : NeZero (p^r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let U := (range (p^r)).filter fun j => ¬ p ∣ j
  have hunit (j : ℕ) (hj : j ∈ U) : IsUnit (j : ZMod (p^r)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp hr).2 (mem_filter.mp hj).2
  let toU (j : ℕ) (hj : j ∈ U) := ((hunit j hj).unit)⁻¹
  trans ∑ u : (ZMod (p^r))ˣ, (u : ZMod (p^r))^2
  · apply Finset.sum_bij toU
    · simp
    · intro a ha b hb h
      have hab : (a : ZMod (p^r)) = (b : ZMod (p^r)) := by
        simpa [toU] using congrArg (fun u : (ZMod (p^r))ˣ => ((u⁻¹ : (ZMod (p^r))ˣ) : ZMod (p^r))) h
      have hh := congrArg ZMod.val hab
      simpa [ZMod.val_natCast_of_lt (mem_range.mp (mem_filter.mp ha).1),
        ZMod.val_natCast_of_lt (mem_range.mp (mem_filter.mp hb).1)] using hh
    · intro u _
      let j := (u⁻¹ : (ZMod (p^r))ˣ).val.val
      have hjc : (j : ZMod (p^r)) = ↑(u⁻¹) := ZMod.natCast_zmod_val _
      have hj : j ∈ U := mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _),
        (ZMod.isUnit_natCast_iff_not_dvd_pow hp hr).mp (hjc ▸ (u⁻¹).isUnit)⟩
      refine ⟨j, hj, ?_⟩
      apply inv_injective
      change ((hunit j hj).unit⁻¹)⁻¹ = u⁻¹
      rw [inv_inv]; exact Units.ext ((hunit j hj).unit_spec.trans hjc)
    · intro j hj
      congr 1
      simp only [toU, ← ZMod.inv_coe_unit, IsUnit.unit_spec]
  · exact all_unit_squares hp h5 hr

private theorem reflect_zero {p r : ℕ} (F : ZMod (p^r) → ZMod (p^r)) (hp : p.Prime) (h5 : 5 ≤ p)
    (hr : 0 < r) (hF : ∀ x, F (-x) = F x) (h0 : F 0 = 0)
    (hs : ∑ j ∈ range (p^r), F j = 0) :
    ∑ j ∈ range (p^r / 2 + 1), F j = 0 := by
  obtain ⟨k, hk⟩ := (hp.odd_of_ne_two (by omega)).pow (n:=r)
  let H := ∑ j ∈ range k, F ((j+1 : ℕ) : ZMod (p^r))
  have hh : ∑ j ∈ range (k+1), F j = H := by
    rw [Finset.sum_range_succ']; simp [H,h0]
  have ht : ∑ j ∈ range k, F ((k+1+j : ℕ) : ZMod (p^r)) = H := by
    dsimp only [H]
    rw [←Finset.sum_range_reflect (fun i => F ((i+1 : ℕ) : ZMod (p^r))) k]
    apply Finset.sum_congr rfl
    intro j hj
    have hkj := mem_range.mp hj
    have hjj : k+1+j+(k-1-j+1)=p^r := by omega
    have hz : (((k+1+j : ℕ) : ZMod (p^r))+((k-1-j+1 : ℕ) : ZMod (p^r)))=0 := by
      rw [← Nat.cast_add, hjj, ZMod.natCast_self]
    rw [eq_neg_of_add_eq_zero_left hz, hF]
  have hsplit : (p^r : ℕ) = (k+1)+k := by omega
  have htw : 2 * H = 0 := by
    have hsum : (∑ j ∈ range ((k+1)+k), F ((j : ℕ) : ZMod (p^r))) = 0 := by
      rw [←hsplit]; exact hs
    rw [Finset.sum_range_add, hh, ht] at hsum
    simpa [two_mul] using hsum
  have h₂ : IsUnit (2 : ZMod (p^r)) := by exact_mod_cast small_unit (a:=2) hp hr (by decide) (by omega)
  rw [show p^r / 2 = k by omega, hh]
  exact h₂.mul_right_inj.mp (by simpa using htw)

theorem half_inv_sq (p r n : ℕ) (hp : p.Prime) (h5 : 5≤p) (hr : 0<r) :
    ∑ j ∈ (Finset.Icc 1 (n*p^r/2)).filter (fun j => ¬ p ∣ j),
      ((j : ZMod (p^r))⁻¹)^2 = 0 := by
  classical
  let F (x : ZMod (p^r)) := if IsUnit x then (x⁻¹)^2 else 0
  have h0 : F 0 = 0 := by simp [F, ZMod.inv_zero]
  have hneg (x : ZMod (p^r)) : F (-x) = F x := by
    by_cases hx : IsUnit x
    · simp only [F, if_pos hx, if_pos hx.neg]
      rw [← hx.unit_spec, ← Units.val_neg, ZMod.inv_coe_unit, ZMod.inv_coe_unit]
      simp
    · have hxn : ¬ IsUnit (-x) := fun h => hx (by simpa using h.neg)
      simp [F, hx, hxn]
  have hblock : ∑ j ∈ range (p^r), F j = 0 := by
    simpa only [Finset.sum_filter, F, ZMod.isUnit_natCast_iff_not_dvd_pow hp hr] using
      full_harmonic hp h5 hr
  have hpref (t b : ℕ) : ∑ j ∈ range (t*p^r+b), F j = ∑ j ∈ range b, F j := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [show (t+1)*p^r+b=p^r+(t*p^r+b) by ring, Finset.sum_range_add, hblock, zero_add]
      convert ih using 2 with j
      simp [Nat.cast_add]
  let b := n*p^r/2
  have hi : insert 0 (Icc 1 b) = range (b+1) := by ext i; simp; omega
  calc
    _ = ∑ i ∈ Icc 1 b, F i := by
      simp only [Finset.sum_filter, F, ZMod.isUnit_natCast_iff_not_dvd_pow hp hr, b]
    _ = ∑ i ∈ range (b+1), F i := by rw [←hi, Finset.sum_insert (by simp), Nat.cast_zero, h0, zero_add]
    _ = 0 := by
      obtain ⟨t, he | he⟩ := Nat.even_or_odd' n
      · have ht : n*p^r = 2*(t*p^r) := by rw[he]; ring
        rw [show b+1=t*p^r+1 by dsimp [b]; omega, hpref]; simp [h0]
      · have ht : n*p^r=2*(t*p^r)+p^r := by rw[he]; ring
        rw [show b+1=t*p^r+(p^r/2+1) by dsimp[b]; omega, hpref]
        exact reflect_zero F hp h5 hr hneg h0 hblock

end Dixon716

namespace Dixon716

open Finset OMA.S_oeis_a361716

theorem super_of_product
    (eval : ∀ N : ℕ, 0 < N → (a N : ℚ) =
      ∏ j ∈ Icc 1 (N / 2), (1 - (N : ℚ)^2 / (j : ℚ)^2)) :
    type_of% @OMA.S_oeis_a361716.main :=
  super_of_product_aux eval half_inv_sq

end Dixon716

namespace Dixon716

def dc (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n+1), (-1:ℤ)^k * (n.choose k:ℤ)^3

end Dixon716

namespace Dixon716
open Finset

private def summand (n k : ℕ) : ℤ := (-1:ℤ)^k * (n.choose k:ℤ)^3

private theorem binom_row (n k : ℕ) :
    ((n:ℤ)+1)*(n.choose k:ℤ) = ((n:ℤ)+1-k)*((n+1).choose k:ℤ) := by
  by_cases h : k≤n+1
  · have e := congrArg (fun v : ℕ => (v:ℤ)) (Nat.choose_mul_succ_eq n k)
    push_cast [Nat.cast_sub h] at e
    linear_combination e
  · simp [Nat.choose_eq_zero_of_lt (by omega : n<k),
      Nat.choose_eq_zero_of_lt (by omega : n+1<k)]

private theorem binom_col (n k : ℕ) :
    ((k:ℤ)+1)*(n.choose (k+1):ℤ) = ((n:ℤ)-k)*(n.choose k:ℤ) := by
  by_cases h : k≤n
  · have e := congrArg (fun v : ℕ => (v:ℤ)) (Nat.choose_succ_right_eq n k)
    push_cast [Nat.cast_sub h] at e
    linear_combination e
  · simp [Nat.choose_eq_zero_of_lt (by omega : n<k),
      Nat.choose_eq_zero_of_lt (by omega : n<k+1)]

private theorem row_two (n k : ℕ) :
    (((n:ℤ)+2)*((n:ℤ)+1))^3 * summand n k =
    (((n:ℤ)+2-k)*((n:ℤ)+1-k))^3 * summand (n+2) k := by
  have e₁ := binom_row n k
  have e₂ := binom_row (n+1) k
  push_cast at e₂
  have e : ((n:ℤ)+2)*((n:ℤ)+1)*(n.choose k:ℤ) =
      (((n:ℤ)+2-k)*((n:ℤ)+1-k))*((n+2).choose k:ℤ) := by
    linear_combination ((n:ℤ)+2)*e₁ + ((n:ℤ)+1-k)*e₂
  calc
    _ = (-1:ℤ)^k * (((n:ℤ)+2)*((n:ℤ)+1)*(n.choose k:ℤ))^3 := by unfold summand; ring
    _ = _ := by rw [e]; unfold summand; ring

private theorem col_one (n k : ℕ) :
    ((k:ℤ)+1)^3*summand n (k+1) = -((n:ℤ)-k)^3*summand n k := by
  calc
    _ = -(-1:ℤ)^k * (((k:ℤ)+1)*(n.choose (k+1):ℤ))^3 := by unfold summand; rw [pow_succ (-1:ℤ) k]; ring
    _ = _ := by rw [binom_col]; unfold summand; ring

/-- A polynomial certificate for the recurrence of the alternating cubic binomial sum. -/
private def certPoly (N x : ℤ) : ℤ :=
  2*N^2*(N-1)*(14*N^2-16*N+5) -3*N*(2*N-1)*(13*N^2-17*N+5)*x +
  3*(29*N^3-42*N^2+18*N-2)*x^2 -3*(3*N-2)*(5*N-2)*x^3 +3*(3*N-2)*x^4

private theorem cert_identity (N x : ℤ) :
    (N-x)^3*certPoly N (x+1) + x^3*certPoly N x =
      N^5*(N-1)^3+3*(3*N-4)*(3*N-2)*((N-x)*(N-x-1))^3 := by unfold certPoly; ring

private def boundary (n k : ℕ) : ℤ := (k:ℤ)^3*certPoly n k*summand n k

private theorem local_identity (n k : ℕ) :
    (((n:ℤ)+2)*((n:ℤ)+1))^3 * (((n:ℤ)+2)^2*summand (n+2) k +
      3*(3*(n:ℤ)+2)*(3*(n:ℤ)+4)*summand n k) =
      boundary (n+2) k - boundary (n+2) (k+1) := by
  have cert := cert_identity ((n:ℤ)+2) k
  have c := col_one (n+2) k
  push_cast at c
  unfold boundary
  push_cast
  linear_combination -summand (n+2) k*cert +
    certPoly ((n:ℤ)+2) ((k:ℤ)+1)*c +
    (3*(3*(n:ℤ)+2)*(3*(n:ℤ)+4))*row_two n k

theorem dc_rec (n : ℕ) : ((n:ℤ)+2)^2 * dc (n+2) +
    3*(3*(n:ℤ)+2)*(3*(n:ℤ)+4)*dc n = 0 := by
  have ext_sum : ∑ k ∈ range (n+2+1), summand n k = dc n := by
    rw [sum_range_succ,sum_range_succ]
    simp only [summand,Nat.choose_eq_zero_of_lt (by omega : n<n+2),
      Nat.choose_eq_zero_of_lt (by omega : n<n+1),Nat.cast_zero,zero_pow (by decide : 3≠0),
      mul_zero,add_zero,dc]
  have edge : boundary (n+2) (n+2+1)=0 := by
    simp [boundary,summand]
  have hz : (((n:ℤ)+2)*((n:ℤ)+1))^3 *
      (((n:ℤ)+2)^2*dc (n+2)+3*(3*(n:ℤ)+2)*(3*(n:ℤ)+4)*dc n)=0 := by
    calc
      _ = ∑ k ∈ range (n+2+1), (((n:ℤ)+2)*((n:ℤ)+1))^3 *
          (((n:ℤ)+2)^2*summand (n+2) k+3*(3*(n:ℤ)+2)*(3*(n:ℤ)+4)*summand n k) := by
            rw [←mul_sum,sum_add_distrib,←mul_sum,←mul_sum,ext_sum]; rfl
      _ = ∑ k ∈ range (n+2+1), (boundary (n+2) k - boundary (n+2) (k+1)) :=
        sum_congr rfl (fun k _ => local_identity n k)
      _ = _ := by rw [sum_range_sub',edge]; simp [boundary]
  exact (mul_eq_zero.mp hz).resolve_left (by positivity)

end Dixon716

namespace Dixon716

private def centralTerm (m : ℕ) : ℤ :=
  ((2*m).choose m : ℤ) * ((3*m).choose (2*m) : ℤ)

private theorem central_factorial (m : ℕ) :
    centralTerm m * (m.factorial : ℤ)^3 = (3*m).factorial := by
  have h₁ := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2*m by omega)
  have h₂ := Nat.choose_mul_factorial_mul_factorial (show 2*m ≤ 3*m by omega)
  rw [show 2*m-m=m by omega] at h₁
  rw [show 3*m-2*m=m by omega] at h₂
  unfold centralTerm
  exact_mod_cast (calc
    (2*m).choose m * (3*m).choose (2*m) * m.factorial^3 =
      (3*m).choose (2*m) * ((2*m).choose m * m.factorial * m.factorial) * m.factorial := by ring
    _ = _ := by rw [h₁,h₂])

private theorem central_step (m : ℕ) :
    (2*(m:ℤ)+2)^2 * centralTerm (m+1) =
      3*(6*(m:ℤ)+2)*(6*(m:ℤ)+4)*centralTerm m := by
  have up : ((m:ℤ)+1)^3 * centralTerm (m+1) =
      (3*(m:ℤ)+3)*(3*(m:ℤ)+2)*(3*(m:ℤ)+1)*centralTerm m := by
    apply mul_right_cancel₀ (show (m.factorial:ℤ)^3 ≠ 0 by positivity)
    have h₁ := central_factorial (m+1)
    rw [show 3*(m+1) = 3*m+1+1+1 by omega, Nat.factorial_succ (3*m+1+1),
      Nat.factorial_succ (3*m+1),Nat.factorial_succ (3*m),Nat.factorial_succ m] at h₁
    push_cast at h₁
    have h₂ := central_factorial m
    linear_combination h₁ - (3*(m:ℤ)+3)*(3*(m:ℤ)+2)*(3*(m:ℤ)+1)*h₂
  apply mul_left_cancel₀ (show (m:ℤ)+1 ≠ 0 by positivity)
  linear_combination 4*up

theorem dixon_of_rec
    (R : ∀ n : ℕ, ((n:ℤ)+2)^2 * dc (n+2) + 3*(3*(n:ℤ)+2)*(3*(n:ℤ)+4)*dc n=0) :
    ∀ m : ℕ, dc (2*m) = (-1:ℤ)^m * ((2*m).choose m:ℤ) * ((3*m).choose (2*m):ℤ) := by
  intro m
  suffices hh : dc (2*m) = (-1:ℤ)^m * centralTerm m by
    simpa only [centralTerm,mul_assoc] using hh
  induction m with
  | zero => simp [dc,centralTerm]
  | succ m ih =>
    have h := R (2*m)
    rw [ih] at h
    push_cast at h
    rw [show 2*(m+1) = 2*m+2 by omega,pow_succ]
    apply mul_left_cancel₀ (show (2*(m:ℤ)+2)^2 ≠ 0 by positivity)
    linear_combination h + (-1:ℤ)^m * central_step m

end Dixon716

namespace Dixon716

open Finset OMA.S_oeis_a361716

private theorem reflected (n : ℕ) (f : ℕ → ℚ) :
    ∑ k ∈ range (n+1), (-1:ℚ)^k*f (n-k) =
      (-1:ℚ)^n * ∑ k ∈ range (n+1), (-1:ℚ)^k*f k := by
  rw [Finset.mul_sum, ← Finset.sum_range_reflect (fun k => (-1:ℚ)^n*((-1:ℚ)^k*f k))]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  simp only [Nat.add_sub_cancel]
  have e := pow_add (-1:ℚ) k (n-k)
  rw [show k+(n-k)=n by omega] at e
  have sq : ((-1:ℚ)^(n-k))^2=1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [e]
  linear_combination -((-1:ℚ)^k*f (n-k)) * sq

private theorem even_moment (m : ℕ) :
    (∑ k ∈ range (2*m+1), (-1:ℚ)^k * k * ((2*m).choose k : ℚ)^3) =
       (m:ℚ)*∑ k ∈ range (2*m+1), (-1:ℚ)^k*((2*m).choose k : ℚ)^3 := by
  have hr := reflected (2*m) (fun k => (k:ℚ)*((2*m).choose k : ℚ)^3)
  rw [pow_mul] at hr
  norm_num only [neg_one_sq, one_pow, one_mul] at hr
  have hc : ∀ k ∈ range (2*m+1), ((2*m-k:ℕ):ℚ)*((2*m).choose (2*m-k):ℚ)^3 =
      (2*(m:ℚ)-k)*((2*m).choose k:ℚ)^3 := by
    intro k hk
    have h : k≤2*m := by simpa using hk
    rw [Nat.choose_symm h, Nat.cast_sub h]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun k hk => congrArg ((-1:ℚ)^k * ·) (hc k hk))] at hr
  rw [Finset.mul_sum]
  simp_rw [show ∀ k : ℕ, (-1:ℚ)^k*((2*(m:ℚ)-k)*((2*m).choose k : ℚ)^3) =
        2*((m:ℚ)*((-1:ℚ)^k*((2*m).choose k:ℚ)^3)) -
        (-1:ℚ)^k*k*((2*m).choose k:ℚ)^3 by intro k; ring] at hr
  simp_rw [show ∀ k : ℕ, (-1:ℚ)^k*((k:ℚ)*((2*m).choose k : ℚ)^3) =
        (-1:ℚ)^k*k*((2*m).choose k:ℚ)^3 by intro k; ring] at hr
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hr
  linarith

private theorem padded (N : ℕ) (hp : 0<N) :
    (a N : ℚ) = ∑ k ∈ range (N+1),
      (-1:ℚ)^k * (N.choose k : ℚ)^2 * ((N-1).choose k : ℚ) := by
  rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (show N-1<N by omega)]
  simp [a]

private theorem even_eval (m : ℕ) (hm : 0 < m) :
    2*(a (2*m):ℚ) = ∑ k ∈ range (2*m+1), (-1:ℚ)^k*((2*m).choose k : ℚ)^3 := by
  have e : (2*(m:ℚ))*(a (2*m):ℚ) =
      (2*(m:ℚ))*(∑ k ∈ range (2*m+1), (-1:ℚ)^k*((2*m).choose k : ℚ)^3) -
      ∑ k ∈ range (2*m+1), (-1:ℚ)^k*k*((2*m).choose k:ℚ)^3 := by
    rw [padded (2*m) (by omega), Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k≤2*m := by simpa using hk
    have h := Nat.choose_mul_succ_eq (2*m-1) k
    rw [show 2*m-1+1=2*m by omega] at h
    have h' : ((2*m-1).choose k:ℚ)*(2*m) = ((2*m).choose k:ℚ)*(2*(m:ℚ)-k) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hk'] using
        (show (((2*m-1).choose k:ℕ):ℚ)*((2*m:ℕ):ℚ) =
          ((2*m).choose k:ℚ)*((2*m-k:ℕ):ℚ) by exact_mod_cast h)
    linear_combination ((-1:ℚ)^k*((2*m).choose k:ℚ)^2) * h'
  rw [even_moment] at e
  exact (mul_left_cancel₀ (a := (m:ℚ)) (by exact_mod_cast hm.ne')) (by linarith only [e] :
    (m:ℚ)*(2*(a (2*m):ℚ)) = m*_)

private theorem odd_eval (m : ℕ) :
    (2*(m:ℚ)+1)*(a (2*m+1):ℚ) = (3*(m:ℚ)+1)*
      ∑ k ∈ range (2*m+1), (-1:ℚ)^k*((2*m).choose k:ℚ)^3 := by
  let N := 2*m+1
  let b := fun k => ((2*m).choose k : ℚ)
  let C := fun k => (N.choose k : ℚ)
  let H := fun k : ℕ => (N:ℚ)*(C k)^2*b k - ((N:ℚ)+k)*(b k)^3
  have cm (k : ℕ) (hk : k ≤ N) : (N:ℚ)*b k = ((N:ℚ)-k)*C k := by
    have h := Nat.choose_mul_succ_eq (2*m) k
    change (2*m).choose k * N = N.choose k*(N-k) at h
    have : b k * (N:ℚ) = C k * ((N-k:ℕ):ℚ) := by dsimp [b,C]; exact_mod_cast h
    rw [Nat.cast_sub hk] at this
    linarith
  have symmH (k : ℕ) (hk : k ≤ N) : H (N-k) = H k := by
    have r := cm (N-k) (by omega)
    have s := cm k hk
    have cr : C (N-k)=C k := by dsimp [C]; exact_mod_cast Nat.choose_symm hk
    rw [cr, Nat.cast_sub hk] at r
    have sum : C k = b k + b (N-k) := by
      apply (mul_left_cancel₀ (a := (N:ℚ)) (by dsimp [N]; positivity))
      linarith
    unfold H
    rw [cr, Nat.cast_sub hk, sum]
    rw [sum] at s
    linear_combination (b k^2 - b k * b (N-k) + b (N-k)^2) * s
  have anti := reflected N H
  rw [Finset.sum_congr rfl (fun k hk => congrArg ((-1:ℚ)^k * ·)
    (symmH k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))))] at anti
  have sn : (-1:ℚ)^N = -1 := by dsimp [N]; rw [pow_succ, pow_mul]; norm_num
  rw [sn] at anti
  have z : ∑ k ∈ range (N+1), (-1:ℚ)^k*H k = 0 := by linarith
  have z' : (N:ℚ)*(a N:ℚ) - ((N:ℚ)*(∑ k ∈ range (N+1), (-1:ℚ)^k*(b k)^3)
            + ∑ k ∈ range (N+1), (-1:ℚ)^k*k*(b k)^3) = 0 := by
    rw [padded N (by dsimp [N]; omega), Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← z]
    apply Finset.sum_congr rfl
    intro k hk
    change (N:ℚ)*((-1:ℚ)^k*C k^2*b k) - (_+_) = _
    dsimp only [H]
    ring
  have bz : b N = 0 := by dsimp [b]; exact_mod_cast Nat.choose_eq_zero_of_lt (show 2*m<N by dsimp [N]; omega)
  rw [Finset.sum_range_succ, Finset.sum_range_succ (f := fun k => (-1:ℚ)^k*k*(b k)^3), bz] at z'
  simp only [zero_pow (by decide : 3≠0), mul_zero, add_zero] at z'
  change (N:ℚ)*(a N:ℚ)-((N:ℚ)*_ + ∑ k ∈ range (2*m+1), (-1:ℚ)^k*k*((2*m).choose k:ℚ)^3)=0 at z'
  rw [even_moment] at z'
  dsimp [N,b] at z'
  push_cast at z'
  linarith

theorem closed_choose_of_dixon
    (dixon : ∀ m : ℕ, (∑ k ∈ range (2*m+1), (-1:ℤ)^k * ((2*m).choose k:ℤ)^3) =
      (-1:ℤ)^m * ((2*m).choose m:ℤ) * ((3*m).choose (2*m):ℤ))
    (N : ℕ) (hN : 0<N) : (a N : ℚ) =
      (-1:ℚ)^(N/2)*((N-1).choose (N/2):ℚ)*((N+N/2).choose (N/2):ℚ) := by
  set m := N/2 with hm
  have d : (∑ k ∈ range (2*m+1), (-1:ℚ)^k * ((2*m).choose k:ℚ)^3) =
      (-1:ℚ)^m * ((2*m).choose m:ℚ) * ((3*m).choose m:ℚ) := by
    have dc := dixon m
    rw [show (3*m).choose (2*m) = (3*m).choose m by
      simpa only [show 3*m-m=2*m by omega] using Nat.choose_symm (show m≤3*m by omega)] at dc
    exact_mod_cast dc
  rcases (show N=2*m ∨ N=2*m+1 by omega) with he|ho
  · rw [he, show 2*m+m=3*m by omega]
    have mp : 0 < m := by omega
    have e := even_eval m mp
    rw [d] at e
    have eq := Nat.choose_mul_succ_eq (2*m-1) m
    rw [show 2*m-1+1=2*m by omega, show 2*m-m=m by omega] at eq
    have eq' : ((2*m-1).choose m:ℚ)*(2*(m:ℚ)) = ((2*m).choose m:ℚ)*m := by exact_mod_cast eq
    have half : 2*((2*m-1).choose m:ℚ) = ((2*m).choose m:ℚ) := by
      apply mul_right_cancel₀ (show (m:ℚ) ≠ 0 by exact_mod_cast mp.ne')
      linarith only [eq']
    rw [←half] at e
    linarith only [e]
  · rw [ho, Nat.add_sub_cancel, show 2*m+1+m=3*m+1 by omega]
    have e := odd_eval m
    rw [d] at e
    have eq := Nat.choose_mul_succ_eq (3*m) m
    rw [show 3*m+1-m=2*m+1 by omega] at eq
    have eq' : ((3*m).choose m:ℚ)*(3*(m:ℚ)+1) = ((3*m+1).choose m:ℚ)*(2*(m:ℚ)+1) := by exact_mod_cast eq
    apply mul_left_cancel₀ (a := 2*(m:ℚ)+1) (by positivity)
    linear_combination e + ((-1:ℚ)^m*((2*m).choose m:ℚ))*eq'

end Dixon716

namespace Dixon716
open Finset

/-- The factors from 1 through m are the product of two binomial coefficients. -/
theorem choose_product (N m : ℕ) (hm : m<N) :
    (-1:ℚ)^m * ((N-1).choose m : ℚ) * ((N+m).choose m : ℚ) =
      ∏ j ∈ Icc 1 m, (1-(N:ℚ)^2/(j:ℚ)^2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_Icc_succ_top (by omega),←ih (by omega),pow_succ]
    have e₁ : ((N-1).choose (m+1):ℚ)*((m:ℚ)+1) =
        ((N-1).choose m:ℚ)*((N:ℚ)-1-m) := by
      have h := congrArg (fun v : ℕ => (v:ℚ)) (Nat.choose_succ_right_eq (N-1) m)
      push_cast [Nat.cast_sub (by omega : m ≤ N-1),Nat.cast_sub (by omega : 1≤N)] at h
      exact h
    have e₂ : ((N+(m+1)).choose (m+1):ℚ)*((m:ℚ)+1) =
        ((N:ℚ)+m+1)*((N+m).choose m:ℚ) := by
      have h := congrArg (fun v : ℕ => (v:ℚ)) (Nat.add_one_mul_choose_eq (N+m) m).symm
      push_cast at h
      exact h
    rw [show ((m+1:ℕ):ℚ)=(m:ℚ)+1 by push_cast; rfl]
    have hn : (m:ℚ)+1 ≠ 0 := by positivity
    field_simp
    linear_combination
      -(((N+(m+1)).choose (m+1):ℚ) * ((m:ℚ)+1)) * e₁
      -(((N-1).choose m:ℚ) * ((N:ℚ)-1-m)) * e₂

end Dixon716

open Dixon716 OMA.S_oeis_a361716 in
theorem OMA.solution : type_of% @OMA.S_oeis_a361716.main := by
  apply super_of_product
  intro N hN
  exact (closed_choose_of_dixon (dixon_of_rec dc_rec) N hN).trans (choose_product N (N/2) (by omega))
