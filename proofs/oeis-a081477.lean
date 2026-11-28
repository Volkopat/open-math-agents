import OMAStatements.S_oeis_a081477
import Mathlib

/-!
# Kimberling's conjectures on OEIS A081477

This proof starts from the accepted A086377 floor formula of Bosma, Dekking
and Steiner (https://arxiv.org/abs/1710.01498). An elementary rank argument
enumerates its complement, giving the nearest-integer formula for A081477.
The fractional-part computation then proves both of Kimberling's 2022
conjectures (https://oeis.org/A081477). Additional results give an exact
membership test, translated interval discrepancy, and a classification
of quadratic slopes yielding the same floor cancellation.
-/

namespace Beat81

/-- If an integer lies between excluded values t and t+1, precisely t+1 excluded
values (including index zero) lie below it. -/
theorem nth_off_range {f : ℕ → ℕ} (hf : StrictMono f) {t n : ℕ}
    (hlo : f t < n+t) (hhi : n+t < f (t+1)) :
    Nat.nth (fun k => k ∉ Set.range f) (n-1) = n+t := by
  classical
  let b := n+t
  have hnot : b ∉ Set.range f := by
    rintro ⟨i,hi⟩
    rcases le_or_gt i t with h | h
    · have h' := (hf.monotone h).trans_lt hlo
      exact h'.ne hi
    · have h' := hhi.trans_le (hf.monotone (show t+1≤ i by omega))
      exact h'.ne hi.symm
  have himage : (Finset.range b).filter (fun z => z∈Set.range f) = (Finset.range (t+1)).image f := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hz,i,rfl⟩
      refine ⟨i,?_,rfl⟩
      by_contra! hh
      exact (not_lt_of_ge (hhi.le.trans (hf.monotone hh))) hz
    · rintro ⟨i,hi,rfl⟩
      exact ⟨(hf.monotone (by omega)).trans_lt hlo, i,rfl⟩
  have hc : Nat.count (fun k => k∉Set.range f) b = n-1 := by
    rw [Nat.count_eq_card_filter_range]
    have hsum := Finset.card_filter_add_card_filter_not (s:=Finset.range b) (p:=fun k => k∈Set.range f)
    rw [himage,Finset.card_image_of_injective _ hf.injective,Finset.card_range,Finset.card_range] at hsum
    dsimp [b] at hsum ⊢
    omega
  rw [←hc]
  exact Nat.nth_count hnot
end Beat81

namespace Beat81

/-- Add an integer to the rounded number of excluded terms preceding it. The
reciprocal formula is valid for every positive irrational slope. -/
theorem rounded_reciprocal {r : ℝ} (hr : 0<r) (irr : Irrational r) {n : ℕ} (hn : 1≤n) :
    Nat.nth (fun k => k ∉ Set.range (fun m : ℕ => m + ⌊r*((m:ℝ)-1/2)⌋₊)) (n-1) =
      n+⌊(n:ℝ)/r+1/2⌋₊ := by
  let t : ℕ := ⌊(n:ℝ)/r+1/2⌋₊
  have nn : 0≤(n:ℝ)/r+1/2 := by positivity
  have hle : (t:ℝ) ≤ (n:ℝ)/r+1/2 := Nat.floor_le nn
  have htlt : (t:ℝ) < (n:ℝ)/r+1/2 := by
    apply lt_of_le_of_ne hle
    intro heq
    have dn : (2*(t:ℤ)-1)≠0 := by omega
    apply (irrational_iff_ne_rational r).mp irr (2*(n:ℤ)) (2*(t:ℤ)-1) dn
    apply (eq_div_iff (by exact_mod_cast dn)).mpr
    push_cast
    have hdiv := div_mul_cancel₀ (n:ℝ) hr.ne'
    nlinarith only [congrArg (fun z : ℝ => z*r) heq,hdiv]
  have hgt : (n:ℝ)/r+1/2 < (t:ℝ)+1 := Nat.lt_floor_add_one _
  have mon : StrictMono (fun m : ℕ => m + ⌊r*((m:ℝ)-1/2)⌋₊) := by
    intro a b ha
    have hab : (a:ℝ) < b := by exact_mod_cast ha
    exact Nat.add_lt_add_of_lt_of_le ha (Nat.floor_mono (mul_le_mul_of_nonneg_left (by linarith : (a:ℝ)-1/2 ≤ (b:ℝ)-1/2) hr.le))
  change Nat.nth _ (n-1) = n+t
  refine nth_off_range (t:=t) mon ?_ ?_
  · have h1 : r*((t:ℝ)-1/2) < n := by
      rw [mul_comm,←lt_div_iff₀ hr]; linarith
    have h2 := (Nat.floor_lt' (by omega : n≠0)).mpr h1
    omega
  · have h1 : (n:ℝ) ≤ r*((t:ℝ)+1-1/2) := by
      rw [mul_comm,←div_le_iff₀ hr]; linarith
    have h2 : n ≤ ⌊r*(((t+1:ℕ):ℝ)-1/2)⌋₊ := Nat.le_floor (by push_cast; exact h1)
    omega
end Beat81

namespace Beat81
open OMA.S_oeis_a081477

/-- Kimberling's nth positive complementary value as an explicit shifted Beatty term. -/
theorem complement_nth {n : ℕ} (hn : 1≤n) :
    (a n : ℤ) = (n:ℤ) + ⌊(n:ℝ)/Real.sqrt 2+1/2⌋ := by
  let r := Real.sqrt 2
  let F := fun m : ℕ => m+⌊r*((m:ℝ)-1/2)⌋₊
  have hr : 0<r := Real.sqrt_pos.mpr (by norm_num)
  have hs : r*r=2 := Real.mul_self_sqrt (by norm_num)
  have shift : 1/r=r/2 := (div_eq_div_iff hr.ne' (by norm_num)).mpr (by nlinarith only [hs])
  have Fpos {m : ℕ} (hm : 0 < m) : a086377 m = (F m : ℤ) := by
    have pos : 1≤(m:ℝ) := by exact_mod_cast hm
    have harg : 0≤r*((m:ℝ)-1/2) := mul_nonneg hr.le (by linarith)
    change ⌊(1+r)*(m:ℝ)-1/r⌋ = ((m+⌊r*((m:ℝ)-1/2)⌋₊:ℕ):ℤ)
    rw [shift,show (1+r)*(m:ℝ)-r/2 = (m:ℝ)+r*((m:ℝ)-1/2) by ring,
      Int.floor_natCast_add,Nat.cast_add,Int.natCast_floor_eq_floor harg]
  have F0 : F 0=0 := by
    dsimp only [F]
    rw [Nat.cast_zero,Nat.zero_add]
    exact Nat.floor_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hr.le (by norm_num))
  have hpred : IsA081477 = (fun k => k ∉ Set.range F) := by
    funext k
    apply propext
    constructor
    · rintro ⟨hk,hk'⟩ ⟨m,he⟩
      rcases eq_or_ne m 0 with rfl|hm
      · omega
      · exact hk' m (by omega) (by rw [Fpos (by omega : 0 < m),he])
    · intro h
      refine ⟨?_,?_⟩
      · by_contra! hz
        exact h ⟨0,by omega⟩
      · intro m hm he
        apply h
        refine ⟨m,?_⟩
        rw [Fpos hm] at he
        exact_mod_cast he
  have hform := rounded_reciprocal hr irrational_sqrt_two hn
  unfold a
  rw [hpred]
  change (Nat.nth (fun k => k ∉ Set.range (fun m:ℕ => m+⌊r*((m:ℝ)-1/2)⌋₊)) (n-1) : ℤ) = _
  rw [hform,Nat.cast_add,Int.natCast_floor_eq_floor (by positivity)]
end Beat81

namespace Beat81
open OMA.S_oeis_a081477

/-- Multiplying the rounded Beatty value by `√2` maps each half of the fractional
interval affinely onto a shorter interval of slope `2-√2`. -/
theorem rounded_floor_fract (n z : ℕ)
    (hz : (z:ℤ) = (n:ℤ) + ⌊(n:ℝ)/Real.sqrt 2+1/2⌋) :
    ⌊(z:ℝ)*Real.sqrt 2⌋ = (n:ℤ)+⌊(n:ℝ)*Real.sqrt 2⌋ ∧
    Int.fract ((z:ℝ)*Real.sqrt 2) = (2-Real.sqrt 2)*Int.fract ((n:ℝ)/Real.sqrt 2) +
      (if Int.fract ((n:ℝ)/Real.sqrt 2)<1/2 then 0 else Real.sqrt 2-1) := by
  let r := Real.sqrt 2
  let y := (n:ℝ)/r
  let m := ⌊y⌋
  let t := Int.fract y
  let b : ℤ := if t<1/2 then 0 else 1
  let s : ℝ := (2-r)*t + (b:ℝ)*(r-1)
  have rr : r^2=2 := Real.sq_sqrt (by norm_num)
  have rpos : 0<r := Real.sqrt_pos.mpr (by norm_num)
  have rlo : 1<r := by nlinarith
  have rhi : r<2 := by nlinarith
  have tlo : 0≤t := Int.fract_nonneg _
  have thi : t<1 := Int.fract_lt_one _
  have hy : y=(m:ℝ)+t := by dsimp only [m,t,Int.fract]; ring
  have yn : y*r=n := div_mul_cancel₀ _ rpos.ne'
  have ny : (n:ℝ)*r=2*y := by nlinarith only [congrArg (· * r) yn,congrArg (y * ·) rr]
  have floors : ⌊y+1/2⌋=m+b ∧ ⌊(n:ℝ)*r⌋=2*m+b := by
    by_cases h : t<1/2
    · simp only [b,if_pos h,add_zero]
      constructor <;> apply Int.floor_eq_iff.mpr <;> push_cast <;> constructor <;> linarith
    · simp only [b,if_neg h]
      constructor <;> apply Int.floor_eq_iff.mpr <;> push_cast <;> constructor <;> linarith
  have fs : 0 ≤ s ∧ s < 1 := by
    have hl := mul_nonneg (sub_nonneg.mpr rhi.le) tlo
    have ht := mul_pos (sub_pos.mpr rhi) (sub_pos.mpr thi)
    by_cases h : t<1/2
    · simp only [s,b,if_pos h,Int.cast_zero,zero_mul,add_zero]
      constructor <;> nlinarith only [hl,ht,rlo]
    · simp only [s,b,if_neg h,Int.cast_one,one_mul]
      constructor <;> nlinarith only [hl,ht,rlo]
  have zcast : (z:ℝ)=(n:ℝ)+(m:ℝ)+(b:ℝ) := by
    change (z:ℤ)=(n:ℤ)+⌊y+1/2⌋ at hz
    rw [floors.1] at hz
    exact_mod_cast (hz.trans (add_assoc ..).symm)
  have eq : (z:ℝ)*r=(n:ℝ)+(2*(m:ℝ)+(b:ℝ))+s := by
    rw [zcast]
    dsimp only [s]
    nlinarith only [ny,yn,hy,congrArg (·*r) hy]
  have fv : ⌊(z:ℝ)*r⌋ = (n:ℤ)+(2*m+b) := by
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith [fs.1,fs.2]
  change ⌊(z:ℝ)*r⌋ = (n:ℤ)+⌊(n:ℝ)*r⌋ ∧ Int.fract ((z:ℝ)*r) = (2-r)*t + (if t<1/2 then 0 else r-1)
  refine ⟨by rw [floors.2, fv], ?_⟩
  rw [Int.fract, fv]
  push_cast
  rw [eq]
  by_cases h : t<1/2
  · simp only [s,b,if_pos h,Int.cast_zero,zero_mul,add_zero]
    ring
  · simp only [s,b,if_neg h,Int.cast_one,one_mul]
    ring

/-- The two fractional parts lie on the same side of `1/2`, with a gap around the
midpoint of width `√2-1` in the possible output values. -/
theorem rounded_gap (n z : ℕ) (hn : 1≤n)
    (hz : (z:ℤ)=(n:ℤ)+⌊(n:ℝ)/Real.sqrt 2+1/2⌋) :
    (IsA120753 n → Real.sqrt 2/2 < Int.fract ((z:ℝ)*Real.sqrt 2)) ∧
    (IsA120752 n → Int.fract ((z:ℝ)*Real.sqrt 2)<(2-Real.sqrt 2)/2) := by
  let r := Real.sqrt 2
  let t := Int.fract ((n:ℝ)/r)
  have hr : r^2=2 := Real.sq_sqrt (by norm_num)
  have rp : 0<r := Real.sqrt_pos.mpr (by norm_num)
  have rhi : r<2 := by nlinarith
  have base : Real.sqrt (1/2) = 1/r := by rw [Real.sqrt_div (by norm_num : (0:ℝ)≤1),Real.sqrt_one]
  have freq : Real.sqrt (1/2) * n = (n:ℝ)/r := by rw [base]; ring
  have nothalf : t ≠ 1/2 := by
    have hI := (irrational_sqrt_two.natCast_div (show n≠0 by omega)).sub_intCast ⌊(n:ℝ)/r⌋
    change (n:ℝ)/r - (⌊(n:ℝ)/r⌋:ℝ) ≠ 1/2
    convert hI.ne_rat (1/2) using 1
    norm_num [r]
  have ff := (rounded_floor_fract n z hz).2
  change Int.fract ((z:ℝ)*r)=(2-r)*t+(if t<1/2 then 0 else r-1) at ff
  constructor
  · rintro ⟨_,ht⟩
    rw [freq] at ht
    change 1/2<t at ht
    rw [if_neg ht.not_gt] at ff
    nlinarith only [ff,mul_pos (sub_pos.mpr rhi) (sub_pos.mpr ht)]
  · rintro ⟨_,ht⟩
    rw [freq] at ht
    have h : t<1/2 := lt_of_le_of_ne ht nothalf
    rw [if_pos h] at ff
    nlinarith only [ff,mul_pos (sub_pos.mpr rhi) (sub_pos.mpr h)]

theorem conclusions_of_closed (n : ℕ) (hn : 1≤n)
    (hz : (a n:ℤ)=(n:ℤ)+⌊(n:ℝ)/Real.sqrt 2+1/2⌋) :
    ⌊(a n:ℝ)*Real.sqrt 2⌋ = (n:ℤ)+⌊(n:ℝ)*Real.sqrt 2⌋ ∧
    (IsA120753 n → 1/2 < Int.fract ((a n:ℝ)*Real.sqrt 2)) ∧
    (IsA120752 n → Int.fract ((a n:ℝ)*Real.sqrt 2)≤1/2) := by
  have rlo : 1<Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]
  have H := rounded_gap n (a n) hn hz
  exact ⟨(rounded_floor_fract n (a n) hz).1, fun h => by linarith [H.1 h], fun h => by linarith [H.2 h]⟩

end Beat81

namespace Beatty81

/-- A family of rounded Beatty sequences for quadratic irrational slopes.
The formula is valid at every integer index, including negative indices. -/
theorem quadratic_round {h c : ℤ} {r : ℝ} (hr₁ : 1<r) (hr₂ : r<2)
    (hs : r^2/2 + ((h:ℝ)-1)*r = c) (n : ℤ) :
    let m := h*n + ⌊(n:ℝ)*r/2+1/2⌋
    let t := Int.fract ((n:ℝ)*r/2)
    ⌊(m:ℝ)*r⌋ = c*n + ⌊(n:ℝ)*r⌋ ∧
      Int.fract ((m:ℝ)*r) = if t<1/2 then (2-r)*t else (2-r)*t+r-1 := by
  let z := ⌊(n:ℝ)*r/2⌋
  let t := Int.fract ((n:ℝ)*r/2)
  let b : ℤ := if t<1/2 then 0 else 1
  have ht : (z:ℝ)+t = (n:ℝ)*r/2 := Int.floor_add_fract _
  have ht0 : 0≤t := Int.fract_nonneg _
  have ht1 : t<1 := Int.fract_lt_one _
  have rnd : ⌊(n:ℝ)*r/2 + 1/2⌋ = z+b := by
    apply Int.floor_eq_iff.mpr
    by_cases hhalf : t<1/2 <;> simp only [b,hhalf,if_true,if_false,Int.cast_add,Int.cast_zero,Int.cast_one] <;> constructor <;> linarith
  have dbl : ⌊(n:ℝ)*r⌋ = 2*z+b := by
    apply Int.floor_eq_iff.mpr
    by_cases hhalf : t<1/2 <;> simp only [b,hhalf,if_true,if_false,Int.cast_add,Int.cast_mul,Int.cast_zero,Int.cast_one,Int.cast_ofNat] <;> constructor <;> linarith
  let y := (2-r)*t + (r-1)*(b:ℝ)
  have hy : 0≤y ∧ y<1 := by
    have h0 := mul_nonneg (sub_nonneg.mpr hr₂.le) ht0
    have h1 := mul_lt_mul_of_pos_left ht1 (sub_pos.mpr hr₂)
    by_cases hhalf : t<1/2 <;> simp only [y,b,hhalf,if_true,if_false,Int.cast_zero,Int.cast_one] <;> constructor <;> linarith
  have err : ((h*n+(z+b) : ℤ):ℝ)*r = ((c*n+(2*z+b): ℤ):ℝ)+y := by
    push_cast
    dsimp only [y]
    nlinarith [congrArg (fun v : ℝ => (n:ℝ)*v) hs,
      congrArg (fun v : ℝ => r*v) ht]
  have fl : ⌊((h*n+(z+b) : ℤ):ℝ)*r⌋ = c*n+(2*z+b) :=
    Int.floor_eq_iff.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  dsimp only
  rw [rnd,dbl,fl]
  refine ⟨rfl, ?_⟩
  rw [Int.fract,fl]
  change _ = if t<1/2 then (2-r)*t else (2-r)*t+r-1
  rw [err]
  by_cases hhalf : t<1/2 <;> simp only [y,b,hhalf,if_true,if_false,Int.cast_zero,Int.cast_one] <;> ring

/-- For each positive h, the h integers c from h to 2h−1 provide slopes in (1,2). -/
theorem quadratic_slope {h c : ℕ} (hh : 1≤h) (hc : h≤c) (hc' : c<2*h) :
    let r := Real.sqrt (((h:ℝ)-1)^2 + 2*c) - ((h:ℝ)-1)
    1<r ∧ r<2 ∧ r^2/2 + ((h:ℝ)-1)*r = c := by
  dsimp only
  have h1 : (1:ℝ) ≤ h := by exact_mod_cast hh
  have hlo : (h:ℝ) ≤ c := by exact_mod_cast hc
  have hhi : (c:ℝ) < 2*h := by exact_mod_cast hc'
  have rad : 0≤((h:ℝ)-1)^2 + 2*c := by positivity
  have hs := Real.sq_sqrt rad
  have hn := Real.sqrt_nonneg (((h:ℝ)-1)^2 + 2*c)
  constructor
  · nlinarith [sq_nonneg (Real.sqrt (((h:ℝ)-1)^2 + 2*c)-(h:ℝ))]
  constructor
  · nlinarith [sq_nonneg (Real.sqrt (((h:ℝ)-1)^2 + 2*c)-((h:ℝ)+1))]
  · nlinarith

theorem round_hit_error {h c n : ℤ} {r : ℝ} (hr₁ : 1<r) (hr₂ : r<2)
    (hit : ⌊((h*n+⌊(n:ℝ)*r/2+1/2⌋ : ℤ):ℝ)*r⌋ = c*n+⌊(n:ℝ)*r⌋) :
    |(n:ℝ)*(r^2/2+((h:ℝ)-1)*r-c)| < 2 := by
  let z := ⌊(n:ℝ)*r/2+1/2⌋
  have lo : (z:ℝ) ≤ (n:ℝ)*r/2+1/2 := Int.floor_le _
  have hi : (n:ℝ)*r/2+1/2 < (z:ℝ)+1 := Int.lt_floor_add_one _
  have hlo := Int.floor_le ((n:ℝ)*r)
  have hhi := Int.lt_floor_add_one ((n:ℝ)*r)
  have flo := Int.floor_le (((h*n+z:ℤ):ℝ)*r)
  have fhi := Int.lt_floor_add_one (((h*n+z:ℤ):ℝ)*r)
  change ⌊((h*n+z : ℤ):ℝ)*r⌋ = c*n+⌊(n:ℝ)*r⌋ at hit
  rw [hit] at flo fhi
  push_cast at flo fhi
  apply abs_lt.mpr
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right lo (by linarith : 0≤r),
    mul_lt_mul_of_pos_right hi (by linarith : 0<r)]

/-- Even a cofinal subsequence of exact floor identities characterizes the quadratic slope. -/
theorem quadratic_iff_cofinal {h c : ℤ} {r : ℝ} (hr₁ : 1<r) (hr₂ : r<2) :
    r^2/2+((h:ℝ)-1)*r = c ↔
    ∀ N : ℕ, ∃ n : ℕ, N≤n ∧
      ⌊((h*(n:ℤ)+⌊(n:ℝ)*r/2+1/2⌋:ℤ):ℝ)*r⌋ = c*n+⌊(n:ℝ)*r⌋ := by
  constructor
  · intro hs N
    exact ⟨N,le_rfl, by simpa only [Int.cast_natCast] using (quadratic_round hr₁ hr₂ hs N).1⟩
  · intro cofinal
    by_contra ne
    let e := r^2/2+((h:ℝ)-1)*r-c
    have hpos : 0 < |e| := abs_pos.mpr (sub_ne_zero.mpr ne)
    obtain ⟨N,hN⟩ := exists_nat_gt (2/|e|)
    obtain ⟨n,hn,hit⟩ := cofinal N
    have big : 2<(n:ℝ)*|e| := (div_lt_iff₀ hpos).mp (hN.trans_le (by exact_mod_cast hn))
    have small := round_hit_error (n:=(n:ℤ)) hr₁ hr₂ (by simpa only [Int.cast_natCast] using hit)
    change |((n:ℤ):ℝ)*e|<2 at small
    rw [Int.cast_natCast,abs_mul,abs_of_nonneg (Nat.cast_nonneg n)] at small
    exact (not_lt_of_ge big.le) small

theorem quadratic_slope_irrational {h c : ℕ} (hh : 1≤h) (hc : h≤c) (hc' : c<2*h) :
    Irrational (Real.sqrt (((h:ℝ)-1)^2+2*c)-((h:ℝ)-1)) := by
  let d := (h-1)^2+2*c
  have cd : (d:ℝ) = ((h:ℝ)-1)^2+2*c := by
    dsimp [d]
    push_cast [Nat.cast_sub hh]
    rfl
  have irr : Irrational (Real.sqrt (d:ℝ)) := by
    apply irrational_sqrt_natCast_iff.mpr
    rintro ⟨j,hj⟩
    have sj : Real.sqrt (d:ℝ) = j := by rw [hj]; push_cast; simp
    have bounds := quadratic_slope hh hc hc'
    dsimp only at bounds
    rw [←cd,sj] at bounds
    have lo : (h:ℝ)<j := by linarith [bounds.1]
    have hi : (j:ℝ)<h+1 := by linarith [bounds.2.1]
    have : h<j := by exact_mod_cast lo
    have : j<h+1 := by exact_mod_cast hi
    omega
  rw [←cd,←show ((h-1:ℕ):ℝ)=(h:ℝ)-1 by rw [Nat.cast_sub hh]; norm_num]
  exact irr.sub_natCast _

theorem quadratic_parameters {h c : ℕ} {r : ℝ} (hh : 1≤h) (hr₁ : 1<r) (hr₂ : r<2)
    (hs : r^2/2+((h:ℝ)-1)*r=c) :
    h≤c ∧ c<2*h ∧ r = Real.sqrt (((h:ℝ)-1)^2+2*c)-((h:ℝ)-1) := by
  have hpos : 0≤(h:ℝ)-1 := sub_nonneg.mpr (by exact_mod_cast hh)
  have lower : (h:ℝ)<c+1 := by
    nlinarith [mul_nonneg hpos (sub_nonneg.mpr hr₁.le), sq_nonneg (r-1)]
  have upper : (c:ℝ)<2*h := by
    nlinarith [mul_nonneg hpos (sub_nonneg.mpr hr₂.le),
      mul_pos (sub_pos.mpr hr₂) (by linarith : 0<2+r)]
  have low : h<c+1 := by exact_mod_cast lower
  refine ⟨by omega, by exact_mod_cast upper, ?_⟩
  have sq : ((h:ℝ)-1)^2+2*c = ((h:ℝ)-1+r)^2 := by nlinarith
  rw [sq, Real.sqrt_sq (by linarith)]
  ring

end Beatty81

namespace Beat81
open OMA.S_oeis_a081477

/-- A membership test for the excluded sequence using a single rotation by √2. -/
theorem excluded_iff (m : ℕ) :
    (∃ j : ℕ, 1 ≤ j ∧ a086377 j = (m : ℤ)) ↔
    1-Real.sqrt 2/2 < Int.fract ((m : ℝ)*Real.sqrt 2) ∧
    Int.fract ((m : ℝ)*Real.sqrt 2) ≤ Real.sqrt 2/2 := by
  let r : ℝ := Real.sqrt 2
  let s := r/2
  have hr : r^2=2 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 < r := Real.sqrt_pos.2 (by norm_num)
  have hrl : 1 < r := by nlinarith
  have hru : r < 2 := by nlinarith
  have hs0 : 0 < s := by dsimp [s]; positivity
  have hsu : s < 1 := by dsimp [s]; linarith
  have hrec : 1/r=s := (div_eq_iff hr0.ne').mpr (by dsimp [s]; nlinarith)
  have hscale : 0 < 1+r := by linarith
  let x := (m : ℝ)*r
  let f := ⌊x⌋
  let t := Int.fract x
  have hx : (f : ℝ)+t=x := Int.floor_add_fract _
  have ht0 : 0 ≤ t := Int.fract_nonneg _
  have ht1 : t < 1 := Int.fract_lt_one _
  have lower : (1+r)*(x-m+1-s)=(m:ℝ)+s := by
    dsimp only [x,s]; linear_combination ((m:ℝ)-1/2)*hr
  have upper : (1+r)*(x-m+s)=(m:ℝ)+1+s := by
    dsimp only [x,s]; linear_combination ((m:ℝ)+1/2)*hr
  have hit (j : ℕ) : a086377 j = (m:ℤ) ↔ x-m+1-s ≤ j ∧ (j:ℝ) < x-m+s := by
    change ⌊(1+r)*(j:ℝ)-1/r⌋ = (m:ℤ) ↔ _
    rw [hrec,Int.floor_eq_iff]
    push_cast
    constructor
    · rintro ⟨hl,hu⟩
      exact ⟨(mul_le_mul_iff_right₀ hscale).mp (by rw [lower]; linarith),
        (mul_lt_mul_iff_right₀ hscale).mp (by rw [upper]; linarith)⟩
    · rintro ⟨hl,hu⟩
      have hl' := mul_le_mul_of_nonneg_left hl hscale.le
      have hu' := mul_lt_mul_of_pos_left hu hscale
      rw [lower] at hl'
      rw [upper] at hu'
      exact ⟨by linarith,by linarith⟩
  change _ ↔ 1-s < t ∧ t ≤ s
  constructor
  · rintro ⟨j,_,hj⟩
    obtain ⟨hl,hu⟩ := (hit j).mp hj
    have h1 : (f : ℝ)-m < j := by linarith
    have h2 : (j : ℝ) < f-m+2 := by linarith
    have hi : f-(m:ℤ) < (j:ℤ) := by exact_mod_cast h1
    have hi' : (j:ℤ) < f-(m:ℤ)+2 := by exact_mod_cast h2
    have he : (j:ℤ)=f-m+1 := by omega
    have he' := congrArg (fun z : ℤ => (z:ℝ)) he
    push_cast at he'
    exact ⟨by linarith,by linarith⟩
  · rintro ⟨hl,hu⟩
    have hfx : (m:ℝ) ≤ x := by dsimp [x]; nlinarith only [Nat.cast_nonneg (α:=ℝ) m,mul_nonneg (Nat.cast_nonneg (α:=ℝ) m) (le_of_lt (sub_pos.mpr hrl))]
    have hmf : (m:ℤ) ≤ f := Int.le_floor.mpr (by exact_mod_cast hfx)
    let j := (f-(m:ℤ)+1).toNat
    have hj : (j:ℤ)=f-m+1 := Int.toNat_of_nonneg (by omega)
    have hj' := congrArg (fun z : ℤ => (z:ℝ)) hj
    push_cast at hj'
    refine ⟨j,by omega,(hit j).mpr ⟨by linarith,by linarith⟩⟩

theorem membership_iff (m : ℕ) : IsA081477 m ↔ 0 < m ∧
    (Int.fract ((m:ℝ)*Real.sqrt 2) ≤ 1-Real.sqrt 2/2 ∨
    Real.sqrt 2/2 < Int.fract ((m:ℝ)*Real.sqrt 2)) := by
  unfold IsA081477
  have h := not_congr (excluded_iff m)
  push Not at h
  rw [h, imp_iff_not_or, not_lt]

end Beat81

namespace Beat81
open OMA.S_oeis_a081477
open scoped Classical

/-- Exact bounds for the rank through M, including its half-unit offset. -/
theorem rank_window
    (H : ∀ n : ℕ, 1 ≤ n → (a n : ℤ) = (n:ℤ)+⌊(n:ℝ)/Real.sqrt 2+1/2⌋) (M : ℕ) :
    (Nat.count IsA081477 (M+1):ℝ) < (2-Real.sqrt 2)*((M:ℝ)+1/2) ∧
    (2-Real.sqrt 2)*((M:ℝ)+1/2) ≤ (Nat.count IsA081477 (M+1):ℝ)+1 := by
  classical
  let r := Real.sqrt 2
  let δ := 2-r
  have hsq : r^2=2 := Real.sq_sqrt (by norm_num)
  have hr : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hδ : 0 < δ := by dsimp [δ]; nlinarith
  have hsc : δ*(1+1/r)=1 := by
    dsimp only [δ]; field_simp; nlinarith
  have hinf : (Set.ofPred IsA081477).Infinite := by
    intro hf
    let i := hf.toFinset.card
    have hz : a (i+1)=0 := by simpa [a,i] using (Nat.nth_of_card_le hf (le_refl hf.toFinset.card))
    have hh := H (i+1) (by omega)
    rw [hz] at hh
    have ht : 0 ≤ ⌊((i+1:ℕ):ℝ)/Real.sqrt 2 + 1/2⌋ := Int.floor_nonneg.mpr (by positivity)
    omega
  let X := δ*((M:ℝ)+1/2)
  let c := Nat.count IsA081477 (M+1)
  have hX : 0<X := by dsimp only [X]; positivity
  have lower (i : ℕ) : i < c ↔ (i:ℝ)+1<X := by
    change i < Nat.count IsA081477 (M+1) ↔ _
    rw [Nat.lt_nth_iff_count_lt hinf]
    change a (i+1) < M+1 ↔ _
    let j := i+1
    have hj := H j (by dsimp [j]; omega)
    change (a j < M+1) ↔ _
    calc
      _ ↔ (a j:ℤ) < (M:ℤ)+1 := by omega
      _ ↔ ⌊(j:ℝ)/r+1/2⌋ < (M:ℤ)+1-j := by dsimp only [r]; omega
      _ ↔ (j:ℝ)/r+1/2 < (M:ℝ)+1-j := by rw [Int.floor_lt]; push_cast; rfl
      _ ↔ (1+1/r)*(j:ℝ) < (M:ℝ)+1/2 := by simp only [div_eq_mul_inv,one_mul]; constructor <;> intro h <;> nlinarith only [h]
      _ ↔ _ := by
        rw [← mul_lt_mul_iff_right₀ hδ,←mul_assoc,hsc,one_mul]
        simp [j,X]
  change (c:ℝ) < X ∧ X ≤ (c:ℝ)+1
  constructor
  · rcases eq_or_ne c 0 with hc | hc
    · simpa [hc] using hX
    · have hh := (lower (c-1)).mp (by omega)
      have he : (c-1:ℕ)+1=c := by omega
      exact_mod_cast (by simpa only [← Nat.cast_add_one,he] using hh : (c:ℝ) < X)
  · exact not_lt.mp (fun hx => (lt_irrefl c) ((lower c).mpr hx))

/-- Every translated interval has an error of strictly less than one from
its length times 2-√2. -/
theorem interval_discrepancy
    (H : ∀ n : ℕ, 1 ≤ n → (a n : ℤ) = (n:ℤ)+⌊(n:ℝ)/Real.sqrt 2+1/2⌋) (b L : ℕ) :
    |((Nat.count IsA081477 (b+L+1):ℝ) - (Nat.count IsA081477 (b+1):ℝ)) -
      (2-Real.sqrt 2)*(L:ℝ)| < 1 := by
  obtain ⟨h₁,h₂⟩ := rank_window H b
  obtain ⟨h₃,h₄⟩ := rank_window H (b+L)
  push_cast at h₃ h₄
  rw [abs_lt]
  constructor <;> nlinarith only [h₁,h₂,h₃,h₄]

end Beat81

theorem OMA.solution : type_of% @OMA.S_oeis_a081477.main := by
  intro n hn
  exact Beat81.conclusions_of_closed n hn (Beat81.complement_nth hn)
