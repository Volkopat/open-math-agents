import OMAStatements.S_mo_161095

/-!
# Restrictions on equal products of two Hikorski triples

Source: Jonny Griffiths, *Lyness cycles, elliptic curves, and Hikorski Triples*,
chapter 13, especially Theorem 13.1 and the cross-gcd table.
https://ueaeprints.uea.ac.uk/id/eprint/38238/
https://mathoverflow.net/questions/161095/uniqueness-conjecture-for-integer-triples

For product P the minimum c satisfies c² ∣ P+c; the two other entries
are reconstructed by a quadratic discriminant. Equal products force a gap
between the two minima, bounded quantitatively below in terms of their size.
For distinct triples, no coordinate of either triple can divide a coordinate
of the other. Their three-by-three table of gcds consequently has degree at
least two in every row and column. Six occupied cells form a cycle. Each
edge label divides the sum or difference of its neighbors according to the
two signs; elimination of maxima rules out that cycle. In particular the
four-prime-factor case of the thesis extends to six distinct prime factors.

Seven occupied cells admit the explicit seven-parameter shape in H1.
For the eight- and nine-cell cases H2 uses just the smaller divisor
parameters v and w and the two minima, with an effective finite bound for
each gap. Numerical checks appearing as Lean theorems are kernel proofs.
-/

open OMA.S_mo_161095

namespace Hik

theorem bounds {a b c : ℕ} (h : IsNontrivialHT a b c) : 2 ≤ c ∧ c < b ∧ b ≤ a := by
  obtain ⟨⟨hb, hab, he⟩, hn⟩ := h
  have hb2 : 2 ≤ b := by
    by_contra! hl
    have hb1 : b = 1 := by omega
    subst b
    simp only [Nat.mul_one] at he
    have hc : c = 1 := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos a)
      simpa using he
    exact hn ⟨rfl,hc⟩
  have hc2 : 2 ≤ c := by
    by_contra! hl
    have hlim := Nat.mul_le_mul_left (a+b) (show c ≤ 1 by omega)
    obtain ⟨i, hi⟩ := Nat.exists_eq_add_of_le hb2
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (show 2 ≤ a by omega)
    subst a b
    nlinarith
  have hcb : c < b := by
    by_contra! hl
    nlinarith [Nat.mul_le_mul_left (a+b) hl, Nat.mul_self_le_mul_self hb2]
  exact ⟨hc2,hcb,hab⟩

theorem factor_param {a b c : ℕ} : IsNontrivialHT a b c ↔
    2 ≤ c ∧ ∃ u v : ℕ, 1 ≤ v ∧ v ≤ u ∧ a=c+u ∧ b=c+v ∧ u*v+1=c^2 := by
  constructor
  · intro h
    obtain ⟨hc,hcb,hba⟩ := bounds h
    obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le hcb.le
    obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le (show c ≤ a by omega)
    exact ⟨hc,u,v,by omega,by omega,rfl,rfl,by nlinarith [h.1.2.2]⟩
  · rintro ⟨hc,u,v,hv,hvu,rfl,rfl,hprod⟩
    exact ⟨⟨by omega,by omega,by nlinarith⟩,by omega⟩

theorem same_c {a b p q c : ℕ} (h : IsNontrivialHT a b c) (k : IsNontrivialHT p q c)
    (he : a*b*c=p*q*c) : (a,b,c)=(p,q,c) := by
  have hc : 0 < c := by have := (bounds h).1; omega
  have hp := Nat.eq_of_mul_eq_mul_right hc he
  have hs : a+b=p+q := Nat.eq_of_mul_eq_mul_right hc (by rw [h.1.2.2,k.1.2.2,hp])
  have hba := h.1.2.1
  have hqp := k.1.2.1
  zify at hp hs
  have hz : ((a:ℤ)-p)*((a:ℤ)-q)=0 := by linear_combination (a:ℤ)*hs-hp
  rcases mul_eq_zero.mp hz with hz|hz <;>
    obtain ⟨rfl,rfl⟩ : a=p ∧ b=q := by constructor <;> omega
  all_goals rfl

theorem product_data {a b c : ℕ} (h : IsNontrivialHT a b c) :
    c^2 ∣ a*b*c+c ∧ c ∣ a*b*c ∧ c.Coprime (a*b*c/c) ∧
    (a*b*c+c)/c^2 = a+b ∧ a*b*c/c = a*b := by
  have hc : 0 < c := by have := (bounds h).1; omega
  have he := h.1.2.2
  have he' : a*b*c+c = (a+b)*c^2 := calc
    _ = (a*b+1)*c := by ring
    _ = _ := by rw [←he]; ring
  have hdiv : a*b*c/c=a*b := Nat.mul_div_cancel _ hc
  have hcdiv : c ∣ a*b+1 := ⟨a+b, by rw [←he, Nat.mul_comm]⟩
  have cop : c.Coprime (a*b) := by
    exact Nat.Coprime.of_dvd_left hcdiv (by simp)
  exact ⟨⟨a+b,by rw [he',Nat.mul_comm]⟩,dvd_mul_left _ _,by simpa only [hdiv] using cop,
    by rw [he', Nat.mul_div_cancel _ (pow_pos hc _)],hdiv⟩

private theorem square_reconstruct {s t d : ℕ} (ht : 0<t) (hh : d^2 + 4*t = s^2) :
    ∃ a b : ℕ, 1 ≤ b ∧ b ≤ a ∧ a+b=s ∧ a*b=t := by
  have hd : d < s := by
    by_contra! h
    nlinarith [Nat.mul_self_le_mul_self h]
  have hmod : d % 2 = s % 2 := by
    have hsq (k : ℕ) : k^2%2=k%2 := by
      rw [pow_two, Nat.mul_mod]
      have hk := Nat.mod_lt k (by decide : 0<2)
      interval_cases h : k%2 <;> decide
    calc
      _ = d^2%2 := (hsq d).symm
      _ = (d^2+4*t)%2 := by omega
      _ = s^2%2 := congrArg (· % 2) hh
      _ = _ := hsq s
  let b := (s-d)/2
  have hsb : s = 2*b+d := by dsimp [b]; omega
  refine ⟨b+d,b,by omega,by omega,by omega,?_⟩
  rw [hsb] at hh
  nlinarith

theorem admissible_iff (P c : ℕ) :
    (∃ a b : ℕ, IsNontrivialHT a b c ∧ a*b*c=P) ↔
      2 ≤ c ∧ c^2 ∣ P+c ∧ ∃ d : ℕ, d^2 + 4*(P/c) = ((P+c)/c^2)^2 := by
  constructor
  · rintro ⟨a,b,h,rfl⟩
    obtain ⟨hdiv,_,_,hs,hp⟩ := product_data h
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le h.1.2.1
    refine ⟨(bounds h).1,hdiv,k,?_⟩
    rw [hs,hp,hk]
    ring
  · rintro ⟨hc, hdiv,d,hd⟩
    have hcpos : 0<c := by omega
    let s := (P+c)/c^2
    have hs : s*c^2=P+c := Nat.div_mul_cancel hdiv
    have hcp : c ∣ P := by
      have hd' : c ∣ P+c := dvd_trans (dvd_pow_self _ (by decide : 2≠0)) hdiv
      simpa using Nat.dvd_sub hd' (dvd_refl c)
    let t := P/c
    have ht : t*c=P := Nat.div_mul_cancel hcp
    have hpt : 0<t := by
      by_contra! hz
      have ht0 : t = 0 := by omega
      rw [ht0,zero_mul] at ht
      rw [←ht,zero_add] at hdiv
      have hle := Nat.le_of_dvd hcpos hdiv
      nlinarith [Nat.mul_le_mul_right c hc]
    obtain ⟨a,b,hb,hab,hsum,hmul⟩ := square_reconstruct hpt hd
    have hlin : s*c=t+1 := by
      apply Nat.eq_of_mul_eq_mul_right hcpos
      calc
        s*c*c = s*c^2 := by ring
        _ = P+c := hs
        _ = (t+1)*c := by rw [←ht, add_mul, one_mul]
    exact ⟨a,b,⟨⟨hb,hab,by rw [hsum,hmul,hlin]⟩,by omega⟩,by rw [hmul,ht]⟩


theorem sharp_bounds {a b c : ℕ} (h : IsNontrivialHT a b c) :
    4*c^3 ≤ a*b*c+c ∧ a*b*c+c ≤ c^4 + 2*c^3 := by
  obtain ⟨hc,u,v,hv,hvu,rfl,rfl,hprod⟩ := factor_param.mp h
  have lower : 2*c ≤ u+v := by
    by_contra! hl
    have hsq := Nat.pow_le_pow_left (show u+v+1 ≤ 2*c by omega) 2
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hvu
    nlinarith
  have upper : u+v ≤ c^2 := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ u by omega)
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hv
    nlinarith
  have he := h.1.2.2
  have hr : (c+u)*(c+v)*c+c = (2*c+(u+v))*c^2 := calc
    _ = ((c+u)*(c+v)+1)*c := by ring
    _ = _ := by rw [←he]; ring
  rw [hr]
  constructor
  · nlinarith only [Nat.mul_le_mul_right (c^2) lower]
  · nlinarith only [Nat.mul_le_mul_right (c^2) upper]

theorem bounds_attained {c : ℕ} (hc : 2 ≤ c) :
    (∃ a b : ℕ, IsNontrivialHT a b c ∧ a*b*c+c=4*c^3) ∧
    (∃ a b : ℕ, IsNontrivialHT a b c ∧ a*b*c+c=c^4+2*c^3) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hc
  constructor
  · refine ⟨(2+k)+(k+3),(2+k)+(k+1),factor_param.mpr
      ⟨hc,k+3,k+1,by omega,by omega,rfl,rfl,by ring⟩,by ring⟩
  · refine ⟨(2+k)+(3+4*k+k^2),(2+k)+1,factor_param.mpr
      ⟨hc,3+4*k+k^2,1,by decide,by omega,rfl,rfl,by ring⟩,by ring⟩

theorem divisor_test (P c : ℕ) :
    (∃ a b : ℕ, IsNontrivialHT a b c ∧ a*b*c=P) ↔
      2 ≤ c ∧ ∃ v : ℕ, 1 ≤ v ∧ v < c ∧ v ∣ c^2-1 ∧
        (c+(c^2-1)/v)*(c+v)*c=P := by
  constructor
  · rintro ⟨a,b,h,rfl⟩
    obtain ⟨hc,u,v,hv,hvu,rfl,rfl,hp⟩ := factor_param.mp h
    have he : c^2-1=u*v := by omega
    have hvc : v<c := by
      by_contra! h
      nlinarith [Nat.mul_le_mul (show c ≤ u by omega) h]
    refine ⟨hc,v,hv,hvc,⟨u,by rw [he,mul_comm]⟩,?_⟩
    rw [he, Nat.mul_div_cancel _ (by omega)]
  · rintro ⟨hc,v,hv,hvc,hdiv,rfl⟩
    let u := (c^2-1)/v
    have hp : u*v+1=c^2 := by
      have hsq : 1 ≤ c^2 := by simpa using Nat.pow_le_pow_left (show 1 ≤ c by omega) 2
      have := Nat.div_mul_cancel hdiv
      dsimp [u]
      omega
    have hvu : v ≤ u := by
      by_contra! h
      have hsq := Nat.mul_le_mul (show u+1 ≤ c by omega) (show v+1 ≤ c by omega)
      nlinarith
    exact ⟨c+u,c+v,factor_param.mpr ⟨hc,u,v,hv,hvu,rfl,rfl,hp⟩,rfl⟩

theorem uniqueness_iff : (type_of% @OMA.S_mo_161095.main) ↔
    ∀ P c r : ℕ,
      (2 ≤ c ∧ c^2 ∣ P+c ∧ ∃ d : ℕ, d^2+4*(P/c)=((P+c)/c^2)^2) →
      (2 ≤ r ∧ r^2 ∣ P+r ∧ ∃ d : ℕ, d^2+4*(P/r)=((P+r)/r^2)^2) → c=r := by
  constructor
  · intro H P c r hc hr
    obtain ⟨a,b,ht,he⟩ := (admissible_iff P c).mpr hc
    obtain ⟨p,q,ht',he'⟩ := (admissible_iff P r).mpr hr
    exact congrArg (fun x : ℕ × ℕ × ℕ => x.2.2) (H a b c p q r ht ht' (he.trans he'.symm))
  · intro H a b c p q r ht ht' he
    have hc := (admissible_iff (a*b*c) c).mp ⟨a,b,ht,rfl⟩
    have hr := (admissible_iff (a*b*c) r).mp ⟨p,q,ht',he.symm⟩
    obtain rfl := H _ _ _ hc hr
    exact same_c ht ht' he

end Hik

open OMA.S_mo_161095

namespace Hik

private theorem offset_congr {P Q c : ℕ} (hp : c^2 ∣ P+c) (hq : c^2 ∣ Q+c) :
    P ≡ Q [MOD c^2] :=
  Nat.ModEq.add_right_cancel' c ((Nat.modEq_zero_iff_dvd.mpr hp).trans
    (Nat.modEq_zero_iff_dvd.mpr hq).symm)

theorem unique_crt_candidate {P Q c r : ℕ} (h : c.Coprime r)
    (hpc : c^2 ∣ P+c) (hpr : r^2 ∣ P+r) (hqc : c^2 ∣ Q+c) (hqr : r^2 ∣ Q+r)
    (hp : P < c^2*r^2) (hq : Q < c^2*r^2) : P=Q := by
  have hh := (Nat.modEq_and_modEq_iff_modEq_mul ((h.pow_left 2).pow_right 2)).mp
    ⟨offset_congr hpc hqc,offset_congr hpr hqr⟩
  simpa only [Nat.ModEq,Nat.mod_eq_of_lt hp,Nat.mod_eq_of_lt hq] using hh

theorem no_consecutive {a b p q c : ℕ} (h : IsNontrivialHT a b c)
    (h' : IsNontrivialHT p q (c+1)) : a*b*c ≠ p*q*(c+1) := by
  intro he
  have hc := (bounds h).1
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hc
  let Q := c*(c+1)*(k^2+3*k+1)
  have hqc : Q+c = c^2*(k^2+4*k+2) := by dsimp [Q]; rw [hk]; ring
  have hqr : Q+(c+1) = (c+1)^2*(k+1)^2 := by dsimp [Q]; rw [hk]; ring
  have hU := (sharp_bounds h).2
  have hP : a*b*c=Q := by
    apply unique_crt_candidate (c := c) (r := c+1) (by simp)
      (product_data h).1 (by rw [he]; exact (product_data h').1)
      ⟨_,hqc⟩ ⟨_,hqr⟩
    · nlinarith
    · dsimp [Q]; rw [hk]; nlinarith
  have hrLow := (sharp_bounds h').1
  rw [←he,hP,hqr] at hrLow
  have hk5 : 5≤k := by
    by_contra! hl
    rw [hk] at hrLow
    interval_cases k <;> norm_num at hrLow
  obtain ⟨_,u,v,hv,hvu,ha,hb,huv⟩ := factor_param.mp h
  have hs : a+b=k^2+4*k+2 := by
    have hh := (product_data h).2.2.2.1
    rw [hP,hqc,Nat.mul_div_cancel_left _ (by positivity : 0 < c^2)] at hh
    exact hh.symm
  have hv2 : 2≤v := by
    by_contra! hl
    have hv1 : v=1 := by omega
    rw [hv1,mul_one] at huv
    rw [ha,hb,hv1,hk] at hs
    rw [hk] at huv
    nlinarith
  obtain ⟨i,hi⟩ := Nat.exists_eq_add_of_le hv2
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le (show 2≤u by omega)
  have hgap : 2*(u+v) ≤ u*v+4 := by rw [hi,hj]; nlinarith only [Nat.zero_le (i*j)]
  rw [ha,hb,hk] at hs
  rw [hk] at huv
  nlinarith only [hs,huv,hgap,Nat.mul_self_le_mul_self hk5]


theorem shared_square_dvd_gap {P c r g : ℕ} (hgc : g ∣ c) (hgr : g ∣ r)
    (hc : c^2 ∣ P+c) (hr : r^2 ∣ P+r) : g^2 ∣ r-c := by
  have hx := Nat.dvd_sub ((pow_dvd_pow_of_dvd hgr 2).trans hr) ((pow_dvd_pow_of_dvd hgc 2).trans hc)
  simpa only [Nat.add_sub_add_left] using hx

theorem no_gap_two {a b p q c : ℕ} (h : IsNontrivialHT a b c)
    (h' : IsNontrivialHT p q (c+2)) : a*b*c ≠ p*q*(c+2) := by
  intro he
  have hpc := (product_data h).1
  have hpr : (c+2)^2 ∣ a*b*c+(c+2) := by rw [he]; exact (product_data h').1
  have hodd : Odd c := by
    by_contra hn
    obtain ⟨i,hi⟩ := Nat.not_odd_iff_even.mp hn
    have heven : 2 ∣ c := ⟨i,by omega⟩
    have heven' : 2 ∣ c+2 := dvd_add heven (dvd_refl 2)
    have hfour := shared_square_dvd_gap heven heven' hpc hpr
    simp at hfour
  obtain ⟨k,hk⟩ := hodd
  let Q := c*(c+2)*(4*k^2+7*k+2)
  have hqc : Q+c = c^2*(4*k^2+11*k+7) := by dsimp [Q]; rw [hk]; ring
  have hqr : Q+(c+2) = (c+2)^2*(4*k^2+3*k+1) := by dsimp [Q]; rw [hk]; ring
  have hco : c.Coprime (c+2) := by
    rw [Nat.coprime_self_add_right]
    exact Nat.coprime_two_right.mpr ⟨k,hk⟩
  have hu := (sharp_bounds h).2
  have hQ : a*b*c=Q := by
    apply unique_crt_candidate hco hpc hpr ⟨_,hqc⟩ ⟨_,hqr⟩
    · nlinarith only [hu, (bounds h).1, Nat.zero_le (c^2),Nat.zero_le (c^3)]
    · dsimp [Q]; rw [hk]; nlinarith only [Nat.zero_le k, Nat.zero_le (k^2), Nat.zero_le (k^3)]
  rw [hQ,hqc,hk] at hu
  nlinarith only [hu,Nat.zero_le k,Nat.zero_le (k^2),Nat.zero_le (k^3)]

end Hik

namespace Hik

theorem gap_estimate {c r d v g k : ℤ} (hc : 1≤c) (hd : 1≤d) (hr : r=c+d)
    (hv : 1≤v) (hvc : v≤c) (hg : 1≤g) (hgd : g^2≤d) (hk : 1≤k)
    (he : k*v*r^2 = g*(d^2*(c+v)^2+(3*r-c)*v-d^2)) : r ≤ 49*d^5 := by
  have hrp : 0<r := by omega
  have hds : 1≤d^2 := by nlinarith only [sq_nonneg (d-1),hd]
  have hrs : 0<r^2 := sq_pos_of_pos hrp
  have hgs : 0≤g := by omega
  have hvr : 0≤v*r^2 := by positivity
  have hD : 0≤3*r-c := by omega
  have hsa : (c+v)^2 ≤ 4*r^2 := calc
    _ ≤ (2*r)^2 := by gcongr; omega
    _ = _ := by ring
  have hcv : (3*r-c)*v ≤ 3*r^2 := calc
    _ ≤ (3*r)*r := by gcongr <;> omega
    _ = _ := by ring
  let M := 7*g*d^2
  have hvM : v≤M := by
    apply le_of_mul_le_mul_right (a := r^2) _ hrs
    calc
      v*r^2 ≤ k*v*r^2 := by nlinarith only [mul_nonneg (show 0≤k-1 by omega) hvr]
      _ = _ := he
      _ ≤ g*((4*d^2+3)*r^2) := by
        apply mul_le_mul_of_nonneg_left _ hgs
        nlinarith only [mul_le_mul_of_nonneg_left hsa (sq_nonneg d), hcv,sq_nonneg d]
      _ ≤ M*r^2 := by
        dsimp [M]
        nlinarith only [mul_nonneg (mul_nonneg hgs (show 0≤d^2-1 by omega)) hrs.le]
  have hdM : d≤M := by
    dsimp [M]
    have hh : d ≤ d^2 := by nlinarith only [mul_nonneg (show 0≤d-1 by omega) (show 0≤d by omega)]
    nlinarith only [mul_nonneg (show 0≤g-1 by omega) (sq_nonneg d), hh, sq_nonneg d]
  have hMp : 0≤M := by omega
  let F := d^2*(v-d)*(c+v+r)+(3*r-c)*v-d^2
  have hdelta : (k*v-g*d^2)*r^2=g*F := by
    dsimp [F]
    rw [hr] at he ⊢
    linear_combination he
  have hF : F ≠ 0 := by
    rcases le_or_gt d v with h | h
    · have hpos : 0≤d^2*(v-d)*(c+v+r) := by
        exact mul_nonneg (mul_nonneg (sq_nonneg d) (by omega)) (by omega)
      have hh : d*d < (3*r-c)*v := calc
        _ < (3*r-c)*d := by gcongr; omega
        _ ≤ (3*r-c)*v := mul_le_mul_of_nonneg_left h hD
      dsimp [F]
      nlinarith only [hpos,hh]
    · have hpow : 3*v ≤ d^2 := by nlinarith only [sq_nonneg (d-2),h,hv]
      have hneg : d^2*(v-d)*(c+v+r) ≤ -d^2*(c+v+r) := by
        apply mul_le_mul_of_nonneg_right _ (by omega)
        nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg d) (show v-d+1≤0 by omega)]
      have hfirst : 3*v*r ≤ d^2*(c+v+r) := calc
        _ ≤ d^2*r := mul_le_mul_of_nonneg_right hpow hrp.le
        _ ≤ _ := mul_le_mul_of_nonneg_left (by omega) (sq_nonneg d)
      have hsecond : (3*r-c)*v ≤ 3*v*r := by nlinarith only [mul_nonneg (show 0≤c by omega) (show 0≤v by omega)]
      dsimp [F]
      nlinarith only [hneg,hfirst,hsecond,hds]
  have hneq : k*v ≠ g*d^2 := by
    intro hh
    rw [hh,sub_self,zero_mul] at hdelta
    exact hF ((mul_eq_zero.mp hdelta.symm).resolve_left (by omega))
  have hlead (z : ℤ) (hz : z≤M) : d^2*z*(c+v+r) ≤ 3*d^2*M*r := calc
    _ ≤ d^2*M*(c+v+r) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz (sq_nonneg d)) (by omega)
    _ ≤ d^2*M*(3*r) := mul_le_mul_of_nonneg_left (by omega) (mul_nonneg (sq_nonneg d) hMp)
    _ = _ := by ring
  have hsmall : (3*r-c)*v ≤ 3*M*r := calc
    _ ≤ (3*r)*M := by gcongr; omega
    _ = _ := by ring
  have hMr : 1≤M*r := by
    calc
      (1:ℤ) = 1*1 := by norm_num
      _ ≤ M*r := by gcongr <;> omega
  have hMr' : 0≤M*r := by omega
  have hsmall' : M*r ≤ d^2*M*r := by nlinarith only [mul_nonneg (show 0≤d^2-1 by omega) hMr']
  have hlast : d^2 ≤ d^2*M*r := by nlinarith only [mul_nonneg (sq_nonneg d) (show 0≤M*r-1 by omega)]
  have hweight : 0≤d^2*M*r := by positivity
  have huF : F≤7*d^2*M*r := by
    dsimp [F]
    nlinarith only [hlead (v-d) (by omega),hsmall,hsmall',sq_nonneg d,hweight]
  have hlF : -(7*d^2*M*r)≤F := by
    dsimp [F]
    nlinarith only [hlead (d-v) (by omega),mul_nonneg hD (show 0≤v by omega),hlast,hweight]
  have hcr : r^2 ≤ (7*g*d^2*M)*r := by
    rcases lt_or_gt_of_ne hneq with ht|ht
    · nlinarith only [hdelta,mul_le_mul_of_nonneg_right (show k*v-g*d^2 ≤ -1 by omega) hrs.le,
        mul_le_mul_of_nonneg_left hlF hgs]
    · nlinarith only [hdelta,mul_le_mul_of_nonneg_right (show 1 ≤ k*v-g*d^2 by omega) hrs.le,
        mul_le_mul_of_nonneg_left huF hgs]
  rw [pow_two] at hcr
  have hrM := le_of_mul_le_mul_right hcr hrp
  dsimp [M] at hrM
  nlinarith only [hrM,mul_le_mul_of_nonneg_right hgd (show 0≤d^4 by positivity)]

end Hik

namespace Hik

/-- A pair of different roots forces the larger denominator to grow by at least one. -/
theorem two_root_estimate {c r d v w P : ℤ} (hc : 2≤c) (hd : 1≤d) (hr : r=c+d)
    (hv : 1≤v) (hw : 1≤w) (hwr : w≤r)
    (hp : v*P=c^2*(c+v)^2-c*(c+v))
    (hp' : w*P=r^2*(r+w)^2-r*(r+w)) : r≤385*v*d := by
  have hdp : 0≤d := by omega
  have hvp : 0≤v := by omega
  have hwp : 0≤w := by omega
  have hcp : 0<c := by omega
  have hrp : 0<r := by omega
  have hVD : d ≤ v*d := by nlinarith only [mul_nonneg (show 0≤v-1 by omega) hdp]
  have hVD' : v ≤ v*d := by nlinarith only [mul_nonneg (show 0≤d-1 by omega) hvp]
  by_cases hshort : 2*c < r
  · nlinarith only [hr,hshort,hVD,hd]
  by_cases hlarge : c < 4*v
  · nlinarith only [hr,hlarge,hVD,hVD',hv]
  have hc2 : 4≤c^2 := by nlinarith only [sq_nonneg (c-2),hc]
  let B := c^2-1-v*w
  let K := r^3+r^2*c+r*c^2+c^3 +
      2*w*(r^2+r*c+c^2) + (w^2-1)*(r+c) - w
  have hsq : 2*v*w ≤ c^2 := calc
    _ ≤ (2*v)*(2*c) := mul_le_mul_of_nonneg_left (by omega) (show 0≤2*v by omega)
    _ ≤ c*c := by nlinarith only [mul_nonneg (show 0≤c-4*v by omega) hcp.le]
    _ = _ := by ring
  have hBk : c^2≤4*B := by dsimp [B]; nlinarith only [hsq,hc2]
  have hBp : 0<B := by omega
  have hKp : 0<K := by
    have hw2 : 1≤w^2 := by nlinarith only [sq_nonneg (w-1),hw]
    have hu : w ≤ 2*w*(r^2+r*c+c^2) := by
      have ha : 1 ≤ r^2+r*c+c^2 := by nlinarith only [hc2,sq_nonneg r,mul_nonneg hrp.le hcp.le]
      nlinarith only [mul_nonneg hwp (show 0≤r^2+r*c+c^2-1 by omega),hw]
    dsimp [K]
    nlinarith only [hu,mul_nonneg (show 0≤w^2-1 by omega) (show 0≤r+c by omega),
      pow_pos hrp 3,mul_nonneg (sq_nonneg r) hcp.le,mul_nonneg hrp.le (sq_nonneg c),pow_nonneg hcp.le 3]
  have hck : c≤r := by omega
  have h1 : r^2*c ≤ r^3 := by
    calc
      _ ≤ r^2*r := by gcongr
      _ = _ := by ring
  have h2 : r*c^2 ≤ r^3 := by
    calc
      _ ≤ r*r^2 := by gcongr
      _ = _ := by ring
  have h3 : c^3 ≤ r^3 := by gcongr
  have h4 : 2*w*(r^2+r*c+c^2) ≤ 6*r^3 := calc
    _ ≤ 2*r*(r^2+r*r+r^2) := by gcongr
    _ = _ := by ring
  have h5 : (w^2-1)*(r+c) ≤ 2*r^3 := calc
    _ ≤ w^2*(r+c) := by gcongr; omega
    _ ≤ r^2*(r+r) := by gcongr
    _ = _ := by ring
  have hK : K≤12*r^3 := by dsimp [K]; linarith
  have hid : (w-v)*c^2*B = v*d*K := by
    dsimp [B,K]
    rw [hr] at hp' ⊢
    linear_combination v*hp'-w*hp
  have hwv : v<w := by
    by_contra! h
    have hn : (w-v)*c^2*B ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by omega) (sq_nonneg c)) hBp.le
    have hpositive : 0<v*d*K := mul_pos (mul_pos (by omega) (by omega)) hKp
    omega
  have hl : c^4 ≤ 4*((w-v)*c^2*B) := calc
    _ = c^2*c^2 := by ring
    _ ≤ c^2*(4*B) := mul_le_mul_of_nonneg_left hBk (sq_nonneg c)
    _ ≤ 4*((w-v)*c^2*B) := by nlinarith only [mul_nonneg (mul_nonneg (show 0≤w-v-1 by omega) (sq_nonneg c)) hBp.le]
  have hup : 4*(v*d*K) ≤ 384*v*d*c^3 := calc
    _ ≤ 4*(v*d*(12*r^3)) := by gcongr
    _ ≤ 4*(v*d*(12*(2*c)^3)) := by gcongr; omega
    _ = _ := by ring
  rw [hid] at hl
  have hupper : c*c^3 ≤ (384*v*d)*c^3 := by nlinarith only [hl,hup]
  have hCb := le_of_mul_le_mul_right hupper (pow_pos hcp 3)
  nlinarith only [hCb,hVD,hr]

end Hik

open OMA.S_mo_161095

namespace Hik

private theorem mod_aux {x y t H : ℕ} (ht : (t:ℤ)^2 = ((y:ℤ)-x)^2)
    (h : x ∣ y*H+1) : x ∣ t^2*H+x+y := by
  obtain ⟨m,hm⟩ := h
  rw [←Int.natCast_dvd_natCast]
  push_cast
  zify at hm
  refine ⟨(x:ℤ)*H-2*y*H+1+y*m,?_⟩
  rw [ht]
  linear_combination (y:ℤ)*hm

private theorem collision_coefficient {P c r : ℕ} (hc : 0<c) (hcr : c<r)
    (hpc : c ∣ P) (hpr : r ∣ P) (hsc : c^2 ∣ P+c) (hsr : r^2 ∣ P+r) :
    ∃ k : ℕ, 0<k ∧ (c.gcd r)*((r-c)^2*P+c*r*(c+r))=k*c^2*r^2 := by
  let g := c.gcd r
  let x := c/g
  let y := r/g
  have hg : 0<g := Nat.gcd_pos_of_pos_left _ hc
  have hgc : g ∣ c := Nat.gcd_dvd_left _ _
  have hgr : g ∣ r := Nat.gcd_dvd_right _ _
  have hx : x*g=c := Nat.div_mul_cancel hgc
  have hy : y*g=r := Nat.div_mul_cancel hgr
  have hcop : x.Coprime y := Nat.coprime_div_gcd_div_gcd hg
  have hdvd (w z : ℕ) (hw : w*g=z) (hz : z ∣ P) : w ∣ P/g := by
    obtain ⟨m,hm⟩ := hz
    refine ⟨m,?_⟩
    rw [hm,←hw,mul_right_comm w g m,Nat.mul_div_cancel _ hg]
  have hprod : x*y ∣ P/g := hcop.mul_dvd_of_dvd_of_dvd (hdvd _ _ hx hpc) (hdvd _ _ hy hpr)
  obtain ⟨H,hH⟩ := hprod
  have he : P=x*y*H*g := by rw [←hH,Nat.div_mul_cancel (hgc.trans hpc)]
  have hxy : x<y := lt_of_mul_lt_mul_right (hx.trans_lt (hcr.trans_eq hy.symm)) (Nat.zero_le _)
  obtain ⟨t,ht⟩ := Nat.exists_eq_add_of_le hxy.le
  have hd : r-c=t*g := by rw [ht,add_mul,hx] at hy; omega
  obtain ⟨s,hs⟩ := hsc
  obtain ⟨z,hz⟩ := hsr
  have hsx : y*H+1=c*s := by
    apply Nat.eq_of_mul_eq_mul_left hc
    calc
      c*(y*H+1)=P+c := by rw [he,←hx]; ring
      _=c*(c*s) := by rw [hs]; ring
  have hsy : x*H+1=r*z := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0<r)
    calc
      r*(x*H+1)=P+r := by rw [he,←hy]; ring
      _=r*(r*z) := by rw [hz]; ring
  have htI : (t:ℤ)=(y:ℤ)-x := by omega
  have dx : x ∣ t^2*H+x+y := mod_aux (by rw [htI]) ⟨g*s,by rw [hsx,←hx]; ring⟩
  have dy' : y ∣ t^2*H+y+x := mod_aux (by rw [htI]; ring) ⟨g*z,by rw [hsy,←hy]; ring⟩
  have dy : y ∣ t^2*H+x+y := by simpa only [add_right_comm] using dy'
  obtain ⟨k,hk⟩ := hcop.mul_dvd_of_dvd_of_dvd dx dy
  have hkpos : 0<k := by
    have hp : 0<y := lt_of_le_of_lt (Nat.zero_le x) hxy
    by_contra! h
    have hk0 : k=0 := by omega
    rw [hk0,mul_zero] at hk
    exact (Nat.ne_of_gt (Nat.add_pos_right _ hp)) hk
  refine ⟨k,hkpos,?_⟩
  change g*((r-c)^2*P+c*r*(c+r))=k*c^2*r^2
  rw [hd,he,←hx,←hy]
  linear_combination (g^4*x*y)*hk


private theorem digit_identity {c r d v u g P k : ℤ} (hr : r=c+d)
    (huv : u*v+1=c^2) (hp : P=(c+u)*(c+v)*c) (hc : c≠0)
    (hs : g*(d^2*P+c*r*(c+r))=k*c^2*r^2) :
    k*v*r^2=g*(d^2*(c+v)^2+(3*r-c)*v-d^2) := by
  have hvp : v*P=c^2*(c+v)^2-c*(c+v) := by
    rw [hp]
    linear_combination (c*(c+v))*huv
  apply mul_left_cancel₀ (pow_ne_zero 2 hc)
  calc
    c^2*(k*v*r^2) = v*(k*c^2*r^2) := by ring
    _ = g*(d^2*(v*P)+v*c*r*(c+r)) := by rw [←hs]; ring
    _ = _ := by rw [hvp,hr]; ring

theorem uniform_gap {a b p q c r : ℕ} (h : IsNontrivialHT a b c)
    (h' : IsNontrivialHT p q r) (he : a*b*c=p*q*r) (hcr : c<r) : r ≤ 49*(r-c)^5 := by
  let P := a*b*c
  let g := c.gcd r
  let d := r-c
  have hc := (bounds h).1
  have hg : 0<g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hd : 0<d := Nat.sub_pos_of_lt hcr
  have hr : r=c+d := by dsimp [d]; omega
  have hsc : c^2 ∣ P+c := (product_data h).1
  have hsr : r^2 ∣ P+r := by dsimp [P]; rw [he]; exact (product_data h').1
  have hpc : c ∣ P := (product_data h).2.1
  have hpr : r ∣ P := by dsimp [P]; rw [he]; exact (product_data h').2.1
  have hgd : g^2≤d := Nat.le_of_dvd hd
    (shared_square_dvd_gap (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _) hsc hsr)
  obtain ⟨k,hk,hF⟩ := collision_coefficient (by omega) hcr hpc hpr hsc hsr
  change g*(d^2*P+c*r*(c+r))=k*c^2*r^2 at hF
  obtain ⟨_,u,v,hv,hvu,ha,hb,huv⟩ := factor_param.mp h
  have hvb : v≤c := by
    by_contra! ht
    nlinarith only [huv,Nat.mul_le_mul (show c+1≤u by omega) (show c+1≤v by omega)]
  have hp : P=(c+u)*(c+v)*c := by dsimp [P]; rw [ha,hb]
  zify at hr huv hp hF hgd
  have heq := digit_identity hr huv hp (by exact_mod_cast (show c≠0 by omega)) hF
  change r ≤ 49*d^5
  exact_mod_cast gap_estimate (c := (c:ℤ)) (by omega) (by exact_mod_cast hd) hr
    (by exact_mod_cast hv) (by exact_mod_cast hvb) (by exact_mod_cast hg) hgd
    (by exact_mod_cast hk) heq

private theorem row_bound {c r d v g k : ℤ} (hc : 1≤c) (hd : 1≤d) (hr : r=c+d)
    (hv : 1≤v) (hvc : v≤c) (hg : 1≤g) (hk : 1≤k)
    (he : k*v*r^2 = g*(d^2*(c+v)^2+(3*r-c)*v-d^2)) : v ≤ 7*g*d^2 := by
  have hrp : 0<r := by omega
  have hds : 1≤d^2 := by nlinarith only [sq_nonneg (d-1),hd]
  have hrs : 0<r^2 := sq_pos_of_pos hrp
  have hgs : 0≤g := by omega
  have hvr : 0≤v*r^2 := by positivity
  have hD : 0≤3*r-c := by omega
  have hsa : (c+v)^2 ≤ 4*r^2 := calc
    _ ≤ (2*r)^2 := by gcongr; omega
    _ = _ := by ring
  have hcv : (3*r-c)*v ≤ 3*r^2 := calc
    _ ≤ (3*r)*r := by gcongr <;> omega
    _ = _ := by ring
  let M := 7*g*d^2
  have hvM : v≤M := by
    apply le_of_mul_le_mul_right (a := r^2) _ hrs
    calc
      v*r^2 ≤ k*v*r^2 := by nlinarith only [mul_nonneg (show 0≤k-1 by omega) hvr]
      _ = _ := he
      _ ≤ g*((4*d^2+3)*r^2) := by
        apply mul_le_mul_of_nonneg_left _ hgs
        nlinarith only [mul_le_mul_of_nonneg_left hsa (sq_nonneg d), hcv,sq_nonneg d]
      _ ≤ M*r^2 := by
        dsimp [M]
        nlinarith only [mul_nonneg (mul_nonneg hgs (show 0≤d^2-1 by omega)) hrs.le]
  exact hvM

theorem joint_gap {a b p q c r : ℕ} (h : IsNontrivialHT a b c)
    (h' : IsNontrivialHT p q r) (he : a*b*c=p*q*r) (hcr : c<r) :
    r ≤ 2695*(c.gcd r)*(r-c)^3 ∧ r^2 ≤ 7263025*(r-c)^7 := by
  let P := a*b*c
  let g := c.gcd r
  let d := r-c
  have hc := (bounds h).1
  have hg : 0<g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hd : 0<d := Nat.sub_pos_of_lt hcr
  have hr : r=c+d := by dsimp [d]; omega
  have hsc : c^2 ∣ P+c := (product_data h).1
  have hsr : r^2 ∣ P+r := by dsimp [P]; rw [he]; exact (product_data h').1
  have hpc : c ∣ P := (product_data h).2.1
  have hpr : r ∣ P := by dsimp [P]; rw [he]; exact (product_data h').2.1
  have hgd : g^2≤d := Nat.le_of_dvd hd
    (shared_square_dvd_gap (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _) hsc hsr)
  obtain ⟨k,hk,hF⟩ := collision_coefficient (by omega) hcr hpc hpr hsc hsr
  change g*(d^2*P+c*r*(c+r))=k*c^2*r^2 at hF
  obtain ⟨_,u,v,hv,hvu,ha,hb,huv⟩ := factor_param.mp h
  have hvb : v≤c := by
    by_contra! ht
    nlinarith only [huv,Nat.mul_le_mul (show c+1≤u by omega) (show c+1≤v by omega)]
  have hp : P=(c+u)*(c+v)*c := by dsimp [P]; rw [ha,hb]

  obtain ⟨_,u',w,hw,hwu,ha',hb',hu'w⟩ := factor_param.mp h'
  have hwr : w≤r := by
    by_contra! ht
    nlinarith only [hu'w,Nat.mul_le_mul (show r+1≤u' by omega) (show r+1≤w by omega)]
  have hp' : P=(r+u')*(r+w)*r := by dsimp [P]; rw [he,ha',hb']
  zify at hr huv hp hF hgd hu'w hp'
  have heq := digit_identity hr huv hp (by exact_mod_cast (show c≠0 by omega)) hF
  have hrow := row_bound (c := (c:ℤ)) (by omega) (by exact_mod_cast hd) hr
    (by exact_mod_cast hv) (by exact_mod_cast hvb) (by exact_mod_cast hg) (by exact_mod_cast hk) heq
  have href {C U V : ℤ} (hs : U*V+1=C^2) (hp₀ : (P:ℤ)=(C+U)*(C+V)*C) :
      V*P=C^2*(C+V)^2-C*(C+V) := by
    rw [hp₀]
    linear_combination (C*(C+V))*hs
  have hR := two_root_estimate (by exact_mod_cast hc) (by exact_mod_cast hd) hr
    (by exact_mod_cast hv) (by exact_mod_cast hw) (by exact_mod_cast hwr) (href huv hp) (href hu'w hp')
  have zD : 0≤(d:ℤ) := by positivity
  have hlim : (r:ℤ) ≤ 2695*g*d^3 := by
    nlinarith only [hR,mul_le_mul_of_nonneg_right hrow zD]
  have hsq : (r:ℤ)^2 ≤ 7263025*d^7 := calc
    _ ≤ (2695*(g:ℤ)*d^3)^2 := by gcongr
    _ = 7263025*(g:ℤ)^2*d^6 := by ring
    _ ≤ 7263025*d*d^6 := by gcongr
    _ = _ := by ring
  change r ≤ 2695*g*d^3 ∧ r^2 ≤ 7263025*d^7
  exact ⟨by exact_mod_cast hlim,by exact_mod_cast hsq⟩

private theorem coeff_bound {c r d v g k : ℤ} (hc : 1≤c) (hd : 1≤d) (hr : r=c+d)
    (hv : 1≤v) (hvc : v≤c) (hg : 1≤g) (_hk : 1≤k)
    (he : k*v*r^2 = g*(d^2*(c+v)^2+(3*r-c)*v-d^2)) : k*v ≤ 7*g*d^2 := by
  have hrp : 0<r := by omega
  have hds : 1≤d^2 := by nlinarith only [sq_nonneg (d-1),hd]
  have hrs : 0<r^2 := sq_pos_of_pos hrp
  have hgs : 0≤g := by omega
  have hvr : 0≤v*r^2 := by positivity
  have hD : 0≤3*r-c := by omega
  have hsa : (c+v)^2 ≤ 4*r^2 := calc
    _ ≤ (2*r)^2 := by gcongr; omega
    _ = _ := by ring
  have hcv : (3*r-c)*v ≤ 3*r^2 := calc
    _ ≤ (3*r)*r := by gcongr <;> omega
    _ = _ := by ring
  let M := 7*g*d^2
  have hvM : k*v≤M := by
    apply le_of_mul_le_mul_right (a := r^2) _ hrs
    calc
      k*v*r^2 = _ := he
      _ ≤ g*((4*d^2+3)*r^2) := by
        apply mul_le_mul_of_nonneg_left _ hgs
        nlinarith only [mul_le_mul_of_nonneg_left hsa (sq_nonneg d), hcv,sq_nonneg d]
      _ ≤ M*r^2 := by
        dsimp [M]
        nlinarith only [mul_nonneg (mul_nonneg hgs (show 0≤d^2-1 by omega)) hrs.le]
  exact hvM


theorem collision_certificate {a b p q c r : ℕ} (h : IsNontrivialHT a b c)
    (h' : IsNontrivialHT p q r) (he : a*b*c=p*q*r) (hcr : c<r) :
    let P := a*b*c
    let d := r-c
    let g := c.gcd r
    ∃ k v : ℕ, 1≤k ∧ 1≤v ∧ v<c ∧ v ∣ c^2-1 ∧ P=(c+(c^2-1)/v)*(c+v)*c ∧
      1≤g ∧ g^2∣d ∧ k*v≤7*g*d^2 ∧
      ((k:ℤ)*v-g*d^2)*c^2 + 2*((k:ℤ)*v*d-(g:ℤ)*(d^2+1)*v)*c +
        ((k:ℤ)*v*d^2-(g:ℤ)*d^2*v^2-3*(g:ℤ)*d*v+(g:ℤ)*d^2)=0 := by
  dsimp only
  let P := a*b*c
  let g := c.gcd r
  let d := r-c
  have hc := (bounds h).1
  have hg : 0<g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hd : 0<d := Nat.sub_pos_of_lt hcr
  have hr : r=c+d := by dsimp [d]; omega
  have hsc : c^2 ∣ P+c := (product_data h).1
  have hsr : r^2 ∣ P+r := by dsimp [P]; rw [he]; exact (product_data h').1
  have hpc : c ∣ P := (product_data h).2.1
  have hpr : r ∣ P := by dsimp [P]; rw [he]; exact (product_data h').2.1
  have hgd : g^2≤d := Nat.le_of_dvd hd
    (shared_square_dvd_gap (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _) hsc hsr)
  obtain ⟨k,hk,hF⟩ := collision_coefficient (by omega) hcr hpc hpr hsc hsr
  change g*(d^2*P+c*r*(c+r))=k*c^2*r^2 at hF
  obtain ⟨_,u,v,hv,hvu,ha,hb,huv⟩ := factor_param.mp h
  have hvb : v≤c := by
    by_contra! ht
    nlinarith only [huv,Nat.mul_le_mul (show c+1≤u by omega) (show c+1≤v by omega)]
  have hp : P=(c+u)*(c+v)*c := by dsimp [P]; rw [ha,hb]
  have hvs : v<c := by
    by_contra! ht
    nlinarith only [huv,Nat.mul_le_mul (show c≤u by omega) ht]
  have hdiv : c^2-1=u*v := by omega
  have hgd' : g^2∣d := shared_square_dvd_gap (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _) hsc hsr
  refine ⟨k,v,hk,hv,hvs,⟨u,by rw [hdiv,mul_comm]⟩,by rw [hdiv,Nat.mul_div_cancel _ hv,ha,hb],hg,hgd',?_ ,?_⟩
  all_goals zify at hr huv hp hF hgd
  all_goals have heq := digit_identity hr huv hp (by exact_mod_cast (show c≠0 by omega)) hF
  · have hk' := coeff_bound (c := (c:ℤ)) (by omega) (by exact_mod_cast hd) hr
      (by exact_mod_cast hv) (by exact_mod_cast hvb) (by exact_mod_cast hg) (by exact_mod_cast hk) heq
    exact_mod_cast hk'
  · rw [hr] at heq
    linear_combination heq

end Hik

namespace Hik

private theorem signed_root {x S : ℤ} (hx : x*x=S) :
    x = Int.sqrt S ∨ x = -Int.sqrt S := by
  rw [←hx,Int.sqrt_eq,Int.natCast_natAbs]
  rcases le_total 0 x with hh|hh
  · left; simp [abs_of_nonneg hh]
  · right; simp [abs_of_nonpos hh]

theorem quadratic_check {A B C x : ℤ} (f : ℤ → Bool) (hx : A*x^2+2*B*x+C=0)
    (h : (if A=0 then (if B=0 then decide (C≠0) else f ((-C)/(2*B)))
          else (let s := Int.sqrt (B^2-A*C); f ((s-B)/A) && f ((-s-B)/A))) = true) :
    f x=true := by
  by_cases ha : A=0
  · rw [if_pos ha] at h
    by_cases hb : B=0
    · simp [ha,hb] at hx
      simp [hb,hx] at h
    · rw [if_neg hb] at h
      have he : -C = x*(2*B) := by rw [ha] at hx; linarith
      simpa only [he,Int.mul_ediv_cancel _ (mul_ne_zero (by decide : (2:ℤ)≠0) hb)] using h
  · rw [if_neg ha] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1,h2⟩ := h
    have hs : (A*x+B)*(A*x+B)=B^2-A*C := by linear_combination A*hx
    rcases signed_root hs with he|he
    · have hh : Int.sqrt (B^2-A*C)-B=x*A := by linear_combination -he
      simpa only [hh,Int.mul_ediv_cancel _ ha] using h1
    · have hh : -Int.sqrt (B^2-A*C)-B=x*A := by linear_combination -he
      simpa only [hh,Int.mul_ediv_cancel _ ha] using h2

end Hik

open OMA.S_mo_161095
namespace Hik

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fixed_gap {a b p q c r : ℕ} (ht : IsNontrivialHT a b c)
    (ht' : IsNontrivialHT p q r) (hP : a*b*c=p*q*r) (hcr : c<r) : 3<r-c := by
  let reject (d g v : ℕ) (x : ℤ) : Bool :=
    let t := x.toNat
    let j := t+d
    let n := (t+(t^2-1)/v)*(t+v)*t
    let s := (n+j)/j^2
    decide (¬(v<t ∧ t.gcd j=g ∧ v ∣ t^2-1 ∧ j^2 ∣ n+j ∧
      (Nat.sqrt (s^2-4*(n/j)))^2+4*(n/j)=s^2))
  let visit (d g k v : ℕ) : Bool :=
    let x : ℤ := (k:ℤ)*v-g*d^2
    let y : ℤ := (k:ℤ)*v*d-(g:ℤ)*(d^2+1)*v
    let z : ℤ := (k:ℤ)*v*d^2-(g:ℤ)*d^2*v^2-3*(g:ℤ)*d*v+(g:ℤ)*d^2
    if x=0 then if y=0 then decide (z≠0) else reject d g v ((-z)/(2*y))
    else
      let s := Int.sqrt (y^2-x*z)
      reject d g v ((s-y)/x) && reject d g v ((-s-y)/x)
  let layer (d : ℕ) : Bool := (List.range' 1 (Nat.sqrt d)).all fun g =>
    if g^2 ∣ d then
      (List.range' 1 (7*g*d^2)).all fun v =>
        (List.range' 1 (7*g*d^2/v)).all fun k => visit d g k v
    else true
  have checked : (List.range' 1 3).all layer=true := by decide +kernel
  by_contra! hdmax
  let d := r-c
  let g := c.gcd r
  have hd : 0<d := Nat.sub_pos_of_lt hcr
  have hr : c+d=r := by dsimp [d]; omega
  obtain ⟨k,v,hk,hv,hvc,hvdiv,hprod,hg,hgd,hkv,heq⟩ := collision_certificate ht ht' hP hcr
  change g^2 ∣ d at hgd
  change k*v ≤ 7*g*d^2 at hkv
  have mem (x n : ℕ) (h : 1≤x) (h' : x≤n) : x ∈ List.range' 1 n :=
    List.mem_range'.mpr ⟨x-1,by omega,by omega⟩
  have hdcheck := List.all_eq_true.mp checked d (mem _ _ hd hdmax)
  change ((List.range' 1 (Nat.sqrt d)).all _)=true at hdcheck
  have hgsq : g ≤ Nat.sqrt d := Nat.le_sqrt.mpr (by simpa [pow_two] using Nat.le_of_dvd hd hgd)
  have hgcheck := List.all_eq_true.mp hdcheck g (mem _ _ hg hgsq)
  rw [if_pos hgd] at hgcheck
  have hvb : v ≤ 7*g*d^2 := le_trans (by simpa using Nat.mul_le_mul_right v hk) hkv
  have hvcheck := List.all_eq_true.mp hgcheck v (mem _ _ hv hvb)
  have hkcheck := List.all_eq_true.mp hvcheck k (mem _ _ hk ((Nat.le_div_iff_mul_le hv).mpr hkv))
  have hbad := quadratic_check (reject d g v) heq hkcheck
  have hnot := of_decide_eq_true hbad
  dsimp only [Int.toNat_natCast] at hnot
  rw [hr,←hprod] at hnot
  obtain ⟨_,hdiv,t,hs⟩ := (admissible_iff (a*b*c) r).mp ⟨p,q,ht',hP.symm⟩
  have hs' : ((a*b*c+r)/r^2)^2-4*(a*b*c/r)=t^2 := by omega
  exact hnot ⟨hvc,rfl,hvdiv,hdiv,by rw [hs',Nat.sqrt_eq']; exact hs⟩

end Hik

open OMA.S_mo_161095

namespace Hik

private theorem monotone_roots {c r d v w P : ℤ} (hc : 2≤c) (hd : 1≤d) (hr : r=c+d)
    (hv : 1≤v) (hw : 1≤w) (hvc : v<c)
    (hp : v*P=c^2*(c+v)^2-c*(c+v))
    (hp' : w*P=r^2*(r+w)^2-r*(r+w)) : v<w := by
  have hcp : 0<c := by omega
  have hrp : 0<r := by omega
  have hwp : 0≤w := by omega
  have hc2 : 4≤c^2 := by nlinarith only [sq_nonneg (c-2),hc]
  let B := c^2-1-v*w
  let K := r^3+r^2*c+r*c^2+c^3 +
      2*w*(r^2+r*c+c^2) + (w^2-1)*(r+c) - w
  have hKp : 0<K := by
    have hw2 : 1≤w^2 := by nlinarith only [sq_nonneg (w-1),hw]
    have hu : w ≤ 2*w*(r^2+r*c+c^2) := by
      have ha : 1 ≤ r^2+r*c+c^2 := by nlinarith only [hc2,sq_nonneg r,mul_nonneg hrp.le hcp.le]
      nlinarith only [mul_nonneg hwp (show 0≤r^2+r*c+c^2-1 by omega),hw]
    dsimp [K]
    nlinarith only [hu,mul_nonneg (show 0≤w^2-1 by omega) (show 0≤r+c by omega),
      pow_pos hrp 3,mul_nonneg (sq_nonneg r) hcp.le,mul_nonneg hrp.le (sq_nonneg c),pow_nonneg hcp.le 3]
  have hid : (w-v)*c^2*B = v*d*K := by
    dsimp [B,K]
    rw [hr] at hp' ⊢
    linear_combination v*hp'-w*hp
  by_contra! h
  have hbound : v*w ≤ (c-1)*(c-1) := by gcongr <;> omega
  have hB : 0≤B := by dsimp [B]; nlinarith only [hbound,hc]
  have hn : (w-v)*c^2*B ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by omega) (sq_nonneg c)) hB
  have hpos : 0<v*d*K := mul_pos (mul_pos (by omega) (by omega)) hKp
  omega

theorem small_divisor_strict {a b p q c r : ℕ} (h : IsNontrivialHT a b c)
    (h' : IsNontrivialHT p q r) (he : a*b*c=p*q*r) (hcr : c<r) :
    b-c < q-r ∧ b<q ∧ p<a := by
  let P := a*b*c
  let d := r-c
  have hd : 0<d := Nat.sub_pos_of_lt hcr
  have hr : r=c+d := by dsimp [d]; omega
  have hc := (bounds h).1
  obtain ⟨_,u,v,hv,hvu,ha,hb,huv⟩ := factor_param.mp h
  obtain ⟨_,u',w,hw,hwu,ha',hb',hu'w⟩ := factor_param.mp h'
  have hvc : v<c := by
    by_contra! ht
    nlinarith only [huv,Nat.mul_le_mul (show c≤u by omega) ht]
  have hp : P=(c+u)*(c+v)*c := by dsimp [P]; rw [ha,hb]
  have hp' : P=(r+u')*(r+w)*r := by dsimp [P]; rw [he,ha',hb']
  zify at hp hp' hr huv hu'w
  have href {C U V : ℤ} (hs : U*V+1=C^2) (hp₀ : (P:ℤ)=(C+U)*(C+V)*C) :
      V*P=C^2*(C+V)^2-C*(C+V) := by
    rw [hp₀]
    linear_combination (C*(C+V))*hs
  have hs := monotone_roots (by exact_mod_cast hc) (by exact_mod_cast hd) hr
    (by exact_mod_cast hv) (by exact_mod_cast hw) (by exact_mod_cast hvc) (href huv hp) (href hu'w hp')
  have hbq : b<q := by omega
  refine ⟨by omega,hbq,?_⟩
  by_contra! hpa
  have hpos : 0<a*b := Nat.mul_pos (by omega) (by omega)
  have hlt := Nat.mul_lt_mul_of_pos_left hcr hpos
  have hle := Nat.mul_le_mul_right r (Nat.mul_le_mul hpa hbq.le)
  omega

end Hik

open OMA.S_mo_161095

namespace Hik

theorem signed_squares {a b c : ℕ} (h : IsNontrivialHT a b c) :
    ((a:ℤ)^2 ∣ (a*b*c:ℕ)- (a:ℤ)) ∧ ((b:ℤ)^2 ∣ (a*b*c:ℕ)- (b:ℤ)) ∧
    ((c:ℤ)^2 ∣ (a*b*c:ℕ)+ (c:ℤ)) := by
  have he := h.1.2.2
  zify at he
  push_cast
  exact ⟨⟨(b:ℤ)-c, by linear_combination (a:ℤ)*he⟩,
    ⟨(a:ℤ)-c, by linear_combination (b:ℤ)*he⟩,
    ⟨(a:ℤ)+b, by linear_combination -(c:ℤ)*he⟩⟩

theorem cross_signed_cell {P g u v e f : ℤ} (hg : g≠0)
    (hl : (g*u)^2 ∣ P-e*(g*u)) (hr : (g*v)^2 ∣ P-f*(g*v)) : g∣e*u-f*v := by
  obtain ⟨l,hl⟩ := hl
  obtain ⟨r,hr⟩ := hr
  refine ⟨v^2*r-u^2*l,mul_left_cancel₀ hg ?_⟩
  linear_combination hr-hl

private theorem leaf_signed_member {a b c t : ℕ} (h : IsNontrivialHT a b c) (ht : t∈[a,b,c]) :
    ∃ e : ℤ, (e=1 ∨ e= -1) ∧ (t:ℤ)^2 ∣ (a*b*c:ℕ) - e*t := by
  obtain ⟨d,f,g⟩ := signed_squares h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl|rfl
  · exact ⟨1,Or.inl rfl,by simpa using d⟩
  · exact ⟨1,Or.inl rfl,by simpa using f⟩
  · exact ⟨-1,Or.inr rfl,by simpa using g⟩

private theorem leaf_modulus {a b c p q r t v : ℕ} (h : IsNontrivialHT a b c)
    (k : IsNontrivialHT p q r) (eq : a*b*c=p*q*r) (ht : t∈[a,b,c])
    (hs : t*v∈[p,q,r]) (hu : 2≤t) (hv : 2≤v) : t ∣ v-1 ∨ t ∣ v+1 := by
  obtain ⟨e,he,de⟩ := leaf_signed_member h ht
  obtain ⟨f,hf,df⟩ := leaf_signed_member k hs
  rw [←eq] at df
  push_cast at df
  have d := cross_signed_cell (u:=1) (v:=(v:ℤ)) (g:=(t:ℤ)) (e:=e) (f:=f)
    (by omega) (by simpa using de) df
  have di : ((t:ℤ)∣(v:ℤ)-1) ∨ ((t:ℤ)∣(v:ℤ)+1) := by
    rcases he with rfl|rfl <;> rcases hf with rfl|rfl <;> simp only [one_mul,mul_one,neg_mul] at d
    · left; simpa only [neg_sub] using (dvd_neg.mpr d)
    · right; simpa only [sub_neg_eq_add,add_comm] using d
    · right
      have ee : -(-1-(v:ℤ))=(v:ℤ)+1 := by ring
      exact ee ▸ dvd_neg.mpr d
    · left
      have ee : -1- -(v:ℤ)=(v:ℤ)-1 := by ring
      exact ee ▸ d
  rcases di with di|di
  · left; exact_mod_cast (show (t:ℤ) ∣ ((v-1:ℕ):ℤ) by simpa [Nat.cast_sub (show 1≤v by omega)] using di)
  · right; exact_mod_cast di

private theorem leaf_between {a b c t : ℕ} (h : IsNontrivialHT a b c) (ht : t∈[a,b,c]) :
    c≤t ∧ t*t<a*b*c := by
  obtain ⟨hc,hcb,hba⟩ := bounds h
  have ha : a<b*c := by nlinarith [h.1.2.2,Nat.mul_le_mul_left a (show c+1≤b by omega)]
  have hmax := Nat.mul_lt_mul_of_pos_left ha (show 0<a by omega)
  have hbds : c≤t ∧ t≤a := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl <;> omega
  exact ⟨hbds.1,by nlinarith [Nat.mul_self_le_mul_self hbds.2]⟩

private theorem leaf_upper {a b c : ℕ} (h : IsNontrivialHT a b c) :
    a*b*c < (c*(c+1))^2 := by
  have he := h.1.2.2
  obtain ⟨hc,u,v,hv,hvu,rfl,rfl,huv⟩ := factor_param.mp h
  have hs : u+v≤c^2 := by
    obtain ⟨i,hi⟩ := Nat.exists_eq_add_of_le (show 1≤u by omega)
    obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le hv
    subst u v; nlinarith [Nat.zero_le (i*j)]
  have hi := Nat.mul_le_mul_left (c*c) hs
  nlinarith [congrArg (· * c) he]

private theorem leaf_small {a b c p q r : ℕ} (h : IsNontrivialHT a b c)
    (k : IsNontrivialHT p q r) (eq : a*b*c=p*q*r) (hm : c*(c-1)∈[p,q,r])
    (hc : 3≤c) : c≤8 → False := by
  intro hlo
  have hPu := leaf_upper h
  have hbound : c*(c+1)≤72 := by nlinarith [Nat.mul_le_mul hlo (show c+1≤9 by omega)]
  have hn : a*b*c<72^2 := by nlinarith [Nat.mul_self_le_mul_self hbound]
  have hr : r<18 := by
    by_contra! hr
    obtain ⟨_,hrq,hqp⟩ := bounds k
    have hprod := Nat.mul_le_mul (Nat.mul_le_mul (show 18≤p by omega) (show 18≤q by omega)) hr
    omega
  have parameters {A B C : ℕ} (hh : IsNontrivialHT A B C) :
      ∃ v : ℕ, 1≤v ∧ v<C ∧ v∣C^2-1 ∧ A=C+(C^2-1)/v ∧ B=C+v := by
    obtain ⟨_,u,v,hv,hvu,rfl,rfl,hut⟩ := factor_param.mp hh
    have hcv : v<C := by
      by_contra! hg
      nlinarith [Nat.mul_le_mul (show C≤u by omega) hg]
    have he : C^2-1=u*v := by omega
    exact ⟨v,hv,hcv,⟨u,by rw [he,mul_comm]⟩,by rw [he,Nat.mul_div_cancel _ (by omega)],rfl⟩
  obtain ⟨v,v1,vc,dv,rfl,rfl⟩ := parameters h
  obtain ⟨w,w1,wr,dw,rfl,rfl⟩ := parameters k
  have cert : ∀ C V : Fin 9, 3≤C.val → 1≤V.val → V.val<C.val → V.val∣C.val^2-1 →
      ∀ R W : Fin 18, 2≤R.val → 1≤W.val → W.val<R.val → W.val∣R.val^2-1 →
      (C.val+(C.val^2-1)/V.val)*(C.val+V.val)*C.val=
      (R.val+(R.val^2-1)/W.val)*(R.val+W.val)*R.val →
      C.val*(C.val-1)∉[R.val+(R.val^2-1)/W.val,R.val+W.val,R.val] := by decide +kernel
  exact cert ⟨c,by omega⟩ ⟨v,by omega⟩ hc v1 vc dv ⟨r,hr⟩ ⟨w,by omega⟩ (bounds k).1 w1 wr dw eq hm

/-- Entries of distinct triples with the same product cannot properly divide one another. -/
theorem no_proper_cross_dvd {a b c p q r t s : ℕ} (h : IsNontrivialHT a b c)
    (k : IsNontrivialHT p q r) (eq : a*b*c=p*q*r) (ht : t∈[a,b,c])
    (hs : s∈[p,q,r]) (dvd : t∣s) : t=s := by
  obtain ⟨v,rfl⟩ := dvd
  by_contra ne
  obtain ⟨hc,hcb,hba⟩ := bounds h
  obtain ⟨ct,_⟩ := leaf_between h ht
  obtain ⟨rv,hlo⟩ := leaf_between k hs
  have hr := (bounds k).1
  rw [←eq] at hlo
  have hv : 2≤v := by
    by_contra! hv0
    interval_cases v <;> simp_all
  have ht2 : 2≤t := by omega
  have hdiv := leaf_modulus h k eq ht hs ht2 hv
  have hcand : t≤v+1 := by
    rcases hdiv with d|d
    · have := Nat.le_of_dvd (show 0<v-1 by omega) d; omega
    · exact Nat.le_of_dvd (by omega) d
  have hhi := leaf_upper h
  have hcut : t*v<c*(c+1) := by
    by_contra! le
    nlinarith [Nat.mul_self_le_mul_self le]
  have hcenter : t=c := by
    by_contra hn
    have hbad := Nat.mul_le_mul (show c+1≤t by omega) (show c≤v by omega)
    nlinarith
  subst t
  have hv' : v=c-1 := by
    have hlt : v<c+1 := by
      by_contra! hge
      have := Nat.mul_le_mul_left c hge
      omega
    by_contra hn
    obtain rfl : v=c := by omega
    rcases hdiv with d|d
    · have := Nat.le_of_dvd (show 0<v-1 by omega) d; omega
    · have d1 : v∣1 := by simpa using d
      have := Nat.le_of_dvd (by decide : 0<1) d1; omega
  have cs : c=v+1 := by omega
  have hc3 : 3≤c := by omega
  apply leaf_small h k eq (by simpa only [hv'] using hs) hc3
  have htprod : c*v∣a*b*c := by
    rw [eq]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with hp|hq|hr'
    · rw [←hp]; exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    · rw [←hq]; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    · rw [←hr']; exact dvd_mul_left _ _
  have he := h.1.2.2
  obtain ⟨_,α,β,hβ,hα,rfl,rfl,hαβ⟩ := factor_param.mp h
  by_cases hb : β=1
  · subst β
    have hcof : v∣(c+α)*(c+1) := Nat.dvd_of_mul_dvd_mul_left (by omega : 0<c) (by simpa only [Nat.mul_comm c ((c+α)*(c+1))] using htprod)
    have ha' : α=v*v+2*v := by rw [cs] at hαβ; nlinarith
    have hform : (c+α)*(c+1)=v*(v^2+5*v+7)+2 := by rw [cs,ha']; ring
    rw [hform] at hcof
    have hd2 : v∣2 := (Nat.dvd_add_right (dvd_mul_right _ _)).mp hcof
    have := Nat.le_of_dvd (by decide : 0<2) hd2; omega
  · have hsum : 2*(α+β)≤c^2+3 := by
      obtain ⟨i,hi⟩ := Nat.exists_eq_add_of_le (show 2≤α by omega)
      obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le (show 2≤β by omega)
      subst α β; nlinarith [Nat.zero_le (i*j)]
    have hmul : (c*c)*(v*v)<(c*c)*(2*c+α+β) := by nlinarith [congrArg (· * c) he]
    have hl := Nat.lt_of_mul_lt_mul_left hmul
    by_contra! hlarge
    nlinarith [Nat.mul_le_mul_left c (show 9≤c by omega),congrArg (fun t => t*t) cs]

end Hik

namespace Hik

/- Consider the six cyclic edge labels. At label m the signed vertex
congruences give m ∣ a − s b, with adjacent labels a and b and s = ±1.
A largest label therefore has s = −1 and m = a+b. Erasing it preserves
the congruences at both neighboring labels. Two nonadjacent labels with
s = 1 can never be removed. Once the last interior label on each of the
two arcs between them is removed, those two different labels equal the
same endpoint sum. In the finite cases below, the digits in each local
lemma name specify the retained vertices in cyclic order, and w0,w1
record that endpoint sum after their respective arcs are emptied. -/

private theorem cycle_peak {a m b s : ℤ} (ha : 0<a) (hb : 0<b) (ham : a < m)
    (hbm : b < m) (hne : a≠b) (hs : s=1 ∨ s=-1) (hd : m∣a-s*b) :
    s=-1 ∧ m=a+b := by
  rcases hs with rfl|rfl
  · have ht : |a-b| < m := abs_lt.mpr ⟨by omega,by omega⟩
    have h := Int.eq_zero_of_abs_lt_dvd (show m∣a-b by simpa using hd) ht
    omega
  · have h : m ∣ a+b := by simpa using hd
    obtain ⟨v,hv⟩ := h
    constructor
    · rfl
    · have hm : 0 < m := by omega
      have hpos : 0<v := by by_contra! e; nlinarith [mul_nonpos_of_nonneg_of_nonpos hm.le e]
      have hsmall : v<2 := by by_contra! e; nlinarith [mul_le_mul_of_nonneg_left e hm.le]
      rw [show v=1 by omega,mul_one] at hv
      exact hv.symm

private theorem cycle_drop_right {v a b m s : ℤ} (he : m=v+b) (hd : v∣a-s*m) :
    v∣a-s*b := by
  subst m
  obtain ⟨k,h⟩ := hd
  exact ⟨k+s,by linear_combination h⟩

private theorem cycle_drop_left {v a b m s : ℤ} (he : m=a+v) (hd : v∣m-s*b) :
    v∣a-s*b := by
  subst m
  obtain ⟨k,h⟩ := hd
  exact ⟨k-1,by linear_combination h⟩

set_option maxHeartbeats 8500000 in
/-- Two difference-type vertices separated by 2 edges are impossible. -/
private theorem cycle_two_2 (x s : Fin 6 → ℤ) (pos : ∀ i, 0 < x i)
    (inj : Function.Injective x) (sign : ∀ i, s i=1 ∨ s i=-1)
    (stable0 : s 0=1) (stable1 : s 2=1)
    (h : ∀ i, x i∣x (i-1)-s i*x (i+1)) : False := by
  classical
  have s02 (w0 : x 1=x 0+x 2) (w1 : x 3=x 0+x 2 ∨ x 4=x 0+x 2 ∨ x 5=x 0+x 2) : False := by
    have w01 := w0
    rcases w1 with w13|w14|w15
    · exact (by decide : (1:Fin 6) ≠ 3) (inj (w01.trans w13.symm))
    · exact (by decide : (1:Fin 6) ≠ 4) (inj (w01.trans w14.symm))
    · exact (by decide : (1:Fin 6) ≠ 5) (inj (w01.trans w15.symm))
  have s012 (w1 : x 3=x 0+x 2 ∨ x 4=x 0+x 2 ∨ x 5=x 0+x 2)
      (h0 : x 0∣x 2-s 0*x 1)
      (h1 : x 1∣x 0-s 1*x 2)
      (h2 : x 2∣x 1-s 2*x 0) : False := by
    let T : Finset (Fin 6) := {0,1,2}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 1) (peak 2 (by decide) (by decide)) (peak 1 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 2) (peak 0 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 1) h1
      exact s02 he w1
    · obtain ⟨hs,he⟩ := cycle_peak (pos 1) (pos 0) (peak 1 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
  have s023 (w0 : x 1=x 0+x 2)
      (h0 : x 0∣x 3-s 0*x 2)
      (h2 : x 2∣x 0-s 2*x 3)
      (h3 : x 3∣x 2-s 3*x 0) : False := by
    let T : Finset (Fin 6) := {0,2,3}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 2) (peak 3 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 3) (peak 0 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 0) (peak 2 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact s02 w0 (Or.inl (he.trans (add_comm _ _)))
  have s024 (w0 : x 1=x 0+x 2)
      (h0 : x 0∣x 4-s 0*x 2)
      (h2 : x 2∣x 0-s 2*x 4)
      (h4 : x 4∣x 2-s 4*x 0) : False := by
    let T : Finset (Fin 6) := {0,2,4}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 4) (pos 2) (peak 4 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 4) (peak 0 (by decide) (by decide)) (peak 4 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 0) (peak 2 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 4) h4
      exact s02 w0 (Or.inr (Or.inl (he.trans (add_comm _ _))))
  have s025 (w0 : x 1=x 0+x 2)
      (h0 : x 0∣x 5-s 0*x 2)
      (h2 : x 2∣x 0-s 2*x 5)
      (h5 : x 5∣x 2-s 5*x 0) : False := by
    let T : Finset (Fin 6) := {0,2,5}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 5) (pos 2) (peak 5 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 5) (peak 0 (by decide) (by decide)) (peak 5 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 0) (peak 2 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 5) h5
      exact s02 w0 (Or.inr (Or.inr (he.trans (add_comm _ _))))
  have s0123
      (h0 : x 0∣x 3-s 0*x 1)
      (h1 : x 1∣x 0-s 1*x 2)
      (h2 : x 2∣x 1-s 2*x 3)
      (h3 : x 3∣x 2-s 3*x 0) : False := by
    let T : Finset (Fin 6) := {0,1,2,3}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 1) (peak 3 (by decide) (by decide)) (peak 1 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 2) (peak 0 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 1) h1
      exact s023 he (cycle_drop_right he h0) (cycle_drop_left he h2) h3
    · obtain ⟨hs,he⟩ := cycle_peak (pos 1) (pos 3) (peak 1 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 0) (peak 2 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact s012 (Or.inl (he.trans (add_comm _ _))) (cycle_drop_left he h0) h1 (cycle_drop_right he h2)
  have s0124
      (h0 : x 0∣x 4-s 0*x 1)
      (h1 : x 1∣x 0-s 1*x 2)
      (h2 : x 2∣x 1-s 2*x 4)
      (h4 : x 4∣x 2-s 4*x 0) : False := by
    let T : Finset (Fin 6) := {0,1,2,4}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 4) (pos 1) (peak 4 (by decide) (by decide)) (peak 1 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 2) (peak 0 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 1) h1
      exact s024 he (cycle_drop_right he h0) (cycle_drop_left he h2) h4
    · obtain ⟨hs,he⟩ := cycle_peak (pos 1) (pos 4) (peak 1 (by decide) (by decide)) (peak 4 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 0) (peak 2 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 4) h4
      exact s012 (Or.inr (Or.inl (he.trans (add_comm _ _)))) (cycle_drop_left he h0) h1 (cycle_drop_right he h2)
  have s0125
      (h0 : x 0∣x 5-s 0*x 1)
      (h1 : x 1∣x 0-s 1*x 2)
      (h2 : x 2∣x 1-s 2*x 5)
      (h5 : x 5∣x 2-s 5*x 0) : False := by
    let T : Finset (Fin 6) := {0,1,2,5}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 5) (pos 1) (peak 5 (by decide) (by decide)) (peak 1 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 2) (peak 0 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 1) h1
      exact s025 he (cycle_drop_right he h0) (cycle_drop_left he h2) h5
    · obtain ⟨hs,he⟩ := cycle_peak (pos 1) (pos 5) (peak 1 (by decide) (by decide)) (peak 5 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 0) (peak 2 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 5) h5
      exact s012 (Or.inr (Or.inr (he.trans (add_comm _ _)))) (cycle_drop_left he h0) h1 (cycle_drop_right he h2)
  have s0234 (w0 : x 1=x 0+x 2)
      (h0 : x 0∣x 4-s 0*x 2)
      (h2 : x 2∣x 0-s 2*x 3)
      (h3 : x 3∣x 2-s 3*x 4)
      (h4 : x 4∣x 3-s 4*x 0) : False := by
    let T : Finset (Fin 6) := {0,2,3,4}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 4) (pos 2) (peak 4 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 3) (peak 0 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 4) (peak 2 (by decide) (by decide)) (peak 4 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact s024 w0 h0 (cycle_drop_right he h2) (cycle_drop_left he h4)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 0) (peak 3 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 4) h4
      exact s023 w0 (cycle_drop_left he h0) h2 (cycle_drop_right he h3)
  have s0235 (w0 : x 1=x 0+x 2)
      (h0 : x 0∣x 5-s 0*x 2)
      (h2 : x 2∣x 0-s 2*x 3)
      (h3 : x 3∣x 2-s 3*x 5)
      (h5 : x 5∣x 3-s 5*x 0) : False := by
    let T : Finset (Fin 6) := {0,2,3,5}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 5) (pos 2) (peak 5 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 3) (peak 0 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 5) (peak 2 (by decide) (by decide)) (peak 5 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact s025 w0 h0 (cycle_drop_right he h2) (cycle_drop_left he h5)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 0) (peak 3 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 5) h5
      exact s023 w0 (cycle_drop_left he h0) h2 (cycle_drop_right he h3)
  have s0245 (w0 : x 1=x 0+x 2)
      (h0 : x 0∣x 5-s 0*x 2)
      (h2 : x 2∣x 0-s 2*x 4)
      (h4 : x 4∣x 2-s 4*x 5)
      (h5 : x 5∣x 4-s 5*x 0) : False := by
    let T : Finset (Fin 6) := {0,2,4,5}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 5) (pos 2) (peak 5 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 4) (peak 0 (by decide) (by decide)) (peak 4 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 5) (peak 2 (by decide) (by decide)) (peak 5 (by decide) (by decide)) (inj.ne (by decide)) (sign 4) h4
      exact s025 w0 h0 (cycle_drop_right he h2) (cycle_drop_left he h5)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 4) (pos 0) (peak 4 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 5) h5
      exact s024 w0 (cycle_drop_left he h0) h2 (cycle_drop_right he h4)
  have s01234
      (h0 : x 0∣x 4-s 0*x 1)
      (h1 : x 1∣x 0-s 1*x 2)
      (h2 : x 2∣x 1-s 2*x 3)
      (h3 : x 3∣x 2-s 3*x 4)
      (h4 : x 4∣x 3-s 4*x 0) : False := by
    let T : Finset (Fin 6) := {0,1,2,3,4}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 4) (pos 1) (peak 4 (by decide) (by decide)) (peak 1 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 2) (peak 0 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 1) h1
      exact s0234 he (cycle_drop_right he h0) (cycle_drop_left he h2) h3 h4
    · obtain ⟨hs,he⟩ := cycle_peak (pos 1) (pos 3) (peak 1 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 4) (peak 2 (by decide) (by decide)) (peak 4 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact s0124 h0 h1 (cycle_drop_right he h2) (cycle_drop_left he h4)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 0) (peak 3 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 4) h4
      exact s0123 (cycle_drop_left he h0) h1 h2 (cycle_drop_right he h3)
  have s01235
      (h0 : x 0∣x 5-s 0*x 1)
      (h1 : x 1∣x 0-s 1*x 2)
      (h2 : x 2∣x 1-s 2*x 3)
      (h3 : x 3∣x 2-s 3*x 5)
      (h5 : x 5∣x 3-s 5*x 0) : False := by
    let T : Finset (Fin 6) := {0,1,2,3,5}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 5) (pos 1) (peak 5 (by decide) (by decide)) (peak 1 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 2) (peak 0 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 1) h1
      exact s0235 he (cycle_drop_right he h0) (cycle_drop_left he h2) h3 h5
    · obtain ⟨hs,he⟩ := cycle_peak (pos 1) (pos 3) (peak 1 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 5) (peak 2 (by decide) (by decide)) (peak 5 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact s0125 h0 h1 (cycle_drop_right he h2) (cycle_drop_left he h5)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 0) (peak 3 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 5) h5
      exact s0123 (cycle_drop_left he h0) h1 h2 (cycle_drop_right he h3)
  have s01245
      (h0 : x 0∣x 5-s 0*x 1)
      (h1 : x 1∣x 0-s 1*x 2)
      (h2 : x 2∣x 1-s 2*x 4)
      (h4 : x 4∣x 2-s 4*x 5)
      (h5 : x 5∣x 4-s 5*x 0) : False := by
    let T : Finset (Fin 6) := {0,1,2,4,5}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 5) (pos 1) (peak 5 (by decide) (by decide)) (peak 1 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 2) (peak 0 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 1) h1
      exact s0245 he (cycle_drop_right he h0) (cycle_drop_left he h2) h4 h5
    · obtain ⟨hs,he⟩ := cycle_peak (pos 1) (pos 4) (peak 1 (by decide) (by decide)) (peak 4 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 5) (peak 2 (by decide) (by decide)) (peak 5 (by decide) (by decide)) (inj.ne (by decide)) (sign 4) h4
      exact s0125 h0 h1 (cycle_drop_right he h2) (cycle_drop_left he h5)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 4) (pos 0) (peak 4 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 5) h5
      exact s0124 (cycle_drop_left he h0) h1 h2 (cycle_drop_right he h4)
  have s02345 (w0 : x 1=x 0+x 2)
      (h0 : x 0∣x 5-s 0*x 2)
      (h2 : x 2∣x 0-s 2*x 3)
      (h3 : x 3∣x 2-s 3*x 4)
      (h4 : x 4∣x 3-s 4*x 5)
      (h5 : x 5∣x 4-s 5*x 0) : False := by
    let T : Finset (Fin 6) := {0,2,3,4,5}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 5) (pos 2) (peak 5 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 3) (peak 0 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 4) (peak 2 (by decide) (by decide)) (peak 4 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact s0245 w0 h0 (cycle_drop_right he h2) (cycle_drop_left he h4) h5
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 5) (peak 3 (by decide) (by decide)) (peak 5 (by decide) (by decide)) (inj.ne (by decide)) (sign 4) h4
      exact s0235 w0 h0 h2 (cycle_drop_right he h3) (cycle_drop_left he h5)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 4) (pos 0) (peak 4 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 5) h5
      exact s0234 w0 (cycle_drop_left he h0) h2 h3 (cycle_drop_right he h4)
  have s012345
      (h0 : x 0∣x 5-s 0*x 1)
      (h1 : x 1∣x 0-s 1*x 2)
      (h2 : x 2∣x 1-s 2*x 3)
      (h3 : x 3∣x 2-s 3*x 4)
      (h4 : x 4∣x 3-s 4*x 5)
      (h5 : x 5∣x 4-s 5*x 0) : False := by
    let T : Finset (Fin 6) := {0,1,2,3,4,5}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 5) (pos 1) (peak 5 (by decide) (by decide)) (peak 1 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 2) (peak 0 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 1) h1
      exact s02345 he (cycle_drop_right he h0) (cycle_drop_left he h2) h3 h4 h5
    · obtain ⟨hs,he⟩ := cycle_peak (pos 1) (pos 3) (peak 1 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 4) (peak 2 (by decide) (by decide)) (peak 4 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact s01245 h0 h1 (cycle_drop_right he h2) (cycle_drop_left he h4) h5
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 5) (peak 3 (by decide) (by decide)) (peak 5 (by decide) (by decide)) (inj.ne (by decide)) (sign 4) h4
      exact s01235 h0 h1 h2 (cycle_drop_right he h3) (cycle_drop_left he h5)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 4) (pos 0) (peak 4 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 5) h5
      exact s01234 (cycle_drop_left he h0) h1 h2 h3 (cycle_drop_right he h4)
  exact s012345 (h 0) (h 1) (h 2) (h 3) (h 4) (h 5)

set_option maxHeartbeats 8500000 in
/-- Two difference-type vertices separated by 3 edges are impossible. -/
private theorem cycle_two_3 (x s : Fin 6 → ℤ) (pos : ∀ i, 0 < x i)
    (inj : Function.Injective x) (sign : ∀ i, s i=1 ∨ s i=-1)
    (stable0 : s 0=1) (stable1 : s 3=1)
    (h : ∀ i, x i∣x (i-1)-s i*x (i+1)) : False := by
  classical
  have s03 (w0 : x 1=x 0+x 3 ∨ x 2=x 0+x 3) (w1 : x 4=x 0+x 3 ∨ x 5=x 0+x 3) : False := by
    rcases w0 with w01|w02
    all_goals rcases w1 with w14|w15
    · exact (by decide : (1:Fin 6) ≠ 4) (inj (w01.trans w14.symm))
    · exact (by decide : (1:Fin 6) ≠ 5) (inj (w01.trans w15.symm))
    · exact (by decide : (2:Fin 6) ≠ 4) (inj (w02.trans w14.symm))
    · exact (by decide : (2:Fin 6) ≠ 5) (inj (w02.trans w15.symm))
  have s013 (w1 : x 4=x 0+x 3 ∨ x 5=x 0+x 3)
      (h0 : x 0∣x 3-s 0*x 1)
      (h1 : x 1∣x 0-s 1*x 3)
      (h3 : x 3∣x 1-s 3*x 0) : False := by
    let T : Finset (Fin 6) := {0,1,3}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 1) (peak 3 (by decide) (by decide)) (peak 1 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 3) (peak 0 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 1) h1
      exact s03 (Or.inl he) w1
    · obtain ⟨hs,he⟩ := cycle_peak (pos 1) (pos 0) (peak 1 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
  have s023 (w1 : x 4=x 0+x 3 ∨ x 5=x 0+x 3)
      (h0 : x 0∣x 3-s 0*x 2)
      (h2 : x 2∣x 0-s 2*x 3)
      (h3 : x 3∣x 2-s 3*x 0) : False := by
    let T : Finset (Fin 6) := {0,2,3}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 2) (peak 3 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 3) (peak 0 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact s03 (Or.inr he) w1
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 0) (peak 2 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
  have s034 (w0 : x 1=x 0+x 3 ∨ x 2=x 0+x 3)
      (h0 : x 0∣x 4-s 0*x 3)
      (h3 : x 3∣x 0-s 3*x 4)
      (h4 : x 4∣x 3-s 4*x 0) : False := by
    let T : Finset (Fin 6) := {0,3,4}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 4) (pos 3) (peak 4 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 4) (peak 0 (by decide) (by decide)) (peak 4 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 0) (peak 3 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 4) h4
      exact s03 w0 (Or.inl (he.trans (add_comm _ _)))
  have s035 (w0 : x 1=x 0+x 3 ∨ x 2=x 0+x 3)
      (h0 : x 0∣x 5-s 0*x 3)
      (h3 : x 3∣x 0-s 3*x 5)
      (h5 : x 5∣x 3-s 5*x 0) : False := by
    let T : Finset (Fin 6) := {0,3,5}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 5) (pos 3) (peak 5 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 5) (peak 0 (by decide) (by decide)) (peak 5 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 0) (peak 3 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 5) h5
      exact s03 w0 (Or.inr (he.trans (add_comm _ _)))
  have s0123 (w1 : x 4=x 0+x 3 ∨ x 5=x 0+x 3)
      (h0 : x 0∣x 3-s 0*x 1)
      (h1 : x 1∣x 0-s 1*x 2)
      (h2 : x 2∣x 1-s 2*x 3)
      (h3 : x 3∣x 2-s 3*x 0) : False := by
    let T : Finset (Fin 6) := {0,1,2,3}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 1) (peak 3 (by decide) (by decide)) (peak 1 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 2) (peak 0 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 1) h1
      exact s023 w1 (cycle_drop_right he h0) (cycle_drop_left he h2) h3
    · obtain ⟨hs,he⟩ := cycle_peak (pos 1) (pos 3) (peak 1 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact s013 w1 h0 (cycle_drop_right he h1) (cycle_drop_left he h3)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 0) (peak 2 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
  have s0134
      (h0 : x 0∣x 4-s 0*x 1)
      (h1 : x 1∣x 0-s 1*x 3)
      (h3 : x 3∣x 1-s 3*x 4)
      (h4 : x 4∣x 3-s 4*x 0) : False := by
    let T : Finset (Fin 6) := {0,1,3,4}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 4) (pos 1) (peak 4 (by decide) (by decide)) (peak 1 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 3) (peak 0 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 1) h1
      exact s034 (Or.inl he) (cycle_drop_right he h0) (cycle_drop_left he h3) h4
    · obtain ⟨hs,he⟩ := cycle_peak (pos 1) (pos 4) (peak 1 (by decide) (by decide)) (peak 4 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 0) (peak 3 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 4) h4
      exact s013 (Or.inl (he.trans (add_comm _ _))) (cycle_drop_left he h0) h1 (cycle_drop_right he h3)
  have s0135
      (h0 : x 0∣x 5-s 0*x 1)
      (h1 : x 1∣x 0-s 1*x 3)
      (h3 : x 3∣x 1-s 3*x 5)
      (h5 : x 5∣x 3-s 5*x 0) : False := by
    let T : Finset (Fin 6) := {0,1,3,5}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 5) (pos 1) (peak 5 (by decide) (by decide)) (peak 1 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 3) (peak 0 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 1) h1
      exact s035 (Or.inl he) (cycle_drop_right he h0) (cycle_drop_left he h3) h5
    · obtain ⟨hs,he⟩ := cycle_peak (pos 1) (pos 5) (peak 1 (by decide) (by decide)) (peak 5 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 0) (peak 3 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 5) h5
      exact s013 (Or.inr (he.trans (add_comm _ _))) (cycle_drop_left he h0) h1 (cycle_drop_right he h3)
  have s0234
      (h0 : x 0∣x 4-s 0*x 2)
      (h2 : x 2∣x 0-s 2*x 3)
      (h3 : x 3∣x 2-s 3*x 4)
      (h4 : x 4∣x 3-s 4*x 0) : False := by
    let T : Finset (Fin 6) := {0,2,3,4}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 4) (pos 2) (peak 4 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 3) (peak 0 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact s034 (Or.inr he) (cycle_drop_right he h0) (cycle_drop_left he h3) h4
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 4) (peak 2 (by decide) (by decide)) (peak 4 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 0) (peak 3 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 4) h4
      exact s023 (Or.inl (he.trans (add_comm _ _))) (cycle_drop_left he h0) h2 (cycle_drop_right he h3)
  have s0235
      (h0 : x 0∣x 5-s 0*x 2)
      (h2 : x 2∣x 0-s 2*x 3)
      (h3 : x 3∣x 2-s 3*x 5)
      (h5 : x 5∣x 3-s 5*x 0) : False := by
    let T : Finset (Fin 6) := {0,2,3,5}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 5) (pos 2) (peak 5 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 3) (peak 0 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact s035 (Or.inr he) (cycle_drop_right he h0) (cycle_drop_left he h3) h5
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 5) (peak 2 (by decide) (by decide)) (peak 5 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 0) (peak 3 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 5) h5
      exact s023 (Or.inr (he.trans (add_comm _ _))) (cycle_drop_left he h0) h2 (cycle_drop_right he h3)
  have s0345 (w0 : x 1=x 0+x 3 ∨ x 2=x 0+x 3)
      (h0 : x 0∣x 5-s 0*x 3)
      (h3 : x 3∣x 0-s 3*x 4)
      (h4 : x 4∣x 3-s 4*x 5)
      (h5 : x 5∣x 4-s 5*x 0) : False := by
    let T : Finset (Fin 6) := {0,3,4,5}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 5) (pos 3) (peak 5 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 4) (peak 0 (by decide) (by decide)) (peak 4 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 5) (peak 3 (by decide) (by decide)) (peak 5 (by decide) (by decide)) (inj.ne (by decide)) (sign 4) h4
      exact s035 w0 h0 (cycle_drop_right he h3) (cycle_drop_left he h5)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 4) (pos 0) (peak 4 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 5) h5
      exact s034 w0 (cycle_drop_left he h0) h3 (cycle_drop_right he h4)
  have s01234
      (h0 : x 0∣x 4-s 0*x 1)
      (h1 : x 1∣x 0-s 1*x 2)
      (h2 : x 2∣x 1-s 2*x 3)
      (h3 : x 3∣x 2-s 3*x 4)
      (h4 : x 4∣x 3-s 4*x 0) : False := by
    let T : Finset (Fin 6) := {0,1,2,3,4}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 4) (pos 1) (peak 4 (by decide) (by decide)) (peak 1 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 2) (peak 0 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 1) h1
      exact s0234 (cycle_drop_right he h0) (cycle_drop_left he h2) h3 h4
    · obtain ⟨hs,he⟩ := cycle_peak (pos 1) (pos 3) (peak 1 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact s0134 h0 (cycle_drop_right he h1) (cycle_drop_left he h3) h4
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 4) (peak 2 (by decide) (by decide)) (peak 4 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 0) (peak 3 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 4) h4
      exact s0123 (Or.inl (he.trans (add_comm _ _))) (cycle_drop_left he h0) h1 h2 (cycle_drop_right he h3)
  have s01235
      (h0 : x 0∣x 5-s 0*x 1)
      (h1 : x 1∣x 0-s 1*x 2)
      (h2 : x 2∣x 1-s 2*x 3)
      (h3 : x 3∣x 2-s 3*x 5)
      (h5 : x 5∣x 3-s 5*x 0) : False := by
    let T : Finset (Fin 6) := {0,1,2,3,5}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 5) (pos 1) (peak 5 (by decide) (by decide)) (peak 1 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 2) (peak 0 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 1) h1
      exact s0235 (cycle_drop_right he h0) (cycle_drop_left he h2) h3 h5
    · obtain ⟨hs,he⟩ := cycle_peak (pos 1) (pos 3) (peak 1 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact s0135 h0 (cycle_drop_right he h1) (cycle_drop_left he h3) h5
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 5) (peak 2 (by decide) (by decide)) (peak 5 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 0) (peak 3 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 5) h5
      exact s0123 (Or.inr (he.trans (add_comm _ _))) (cycle_drop_left he h0) h1 h2 (cycle_drop_right he h3)
  have s01345
      (h0 : x 0∣x 5-s 0*x 1)
      (h1 : x 1∣x 0-s 1*x 3)
      (h3 : x 3∣x 1-s 3*x 4)
      (h4 : x 4∣x 3-s 4*x 5)
      (h5 : x 5∣x 4-s 5*x 0) : False := by
    let T : Finset (Fin 6) := {0,1,3,4,5}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 5) (pos 1) (peak 5 (by decide) (by decide)) (peak 1 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 3) (peak 0 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 1) h1
      exact s0345 (Or.inl he) (cycle_drop_right he h0) (cycle_drop_left he h3) h4 h5
    · obtain ⟨hs,he⟩ := cycle_peak (pos 1) (pos 4) (peak 1 (by decide) (by decide)) (peak 4 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 5) (peak 3 (by decide) (by decide)) (peak 5 (by decide) (by decide)) (inj.ne (by decide)) (sign 4) h4
      exact s0135 h0 h1 (cycle_drop_right he h3) (cycle_drop_left he h5)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 4) (pos 0) (peak 4 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 5) h5
      exact s0134 (cycle_drop_left he h0) h1 h3 (cycle_drop_right he h4)
  have s02345
      (h0 : x 0∣x 5-s 0*x 2)
      (h2 : x 2∣x 0-s 2*x 3)
      (h3 : x 3∣x 2-s 3*x 4)
      (h4 : x 4∣x 3-s 4*x 5)
      (h5 : x 5∣x 4-s 5*x 0) : False := by
    let T : Finset (Fin 6) := {0,2,3,4,5}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 5) (pos 2) (peak 5 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 3) (peak 0 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact s0345 (Or.inr he) (cycle_drop_right he h0) (cycle_drop_left he h3) h4 h5
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 4) (peak 2 (by decide) (by decide)) (peak 4 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 5) (peak 3 (by decide) (by decide)) (peak 5 (by decide) (by decide)) (inj.ne (by decide)) (sign 4) h4
      exact s0235 h0 h2 (cycle_drop_right he h3) (cycle_drop_left he h5)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 4) (pos 0) (peak 4 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 5) h5
      exact s0234 (cycle_drop_left he h0) h2 h3 (cycle_drop_right he h4)
  have s012345
      (h0 : x 0∣x 5-s 0*x 1)
      (h1 : x 1∣x 0-s 1*x 2)
      (h2 : x 2∣x 1-s 2*x 3)
      (h3 : x 3∣x 2-s 3*x 4)
      (h4 : x 4∣x 3-s 4*x 5)
      (h5 : x 5∣x 4-s 5*x 0) : False := by
    let T : Finset (Fin 6) := {0,1,2,3,4,5}
    obtain ⟨i,hi,large⟩ := Finset.exists_max_image T x (by decide)
    have peak (j : Fin 6) (hj : j∈T) (hd : j≠i) : x j < x i := lt_of_le_of_ne (large j hj) (inj.ne hd)
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    · obtain ⟨hs,he⟩ := cycle_peak (pos 5) (pos 1) (peak 5 (by decide) (by decide)) (peak 1 (by decide) (by decide)) (inj.ne (by decide)) (sign 0) h0
      exact (by decide : (1:ℤ)≠ -1) (stable0.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 0) (pos 2) (peak 0 (by decide) (by decide)) (peak 2 (by decide) (by decide)) (inj.ne (by decide)) (sign 1) h1
      exact s02345 (cycle_drop_right he h0) (cycle_drop_left he h2) h3 h4 h5
    · obtain ⟨hs,he⟩ := cycle_peak (pos 1) (pos 3) (peak 1 (by decide) (by decide)) (peak 3 (by decide) (by decide)) (inj.ne (by decide)) (sign 2) h2
      exact s01345 h0 (cycle_drop_right he h1) (cycle_drop_left he h3) h4 h5
    · obtain ⟨hs,he⟩ := cycle_peak (pos 2) (pos 4) (peak 2 (by decide) (by decide)) (peak 4 (by decide) (by decide)) (inj.ne (by decide)) (sign 3) h3
      exact (by decide : (1:ℤ)≠ -1) (stable1.symm.trans hs)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 3) (pos 5) (peak 3 (by decide) (by decide)) (peak 5 (by decide) (by decide)) (inj.ne (by decide)) (sign 4) h4
      exact s01235 h0 h1 h2 (cycle_drop_right he h3) (cycle_drop_left he h5)
    · obtain ⟨hs,he⟩ := cycle_peak (pos 4) (pos 0) (peak 4 (by decide) (by decide)) (peak 0 (by decide) (by decide)) (inj.ne (by decide)) (sign 5) h5
      exact s01234 (cycle_drop_left he h0) h1 h2 h3 (cycle_drop_right he h4)
  exact s012345 (h 0) (h 1) (h 2) (h 3) (h 4) (h 5)

open OMA.S_mo_161095



private theorem cycle_vertex_sign {a b c : ℕ} (h : IsNontrivialHT a b c)
    (v : Fin 3 → ℕ) (perm : [v 0,v 1,v 2].Perm [a,b,c]) :
    ∃ i : Fin 3, ∀ j : Fin 3, (v j:ℤ)^2 ∣ (a*b*c:ℕ)-
      (if j=i then (-1:ℤ) else 1)*(v j:ℤ) := by
  obtain ⟨da,db,dc⟩ := signed_squares h
  obtain ⟨_,hcb,hba⟩ := bounds h
  have hac : a≠c := by omega
  have hbc : b≠c := by omega
  have say (j : Fin 3) : (v j:ℤ)^2 ∣ (a*b*c:ℕ)-
      (if v j=c then (-1:ℤ) else 1)*(v j:ℤ) := by
    have hh : v j ∈ [a,b,c] := perm.mem_iff.mp (by fin_cases j <;> simp)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
    rcases hh with he|he|he
    · simpa only [he,if_neg hac,one_mul] using da
    · simpa only [he,if_neg hbc,one_mul] using db
    · simpa [he] using dc
  have cnt := perm.count_eq c
  have exactly : (v 0=c ∧ v 1≠c ∧ v 2≠c) ∨ (v 0≠c ∧ v 1=c ∧ v 2≠c) ∨
      (v 0≠c ∧ v 1≠c ∧ v 2=c) := by
    by_cases h0 : v 0=c <;> by_cases h1 : v 1=c <;> by_cases h2 : v 2=c <;>
      simp [h0,h1,h2,hac,hbc] at cnt ⊢
  obtain h0|h1|h2 := exactly
  · rcases h0 with ⟨u,v',w⟩
    exact ⟨0,fun j => by have hj := say j; fin_cases j <;> simpa [u,v',w] using hj⟩
  · rcases h1 with ⟨u,v',w⟩
    exact ⟨1,fun j => by have hj := say j; fin_cases j <;> simpa [u,v',w] using hj⟩
  · rcases h2 with ⟨u,v',w⟩
    exact ⟨2,fun j => by have hj := say j; fin_cases j <;> simpa [u,v',w] using hj⟩

/-- A six-cycle in the common factor table of two nontrivial triples with
equal product is impossible. Edges are listed in cyclic order. -/
theorem no_cycle_triples {a b c p q r x0 x1 x2 x3 x4 x5 : ℕ}
    (h : IsNontrivialHT a b c) (k : IsNontrivialHT p q r)
    (eqP : a*b*c=p*q*r)
    (pos : ∀ i : Fin 6, 1 < ![x0,x1,x2,x3,x4,x5] i)
    (inj : Function.Injective (![x0,x1,x2,x3,x4,x5] : Fin 6 → ℕ))
    (left : [x0*x1,x2*x3,x4*x5].Perm [a,b,c])
    (right : [x1*x2,x3*x4,x5*x0].Perm [p,q,r]) : False := by
  let x (i : Fin 6) : ℤ := ![x0,x1,x2,x3,x4,x5] i
  let P : ℤ := (a*b*c:ℕ)
  obtain ⟨l,hl⟩ := cycle_vertex_sign h ![x0*x1,x2*x3,x4*x5] left
  obtain ⟨r',hr⟩ := cycle_vertex_sign k ![x1*x2,x3*x4,x5*x0] right
  let g (j i : Fin 3) : ℤ := if i=j then -1 else 1
  let v := ![g l 0,g r' 0,g l 1,g r' 1,g l 2,g r' 2]
  let s (i : Fin 6) := v (i-1)*v i
  have gsign (i : Fin 6) : v i=1 ∨ v i = -1 := by
    fin_cases i <;> simp [v,g] <;> tauto
  have sign (i : Fin 6) : s i=1 ∨ s i = -1 := by
    rcases gsign (i-1) with hj|hj <;> rcases gsign i with hi|hi <;> simp [s,hj,hi]
  have pos' (i : Fin 6) : 0<x i := by dsimp only [x]; exact_mod_cast Nat.zero_lt_of_lt (pos i)
  have inj' : Function.Injective x := by
    intro i j he
    apply inj
    dsimp only [x] at he
    exact_mod_cast he
  have er : (a:ℤ)*b*c=(p:ℤ)*q*r := by exact_mod_cast eqP
  have square (i : Fin 6) : (x i*x (i+1))^2 ∣ P-v i*(x i*x (i+1)) := by
    fin_cases i
    · simpa [x,v,P,g] using hl 0
    · simpa [x,v,P,g,er] using hr 0
    · simpa [x,v,P,g] using hl 1
    · simpa [x,v,P,g,er] using hr 1
    · simpa [x,v,P,g] using hl 2
    · simpa [x,v,P,g,er] using hr 2
  have con (i : Fin 6) : x i ∣ x (i-1)-s i*x (i+1) := by
    have a1 : (x i*x (i-1))^2 ∣ P-v (i-1)*(x i*x (i-1)) := by
      simpa only [sub_add_cancel, mul_comm (x (i-1))] using square (i-1)
    have dc := cross_signed_cell (ne_of_gt (pos' i)) a1 (square i)
    rcases gsign (i-1) with he|he
    · simpa [s,he] using dc
    · have hn := dvd_neg.mpr dc
      rw [he] at hn
      rw [show x (i-1)-s i*x (i+1) = -(-1*x (i-1)-v i*x (i+1)) by dsimp only [s]; rw [he]; ring]
      exact hn
  have sep : ∃ t : Fin 6, s t=1 ∧ (s (t+2)=1 ∨ s (t+3)=1) := by
    dsimp only [s,v,g]
    fin_cases l <;> fin_cases r' <;> decide
  obtain ⟨t,st,st'⟩ := sep
  let X (i : Fin 6) := x (t+i)
  let S (i : Fin 6) := s (t+i)
  have injX : Function.Injective X := fun _ _ he => add_left_cancel (inj' he)
  have con' (i : Fin 6) : X i∣X (i-1)-S i*X (i+1) := by
    simpa only [X,S,add_sub_assoc,add_assoc] using con (t+i)
  rcases st' with h2|h3
  · exact cycle_two_2 X S (fun i=>pos' _) injX (fun i=>sign _) (by simpa [S] using st) h2 con'
  · exact cycle_two_3 X S (fun i=>pos' _) injX (fun i=>sign _) (by simpa [S] using st) h3 con'

end Hik

namespace Hik
open OMA.S_mo_161095 Finset

private theorem same_positive_aux {t u v s r : ℤ} (ht : 0<t) (hu : 0<u) (hr : 0<r)
    (hh : t*(u-v)=u*v-1) (hk : t*(s-r)=s*r-1) (hp : t*(u*v)=t*(s*r)) : v=r := by
  have he := mul_left_cancel₀ ht.ne' hp
  have hd : u-v=s-r := mul_left_cancel₀ ht.ne' (by rw [hh,hk,he])
  have hz : (u+r)*(v-r)=0 := by linear_combination he - r*hd
  rcases mul_eq_zero.mp hz with e|e <;> omega

private theorem mixed_sign_aux {t u v s r : ℤ} (ht : 2<t)
    (hh : t*(u-v)=u*v-1) (hk : t*(s+r)=s*r+1) (hp : t*(u*v)=t*(s*r)) : False := by
  have he := mul_left_cancel₀ (by omega : t≠0) hp
  have hd : t∣2 := ⟨(s+r)-(u-v), by linear_combination hh-hk+he⟩
  have := Int.le_of_dvd (by decide : 0<(2:ℤ)) hd
  omega

/-- An entry, together with the product, determines the entire ordered triple. -/
theorem common_entry {a b c p q r t : ℕ} (h : IsNontrivialHT a b c)
    (k : IsNontrivialHT p q r) (he : a*b*c=p*q*r)
    (hm : t∈[a,b,c]) (hn : t∈[p,q,r]) : (a,b,c)=(p,q,r) := by
  have ha := h.1.2.2
  have hp := k.1.2.2
  obtain ⟨hc,hcb,hba⟩ := bounds h
  obtain ⟨hr,hrq,hqp⟩ := bounds k
  have eqz := he
  zify at ha hp eqz
  have ea : (a:ℤ)*(b-c)=b*c-1 := by linarith only [ha]
  have eb : (b:ℤ)*(a-c)=a*c-1 := by linarith only [ha]
  have ep : (p:ℤ)*(q-r)=q*r-1 := by linarith only [hp]
  have eq : (q:ℤ)*(p-r)=p*r-1 := by linarith only [hp]
  have ec : (c:ℤ)*(a+b)=a*b+1 := by linarith only [ha]
  have er : (r:ℤ)*(p+q)=p*q+1 := by linarith only [hp]
  suffices hh : c=r by subst r; exact same_c h k he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm hn
  rcases hm with e|e|e <;> subst t <;> rcases hn with e|e|e
  all_goals first | exact e | subst_vars
  all_goals first
    | exact_mod_cast same_positive_aux (by omega) (by omega) (by omega) ea ep (by linear_combination eqz)
    | exact_mod_cast same_positive_aux (by omega) (by omega) (by omega) ea eq (by linear_combination eqz)
    | exact_mod_cast same_positive_aux (by omega) (by omega) (by omega) eb ep (by linear_combination eqz)
    | exact_mod_cast same_positive_aux (by omega) (by omega) (by omega) eb eq (by linear_combination eqz)
    | exact (mixed_sign_aux (by omega) ea er (by linear_combination eqz)).elim
    | exact (mixed_sign_aux (by omega) eb er (by linear_combination eqz)).elim
    | exact (mixed_sign_aux (by omega) ep ec (by linear_combination -eqz)).elim
    | exact (mixed_sign_aux (by omega) eq ec (by linear_combination -eqz)).elim

theorem pairwise_entries {a b c : ℕ} (h : IsNontrivialHT a b c) :
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c := by
  have e := h.1.2.2
  have dc := (product_data h).2.2.1
  rw [(product_data h).2.2.2.2] at dc
  obtain ⟨ca,cb⟩ := Nat.coprime_mul_iff_right.mp dc
  refine ⟨?_,ca.symm,cb.symm⟩
  let g := a.gcd b
  have hleft : g∣(a+b)*c := dvd_mul_of_dvd_left (dvd_add (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)) c
  have hright : g∣a*b := dvd_mul_of_dvd_left (Nat.gcd_dvd_left a b) b
  rw [e] at hleft
  exact Nat.dvd_one.mp ((Nat.dvd_add_iff_right hright).mpr hleft)

theorem entry_mem (a b c : ℕ) (i : Fin 3) : ![a,b,c] i ∈ [a,b,c] := by
  fin_cases i <;> simp

theorem entry_coprime {a b c : ℕ} (h : IsNontrivialHT a b c) {i j : Fin 3} (hne : i≠j) :
    (![a,b,c] i).Coprime (![a,b,c] j) := by
  obtain ⟨ab,ac,bc⟩ := pairwise_entries h
  fin_cases i <;> fin_cases j <;> first | exact ab | exact ac | exact bc | exact ab.symm | exact ac.symm | exact bc.symm | exact (hne rfl).elim

theorem entry_dvd (a b c : ℕ) (i : Fin 3) : ![a,b,c] i ∣ a*b*c := by
  fin_cases i <;> simp [dvd_mul_left,dvd_mul_right,dvd_mul_of_dvd_left]

theorem entry_positive {a b c : ℕ} (h : IsNontrivialHT a b c) (i : Fin 3) :
    1 < ![a,b,c] i := by
  obtain ⟨hc,hcb,hba⟩ := bounds h
  fin_cases i <;> simp <;> omega

/-- Each row of the gcd table factors its entry into three coprime pieces. -/
theorem row_gcd_product {p q r x : ℕ} (k : IsNontrivialHT p q r) (hx : x ∣ p*q*r) :
    x.gcd p * x.gcd q * x.gcd r = x := by
  obtain ⟨pq,pr,qr⟩ := pairwise_entries k
  have cg := (Nat.coprime_mul_iff_left.mpr ⟨pr,qr⟩)
  rw [← pq.gcd_mul, ← cg.gcd_mul, Nat.gcd_eq_left hx]

end Hik

open Finset OMA.S_mo_161095

namespace Hik

/-- The row and column degrees of the intersection table are at least two. -/
theorem row_degree {a b c p q r : ℕ} (h : IsNontrivialHT a b c) (k : IsNontrivialHT p q r)
    (hp : a*b*c=p*q*r) (hn : (a,b,c)≠(p,q,r)) (i : Fin 3) :
    2 ≤ (univ.filter (fun j : Fin 3 => 1 < (![a,b,c] i).gcd (![p,q,r] j))).card := by
  let t := ![a,b,c] i
  have ht := entry_positive h i
  have hd := entry_dvd a b c i
  rw [hp] at hd
  have hh := row_gcd_product k hd
  have pos (j : Fin 3) : 0 < t.gcd (![p,q,r] j) := Nat.gcd_pos_of_pos_left _ (by omega : 0<t)
  have neq (j : Fin 3) : ¬t ∣ ![p,q,r] j := by
    intro ha
    have e := no_proper_cross_dvd h k hp (entry_mem a b c i) (entry_mem p q r j) ha
    exact hn (common_entry h k hp (entry_mem a b c i) (e ▸ entry_mem p q r j))
  have n0 := neq 0
  have n1 := neq 1
  have n2 := neq 2
  change ¬t∣p at n0
  change ¬t∣q at n1
  change ¬t∣r at n2
  change t.gcd p * t.gcd q * t.gcd r = t at hh
  have pk := pos 0
  have qk := pos 1
  have rk := pos 2
  change 0<t.gcd p at pk
  change 0<t.gcd q at qk
  change 0<t.gcd r at rk
  have pairs (j k : Fin 3) (hj : 1<t.gcd (![p,q,r] j)) (hk : 1<t.gcd (![p,q,r] k))
      (jk : j≠k) : 2 ≤ (univ.filter (fun s : Fin 3 => 1<t.gcd (![p,q,r] s))).card :=
    one_lt_card.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,hj⟩,k,mem_filter.mpr ⟨mem_univ _,hk⟩,jk⟩
  have d0 : t.gcd q ≠ 1 ∨ t.gcd r ≠ 1 := by
    by_contra! hh1
    rw [hh1.1,hh1.2,mul_one,mul_one] at hh
    exact n0 (hh ▸ Nat.gcd_dvd_right t p)
  have d1 : t.gcd p ≠ 1 ∨ t.gcd r ≠ 1 := by
    by_contra! hh1
    rw [hh1.1,hh1.2,one_mul,mul_one] at hh
    exact n1 (hh ▸ Nat.gcd_dvd_right t q)
  have d2 : t.gcd p ≠ 1 ∨ t.gcd q ≠ 1 := by
    by_contra! hh1
    rw [hh1.1,hh1.2,one_mul,one_mul] at hh
    exact n2 (hh ▸ Nat.gcd_dvd_right t r)
  by_cases xp : 1<t.gcd p <;> by_cases xq : 1<t.gcd q
  · exact pairs 0 1 xp xq (by decide)
  · exact pairs 0 2 xp (by change 1<t.gcd r; omega) (by decide)
  · exact pairs 1 2 xq (by change 1<t.gcd r; omega) (by decide)
  · omega

theorem prime_cells {a b c p q r : ℕ} (h : IsNontrivialHT a b c) (k : IsNontrivialHT p q r) :
    let C (z : Fin 3 × Fin 3) := (![a,b,c] z.1).gcd (![p,q,r] z.2)
    ((univ : Finset (Fin 3 × Fin 3)).filter (fun z => 1<C z)).card ≤ (a*b*c).primeFactors.card := by
  intro C
  apply card_le_card_of_injOn (fun z => (C z).minFac)
  · intro z hz
    have hg := (mem_filter.mp hz).2
    have hd := (Nat.minFac_dvd (C z)).trans (Nat.gcd_dvd_left _ _)
    obtain ⟨hc,hcb,hba⟩ := bounds h
    exact Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), hd.trans (entry_dvd a b c _), (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)).ne'⟩
  · intro z hz w hw eq
    have hg := (mem_filter.mp hz).2
    have hprime := Nat.minFac_prime (by omega : C z ≠ 1)
    have dl := Nat.minFac_dvd (C z)
    have dr := Nat.minFac_dvd (C w)
    change (C z).minFac = (C w).minFac at eq
    rw [←eq] at dr
    apply Prod.ext
    · by_contra ne
      have := Nat.eq_one_of_dvd_coprimes (entry_coprime h ne)
        (dl.trans (Nat.gcd_dvd_left _ _)) (dr.trans (Nat.gcd_dvd_left _ _))
      exact hprime.ne_one this
    · by_contra ne
      have := Nat.eq_one_of_dvd_coprimes (entry_coprime k ne)
        (dl.trans (Nat.gcd_dvd_right _ _)) (dr.trans (Nat.gcd_dvd_right _ _))
      exact hprime.ne_one this

/- Finite classification of 3-by-3 Boolean tables of minimum degree two.
For a six-cell table the rows are already in cycle order. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem table_shapes : ∀ M : Fin 3 → Fin 3 → Bool,
    (∀ i, 2 ≤ (univ.filter (fun j => M i j = true)).card) →
    (∀ j, 2 ≤ (univ.filter (fun i => M i j = true)).card) →
    7 ≤ (univ.filter (fun z : Fin 3 × Fin 3 => M z.1 z.2 = true)).card ∨
    ∃ j k l : Fin 3, j≠k ∧ j≠l ∧ k≠l ∧
      (M 0 j && M 0 k && M 1 k && M 1 l && M 2 l && M 2 j) = true ∧
      (M 0 l || M 1 j || M 2 k) = false := by decide

end Hik

open OMA.S_mo_161095 Finset

namespace Hik

private theorem three_perm : ∀ j k l : Fin 3, j≠k → j≠l → k≠l →
    [j,k,l].Perm [0,1,2] := by decide

private theorem six_injective : ∀ j k l : Fin 3, j≠k → j≠l → k≠l →
    Function.Injective (![(0,j),(0,k),(1,k),(1,l),(2,l),(2,j)] : Fin 6 → Fin 3 × Fin 3) := by decide

theorem cell_unique {a b c p q r : ℕ} (h : IsNontrivialHT a b c) (k : IsNontrivialHT p q r)
    (z w : Fin 3 × Fin 3) (hg : 1 < (![a,b,c] z.1).gcd (![p,q,r] z.2))
    (eq : (![a,b,c] z.1).gcd (![p,q,r] z.2) = (![a,b,c] w.1).gcd (![p,q,r] w.2)) : z=w := by
  apply Prod.ext
  · by_contra ne
    have e := Nat.eq_one_of_dvd_coprimes (entry_coprime h ne) (Nat.gcd_dvd_left (![a,b,c] z.1) (![p,q,r] z.2))
      (by rw [eq]; exact Nat.gcd_dvd_left _ _)
    omega
  · by_contra ne
    have e := Nat.eq_one_of_dvd_coprimes (entry_coprime k ne) (Nat.gcd_dvd_right (![a,b,c] z.1) (![p,q,r] z.2))
      (by rw [eq]; exact Nat.gcd_dvd_right _ _)
    omega

/-- In the sole remaining six-cell pattern the row and column products alternate around a cycle. -/
theorem cycle_or_seven {a b c p q r : ℕ} (h : IsNontrivialHT a b c) (k : IsNontrivialHT p q r)
    (hp : a*b*c=p*q*r) (hn : (a,b,c)≠(p,q,r)) :
    7 ≤ (univ.filter (fun z : Fin 3 × Fin 3 => 1 < (![a,b,c] z.1).gcd (![p,q,r] z.2))).card ∨
    ∃ x0 x1 x2 x3 x4 x5 : ℕ, (∀ i : Fin 6, 1 < ![x0,x1,x2,x3,x4,x5] i) ∧
      Function.Injective (![x0,x1,x2,x3,x4,x5] : Fin 6 → ℕ) ∧
      [x0*x1,x2*x3,x4*x5].Perm [a,b,c] ∧ [x1*x2,x3*x4,x5*x0].Perm [p,q,r] := by
  let R := ![a,b,c]
  let S := ![p,q,r]
  let G (i j : Fin 3) := (R i).gcd (S j)
  let M (i j : Fin 3) := decide (1<G i j)
  have row (i : Fin 3) : 2 ≤ (univ.filter (fun j => M i j = true)).card := by
    simpa only [M,decide_eq_true_eq] using row_degree h k hp hn i
  have col (j : Fin 3) : 2 ≤ (univ.filter (fun i => M i j = true)).card := by
    simpa only [M,G,R,S,decide_eq_true_eq,Nat.gcd_comm] using row_degree k h hp.symm (Ne.symm hn) j
  rcases table_shapes M row col with hh|⟨j,k',l,jk,jl,kl,on,off⟩
  · exact Or.inl (by simpa only [M,decide_eq_true_eq] using hh)
  right
  simp only [Bool.and_eq_true,M,decide_eq_true_eq] at on
  simp only [Bool.or_eq_false_iff,M,decide_eq_false_iff_not] at off
  have pos (i j : Fin 3) : 0<G i j := Nat.gcd_pos_of_pos_left _ (by have := entry_positive h i; dsimp [R]; omega)
  have e0 : G 0 l=1 := by have := pos 0 l; omega
  have e1 : G 1 j=1 := by have := pos 1 j; omega
  have e2 : G 2 k'=1 := by have := pos 2 k'; omega
  have pm := three_perm j k' l jk jl kl
  have rr (i : Fin 3) : G i j * G i k' * G i l = R i := by
    have hh := row_gcd_product k (hp ▸ entry_dvd a b c i)
    have pp := (pm.map (G i)).prod_eq
    simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at pp
    have hi : G i 0 * (G i 1 * G i 2) = R i := by
      change (R i).gcd p * ((R i).gcd q * (R i).gcd r) = R i
      rw [←mul_assoc]
      exact hh
    simpa only [mul_assoc] using pp.trans hi
  have cc (j : Fin 3) : G 0 j * G 1 j * G 2 j = S j := by
    have hh := row_gcd_product h (hp.symm ▸ entry_dvd p q r j)
    change a.gcd (S j) * b.gcd (S j) * c.gcd (S j) = S j
    rw [Nat.gcd_comm a, Nat.gcd_comm b, Nat.gcd_comm c]
    exact hh
  have r0 : R 0 = a := rfl
  have r1 : R 1 = b := rfl
  have r2 : R 2 = c := rfl
  have f0 : G 0 j * G 0 k'=a := by simpa only [e0,mul_one,r0] using rr 0
  have f1 : G 1 k' * G 1 l=b := by simpa only [e1,one_mul,r1] using rr 1
  have f2 : G 2 l * G 2 j=c := by simpa only [e2,mul_one,one_mul,mul_comm,r2] using rr 2
  have c0 : G 0 k' * G 1 k'=S k' := by simpa only [e2,mul_one] using cc k'
  have c1 : G 1 l * G 2 l=S l := by simpa only [e0,one_mul] using cc l
  have c2 : G 2 j * G 0 j=S j := by simpa only [e1,mul_one,one_mul,mul_comm] using cc j
  let ix : Fin 6 → Fin 3 × Fin 3 := ![(0,j),(0,k'),(1,k'),(1,l),(2,l),(2,j)]
  have ixpos (i : Fin 6) : 1<G (ix i).1 (ix i).2 := by
    fin_cases i <;> dsimp [ix] <;> tauto
  refine ⟨G 0 j,G 0 k',G 1 k',G 1 l,G 2 l,G 2 j,?_,?_,?_,?_⟩
  · intro i
    fin_cases i <;> simp <;> tauto
  · intro i i' he
    have lab (n : Fin 6) : ![G 0 j,G 0 k',G 1 k',G 1 l,G 2 l,G 2 j] n =
        G (ix n).1 (ix n).2 := by fin_cases n <;> rfl
    rw [lab i,lab i'] at he
    exact six_injective j k' l jk jl kl (cell_unique h k (ix i) (ix i') (ixpos i) he)
  · rw [f0,f1,f2]
  · rw [c0,c1,c2]
    exact (three_perm k' l j kl jk.symm jl.symm).map S

end Hik

open OMA.S_mo_161095 Finset

namespace Hik

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
set_option synthInstance.maxSize 512 in
private theorem theta_table : ∀ M : Fin 3 → Fin 3 → Bool,
    (∀ i, 2 ≤ (univ.filter (fun j => M i j = true)).card) →
    (∀ j, 2 ≤ (univ.filter (fun i => M i j = true)).card) →
    (univ.filter (fun z : Fin 3 × Fin 3 => M z.1 z.2 = true)).card = 7 →
    ∃ i j k a b c : Fin 3, i≠j ∧ i≠k ∧ j≠k ∧ a≠b ∧ a≠c ∧ b≠c ∧
      (M i a && M i b && M j b && M j a && M i c && M k c && M k a) = true ∧
      (M j c || M k b) = false := by decide

private theorem triple_perm : ∀ u v w : Fin 3, u≠v → u≠w → v≠w →
    [u,v,w].Perm [0,1,2] := by decide

private theorem distinct_theta : ∀ i j k a b c : Fin 3, i≠j → i≠k → j≠k → a≠b → a≠c → b≠c →
    Function.Injective (![(i,a),(i,b),(j,b),(j,a),(i,c),(k,c),(k,a)] : Fin 7 → Fin 3 × Fin 3) := by decide

theorem cell_coprime {a b c p q r : ℕ} (h : IsNontrivialHT a b c) (k : IsNontrivialHT p q r)
    {z w : Fin 3 × Fin 3} (ne : z≠w) :
    ((![a,b,c] z.1).gcd (![p,q,r] z.2)).Coprime ((![a,b,c] w.1).gcd (![p,q,r] w.2)) := by
  by_cases hi : z.1 = w.1
  · have hj : z.2≠w.2 := fun hj => ne (Prod.ext hi hj)
    exact ((entry_coprime k hj).of_dvd_left (Nat.gcd_dvd_right _ _)).of_dvd_right (Nat.gcd_dvd_right _ _)
  · exact ((entry_coprime h hi).of_dvd_left (Nat.gcd_dvd_left _ _)).of_dvd_right (Nat.gcd_dvd_left _ _)

private theorem perm_product {a b c : ℕ} (h : IsNontrivialHT a b c) {t : ℕ} (hd : t∣a*b*c)
    {i j k : Fin 3} (pm : [i,j,k].Perm [0,1,2]) :
    t.gcd (![a,b,c] i) * t.gcd (![a,b,c] j) * t.gcd (![a,b,c] k) = t := by
  have hh := row_gcd_product h hd
  have pp := (pm.map (fun n => t.gcd (![a,b,c] n))).prod_eq
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at pp
  rw [mul_assoc,pp,←mul_assoc]
  exact hh

theorem seven_factor_shape {a b c p q r : ℕ} (h : IsNontrivialHT a b c) (k : IsNontrivialHT p q r)
    (hp : a*b*c=p*q*r) (hn : (a,b,c)≠(p,q,r))
    (h7 : (univ.filter (fun z : Fin 3 × Fin 3 => 1 < (![a,b,c] z.1).gcd (![p,q,r] z.2))).card=7) :
    ∃ t u v w x y z : ℕ, (∀ i : Fin 7, 1 < ![t,u,v,w,x,y,z] i) ∧
      (∀ i j : Fin 7, i≠j → (![t,u,v,w,x,y,z] i).Coprime (![t,u,v,w,x,y,z] j)) ∧
      [t*u*x,v*w,y*z].Perm [a,b,c] ∧ [t*w*z,u*v,x*y].Perm [p,q,r] := by
  let R := ![a,b,c]
  let S := ![p,q,r]
  let G (i j : Fin 3) := (R i).gcd (S j)
  let M (i j : Fin 3) := decide (1<G i j)
  have rows (i : Fin 3) : 2 ≤ (univ.filter (fun j => M i j = true)).card := by
    simpa only [M,decide_eq_true_eq] using row_degree h k hp hn i
  have cols (j : Fin 3) : 2 ≤ (univ.filter (fun i => M i j = true)).card := by
    simpa only [M,G,R,S,decide_eq_true_eq,Nat.gcd_comm] using row_degree k h hp.symm (Ne.symm hn) j
  obtain ⟨i,j,l,f,g,m,ij,il,jl,fg,fm,gm,on,off⟩ := theta_table M rows cols
    (by simpa only [M,decide_eq_true_eq] using h7)
  simp only [Bool.and_eq_true,M,decide_eq_true_eq] at on
  simp only [Bool.or_eq_false_iff,M,decide_eq_false_iff_not] at off
  have pos (i j : Fin 3) : 0<G i j := Nat.gcd_pos_of_pos_left _ (by have := entry_positive h i; dsimp [R]; omega)
  have e1 : G j m=1 := by have := pos j m; omega
  have e2 : G l g=1 := by have := pos l g; omega
  have pi := triple_perm i j l ij il jl
  have pj := triple_perm f g m fg fm gm
  have row (n : Fin 3) : G n f*G n g*G n m=R n := perm_product k (hp ▸ entry_dvd a b c n) pj
  have col (n : Fin 3) : G i n*G j n*G l n=S n := by
    have e := perm_product h (hp.symm ▸ entry_dvd p q r n) pi
    change (R i).gcd (S n) * (R j).gcd (S n) * (R l).gcd (S n) = S n
    rw [Nat.gcd_comm (R i),Nat.gcd_comm (R j),Nat.gcd_comm (R l)]
    exact e
  let ix : Fin 7 → Fin 3 × Fin 3 := ![(i,f),(i,g),(j,g),(j,f),(i,m),(l,m),(l,f)]
  let A := ![G i f,G i g,G j g,G j f,G i m,G l m,G l f]
  have lab (n : Fin 7) : A n=G (ix n).1 (ix n).2 := by fin_cases n <;> rfl
  refine ⟨G i f,G i g,G j g,G j f,G i m,G l m,G l f,?_,?_,?_,?_⟩
  · intro n
    fin_cases n <;> simp <;> tauto
  · intro s n ne
    change (A s).Coprime (A n)
    rw [lab s,lab n]
    exact cell_coprime h k (fun eq => ne (distinct_theta i j l f g m ij il jl fg fm gm eq))
  · have h0 := row i
    have h1 : G j g*G j f=R j := by simpa only [e1,mul_one,one_mul,mul_comm] using row j
    have h2 : G l m*G l f=R l := by simpa only [e2,mul_one,one_mul,mul_comm] using row l
    rw [h0,h1,h2]
    exact pi.map R
  · have h0 := col f
    have h1 : G i g*G j g=S g := by simpa only [e2,mul_one] using col g
    have h2 : G i m*G l m=S m := by simpa only [e1,mul_one] using col m
    rw [h0,h1,h2]
    exact pj.map S

end Hik

open OMA.S_mo_161095 Finset

namespace Hik

theorem seven_cells_of_collision {a b c p q r : ℕ} (h : IsNontrivialHT a b c) (k : IsNontrivialHT p q r)
    (hp : a*b*c=p*q*r) (hn : (a,b,c)≠(p,q,r)) :
    7 ≤ (univ.filter (fun z : Fin 3 × Fin 3 => 1 < (![a,b,c] z.1).gcd (![p,q,r] z.2))).card := by
  rcases cycle_or_seven h k hp hn with ht|⟨x0,x1,x2,x3,x4,x5,pos,inj,lhs,rhs⟩
  · exact ht
  · exact (no_cycle_triples h k hp pos inj lhs rhs).elim

/-- Any product with at most six distinct prime factors determines its triple. -/
theorem six_primes_unique {a b c p q r : ℕ} (h : IsNontrivialHT a b c) (k : IsNontrivialHT p q r)
    (hp : a*b*c=p*q*r) (hs : (a*b*c).primeFactors.card≤6) : (a,b,c)=(p,q,r) := by
  by_contra ne
  have hg := (seven_cells_of_collision h k hp ne).trans (prime_cells h k)
  omega

theorem small_divisor_rep {a b c : ℕ} (h : IsNontrivialHT a b c) :
    ∃ v : ℕ, 0<v ∧ v<c ∧ v∣c^2-1 ∧ b=c+v ∧ a=c+(c^2-1)/v := by
  obtain ⟨hc,u,v,hv,hvu,ha,hb,he⟩ := factor_param.mp h
  have vc : v<c := by
    by_contra! hl
    nlinarith only [he,Nat.mul_le_mul (show c≤u by omega) hl]
  have hvu' : u*v=c^2-1 := by omega
  refine ⟨v,hv,vc,⟨u,by rw [←hvu',Nat.mul_comm]⟩,hb,?_⟩
  rw [←hvu',Nat.mul_div_cancel u hv,ha]

/-- The unsigned ordering of three magnitudes gives three possible positions for the
smallest entry. The defining equation is symmetric in the two other positions. -/
theorem unsigned_triple {a b c u v w : ℕ} (h : IsNontrivialHT a b c)
    (pm : [u,v,w].Perm [a,b,c]) :
    (u+v)*w=u*v+1 ∨ (v+w)*u=v*w+1 ∨ (w+u)*v=w*u+1 := by
  have mem := List.mem_permutations'.mpr pm
  change [u,v,w] ∈ [[a,b,c],[b,a,c],[b,c,a],[a,c,b],[c,a,b],[c,b,a]] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false,List.cons.injEq,and_true] at mem
  rcases mem with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;>
    have e := h.1.2.2 <;> first | exact Or.inl (by linarith only [e]) | exact Or.inr (Or.inl (by linarith only [e])) | exact Or.inr (Or.inr (by linarith only [e]))

end Hik

open OMA.S_mo_161095
namespace Hik

private theorem finite_least_index {a b c m : ℕ} (h : IsNontrivialHT a b c) (hm : 2≤ m)
    (hlim : a*b*c < m*m*(4*m-2)) : c< m := by
  by_contra! hc
  have he := h.1.2.2
  obtain ⟨hc2,u,v,hv,hvu,rfl,rfl,hprod⟩ := factor_param.mp h
  have hsum : 2*c≤u+v+1 := by
    by_contra! hg
    have csub : c=(c-1)+1 := by omega
    have h1 : u+v≤2*(c-1) := by omega
    have h2 := Nat.mul_self_le_mul_self h1
    have h3 : 4*(u*v)≤(u+v)^2 := by
      obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hvu
      subst u; nlinarith [Nat.zero_le (d*d)]
    nlinarith [congrArg (fun t => t*t) csub]
  have hl := Nat.mul_le_mul (Nat.mul_le_mul hc hc) (show 4*m-2≤4*c-2 by omega)
  have hle := Nat.mul_le_mul_left (c*c) (show (4*c-2)+1≤2*c+u+v by omega)
  have hbig := Nat.mul_le_mul_left c (show 1≤c by omega)
  nlinarith [congrArg (· * c) he]

private theorem finite_lookup_all {m bound : ℕ} {decode : ℕ→ℕ}
    (hm : 2≤ m) (hb : bound< m*m*(4*m-2))
    (cert : (let ds (n : ℕ) := (List.range n.sqrt).flatMap (fun i =>
      if n%(i+1)==0 then [i+1,n/(i+1)] else [])
     (List.range m).all (fun c => (ds (c-1)).all (fun s => (ds (c+1)).all (fun t =>
      let v := s*t
      if c≤v then true else
      let P := (c+(c^2-1)/v)*(c+v)*c
      P>bound || decode P==c)))) = true)
    {a b c p q r : ℕ} (h : IsNontrivialHT a b c) (k : IsNontrivialHT p q r)
    (eq : a*b*c=p*q*r) (hlim : a*b*c≤bound) : (a,b,c)=(p,q,r) := by
  let ds (n : ℕ) := (List.range n.sqrt).flatMap (fun i => if n%(i+1)==0 then [i+1,n/(i+1)] else [])
  have cover {n d : ℕ} (hn : 0<n) (hd : d∣n) : d∈ds n := by
    obtain ⟨z,hz⟩ := hd
    have hd0 : 0<d := Nat.pos_of_dvd_of_pos ⟨z,hz⟩ hn
    have hz0 : 0<z := by by_contra! hh; simp_all
    have useSmall {i : ℕ} (hi : 0 < i) (hle : i≤n.sqrt) (hdi : i∣n) : i∈ds n ∧ n/i∈ds n := by
      have hpred : i-1+1=i := by omega
      have mem : i-1∈List.range n.sqrt := List.mem_range.mpr (by omega)
      have dd := Nat.mod_eq_zero_of_dvd hdi
      constructor <;> apply List.mem_flatMap.mpr <;> refine ⟨i-1,mem,?_⟩ <;> simp [hpred,dd]
    by_cases small : d≤n.sqrt
    · exact (useSmall hd0 small ⟨z,hz⟩).1
    · have sz : z≤n.sqrt := by
        by_contra! zz
        have lo := Nat.mul_le_mul (show n.sqrt+1≤d by omega) (show n.sqrt+1≤z by omega)
        exact (Nat.not_le_of_lt (Nat.lt_succ_sqrt n)) (lo.trans_eq hz.symm)
      have ret := (useSmall hz0 sz ⟨d,hz.trans (Nat.mul_comm d z)⟩).2
      rwa [show n/z=d by rw [hz,Nat.mul_div_cancel _ hz0]] at ret
  have recover {A B C : ℕ} (good : IsNontrivialHT A B C) (lim : A*B*C≤bound) : decode (A*B*C)=C := by
    have sm := finite_least_index good hm (lt_of_le_of_lt lim hb)
    obtain ⟨hC,v,_,hvc,hd,he⟩ := (divisor_test (A*B*C) C).mp ⟨A,B,good,rfl⟩
    have form : C^2-1=(C-1)*(C+1) := by
      have ec : C=C-1+1 := by omega
      have p := congrArg (fun t => t*t) ec
      have : 1≤C^2 := by nlinarith [Nat.mul_le_mul hC hC]
      have sh := Nat.sub_add_cancel this
      nlinarith
    rw [form] at hd
    obtain ⟨s,t,hs,ht,hv⟩ := exists_dvd_and_dvd_of_dvd_mul hd
    have line := List.all_eq_true.mp cert C (List.mem_range.mpr sm)
    have cell := List.all_eq_true.mp (List.all_eq_true.mp line s (cover (by omega) hs)) t (cover (by omega) ht)
    simp only [←hv] at cell
    simpa [show ¬C≤v by omega,he,show ¬A*B*C>bound by omega] using cell
  have e1 := recover h hlim
  have e2 := recover k (eq ▸ hlim)
  rw [eq] at e1
  have e : c=r := e1.symm.trans e2
  subst r
  exact same_c h k eq

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem ten_billion_unique {a b c p q r : ℕ} (h : IsNontrivialHT a b c)
    (k : IsNontrivialHT p q r) (eq : a*b*c=p*q*r) (hlim : a*b*c≤10000000000) :
    (a,b,c)=(p,q,r) := by
  let shift (P : ℕ) := (0x1003802402400003c80040027b415d0028000c0d00680fc056000000000000a13f004000000000e00a0000000000001800408ea7c007807800000000300080060020300000008013737800c016000002802c0100df0051e20006002163016803c004096000430c00f4f5001201e018008000400000000680ac0367a202180180022aa0010014000002003045000000b006000c00000c49a9b1c04e0170000000000005001001400200500280c00020000048000000b052b200000060030018040010000071800401a00100380100100010320004002005786801000000200080280020010f380000244ea000800c0005ab0040020010004000002002c00b0b68000016017035803001600600200e40060070018091c88008023000c2ea00300000000146380048001050000002805c004004003000000002d007002c0060000438004ffa0010010048004b3c001800000400f45b800003000800d801400040e00300900200030060010000afd0040008024009000000c008000000b02c002000014b934008001006001003200a00080242d000554700b40000030008068000001000000801a00100611700060020048f9c05c59b0028004020017000000001019b007001c074795002805800400100a099800034813f27e002c0c0002800403c000000000000010a000005c0000195f8800000600d00101a00027ee00d0000858a1a00900340040090000020036001307800003c00500000000120060008000012007000003403482700500f028200e51f345c474005592000400a00b0b10078316005000001401600901e000001400000580c802a004001800801801046c00140060010000554042bae01780001bc00200007e0004008169000c0040180013eec30e00c008af7801e00000f0144000000389001400a002001a22c00600600c000014eb8f0018000000002269001c00069a76b001801e8e500d000400a01100200200780000268000b30b57000000403400e4873a000100000010000004ec2631005c01000401e000803213200580280160bf0010000004010007000400a01f000000566e3a303d801c008012003000000002800012f400c00700a0008032062000801000643a007807804c00100024cc00b0150000078514000005124c02257b001800000000400000080003d6001002800600b001001d05a0002be8000004002002000198a00c0020000000000004003c004169000003000a02f00100080080140039700000002004001400c01200a803ca620000a4007404200a5c6027c00047500b800034e004000804c05c0040088004008002002003c00033e00500286968d3001001031e07300b017000200000680104500014e0801401605f00180008be30e0658009312009000800018a002003000001a000000000c01804d00180140121af00b0178088002005000000200108600183b800000d00280020002a2000c06c001000001000051b00011340285fe00a19bc04600700f0da807e00007d802c008001254000000800609c0034c98007000000000e004008000802400054e0010040000007008c00e00102c8000000370003000801e0000000000008026001237400a0000040004006009000009000000002f00086787a900305b4002000000800c8de18000780904b6030000808a3940000028f4800220a000801c0029be00782ac0000000080000216009608803402e0070178004006001001803c5c8009000000000000e007002400c000001800c00200d1eb800800838f00000180000050000000000014001000962803c00d800247e00101718e00740d600000009be48f0020a74004002000804c042c3c002800929a00003980409d00083ee21240300000040028df40091578018000009020000823e00200380208c4aa43b200285ba01900e800000800d000003400e086006000003c02000000000000000000f1c000000000000400000000000740000040001ef521a007002800401200400000009f00000120004b5c11d0000038026000037800ca6e002003802c03a000000000400e0000020001b8c01500280213e00091c7007801e00600c8014004018000800000a018000802c6780050529d75152003001a25001a0008c0800800000601900100004020000000000016001000003400b00080ac00800c000000002e01c000000001400c002b3a40020113b7000000a0013350010002000001803c0000560010064000006014000000e25000192ec24601b001802802c0ce134001c01600600118f400400a002803c00a0052a20084056000000804803e000023801c00201f000004c0020000100198000007000000016e00f000000000e00001c800401a007000000404a00a456800c03c000002000056400a08f800413686a000015c02800d00a0034006021000802401600175fa340024107000033800649545abd0400a003006000c00618401c0014004007000009800201200c002000000e00300f4000000000803c03811600a8000000959000316c002000005008000804f017005007409d000845c000000000807000200a001800001400a000800001c0080000000000008003805c010004469800800e000001013c000016000802400200500480040125ae002000c00c43a000a974002002005049c01000301e0004002016252801c01000b007341c0380020310000826005001805dc26000000005800800400f800000c52800100540020010010024004008000000c830000001800ce483b7000004001600122c800c00e000000001400200900091e001244d4c5000800800d73800000100210048000002001007001c00a007003800400000000c803002231900117a800e006000a8d800400207d0060ca889d00480107b0002002800000800625900180141f400180040084c70000078b6207a00e84d400215e00000c0094002003000000e00000100140b607b011853800000000000092ba0010010020592baf00080540000160022e80008000002012000200100a920c00644100280380024e56980000000001000002c27c005000801400c02100600000200050070014000019000803400600400200140060260010080002002000000400400300380002400060000004490005007001000200500b81492a200000208fc0002500008a54010d2000000140000030050008002348000004000000100000080065e800000006a60040000004002005001000d34800000c800c05e00600400000120021f08000002aca01a002005400c0008b00ad63ac00ca3b805849c0000f3c03e000321800c74401c002952c000007001805893c62d00400ac63c000001800000a008000000493a0000048030006457013829c75a00023181040da018001800000202c00000100042f700200f0002001009001000400000080ac002002004003404c0030000024000013001000c01800b04e0000c2a00001c061c000000003001400800500680000006e9000000d320e240cf800000a003017805d35a000238112800c578000800000003100db03c84000b002800000c00a0000efdd14014003800000001d11480140000004e2000402a00900f00200009980090cac00213600200e00040050018000e1c00208b803c00e003001008800a00001000040480080008000008010000002c00600f0a2800403400700000e4002001001005000002300a83d80040050020014d2c0030060010000895319000003600200023ac04c415004844c004003000800002e0000011c7c000018000800c02a00907b8ddc000001000000004000149800000000010598008ce800400300000049b9000001000ae46369009800000700000640000150188018a1e0060000008016001000800c000000003801c0003ac00980e400400200700000000030a5800000c0320008000002000000801c0000090080000006000000000400600100000dc0000060008008016000000001c01601b3e5002d2b20070068ac0002000000002001a00100083b400000622e80040120120008010030109003003800808221980040000021f2002c37200400200080000010060f100060000008004002012005397801801a6220024212002000800000c000000801800c00a0008000006001000106c00c000004051400603d006002002e95a00200b0004000003110800280c004801003a0010028010006002003000000a8ac001801000800561e234c01a005005000c0e80070030004006000000000085e00d1f80004016001001805c00200200580040168f4002801d1f8007001000c000004003001401600000080900002ec5068000004005000800001400100600041f6007000001c892001004800000c01e000009800a000003002c0080170020044016003000815801c0030008000046004003800803c00c0000024004007009800000603607f00000020180008008006000000800039400628b001c008003000001805600000404c000027a001000400000201600047d20070000010020000000000400200600e80180020000000050000001001801c004000099a3a002e00d000000401200301480140020090028004000004032800009c001000803001a037003800000a0000001c1800200000100040360fe000069800c0071670004002001001a33828a00200000080000020038a0c09e0070028010006009000000003e00000019040040000000004e1012e004803c0180046a70044032000001804405a0003db002000a8e700180040000130038000012003001800055a00200a957422015b00000194702520030008010004000001007285a002801c006000008165c6dc01100280340080110060f6c00600d002003801e12c0040000000000000000888e08900080000007f500000086cc0000038004006000001800c266012001800800200200b00940fe0070028000280007001002000200400190cc002e19000003800000100280040040080048028006000007004c004004003800000e000583000400800b0008fb001000206c005c056002002001402201e0048004014005002002034600f003b61400400200000349dc2931f8005078e00400700006a800d00400040023ae001000400803d1cd00000043a2000001510e309000001c002001000806803c000000000c00e008002801400869e006000862e0df00080180166f9004000c0020040020000004001000000c00800c008801c00400400000040080000038000aca00100a001c01c0010000058004001007000001a00000286a871a002003800c0080000138000006017006001c3ac2932008034002000000001c02800700400b001a6a6006800000038907581480040110000010014004002075000a00113a8c5803000000380080023290030020346007000800403200300000100dc000009000800000700088d800400112f001800a005001813800200f2a3801002062100380200020002360c84000000000001800800000000000020032c4802400000123d803001e000002800800a006003802400000500599600000a00018000004000002000107400a001802401a00001080040060000000000004000004000c00620e007000c0040000050008004000004800400800d001000802a009007980cb5464600500000020030030001232000004801401400000602a00020000038000004a9200600000160010018010004585002003000e00002a000047600b0000008002004000001000c001435802400800a009801cd180046478014006001000800001c00300000300020000120000000002000800023a002002006000435963c058400200200003fc006002011000000c000001800c00600b00080284de011002065800a7e400e003400400400d003000000b00500040061ce0018008002002003000000a38a001001400200f00000080060060048000002000000800001c0000022ac800000200280000001a1000000c02e0000b200741d6002005801800c00300100000040070018d743cc000004009c02a10708080110380000000000004001001127c1d60000010000010016000010c00c54f001801800600519a802400a003002003c0040050060ba001000300880009f298e0b5239c0000000058008008017000007800400000280000022b10090020002001001000000a0040248020000836000001002800f003906c05a008000000000000700084000040060030af4010000001804400400200a0010076000003800002a0000060014af222f001000800200c0df803431c028257004000a0fe003803804000a000800c01200300f0010018011006955000000800100180380610018df803e002006000c0000020001180028005002000c004000000800003c00a011800001a030000800001601a0090018002006061802400637d00180000080030030020002000000b40400a00500103b00120140048024e880050070000002000003034401000e001800400000c000004c008002000001400200100480040500010098040002000128801000201d0080004000002001800000000000280040040190001e945fa04a000000c0ca01400b002800200500403a5bbc0050040034000003000886c00400245a0014004008000000000200800b800802c00200100b80040060370034002010000800c526004001000000400e0088000b9400f0470008000000000000400c00365780145d000c000006800200f0040000274002001003802c01503f000c05c02200000180040a6008800c01e001002000801c004084001c01201300100080020000008004664000003800000c00000080a8022006000000000a000000800074400200102e8000000004800000000000000008b0015008800000200700480040020010018004000002008000000600000180200080000da004800000009a8000006096171003000000600180044ac012000003801000001d000000a0000000ca400825100100687842b20a50008004000001000000265700080000164fa0000b40000001001001c02200100080080100010010030012000001001801a000001801c0100070679e48018000000001400000010a00040040090000030008004002000000200d00500044a25fa0010064ed20010008000004000004800000201801e000402069f00100000420000341774002009005000400a0050010000000000001000c00a4a40008014000000399000c000000000001005a014000801002a000001000000800005e801004e00200000180100000048008004004030023863a001002000000a001000000800200000000100060010008098002002001800000200300200080040051af005000e00308d0560002004006000c5aa0a103c800802802c00a000c006001002806c3d800000180380040090018008008000002801802800c001800000000500c8030006001341808043001a00100040042e2000010000a00100008cc000006439800c04200169100040300ff003800433600000091c8018013001000c00a00264a0018004000000805800200400080080040120010000000005202000c016000002000000a34800280080146220000004004003003800c00401400300040040020020004014000000007400c00100080340000010b200040100050008008010192000000c00401400480115e00252d880040020010010018012000000001c002001491800401000200980100020540010008de000e0000024000003000000400201700000382723981ad00040027110000000620000000806000c00200025c000a002008800800e000002801036e2cc2eb00380180000010020002030002000000200600080084c0004005002c002000001000800200d001045400000000107f40020000000024000001003008800c00d000800400200c0000ed8004000062000000472e0010000010025002800400470a002800000200c00c800000c0010008254004000005000001000000a1a6c0000000000018dc600d00c0000016000002800000200100100000640150000024002002001800000201d002000000000a000001800c0050000029a5c000002001c0000000000000004001003000800200200480080080c6177802800071f000800c0043c92e9000800000b0050000016090001800000a00100300080000010008028006008000800800000e000003c01202500c000019200000000040000060040000008025003003000a0020018024018002002000001000a00580180000010030080000000002000000a02000a000c01800300280040005700031bc85800161d78de001000367b00a80102ed001001427c000002000c00000000ca964000000001000800600133600040320800010000590000006000c0022f132400200000010008004000001009800c0000010000b48010000002000c2c4019007801800600200100041940080018030002000005800c000003000000000200400822a4012000001000c0000060038004014000001000400000329f8014002001000162c002002000000400000000192600020000000bfc024004002805000000b00000105fa0010008034012015005800401200d00000052467e4001001000a00000983300000000b4802400c00d004acc0000001005800800209c000000c000010003000000a0020550004ad800802a8000004000002801c00e004001996c01001600c002400600f000004520e001003800000201300096540021440008030028000668800c0000023660000086000015000003a0020001ab0d68000000000400000000280200040000001090006000000800110600a0000010004000003800c012028000000001a0012de80380020110390470cc400b00100497f40000008004000000017004801000100400080060050028008022035003893c000409003000000220e00181d40120fe004801c00a00500480053c2000002800001200038d002800200200100000040020038010078004000801001e004001001c00a01b00400100000050018044002005000000c00800000083680409aa005801000000c003000000402c316800c81800300000000000000008028006005000005800000a00580000260040008000006001000025c17400b000000000e00000080000000000040008012000000026400000b0030004e50000000000000c00a0040000008002000002001800200000a800a00100000240022540030028c747ee005800000000000a0020000000002806000001700180100020020000010000000001000491c2d502e800000401400980000020070050004002003005801802e2b100100100020000008000000002244800400800000000000320050050af005a00752f00154e2283000002400c00047c003800e00100282cc0000040008020008002003001c000095000000c0000010000030002b9200c003000043e004801c00a01200000040000000018948012001001002c01c9d60038040004000001859001800a003800800c011001800000400700100042c2000001071800400100c0008014240002804c0000150000000012000000000000000d0000a70000002000000800200000a9048124000001001000a0250a9801000000600000000240920000000c4000600e800c00000a001001002e009000000c0080060000038000c96000004c00a002001808400000a01380740020000060008000000003a390032002006800800000100100055e20032d4000800600600000143f000200081800000000028028012004001800cb3408400080000082f2002000c002000000000401e000005803c0000020001748002007000000000c0000a885600085240038038002000000000400c000007801525e27b19d8008004000002001c002001003000800000200180000120090f9002002000100c803800202701b800003400200000000026fd00100140000000030020000090000000800000000280000120040020018832005002003000c016001001c006015002000802c1b400014c000001b000802001c0022fa00080040000000004002005002000086000f000000000400400100300000000018010002000000002003c0000008d0c002020007000001600064d00043f2000003001000600200000048da0000028008000002003009400000100180000140030020a8c4f0005000207c002008000139800c008004000000209e0010008006000000800000000000017b00360030040000002006000800800000300117a417c00002a002c00a00b002000800600b0038029674003008825c39c00f00a00000002c433e8008006000000001c01c000004002000200100000180040010fd00080b00040010b34000001002801000a000002802000200000400080049d7000001000200000080040204db00000000000000010004002008001800c0000043ad00000020000000018002000000000400600010500180020180020000008000001800000e002002000000400514b000000200a0010000008000002800c01a014001800401800b004001800c001003077400000c07b1b240080020008000038009001000800000d000801c01cbbf5e0000400002300080043cc0070000004000000000000c0040bc000002000200a00080040040000000000028008002800c00a000000000800400000300180065d1000003857800100000040000010c300000000150001158000254000036c00e00100602fc0160fb1b00018000009003807400800f0008000006000001074800000100000180000030020c480040040008008b960010edaea40040030030000006001001802000001800180000000040731ca8000000004001401a0052f2803c0004640018570000004004801800a000001802400400800000000040070020894004000001001c8ea00b003800000a00b00100000042d7000000000e00c000000800200600080041e600100b08c01ca03f009800400c000000000401a21b001000000600100600040000002cd01d4000004000800c01223c00d8000002000001800000a00100000080020010040188000004000000000022600000000080004d0000000200300097c800800100001000181590000044012002003800800e01800080280ca007056000c03602537980140040130000014008000001000c00000000118cc000000009000000a02700111480140e0000057404800f11886ac4b8000003802010a0090010000006012002806001a0000080008010009001800000408b00500040023ee0010004006007000801000400700095c800800500980000021310040000002005000002400200300000f80043e10b08048002003000000402e00100000108440000000000008000007802c00a00b0010008000000010007c0000012d380100041f00738f8800400000100040060010e28000006003000003803a1ed000a7541d200600200400020030000000220000003021800400a004800800800100600000000030c100000060050008000006001002802400800b000800000000e00100140020020008010000000000000c00200200000240040060aa002401001300300080020010f304a4000008000000c008002000801000082d002000000800200000900045920010000b40000001001426c015000000c000004000802400401a000000000a000000002c00a0010818094118002004000000400400000000240025ce8000256001000971cbb48ec0050000006001000000400c00d00000000060020010024004436000000003a0000010000004025002000000400d0018014002000005000c0003f200000000040020000000004000009914c00000600300205a00020000710006002001801000000000000002ec00200400040000020010018000001000b13800208b00080080001c1008001c3d00010000000000006000804000a004000000800000e000004c00c00d0010018000000000000000c4fb0328000010092000000000c1d3001000000200200101d400000000600000060010010018008000001000003e0000000004000000004000c00600600000300000060f1800000200f001800189a003000000000000000b0004008009005000000c001000001c004007000000c04200700d028c0080054ce0000000001000000800000700280040d2008001860c00400b1ea800c00000100080083da0030008018000005 >>> (13*(P%5381)))%8192
  let val (P : ℕ) := (0x33729e94c0000000000000259683264000001ee001b8a1300083dc78003820024da61206fc55f8000000010695800073c000008186b000000000002278000004b22c000000000001bd00000000000350445a0a0b00051c004010013edcab2f542001108000007be139a8652644ca22175b2e1fea154225d4c980000109dc7b01936000000005ea0000017700061175a273fafbe2d32665a8e00021524e5d5c435b00000143b7a34a000cd8000000017b9437b252cdd9823f2b1cd88007c11ac8ba2f5a86ddd8a2d56c2b1a22897c20012db4e00070e1d1673e0a9d6bcf323200000000356511fdab36f24e4001ab2f4000000003d66794e00063b414b70f6000df08f237000000001093f329625a303dca693b36d0003bc000000006bdca8005de415bebab000001c1cf15b86080000000049c0020b0007dc0000071eedd498f10011c5238007e427886b7a0004a9990006e2f2d14800000000880005c64ad3fb49144000e6000688a15678002ae7fd7092723b09499d2361aaf40046150f22162b235ea6dd4296b0013ecd490952a7fc003410008c570a2731a260005357be000000000005e400000000000ecbc9000554003df842f2e8b80014ed38000fe8fe8395e8002131dcc5acb00106628955000001abb2b70a000000000010fc000000013e5a7b7c0005e40036b2d68ec0000078e48c000009b8fa48f9b745c2bc65cb511e46ca29db00000196aa96f6a1e258000000000031d676a24e30001d60023380000074880ae16fe8fc000000000000040d0013340000000047c8b800000a0c002a70000028580000000089bf162644494b0d41e0007f2302c0e14328006f4cdc001be7e84f100945000001ef8003c23ec00000000f11610007b2736529c166f364fc9dc35e0000011200084c000000004fc000004e2000bc93539a0000000025470800000000575d4beb2329540000000047e058004c2c04002ff52600131a41000001dcc113f46e00018744a2ae849e73ca7b4004690000009580052b1440009592600217c5a0009051f1693863d000000000000d82bd0000016a80096a00181800000000002cf00139d94800292000003293864c4001330007e4ba800346001508008645e1b5c010003e096b715668140000026279e7d8003b883e4b4e7152001e737500067c9e42573b085c2bf55ae6717ca0597c4020cb11720d9547b1a442af5b6cc744b3f54f000000000c3aed00000000000000000978000007b40040d631254004a54ae000f1abd7fe67ca450942ad3a3da2da7249df02ed24e4cc70aef6f647a4c3414dec7e1e9298f6001accb97d48250228c6ac0000009f24a53c000c750a3b648c258787f60cb677431353a3832809460abf13e0f358227ca5cded2c0008ae001c29d566ab8d208ec0010ac0011d46276446bb523abcdbc29333e748689b1000000cbbdf792f74003b900135a7f0003924948a80029298644c25796f754f8bc8aeb5d318f464e001c58000000000028428600000350000000000003b25ccd780000126cd2aab00077d6117878e608d1c3765e5ecca9d30000000037e0004740046c000915029bb96e9fc60a708ee9bdc5a1155b085a709d9086fd1d8006ee4dd6a8002e2000c437a31444d4cb08350544000000000000000050e000000d939200000000000a453f89b26a000000000000000012839f4cc001c90003ec002e16e61de504142bea2553bdf18ece40025755e0008691f000000638000004ed8827f89600000149836000002e3854000f98004ae5ee2593534646c001af91e000000006526596baec2d2000004fb5e60007fa982c6b3d209cd7b30fd2ca210006bc0000093657aa380098800000484476374ed8bf46e00230baf63e000748003faaf56ac070007b493a003aa00000301000000003318d2000004932d2dc4d5ba11550dcaa80093243d0e9b347284dd6a9c6e6ca134c1f8a2e05f42db9d64493a8003dc0019090c0004e490b1f000000001f99ee000004e194adc4dc80081885000346106000fd16d288f751999939a49400000000824aad0935267d5f9cd35e6b400277000001b10000000018800000100c00000288c0d8b8b09b28f4002d75520006eba566a0000000000060678800a2727525cca91ecc4000e0856001329773ae7cc698007be5791dc8fa5e0028c80047a54cd1a317ea000003230f109c00000000001e0a21516000003c1000000000000000000018721e0000000085e001c78000012940011b6e800193ae38973a0002e45360000016f000cc8879cb5888fc0000024200084c4f6ee3d1449fba661913ac7d0002807497384b18543000422ca45d8a5552000000005f8c92989370009b496c03a12000002d1592e2cb10003700012b98b0000015a2bf1820025aa81952a363e94377262105ad14ae8b1298b5000afc9380076a8ed0f000000498dcc0744abcc0023d51200195a2039a000aca391f6001abd15616000c9ce10009b2048004720016ca1d5fe5518f8005e63f4aa24731a92d5680044e9dd69bb9001174dda2d7a6d4d108e8000d4c000000000000000000000149ad5000c34ee000000fa12980000133cff80000079400434000f393bb3f6f2838d732f000001a11376bee1e458df000506448001e2864819af9daade269ee3555317a29b86edc4001eb1a2ef23fad78fea05209e500120c0033c4fa7a4bc800896001058e58fa3780039d4040011a9576526ac000003eb0a4001f72aa7d4bb3a11bef040017d45e000000003f449c9dc91956b8d36c9544e6dc4297385ac3858ad11d6f0d2bb7124345cf193624a5a40041c3e34f40014e0000000026939a000ed00000113c002530000026f800702f7c003390009d285800000001a9800000000000d00000000031b6b247c7c26b00000261800000c659e9ff1f8dcc001836226752b8d748a000003325344293b80054e47d3480021e3980032b00078400000a70424e48001aac3c004a557a92e5f4773b289c8a8007eae3c000008de8266f8005f2e81031fd50cd44d9000440fee368007a6a1c8cbb343ed6d9c19183c00141aaf2ceb8d0819d44eb50adbdf3dd144f49872472acb4aad2b0b4581bdd0007fe378000004a16097900106400468392ebc8c80000082140a2789aaf46280096eacc000e5822209302b777351d49ba71a066c5c924000d14d1b5b000b24ae8000005d5ab9679200018e8004de574000009aefd60398f5f270e019090012a5eb4690008bd272c74de64540a0e657005b5afc858abd778c800000124000422000000000005140032f14abc45c8007ba0000026932d1b400000000ee4002b1256001089758ec002121df54a6b8baa7f000704f5c553c2af4f58003fa000c2cca1f6edcf70000009d1eeb6d53f508cf8c96c4000f98b78de4952b800566af5548004fcc34001512ee000f68005e670c00000502df0d6a6d766705a9a021a2001cdbb693f1bd2bab6116454f6a5f00100c001c73a600090b8d5e292da9bab0003260c96f21800000437450d0d86b016e69447dafc9860000038d4ea48c478000000000018700088d723d300098d2696b5ae000003182f60016f11f476f052880043aaa400000592954d6973232394f99eb33e6e800164000bb4ff938000e5400236000ec53f26157e741ad8f866a664002d148ade4d32bd5b2d5cf10008a40013ec01000000001e438e00180b12222c9d4e24b0003d0eab0f31e9fd408e14211a9fd96c0003be3e80000018d0f8e77127b5573a122e00000000676f7689ad776ae3c8b8008c2bd4a9987346000003298c2b1c8fc5400075cecc91000000c49335f2af4a5b1757edd594a4a6e298ce6bb0320484c6a646e315d1e31f17e43d0db0146240ccc96f1fc7e4c2ab485645c000007060016ba962445c64700020073cb99782373ad0816c4b8c1e638007345aca42326065c8aac7f0004c4003fa2e82ccb8ad1500af4f5800922484b5bc5782000000006ca0024b153000ad087bdd7666f8728d9000001edbdf000001c79437e60020c9b99c280000211124548000004f4e0958a21000cc5840000008b40033b146001b9b32773226529d58504dd1da054a4b295f91f5e6000000007be0000015561af75d3a859068514abdf7a6a69e0875a2ab0c004c7000bb483800000d6d64a34896764b399b54a89d28af09a00009080076e6b0000003da614672e76646247cb6566ee5d2f211408f29d0800422944000000007f800255000000d48ca4ea47c002f32d500da7c3c30e00206a272431ec92b112aafe95b96563e5768f1ad5c70e5788777723f6872935800015e8e253127800000000cf400000000e5400000000f4e288006ce5040011215edcc000006db34a4d00023cc940000055f1858b9ef422cf45e9a54505b54f8fd3facb96d27486aff4000002ba86c003995f921cfb9060004159123f346d94b2a2f5d2815808000000000020b6ce3b5d9bdf3d92952b24f000b947f21700068d6895143a0000049b3d2d549b8002333e15e8000008bcce38f000dad4498d4129445598f9ecb8dc38000005ce2912160e9500033d5006dc0025734666cbcbf788600000000000000000000000013b94d47e00240ce7000000002e322a57c0012035e47c00000242a4cfcc4300000000000000c91a48dd5326085da8b463280538c52a24c205b015e6c34fcb7337a35c002f370910d3eccd1f6cca6ba7732e0019da6921ac04000f6256a4149a6f7e6001003205a4d647a8e34ba000001b900066c0000076ed8d529d894ae3d52c793f2cf46d4b1412b1da09f71cefa1c79845de451b59c170294c0032947259dfd8f2416000afabf2ccfc52a19f18ecac001196e340d5e53c6de9ac762fe0008d57980046cf8c8c8cd16a6b0e90009ae55d659c63d6844b99fd676a9c46b916b67688f99638c0000017d0003a948b1d45f2c5868009d69b997b732aa00000000482b28f70000012b128b010002752faed7100000011f7d000134a1e32e524cb47869846c003c1892db40013e160000e79d5356000002fe000000000fb44ac3cec3df3f27fd04a2f9c32bded9397d4b95e39fd2245ed71abd72e8549a996486e783135378c9fc98af34ca3bdb9beb34a3d48fa1129e84555a2169a734fcbee36e6594817284aa60dbb4f3fecc5f516d77ed2577c191fa8ed83800832884f593f79710e528001ee37487c2f31e69c00000562b25db9ee000001db90655715d80800000e7dc6800000a4db980000000175a45000000004b5322735529ff0006e945a3b36e0000000099e82c000802265768a8006c27c13a0976c20021580068637131000000a0559b1700047887800208af6363715c0bb5049fd39a0017480000000000167000001439d522695cd09d90005be5dba60003100032d27a47c00429000001fa8a344e71a27d093a6a0db39ef6410d5019a3112d9c0016f798f040035840089579b4b3d6ff40000000075d571f700078a7b000000714000000000000000000040c00000000000000000000009380065e0000000033e614b1cc7000bc40013a1ee000b9800000a4dee8006c239e529995be0016b94358a484c126300000000120556001bfcdd67625d2f8f116eb255f8005fc001acc61000fc468a39000000001711f7084000003468853a800000000003ac000bc8e52e3000000b195f56d29667800001365a41e96b65e4001121c228483c2338a644c58001e20020680000046c0037e000002148007969700010f00000119cc153abe4001192ae001a1afb7b4d550a80084ab45a9aad3f28e5a4aef2823800031b49a002369aa000fd400407000756453844ca0010aa3d358bb0000007e60000000099e000fe00074879c93942000000000a9001094000004ae2b4480000003a8003a9508000833e36d00014dc4f7ba585e09db000001c3b3b3d236d73c37000dcdf544f0008ee2f8000000019a8009ee8a478ce1286a746c0cd4becc950a6b00065d9e800000000e18005ae0000011100053ce50ad4d33ad2aa8377316c000be88c000000000005fc00000238acc002bd836aee061110009ac002e715200168bb5602d762930c7ba26cb7ae52da3bdeeb5571ea657f2693828fd268009c2001dbb51000f994c3a9556001dd800000002918001086408e959001004e6a814b8424890fb8933854fb9d71e6fc86800000000ba9c66d45dc00239000af4ccc0b7d6f050dbb033efa1a5a6e84e8446f800350000778005cc4940000049a7a50eb51676000999d5552dc4ab000968cf49e800000a88000003f53ec0036445661c002a90002cc004b81e0001a8acb2e10543f8df1a6002059d56e2e3cb98005de8bd96ada2ea35c003118332c56090145f12db0a615263b187a3b6c261d64c593332e40011b3e63d08cb1f43a002678002c26e4f780023b0ec0023b8db04c3995f86b2dc8094e3648f400000636000f480076a001600000003e58f97833af76079c135e0018131f0009f4e797b3405b162c2f0c29acca80066a001b280000000270800000b44b6000000000d5a6341295490bc50009ec0000000000099bab000001e38000005b484800000000d8800896c25c1b9235226c004513720011221a4da3d8000001f600085b8f530001ae80050e5a5d48d34f8000003c5266e4800164000000000009869b4eaa7f47a88e294616948e8001d60010c00000000000000345788000a34219ce00000000000000003e340e0000011a28e880a996121eec65a90000081a2ebc1000001988000013640000000057d47a1700000000110305305e11174a23b8a70000000025d9401d69b479b1f28633c8cb0a21e3a607abd1710f0a7b0d2de9a07f8e633868c0040b556000000f1304a240024d7a2000001191c4a6068a1d2f63ecb09095ae98c57931394000000008050360f4cf000000001bd000000d400083e00089000580001288000000000044e2322d4002551e92900000000039db29f76020000000075c744002e2000c7ccacf274a5ed6880000025508a6b3f2906209974d288c001d2752ae98f800a260000030f000b5df4bbf5dadb400000752001a2119000d95bc0b9542000db800300bcc74b9d0ec9fc002bd000afca909e39e8540045b22ad4dee800a2a0017e800000c440039744e000000cb000000003ef4449d61cc002bad2666b0121257d6a80057ac2931bdf86eaa512a710c117d77800000b2c004b95dafc4dad0934646c002826d7455969d565692096800322605b89cf000000004970007acdb80067e0013aabf6d4001568006e8000c5800422ee1873c176f0004fa094460010baab4b31a40000010f37de8ab55b2e346bc4339a0006e17b001444f5800000001704839b631e7fb1c5168955fa6d97ab840000050a8526c96b0012986ebce64eaa087acf1ea3148c928304460c0c111d6f54df8f1000c04004278cc0009f800526e5da39127ea4351ec9c6885a5e4c4a646000e1b7d2dca61ef8cb1a2e3c000000000000000063ee3c000000005b400000592bcd8895f00121d6c90d80b174e6a75224951faa1c472e65bc9fb656bc98c8c345317d42b535e63d0ce8bc3544de438d25c106d2c8ed9570cdca000000d510ca7520a3f9b9c233320006f9d500054cb69e38c12369a800000000000004f87040000000000118425000c04a58004d2b800000000081cad4912da584e193c2731fe94000506930a000039a0011d88e63e0014fbcb70645de08c33e10dd80909657184003f60003c9e0c7e00081400261000000de40a26e50d5faab000002759d100137d6ab337a657c0016b0008f556000000000000004ea81a1ba8f20665c0000040e0009210f55aad489bb52f200104a0c5caabe52b398c27ee608fd6b26c49d9a184e95c893776d42e64ea9f974a78f6b5f566a9180b070004cdc33331fc000001c31ca531310ba00063c4d0db4708940025e75e001788d43f257c87b173cefbc002070010c153b3f64a544eea751a6b80820005e673e731a12c8848cba3b5305561b8ed41289c0021b9880000000020e0000016d6d718400000000f75d1a234ea000f2a39000001179db2bee14808003a654d5291614a57cf78008ba0000021d512000000000013fc0028864a001d800064e00073b2b00000085800000000001a7000a063dac53987f4000e0001356118003ca0019d8aa0010acf50008f23725cb83000000e68002b684c4c9c94ea5613180000076c001b12de42e619449ea00057169286001c2b9336673da29109829b0869e7743478aa17b5fc97000281a2e8062f80065e000000000000021bad75220003e957000be4003c52ba4dc69cc3000db0878000000000022142e52cd01e771c61c8ec37512e500015f22600000223000d340000000000231800000934f137195640e3e0006882d0004eb0002b00033522ab85fc80049040c00000000000000003460028432b6ce001d9000001095c63dc652b8cd08007420000000000000111ca7512c3474cfd7466ec001b982ad54001d611a505c7a7769f01d798bf5dacf5b0295222afc001a149a560fbaa78665cda81916c9190ffc1f18aae5dc919584001dfc762be750793266752add6c1126085664ce1a7317d9235b77cb3dda94597b19d528716d6eecb62bd000cce34b8f2f2b84f5ba42867563e80030e6dd14bc32c27e8abb2d686ab6689a34fe001769644971f40012b58a42cd89c70000008f9672c86ec7dbde2291240039c000e01a3b010003b000000266904b0a5981a61c000006f848cb12975e66659dbc134a6a4878000007cdd887c4363600021b49acecb68000004248900039a43c7c8b59b6001c909d3fe00195a1b5ae3be28abf89ee008216640ed82024232defde2180000074400000000ebc002511b200000000000000000002124ac0022f00074dee9a164069800335000fec0000035e9ddd680011697462aed0014b4000bc2723ea3a91ea164c4e68fb00000000291000001198005566a4000ed000000000006cef75868e22bb1ba4e80037a84d1099400089daf8002eef2c00310422000d19152440000021d9eec05588a147e000000d11be8fd299131ba8e58705f396dc47531165cb8d86c8d8babdd25a722903bd608cb50e0011090667689c0000080643d1e8006e2b40c98858f249dc9af70009dc000ef4a43c4001e17ba2dd58c3d52a3a48918361ae3c004ff000000000002d6ca663c510004d631aa334a4b144bf0000b85d08006ea73400180a2b2aa4b1e70004c0aea17000839cba7500000297a1a4aeb5d3f3eb2ba94c000e06c22f5efc7f1ca504000ce000d5464ae34da000eb80036890c63be745e000d4cc15da00156ba90000005ac432acec4002e3000645a0bd1000c9000000216f04000007d4934001e7336000000004ce449879952fe0020f8003f2e18be800001260000004e498c001c1590001f4800000a44a98eb94afb11c397176cd4fcb890eae8c0024d47e000b6b5b4fb075e58c700048c688830013ac004ec54e00000172a3089d69abe596e3d9a8002b4bcd0e80048ce75482066aa5e0d013118e57d8fc3663273d65c690005ae73a596b7055029a500000169000000e2483c2a00000224800000655c28000005d609b0f356a5c0043300101cd40008904280000057682400437436520cc9613827ed86a99000000000e93e23fcc0000674694d1937000000fbaa33f29ec00490000bdc00000000000001110003ed2380000076153c6d22c35c001e986a9fcf81c100073c522e75b40000016a8851f5bfa3d6b68ecbda3636243cfc8bf2ae0007c19f7966e534ae372b134a49f333f14519000000aac610005560000000000000086b06a4308481800000dc5448d93f2000f5a5184e67e289109823ad36cc624243e0348d26f295229e2796001e822100000000000000000f492700081d5fbc27ca9ac00175242000f79eb000754f094b2fd3d457ca56e32ee99000000d24003c71c00021bc73166e3cefccf1faafe1b91300000087800000bcce6800000e1624ab11ee34ca08c44a6000000b3342000000000004240021a48adc588909a2eb846d8007833fd4a8006ea5dca790a342000000002f6af4fe80032901d6cb0d3d63cd960000000000000000000000373000851b88000004fd40a2f000ba4e88fb00115d60c4b29822c002699f23413fd1b20a20c8925b296a618b99560ad96048002126bc98af700117d5699376ec78002233c8d04001db57a2454fd1f53e514000008ba414002210009c400000000d34ab80078f33ce94619740004da05296c1558b3f3ae944d9b9e3ca7c278800346b542f000000000c929800073db1800000e240010f000d54000ef85e000003a2626cb4cb8c16e643e6880000000099b270000010280042b408000009c24340000000000063a53000cbd7b9a1382ab4c08000009040045f000000f5a8a001145189a48ccff4850002b673c002e100000000154000ddc000e972ed5800317000e24004557a63bc00000000734004340005740000000000000000000ecc9b9cd001125e81bd00026c4b00039e6b8001e531afb21bc2da96d1d3f000000964b7c636ce000b3800000314f71580000000025221a61de4c308040000000000000189b674faaa4001a3000dfd1d8004728bd499e24a31c49690da3a001b5d37000b6c0000000043a1bbb73a4c55850000012d40000064c9f83780070e4a100000000f6909aff1ee000000a6000000000005eeaad4799f00000183b7b4d657c000006a675c0036521af0400449000000000000004f00019624660a0f800000001d6800620df084800000000d19f9728ce8000005530640040900040c819251ea00126a37842989ab92a4268c4a596f0000023080048320cb500048a7e13a9910005a0002bd53e53cb19f161ee51c393c2062f52c96467aa65bd0f9000000e50002d2af5d5b7931ae5e3e8004422a46e9011df1cc7c800000000002a121a33176af13470dc953083d68ec0000092e0000027d3262e40028f000c0cd18004b507d8bbe361efa1229cb001518002570000007c9846aa00082afb4fb4f18e8f41ee0007db2f9b2b2527aed00000092909000754e6ba33fa000b4cf200122516a518241e8000008de5111d9cd000000aa80000067800351346e5c00000000d34000004365b4dbad12e12c155a694720000054132668d449bb606ec5798004eaedda1bd917c0015fc3700000000000296000002b2000000000000005a917a215de58469b98502904cfb3b542664004d939e46c003250007c484a847971a4860007b45ecfecd54326fcfbc632aa92644800000e15843db370a24000004f83f0ed80049f024000e72567e4002033463b5202ff526000001733f4f1c0000025e000a1b2b000b75360a33ce7fcf44e63a246988c5d000d10d78003c6cd192c3b23eb15154015744620090b1fc694b39995f278221a094e2fc52546155a261882bd20303c67c3a2b330d35a8740e00221acf0bb3de52bbb34b4b0cea8d86258257800a1ad080036567296c9b95940e3de1380081e594001c18ae000dbac72f6f768690142a4d4c3c885e8f51efb734d480c8f97587884d51a3b5e257d1eb0044a904df90b1a09e4dca2f6b2545c5c7f6d6d44000df9127115eaae4543edb62575f834d0a96d2ae518003a57ba9657038353e76e0fa1a704b00000005c6c3c8951d1fa7c0004bb7fabbcefa2f000002378992825c4aec58000001ea800143455250b72e66e9200f26be9454f90750e000003460000003a0dd00000047ab14e4724a88001530c4004c771a7200029600116800000482001a8bd1000e187b1585b2f447c9d333a424992aa000000000005f88e516abf9f03396cc492d8e5e498ef11a000ec8001b6001ac800000f74000008840005826c6560007297c35a001e28001c24fc0031f632fce058004ae0020d38d9b927c819313448a089894342c146510732ee8cd0b1d436d9ccfab33fa7dd629c37e307ccf3d12ba9dd0db8f2cc1e5a7b2b85643c0011e000000719100009c4f480030a8fc0040c39adce0dc16000f2dbc8008d2bb5138a434ca24000002120010880021200204cc11e317ddbac74ae000f799f20e665ebcb51feb652417948280128cb765e5852ba1d000000ea800000bb40042d000614689814128460d997502000cac01000001f8ab19fea8cf5800534314000ff976ac084c7f0000009c8a75d8bd513a09154f4d840000008fc001d000000195980000e5c0023600000000000000574002452c6484fe8d1000000000b33eab64002ed0006440040127e001048003ce0006880038cb4cd880039ed25fe9d00000026d8002063c55c2f12bee5d8692676a3d8002f300000172abd4046980000000000000000000000000004ce0000000038ebe4002d9000a94002a7000000c3a00782001448004220000000089e0005c0002f7000dfb65000844d2a30000ad9af93500117e67af020a6cc0006d1353ea3fac0566cb5d4c4d10294546cd9284a451cc662106085e4576df08d761b184a7196a1ff4dc48c4411f4307b50eabf75a3ccb280068eb7544a6037e78da897d26ca9219499000644cf80088684cc49c174ac656ca9948657c001498127cc004ae3f20000040956673c0012d2af084001214160000029565a000a49cd916b5c64c690b8000bcb2b9305546200071e8eceb8001caea5eec4f000c2c0040d000304d0a2d96ccac003f1000208d28e5876000001649102c622bd73220007e9a35a2734cbaef000704b09575be38db98dd0004de1389d1fa839104a591e41c6c2bd2d2d9c44901000d9d1d8a73428e5af8ab80e78cae9f380a8fd85800000001548008e0000da9152624cccbc61000e519f9cc1fc60969a037f09ac001ff000001428002060000023958a000fe000959380bca4d7b80026c8f529259dbd45e2ea4aa06000832ead958007ba9dcc38006027249ca72000760eea8f8de0007799d000a24e0b1d2326140021a2783ace68001f6000ccc22310000f28005860014000013ed4c6aaf5362a805fc257b255c77387000c3557a7200128c0042a3ecf04001eb1d02d44bb7f904755979d8000edc0030d1fa40c0018b71733c002596928fcaac3f0008f4830006060022fa4d3947e4eca2f1628a52e3da2df199752360000000020300025c00000506c94f09490009a52bb4783c734001860007dd6f9ee00081d73c961caca5908004b74198d269000a908ab6f4c2000a315342af56148006b0000e7800293185a7a2188281c0000018e324000005766580036b5fd33cf58f15aada15cceb60267e999bd208cbca4b3230e998708000000000000062e000553ff9eee88001a0292000491bb7ea300879736563edb480094a000000003fef94b0949000c0400350000000000000000013e18551318c54105530001451d33aa7a4000004a63ec004412e200128c0196b27cc7bd98c2681c2a9f5da70d089c62863bd04a672da001e0c9999eb6d4aa77a16edd95ca500110cf68006b20000000037a6669200059f0a40019d39a000004eb00057c3fc20000eb4002ab5f26b103ac3000e0ce680000040400289556d39cdbca8c2a16913854d2fbdaa8cd4d6000778e94baf9947b5f7f08d5508008560016d8006b694000000000000000002c6b240036d000b29d8b0d000000940dc00075e1b80063e35e1e29541c4006b2bd1ee00082000000000000003b66f5b60007fe2fd6707700000192800824a0df0b732f2694eb8e943f32d5e31f18a001d3c0b50e40d678d32ab2ed0bcfb70a79e4385b7f29951cc4f59333c0000000087c000000000015daf3000944910ec70a67d589ac530000abaa9142574caa46000000000f6000d35bb4799794358b94215e964aab5261a0000026700000176a3f8f71980029c8123e40027f0000029a80000000284c4399effc003114964ae85800764a1555a992d5348e6d12824c699e9c19f2f6d4a1199b71d451800322e4a5d800000948000002060017f0000011d507873000000a5c0f49000075ceb9b4000ee88625a0007c800a8aa7c80b652460000000026719a4dc790003440034c000de863aab000000000bc80e6960b34361e8c0988b846acad50b73572bfe78b1765698c74bf11be87cc780021e8e4af8002aa000001f51e8f64004291bea30001628df1e00039b39d184003b7000000003df4c31bdf52468aefe46c99f1a247400000001264004cf61e000d1a2d00110d700009d60000014e1f64a1271a557a57507b040000000000083efa478800882c352290263a3f92bc4b23a0009f800562bbd8726e00063d6a800922b9dfe8004125add4b850000018280050eb1545c1f000001ee2e9592000003b062c5465a1e5000000bc800001134dcbdd41c25614b79000001fd80049afb8cc9b7152c84f2b318e8fade5a990000000000000000192c4d3f307db3a05000000001e6000b09ada6159ee6cb28707c274d9c18b000358da4eb4611b4e1b297b24161e963320365c28cb2e2936309da7e740df8a300d63ddb99672fe89c67af97be8f469d338be90e0027b0ed2e0509f07e49e4661b773a404001c75f8ccc001516cb0c14d30b73a0021b800000f24000000007500000092cde526c931e2eb1eaa214720008c90d1a222d28a3f8fa9fd108003820006e9ed00130dd0cc20011d660d3173ccf60b8001f60000000044e9947eccf72230ced0009b9454f8b051ca000003e166a5c9e01619ca858003df6e689d8f9af35e61c0000068b351e000040a00000423397424002a10003a4e81cd3e69fe2a92f70400186b293c2ee4002e3000bf183a0140cd952eb3f49000107b300006b12db71206000a215f7c8400fcbdd1fc9a0004f9000001f4b0b0b4bc5329e40006e558a157fb105e4a872f054c0039761ebbd6d8007f295c0015127ac89818001f2678e3800000001aaae1526554001cb6d484ddd8006bc665219897c4855633a7412000000003372640027b1d000270afe468bb4af80044afb800293000734a9b5b1f7325eec361ae000002155c05ce64000282f14ed8c548e000000002d90604c23743e00000000000784001f90006ba284245c2379db9ed000735db1217d33398b80000068c7f8fb5ceb9c82b814c6485d9a308f63ad98c038e600140a4f0003d52aaba5a2e540000083e000000003ce0000018d7b6afcc98b5000000001aa48c3f29397b0014fcfd0f549a00000000000000709993a6dc4ddb693e842e182a732850000000000000b02d90000000000039e6340025c000001c08000013153b9e50014fca10003e6c340017b6e2aac002814283ec0017b000000a49b747a000000003107f4e0aaa35e6a00000065ea4de4800000000e339b352aad3fc8d3ea4e80031f71842654a89382b5c0011539eed46d8004023f84a80099600195a3f3da56c688006b65cc003a92de6ec0000094b2940025980400000000000a1cf28005ce000000df680a9c001733de9dc7db0b000001c6000000001e28006d2000000f9000dfc0035614e90e7e00000057db55112be31c001c149a3c54fa892daaf5cb997430875221874270b477c8f93ee5e438df806ca53eb0da0e4bcb68fb3c8964a991964c4843e9d5902a6e1bba91baafde3ac988edc52e18d27e4a85e8bb60aafc7e93f126808b0cdf3b8c04bccb55c2398a0b081b266dfb99d41820513a11000cbcbdced836001df913000001e9c520003f4002012420018e32a152c7c79bfb9d68c1f899982e00109bb96f2001ac8c7152bd4002f845e00155a35406c34d10e76570445495f0003cc0035540a0010d8001dee8ca30006a6d70f29a3172e840017b7ba001ffaa8000634c69e22b6c680020f8aa80000000000fd4cdabb4be2646e8002390c00010d00071c0027e0002de52cef90e0007288c5f2d94b8b7155ad1c2cabd2f6d95efc1e000000002272aa365668871f6fa4d8aa75dc001e2a8939a0000014580050400000000244c3889652eae1a8004066bd7e800802544df1018a4730aaa870006e4000e192c0000000052707d5fc6e00065cca8000003ad68c2936a3ed35b692b45247b97b43a8f80000000000087b19000a6d5ebb594e28c5a80000124c0010d2bb24c668000007acb4911000000a8800000000001971f6771c28000e80000000034a00041800166000000000003ee34adb00000180afc000000000003aa1c80023f000000000f416a9dceab1117eee8883515560007dac63586c4be8006ca85495b85000ee4000003b8000c7b510010bcf880000080c000002ba33a009ed92d30c349f37e63c57da12000000f2800266d4c004552a2000a98002bd3ecae97f4cf3ac78ade81e2f8f23d774d2713744d0003be81b918548cd5f90aa46000001ef70ad3dafd210003dc9fa2f4eedc400000000c5cf70000004d4ce11b0013940000026ada0002ea000d25048000009edeb2114f4ea4002ad91676c00283000bbdb88000006d550b7157e576078007ba89d86a671ea8fcae8f977c255b9cc14e43ea1c9115869367b1e5000001108000012123fd2c79c0008fa7e4231eca8cb53f2001d6b2535aa3c7339e1733ac96b1122e000003e911a00137bf71c6001a60004ca000dab176323140049d71e78ca59632dae5de5a2f000000da9da0009380021d0000000000000077ddc8002547c19aafe7fa000002d72b035c002070006a5df800000ec0000000000007a0b31ca3dd7e000000734ca00062a00000487742eb4004a53d6505318003ce83949935000001388008262dc0037371eb0da78f96d6f75218fe742c38c38000003880000057afc53a1764a25d62c0007908e48ca4191a93caea076b70de8b8000003dd08800000000aec7f1de824001dc3d63451180000000078a595c07dc000ef000000c68003fed24000000000016587338f4b586a2f396df5e58a722616000000000000000005269340009f94e939049377c6cf6448f55fa9f878b5143a000a013f212002501cb2ca0000036a0000009ead162f3f50c0009fe2a5d09218aea14e0a098bf456108eb26a784c08f82272057787b4cae5d71cae8970dcefa3f1ba3300031f67689c00375562264eb14f1cb065372ab2c8ac60c8005905540018a3733840019b156f7c003b036231d32bdc90ee3dbc95f00102c969b4a166c58fcbd000f6c0000000000144c55000000000006b665212ab126b3840018b400355223d427544d279c998e001d78e729e9d45e47f2ee0000000000065d688003ceb892b8003320011bb6557b2d46397130e00000451994ee5e7ae523cd44d69df51a7a40026e26aaad54a9f5ae3de3faad0005eccccaf3eefdcba94f68a48c9aaee4eabb45309b0000017080065662cf93ee922346208005a2d4c8f3c72b83d40013c66ee1d8594b476558000ed6c4000fd8001aa0016e4ab71e000001e944ee68c78004b8001e38000013cc0036b52681000488428884779ee1c06140018b6fedc6268ed2866bc000004209200008175465800157a524b58f80045eeb663ba415cd89ec9f932e000002c56fb4cc7a4312a20000031a4ca39c00000512000000004fa810001732aa3d8000004120026fd312d2000003272ef09cc78003460027c999000002319fe19c0005f97b0007055f8009de8ee5bbc9290000b59a900000000000932dcc000001d30cc000df000000001a049ab7c00000534001471410007dd2498b30e000000008bb3ec0000000000134a8d0012c4ac23212e3bc8a2363db0ae489eb0008bd4980062ee8cd8979000000c5bf539e00165ce500000000217000bb601a25182a25a247a0000012b8ff67a001548f569ca9c001a554e22cc39ca00108400448000b90003b300000057ae5812b04cd2211ca4cd9db8986e001bf9990008a8c489d5263240015b000000000ef326c606da950aef94ad0003c4be5688007c634c62a87853064bd80000000137c9a64a554f08eb0cf004caaba2ae6c5cf23f7dc7fdbe16154e000788003820019db713229a53496062ea7c959b111e3ac0000027ed98ed000000af400000000b251f2726e31740020c000b14004f8000c0e3e9b10000000019f3e64e977800152000000f442e00000000000001c2a3f0009f472a3b9aa001ec9c42d23c5bfa662f09351a89454a9c00022357efe0000005986ed32b5d1840000000058b3940000055a001130000005354495a3ab0cc000007bad655dad715a2ecfd8000000000014340e000b395d91a88dc2b6971e0013400057acb80032f00000110800000000ffb19000e1c000004ae00000000000a253ead229b2d627b8f4710652287157268cafb1f6aadc5098a41ba3b5a1a1147e375dc8f16201c44e0f35db4d8b7a6957e8b5808b58a23ed6a09971eaa186aad32c68dbea558da96cd1cc5582ac460c2547e2c14c8d1382be4003100f2a7dd5c5734a6088aa8739ea14892f356eca468c7932e7c4588de4f29fddeb1b000cd078b1f0006c4fbbf1594a7cabc39a943a508c0c00000080800a2302042bb00000005a9c328a2bc6e0000000000045b2323a54480072c83a2f4991de000ddb0100068c000ac0004840016130234cf897a516540e6b474aaa905fb292aa504cc8f24127b92c9312e4959c01db1f6f8e7c800000000000000000008b21d4c44259f8004606a0638006e0000000005ba000f7975000f1d6da932f2000c5a570000018b80019a001b19d545e6252410380f4309d3bf000d94000002663bce4800362edd3900000063c5ba59000000000007240024100021e000004af0003bcf853b00067e18a2f1de3b51c800000c1c7622735625558800000001cb8d74c6000002e0434664d691c9fa52500ac06a4000ddc819e83c45cab90acd0d31ce40006840018991ea74001f90aab26639c14f2000fc993a8ae05f49e436226ded8df37e0000028c0010cdf68000011340030c2b2000000000008d8004b5000001c28e538283170b5ba80000000801ac6509fbf875238c7400036e4a5da8001ceb64e680062c001138004aeff473a77000000000000000000023d752001538000003bc0038b3623457f9571ce61d0b2311233e4e6a3133acae8e2ef81e001508002064e59a0f02aa5cd65a0986e0014c0cf0000011faa95df0bcda00011b288001b332e50cffc95001280000002bab1c00187000369bbc7939e0010700067e0000010000052de28002e60010131f68efcd7e8b365298c001b733e000bc8007fa000004690004fc000006bd24e82aa345a9b8a595d3de724000001deb8400000a02df09080000027400123000774900001a273c001c15c684606b790000000029252266000000000000000003543bdbcbb90003640000000000077800000d9c001531d2e64c480065e000a580051200069d0971e43d8e25d94b2443f4a0756000d42a540a3ac98d150009fc6227d0000000027098896ccba3135ed04000aa2b05f4004c129e68e46a680007053129f436000002273bc0007e800000a611980016a000000003bb37cfd9e24ea294651f035e001489212f2000728000ca000000001cb294000002da000a729f000a28004655029c40023619a858728ee45242541aad00000000000000000b88000000017b17b000524cb93a00082c001c81b6000d4800422930dc9d5176504001ad0000000000028a001c78000008bd3fc6f3820000000089a545c110a10639800000000945e38e777e001809cf98200188a9555700874aed6801dc509550005c8fb8002aef1cf29c38c29958f800a22e14001359aaf487a2c521a55144800000000ed1c300103d95b7732cadd289be78e001cb8ab8de35905aa64363400035b62e4d12a0ed9320011b88b16e3951daef514d6d5da3d3280000017757a88da180000031c002d2000000000006973290920e330485288003be001dbc041ae00113c370011f4bd0001f6c056c8dd6e2f7c001e71d6badae800670d1caba2d27a000af80078eb9623800318001919f83aa00071a5760297ce68004c2e9e2040918a34565a3531ac05c29eb21f3161e2db78ef6cc38df00065c84885326844820e94f8298000004d2524001f77229087f000000ae564a5f3aa3b2360e3000000adba31a6d42391662f6b822188f63ed3d1380069c000000b63c6001ee9cd51b1bc6b000000454638ce1852bc000001ea0004a47348733e13cb73ff16c5e38f6068e49991961aa8445800000000002077ba000c2cbb50ecf67d1eb4ce0027d80013632cb3a4d6a60016b8003333040000076b14917c370006ad3ead16a693c000002ea3c58fc662aeb81fb8002424152a263a7e39d2080047abb58bb365320012cd111d6001b58bd45e0015ba3530e40d658e989f1f526991476b7d9595889a4dcdc8703ca8d8b3a0552a5816bac965e68cfe97944c29cf0bc73e27c0da2f53f20008cc85526525a39270000000014b8027c52e19e00064597a635af09e08230382ba9ffbd32ad25c998b90dc001ba0000008bcbaad31b8f5da0b9765b01c004592f639caa800816ff6639fd7ee865428d926c38456c2777871e13ae35b0001cb80045a3a85989d0000006a000482314001e17211bdf1a953def247287c1c2491088b53b67fcf10000009360a00000054493b0735eaad44b3b87800000317000218678000009c000000152e15fa979186dc4ae8547520000046d000bec000009b25ec5c8c948e0018fa2a000001a622568494c74b23000001f431f7b20010ab42142000a293129c3f0dc800390a19ad800000658004550000022e80025c0007480000000000000000bcca18006e27f5d0309000435869551340019f9491860004b9460002bcbb343000d755e8c7000d6c9f8b01a2000f4c43752000dd9f39c326dc4bfd6f8ed4daba33ca5399221227e0005f0bf1be001f63294c200117a073828866fbb718e36465955865305319b97067b8000d30000016f80076ede8002d9a6641ccdb718a2c80aaba83d8825bc9534421d45f8e5000fa1f8aad21a000de8005b200095afe00018cccb7151e5086fb715303a13bcf070ae8c738001a600180d210000004b80000037c004d2386b5dd1904001304004e34c6b94dabbb856000ce800001294d7b6138e000ab2728968440000064a5f800000562fa555a2f0da000e6a4b84a00116281000a620d8c5000a44003714c715c000007c2bb4f238d4b30c523cf93247540031a0005f4ee3e140aabd56b3985238c6d2750004dc4943063a49586a32000fd5efd074050a4e1cdf53e224a095121e5bc94a8b38239d22b7f4ee3d0aba361fa94d17a770005fe0c800426ff80000043a511fc4d34c8314aeb9553cd7054c1b000a1d49c8959e6a86390922c5551b1254cef5d42b3148251c9c80067626c0000046a49ded800000f7494adb0007f0dd800650ad8928007f02dda9abd3e24cd44a9f310b25f4a4b9528a8e33dd34600230cc1792d10000006120013a0dd32b2395eaad0004fc718e52a8001449470004d4cb00049a398edac8000591b9800000394688000002d4298000000000000000102c0019098e001b40004832a0000dd6cc000af000a220021c47f1e4aa0b80bd6464cd4c80000027d5741d000a840016967a00051a2f29c5259799f000c9a151f340a3e5e79c19c30dcc2ab14427ba66c070006b10a000204dc4c2af384f105f0ab68988c11fac71cb11d0d8d37903c5819c1000000a78d012a000421940005d5e4b3855eaf45747b286000000002828c4ed99c2cebf0d613a67a0000000059800164800000000002ed5da4ba3fd09782fd99dc076e342e528006d4000e78000009ec0011554a00117bb50003b47da1b0000000000000033171c180000000044d6a6614bc1410014451780063a665bf80000000177bb8852b44668006050c5dc9874eee84c687f5e6a2cac1c122e79db89b60012a4e0800000001a845a5848150a80071e54c0000053e3900000000074dee2270011f62e80060236c6d9311ba0000000026e000001750000003f9c1000000cf8000000000000072243c0000000036d568000011f51f16d534000e0bcf000c3531a573fe001e9c372694c40011f000dc50a8004ae5547b8004165bc0010a3c2bed4f80024a29cd1800000808000006e6ce800133476c7e498005a6f0400000886704e095139f12d73cc017a650399ff570985578001c667dca91c1eec717618792ccae1aae5390eae6180061e2a1f20001a2000000d361600059ad10007bd4eb0f152ccc43c4b412e5dd52ad39aa06243ef35254e4896319cb65e7000536ef03c8ba5bc31d613f55ca8940000076ecad2c9914fa4b4000df402000869c588636400219420f7d070a26e6848293ed1ea000a88001c40000049d8c30dc61c9b000000001c06cc0018fac9001158f9c9f0d62855b3a91ba515188001a6345bd8003da1b99eacf0c21bcc39333b2d6da9d3819acc4c08b53e4000001052a4bc8c38005a000000185000b64849c400000075d090000012c8d9000000000008606e580c677ff064f120f4faf54a2b53292000afad90009109697544ede5290af000e1cc68000002c27d80066e62c6142d53eb2a0d8001ae8b274c5f512d1d92c1f714000b7b733d292163b0e0007ac000001c2405b3b71432471c496938e928682d697e6dc002773c250e30c205ae000db8005ea9ad11bdf0000018793f57edacf6a0e77c2984694376f264f2890702f0cc2c2d6e2bec00205000292933e82e637cd9bb9364dcc9192b00081c005064671855d9293bef746a9a163e00159a5f0009dc0050f54e0000025983ab027fa511820011d80022e2459bc61392c64fec3786f0300000053abcc000e023e7d4000e01ba6be1c91c9cef11d20006b6000000003a64cd60bd71ae784c9bb42a28ece339748ea06142ef8aa6ddf1a0244e0005c0000000006e87d46470cb0aad1ae0026fc8d000d04d9a8b29600068941106000000df42698ca8ae30000006580056c56d67a774cecac8c8009522a5372e536ea617c86a00000186b7b3f277167b5200059c0000088e7ec628005f8850000df3fe001484f0396001ee8d955a508004c92060015e8eb18e000e0959614d245a93116ed40efa4b194c7cccc0f80e000628ef1fa002759975da0019e90d516000002330002bc289035da8b80027e00060db9c5d0013e4002a72eaa6c79c8b388705b29ef212dc442a576213a913a9300117d58bf1000af45e18d69e4d53abab752afdce967764001c7c63000cd62618a320f9c004373f6000afa4d0011746f17b602a6216c87000784c6acc2b6d0c38b951ba2d4c3adb59ee3d95a35000de9e7183000355958f79faa6d37d078ff094888003aaa9da387747e49dd49401ba000fa8002a0c1d268005c3184748006865a4dcc613d69e15d0bf6d25600033d386001a89174a8a144d9bf4e2745688b5286ceca4a022ac001a0a876ce00000000228644444eb000001db90d99e77e268d152aae0488dd62e00119a0977297ccc9861a636c0000000082c004df000001d80b75ec0023b0c158683ca1a073fe614001820007840027a5d4b3c678bf6ba002020c371e000bc08e000a4cd988b00115c000dc68e5ce5700030e825e6ba1000a1cf151d25892c282487eb01204a2f1624cd33b51732ffc728002433649894b3f253c000008cebf80023b000001458dc2620009ea091b288c7d9d9000e290a00019128c5dad500017c0042f00103e2a8001420008f9e70000014988a0013f673b9a3d600126000000000001870002f453800000345f880000090c9f8d333eac478b2f548784cfcd262ea714f927000afea3b6b2ae000a88d3000c144d9b9572fdcd190d8ff07c8fa9a6842b52baca00031e79b29000001438007bf364839495cae1186a670012048b8db846e9c8e16d000001360006b252d2fa3d79af5ca7b1932e95dda9d921a839c797993625e1bacc37a358c78cc4eef7cbba8c57aa4dbf000132001fe9710000012580018af44e880000044907bdf2ef0ac9cb736ce000004535f2b5c8b99a7e247994b083023509524560600149a092606bc002150000010380026a82c002ef2f6000001ba24ca68001c30000009796f62a65c818832f10e46d0d847b26534a4962301295a7f1ae9703f800000d34af30136e000000d34ee00000241000000002130001a1089914e2000d8937870e8e8b1e529ecac000e7436340a5ae300000093800000344599b955a73cbda9c26e00289b2127400104a8315f2fd4c0000009517a9675f6345938af000fc6979eb56e001d58007aa23c004fb21e3a6268002c25c5d8000546001cbccf1b2000002c2152218c4000000000000001771244d46c98e0006b9d62bb155910e363e000378c55a20000043f4c2950000000002d5cb9de2c6dc586add8be000d88eb0000007c96c19047da89e018e27ca714154a694001af1830fc0000066ad4e3f8001a2638c98cb6723c6309a871f0ad3aba9000001730005c631cdbab32b088c0022d5ae0016dc3724e361de248766c297080073eec180b79920fbc620005c600108cf42f00000036528213c0026649467d55cff0005751d9b11a2564a48001fa6e5de9b74af00d75be74c52005ab858d66053ab1f328000001e264aaf5bfc6119ef2cf5800000a68001019f62828318b000000000002560010d93333232400107000ab467b9575a4dd798003e6254a4ca517219cf210400035cba00022e7bc4b80070a62cadb176e62c0002876e20028abb918f296108791628c4d88bc62a590a598181a81e9ab1f65e7b499a53000b259680079e998edb033d2b6ca1c7c28abcce5a6128c754e693717ed9cfd24a3770018507451e3462e9e712641d80800000c22449c53cea6e4cd3f120a0625b2541f3a4002050004492b92f1f60000000000067c0014d1ac8ee2880039e9dc650d30000012c800001424fc800000af4004915d8fdc3f3394ca8691f9c29c8dcc5134f102175e89906ca00062bdb91c47c0000090c000af97b23f1692099d71e316338bf7fc525c32130fa000000001f60005ab4d8c90dc669c12e6260590005aaff4003c7172000000006d2000001cf5533f4519f537c5b4c58cd2f2a464a21742312c6abdf00097e6f0006bf33da98d155eb5c001d04ef03d2b8c727a9dd883f76aeeac63a1b76a0004eb859165354ecd90000005994b00130513cff34ea46099cd32e41ca7bb9a60000d991b942704000000001d9b8ca31a62fdfeb65000d30003b90006459fc8429d006408004f2ea4004b41a82d456abd0003ac0020932870c839f05628a9c78e7a76a7cef80070a85d0486d45e7ac0041551234d3ab1f3aa83ce095b19c6e59d8d1000438e694c56cb1427000000ff5da9436b669457353242b5c0019d45530d27d235ae29cfdb8300075c0000016ad84004f53ca32c002ad2320023c93f5f2c04408000003ed0b9280002a5ed2bf4de00227ac919512c002d5616002368005e64c868800818f7528bf100032ca31452084fdd0b8f292bd4f3a6b41a9992fa890007e46700021f2464ea935b400094b7e346df4a4b185ce518c7c09660c3df8c4d836f7df7cf3792ca4689018b0f69dfb0d6be920502dd8d82a51788e62650e272da610e00821e51eaef4a392d57aafc5a8d10000019580067f2ca35800584d6561b652f707c3e8c75ea000b0aef000f9c5fb1900034974c890003c4001c13e2524fcbc77b919c68a7d142dd5700ef53e4dd2cb712bee221f9eb124c2ca8c8830a920d18771caa8cdb07211ebce233f16b6aadd6c7232eec5fea5924a194fc9a5782a246387f57e324fca5d59422d012391a3365ca0be6e2b651f9873d4b011ea775ea344dd80093297d160005ae838eb9bd1a2f7cc0a230008845d3926f4a4e1f8c923aefc62d231c64b44c9cf6aa3cc0036441a000000001a08ec000005d47fdc8bbf798af60f8004c254c758e50006ca85a4468a651e38fb3dc448cfcd37605ee062cc306000a194b00028cf2c5d62a00104a21a16a95328007be2ad6d80051329c4a84d000b04001964765fcbf8003834d4001977526bd1d80025a000002481a00006ccf75d4dc609c37680525739e919a305319a81da75c9da4f7564d4b5a0532e4ad9328f3f26c5419174a8acd240c50b66c5a50e95167a1a337b67b4b44cc9a668e2534b6f166cb400000000b95481ad2d4b75289f32fe3ed103852e233c002750004940023141eea614a000006085b8007ea28cee2271de31c002bb2ba000971ee1743b4fe95700061e3688b00026c0000055b0640046118ec840013f0000005e22f0c8000db9375ff4ccc380063e52979abd0d6d395b9a30012943680000137899abd000884c698e412f86a4b5b4d6ad80040900043e801b1000000001df78e98da080035e00243800000000000008147de44a850000000000027acc8003170005a65ccba19c2ecd78cc000000003e958b028000005449fc001090008a4000b1000000abc15a36001a9b731960021b8007c717c001316e6bcc62a1d2c2000000001127acc393d000bbc4b95528a36559c397e7160cb96686e65d1895d34709dce4fa82f09400000a74000c38000000000020735f4546d89762a000001b986e67c00000000314e78cd87093c0000077a000000005629d5688c74d2284000007be0014813760e50400179136aa40008100000000169a402c9648002720000004c5da935db9c017efb1ad8b55020012d32d5370a8000b7a22f6c840002f20004188d472dc40000000000186ab3000246a20cb51c4e5d98005f4b8487925000d1400149152000dca540003327d3f164800050d3f0000010936100000000000000f4c95c377100016100068240c000003d254522ab74b2bcc0009d3aec693bca72aa00000000354f70520f18e657c908b93ae65c6335957e000000002fae81ec906556b3531800642814638002e6a2469c8492e81de6ba14928be4f80072e59d9244117e002208c3402b21e7293590f893b91f0002bd22a473826097433d5d50013fa7810a376638c354e0005c2b42e26364e80000000000000000001178000005e568a390feabd930ae69e0000044b9761bc3c1a383e545e098547c81e539433fa0000000089a9acdd9a54180005328728c291929610006ec6532b17a9bc5eb2c30274133b564ee001eeba711c8ae42a0783aaf635b5b31c52cb992a236b14c10c716a43cd78008a4e654d80069ece4a404b0b2314e9c21390000001ef30f454348001e6a8945b0b000001419e438722cc246661b184311cf950f652c9af288c1d26bf1000dfdce3171322ac9398791b0851e8cd34b18dc6cd96b037c8fa4900122c568c900062c768c19b01ed75a3f4ff44463a531825b4bdb803c2e196da72154dc8d293b6e25c4478006e2904459221c6e85978eb76124c399a70012b0001190002f0c3800000b5d04a9b4c6a4e25b2f000772600c70005f5688c543689d8489b2bed24efc1fa170bcddabd3ca2d8dcb791723e93bacb276a25c14979d6a1d2b8000002d4001cd1120013100086e5bc00196230afe66b1f000ffc000c533a00177b4f39a394a1b979b28fc99b0f37f21c63bdb786605bcade602d24002994bea44578000002545a97d1663e8639a887eeb4000000000000036a3d2002379ed98aa66500c7000ff4748000005ec000ef00000050a7518e001228001d2000001316b40000006180c63041800766bd4dd3dd1cac145f8000013bca38005448705b80048b23cae9555f2434002f36eeda1fb8bf62e82c002234ca00213bc560305062977000000e4c40000000000a90fb14d7c87d00000000000156001300004fa35cc8b3b3b498479be94b2314000c62926c5aaaed12252800000000b440022110a0011180073e2d436bc17427ca25ccd5628556c94f8f241ce0b0b3beed50891f8167dc003e999e12934ab64dee3db8a7e00133c000c59d734a48a5341c994eda8798c9215795d0000009a8009eaf39758003ee8009397859b0352f8a729c7559c8cf18b2e541800000af5d2357000c7c0008b258d6c598000002d400119000001990bd366cb5178798d23fda8bbb000a44cb80053ebcda9b0f00000033a2f764295b33976722f5d7800000f40c036456800071c232aa2a44d8000d8000000ef74272c0045d00061e6dbf8614284004cc0005aa01ae13861c40000035a310dc8002fe000a3144000000f48000005b40043742a001a891b000304004460aeb4554b9e46c7540000095a000f080030ea4c001f727e55e21935174daa2e93345eea5c6aa990adc5bfaed2031cd7c9822cb33d0589417e002571433b65e5cbd0b00030cf3ab61a2000f82a9000338d5aef000a14f69690004e6081394ef2edb8aef93259d2c9289350349caf90aa6b658b6a316e6cda970992b3e061be5ae6150aa5f16a2ec47ab592e8a9448bc5428fc584c50002fd0b800000001ef80017697c004ff4aa20c001d32ea284fead31df13c002a11468cd2352025800248b17742ed5788ef0930dd150eb1846ed108e2000000ff8ca3e00023fbe92660009d8b511922c003db40625db2b4017e3bc0017d71e29cdd92d000000de53345eaa4581305ae0019e8002e2a5a2280000027c00359000a340044b8020000005f40e3065cbdd4deacc0027e7c2b84fc94500000000000000cec0030153a248000001820004db9c1a63bde38af3be3be029bb6fea5a961274b30040032500000000000000000c14850001dd3ba8695c574c10001162e4003c57b2aac6d98e60704c5fc2b0000015e897a762e58f8008be000000bf9080000028a000f8e3f9432e4000b31c318077ddca3616600057b651c659cee910000b3c4bc31358001f43988c279c001992f60013ad100006145496e6926145a80045e5a4002ab282195abbf81103d89bb3585b0fd4f8bfa405b0908002e600164cdf48a2cc001140000014c00048e2f28b9f0142000efb5d0009658280008a0022e4d962e0005f800000dc400000346824b8be314edf48fc1b8de0000027b1d25ed79a6e0bd2a400000000001938486dc6280014712a0017e06a666d3cc9a7b000dcc00000000b958911890c2dc998ad283444e0b733eb2758b484288a4d49c5316e000bd9e53d2da40039e13e2663088944e0016680017cc044e10928820c8b8758c295c5a80058e9ac000001b08ec8518d5f800162afc17a9dc4d2fa506a5490bc1232f1dcb0bb000000000006b87ac560005c86dc00000000000002d73ee71586800000770dd1433866452a22f0007f054a773cada80000017abe4519af176000de80030e0009b8008a051e3cbdd2ba28ddf91715ea0611aa56fe5cd0893f71c5d52bb173e0cad5389514e73d4f28717838c78b732ba002629558051fc9311e6ca001d7c917a800185137000001df0007d6dc4004c769a97e7e8bb27ec3174b137260015b89210c001d0c3a6a6664002b164ad552c80017800152ad194b0f1050b816e0023f9eb62280e7c80089b424982c7000754e3aed526000001cda2b2edb88000009dc50a5112253c3fbfd5ceb445c8000be935dcaeb000a9ea39433aa000d18009d68bc38c1933931cefbe10001b60698933e874449fb134754c42e7886a845500008e1308e9ed0008fa1b953000eccefabd31625de5a8749f4540000030a4f1108b016f31cb9be80c74bc581ff10ecac3f800001364002237fae221b8000004a0000000b22e49c08116744c81b8d8868391298970a2a58c88d3dd185c499416677cd4bb94420005d13383e26dcbaa643a1fc000000d0f19c89bf73c001ecc9d00043d1d97770e5ee5999581c2d4edb834522d4004160b8ee60f8b14febb0f9800602001d4340000000000004e40000039d24a0000034e5e6824eaa9f64a2d5133ef00000000000000001195055ae0014fa8f172799b2d09988000001250000013a8002a2000bfa1800061dd0bc04174aa3fae350a6acf82b35581e68f3d3922824d69b12c65fe7188c25650c978a910f22c002bd53ecc8359424b22c44fa732f089e7487316316db3cc96e2644669002482e03b1551704c49e8e20a6b5d13b084126547d92133e7e4000b5a2a8eca5acc0000014396a16aabd41b8f71f47c9e9f153029c001c94264cd10b075dac5ce98cf16ec4c230838620023a9ab0006f00014176245528c451561bd2cd254a24c55eb7116a43c5590f2627e642c615b0675bcbb216ec845a9d9986c2dfa8a687c284459f66b21f5090b66564d4001f957b28ced05b2167ac0006b2f22b53abf148f1e5a7b5b13a9655ebc426ac5db2aa960e44a872154a2cac000006450dd2ca2d957148f23cd6763f58fa4a7ba2be2eccd50e93555b083760005b000000df0b200083270457d2ca0c4f0e999300052c003b72feab49fb654761856f1720009d40007a4b2834699793df10c7a0bf9cae843ba094c2cfd3b0b3000e645aa2a000479461f5282e0800301001001259df16a000478004e62d4d1c6339a0006e90812a9c904aef366d0d13b11362b8df62b41e2000c3a5910a000001a3153304001ee142c040034e0011fe3db6a4e10240000029121d1c98500089e2f800232616809b90002914500015e514c7400736ecde0c348cc2b565a470001c43a12e778b9c5a2a1442591a787c152fd16400071e2b5d80000fe00000209000000000a30009244da9250287d73baf00047c0030b2ac001f43116571ec000000007d4cc34329e001c59af472d957012f286555b89c12a242c0022954503e07b999225d8003ef0ca00059b7639af88fca6e16ae6ce0c312f024dcb9bb66600154800000ac4002db8b2001bf96f6ca7b40044d1e26b0002ce644b8c00349534aae26b1780a63da900037698e0e1513e6a54b5aa9000de652abf000144003df1ba94077c4156e000a052171e4a05910c1242ad259bf0b69f5acabd23abe44c9172f26449f8780009dc8c8007eed6cc380031c5740021372e8e4f29cd65aa1d4dbb79262bd1f95f5e2cb8c292725709d2f0a138f44d4ca25254a4caaa5c852cc994c7f1366ec4a929532219da9de16298d242c191333c4d0a92bab94c380001743db99b586e894bdc7804e22d7a90d286a25b2a432c6a41878c1840110d092a65e369029c156109537b0c390284500810d69fc999a323691e289311b0b951446a15ec042081f38c5403fa0e0dee3ccecf12326d11c0a956d15c238e909e1f48f93139aeed2cb0e5762a6309eb22c2211d9412e44f44d9947f0d956dae10f24dcd2bd376aa1456b714908c552277963086502269762bc3896d24ebbdd79094e4824ac0f84508ed1f09531625d03a433a6334c2bf50b061c9109065a4fd3008b0c67660b31f79ae8485c2e17eb1967b2b5b3474fccb342c724da3658e2c7c56a8f4feb6c8986d4f67fcb8b4f3b73b464c225d05b1d1b955f2985058ae736914743417e22848495f3f278601c523fedd930ab96229106e93577229c3389e634fccdcb3f13474c7cb01932a65874b3108574c092b14f45461089412ece25a3c70a98879a7726733cd88974e2435ea9340625f657a7776e2b46d11d0865d4849b424eba6028a72202763795a56a975582176564b52cbd818819c4cc285b6194549a1164c066ccf741e244dbcb5686b9d3e17710cd461b2593327c170aa0142f5c353f5242cd69384f61a9643f13138338cd1b1d1525048383b3661dc2e8a30da790528ac30cb8c5508d2f63749b8ab1f68c50e2e72e49cc44a261c538ddc9a952b1d8938ff3ba5a587a415f0fcdf40a92c24f8528212a61a93a0602324cdc19202ee13d204a3a6668d95b3b5ba8f61995b7a284cd7abd3ad33c55be8676f4c49208530de953d314764dcdd461372cf4c39693506dc910a93425f4963272662a544bdd72e414dc2570221f04a8fd72e4b922ba1136c88bda5f11a24cd4aa79e857e7caed4dece5b7b9d7662bd8bb4311e45522a89796a4d450aa75627e919311064a9449e406052450b164ba2a421101106dcc3289a8c428e5c05603b014549096daef9728a062869dc28a306e24113a512ba1e433a7488a70c6907323229c879396b67a488bcf51e214c893127425d3a8a935e481bb9ff5a86a52e88b6b72de28b97472615fda2f7faa942396f5444b903abf122fbc9f11794a20420ad741ea754789b016c78b38a83541a120c8445e4c53a98a372d6c88afe2e8760fbb2b6522fdc7b4935895d3ea987bb3889a93f2a24f435b850826445089313a7443fb5b142ebd12bfd22657c4bb665f2aedea85b75ebce2cc37742b8c5e40577473c470a162a47df0ab883ca2d16898532f2c2aa8d6065dcbab0184a215031552f60c5c045f56730d2539747e1ce2c38da02710b6a210a290c2d41b52689e1fcc326e614269a30e257840af72865eccd84c0a6bc49648a512a7c45bf70ecf4e148a10dab2d789dd6b249cf593740ac99be17852f0b8533640cebb5cbb5960a27c4ca511b498913aff44e6e1da9dc11e221a686f864744ed88567618d6bb4c70a6bc6db1f25b03cd0a3b13e4cc3c8e1146d4637c77152a0cc81213ce8bc95c523220a451a1f2eac5c338a50d620d852578c2c64d7c4b1beacd5f9cf68e6743eb8f22443630a8914293542b2f65f024aa8690cc26cdbabd37294d169494e9465fe8a36484e99237c278e3cff099042c1c763a735f0961309c2e2b65038a433a61437ab65a22544694f246d943ea057a6884c1293782d440d4ad29e22556984232838560ad06d09e0a09d778dbe0fa3b86efd4dd8c90bccb4db8f4080c7d5d8a138695e3fb1d0c2252062306b22cc4b96114647c4bc4507a665748412625e5b8a2937acfc432113467cd118743cb474814a5a5ef7441c06530b943bcc54c2a4def85908e1acf79732ee8b5fe9f197205d0e9f33542850d83a9f2289749cf2fe82521c9f98614d4fbd12a6044db97f3e602dc888e1169de998974c70a4da22878a1b477902116c804dcd33221fd6592f796285809eb6f27b8a48bf26e81c4d9e32ea07c16c2d233234f10ef0b6c4c8f09b2502862a29330412c37a63724609d08614764843893b08e248a8cdd486c1cf21cf0fa98897a07594f4c5d3df6cefc5d3c5308cc1cdc1050be050b60300987b985b8d5cf0c06abd130eda6854ed67698e278a0206c14ba867382314d589b34a89d3e8913a86e65d9031f00fd1c0521064fc788227ec6fcf98b140a8fd8fa21634e0e4632f1331862789d12a26cb38893f70f43bb8771ea9c229546602268489f7d8bccd5341048e6e37b683685ece99c163a1044d4c413670c32ad72c0b68cb8e09ff13c2bcf3896184698781cf2966085d6ae1f48cab87bb3c8dbb618cd24622b235e62787686788adac7ccf95173dd7c9cd91284c31b17056a257b9052aa68d109dd28626c459d55de8443da932d2ba4878260f61c5978554b43ddc685b0da2694a8c211e2759089712e9d62b87427470e8f11f49f304ab88d242609d4b941321a589c8944f30cdacdf14269c14c275d6cc84723b4266c42f88841c43d6287f932ad843813776195605170b60f917a878fa5ec4bca70634560dba73623bd8317231a2712727e4229164890976e22dee99b44f09e1da4d53ed0c5f26b3f67d17089535456d34b1d416e5d2da3994a14824c3a4fa26c158f92471957389b12011d588f718a1703b20c6e24c83308b752204ea9a7306171f1095692778b6883642d88b3a3650a0ed28ade7434d2a6aef43e9ad0398089e526561914b21c5652bf42214049856132cadc296310cb01449c75da495639c10ce2597f3d32fc89830c840f23622ebfd8ccafd179330da731e287d94c25c132f15b06b82c93c66ebbde0a893ab2fcbcbab7ea7a44cb7912e2652088b4e24b47dd1a4e887449aad07a9d0890553db384163f54425045f3534664c60a97b28b3dca688d7bf084488137e24a07dabd6e65549ca046ce165318ef5b4b745695d8733ae6d92d35e08661c3723647d583177fe2609ed157b018e6ba9912e13cf10835eea2934ba372ef94723fc8c143e5d18c426f86488824c65a544a3b55ac649bb705941fd6a1d62d2ed9289071f0a2c2989111a25c4a8db2987f4ffc7d3823147fb581ba76d048918e91fcfc9a16761dc3e329112a1db2b8f102d38229891025ede18358280f05d2539dcc3e3c1377d01ad588df50af9c4aa5c6f209583a851282d408195238220ca1ed584434891e708ea2573ad75ae5d89401f12a95d808134a658cdb9b219a9458ebec2720584908b964cd0fba89802bdc0f80526a255db8634840fd39be590a190b4a7111e23d424ad328c6165a5350e93c9792833f4e46616196f294b98614c61f5b54a526b520f2c9111214cd8ca539ea44dc83584e0482db2d06606c439b764f265f6bc747e98ddb9c1266a283503911b04ca9aaf26e1d9ac8798a476e3a933124b54da0741e2244edb5910c3849711f10622ddb9032e624d1d9b1832264c89a398b035959b310afa826c5b3ba5dc5043035e401e68652373419f94b44f30e0c91d26eec637bbb1063e41dcd111819c98ce40ee1cc958ab4134f55eb511241bc8412324acdc639f32a6eecb09cf83a73d4081c602cbc480cb02249ce082f8a606543c1b254964bdb03a7c245eed430fa9843685630e966699dc0c4d923eab24d6edc2aaad11e954459337e701d48acc14e22cb8ba933e7e5179d36e61dc940522bb32d09b1f67ec7c92a8a59f16c262bf0d2285f4a2145c42c2a19d5fc20c894e97fa4ac3f93762a2182ca2f36aef82a8813db215ee9f01fa1440c9200de794e0ad60843b86bbb723eabce40654e11aceab016d2bb47b4940e219d5883a05020447b1f1be7b48792b67b23ca8a6b10e1ed96b31282224ee88657e7e5569eb94a4f55496d90a22499bb951227517b9771eada2497b5c2f09cdb2b2f66ec47240760a6c9521a57a26a4c9cc54407544b4f0fe9894995e44276605bf5726030369a33b61d0c0ca778e7189834143444c7ac7f7821f44315b9221908f0df116200f09cb26ab842a4b78beaa5099642ce90649c990f2f84cf1dd1ed03c3d055350f342ec0f1a241c41887548f8c5a8837b4c7c2d361072aa5f9d036701fcbfa253dcc7d4ac1b656d549f9c17be8512dc07534518d686535022d809af63e77c3d36f53e12836c321161344188b36c20ccd1fa0fe1a027c27372a1ded9a14a6c344484370acac9b1738cc1ccdaca53421b440a4711047981bc75b41c869395816229c30850b6c3d298893865d4963dd5c08959cae649e09d49877526c3841b4d7d655e24abd3e329c3fce31929c600a9f52e67c3e98e0c46251da094570f53a8d155e5d49aa41412ea469bf81120e024a214fca2414c610f8560e18914a61a085bd9066f95993c126a9d1e38c309816d0b17001673538272700cf83495d106ff66c2d91fc1d4d292732d07d279cd7961c53e2bf2f66a58431f9c218c2aa592f29f43686f4b30dcca07166eebc4346c7dac8da79d5660c9c1bc1f0868fdec8874be1e44281b322e4486a778524a9f888609a04ccfa9e4b6280b69e51024655e9f123a7c60795d2423bde115926289c3d133512ac5109140a6d2c4192983233c2481149c01a1cac5674cc62d1351fca54c027a7e60dd792766c6534b3b9c0ced04398375148accc92881e216618d00c20c4263970ca524060618be20ca5979216fc4b89ef0b33ac249ed252076003b05881b521847782b4436b050b095e7e87118a2102d87f1fd10d0a87d85a1941694343b0f12db5b2f71cdcec172ed086978cb21e298c5a414485f090883656a64b88191067fdd81f30cf01c2587767d0f54b9b96ee118319754a2b2815be343a395161a50febcc6806d2ccb84e1cb80fa32c939f19220d83b118104bfa0984c3fee142ab7b0daf067f9416dc635e5a4b5061e432c7f53620470b8b9f259c309c743f368353a172e0ea8f85f2c8a0c111332cec5c2cc650ff054328800ae9c5269c16ab2b03f97b0decac3e9154431309685b57aa263fb2b07ecc8f03ee5b28a5d307b0e24d1628517926943dc013aa81c15b1d09e824b68680921843447e0feb662591f50a580cb8770c66b831b254d22443f86f48679c1abc90f81cc3e80589695c0320f44e16402a3b8a71c5c414194a0a814a390153303ca6b266b303f0296234a47a14b3fe14c3eb2b35e1e429921096ac58bb0709e88ca385926642544849072df513b430de83d3f87d30e1a4918555daef8224fd0ec61cebadb9ba5fd1fb730b2c503a034532144dd9b1010cd59facc33322cbd86d5c201236c090e2bb4c7a9f7ca1f02d86b5cf1843b87728aae5278111f673404b9f08208837aff79c1c00c04f0c25ad243db55a86c388653220d40d85a0f7375a3a4d2624b95883d6b61e5123d90d250d3192571c10c20a0706a0942daa98ae94db9a0f21e84d0607a0ead88998780ec6701903b0ea7bdefa2f4a8074cb9b40a62f42e27f2b210540a2f08ee542ca6f408ac42397b1faf1d64079a661b86fafb6220ccfc90b0f08983b8c806e18c3285e35e40e8583e0540ccec85f1560841ec611760d482475076f1179cc772e0b59e81d4af3ad922a90e6129151fd5b21347b2170e87088c1555cce5d5fd470ec165268593881bd5e82505a0a51f02e78e1d179ba70ca6e546c352f343c2bc417dc7363ca0507603c3386b03e1d8818430da15839c6932c14d2b86b0e242cdc071064ac572b8607647d1cae0710a4e0dcd90ea1801da180532640a2e72f61a81a1c769a0342284f06af0c15af60e69649ca2170c524ed17b3aa1386f92d0db0f8338740c20ecf7ab07a929c2d86d03e5e5c106f0dec4478c4316a4d514840264e20afce82aaea432a3e2d21ce349b402217a308e80e3010f486349e719da96106208d26c9208e1a059ba305652c0bae00dae7c390c770a13c0f9160de0ac2006d39a27c2494506f0003287134611d208430e21bd11a3f2569803196f0c2e3e3806f6de0c5108400b2ecd4503986e8be5e98a21aae5cba5c1a6e0a08d210a01c18686f0bc7957f1550a01b5394d95ab410da1a834e1bc358c427468c3595b25a1b947a590ce1646c8650b60790b4c10d614423bce25a1b55ec016143a00493116017dec86409a08d1d8d699eca5efa851e6f7c81aff3ea09c2496f46cf1d5f1770c21603686987aaed9004564093ca786d86e1b40a93933eb002e0283fe10a5110f2620781eb590b60bd219616bc19ca885d33a104360595561582bb8f4863ec3130920e11dabb9486e6664eb9706e13d2cb9906e3d40b83426e19c0684f046544fc84b75a79c6485b40e4960f82324ab94041573d6b2e88a0b0b216c3501d0768846186330e0b8d88596e6c05ee2d18ca9891d856454aacfc86547e1a41c2fe5da150cb031098bd4e7ca1592a221682c0be6dd73a873e2e987b80886f12cbc84d3d28f4d099b0b809c2c83f6fedbc179992f813832d2c09eb2cbb3258cc11c24c51676e5d5dc6f452edcdca9d3aa13cbec1e516dbd840d92b46b25299e9b0374229cf3226c63800776a31c318250872d8b18eb05909477ac953e7e40e05c00e184d88610ae6446881702e0f50486109841c24819362154149a15da8bcd9ba60c8d351d84309480d9fb8547a9149803d0be0b1d304009a0e5c7d052941343183d50e075b58862f617d37a8367a2421a82c096cfce08c22a60659486210a88cffad10b2474dbbad53e10e089f92a21841981f6b63c418b2f15617616838a481743c9db0bc1042c85f5066512b8453461808c85b0a6e356623b61a13de38375b43d86b9c9032a2420a070a24101d933026c202f92b5e60dcb42ed09aec1229213c22a5618470521796f85360699c2cbc42128711185560b2b81483561f0108991e080035349798de16412ad147af1db18295c7184d782994a10dca83b4a2b257c0594da1341583e5565c42d8050b6a48c384f89e04cee3470b6dc50d85205a57c1b0407781642b84506e11ce58570b33ac1ab1f20a3a41cc843b68996783309ab465e8590b20ddd0b0d40015423a91316b441e92f07509d42a514c259d7691e5e20693eb3d85a0802b05057a13c2bced04e05c7117b44614409a02092dc423849082a447ea26600054d184c47a15429ccf0620a427c2d2da4841aa590aa1002989735f154b5c1e1c28fdb18470760881e9856a6b84269af22e1447305108e0e0218f908ac7e04acb506ee40794f06e0fe66b010a613091b8506a8ecff84505b058f484f0820f423b3d08e13c5c8316ca0e01f4d96440c4fea0c09404d6f8230a28fd53ca502a398249b209e13c74cff3e01241e8453460e1900394ae10c8084f4d223c12b5565aaf42702f02e118ed84d762ec02084705612c1c84d7a60f60fabf0803380c2e308605017b2186e0400881d01e8bdf38150400904328308e2cc0a83d9ce7dc0d84705609810bb908a5b4259960880dd37015076434218d73831ac2504308a0e0a58d171e08cabb5f6d686c2383f66a1140d39e5ce98c2383708e120239c108aca4f5841404da4e782f0360c415bd308a094203fb01ef8c1b00e0762f4189d74ef4258d4440520e021beb3126c50da00033451c28448020f80d20d08302d7aacf05a0855f90103b08c170336946c42118a0648a41483707eae42003d50e6841b82e04c06cd0a0203e47c1b84005eea4128da2d20f4878355906481f8320504a81883332e0c01f17b0760d41607955ec740fc8b3966741e1d30040e41882901c5301582f7be0e40e83301406805810460ee413ae70200dcfc80b00608c15c61062afc1a82e868058158fd06e0741a82b06407017a2206a0b41881325a08c1294306609e89bbb01e06cf60340620cc1982e32e0880f80b01a0640783233b284120fd6840bc0d82526e02817b474be09c1780e03a464128152c8090148270520881402b04683c0e80902c0a40cc2205305811b0336207c138224e201c059dd04608412a830444841002303a0357281d0400445d81803a0680f81f02e0700b81600e0500a81901c04c0680702e0240880984204c0981200803406803 >>> (11*((P/5381+shift P)%20161)))%2048
  apply finite_lookup_all (m:=1359) (decode:=val) (by decide) (by decide) _ h k eq hlim
  dsimp only [val, shift]
  decide +kernel

end Hik

open OMA.S_mo_161095
namespace Hik

set_option maxHeartbeats 900000 in
private theorem fourth_opposite {t b c P r g u v : ℕ} (eqn : (t+b)*c=t*b+1)
    (ht : 0<t) (hb : c<b) (prod : P=t*b*c) (small : r^3<P) (bound : P≤g^4)
    (hgt : t=g*u) (hgr : r=g*v) (hsum : t+r=g^2) (hv : 2≤v) : False := by
  have hg : 0<g := Nat.pos_of_mul_pos_right (hgt ▸ ht)
  have hu : 0<u := Nat.pos_of_mul_pos_left (hgt ▸ ht)
  have gsum : g=u+v := Nat.eq_of_mul_eq_mul_left hg (by nlinarith only [hsum,hgt,hgr])
  have vsmall : v^3<g := by
    apply Nat.lt_of_mul_lt_mul_left (a:=g^3)
    nlinarith only [small,bound,show (g*v)^3=r^3 by rw [hgr]]
  have v3 : 3*v≤u := by
    have hsq := Nat.mul_self_le_mul_self hv
    nlinarith only [vsmall,gsum,Nat.mul_le_mul_right v hsq]
  have gquad : g*g<2*(u*u) := by
    have hsq := Nat.mul_self_le_mul_self (show 3*g≤4*u by omega)
    nlinarith only [hsq,Nat.mul_pos hu hu]
  have near : P<2*t*t := by
    rw [hgt]
    nlinarith only [bound,Nat.mul_lt_mul_of_pos_left gquad (Nat.mul_pos hg hg)]
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hb.le
  have pp : P=t^2*d+t := by rw [prod,hd]; rw [hd] at eqn; nlinarith only [congrArg (· * t) eqn]
  have d1 : d=1 := by
    by_contra! ne
    have dd : 2≤d := by omega
    nlinarith only [ht,near,pp,Nat.mul_le_mul_left (t*t) dd]
  have htcc : t+1=c*(c+1) := by rw [hd,d1] at eqn; nlinarith only [eqn]
  rw [hgt,gsum] at htcc
  have sq : (2*c+1)^2+v*v=(2*u+v)^2+5 := by nlinarith only [htcc]
  have hcube : v*v≤v^3 := by nlinarith only [Nat.mul_le_mul_right (v*v) (show 1≤v by omega)]
  by_cases v2 : v=2
  · subst v
    by_cases h : 2*c+1≤2*u+2
    · nlinarith only [sq, Nat.mul_self_le_mul_self h]
    · nlinarith only [sq, hu, Nat.mul_self_le_mul_self (show (2*u+2)+1≤2*c+1 by omega)]
  · have vbig := Nat.mul_self_le_mul_self (show 3≤v by omega)
    by_cases h : 2*u+v≤2*c+1
    · nlinarith only [sq,vbig, Nat.mul_self_le_mul_self h]
    · have h3 := Nat.mul_self_le_mul_self (show (2*c+1)≤(2*u+v)-1 by omega)
      have hw : 2*u+v=(2*u+v-1)+1 := by omega
      have hdelta : v*v<4*u+2*v := by omega
      nlinarith only [sq, hdelta, h3, hw, congrArg (fun n => n*n) hw]

private theorem fourth_signed_pair {P t s g : ℕ} {e f : ℤ} (dt : g∣t) (ds : g∣s)
    (ht : (t:ℤ)^2∣(P:ℤ)-e*t) (hs : (s:ℤ)^2∣(P:ℤ)-f*s) :
    (g:ℤ)^2 ∣ e*t-f*s := by
  have gd : (g:ℤ)^2∣(t:ℤ)^2 := pow_dvd_pow_of_dvd (by exact_mod_cast dt) 2
  have ge : (g:ℤ)^2∣(s:ℤ)^2 := pow_dvd_pow_of_dvd (by exact_mod_cast ds) 2
  have ex : ((P:ℤ)-f*s)-((P:ℤ)-e*t)=e*t-f*s := by ring
  exact ex ▸ dvd_sub (ge.trans hs) (gd.trans ht)

private theorem fourth_magnitude {a b c t : ℕ} (h : IsNontrivialHT a b c) (ht : t∈[a,b,c]) :
    c≤t ∧ t*t<a*b*c := by
  obtain ⟨hc,hcb,hba⟩ := bounds h
  have ha : a<b*c := by nlinarith [h.1.2.2,Nat.mul_le_mul_left a (show c+1≤b by omega)]
  have hmax := Nat.mul_lt_mul_of_pos_left ha (show 0<a by omega)
  have hbds : c≤t ∧ t≤a := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl <;> omega
  exact ⟨hbds.1,by nlinarith [Nat.mul_self_le_mul_self hbds.2]⟩

private theorem fourth_member {a b c t : ℕ} (h : IsNontrivialHT a b c) (ht : t∈[a,b,c]) :
    (∃ w : ℕ, c<w ∧ (t+w)*c=t*w+1 ∧ a*b*c=t*w*c ∧ ((t:ℤ)^2 ∣ (a*b*c:ℕ)-(t:ℤ))) ∨
    (t=c ∧ ((t:ℤ)^2 ∣ (a*b*c:ℕ)+(t:ℤ))) := by
  obtain ⟨da,db,dc⟩ := signed_squares h
  obtain ⟨_,hcb,hba⟩ := bounds h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl|rfl
  · exact Or.inl ⟨b,hcb,h.1.2.2,rfl,da⟩
  · left; exact ⟨a,by omega,by simpa only [add_comm,mul_comm] using h.1.2.2,by ring,db⟩
  · exact Or.inr ⟨rfl,dc⟩

private theorem fourth_lt_square {t N g : ℕ} (ht : t*t<N) (hn : N≤g^4) : t<g^2 := by
  by_contra! hx
  nlinarith [Nat.mul_self_le_mul_self hx]

private theorem fourth_mix {a b c p q r t w g : ℕ} (h : IsNontrivialHT a b c)
    (k : IsNontrivialHT p q r) (eq : a*b*c=p*q*r) (ne : t≠r) (tm : t∈[a,b,c])
    (dt : g∣t) (dr : g∣r) (hbad : a*b*c≤g^4) (wc : c<w)
    (we : (t+w)*c=t*w+1) (pe : a*b*c=t*w*c) (td : (t:ℤ)^2∣(a*b*c:ℕ)-(t:ℤ)) : False := by
  obtain ⟨hc,_,_⟩ := bounds h
  obtain ⟨hr,hrq,hqp⟩ := bounds k
  obtain ⟨ct,tsq⟩ := fourth_magnitude h tm
  have rsq := (fourth_magnitude k (show r∈[p,q,r] by simp)).2
  rw [←eq] at rsq
  have ts := fourth_lt_square tsq hbad
  have rs := fourth_lt_square rsq hbad
  have hd := (signed_squares k).2.2
  rw [←eq] at hd
  have sd := fourth_signed_pair (P:=a*b*c) (e:=1) (f:=-1) dt dr (by simpa using td) (by simpa using hd)
  have dsum : g^2∣t+r := by exact_mod_cast (show (g:ℤ)^2∣(t:ℤ)+r by simpa using sd)
  have eqs := Nat.eq_of_dvd_of_lt_two_mul (show t+r≠0 by omega) dsum (show t+r<2*g^2 by omega)
  obtain ⟨v,hv⟩ := dr
  obtain ⟨u,hu⟩ := dt
  have hv2 : 2≤v := by
    by_contra! hl
    interval_cases v
    · simp_all
    · simp only [mul_one] at hv
      have rd : r∣t := ⟨u,hv ▸ hu⟩
      exact ne (no_proper_cross_dvd k h eq.symm (by simp) tm rd).symm
  have cube : r^3<a*b*c := by
    rw [eq]
    have hpos : 0<r := by omega
    have lt1 := Nat.mul_lt_mul_of_pos_left hrq hpos
    have lt2 := Nat.mul_lt_mul_of_pos_right lt1 hpos
    nlinarith [Nat.mul_le_mul_right (q*r) (show r≤p by omega)]
  exact fourth_opposite we (by omega) wc pe cube hbad hu hv eqs hv2

/-- A common divisor of unequal entries in equal-product triples is below the fourth root. -/
theorem cross_fourth_bound {a b c p q r t s g : ℕ} (h : IsNontrivialHT a b c)
    (k : IsNontrivialHT p q r) (eq : a*b*c=p*q*r) (ht : t∈[a,b,c]) (hs : s∈[p,q,r])
    (hne : t≠s) (dt : g∣t) (ds : g∣s) : g^4<a*b*c := by
  by_contra! hbad
  have ts := fourth_lt_square (fourth_magnitude h ht).2 hbad
  have ss := fourth_lt_square (fourth_magnitude k hs).2 (eq ▸ hbad)
  have diff (d : (g:ℤ)^2 ∣ (t:ℤ)-s) : False := by
    have hz : (t:ℤ)-s=0 := Int.eq_zero_of_abs_lt_dvd d (by
      zify at ss ts
      exact abs_lt.mpr ⟨by linarith only [ss,Int.natCast_nonneg t],by linarith only [ts,Int.natCast_nonneg s]⟩)
    omega
  rcases fourth_member h ht with ⟨w,wc,we,pe,td⟩|⟨tc,td⟩ <;>
    rcases fourth_member k hs with ⟨v,vr,ve,qe,sd⟩|⟨sr,sd⟩
  · rw [←eq] at sd
    apply diff
    simpa using fourth_signed_pair (P:=a*b*c) (e:=1) (f:=1) dt ds (by simpa using td) (by simpa using sd)
  · subst s; exact fourth_mix h k eq hne ht dt ds hbad wc we pe td
  · subst t; exact fourth_mix k h eq.symm hne.symm hs ds dt (eq ▸ hbad) vr ve qe sd
  · rw [←eq] at sd
    have dd := fourth_signed_pair (P:=a*b*c) (e:=-1) (f:=-1) dt ds (by simpa using td) (by simpa using sd)
    apply diff
    simpa only [neg_mul,one_mul,neg_sub_neg,neg_sub] using dvd_neg.mpr dd

/-- Every prime-power divisor of a collision is smaller than the fourth root of the common product. -/
theorem prime_power_fourth {a b c p q r z : ℕ} (h : IsNontrivialHT a b c)
    (k : IsNontrivialHT p q r) (eq : a*b*c=p*q*r) (ne : (a,b,c)≠(p,q,r))
    (hz : IsPrimePow z) (hd : z∣a*b*c) : z^4<a*b*c := by
  have locate {A B C : ℕ} (good : IsNontrivialHT A B C) (div : z∣A*B*C) :
      ∃ t∈[A,B,C], z∣t := by
    obtain ⟨ab,ac,bc⟩ := pairwise_entries good
    rcases ((Nat.coprime_mul_iff_left.mpr ⟨ac,bc⟩).isPrimePow_dvd_mul hz).mp div with d|d
    · rcases (ab.isPrimePow_dvd_mul hz).mp d with d|d
      · exact ⟨A,by simp,d⟩
      · exact ⟨B,by simp,d⟩
    · exact ⟨C,by simp,d⟩
  obtain ⟨t,ht,dt⟩ := locate h hd
  obtain ⟨s,hs,ds⟩ := locate k (eq ▸ hd)
  exact cross_fourth_bound h k eq ht hs (fun e => ne (common_entry h k eq ht (e ▸ hs))) dt ds

end Hik

open OMA.S_mo_161095

namespace Hik

private theorem seven_positive_other {a b c V W : ℕ} (h : IsNontrivialHT a b c)
    (perm : [c,V,W].Perm [a,b,c]) :
    (c<V ∧ (V:ℤ)^2∣(a*b*c:ℕ)-(V:ℤ)) ∧ (c<W ∧ (W:ℤ)^2∣(a*b*c:ℕ)-(W:ℤ)) := by
  have rot : [a,b,c].Perm [c,a,b] :=
    (List.perm_append_comm : ([a,b]++[c]).Perm ([c]++[a,b]))
  have ab := (perm.trans rot).cons_inv
  obtain ⟨_,hcb,hba⟩ := bounds h
  obtain ⟨da,db,_⟩ := signed_squares h
  have imp (v : ℕ) (hv : v∈[V,W]) : c<v ∧ (v:ℤ)^2∣(a*b*c:ℕ)-(v:ℤ) := by
    have hv' := ab.mem_iff.mp hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv'
    rcases hv' with rfl|rfl
    · exact ⟨by omega,da⟩
    · exact ⟨hcb,db⟩
  exact ⟨imp _ (by simp),imp _ (by simp)⟩

private theorem seven_bound {u w v : ℕ} (hu : 0<u) (hw : 0<w) (ne : u≠w)
    (d : (v:ℤ)∣(u:ℤ)-w) : v < max u w := by
  have hne : (u:ℤ)-(w:ℤ)≠0 := sub_ne_zero.mpr (by exact_mod_cast ne)
  have he := Int.le_abs_of_dvd hne d
  rcases le_total u w with h|h
  · rw [max_eq_right h]
    have h' : (u:ℤ)≤w := by exact_mod_cast h
    rw [abs_of_nonpos (sub_nonpos.mpr h')] at he
    omega
  · rw [max_eq_left h]
    have h' : (w:ℤ)≤u := by exact_mod_cast h
    rw [abs_of_nonneg (sub_nonneg.mpr h')] at he
    omega

/-- In the seven-edge factor table the two vertices of degree three cannot
both represent the smallest entry of their respective triples. -/
theorem seven_not_both_centers {a b c p q r t u v w x y z : ℕ}
    (h : IsNontrivialHT a b c) (k : IsNontrivialHT p q r) (eqP : a*b*c=p*q*r)
    (pos : ∀ i : Fin 7, 1 < ![t,u,v,w,x,y,z] i)
    (cop : ∀ i j : Fin 7, i≠j → (![t,u,v,w,x,y,z] i).Coprime (![t,u,v,w,x,y,z] j))
    (left : [t*u*x,v*w,y*z].Perm [a,b,c]) (right : [t*w*z,u*v,x*y].Perm [p,q,r]) :
    ¬(t*u*x=c ∧ t*w*z=r) := by
  rintro ⟨hc,hr⟩
  obtain ⟨⟨hc1,svw⟩,⟨hc2,syz⟩⟩ := seven_positive_other h (hc ▸ left)
  obtain ⟨⟨hr1,suv⟩,⟨hr2,sxy⟩⟩ := seven_positive_other k (hr ▸ right)
  have ht : 0<t := Nat.zero_lt_of_lt (pos 0)
  have hu : 0<u := Nat.zero_lt_of_lt (pos 1)
  have hv : 0<v := Nat.zero_lt_of_lt (pos 2)
  have hw : 0<w := Nat.zero_lt_of_lt (pos 3)
  have hx : 0<x := Nat.zero_lt_of_lt (pos 4)
  have hy : 0<y := Nat.zero_lt_of_lt (pos 5)
  have hz : 0<z := Nat.zero_lt_of_lt (pos 6)
  have uw : u≠w := by
    have hh : u.Coprime w := cop 1 3 (by decide)
    intro e
    have := pos 1
    simp [e] at hh
    change 1<u at this
    omega
  have xz : x≠z := by
    have hh : x.Coprime z := cop 4 6 (by decide)
    intro e
    have := pos 4
    simp [e] at hh
    change 1<x at this
    omega
  rw [←eqP] at suv sxy
  have vm : v < max u w := seven_bound hu hw uw (by
    have hd := cross_signed_cell (P:=((a*b*c:ℕ):ℤ)) (e:=1) (f:=1)
      (g:=(v:ℤ)) (u:=(u:ℤ)) (v:=(w:ℤ)) (by positivity)
      (by simpa [mul_comm] using suv) (by simpa using svw)
    simpa using hd)
  have ym : y < max x z := seven_bound hx hz xz (by
    have hd := cross_signed_cell (P:=((a*b*c:ℕ):ℤ)) (e:=1) (f:=1)
      (g:=(y:ℤ)) (u:=(x:ℤ)) (v:=(z:ℤ)) (by positivity)
      (by simpa [mul_comm] using sxy) (by simpa using syz)
    simpa using hd)
  rw [←hc] at hc1 hc2
  rw [←hr] at hr1 hr2
  have mz : min x z < min u w := by
    rcases le_total u w with e|e
    · rw [max_eq_right e] at vm
      rw [min_eq_left e]
      have f : z<u := by
        apply Nat.lt_of_mul_lt_mul_right (a:=w)
        calc z*w ≤ t*w*z := by nlinarith [Nat.mul_le_mul_right (z*w) ht]
             _ < u*v := hr1
             _ ≤ u*w := Nat.mul_le_mul_left _ vm.le
      exact (min_le_right _ _).trans_lt f
    · rw [max_eq_left e] at vm
      rw [min_eq_right e]
      have f : x<w := by
        apply Nat.lt_of_mul_lt_mul_right (a:=u)
        calc x*u ≤ t*u*x := by nlinarith [Nat.mul_le_mul_right (x*u) ht]
             _ < v*w := hc1
             _ ≤ w*u := by simpa [mul_comm] using Nat.mul_le_mul_left w vm.le
      exact (min_le_left _ _).trans_lt f
  have mw : min u w < min x z := by
    rcases le_total x z with e|e
    · rw [max_eq_right e] at ym
      rw [min_eq_left e]
      have f : w<x := by
        apply Nat.lt_of_mul_lt_mul_right (a:=z)
        calc w*z ≤ t*w*z := by nlinarith [Nat.mul_le_mul_right (w*z) ht]
             _ < x*y := hr2
             _ ≤ x*z := Nat.mul_le_mul_left _ ym.le
      exact (min_le_right _ _).trans_lt f
    · rw [max_eq_left e] at ym
      rw [min_eq_right e]
      have f : u<z := by
        apply Nat.lt_of_mul_lt_mul_right (a:=x)
        calc u*x ≤ t*u*x := by nlinarith [Nat.mul_le_mul_right (u*x) ht]
             _ < y*z := hc2
             _ ≤ z*x := by simpa [mul_comm] using Nat.mul_le_mul_left z ym.le
      exact (min_le_left _ _).trans_lt f
  omega

/-- If the central row and its neighboring outer column are both negative,
their common factor lies strictly below the opposite factor on that path. -/
theorem seven_mixed_order {a b c p q r t u v w x y z : ℕ}
    (h : IsNontrivialHT a b c) (k : IsNontrivialHT p q r) (eqP : a*b*c=p*q*r)
    (pos : ∀ i : Fin 7, 1 < ![t,u,v,w,x,y,z] i)
    (cop : ∀ i j : Fin 7, i≠j → (![t,u,v,w,x,y,z] i).Coprime (![t,u,v,w,x,y,z] j))
    (left : [t*u*x,v*w,y*z].Perm [a,b,c]) (right : [t*w*z,u*v,x*y].Perm [p,q,r])
    (hc : t*u*x=c) (hr : u*v=r) : u<w := by
  obtain ⟨⟨hc1,svw⟩,⟨_,syz⟩⟩ := seven_positive_other h (hc ▸ left)
  have rot : [u*v,t*w*z,x*y].Perm [p,q,r] :=
    (List.Perm.swap (t*w*z) (u*v) [x*y]).trans right
  obtain ⟨⟨_,stwz⟩,⟨hr2,sxy⟩⟩ := seven_positive_other k (hr ▸ rot)
  have ht : 2≤t := pos 0
  have hu : 0<u := Nat.zero_lt_of_lt (pos 1)
  have hv : 0<v := Nat.zero_lt_of_lt (pos 2)
  have hw : 0<w := Nat.zero_lt_of_lt (pos 3)
  have hx : 0<x := Nat.zero_lt_of_lt (pos 4)
  have hy : 0<y := Nat.zero_lt_of_lt (pos 5)
  have hz : 0<z := Nat.zero_lt_of_lt (pos 6)
  have xz : x≠z := by
    have hh : x.Coprime z := cop 4 6 (by decide)
    intro e
    have h1 : 1<x := pos 4
    simp [e] at hh
    omega
  have neg := (signed_squares k).2.2
  rw [←eqP] at neg stwz sxy
  rw [←hr] at neg
  have sv := cross_signed_cell (P:=((a*b*c:ℕ):ℤ)) (e:=1) (f:= -1)
    (g:=(v:ℤ)) (u:=(w:ℤ)) (v:=(u:ℤ)) (by positivity)
    (by simpa using svw) (by simpa [mul_comm] using neg)
  have dv : v∣w+u := by exact_mod_cast (show (v:ℤ)∣(w:ℤ)+u by simpa using sv)
  have vv := Nat.le_of_dvd (show 0<w+u by omega) dv
  have ym : y < max x z := seven_bound hx hz xz (by
    have hd := cross_signed_cell (P:=((a*b*c:ℕ):ℤ)) (e:=1) (f:=1)
      (g:=(y:ℤ)) (u:=(x:ℤ)) (v:=(z:ℤ)) (by positivity)
      (by simpa [mul_comm] using sxy) (by simpa using syz)
    simpa using hd)
  have dz : (z:ℤ)∣(t:ℤ)*w-y := by
    have sz := cross_signed_cell (P:=((a*b*c:ℕ):ℤ)) (e:=1) (f:=1)
      (g:=(z:ℤ)) (u:=((t:ℤ)*w)) (v:=(y:ℤ)) (by positivity)
      (by simpa [mul_comm,mul_left_comm,mul_assoc] using stwz) (by simpa [mul_comm] using syz)
    simpa using sz
  rw [←hc] at hc1
  rw [←hr] at hr2
  by_contra! e
  have txv : t*x<v := Nat.lt_of_mul_lt_mul_right (a:=u) (calc
    (t*x)*u = t*u*x := by ring
    _ < v*w := hc1
    _ ≤ v*u := Nat.mul_le_mul_left v e)
  have xw : x<w := by
    have f : x*(2*u)<w*(2*u) := calc
      x*(2*u) ≤ t*u*x := by nlinarith [Nat.mul_le_mul_right (u*x) ht]
      _ < v*w := hc1
      _ ≤ w*(2*u) := by simpa [mul_comm] using Nat.mul_le_mul_left w (show v≤2*u by omega)
    exact Nat.lt_of_mul_lt_mul_right f
  have tuy : t*u<y := Nat.lt_of_mul_lt_mul_right (a:=x) (calc
    t*u*x = u*(t*x) := by ring
    _ ≤ u*v := Nat.mul_le_mul_left u txv.le
    _ < x*y := hr2
    _ = y*x := by ring)
  have twy := (Nat.mul_le_mul_left t e).trans_lt tuy
  have xy : x<y := by
    have hl : w≤t*w := by nlinarith [Nat.mul_le_mul_right w ht]
    omega
  have yz : y<z := by omega
  have a1 : (t:ℤ)*w<(y:ℤ) := by exact_mod_cast twy
  have a2 : (y:ℤ)<z := by exact_mod_cast yz
  have a0 : 0≤(t:ℤ)*w := by positivity
  have he := Int.eq_zero_of_abs_lt_dvd dz (abs_lt.mpr ⟨by omega,by omega⟩)
  omega

end Hik

open OMA.S_mo_161095 Hik Finset

namespace OMA.R_mo_161095_R1

private theorem center_minimum {a b c A B C : ℕ} (h : IsNontrivialHT a b c) (pm : [A,B,C].Perm [a,b,c])
    (hb : A≤B) (hc : A≤C) : A=c := by
  have mem := pm.mem_iff.mpr (by simp : c∈[a,b,c])
  have ma := pm.mem_iff.mp (by simp : A∈[A,B,C])
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem ma
  obtain ⟨_,hcb,hba⟩ := bounds h
  omega

private theorem min_entry {a b c A B C : ℕ} (h : IsNontrivialHT a b c) (pm : [A,B,C].Perm [a,b,c]) :
    min A (min B C)=c := by
  have mem := List.mem_permutations'.mpr pm
  change [A,B,C] ∈ [[a,b,c],[b,a,c],[b,c,a],[a,c,b],[c,a,b],[c,b,a]] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false,List.cons.injEq,and_true] at mem
  obtain ⟨_,hcb,hba⟩ := bounds h
  rcases mem with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;> omega

/-- Seven occupied gcd cells form two length-three paths and a single edge
joining the two degree-three vertices. Test the two unsigned triple equations
in the seven pairwise coprime edge labels. -/
def H1 : Prop := ∀ t u v w x y z : ℕ,
  (∀ i : Fin 7, 1 < ![t,u,v,w,x,y,z] i) →
  (∀ i j : Fin 7, i≠j → (![t,u,v,w,x,y,z] i).Coprime (![t,u,v,w,x,y,z] j)) →
  10000000000 < (t*u*x)*(v*w)*(y*z) →
  (∀ s : ℕ, IsPrimePow s → s∣(t*u*x)*(v*w)*(y*z) → s^4 < (t*u*x)*(v*w)*(y*z)) →
  ¬(t*u*x≤v*w ∧ t*u*x≤y*z ∧ t*w*z≤u*v ∧ t*w*z≤x*y) →
  (t*u*x≤v*w → t*u*x≤y*z → u*v≤t*w*z → u*v≤x*y → u<w) →
  min (t*u*x) (min (v*w) (y*z))+4 ≤ min (t*w*z) (min (u*v) (x*y)) →
  let valid (A B C : ℕ) := (A+B)*C=A*B+1 ∨ (B+C)*A=B*C+1 ∨ (C+A)*B=C*A+1
  ¬(valid (t*u*x) (v*w) (y*z) ∧ valid (t*w*z) (u*v) (x*y))

/-- For the denser supports, only two small divisors and two minima are
needed to specify a candidate. Each fixed minimum gap gives a finite search. -/
def H2 : Prop := ∀ c r v w : ℕ,
  2≤c → c+4≤r → 0<v → v<c → v<w → w<r →
  v∣c^2-1 → w∣r^2-1 → (c.gcd r)^2∣r-c →
  r ≤ 2695*(c.gcd r)*(r-c)^3 →
  let a := c+(c^2-1)/v
  let b := c+v
  let p := r+(r^2-1)/w
  let q := r+w
  10000000000 < a*b*c → p<a →
  (∀ s : ℕ, IsPrimePow s → s∣a*b*c → s^4<a*b*c) →
  8 ≤ (univ.filter (fun z : Fin 3 × Fin 3 => 1 < (![a,b,c] z.1).gcd (![p,q,r] z.2))).card →
  a*b*c≠p*q*r

theorem exclude_ordered (hh1 : H1) (hh2 : H2) {a b c p q r : ℕ} (h : IsNontrivialHT a b c)
    (k : IsNontrivialHT p q r) (eq : a*b*c=p*q*r) (hcr : c<r) : False := by
  have ne : (a,b,c)≠(p,q,r) := by rintro he; have := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) he; dsimp only at this; omega
  have lim : 10000000000 < a*b*c := by by_contra! le; exact ne (ten_billion_unique h k eq le)
  have ppBound (s : ℕ) (hs : IsPrimePow s) (hd : s∣a*b*c) := prime_power_fourth h k eq ne hs hd
  have gap : c+4≤r := by have := fixed_gap h k eq hcr; omega
  have cells := seven_cells_of_collision h k eq ne
  by_cases seven : (univ.filter (fun z : Fin 3 × Fin 3 => 1 < (![a,b,c] z.1).gcd (![p,q,r] z.2))).card=7
  · obtain ⟨t,u,v,w,x,y,z,gt,cop,lp,rp⟩ := seven_factor_shape h k eq ne seven
    have Hprod : (t*u*x)*(v*w)*(y*z)=a*b*c := by
      simpa only [List.prod_cons,List.prod_nil,mul_one,mul_assoc] using lp.prod_eq
    have ncenters := seven_not_both_centers h k eq gt cop lp rp
    apply hh1 t u v w x y z gt cop (by rwa [Hprod]) (by rw [Hprod]; exact ppBound) ?_ ?_
        (by rw [min_entry h lp,min_entry k rp]; exact gap) ⟨unsigned_triple h lp,unsigned_triple k rp⟩
    · rintro ⟨h1,h2,h3,h4⟩
      exact ncenters ⟨center_minimum h lp h1 h2,center_minimum k rp h3 h4⟩
    · intro h1 h2 h3 h4
      have perm := (List.Perm.swap (t*w*z) (u*v) [x*y]).trans rp
      exact seven_mixed_order h k eq gt cop lp rp (center_minimum h lp h1 h2) (center_minimum k perm h3 h4)
  have dense : 8 ≤ (univ.filter (fun z : Fin 3 × Fin 3 => 1 < (![a,b,c] z.1).gcd (![p,q,r] z.2))).card := by omega
  have hc := (bounds h).1
  have gcd := shared_square_dvd_gap (Nat.gcd_dvd_left c r) (Nat.gcd_dvd_right c r)
    (product_data h).1 (by rw [eq]; exact (product_data k).1)
  have bound := (joint_gap h k eq hcr).1
  obtain ⟨hvlt,_,hpa⟩ := small_divisor_strict h k eq hcr
  obtain ⟨v,hv,hvc,hvd,hb,ha⟩ := small_divisor_rep h
  obtain ⟨w,hw,hwr,hwd,hq,hp⟩ := small_divisor_rep k
  have hvw : v<w := by omega
  subst a b p q
  exact (hh2 c r v w hc gap hv hvc hvw hwr hvd hwd gcd bound lim hpa ppBound dense) eq

theorem main : H1 → H2 → type_of% @OMA.S_mo_161095.main := by
  intro h1 h2 a b c p q r h k eq
  rcases lt_trichotomy c r with hcr|hcr|hrc
  · exact (exclude_ordered h1 h2 h k eq hcr).elim
  · subst r; exact same_c h k eq
  · exact (exclude_ordered h1 h2 k h eq.symm hrc).elim

end OMA.R_mo_161095_R1
