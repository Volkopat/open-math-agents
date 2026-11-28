import OMAStatements.S_oeis_a393168
import Mathlib

/-!
A reduction of the explicit 6563 cutoff for bounded representations by x²+y²−z².
A counterexample has tightly restricted factorizations at the two neighboring odd
offsets from its square root. Separating its squarefree part gives two smaller
problems. A finite certificate leaves 73 possible small squarefree parts.

The odd-gap construction also appears in @jonas-klesen's proof of the weaker
variant of Erdős 1148 in this repository. The sufficiently-large result for the
related Erdős problem is due to P. Chojecki (arXiv:2603.18087).
-/

namespace OMA.R_oeis_a393168_R1
open OMA.S_oeis_a393168

private lemma oma_pair_repr (k x u v : ℕ) (hx : x ≤ k.sqrt)
    (he : k = x^2+u*v) (hu : u%2=1) (hv : v%2=1) (hsize : u+v ≤ 2*k.sqrt) :
    IsRepresentable k := by
  let y : ℤ := ((u:ℤ)+v)/2
  let z : ℤ := ((u:ℤ)-v)/2
  have h1 : 2*y = (u:ℤ)+v := by dsimp [y]; omega
  have h2 : 2*z = (u:ℤ)-v := by dsimp [z]; omega
  have ss : (k.sqrt:ℤ)^2 ≤ k := by exact_mod_cast Nat.sqrt_le' k
  have bound (w : ℤ) (lo : -(k.sqrt:ℤ)≤w) (hi : w≤k.sqrt) : w^2 ≤ (k:ℤ) := by
    nlinarith only [ss,mul_nonneg (sub_nonneg.mpr hi) (show 0 ≤ (k.sqrt:ℤ)+w by omega)]
  have he' : (k:ℤ) = (x:ℤ)^2+u*v := by exact_mod_cast he
  refine ⟨(x:ℤ),y,z,bound _ (by omega) (by exact_mod_cast hx),
    bound _ (by omega) (by omega),bound _ (by omega) (by omega),?_⟩
  have hu' : (u:ℤ) = y+z := by omega
  have hv' : (v:ℤ) = y-z := by omega
  rw [hu', hv'] at he'
  linarith only [he', show (y+z)*(y-z)=y^2-z^2 by ring]

private lemma oma_bounded_square_four {k : ℕ} (hk : 6563 < k)
    (hres : k % 4 = 0 ∨ k % 4 = 1) : IsRepresentable k := by
  let s := Nat.sqrt k
  have hs : 1 ≤ s := Nat.le_sqrt'.mpr (by norm_num; omega)
  obtain ⟨x,hlo,hhi,hmod⟩ : ∃ x : ℕ, s ≤ x+1 ∧ x ≤ s ∧ x%2 = k%4 := by
    by_cases h : s%2 = k%4
    · exact ⟨s,by omega,le_rfl,h⟩
    · exact ⟨s-1,by omega,by omega,by omega⟩
  have sqmod : x^2 % 4 = x % 2 := by
    calc
      x^2 % 4 = (x%4)^2 %4 := Nat.pow_mod _ _ _
      _ = x%4%2 := by
        have h := Nat.mod_lt x (by decide : 0 < 4)
        interval_cases x%4 <;> decide
      _ = x%2 := Nat.mod_mod_of_dvd _ (by decide)
  have congr : (x : ℤ)^2 % 4 = (k : ℤ) % 4 := by exact_mod_cast sqmod.trans hmod
  have ss : (s : ℤ)^2 ≤ (k : ℤ) := by
    exact_mod_cast (show s^2 ≤ k from Nat.le_sqrt'.mp le_rfl)
  have upper : (k : ℤ) ≤ (s : ℤ)*s+s+s := by exact_mod_cast Nat.sqrt_le_add k
  have small : (x : ℤ)^2 ≤ (s : ℤ)^2 := by gcongr
  have large : ((s : ℤ)-1)^2 ≤ (x : ℤ)^2 := by
    apply pow_le_pow_left₀ <;> omega
  let d : ℤ := ((k : ℤ)-(x : ℤ)^2)/4
  have exact_rem : (k : ℤ)-(x : ℤ)^2 = 4*d := by dsimp [d]; omega
  have hpos : 0 ≤ d := by omega
  have hd : d+1 ≤ (s : ℤ) := by nlinarith
  have bounded (u : ℤ) (hl : -(s : ℤ) ≤ u) (hh : u ≤ s) : u^2 ≤ (k : ℤ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) (show 0 ≤ (s : ℤ)+u by omega)]
  exact ⟨x,d+1,d-1,small.trans ss,bounded _ (by omega) hd,
    bounded _ (by omega) (by omega),by nlinarith⟩

private lemma oma_sq_rem_two (x : ℕ) : x^2 % 2 = x % 2 := by
  rw [sq, Nat.mul_mod]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

private lemma oma_representable_odd_gap (k : ℕ) (hpar : k % 2 ≠ k.sqrt % 2) :
    IsRepresentable k := by
  let x := k.sqrt
  let d := (k - x^2) / 2
  have hx : x^2 ≤ k := Nat.sqrt_le' _
  have upper : k ≤ x^2 + x + x := by
    simpa only [sq, x] using Nat.sqrt_le_add k
  have par := oma_sq_rem_two x
  change k % 2 ≠ x % 2 at hpar
  have hd : k = x^2 + 2*d + 1 := by dsimp only [d]; omega
  have bound : d+1 ≤ x := by omega
  refine ⟨(x : ℤ), (d+1 : ℕ), (d : ℤ), by exact_mod_cast hx, ?_, ?_, ?_⟩
  · exact_mod_cast (Nat.pow_le_pow_left bound 2).trans hx
  · exact_mod_cast (Nat.pow_le_pow_left (by omega : d ≤ x) 2).trans hx
  · push_cast
    have eq : (k : ℤ) = (x : ℤ)^2 + 2*d + 1 := by exact_mod_cast hd
    linarith only [eq, show ((d : ℤ)+1)^2 = (d : ℤ)^2+2*d+1 by ring]

private lemma oma_first_residual_prime {k : ℕ} (hk : 6563 < k) (par : k%2=k.sqrt%2)
    (hn : ¬ IsRepresentable k)
    (pairRep : ∀ (x u v : ℕ), x ≤ k.sqrt → k = x^2+u*v →
      u%2 = 1 → v%2 = 1 → u+v ≤ 2*k.sqrt → IsRepresentable k) :
    (k-(k.sqrt-1)^2).Prime := by
  let t := k.sqrt
  let x := t-1
  let r := k-x^2
  have ht : 81 ≤ t := Nat.le_sqrt'.mpr (by norm_num; omega)
  have tx : t = x+1 := by dsimp [x]; omega
  have tl : t^2 ≤ k := Nat.le_sqrt'.mp le_rfl
  have tu : k ≤ t*t+t+t := Nat.sqrt_le_add k
  have lo : x^2 + 2*x + 1 ≤ k := by rw [tx] at tl; nlinarith
  have hi : k+1 ≤ x^2+4*t := by rw [tx] at tu ⊢; nlinarith
  have sum : k = x^2+r := by dsimp [r]; omega
  have rbig : 2 ≤ r := by omega
  have xmod : x^2%2=x%2 := by
    rw [Nat.pow_mod]
    have : x%2 < 2 := Nat.mod_lt _ (by decide)
    interval_cases x%2 <;> decide
  change k%2=t%2 at par
  have rodd : r%2 = 1 := by omega
  change r.Prime
  refine Nat.prime_iff_not_exists_mul_eq.mpr ⟨rbig,?_⟩
  rintro ⟨u,v,hu,hv,mul⟩
  have oddprod : (u%2 * (v%2))%2 = 1 := by
    rw [← Nat.mul_mod,mul,rodd]
  have ou : u%2 = 1 := by
    by_contra! h
    have h0 : u%2 = 0 := by omega
    simp [h0] at oddprod
  have ov : v%2 = 1 := by
    by_contra! h
    have h0 : v%2 = 0 := by omega
    simp [h0] at oddprod
  have ub : 3 ≤ u := by
    by_contra! h
    have : u = 1 := by omega
    rw [this,one_mul] at mul
    omega
  have vb : 3 ≤ v := by
    by_contra! h
    have : v = 1 := by omega
    rw [this,mul_one] at mul
    omega
  have prodBound : 3*(u+v) ≤ u*v+9 := by
    obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le ub
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le vb
    rw [ha,hb]
    nlinarith [Nat.zero_le (a*b)]
  exact hn (pairRep x u v (by change x ≤ t; omega) (by omega) ou ov (by change u+v ≤ 2*t; omega))

private lemma oma_composite_factors {n : ℕ} (hn : 2 ≤ n) (hp : ¬n.Prime) :
    ∃ u v : ℕ, 2 ≤ u ∧ 2 ≤ v ∧ u*v = n := by
  obtain ⟨u,v,hu,hv,he⟩ := (Nat.not_prime_iff_exists_mul_eq hn).mp hp
  refine ⟨u,v,?_,?_,he⟩
  · by_contra! hh
    interval_cases u <;> simp_all
  · by_contra! hh
    interval_cases v <;> simp_all

private lemma oma_odd_almost_prime {q : ℕ} (hlarge : 81 < q) (hodd : q%2 = 1)
    (hblock : ∀ u v : ℕ, 5 ≤ u → 5 ≤ v → u*v ≠ q) :
    q.Prime ∨ ∃ p : ℕ, p.Prime ∧ q = 3*p := by
  by_cases hp : q.Prime
  · exact Or.inl hp
  right
  have three (s : ℕ) (he : q = 3*s) : s.Prime := by
    by_contra hn
    obtain ⟨u,v,hu,hv,huv⟩ := oma_composite_factors (n := s) (by omega) hn
    have hprod : 3 * (u*v) = q := by rw [huv, he]
    by_cases hu5 : 5 ≤ u
    · exact hblock u (3*v) hu5 (by omega) (by linarith only [hprod])
    by_cases hv5 : 5 ≤ v
    · exact hblock (3*u) v (by omega) hv5 (by linarith only [hprod])
    have hh := Nat.mul_le_mul (by omega : u ≤ 4) (by omega : v ≤ 4)
    omega
  obtain ⟨u,v,hu,hv,huv⟩ := oma_composite_factors (by omega : 2 ≤ q) hp
  have ho : Odd (u*v) := Nat.odd_iff.mpr (huv ▸ hodd)
  obtain ⟨hou,hov⟩ := Nat.odd_mul.mp ho
  have ou := Nat.odd_iff.mp hou
  have ov := Nat.odd_iff.mp hov
  by_cases hu5 : 5 ≤ u
  · have hv3 : v = 3 := by
      by_contra hh
      exact hblock u v hu5 (by omega) huv
    have he : q = 3*u := by rw [← huv, hv3, mul_comm]
    exact ⟨u,three u he,he⟩
  · have hu3 : u = 3 := by omega
    have he : q = 3*v := by rw [← huv, hu3]
    exact ⟨v,three v he,he⟩

private lemma oma_second_prime_obstruction (k : ℕ) (hk : 6563 < k)
    (par : k%2 = k.sqrt%2) (hn : ¬ IsRepresentable k)
    (pairRep : ∀ x u v : ℕ, x ≤ k.sqrt → k = x^2 + u*v →
      u%2=1 → v%2=1 → u+v ≤ 2*k.sqrt → IsRepresentable k) :
    let q := k - (k.sqrt-3)^2
    q.Prime ∨ ∃ p : ℕ, p.Prime ∧ q = 3*p := by
  let t := k.sqrt
  let a := t-3
  let q := k-a^2
  change q.Prime ∨ ∃ p : ℕ, p.Prime ∧ q = 3*p
  have ht : 81 ≤ t := Nat.le_sqrt'.mpr (by norm_num; omega)
  have back : a+3=t := by dsimp [a]; omega
  have hs : t^2 ≤ k := Nat.sqrt_le' _
  have upper : k ≤ t^2+t+t := by simpa only [sq,t] using Nat.sqrt_le_add k
  have adj : a^2+6*t=t^2+9 := by rw [← back]; ring
  have hq : a^2+q=k := by dsimp [q]; omega
  have qab : 81 < q := by omega
  have qu : q ≤ 8*t := by omega
  have pa : a^2 % 2 = a % 2 := by
    rw [sq,Nat.mul_mod]
    rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;> simp [ha]
  change k%2 = t%2 at par
  have qo : q%2=1 := by omega
  apply oma_odd_almost_prime qab qo
  intro u v hu hv he
  have ho : Odd (u*v) := Nat.odd_iff.mpr (he ▸ qo)
  obtain ⟨hou,hov⟩ := Nat.odd_mul.mp ho
  have prod : 5*(u+v) ≤ u*v+25 := by
    obtain ⟨u',rfl⟩ := Nat.exists_eq_add_of_le hu
    obtain ⟨v',rfl⟩ := Nat.exists_eq_add_of_le hv
    nlinarith [Nat.zero_le (u'*v')]
  apply hn (pairRep a u v (by omega) (by omega) (Nat.odd_iff.mp hou)
    (Nat.odd_iff.mp hov) (by omega))

private lemma oma_repr_scale {m : ℕ} (h : IsRepresentable m) (t : ℕ) :
    IsRepresentable (m*t^2) := by
  obtain ⟨x,y,z,hx,hy,hz,hm⟩ := h
  refine ⟨x*t,y*t,z*t,?_,?_,?_,?_⟩
  · push_cast
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hx (sq_nonneg _)
  · push_cast
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hy (sq_nonneg _)
  · push_cast
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hz (sq_nonneg _)
  · push_cast
    rw [hm]
    ring

private lemma oma_squarefree_decomp {n : ℕ} (hn : 0 < n) :
    ∃ s t : ℕ, Squarefree s ∧ 0 < t ∧ n = s*t^2 := by
  obtain ⟨s,t,hs,ht,hn',hsf⟩ := Nat.sq_mul_squarefree_of_pos hn
  exact ⟨s,t,hsf,ht,by simpa [mul_comm] using hn'.symm⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
/-- Finite exceptional values obtained by checking short differences of squares. -/
private lemma oma_small_exceptions (n : ℕ) (hn : n ≤ 6563) (h : ¬ IsRepresentable n) :
    n ∈ (([3, 6, 11, 15, 22, 35, 38, 42, 55, 59, 66, 78, 83, 87, 95, 110, 118, 123, 131, 143, 187, 210,
   222, 227, 255, 262, 266, 278, 299, 303, 323, 326, 395, 402, 447, 483, 502, 551, 563, 590, 618,
   635, 678, 755, 838, 843, 902, 930, 942, 1003, 1007, 1034, 1091, 1162, 1190, 1295, 1326, 1482,
   1523, 1770, 1790, 2067, 2103, 2407, 2483, 2598, 2782, 3422, 3495, 4686, 5447, 5727, 6563] : List ℕ) ++ [27, 150, 735, 867]) := by
  let holes : List ℕ := ([3, 6, 11, 15, 22, 35, 38, 42, 55, 59, 66, 78, 83, 87, 95, 110, 118, 123, 131, 143, 187, 210,
   222, 227, 255, 262, 266, 278, 299, 303, 323, 326, 395, 402, 447, 483, 502, 551, 563, 590, 618,
   635, 678, 755, 838, 843, 902, 930, 942, 1003, 1007, 1034, 1091, 1162, 1190, 1295, 1326, 1482,
   1523, 1770, 1790, 2067, 2103, 2407, 2483, 2598, 2782, 3422, 3495, 4686, 5447, 5727, 6563] : List ℕ) ++ [27, 150, 735, 867]
  let offsets : List (ℕ × ℕ) := [(0,1), (0,2), (1,3), (1,5), (1,7), (3,5), (0,0), (3,7), (1,11), (3,9), (1,13), (5,7), (3,11), (5,9), (3,13), (5,13), (5,11), (3,17), (7,11), (5,19), (3,19), (7,19), (5,17), (7,13), (7,17), (9,17), (7,25), (7,23), (9,11), (9,19), (9,13), (1,17), (5,15), (9,23), (9,29), (11,27), (7,29), (5,25), (3,23), (9,25), (11,21), (9,15), (9,21), (5,23), (15,29), (13,19), (7,31), (11,23), (11,29), (13,23), (13,41), (11,19), (17,33), (17,29), (5,29), (13,31)]
  let works (m k : ℕ) (p : ℕ × ℕ) : Bool :=
    let a := m - p.1
    let d := p.2
    let z := (k - a*a - d*d) / (2*d)
    decide (z+d ≤ m ∧ k = a*a + d*d + 2*d*z)
  let certify (m r : ℕ) : Bool :=
    let k := m*m + r
    decide (6563 < k) || offsets.any (works m k) || holes.contains k
  have cert : ((List.range 82).all fun m =>
      (List.range (2*m+1)).all (certify m)) = true := by decide
  let m := n.sqrt
  have hm : m*m ≤ n := Nat.sqrt_le _
  have upper : n ≤ m*m+m+m := Nat.sqrt_le_add _
  have msmall : m < 82 := Nat.sqrt_lt.mpr (by omega)
  have rsmall : n-m*m < 2*m+1 := by omega
  have cm := List.all_eq_true.mp cert m (List.mem_range.mpr msmall)
  have ok := List.all_eq_true.mp cm (n-m*m) (List.mem_range.mpr rsmall)
  have addsub : m*m + (n-m*m) = n := by omega
  simp only [certify, addsub, Bool.or_eq_true, decide_eq_true_eq, not_lt.mpr hn,
    false_or, List.contains_iff_mem] at ok
  rcases ok with found | member
  · obtain ⟨⟨s,d⟩,_,hw⟩ := List.any_eq_true.mp found
    let a := m-s
    let z := (n-a*a-d*d)/(2*d)
    have sample : z+d ≤ m ∧ n = a*a+d*d+2*d*z := of_decide_eq_true hw
    have ha : a ≤ m := Nat.sub_le _ _
    have hz : z ≤ m := by omega
    apply False.elim (h ?_)
    refine ⟨(a:ℤ), (z+d:ℕ), (z:ℤ), ?_, ?_, ?_, ?_⟩
    · simp only [sq]
      exact_mod_cast (Nat.mul_self_le_mul_self ha).trans hm
    · simp only [sq]
      exact_mod_cast (Nat.mul_self_le_mul_self sample.1).trans hm
    · simp only [sq]
      exact_mod_cast (Nat.mul_self_le_mul_self hz).trans hm
    · have eq : (n:ℤ) = (a:ℤ)*a + (d:ℤ)*d + 2*d*z := by exact_mod_cast sample.2
      push_cast
      rw [eq]
      ring
  · exact member

private lemma small_core_mem {s : ℕ} (hs : Squarefree s) (hsize : s ≤ 6563)
    (hn : ¬ IsRepresentable s) : s ∈ ([3, 6, 11, 15, 22, 35, 38, 42, 55, 59, 66, 78, 83, 87, 95, 110, 118, 123, 131, 143, 187, 210,
   222, 227, 255, 262, 266, 278, 299, 303, 323, 326, 395, 402, 447, 483, 502, 551, 563, 590, 618,
   635, 678, 755, 838, 843, 902, 930, 942, 1003, 1007, 1034, 1091, 1162, 1190, 1295, 1326, 1482,
   1523, 1770, 1790, 2067, 2103, 2407, 2483, 2598, 2782, 3422, 3495, 4686, 5447, 5727, 6563] : List ℕ) := by
  have h := oma_small_exceptions s hsize hn
  rcases List.mem_append.mp h with h | h
  · exact h
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact False.elim ((Nat.squarefree_iff_prime_squarefree.mp hs 3 (by decide)) (by decide))
  · exact False.elim ((Nat.squarefree_iff_prime_squarefree.mp hs 5 (by decide)) (by decide))
  · exact False.elim ((Nat.squarefree_iff_prime_squarefree.mp hs 7 (by decide)) (by decide))
  · exact False.elim ((Nat.squarefree_iff_prime_squarefree.mp hs 17 (by decide)) (by decide))

/-- The remaining squarefree indices. -/
def H1 : Prop := ∀ n : ℕ, 6563 < n → Squarefree n → (2 ≤ n % 4 ∧ n % 2 = n.sqrt % 2 ∧ (n - (n.sqrt-1)^2).Prime ∧
    ((n - (n.sqrt-3)^2).Prime ∨ ∃ p : ℕ, p.Prime ∧ n - (n.sqrt-3)^2 = 3*p)) → IsRepresentable n

/-- Squares times a small squarefree exceptional index. -/
def H2 : Prop := ∀ s t : ℕ, s ∈ ([3, 6, 11, 15, 22, 35, 38, 42, 55, 59, 66, 78, 83, 87, 95, 110, 118, 123, 131, 143, 187, 210,
   222, 227, 255, 262, 266, 278, 299, 303, 323, 326, 395, 402, 447, 483, 502, 551, 563, 590, 618,
   635, 678, 755, 838, 843, 902, 930, 942, 1003, 1007, 1034, 1091, 1162, 1190, 1295, 1326, 1482,
   1523, 1770, 1790, 2067, 2103, 2407, 2483, 2598, 2782, 3422, 3495, 4686, 5447, 5727, 6563] : List ℕ) →
  1 < t → 6563 < s*t^2 → (2 ≤ (s*t^2) % 4 ∧ (s*t^2) % 2 = (s*t^2).sqrt % 2 ∧ ((s*t^2) - ((s*t^2).sqrt-1)^2).Prime ∧
    (((s*t^2) - ((s*t^2).sqrt-3)^2).Prime ∨ ∃ p : ℕ, p.Prime ∧ (s*t^2) - ((s*t^2).sqrt-3)^2 = 3*p)) → IsRepresentable (s*t^2)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a393168.main := by
  intro hlarge hsmall n hn
  by_contra hnrep
  have conditions (k : ℕ) (hk : 6563 < k) (hkrep : ¬ IsRepresentable k) : (2 ≤ k % 4 ∧ k % 2 = k.sqrt % 2 ∧ (k - (k.sqrt-1)^2).Prime ∧
    ((k - (k.sqrt-3)^2).Prime ∨ ∃ p : ℕ, p.Prime ∧ k - (k.sqrt-3)^2 = 3*p)) := by
    have hr : 2 ≤ k%4 := by
      by_contra! h
      exact hkrep (oma_bounded_square_four hk (by omega))
    have hpar : k%2=k.sqrt%2 := by
      by_contra h
      exact hkrep (oma_representable_odd_gap k h)
    exact ⟨hr, hpar, oma_first_residual_prime hk hpar hkrep (oma_pair_repr k),
      oma_second_prime_obstruction k hk hpar hkrep (oma_pair_repr k)⟩
  obtain ⟨s,t,hs,ht,rfl⟩ := oma_squarefree_decomp (by omega : 0<n)
  have hsr : ¬ IsRepresentable s := fun h => hnrep (oma_repr_scale h t)
  by_cases hcut : 6563 < s
  · exact hsr (hlarge s hcut hs (conditions s hcut hsr))
  · have htbig : 1 < t := by
      by_contra! ht'
      have ht1 : t=1 := by omega
      simp [ht1] at hn
      omega
    exact hnrep (hsmall s t (small_core_mem hs (by omega) hsr) htbig hn (conditions _ hn hnrep))

end OMA.R_oeis_a393168_R1
