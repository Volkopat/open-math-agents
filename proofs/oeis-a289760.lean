import OMAStatements.S_oeis_a289760
import Mathlib

open OMA.S_oeis_a289760 Finset

/- At 13 the residue 5 is missing. The primes congruent to 5 modulo 6 reduce to the two-square theorem, and 19 is a finite computation. -/
private lemma missing_thirteen : HasMissingResidue 13 := by
  refine ⟨5, ?_⟩
  have small : ∀ a b : ZMod 13, a^6 + b^6 ∈ ({0,1,2,11,12} : Finset (ZMod 13)) := by decide
  have impossible : ∀ u ∈ ({0,1,2,11,12} : Finset (ZMod 13)),
      ∀ v ∈ ({0,1,2,11,12} : Finset (ZMod 13)), u+v ≠ 5 := by decide
  rintro ⟨a,b,c,d,he⟩
  exact impossible _ (small a b) _ (small c d) (by simpa only [add_assoc] using he)

private lemma no_missing_five_mod_six {p : ℕ} (hp : p.Prime) (hcong : p % 6 = 5) :
    ¬ HasMissingResidue p := by
  let _ : Fact p.Prime := ⟨hp⟩
  have power (a : ZMod p) : (a ^ ((p+1)/6)) ^ 6 = a^2 := by
    rw [← pow_mul, show (p+1)/6*6 = p+1 by omega, pow_succ, ZMod.pow_card, sq]
  rintro ⟨r,hr⟩
  obtain ⟨a,b,h⟩ := ZMod.sq_add_sq p r
  apply hr
  exact ⟨a^((p+1)/6), b^((p+1)/6), 0, 0, by simpa only [power, zero_pow (by decide : 6 ≠ 0), add_zero] using h⟩

private lemma no_missing_nineteen : ¬ HasMissingResidue 19 := by
  let v : Fin 4 → ZMod 19 := ![0,1,2,4]
  have check : ∀ r : ZMod 19, ∃ i j k l : Fin 4,
      v i ^ 6 + v j ^ 6 + v k ^ 6 + v l ^ 6 = r := by
    dsimp only [v]
    decide
  rintro ⟨r, hr⟩
  obtain ⟨i,j,k,l,h⟩ := check r
  exact hr ⟨v i, v j, v k, v l, h⟩

/- The nonzero sixth powers form a multiplicative subgroup of size h when p = 6h+1. -/
private lemma oma_sixth_image_card {p h : ℕ} [Fact p.Prime] (ph : p = 6*h+1) :
    (Finset.univ.image (fun u : (ZMod p)ˣ => (u : ZMod p)^6)).card = h := by
  classical
  let T := Finset.univ.image (fun u : (ZMod p)ˣ => u^6)
  have coeT : (T : Set (ZMod p)ˣ) =
      ((powMonoidHom 6 : (ZMod p)ˣ →* (ZMod p)ˣ).range : Set (ZMod p)ˣ) := by
    ext u
    simp [T]
  have cardT : T.card = Nat.card (powMonoidHom 6 : (ZMod p)ˣ →* (ZMod p)ˣ).range := by
    calc
      T.card = Nat.card (T : Set (ZMod p)ˣ) := by simp
      _ = _ := Nat.card_congr (Equiv.setCongr coeT)
  have img : Finset.univ.image (fun u : (ZMod p)ˣ => (u : ZMod p)^6) =
      T.image (fun u : (ZMod p)ˣ => (u : ZMod p)) := by
    simp [T, Finset.image_image, Function.comp_def]
  have gsize : Nat.card (ZMod p)ˣ = 6*h := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : p.Prime)]
    omega
  rw [img, Finset.card_image_of_injective _ Units.val_injective, cardT,
    IsCyclic.card_powMonoidHom_range, gsize, Nat.gcd_eq_right (by simp)]
  omega

/- Let B be the sums of two sixth powers. A missing four-term sum r makes B disjoint from r-B. Three nonzero sixth-power cosets, together with zero, would violate the resulting size bound. -/
private lemma oma_missing_identity {p h : ℕ} [Fact p.Prime] (hph : p=6*h+1)
    (hcard : (univ.image (fun x : (ZMod p)ˣ => (x : ZMod p)^6)).card = h)
    (miss : HasMissingResidue p) :
    ∃ s t : ZMod p, ∀ x : ZMod p,
     (1+x^6)^(2*h+1)-s*(1+x^6)^(h+1)+t*(1+x^6)=0 := by
  classical
  obtain ⟨r, hr⟩ := miss
  let B : Finset (ZMod p) := univ.image (fun w : ZMod p × ZMod p => w.1^6 + w.2^6)
  have memB (v : ZMod p) : v ∈ B ↔ ∃ a b : ZMod p, a^6+b^6=v := by
    simp [B]
  have zeroB : 0 ∈ B := (memB _).2 ⟨0,0,by norm_num⟩
  have oneB : 1 ∈ B := (memB _).2 ⟨1,0,by norm_num⟩
  have hdis : Disjoint B (B.image (fun x => r-x)) := by
    refine disjoint_left.mpr ?_
    intro z hz hz'
    obtain ⟨v,hv,hd⟩ := mem_image.mp hz'
    obtain ⟨a,b,hab⟩ := (memB _).mp hz
    obtain ⟨c,d,hcd⟩ := (memB _).mp hv
    exact hr ⟨a,b,c,d,by linear_combination hab+hcd-hd⟩
  have cardB : 2*B.card ≤ p := by
    have hh := card_le_univ (B ∪ B.image (fun x => r-x))
    rw [card_union_of_disjoint hdis,card_image_of_injective B (by intro x y; simp),ZMod.card] at hh
    omega
  let H := univ.image (fun x : (ZMod p)ˣ => (x : ZMod p)^6)
  let orbit (v : ZMod p) := H.image (fun x => v*x)
  have ocard (v : ZMod p) (hv : v ≠ 0) : (orbit v).card = h := by
    exact (card_image_of_injective H (mul_right_injective₀ hv)).trans hcard
  have oB {v : ZMod p} (hv : v ∈ B) : orbit v ⊆ B := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hy
    obtain ⟨u,_,rfl⟩ := mem_image.mp hw
    obtain ⟨a,b,rfl⟩ := (memB _).mp hv
    exact (memB _).mpr ⟨a*u,b*u,by simp only [mul_pow]; ring⟩
  have oprop {v y : ZMod p} (hv : v ≠ 0) (hy : y ∈ orbit v) : y ≠ 0 ∧ y^h=v^h := by
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hy
    obtain ⟨u,_,rfl⟩ := mem_image.mp hw
    constructor
    · exact mul_ne_zero hv (pow_ne_zero _ u.ne_zero)
    · rw [mul_pow,←pow_mul,show 6*h=p-1 by omega,ZMod.pow_card_sub_one_eq_one u.ne_zero,mul_one]
  have dis {v w : ZMod p} (hv : v ≠ 0) (hw : w ≠ 0) (hd : v^h ≠ w^h) :
      Disjoint (orbit v) (orbit w) :=
    disjoint_left.mpr fun _ hy hz => hd ((oprop hv hy).2.symm.trans (oprop hw hz).2)
  have atmost {b c : ZMod p} (hb : b ∈ B) (hc : c ∈ B) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
      (hb1 : b^h ≠ 1) (hc1 : c^h ≠ 1) : b^h=c^h := by
    by_contra hn
    have d1 := dis (v:=(1:ZMod p)) one_ne_zero hb0 (by simpa using hb1.symm)
    have d2 := dis (v:=(1:ZMod p)) one_ne_zero hc0 (by simpa using hc1.symm)
    have d3 := dis hb0 hc0 hn
    let U := orbit 1 ∪ orbit b ∪ orbit c
    have cardU : U.card = 3*h := by
      dsimp only [U]
      rw [card_union_of_disjoint (show Disjoint (orbit 1 ∪ orbit b) (orbit c) from disjoint_sup_left.mpr ⟨d2,d3⟩),card_union_of_disjoint d1,
        ocard _ one_ne_zero, ocard _ hb0, ocard _ hc0]
      omega
    have zeroU : 0 ∉ U := by
      simp only [U,mem_union]
      rintro ((ha|ha)|ha)
      · exact (oprop one_ne_zero ha).1 rfl
      · exact (oprop hb0 ha).1 rfl
      · exact (oprop hc0 ha).1 rfl
    have sub : insert 0 U ⊆ B :=
      insert_subset zeroB (union_subset (union_subset (oB oneB) (oB hb)) (oB hc))
    have hh := card_le_card sub
    rw [card_insert_of_notMem zeroU,cardU] at hh
    omega
  obtain ⟨z,hz⟩ : ∃ z : ZMod p, ∀ b ∈ B, b = 0 ∨ b^h=1 ∨ b^h=z := by
    by_cases ex : ∃ c ∈ B, c ≠ 0 ∧ c^h ≠ 1
    · obtain ⟨c,hc,hc0,hc1⟩ := ex
      refine ⟨c^h, fun b hb => ?_⟩
      by_cases hb0 : b=0
      · exact Or.inl hb0
      by_cases hb1 : b^h=1
      · exact Or.inr (Or.inl hb1)
      exact Or.inr (Or.inr (atmost hb hc hb0 hc0 hb1 hc1))
    · refine ⟨1, fun b hb => ?_⟩
      by_contra! bad
      exact ex ⟨b,hb,bad.1,bad.2.1⟩
  refine ⟨1+z,z,fun x => ?_⟩
  let v : ZMod p := 1+x^6
  have hv : v ∈ B := (memB _).2 ⟨1,x,by simp [v]⟩
  change v^(2*h+1)-(1+z)*v^(h+1)+z*v=0
  have fact : v*(v^h-1)*(v^h-z) = 0 := by
    rcases hz v hv with hh | hh | hh <;> simp [hh]
  rw [pow_succ, pow_succ,show 2*h=h*2 by omega,pow_mul]
  linear_combination fact

/- Sum the polynomial identity over units with weight x^(6(h-i)). Only binomial terms of degrees i and h+i survive. -/
private lemma oma_waring_hits {h i j : ℕ} (hh : 5 ≤ h) (hi : 2 ≤ i) (hi' : i ≤ 4)
    (hj : j ≤ 2*h+1) : h ∣ h-i+j ↔ j=i ∨ j=h+i := by
  constructor
  · rintro ⟨z,hz⟩
    have hz3 : z < 3 := by
      by_contra! hg
      have := Nat.mul_le_mul_left h hg
      omega
    interval_cases z <;> simp_all <;> omega
  · rintro (rfl | rfl)
    · exact ⟨1, by omega⟩
    · exact ⟨2, by omega⟩

private lemma oma_waring_moment {p h i : ℕ} [Fact p.Prime]
    (hph : p = 6*h+1) (hh : 5 ≤ h) (hi : 2 ≤ i) (hi' : i ≤ 4)
    (m : ℕ) (hm : m ≤ 2*h+1) :
    (∑ x : (ZMod p)ˣ, (x : ZMod p)^(6*(h-i)) * (1+(x : ZMod p)^6)^m) =
      -(m.choose i : ZMod p) - (m.choose (h+i) : ZMod p) := by
  classical
  have expnd (x : (ZMod p)ˣ) :
      (x : ZMod p)^(6*(h-i)) * (1+(x : ZMod p)^6)^m =
      ∑ j ∈ range (m+1), (x : ZMod p)^(6*(h-i+j)) * m.choose j := by
    rw [add_comm (1 : ZMod p), add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [one_pow, mul_one, ← pow_mul]
    rw [← mul_assoc, ← pow_add, Nat.mul_add]
  simp_rw [expnd]
  rw [Finset.sum_comm]
  have inner (j : ℕ) (hj : j ∈ range (m+1)) :
      (∑ x : (ZMod p)ˣ, (x : ZMod p)^(6*(h-i+j)) * m.choose j) =
        -(if j=i then (m.choose i : ZMod p) else 0) -
         (if j=h+i then (m.choose (h+i) : ZMod p) else 0) := by
    rw [← Finset.sum_mul, FiniteField.sum_pow_units, ZMod.card,
      show p-1 = 6*h by omega]
    have hd : 6*h ∣ 6*(h-i+j) ↔ j=i ∨ j=h+i := by
      rw [Nat.mul_dvd_mul_iff_left (by decide : 0 < 6)]
      exact oma_waring_hits hh hi hi' (by have := Finset.mem_range.mp hj; omega)
    simp only [hd]
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl inner,Finset.sum_sub_distrib,Finset.sum_neg_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_range]
  split_ifs <;> simp_all [Nat.choose_eq_zero_of_lt]

private lemma oma_waring_extract {p h : ℕ} [Fact p.Prime]
    (hph : p = 6*h+1) (hh : 5 ≤ h) (s t : ZMod p)
    (hyp : ∀ x : ZMod p, (1+x^6)^(2*h+1) - s*(1+x^6)^(h+1) + t*(1+x^6) = 0)
    (i : ℕ) (hi : 2 ≤ i) (hi' : i ≤ 4) :
    ((2*h+1).choose i : ZMod p) + (2*h+1).choose (h+i) = s*(h+1).choose i := by
  let weight (x : (ZMod p)ˣ) : ZMod p := (x : ZMod p)^(6*(h-i))
  have iden (x : (ZMod p)ˣ) :
      weight x * (1+(x:ZMod p)^6)^(2*h+1) -
      s*(weight x * (1+(x:ZMod p)^6)^(h+1)) +
      t*(weight x * (1+(x:ZMod p)^6)^1) = 0 := by
    linear_combination weight x * hyp (x : ZMod p)
  have sumId := Finset.sum_congr (s₁ := (Finset.univ : Finset (ZMod p)ˣ)) rfl (fun x _ => iden x)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const_zero] at sumId
  dsimp only [weight] at sumId
  rw [oma_waring_moment hph hh hi hi' _ (by omega),
    oma_waring_moment hph hh hi hi' _ (by omega),
    oma_waring_moment hph hh hi hi' _ (by omega)] at sumId
  simp only [Nat.choose_eq_zero_of_lt (by omega : h+1 < h+i),
    Nat.choose_eq_zero_of_lt (by omega : 1 < i),
    Nat.choose_eq_zero_of_lt (by omega : 1 < h+i), Nat.cast_zero, sub_zero,
    neg_zero, mul_zero, add_zero] at sumId
  linear_combination -sumId

/- Use consecutive binomial coefficient ratios without division. The rows i = 2, 3, 4 give three linear equations in the common coefficient s and the shifted binomial coefficient T 1. -/
private lemma oma_waring_coeff_contradiction {p h : ℕ} [Fact p.Prime]
    (ph : p = 6*h+1) (hh : 5 ≤ h) (_hp : 31 ≤ p) (s : ZMod p)
    (rows : ∀ i : ℕ, 2 ≤ i → i ≤ 4 →
      ((2*h+1).choose i : ZMod p) + ((2*h+1).choose (h+i) : ZMod p) =
        s * ((h+1).choose i : ZMod p)) : False := by
  let B (i : ℕ) : ZMod p := (2*h+1).choose i
  let D (i : ℕ) : ZMod p := (h+1).choose i
  let T (i : ℕ) : ZMod p := (2*h+1).choose (h+i)
  have h6 : 6*(h : ZMod p)+1 = 0 := calc
    _ = ((6*h+1 : ℕ) : ZMod p) := by push_cast; ring
    _ = (p : ZMod p) := congrArg (fun n : ℕ => (n : ZMod p)) ph.symm
    _ = 0 := ZMod.natCast_self p
  have step (n k : ℕ) (hk : k ≤ n) :
      (n.choose (k+1) : ZMod p)*((k : ZMod p)+1) =
        (n.choose k : ZMod p)*((n : ZMod p)-k) := by
    have e := congrArg (fun t : ℕ => (t : ZMod p)) (Nat.choose_succ_right_eq n k)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hk] using e
  have bs (i : ℕ) (hi : i ≤ 4) : (6*((i:ZMod p)+1))*B (i+1) = (4-6*i)*B i := by
    have e := step (2*h+1) i (by omega)
    change B (i+1)*((i:ZMod p)+1) = B i*(((2*h+1 : ℕ):ZMod p)-i) at e
    push_cast at e
    linear_combination 6*e + (2*B i)*h6
  have ds (i : ℕ) (hi : i ≤ 4) : (6*((i:ZMod p)+1))*D (i+1) = (5-6*i)*D i := by
    have e := step (h+1) i (by omega)
    change D (i+1)*((i:ZMod p)+1) = D i*(((h+1 : ℕ):ZMod p)-i) at e
    push_cast at e
    linear_combination 6*e + (D i)*h6
  have ts (i : ℕ) (hi : i ≤ 4) : (6*(i:ZMod p)+5)*T (i+1) = (5-6*i)*T i := by
    have e := step (2*h+1) (h+i) (by omega)
    change T (i+1)*(((h+i:ℕ):ZMod p)+1) = T i*(((2*h+1:ℕ):ZMod p)-(↑(h+i:ℕ))) at e
    push_cast at e
    linear_combination 6*e + (T i - T (i+1))*h6
  have b0 : B 0 = 1 := by simp [B]
  have d0 : D 0 = 1 := by simp [D]
  have b1 : 6*B 1 = 4 := by linear_combination bs 0 (by decide) + 4*b0
  have b2 : 72*B 2 = -8 := by linear_combination 6*bs 1 (by decide) - 2*b1
  have b3 : 1296*B 3 = 64 := by linear_combination 72*bs 2 (by decide) - 8*b2
  have b4 : 31104*B 4 = -896 := by linear_combination 1296*bs 3 (by decide) -14*b3
  have d1 : 6*D 1 = 5 := by linear_combination ds 0 (by decide) + 5*d0
  have d2 : 72*D 2 = -5 := by linear_combination 6*ds 1 (by decide) - d1
  have d3 : 1296*D 3 = 35 := by linear_combination 72*ds 2 (by decide) - 7*d2
  have d4 : 31104*D 4 = -455 := by linear_combination 1296*ds 3 (by decide) -13*d3
  have t2 : 11*T 2 = -T 1 := by linear_combination ts 1 (by decide)
  have t3 : 187*T 3 = 7*T 1 := by linear_combination 11*ts 2 (by decide) - 7*t2
  have t4 : 4301*T 4 = -91*T 1 := by linear_combination 187*ts 3 (by decide) - 13*t3
  have rr (i : ℕ) (hi : 2 ≤ i) (hi' : i ≤ 4) : B i + T i = s*D i := rows i hi hi'
  have e2 : -72*T 1 + 55*s - 88 = 0 := by
    linear_combination 792*rr 2 (by decide) (by decide) -11*b2 -72*t2 + (11*s)*d2
  have e3 : 9072*T 1 - 6545*s +11968 = 0 := by
    linear_combination 242352*rr 3 (by decide) (by decide) -187*b3 -1296*t3 + (187*s)*d3
  have e4 : -2830464*T 1 +1956955*s -3853696 = 0 := by
    linear_combination 133778304*rr 4 (by decide) (by decide) -4301*b4 -31104*t4 + (4301*s)*d4
  have absurdity : (74800 : ZMod p) = 0 := by linear_combination 27846*e2 + 533*e3 + e4
  have hd : p ∣ (74800 : ℕ) := (ZMod.natCast_eq_zero_iff 74800 p).mp absurdity
  rw [show (74800 : ℕ) = 16*25*11*17 by decide] at hd
  have pp : p.Prime := Fact.out
  rcases pp.dvd_mul.mp hd with hd | hd
  · rcases pp.dvd_mul.mp hd with hd | hd
    · rcases pp.dvd_mul.mp hd with hd | hd <;> have := Nat.le_of_dvd (by decide) hd <;> omega
    · have := Nat.le_of_dvd (by decide) hd; omega
  · have := Nat.le_of_dvd (by decide) hd; omega

theorem OMA.solution : type_of% @OMA.S_oeis_a289760.main := by
  refine ⟨⟨by decide, missing_thirteen⟩, ?_⟩
  rintro p ⟨hp, hmiss⟩
  by_contra! hlarge
  have nd₂ : ¬ 2 ∣ p := by
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd
    omega
  have nd₃ : ¬ 3 ∣ p := by
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd
    omega
  by_cases rem5 : p % 6 = 5
  · exact no_missing_five_mod_six hp rem5 hmiss
  have rem1 : p % 6 = 1 := by omega
  by_cases small : p < 31
  · have alternatives : p = 19 ∨ p = 25 := by omega
    rcases alternatives with rfl | rfl
    · exact no_missing_nineteen hmiss
    · exact (by decide : ¬ Nat.Prime 25) hp
  let _ : Fact p.Prime := ⟨hp⟩
  let h := p / 6
  have hph : p = 6*h+1 := by dsimp [h]; omega
  have hh : 5 ≤ h := by omega
  obtain ⟨s,t,hid⟩ := oma_missing_identity hph (oma_sixth_image_card hph) hmiss
  exact oma_waring_coeff_contradiction hph hh (by omega) s
    (oma_waring_extract hph hh s t hid)
