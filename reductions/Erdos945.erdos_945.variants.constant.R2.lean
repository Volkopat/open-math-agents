import FormalConjectures.ErdosProblems.«945»

/-! A collision criterion allowing one prime cube of arbitrary multiplicity.
The two estimates count integers with a pair of distinct large prime cubes,
split according to the size of the larger prime relative to the cofactor. -/
-- Credit: @Pixelstorm44
namespace OMA.R_Erdos945_erdos_945_variants_constant_R2
open Finset Filter Real Erdos945
open scoped Classical

private lemma small_product {s : Finset ℕ} {v : ℕ → ℕ}
    (h : ∀ p ∈ s, v p = 1 ∨ v p = 2) :
    ∃ a b : ℕ, (∏ p ∈ s, (v p + 1)) = 2^a * 3^b := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, by simp⟩
  | @insert p s hp ih =>
    obtain ⟨a,b,hab⟩ := ih (fun q hq => h q (mem_insert_of_mem hq))
    rw [prod_insert hp, hab]
    rcases h p (mem_insert_self ..) with h₁ | h₂
    · exact ⟨a+1,b,by rw [h₁, pow_succ]; ring⟩
    · exact ⟨a,b+1,by rw [h₂, pow_succ]; ring⟩

private lemma profile {t m : ℕ} (ht : 0 < t) (htm : t ≤ 2^m)
    (h : ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ p^3 ∣ t ∧ q^3 ∣ t) :
    ∃ a ≤ m, ∃ b ≤ m, ∃ e ≤ m, τ t = 2^a * 3^b * (e+1) := by
  classical
  have vals (p : ℕ) (hp : p ∈ t.primeFactors) (hc : ¬ p^3 ∣ t) :
      t.factorization p = 1 ∨ t.factorization p = 2 := by
    have pp := Nat.prime_of_mem_primeFactors hp
    have pos := pp.factorization_pos_of_dvd ht.ne' (Nat.dvd_of_mem_primeFactors hp)
    rw [pp.pow_dvd_iff_le_factorization ht.ne'] at hc
    omega
  have repr : ∃ a b e : ℕ, e ≤ m ∧ τ t = 2^a * 3^b * (e+1) := by
    rw [τ, Nat.card_divisors ht.ne']
    by_cases hex : ∃ p ∈ t.primeFactors, p^3 ∣ t
    · obtain ⟨p,hp,hc⟩ := hex
      have pp := Nat.prime_of_mem_primeFactors hp
      obtain ⟨a,b,hab⟩ := small_product (s := t.primeFactors.erase p)
        (v := t.factorization) (by
          intro q hq
          obtain ⟨hne,hmem⟩ := mem_erase.mp hq
          apply vals q hmem
          intro hd
          rcases lt_or_gt_of_ne hne with hl | hg
          · exact h ⟨q,p,Nat.prime_of_mem_primeFactors hmem,pp,hl,hd,hc⟩
          · exact h ⟨p,q,pp,Nat.prime_of_mem_primeFactors hmem,hg,hc,hd⟩)
      have he : 2 ^ t.factorization p ≤ 2 ^ m :=
        (Nat.pow_le_pow_left pp.two_le _).trans
          ((Nat.le_of_dvd ht (Nat.ordProj_dvd t p)).trans htm)
      refine ⟨a,b,t.factorization p,(pow_le_pow_iff_right₀ (by decide : 1 < (2:ℕ))).mp he,?_⟩
      rw [←prod_erase_mul _ (fun q => t.factorization q + 1) hp, hab]
    · obtain ⟨a,b,hab⟩ := small_product (s := t.primeFactors)
        (fun p hp => vals p hp (fun hc => hex ⟨p,hp,hc⟩))
      exact ⟨a,b,0,Nat.zero_le _,by simpa using hab⟩
  obtain ⟨a,b,e,he,hab⟩ := repr
  have htau := (Nat.card_divisors_le_self t).trans htm
  change τ t ≤ 2^m at htau
  rw [hab] at htau
  have ha : 2^a ≤ 2^a * 3^b := Nat.le_mul_of_pos_right _ (by positivity)
  have hb : 3^b ≤ 2^a * 3^b := Nat.le_mul_of_pos_left _ (by positivity)
  have hmul : 2^a * 3^b ≤ 2^a * 3^b * (e+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hpow : 2^a ≤ (2:ℕ)^m ↔ a ≤ m := (pow_le_pow_iff_right₀ (by decide : 1 < (2:ℕ)))
  exact ⟨a,hpow.mp (ha.trans (hmul.trans htau)),b,
    (pow_le_pow_iff_right₀ (by decide : 1 < (2:ℕ))).mp
      ((Nat.pow_le_pow_left (by decide : 2 ≤ 3) b).trans (hb.trans (hmul.trans htau))),
    e,he,hab⟩

private lemma multiples {n L d : ℕ} (hd : 0 < d) :
    (((Ioc n (n+L)).filter (d ∣ ·)).card : ℝ) ≤ (L:ℝ)/d + 1 := by
  classical
  have hu := Ioc_union_Ioc_eq_Ioc (Nat.zero_le n) (Nat.le_add_right n L)
  have hj : Disjoint ((Ioc 0 n).filter (d ∣ ·)) ((Ioc n (n+L)).filter (d ∣ ·)) := by
    rw [Finset.disjoint_left]
    intro t ht ht'
    have := (mem_Ioc.mp (mem_filter.mp ht).1).2
    have := (mem_Ioc.mp (mem_filter.mp ht').1).1
    omega
  have hc := card_union_of_disjoint hj
  rw [←filter_union, hu, Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div] at hc
  have hrem := Nat.mod_lt n hd
  have hleft := Nat.div_add_mod n d
  have hright := Nat.div_add_mod (n+L) d
  have hbound : ((Ioc n (n+L)).filter (d ∣ ·)).card * d ≤ L + d := by
    rw [hc, Nat.mul_add] at hright
    rw [Nat.mul_comm]
    omega
  rw [←div_self (by positivity : (d:ℝ) ≠ 0), ←add_div, le_div_iff₀ (by positivity)]
  exact_mod_cast hbound

private lemma small_cubes (n k : ℕ) :
    ((Ioc n (n+16*k)).filter (fun t => ∃ p : ℕ, p.Prime ∧ p ≤ k ∧ p^3 ∣ t)).card ≤ 9*k := by
  classical
  let S := Ioc n (n+16*k)
  let B (i : ℕ) := S.filter ((i+2)^3 ∣ ·)
  have sub : (S.filter (fun t => ∃ p : ℕ, p.Prime ∧ p ≤ k ∧ p^3 ∣ t)) ⊆
      (range k).biUnion B := by
    intro t ht
    obtain ⟨ht,p,pp,hpk,hdiv⟩ := mem_filter.mp ht
    have hp := pp.two_le
    refine mem_biUnion.mpr ⟨p-2,mem_range.mpr (by omega),?_⟩
    simpa [B,Nat.sub_add_cancel hp,ht] using hdiv
  have single (i : ℕ) : ((B i).card : ℝ) ≤
      (8*k/(i+1) - 8*k/(i+2) : ℝ) + 1 := by
    have hh := multiples (n:=n) (L:=16*k) (d:=(i+2)^3) (by positivity)
    change ((B i).card : ℝ) ≤ _ at hh
    push_cast at hh
    apply hh.trans
    apply add_le_add_left
    field_simp
    ring_nf
    nlinarith [show 0 ≤ (k:ℝ)*i by positivity, show 0 ≤ (k:ℝ)*i^2 by positivity]
  have hs := Finset.sum_le_sum fun i (_ : i ∈ range k) => single i
  have htel := sum_range_sub' (fun i : ℕ => (8*k/(i+1) : ℝ)) k
  push_cast at htel
  simp only [add_assoc, one_add_one_eq_two] at htel
  rw [sum_add_distrib, htel] at hs
  simp at hs
  have hk' : 0 ≤ (8*(k:ℝ))/((k:ℝ)+1) := by positivity
  have htotal : (∑ i ∈ range k, (B i).card) ≤ 9*k := by
    exact_mod_cast (show (∑ i ∈ range k, ((B i).card:ℝ)) ≤ 9*(k:ℝ) by linarith)
  exact (card_le_card sub).trans (card_biUnion_le.trans htotal)

private lemma short_cofactors (n k : ℕ) :
    ((Ioc n (n+16*k)).filter (fun t => ∃ u : ℕ, 0 < u ∧ u ≤ k ∧ ∃ r : ℕ,
      6 ≤ r ∧ k < r ∧ t = r^3*u)).card ≤ k := by
  classical
  let B (u : ℕ) := (Ioc n (n+16*k)).filter (fun t => ∃ r : ℕ,
    6 ≤ r ∧ k < r ∧ t = r^3*u)
  have hsub : ((Ioc n (n+16*k)).filter (fun t => ∃ u : ℕ, 0 < u ∧ u ≤ k ∧ ∃ r : ℕ,
      6 ≤ r ∧ k < r ∧ t = r^3*u)) ⊆ (Icc 1 k).biUnion B := by
    intro t ht
    obtain ⟨hm,u,hpos,hu,hr⟩ := mem_filter.mp ht
    exact mem_biUnion.mpr ⟨u,mem_Icc.mpr ⟨hpos,hu⟩,mem_filter.mpr ⟨hm,hr⟩⟩
  have hcard (u : ℕ) (hu : u ∈ Icc 1 k) : (B u).card ≤ 1 := by
    have hu' := (mem_Icc.mp hu).1
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha,r,hr,hkr,rfl⟩ := mem_filter.mp ha
    obtain ⟨hb,s,hs,hks,rfl⟩ := mem_filter.mp hb
    have sep (i j : ℕ) (hi : 6 ≤ i) (hk : k < i) (hij : i < j) :
        i^3*u + 16*k < j^3*u := by
      have step : 16*k < 3*i^2 := by nlinarith [Nat.mul_le_mul_left i hi]
      have step' : 3*i^2 ≤ 3*i^2*u := Nat.le_mul_of_pos_right _ hu'
      have grows := Nat.mul_le_mul_right u (Nat.pow_le_pow_left (Nat.succ_le_of_lt hij) 3)
      nlinarith [Nat.zero_le (i*u)]
    obtain ⟨hal,hau⟩ := mem_Ioc.mp ha
    obtain ⟨hbl,hbu⟩ := mem_Ioc.mp hb
    rcases lt_trichotomy r s with h | rfl | h
    · have := sep _ _ hr hkr h
      omega
    · rfl
    · have := sep _ _ hs hks h
      omega
  calc
    _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ _ ∈ Icc 1 k, 1 := sum_le_sum hcard
    _ = _ := by simp

private lemma collision {m n k : ℕ} (hsize : (m+1)^3 ≤ k) (hmax : n+16*k ≤ 2^m)
    (h₁ : ((Ioc n (n+16*k)).filter (fun t => ∃ p q : ℕ,
      p.Prime ∧ q.Prime ∧ k < p ∧ p < q ∧ p^3 ∣ t ∧ q^3 ∣ t ∧ k*(p*q)^3 < t ∧ q^4 ≤ t)).card ≤ k)
    (h₂ : ((Ioc n (n+16*k)).filter (fun t => ∃ p q : ℕ,
      p.Prime ∧ q.Prime ∧ k < p ∧ p < q ∧ p^3 ∣ t ∧ q^3 ∣ t ∧ k*(p*q)^3 < t ∧ t < q^4)).card ≤ k) :
    ∃ a ∈ Ioc n (n+16*k), ∃ b ∈ Ioc n (n+16*k), a ≠ b ∧ τ a = τ b := by
  classical
  let S := Ioc n (n+16*k)
  let P (t : ℕ) := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ p^3 ∣ t ∧ q^3 ∣ t
  let small := S.filter (fun t => ∃ p : ℕ, p.Prime ∧ p ≤ k ∧ p^3 ∣ t)
  let mid := S.filter (fun t => ∃ p q : ℕ,
    p.Prime ∧ q.Prime ∧ k < p ∧ p < q ∧ p^3 ∣ t ∧ q^3 ∣ t ∧ k*(p*q)^3 < t ∧ q^4 ≤ t)
  let large := S.filter (fun t => ∃ p q : ℕ,
    p.Prime ∧ q.Prime ∧ k < p ∧ p < q ∧ p^3 ∣ t ∧ q^3 ∣ t ∧ k*(p*q)^3 < t ∧ t < q^4)
  let short := S.filter (fun t => ∃ u : ℕ, 0 < u ∧ u ≤ k ∧ ∃ r : ℕ, 6 ≤ r ∧ k < r ∧ t = r^3*u)
  have hsub : S.filter P ⊆ (small ∪ mid ∪ large) ∪ short := by
    intro t ht
    obtain ⟨hm,p,q,pp,qp,hl,hp,hq⟩ := mem_filter.mp ht
    rcases le_or_gt p k with hs | hs
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hm,p,pp,hs,hp⟩)))
    rcases lt_or_ge (k*(p*q)^3) t with hbig | hshort
    swap
    · have hd : (p*q)^3 ∣ t := by
        rw [mul_pow]
        exact (Nat.coprime_pow_primes 3 3 pp qp hl.ne).mul_dvd_of_dvd_of_dvd hp hq
      obtain ⟨u,he⟩ := hd
      have p2 := pp.two_le
      have q3 : 3 ≤ q := by omega
      have hpq : 6 ≤ p*q := by simpa using Nat.mul_le_mul p2 q3
      have hlt : k < p*q := hs.trans_le (Nat.le_mul_of_pos_right _ qp.pos)
      have hu : u ≤ k := by
        rw [he, Nat.mul_comm k] at hshort
        exact Nat.le_of_mul_le_mul_left hshort (by positivity)
      have hlo := (mem_Ioc.mp hm).1
      have hpos : 0 < u := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at he; omega
      exact mem_union_right _ (mem_filter.mpr ⟨hm,u,hpos,hu,p*q,hpq,hlt,he⟩)
    apply mem_union_left
    rcases le_or_gt (q^4) t with he | he
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hm,p,q,pp,qp,hs,hl,hp,hq,hbig,he⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨hm,p,q,pp,qp,hs,hl,hp,hq,hbig,he⟩)
  have hbad := (card_le_card hsub).trans (card_union_le ..)
  have hun := card_union_le small mid
  have hun' := card_union_le (small ∪ mid) large
  have hshort : short.card ≤ k := short_cofactors n k
  have hsmall : small.card ≤ 9*k := small_cubes n k
  change mid.card ≤ k at h₁
  change large.card ≤ k at h₂
  have hs : S.card = 16*k := by simp [S]
  have hparts := card_filter_add_card_filter_not (s:=S) P
  let G := S.filter (fun t => ¬P t)
  change _ + G.card = _ at hparts
  let I := range (m+1)
  let V := (I ×ˢ (I ×ˢ I)).image (fun z : ℕ × ℕ × ℕ => (2:ℕ)^z.1 * 3^z.2.1 * (z.2.2+1))
  have hv : V.card ≤ (m+1)^3 := by
    apply card_image_le.trans
    simp [I,pow_succ,Nat.mul_assoc]
  have hpos : 0 < (m+1)^3 := by positivity
  have maps : Set.MapsTo τ ↑G ↑V := by
    intro t ht
    obtain ⟨hS,hP⟩ := mem_filter.mp ht
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hS
    obtain ⟨a,ha,b,hb,e,he,hh⟩ := profile (by omega : 0<t) (hu.trans hmax) hP
    exact mem_image.mpr ⟨(a,b,e),by simp [I,ha,hb,he],hh.symm⟩
  obtain ⟨a,ha,b,hb,hne,heq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to (by omega : V.card < G.card) maps
  exact ⟨a,(mem_filter.mp ha).1,b,(mem_filter.mp hb).1,hne,heq⟩

/-- Pairs of distinct prime cubes with both roots and their common cofactor above k,
and the larger root at most the fourth root of the integer. -/
def H1 : Prop := ∃ A : ℕ, ∀ m n k : ℕ, (m+1)^A ≤ k → n+16*k ≤ 2^m →
  ((Ioc n (n+16*k)).filter (fun t => ∃ p q : ℕ,
    p.Prime ∧ q.Prime ∧ k < p ∧ p < q ∧ p^3 ∣ t ∧ q^3 ∣ t ∧ k*(p*q)^3 < t ∧ q^4 ≤ t)).card ≤ k

/-- The remaining pairs with cofactor after division by (pq)³ above k,
and cofactor after division by q³ below q. -/
def H2 : Prop := ∃ A : ℕ, ∀ m n k : ℕ, (m+1)^A ≤ k → n+16*k ≤ 2^m →
  ((Ioc n (n+16*k)).filter (fun t => ∃ p q : ℕ,
    p.Prime ∧ q.Prime ∧ k < p ∧ p < q ∧ p^3 ∣ t ∧ q^3 ∣ t ∧ k*(p*q)^3 < t ∧ t < q^4)).card ≤ k

theorem main : H1 → H2 → type_of% @Erdos945.erdos_945.variants.constant := by
  rintro ⟨A,hA⟩ ⟨B,hB⟩
  let D := max 3 (max A B)
  let C := 2*D+1
  refine ⟨(C:ℝ),by dsimp [C]; positivity,?_⟩
  have hslow := (isLittleO_log_rpow_rpow_atTop (C:ℝ) (by norm_num : (0:ℝ)<1)).bound
    (by norm_num : (0:ℝ)<1)
  filter_upwards [eventually_ge_atTop (1:ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 16,
    hslow] with x hx hlog hslowx
  have xpos : 0 < x := by linarith
  have logpos : 0 ≤ log x := by linarith
  have hslow' : log x ^ C ≤ x := by
    simpa [Real.rpow_natCast,Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg logpos,
      abs_of_nonneg xpos.le, abs_of_nonneg (pow_nonneg logpos C)] using hslowx
  let j := ⌈Real.logb 2 x⌉₊
  let m := j+1
  let k := (m+1)^D
  let n := ⌊x⌋₊
  have hj : x ≤ (2:ℝ)^j := by
    calc x = (2:ℝ) ^ Real.logb 2 x := (Real.rpow_logb (by norm_num) (by norm_num) xpos).symm
         _ ≤ (2:ℝ) ^ (j:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
         _ = _ := Real.rpow_natCast ..
  have hlogb : 0 ≤ Real.logb 2 x := by rw [Real.logb]; positivity
  have hceil : (j:ℝ) < Real.logb 2 x + 1 := Nat.ceil_lt_add_one hlogb
  have hmsq : (m:ℝ)+1 ≤ log x ^ 2 := by
    dsimp [m]
    push_cast
    rw [Real.logb] at hceil
    have hd : log x / log 2 ≤ 2*log x := by
      rw [div_le_iff₀ (Real.log_pos (by norm_num))]
      nlinarith [mul_nonneg logpos (show 0 ≤ log 2 - 1/2 by linarith [Real.log_two_gt_d9])]
    nlinarith [mul_nonneg logpos (show 0 ≤ log x - 16 by linarith)]
  have hwidth : 16*(k:ℝ) ≤ log x ^ C := by
    dsimp [k,C]
    push_cast
    calc 16 * ((m:ℝ)+1)^D ≤ log x * (log x ^ 2)^D := by gcongr
         _ = _ := by rw [pow_succ _ (2*D),pow_mul]; ring
  have hn : (n:ℝ) ≤ x := Nat.floor_le xpos.le
  have hmax : n+16*k ≤ 2^m := by
    have h : (n:ℝ)+16*(k:ℝ) ≤ (2:ℝ)^m := by
      dsimp [m]
      rw [pow_succ]
      linarith [hwidth.trans hslow']
    exact_mod_cast h
  have hbnd (i : ℕ) (hi : i ≤ D) : (m+1)^i ≤ k :=
    Nat.pow_le_pow_right (by omega) hi
  obtain ⟨a,ha,b,hb,hne,heq⟩ := collision (hbnd 3 (le_max_left ..)) hmax
    (hA m n k (hbnd A ((le_max_left ..).trans (le_max_right ..))) hmax)
    (hB m n k (hbnd B ((le_max_right ..).trans (le_max_right ..))) hmax)
  have inside {t : ℕ} (ht : t ∈ Ioc n (n+16*k)) :
      (t:ℝ) ∈ Set.Icc x (x + log x ^ (C:ℝ)) := by
    obtain ⟨hlo,hhi⟩ := mem_Ioc.mp ht
    have hu : (t:ℝ) ≤ (n:ℝ)+16*(k:ℝ) := by exact_mod_cast hhi
    rw [Real.rpow_natCast]
    exact ⟨((Nat.floor_lt xpos.le).mp hlo).le,by linarith⟩
  exact ⟨a,b,hne,inside ha,inside hb,heq⟩

end OMA.R_Erdos945_erdos_945_variants_constant_R2
