import OMAReductions.R_Erdos687_erdos_687_variants_fgkmt_R1
import Mathlib


-- Reduction Erdos687.erdos_687.variants.fgkmt.R1.H1.R1 of step Erdos687.erdos_687.variants.fgkmt.R1.H1
-- Credit: @carterleffen

/-!
# Sieving primes in FGKMT via shift compression, pair concentration, and sparse rounding

Reduces Theorem 2 of Ford, Green, Konyagin, Maynard and Tao, *Long gaps between primes*,
J. Amer. Math. Soc. 31 (2018), to three decoupled hypotheses:

* `H1`: Preliminary-sieve first moment and elementary range bounds on the prime band
  `(log^20 x, z]` and target primes `(x, y]`.
* `H2`: Existence of conditional integer-shift laws with controlled hit marginals and small
  exceptional set on at least half of all small-prime residue assignments.
* `H3`: Sparse, nearly regular finite hypergraph rounding (Corollary 4 of [FGKMT18]) with
  strict lower cardinality `U^3 < |V|` and polynomial upper bound `|V| <= x^100`.

Adapts the shift-compression, pair-concentration, edge-pushforward, growth, and codegree
machinery from the merged `Green46.green_46.variants.lower` reductions and proofs.
-/

namespace OMA.R_Erdos687_erdos_687_variants_fgkmt_R1_H1_R1
open Finset
namespace ShiftCompression

lemma compress {α : Type*} (Q : Finset α) (hits : α → Finset ℤ) (law : PMF ℤ) :
    ∃ (T : Finset ℤ) (w : ℤ → ℝ), (∑ t ∈ T, w t)=1 ∧ (∀ t ∈ T, 0 ≤ w t) ∧
      ∀ q ∈ Q, ∑ t ∈ T.filter (· ∈ hits q), w t = ∑ t ∈ hits q, (law t).toReal := by
  classical
  let A := Q.biUnion hits
  obtain ⟨d,hd⟩ := Infinite.exists_notMem_finset A
  let v (t : ℤ) := (law t).toReal
  let rem := 1-∑ t ∈ A, v t
  let w (t : ℤ) := if t=d then rem else v t
  have upper : (∑ t ∈ A, v t) ≤ 1 := by
    have bound : (∑ t ∈ A, law t) ≤ ∑' t, law t := ENNReal.sum_le_tsum _
    rw [law.tsum_coe] at bound
    have realBound := ENNReal.toReal_mono (by simp : (1:ENNReal) ≠ ⊤) bound
    simpa [v,ENNReal.toReal_sum (fun t _ => law.apply_ne_top t)] using realBound
  have onA (t) (ht : t ∈ A) : w t = v t := if_neg (by rintro rfl; exact hd ht)
  refine ⟨insert d A,w,?_,?_,?_⟩
  · rw [sum_insert hd,sum_congr rfl onA]
    simp [w,rem]
  · intro t _
    dsimp [w]
    split <;> first | exact sub_nonneg.mpr upper | exact ENNReal.toReal_nonneg
  · intro q hq
    have sub : hits q ⊆ A := fun t ht => mem_biUnion.mpr ⟨q,hq,ht⟩
    have eq : (insert d A).filter (· ∈ hits q) = hits q := by
      ext t; exact ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨mem_insert_of_mem (sub h),h⟩⟩
    rw [eq]
    exact sum_congr rfl fun t ht => onA t (sub ht)

lemma shifts (Q H : Finset ℕ) (p : ℕ) (law : PMF ℤ) :
    ∃ (T : Finset ℤ) (w : ℤ → ℝ), (∑ t ∈ T,w t)=1 ∧ (∀ t ∈ T, 0 ≤ w t) ∧
      ∀ q ∈ Q, (∑ t ∈ T.filter (fun t => ∃ h ∈ H, (q:ℤ)=t+(h:ℤ)*p), w t) =
        ∑ t ∈ H.image (fun h : ℕ => (q:ℤ)-(h:ℤ)*p), (law t).toReal := by
  classical
  let hits (q : ℕ) := H.image (fun h : ℕ => (q:ℤ)-(h:ℤ)*p)
  obtain ⟨T,w,tot,pos,agree⟩ := compress Q hits law
  refine ⟨T,w,tot,pos,?_⟩
  intro q hq
  convert agree q hq using 2
  ext t
  simp only [mem_filter,hits,mem_image]
  constructor
  · rintro ⟨hT,k,hk,eq⟩
    exact ⟨hT,k,hk,by omega⟩
  · rintro ⟨hT,k,hk,eq⟩
    exact ⟨hT,k,hk,by omega⟩

end ShiftCompression


open Finset Real
open scoped Classical
namespace SievePairs

lemma residue_count {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℕ) (u v : ∀ i, Fin (p i)) :
    (univ.filter (fun a : ∀ i, Fin (p i) => (∀ i, a i ≠ u i) ∧ ∀ i, a i ≠ v i)).card =
      ∏ i, (if u i=v i then p i-1 else p i-2) := by
  classical
  let C (i : ι) := ((univ : Finset (Fin (p i))).erase (u i)).erase (v i)
  have eq : univ.filter (fun a : ∀ i, Fin (p i) => (∀ i, a i ≠ u i) ∧ ∀ i, a i ≠ v i) =
      Fintype.piFinset C := by
    ext a
    simp [C,forall_and, and_comm]
  rw [eq,Fintype.card_piFinset]
  apply prod_congr rfl
  intro i _
  by_cases h : u i=v i
  · simp [C,h]
  · have hv : v i ∈ (univ : Finset (Fin (p i))).erase (u i) := by simp [Ne.symm h]
    simp [C,h,card_erase_of_mem hv]; omega

lemma factors {d : ℕ} (hd : 0 < d) : (d.primeFactors.card:ℝ) ≤ log d / log 2 := by
  have prod : 2^d.primeFactors.card ≤ ∏ p ∈ d.primeFactors, p := by
    simpa using (prod_le_prod' (s := d.primeFactors) (f := fun _ => (2:ℕ)) (g := id)
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le))
  have h := prod.trans (Nat.le_of_dvd hd d.prod_primeFactors_dvd)
  apply (le_div_iff₀ (log_pos (by norm_num : (1:ℝ)<2))).mpr
  have hr : (2:ℝ)^d.primeFactors.card ≤ d := by exact_mod_cast h
  simpa [Real.log_pow] using Real.log_le_log (by positivity) hr

lemma survival {d : ℕ} (hd : 0 < d) (S : Finset ℕ) (sieve : ∀ p ∈ S, p.Prime)
    (L : ℝ) (hL : 1 < L) (cut : ∀ p ∈ S, L ≤ p) :
    (∏ p ∈ S, (1 - (if p ∣ d then 1 else 2)/(p:ℝ))) ≤
      (∏ p ∈ S, (1-1/(p:ℝ)))^2 * exp ((log d / log 2)/(L-1)) := by
  let extra (p : ℕ) : ℝ := if p ∣ d then 1/(L-1) else 0
  have unit (p : ℕ) (hp : p∈S) : (2:ℝ) ≤ p := by exact_mod_cast (sieve p hp).two_le
  have loc (p : ℕ) (hp : p∈S) :
      (1 - (if p ∣ d then 1 else 2)/(p:ℝ)) ≤ (1-1/(p:ℝ))^2 * exp (extra p) := by
    have two := unit p hp
    have pp : 0 < (p:ℝ) := by linarith
    by_cases dv : p ∣ d
    · simp only [extra,dv,if_true]
      have inv : 1/((p:ℝ)-1) ≤ 1/(L-1) := by gcongr; exact cut p hp
      have expB : 1/((p:ℝ)-1) + 1 ≤ exp (1/(L-1)) := (by linarith : 1/((p:ℝ)-1)+1 ≤ 1/(L-1)+1).trans (add_one_le_exp _)
      calc
        1-1/(p:ℝ) = (1-1/(p:ℝ))^2 * (1/((p:ℝ)-1)+1) := by
          field_simp [ne_of_gt pp, ne_of_gt (show 0 < (p:ℝ)-1 by linarith)]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left expB (sq_nonneg _)
    · simp only [extra,dv,if_false,exp_zero,mul_one]
      nlinarith [sq_nonneg (1/(p:ℝ)), show 2/(p:ℝ)=2*(1/(p:ℝ)) by ring]
  have pos (p : ℕ) (hp : p∈S) : 0 ≤ 1-(if p ∣ d then 1 else 2)/(p:ℝ) := by
    have two := unit p hp
    apply sub_nonneg.mpr
    apply (div_le_one (by linarith)).mpr
    split <;> linarith
  have card : (S.filter (· ∣ d)).card ≤ d.primeFactors.card :=
    card_le_card (fun p hp => Nat.mem_primeFactors.mpr
      ⟨sieve p (mem_filter.mp hp).1,(mem_filter.mp hp).2,hd.ne'⟩)
  have total : ∑ p ∈ S, extra p ≤ (log d/log 2)/(L-1) := by
    simp only [extra,← sum_filter,sum_const,nsmul_eq_mul]
    have c : ((S.filter (· ∣ d)).card:ℝ) ≤ log d/log 2 :=
      (by exact_mod_cast card : ((S.filter (· ∣ d)).card:ℝ) ≤ d.primeFactors.card).trans (factors hd)
    rw [← div_eq_mul_one_div]
    exact div_le_div_of_nonneg_right c (by linarith)
  calc
    _ ≤ _ := prod_le_prod pos loc
    _ = (∏ p ∈ S, (1-1/(p:ℝ)))^2 * exp (∑ p ∈ S,extra p) := by
      simp only [sq,prod_mul_distrib,Real.exp_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr total) (sq_nonneg _)

end SievePairs

namespace SievePairs
open scoped Classical

lemma probability (S : Finset ℕ) (primes : ∀ p ∈ S,p.Prime) (u v : ℕ) (ord : u ≤ v) :
    let res (n : ℕ) (p : S) : Fin (p:ℕ) := ⟨n%p.val,Nat.mod_lt _ (primes p p.property).pos⟩
    let both := (univ : Finset (∀ p : S, Fin (p:ℕ))).filter (fun a => (∀ p,a p ≠ res u p) ∧ ∀ p,a p ≠ res v p)
    (both.card:ℝ) / Fintype.card (∀ p : S, Fin (p:ℕ)) =
      ∏ p ∈ S,(1-(if p ∣ v-u then 1 else 2)/(p:ℝ)) := by
  intro res both
  have count := residue_count (fun p : S => p.val) (res u) (res v)
  dsimp only [both]
  have eq (p : S) : res u p=res v p ↔ p.val ∣ v-u := by
    exact Fin.ext_iff.trans (Nat.modEq_iff_dvd' ord)
  have totals : Fintype.card (∀ p : S, Fin (p:ℕ)) = ∏ p : S,p.val := by simp [Fintype.card_pi]
  erw [count]
  rw [totals,Nat.cast_prod,Nat.cast_prod,← prod_div_distrib,← prod_attach (f := fun p : ℕ =>
    1-(if p ∣ v-u then 1 else 2)/(p:ℝ))]
  apply prod_congr rfl
  intro p _
  have two := (primes p p.property).two_le
  have pos : (p.val:ℝ) ≠ 0 := by positivity
  simp only [eq]
  by_cases h : p.val ∣ v-u
  · simp [h,Nat.cast_sub (by omega : 1 ≤ p.val)]
    field_simp
  · simp [h,Nat.cast_sub two]
    field_simp

lemma secondMoment {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) (D σ e : ℝ) (hD : 0 < D) (_hσ : 0 ≤ σ) (he : 0 ≤ e)
    (size : (Fintype.card α : ℝ) = D)
    (binary : ∀ a i, f a i * f a i = f a i)
    (single : ∀ i, ∑ a,f a i = D*σ)
    (pair : ∀ i j, i≠j → ∑ a,f a i*f a j ≤ D*(1+e)*σ^2) :
    let M := (Fintype.card β:ℝ)*σ
    (∑ a,((∑ i,f a i) - M)^2)/D ≤ M + e*M^2 := by
  classical
  intro M
  let T (a : α) := ∑ i,f a i
  have first : ∑ a,T a = D*M := by
    dsimp [T,M]; rw [sum_comm]; simp [single]; ring
  have fact (a : α) : T a^2 = ∑ i,∑ j,f a i*f a j := by simp [T,sq,sum_mul,mul_sum]; exact sum_comm
  have upper (i j : β) : ∑ a,f a i*f a j ≤ (if i=j then D*σ else 0) + D*(1+e)*σ^2 := by
    by_cases eq : i=j
    · subst j; simp [binary,single]; positivity
    · simpa [eq] using pair i j eq
  have second : ∑ a,T a^2 ≤ D*M+D*(1+e)*M^2 := by
    simp only [fact]; rw [sum_comm]
    calc
      _ = ∑ i,∑ j,∑ a,f a i*f a j := sum_congr rfl (fun _ _ => sum_comm)
      _ ≤ _ := sum_le_sum (fun i _ => sum_le_sum (fun j _ => upper i j))
      _ = _ := by simp [sum_add_distrib,M]; ring
  have dev : (∑ a,(T a-M)^2) = (∑ a,T a^2)-2*M*(∑ a,T a)+(Fintype.card α)*M^2 := by
    simp only [sub_sq,sum_add_distrib,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,← sum_mul]
    rw [← Finset.mul_sum]
    ring
  change (∑ a,(T a-M)^2)/D ≤ _
  rw [dev,first,size]
  apply (div_le_iff₀ hD).mpr
  nlinarith [second]

end SievePairs

namespace SievePairs
open scoped Classical

lemma concentration {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) (D σ e : ℝ) (hD : 0 < D) (hσ : 0 ≤ σ) (he : 0 ≤ e)
    (size : (Fintype.card α : ℝ) = D)
    (binary : ∀ a i, f a i * f a i = f a i)
    (single : ∀ i, ∑ a,f a i = D*σ)
    (pair : ∀ i j, i≠j → ∑ a,f a i*f a j ≤ D*(1+e)*σ^2)
    (small : e ≤ 1/128) (large : 128 ≤ (Fintype.card β:ℝ)*σ) :
    let M := (Fintype.card β:ℝ)*σ
    ((univ.filter (fun a : α => M/3 ≤ |(∑ i,f a i)-M|)).card:ℝ) ≤ D/4 := by
  classical
  intro M
  let T (a : α) := ∑ i,f a i
  let B := univ.filter (fun a : α => M/3 ≤ |T a-M|)
  have positive : 0 < M := by dsimp [M]; linarith
  have low (a : α) (ha : a∈B) : (M/3)^2 ≤ (T a-M)^2 := by
    have z := (mem_filter.mp ha).2
    calc
      _ ≤ |T a-M|^2 := pow_le_pow_left₀ (by positivity) z 2
      _ = _ := sq_abs _
  have hsum := sum_le_sum low
  have total := sum_le_sum_of_subset_of_nonneg (s := B) (t := univ)
    (subset_univ _) (fun a _ _ => sq_nonneg (T a-M))
  have high := (div_le_iff₀ hD).mp (secondMoment f D σ e hD hσ he size binary single pair)
  change (∑ a,(T a-M)^2) ≤ (M+e*M^2)*D at high
  have maxvar : M+e*M^2 ≤ M^2/64 := by
    change 128 ≤ M at large
    nlinarith [mul_nonneg (sub_nonneg.mpr large) positive.le,
      mul_nonneg (sub_nonneg.mpr small) (sq_nonneg M)]
  have h := (hsum.trans total).trans (high.trans (mul_le_mul_of_nonneg_right maxvar hD.le))
  simp only [sum_const,nsmul_eq_mul] at h
  change (B.card:ℝ) ≤ D/4
  apply le_of_mul_le_mul_right (a := M^2) _ (sq_pos_of_pos positive)
  nlinarith

end SievePairs

namespace SievePairs
open scoped Classical

lemma sieve_concentration (V S : Finset ℕ) (pr : ∀ p ∈ S,p.Prime) {Y : ℕ}
    (maxV : ∀ q ∈ V, q ≤ Y) {L : ℝ} (hL : 1 < L) (minS : ∀ p ∈ S,L ≤ p)
    (eps : exp ((log Y / log 2)/(L-1)) ≤ 1+1/128) (ypos : 0 < Y)
    (large : 128 ≤ (V.card : ℝ)*(∏ p ∈ S,(1-1/(p:ℝ)))) :
    let σ := ∏ p ∈ S,(1-1/(p:ℝ))
    let M := (V.card:ℝ)*σ
    let res (q : ℕ) (p : S) : Fin p.val := ⟨q%p.val,Nat.mod_lt _ (pr p p.property).pos⟩
    let count (a : ∀ p : S, Fin p.val) := (V.filter fun q => ∀ p, a p≠res q p).card
    ((univ.filter (fun a => M/3 ≤ |(count a:ℝ)-M|)).card:ℝ) ≤
      (Fintype.card (∀ p : S, Fin p.val):ℝ)/4 := by
  classical
  intro σ M res count
  let Ω := ∀ p : S, Fin p.val
  let D := (Fintype.card Ω:ℝ)
  let f (a : Ω) (q : V) : ℝ := if ∀ p,a p≠res q.val p then 1 else 0
  have nonempty : Nonempty Ω := ⟨res 0⟩
  have hD : 0 < D := by dsimp [D]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Ω)
  have hσ : 0 ≤ σ := prod_nonneg (fun p hp => by
    have pos : (0:ℝ)<p := by exact_mod_cast (pr p hp).pos
    have two : (2:ℝ) ≤ p := by exact_mod_cast (pr p hp).two_le
    apply sub_nonneg.mpr; apply (div_le_one pos).mpr; linarith)
  have bin (a : Ω) (q : V) : f a q*f a q=f a q := by dsimp [f]; split <;> norm_num
  have ratio (i j : V) (le : i.val ≤ j.val) :
      (∑ a, f a i*f a j)/D = ∏ p ∈ S,(1-(if p ∣ j.val-i.val then 1 else 2)/(p:ℝ)) := by
    have count' := probability S pr i.val j.val le
    change ((univ.filter (fun a : Ω => (∀ p,a p≠res i.val p) ∧ ∀ p,a p≠res j.val p)).card:ℝ)/D = _ at count'
    rw [←count']
    congr 1
    rw [← sum_boole]
    apply sum_congr rfl
    intro a _
    dsimp [f]
    split_ifs <;> simp_all
  have single (i : V) : ∑ a, f a i = D*σ := by
    have h := ratio i i le_rfl
    simp only [Nat.sub_self,dvd_zero,if_true,bin] at h
    exact (div_eq_iff hD.ne').mp h |>.trans (mul_comm ..)
  let e := exp ((log Y/log 2)/(L-1))-1
  have he : 0 ≤ e := by
    apply sub_nonneg.mpr
    apply Real.one_le_exp
    exact div_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast ypos)) (by positivity)) (by linarith)
  have ordered (i j : V) (lt : i.val < j.val) : ∑ a,f a i*f a j ≤ D*(1+e)*σ^2 := by
    have diff : 0 < j.val-i.val := by omega
    have dh : j.val-i.val ≤ Y := (Nat.sub_le ..).trans (maxV j j.property)
    have prob := ratio i j lt.le
    have up := survival diff S pr L hL minS
    have expB : exp ((log (j.val-i.val : ℕ)/log 2)/(L-1)) ≤ 1+e := by
      have eq : 1+e=exp ((log Y/log 2)/(L-1)) := by dsimp [e]; ring
      rw [eq]
      gcongr
    have z := (div_le_iff₀ hD).mp (prob.le.trans (up.trans (mul_le_mul_of_nonneg_left expB (sq_nonneg _))))
    dsimp only [σ] at *
    linarith only [z]
  have pair (i j : V) (ne : i≠j) : ∑ a,f a i*f a j ≤ D*(1+e)*σ^2 := by
    have diff : i.val≠j.val := fun h => ne (Subtype.ext h)
    rcases lt_or_gt_of_ne diff with h|h
    · exact ordered i j h
    · simpa [mul_comm] using ordered j i h
  have bound := concentration f D σ e hD hσ he rfl bin single pair (by dsimp [e]; linarith) (by simpa [σ] using large)
  have point (a : Ω) : (∑ i, f a i) = count a := by
    dsimp only [f,count]
    rw [sum_coe_sort V (fun q : ℕ => if ∀ p,a p ≠ res q p then (1:ℝ) else 0), sum_boole]
  simpa only [point,Fintype.card_coe,M] using bound

end SievePairs

open Filter Finset Real
open scoped Classical
lemma ev_log (B : ℝ) : ∀ᶠ x : ℕ in atTop, B ≤ log (x : ℝ) :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop B

lemma ev_log2 (B : ℝ) : ∀ᶠ x : ℕ in atTop, B ≤ log (log (x : ℝ)) :=
  (Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop B

private lemma one_large_prime {x q r p s : ℕ} (qr : q < r) (short : 4*r < x*x)
    (pp : p.Prime) (sp : s.Prime) (lp : x < 2*p) (ls : x < 2*s)
    (dp : q ≡ r [MOD p]) (ds : q ≡ r [MOD s]) : p = s := by
  by_contra different
  have cp := (Nat.coprime_primes pp sp).mpr different
  have prod := cp.mul_dvd_of_dvd_of_dvd ((Nat.modEq_iff_dvd' qr.le).mp dp)
    ((Nat.modEq_iff_dvd' qr.le).mp ds)
  have bound := (Nat.le_of_dvd (Nat.sub_pos_of_lt qr) prod).trans (Nat.sub_le r q)
  have hx : x*x < (2*p)*(2*s) := lt_of_le_of_lt
    (Nat.mul_le_mul_right x lp.le) (Nat.mul_lt_mul_of_pos_left ls (by omega))
  nlinarith

private lemma pair_weight (P : Finset ℕ) (E : ℕ → Finset (Finset ℕ))
    (w : ℕ → Finset ℕ → ℝ) {x q r : ℕ} (qr : q < r) (short : 4*r < x*x)
    (large : ∀ p ∈ P, p.Prime ∧ x < 2*p)
    (labels : ∀ p ∈ P, ∀ e ∈ E p, ∃ a : ℕ, ∀ v ∈ e, v ≡ a [MOD p])
    (pos : ∀ p ∈ P, ∀ e ∈ E p, 0 ≤ w p e)
    {ε : ℝ} (hε : 0 ≤ ε)
    (sparse : ∀ p ∈ P, (∑ e ∈ (E p).filter (q ∈ ·), w p e) ≤ ε) :
    (∑ p ∈ P, ∑ e ∈ (E p).filter (fun e => q ∈ e ∧ r ∈ e), w p e) ≤ ε := by
  classical
  let J (p : ℕ) := (E p).filter (fun e => q ∈ e ∧ r ∈ e)
  change (∑ p ∈ P, ∑ e ∈ J p, w p e) ≤ ε
  have empty (p : ℕ) (hp : p ∈ P) (incompatible : ¬ q ≡ r [MOD p]) : J p = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro e he both
    obtain ⟨a, ha⟩ := labels p hp e he
    exact incompatible ((ha q both.1).trans (ha r both.2).symm)
  by_cases ex : ∃ p ∈ P, q ≡ r [MOD p]
  · obtain ⟨p, hp, hmod⟩ := ex
    have only : (∑ s ∈ P, ∑ e ∈ J s, w s e) = ∑ e ∈ J p, w p e := by
      apply Finset.sum_eq_single p
      · intro s hs hne
        have no : ¬ q ≡ r [MOD s] := fun h =>
          hne (one_large_prime qr short (large s hs).1 (large p hp).1
            (large s hs).2 (large p hp).2 h hmod)
        simp [empty s hs no]
      · intro h
        exact (h hp).elim
    rw [only]
    apply le_trans _ (sparse p hp)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      obtain ⟨he', hq, _⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨he', hq⟩
    · intro e he _
      exact pos p hp e (Finset.mem_filter.mp he).1
  · have zero : (∑ p ∈ P, ∑ e ∈ J p, w p e) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      have no : ¬ q ≡ r [MOD p] := fun h => ex ⟨p, hp, h⟩
      simp [empty p hp no]
    simpa only [zero] using hε


def H1 : Prop := ∀ c : ℝ, 0<c → ∀ᶠ x : ℕ in atTop,
  let X : ℝ := x
  let U := log (log X)
  let y := c*X*log X*log U/U
  let z := X^(log U/(4*U))
  let P := (Ioc (x/2) x).filter Nat.Prime
  let S := (range (⌊z⌋₊+1)).filter (fun p : ℕ => p.Prime ∧ p ∉ P ∧ log X^20 < p)
  let V := (Ioc x ⌊y⌋₊).filter Nat.Prime
  let M := (V.card:ℝ)*(∏ p ∈ S,(1-1/(p:ℝ)))
  0 < ⌊y⌋₊ ∧ 1 < log X^20 ∧ exp ((log ⌊y⌋₊ / log 2)/(log X^20-1)) ≤ 1+1/128 ∧
  128 ≤ M ∧ 60*c*(X*U/log X) ≤ M ∧ M ≤ 100*c*(X*U/log X)

def H2 : Prop := ∃ c K : ℝ, 0<c ∧ 3 ≤ K ∧ ∀ᶠ x : ℕ in atTop,
  let X : ℝ := x
  let U := log (log X)
  let y := c*X*log X*log U/U
  let z := X^(log U/(4*U))
  let P := (Ioc (x/2) x).filter Nat.Prime
  let S := (range (⌊z⌋₊+1)).filter (fun p : ℕ => p.Prime ∧ p ∉ P ∧ log X^20 < p)
  let V := (Ioc x ⌊y⌋₊).filter Nat.Prime
  let Ω := ∀ p : S, Fin p.val
  ∃ G : Finset Ω, (Fintype.card Ω:ℝ)/2 ≤ G.card ∧
  ∀ a ∈ G, let Q := V.filter (fun q => ∀ p : S, (a p).val ≠ q%p.val)
    ∃ (H : Finset ℕ) (law : ℕ → PMF ℤ) (C : ℝ),
    let mass (p q : ℕ) := ∑ t ∈ H.image (fun h : ℕ => (q:ℤ)-(h:ℤ)*p), (law p t).toReal
    (H.card:ℝ) ≤ √(log X) ∧ 3 ≤ C ∧ C ≤ K ∧
    (∀ p ∈ P, ∀ q ∈ Q, mass p q ≤ X^(-3/5:ℝ)) ∧
    (((Q.filter (fun q => 1/U^2 < |(∑ p ∈ P,mass p q)-C|)).card:ℝ) ≤ X/log X)

def H3 : Prop := ∀ K : ℝ, 3≤K → ∃ D : ℝ, 0<D ∧ ∀ᶠ x : ℕ in atTop,
    let X : ℝ := x
    let U := log (log X)
    ∀ (P V : Finset ℕ) (E : ℕ → Finset (Finset ℕ)) (w : ℕ → Finset ℕ → ℝ) (C : ℝ),
      P.card ≤ x → U^3 < V.card → V.card ≤ x^100 → 3≤C → C≤K →
      (∀ p ∈ P, ∀ e ∈ E p, e ⊆ V ∧ (e.card:ℝ) ≤ √(log X)) →
      (∀ p ∈ P, (∑ e ∈ E p, w p e)=1 ∧ ∀ e ∈ E p, 0≤w p e) →
      (∀ p ∈ P, ∀ q ∈ V, (∑ e ∈ (E p).filter (q ∈ ·), w p e) ≤ X^(-3/5:ℝ)) →
      (∀ q ∈ V, |(∑ p ∈ P, ∑ e ∈ (E p).filter (q ∈ ·), w p e)-C| ≤ 1/U^2) →
      (∀ q ∈ V, ∀ r ∈ V, q<r →
        (∑ p ∈ P, ∑ e ∈ (E p).filter (fun e => q ∈ e ∧ r ∈ e), w p e) ≤ X^(-3/5:ℝ)) →
      ∃ f : ℕ → Finset ℕ, (∀ p ∈ P, f p = ∅ ∨ f p ∈ E p) ∧
        ((V\P.biUnion f).card:ℝ) ≤ D*V.card/U

lemma stage1 : H1 → H2 → (∃ c K : ℝ, 0<c ∧ 3≤K ∧ ∀ᶠ x : ℕ in atTop,
    let X : ℝ := x
    let U := log (log X)
    let y := c*X*log X*log U/U
    let z := X^(log U/(4*U))
    let P := (Ioc (x/2) x).filter Nat.Prime
    ∃ a : ℕ → ℕ,
    let Q := (Ioc x ⌊y⌋₊).filter (fun q => q.Prime ∧
      ∀ p : ℕ, p.Prime → p ∉ P → log X^20 < p → (p:ℝ) ≤ z → ¬q ≡ a p [MOD p])
    ∃ (H : Finset ℕ) (T : ℕ → Finset ℤ) (μ : ℕ → ℤ → ℝ) (C : ℝ),
      let hit (p q : ℕ) (t : ℤ) := ∃ h ∈ H, (q : ℤ) = t + (h : ℤ)*p
      let mass (p q : ℕ) := ∑ t ∈ (T p).filter (hit p q), μ p t
      40*c*X*U/log X ≤ Q.card ∧ (Q.card:ℝ) ≤ K*X*U/log X ∧
      (H.card:ℝ) ≤ √(log X) ∧ 3 ≤ C ∧ C ≤ K ∧
      (∀ p ∈ P, (∑ t ∈ T p, μ p t) = 1 ∧ ∀ t ∈ T p, 0 ≤ μ p t) ∧
      (∀ p ∈ P, ∀ q ∈ Q, mass p q ≤ X^(-3/5:ℝ)) ∧
      (((Q.filter (fun q => 1/U^2 < |(∑ p ∈ P, mass p q)-C|)).card:ℝ) ≤ X/log X)) := by
  classical
  intro mean cover
  obtain ⟨c,K,hc,hK,typical⟩ := cover
  refine ⟨c,max K (200*c),hc,hK.trans (le_max_left ..),?_⟩
  filter_upwards [mean c hc,typical] with x hm hg
  let X : ℝ := x
  let U := log (log X)
  let y := c*X*log X*log U/U
  let z := X^(log U/(4*U))
  let P := (Ioc (x/2) x).filter Nat.Prime
  let S := (range (⌊z⌋₊+1)).filter (fun p : ℕ => p.Prime ∧ p ∉ P ∧ log X^20 < p)
  let V := (Ioc x ⌊y⌋₊).filter Nat.Prime
  let Ω := ∀ p : S, Fin p.val
  let σ := ∏ p ∈ S,(1-1/(p:ℝ))
  let M := (V.card:ℝ)*σ
  let Q (a : Ω) := V.filter fun q => ∀ p : S,(a p).val ≠ q%p.val
  have spec (p : ℕ) : p∈S ↔ p.Prime ∧ p ∉ P ∧ log X^20<p ∧ (p:ℝ)≤z := by
    have hz : 0 ≤ z := Real.rpow_nonneg (by positivity : 0 ≤ (x:ℝ)) _
    simp only [S,mem_filter,mem_range,Nat.lt_succ_iff,Nat.le_floor_iff hz]
    tauto
  have pr (p : ℕ) (hp : p∈S) := (spec p).mp hp |>.1
  have minS (p : ℕ) (hp : p∈S) := ((spec p).mp hp).2.2.1.le
  obtain ⟨ypos,lowerL,eps,large,low,high⟩ := hm
  change 128 ≤ M at large
  change 60*c*(X*U/log X) ≤ M at low
  change M ≤ 100*c*(X*U/log X) at high
  have con := SievePairs.sieve_concentration V S pr
    (fun q hq => (mem_Ioc.mp (mem_filter.mp hq).1).2) lowerL minS eps ypos large
  let B := univ.filter (fun a : Ω => M/3 ≤ |((Q a).card:ℝ)-M|)
  have bound : (B.card:ℝ) ≤ (Fintype.card Ω:ℝ)/4 := by
    simpa only [B,Q,M,σ,Fin.ne_iff_vne] using con
  obtain ⟨G,count,good⟩ := hg
  have has : Nonempty Ω := ⟨fun p => ⟨0,(pr p p.property).pos⟩⟩
  have posD : (0:ℝ) < Fintype.card Ω := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Ω)
  have lt : B.card < G.card := by
    have : (Fintype.card Ω:ℝ)/2 ≤ G.card := count
    exact_mod_cast (by linarith : (B.card:ℝ) < G.card)
  obtain ⟨a,ag,ab⟩ := exists_mem_notMem_of_card_lt_card lt
  have err : |((Q a).card:ℝ)-M| < M/3 := by simpa [B] using ab
  let lift (p : ℕ) : ℕ := if h : p∈S then (a ⟨p,h⟩).val else 0
  have equiv (q : ℕ) : (∀ p : S,(a p).val ≠ q%p.val) ↔
      (∀ p : ℕ, p.Prime → p ∉ P → log X^20 < p → (p:ℝ)≤z → ¬q ≡ lift p [MOD p]) := by
    constructor
    · intro avoiding p hp hP hL hz eq
      have h := (spec p).mpr ⟨hp,hP,hL,hz⟩
      apply avoiding ⟨p,h⟩
      exact (by simpa [Nat.ModEq,lift,h,Nat.mod_eq_of_lt (a ⟨p,h⟩).isLt] using eq.symm)
    · intro avoiding p eq
      obtain ⟨prime,hP,hL,hz⟩ := (spec p).mp p.property
      apply avoiding _ prime hP hL hz
      simpa [Nat.ModEq,lift,p.property,Nat.mod_eq_of_lt (a p).isLt] using eq.symm
  have same : (Ioc x ⌊y⌋₊).filter (fun q => q.Prime ∧
      ∀ p : ℕ,p.Prime → p ∉ P → log X^20 < p → (p:ℝ) ≤ z → ¬q ≡ lift p [MOD p]) = Q a := by
    ext q
    simp only [Q,V,mem_filter,equiv]
    tauto
  obtain ⟨H,law,C,sz,lc,uc,hit,exceptions⟩ := good a ag
  choose T w total nn agree using (fun p : ℕ => ShiftCompression.shifts (Q a) H p (law p))
  refine ⟨lift,?_⟩
  change ∃ (H : Finset ℕ) (T : ℕ → Finset ℤ) (μ : ℕ → ℤ → ℝ) (C : ℝ), _
  refine ⟨H,T,w,C,?_⟩
  dsimp only
  change 40*c*X*U/log X ≤ _ ∧ _ ≤ max K (200*c)*X*U/log X ∧ _
  rw [same]
  have scale : 0 ≤ X*U/log X := by
    by_contra! neg
    have := mul_neg_of_pos_of_neg (show 0 < 100*c by positivity) neg
    linarith
  have frac := abs_lt.mp err
  refine ⟨?_,?_,sz,lc,uc.trans (le_max_left ..),fun p _ => ⟨total p,nn p⟩,?_,?_⟩
  · rw [show 40*c*X*U/log X = 40*c*(X*U/log X) by ring]
    linarith
  · rw [show max K (200*c)*X*U/log X = max K (200*c)*(X*U/log X) by ring]
    have upper := mul_le_mul_of_nonneg_right (le_max_right K (200*c)) scale
    nlinarith only [high,low,frac.2,upper,mul_nonneg hc.le scale]
  · intro p hp q hq
    rw [agree p q hq]
    exact hit p hp q hq
  · have sameBad : (Q a).filter (fun q : ℕ => 1/U^2 <
        |(∑ p ∈ P, ∑ t ∈ (T p).filter (fun t => ∃ h ∈ H, (q:ℤ)=t+(h:ℤ)*p), w p t)-C|) =
        (Q a).filter (fun q : ℕ => 1/U^2 <
        |(∑ p ∈ P, ∑ t ∈ H.image (fun h : ℕ => (q:ℤ)-(h:ℤ)*p), (law p t).toReal)-C|) := by
      apply filter_congr
      intro q hq
      simp only [agree _ q hq]
    change (((Q a).filter _).card:ℝ) ≤ X/log X
    rw [sameBad]
    exact exceptions


lemma pushEdge : (∀ (P V H : Finset ℕ) (T : ℕ → Finset ℤ) (μ : ℕ → ℤ → ℝ),
    (∀ p ∈ P, 0 < p) →
    (∀ p ∈ P, (∑ t ∈ T p, μ p t) = 1 ∧ ∀ t ∈ T p, 0 ≤ μ p t) →
    ∃ (E : ℕ → Finset (Finset ℕ)) (w : ℕ → Finset ℕ → ℝ),
      (∀ p ∈ P, ∀ e ∈ E p, e ⊆ V ∧ e.card ≤ H.card ∧
        ∃ b : ℕ, ∀ q ∈ e, q ≡ b [MOD p]) ∧
      (∀ p ∈ P, (∑ e ∈ E p, w p e)=1 ∧ ∀ e ∈ E p, 0 ≤ w p e) ∧
      (∀ p ∈ P, ∀ q ∈ V, (∑ e ∈ (E p).filter (q ∈ ·), w p e) =
        ∑ t ∈ (T p).filter (fun t => ∃ h ∈ H, (q : ℤ) = t + (h : ℤ)*p), μ p t)) := by
  intro P V H T μ hP hμ
  let edge : ℕ → ℤ → Finset ℕ := fun p t => V.filter (fun q => ∃ h ∈ H, (q : ℤ) = t + (h : ℤ)*p)
  let w : ℕ → Finset ℕ → ℝ := fun p e => ∑ t ∈ (T p).filter (fun t => edge p t = e), μ p t
  have hfib : ∀ p (g : ℤ → ℝ), (∑ e ∈ (T p).image (edge p),
      ∑ t ∈ (T p).filter (fun t => edge p t = e), g t) = ∑ t ∈ T p, g t :=
    fun p g => Finset.sum_fiberwise_of_maps_to (fun t ht => Finset.mem_image_of_mem _ ht) g
  refine ⟨fun p => (T p).image (edge p), w, ?_, ?_, ?_⟩
  · intro p hp e he
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp he
    refine ⟨Finset.filter_subset _ _, ?_, ?_⟩
    · have hsub : edge p t ⊆ H.image (fun h : ℕ => (t + (h:ℤ)*p).toNat) := by
        intro q hq
        obtain ⟨-, h, hh, hq⟩ := Finset.mem_filter.mp hq
        exact Finset.mem_image.mpr ⟨h, hh, by rw [← hq]; simp⟩
      exact (Finset.card_le_card hsub).trans Finset.card_image_le
    · refine ⟨(t % (p:ℤ)).toNat, fun q hq => ?_⟩
      obtain ⟨-, h, hh, hq⟩ := Finset.mem_filter.mp hq
      have hp0 : (0:ℤ) < p := by exact_mod_cast hP p hp
      rw [← Int.natCast_modEq_iff]
      have e1 : (((t % (p:ℤ)).toNat : ℕ) : ℤ) = t % p := Int.toNat_of_nonneg (Int.emod_nonneg _ hp0.ne')
      rw [e1, hq]
      unfold Int.ModEq
      rw [Int.add_mul_emod_self_right, Int.emod_emod]
  · intro p hp
    refine ⟨?_, ?_⟩
    · simp only [w]
      rw [hfib p (μ p)]
      exact (hμ p hp).1
    · intro e he
      exact Finset.sum_nonneg fun t ht => (hμ p hp).2 t (Finset.mem_filter.mp ht).1
  · intro p hp q hq
    calc ∑ e ∈ ((T p).image (edge p)).filter (q ∈ ·), w p e
        = ∑ e ∈ (T p).image (edge p), ∑ t ∈ (T p).filter (fun t => edge p t = e),
            (if q ∈ edge p t then μ p t else 0) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro e he
          split_ifs with hqe
          · apply Finset.sum_congr rfl
            intro t ht
            rw [(Finset.mem_filter.mp ht).2, if_pos hqe]
          · symm
            apply Finset.sum_eq_zero
            intro t ht
            rw [(Finset.mem_filter.mp ht).2, if_neg hqe]
      _ = ∑ t ∈ T p, (if q ∈ edge p t then μ p t else 0) := hfib p _
      _ = _ := by
          rw [← Finset.sum_filter]
          apply Finset.sum_congr _ (fun _ _ => rfl)
          apply Finset.filter_congr
          intro t _
          simp [edge, hq]

lemma growth : ∀ c : ℝ, 0 < c → ∀ᶠ x : ℕ in atTop,
    let X : ℝ := x
    let U := log (log X)
    4*(c*X*log X*log U/U) < X*X ∧
      U^3 + X/log X < 40*c*X*U/log X := by
  intro c hc
  have hR : ∀ᶠ X : ℝ in atTop, 4*(c*X*log X*log (log (log X))/log (log X)) < X*X ∧
      (log (log X))^3 + X/log X < 40*c*X*log (log X)/log X := by
    have h1 : ∀ᶠ X : ℝ in atTop, log X ^ 4 ≤ X := by
      filter_upwards [(isLittleO_pow_log_id_atTop (n := 4)).bound one_pos, eventually_ge_atTop (1:ℝ)]
        with X hX hX1
      have h0 : 0 ≤ log X := log_nonneg hX1
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 4), id,
        abs_of_nonneg (by linarith), one_mul] at hX
      exact hX
    have h2 : ∀ᶠ X : ℝ in atTop, log X ≤ 1/(8*c) * X := by
      filter_upwards [isLittleO_log_id_atTop.bound (show (0:ℝ) < 1/(8*c) by positivity),
        eventually_ge_atTop (1:ℝ)] with X hX hX1
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (log_nonneg hX1), id,
        abs_of_nonneg (by linarith)] at hX
      exact hX
    have hll : Tendsto (fun X : ℝ => log (log X)) atTop atTop :=
      tendsto_log_atTop.comp tendsto_log_atTop
    filter_upwards [h1, h2, hll.eventually_gt_atTop (1/(20*c)), hll.eventually_ge_atTop 1,
      eventually_gt_atTop (1:ℝ)] with X h1 h2 h3 h4 hX
    have hL : 0 < log X := log_pos hX
    have hX0 : 0 < X := by linarith
    set L := log X with hLdef
    set U := log L with hUdef
    have hU0 : 0 < U := by linarith
    have hUL : U ≤ L := by
      have := Real.log_le_sub_one_of_pos hL
      linarith
    constructor
    · have hlogU : log U / U < 1 := by
        rw [div_lt_one hU0]
        have := Real.log_le_sub_one_of_pos hU0
        linarith
      have hpos : 0 < c*X*L := by positivity
      calc 4*(c*X*L*log U/U) = 4*(c*X*L)*(log U/U) := by ring
        _ ≤ 4*(c*X*L)*1 := by
          apply mul_le_mul_of_nonneg_left hlogU.le (by positivity)
        _ < X*X := by
          have : 8*c*L ≤ X := by
            have := mul_le_mul_of_nonneg_left h2 (show (0:ℝ) ≤ 8*c by positivity)
            rw [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at this
            linarith
          nlinarith
    · have hU3 : U^3 ≤ X/L := by
        rw [le_div_iff₀ hL]
        calc U^3 * L ≤ L^3 * L := by
              apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hU0.le hUL 3) hL.le
          _ = L^4 := by ring
          _ ≤ X := h1
      have h40 : 2 < 40*c*U := by
        have := mul_lt_mul_of_pos_left h3 (show (0:ℝ) < 40*c by positivity)
        rw [show 40*c*(1/(20*c)) = 2 by field_simp; norm_num] at this
        linarith
      have hXL : 0 < X/L := by positivity
      calc U^3 + X/L ≤ 2*(X/L) := by linarith
        _ < (40*c*U)*(X/L) := mul_lt_mul_of_pos_right h40 hXL
        _ = 40*c*X*U/L := by ring
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hR] with x hx
  exact hx

lemma stage2 : (∃ c K : ℝ, 0<c ∧ 3≤K ∧ ∀ᶠ x : ℕ in atTop,
    let X : ℝ := x
    let U := log (log X)
    let y := c*X*log X*log U/U
    let z := X^(log U/(4*U))
    let P := (Ioc (x/2) x).filter Nat.Prime
    ∃ a : ℕ → ℕ,
    let Q := (Ioc x ⌊y⌋₊).filter (fun q => q.Prime ∧
      ∀ p : ℕ, p.Prime → p ∉ P → log X^20 < p → (p:ℝ) ≤ z → ¬q ≡ a p [MOD p])
    ∃ (H : Finset ℕ) (T : ℕ → Finset ℤ) (μ : ℕ → ℤ → ℝ) (C : ℝ),
      let hit (p q : ℕ) (t : ℤ) := ∃ h ∈ H, (q : ℤ) = t + (h : ℤ)*p
      let mass (p q : ℕ) := ∑ t ∈ (T p).filter (hit p q), μ p t
      40*c*X*U/log X ≤ Q.card ∧ (Q.card:ℝ) ≤ K*X*U/log X ∧
      (H.card:ℝ) ≤ √(log X) ∧ 3 ≤ C ∧ C ≤ K ∧
      (∀ p ∈ P, (∑ t ∈ T p, μ p t) = 1 ∧ ∀ t ∈ T p, 0 ≤ μ p t) ∧
      (∀ p ∈ P, ∀ q ∈ Q, mass p q ≤ X^(-3/5:ℝ)) ∧
      (((Q.filter (fun q => 1/U^2 < |(∑ p ∈ P, mass p q)-C|)).card:ℝ) ≤ X/log X)) → (∀ (P V H : Finset ℕ) (T : ℕ → Finset ℤ) (μ : ℕ → ℤ → ℝ),
    (∀ p ∈ P, 0 < p) →
    (∀ p ∈ P, (∑ t ∈ T p, μ p t) = 1 ∧ ∀ t ∈ T p, 0 ≤ μ p t) →
    ∃ (E : ℕ → Finset (Finset ℕ)) (w : ℕ → Finset ℕ → ℝ),
      (∀ p ∈ P, ∀ e ∈ E p, e ⊆ V ∧ e.card ≤ H.card ∧
        ∃ b : ℕ, ∀ q ∈ e, q ≡ b [MOD p]) ∧
      (∀ p ∈ P, (∑ e ∈ E p, w p e)=1 ∧ ∀ e ∈ E p, 0 ≤ w p e) ∧
      (∀ p ∈ P, ∀ q ∈ V, (∑ e ∈ (E p).filter (q ∈ ·), w p e) =
        ∑ t ∈ (T p).filter (fun t => ∃ h ∈ H, (q : ℤ) = t + (h : ℤ)*p), μ p t)) → (∀ c : ℝ, 0 < c → ∀ᶠ x : ℕ in atTop,
    let X : ℝ := x
    let U := log (log X)
    4*(c*X*log X*log U/U) < X*X ∧
      U^3 + X/log X < 40*c*X*U/log X) → (∃ c K : ℝ, 0<c ∧ 3≤K ∧ ∀ᶠ x : ℕ in atTop,
    let X : ℝ := x
    let U := log (log X)
    let y := c*X*log X*log U/U
    let z := X^(log U/(4*U))
    let P := (Ioc (x/2) x).filter Nat.Prime
    ∃ a : ℕ → ℕ,
    let Q := (Ioc x ⌊y⌋₊).filter (fun q => q.Prime ∧
      ∀ p : ℕ, p.Prime → p ∉ P → log X^20 < p → (p:ℝ) ≤ z → ¬q ≡ a p [MOD p])
    ∃ (V : Finset ℕ) (E : ℕ → Finset (Finset ℕ)) (w : ℕ → Finset ℕ → ℝ) (C : ℝ),
      V ⊆ Q ∧ (∀ r ∈ V, 4*r < x*x) ∧ U^3 < V.card ∧ V.card ≤ x^100 ∧ (V.card:ℝ) ≤ K*X*U/log X ∧
      ((Q\V).card:ℝ) ≤ K*X/log X ∧ 3≤C ∧ C≤K ∧
      (∀ p ∈ P, ∀ e ∈ E p, e ⊆ V ∧ (e.card:ℝ) ≤ √(log X) ∧
        ∃ b : ℕ, ∀ q ∈ e, q ≡ b [MOD p]) ∧
      (∀ p ∈ P, (∑ e ∈ E p, w p e)=1 ∧ ∀ e ∈ E p, 0≤w p e) ∧
      (∀ p ∈ P, ∀ q ∈ V, (∑ e ∈ (E p).filter (q ∈ ·), w p e) ≤ X^(-3/5:ℝ)) ∧
      (∀ q ∈ V, |(∑ p ∈ P, ∑ e ∈ (E p).filter (q ∈ ·), w p e)-C| ≤ 1/U^2)) := by
  classical
  intro model push growth
  obtain ⟨c,K,hc,hK,model⟩ := model
  refine ⟨c,K,hc,hK,?_⟩
  filter_upwards [model, growth c hc, ev_log 1, eventually_ge_atTop (1:ℕ)] with x hx hg hlog xpos
  let X : ℝ := x
  let U := log (log X)
  let y := c*X*log X*log U/U
  let z := X^(log U/(4*U))
  let P := (Ioc (x/2) x).filter Nat.Prime
  obtain ⟨a,H,T,μ,C,ql,qu,hs,cmin,cmax,law,sparse,exc⟩ := hx
  refine ⟨a,?_⟩
  let Q := (Ioc x ⌊y⌋₊).filter (fun q => q.Prime ∧
    ∀ p : ℕ, p.Prime → p ∉ P → log X^20 < p → (p:ℝ) ≤ z → ¬q ≡ a p [MOD p])
  let mass (p q : ℕ) := ∑ t ∈ (T p).filter (fun t => ∃ h ∈ H, (q : ℤ) = t + (h : ℤ)*p), μ p t
  let B := Q.filter (fun q => 1/U^2 < |(∑ p ∈ P, mass p q)-C|)
  let V := Q \ B
  have vsub : V ⊆ Q := sdiff_subset
  have bsub : B ⊆ Q := filter_subset _ _
  have partition : V.card + B.card = Q.card := card_sdiff_add_card_eq_card bsub
  have partR : (V.card : ℝ) + B.card = Q.card := by exact_mod_cast partition
  have short (q : ℕ) (hq : q ∈ V) : 4*q < x*x := by
    have hy : 0 ≤ y := by
      by_contra! h
      have upper := (mem_Ioc.mp (mem_filter.mp (vsub hq)).1).2
      change q ≤ ⌊y⌋₊ at upper
      rw [Nat.floor_of_nonpos h.le] at upper
      have lower := (mem_Ioc.mp (mem_filter.mp (vsub hq)).1).1
      omega
    have bound : (q:ℝ) ≤ y := (Nat.le_floor_iff hy).mp (mem_Ioc.mp (mem_filter.mp (vsub hq)).1).2
    have shortR : 4*(q:ℝ) < (x:ℝ)*x := (mul_le_mul_of_nonneg_left bound (by norm_num : (0:ℝ) ≤ 4)).trans_lt hg.1
    exact_mod_cast shortR
  have ids : Q \ V = B := Finset.sdiff_sdiff_eq_self bsub
  change (B.card : ℝ) ≤ X/log X at exc
  change 40*c*X*U/log X ≤ Q.card at ql
  have large := hg.2
  change U^3 + X/log X < 40*c*X*U/log X at large
  obtain ⟨E,w,edge,prob,hit⟩ := push P V H T μ
    (fun p hp => (mem_filter.mp hp).2.pos) law
  have poly : V.card ≤ x^100 := by
    calc V.card ≤ (Finset.range (x^2)).card := Finset.card_le_card (fun q hq => Finset.mem_range.mpr (by have hs := short q hq; rw [pow_two]; omega))
         _ = x^2 := Finset.card_range _
         _ ≤ x^100 := Nat.pow_le_pow_right xpos (by decide)
  refine ⟨V,E,w,C,vsub,short,by linarith,poly,
    (Nat.cast_le.mpr (card_le_card vsub)).trans qu,?_,cmin,cmax,?_,prob,?_,?_⟩
  · rw [ids]
    have h : 0 ≤ X/log X := div_nonneg (Nat.cast_nonneg _) (by linarith)
    exact exc.trans (by calc
      X/log X ≤ K*(X/log X) := le_mul_of_one_le_left h (by linarith)
      _ = K*X/log X := by ring)
  · intro p hp e he
    obtain ⟨sub,card,label⟩ := edge p hp e he
    exact ⟨sub,(Nat.cast_le.mpr card).trans hs,label⟩
  · intro p hp q hq
    rw [hit p hp q hq]
    exact sparse p hp q (vsub hq)
  · intro q hq
    have outside := (mem_sdiff.mp hq).2
    have good : |(∑ p ∈ P, mass p q)-C| ≤ 1/U^2 := by
      by_contra! bad
      exact outside (mem_filter.mpr ⟨vsub hq,bad⟩)
    have eq : (∑ p ∈ P, ∑ e ∈ (E p).filter (q ∈ ·), w p e) = ∑ p ∈ P, mass p q :=
      Finset.sum_congr rfl (fun p hp => hit p hp q hq)
    change |(∑ p ∈ P, ∑ e ∈ (E p).filter (q ∈ ·), w p e)-C| ≤ 1/U^2
    rwa [eq]


lemma stage3 : (∃ c K : ℝ, 0<c ∧ 3≤K ∧ ∀ᶠ x : ℕ in atTop,
    let X : ℝ := x
    let U := log (log X)
    let y := c*X*log X*log U/U
    let z := X^(log U/(4*U))
    let P := (Ioc (x/2) x).filter Nat.Prime
    ∃ a : ℕ → ℕ,
    let Q := (Ioc x ⌊y⌋₊).filter (fun q => q.Prime ∧
      ∀ p : ℕ, p.Prime → p ∉ P → log X^20 < p → (p:ℝ) ≤ z → ¬q ≡ a p [MOD p])
    ∃ (V : Finset ℕ) (E : ℕ → Finset (Finset ℕ)) (w : ℕ → Finset ℕ → ℝ) (C : ℝ),
      V ⊆ Q ∧ (∀ r ∈ V, 4*r < x*x) ∧ U^3 < V.card ∧ V.card ≤ x^100 ∧ (V.card:ℝ) ≤ K*X*U/log X ∧
      ((Q\V).card:ℝ) ≤ K*X/log X ∧ 3≤C ∧ C≤K ∧
      (∀ p ∈ P, ∀ e ∈ E p, e ⊆ V ∧ (e.card:ℝ) ≤ √(log X) ∧
        ∃ b : ℕ, ∀ q ∈ e, q ≡ b [MOD p]) ∧
      (∀ p ∈ P, (∑ e ∈ E p, w p e)=1 ∧ ∀ e ∈ E p, 0≤w p e) ∧
      (∀ p ∈ P, ∀ q ∈ V, (∑ e ∈ (E p).filter (q ∈ ·), w p e) ≤ X^(-3/5:ℝ)) ∧
      (∀ q ∈ V, |(∑ p ∈ P, ∑ e ∈ (E p).filter (q ∈ ·), w p e)-C| ≤ 1/U^2)) → H3 → (∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, ∀ᶠ x : ℕ in atTop, ∃ a : ℕ → ℕ,
    ({q : ℕ | q.Prime ∧ x < q ∧
        (q : ℝ) ≤ c * (x : ℝ) * Real.log (x : ℝ) * Real.log (Real.log (Real.log (x : ℝ))) /
          Real.log (Real.log (x : ℝ)) ∧
        ∀ p : ℕ, p.Prime →
          (Real.log (x : ℝ) ^ 20 < (p : ℝ) ∧
              (p : ℝ) ≤ (x : ℝ) ^
                (Real.log (Real.log (Real.log (x : ℝ))) / (4 * Real.log (Real.log (x : ℝ)))) ∨
            x < 2 * p ∧ p ≤ x) →
          ¬ q ≡ a p [MOD p]}.ncard : ℝ) ≤ K * (x : ℝ) / Real.log (x : ℝ)) := by
  classical
  intro model rounding
  obtain ⟨c, K, hc, hK, good⟩ := model
  obtain ⟨D, hD, round⟩ := rounding K hK
  refine ⟨c, hc, K+D*K, ?_⟩
  filter_upwards [good, round, ev_log 1,
    ev_log2 1] with x hg hr hlog hlog₂
  let X : ℝ := x
  let U := log (log X)
  let y := c*X*log X*log U/U
  let z := X^(log U/(4*U))
  let P := (Ioc (x/2) x).filter Nat.Prime
  obtain ⟨a, V, E, w, C, _, small, big, poly, vupper, exceptional, hC, hCK, edges, prob, sparse, degrees⟩ := hg
  let Q := (Ioc x ⌊y⌋₊).filter (fun q => q.Prime ∧
    ∀ p : ℕ, p.Prime → p ∉ P → log X^20 < p → (p:ℝ) ≤ z → ¬q ≡ a p [MOD p])
  have large (p : ℕ) (hp : p ∈ P) : p.Prime ∧ x < 2*p := by
    obtain ⟨hm, pr⟩ := Finset.mem_filter.mp hp
    have lower := (Finset.mem_Ioc.mp hm).1
    exact ⟨pr, by omega⟩
  have psize : P.card ≤ x := by
    have le := Finset.card_le_card (Finset.filter_subset Nat.Prime (Ioc (x/2) x))
    simpa [P] using le.trans (show (Ioc (x/2) x).card ≤ x by simp)
  obtain ⟨f, choices, leftover⟩ := hr P V E w C psize big poly hC hCK
    (fun p hp e he => ⟨(edges p hp e he).1, (edges p hp e he).2.1⟩) prob sparse degrees
    (fun q hq r hr' qr => pair_weight P E w qr (small r hr') large
      (fun p hp e he => (edges p hp e he).2.2) (fun p hp => (prob p hp).2)
      (Real.rpow_nonneg (Nat.cast_nonneg x) _) (fun p hp => sparse p hp q hq))
  let b (p : ℕ) : ℕ := if hp : p ∈ P then
    if he : f p ∈ E p then Classical.choose ((edges p hp (f p) he).2.2) else 0 else a p
  have chosen (p : ℕ) (hp : p ∈ P) (q : ℕ) (hq : q ∈ f p) : q ≡ b p [MOD p] := by
    rcases choices p hp with hem | he
    · simp [hem] at hq
    · simpa only [b, dif_pos hp, dif_pos he] using
        (Classical.choose_spec ((edges p hp (f p) he).2.2)) q hq
  refine ⟨b, ?_⟩
  let T : Set ℕ := {q | q.Prime ∧ x < q ∧ (q:ℝ) ≤ y ∧ ∀ p : ℕ, p.Prime →
    (log X^20 < p ∧ (p:ℝ) ≤ z ∨ x < 2*p ∧ p ≤ x) → ¬q ≡ b p [MOD p]}
  change (T.ncard:ℝ) ≤ (K+D*K)*X/log X
  have contained : T ⊆ (↑((Q\V) ∪ (V\P.biUnion f)) : Set ℕ) := by
    intro q hq
    obtain ⟨prime, low, high, missed⟩ := hq
    have inQ : q ∈ Q := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨low, Nat.le_floor high⟩, prime, ?_⟩
      intro p pp hp lo hi hit
      apply missed p pp (Or.inl ⟨lo,hi⟩)
      simpa only [b, dif_neg hp] using hit
    by_cases hv : q ∈ V
    · refine Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hv, ?_⟩))
      intro hu
      obtain ⟨p, hp, inc⟩ := Finset.mem_biUnion.mp hu
      have endp := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
      exact missed p (large p hp).1 (Or.inr ⟨(large p hp).2, endp⟩) (chosen p hp q inc)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨inQ,hv⟩))
  have count : T.ncard ≤ (Q\V).card + (V\P.biUnion f).card := by
    have le := Set.ncard_le_ncard contained (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at le
    exact le.trans (Finset.card_union_le _ _)
  have countR : (T.ncard:ℝ) ≤ ((Q\V).card:ℝ) + ((V\P.biUnion f).card:ℝ) := by exact_mod_cast count
  change ((Q\V).card:ℝ) ≤ K*X/log X at exceptional
  change (V.card:ℝ) ≤ K*X*U/log X at vupper
  change ((V\P.biUnion f).card:ℝ) ≤ D*V.card/U at leftover
  have hU : 0 < U := lt_of_lt_of_le zero_lt_one hlog₂
  have lx : 0 < log X := lt_of_lt_of_le zero_lt_one hlog
  calc
    (T.ncard:ℝ) ≤ K*X/log X + D*V.card/U := countR.trans (add_le_add exceptional leftover)
    _ ≤ K*X/log X + D*(K*X*U/log X)/U := by gcongr
    _ = (K+D*K)*X/log X := by field_simp


theorem main : H1 → H2 → H3 → OMA.R_Erdos687_erdos_687_variants_fgkmt_R1.H1 := by
  classical
  intro h1 h2 h3
  obtain ⟨c,hc,K,h⟩ := stage3 (stage2 (stage1 h1 h2) pushEdge growth) h3
  refine ⟨c,hc,max K 1,lt_of_lt_of_le zero_lt_one (le_max_right ..),?_⟩
  filter_upwards [h, ev_log 1] with x hx hlog
  obtain ⟨a, ha⟩ := hx
  refine ⟨a,a,?_⟩
  let X : ℝ := x
  let y := c*X*log X*log (log (log X))/log (log X)
  let z := X^(log (log (log X))/(4*log (log X)))
  let A := (Ioc x ⌊y⌋₊).filter fun q => q.Prime ∧
    (∀ s ≤ ⌊z⌋₊, s.Prime → log X ^ 20 < s → ¬q ≡ a s [MOD s]) ∧
    (∀ p ≤ x, p.Prime → X/2 < p → ¬q ≡ a p [MOD p])
  let T : Set ℕ := {q : ℕ | q.Prime ∧ x < q ∧ (q:ℝ) ≤ y ∧ ∀ p : ℕ, p.Prime →
    (log X^20 < p ∧ (p:ℝ) ≤ z ∨ x < 2*p ∧ p ≤ x) → ¬q ≡ a p [MOD p]}
  have fin : T.Finite := by
    apply (Finset.finite_toSet (Ioc x ⌊y⌋₊)).subset
    intro q hq
    exact mem_Ioc.mpr ⟨hq.2.1,Nat.le_floor hq.2.2.1⟩
  have incl : (A:Set ℕ) ⊆ T := by
    intro q hq
    obtain ⟨interval,pr,sm,lg⟩ := mem_filter.mp hq
    obtain ⟨lo,hi⟩ := mem_Ioc.mp interval
    have ypos : 0 ≤ y := by
      by_contra! hy
      rw [Nat.floor_of_nonpos hy.le] at hi
      omega
    refine ⟨pr,lo,(Nat.le_floor_iff ypos).mp hi,?_⟩
    intro p pp hp
    rcases hp with ⟨lb,ub⟩|⟨lb,ub⟩
    · exact sm p (Nat.le_floor ub) pp lb
    · apply lg p ub pp
      have rel : (x:ℝ) < 2*(p:ℝ) := by exact_mod_cast lb
      change (x:ℝ)/2 < p
      linarith
  have bound := Set.ncard_le_ncard incl fin
  rw [Set.ncard_coe_finset] at bound
  change (A.card:ℝ) ≤ max K 1 * X / log X
  change (T.ncard:ℝ) ≤ K * X / log X at ha
  exact (Nat.cast_le.mpr bound).trans (ha.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left ..) (Nat.cast_nonneg _)) (by change 0 ≤ log (x:ℝ); linarith)))
end OMA.R_Erdos687_erdos_687_variants_fgkmt_R1_H1_R1
