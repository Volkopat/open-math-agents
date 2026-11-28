import OMAReductions.R_Green46_green_46_variants_lower_R1_H1_R1_H1_R1
import Mathlib

/-! The sieve of Ford, Green, Konyagin, Maynard and Tao (Long gaps
between primes, Theorem 4) uses independent uniform residue choices.
The two-point count below gives concentration of the surviving primes
from their mean. This permits choosing a single residue vector satisfying
both size and coverage bounds, then replacing each conditional shift law
by a finite law with exactly the same hit probabilities. -/


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
    simp [C,h,card_erase_of_mem hv] <;> omega

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
    (f : α → β → ℝ) (D σ e : ℝ) (hD : 0 < D) (hσ : 0 ≤ σ) (he : 0 ≤ e)
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
namespace OMA.R_Green46_green_46_variants_lower_R1_H1_R1_H1_R1_H1_R1

/-- First moment of the preliminary sieve and elementary bounds on its range. -/
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

/-- Coverage for at least half the choices of residues. Integer-valued
conditional laws may have infinite support. -/
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

theorem main : H1 → H2 → OMA.R_Green46_green_46_variants_lower_R1_H1_R1_H1_R1.H1 := by
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

end OMA.R_Green46_green_46_variants_lower_R1_H1_R1_H1_R1_H1_R1
