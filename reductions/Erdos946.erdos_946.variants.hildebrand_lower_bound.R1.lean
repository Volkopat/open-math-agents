import FormalConjectures.ErdosProblems.«946»
import Mathlib

/-! Quantitative counting of Hildebrand's seven translates for the divisor problem. -/

namespace OMA.R_Erdos946_erdos_946_variants_hildebrand_lower_bound_R1
open Filter Finset Real Erdos946 ArithmeticFunction

def H1 : Prop := ∀ c : Fin 7 → ℕ, (∀ i, 0 < c i) → (∑ i, c i) ≤ 27 →
  ∃ i j, i < j ∧ c i=c j

lemma seven_collision : H1 := by
  intro c pos small
  by_contra fail
  have inj : Function.Injective c := by
    intro i j eqn
    rcases lt_trichotomy i j with h|h|h
    · exact (fail ⟨i,j,h,eqn⟩).elim
    · exact h
    · exact (fail ⟨j,i,h,eqn.symm⟩).elim
  let S := univ.image c
  have card : S.card=7 := by simp [S,card_image_of_injective _ inj]
  let f := S.orderEmbOfFin card
  have base (i : Fin 7) : 0 < f i := by
    have hm := S.orderEmbOfFin_mem card i
    obtain ⟨j,_,hj⟩ := mem_image.mp hm
    exact hj ▸ pos j
  have bound (j : ℕ) (hj : j < 7) : j+1 ≤ f ⟨j,hj⟩ := by
    induction j with
    | zero => exact base _
    | succ j ih =>
      have hlt : f ⟨j,by omega⟩ < f ⟨j+1,hj⟩ := f.strictMono (by exact Nat.lt_succ_self j)
      have hh := ih (by omega)
      omega
  have total : (∑ i, f i) = ∑ i, c i := by
    calc
      (∑ i, f i) = ∑ a ∈ S, a := by
        rw [← S.image_orderEmbOfFin_univ card, sum_image]
        exact f.injective.injOn
      _ = _ := sum_image inj.injOn
  have hh := sum_le_sum (s:=(univ : Finset (Fin 7))) (fun i (_:i∈univ) => bound i.val i.isLt)
  have ex : (∑ i : Fin 7, ((i:ℕ)+1))=28 := by decide +kernel
  rw [ex,total] at hh
  omega

lemma tau_squarefree {q : ℕ} (hq : Squarefree q) : sigma 0 q=2^q.primeFactors.card := by
  have ne := hq.ne_zero
  rw [sigma_zero_apply,Nat.card_divisors ne]
  calc
    _ = ∏ _p ∈ q.primeFactors,(2:ℕ) := by
      apply prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree hq (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
    _ = _ := by simp

/-- The reciprocal-mass and rough-value estimates in Hildebrand §4, for disjoint
families of translates, with the divisor multipliers after normalization. -/
def H2 : Prop := ∃ (a : Fin 7 → ℕ) (K D : ℝ), StrictMono a ∧ 0 < K ∧ 0 < D ∧
    ∀ᶠ x : ℝ in atTop, ∃ (M : Finset (Fin 7 → ℕ)) (T : (Fin 7 → ℕ) → Finset ℕ),
    (log x)^7/(log (log x))^3 ≤ K * ∑ m ∈ M, (1:ℝ)/(∏ i, (m i:ℝ)) ∧
    (∀ m ∈ M, x/(log x)^7*((1:ℝ)/(∏ i, (m i:ℝ))) ≤ D*(T m).card) ∧
    (M : Set (Fin 7 → ℕ)).PairwiseDisjoint T ∧
    ∀ m ∈ M, ∀ t ∈ T m, (∀ i, t+a i ≤ ⌊x⌋₊) ∧ ∃ q : Fin 7 → ℕ,
      (∀ i, Squarefree (q i) ∧ 0 < (q i).primeFactors.card) ∧
      (∑ i, (q i).primeFactors.card) ≤ 27 ∧
      ∀ i j, i < j → let d := a j-a i
        d ∣ t+a i ∧ ∃ w : ℕ,
          sigma 0 ((t+a i)/d)=w*sigma 0 (q i) ∧ sigma 0 ((t+a j)/d)=w*sigma 0 (q j)

lemma reconstruct {a : Fin 7 → ℕ} (asort : StrictMono a) {t N : ℕ}
    (bounds : ∀ i, t+a i ≤ N) {q : Fin 7 → ℕ} (sf : ∀ i, Squarefree (q i))
    {i j : Fin 7} (ij : i < j) (counts : (q i).primeFactors.card=(q j).primeFactors.card)
    (h : (a j-a i) ∣ t+a i ∧ ∃ w : ℕ,
      sigma 0 ((t+a i)/(a j-a i))=w*sigma 0 (q i) ∧
      sigma 0 ((t+a j)/(a j-a i))=w*sigma 0 (q j)) :
    ∃ n : ℕ, n ≤ N ∧ sigma 0 n = sigma 0 (n+1) ∧ t+a i=(a j-a i)*n := by
  let d := a j-a i
  have hd : 0 < d := Nat.sub_pos_of_lt (asort ij)
  let n := (t+a i)/d
  obtain ⟨dv,w,eqi,eqj⟩ := h
  have ax : t+a i=d*n := (Nat.mul_div_cancel' dv).symm
  have bx : (t+a j)/d=n+1 := by
    have : t+a j=(t+a i)+d := by dsimp [d]; omega
    rw [this,Nat.add_div_right _ hd]
  change sigma 0 n=w*sigma 0 (q i) at eqi
  change sigma 0 ((t+a j)/d)=w*sigma 0 (q j) at eqj
  rw [bx,tau_squarefree (sf j),←counts,←tau_squarefree (sf i)] at eqj
  exact ⟨n,(Nat.div_le_self _ _).trans (bounds i),eqi.trans eqj.symm,ax⟩

theorem main : H1 → H2 → type_of% @Erdos946.erdos_946.variants.hildebrand_lower_bound := by
  classical
  intro hp ⟨a,K,D,asort,hK,hD,supply⟩
  apply Asymptotics.IsBigO.of_bound (21*(K*D))
  filter_upwards [supply,eventually_ge_atTop (Real.exp 2)] with x supplied hx
  obtain ⟨M,sets,mass,sift,disjoint,pieces⟩ := supplied
  let T := M.biUnion sets
  have x0 := (Real.exp_pos 2).trans_le hx
  have lx : 0 < log x := by
    have h := Real.log_le_log (Real.exp_pos 2) hx
    rw [Real.log_exp] at h
    linarith
  let W := fun m : Fin 7 → ℕ => (1:ℝ)/(∏ i, (m i:ℝ))
  have summed := sum_le_sum sift
  rw [←mul_sum,←mul_sum,←Nat.cast_sum,←card_biUnion disjoint] at summed
  change x/(log x)^7 * (∑ m ∈ M, W m) ≤ D*T.card at summed
  change (log x)^7/(log (log x))^3 ≤ K*(∑ m ∈ M,W m) at mass
  have estimate : x/(log (log x))^3 ≤ (K*D)*T.card := by
    calc
      _ = (x/(log x)^7)*((log x)^7/(log (log x))^3) := by field_simp [lx.ne']
      _ ≤ (x/(log x)^7)*(K*∑ m ∈ M,W m) := mul_le_mul_of_nonneg_left mass (by positivity)
      _ = K*((x/(log x)^7)*∑ m ∈ M,W m) := by ring
      _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left summed hK.le

  let S := (range (⌊x⌋₊+1)).filter (fun n => sigma 0 n=sigma 0 (n+1))
  let pairs := (univ : Finset (Fin 7 × Fin 7)).filter (fun p => p.1<p.2)
  have pairsize : pairs.card=21 := by decide +kernel
  have hits (t : ℕ) (ht : t∈T) : ∃ v ∈ S ×ˢ pairs, t+a v.2.1=(a v.2.2-a v.2.1)*v.1 := by
    obtain ⟨m,hm,ht'⟩ := mem_biUnion.mp ht
    obtain ⟨bounds,q,shape,count,localData⟩ := pieces m hm t ht'
    obtain ⟨i,j,ij,eqn⟩ := hp _ (fun i => (shape i).2) count
    obtain ⟨n,hn,eqt,link⟩ := reconstruct asort bounds (fun i => (shape i).1) ij eqn (localData i j ij)
    exact ⟨(n,i,j),mem_product.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega),eqt⟩,mem_filter.mpr ⟨mem_univ _,ij⟩⟩,link⟩
  let F (t : ℕ) := if ht : t∈T then (hits t ht).choose else (0,(0,0))
  have spec {t : ℕ} (ht : t∈T) : F t ∈ S ×ˢ pairs ∧ t+a (F t).2.1=(a (F t).2.2-a (F t).2.1)*(F t).1 := by
    simpa only [F,dif_pos ht] using (hits t ht).choose_spec
  have hc := card_le_card_of_injOn F (fun _ ht => (spec ht).1) (by
    intro t ht s hs eqn
    have hh := (spec ht).2
    rw [eqn] at hh
    exact Nat.add_right_cancel (hh.trans (spec hs).2.symm))
  rw [card_product,pairsize] at hc
  have xr : 0 ≤ x := (exp_pos 2).le.trans hx
  have logs : 0 ≤ log (log x) := Real.log_nonneg (by
    have aux := (Real.log_le_log (exp_pos 2) hx)
    rw [Real.log_exp] at aux
    linarith)
  change ‖x/(log (log x))^3‖ ≤ 21*(K*D)*‖(S.card:ℝ)‖
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
  have hcast : (T.card:ℝ) ≤ (S.card:ℝ)*21 := by exact_mod_cast hc
  nlinarith only [estimate,mul_le_mul_of_nonneg_left hcast (mul_pos hK hD).le]
end OMA.R_Erdos946_erdos_946_variants_hildebrand_lower_bound_R1
