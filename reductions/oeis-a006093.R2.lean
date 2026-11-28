import OMAStatements.S_oeis_a006093
import Mathlib
namespace OMA.R_oeis_a006093_R2
open OMA.S_oeis_a006093
open Finset

lemma prime_den {p m : ℕ} (hp : p.Prime) :
    ((1 : ℚ) / (p : ℚ)^m).den = p^m := by
  rw [←Nat.cast_pow]
  simp [hp.ne_zero]

lemma coprime_rest {p m : ℕ} (hp : p.Prime) (A : Finset ℕ)
    (pr : ∀ q ∈ A, Nat.Prime q) (absent : p ∉ A) :
    p.Coprime (∑ q ∈ A, (1 : ℚ)/(q : ℚ)^m).den := by
  apply Nat.Coprime.of_dvd_right (Rat.den_sum_dvd_prod_den _ _)
  apply Nat.Coprime.prod_right
  intro q hq
  rw [prime_den (pr q hq)]
  apply Nat.Coprime.pow_right
  exact (Nat.coprime_primes hp (pr q hq)).mpr (fun eq => absent (eq.symm ▸ hq))

lemma prime_sum_subset {A B : Finset ℕ} {m : ℕ} (hm : 0 < m)
    (hA : ∀ p ∈ A, Nat.Prime p) (hB : ∀ p ∈ B, Nat.Prime p)
    (same : (∑ p ∈ A, (1 : ℚ)/(p : ℚ)^m) = ∑ p ∈ B, (1 : ℚ)/(p : ℚ)^m) : A ⊆ B := by
  intro p ha
  by_contra hb
  have hp := hA p ha
  have b := coprime_rest (m:=m) hp B hB hb
  have a := coprime_rest (m:=m) hp (A.erase p) (fun q hq => hA q (mem_of_mem_erase hq)) (notMem_erase _ _)
  have eqn : (1:ℚ)/(p:ℚ)^m = (∑ q ∈ B,(1:ℚ)/(q:ℚ)^m) + (-(∑ q ∈ A.erase p,(1:ℚ)/(q:ℚ)^m)) := by
    have hs := sum_erase_add A (fun q : ℕ => (1:ℚ)/(q:ℚ)^m) ha
    rw [same] at hs
    linarith
  have h := Rat.add_den_dvd (∑ q ∈ B,(1:ℚ)/(q:ℚ)^m) (-(∑ q ∈ A.erase p,(1:ℚ)/(q:ℚ)^m))
  rw [←eqn, prime_den hp, Rat.neg_den] at h
  exact (hp.coprime_iff_not_dvd.mp (b.mul_right a)) ((dvd_pow_self _ hm.ne').trans h)

lemma unshifted {m i j s t : ℕ} (hm : 0 < m) (hi : 0 < i) (hij : i ≤ j)
    (hs : 0 < s) (hst : s ≤ t)
    (same : intervalSum 0 m i j = intervalSum 0 m s t) : (i,j)=(s,t) := by
  let P := fun k : ℕ => Nat.nth Nat.Prime (k-1)
  have prime (k) : Nat.Prime (P k) := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
  have inj {k l : ℕ} (hk : 0 < k) (hl : 0 < l) (he : P k=P l) : k=l := by
    have hh := Nat.nth_injective Nat.infinite_setOfPred_prime he
    omega
  have convertSum {a b : ℕ} (ha : 0 < a) :
      (∑ p ∈ (Icc a b).image P, (1:ℚ)/(p:ℚ)^m) = intervalSum 0 m a b := by
    rw [sum_image]
    · simp [intervalSum,P]
    · intro k hk l hl he
      exact inj (lt_of_lt_of_le ha (mem_Icc.mp hk).1) (lt_of_lt_of_le ha (mem_Icc.mp hl).1) he
  have pr {a b : ℕ} : ∀ q ∈ (Icc a b).image P, Nat.Prime q := by
    intro q hq
    obtain ⟨k,_,rfl⟩ := mem_image.mp hq
    exact prime k
  have he := (convertSum hi).trans (same.trans (convertSum hs).symm)
  have eqs := Finset.Subset.antisymm (prime_sum_subset hm pr pr he) (prime_sum_subset hm pr pr he.symm)
  have contain {a b c d : ℕ} (ha : 0 < a) (hc : 0 < c)
      (hh : (Icc a b).image P = (Icc c d).image P) {k : ℕ} (hk : k ∈ Icc a b) :
      k ∈ Icc c d := by
    have member := hh ▸ mem_image_of_mem P hk
    obtain ⟨l,hl,heq⟩ := mem_image.mp member
    have kl := inj (lt_of_lt_of_le hc (mem_Icc.mp hl).1) (lt_of_lt_of_le ha (mem_Icc.mp hk).1) heq
    exact kl ▸ hl
  have h1 := mem_Icc.mp (contain hi hs eqs (left_mem_Icc.mpr hij))
  have h2 := mem_Icc.mp (contain hi hs eqs (right_mem_Icc.mpr hij))
  have h3 := mem_Icc.mp (contain hs hi eqs.symm (left_mem_Icc.mpr hst))
  have h4 := mem_Icc.mp (contain hs hi eqs.symm (right_mem_Icc.mpr hst))
  congr 1 <;> omega

def H1 : Prop := ∀ m i j s t : ℕ, 0 < m → 0 < i → i ≤ j → j < s → s ≤ t →
  intervalSum (-1) m i j ≠ intervalSum (-1) m s t

def H2 : Prop := ∀ (d : ℤ) (m i j s t : ℕ), 0 < d → 0 < m → 0 < i → i ≤ j → j < s → s ≤ t →
  intervalSum d m i j = intervalSum d m s t →
  d=1 ∧ m=1 ∧ i=4 ∧ j=4 ∧ s=8 ∧ t=10

lemma ordered {d : ℤ} {m i j s t : ℕ} (hd : -1 ≤ d) (hi : 0 < i) (hij : i ≤ j)
    (isle : i ≤ s) (hst : s ≤ t)
    (sep : ∀ a b c e : ℕ, 0 < a → a ≤ b → b < c → c ≤ e →
      intervalSum d m a b = intervalSum d m c e → d=1 ∧ m=1 ∧ a=4 ∧ b=4 ∧ c=8 ∧ e=10)
    (he : intervalSum d m i j = intervalSum d m s t) :
    (i,j)=(s,t) ∨ (d=1 ∧ m=1 ∧ ExceptionalIntervals (i,j) (s,t)) := by
  let f := fun k : ℕ => (1 : ℚ)/((Nat.nth Nat.Prime (k-1) : ℚ)+(d:ℚ))^m
  let P := fun k : ℕ => ∑ a ∈ range k, f a
  have sm : StrictMono P := by
    apply strictMono_nat_of_lt_succ
    intro k
    have hp := (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (k-1)).two_le
    have hbase : (0:ℚ) < (Nat.nth Nat.Prime (k-1) : ℚ)+(d:ℚ) := by
      have h1 : (2:ℚ) ≤ (Nat.nth Nat.Prime (k-1) : ℚ) := by exact_mod_cast hp
      have h2 : (-1:ℚ) ≤ (d:ℚ) := by exact_mod_cast hd
      linarith
    change P k < ∑ a ∈ range (k+1), f a
    rw [sum_range_succ]
    change P k < P k + 1/_^m
    have hpos := one_div_pos.mpr (pow_pos hbase m)
    linarith
  have form {a b : ℕ} (h : a ≤ b) : intervalSum d m a b = P (b+1)-P a := by
    have eqi : Icc a b = Ico a (b+1) := by ext k; simp
    unfold intervalSum
    rw [eqi]
    exact sum_Ico_eq_sub f (by omega)
  have he' := he
  rw [form hij,form hst] at he'
  rcases eq_or_lt_of_le isle with h|h
  · subst s
    have hp : P (j+1)=P (t+1) := by linarith
    have ht := sm.injective hp
    exact Or.inl (by congr 1 <;> omega)
  have jt : j < t := by
    by_contra! hg
    have ht := sm.monotone (Nat.succ_le_succ hg)
    have hlt := sm h
    linarith
  right
  by_cases gap : j < s
  · obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := sep i j s t hi hij gap hst he
    exact ⟨rfl,rfl,Or.inl rfl⟩
  · have ha : i ≤ s-1 := by omega
    have hb : j+1 ≤ t := by omega
    have hh : intervalSum d m i (s-1) = intervalSum d m (j+1) t := by
      rw [form ha,form hb,show s-1+1=s by omega]
      linarith
    obtain ⟨rfl,rfl,ia,sb,jc,td⟩ := sep i (s-1) (j+1) t hi ha (by omega) hb hh
    have si : s=5 := by omega
    have ji : j=7 := by omega
    subst_vars
    exact ⟨rfl,rfl,Or.inr rfl⟩

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a006093.main := by
  intro h1 h2 d m i j s t hd hm hi hij hs hst he
  by_cases zero : d=0
  · subst d
    exact Or.inl (unshifted hm hi hij hs hst he)
  have sep : ∀ a b c e : ℕ, 0 < a → a ≤ b → b < c → c ≤ e →
      intervalSum d m a b = intervalSum d m c e → d=1 ∧ m=1 ∧ a=4 ∧ b=4 ∧ c=8 ∧ e=10 := by
    intro a b c e ha hab hbc hce eqn
    by_cases neg : d = -1
    · subst d
      exact (h1 m a b c e hm ha hab hbc hce eqn).elim
    exact h2 d m a b c e (by omega) hm ha hab hbc hce eqn
  rcases le_total i s with h|h
  · exact ordered hd hi hij h hst sep he
  · rcases ordered hd hs hst h hij sep he.symm with eqn|⟨e1,e2,exceptions⟩
    · exact Or.inl eqn.symm
    · exact Or.inr ⟨e1,e2,by simpa [ExceptionalIntervals,Finset.pair_comm] using exceptions⟩
end OMA.R_oeis_a006093_R2
