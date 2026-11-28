import OMAReductions.R_OeisA245212_conjecture_R1_H2_R3

/-! Nonexistence for the even-input branch with at most two distinct odd primes. -/
section
namespace OMA.Smooth245212
open Finset
def Y (p : ℕ) : Option ℕ → ℚ
  | none => 0
  | some e => (((p:ℚ)⁻¹^(e+1)-1)/((p:ℚ)⁻¹-1))/(e+1)
def X (p : ℕ) (e : Option ℕ) : ℚ := 1+(1-Y p e)/((p:ℚ)-1)
theorem y_avg {p : ℕ} (hp : 1<p) (e : ℕ) :
    Y p (some e)=(∑ i ∈ range (e+1), (p:ℚ)⁻¹^i)/((e:ℚ)+1) := by
  rw [geom_sum_eq (x := (p:ℚ)⁻¹) (by
    have : (1:ℚ)<p := by exact_mod_cast hp
    exact (inv_lt_one_of_one_lt₀ this).ne)]; rfl
theorem y_nonneg {p : ℕ} (hp : 1<p) (e : Option ℕ) : 0≤Y p e := by
  cases e with
  | none => rfl
  | some e => rw [y_avg hp]; positivity
theorem y_anti {p : ℕ} (hp : 1<p) : Antitone (fun e : ℕ => Y p (some e)) := by
  have pr : (1:ℚ)<p := by exact_mod_cast hp
  have lp := (inv_lt_one_of_one_lt₀ pr).le
  have pos : 0≤(p:ℚ)⁻¹ := by positivity
  apply antitone_nat_of_succ_le
  intro e
  simp only [y_avg hp,Nat.cast_add,Nat.cast_one]
  rw [sum_range_succ _ (e+1),div_le_div_iff₀ (by positivity) (by positivity)]
  have small : (∑ _i ∈ range (e+1), (p:ℚ)⁻¹^(e+1)) ≤ ∑ i∈range (e+1), (p:ℚ)⁻¹^i :=
    sum_le_sum (fun i hi => pow_le_pow_of_le_one pos lp (mem_range.mp hi).le)
  simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at small
  nlinarith only [small]
theorem y_one {p : ℕ} (hp : 1<p) (e : Option ℕ) : Y p e ≤ 1 := by
  cases e with
  | none => norm_num [Y]
  | some e =>
    have h := y_anti hp (Nat.zero_le e)
    simpa [y_avg hp] using h
theorem x_nonneg {p : ℕ} (hp : 1<p) (e : Option ℕ) : 0≤X p e := by
  have pr : (1:ℚ)<p := by exact_mod_cast hp
  have := sub_nonneg.mpr (y_one hp e)
  unfold X; positivity
structure Band where
  lo : ℕ
  hi : Option ℕ
  deriving DecidableEq
def Band.Contains (b : Band) (e : ℕ) := b.lo≤e ∧ ∀ h, b.hi=some h → e≤h
private theorem mono_range {p e : ℕ} (hp : 1<p) {b : Band} (h : b.Contains e) :
    Y p b.hi ≤ Y p (some e) ∧ Y p (some e) ≤ Y p (some b.lo) ∧
    X p (some b.lo) ≤ X p (some e) ∧ X p (some e) ≤ X p b.hi := by
  have le' : Y p b.hi ≤ Y p (some e) := by
    cases hh : b.hi with
    | none => exact y_nonneg hp _
    | some t => exact y_anti hp (h.2 t hh)
  have ge' := y_anti hp h.1
  have pr : (1:ℚ)<p := by exact_mod_cast hp
  exact ⟨le',ge',by unfold X; gcongr,by unfold X; gcongr⟩
abbrev I := Fin 4
abbrev Box := I → Band
def prime (i : I) : ℕ := ![2,3,5,7] i
theorem prime_lt (i : I) : 1 < prime i := by fin_cases i <;> decide
def score (e : I → ℕ) : ℚ :=
  (∏ i, X (prime i) (some (e i))) + ∏ i, Y (prime i) (some (e i))
def lower (b : Box) : ℚ :=
  (∏ i, X (prime i) (some (b i).lo)) + ∏ i, Y (prime i) (b i).hi
def upper (b : Box) : ℚ :=
  (∏ i, X (prime i) (b i).hi) + ∏ i, Y (prime i) (some (b i).lo)
theorem enclosure {b : Box} {e : I → ℕ} (h : ∀ i,(b i).Contains (e i)) :
    lower b ≤ score e ∧ score e ≤ upper b := by
  have v (i : I) := mono_range (prime_lt i) (h i)
  constructor
  · exact add_le_add
      (prod_le_prod (fun i _ => x_nonneg (prime_lt i) _) (fun i _ => (v i).2.2.1))
      (prod_le_prod (fun i _ => y_nonneg (prime_lt i) _) (fun i _ => (v i).1))
  · exact add_le_add
      (prod_le_prod (fun i _ => x_nonneg (prime_lt i) _) (fun i _ => (v i).2.2.2))
      (prod_le_prod (fun i _ => y_nonneg (prime_lt i) _) (fun i _ => (v i).2.1))
inductive Tree
| leaf
| split (i : I) (cut : ℕ) (left right : Tree)
def left (b : Box) (i : I) (cut : ℕ) : Box := Function.update b i ⟨(b i).lo, some cut⟩
def right (b : Box) (i : I) (cut : ℕ) : Box := Function.update b i ⟨cut+1, (b i).hi⟩
def Tree.check : Tree → Box → Bool
| .leaf,b => decide (2 < lower b ∨ upper b < 2)
| .split i cut l r,b => l.check (left b i cut) && r.check (right b i cut)
theorem Tree.sound (tree : Tree) {b : Box} (cert : tree.check b = true)
    {e : I → ℕ} (h : ∀ i,(b i).Contains (e i)) : score e ≠ 2 := by
  induction tree generalizing b with
  | leaf =>
    obtain pos|neg := of_decide_eq_true cert
    · exact ((enclosure h).1.trans_lt' pos).ne'
    · exact ((enclosure h).2.trans_lt neg).ne
  | split i cut l r il ir =>
    obtain ⟨cl,cr⟩ := Bool.and_eq_true_iff.mp cert
    by_cases ec : e i≤cut
    · apply il cl
      intro j; by_cases ji : j=i
      · subst j; simpa [left,Band.Contains] using And.intro (h i).1 ec
      · simpa [left,ji] using h j
    · apply ir cr
      intro j; by_cases ji : j=i
      · subst j; simpa [right,Band.Contains] using And.intro (by omega : cut+1≤e i) (h i).2
      · simpa [right,ji] using h j
end OMA.Smooth245212
end
section
namespace OMA.Smooth245212
open Finset ArithmeticFunction Nat
open scoped ArithmeticFunction.sigma Function
def W : ArithmeticFunction ℕ := (ArithmeticFunction.id.pmul (σ 0)) * ArithmeticFunction.zeta
lemma w_mult : W.IsMultiplicative :=
  (isMultiplicative_id.pmul isMultiplicative_sigma).mul isMultiplicative_zeta
lemma w_apply (n : ℕ) : W n = ∑ d∈n.divisors, d*d.divisors.card := by
  rw [W,mul_zeta_apply]
  simp only [pmul_apply,id_apply,sigma_zero_apply]
lemma w_pow {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    W (p^e) = ∑ j ∈ range (e+1), p^j*(j+1) := by
  rw [w_apply,Nat.sum_divisors_prime_pow hp]
  simp [Nat.divisors_prime_pow hp]
private lemma weighted (p : ℚ) (e : ℕ) :
    (p-1)*(∑ j ∈ range (e+1), p^j*((j:ℚ)+1)) =
      ((e:ℚ)+1)*p^(e+1)-∑ j ∈ range (e+1), p^j := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ _ (e+1),sum_range_succ _ (e+1),mul_add,ih,pow_succ p (e+1)]
    push_cast; ring
theorem y_factor {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    Y p (some e)*(((e:ℚ)+1)*(p:ℚ)^e) = (σ 1 (p^e) : ℚ) := by
  have pn : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [y_avg hp.one_lt,sigma_one_apply_prime_pow hp]
  push_cast
  calc
    _ = ∑ j ∈ range (e+1), (p:ℚ)⁻¹^j*(p:ℚ)^e := by rw [←sum_mul]; field_simp
    _ = ∑ j ∈ range (e+1), (p:ℚ)^(e-j) := by
      refine sum_congr rfl fun j hj => ?_
      have add : j+(e-j)=e := by have := mem_range.mp hj; omega
      calc
        _ = (p:ℚ)⁻¹^j*((p:ℚ)^j*(p:ℚ)^(e-j)) := by rw [←pow_add,add]
        _ = _ := by rw [inv_pow,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ pn),one_mul]
    _ = _ := by simpa using sum_range_reflect (fun j => (p:ℚ)^j) (e+1)
theorem x_factor {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    X p (some e)*(((e:ℚ)+1)*(p:ℚ)^e) = (W (p^e) : ℚ) := by
  have y := y_factor hp e
  rw [sigma_one_apply_prime_pow hp] at y
  push_cast at y
  rw [w_pow hp]; push_cast
  have pp : (1:ℚ)<p := by exact_mod_cast hp.one_lt
  have h := weighted (p:ℚ) e
  rw [pow_succ] at h
  dsimp [X]
  field_simp [sub_ne_zero.mpr pp.ne']
  linear_combination -h - y
theorem prime_prime (i : I) : Nat.Prime (prime i) := by fin_cases i <;> decide
theorem different : Function.Injective prime := by decide
def number (e : I → ℕ) := ∏ i, prime i^(e i)
section General
variable {ι : Type*} [Fintype ι] (p : ι → ℕ)
def total (e : ι → ℕ) : ℕ := ∏ i, p i^(e i)
private def tax (e : ι → ℕ) : ℚ := ∏ i, (((e i:ℕ):ℚ)+1)*(p i:ℚ)^(e i)
def normalized (e : ι → ℕ) : ℚ :=
  (∏ i, X (p i) (some (e i))) + ∏ i, Y (p i) (some (e i))
theorem normalized_of_eq (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (e : ι → ℕ) (heq : OeisA245212.a (total p e)=(σ 1 (total p e) : ℤ)) :
    normalized p e=2 := by
  classical
  let z (i : ι) := p i ^ (e i)
  have cop : (↑(univ : Finset ι) : Set ι).Pairwise (Coprime on z) := by
    intro i _ j _ h
    exact (((Nat.coprime_primes (hp i) (hp j)).mpr
      (fun eq => h (hinj eq))).pow_left _).pow_right _
  have nz (i : ι) : z i ≠ 0 := pow_ne_zero _ (hp i).ne_zero
  have nn : total p e ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => nz i)
  have tot : W (total p e) = total p e*(total p e).divisors.card +
      ∑ d ∈ (total p e).properDivisors,d*d.divisors.card := by
    calc
      _ = ∑ d ∈ insert (total p e) (total p e).properDivisors, d*d.divisors.card := by
        rw [Nat.insert_self_properDivisors nn,w_apply]
      _ = _ := sum_insert Nat.self_notMem_properDivisors
  have balanced : (W (total p e) : ℚ)+(σ 1 (total p e) : ℚ) =
      2*(total p e:ℚ)*(σ 0 (total p e) : ℚ) := by
    unfold OeisA245212.a at heq
    have ti : (W (total p e):ℤ) = (total p e:ℤ)*(total p e).divisors.card+
        ∑ d∈(total p e).properDivisors,(d:ℤ)*d.divisors.card := by exact_mod_cast tot
    rw [sigma_zero_apply]
    exact_mod_cast (by linarith : (W (total p e):ℤ)+(σ 1 (total p e):ℤ) =
      2*(total p e:ℤ)*(total p e).divisors.card)
  have wp := IsMultiplicative.map_prod z w_mult univ cop
  have sp := IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=1)) univ cop
  have tp := IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=0)) univ cop
  change W (total p e)=_ at wp
  change σ 1 (total p e)=_ at sp
  change σ 0 (total p e)=_ at tp
  simp only [z,sigma_zero_apply_prime_pow (hp _)] at tp
  have factors : tax p e = (total p e:ℚ)*(σ 0 (total p e):ℚ) := by
    rw [tax,prod_mul_distrib,tp,total]
    push_cast; ring
  have taxpos : 0<tax p e := by
    unfold tax
    exact prod_pos fun i _ => mul_pos (by positivity) (pow_pos (by exact_mod_cast (hp i).pos) _)
  apply mul_right_cancel₀ taxpos.ne'
  unfold normalized
  rw [add_mul,show (∏ i, X (p i) (some (e i)))*tax p e = (W (total p e):ℚ) by
    rw [tax,←prod_mul_distrib,wp]; push_cast
    exact prod_congr rfl fun i _ => x_factor (hp i) (e i),
    show (∏ i, Y (p i) (some (e i)))*tax p e = (σ 1 (total p e):ℚ) by
      rw [tax,←prod_mul_distrib,sp]; push_cast
      exact prod_congr rfl fun i _ => y_factor (hp i) (e i),factors]
  linarith only [balanced]
end General
theorem score_of_eq (e : I → ℕ)
    (heq : OeisA245212.a (number e)=(σ 1 (number e) : ℤ)) : score e=2 :=
  normalized_of_eq prime prime_prime different e heq
end OMA.Smooth245212
end
section
namespace OMA.Abundance245212
open OMA.Smooth245212 Finset ArithmeticFunction Nat
open scoped ArithmeticFunction.sigma
private theorem twice_weighted {p : ℕ} (hp : 1≤p) (e : ℕ) :
    (e+1)*(p^e+∑ i∈range (e+1),p^i) ≤
      2*(∑ i∈range (e+1),p^i*(i+1)) := by
  induction e with
  | zero => simp
  | succ e ih =>
    have bound : (∑ i∈range (e+1), p^i) ≤ (e+1)*p^e := by
      calc
        _ ≤ ∑ _i∈range (e+1),p^e := sum_le_sum (fun i hi =>
          Nat.pow_le_pow_right hp (by have := mem_range.mp hi; omega))
        _ = _ := by simp
    rw [sum_range_succ _ (e+1),sum_range_succ _ (e+1)]
    linarith only [ih,bound]
theorem square_bound (n : ℕ) : (σ 0 n)^2*n*(σ 1 n) ≤ (W n)^2 := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p e hp =>
    rw [sigma_zero_apply_prime_pow hp,sigma_one_apply_prime_pow hp,w_pow hp]
    have h := twice_weighted hp.pos e
    have hs := Nat.pow_le_pow_left h 2
    have am (u v : ℕ) : 4*u*v ≤ (u+v)^2 := by
      zify; nlinarith only [sq_nonneg ((u:ℤ)-v)]
    have haux := Nat.mul_le_mul_left ((e+1)^2) (am (p^e) (∑ i∈range (e+1),p^i))
    linarith only [haux,hs]
  | coprime a b _ _ cop ia ib =>
    rw [isMultiplicative_sigma.map_mul_of_coprime cop,
      isMultiplicative_sigma.map_mul_of_coprime cop,w_mult.map_mul_of_coprime cop]
    simpa only [mul_pow,mul_assoc,mul_left_comm,mul_comm] using Nat.mul_le_mul ia ib
theorem balance {n : ℕ} (hn : n≠0)
    (eq : OeisA245212.a n=(σ 1 n:ℤ)) : W n+σ 1 n=2*n*(σ 0 n) := by
  have total : W n = n*n.divisors.card+∑ d∈n.properDivisors,d*d.divisors.card := by
    calc
      _ = ∑ d∈insert n n.properDivisors,d*d.divisors.card := by
        rw [Nat.insert_self_properDivisors hn,w_apply]
      _ = _ := sum_insert Nat.self_notMem_properDivisors
  unfold OeisA245212.a at eq
  zify at total ⊢
  simp only [sigma_zero_apply]
  linarith
theorem sigma_lt {n : ℕ} (hn : n≠0)
    (eq : OeisA245212.a n=(σ 1 n:ℤ)) : σ 1 n<4*n := by
  have tpos : 0<σ 0 n := by
    rw [sigma_zero_apply,card_pos]; exact ⟨n,Nat.mem_divisors_self _ hn⟩
  have spos : 0<σ 1 n := by
    rw [sigma_one_apply]; exact sum_pos' (fun _ _ => by omega)
      ⟨n,Nat.mem_divisors_self _ hn,by omega⟩
  have bal := balance hn eq
  have ww : W n < 2*n*(σ 0 n) := by omega
  have strict := (square_bound n).trans_lt (Nat.pow_lt_pow_left ww (by decide : 2≠0))
  by_contra! ge
  have bad := Nat.mul_le_mul_left ((σ 0 n)^2*n) ge
  linarith only [bad,strict]
private theorem tau_gt_one {n : ℕ} (h : 1<n) : 1<σ 0 n := by
  rw [sigma_zero_apply]
  have hs : ({1,n}:Finset ℕ) ⊆ n.divisors := by
    intro d hd; simp only [mem_insert,mem_singleton] at hd
    rcases hd with rfl|rfl
    · exact one_mem_divisors.mpr (by omega)
    · exact mem_divisors_self _ (by omega)
  have := card_le_card hs
  have hc : 2≤n.divisors.card := by simpa [h.ne] using this
  omega
private theorem sigma_lt_twice_of_prime_tau (n : ℕ) :
    Nat.Prime (σ 0 n) → σ 1 n < 2*n := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p e hp =>
    intro ht; clear ht; rw [sigma_one_apply_prime_pow hp]
    induction e with
    | zero => simp
    | succ e ih =>
      rw [sum_range_succ _ (e+1),pow_succ]
      have hh := Nat.mul_le_mul_left (p^e) hp.two_le
      omega
  | coprime a b ha hb cop _ _ =>
    rw [isMultiplicative_sigma.map_mul_of_coprime cop]
    intro h
    rcases Nat.prime_mul_iff.mp h with ⟨_,h⟩|⟨_,h⟩
    · have := tau_gt_one hb; omega
    · have := tau_gt_one ha; omega
theorem no_resonance {m p : ℕ} (hm : m≠0) (hp : Nat.Prime p) (cop : ¬p∣m)
    (eq : OeisA245212.a m=(σ 1 m:ℤ)) (resonant : p*(σ 1 m)=2*m*(σ 0 m)) :
    p=2 ∧ m=1 := by
  by_cases p2 : p=2
  · subst p; refine ⟨rfl,?_⟩
    by_contra! more
    have s : σ 1 m < (σ 0 m)*m := by
      rw [sigma_one_apply,sigma_zero_apply]
      calc
        _ < ∑ _i∈m.divisors,m := sum_lt_sum
          (fun i hi => le_of_dvd (by omega) (dvd_of_mem_divisors hi))
          ⟨1,one_mem_divisors.mpr hm,by omega⟩
        _ = _ := by simp
    linarith only [s,resonant]
  · have p2nd : ¬p∣2 := fun h => p2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    have hdiv : p ∣ 2*m*(σ 0 m) := resonant ▸ dvd_mul_right _ _
    obtain ⟨k,hk⟩ := (hp.dvd_mul.mp hdiv).resolve_left
      (fun f => (hp.dvd_mul.mp f).elim p2nd cop)
    have can : p*(σ 1 m) = p*(2*m*k) := by rw [resonant,hk]; ring
    have sm := Nat.eq_of_mul_eq_mul_left hp.pos can
    have low := sigma_lt hm eq
    have tpos : 0<σ 0 m := by
      rw [sigma_zero_apply,Finset.card_pos]; exact ⟨m,mem_divisors_self _ hm⟩
    have k0 : 0<k := by by_contra! hz; simp [show k=0 by omega] at hk; omega
    have k1 : k=1 := by
      by_contra! h; have large := Nat.mul_le_mul_left (2*m) (show 2≤k by omega)
      linarith only [low,sm,large]
    rw [k1,mul_one] at hk sm
    have hlt := sigma_lt_twice_of_prime_tau m (hk ▸ hp)
    omega
theorem eq_of_balance {n : ℕ} (hn : n≠0) (bal : W n+σ 1 n=2*n*(σ 0 n)) :
    OeisA245212.a n=(σ 1 n:ℤ) := by
  have total : W n = n*n.divisors.card+∑ d∈n.properDivisors,d*d.divisors.card := by
    calc
      _ = ∑ d∈insert n n.properDivisors,d*d.divisors.card := by
        rw [Nat.insert_self_properDivisors hn,w_apply]
      _ = _ := sum_insert Nat.self_notMem_properDivisors
  rw [sigma_zero_apply] at bal
  unfold OeisA245212.a
  zify at total bal
  linarith
theorem affine_of_eq {p m e : ℕ} (hm : m≠0) (hp : Nat.Prime p) (cop : ¬p∣m)
    (eq : OeisA245212.a (m*p^e)=(σ 1 (m*p^e):ℤ)) :
    (W m:ℚ)*X p (some e)+(σ 1 m:ℚ)*Y p (some e)=2*m*(σ 0 m:ℚ) := by
  have cb := ((hp.coprime_iff_not_dvd.mpr cop).pow_left e).symm
  have bal := balance (mul_ne_zero hm (pow_ne_zero _ hp.ne_zero)) eq
  rw [w_mult.map_mul_of_coprime cb,isMultiplicative_sigma.map_mul_of_coprime cb,
    isMultiplicative_sigma.map_mul_of_coprime cb,sigma_zero_apply_prime_pow hp] at bal
  have cast : (W m:ℚ)*(W (p^e):ℚ)+(σ 1 m:ℚ)*(σ 1 (p^e):ℚ)=
      2*(m*(p:ℚ)^e)*((σ 0 m:ℚ)*((e:ℚ)+1)) := by exact_mod_cast bal
  have z : ((e:ℚ)+1)*(p:ℚ)^e ≠ 0 := mul_ne_zero (by positivity)
    (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))
  apply mul_right_cancel₀ z
  rw [add_mul,mul_assoc,mul_assoc (σ 1 m:ℚ),x_factor hp e,y_factor hp e]
  linarith only [cast]
theorem y_strict {p : ℕ} (hp : 1<p) : StrictAnti (fun e : ℕ => Y p (some e)) := by
  have pp : (1:ℚ)<p := by exact_mod_cast hp
  have pos : 0<(p:ℚ)⁻¹ := by positivity
  have lt := inv_lt_one_of_one_lt₀ pp
  apply strictAnti_nat_of_succ_lt
  intro e
  simp only [y_avg hp,Nat.cast_add,Nat.cast_one]
  rw [sum_range_succ _ (e+1),div_lt_div_iff₀ (by positivity) (by positivity)]
  have small : (∑ _i ∈ range (e+1), (p:ℚ)⁻¹^(e+1)) < ∑ i∈range (e+1), (p:ℚ)⁻¹^i :=
    sum_lt_sum_of_nonempty (by simp) (fun _ hi =>
      pow_right_strictAnti₀ pos lt (mem_range.mp hi))
  simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at small
  linarith only [small]
theorem unique_exponent {p m e f : ℕ} (hm : m≠0) (hp : Nat.Prime p) (cop : ¬p∣m)
    (he : OeisA245212.a (m*p^e)=(σ 1 (m*p^e):ℤ))
    (hf : OeisA245212.a (m*p^f)=(σ 1 (m*p^f):ℤ)) :
    e=f ∨ p=2 ∧ m=1 := by
  by_cases ef : e=f
  · exact Or.inl ef
  refine Or.inr ?_
  have ee := affine_of_eq hm hp cop he
  have ff := affine_of_eq hm hp cop hf
  have ne := (y_strict hp.one_lt).injective.ne ef
  have pp : (p:ℚ) ≠ 1 := by exact_mod_cast hp.ne_one
  unfold X at ee ff
  field_simp [sub_ne_zero.mpr pp] at ee ff
  have coeff : ((σ 1 m:ℚ)*((p:ℚ)-1)-(W m:ℚ)) *
      (Y p (some e)-Y p (some f))=0 := by linear_combination ee-ff
  have w := (mul_eq_zero.mp coeff).resolve_right (sub_ne_zero.mpr ne)
  have res : (p:ℚ)*(σ 1 m:ℚ)=2*m*(σ 0 m:ℚ) := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr pp)
    linear_combination ee+w*((p:ℚ)-Y p (some e))
  apply no_resonance hm hp cop _ (by exact_mod_cast res)
  apply eq_of_balance hm
  exact_mod_cast (show (W m:ℚ)+(σ 1 m:ℚ)=2*m*(σ 0 m:ℚ) by linarith only [w,res])
end OMA.Abundance245212
end
section
namespace OMA.PrimePowerDiv245212
open Finset ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212
open scoped ArithmeticFunction.sigma
theorem weighted {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (p-1)*W (p^e)+σ 1 (p^e)=p*((e+1)*p^e) := by
  rw [w_pow hp,sigma_one_apply_prime_pow hp]
  induction e with
  | zero => simp; have := hp.one_lt; omega
  | succ e ih =>
    rw [sum_range_succ _ (e+1),sum_range_succ _ (e+1),mul_add,pow_succ]
    have add := Nat.sub_add_cancel (show 1≤p from hp.pos)
    nlinarith only [ih,congrArg (fun z:ℕ => z*(p^e*p)*(e+2)) add]
theorem power_divides {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (cop : m.Coprime p) (e : ℕ)
    (eq : OeisA245212.a (m*p^e)=(σ 1 (m*p^e):ℤ)) :
    (p:ℤ)^e ∣ (W m:ℤ)-((p:ℤ)-1)*(σ 1 m:ℤ) := by
  have van : (p:ZMod (p^e))^e=0 := by rw [←Nat.cast_pow]; exact ZMod.natCast_self _
  have w := congrArg (fun n : ℕ => (n:ZMod (p^e))) (weighted hp e)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub hp.pos,Nat.cast_one,Nat.cast_pow,van,
    mul_zero] at w
  have s : ((p:ZMod (p^e))-1)*(σ 1 (p^e):ℕ) = -1 := by
    rw [sigma_one_apply_prime_pow hp]
    simp only [Nat.cast_sum,Nat.cast_pow]
    rw [mul_comm,geom_sum_mul,pow_succ,van,zero_mul,zero_sub]
  have b := balance (mul_ne_zero hm.ne' (pow_ne_zero _ hp.ne_zero)) eq
  rw [w_mult.map_mul_of_coprime (cop.pow_right e),
    isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right e)] at b
  have bb := congrArg (fun n : ℕ => (n:ZMod (p^e))) b
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,van,mul_zero,zero_mul] at bb
  rw [←Nat.cast_pow]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p^e)).mp
  push_cast
  linear_combination ((p:ZMod (p^e))-1)^2*bb - (W m:ZMod (p^e))*((p:ZMod (p^e))-1)*w +
    ((W m:ZMod (p^e))-((p:ZMod (p^e))-1)*(σ 1 m:ZMod (p^e)))*s
theorem nonzero {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hp2 : p≠2)
    (cop : m.Coprime p) (e : ℕ) (eq : OeisA245212.a (m*p^e)=(σ 1 (m*p^e):ℤ)) :
    (W m:ℤ)-((p:ℤ)-1)*(σ 1 m:ℤ)≠0 := by
  intro zero
  have same : W m=(p-1)*(σ 1 m) := by
    apply Nat.cast_inj (R:=ℤ) |>.mp
    push_cast [Nat.cast_sub hp.pos]; omega
  have b := balance (mul_ne_zero hm.ne' (pow_ne_zero _ hp.ne_zero)) eq
  rw [w_mult.map_mul_of_coprime (cop.pow_right e),
    isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right e),
    isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right e),
    sigma_zero_apply_prime_pow hp,same] at b
  have t := congrArg (fun v:ℕ => v*(σ 1 m)) (weighted hp e)
  have v : (p*(σ 1 m))*((e+1)*p^e)=(2*m*(σ 0 m))*((e+1)*p^e) := by
    nlinarith only [b,t]
  have res := Nat.eq_of_mul_eq_mul_right (show 0<(e+1)*p^e by have := hp.pos; positivity) v
  have mb : W m+σ 1 m=2*m*(σ 0 m) := by
    rw [←res,same]
    nlinarith only [congrArg (fun v:ℕ => v*(σ 1 m)) (Nat.sub_add_cancel hp.pos)]
  exact hp2 (no_resonance hm.ne' hp (hp.coprime_iff_not_dvd.mp cop.symm)
    (eq_of_balance hm.ne' mb) res).1
theorem cofactor_bound {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hp2 : p≠2)
    (cop : m.Coprime p) (e : ℕ) (eq : OeisA245212.a (m*p^e)=(σ 1 (m*p^e):ℤ)) :
    p^e ≤ ((W m:ℤ)-((p:ℤ)-1)*(σ 1 m:ℤ)).natAbs := by
  have d := power_divides hm hp cop e eq
  have nz := nonzero hm hp hp2 cop e eq
  apply Nat.le_of_dvd (Int.natAbs_pos.mpr nz)
  simpa using Int.natAbs_dvd_natAbs.mpr d
end OMA.PrimePowerDiv245212
end
section
namespace OMA.TwoOddGlobalGap245212
def defect (f g p q B C : ℤ) :=
  (f+g)*B*C*(p-1)^2*(q-1)^2 -
    p*q*(f*(B*(p-1)-1)*(C*(q-1)-1)+g*(p-1)*(q-1))
def alpha (f g p q C : ℤ) := q*(f*(C*(q-1)-1)-g*(p-1)*(q-1))
def beta (f g p q B : ℤ) := p*(f*(B*(p-1)-1)-g*(p-1)*(q-1))
theorem expansion (f g p q B C P Q W V S T : ℤ)
    (pw : (p-1)^2*W=p*(B*(p-1)-1)*P+1)
    (qw : (q-1)^2*V=q*(C*(q-1)-1)*Q+1)
    (ps : (p-1)*S=p*P-1) (qs : (q-1)*T=q*Q-1) :
    (p-1)^2*(q-1)^2*(f*W*V+g*S*T-(f+g)*B*C*P*Q) =
      -defect f g p q B C*P*Q+alpha f g p q C*Q+beta f g p q B*P+f+g*(p-1)*(q-1) := by
  unfold defect alpha beta
  linear_combination f*((q-1)^2*V)*pw+f*(p*(B*(p-1)-1)*P+1)*qw+
    g*(p-1)*(q-1)*((q-1)*T)*ps+g*(p-1)*(q-1)*(p*P-1)*qs
private theorem divides {f g p q B C : ℕ} (hq : q.Prime) (hp : 3≤p) (pq : p<q)
    (zero : defect f g p q B C=0) : q ∣ (f+g)*B*C := by
  let : Fact q.Prime := ⟨hq⟩
  have modq := congrArg (fun z:ℤ => (z:ZMod q)) zero
  unfold defect at modq
  push_cast at modq
  simp only [ZMod.natCast_self] at modq
  have mz : (((f:ZMod q)+g)*B*C)*((p:ZMod q)-1)^2=0 := by linear_combination modq
  have pn : (p:ZMod q)-1≠0 := by
    rw [←Nat.cast_one,←Nat.cast_sub (by omega : 1≤p)]
    exact fun h => Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      ((ZMod.natCast_eq_zero_iff (p-1) q).mp h)
  have dm := (mul_eq_zero.mp mz).resolve_right (pow_ne_zero _ pn)
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  push_cast; exact dm
theorem nonzero_of_positive_alpha {p q B C k f g l : ℕ} (hq : q.Prime) (hp : 3≤p) (pq : p<q)
    (hb : 2≤B) (hc : 2≤C) (hk : 2≤k) (small : (p:ℤ)-1<(k:ℤ)*(C-1))
    (gpos : 0<g) (fg : k*g≤f) (frac : f+g=(k+1)*l) (unit : ¬q∣l)
    (actual : alpha f g p q C*(q:ℤ)^(C-1)+beta f g p q B*(p:ℤ)^(B-1)+f+
      g*(p-1)*(q-1)≤defect f g p q B C*(p:ℤ)^(B-1)*(q:ℤ)^(C-1)) :
    defect f g p q B C ≠ 0 := by
  intro zero
  have dv := divides hq hp pq zero
  rw [frac] at dv
  let u : ℤ := p-1
  let v : ℤ := q-1
  have pp' : (0:ℤ)<p := by omega
  have qp' : (0:ℤ)<q := by omega
  have uv : u<v := by dsimp [u,v]; omega
  have up : (2:ℤ)≤u := by dsimp [u]; omega
  have vp : (2:ℤ)≤v := by omega
  have fp : (k:ℤ)*g≤f := by exact_mod_cast fg
  have pp : (0:ℤ)<g := by exact_mod_cast gpos
  have posf : 0<(f:ℤ) := by nlinarith only [fp,mul_pos (by omega : (0:ℤ)<k) pp]
  have kb : (B:ℤ)≤k*(B-1) := by
    nlinarith only [mul_nonneg (by omega : (0:ℤ)≤k-2) (by omega : (0:ℤ)≤B-1), (show (2:ℤ)≤B by exact_mod_cast hb)]
  have kbase : (k:ℤ)≤k*(B-1) := by
    nlinarith only [mul_nonneg (by positivity : (0:ℤ)≤k) (by omega : (0:ℤ)≤B-2)]
  have kc : u<k*(C-1) := small
  have cden : 0<(C:ℤ)*v-1 := by nlinarith only [mul_nonneg (by omega : (0:ℤ)≤C-2) (by omega : 0≤v),vp]
  have bden : 0<(B:ℤ)*u-1 := by nlinarith only [mul_nonneg (by omega : (0:ℤ)≤B-2) (by omega : 0≤u),up]
  have compare (N h z : ℤ) (zd : 1≤z) (den : 0<N*z-1)
      (lim : h<(k:ℤ)*(N-1)) : (g:ℤ)*h*z < f*(N*z-1) := by
    have hm := mul_lt_mul_of_pos_right lim (mul_pos pp (by omega : 0<z))
    have kern := mul_le_mul_of_nonneg_right fp den.le
    nlinarith only [hm,kern,mul_nonneg (mul_nonneg (by positivity : (0:ℤ)≤k) pp.le)
      (by omega : 0≤z-1)]
  have first := compare C u v (by omega) cden kc
  have al : 0<alpha f g p q C := by
    unfold alpha
    exact mul_pos (by positivity) (sub_pos.mpr first)
  rw [zero,zero_mul,zero_mul] at actual
  have bp : beta f g p q B<0 := by
    by_contra! ge
    nlinarith only [actual,mul_pos al (by positivity : (0:ℤ)<q^(C-1)),
      mul_nonneg ge (by positivity : (0:ℤ)≤p^(B-1)),posf,
      mul_nonneg (mul_nonneg pp.le (by omega : 0≤u)) (by omega : 0≤v)]
  have bound : k*(B-1)<v := by
    have neg : (f:ℤ)*(B*u-1)<g*u*v :=
      sub_neg.mp (neg_of_mul_neg_right bp (by positivity : (0:ℤ)≤p))
    by_contra! bad
    have m := mul_le_mul_of_nonneg_right bad (mul_nonneg pp.le (by omega : 0≤u))
    have kern := mul_le_mul_of_nonneg_right fp bden.le
    nlinarith only [neg,m,kern,mul_nonneg (mul_nonneg (by positivity : (0:ℤ)≤k) pp.le) (by omega : 0≤u-1)]
  have qB : B<q := by dsimp [v] at bound; omega
  have qK : k+1<q := by dsimp [v] at bound; omega
  have divC : q∣C := by
    rcases hq.dvd_mul.mp dv with previous | done
    · rcases hq.dvd_mul.mp previous with pre | bBad
      · rcases hq.dvd_mul.mp pre with kBad | lBad
        · exact False.elim (Nat.not_dvd_of_pos_of_lt (by omega) qK kBad)
        · exact False.elim (unit lBad)
      · exact False.elim (Nat.not_dvd_of_pos_of_lt (by omega) qB bBad)
    · exact done
  have qC := Nat.le_of_dvd (by omega : 0<C) divC
  have kC : 2*u < (k:ℤ)*(C-1) := by
    dsimp [u,v] at uv ⊢
    nlinarith only [mul_nonneg (by omega : (0:ℤ)≤k-2) (by omega : (0:ℤ)≤C-1),
      (show (q:ℤ)≤C by exact_mod_cast qC),uv]
  have stronger := compare C (2*u) v (by omega) cden kC
  have asum : 0<alpha f g p q C + beta f g p q B := by
    change 0<(q:ℤ)*(f*(C*v-1)-g*u*v)+p*(f*(B*u-1)-g*u*v)
    nlinarith only [mul_pos (by positivity : (0:ℤ)<q) (sub_pos.mpr stronger),
      mul_nonneg (by omega : (0:ℤ)≤q-p) (mul_nonneg (mul_nonneg pp.le (by omega : 0≤u)) (by omega : 0≤v)),
      mul_pos (mul_pos (by positivity : (0:ℤ)<p) posf) bden]
  have sizes : (p:ℤ)^(B-1)≤(q:ℤ)^(C-1) := calc
    _ ≤ (q:ℤ)^(B-1) := pow_le_pow_left₀ (by positivity) (by exact_mod_cast pq.le) _
    _ ≤ _ := pow_le_pow_right₀ (by omega : (1:ℤ)≤q) (by omega)
  nlinarith only [actual,mul_pos asum (by positivity : (0:ℤ)<p^(B-1)),
    mul_nonneg al.le (sub_nonneg.mpr sizes),posf,
    mul_nonneg (mul_nonneg pp.le (by omega : 0≤u)) (by omega : 0≤v)]
theorem nonzero {p q B C k f g l : ℕ} (hq : q.Prime) (hp : 3≤p) (pq : p<q)
    (hb : 2≤B) (hc : 16≤C) (hk : 2≤k) (small : p≤5*(k+1))
    (gpos : 0<g) (fg : k*g≤f) (frac : f+g=(k+1)*l) (unit : ¬q∣l)
    (actual : alpha f g p q C*(q:ℤ)^(C-1)+beta f g p q B*(p:ℤ)^(B-1)+f+
      g*(p-1)*(q-1)≤defect f g p q B C*(p:ℤ)^(B-1)*(q:ℤ)^(C-1)) :
    defect f g p q B C ≠ 0 := by
  apply nonzero_of_positive_alpha hq hp pq hb (by omega) hk _ gpos fg frac unit actual
  have hs : (p:ℤ)≤5*((k:ℤ)+1) := by exact_mod_cast small
  nlinarith only [hs,mul_nonneg (by positivity : (0:ℤ)≤k) (by omega : (0:ℤ)≤C-16),
    (show (2:ℤ)≤k by exact_mod_cast hk)]
end OMA.TwoOddGlobalGap245212
end
section
namespace OMA.ComplementaryLocal245212
open Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
theorem moments {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ((p:ℤ)-1)*(σ 1 (p^e):ℤ)=p*(p:ℤ)^e-1 ∧
    ((p:ℤ)-1)^2*(W (p^e):ℤ)=p*((e+1)*(p-1)-1)*(p:ℤ)^e+1 := by
  have g : ((p:ℤ)-1)*(σ 1 (p^e):ℤ)=p*(p:ℤ)^e-1 := by
    rw [sigma_one_apply_prime_pow hp]
    push_cast
    rw [mul_comm ((p:ℤ)-1),geom_sum_mul,pow_succ,mul_comm]
  refine ⟨g,?_⟩
  have w := OMA.PrimePowerDiv245212.weighted hp e
  zify [Nat.cast_sub hp.pos] at w
  linear_combination ((p:ℤ)-1)*w-g
theorem bounds {p : ℕ} (hp : p.Prime) (odd : 3≤p) (e : ℕ) :
    2*(σ 1 (p^e))≤3*p^e ∧ 2*W (p^e)≤3*(e+1)*p^e ∧
    (e+1)*p^e≤W (p^e) ∧ σ 1 (p^e)≤W (p^e) := by
  have g := (moments hp e).1
  have ps : ((p:ℤ)-1)*((3:ℤ)*p^e-2*(σ 1 (p^e):ℤ)) =
      ((p:ℤ)-3)*p^e+2 := by linear_combination -2*g
  have sb : 2*(σ 1 (p^e))≤3*p^e := by
    have pp : (0:ℤ)≤p-3 := by omega
    have : 0≤((p:ℤ)-1)*(3*(p:ℤ)^e-2*(σ 1 (p^e):ℤ)) :=
      ps ▸ (by positivity)
    have hh := nonneg_of_mul_nonneg_right this (by omega : (0:ℤ)<p-1)
    exact_mod_cast (sub_nonneg.mp hh)
  have simple : W (p^e) ≤ (e+1)*(σ 1 (p^e)) := by
    rw [w_pow hp,sigma_one_apply_prime_pow hp,mul_sum]
    refine sum_le_sum fun i hi => ?_
    rw [mul_comm (e+1)]
    exact Nat.mul_le_mul_left _ (by have := mem_range.mp hi; omega)
  refine ⟨sb,by nlinarith only [Nat.mul_le_mul_left 2 simple,Nat.mul_le_mul_left (e+1) sb],?_,?_⟩
  · rw [w_pow hp,sum_range_succ]
    nlinarith only [Nat.zero_le (∑ i∈range e,p^i*(i+1))]
  · rw [w_pow hp,sigma_one_apply_prime_pow hp]
    exact sum_le_sum fun i _ => by nlinarith only [Nat.zero_le (p^i*i)]
theorem last {p : ℕ} (hp : p.Prime) (odd : 3≤p) (e : ℕ) :
    W (p^(e+1))=(e+2)*p^(e+1)+W (p^e) ∧
    σ 1 (p^(e+1))=p^(e+1)+σ 1 (p^e) ∧ 2*W (p^e)≤3*(e+1)*p^e := by
  refine ⟨?_,?_,(bounds hp odd e).2.1⟩
  · rw [w_pow hp,w_pow hp,sum_range_succ]; ring
  · rw [sigma_one_apply_prime_pow hp,sigma_one_apply_prime_pow hp,sum_range_succ,add_comm]
private theorem binary (k : ℕ) :
    (σ 1 (2^k):ℤ)=(2:ℤ)^(k+1)-1 ∧ (W (2^k):ℤ)=1+k*(2:ℤ)^(k+1) := by
  have h := moments Nat.prime_two k
  norm_num at h
  rw [pow_succ]; constructor <;> nlinarith only [h.1,h.2]
theorem physical {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (op : p≠2)
    (oq : q≠2) (pq : p≠q) (a d k : ℕ)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    (1+k*(2:ℤ)^(k+1))*(W (p^a):ℤ)*(W (q^d):ℤ)+
      ((2:ℤ)^(k+1)-1)*(σ 1 (p^a):ℤ)*(σ 1 (q^d):ℤ) =
      (2:ℤ)^(k+1)*(k+1)*(a+1)*(d+1)*p^a*q^d := by
  have tp : (2^k).Coprime (p^a) :=
    (((Nat.coprime_primes Nat.prime_two hp).mpr op.symm).pow_left k).pow_right a
  have tq : (2^k*p^a).Coprime (q^d) :=
    ((((Nat.coprime_primes Nat.prime_two hq).mpr oq.symm).pow_left k).mul_left
      (((Nat.coprime_primes hp hq).mpr pq).pow_left a)).pow_right d
  have pos : 0<p := hp.pos
  have pos' : 0<q := hq.pos
  have b := OMA.Abundance245212.balance (show 2^k*p^a*q^d≠0 by positivity) eqn
  rw [w_mult.map_mul_of_coprime tq,w_mult.map_mul_of_coprime tp,
    isMultiplicative_sigma.map_mul_of_coprime tq,isMultiplicative_sigma.map_mul_of_coprime tp,
    isMultiplicative_sigma.map_mul_of_coprime tq,isMultiplicative_sigma.map_mul_of_coprime tp,
    sigma_zero_apply_prime_pow Nat.prime_two,sigma_zero_apply_prime_pow hp,sigma_zero_apply_prime_pow hq] at b
  zify at b
  rw [(binary k).1,(binary k).2] at b
  rw [pow_succ (2:ℤ) k] at b ⊢
  linear_combination b
theorem original_separations {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (pq : p<q) {a d k : ℕ} (ha : 1≤a) (hd : 15≤d) (hk : 2≤k) (small : p≤5*(k+1))
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    OMA.TwoOddGlobalGap245212.defect k 1 p q (a+1) (d+1)≠0 ∧
    OMA.TwoOddGlobalGap245212.defect (1+k*(2:ℤ)^(k+1)) ((2:ℤ)^(k+1)-1) p q (a+1) (d+1)≠0 := by
  have bal := physical hp hq (by omega) (by omega) pq.ne a d k eqn
  let P : ℤ := (p:ℤ)^a
  let Q : ℤ := (q:ℤ)^d
  let W : ℤ := OMA.Smooth245212.W (p^a)
  let V : ℤ := OMA.Smooth245212.W (q^d)
  let S : ℤ := σ 1 (p^a)
  let T : ℤ := σ 1 (q^d)
  let B : ℤ := (a:ℤ)+1
  let C : ℤ := (d:ℤ)+1
  let G : ℤ := (2:ℤ)^(k+1)-1
  let F : ℤ := 1+k*(2:ℤ)^(k+1)
  have hfg : F+G=(2:ℤ)^(k+1)*(k+1) := by dsimp [F,G];ring
  change F*W*V+G*S*T=(2:ℤ)^(k+1)*(k+1)*B*C*P*Q at bal
  rw [←hfg] at bal
  have w₁ : B*P ≤ W := by dsimp [B,P,W]; exact_mod_cast (bounds hp op a).2.2.1
  have w₂ : C*Q ≤ V := by dsimp [C,Q,V]; exact_mod_cast (bounds hq (by omega) d).2.2.1
  have ww : B*C*P*Q ≤ W*V := by
    have := mul_le_mul w₁ w₂ (by dsimp [C,Q];positivity) (by dsimp [W];positivity)
    nlinarith only [this]
  have gp : 0<G := by
    dsimp [G]; have := one_lt_pow₀ (a:=(2:ℤ)) (by norm_num) (show k+1≠0 by omega); omega
  have fg : F=(k:ℤ)*G+(k+1) := by dsimp [F,G];ring
  have low : (k:ℤ)*W*V+S*T≤((k:ℤ)+1)*B*C*P*Q := by
    have m : G*((k:ℤ)*W*V+S*T-((k:ℤ)+1)*B*C*P*Q)=
        -((k:ℤ)+1)*(W*V-B*C*P*Q) := by
      rw [fg] at bal
      linear_combination bal
    have hh : G*((k:ℤ)*W*V+S*T-((k:ℤ)+1)*B*C*P*Q) ≤ 0 :=
      m ▸ (mul_nonpos_of_nonpos_of_nonneg (by omega) (sub_nonneg.mpr ww))
    exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hh gp)
  have apply_for (f g l : ℕ) (gpos : 0<g) (fg' : k*g≤f) (sum : f+g=(k+1)*l)
      (unit : ¬q∣l) (w : (f:ℤ)*W*V+g*S*T≤(f+g)*B*C*P*Q) :
      OMA.TwoOddGlobalGap245212.defect f g p q B C ≠ 0 := by
    have hi := OMA.TwoOddGlobalGap245212.expansion f g p q B C P Q W V S T
      (moments hp a).2 (moments hq d).2 (moments hp a).1 (moments hq d).1
    have v0 := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (sq_nonneg ((p:ℤ)-1)) (sq_nonneg ((q:ℤ)-1))) (sub_nonpos.mpr w)
    rw [hi] at v0
    apply OMA.TwoOddGlobalGap245212.nonzero (B:=a+1) (C:=d+1) hq op pq (by omega) (by omega)
      hk small gpos fg' sum unit
    simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel]
    dsimp only [B,C,P,Q] at v0
    linarith only [v0]
  refine ⟨apply_for k 1 1 (by decide) (by simp) (by simp)
    (by simpa using hq.not_dvd_one) (by simpa using low),?_⟩
  let z := 2^(k+1)
  have zp : 0<z := by dsimp [z];positivity
  have zcast : (z:ℤ)=(2:ℤ)^(k+1) := by push_cast [z];rfl
  have dvz : ¬q∣z := fun bad => Nat.not_dvd_of_pos_of_lt (by decide : 0<2) (by omega)
    (hq.dvd_of_dvd_pow bad)
  have app := apply_for (1+k*z) (z-1) z (by
    dsimp [z];have := Nat.one_lt_pow (by omega : k+1≠0) (by decide : 1<2);omega)
    (by nlinarith only [Nat.mul_le_mul_left k (Nat.sub_le z 1)])
    (by have h := Nat.sub_add_cancel (by omega : 1≤z); nlinarith only [h])
    dvz (by
      push_cast [Nat.cast_sub zp,zcast]
      exact bal.le)
  simpa [Nat.cast_sub zp,zcast,F,G] using app
end OMA.ComplementaryLocal245212
end
section
namespace OMA.ComplementaryPole245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryLocal245212
open scoped ArithmeticFunction.sigma
def z (k : ℕ) : ℤ := 2^(k+1)
def G (k : ℕ) : ℤ := z k-1
def F (k : ℕ) : ℤ := 1+k*z k
theorem dyad (k : ℕ) : 0<G k ∧ 0<F k ∧ F k≤((k:ℤ)+1)*G k ∧
    F k+G k=z k*(k+1) := by
  have h : k+1<2^(k+1) := Nat.lt_pow_self (by decide)
  have h' : (k:ℤ)+1<(2:ℤ)^(k+1) := by exact_mod_cast h
  dsimp [G,F,z]
  refine ⟨by omega,by positivity,by nlinarith only [h'],by ring⟩
def den (k : ℕ) (b h P W S : ℤ) :=
  (F k+G k)*b*h*P - h*F k*W - G k*S
theorem tail {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q)
    (pq : p≠q) (a d k : ℕ)
    (eqn : OeisA245212.a (2^k*p^a*q^(d+1))=(σ 1 (2^k*p^a*q^(d+1)):ℤ)) :
    let D:=den k (a+1) (d+2) ((p:ℤ)^a) (W (p^a)) (σ 1 (p^a))
    0<D ∧ q*D≤3*(d+2)*(k+1)*(a+1)*G k*(p:ℤ)^a := by
  let P : ℤ := (p:ℤ)^a
  let Q : ℤ := (q:ℤ)^(d+1)
  let U : ℤ := (q:ℤ)^d
  let w : ℤ := W (p^a)
  let s : ℤ := σ 1 (p^a)
  let V : ℤ := W (q^d)
  let T : ℤ := σ 1 (q^d)
  let b : ℤ := (a:ℤ)+1
  let h : ℤ := (d:ℤ)+2
  let D := den k b h P w s
  change 0<D ∧ (q:ℤ)*D≤3*h*(k+1)*b*G k*P
  have qp : Q=U*q := by dsimp [Q,U];rw [pow_succ]
  have posq : (0:ℤ)<q := by omega
  have posp : (0:ℤ)<p := by omega
  have pQ : 0<Q := by dsimp [Q];positivity
  have pU : 0<U := by dsimp [U];positivity
  have pP : 0<P := by dsimp [P];positivity
  have hb : 1≤b := by dsimp [b];omega
  have hh : 2≤h := by dsimp [h];omega
  have dy := dyad k
  have bP := bounds hp op a
  have bQ := bounds hq oq d
  have w₀ : b*P≤w := by dsimp [b,P,w]; exact_mod_cast bP.2.2.1
  have wMax : 2*w≤3*b*P := by dsimp [b,P,w]; exact_mod_cast bP.2.1
  have sMax : 2*s≤3*P := by dsimp [s,P]; exact_mod_cast bP.1
  have vMax : 2*V≤3*(h-1)*U := by
    dsimp [V,h,U]; convert! (show 2*(W (q^d):ℤ)≤3*((d:ℤ)+1)*(q:ℤ)^d by exact_mod_cast bQ.2.1) using 1; ring
  have vMin : ((d:ℤ)+1)*U≤V := by dsimp [V,U]; exact_mod_cast bQ.2.2.1
  have tMax : 2*T≤3*U := by dsimp [T,U]; exact_mod_cast bQ.1
  have wPos : 0<w := (mul_pos (by omega : 0<b) pP).trans_le w₀
  have vPos : 0<V := (mul_pos (by positivity) pU).trans_le vMin
  have s0 : 0 ≤ s := by dsimp [s];positivity
  have t0 : 0≤T := by dsimp [T];positivity
  have bal := physical hp hq (by omega) (by omega) pq a (d+1) k eqn
  have ends := last hq oq d
  rw [ends.1,ends.2.1] at bal
  push_cast at bal
  have iden : D*Q=F k*w*V+G k*s*T := by
    dsimp only [D,den,b,h,w,s,V,T,P,Q]
    rw [dy.2.2.2];dsimp [F,G,z]
    linear_combination -bal
  have dPos : 0<D := pos_of_mul_pos_left (iden ▸ add_pos_of_pos_of_nonneg
    (mul_pos (mul_pos dy.2.1 wPos) vPos) (mul_nonneg (mul_nonneg dy.1.le s0) t0)) pQ.le
  refine ⟨dPos,?_⟩
  have ma := mul_le_mul wMax vMax (mul_nonneg (by decide) vPos.le)
    (mul_nonneg (mul_nonneg (by decide) (by omega : 0≤b)) pP.le)
  have mb := mul_le_mul sMax tMax (mul_nonneg (by decide) t0) (mul_nonneg (by decide) pP.le)
  have wa := mul_le_mul_of_nonneg_left ma dy.2.1.le
  have wb := mul_le_mul_of_nonneg_left mb dy.1.le
  have wc := mul_le_mul_of_nonneg_right dy.2.2.1
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by decide : (0:ℤ)≤9) (by omega : 0≤b)) pP.le)
      (by omega : 0≤h-1)) pU.le)
  have one : G k*P*U ≤ (k+1)*b*G k*P*U := by
    have kb : (1:ℤ)≤(k+1)*b := by nlinarith only [hb,mul_nonneg (by positivity : (0:ℤ)≤k) (by omega : 0≤b)]
    nlinarith only [mul_le_mul_of_nonneg_right kb (mul_nonneg (mul_nonneg dy.1.le pP.le) pU.le)]
  have grand : (q*D)*U≤(3*h*(k+1)*b*G k*P)*U := by
    rw [qp] at iden
    nlinarith only [iden,wa,wb,wc,one,
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by omega : 0≤h)
        (by positivity : (0:ℤ)≤k+1)) (by omega : 0≤b)) dy.1.le) pP.le) pU.le]
  exact (mul_le_mul_iff_left₀ pU).mp grand
private theorem integral_pole (K G F p b h P W S : ℤ)
    (gpos : 0<G) (posp : 2≤p) (beyond : p<b*(p-1)) (hpos : 2≤h) (ppos : 0<P)
    (fg : F≤K*G) (w : (p-1)^2*W=p*(b*(p-1)-1)*P+1)
    (s : (p-1)*S=p*P-1) (D : ℤ)
    (den : D=(F+G)*b*h*P-h*F*W-G*S) (plus : 0<D) :
    P≤2*G*h*K ∨ P≤2*(p-1)^2*D := by
  let u:=p-1
  let L:=G*h*b*u^2+F*h*(p-b*u)-G*p*u
  have u0 : 0<u := by dsimp [u];omega
  have iden : u^2*D=P*L-(h*F-G*u) := by
    rw [den];dsimp [L,u]
    linear_combination -h*F*w - G*(p-1)*s
  have lp : 0<L := by
    by_cases yes : G*u≤h*F
    · have prod : 0<P*L := by nlinarith only [iden,yes,mul_pos (sq_pos_of_pos u0) plus]
      exact pos_of_mul_pos_right prod ppos.le
    · have al : L=(b*u)*((h-1)*G*u)+(b*u-p)*(G*u-h*F) := by dsimp [L,u]; ring
      rw [al]
      exact add_pos_of_pos_of_nonneg (mul_pos (by dsimp [u];omega)
        (mul_pos (mul_pos (by omega) gpos) u0)) (mul_nonneg (by dsimp [u];omega) (by omega))
  by_cases cap : P≤2*G*h*K
  · exact Or.inl cap
  right
  change P≤2*u^2*D
  nlinarith only [iden,cap,mul_nonneg ppos.le (by omega : 0≤L-1),
    mul_le_mul_of_nonneg_left fg (by omega : 0≤h),mul_pos gpos u0]
theorem alternative {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q)
    (pq : p≠q) (a d k : ℕ) (a2 : 2≤a)
    (eqn : OeisA245212.a (2^k*p^a*q^(d+1))=(σ 1 (2^k*p^a*q^(d+1)):ℤ)) :
    p^a≤2*2^(k+1)*(d+2)*(k+1) ∨ q≤6*(d+2)*(k+1)*(a+1)*2^(k+1)*p^2 := by
  have tt := tail hp hq op oq pq a d k eqn
  dsimp only at tt
  let D:=den k (a+1) (d+2) ((p:ℤ)^a) (W (p^a)) (σ 1 (p^a))
  have di := dyad k
  have pp : (0:ℤ)<p := by omega
  have ma := moments hp a
  have res := integral_pole ((k:ℤ)+1) (G k) (F k) p (a+1) (d+2) (p^a)
    (W (p^a)) (σ 1 (p^a)) di.1 (by omega) (by
      nlinarith only [mul_nonneg (by omega : (0:ℤ)≤a-2) (by omega : (0:ℤ)≤p-1),
        (show (3:ℤ)≤p by exact_mod_cast op)]) (by omega) (by positivity) di.2.2.1 ma.2 ma.1 D rfl tt.1
  have gz : G k≤z k := by dsimp [G];omega
  rcases res with cap | cap
  · left
    have z := mul_le_mul_of_nonneg_right gz (by positivity : (0:ℤ)≤2*(d+2)*(k+1))
    dsimp [OMA.ComplementaryPole245212.z] at z
    exact_mod_cast (show (p:ℤ)^a≤2*2^(k+1)*(d+2)*(k+1) by nlinarith only [cap,z])
  · right
    have factor := mul_le_mul_of_nonneg_left cap (by positivity : (0:ℤ)≤q)
    have prod := mul_le_mul_of_nonneg_right tt.2 (mul_nonneg (by decide : (0:ℤ)≤2) (sq_nonneg ((p:ℤ)-1)))
    change (q:ℤ)*D*(2*(p-1)^2) ≤ 3*(d+2)*(k+1)*(a+1)*G k*(p:ℤ)^a*(2*(p-1)^2) at prod
    have comp : (q:ℤ)*(p:ℤ)^a≤(6*(d+2)*(k+1)*(a+1)*G k*(p-1)^2)*(p:ℤ)^a := by
      nlinarith only [factor,prod]
    have v := (mul_le_mul_iff_left₀ (by positivity : 0<(p:ℤ)^a)).mp comp
    have pcap : ((p:ℤ)-1)^2≤(p:ℤ)^2 := by nlinarith only [pp]
    have gcap := mul_le_mul gz pcap (sq_nonneg _) (by dsimp [z];positivity)
    have upper := mul_le_mul_of_nonneg_left gcap (by positivity : (0:ℤ)≤6*(d+2)*(k+1)*(a+1))
    dsimp [z] at upper
    exact_mod_cast (show (q:ℤ)≤6*(d+2)*(k+1)*(a+1)*2^(k+1)*p^2 by nlinarith only [v,upper])
end OMA.ComplementaryPole245212
end
section
namespace OMA.TwoOddJoint245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryPole245212 OMA.ComplementaryLocal245212
open scoped ArithmeticFunction.sigma
private theorem round {k : ℕ} {p b h P W S : ℤ} (hp : 3≤p) (hb : 3≤b) (hh : 2≤h) (hP : 0<P)
    (w : (p-1)^2*W=p*(b*(p-1)-1)*P+1) (s : (p-1)*S=p*P-1)
    (plus : 0<den k b h P W S) (small : p-1≤h*(k:ℤ))
    (joint : 2*(((k:ℤ)+1)*h*b*p*P+G k*h*(k+1))≤G k*P) :
    G k*P≤2*(p-1)^2*den k b h P W S := by
  let u:=p-1
  let L:=h*b*u^2+(k:ℤ)*h*(p-b*u)-p*u
  let D:=den k b h P W S
  change G k*P≤2*u^2*D
  have up : 0<u := by dsimp [u];omega
  have kp : (0:ℤ)<k+1 := by positivity
  have bp : 0<b*u-p := by
    dsimp [u];nlinarith only [hp,hb,mul_nonneg (show 0≤b-3 by omega) (show 0≤p-1 by omega)]
  have gp := (dyad k).1
  have fg : F k=(k:ℤ)*G k+(k+1) := by dsimp [F,G];ring
  have iden : u^2*D=P*G k*L-P*(k+1)*h*(b*u-p)-(h*F k-G k*u) := by
    dsimp [L,D,den,u];rw [fg]
    linear_combination -h*((k:ℤ)*G k+(k+1))*w-G k*(p-1)*s
  have ef : 0≤h*F k-G k*u := by
    rw [fg];nlinarith only [mul_nonneg gp.le (sub_nonneg.mpr small),mul_nonneg (by omega : 0≤h) kp.le]
  have pl : 0<(P*G k)*L := by
    nlinarith only [iden,ef,mul_pos (sq_pos_of_pos up) plus,
      mul_nonneg (mul_nonneg (mul_nonneg hP.le kp.le) (by omega : 0≤h)) bp.le]
  have lp := pos_of_mul_pos_right pl (mul_nonneg hP.le gp.le)
  have gain := mul_nonneg (mul_nonneg hP.le gp.le) (show 0≤L-1 by omega)
  have fcap := mul_le_mul_of_nonneg_left (dyad k).2.2.1 (by omega : 0≤h)
  have bu : b*u-p≤b*p := by dsimp [u];nlinarith only [hp,hb]
  have sf := mul_le_mul_of_nonneg_left bu (show (0:ℤ)≤P*(k+1)*h by positivity)
  nlinarith only [iden,gain,joint,fcap,sf,mul_nonneg gp.le up.le]
private theorem enlarge {A B G R P : ℕ} (r0 : 0<R) (rP : R≤P) (box : 2*(A*R+B)≤G*R) :
    2*(A*P+B)≤G*P := by
  have ca : 2*A≤G := (mul_le_mul_iff_left₀ r0).mp (by nlinarith only [box,Nat.zero_le B])
  obtain ⟨n,rfl⟩:=Nat.exists_eq_add_of_le rP
  nlinarith only [box,Nat.mul_le_mul_right n ca]
theorem near {p q a d k R : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (ha : 2≤a) (hd : 1≤d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ))
    (small : p-1≤(d+1)*k) (r0 : 0<R) (rP : R≤p^a)
    (box : 2*((k+1)*(d+1)*(a+1)*p*R+(2^(k+1)-1)*(d+1)*(k+1))≤(2^(k+1)-1)*R) :
    q≤6*(d+1)*(k+1)*(a+1)*p^2 := by
  obtain ⟨e,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
  let D:=den k (a+1) (e+2) ((p:ℤ)^a) (W (p^a)) (σ 1 (p^a))
  obtain ⟨plus,tail'⟩ := tail hp hq op oq pq a e k eqn
  change 0<D at plus
  have jc:=enlarge r0 rP box
  have gz : 1≤2^(k+1) := Nat.one_le_pow _ _ (by decide : 0<2)
  zify [Nat.cast_sub gz] at jc
  have joint : 2*(((k:ℤ)+1)*(e+2)*(a+1)*p*p^a+G k*(e+2)*(k+1))≤G k*(p:ℤ)^a := by
    dsimp [G,z];nlinarith only [jc]
  have sm : (p:ℤ)-1≤((e:ℤ)+2)*k := by
    zify [Nat.cast_sub hp.pos] at small;linarith only [small]
  have m:=moments hp a
  have rr:=round (show (3:ℤ)≤p by omega) (show (3:ℤ)≤a+1 by omega) (show (2:ℤ)≤e+2 by omega)
    (pow_pos (show (0:ℤ)<p by omega) a) m.2 m.1 plus sm joint
  change (q:ℤ)*D≤3*(e+2)*(k+1)*(a+1)*G k*(p:ℤ)^a at tail'
  have qk : (q:ℤ)*(G k*(p:ℤ)^a)≤(6*(e+2)*(k+1)*(a+1)*((p:ℤ)-1)^2)*(G k*(p:ℤ)^a) := by
    nlinarith only [mul_le_mul_of_nonneg_left rr (show (0:ℤ)≤q by positivity),
      mul_le_mul_of_nonneg_left tail' (mul_nonneg (show (0:ℤ)≤2 by decide) (sq_nonneg ((p:ℤ)-1)))]
  have cap := (mul_le_mul_iff_left₀ (mul_pos (dyad k).1 (pow_pos (show (0:ℤ)<p by omega) a))).mp qk
  have sq : ((p:ℤ)-1)^2≤(p:ℤ)^2 := by nlinarith only [show (3:ℤ)≤p by omega]
  exact_mod_cast cap.trans (mul_le_mul_of_nonneg_left sq (by positivity))
end OMA.TwoOddJoint245212
end
section
namespace OMA.RankTwoPoleInterior245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryPole245212 OMA.ComplementaryLocal245212
open scoped ArithmeticFunction.sigma
def L (k p b c : ℤ) := c*b*(p-1)*((p-1)-k)+(c*k-(p-1))*p
theorem point {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q)
    (pq : p≠q) (ha : 2≤a) (small : (p:ℤ)-1≤((d:ℤ)+2)*k)
    (eqn : OeisA245212.a (2^k*p^a*q^(d+1))=(σ 1 (2^k*p^a*q^(d+1)):ℤ)) :
    let b : ℤ := a+1; let c : ℤ := d+2; let u : ℤ := p-1; let K : ℤ := k+1
    0<L k p b c ∧ ∀ x y : ℤ, K*c*b*u≤x*G k → c*K≤y*(p:ℤ)^a →
      (q:ℤ)*(L k p b c-(x+y))≤3*c*K*b*u^2 := by
  dsimp only
  let b : ℤ := a+1
  let c : ℤ := d+2
  let u : ℤ := p-1
  let K : ℤ := k+1
  let P : ℤ := (p:ℤ)^a
  let D := den k b c P (W (p^a)) (σ 1 (p^a))
  have gp := (dyad k).1
  have pp : 0<P := pow_pos (by omega) _
  have up : 0<u := by dsimp [u];omega
  have cb : 0<c := by dsimp [c];positivity
  have bp : 0<b := by dsimp [b];positivity
  have kp : 0<K := by dsimp [K];positivity
  have ppos : (0:ℤ)<p := by omega
  have qpos : (0:ℤ)<q := by omega
  have bu : 0<b*u-p := by
    dsimp [b,u]
    nlinarith only [mul_nonneg (by omega : (0:ℤ)≤a-2) (by omega : (0:ℤ)≤p-1),op]
  have fg : F k=(k:ℤ)*G k+K := by dsimp [F,G,K];ring
  have cf : 0≤c*F k-G k*u := by
    change u≤c*k at small
    rw [fg]; nlinarith only [mul_nonneg gp.le (sub_nonneg.mpr small),mul_pos cb kp]
  have m := moments hp a
  have id : u^2*D=P*G k*(L k p b c)-P*K*c*(b*u-p)-(c*F k-G k*u) := by
    dsimp [D,den,L,u,b,c,P,K] at *
    rw [fg]
    linear_combination -((d:ℤ)+2)*((k:ℤ)*G k+(k+1))*m.2-G k*(p-1)*m.1
  obtain ⟨plus,tail⟩ := tail hp hq op oq pq a d k eqn
  change 0<D at plus
  change (q:ℤ)*D≤3*c*K*b*G k*P at tail
  have pl : 0<(P*G k)*(L k p b c) := by
    nlinarith only [id,cf,mul_pos (sq_pos_of_pos up) plus,
      mul_nonneg (mul_nonneg (mul_nonneg pp.le kp.le) cb.le) bu.le]
  refine ⟨pos_of_mul_pos_right pl (mul_nonneg pp.le gp.le),?_⟩
  intro x y hx hy
  have fcap := mul_le_mul_of_nonneg_left (dyad k).2.2.1 cb.le
  have room : (P*G k)*(L k p b c-(x+y))≤u^2*D := by
    nlinarith only [id,mul_le_mul_of_nonneg_left hx pp.le,mul_le_mul_of_nonneg_left hy gp.le,
      fcap,mul_nonneg gp.le up.le,mul_nonneg (mul_nonneg (mul_nonneg pp.le kp.le) cb.le) ppos.le]
  apply le_of_mul_le_mul_right (a:=P*G k) _ (mul_pos pp gp)
  nlinarith only [mul_le_mul_of_nonneg_left room qpos.le,
    mul_le_mul_of_nonneg_left tail (sq_nonneg u)]
def underSlope (l h s : ℤ) := if s<0 then h*s else l*s
def overSlope (l h s : ℤ) := if s<0 then l*s else h*s
private theorem bracket {l h x s t w : ℤ} (lo : l≤x) (hi : x≤h)
    (xp : 0≤x) (sl : s≤t) (sw : t≤w) :
    underSlope l h s≤x*t ∧ x*t≤overSlope l h w := by
  have low := mul_le_mul_of_nonneg_left sl xp
  have high := mul_le_mul_of_nonneg_left sw xp
  constructor
  · unfold underSlope; split
    · exact (mul_le_mul_of_nonpos_right hi (by omega)).trans low
    · exact (mul_le_mul_of_nonneg_right lo (by omega)).trans low
  · unfold overSlope; split
    · exact high.trans (mul_le_mul_of_nonpos_right lo (by omega))
    · exact high.trans (mul_le_mul_of_nonneg_right hi (by omega))
def lowPole (kl kh bl bh cl ch p r : ℤ) :=
  underSlope (cl*bl*(p-1)) (ch*bh*(r-1)) (p-1-kh)+max 0 (cl*kl-(r-1))*p
def highPole (kl kh bl bh cl ch p r : ℤ) :=
  overSlope (cl*bl*(p-1)) (ch*bh*(r-1)) (r-1-kl)+(ch*kh-(p-1))*r
theorem pole_interval {kl kh bl bh cl ch pl ph k p b c : ℤ}
    (k0 : 0≤kl) (b0 : 0≤bl) (c0 : 0≤cl) (p0 : 1≤pl)
    (kl' : kl≤k) (kh' : k≤kh) (bl' : bl≤b) (bh' : b≤bh)
    (cl' : cl≤c) (ch' : c≤ch) (pl' : pl≤p) (ph' : p≤ph)
    (small : p-1≤c*k) :
    lowPole kl kh bl bh cl ch pl ph≤L k p b c ∧ L k p b c≤highPole kl kh bl bh cl ch pl ph := by
  have pp : 0≤p := by omega
  have up : 0≤p-1 := by omega
  have bp : 0≤b := by omega
  have cp : 0≤c := by omega
  have bh0 : 0≤bh := by omega
  have ch0 : 0≤ch := by omega
  have kk : 0≤k := by omega
  have blim : cl*bl*(pl-1)≤c*b*(p-1) := by gcongr
  have bhim : c*b*(p-1)≤ch*bh*(ph-1) := by gcongr
  have first := bracket blim bhim (by positivity : 0≤c*b*(p-1))
    (show pl-1-kh≤p-1-k by omega) (show p-1-k≤ph-1-kl by omega)
  have a : cl*kl≤c*k := by gcongr
  have z : c*k≤ch*kh := by gcongr
  have e : max 0 (cl*kl-(ph-1))≤c*k-(p-1) := max_le (by omega) (by omega)
  have f : c*k-(p-1)≤ch*kh-(pl-1) := by omega
  have lower := mul_le_mul e pl' (by omega : 0≤pl) (by omega : 0≤c*k-(p-1))
  have upper := mul_le_mul f ph' pp (by omega : 0≤ch*kh-(pl-1))
  exact ⟨add_le_add first.1 lower,add_le_add first.2 upper⟩
end OMA.RankTwoPoleInterior245212
end
section
namespace OMA.SimultaneousBound245212
open OMA.TwoOddGlobalGap245212 OMA.ComplementaryPole245212 OMA.ComplementaryLocal245212
open OMA.Smooth245212 ArithmeticFunction
open scoped ArithmeticFunction.sigma
def error (p q K B C P Q : ℕ) :=
  q^2*(K*C+p)*Q+p^2*(K*B+q)*P+K+p*q
private theorem alpha_bound {f g p q C K : ℤ} (hp : 2≤p) (hq : 2≤q) (hc : 1≤C)
    (fg : f≤K*g) (f0 : 0≤f) (g0 : 0≤g) (k0 : 0≤K) :
    |alpha f g p q C|≤g*q^2*(K*C+p) := by
  have vp : 0≤q-1 := by omega
  have up : 0≤p-1 := by omega
  have pos : 0≤C*(q-1)-1 := by
    nlinarith only [mul_nonneg (show 0≤C-1 by omega) vp,hq]
  have top : C*(q-1)-1≤C*q := by nlinarith only [hc]
  have down : (p-1)*(q-1)≤p*q := by nlinarith only [hp,hq]
  have fterm := mul_le_mul fg top pos (mul_nonneg k0 g0)
  have gterm := mul_le_mul_of_nonneg_left down g0
  dsimp [alpha]
  apply abs_le.mpr
  constructor
  · nlinarith only [mul_le_mul_of_nonneg_left gterm (show 0≤q by omega),
      mul_nonneg (mul_nonneg (show 0≤q by omega) f0) pos,
      mul_nonneg (mul_nonneg g0 (sq_nonneg q)) (mul_nonneg k0 (show 0≤C by omega))]
  · nlinarith only [mul_le_mul_of_nonneg_left fterm (show 0≤q by omega),
      mul_nonneg (mul_nonneg (mul_nonneg g0 up) vp) (show 0≤q by omega),
      mul_nonneg (mul_nonneg g0 (sq_nonneg q)) (show 0≤p by omega)]
private theorem abs_terms {f g p q B C P Q K : ℤ} (hp : 2≤p) (hq : 2≤q) (hb : 1≤B)
    (hc : 1≤C) (fg : f≤K*g) (f0 : 0≤f) (g0 : 0≤g) (k0 : 0≤K) (p0 : 0≤P) (q0 : 0≤Q) :
    |alpha f g p q C*Q+beta f g p q B*P+f+g*(p-1)*(q-1)| ≤
    g*(q^2*(K*C+p)*Q+p^2*(K*B+q)*P+K+p*q) := by
  have ab := alpha_bound hp hq hc fg f0 g0 k0
  have ba := alpha_bound hq hp hb fg f0 g0 k0
  have sym : alpha f g q p B=beta f g p q B := by dsimp [alpha,beta];ring
  rw [sym] at ba
  have uv : g*(p-1)*(q-1)≤g*(p*q) := by
    have h : (p-1)*(q-1)≤p*q := by nlinarith only [hp,hq]
    nlinarith only [mul_le_mul_of_nonneg_left h g0]
  have s : 0≤g*(p-1)*(q-1) := mul_nonneg (mul_nonneg g0 (by omega)) (by omega)
  calc
    _ ≤ (|alpha f g p q C*Q|+|beta f g p q B*P|)+|f|+|g*(p-1)*(q-1)| := by
      have t1 := abs_add_le (alpha f g p q C*Q) (beta f g p q B*P)
      have t2 := abs_add_le (alpha f g p q C*Q+beta f g p q B*P) f
      have t3 := abs_add_le (alpha f g p q C*Q+beta f g p q B*P+f) (g*(p-1)*(q-1))
      linarith only [t1,t2,t3]
    _ ≤ _ := by
      rw [abs_mul,abs_of_nonneg q0,abs_mul,abs_of_nonneg p0,abs_of_nonneg f0,abs_of_nonneg s]
      nlinarith only [mul_le_mul_of_nonneg_right ab q0,mul_le_mul_of_nonneg_right ba p0,fg,uv]
theorem of_separations {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q)
    (pq : p≠q) (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ))
    (s1 : defect k 1 p q (a+1) (d+1) ≠ 0)
    (s2 : defect (F k) (G k) p q (a+1) (d+1) ≠ 0) :
    let K:=k+1; let B:=a+1; let C:=d+1; let gn:=2^K-1; let P:=p^a; let Q:=q^d
    P*Q ≤ gn*error p q K B C P Q ∧
    4*gn*P*Q ≤ 4*gn*error p q K B C P Q + 9*K*p^2*q^2*B*C*P*Q := by
  let K:ℤ:=k+1
  let B:ℤ:=a+1
  let C:ℤ:=d+1
  let W : ℤ:=OMA.Smooth245212.W (p^a)
  let V : ℤ:=OMA.Smooth245212.W (q^d)
  let S : ℤ:=σ 1 (p^a)
  let T : ℤ:=σ 1 (q^d)
  let P : ℤ:=(p:ℤ)^a
  let Q : ℤ:=(q:ℤ)^d
  let err := (q:ℤ)^2*(K*C+p)*Q+(p:ℤ)^2*(K*B+q)*P+K+p*q
  let terms (f g : ℤ) := alpha f g p q C*Q+beta f g p q B*P+f+g*(p-1)*(q-1)
  have gp := (dyad k).1
  have fp := (dyad k).2.1
  have zz := (dyad k).2.2.2
  have op' : (3:ℤ)≤p := by omega
  have oq' : (3:ℤ)≤q := by omega
  have pp : 0<P := by dsimp [P];positivity
  have qq : 0<Q := by dsimp [Q];positivity
  have phys := physical hp hq (by omega) (by omega) pq a d k eqn
  change F k*W*V+G k*S*T=z k*(k+1)*B*C*P*Q at phys
  rw [←zz] at phys
  have bound (f g : ℤ) (fg : f≤K*g) (f0 : 0≤f) (g0 : 0≤g) : |terms f g|≤g*err :=
    abs_terms (by omega) (by omega) (by dsimp [B];omega) (by dsimp [C];omega)
      fg f0 g0 (by dsimp [K];omega) pp.le qq.le
  have iden (f g : ℤ) :
      (p-1:ℤ)^2*(q-1:ℤ)^2*(f*W*V+g*S*T-(f+g)*B*C*P*Q) =
      -defect f g p q B C*P*Q+terms f g := by
    simpa only [terms,add_assoc] using expansion f g p q B C P Q W V S T
      (moments hp a).2 (moments hq d).2 (moments hp a).1 (moments hq d).1
  have l := iden (F k) (G k)
  rw [phys,sub_self,mul_zero] at l
  have l' : defect (F k) (G k) p q B C*P*Q=terms (F k) (G k) := by linarith only [l]
  have mag (e : ℤ) (ne : e≠0) : P*Q≤|e*P*Q| := by
    rw [abs_mul,abs_mul,abs_of_pos pp,abs_of_pos qq]
    nlinarith only [mul_nonneg (show 0≤|e|-1 by have := abs_pos.mpr ne;omega) (mul_pos pp qq).le]
  have lhs := mag _ s2
  change P*Q≤|defect (F k) (G k) p q B C*P*Q| at lhs
  rw [l'] at lhs
  have lfinal := lhs.trans (bound _ _ (dyad k).2.2.1 fp.le gp.le)
  have km := iden k 1
  let U : ℤ := (p-1:ℤ)^2*(q-1:ℤ)^2
  have fg : F k=(k:ℤ)*G k+K := by dsimp [K,F,G,z]; ring
  have rel : G k*((k:ℤ)*W*V+S*T-(k+1)*B*C*P*Q) = -K*(W*V-B*C*P*Q) := by
    rw [fg] at phys; dsimp [K] at phys ⊢;linear_combination phys
  have k' : G k*(defect k 1 p q B C*P*Q)=G k*terms k 1+K*U*(W*V-B*C*P*Q) := by
    simp only [one_mul] at km
    dsimp only [U]
    linear_combination (G k)*km - ((p:ℤ)-1)^2*((q:ℤ)-1)^2*rel
  have bp := bounds hp op a
  have bq := bounds hq oq d
  have wmin : B*P≤W := by dsimp [B,P,W];exact_mod_cast bp.2.2.1
  have vmin : C*Q≤V := by dsimp [C,Q,V];exact_mod_cast bq.2.2.1
  have wmax : 2*W≤3*B*P := by dsimp [B,P,W];exact_mod_cast bp.2.1
  have vmax : 2*V≤3*C*Q := by dsimp [C,Q,V];exact_mod_cast bq.2.1
  have w0 : 0≤W := by dsimp [W];positivity
  have v0 : 0≤V := by dsimp [V];positivity
  have bpos : 0<B := by dsimp [B];positivity
  have cpos : 0<C := by dsimp [C];positivity
  have rmin : 0≤W*V-B*C*P*Q := by
    nlinarith only [mul_le_mul wmin vmin (mul_pos cpos qq).le w0]
  have rmax : 4*(W*V-B*C*P*Q)≤9*B*C*P*Q := by
    have lim := mul_le_mul wmax vmax (show 0≤2*V by positivity) (show 0≤3*B*P by positivity)
    nlinarith only [lim,mul_nonneg (mul_nonneg (mul_nonneg bpos.le cpos.le) pp.le) qq.le]
  have u0 : 0≤U := by dsimp [U];positivity
  have uc : U≤(p:ℤ)^2*q^2 := mul_le_mul
    (show ((p:ℤ)-1)^2≤(p:ℤ)^2 by nlinarith only [op'])
    (show ((q:ℤ)-1)^2≤(q:ℤ)^2 by nlinarith only [oq']) (sq_nonneg _) (sq_nonneg _)
  have kp : 0<K := by dsimp [K];positivity
  have product := mul_le_mul uc rmax (mul_nonneg (show (0:ℤ)≤4 by decide) rmin)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have dmag := mul_le_mul_of_nonneg_left (mag _ s1) gp.le
  change G k*(P*Q)≤G k*|defect k 1 p q B C*P*Q| at dmag
  rw [←abs_of_pos gp,←abs_mul,k',abs_of_pos gp] at dmag
  have triangle := abs_add_le (G k*terms k 1) (K*U*(W*V-B*C*P*Q))
  have target := dmag.trans triangle
  rw [abs_mul,abs_of_pos gp,abs_of_nonneg (mul_nonneg (mul_nonneg kp.le u0) rmin)] at target
  have tb := bound k 1 (by dsimp [K];omega) (by positivity) (by decide)
  have final : 4*G k*P*Q≤4*G k*err+9*K*(p:ℤ)^2*q^2*B*C*P*Q := by
    nlinarith only [target,mul_le_mul_of_nonneg_left tb gp.le,mul_le_mul_of_nonneg_left product kp.le]
  have gcast : ((2^(k+1)-1:ℕ):ℤ)=G k := by
    dsimp [G,z];push_cast [Nat.cast_sub (Nat.one_le_pow _ _ (by decide : 0<2))];rfl
  dsimp only [error]
  constructor
  · zify;rw [gcast];exact lfinal
  · zify;rw [gcast];exact final
theorem original {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (pq : p<q) (ha : 1≤a) (hd : 15≤d) (hk : 2≤k) (small : p≤5*(k+1))
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    let K:=k+1; let B:=a+1; let C:=d+1; let gn:=2^K-1; let P:=p^a; let Q:=q^d
    P*Q ≤ gn*error p q K B C P Q ∧
    4*gn*P*Q ≤ 4*gn*error p q K B C P Q + 9*K*p^2*q^2*B*C*P*Q := by
  obtain ⟨a,b⟩ := original_separations hp hq op pq ha hd hk small eqn
  exact of_separations hp hq op (by omega) pq.ne eqn a b
end OMA.SimultaneousBound245212
end
section
namespace OMA.RankTwoInteriorBox245212
open OMA.RankTwoPoleInterior245212 OMA.ComplementaryPole245212
open ArithmeticFunction OMA.SimultaneousBound245212
open scoped ArithmeticFunction.sigma
theorem no_exact {A B C P Q G : ℕ} (pp : 0<P) (qp : 0<Q)
    (necessary : P*Q≤G*(A*Q+B*P+C)) (a : 3*G*A<P) (b : 3*G*B<Q)
    (c : 3*G*C<P*Q) : False := by
  nlinarith only [necessary,Nat.mul_lt_mul_of_pos_right a qp,Nat.mul_lt_mul_of_pos_right b pp,c]
theorem no_integer {A B C P Q G F : ℕ} (pp : 0<P) (qp : 0<Q) (gp : 0<G)
    (necessary : 4*G*P*Q≤4*G*(A*Q+B*P+C)+F*P*Q)
    (a : 4*A<P) (b : 4*B<Q) (c : 4*C<P*Q) (drift : F<G) : False := by
  have three : 4*(A*Q+B*P+C)<3*P*Q := by
    nlinarith only [Nat.mul_lt_mul_of_pos_right a qp,Nat.mul_lt_mul_of_pos_right b pp,c]
  nlinarith only [necessary,Nat.mul_lt_mul_of_pos_left three gp,
    Nat.mul_lt_mul_of_pos_right drift (Nat.mul_pos pp qp)]
structure Cell where
  kl : ℕ
  kh : ℕ
  bl : ℕ
  bh : ℕ
  cl : ℕ
  ch : ℕ
  pl : ℕ
  ph : ℕ
  deriving Repr
def Fits (t : Cell) (K B C p : ℕ) : Prop :=
  t.kl≤K ∧ K≤t.kh ∧ t.bl≤B ∧ B≤t.bh ∧ t.cl≤C ∧ C≤t.ch ∧ t.pl≤p ∧ p≤t.ph
def gLow (t : Cell) := 2^t.kl-1
def gHigh (t : Cell) := 2^t.kh-1
def pLow (t : Cell) := t.pl^(t.bl-1)
def qLow (t : Cell) := (t.pl+2)^(t.cl-1)
def low (t : Cell) := lowPole ((t.kl:ℤ)-1) ((t.kh:ℤ)-1) t.bl t.bh t.cl t.ch t.pl t.ph
def high (t : Cell) := highPole ((t.kl:ℤ)-1) ((t.kh:ℤ)-1) t.bl t.bh t.cl t.ch t.pl t.ph
def e₁ (t : Cell) := (t.kh*t.ch*t.bh*(t.ph-1)+gLow t-1)/gLow t
def e₂ (t : Cell) := (t.ch*t.kh+pLow t-1)/pLow t
def gap (t : Cell) : ℤ := low t-e₁ t-e₂ t
def numerator (t : Cell) := 3*t.ch*t.bh*t.kh*(t.ph-1)^2
def yCap (t : Cell) := numerator t/(gap t).toNat
def witness (t : Cell) : Bool := decide (
  t.kh*t.ch*t.bh*(t.ph-1)≤e₁ t*gLow t ∧ t.ch*t.kh≤e₂ t*pLow t ∧
  0<gap t ∧ numerator t<(yCap t+1)*(gap t).toNat)
def budget (t : Cell) (y : ℕ) : Bool :=
  let x := y^2*(t.kh*t.ch+t.ph)
  let z := t.ph^2*(t.kh*t.bh+y)
  let w := t.kh+t.ph*y
  let P := pLow t
  let Q := qLow t
  let G := gHigh t
  decide (3*G*x<P ∧ 3*G*z<Q ∧ 3*G*w<P*Q) ||
    decide (4*x<P ∧ 4*z<Q ∧ 4*w<P*Q ∧ 9*t.kh*t.ph^2*y^2*t.bh*t.ch<gLow t)
def veto (t : Cell) : Bool :=
  decide (high t≤0) || (witness t && (decide (yCap t<t.pl+2) || budget t (yCap t)))
theorem budget_false {t : Cell} {p q K B C P Q G y : ℕ}
    (fit : Fits t K B C p) (qy : q≤y)
    (pp : 0<P) (qp : 0<Q) (gp : 0<G)
    (rp : pLow t≤P) (rq : qLow t≤Q) (gl : gLow t≤G) (gh : G≤gHigh t)
    (ex : P*Q≤G*error p q K B C P Q)
    (int : 4*G*P*Q≤4*G*error p q K B C P Q+9*K*p^2*q^2*B*C*P*Q) :
    budget t y=false := by
  obtain ⟨_,kh,_,bh,_,ch,_,ph⟩ := fit
  have ae : q^2*(K*C+p)≤y^2*(t.kh*t.ch+t.ph) := by gcongr
  have be : p^2*(K*B+q)≤t.ph^2*(t.kh*t.bh+y) := by gcongr
  have ce : K+p*q≤t.kh+t.ph*y := by gcongr
  have de : 9*K*p^2*q^2*B*C≤9*t.kh*t.ph^2*y^2*t.bh*t.ch := by gcongr
  have prod := Nat.mul_le_mul rp rq
  by_contra! bad
  have ok : budget t y=true := Bool.eq_true_of_not_eq_false bad
  simp only [budget,Bool.or_eq_true,decide_eq_true_eq] at ok
  rcases ok with ⟨a,b,c⟩ | ⟨a,b,c,d⟩
  · apply no_exact pp qp (by simpa [error,add_assoc] using ex)
    · exact (Nat.mul_le_mul (Nat.mul_le_mul_left _ gh) ae).trans_lt (a.trans_le rp)
    · exact (Nat.mul_le_mul (Nat.mul_le_mul_left _ gh) be).trans_lt (b.trans_le rq)
    · exact (Nat.mul_le_mul (Nat.mul_le_mul_left _ gh) ce).trans_lt (c.trans_le prod)
  · apply no_integer pp qp gp (by simpa [error,add_assoc] using int)
    · exact (Nat.mul_le_mul_left _ ae).trans_lt (a.trans_le rp)
    · exact (Nat.mul_le_mul_left _ be).trans_lt (b.trans_le rq)
    · exact (Nat.mul_le_mul_left _ ce).trans_lt (c.trans_le prod)
    · exact de.trans_lt (d.trans_le gl)
theorem veto_false {t : Cell} {p q a d k : ℕ}
    (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (pq : p+2≤q) (ha : 2≤a)
    (kl : 1≤t.kl) (pl : 1≤t.pl) (fit : Fits t (k+1) (a+1) (d+2) p)
    (small : (p:ℤ)-1≤((d:ℤ)+2)*k)
    (eqn : OeisA245212.a (2^k*p^a*q^(d+1))=(σ 1 (2^k*p^a*q^(d+1)):ℤ))
    (ex : p^a*q^(d+1)≤(2^(k+1)-1)*error p q (k+1) (a+1) (d+2) (p^a) (q^(d+1)))
    (int : 4*(2^(k+1)-1)*p^a*q^(d+1)≤4*(2^(k+1)-1)*error p q (k+1) (a+1) (d+2) (p^a) (q^(d+1))+
      9*(k+1)*p^2*q^2*(a+1)*(d+2)*p^a*q^(d+1)) : veto t=false := by
  obtain ⟨k₀,k₁,b₀,b₁,c₀,c₁,p₀,p₁⟩ := fit
  have qpos := hq.pos
  have ppos := hp.pos
  have rp : pLow t≤p^a := by
    exact (Nat.pow_le_pow_left p₀ _).trans (Nat.pow_le_pow_right hp.pos (by omega))
  have rq : qLow t≤q^(d+1) := by
    exact (Nat.pow_le_pow_left (by omega : t.pl+2≤q) _).trans
      (Nat.pow_le_pow_right hq.pos (by omega))
  have gl : gLow t≤2^(k+1)-1 :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) k₀) 1
  have gh : 2^(k+1)-1≤gHigh t :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) k₁) 1
  have pow2 : 2≤2^(k+1) := by simpa only [pow_one] using
    (Nat.pow_le_pow_right (by decide : 0<2) (by omega : 1≤k+1))
  have pole := point hp hq op (by omega) (by omega) ha small eqn
  dsimp only at pole
  have lim := pole_interval (p:=p) (b:=(a:ℤ)+1) (c:=(d:ℤ)+2) (k:=k)
    (kl:=(t.kl:ℤ)-1) (kh:=(t.kh:ℤ)-1) (bl:=t.bl) (bh:=t.bh) (cl:=t.cl)
    (ch:=t.ch) (pl:=t.pl) (ph:=t.ph)
    (by omega) (Int.natCast_nonneg _) (Int.natCast_nonneg _) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) small
  change low t≤L k p (a+1) (d+2) ∧ L k p (a+1) (d+2)≤high t at lim
  have pos := pole.1.trans_le lim.2
  by_cases test : witness t=true
  · have pieces := test
    simp only [witness,decide_eq_true_eq] at pieces
    obtain ⟨ex₁,ex₂,gapp,cover⟩ := pieces
    have xu : (k+1)*(d+2)*(a+1)*(p-1)≤e₁ t*(2^(k+1)-1) := calc
      _ ≤ t.kh*t.ch*t.bh*(t.ph-1) := by gcongr
      _ ≤ _ := ex₁.trans (Nat.mul_le_mul_left _ gl)
    have yu : (d+2)*(k+1)≤e₂ t*p^a :=
      (Nat.mul_le_mul c₁ k₁).trans (ex₂.trans (Nat.mul_le_mul_left _ rp))
    zify [Nat.cast_sub hp.pos,Nat.cast_sub (by omega : 1≤2^(k+1))] at xu
    have bound := pole.2 (e₁ t) (e₂ t) (by simpa [G,z,mul_assoc] using xu)
      (by exact_mod_cast yu)
    have gp : gap t≤L k p (a+1) (d+2)-(e₁ t+e₂ t) := by
      dsimp [gap];linarith only [lim.1]
    have num : 3*(d+2)*(k+1)*(a+1)*(p-1)^2≤numerator t := by
      unfold numerator
      rw [show 3*t.ch*t.bh*t.kh=3*t.ch*t.kh*t.bh by ring]
      gcongr
    zify [Nat.cast_sub hp.pos] at num
    have l : (q:ℤ)*gap t≤numerator t :=
      (mul_le_mul_of_nonneg_left gp (Int.natCast_nonneg q)).trans (bound.trans num)
    have yi : q≤yCap t := by
      have val : (((gap t).toNat:ℕ):ℤ)=gap t := Int.toNat_of_nonneg gapp.le
      rw [←val] at l
      have qg : q*(gap t).toNat≤numerator t := by exact_mod_cast l
      by_contra! bad
      exact (not_lt_of_ge (Nat.mul_le_mul_right _ (by omega : yCap t+1≤q))) (qg.trans_lt cover)
    have order : ¬yCap t<t.pl+2 := by omega
    have b := budget_false ⟨k₀,k₁,b₀,b₁,c₀,c₁,p₀,p₁⟩ yi (pow_pos ppos _) (pow_pos qpos _)
      (by omega : 0<2^(k+1)-1) rp rq gl gh ex int
    simp [veto,not_le_of_gt pos,test,order,b]
  · simp [veto,not_le_of_gt pos,Bool.eq_false_of_not_eq_true test]
end OMA.RankTwoInteriorBox245212
end
section
namespace OMA.OddBox245212
noncomputable def logSize (x : ℝ) := 16*Real.logb 2 x
def down (n : ℕ) : ℤ := Nat.log 2 (n^16)
def up (n : ℕ) : ℤ := Nat.clog 2 (n^16)
def roundedQuot (n : ℤ) (d : ℕ) := -((-n)/(d:ℤ))
theorem mono {x y : ℝ} (hx : 0<x) (xy : x≤y) : logSize x≤logSize y :=
  mul_le_mul_of_nonneg_left (Real.logb_le_logb_of_le (by norm_num) hx xy) (by norm_num)
theorem reflect {x y : ℝ} (hx : 0<x) (hy : 0<y) : logSize x≤logSize y ↔ x≤y := by
  unfold logSize; rw [mul_le_mul_iff_right₀ (by norm_num : (0:ℝ)<16)]
  exact Real.logb_le_logb (by norm_num) hx hy
theorem enclosed (n : ℕ) (pos : 0<n) : (down n:ℝ)≤logSize n ∧ logSize n≤up n := by
  have x : 0≤Real.logb 2 ((n:ℝ)^16) :=
    Real.logb_nonneg (by norm_num) (one_le_pow₀ (by exact_mod_cast pos : (1:ℝ)≤n))
  have fid := Nat.floor_le x
  have cid := Nat.le_ceil (Real.logb 2 ((n:ℝ)^16))
  have fn := Real.natFloor_logb_natCast 2 (n^16)
  have cn := Real.natCeil_logb_natCast 2 (n^16)
  norm_num only [Nat.cast_ofNat,Nat.cast_pow] at fn cn
  rw [fn] at fid
  rw [cn] at cid
  dsimp [down,up,logSize]
  push_cast at fid cid ⊢
  rw [Real.logb_pow] at fid cid
  norm_num at fid cid
  exact ⟨fid,cid⟩
theorem mul {x y : ℝ} (hx : 0<x) (hy : 0<y) : logSize (x*y)=logSize x+logSize y := by
  simp only [logSize,Real.logb_mul hx.ne' hy.ne',mul_add]
theorem pow (x : ℝ) (n : ℕ) : logSize (x^n)=n*logSize x := by
  simp only [logSize,Real.logb_pow];ring
@[simp] theorem two : logSize 2=16 := by norm_num [logSize,Real.logb_self_eq_one]
@[simp] theorem one : logSize 1=0 := by simp [logSize]
theorem nat_nonneg (n : ℕ) (hn : 0<n) : 0≤logSize n := by
  simpa using mono (by norm_num : (0:ℝ)<1) (show (1:ℝ)≤n by exact_mod_cast hn)
theorem over_bound {x : ℝ} {a : ℤ} {d : ℕ} (hd : 0<d) (h : (d:ℝ)*x≤a) : x≤roundedQuot a d := by
  have pos : (0:ℤ)<d := by exact_mod_cast hd
  have cut := Int.ediv_mul_le (-a) pos.ne'
  have z : a≤d*roundedQuot a d := by dsimp [roundedQuot];nlinarith only [cut]
  have lift : (a:ℝ)≤(d:ℝ)*(roundedQuot a d:ℝ) := by exact_mod_cast z
  exact (mul_le_mul_iff_right₀ (show (0:ℝ)<d by exact_mod_cast hd)).mp (h.trans lift)
theorem max_sum {x y : ℝ} (hx : 0<x) (hy : 0<y) :
    logSize (x+y)≤16+max (logSize x) (logSize y) := by
  rcases le_total x y with h|h
  · rw [max_eq_right (mono hx h),←two,←mul (by norm_num) hy]
    exact mono (by positivity) (by linarith)
  · rw [max_eq_left (mono hy h),←two,←mul (by norm_num) hx]
    exact mono (by positivity) (by linarith)
end OMA.OddBox245212
end
section
namespace OMA.OddBox245212
def lowPrime (kl bl pl : ℕ) :=
  let l := max 13 (max pl (1+(kl-1)*(bl-1)/bl))
  l+(1-l%2)
def highPrime (kh ph : ℕ) := min ph (1+9*kh/4)
def compVeto (kl kh bl bh ch : ℕ) (x y : ℤ) : Bool :=
  let fst := up (2*ch*bh*kh)+2*x+(ch-1:ℕ)*y
  let snd := up (6*ch^2*bh)+16+max (up kh) x+2*(ch-1:ℕ)*y
  decide (2*ch+3≤bl ∧ max 0 (max fst snd)+up 3<16*(kl:ℤ))
structure Frame where
  kl : ℕ
  kh : ℕ
  bl : ℕ
  bh : ℕ
  cl : ℕ
  ch : ℕ
  lo : ℕ
  hi : ℕ
namespace Frame
def qlo (f : Frame) := f.lo+2
def xp (f : Frame) := (f.bl-1:ℕ)*down f.lo
def yq (f : Frame) := (f.cl-1:ℕ)*down f.qlo
def dz (f : Frame) : ℤ := 16*f.kh
def dg (f : Frame) : ℤ := 16*(f.kl-1:ℕ)
def cap (f : Frame) := f.dz+up (3*f.kh*f.bh)
def capY (f : Frame) := f.cap+(f.bh-1:ℕ)*up f.hi
def residue (f : Frame) := up (6*f.ch*f.bh*f.kh*f.hi^2)
def y (f : Frame) : ℤ :=
  let upper := roundedQuot f.capY (f.cl-2)
  let near := if f.dz+up (2*f.ch*f.kh)≤f.xp then min upper (f.dz+f.residue) else upper
  if max (up (f.ch*f.kh*f.bh*f.hi)-f.dg) (up (f.ch*f.kh)-f.xp)≤ -32 then
    min near f.residue else near
def normalized (f : Frame) := min (roundedQuot (2*f.cap-(f.cl-4:ℕ)*f.xp) (f.cl-2)) (2*f.y-f.xp)
def e1 (f : Frame) := up (f.kh*f.ch+f.hi)+f.normalized
def e2 (f : Frame) := 2*up f.hi+up (f.kh*f.bh+f.qlo)-f.yq
def e3 (f : Frame) := up (f.kh+f.hi*f.qlo)-f.xp-f.yq
def largest (f : Frame) := max f.e1 (max f.e2 f.e3)
def drift (f : Frame) := up (3*f.kh*f.bh*f.ch)+2*up f.hi+2*f.y-f.dg
def reject (f : Frame) : Bool :=
  decide (f.hi<f.lo ∨ f.capY<(f.cl-2:ℕ)*down f.qlo ∨
    f.cap<((f.cl:ℤ)-f.bh-1)*down f.qlo ∨ f.y<down f.qlo ∨
    f.dz+up (3*f.kh*f.ch)+(f.ch-1:ℕ)*f.y<(f.bl-2:ℕ)*down f.lo ∨
    up (3*f.bh*f.ch)+(f.bh-1:ℕ)*up f.hi+(f.ch-1:ℕ)*f.y<16*(f.kl:ℤ) ∨
    f.largest+up 3+f.dz<0 ∨ max f.largest f.drift+32<0) ||
    compVeto f.kl f.kh f.bl f.bh f.ch (up f.hi) f.y ||
    compVeto f.kl f.kh f.cl f.ch f.bh f.y (up f.hi)
end Frame
def veto (kl kh bl bh cl ch pl ph : ℕ) : Bool :=
  if 6≤kl ∧ 6≤bl ∧ 6≤cl then
    Frame.reject ⟨kl,kh,bl,bh,cl,ch,lowPrime kl bl pl,highPrime kh ph⟩
  else false
end OMA.OddBox245212
end
section
namespace OMA.OddBox245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryLocal245212
open scoped ArithmeticFunction.sigma
theorem separations {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (pq : p<q) {a d k : ℕ} (ha : 1≤a) (hd : 1≤d) (hk : 2≤k) (small : (p:ℤ)-1<(k:ℤ)*d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    OMA.TwoOddGlobalGap245212.defect k 1 p q (a+1) (d+1)≠0 ∧
    OMA.TwoOddGlobalGap245212.defect (1+k*(2:ℤ)^(k+1)) ((2:ℤ)^(k+1)-1) p q (a+1) (d+1)≠0 := by
  have bal := physical hp hq (by omega) (by omega) pq.ne a d k eqn
  let P : ℤ := (p:ℤ)^a
  let Q : ℤ := (q:ℤ)^d
  let W : ℤ := OMA.Smooth245212.W (p^a)
  let V : ℤ := OMA.Smooth245212.W (q^d)
  let S : ℤ := σ 1 (p^a)
  let T : ℤ := σ 1 (q^d)
  let B : ℤ := (a:ℤ)+1
  let C : ℤ := (d:ℤ)+1
  let G : ℤ := (2:ℤ)^(k+1)-1
  let F : ℤ := 1+k*(2:ℤ)^(k+1)
  have hfg : F+G=(2:ℤ)^(k+1)*(k+1) := by dsimp [F,G];ring
  change F*W*V+G*S*T=(2:ℤ)^(k+1)*(k+1)*B*C*P*Q at bal
  rw [←hfg] at bal
  have w₁ : B*P ≤ W := by dsimp [B,P,W]; exact_mod_cast (bounds hp op a).2.2.1
  have w₂ : C*Q ≤ V := by dsimp [C,Q,V]; exact_mod_cast (bounds hq (by omega) d).2.2.1
  have ww : B*C*P*Q ≤ W*V := by
    have := mul_le_mul w₁ w₂ (by dsimp [C,Q];positivity) (by dsimp [W];positivity)
    nlinarith only [this]
  have gp : 0<G := by
    dsimp [G]; have := one_lt_pow₀ (a:=(2:ℤ)) (by norm_num) (show k+1≠0 by omega); omega
  have fg : F=(k:ℤ)*G+(k+1) := by dsimp [F,G];ring
  have low : (k:ℤ)*W*V+S*T≤((k:ℤ)+1)*B*C*P*Q := by
    have m : G*((k:ℤ)*W*V+S*T-((k:ℤ)+1)*B*C*P*Q)=
        -((k:ℤ)+1)*(W*V-B*C*P*Q) := by
      rw [fg] at bal
      linear_combination bal
    have hh : G*((k:ℤ)*W*V+S*T-((k:ℤ)+1)*B*C*P*Q) ≤ 0 :=
      m ▸ (mul_nonpos_of_nonpos_of_nonneg (by omega) (sub_nonneg.mpr ww))
    exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hh gp)
  have apply_for (f g l : ℕ) (gpos : 0<g) (fg' : k*g≤f) (sum : f+g=(k+1)*l)
      (unit : ¬q∣l) (w : (f:ℤ)*W*V+g*S*T≤(f+g)*B*C*P*Q) :
      OMA.TwoOddGlobalGap245212.defect f g p q B C ≠ 0 := by
    have hi := OMA.TwoOddGlobalGap245212.expansion f g p q B C P Q W V S T
      (moments hp a).2 (moments hq d).2 (moments hp a).1 (moments hq d).1
    have v0 := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (sq_nonneg ((p:ℤ)-1)) (sq_nonneg ((q:ℤ)-1))) (sub_nonpos.mpr w)
    rw [hi] at v0
    apply OMA.TwoOddGlobalGap245212.nonzero_of_positive_alpha (B:=a+1) (C:=d+1) hq op pq (by omega) (by omega)
      hk (by simpa using small) gpos fg' sum unit
    simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel]
    dsimp only [B,C,P,Q] at v0
    linarith only [v0]
  refine ⟨apply_for k 1 1 (by decide) (by simp) (by simp)
    (by simpa using hq.not_dvd_one) (by simpa using low),?_⟩
  let z := 2^(k+1)
  have zp : 0<z := by dsimp [z];positivity
  have zcast : (z:ℤ)=(2:ℤ)^(k+1) := by push_cast [z];rfl
  have dvz : ¬q∣z := fun bad => Nat.not_dvd_of_pos_of_lt (by decide : 0<2) (by omega)
    (hq.dvd_of_dvd_pow bad)
  have app := apply_for (1+k*z) (z-1) z (by
    dsimp [z];have := Nat.one_lt_pow (by omega : k+1≠0) (by decide : 1<2);omega)
    (by nlinarith only [Nat.mul_le_mul_left k (Nat.sub_le z 1)])
    (by have h := Nat.sub_add_cancel (by omega : 1≤z); nlinarith only [h])
    dvz (by
      push_cast [Nat.cast_sub zp,zcast]
      exact bal.le)
  simpa [Nat.cast_sub zp,zcast,F,G] using app
end OMA.OddBox245212
end
section
namespace OMA.LastDigit245212
open Finset ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212
open scoped ArithmeticFunction.sigma
def digitSum (p A S e : ℕ) := ∑ j∈range e,p^j*(A*(j+1)+S)
def denom (A S T d : ℕ) := 2*T*(d+1)-(A*(d+1)+S)
private theorem digit_pos {p A S d : ℕ} (hs : 0<S) (hd : 0<d) :
    0<digitSum p A S d := by
  apply sum_pos' (fun _ _ => Nat.zero_le _)
  exact ⟨0,mem_range.mpr hd,by simpa using (show 0<A+S by omega)⟩
private theorem geom (p e : ℕ) (hp : 1≤p) :
    (∑ j∈range e,p^j)*(p-1)+1=p^e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ,add_mul,pow_succ]
    have v := congrArg (fun x : ℕ => p^e*x) (Nat.sub_add_cancel hp)
    simp only [Nat.mul_add,Nat.mul_one] at v
    nlinarith only [ih,v]
theorem digits {p A S T d : ℕ} (hp : 1<p) (hs : 0<S) (hd : 0<d)
    (eq : digitSum p A S (d+1)=p^d*(2*T*(d+1))) :
    0<denom A S T d ∧ denom A S T d*(p-1)<A*d+S ∧ A*d+S≤denom A S T d*p ∧
      (1<d → A*d+S<denom A S T d*p) := by
  have dp := digit_pos (p:=p) (A:=A) hs hd
  have h := eq
  rw [digitSum,sum_range_succ,←digitSum] at h
  have co : A*(d+1)+S<2*T*(d+1) := by
    by_contra! v
    have := Nat.mul_le_mul_left (p^d) v
    omega
  have cut := Nat.sub_add_cancel co.le
  change denom A S T d+_= _ at cut
  have rest : digitSum p A S d=p^d*denom A S T d := by
    rw [←cut] at h
    rw [Nat.mul_add (p^d) (denom A S T d)] at h
    exact Nat.add_right_cancel h
  have ppos : 0<p^d := by positivity
  have up : digitSum p A S d ≤ (∑ j∈range d,p^j)*(A*d+S) := by
    rw [sum_mul]
    exact sum_le_sum (fun j hj => Nat.mul_le_mul_left _ (Nat.add_le_add_right
      (Nat.mul_le_mul_left A (mem_range.mp hj)) S))
  have sm := Nat.mul_le_mul_right (p-1) up
  have strict : denom A S T d*(p-1)<A*d+S := by
    apply Nat.lt_of_mul_lt_mul_left (a:=p^d)
    calc
      p^d*(denom A S T d*(p-1)) = digitSum p A S d*(p-1) := by rw [rest,mul_assoc]
      _ ≤ ((∑ j∈range d,p^j)*(p-1))*(A*d+S) := by simpa only [mul_right_comm] using sm
      _ < p^d*(A*d+S) := Nat.mul_lt_mul_of_pos_right (by have := geom p d hp.le; omega) (by omega)
  refine ⟨Nat.sub_pos_of_lt co,strict,?_⟩
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  rw [digitSum,sum_range_succ,←digitSum,pow_succ,mul_assoc] at rest
  have v : (A*(k+1)+S)*p^k ≤ (denom A S T (k+1)*p)*p^k := by
    nlinarith only [rest, Nat.zero_le (digitSum p A S k)]
  have pk : 0<p^k := by positivity
  exact ⟨(le_of_mul_le_mul_right v pk), fun hk =>
    (lt_of_mul_lt_mul_right (by nlinarith only [rest, digit_pos (p:=p) (A:=A) hs (by omega : 0<k)] :
      (A*(k+1)+S)*p^k < (denom A S T (k+1)*p)*p^k) (Nat.zero_le _))⟩
theorem balance_digits {p m d : ℕ} (hm : 0 < m) (hp : Nat.Prime p) (cop : m.Coprime p) (hd : 0<d)
    (eq : OeisA245212.a (m*p^d)=(σ 1 (m*p^d):ℤ)) :
    let A := W m; let S := σ 1 m; let T := m*(σ 0 m);
    0<denom A S T d ∧ denom A S T d*(p-1)<A*d+S ∧ A*d+S≤denom A S T d*p ∧
      (1<d → A*d+S<denom A S T d*p) := by
  have b := balance (mul_ne_zero hm.ne' (pow_ne_zero _ hp.ne_zero)) eq
  have c := cop.pow_right d
  rw [w_mult.map_mul_of_coprime c,isMultiplicative_sigma.map_mul_of_coprime c,
    isMultiplicative_sigma.map_mul_of_coprime c,w_pow hp,sigma_one_apply_prime_pow hp,
    sigma_zero_apply_prime_pow hp] at b
  have spos : 0<σ 1 m := by
    rw [sigma_one_apply]
    exact sum_pos' (fun _ _ => Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr hm.ne',by decide⟩
  apply digits hp.one_lt spos hd
  unfold digitSum
  simp_rw [show ∀ j:ℕ,p^j*(W m*(j+1)+σ 1 m)=W m*(p^j*(j+1))+σ 1 m*p^j by intro j; ring]
  rw [sum_add_distrib,←mul_sum,←mul_sum]
  simpa only [mul_comm,mul_left_comm,mul_assoc] using b
end OMA.LastDigit245212
end
section
namespace OMA.OddCofactor245212
open Finset ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212
open scoped ArithmeticFunction.sigma
theorem last_dvd {m p d : ℕ} (hm : 0 < m) (hp : Nat.Prime p) (cop : m.Coprime p)
    (hd : 0<d) (eq : OeisA245212.a (m*p^d)=(σ 1 (m*p^d):ℤ)) : p∣W m+σ 1 m := by
  have b := balance (mul_ne_zero hm.ne' (pow_ne_zero _ hp.ne_zero)) eq
  have c := cop.pow_right d
  rw [w_mult.map_mul_of_coprime c,isMultiplicative_sigma.map_mul_of_coprime c,
    w_pow hp,sigma_one_apply_prime_pow hp] at b
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  have b' := congrArg (fun t : ℕ => (t:ZMod p)) b
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sum,Nat.cast_pow,Nat.cast_ofNat,
    Nat.cast_one,ZMod.natCast_self] at b' ⊢
  rw [sum_range_succ',sum_range_succ'] at b'
  simp [zero_pow hd.ne',pow_succ] at b'
  exact b'
end OMA.OddCofactor245212
end
section
namespace OMA.Large245212
open OMA.Smooth245212 OMA.LastDigit245212 Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma Function
def tax (p e : ℕ) := (e+1)*p^e
def sig (p e : ℕ) := (p^(e+1)-1)/(p-1)
def wt (p e : ℕ) := (p*tax p e-sig p e)/(p-1)
theorem moments {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    sig p e=σ 1 (p^e) ∧ wt p e=W (p^e) := by
  have pp : 0<p-1 := by have := hp.one_lt; omega
  have s : sig p e=σ 1 (p^e) := by
    rw [sig,sigma_one_apply_prime_pow hp,←geom_sum_mul_of_one_le hp.pos (e+1),Nat.mul_div_cancel _ pp]
  refine ⟨s,?_⟩
  have w : (p-1)*W (p^e)+σ 1 (p^e)=p*tax p e := by
    clear s
    rw [w_pow hp,sigma_one_apply_prime_pow hp,tax]
    induction e with
    | zero => simp; omega
    | succ k ih =>
      rw [sum_range_succ _ (k+1),sum_range_succ _ (k+1),mul_add,pow_succ]
      have add := Nat.sub_add_cancel (show 1≤p from hp.pos)
      nlinarith only [ih,congrArg (fun z:ℕ => z*(p^k*p)*(k+2)) add]
  rw [wt,s,←w,Nat.add_sub_cancel,Nat.mul_div_cancel_left _ pp]
def candidate (A S T d : ℕ) := (A*d+S-1)/denom A S T d+1
theorem force {A S T d p : ℕ} (hs : 0<S) (hp : 1<p) (hD : 0<denom A S T d)
    (lo : denom A S T d*(p-1)<A*d+S) (hi : A*d+S≤denom A S T d*p) :
    candidate A S T d=p := by
  unfold candidate
  have low : p-1≤(A*d+S-1)/denom A S T d := (Nat.le_div_iff_mul_le hD).2 (by rw [mul_comm]; omega)
  have up : (A*d+S-1)/denom A S T d<p := (Nat.div_lt_iff_lt_mul hD).2
    (by rw [Nat.mul_comm p (denom A S T d)]; omega)
  omega
end OMA.Large245212
end
section
namespace OMA.Height245212
open OMA.Smooth245212 Finset
def den (p e : ℕ) : ℕ := (e+1)*(p-1)^2
def err (p e : ℕ) : ℚ := 1 / ((den p e : ℚ)*(p:ℚ)^e)
def yr (p e : ℕ) : ℚ := p / (((p:ℚ)-1)*(e+1))
theorem localY {p : ℕ} (hp : 1<p) (e : ℕ) :
    Y p (some e)=yr p e-((p:ℚ)-1)*err p e := by
  have pp : (1:ℚ)<p := by exact_mod_cast hp
  have p0 : (p:ℚ)≠0 := by linarith
  have p1 : (p:ℚ)-1≠0 := by linarith
  have inv1 : (p:ℚ)⁻¹-1≠0 := sub_ne_zero.mpr (inv_lt_one_of_one_lt₀ pp).ne
  have flip : (1:ℚ)-p≠0 := by linarith
  simp only [Y,yr,err,den,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
    Nat.cast_pow,Nat.cast_sub (by omega : 1≤p),inv_pow,pow_succ (p:ℚ) e]
  field_simp
  ring_nf
end OMA.Height245212
end
section
namespace OMA.ReverseDigit245212
open OMA.Smooth245212 OMA.Abundance245212 OMA.Height245212
open scoped ArithmeticFunction.sigma
def numerator (p A S : ℚ) := p*((p-1)*S-A)
def denominator (p A T : ℚ) := (p-1)*(2*T*(p-1)-p*A)
private theorem y_closed {p : ℕ} (hp : 1<p) (e : ℕ) :
    Y p (some e)*(((e:ℚ)+1)*((p:ℚ)-1)*(p:ℚ)^(e+1)) =
      (p:ℚ)*((p:ℚ)^(e+1)-1) := by
  have hpp : (1:ℚ)<p := by exact_mod_cast hp
  rw [localY hp]
  simp only [yr,err,den,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow,
    Nat.cast_sub (by omega : 1≤p),pow_succ (p:ℚ) e]
  field_simp [show (p:ℚ)-1≠0 by linarith,show (p:ℚ)≠0 by linarith,
    show (e:ℚ)+1≠0 by positivity]
theorem identity {p e : ℕ} (hp : 1<p) {A S T : ℚ}
    (balance : A*X p (some e)+S*Y p (some e)=2*T) :
    numerator p A S*((p:ℚ)^(e+1)-1)=denominator p A T*((e:ℚ)+1)*(p:ℚ)^(e+1) := by
  have hpp : (1:ℚ)<p := by exact_mod_cast hp
  unfold X at balance
  field_simp [(show (p:ℚ)-1≠0 by linarith)] at balance
  have y:=y_closed hp e
  unfold numerator denominator
  linear_combination (((e:ℚ)+1)*((p:ℚ)-1)*(p:ℚ)^(e+1))*balance -
    (((p:ℚ)-1)*S-A)*y
private theorem grows {p : ℕ} (hp : 3≤p) (e : ℕ) : e+2<p^(e+1) := by
  induction e with
  | zero => simpa using (show 2<p by omega)
  | succ e ih => rw [pow_succ p (e+1)];nlinarith
theorem recover {p m e : ℕ} (hm : 0 < m) (hp : p.Prime) (odd : p≠2) (cop : m.Coprime p)
    (eq : OeisA245212.a (m*p^e)=(σ 1 (m*p^e):ℤ)) :
    let C:=numerator p (W m) (σ 1 m)
    let D:=denominator p (W m) (m*(σ 0 m:ℚ))
    D≠0 ∧ C/D=((e:ℚ)+1)+((e:ℚ)+1)/((p:ℚ)^(e+1)-1) ∧
      ⌊C/D⌋=(e:ℤ)+1 := by
  let C:=numerator p (W m) (σ 1 m)
  let D:=denominator p (W m) (m*(σ 0 m:ℚ))
  have bal:=affine_of_eq hm.ne' hp (hp.coprime_iff_not_dvd.mp cop.symm) eq
  have exactId : C*((p:ℚ)^(e+1)-1)=D*((e:ℚ)+1)*(p:ℚ)^(e+1) :=
    identity hp.one_lt (by simpa only [mul_assoc] using bal)
  have nonzero:=OMA.PrimePowerDiv245212.nonzero hm hp odd cop e eq
  have nQ : (W m:ℚ)-((p:ℚ)-1)*(σ 1 m:ℚ)≠0 := by exact_mod_cast nonzero
  have cne : C≠0 := mul_ne_zero (Nat.cast_ne_zero.mpr hp.ne_zero) (sub_ne_zero.mpr
    (sub_ne_zero.mp nQ).symm)
  have big0:=grows (p:=p) (by have:=hp.two_le;omega) e
  have big : (e:ℚ)+2 < (p:ℚ)^(e+1) := by exact_mod_cast big0
  have pos : 0<(p:ℚ)^(e+1)-1 := by linarith [Nat.cast_nonneg (α:=ℚ) e]
  have dne : D≠0 := by
    intro z;rw [z,zero_mul,zero_mul] at exactId
    exact (mul_ne_zero cne pos.ne') exactId
  have ratio : C/D=((e:ℚ)+1)+((e:ℚ)+1)/((p:ℚ)^(e+1)-1) := by
    field_simp [dne,pos.ne']
    linear_combination exactId
  refine ⟨dne,ratio,?_⟩
  change ⌊C/D⌋=_
  rw [ratio,Int.floor_eq_iff]
  push_cast
  have lo : 0≤((e:ℚ)+1)/((p:ℚ)^(e+1)-1) := div_nonneg (by positivity) pos.le
  have hi : ((e:ℚ)+1)/((p:ℚ)^(e+1)-1)<1 := (div_lt_one pos).mpr (by linarith)
  constructor <;> linarith
end OMA.ReverseDigit245212
end
section
namespace OMA.PairExtension245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.LastDigit245212 OMA.Large245212
open scoped ArithmeticFunction.sigma
open OMA.Large245212 (force)
open OMA.Large245212 (moments)
theorem last_log_base {a q f b : ℕ} (ha : 0<a) (hq : q.Prime) (oq : q≠2) (cop : a.Coprime q)
    (base : 1<b) (below : b≤q)
    (pos : 0<f) (eq : OeisA245212.a (a*q^f)=(σ 1 (a*q^f):ℤ)) :
    f≤Nat.log b (W a+σ 1 a)+1 := by
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
  have raw := OMA.PrimePowerDiv245212.cofactor_bound ha hq oq cop (g+1) eq
  let A := W a
  let S := σ 1 a
  have q1 : (1:ℤ)≤q := by exact_mod_cast hq.one_le
  have absBound : ((A:ℤ)-((q:ℤ)-1)*(S:ℤ)).natAbs≤q*(A+S) := by
    apply Int.ofNat_le.mp
    rw [Int.natCast_natAbs]
    push_cast
    apply abs_le.mpr
    constructor <;> nlinarith only [Int.natCast_nonneg A,Int.natCast_nonneg S,
      mul_nonneg (sub_nonneg.mpr q1) (Int.natCast_nonneg A),
      mul_nonneg (sub_nonneg.mpr q1) (Int.natCast_nonneg S)]
  have power := raw.trans absBound
  change q^(g+1)≤q*(A+S) at power
  rw [pow_succ'] at power
  have small := (Nat.pow_le_pow_left below g).trans (Nat.le_of_mul_le_mul_left power hq.pos)
  have sz : 0<S := sigma_pos 1 a ha.ne'
  exact Nat.add_le_add_right ((Nat.le_log_iff_pow_le base (by omega)).mpr small) 1
def lowerBase (R A T : ℕ) := max 2 (max R (A/(2*(2*T-A))))
theorem lowerBase_le {R A S T q f : ℕ} (q2 : 2≤q) (rq : R≤q) (fp : 0<f)
    (pos : 0<denom A S T f) (digit : A*f+S≤denom A S T f*q) : lowerBase R A T≤q := by
  have a : A<2*T := by
    by_contra! le
    have ge := Nat.mul_le_mul_right (f+1) le
    unfold denom at pos; omega
  have gd : 0<2*T-A := Nat.sub_pos_of_lt a
  have cap : denom A S T f≤(2*T-A)*(f+1) := by
    rw [Nat.sub_mul]; unfold denom; omega
  have two : (2*T-A)*(f+1)≤(2*T-A)*(2*f) := Nat.mul_le_mul_left _ (by omega)
  have lim := digit.trans (Nat.mul_le_mul_right q (cap.trans two))
  have val : A*f≤(2*(2*T-A)*q)*f := by nlinarith only [lim,Nat.zero_le S]
  have num := Nat.le_of_mul_le_mul_right val fp
  have le : A/(2*(2*T-A))≤q := by
    exact (Nat.div_le_div_right num).trans_eq (by rw [Nat.mul_comm (2*_) q,Nat.mul_div_cancel _ (by omega)])
  exact max_le q2 (max_le rq le)
def permitted (A S T q f : ℕ) : Bool :=
  decide (q∣A+S) && decide (A*wt q f+S*sig q f=2*T*OMA.Large245212.tax q f)
theorem fit {a q f : ℕ} (ha : 0<a) (hq : q.Prime) (cop : a.Coprime q)
    (hf : 0<f) (eq : OeisA245212.a (a*q^f)=(σ 1 (a*q^f):ℤ)) :
    permitted (W a) (σ 1 a) (a*(σ 0 a)) q f=true := by
  obtain ⟨ss,ww⟩ := OMA.Large245212.moments hq f
  have b := OMA.Abundance245212.balance (mul_ne_zero ha.ne' (pow_ne_zero _ hq.ne_zero)) eq
  have cf := cop.pow_right f
  rw [w_mult.map_mul_of_coprime cf,isMultiplicative_sigma.map_mul_of_coprime cf,
    isMultiplicative_sigma.map_mul_of_coprime cf,sigma_zero_apply_prime_pow hq] at b
  simp only [permitted,Bool.and_eq_true,decide_eq_true_eq,ss,ww,OMA.Large245212.tax]
  exact ⟨OMA.OddCofactor245212.last_dvd ha hq cop hf eq,by linear_combination b⟩
def free (R A S T : ℕ) : Bool := (List.range (Nat.log (lowerBase R A T) (A+S)+1)).all fun i =>
  let f := i+1
  let q := candidate A S T f
  decide (denom A S T f=0 ∨ q<R) || !permitted A S T q f
theorem free_sound {a q f R : ℕ} (ha : 0<a) (hq : q.Prime) (oq : q≠2) (cop : a.Coprime q)
    (hf : 0<f) (lo : R≤q) (check : free R (W a) (σ 1 a) (a*(σ 0 a))=true) :
    OeisA245212.a (a*q^f)≠(σ 1 (a*q^f):ℤ) := by
  intro eq
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hf.ne'
  obtain ⟨pos,low,high,_⟩ := balance_digits ha hq cop hf eq
  have base := lowerBase_le hq.two_le lo hf pos high
  have limit := last_log_base (b:=lowerBase R (W a) (a*(σ 0 a))) ha hq oq cop
    (lt_of_lt_of_le (by decide : 1<2) (le_max_left _ _)) base hf eq
  have val := OMA.Large245212.force (sigma_pos 1 a ha.ne') hq.one_lt pos low high
  have h := List.all_eq_true.mp check g (List.mem_range.mpr (by omega))
  simp [val,pos.ne',Nat.not_lt_of_ge lo,fit ha hq cop hf eq] at h
def known (A S T q : ℕ) : Bool :=
  let C := OMA.ReverseDigit245212.numerator q A S
  let D := OMA.ReverseDigit245212.denominator q A T
  if ¬q∣A+S ∨ D=0 then true else
    let f := (⌊C/D⌋-1).toNat
    Bool.not (permitted A S T q f)
theorem known_sound {a q f : ℕ} (ha : 0<a) (hq : q.Prime) (oq : q≠2) (cop : a.Coprime q)
    (hf : 0<f) (check : known (W a) (σ 1 a) (a*(σ 0 a)) q=true) :
    OeisA245212.a (a*q^f)≠(σ 1 (a*q^f):ℤ) := by
  intro eq
  obtain ⟨nz,_,recover⟩ := OMA.ReverseDigit245212.recover ha hq oq cop eq
  have dv := OMA.OddCofactor245212.last_dvd ha hq cop hf eq
  simp only [known,Nat.cast_mul] at check
  simp [dv,nz,recover,fit ha hq cop hf eq] at check
end OMA.PairExtension245212
end
section
namespace OMA.Moving245212
open Finset OMA.Smooth245212
def approx (upper : Bool) (q e : Option ℕ) : ℚ :=
  match q, e with
  | _, none => 0
  | none, some k => 1/((k:ℚ)+1)
  | some p, some k =>
    if k<32 then Y p (some k) else
      let v := (p:ℚ)/(((p:ℚ)-1)*((k:ℚ)+1))
      if upper then v else v*(1-(p:ℚ)⁻¹^32)
private theorem approx_correct {p e : ℕ} (hp : 1<p) :
    approx false (some p) (some e) ≤ Y p (some e) ∧
      Y p (some e) ≤ approx true (some p) (some e) := by
  by_cases small : e<32
  · simp [approx,small]
  simp only [approx,if_neg small,Bool.false_eq_true,↓reduceIte]
  have pp : (1:ℚ)<p := by exact_mod_cast hp
  have pn : (p:ℚ)≠0 := by positivity
  have pe := sub_ne_zero.mpr pp.ne'
  have norm : Y p (some e) =
      (p:ℚ)/(((p:ℚ)-1)*((e:ℚ)+1)) * (1-(p:ℚ)⁻¹^(e+1)) := by
    simp only [Y]
    rw [show (p:ℚ)⁻¹-1=(1-p)/p by field_simp]
    generalize (p:ℚ)⁻¹^(e+1) = z
    field_simp [show 1-(p:ℚ)≠0 by linarith]
    ring
  rw [norm]
  have hle : (p:ℚ)⁻¹^(e+1) ≤ (p:ℚ)⁻¹^32 :=
    pow_le_pow_of_le_one (by positivity) (inv_lt_one_of_one_lt₀ pp).le (by omega)
  have v : 0≤(p:ℚ)/(((p:ℚ)-1)*((e:ℚ)+1)) := by positivity
  constructor
  · exact mul_le_mul_of_nonneg_left (by linarith only [hle]) v
  · simpa using mul_le_mul_of_nonneg_left
      (show 1-(p:ℚ)⁻¹^(e+1) ≤ 1 by exact sub_le_self _ (by positivity)) v
private theorem y_prime {p q : ℕ} (hp : 1<p) (hpq : p≤q) (e : ℕ) :
    Y q (some e) ≤ Y p (some e) := by
  rw [y_avg hp,y_avg (hp.trans_le hpq)]
  gcongr with i _
private theorem y_infty {p e : ℕ} (hp : 1<p) :
    1/((e:ℚ)+1) ≤ Y p (some e) := by
  rw [y_avg hp]
  gcongr
  calc
    (1:ℚ) = (p:ℚ)⁻¹^0 := by simp
    _ ≤ ∑ i∈range (e+1),(p:ℚ)⁻¹^i :=
      single_le_sum (f:= fun i => (p:ℚ)⁻¹^i) (fun _ _ => by positivity) (by simp)
def yl (prime exp : Band) := max 0 (approx false prime.hi exp.hi)
def yu (prime exp : Band) := approx true (some prime.lo) (some exp.lo)
def xl (prime exp : Band) : ℚ := match prime.hi with
  | none => 1
  | some p => max 1 (1+(1-yu prime exp)/((p:ℚ)-1))
def xu (prime exp : Band) : ℚ := 1+(1-yl prime exp)/((prime.lo:ℚ)-1)
private theorem y_bounds {p e : ℕ} {pb eb : Band} (hp : 1<pb.lo)
    (pi : pb.Contains p) (ei : eb.Contains e) :
    yl pb eb ≤ Y p (some e) ∧ Y p (some e) ≤ yu pb eb := by
  have pp := hp.trans_le pi.1
  constructor
  · refine max_le (y_nonneg pp _) ?_
    cases he : eb.hi with
    | none => simpa [he,approx] using y_nonneg pp (some e)
    | some t =>
      have et := y_anti pp (ei.2 _ he)
      cases hq : pb.hi with
      | none => simpa [he,hq,approx] using (y_infty pp).trans et
      | some q =>
        have pq := pi.2 _ hq
        exact (approx_correct (e:=t) (pp.trans_le pq)).1.trans
          ((y_prime pp pq t).trans et)
  · exact (y_anti pp ei.1).trans ((y_prime hp pi.1 _).trans (approx_correct hp).2)
theorem factor_bounds {p e : ℕ} {pb eb : Band} (hp : 1<pb.lo)
    (pi : pb.Contains p) (ei : eb.Contains e) :
    0≤xl pb eb ∧ xl pb eb ≤ X p (some e) ∧ X p (some e) ≤ xu pb eb ∧
    0≤yl pb eb ∧ yl pb eb ≤ Y p (some e) ∧ Y p (some e) ≤ yu pb eb := by
  obtain ⟨ylb,yub⟩ := y_bounds hp pi ei
  have pp := hp.trans_le pi.1
  have pp' : (1:ℚ)<p := by exact_mod_cast pp
  have pl : (1:ℚ)<pb.lo := by exact_mod_cast hp
  have oneX : 1≤X p (some e) := by
    have := sub_nonneg.mpr (y_one pp (some e))
    exact le_add_of_nonneg_right (by positivity)
  have yl0 : 0≤yl pb eb := le_max_left _ _
  refine ⟨?_,?_,?_,yl0,ylb,yub⟩
  · cases h : pb.hi <;> simp [xl,h]
  · cases h : pb.hi with
    | none => simpa [xl,h] using oneX
    | some q =>
      simp only [xl,h,max_le_iff]
      refine ⟨oneX,?_⟩
      have pq : (p:ℚ)≤q := by exact_mod_cast pi.2 q h
      unfold X
      apply add_le_add_right
      exact div_le_div₀ (by linarith only [y_one pp (some e)]) (by linarith only [yub])
        (by linarith only [pp']) (by linarith only [pq])
  · have pq : (pb.lo:ℚ) ≤ p := by exact_mod_cast pi.1
    unfold X xu
    apply add_le_add_right
    exact div_le_div₀ (by linarith only [y_one pp (some e),ylb]) (by linarith only [ylb])
      (by linarith only [pl]) (by linarith only [pq])
end OMA.Moving245212
end
section
namespace OMA.Moving245212
open Finset OMA.Smooth245212
def single (p : ℕ) : Band := ⟨p,some p⟩
def primes (e : I → ℕ) : Fin 3 → ℕ := ![2,3,e 3]
def base (b : Box) : Fin 3 → Band := ![single 2,single 3,b 3]
def value (e : I → ℕ) : ℚ :=
  (∏ i:Fin 3, X (primes e i) (some (e i.castSucc)))+
    ∏ i:Fin 3, Y (primes e i) (some (e i.castSucc))
def lower (b : Box) : ℚ := (∏ i:Fin 3, xl (base b i) (b i.castSucc))+
    ∏ i:Fin 3, yl (base b i) (b i.castSucc)
def upper (b : Box) : ℚ := (∏ i:Fin 3, xu (base b i) (b i.castSucc))+
    ∏ i:Fin 3, yu (base b i) (b i.castSucc)
theorem enclose {b : Box} {e : I → ℕ} (hq : 1<(b 3).lo)
    (h : ∀ i, (b i).Contains (e i)) : lower b ≤ value e ∧ value e ≤ upper b := by
  have low (i : Fin 3) : 1<(base b i).lo := by
    fin_cases i <;> simp [base,single,hq]
  have hits (i : Fin 3) : (base b i).Contains (primes e i) := by
    fin_cases i <;> simp [base,primes,single,Band.Contains]
    exact h 3
  have v (i : Fin 3) := factor_bounds (low i) (hits i) (h i.castSucc)
  constructor
  · exact add_le_add
      (prod_le_prod (fun i _ => (v i).1) (fun i _ => (v i).2.1))
      (prod_le_prod (fun i _ => (v i).2.2.2.1) (fun i _ => (v i).2.2.2.2.1))
  · exact add_le_add
      (prod_le_prod (fun i _ => (v i).1.trans (v i).2.1) (fun i _ => (v i).2.2.1))
      (prod_le_prod (fun i _ => (v i).2.2.2.1.trans (v i).2.2.2.2.1)
        (fun i _ => (v i).2.2.2.2.2))
def check : Tree → Box → Bool
| .leaf,b => decide (((b 3).hi = some (b 3).lo ∧ ¬Nat.Prime (b 3).lo) ∨
    1<(b 3).lo ∧ (2<lower b ∨ upper b<2))
| .split i cut l r,b => check l (left b i cut) && check r (right b i cut)
theorem reject (t : Tree) {b : Box} (cert : check t b=true)
    {e : I → ℕ} (h : ∀ i,(b i).Contains (e i)) (prime : Nat.Prime (e 3)) : value e≠2 := by
  induction t generalizing b with
  | leaf =>
    rcases of_decide_eq_true cert with ⟨same,comp⟩|⟨good,larger|smaller⟩
    · exact (comp ((Nat.le_antisymm (h 3).1 ((h 3).2 _ same)).symm ▸ prime)).elim
    · exact (larger.trans_le (enclose good h).1).ne'
    · exact ((enclose good h).2.trans_lt smaller).ne
  | split i cut l r il ir =>
    obtain ⟨cl,cr⟩ := Bool.and_eq_true_iff.mp cert
    by_cases ec : e i≤cut
    · apply il cl
      intro j; by_cases ji : j=i
      · subst j; simpa [left,Band.Contains] using And.intro (h i).1 ec
      · simpa [left,ji] using h j
    · apply ir cr
      intro j; by_cases ji : j=i
      · subst j; simpa [right,Band.Contains] using And.intro (by omega : cut+1≤e i) (h i).2
      · simpa [right,ji] using h j
def Excluded (b : Box) : Prop := ∀ e : I → ℕ, (∀ i,(b i).Contains (e i)) →
  Nat.Prime (e 3) → value e ≠ 2
theorem bisect (b : Box) (i : I) (cut : ℕ)
    (hl : Excluded (left b i cut)) (hr : Excluded (right b i cut)) : Excluded b := by
  intro e h
  by_cases ec : e i≤cut
  · apply hl
    intro j; by_cases ji : j=i
    · subst j; simpa [left,Band.Contains] using And.intro (h i).1 ec
    · simpa [left,ji] using h j
  · apply hr
    intro j; by_cases ji : j=i
    · subst j; simpa [right,Band.Contains] using And.intro (by omega : cut+1≤e i) (h i).2
    · simpa [right,ji] using h j
end OMA.Moving245212
end
section
namespace OMA.OddFaces245212
open Finset OMA.Smooth245212 OMA.Moving245212
def limitX (p : ℕ) : ℚ := X p none
end OMA.OddFaces245212
end
section
namespace OMA.OddFaces245212
open Finset OMA.Smooth245212
variable {ι : Type*} [DecidableEq ι]
private theorem factor (p e : ℕ) :
    X p (some e)=Y p (some e)+(1-Y p (some e))*limitX p := by
  simp only [limitX,X,Y]; ring
private theorem cap_one {p : ℕ} (hp : 1<p) : 1≤limitX p := by
  have h : (1:ℚ)<p := by exact_mod_cast hp
  simp only [limitX,X,Y,sub_zero]
  exact le_add_of_nonneg_right (by positivity)
theorem envelope (s : Finset ι) (p e : ι → ℕ) (hp : ∀ i,1<p i) :
    (∏ i∈s,X (p i) (some (e i))) ≤ (∏ i∈s,Y (p i) (some (e i)))+
      (1-∏ i∈s,Y (p i) (some (e i)))*(∏ i∈s,limitX (p i)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s js ih =>
    simp only [prod_insert js]
    have mult := mul_le_mul_of_nonneg_left ih (x_nonneg (hp j) (some (e j)))
    refine mult.trans ?_
    rw [factor (p j)]
    let T := ∏ i∈s,Y (p i) (some (e i))
    let C := ∏ i∈s,limitX (p i)
    have t0 : 0≤T := prod_nonneg (fun i _ => y_nonneg (hp i) _)
    have t1 : T≤1 := prod_le_one (fun i _ => y_nonneg (hp i) _) (fun i _ => y_one (hp i) _)
    have c1 : 1≤C := one_le_prod (fun i _ => cap_one (hp i))
    have l1 := cap_one (hp j)
    have u1 := y_one (hp j) (some (e j))
    have u0 := y_nonneg (hp j) (some (e j))
    change (_+_*_)*(T+(1-T)*C)≤_*T+(1-_*T)*(_*C)
    nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg t0 (sub_nonneg.mpr u1)) (by linarith only [l1] : 0≤limitX (p j))) (sub_nonneg.mpr c1),
      mul_nonneg (mul_nonneg (mul_nonneg u0 (sub_nonneg.mpr t1)) (by linarith only [c1] : 0≤C)) (sub_nonneg.mpr l1)]
theorem cap_anti {a b : ℕ} (ha : 1<a) (hab : a≤b) : limitX b≤limitX a := by
  have a' : (1:ℚ)<a := by exact_mod_cast ha
  have ab : (a:ℚ)≤b := by exact_mod_cast hab
  simp only [limitX,X,Y,sub_zero]
  exact add_le_add_right (one_div_le_one_div_of_le (by linarith) (by linarith)) 1
end OMA.OddFaces245212
end
section
namespace OMA.DyadicEuler245212
open Finset Nat OMA.Smooth245212 OMA.OddFaces245212
open scoped ArithmeticFunction.sigma
open OMA.OddFaces245212 (envelope)
theorem cap_needed_at_two {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (p e : ι → ℕ) (hp : ∀ j,1<p j) (i : ι) (ei : 0<e i)
    (eq : X 2 (some k)*(∏ j,X (p j) (some (e j)))+
      Y 2 (some k)*(∏ j,Y (p j) (some (e j)))=2) :
    2≤X 2 (some k)*∏ j,limitX (p j) := by
  let c := X 2 (some k)
  let d := Y 2 (some k)
  have sum : c+d=2 := by dsimp [c,d,X]; norm_num; ring
  have c0 : 0≤c := x_nonneg (by decide) _
  have yl : Y (p i) (some (e i))<1 := by
    simpa [y_avg (hp i)] using OMA.Abundance245212.y_strict (hp i) ei
  have small : (∏ j,Y (p j) (some (e j)))<1 := by
    rw [←prod_erase_mul _ _ (mem_univ i)]
    exact (mul_le_of_le_one_left (y_nonneg (hp i) _) (prod_le_one
      (fun j _ => y_nonneg (hp j) _) (fun j _ => y_one (hp j) _))).trans_lt yl
  have weigh := mul_le_mul_of_nonneg_left (OMA.OddFaces245212.envelope univ p e hp) c0
  change c*(∏ j,X (p j) (some (e j)))+d*(∏ j,Y (p j) (some (e j)))=2 at eq
  change 2≤c*_
  by_contra! low
  let t := ∏ j,Y (p j) (some (e j))
  let C := ∏ j,limitX (p j)
  change c*C<2 at low
  change t<1 at small
  change c*_≤c*(t+(1-t)*C) at weigh
  change c*_+d*t=2 at eq
  nlinarith only [weigh,eq,mul_pos (sub_pos.mpr small) (sub_pos.mpr low),
    congrArg (·*t) sum]
theorem pair_norm (k p q e f : ℕ) (hp : p.Prime) (hq : q.Prime)
    (po : 2<p) (pq : p<q)
    (eq : OeisA245212.a (2^k*p^e*q^f)=(σ 1 (2^k*p^e*q^f):ℤ)) :
    X 2 (some k)*(X p (some e)*X q (some f))+Y 2 (some k)*(Y p (some e)*Y q (some f))=2 := by
  let P : Fin 3 → ℕ := ![2,p,q]
  let E : Fin 3 → ℕ := ![k,e,f]
  have prime (i : Fin 3) : (P i).Prime := by fin_cases i <;> simp [P,hp,hq,prime_two]
  have inj : P.Injective := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [P] <;> omega
  have he : total P E=2^k*p^e*q^f := by simp [total,Fin.prod_univ_three,P,E,mul_assoc]
  have norm := normalized_of_eq P prime inj E (he ▸ eq)
  simpa [normalized,Fin.prod_univ_three,P,E,mul_assoc] using norm
theorem pair_cap (k p q e f : ℕ) (hp : p.Prime) (hq : q.Prime)
    (po : 2<p) (pq : p<q) (ep : 0<e)
    (eq : OeisA245212.a (2^k*p^e*q^f)=(σ 1 (2^k*p^e*q^f):ℤ)) :
    2≤X 2 (some k)*(limitX p*limitX q) := by
  have norm := pair_norm k p q e f hp hq po pq eq
  have lim := cap_needed_at_two k (![p,q] : Fin 2 → ℕ) ![e,f]
    (by intro j; fin_cases j <;> first | exact hp.one_lt | exact hq.one_lt) 0 ep
  simpa [Fin.prod_univ_two,mul_assoc] using lim (by simpa [Fin.prod_univ_two,mul_assoc] using norm)
theorem pair_small {k p q e f u v : ℕ} (hp : p.Prime) (hq : q.Prime)
    (po : 2<p) (pq : p<q) (ep : 0<e) (hu : 1<u) (hv : 1<v) (up : u≤p) (vq : v≤q)
    (small : X 2 (some k)*(limitX u*limitX v)<2) :
    OeisA245212.a (2^k*p^e*q^f)≠(σ 1 (2^k*p^e*q^f):ℤ) := by
  intro eq
  have atMost := mul_le_mul_of_nonneg_left (mul_le_mul (cap_anti hu up) (cap_anti hv vq)
    (x_nonneg hq.one_lt none) (x_nonneg hu none)) (x_nonneg (by decide : 1<2) (some k))
  exact ((pair_cap k p q e f hp hq po pq ep eq).trans atMost).not_gt small
end OMA.DyadicEuler245212
end
section
namespace OMA.DyadicBlocks245212
open Finset Nat
def geom (p n : ℕ) := ∑ i∈range n,p^i
def weight (p n : ℕ) := ∑ i∈range n,p^i*(i+1)
theorem split_g (p m n : ℕ) : geom p (m+n)=geom p m+p^m*geom p n := by
  simp only [geom,sum_range_add,mul_sum,pow_add]
theorem split_w (p m n : ℕ) :
    weight p (m+n)=weight p m+p^m*(weight p n+m*geom p n) := by
  simp only [weight,geom,sum_range_add]
  congr 1
  simp only [mul_sum,←sum_add_distrib,pow_add]
  apply sum_congr rfl
  intro i _
  ring
theorem pow_block (p h : ℕ) (ho : Odd p) :
    p^(2^h) ≡ 1 [MOD 2^(h+1)] := by
  have cop := (Nat.coprime_two_right.mpr ho).pow_right (h+1)
  simpa only [Nat.totient_prime_pow_succ Nat.prime_two,Nat.reduceSub,mul_one] using
    Nat.ModEq.pow_totient cop
theorem div_geom (p : ℕ) (ho : Odd p) (h : ℕ) : 2^h ∣ geom p (2^h) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [pow_succ, Nat.mul_two,split_g,←one_add_mul]
    have even := (ho.pow (n:=2^h)).add_one
    simpa [Nat.two_mul,add_comm] using Nat.mul_dvd_mul (even_iff_two_dvd.mp even) ih
theorem weight_block (p : ℕ) (ho : Odd p) (h : ℕ) :
    weight p (2^(h+1)) ≡ 2^h [MOD 2^(h+1)] := by
  induction h with
  | zero => simp [weight,sum_range_succ,Nat.ModEq]
  | succ h ih =>
    let N := 2^(h+1)
    have even : 2∣geom p N := (dvd_pow_self 2 (by omega : h+1≠0)).trans (div_geom p ho _)
    have off : N*geom p N ≡ 0 [MOD 2*N] := by
      apply Nat.modEq_zero_iff_dvd.mpr
      simpa [mul_comm] using Nat.mul_dvd_mul_left N even
    have pp : p^N ≡ 1 [MOD 2*N] := by
      simpa only [N,pow_succ (2:ℕ) (h+1),mul_comm] using pow_block p (h+1) ho
    have twice : 2*weight p N ≡ N [MOD 2*N] := by
      simpa only [N,pow_succ' (2:ℕ) h] using ih.mul_left' 2
    have bridge := (Nat.ModEq.rfl (a:=weight p N)).add
      (pp.mul ((Nat.ModEq.rfl (a:=weight p N)).add off))
    change weight p (2^(h+1+1)) ≡ 2^(h+1) [MOD 2^(h+1+1)]
    rw [pow_succ' (2:ℕ) (h+1)]
    change weight p (2*N) ≡ N [MOD 2*N]
    rw [show 2*N=N+N by omega,split_w]
    simpa [Nat.two_mul] using bridge.trans (by simpa [Nat.two_mul] using twice)
theorem prime_block (p h a : ℕ) (hp : p.Prime) (ho : Odd p) :
    let N := 2^(h+1)
    let n := p^(a*N)
    n ≡ 1 [MOD N] ∧ ArithmeticFunction.sigma 0 n ≡ 1 [MOD N] ∧
      ArithmeticFunction.sigma 1 n ≡ 1 [MOD N] ∧
      OMA.Smooth245212.W n ≡ 1+a*2^h [MOD N] := by
  let N := 2^(h+1)
  have p1 : p^N ≡ 1 [MOD N] := (pow_block p (h+1) ho).of_dvd
    (pow_dvd_pow _ (by omega : h+1≤h+1+1))
  have zeroG := Nat.modEq_zero_iff_dvd.mpr (div_geom p ho (h+1))
  have we := weight_block p ho h
  have powr (b : ℕ) : p^(b*N) ≡ 1 [MOD N] := by
    rw [Nat.mul_comm b N,pow_mul]
    simpa only [one_pow] using p1.pow b
  have dz (b : ℕ) : b*N ≡ 0 [MOD N] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left _ _)
  have blk (b : ℕ) : geom p (b*N) ≡ 0 [MOD N] ∧ weight p (b*N) ≡ b*2^h [MOD N] := by
    induction b with
    | zero => simp [geom,weight,Nat.ModEq]
    | succ b ih =>
      rw [Nat.succ_mul,split_g,split_w]
      constructor
      · simpa only [mul_zero,add_zero] using ih.1.add ((powr b).mul zeroG)
      · simpa only [zero_mul,add_zero,one_mul,Nat.succ_mul] using
          ih.2.add ((powr b).mul (we.add ((dz b).mul zeroG)))
  have times (b : ℕ) : b*N+1 ≡ 1 [MOD N] := (dz b).add_right 1
  refine ⟨powr a,?_,?_,?_⟩
  · rw [ArithmeticFunction.sigma_zero_apply_prime_pow hp]; exact times a
  · rw [ArithmeticFunction.sigma_one_apply_prime_pow hp,sum_range_succ]
    simpa only [geom,N,zero_add] using (blk a).1.add (powr a)
  · rw [OMA.Smooth245212.w_pow hp,sum_range_succ]
    simpa only [weight,N,one_mul,add_comm 1] using (blk a).2.add ((powr a).mul (times a))
end OMA.DyadicBlocks245212
end
section
namespace OMA.CapOrder245212
open Finset OMA.Smooth245212 OMA.Abundance245212
private theorem geom (p : ℕ) (hp : 1<p) (e : ℕ) :
    (∑ i∈range (e+1),p^i)<2*p^e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ _ (e+1),pow_succ]
    have := Nat.mul_le_mul_left (p^e) (show 2≤p from hp)
    omega
theorem y_short {q : ℕ} (hq : Nat.Prime q) (e : ℕ) :
    Y q (some e)*((e:ℚ)+1)<2 := by
  have h := y_factor hq e
  have l : (ArithmeticFunction.sigma 1 (q^e):ℚ)<2*(q:ℚ)^e := by
    exact_mod_cast (show ArithmeticFunction.sigma 1 (q^e)<2*q^e by
      rw [ArithmeticFunction.sigma_one_apply_prime_pow hq]; exact geom q hq.one_lt e)
  apply lt_of_mul_lt_mul_right (a:= (q:ℚ)^e)
  · linarith only [h,l]
  · positivity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end OMA.CapOrder245212
end
section
namespace OMA.SquareCompact245212
open Finset Filter Topology OMA.Smooth245212
end OMA.SquareCompact245212
end
section
namespace OMA.DyadicPower245212
open Finset Nat ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212 OMA.DyadicBlocks245212
open scoped ArithmeticFunction.sigma ArithmeticFunction.Omega
private theorem odd_block (u h : ℕ) (odd : Odd u) :
    let N := 2^(h+1)
    let v := u^N
    v ≡ 1 [MOD N] ∧ σ 0 v ≡ 1 [MOD N] ∧ σ 1 v ≡ 1 [MOD N] ∧
      W v ≡ σ 0 (u^(2^h)) [MOD N] := by
  let N := 2^(h+1)
  induction u using Nat.recOnPrimeCoprime with
  | zero => simp at odd
  | prime_pow p e hp =>
    by_cases zero : e=0
    · subst e; simp [W,Nat.ModEq]
    have op : Odd p := (Nat.prime_two.coprime_iff_not_dvd.mp
      (Nat.coprime_two_left.mpr odd)) |> fun h => Nat.odd_iff.mpr (by
        by_contra! hh
        have d : 2∣p := by omega
        exact h (d.trans (dvd_pow_self _ zero)))
    have hh := prime_block p h e hp op
    simpa only [←pow_mul,sigma_zero_apply_prime_pow hp,add_comm 1] using hh
  | coprime a b ha hb hab ia ib =>
    obtain ⟨oa,ob⟩ := Nat.odd_mul.mp odd
    obtain ⟨a0,a1,a2,a3⟩ := ia oa
    obtain ⟨b0,b1,b2,b3⟩ := ib ob
    have c := (hab.pow_left (2^(h+1))).pow_right (2^(h+1))
    have d := (hab.pow_left (2^h)).pow_right (2^h)
    dsimp only
    simp only [mul_pow,isMultiplicative_sigma.map_mul_of_coprime c,
      isMultiplicative_sigma.map_mul_of_coprime d,w_mult.map_mul_of_coprime c]
    exact ⟨by simpa using a0.mul b0,by simpa using a1.mul b1,by simpa using a2.mul b2,a3.mul b3⟩
theorem dyadic_balance (k : ℕ) :
    W (2^k)+σ 1 (2^k)=2*2^k*(σ 0 (2^k)) := by
  rw [w_pow Nat.prime_two,sigma_zero_apply_prime_pow Nat.prime_two,
    sigma_one_apply_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ _ (k+1),sum_range_succ _ (k+1),pow_succ]
    linarith only [ih]
theorem dyadic_odd (k : ℕ) : Odd (W (2^k)) := by
  rw [w_pow Nat.prime_two,Nat.odd_iff,sum_range_succ']
  have h : 2∣∑ i∈range k, 2^(i+1)*(i+1+1) :=
    Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _)
  simp only [pow_zero,zero_add,one_mul]
  omega
theorem tau_root {k h u : ℕ} (ou : Odd u)
    (eq : OeisA245212.a (2^k*u^(2^(h+1)))=(σ 1 (2^k*u^(2^(h+1))):ℤ)) :
    σ 0 (u^(2^h)) ≡ 1 [MOD 2^(h+1)] := by
  let d := 2^k
  let N := 2^(h+1)
  let v := u^N
  have cop : d.Coprime v := ((Nat.coprime_two_left.mpr ou).pow_left k).pow_right N
  have nz : d*v ≠ 0 := mul_ne_zero (by dsimp [d]; positivity) (pow_ne_zero _ ou.pos.ne')
  have bal := balance nz eq
  rw [w_mult.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
    isMultiplicative_sigma.map_mul_of_coprime cop] at bal
  obtain ⟨v0,t,s,w⟩ := odd_block u h ou
  have red : W d*(σ 0 (u^(2^h)))+σ 1 d ≡ 2*d*(σ 0 d) [MOD N] := by
    have left := (w.mul_left (W d)).add (s.mul_left (σ 1 d))
    have right := ((v0.mul_left d).mul_left 2).mul (t.mul_left (σ 0 d))
    apply (show W d*(σ 0 (u^(2^h)))+σ 1 d ≡ W d*W v+σ 1 d*(σ 1 v) [MOD N] by
      simpa only [mul_one] using left.symm).trans
    rw [bal]
    simpa only [mul_one] using right
  have known := dyadic_balance k
  change W d+σ 1 d=2*d*(σ 0 d) at known
  rw [←known] at red
  have coeff : N.Coprime (W d) := (Nat.coprime_two_left.mpr (dyadic_odd k)).pow_left _
  exact (red.add_right_cancel' _ |>.trans (show W d ≡ W d*1 [MOD N] by rw [mul_one])).cancel_left_of_coprime coeff
private theorem square_of_odd_tau {u : ℕ} (odd : Odd (σ 0 u)) : IsSquare u := by
  induction u using Nat.recOnPrimeCoprime with
  | zero => simp at odd
  | prime_pow p a hp =>
    rw [sigma_zero_apply_prime_pow hp,Nat.odd_iff] at odd
    have even : Even a := Nat.even_iff.mpr (by omega)
    obtain ⟨b,rfl⟩ := even
    exact ⟨p^b,pow_add _ _ _⟩
  | coprime a b _ _ cop ia ib =>
    rw [isMultiplicative_sigma.map_mul_of_coprime cop,Nat.odd_mul] at odd
    exact (ia odd.1).mul (ib odd.2)
theorem square_root_is_square {k u : ℕ} (ou : Odd u)
    (eq : OeisA245212.a (2^k*u^2)=(σ 1 (2^k*u^2):ℤ)) : IsSquare u := by
  have v := tau_root (h:=0) ou eq
  apply square_of_odd_tau
  simpa [Nat.odd_iff,Nat.ModEq] using v
end OMA.DyadicPower245212
end
section
namespace OMA.FixedExponents245212
open Finset OMA.Smooth245212
theorem x_avg {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    X p (some e)=(∑ j∈range (e+1),((e-j+1:ℕ):ℚ)*(p:ℚ)⁻¹^j)/((e:ℚ)+1) := by
  have xf := x_factor hp e
  rw [w_pow hp] at xf
  push_cast at xf
  have nz : (p:ℚ)≠0 := by exact_mod_cast hp.ne_zero
  apply (eq_div_iff (by positivity)).2
  apply mul_right_cancel₀ (pow_ne_zero e nz)
  rw [mul_assoc,xf,sum_mul]
  rw [←sum_range_reflect (fun j => (p:ℚ)^j*((j:ℚ)+1)) (e+1)]
  refine sum_congr rfl fun j hj => ?_
  have h : j≤e := by have := mem_range.mp hj; omega
  have h' : e+1-1-j=e-j := by omega
  rw [h',Nat.cast_add,Nat.cast_one]
  have add : j+(e-j)=e := by omega
  have cancel : (p:ℚ)⁻¹^j*(p:ℚ)^e=(p:ℚ)^(e-j) := by
    calc
      _ = (p:ℚ)⁻¹^j*((p:ℚ)^j*(p:ℚ)^(e-j)) := by rw [←pow_add,add]
      _ = _ := by rw [inv_pow,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ nz),one_mul]
  rw [mul_assoc,cancel,mul_comm]
theorem y_pos {p : ℕ} (hp : Nat.Prime p) (e : ℕ) : 0<Y p (some e) := by
  rw [y_avg hp.one_lt]
  apply div_pos _ (by positivity)
  exact sum_pos' (fun _ _ => by positivity) ⟨0,by simp,by simp⟩
end OMA.FixedExponents245212
end
section
namespace OMA.SquareFinite245212
open Finset OMA.Smooth245212 OMA.SquareCompact245212
open scoped ArithmeticFunction.sigma
end OMA.SquareFinite245212
end
section
namespace OMA.WeightVal245212
open Finset OMA.Smooth245212 OMA.DyadicBlocks245212
open scoped ArithmeticFunction.sigma
open OMA.DyadicBlocks245212 (split_g)
open OMA.DyadicBlocks245212 (split_w)
open OMA.DyadicBlocks245212 (pow_block)
abbrev val (n : ℕ) := n.factorization 2
theorem val_odd {n : ℕ} (h : Odd n) : val n=0 :=
  Nat.factorization_eq_zero_of_not_dvd (by have := Nat.odd_iff.mp h; omega)
theorem identify {n h : ℕ} (nz : 0<n) (mod : n ≡ 2^h [MOD 2^(h+1)]) : val n=h := by
  have pp : 0<2^h := Nat.two_pow_pos _
  have bound : 2^h<2^(h+1) := by rw [pow_succ]; omega
  have low : 2^h∣n := Nat.modEq_zero_iff_dvd.mp
    ((mod.of_dvd (pow_dvd_pow _ (by omega))).trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl _)))
  have high : ¬2^(h+1)∣n := by
    intro d
    have bad := Nat.modEq_zero_iff_dvd.mp (mod.symm.trans (Nat.modEq_zero_iff_dvd.mpr d))
    exact bound.not_ge (Nat.le_of_dvd pp bad)
  have l := (Nat.prime_two.pow_dvd_iff_le_factorization nz.ne').mp low
  have hi := mt (Nat.prime_two.pow_dvd_iff_le_factorization nz.ne').mpr high
  change n.factorization 2=h
  omega
theorem blocks (p : ℕ) (op : Odd p) (h u : ℕ) :
    let N := 2^(h+1)
    geom p (u*N) ≡ 0 [MOD N] ∧ weight p (u*N) ≡ u*2^h [MOD N] := by
  let N := 2^(h+1)
  have p1 : p^N ≡ 1 [MOD N] := (OMA.DyadicBlocks245212.pow_block p (h+1) op).of_dvd
    (pow_dvd_pow _ (by omega : h+1≤h+1+1))
  have gp := Nat.modEq_zero_iff_dvd.mpr (div_geom p op (h+1))
  have wp := weight_block p op h
  have powr (b : ℕ) : p^(b*N) ≡ 1 [MOD N] := by
    rw [Nat.mul_comm b N,pow_mul]; simpa only [one_pow] using p1.pow b
  dsimp only
  change geom p (u*N) ≡ 0 [MOD N] ∧ weight p (u*N) ≡ u*2^h [MOD N]
  induction u with
  | zero => simp [geom,weight,Nat.ModEq]
  | succ u ih =>
    have dz : u*N ≡ 0 [MOD N] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left _ _)
    rw [Nat.succ_mul,OMA.DyadicBlocks245212.split_g,OMA.DyadicBlocks245212.split_w]
    exact ⟨by simpa only [mul_zero,zero_add] using ih.1.add ((powr u).mul gp),
      by simpa only [zero_mul,add_zero,one_mul,Nat.succ_mul] using
        ih.2.add ((powr u).mul (wp.add (dz.mul gp)))⟩
private theorem even_weight {p t : ℕ} (odd : Odd p) (tp : 0<t) (even : Even t) :
    ∃ h, val t=h+1 ∧ weight p t ≡ 2^h [MOD 2^(h+1)] ∧ 2^(h+1)∣geom p t := by
  obtain ⟨k,u,ou,eq⟩ := Nat.exists_eq_two_pow_mul_odd tp.ne'
  cases k with
  | zero => simp only [pow_zero,one_mul] at eq; exact (Nat.not_even_iff_odd.mpr ou (eq ▸ even)).elim
  | succ h =>
    have prod : t=u*2^(h+1) := eq.trans (mul_comm _ _)
    have vv : val t=h+1 := by
      have vu := val_odd ou
      unfold val at vu ⊢
      rw [prod,Nat.factorization_mul ou.pos.ne' (by positivity),Finsupp.add_apply,
        Nat.factorization_pow_self Nat.prime_two,vu,zero_add]
    have b := blocks p odd h u
    dsimp only at b
    have o : u ≡ 1 [MOD 2] := by simpa [Nat.ModEq] using Nat.odd_iff.mp ou
    have reduced : u*2^h ≡ 2^h [MOD 2^(h+1)] := by
      simpa [pow_succ,mul_comm] using o.mul_right' (2^h)
    exact ⟨h,vv,prod ▸ b.2.trans reduced,prod ▸ Nat.modEq_zero_iff_dvd.mp b.1⟩
private theorem weight_pos {p t : ℕ} (ht : 0<t) : 0<weight p t :=
  sum_pos' (fun _ _=>Nat.zero_le _) ⟨0,mem_range.mpr ht,by simp⟩
theorem weight_local {p : ℕ} (hp : p.Prime) (odd : Odd p) (e : ℕ) :
    val (W (p^e))+1=val (e+1)+val (e+2) := by
  rw [w_pow hp]
  change val (weight p (e+1))+1=_
  rcases Nat.even_or_odd (e+1) with ev|od
  · obtain ⟨h,vv,ww,_⟩ := even_weight odd (by omega) ev
    have vo := val_odd (show Odd (e+2) from ev.add_one)
    rw [identify (weight_pos (by omega)) ww,vv,vo,Nat.add_zero]
  · have ev : Even (e+2) := od.add_one
    obtain ⟨h,vv,ww,_⟩ := even_weight odd (by omega) ev
    have d : 2^(h+1)∣e+2 := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : e+2≠0)).mpr vv.ge
    have off : p^(e+1)*(e+2) ≡ 0 [MOD 2^(h+1)] :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right d _)
    have next : weight p (e+2) ≡ weight p (e+1) [MOD 2^(h+1)] := by
      dsimp only [weight]
      rw [sum_range_succ _ (e+1)]
      simpa only [weight,add_zero] using (Nat.ModEq.refl (weight p (e+1))).add off
    rw [identify (weight_pos (by omega)) (next.symm.trans ww),val_odd od,vv,zero_add]
theorem sigma_local {p : ℕ} (hp : p.Prime) (odd : Odd p) (e : ℕ) :
    2^val (e+1)∣ArithmeticFunction.sigma 1 (p^e) := by
  rcases Nat.even_or_odd (e+1) with ev|od
  · obtain ⟨_,vv,_,sg⟩ := even_weight (p:=p) odd (by omega) ev
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp,vv]; exact sg
  · simp [val_odd od]
end OMA.WeightVal245212
end
section
namespace OMA.ExponentParity245212
open Finset Nat ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212
  OMA.WeightVal245212
open scoped ArithmeticFunction.sigma Function
theorem exponent_product {ι : Type*} [Fintype ι] (p e : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (odd : ∀ i, Odd (p i)) (inj : Function.Injective p)
    (a : ℕ) (eq : OeisA245212.a (2^a*total p e) = (σ 1 (2^a*total p e) : ℤ)) :
    2^Fintype.card ι ∣ ∏ i, (e i+2) := by
  classical
  let z (i : ι) := p i^e i
  have cop : (↑(univ : Finset ι) : Set ι).Pairwise (Coprime on z) := by
    intro i _ j _ ne
    exact (((Nat.coprime_primes (hp i) (hp j)).mpr (fun h => ne (inj h))).pow_left _).pow_right _
  have co : (2^a).Coprime (total p e) := (Coprime.prod_right (fun i _ =>
    (Nat.coprime_two_left.mpr (odd i)).pow_right (e i))).pow_left _
  have zn : total p e ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp i).ne_zero)
  have b := balance (mul_ne_zero (by positivity) zn) eq
  rw [w_mult.map_mul_of_coprime co,isMultiplicative_sigma.map_mul_of_coprime co,
    isMultiplicative_sigma.map_mul_of_coprime co] at b
  let T := ∑ i, WeightVal245212.val (e i+1)
  have sd : 2^T ∣ σ 1 (total p e) := by
    rw [show σ 1 (total p e) = ∏ i, σ 1 (z i) from
      IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=1)) univ cop]
    dsimp only [T]
    rw [←prod_pow_eq_pow_sum]
    exact prod_dvd_prod_of_dvd _ _ (fun i _ => sigma_local (hp i) (odd i) (e i))
  have td : 2^T ∣ σ 0 (total p e) := by
    rw [show σ 0 (total p e) = ∏ i, σ 0 (z i) from
      IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=0)) univ cop]
    dsimp only [T,z]
    simp only [sigma_zero_apply_prime_pow (hp _)]
    rw [←prod_pow_eq_pow_sum]
    exact prod_dvd_prod_of_dvd _ _ fun i _ =>
      (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : e i+1≠0)).mpr le_rfl
  have wb : 2^T ∣ W (2^a)*W (total p e) := by
    apply (Nat.dvd_add_iff_left (dvd_mul_of_dvd_right sd (σ 1 (2^a)))).mpr
    rw [b]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right td _) _
  have wd := ((Nat.coprime_two_left.mpr (OMA.DyadicPower245212.dyadic_odd a)).pow_left T).dvd_of_dvd_mul_left wb
  have wm := IsMultiplicative.map_prod z w_mult univ cop
  change W (total p e) = _ at wm
  rw [wm] at wd
  have wpos (i : ι) : W (z i) ≠ 0 := by
    rw [show z i=p i^e i from rfl,w_pow (hp i)]
    exact (sum_pos' (fun _ _ => Nat.zero_le _) ⟨0,mem_range.mpr (by omega),by simp⟩).ne'
  have lower := (Nat.prime_two.pow_dvd_iff_le_factorization
    (prod_ne_zero_iff.mpr (fun i _ => wpos i))).mp wd
  rw [Nat.factorization_prod_apply (fun i _ => wpos i)] at lower
  have allv := Finset.sum_congr (s₁:=univ) rfl (fun i _ => weight_local (hp i) (odd i) (e i))
  simp only [sum_add_distrib,sum_const,smul_eq_mul,mul_one] at allv
  change (∑ i, WeightVal245212.val (W (p i^e i))) + Fintype.card ι =
    (∑ i, WeightVal245212.val (e i+1)) + ∑ i, WeightVal245212.val (e i+2) at allv
  apply (Nat.prime_two.pow_dvd_iff_le_factorization
    (prod_ne_zero_iff.mpr (fun i _ => by omega : ∀ i ∈ univ, e i+2≠0))).mpr
  rw [Nat.factorization_prod_apply (fun i _ => by omega : ∀ i ∈ univ, e i+2≠0)]
  change (∑ i, WeightVal245212.val (e i+1)) ≤ ∑ i, WeightVal245212.val (W (p i^e i)) at lower
  change Fintype.card ι ≤ ∑ i, WeightVal245212.val (e i+2)
  omega
end OMA.ExponentParity245212
end
section
namespace OMA.BoundedAtom245212
open Finset Filter Topology Nat OMA.Smooth245212 OMA.SquareCompact245212
open OMA.WeightVal245212 (weight_local)
open scoped ArithmeticFunction.sigma
theorem normalized_dyadic {K : ℕ} (k : ℕ) (p e : Fin K → ℕ) (hp : ∀ i,Nat.Prime (p i))
    (op : ∀ i,Odd (p i)) (inj : p.Injective)
    (eq : OeisA245212.a (2^k*total p e)=(σ 1 (2^k*total p e):ℤ)) :
    X 2 (some k)*(∏ i,X (p i) (some (e i)))+
      Y 2 (some k)*(∏ i,Y (p i) (some (e i)))=2 := by
  let P : Fin (K+1) → ℕ := Fin.cons 2 p
  let E : Fin (K+1) → ℕ := Fin.cons k e
  have prime : ∀ i,Nat.Prime (P i) := Fin.cases Nat.prime_two hp
  have distinct : P.Injective := Fin.cons_injective_of_injective (by
    rintro ⟨i,hi⟩; have h := op i; rw [hi] at h; norm_num [Nat.odd_iff] at h) inj
  have all : total P E=2^k*total p e := by
    rw [total,Fin.prod_univ_succ]; rfl
  have norm := normalized_of_eq P prime distinct E (by rw [all]; exact eq)
  unfold normalized at norm
  rw [Fin.prod_univ_succ (fun i => X (P i) (some (E i))),
    Fin.prod_univ_succ (fun i => Y (P i) (some (E i)))] at norm
  exact norm
end OMA.BoundedAtom245212
end
section
namespace OMA.TwoOddFinite245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
end OMA.TwoOddFinite245212
end
section
namespace OMA.DyadicLeast245212
open Finset Nat ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
open OMA.FixedExponents245212 (x_avg)
open OMA.FixedExponents245212 (y_pos)
def term (p e : ℕ) : ℚ := (e:ℚ)/(((e:ℚ)+1)*p)
private theorem x_two_terms {p e : ℕ} (hp : p.Prime) (he : 0<e) :
    1+term p e ≤ X p (some e) := by
  rw [OMA.FixedExponents245212.x_avg hp]
  apply (le_div_iff₀ (by positivity)).mpr
  let z (i : ℕ) := ((e-i+1:ℕ):ℚ)*(p:ℚ)⁻¹^i
  have sub : range 2⊆range (e+1) := range_subset_range.mpr (by omega)
  have b := sum_le_sum_of_subset_of_nonneg (f:=z) sub (fun _ _ _ => by dsimp [z]; positivity)
  refine le_trans ?_ b
  simp only [sum_range_succ,sum_range_zero,zero_add,pow_zero,pow_one,mul_one,z,Nat.sub_zero,
    Nat.cast_add,Nat.cast_one,Nat.cast_sub (show 1≤e by omega)]
  have pp : (p:ℚ)≠0 := by exact_mod_cast hp.ne_zero
  unfold term
  field_simp
  ring_nf
  exact le_rfl
private theorem sum_le_product {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p e : ι → ℕ) (hp : ∀ i,(p i).Prime) (he : ∀ i,0<e i) :
    1+∑ i∈s,term (p i) (e i)≤∏ i∈s,X (p i) (some (e i)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi,prod_insert hi]
    have t0 (j) : 0≤term (p j) (e j) := by unfold term; positivity
    have s0 := sum_nonneg (s:=s) (fun j _ => t0 j)
    have b := mul_le_mul (x_two_terms (hp i) (he i)) ih (by linarith only [s0]) (x_nonneg (hp i).one_lt _)
    exact (show 1+(term (p i) (e i)+∑ j∈s,term (p j) (e j))≤_ by
      nlinarith only [mul_nonneg (t0 i) s0]).trans b
private theorem vector {K : ℕ} (k : ℕ) (p e : Fin K → ℕ) (hp : ∀ i,(p i).Prime)
    (he : ∀ i,0<e i) (eq : X 2 (some k)*(∏ i,X (p i) (some (e i)))+
      Y 2 (some k)*(∏ i,Y (p i) (some (e i)))=2) :
    (k:ℚ)*(∑ i,term (p i) (e i))<1 := by
  let c := X 2 (some k)
  let d := Y 2 (some k)
  let S := ∑ i,term (p i) (e i)
  have d0 : 0<d := OMA.FixedExponents245212.y_pos Nat.prime_two k
  have cd : c+d=2 := by dsimp [c,d,X]; norm_num; ring
  have kd : (k:ℚ)*d≤c := by
    have h := OMA.CapOrder245212.y_short prime_two k
    change d*((k:ℚ)+1)<2 at h
    linarith only [cd,h]
  have ys := prod_pos (s:=univ) (fun i _ => OMA.FixedExponents245212.y_pos (hp i) (e i))
  have s0 : 0≤S := sum_nonneg (fun i _ => by unfold term; positivity)
  have b := mul_le_mul_of_nonneg_left (sum_le_product univ p e hp he) (x_nonneg (by decide : 1<2) (some k))
  change c*(1+S)≤c*_ at b
  change c*_+d*_=2 at eq
  apply (mul_lt_mul_iff_right₀ d0).mp
  nlinarith only [eq,cd,b,mul_pos d0 ys,mul_le_mul_of_nonneg_right kd s0]
theorem reciprocal_sum {k m : ℕ} (om : Odd m)
    (eq : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) :
    (k:ℚ)*(∑ q∈m.primeFactors,term q (m.factorization q))<1 := by
  let F := m.primeFactors
  let p := F.orderEmbOfFin rfl
  let e (i : Fin F.card) := m.factorization (p i)
  have mem (i : Fin F.card) : p i∈m.primeFactors := orderEmbOfFin_mem F rfl i
  have hp (i) := prime_of_mem_primeFactors (mem i)
  have po (i) := Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr om).of_dvd_right
    (dvd_of_mem_primeFactors (mem i)))
  have ep (i) := (hp i).factorization_pos_of_dvd om.pos.ne' (dvd_of_mem_primeFactors (mem i))
  have repr : total p e=m :=
    (Fintype.prod_equiv (F.orderIsoOfFin rfl).toEquiv _
      (fun j : F => j.val^(m.factorization j.val)) (fun _ => rfl)).trans
      (Nat.prod_primeFactors_coe_pow_factorization om.pos.ne').symm
  have sm := (Fintype.sum_equiv (F.orderIsoOfFin rfl).toEquiv (fun i => term (p i) (e i))
    (fun j : F => term j.val (m.factorization j.val)) (fun _ => rfl)).trans
    (Finset.sum_coe_sort F (fun q => term q (m.factorization q)))
  rw [←sm]
  exact vector k p e hp ep (OMA.BoundedAtom245212.normalized_dyadic k p e hp po p.injective
    (by rw [repr]; exact eq))
theorem exponent_lt_twice_prime {k m q : ℕ} (om : Odd m) (hq : q∈m.primeFactors)
    (eq : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) : k<2*q := by
  have h := reciprocal_sum om eq
  have pr := prime_of_mem_primeFactors hq
  have ep := pr.factorization_pos_of_dvd om.pos.ne' (dvd_of_mem_primeFactors hq)
  have one := single_le_sum (f:=fun q => term q (m.factorization q)) (fun i _ => by unfold term; positivity) hq
  have ratio := (mul_le_mul_of_nonneg_left one (Nat.cast_nonneg k : (0:ℚ)≤k)).trans_lt h
  let e := m.factorization q
  have he : (1:ℚ)≤e := by exact_mod_cast ep
  have qp : (0:ℚ)<q := by exact_mod_cast pr.pos
  change (k:ℚ)*((e:ℚ)/((e+1)*q))<1 at ratio
  rw [←mul_div_assoc,div_lt_iff₀ (by positivity),one_mul] at ratio
  by_contra! high
  have excess := mul_le_mul_of_nonneg_right (show (2:ℚ)*q≤k by exact_mod_cast high) (le_trans (by norm_num : (0:ℚ)≤1) he)
  nlinarith only [ratio,excess,mul_nonneg qp.le (sub_nonneg.mpr he)]
end OMA.DyadicLeast245212
end
section
namespace OMA.PairSweep245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.Large245212 OMA.PairExtension245212
open scoped ArithmeticFunction.sigma
open OMA.Large245212 (moments)
open OMA.FixedExponents245212 (y_pos)
def run (test : ℕ → ℕ → ℕ → Bool) (k p e : ℕ) :=
  test (wt 2 k*wt p e) (sig 2 k*sig p e) (OMA.Large245212.tax 2 k*OMA.Large245212.tax p e)
theorem run_true {k p e : ℕ} (hp : p.Prime) (po : 2<p) (test : ℕ → ℕ → ℕ → Bool)
    (ok : run test k p e=true) :
    test (W (2^k*p^e)) (σ 1 (2^k*p^e)) ((2^k*p^e)*(σ 0 (2^k*p^e)))=true := by
  have cp := (((Nat.coprime_primes prime_two hp).mpr (by omega)).pow_left k).pow_right e
  rw [w_mult.map_mul_of_coprime cp,isMultiplicative_sigma.map_mul_of_coprime cp,
    isMultiplicative_sigma.map_mul_of_coprime cp,sigma_zero_apply_prime_pow prime_two,
    sigma_zero_apply_prime_pow hp]
  have two := OMA.Large245212.moments prime_two k
  have odd := OMA.Large245212.moments hp e
  simpa [run,two.1,two.2,odd.1,odd.2,OMA.Large245212.tax,mul_comm,mul_assoc,mul_left_comm] using ok
private theorem cop {k p q e : ℕ} (hp : p.Prime) (hq : q.Prime) (oq : 2<q) (diff : p≠q) :
    (2^k*p^e).Coprime q := (((Nat.coprime_primes prime_two hq).mpr (by omega)).pow_left k).mul_left
      (((Nat.coprime_primes hp hq).mpr diff).pow_left e)
private theorem test_free {k p q e f : ℕ} (hp : p.Prime) (hq : q.Prime) (po : 2<p) (pq : p<q)
    (fp : 0<f) (ok : run (free (p+1)) k p e=true) :
    OeisA245212.a (2^k*p^e*q^f)≠(σ 1 (2^k*p^e*q^f):ℤ) :=
  free_sound (by have := hp.pos; positivity) hq (by omega) (cop hp hq (by omega) pq.ne) fp pq
    (run_true hp po _ ok)
private theorem test_known {k p q e f : ℕ} (hp : p.Prime) (hq : q.Prime) (po : 2<p)
    (qo : 2<q) (diff : p≠q) (fp : 0<f) (ok : run (fun a s t => known a s t q) k p e=true) :
    OeisA245212.a (2^k*p^e*q^f)≠(σ 1 (2^k*p^e*q^f):ℤ) :=
  known_sound (by have := hp.pos; positivity) hq (by omega) (cop hp hq qo diff) fp
    (run_true hp po _ ok)
private theorem x_mono {p : ℕ} (hp : 1<p) {e f : ℕ} (ef : e≤f) : X p (some e)≤X p (some f) := by
  have pp : (1:ℚ)<p := by exact_mod_cast hp
  unfold X; gcongr; exact y_anti hp ef
private theorem strict {k p q e f : ℕ} (hp : p.Prime) (hq : q.Prime) (po : 2<p) (pq : p<q)
    (eq : OeisA245212.a (2^k*p^e*q^f)=(σ 1 (2^k*p^e*q^f):ℤ)) :
    X 2 (some k)*(X p (some e)*X q (some f))<2 := by
  have := OMA.DyadicEuler245212.pair_norm k p q e f hp hq po pq eq
  exact lt_of_lt_of_eq (lt_add_of_pos_right _ (mul_pos (OMA.FixedExponents245212.y_pos prime_two k)
    (mul_pos (OMA.FixedExponents245212.y_pos hp e) (OMA.FixedExponents245212.y_pos hq f)))) this
def many (test : ℕ → ℕ → ℕ → Bool) (k p B : ℕ) :=
  (List.range B).all fun i => run test k p (i+1)
private theorem each {test : ℕ → ℕ → ℕ → Bool} {k p B e : ℕ}
    (all : many test k p B=true) (ep : 0<e) (eb : e≤B) : run test k p e=true := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ep.ne'
  exact List.all_eq_true.mp all i (List.mem_range.mpr (by omega))
theorem free_case {k p q e f B : ℕ} (hp : p.Prime) (hq : q.Prime) (po : 2<p) (pq : p<q)
    (ep : 0<e) (fp : 0<f) (high : 2≤X 2 (some k)*X p (some (B+1)))
    (check : many (free (p+1)) k p B=true) :
    OeisA245212.a (2^k*p^e*q^f)≠(σ 1 (2^k*p^e*q^f):ℤ) := by
  by_cases eb : e≤B
  · exact test_free hp hq po pq fp (each check ep eb)
  intro eq
  have q1 : 1≤X q (some f) := le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (y_one hq.one_lt _))
    (sub_nonneg.mpr (by exact_mod_cast hq.one_le)))
  have step := mul_le_mul (x_mono hp.one_lt (by omega : B+1≤e)) q1 (by norm_num) (x_nonneg hp.one_lt _)
  rw [mul_one] at step
  exact ((high.trans (mul_le_mul_of_nonneg_left step (x_nonneg (by decide) _))).not_gt
    (strict hp hq po pq eq))
theorem known_case {k p q e f B : ℕ} (hp : p.Prime) (hq : q.Prime) (po : 2<p) (pq : p<q)
    (ep : 0<e) (fp : 0<f)
    (high : 2≤X 2 (some k)*(X p (some (B+1))*X q (some (B+1))))
    (left : many (fun a s t => known a s t q) k p B=true)
    (right : many (fun a s t => known a s t p) k q B=true) :
    OeisA245212.a (2^k*p^e*q^f)≠(σ 1 (2^k*p^e*q^f):ℤ) := by
  by_cases eb : e≤B
  · exact test_known hp hq po (by omega) pq.ne fp (each left ep eb)
  by_cases fb : f≤B
  · simpa only [mul_right_comm (2^k)] using
      test_known hq hp (po.trans pq) po pq.ne' ep (each right fp fb)
  intro eq
  have steps := mul_le_mul (x_mono hp.one_lt (by omega : B+1≤e)) (x_mono hq.one_lt (by omega : B+1≤f))
    (x_nonneg hq.one_lt _) (x_nonneg hp.one_lt _)
  exact (high.trans (mul_le_mul_of_nonneg_left steps (x_nonneg (by decide) _))).not_gt (strict hp hq po pq eq)
end OMA.PairSweep245212
end
section
namespace OMA.RankTwoReplay245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.Large245212 OMA.LastDigit245212
open scoped ArithmeticFunction.sigma
open OMA.Large245212 (force)
open OMA.PairExtension245212 (fit)
open OMA.PairSweep245212 (run_true)
def excluded (p f A S T : ℕ) : Bool :=
  let D := denom A S T f
  if D=0 then true else
  let q := candidate A S T f
  decide (q≤p) || !OMA.PairExtension245212.permitted A S T q f
theorem leaf {k p e q f : ℕ} (hp : p.Prime) (po : 2<p) (hq : q.Prime) (pq : p<q)
    (fp : 0<f) (ok : OMA.PairSweep245212.run (excluded p f) k p e=true) :
    OeisA245212.a (2^k*p^e*q^f)≠(σ 1 (2^k*p^e*q^f):ℤ) := by
  intro eq
  let b := 2^k*p^e
  have bp : 0<b := by dsimp [b]; have := hp.pos; positivity
  have cop : b.Coprime q :=
    (((Nat.coprime_primes prime_two hq).mpr (by omega)).pow_left k).mul_left
      (((Nat.coprime_primes hp hq).mpr pq.ne).pow_left e)
  obtain ⟨pos,low,high,_⟩ := balance_digits bp hq cop fp eq
  have value := OMA.Large245212.force (sigma_pos 1 b bp.ne') hq.one_lt pos low high
  have r := OMA.PairSweep245212.run_true hp po _ ok
  change excluded p f (W b) (σ 1 b) (b*(σ 0 b))=true at r
  simp [excluded,pos.ne',value,not_le_of_gt pq,OMA.PairExtension245212.fit bp hq cop fp eq] at r
def allIn (lo hi : ℕ) (f : ℕ → Bool) : Bool :=
  (List.range' lo (hi+1-lo)).all f
theorem member {lo hi n : ℕ} {f : ℕ → Bool} (h : allIn lo hi f=true)
    (l : lo≤n) (u : n≤hi) : f n=true :=
  List.all_eq_true.mp h n (List.mem_range'_1.mpr ⟨l,by omega⟩)
end OMA.RankTwoReplay245212
end
section
namespace OMA.ComplementaryDyad245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryPole245212 OMA.ComplementaryLocal245212
open scoped ArithmeticFunction.sigma
private theorem integer_round {k : ℕ} {b h P W S : ℤ} (hh : 0<h)
    (low : b*P≤W) (high : 2*W≤3*b*P)
    (plus : 0<den k b h P W S) (cut : ((k:ℤ)+1)*h*b*P≤G k) :
    G k≤2*den k b h P W S := by
  let u:=((k:ℤ)+1)*b*h*P-h*k*W-S
  have iden : G k*u=den k b h P W S+((k:ℤ)+1)*h*(W-b*P) := by
    dsimp [u,den,G,F]; ring
  have Kh : (0:ℤ)≤(k+1)*h := by positivity
  have gp := (dyad k).1
  have pos : 0<u := by
    apply pos_of_mul_pos_right (a:=G k) _ gp.le
    rw [iden]; exact add_pos_of_pos_of_nonneg plus (mul_nonneg Kh (sub_nonneg.mpr low))
  have gu : G k≤G k*u := by nlinarith only [mul_nonneg gp.le (by omega : 0≤u-1)]
  nlinarith only [iden,cut,gu,mul_le_mul_of_nonneg_left high Kh]
theorem near {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q)
    (pq : p≠q) (hd : 1≤d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ))
    (cut : (k+1)*(d+1)*(a+1)*p^a<2^(k+1)) :
    q≤6*(d+1)*(k+1)*(a+1)*p^a := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
  let D:=den k (a+1) (e+2) ((p:ℤ)^a) (W (p^a)) (σ 1 (p^a))
  obtain ⟨dp,qu⟩ := tail hp hq op oq pq a e k eqn
  change 0<D at dp
  have cut' : ((k:ℤ)+1)*(e+2)*(a+1)*(p:ℤ)^a≤G k := by
    have h : ((k:ℤ)+1)*(e+1+1)*(a+1)*(p:ℤ)^a<(2:ℤ)^(k+1) := by exact_mod_cast cut
    dsimp [G,z]; linarith only [h]
  have bd := bounds hp op a
  have dg := integer_round (by positivity : (0:ℤ)<e+2)
    (by exact_mod_cast bd.2.2.1) (by exact_mod_cast bd.2.1) dp cut'
  change (q:ℤ)*D≤3*(e+2)*(k+1)*(a+1)*G k*(p:ℤ)^a at qu
  have gg : (q:ℤ)*G k≤(6*(e+2)*(k+1)*(a+1)*(p:ℤ)^a)*G k := by
    nlinarith only [qu,mul_le_mul_of_nonneg_left dg (by positivity : (0:ℤ)≤q)]
  exact_mod_cast (mul_le_mul_iff_left₀ (dyad k).1).mp gg
theorem level {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q)
    (pq : p≠q) (hd : 1≤d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    2^(k+1) ≤ 3*(d+1)*(a+1)*p^a*q^d := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
  let Wp : ℤ:=W (p^a)
  let Sp : ℤ:=σ 1 (p^a)
  let Wq : ℤ:=W (q^(e+1))
  let Sq : ℤ:=σ 1 (q^(e+1))
  let J:ℤ:=((k:ℤ)+1)*(a+1)*(e+1+1)*p^a*q^(e+1)
  have phy := physical hp hq (by omega) (by omega) pq a (e+1) k eqn
  change (1+k*z k)*Wp*Wq+(z k-1)*Sp*Sq=z k*(k+1)*(a+1)*(e+1+1)*p^a*q^(e+1) at phy
  have dv : z k∣Wp*Wq-Sp*Sq := ⟨J-k*Wp*Wq-Sp*Sq,by dsimp [J];linear_combination phy⟩
  have bd := bounds hp op a
  have bq := bounds hq oq (e+1)
  have sub : Sq<Wq := by
    dsimp [Sq,Wq]
    have endq := last hq oq e
    rw [endq.1,endq.2.1]
    have rest := (bounds hq oq e).2.2.2
    have top : 0<q^(e+1) := pow_pos hq.pos _
    exact_mod_cast (show q^(e+1)+σ 1 (q^e)<(e+2)*q^(e+1)+W (q^e) by
      nlinarith only [top,rest,Nat.zero_le (e*q^(e+1))])
  have sp : 0<Sp := by
    dsimp [Sp]; exact_mod_cast (show 0<σ 1 (p^a) by
      rw [sigma_one_apply_prime_pow hp];exact Finset.sum_pos (fun i _ => pow_pos hp.pos i) (by simp))
  have sw : Sp≤Wp := by dsimp [Sp,Wp];exact_mod_cast bd.2.2.2
  have lt : 0<Wp*Wq-Sp*Sq := by
    have sq : 0≤Sq := by dsimp [Sq];positivity
    nlinarith only [mul_pos sp (sub_pos.mpr sub),
      mul_nonneg (sub_nonneg.mpr sw) (by omega : 0≤Wq)]
  have dz := Int.le_of_dvd lt dv
  have wp : 2*Wp≤3*((a:ℤ)+1)*p^a := by dsimp [Wp];exact_mod_cast bd.2.1
  have wq : 2*Wq≤3*((e:ℤ)+1+1)*q^(e+1) := by dsimp [Wq];exact_mod_cast bq.2.1
  have qs : 0≤Sq := by dsimp [Sq];positivity
  have zz : z k≤3*(e+1+1)*(a+1)*(p:ℤ)^a*q^(e+1) := by
    nlinarith only [dz,mul_le_mul wp wq (by dsimp [Wq];positivity) (by positivity),
      mul_nonneg sp.le qs, show (0:ℤ)≤(e+1+1)*(a+1)*(p:ℤ)^a*q^(e+1) by positivity]
  dsimp [z] at zz;exact_mod_cast zz
theorem power_floor {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q)
    (pq : p≠q) (hd : 1≤d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    2^(k+1)≤(6*(d+1)*(k+1)*(a+1)*p^a)^(d+1) := by
  let B := 6*(d+1)*(k+1)*(a+1)*p^a
  have bpos : 0<B := by dsimp [B];have := hp.pos;positivity
  change _ ≤ B^(d+1)
  by_cases cut : (k+1)*(d+1)*(a+1)*p^a<2^(k+1)
  · have qB : q≤B := near hp hq op oq pq hd eqn cut
    have small : 3*(d+1)*(a+1)*p^a≤B := by
      dsimp [B];nlinarith only [Nat.zero_le ((d+1)*k*(a+1)*p^a), Nat.zero_le ((d+1)*(a+1)*p^a)]
    exact (level hp hq op oq pq hd eqn).trans (by rw [pow_succ'];exact Nat.mul_le_mul small (Nat.pow_le_pow_left qB _))
  · apply (show 2^(k+1)≤B by dsimp [B];nlinarith only [cut,Nat.zero_le ((d+1)*(k+1)*(a+1)*p^a)]).trans
    simpa using (Nat.pow_le_pow_right bpos (show 1≤d+1 by omega))
end OMA.ComplementaryDyad245212
end
section
namespace OMA.QuadraticPowerGap245212
def A (p b J S : ℤ) := b*(p-1)^2*J-(p-1)*p*S
def H (p b J V : ℤ) := b*(p-1)*(p*V-(p-1)*J)-p*V
def C (p v V S : ℤ) := v*V-(p-1)*S
theorem clear (p b k z P W s J V S : ℤ)
    (weighted : (p-1)*W=b*p*P-s) (geometric : (p-1)*s=p*P-1)
    (balance : (1+k*z)*V*W+(z-1)*S*s=z*(k+1)*b*P*J) :
    P*((z-1)*(A p b J S-k*H p b J V)-(k+1)*H p b J V) =
    (z-1)*C p k V S+(k+1)*V := by
  unfold A H C
  linear_combination -(p-1)^2*balance+(1+k*z)*V*(p-1)*weighted+
    ((p-1)*(z-1)*S-(1+k*z)*V)*geometric
theorem resonance {p b k a J V S : ℕ} (hp : p.Prime) (hp3 : 3≤p) (hb : 3≤b)
    (hS : 0<S) (hV : S≤V) (hJ : J≤V)
    (hit : A p b J S=(k:ℤ)*H p b J V)
    (eqn : (p:ℤ)^a*(((2:ℤ)^(k+1)-1)*(A p b J S-(k:ℤ)*H p b J V)-
          (k+1)*H p b J V)=((2:ℤ)^(k+1)-1)*C p k V S+(k+1)*V) :
    k+1<p ∧ p∣b*J ∧ (J:ℤ)*(V-(S:ℤ))<p*S*(V-(J:ℤ)) ∧
    (p:ℤ)^a < (2:ℤ)^(k+1)*(p-1)*S := by
  let : Fact p.Prime := ⟨hp⟩
  have hp' : (3:ℤ)≤p := by exact_mod_cast hp3
  have hb' : (3:ℤ)≤b := by exact_mod_cast hb
  have hs : (0:ℤ)<S := by exact_mod_cast hS
  have hv : (S:ℤ)≤V := by exact_mod_cast hV
  have hj : (J:ℤ)≤V := by exact_mod_cast hJ
  have bu : (p:ℤ)<b*(p-1) := by
    nlinarith only [hp',hb',mul_nonneg (by omega : (0:ℤ)≤b-3) (by omega : (0:ℤ)≤p-1)]
  have hh : 0<H p b J V := by
    unfold H
    nlinarith only [mul_pos (sub_pos.mpr bu) (by omega : (0:ℤ)<V),
      mul_nonneg (mul_nonneg (by positivity : (0:ℤ)≤b) (sq_nonneg ((p:ℤ)-1))) (sub_nonneg.mpr hj)]
  have zpos : 1<(2:ℤ)^(k+1) := one_lt_pow₀ (by norm_num) (by omega)
  have red : (p:ℤ)^a*(k+1)*H p b J V+(k+1)*V= -((2:ℤ)^(k+1)-1)*C p k V S := by
    rw [hit,sub_self,mul_zero,zero_sub] at eqn
    linear_combination -eqn
  have lhs : 0<(p:ℤ)^a*(k+1)*H p b J V+(k+1)*V := by positivity
  have hneg : C p k V S<0 := by
    by_contra! ge
    nlinarith only [red,lhs,mul_nonneg (by omega : (0:ℤ)≤2^(k+1)-1) ge]
  have hk : k+1<p := by
    by_contra! h
    have hp'' : (p:ℤ)≤k+1 := by exact_mod_cast h
    unfold C at hneg
    nlinarith only [hneg,mul_nonneg (by omega : (0:ℤ)≤k-(p-1)) (by omega : (0:ℤ)≤V),
      mul_nonneg (by omega : (0:ℤ)≤p-1) (sub_nonneg.mpr hv)]
  have modp := congrArg (fun z:ℤ => (z:ZMod p)) hit
  unfold A H at modp
  push_cast at modp
  simp only [ZMod.natCast_self] at modp
  have mod0 : ((b:ZMod p)*J)*(k+1)=0 := by linear_combination modp
  have knz : (↑(k+1:ℕ):ZMod p)≠0 := by
    exact fun he => Nat.not_dvd_of_pos_of_lt (by omega) hk
      ((ZMod.natCast_eq_zero_iff (k+1) p).mp he)
  have dv : p∣b*J := by
    apply (ZMod.natCast_eq_zero_iff (b*J) p).mp
    push_cast at knz ⊢
    exact (mul_eq_zero.mp mod0).resolve_right knz
  have iden : H p b J V*C p k V S=(b:ℤ)*(p-1)^2*
      (J*(V-(S:ℤ))-p*S*(V-(J:ℤ))) := by
    simp only [H,C,A] at hit ⊢
    linear_combination -(V:ℤ)*hit
  have neg := mul_neg_of_pos_of_neg hh hneg
  rw [iden] at neg
  refine ⟨hk,dv,sub_neg.mp (neg_of_mul_neg_right neg (by positivity)),?_⟩
  have hle : 1≤((k:ℤ)+1)*H p b J V := by
    nlinarith only [hh,mul_nonneg (by positivity : (0:ℤ)≤k) hh.le]
  have pbound := mul_le_mul_of_nonneg_left hle (by positivity : 0≤(p:ℤ)^a)
  have cmax : -C p k V S ≤ ((p:ℤ)-1)*S := by unfold C; nlinarith only [mul_nonneg (by positivity : (0:ℤ)≤k) (by positivity : (0:ℤ)≤V)]
  have gc := mul_le_mul_of_nonneg_left cmax (by omega : (0:ℤ)≤2^(k+1)-1)
  nlinarith only [red,pbound,gc,mul_pos (by omega : (0:ℤ)<p-1) hs,
    mul_nonneg (by positivity : (0:ℤ)≤k+1) (by positivity : (0:ℤ)≤V)]
end OMA.QuadraticPowerGap245212
end
section
namespace OMA.ComplementaryNonres245212
open ArithmeticFunction OMA.Smooth245212 OMA.QuadraticPowerGap245212 OMA.ComplementaryLocal245212
open scoped ArithmeticFunction.sigma
theorem cleared {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    let J := ((d:ℤ)+1)*q^d
    let V : ℤ := W (q^d)
    let S : ℤ := σ 1 (q^d)
    (p:ℤ)^a*(((2:ℤ)^(k+1)-1)*(A p (a+1) J S-(k:ℤ)*H p (a+1) J V)-
      (k+1)*H p (a+1) J V)=((2:ℤ)^(k+1)-1)*C p k V S+(k+1)*V := by
  dsimp only
  have weight := OMA.PrimePowerDiv245212.weighted hp a
  zify [Nat.cast_sub hp.pos] at weight
  apply clear p (a+1) k (2^(k+1)) (p^a) (W (p^a)) (σ 1 (p^a))
    (((d:ℤ)+1)*q^d) (W (q^d)) (σ 1 (q^d))
    (by linear_combination weight) (moments hp a).1
  linear_combination physical hp hq (by omega) (by omega) pq a d k eqn
private theorem moments_sep {q d : ℕ} (hq : q.Prime) (oq : 3≤q) (hd : 1≤d) :
    (d:ℤ)*q^d ≤ (W (q^d):ℤ)-(σ 1 (q^d):ℤ) ∧
    2*q*((W (q^d):ℤ)-((d:ℤ)+1)*q^d) ≤ 3*d*(q:ℤ)^d := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
  have ends := last hq oq e
  have rest := (bounds hq oq e).2.2.2
  rw [ends.1,ends.2.1]
  have b : 2*(W (q^e):ℤ)≤3*((e:ℤ)+1)*q^e := by exact_mod_cast ends.2.2
  have l : (σ 1 (q^e):ℤ)≤W (q^e) := by exact_mod_cast rest
  push_cast
  rw [pow_succ]
  constructor
  · linarith only [l]
  · nlinarith only [mul_le_mul_of_nonneg_right b (by positivity : (0:ℤ)≤q)]
private theorem ordered {p q d Q V S : ℤ} (hs : 0 ≤ S) (hQ : 0<Q) (hd : 2≤d)
    (lower : d*Q≤V-S) (error : 0≤V-(d+1)*Q) (up : 2*q*(V-(d+1)*Q)≤3*d*Q)
    (su : 2*S≤3*Q) (strict : (d+1)*Q*(V-S)<p*S*(V-(d+1)*Q)) : q<p := by
  by_contra! pq
  have h1 := mul_le_mul_of_nonneg_right pq (mul_nonneg hs error)
  have h2 := mul_le_mul_of_nonneg_left lower (mul_nonneg (by omega : 0≤d+1) hQ.le)
  have h3 := mul_le_mul_of_nonneg_left up (show 0≤2*S by positivity)
  have h4 := mul_le_mul_of_nonneg_right su (show 0≤3*d*Q by positivity)
  have pos := mul_pos (by omega : 0<4*d-5) (mul_pos (by omega : 0<d) (sq_pos_of_pos hQ))
  nlinarith only [strict,h1,h2,h3,h4,pos]
theorem original {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q)
    (pq : p≠q) (hd : 2≤d) (ha : 2*d+4≤a)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    A p (a+1) (((d:ℤ)+1)*q^d) (σ 1 (q^d)) ≠ (k:ℤ)*H p (a+1) (((d:ℤ)+1)*q^d) (W (q^d)) := by
  intro hit
  have clr := cleared hp hq op oq pq eqn
  have bd := bounds hq oq d
  have ps : 0<σ 1 (q^d) := by
    rw [sigma_one_apply_prime_pow hq]
    exact Finset.sum_pos (fun i _ => pow_pos hq.pos i) (by simp)
  obtain ⟨hk,dv,sep,ub⟩ := resonance (J:=(d+1)*q^d) (b:=a+1) hp op (by omega)
    ps bd.2.2.2 bd.2.2.1 (by exact_mod_cast hit) (by exact_mod_cast clr)
  push_cast at sep
  have loc := moments_sep hq oq (by omega : 1≤d)
  have vj : ((d:ℤ)+1)*q^d≤W (q^d) := by exact_mod_cast bd.2.2.1
  have su : 2*(σ 1 (q^d):ℤ)≤3*(q:ℤ)^d := by exact_mod_cast bd.1
  have qq : (0:ℤ)<q := by omega
  have ordering : q<p := by
    exact_mod_cast ordered (by positivity) (pow_pos qq d) (show (2:ℤ)≤d by omega)
      loc.1 (sub_nonneg.mpr vj) loc.2 su sep
  have pp : (4:ℕ)≤p := by omega
  have notq : ¬p∣q^d := fun eq => Nat.not_dvd_of_pos_of_lt hq.pos ordering (hp.dvd_of_dvd_pow eq)
  have exp : k+1≤2*(a-d-2) := by
    by_cases hsmall : p≤2*d+4
    · omega
    · have nj : ¬p∣(d+1)*q^d := by
        intro bad
        exact ((hp.dvd_mul.mp bad).elim (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) notq)
      have bp := Nat.le_of_dvd (by omega : 0<a+1) ((hp.dvd_mul.mp dv).resolve_right nj)
      omega
  have zz : 2^(k+1)≤p^(a-d-2) := calc
    _ ≤ 2^(2*(a-d-2)) := Nat.pow_le_pow_right (by decide) exp
    _ = 4^(a-d-2) := by rw [pow_mul];norm_num
    _ ≤ _ := Nat.pow_le_pow_left pp _
  have fact := Nat.mul_le_mul_right (p^(d+2)) zz
  rw [←pow_add,show a-d-2+(d+2)=a by omega] at fact
  have smax : (σ 1 (q^d):ℤ)≤(p:ℤ)^d*p := by
    have qp := pow_le_pow_left₀ qq.le (show (q:ℤ)≤p by omega) d
    nlinarith only [su,qp,mul_nonneg (show (0:ℤ)≤p-2 by omega) (show (0:ℤ)≤p^d by positivity)]
  have cap : ((p:ℤ)-1)*(σ 1 (q^d):ℤ)≤(p:ℤ)^(d+2) := by
    rw [pow_succ,pow_succ]
    nlinarith only [mul_le_mul_of_nonneg_left smax (by omega : (0:ℤ)≤p-1),
      mul_nonneg (by positivity : (0:ℤ)≤p^d) (by positivity : (0:ℤ)≤p)]
  have ff : (2:ℤ)^(k+1)*p^(d+2)≤(p:ℤ)^a := by exact_mod_cast fact
  nlinarith only [ff,ub,mul_le_mul_of_nonneg_left cap (by positivity : (0:ℤ)≤2^(k+1))]
end OMA.ComplementaryNonres245212
end
section
namespace OMA.ComplementaryHeight245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryPole245212 OMA.ComplementaryLocal245212
open OMA.QuadraticPowerGap245212
open scoped ArithmeticFunction.sigma
theorem gap {k : ℕ} {P L H p V S R : ℤ} (pp : 0<P) (pv : 0≤V) (ps : 0 ≤ S)
    (p1 : 1≤p) (ph : 0≤H) (sep : L≠0)
    (clear : P*(G k*L-(k+1)*H)=F k*V-G k*(p-1)*S) (level : G k≤P*R) :
    G k≤(k+1)*H+R*((k+1)*V+p*S) := by
  have gp := (dyad k).1
  have fp := (dyad k).2.1
  have fc := mul_le_mul_of_nonneg_right (dyad k).2.2.1 pv
  have ep : (0:ℤ)≤(k+1)*V+p*S := by positivity
  have rr := mul_le_mul_of_nonneg_right level ep
  have common : P*G k≤P*((k+1)*H+R*((k+1)*V+p*S)) := by
    rcases lt_or_gt_of_ne sep with lt | gt
    · nlinarith only [clear,rr,mul_nonneg (mul_nonneg pp.le gp.le) (show 0≤ -L-1 by omega),
        mul_nonneg fp.le pv,mul_nonneg (mul_nonneg pp.le (show (0:ℤ)≤k+1 by positivity)) ph,
        mul_nonneg gp.le ps,mul_nonneg (mul_nonneg gp.le (show (0:ℤ)≤k+1 by positivity)) pv]
    · nlinarith only [clear,rr,fc,mul_nonneg (mul_nonneg pp.le gp.le) (show 0≤L-1 by omega),
        mul_nonneg (mul_nonneg gp.le (show 0≤p-1 by omega)) ps,
        mul_nonneg (mul_nonneg gp.le (show 0≤p by omega)) ps]
  exact (mul_le_mul_iff_right₀ pp).mp common
theorem height {p q a d k B : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (hd : 2≤d) (ha : 2*d+4≤a) (pb : p≤B) (qb : q≤B) (ab : a+1≤B) (kb : k+1≤B)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    2^(k+1)≤16*(d+1)^2*B^(2*d+3) := by
  let h : ℤ := (d:ℤ)+1
  let b : ℤ := (a:ℤ)+1
  let K : ℤ := (k:ℤ)+1
  let Q : ℤ := (q:ℤ)^d
  let P : ℤ := (p:ℤ)^a
  let U : ℤ := p-1
  let V : ℤ := W (q^d)
  let S : ℤ := σ 1 (q^d)
  let J : ℤ := h*Q
  let H0 := H p b J V
  let A0 := A p b J S
  have op' : (3:ℤ)≤p := by omega
  have oq' : (3:ℤ)≤q := by omega
  have pz : (0:ℤ)≤p := by omega
  have uz : 0≤U := by dsimp [U];omega
  have hh : 3≤h := by dsimp [h];omega
  have bh : 3≤b := by dsimp [b];omega
  have b0 : 0≤b := by omega
  have u : U≤(p:ℤ) := by dsimp [U];omega
  have ppos : 0<P := by dsimp [P];positivity
  have qp : 0<Q := by dsimp [Q];positivity
  have v0 : 0≤V := by dsimp [V];positivity
  have s0 : 0 ≤ S := by dsimp [S];positivity
  have j0 : 0≤J := by dsimp [J];positivity
  have bd := bounds hq oq d
  have jv : J≤V := by dsimp [J,V,h,Q];exact_mod_cast bd.2.2.1
  have vh : 2*V≤3*h*Q := by dsimp [V,h,Q];exact_mod_cast bd.2.1
  have sh : 2*S≤3*Q := by dsimp [S,Q];exact_mod_cast bd.1
  have bu : p≤b*U := by dsimp [U];nlinarith only [bh,op',mul_nonneg (show 0≤b-3 by omega) uz]
  have Hpos : 0≤H0 := by
    change 0≤b*U*(p*V-U*J)-p*V
    have id : b*U*(p*V-U*J)-p*V=(b*U-p)*V+b*U^2*(V-J) := by dsimp [U];ring
    rw [id];exact add_nonneg (mul_nonneg (sub_nonneg.mpr bu) v0)
      (mul_nonneg (mul_nonneg b0 (sq_nonneg _)) (sub_nonneg.mpr jv))
  have Hub : H0≤b*(p:ℤ)^2*V := by
    change b*U*(p*V-U*J)-p*V≤_
    nlinarith only [mul_nonneg (mul_nonneg b0 (sq_nonneg U)) j0,mul_nonneg pz v0,
      mul_le_mul_of_nonneg_right u (mul_nonneg (mul_nonneg b0 pz) v0)]
  have raw := OMA.ComplementaryNonres245212.cleared hp hq op oq pq eqn
  change P*(G k*(A0-k*H0)-K*H0)=G k*C p k V S+K*V at raw
  have clr : P*(G k*(A0-k*H0)-(k+1)*H0)=F k*V-G k*(p-1)*S := by
    dsimp only [K,C] at raw
    have fg : F k=(k:ℤ)*G k+(k+1) := by dsimp [F,G];ring
    rw [fg];linear_combination raw
  have nz : A0-k*H0≠0 := sub_ne_zero.mpr
    (OMA.ComplementaryNonres245212.original hp hq op oq pq hd ha eqn)
  have lev := OMA.ComplementaryDyad245212.level hp hq op oq pq (by omega) eqn
  have zz : z k≤3*h*b*P*Q := by dsimp [z,h,b,P,Q];exact_mod_cast lev
  have lev' : G k≤P*(3*h*b*Q) := by dsimp [G];linarith only [zz]
  have g := gap ppos v0 s0 (by omega) Hpos nz clr lev'
  change G k≤K*H0+(3*h*b*Q)*(K*V+p*S) at g
  have bp' : (p:ℤ)≤B := by omega
  have bb : b≤B := by dsimp [b];omega
  have kb' : K≤B := by dsimp [K];omega
  have bB : (1:ℤ)≤B := by omega
  have qB : Q≤(B:ℤ)^d := by dsimp [Q];exact pow_le_pow_left₀ (by omega) (by omega) _
  have VU : V≤2*h*B^d := by
    nlinarith only [vh,mul_le_mul_of_nonneg_left qB (show 0≤h by omega),
      mul_nonneg (show 0≤h by omega) qp.le]
  have SU : S≤2*(B:ℤ)^d := by nlinarith only [sh,qB,qp.le]
  have HH : K*H0≤2*h*(B:ℤ)^(d+4) := calc
    _ ≤ K*(b*p^2*V) := mul_le_mul_of_nonneg_left Hub (by dsimp [K];positivity)
    _ ≤ (B:ℤ)*(B*B^2*(2*h*B^d)) := by gcongr
    _ = _ := by rw [pow_add];ring
  have RR : 3*h*b*Q≤3*h*(B:ℤ)^(d+1) := calc
    _ ≤ 3*h*(B:ℤ)*B^d := by gcongr
    _ = _ := by rw [pow_succ];ring
  have VV : K*V+p*S≤4*h*(B:ℤ)^(d+1) := calc
    _ ≤ (B:ℤ)*(2*h*B^d)+B*(2*(B:ℤ)^d) := by gcongr
    _ ≤ _ := by
      rw [pow_succ]
      have pos := mul_nonneg (show 0≤h-1 by omega)
        (mul_nonneg (show 0≤(B:ℤ) by omega) (show 0≤(B:ℤ)^d by positivity))
      nlinarith only [pos]
  have R : (3*h*b*Q)*(K*V+p*S)≤(3*h*(B:ℤ)^(d+1))*(4*h*B^(d+1)) :=
    mul_le_mul RR VV (by dsimp [K];positivity) (by positivity)
  have rb : (3*h*(B:ℤ)^(d+1))*(4*h*B^(d+1))=12*h^2*(B:ℤ)^(2*d+2) := by
    rw [show 2*d+2=(d+1)+(d+1) by omega,pow_add];ring
  rw [rb] at R
  have pb₁ := pow_le_pow_right₀ bB (show d+4≤2*d+3 by omega)
  have pb₂ := pow_le_pow_right₀ bB (show 2*d+2≤2*d+3 by omega)
  have pb₀ : (1:ℤ)≤(B:ℤ)^(2*d+3) := one_le_pow₀ bB
  have cap : z k≤16*h^2*(B:ℤ)^(2*d+3) := by
    dsimp only [G] at g
    nlinarith only [g,HH,R,mul_le_mul_of_nonneg_left pb₁ (show 0≤2*h by omega),
      mul_le_mul_of_nonneg_left pb₂ (show 0≤12*h^2 by positivity),pb₀,
      mul_nonneg (show 0≤4*h^2-2*h-1 by nlinarith only [hh,sq_nonneg (h-1)])
        (show 0≤(B:ℤ)^(2*d+3) by positivity)]
  dsimp [z,h] at cap;exact_mod_cast cap
end OMA.ComplementaryHeight245212
end
section
namespace OMA.LinearPowerGap245212
def intercept (p x b : ℤ) := 2*b*x*(p-1)^2-(p-1)*(x+1)*p
def slope (p x b : ℤ) := b*(p-1)*(2*x+p)-(2*x+1)*p
def residual (p x k : ℤ) := k*(2*x+1)-(p-1)*(x+1)
private theorem divisor {p x b k : ℕ} (hp : p.Prime) (xp : x<p) (hx : 0<x)
    (kp : k+1<p) (hp2 : 2<p)
    (hit : intercept p x b=(k:ℤ)*slope p x b) : p ∣ b := by
  let : Fact p.Prime := ⟨hp⟩
  have h := congrArg (fun z : ℤ => (z : ZMod p)) hit
  simp only [intercept,slope] at h
  push_cast at h
  simp only [ZMod.natCast_self] at h
  have eqn : (b:ZMod p)*(2*(x:ZMod p)*(k+1))=0 := by
    linear_combination h
  have nonzero (n : ℕ) (h₁ : 0<n) (h₂ : n<p) : (n:ZMod p)≠0 := by
    simpa [ZMod.natCast_eq_zero_iff] using (Nat.not_dvd_of_pos_of_lt h₁ h₂)
  have hn : (2*(x:ZMod p)*(k+1))≠0 := by
    apply mul_ne_zero (mul_ne_zero (by exact_mod_cast nonzero 2 (by omega) hp2)
      (nonzero x hx xp))
    exact_mod_cast nonzero (k+1) (by omega) kp
  exact (ZMod.natCast_eq_zero_iff b p).mp ((mul_eq_zero.mp eqn).resolve_right hn)
theorem gap {p x a k : ℕ} (hp : p.Prime) (hp3 : 3≤p) (hx : 3≤x) (ha : 3≤a)
    (eqn : (p:ℤ)^a * (((2:ℤ)^(k+1)-1)*
      (intercept p x (a+1) - (k:ℤ)*slope p x (a+1)) -
      (k+1)*slope p x (a+1)) =
      ((2:ℤ)^(k+1)-1)*residual p x k+(k+1)*(2*x+1)) :
    intercept p x (a+1) ≠ (k:ℤ)*slope p x (a+1) := by
  intro hit
  let G : ℤ := 2^(k+1)-1
  let B : ℤ := slope p x (a+1)
  let C : ℤ := residual p x k
  have ep : 1<(2:ℤ)^(k+1) := one_lt_pow₀ (by norm_num) (by omega)
  have gpos : 0<G := by dsimp [G]; omega
  have pp : 0<(p:ℤ)^a := by positivity
  have hx' : (3:ℤ)≤x := by exact_mod_cast hx
  have hp' : (3:ℤ)≤p := by exact_mod_cast hp3
  have ha' : (3:ℤ)≤a := by exact_mod_cast ha
  have bu : (p:ℤ)<(a+1)*(p-1) := by
    nlinarith only [ha',hp',mul_nonneg (by omega : (0:ℤ)≤a-3) (by omega : (0:ℤ)≤p-1)]
  have bpos : 0<B := by
    dsimp [B,slope]
    nlinarith only [mul_pos (sub_pos.mpr bu) (by omega : (0:ℤ)<2*x+p),
      mul_pos (by omega : (0:ℤ)<p) (by omega : (0:ℤ)<p-1)]
  have h : (p:ℤ)^a*((k:ℤ)+1)*B+((k:ℤ)+1)*(2*x+1) = -G*C := by
    dsimp [G,B,C]; rw [hit,sub_self,mul_zero,zero_sub] at eqn
    linear_combination -eqn
  have hpos : 0 < (p:ℤ)^a*((k:ℤ)+1)*B+((k:ℤ)+1)*(2*x+1) := by positivity
  have cneg : C<0 := by
    by_contra! hc
    nlinarith only [h,hpos,mul_nonneg gpos.le hc]
  have sep : B*C=((a:ℤ)+1)*(p-1)^2*(2*(x:ℤ)^2-p*(x+1)) := by
    dsimp [B,C,slope,intercept,residual] at hit ⊢
    linear_combination -(2*(x:ℤ)+1)*hit
  have qneg : 2*(x:ℤ)^2<p*(x+1) := by
    have h₁ := mul_neg_of_pos_of_neg bpos cneg
    rw [sep] at h₁
    exact sub_neg.mp (neg_of_mul_neg_right h₁ (by positivity))
  have xp : x<p := by
    by_contra! hxp
    have hp'' : (p:ℤ)≤x := by exact_mod_cast hxp
    nlinarith only [qneg,mul_nonneg (sub_nonneg.mpr hp'') (by positivity : (0:ℤ)≤x+1),
      mul_nonneg (by omega : (0:ℤ)≤x) (by omega : (0:ℤ)≤x-1)]
  have kp : k+1<p := by
    by_contra! hkp
    dsimp [C,residual] at cneg
    have hp'' : (p:ℤ)≤k+1 := by exact_mod_cast hkp
    nlinarith only [cneg,mul_nonneg (by omega : (0:ℤ)≤k-(p-1)) (by omega : (0:ℤ)≤2*x+1),
      mul_nonneg (by omega : (0:ℤ)≤p-1) (by omega : (0:ℤ)≤x)]
  have divis : p ∣ a+1 := divisor hp xp (by omega) kp (by omega) (by exact_mod_cast hit)
  have pa := Nat.le_of_dvd (by omega : 0<a+1) divis
  have hp5 : 5≤p := by
    by_contra! hlt
    have : p=4 := by omega
    subst p; norm_num at hp
  have expPow : 2^(k+1) ≤ p^(a-2) := calc
    2^(k+1) ≤ 2^(2*(p-3)) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 4^(p-3) := by rw [pow_mul]; norm_num
    _ ≤ p^(p-3) := Nat.pow_le_pow_left (by omega) _
    _ ≤ p^(a-2) := Nat.pow_le_pow_right (by omega) (by omega)
  have pw : (p:ℤ)^2 * (2:ℤ)^(k+1) ≤ (p:ℤ)^a := by
    have hh : (2:ℤ)^(k+1) ≤ (p:ℤ)^(a-2) := by exact_mod_cast expPow
    have mul := mul_le_mul_of_nonneg_left hh (sq_nonneg (p:ℤ))
    rwa [←pow_add,show 2+(a-2)=a by omega] at mul
  have hcx : -C ≤ (p:ℤ)^2 := by
    dsimp [C,residual]
    have xp' : (x:ℤ)<p := by exact_mod_cast xp
    nlinarith only [mul_nonneg (by omega : (0:ℤ)≤p) (by omega : (0:ℤ)≤p-x-1),
      mul_nonneg (by positivity : (0:ℤ)≤k) (by positivity : (0:ℤ)≤2*x+1),hx']
  have gg := mul_le_mul_of_nonneg_left hcx gpos.le
  have bk : (1:ℤ)≤((k:ℤ)+1)*B := by
    nlinarith only [mul_nonneg (by positivity : (0:ℤ)≤k) (by omega : 0≤B),bpos]
  have v := mul_le_mul_of_nonneg_left bk pp.le
  dsimp [G] at gg h
  nlinarith only [pw,h,gg,v,sq_nonneg (p:ℤ),
    mul_pos (by positivity : (0:ℤ)<k+1) (by positivity : (0:ℤ)<2*x+1)]
end OMA.LinearPowerGap245212
end
section
namespace OMA.ComplementaryBase245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryLocal245212 OMA.ComplementaryPole245212
open scoped ArithmeticFunction.sigma
private theorem scaled {p k : ℕ} (hp : p.Prime) (op : 3≤p) (large : 5*(k+1)<p)
    (a : ℕ) : (5*((k:ℤ)+1))*(W (p^a):ℤ) ≤ (5*((k:ℤ)+1)+1)*((a:ℤ)+1)*p^a := by
  have w := OMA.PrimePowerDiv245212.weighted hp a
  zify [Nat.cast_sub hp.pos] at w
  have bottom : ((a:ℤ)+1)*p^a ≤ (W (p^a):ℤ) := by exact_mod_cast (bounds hp op a).2.2.1
  have big : 0≤((p:ℤ)-1)-5*(k+1) := by omega
  nlinarith only [w,mul_nonneg big (sub_nonneg.mpr bottom),
    (show (0:ℤ)≤σ 1 (p^a) by positivity)]
private theorem algebra {K Z F G A N : ℤ} (k1 : 1≤K) (z0 : 0<Z) (f0 : 0<F)
    (g0 : 0<G) (frac : F≤K*G) (eqn : F*A+G*N=(F+G)*Z)
    (weight : (5*K)^2*A≤(5*K+1)^2*Z) (ordinary : 2*N≤Z) : False := by
  have diff : G*Z≤2*F*(A-Z) := by
    nlinarith only [eqn,mul_le_mul_of_nonneg_left ordinary g0.le]
  have w' : (5*K)^2*(A-Z)≤(10*K+1)*Z := by nlinarith only [weight]
  have left := mul_le_mul_of_nonneg_left diff (sq_nonneg (5*K))
  have right := mul_le_mul_of_nonneg_left w' (show 0≤2*F by omega)
  have top := mul_le_mul_of_nonneg_right frac
    (mul_nonneg (show 0≤2*(10*K+1) by omega) z0.le)
  have good : 0<25*K^2-2*K*(10*K+1) := by
    nlinarith only [k1,mul_nonneg (by omega : 0≤K-1) (by omega : 0≤K)]
  nlinarith only [left,right,top,mul_pos good (mul_pos g0 z0)]
theorem small_prime {p q k a d : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (oq : 3≤q) (pq : p≠q) (many : 5≤(a+1)*(d+1))
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    p≤5*(k+1) ∨ q≤5*(k+1) := by
  by_contra! bad
  have l := scaled hp op bad.1 a
  have r := scaled hq oq bad.2 d
  have h := mul_le_mul l r (by positivity) (by positivity)
  have h₁ : 2*(σ 1 (p^a):ℤ)≤3*p^a := by exact_mod_cast (bounds hp op a).1
  have h₂ : 2*(σ 1 (q^d):ℤ)≤3*q^d := by exact_mod_cast (bounds hq oq d).1
  have ord := mul_le_mul h₁ h₂ (by positivity) (by positivity)
  have mb : (5:ℤ)≤((a:ℤ)+1)*(d+1) := by exact_mod_cast many
  have up := mul_le_mul_of_nonneg_right mb (by positivity : 0≤(p:ℤ)^a*q^d)
  have e := physical hp hq (by omega) (by omega) pq a d k eqn
  have y := dyad k
  change F k*(W (p^a):ℤ)*(W (q^d):ℤ)+G k*(σ 1 (p^a):ℤ)*(σ 1 (q^d):ℤ)=z k*(k+1)*(a+1)*(d+1)*p^a*q^d at e
  rw [←y.2.2.2] at e
  have pp : (0:ℤ)<p := by omega
  have qp : (0:ℤ)<q := by omega
  apply algebra (K:=(k:ℤ)+1) (Z:=((a:ℤ)+1)*(d+1)*p^a*q^d) (A:=(W (p^a):ℤ)*W (q^d))
    (N:=(σ 1 (p^a):ℤ)*σ 1 (q^d)) (by omega) (by positivity) y.2.1 y.1 y.2.2.1
  · linear_combination e
  · nlinarith only [h]
  · nlinarith only [ord,up, (show (0:ℤ)≤p^a*q^d by positivity)]
theorem cofactor {p q k a d : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (oq : 3≤q) (pq : p≠q)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    p^a ≤ 2*(d+1)*2^(k+1)*(k+1+p)*q^d := by
  have tq : (2^k).Coprime (q^d) := (((Nat.coprime_primes Nat.prime_two hq).mpr (by omega)).pow_left k).pow_right d
  have tp : (2^k*q^d).Coprime p :=
    (((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)).pow_left k).mul_left
      (((Nat.coprime_primes hq hp).mpr pq.symm).pow_left d)
  have pp : 0<p := hp.pos
  have qp : 0<q := hq.pos
  have bound := OMA.PrimePowerDiv245212.cofactor_bound (show 0<2^k*q^d by positivity)
    hp (by omega) tp a (by simpa [mul_right_comm] using eqn)
  rw [w_mult.map_mul_of_coprime tq,isMultiplicative_sigma.map_mul_of_coprime tq] at bound
  have geom := moments Nat.prime_two k
  norm_num at geom
  have g : (σ 1 (2^k):ℤ)=G k := by dsimp [G,z];rw [pow_succ];nlinarith only [geom.1]
  have f : (W (2^k):ℤ)=F k := by dsimp [F,z];rw [pow_succ];nlinarith only [geom.2]
  have first : (W (q^d):ℤ)≤2*((d:ℤ)+1)*q^d := by
    have hh : 2*(W (q^d):ℤ)≤3*((d:ℤ)+1)*q^d := by exact_mod_cast (bounds hq oq d).2.1
    nlinarith only [hh, (show (0:ℤ)≤((d:ℤ)+1)*q^d by positivity)]
  have second : (σ 1 (q^d):ℤ)≤2*q^d := by
    have hh : 2*(σ 1 (q^d):ℤ)≤3*q^d := by exact_mod_cast (bounds hq oq d).1
    nlinarith only [hh, (show (0:ℤ)≤q^d by positivity)]
  have dy := dyad k
  have gz : G k≤z k := by unfold G; omega
  have zpos : 0≤z k := by unfold z;positivity
  have castBound : (p:ℤ)^a ≤ |F k*(W (q^d):ℤ)-((p:ℤ)-1)*G k*(σ 1 (q^d):ℤ)| := by
    zify at bound
    rw [f,g] at bound
    simpa [mul_assoc] using bound
  have pos1 : 0≤F k*(W (q^d):ℤ) := mul_nonneg dy.2.1.le (by positivity)
  have pos2 : 0≤((p:ℤ)-1)*G k*(σ 1 (q^d):ℤ) :=
    mul_nonneg (mul_nonneg (by omega) dy.1.le) (by positivity)
  have direct : |F k*(W (q^d):ℤ)-((p:ℤ)-1)*G k*(σ 1 (q^d):ℤ)| ≤
      F k*(W (q^d):ℤ)+((p:ℤ)-1)*G k*(σ 1 (q^d):ℤ) := by
    apply abs_le.mpr;omega
  have v₁ := mul_le_mul dy.2.2.1 first (by positivity) (mul_nonneg (by positivity) dy.1.le)
  have OMA.WeightVal245212.val := mul_le_mul_of_nonneg_left second (mul_nonneg (by omega : (0:ℤ)≤p-1) dy.1.le)
  have cG := mul_le_mul_of_nonneg_right gz (by positivity : 0≤2*((d:ℤ)+1)*(k+1+p)*q^d)
  have gain : 0≤(2*(d:ℤ)*p+2)*G k*q^d := mul_nonneg (mul_nonneg (by positivity) dy.1.le) (by positivity)
  have result : (p:ℤ)^a ≤ 2*((d:ℤ)+1)*z k*(k+1+p)*q^d := by
    nlinarith only [castBound,direct,v₁,OMA.WeightVal245212.val,cG,gain]
  unfold z at result
  exact_mod_cast result
end OMA.ComplementaryBase245212
end
section
namespace OMA.ComplementarySize245212
theorem absorb {b d : ℕ} (big : 16*(d+1)^2≤b) : b^(2*d)≤2^b := by
  let s := b.sqrt
  have sl : (4*(d+1)) ≤ s := Nat.le_sqrt'.mpr (by nlinarith only [big])
  have slo : s^2≤b := Nat.sqrt_le' b
  have shi : b<(s+1)^2 := Nat.lt_succ_sqrt' b
  have bas : b≤2^(2*s) := calc
    _ ≤ 2*s^2+1 := by
      nlinarith only [shi, Nat.mul_le_mul_left s (show 2 ≤ s by omega)]
    _ ≤ _ := Nat.two_mul_sq_add_one_le_two_pow_two_mul s
  calc
    _ ≤ (2^(2*s))^(2*d) := Nat.pow_le_pow_left bas _
    _ = _ := (pow_mul _ _ _).symm
    _ ≤ 2^b := Nat.pow_le_pow_right (by decide)
      (by nlinarith only [slo,Nat.mul_le_mul_left s sl])
theorem exponents {a d K : ℕ} (hK : 1≤K)
    (power : 2^(a-1)≤2^(16*(d+1)^2)*(2^K)^(d+1)*(a+1)^d*K^(3*d+1)) :
    a+1≤64*(d+1)^2*K := by
  by_cases big : 16*(d+1)^2≤a+1
  · let X := 16*(d+1)^2 + K*(d+1) + K*(3*d+1)
    have scale : K≤(2:ℕ)^K := (Nat.lt_pow_self (by decide : 1<2)).le
    have idpow : 2^X = (2^(16*(d+1)^2)*(2^K)^(d+1))*(2^K)^(3*d+1) := by
      dsimp [X]
      rw [pow_add (2:ℕ) (16*(d+1)^2+K*(d+1)) (K*(3*d+1)),
        pow_add (2:ℕ) (16*(d+1)^2) (K*(d+1)),pow_mul (2:ℕ) K (d+1),
        pow_mul (2:ℕ) K (3*d+1)]
    have input : 2^(a-1)≤2^X*(a+1)^d := calc
      _ ≤ _ := power
      _ ≤ 2^(16*(d+1)^2)*(2^K)^(d+1)*(a+1)^d*(2^K)^(3*d+1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left scale _)
      _ = _ := by
        rw [idpow]
        exact mul_right_comm _ _ _
    have hh := Nat.pow_le_pow_left input 2
    rw [←pow_mul,mul_pow,←pow_mul,←pow_mul] at hh
    have v := Nat.mul_le_mul_left (2^(X*2)) (absorb big)
    rw [Nat.mul_comm 2 d] at v
    rw [←pow_add] at v
    have hb := (pow_le_pow_iff_right₀ (a:=(2:ℕ)) (by decide)).mp (hh.trans v)
    dsimp [X] at hb
    have al : 1≤a := by nlinarith only [big, Nat.zero_le d, Nat.zero_le (d^2)]
    have cut := Nat.sub_add_cancel al
    nlinarith only [hb,cut,
      Nat.mul_le_mul_right ((d+1)^2) hK,
      Nat.zero_le (K*d),Nat.zero_le (K*d^2),hK]
  · nlinarith only [Nat.lt_of_not_ge big, Nat.mul_le_mul_right ((d+1)^2) hK]
end OMA.ComplementarySize245212
end
section
namespace OMA.ComplementaryExp245212
open scoped ArithmeticFunction.sigma
private theorem constant (d : ℕ) :
    4*(d+1)*(150*(d+1))^d ≤ 2^(16*(d+1)^2) := by
  let h := d+1
  have hpos : 1≤h := by dsimp [h];omega
  have small : h≤(2:ℕ)^h := (Nat.lt_pow_self (by decide : 1<2)).le
  have first : 4*h≤2^(3*h) := calc
    _ ≤ 2^2*2^h := Nat.mul_le_mul_left _ small
    _ = _ := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have second : 150*h≤2^(9*h) := calc
    _ ≤ 2^8*2^h := Nat.mul_le_mul (by decide : 150≤(2:ℕ)^8) small
    _ = _ := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have prod := Nat.mul_le_mul first (Nat.pow_le_pow_left second d)
  rw [←pow_mul,←pow_add] at prod
  exact prod.trans (Nat.pow_le_pow_right (by decide) (by dsimp [h];nlinarith only [Nat.zero_le d,Nat.zero_le (d^2)]))
private theorem generic {p q a d K : ℕ} (hp : 2≤p) (ha : 2≤a) (hK : 1≤K)
    (small : p≤5*K ∨ q≤5*K)
    (power : p^a≤2*(d+1)*2^K*(K+p)*q^d)
    (alt : p^a≤2*2^K*(d+1)*K ∨ q≤6*(d+1)*K*(a+1)*2^K*p^2) :
    a+1≤64*(d+1)^2*K := by
  let h:=d+1
  let z:ℕ:=2^K
  let b:=a+1
  have hpos : 1≤h := by dsimp [h];omega
  have bpos : 1≤b := by dsimp [b];omega
  have zpos : 1≤z := Nat.one_le_pow _ _ (by decide : 0<2)
  have zmore : z≤z^h := by simpa using (Nat.pow_le_pow_right zpos hpos)
  have kmore : K≤K^(3*d+1) := by simpa using
    (Nat.pow_le_pow_right hK (show 1≤3*d+1 by omega))
  have Ccap : 4*h*(150*h)^d≤2^(16*h^2) := constant d
  have one : 1≤(150*h)^d := Nat.one_le_pow _ _ (by omega)
  have C₁ : 2*h≤2^(16*h^2) := (show 2*h≤4*h*(150*h)^d by
    nlinarith only [Nat.mul_le_mul_left (4*h) one]).trans Ccap
  have pa : 2^(a-1)≤p^a := (Nat.pow_le_pow_left hp _).trans
    (Nat.pow_le_pow_right (by omega) (Nat.sub_le a 1))
  apply OMA.ComplementarySize245212.exponents hK
  change 2^(a-1)≤2^(16*h^2)*z^h*b^d*K^(3*d+1)
  by_cases direct : p^a≤2*z*h*K
  · have scale := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul C₁ zmore)
      (Nat.one_le_pow d b bpos)) kmore
    exact (pa.trans direct).trans (by nlinarith only [scale])
  · have qlim : q≤150*h*z*b*K^3 := by
      rcases small with pSmall | qSmall
      · have cap := alt.resolve_left direct
        change q≤6*h*K*b*z*p^2 at cap
        have sq := Nat.pow_le_pow_left pSmall 2
        have w := Nat.mul_le_mul_left (6*h*K*b*z) sq
        nlinarith only [cap,w]
      · have z5 : 5≤150*h*z*b*K^2 := calc
          _ ≤ (150*h)*1*1*1 := by omega
          _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ zpos) bpos)
            (Nat.one_le_pow _ _ hK)
        nlinarith only [qSmall,Nat.mul_le_mul_left K z5]
    have kp : K+p≤2*K*p := by
      nlinarith only [Nat.mul_le_mul_right p hK,Nat.mul_le_mul_left K (show 1≤p by omega)]
    have hpow := Nat.mul_le_mul (Nat.mul_le_mul_left (2*h*z) kp) (Nat.pow_le_pow_left qlim d)
    have sub : p^(a-1)*p=p^a := by rw [←pow_succ]; congr 1;omega
    have canceled : p^(a-1)≤4*h*z*K*(150*h*z*b*K^3)^d := by
      apply Nat.le_of_mul_le_mul_right ?_ (by omega : 0<p)
      rw [sub]
      change p^a≤2*h*z*(K+p)*q^d at power
      nlinarith only [power,hpow]
    have exactfactor : 4*h*z*K*(150*h*z*b*K^3)^d =
       (4*h*(150*h)^d)*z^h*b^d*K^(3*d+1) := by
      dsimp [h];rw [pow_succ z d,pow_succ K (3*d), pow_mul K 3 d]
      simp only [mul_pow];ring
    rw [exactfactor] at canceled
    exact ((Nat.pow_le_pow_left hp (a-1)).trans canceled).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ Ccap)))
theorem exponent {p q k a d : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q)
    (pq : p≠q) (hd : 1≤d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    a+1≤64*(d+1)^2*(k+1) := by
  by_cases ha : 2≤a
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
    have many : 5≤(a+1)*(d+1+1) := by
      nlinarith only [ha,Nat.zero_le d,Nat.zero_le (a*d)]
    exact generic (by omega) ha (by omega) (OMA.ComplementaryBase245212.small_prime hp hq op oq pq many eqn)
      (OMA.ComplementaryBase245212.cofactor hp hq op oq pq eqn)
      (OMA.ComplementaryPole245212.alternative hp hq op oq pq a d k ha eqn)
  · nlinarith only [ha,Nat.zero_le d,Nat.zero_le (d^2),Nat.zero_le k,
      Nat.zero_le (k*d),Nat.zero_le (k*d^2)]
end OMA.ComplementaryExp245212
end
section
namespace OMA.ComplementaryFar245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryPole245212 OMA.ComplementaryLocal245212
open scoped ArithmeticFunction.sigma
private theorem round {k : ℕ} {p b h P W S : ℤ} (hp : 3≤p) (hb : 3≤b) (hh : 2≤h) (hP : 0<P)
    (w : (p-1)^2*W=p*(b*(p-1)-1)*P+1) (s : (p-1)*S=p*P-1)
    (plus : 0<den k b h P W S) (gc : 4*((k:ℤ)+1)*h*b*p≤G k)
    (pc : 4*h*((k:ℤ)+1)≤P) : G k*P≤2*(p-1)^2*den k b h P W S := by
  let u:=p-1
  let L:=h*b*u^2+(k:ℤ)*h*(p-b*u)-p*u
  let D:=den k b h P W S
  change G k*P≤2*u^2*D
  have up : 0<u := by dsimp [u];omega
  have kp : (0:ℤ)<k+1 := by positivity
  have bp : 0<b*u-p := by
    dsimp [u];nlinarith only [hp,hb,mul_nonneg (show 0≤b-3 by omega) (show 0≤p-1 by omega)]
  have gp := (dyad k).1
  have fg : F k=(k:ℤ)*G k+(k+1) := by dsimp [F,G];ring
  have iden : u^2*D=P*G k*L-P*(k+1)*h*(b*u-p)-(h*F k-G k*u) := by
    dsimp [L,D,den,u];rw [fg]
    linear_combination -h*((k:ℤ)*G k+(k+1))*w-G k*(p-1)*s
  have lp : 0<L := by
    by_cases low : h*k≤u
    · have decomp : L=b*u*((h-1)*u)+(b*u-p)*(u-h*k) := by dsimp [L,u];ring
      rw [decomp]
      exact add_pos_of_pos_of_nonneg (mul_pos (mul_pos (by omega) up) (mul_pos (by omega) up))
        (mul_nonneg bp.le (by omega))
    · have ef : 0≤h*F k-G k*u := by
        rw [fg];nlinarith only [mul_nonneg gp.le (by omega : 0≤h*k-u),mul_nonneg (by omega : 0≤h) kp.le]
      have pl : 0<(P*G k)*L := by
        nlinarith only [iden,ef,mul_pos (sq_pos_of_pos up) plus,
          mul_nonneg (mul_nonneg (mul_nonneg hP.le kp.le) (by omega : 0≤h)) bp.le]
      exact pos_of_mul_pos_right pl (mul_nonneg hP.le gp.le)
  have PGL := mul_nonneg (mul_nonneg hP.le gp.le) (show 0≤L-1 by omega)
  have scaled := mul_le_mul_of_nonneg_left gc hP.le
  have other := mul_le_mul_of_nonneg_right pc gp.le
  have fcap := mul_le_mul_of_nonneg_left (dyad k).2.2.1 (by omega : 0≤h)
  have hu : b*u-p≤b*p := by dsimp [u];nlinarith only [hp,hb]
  have klein := mul_le_mul_of_nonneg_left hu
    (show (0:ℤ)≤P*(k+1)*h by positivity)
  nlinarith only [iden,PGL,scaled,other,fcap,klein,mul_nonneg gp.le up.le]
theorem far {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (ha : 2≤a) (hd : 1≤d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ))
    (gc : 4*(k+1)*(d+1)*(a+1)*p<2^(k+1)) (pc : 4*(d+1)*(k+1)≤p^a) :
    q≤6*(d+1)*(k+1)*(a+1)*p^2 := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
  let D:=den k (a+1) (e+2) ((p:ℤ)^a) (W (p^a)) (σ 1 (p^a))
  obtain ⟨dp,qu⟩ := tail hp hq op oq pq a e k eqn
  change 0<D at dp
  have gc' : 4*((k:ℤ)+1)*(e+2)*(a+1)*p≤G k := by
    have h : 4*((k:ℤ)+1)*(e+1+1)*(a+1)*p<(2:ℤ)^(k+1) := by exact_mod_cast gc
    dsimp [G,z];linarith only [h]
  have pc' : 4*((e:ℤ)+2)*(k+1)≤(p:ℤ)^a := by
    have h : 4*((e:ℤ)+1+1)*(k+1)≤(p:ℤ)^a := by exact_mod_cast pc
    linarith only [h]
  have m := moments hp a
  have r := round (show (3:ℤ)≤p by omega) (show (3:ℤ)≤a+1 by omega)
    (show (2:ℤ)≤e+2 by omega) (pow_pos (show (0:ℤ)<p by omega) a) m.2 m.1 dp gc' pc'
  change (q:ℤ)*D≤3*(e+2)*(k+1)*(a+1)*G k*(p:ℤ)^a at qu
  have qk : (q:ℤ)*(G k*(p:ℤ)^a)≤(6*(e+2)*(k+1)*(a+1)*((p:ℤ)-1)^2)*(G k*(p:ℤ)^a) := by
    nlinarith only [mul_le_mul_of_nonneg_left r (show (0:ℤ)≤q by positivity),
      mul_le_mul_of_nonneg_left qu (mul_nonneg (show (0:ℤ)≤2 by decide) (sq_nonneg ((p:ℤ)-1)))]
  have cap := (mul_le_mul_iff_left₀ (mul_pos (dyad k).1 (pow_pos (show (0:ℤ)<p by omega) a))).mp qk
  have sq : ((p:ℤ)-1)^2≤(p:ℤ)^2 := by nlinarith only [show (3:ℤ)≤p by omega]
  exact_mod_cast cap.trans (mul_le_mul_of_nonneg_left sq (by positivity))
end OMA.ComplementaryFar245212
end
section
namespace OMA.TwoOddEffectiveTable245212
def floorPrime (K m : ℕ) := max 3 (1+(K-1)*(m-1)/m)
def tail (K : ℕ) := decide (2^(37+3*K)*K^10*119^8 < (floorPrime K 119)^118)
def cell (K m : ℕ) : Bool :=
  let z := 2^K
  let g := z-1
  let R := (floorPrime K m)^(m-1)
  let h := 5*K
  let u := 64*m^2*K
  let t := m*u
  let exact := 3*g*h^2*(K*u+h)<R ∧ 3*g*(K+h^2)<R^2 ∧
    (3*g*(K*u+h))^(m-2)*(3*z*K*u)^2<R^(m-4)
  let y := 6*t*K*h^2
  let a := y^2*(K*u+h)+h^2*(K*u+y)
  let b := K+h*y
  decide (exact ∨ (2*(K*t*h*R+g*u*K)≤g*R ∧
    4*g*(a*R+b)+9*K*h^2*y^2*t*R^2<4*g*R^2))
def row (K : ℕ) := tail K && (List.range' 33 86).all (cell K)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked : (List.range' 3 253).all row = true := by decide +kernel
theorem ranges {K m : ℕ} (lo : 3 ≤ K) (hi : K ≤ 255) (ml : 33 ≤ m) (mh : m ≤ 118) :
    tail K=true ∧ cell K m=true := by
  have ok := List.all_eq_true.mp checked K (List.mem_range'_1.mpr ⟨lo,by omega⟩)
  simp only [row,Bool.and_eq_true] at ok
  exact ⟨ok.1,List.all_eq_true.mp ok.2 m (List.mem_range'_1.mpr ⟨ml,by omega⟩)⟩
end OMA.TwoOddEffectiveTable245212
end
section
namespace OMA.TwoOddParameters245212
open OMA.Smooth245212 OMA.ComplementaryLocal245212 OMA.ComplementaryPole245212 ArithmeticFunction
open scoped ArithmeticFunction.sigma
theorem cofactor {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (hd : 1≤d) (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    q^(d-1)≤3*2^(k+1)*(k+1)*(a+1)*p^a := by
  have eq' : OeisA245212.a (2^k*q^d*p^a)=(σ 1 (2^k*q^d*p^a):ℤ) := by rwa [mul_right_comm]
  have cap := OMA.ComplementaryBase245212.cofactor hq hp oq op pq.symm eq'
  have cq : 2*((k+1)+q)≤3*(k+1)*q := by
    nlinarith only [oq,Nat.mul_le_mul_left k oq]
  apply (mul_le_mul_iff_left₀ hq.pos).mp
  rw [←pow_succ,show d-1+1=d by omega]
  nlinarith only [cap,Nat.mul_le_mul_right ((a+1)*2^(k+1)*p^a) cq]
theorem reciprocal {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (ha : 1≤a) (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    k*a<(a+1)*p := by
  obtain ⟨e,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : a≠0)
  let B : ℤ := e+2
  let C : ℤ := d+1
  let P : ℤ := (p:ℤ)^(e+1)
  let Q : ℤ := (q:ℤ)^d
  let x : ℤ := (p:ℤ)^e
  let W0 : ℤ := W (p^(e+1))
  let V : ℤ := W (q^d)
  let S : ℤ := σ 1 (p^(e+1))
  let T : ℤ := σ 1 (q^d)
  have pp : (0:ℤ)<p := by omega
  have qq : (0:ℤ)<q := by omega
  have xp : 0<x := pow_pos pp _
  have qp : 0<Q := pow_pos qq _
  have cp : 0<C := by dsimp [C];positivity
  have bp : 0<B := by dsimp [B];positivity
  have px : P=x*p := by dsimp [P,x];rw [pow_succ]
  have first : B*P+((e:ℤ)+1)*x≤W0 := by
    dsimp [B,P,x,W0];rw [(last hp op e).1];push_cast
    have low : ((e:ℤ)+1)*(p:ℤ)^e≤W (p^e) := by exact_mod_cast (bounds hp op e).2.2.1
    linarith only [low]
  have second : C*Q≤V := by dsimp [C,Q,V];exact_mod_cast (bounds hq oq d).2.2.1
  have w0 : 0≤W0 := by dsimp [W0];positivity
  have pos (r t : ℕ) (prime : r.Prime) : (0:ℤ)<σ 1 (r^t) := by
    exact_mod_cast (show 0<σ 1 (r^t) by
      rw [sigma_one_apply_prime_pow prime]
      exact Finset.sum_pos (fun i _=>pow_pos prime.pos i) (by simp))
  have phy := physical hp hq (by omega) (by omega) pq (e+1) d k eqn
  change F k*W0*V+G k*S*T=z k*(k+1)*(e+1+1)*C*P*Q at phy
  have ar : ((e:ℤ)+1+1)=B := by dsimp [B];ring
  rw [←(dyad k).2.2.2, ar] at phy
  have prod := mul_le_mul first second (mul_pos cp qp).le w0
  have f : (k:ℤ)*G k≤F k := by dsimp [F,G];nlinarith only [show (0:ℤ)≤k by positivity]
  have up := mul_le_mul_of_nonneg_right f (mul_nonneg (mul_nonneg (by positivity : (0:ℤ)≤e+1) xp.le) (mul_pos cp qp).le)
  have g0 := (dyad k).1
  have st : 0<G k*S*T := mul_pos (mul_pos g0 (pos p (e+1) hp)) (pos q d hq)
  have fact : ((k:ℤ)*(e+1))*(G k*x*C*Q)<(B*p)*(G k*x*C*Q) := by
    rw [px] at phy prod
    nlinarith only [phy,mul_le_mul_of_nonneg_left prod (dyad k).2.1.le,up,st]
  have res := (mul_lt_mul_iff_left₀ (mul_pos (mul_pos (mul_pos g0 xp) cp) qp)).mp fact
  dsimp [B] at res;exact_mod_cast res
theorem floor {p q a d k m : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (ha : 1≤a) (hm : 1 ≤ m) (mb : m≤a+1)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    OMA.TwoOddEffectiveTable245212.floorPrime (k+1) m≤p := by
  have r := reciprocal hp hq op oq pq ha eqn
  unfold OMA.TwoOddEffectiveTable245212.floorPrime
  apply max_le op
  have lt : k*(m-1)<p*m := by
    by_contra! ge
    have sub := Nat.sub_add_cancel hm
    nlinarith only [Nat.mul_le_mul_left (a+1) ge,Nat.mul_lt_mul_of_pos_left r hm,
      Nat.mul_le_mul_left k mb,congrArg (fun x:ℕ=>k*(a+1)*x) sub]
  change 1+k*(m-1)/m≤p
  exact (Nat.div_lt_iff_lt_mul hm).mpr lt |> (by omega : _ → _)
end OMA.TwoOddParameters245212
end
section
namespace OMA.SmallLength245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryPole245212 OMA.ComplementaryLocal245212
open OMA.QuadraticPowerGap245212
open scoped ArithmeticFunction.sigma
open OMA.ComplementaryHeight245212 (gap)
theorem separated {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q)
    (pq : p≠q) (hd : 1≤d) (ha : 2*d+4≤a)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    A p (a+1) (((d:ℤ)+1)*q^d) (σ 1 (q^d)) ≠ (k:ℤ)*H p (a+1) (((d:ℤ)+1)*q^d) (W (q^d)) := by
  by_cases large : 2 ≤ d
  · exact OMA.ComplementaryNonres245212.original hp hq op oq pq large ha eqn
  have one : d=1 := by omega
  subst d
  have sw : (σ 1 q : ℤ) = q+1 := by
    have h := (last hq oq 0).2.1
    norm_num at h
    exact_mod_cast h
  have ww : (W q : ℤ) = 2*q+1 := by
    have h := last hq oq 0
    norm_num at h
    exact_mod_cast h.1
  have ac := OMA.ComplementaryNonres245212.cleared hp hq op oq pq eqn
  simp only [pow_one,Nat.cast_one,sw,ww] at ac ⊢
  have Aeq : A p (a+1) ((1+1)*q) (q+1) = OMA.LinearPowerGap245212.intercept p q (a+1) := by
    unfold A OMA.LinearPowerGap245212.intercept;ring
  have Heq : H p (a+1) ((1+1)*q) (2*q+1) = OMA.LinearPowerGap245212.slope p q (a+1) := by
    unfold H OMA.LinearPowerGap245212.slope;ring
  rw [Aeq,Heq] at ac ⊢
  exact OMA.LinearPowerGap245212.gap hp op oq (by omega) ac
theorem complement {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (hd : 1≤d) (ha : 2*d+4≤a)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    2^(k+1)≤1+2*(d+1)*(a+1)*(k+1)*p^2*q^d+
      6*(d+1)^2*(a+1)*(k+1+p)*(q^d)^2 := by
  let h : ℤ := (d:ℤ)+1
  let b : ℤ := (a:ℤ)+1
  let K : ℤ := (k:ℤ)+1
  let Q : ℤ := (q:ℤ)^d
  let P : ℤ := (p:ℤ)^a
  let U : ℤ := p-1
  let V : ℤ := W (q^d)
  let S : ℤ := σ 1 (q^d)
  let J : ℤ := h*Q
  let H0 := H p b J V
  let A0 := A p b J S
  have op' : (3:ℤ)≤p := by omega
  have oq' : (3:ℤ)≤q := by omega
  have pz : (0:ℤ)≤p := by omega
  have uz : 0≤U := by dsimp [U];omega
  have hh : 2≤h := by dsimp [h];omega
  have bh : 3≤b := by dsimp [b];omega
  have b0 : 0≤b := by omega
  have u : U≤(p:ℤ) := by dsimp [U];omega
  have ppos : 0<P := by dsimp [P];positivity
  have qp : 0<Q := by dsimp [Q];positivity
  have v0 : 0≤V := by dsimp [V];positivity
  have s0 : 0 ≤ S := by dsimp [S];positivity
  have j0 : 0≤J := by dsimp [J];positivity
  have bd := bounds hq oq d
  have jv : J≤V := by dsimp [J,V,h,Q];exact_mod_cast bd.2.2.1
  have vh : 2*V≤3*h*Q := by dsimp [V,h,Q];exact_mod_cast bd.2.1
  have sh : 2*S≤3*Q := by dsimp [S,Q];exact_mod_cast bd.1
  have bu : p≤b*U := by dsimp [U];nlinarith only [bh,op',mul_nonneg (show 0≤b-3 by omega) uz]
  have Hpos : 0≤H0 := by
    change 0≤b*U*(p*V-U*J)-p*V
    have id : b*U*(p*V-U*J)-p*V=(b*U-p)*V+b*U^2*(V-J) := by dsimp [U];ring
    rw [id];exact add_nonneg (mul_nonneg (sub_nonneg.mpr bu) v0)
      (mul_nonneg (mul_nonneg b0 (sq_nonneg _)) (sub_nonneg.mpr jv))
  have Hub : H0≤b*(p:ℤ)^2*V := by
    change b*U*(p*V-U*J)-p*V≤_
    nlinarith only [mul_nonneg (mul_nonneg b0 (sq_nonneg U)) j0,mul_nonneg pz v0,
      mul_le_mul_of_nonneg_right u (mul_nonneg (mul_nonneg b0 pz) v0)]
  have raw := OMA.ComplementaryNonres245212.cleared hp hq op oq pq eqn
  change P*(G k*(A0-k*H0)-K*H0)=G k*C p k V S+K*V at raw
  have clr : P*(G k*(A0-k*H0)-(k+1)*H0)=F k*V-G k*(p-1)*S := by
    dsimp only [K,C] at raw
    have fg : F k=(k:ℤ)*G k+(k+1) := by dsimp [F,G];ring
    rw [fg];linear_combination raw
  have nz : A0-k*H0≠0 := sub_ne_zero.mpr
    (separated hp hq op oq pq hd ha eqn)
  have lev := OMA.ComplementaryDyad245212.level hp hq op oq pq (by omega) eqn
  have zz : z k≤3*h*b*P*Q := by dsimp [z,h,b,P,Q];exact_mod_cast lev
  have lev' : G k≤P*(3*h*b*Q) := by dsimp [G];linarith only [zz]
  have g := OMA.ComplementaryHeight245212.gap ppos v0 s0 (by omega) Hpos nz clr lev'
  change G k≤K*H0+(3*h*b*Q)*(K*V+p*S) at g
  have vr : V≤2*h*Q := by nlinarith only [vh,mul_nonneg (by omega : 0≤h) qp.le]
  have sr : S≤2*h*Q := by nlinarith only [sh,mul_nonneg (show 0≤h-1 by omega) qp.le,qp.le]
  have Hcap := Hub.trans (mul_le_mul_of_nonneg_left vr (mul_nonneg b0 (sq_nonneg _)))
  have Fcap := mul_le_mul_of_nonneg_left Hcap (by dsimp [K];positivity : 0≤K)
  have Ecap : K*V+p*S≤2*h*(K+p)*Q := by
    nlinarith only [mul_le_mul_of_nonneg_left vr (by dsimp [K];positivity : 0≤K),mul_le_mul_of_nonneg_left sr pz]
  have Rcap := mul_le_mul_of_nonneg_left Ecap (show 0≤3*h*b*Q by positivity)
  have result : z k≤1+2*h*b*K*p^2*Q+6*h^2*b*(K+p)*Q^2 := by
    dsimp only [G] at g
    nlinarith only [g,Rcap,Fcap]
  dsimp only [z,h,b,K,Q] at result
  exact_mod_cast result
end OMA.SmallLength245212
end
section
namespace OMA.ComplementaryBox245212
open scoped ArithmeticFunction.sigma
theorem room (d : ℕ) :
    10000*(d+1)^4*5^d≤2^(16*(d+1)^2) := by
  by_cases hd : d=0
  · subst d;decide
  have h : d+1≤2^(d+1) := (Nat.lt_pow_self (by decide : 1<2)).le
  have f : 5^d≤(2^3)^d := Nat.pow_le_pow_left (by decide) d
  have full := Nat.mul_le_mul (Nat.mul_le_mul (show 10000≤(2:ℕ)^14 by decide)
    (Nat.pow_le_pow_left h 4)) f
  rw [←pow_mul,←pow_mul,←pow_add,←pow_add] at full
  exact full.trans (Nat.pow_le_pow_right (by decide) (by nlinarith only [show 1≤d by omega,Nat.zero_le (d^2)]))
theorem box {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (ha : 2≤a) (hd : 2≤d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ))
    (large : (2^(16*(d+1)^2)*(k+1)^(d+3))^(d+1)<2^(k+1)) :
    let B:=2^(16*(d+1)^2)*(k+1)^(d+2)
    p≤B ∧ q≤B ∧ a+1≤B ∧ k+1≤B := by
  let h:=d+1
  let K:=k+1
  let b:=a+1
  let E:ℕ:=2^(16*h^2)
  let B:=E*K^(d+2)
  let D:=E*K^(d+3)
  change p≤B ∧ q≤B ∧ b≤B ∧ K≤B
  change D^h<2^K at large
  have hK : 1≤K := by dsimp [K];omega
  have hh : 3≤h := by dsimp [h];omega
  have he : 1≤E := Nat.one_le_pow _ _ (by decide)
  have hD : 1≤D := Nat.mul_pos he (Nat.one_le_pow _ _ hK)
  have pr : D<2^K := (show D≤D^h by simpa using
    (Nat.pow_le_pow_right hD (show 1≤h by omega))).trans_lt large
  have BD : B≤D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hK (by omega))
  have hb : b≤64*h^2*K := OMA.ComplementaryExp245212.exponent hp hq op oq pq (by omega) eqn
  have room' : 10000*h^4*5^d≤E := room d
  have h34 : h^3≤h^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have h24 : h^2≤h^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have h₄ : 10000*h^4≤E := (show 10000*h^4≤10000*h^4*5^d by
    simpa using (Nat.mul_le_mul_left (10000*h^4) (Nat.one_le_pow d 5 (by decide)))).trans room'
  have c₃ {x : ℕ} (hx : x≤10000) : x*h^3≤E := (Nat.mul_le_mul hx h34).trans h₄
  have cov {v w : ℕ} (u : v≤E) (g : w≤d+2) : v*K^w≤B :=
    Nat.mul_le_mul u (Nat.pow_le_pow_right hK g)
  have ek : 5*K≤B := by
    have five : 5≤E := (show 5≤10000*h^4 from (show 5≤10000*1 by decide).trans
      (Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega)))).trans h₄
    simpa using (cov five (show 1≤d+2 by omega))
  have bB : b≤B := hb.trans (by
    simpa using cov ((Nat.mul_le_mul (show 64≤10000 by decide) h24).trans h₄) (show 1≤d+2 by omega))
  have many : 5≤(a+1)*(d+1) := by nlinarith only [ha,hd,Nat.zero_le (a*d)]
  have bases := OMA.ComplementaryBase245212.small_prime hp hq op oq pq many eqn
  change p≤5*K ∨ q≤5*K at bases
  refine ⟨?_,?_,bB,(show K≤5*K by omega).trans ek⟩
  · rcases bases with h | hqK
    · exact h.trans ek
    have grow : 6*b*K*h*q^d≤B := calc
      _ ≤ 6*(64*h^2*K)*K*h*(5*K)^d := by gcongr
      _ = (384*h^3*5^d)*K^(d+2) := by rw [mul_pow,pow_add (m:=d) (n:=2)];ring
      _ ≤ _ := cov ((Nat.mul_le_mul_right _ (Nat.mul_le_mul (show 384≤10000 by decide) h34)).trans room') (by omega)
    have cut : K*(a+1)*(d+1)*q^d<2^K := by
      change K*b*h*q^d<2^K
      exact (show K*b*h*q^d≤6*b*K*h*q^d by nlinarith only [Nat.zero_le (b*K*h*q^d)]).trans_lt
        (grow.trans_lt (BD.trans_lt pr))
    have swap : OeisA245212.a (2^k*q^d*p^a)=(σ 1 (2^k*q^d*p^a):ℤ) := by
      rwa [mul_right_comm]
    exact (OMA.ComplementaryDyad245212.near hq hp oq op pq.symm (by omega) swap cut).trans grow
  · rcases bases with hpK | h
    · have gc : 4*K*h*b*p<2^K := calc
        _ ≤ 4*K*h*(64*h^2*K)*(5*K) := by gcongr
        _ = (1280*h^3)*K^3 := by ring
        _ ≤ B := cov (c₃ (by decide)) (by omega)
        _ < _ := BD.trans_lt pr
      have pc : 4*h*K≤p^a := by
        by_contra! smaller
        have low := OMA.ComplementaryDyad245212.power_floor hp hq op oq pq (by omega) eqn
        change 2^K≤(6*h*K*b*p^a)^h at low
        have scale : 6*h*K*b*p^a≤D := calc
          _ ≤ 6*h*K*(64*h^2*K)*(4*h*K) := by gcongr
          _ = (1536*h^4)*K^3 := by ring
          _ ≤ B := cov ((Nat.mul_le_mul_right _ (show 1536≤10000 by decide)).trans h₄) (by omega)
          _ ≤ D := BD
        exact (not_lt_of_ge (low.trans (Nat.pow_le_pow_left scale h))) large
      apply (OMA.ComplementaryFar245212.far hp hq op oq pq ha (by omega) eqn gc pc).trans
      change 6*h*K*b*p^2≤B
      calc
        _ ≤ 6*h*K*(64*h^2*K)*(5*K)^2 := by gcongr
        _ = (9600*h^3)*K^4 := by ring
        _ ≤ _ := cov (c₃ (by decide)) (by omega)
    · exact h.trans ek
end OMA.ComplementaryBox245212
end
section
namespace OMA.ComplementaryCut245212
open scoped ArithmeticFunction.sigma
private theorem scalar {h K : ℕ} (hh : 3≤h)
    (growth : 2^K≤2^(16*h^2*(2*h+2))*K^((h+1)*(2*h+1))) :
    K≤512*h^4 := by
  let T:=16*h^2*(2*h+2)
  let s:=(h+1)*(2*h+1)
  let t:=K.sqrt
  change 2^K≤2^T*K^s at growth
  by_contra! wide
  have hs : s≤4*h^2 := by
    dsimp [s];nlinarith only [hh,Nat.mul_le_mul_left h hh]
  have tbound : 2*T≤512*h^4 := by
    dsimp [T]
    have h34:=Nat.pow_le_pow_right (show 1≤h by omega) (show 3≤4 by decide)
    have h24:=Nat.pow_le_pow_right (show 1≤h by omega) (show 2≤4 by decide)
    nlinarith only [h34,h24,Nat.zero_le (h^4)]
  have ss : 4*s≤t := Nat.le_sqrt'.mpr (calc
    (4*s)^2 ≤ (4*(4*h^2))^2 := Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hs) _
    _ ≤ 512*h^4 := by nlinarith only [Nat.zero_le (h^4)]
    _ ≤ K := wide.le)
  have tt : t^2≤K := Nat.sqrt_le' K
  have tt' : K<(t+1)^2 := Nat.lt_succ_sqrt' K
  have two : 2≤t := by dsimp [s] at ss;nlinarith only [ss,hh,Nat.zero_le (h^2)]
  have pk : K≤2^(2*t) := calc
    _ ≤ 2*t^2+1 := by nlinarith only [tt',Nat.mul_le_mul_left t two]
    _ ≤ _ := Nat.two_mul_sq_add_one_le_two_pow_two_mul t
  have powers := growth.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left pk s))
  rw [←pow_mul,←pow_add] at powers
  have rem := (pow_le_pow_iff_right₀ (a:=(2:ℕ)) (by decide)).mp powers
  nlinarith only [rem,tt,Nat.mul_le_mul_left t ss,wide,tbound]
theorem large {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (hd : 2≤d) (ha : 2*d+4≤a)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    k+1≤512*(d+1)^4 := by
  let h:=d+1
  let K:=k+1
  let E:ℕ:=2^(16*h^2)
  let B:=E*K^(d+2)
  let D:=E*K^(d+3)
  let s:=(h+1)*(2*h+1)
  let T:=16*h^2*(2*h+2)
  have hK : 1≤K := by dsimp [K];omega
  have hh : 3≤h := by dsimp [h];omega
  have he : 1≤E := Nat.one_le_pow _ _ (by decide)
  apply scalar hh
  change 2^K≤2^T*K^s
  by_cases small : 2^K≤D^h
  · have comp : E^h≤2^T := by
      dsimp [E,T];rw [←pow_mul]
      apply Nat.pow_le_pow_right (by decide)
      exact Nat.mul_le_mul_left _ (by omega)
    have kcomp : K^((d+3)*h)≤K^s := Nat.pow_le_pow_right hK (by
      dsimp [s,h];nlinarith only [Nat.zero_le d,Nat.zero_le (d^2)])
    change 2^K≤(E*K^(d+3))^h at small
    rw [mul_pow,←pow_mul K (d+3) h] at small
    exact small.trans (Nat.mul_le_mul comp kcomp)
  · obtain ⟨pb,qb,ab,kb⟩:=OMA.ComplementaryBox245212.box hp hq op oq pq (by omega) hd eqn (lt_of_not_ge small)
    have bound := OMA.ComplementaryHeight245212.height hp hq op oq pq hd ha pb qb ab kb eqn
    change 2^K≤16*h^2*B^(2*d+3) at bound
    have initial : 16*h^2≤E := (Nat.lt_pow_self (by decide : 1<2)).le
    have eqE : E*E^(2*d+3)=2^T := by
      rw [←pow_succ'];dsimp [E,T,h];rw [←pow_mul];congr 2
    have eqK : (K^(d+2))^(2*d+3)=K^s := by dsimp [s,h];rw [←pow_mul];congr 1
    dsimp only [B] at bound
    rw [mul_pow,eqK,←mul_assoc] at bound
    exact bound.trans (Nat.mul_le_mul_right _ ((Nat.mul_le_mul_right _ initial).trans_eq eqE))
end OMA.ComplementaryCut245212
end
section
namespace OMA.DivisorEnvelope245212
open Finset
private lemma div_cast {m d : ℕ} (hd : d ∈ m.divisors) :
    ((m/d : ℕ) : ℚ) = (m:ℚ)/d := by
  exact Nat.cast_div (Nat.mem_divisors.mp hd).1 (by
    exact_mod_cast (Nat.pos_of_mem_divisors hd).ne')
theorem egyptian {m : ℕ} (hm : 0 < m) (c : ℚ)
    (balance : ((m:ℚ)*m.divisors.card - ∑ d ∈ m.divisors, (d:ℚ)) =
      c*((∑ d ∈ m.divisors, (d:ℚ)*d.divisors.card)-(m:ℚ)*m.divisors.card)) :
    (m.divisors.card:ℚ)-1 =
      ∑ d ∈ m.divisors.erase 1, (c*((m/d).divisors.card:ℚ)+1)/d := by
  let w (d : ℕ) := (d:ℚ)*(c*d.divisors.card+1)
  have comp := Nat.sum_div_divisors m w
  have id' : ∑ d ∈ m.divisors, (c*((m/d).divisors.card:ℚ)+1)/d =
      (∑ d ∈ m.divisors, w d)/m := by
    rw [←comp, Finset.sum_div]
    refine sum_congr rfl fun d hd => ?_
    dsimp [w]
    rw [div_cast hd]
    field_simp
  have one := Nat.one_mem_divisors.mpr hm.ne'
  have erase := Finset.sum_erase_add _ (fun d : ℕ => (c*((m/d).divisors.card:ℚ)+1)/d) one
  simp only [Nat.div_one,Nat.cast_one,div_one] at erase
  dsimp [w] at id'
  simp_rw [mul_add,mul_one,mul_left_comm (_:ℚ) c] at id'
  rw [sum_add_distrib,←mul_sum] at id'
  have id'' := (eq_div_iff (by exact_mod_cast hm.ne' : (m:ℚ)≠0)).1 id'
  rw [←erase] at id''
  apply (mul_right_cancel₀ (by exact_mod_cast hm.ne' : (m:ℚ) ≠ 0))
  linear_combination balance - id''
theorem gap {b t : ℕ} (hb : 0<b) (s : Finset ℕ) (u : ℕ → ℕ)
    (den : ∀ d ∈ s, d∣b) (pos : ∀ d ∈ s, 0<d)
    (lt : (∑ d ∈ s, (u d : ℚ)/d) < t) :
    1/(b:ℚ) ≤ t-∑ d ∈ s, (u d : ℚ)/d := by
  let v := ∑ d ∈ s, u d*(b/d)
  have id' : ((∑ d ∈ s, (u d:ℚ)/d)*(b:ℚ)) = (v:ℚ) := by
    dsimp [v]
    push_cast
    rw [sum_mul]
    refine sum_congr rfl fun d hd => ?_
    rw [Nat.cast_div (den d hd) (by exact_mod_cast (pos d hd).ne')]
    ring
  have bl : (0:ℚ)<b := by exact_mod_cast hb
  have h := mul_lt_mul_of_pos_right lt bl
  rw [id'] at h
  have hn : v < t*b := by exact_mod_cast h
  have step : (v:ℚ)+1 ≤ (t:ℚ)*b := by exact_mod_cast hn
  apply (div_le_iff₀ bl).2
  rw [sub_mul,id']
  linarith
theorem truncated {s : Finset ℕ} (nonempty : s.Nonempty) {u : ℕ → ℕ}
    {t a b P y : ℕ} (hb : 0<b) (hp : 0<P)
    (count : s.card≤t) (hpos : ∀ d∈s, 0<d)
    (wu : ∀ d∈s, 0<u d ∧ u d≤t) (tail : ∀ d∈s, ¬d∣b → P≤d)
    {δ : ℚ} (hδ : 0<δ)
    (target : (y:ℚ) = ∑ d∈s, (((a:ℚ)+δ)*u d+1)/d) :
    1/(b:ℚ) ≤ t*(δ*t+(((a:ℚ)+δ)*t+1)/P) := by
  classical
  let F := s.filter (· ∣ b)
  let v (d : ℕ) : ℚ := if d∣b then ((a*u d+1:ℕ):ℚ)/d else 0
  let w (d : ℕ) : ℚ := (((a:ℚ)+δ)*u d+1)/d
  have cut : ∑ d∈s, v d = ∑ d∈F, ((a*u d+1:ℕ):ℚ)/d := by
    simp [v,F,sum_filter]
  have diff (d : ℕ) (hd : d∈s) :
      0<w d-v d ∧ w d-v d≤δ*t+(((a:ℚ)+δ)*t+1)/P := by
    have dp : (0:ℚ)<d := by exact_mod_cast hpos d hd
    have one : (1:ℚ)≤d := by exact_mod_cast hpos d hd
    have up : (0:ℚ)<u d := by exact_mod_cast (wu d hd).1
    have ut : (u d:ℚ)≤t := by exact_mod_cast (wu d hd).2
    have pp : (0:ℚ)<P := by exact_mod_cast hp
    dsimp [w,v]
    by_cases dd : d∣b
    · rw [if_pos dd]
      push_cast
      rw [←sub_div,show ((a:ℚ)+δ)*u d+1-(a*u d+1)=δ*u d by ring]
      constructor
      · positivity
      · calc
          _ ≤ δ*u d := div_le_self (by positivity) one
          _ ≤ δ*t := by gcongr
          _ ≤ _ := le_add_of_nonneg_right (by positivity)
    · rw [if_neg dd,sub_zero]
      constructor
      · positivity
      · have pd : (P:ℚ)≤d := by exact_mod_cast tail d hd dd
        calc
          _ ≤ (((a:ℚ)+δ)*t+1)/P := by gcongr
          _ ≤ _ := le_add_of_nonneg_left (by positivity)
  have strict : (∑ d∈F, ((a*u d+1:ℕ):ℚ)/d) < y := by
    rw [←cut,target]
    exact sum_lt_sum_of_nonempty nonempty (fun d hd => sub_pos.mp (diff d hd).1)
  have lower := gap hb F (fun d => a*u d+1)
    (fun d hd => (mem_filter.mp hd).2)
    (fun d hd => hpos d (mem_filter.mp hd).1) strict
  rw [←cut,target,←sum_sub_distrib] at lower
  calc
    _ ≤ ∑ d∈s, (w d-v d) := lower
    _ ≤ ∑ _d∈s, (δ*t+(((a:ℚ)+δ)*t+1)/P) := sum_le_sum fun d hd => (diff d hd).2
    _ ≤ _ := by simp only [sum_const,nsmul_eq_mul]; gcongr
end OMA.DivisorEnvelope245212
end
section
section
namespace OMA.DivisorHeight245212
open Finset Nat ArithmeticFunction OMA.Smooth245212 OMA.DivisorEnvelope245212
open scoped ArithmeticFunction.sigma
private theorem dyadic_moments (a : ℕ) :
    W (2^a) = a*2^(a+1)+1 ∧ σ 1 (2^a)+1 = 2^(a+1) := by
  rw [w_pow Nat.prime_two,sigma_one_apply_prime_pow Nat.prime_two]
  induction a with
  | zero => norm_num
  | succ a ih =>
    rw [sum_range_succ (fun j => 2^j*(j+1)) (a+1),
      sum_range_succ (fun j => 2^j) (a+1),ih.1,pow_succ (2:ℕ) (a+1)]
    constructor <;> nlinarith only [ih.2]
theorem identity {a m : ℕ} (odd : Odd m)
    (eqn : OeisA245212.a (2^a*m)=(σ 1 (2^a*m):ℤ)) :
    (m.divisors.card:ℚ)-1 = ∑ d∈m.divisors.erase 1,
      (((a:ℚ)+((a:ℚ)+1)/(2^(a+1)-1))*(m/d).divisors.card+1)/d := by
  apply egyptian odd.pos
  have cp := (Nat.coprime_two_left.mpr odd).pow_left a
  have natBal := OMA.Abundance245212.balance (mul_ne_zero (pow_ne_zero _ (by decide)) odd.pos.ne') eqn
  rw [w_mult.map_mul_of_coprime cp,isMultiplicative_sigma.map_mul_of_coprime cp,
    isMultiplicative_sigma.map_mul_of_coprime cp,sigma_zero_apply_prime_pow Nat.prime_two,
    (dyadic_moments a).1] at natBal
  have bal := congrArg (Nat.cast : ℕ → ℚ) natBal
  have geom := congrArg (Nat.cast : ℕ → ℚ) (dyadic_moments a).2
  push_cast at bal geom
  rw [sigma_zero_apply,w_apply,sigma_one_apply (n:=m)] at bal
  push_cast at bal
  have dp : 1 < (2:ℚ)^(a+1) := one_lt_pow₀ (by norm_num) (by omega)
  field_simp [sub_ne_zero.mpr dp.ne']
  rw [pow_succ (2:ℚ) a] at bal geom ⊢
  linear_combination -bal + geom * (∑ d ∈ m.divisors, (d:ℚ))
private theorem tail_cut {m d : ℕ} (hd : d∈m.divisors) {s : Finset ℕ}
    (support : d.primeFactors ⊆ s) :
    d ∣ ∏ p∈s, p^m.factorization p := by
  have dz := (Nat.pos_of_mem_divisors hd).ne'
  obtain ⟨div,mz⟩ := Nat.mem_divisors.mp hd
  trans ∏ p∈d.primeFactors, p^m.factorization p
  · nth_rw 1 [Nat.prod_primeFactors_pow_factorization dz]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun p _ =>
      pow_dvd_pow _ ((Nat.factorization_le_iff_dvd dz mz).mpr div p)
  · exact Finset.prod_dvd_prod_of_subset _ _ _ support
private def core (m : ℕ) (s : Finset ℕ) := ∏ p∈s,p^m.factorization p
private theorem prefix_pos {m : ℕ} {s : Finset ℕ} (ss : s ⊆ m.primeFactors) :
    0 < core m s :=
  Finset.prod_pos fun _ h => Nat.pow_pos (Nat.prime_of_mem_primeFactors (ss h)).pos
private theorem prime_bootstrap {m B H : ℕ} (mp : 0 < m)
    (step : ∀ s ⊆ m.primeFactors, ∀ P : ℕ, 0<P →
      (∀ p∈m.primeFactors \ s,P≤p) → B≤H*core m s ∨ P≤H*core m s) :
    B≤H^m.divisors.card := by
  classical
  let M := m.primeFactors
  let t (r : Finset ℕ) := ∏ p∈r,(m.factorization p+1)
  have aux (r : Finset ℕ) (sub : r⊆M) :
      B≤(H*core m (M\r))^(t r) := by
    induction r using Finset.strongInductionOn with | _ r ih =>
    let s := M\r
    have ss : s ⊆ M := sdiff_subset
    have rem : M\s=r := by ext x; simp [s]; grind
    have hr : 0<t r := prod_pos fun _ _ => Nat.succ_pos _
    by_cases done : B≤H*core m s
    · exact done.trans (Nat.le_self_pow hr.ne' _)
    by_cases ne : r.Nonempty
    · let p := r.min' ne
      have pr : p ∈ r := min'_mem _ _
      have ps : p ∉ s := fun h => (mem_sdiff.mp h).2 pr
      have subset := (erase_subset p r).trans sub
      have key := (step s ss p (Nat.prime_of_mem_primeFactors (sub pr)).pos
        (by rw [rem]; exact fun q hq => min'_le _ _ hq)).resolve_left done
      have insert_eq : M\(r.erase p)=insert p s := by
        ext x; simp [s]; grind
      have up : H*core m (M\(r.erase p)) ≤ (H*core m s)^(m.factorization p+1) := by
        rw [insert_eq,core,prod_insert ps,pow_succ']
        change H*(p^m.factorization p*core m s) ≤ _
        rw [show H*(p^m.factorization p*core m s)=(H*core m s)*p^m.factorization p by ring]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left key _)
      have rest := ih (r.erase p) (erase_ssubset pr) subset
      apply rest.trans ((Nat.pow_le_pow_left up _).trans_eq ?_)
      rw [←pow_mul]
      congr 1
      exact mul_prod_erase r (fun q => m.factorization q+1) pr
    · have z := step s ss (H*core m s+1) (by omega) (by
        change ∀ p∈M\s,_
        simp [rem,not_nonempty_iff_eq_empty.mp ne])
      omega
  simpa [M,t,core,Nat.card_divisors mp.ne'] using aux M (Subset.rfl)
private theorem tail_prime {m P : ℕ} {s : Finset ℕ} (hP : ∀ p∈m.primeFactors\s,P≤p)
    {d : ℕ} (hd : d∈m.divisors) (nd : ¬d∣core m s) : P≤d := by
  by_contra! small
  apply nd (tail_cut hd ?_)
  intro p h
  by_contra out
  have hm := Nat.primeFactors_mono (Nat.mem_divisors.mp hd).1 (Nat.mem_divisors.mp hd).2 h
  exact small.not_ge ((hP p (mem_sdiff.mpr ⟨hm,out⟩)).trans (Nat.le_of_mem_primeFactors h))
private theorem counts {m d : ℕ} (hd : d ∈ m.divisors) :
    0 < (m/d).divisors.card ∧ (m/d).divisors.card ≤ m.divisors.card := by
  obtain ⟨dv,mz⟩ := Nat.mem_divisors.mp hd
  have prod := Nat.div_mul_cancel dv
  have nz : m/d≠0 := by intro h; simp [h] at prod; exact mz prod.symm
  exact ⟨card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr nz⟩,
    card_le_card (Nat.divisors_subset_of_dvd mz (Nat.div_dvd_of_dvd dv))⟩
private theorem dyadic_step {a t b P : ℕ} (ht : 0<t) (hb : 0<b)
    {δ : ℚ} (δ1 : δ≤1) (δ2 : δ≤((a:ℚ)+1)/2^a)
    (lower : 1/(b:ℚ) ≤ t*(δ*t+(((a:ℚ)+δ)*t+1)/P)) :
    2^a≤4*(a+2)*t^2*b ∨ P≤4*(a+2)*t^2*b := by
  by_contra! both
  let L : ℚ := 4*(a+2:ℚ)*t^2*b
  have bp : (0:ℚ)<b := by exact_mod_cast hb
  have tp : (0:ℚ)<t := by exact_mod_cast ht
  have t1 : (1:ℚ)≤t := by exact_mod_cast ht
  have lp : 0<L := by dsimp [L]; positivity
  have ll : L≤(2:ℚ)^a := by dsimp [L]; exact_mod_cast both.1.le
  have pl : L≤(P:ℚ) := by dsimp [L]; exact_mod_cast both.2.le
  have δ3 : δ≤((a:ℚ)+1)/L := δ2.trans (by gcongr)
  have z : t*(δ*t+(((a:ℚ)+δ)*t+1)/P) ≤
      t*((((a:ℚ)+1)/L)*t+(((a:ℚ)+1)*t+1)/L) := by gcongr
  have strict : (t:ℚ)*((((a:ℚ)+1)/L)*t+(((a:ℚ)+1)*t+1)/L) < 1/b := by
    field_simp [lp.ne',bp.ne']
    dsimp [L]
    have posat : 0≤(a:ℚ)*t := by positivity
    nlinarith only [mul_pos tp bp, mul_nonneg (sub_nonneg.mpr t1) (mul_pos tp bp).le,
      mul_nonneg posat (mul_pos tp bp).le]
  exact (lower.trans z).not_gt strict
theorem dyadic_height {a m : ℕ} (odd : Odd m) (hm : 1 < m)
    (eqn : OeisA245212.a (2^a*m)=(σ 1 (2^a*m):ℤ)) :
    2^a≤(4*(a+2)*m.divisors.card^2)^m.divisors.card := by
  let t := m.divisors.card
  have tp : 0<t := card_pos.mpr ⟨m,Nat.mem_divisors_self _ odd.pos.ne'⟩
  apply prime_bootstrap odd.pos
  intro s ss P pp hP
  let δ : ℚ := ((a:ℚ)+1)/(2^(a+1)-1)
  have b := prefix_pos ss
  have power : (1:ℚ)≤2^a := one_le_pow₀ (by norm_num)
  have z : (0:ℚ)<2^(a+1)-1 := by rw [pow_succ]; linarith
  have δ1 : δ≤1 := by
    apply (div_le_iff₀ z).mpr
    have grow := (a+1).lt_two_pow_self
    have aux : a+1+1≤2^(a+1) := grow
    have q : (a:ℚ)+1+1≤2^(a+1) := by exact_mod_cast aux
    linarith
  have δ2 : δ≤((a:ℚ)+1)/2^a := by
    dsimp [δ]; gcongr
    rw [pow_succ]; linarith
  have en : (m.divisors.erase 1).Nonempty := ⟨m,mem_erase.mpr ⟨by omega,Nat.mem_divisors_self _ odd.pos.ne'⟩⟩
  have iden := identity odd eqn
  have target : ((t-1:ℕ):ℚ) = ∑ d∈m.divisors.erase 1,
      (((a:ℚ)+δ)*(m/d).divisors.card+1)/d := by
    rw [Nat.cast_sub (by omega : 1≤t)]
    exact iden
  exact dyadic_step tp b δ1 δ2 (truncated en b pp (card_le_card (erase_subset _ _))
    (fun _ h => Nat.pos_of_mem_divisors (mem_of_mem_erase h))
    (fun _ h => counts (mem_of_mem_erase h)) (fun _ h => tail_prime hP (mem_of_mem_erase h))
    (div_pos (by positivity) z) target)
theorem exponent_cutoff {a t : ℕ} (ht : 0<t) (h : 2^a≤(4*(a+2)*t^2)^t) :
    a<t*(2*Nat.log 2 (8*t^3)+2) := by
  let x := a/t
  have lo : x*t≤a := Nat.div_mul_le_self _ _
  have hi : a<(x+1)*t := by
    have rem := Nat.mod_lt a ht
    have eqn := Nat.mod_add_div a t
    dsimp [x]; nlinarith only [rem,eqn]
  have top : a+2≤(x+2)*t := by nlinarith only [hi,ht]
  have base : 2^x≤4*(a+2)*t^2 := by
    apply (Nat.pow_le_pow_iff_left ht.ne').mp
    rw [←pow_mul]; exact (Nat.pow_le_pow_right (by decide) lo).trans h
  have scale : 2*2^x≤8*(x+2)*t^3 := by
    have b := Nat.mul_le_mul_right (4*t^2) top
    nlinarith only [base,b]
  have half : x+2 ≤ 2*2^(x-x/2) := by
    have f := (x-x/2).lt_two_pow_self
    omega
  have hhalf := Nat.mul_le_mul_left (2^(x/2)) half
  rw [show 2^(x/2)*(2*2^(x-x/2))=2*2^x by
    rw [←Nat.mul_assoc,Nat.mul_comm (2^(x/2)) 2,Nat.mul_assoc,←pow_add]
    rw [Nat.add_sub_of_le (Nat.div_le_self x 2)]] at hhalf
  have cap : 2^(x/2)≤8*t^3 := by
    apply (mul_le_mul_iff_left₀ (Nat.succ_pos (x+1))).mp
    nlinarith only [hhalf,scale]
  have logBound := Nat.le_log_of_pow_le (by decide : 1<2) cap
  apply hi.trans_le
  rw [Nat.mul_comm]
  exact Nat.mul_le_mul_left t (by omega)
private theorem exact_cut {s : Finset ℕ} {w : ℕ → ℕ} {y b P t M : ℕ}
    (bp : 0<b) (pp : 0<P) (card : s.card≤t) (ds : ∀ d∈s,0<d)
    (ws : ∀ d∈s,0<w d ∧ w d≤M) (tail : ∀ d∈s,¬d∣b → P≤d)
    (idn : (y:ℚ)=∑ d∈s,(w d:ℚ)/d) :
    (∀ d∈s,d∣b) ∨ P≤b*t*M := by
  classical
  by_cases all : ∀ d∈s,d∣b
  · exact Or.inl all
  right
  push Not at all
  obtain ⟨d,hd,nd⟩ := all
  let f := s.filter (·∣b)
  let r := s\f
  have inside := filter_subset (fun d => d∣b) s
  have rest : ∀ i∈r,i∈s ∧ ¬i∣b := by
    intro i h
    obtain ⟨hs,hf⟩ := mem_sdiff.mp h
    exact ⟨hs,fun dv => hf (mem_filter.mpr ⟨hs,dv⟩)⟩
  have positive : 0<∑ i∈r,(w i:ℚ)/i := by
    apply sum_pos' (fun _ _ => by positivity)
    exact ⟨d,mem_sdiff.mpr ⟨hd,fun h => nd (mem_filter.mp h).2⟩,
      div_pos (by exact_mod_cast (ws d hd).1) (by exact_mod_cast ds d hd)⟩
  have split := sum_sdiff inside (f:=fun i => (w i:ℚ)/i)
  change (∑ i∈r,(w i:ℚ)/i)+(∑ i∈f,(w i:ℚ)/i)=_ at split
  rw [←idn] at split
  have lower := gap bp f w (fun i h => (mem_filter.mp h).2)
    (fun i h => ds i (mem_filter.mp h).1) (show (∑ i∈f,(w i:ℚ)/i)<y by linarith)
  have upper : (∑ i∈r,(w i:ℚ)/i) ≤ t*((M:ℚ)/P) := by
    calc
      _ ≤ ∑ _i∈r,(M:ℚ)/P := by
        apply sum_le_sum; intro i hi
        obtain ⟨si,ni⟩ := rest i hi
        have pe : (P:ℚ) ≤ i := by exact_mod_cast tail i si ni
        have wp : (w i:ℚ)≤M := by exact_mod_cast (ws i si).2
        gcongr
      _ ≤ _ := by
        simp only [sum_const,nsmul_eq_mul]
        gcongr
        exact (card_le_card (sdiff_subset : r⊆s)).trans card
  have le : 1/(b:ℚ) ≤ t*((M:ℚ)/P) := by linarith
  have bq : 0<(b:ℚ) := by exact_mod_cast bp
  have pq : 0<(P:ℚ) := by exact_mod_cast pp
  field_simp at le
  exact_mod_cast (show (P:ℚ) ≤ b*t*M by linarith only [le])
theorem odd_height {a m : ℕ} (odd : Odd m) (hm : 1 < m)
    (eqn : OeisA245212.a (2^a*m)=(σ 1 (2^a*m):ℤ)) :
    m≤((2^(a+1)-1)*(a+2)*m.divisors.card^2)^(m.divisors.card-1) := by
  let t := m.divisors.card
  let z : ℕ := 2^(a+1)-1
  let K := z*(a+2)*t^2
  let u (d : ℕ) := (m/d).divisors.card
  let w (d : ℕ) := (a*z+(a+1))*u d+z
  have tpos : 0<t := card_pos.mpr ⟨m,Nat.mem_divisors_self _ odd.pos.ne'⟩
  have grow := (a+1).lt_two_pow_self
  have az : a+1≤z := by dsimp [z]; omega
  have zp : 0<z := by omega
  have kp : 0<K := by dsimp only [K]; positivity
  have castz : (z:ℚ)=2^(a+1)-1 := by
    dsimp [z]; rw [Nat.cast_sub (by omega : 1≤(2:ℕ)^(a+1))]; push_cast; rfl
  have zq : (z:ℚ)≠0 := by exact_mod_cast zp.ne'
  have target : (((t-1)*z:ℕ):ℚ)=∑ d∈m.divisors.erase 1,(w d:ℚ)/d := by
    have idn := identity odd eqn
    rw [←castz] at idn
    push_cast [Nat.cast_sub (by omega : 1≤t)]
    rw [show (t:ℚ)-1=(m.divisors.card:ℚ)-1 from rfl,idn,sum_mul]
    apply sum_congr rfl
    intro d hd
    dsimp only [w,u]
    push_cast
    field_simp
  have cap : K*m≤K^t := by
    apply prime_bootstrap odd.pos
    intro s ss P pp hP
    have ww (d : ℕ) (h : d∈m.divisors.erase 1) : 0<w d ∧ w d≤z*(a+2)*t := by
      have c := (counts (mem_of_mem_erase h)).2
      change u d≤t at c
      constructor
      · dsimp [w]; positivity
      · calc
          w d ≤ (a*z+z)*t+z := by dsimp [w]; gcongr
          _ ≤ z*(a+2)*t := by
            have bz := Nat.mul_le_mul_left z (show 1≤t from tpos)
            nlinarith only [bz]
    rcases exact_cut (prefix_pos ss) pp (card_le_card (erase_subset _ _ ) : (m.divisors.erase 1).card≤t)
      (fun d h => Nat.pos_of_mem_divisors (mem_of_mem_erase h)) ww
      (fun d h => tail_prime hP (mem_of_mem_erase h)) target with all|bound
    · left; apply Nat.mul_le_mul_left
      exact Nat.le_of_dvd (prefix_pos ss) (all m (mem_erase.mpr ⟨by omega,Nat.mem_divisors_self _ odd.pos.ne'⟩))
    · right; apply bound.trans_eq; dsimp [K]; ring
  have eqt : t=(t-1)+1 := by omega
  rw [eqt] at cap
  rw [pow_succ'] at cap
  exact (mul_le_mul_iff_right₀ kp).mp cap
def exponentLimit (t : ℕ) := t*(2*Nat.log 2 (8*t^3)+2)
def coreLimit (t : ℕ) :=
  ((2^(exponentLimit t+1)-1)*(exponentLimit t+2)*t^2)^(t-1)
theorem effective_box {a m : ℕ} (odd : Odd m) (hm : 1 < m)
    (eqn : OeisA245212.a (2^a*m)=(σ 1 (2^a*m):ℤ)) :
    a<exponentLimit m.divisors.card ∧ m≤coreLimit m.divisors.card := by
  have ht : 0 < m.divisors.card := card_pos.mpr ⟨m,Nat.mem_divisors_self _ odd.pos.ne'⟩
  have ka := exponent_cutoff ht (dyadic_height odd hm eqn)
  refine ⟨ka,(odd_height odd hm eqn).trans ?_⟩
  dsimp only [coreLimit]
  gcongr <;> first | exact ka.le | decide
end OMA.DivisorHeight245212
end
section
namespace OMA.ComplementarySmall245212
open ArithmeticFunction
open scoped ArithmeticFunction.sigma
private theorem limit {t h : ℕ} (hh : 3≤h) (ht : t≤16*h^3) :
    OMA.DivisorHeight245212.exponentLimit t≤512*h^4 := by
  have he : h≤2^h := (Nat.lt_pow_self (by decide : 1<2)).le
  have base : 8*t^3≤2^(15+9*h) := calc
    _ ≤ 8*(16*(2^h)^3)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (ht.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left he 3))) 3)
    _ = _ := by rw [pow_add, Nat.mul_comm 9 h, pow_mul]; ring
  have log := Nat.log_mono_right (b:=2) base
  rw [Nat.log_pow (by decide)] at log
  unfold OMA.DivisorHeight245212.exponentLimit
  have full := Nat.mul_le_mul ht (show 2*Nat.log 2 (8*t^3)+2≤32+18*h by omega)
  nlinarith only [full,Nat.mul_le_mul_left (h^3) hh]
theorem small {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (oq : 3≤q) (pq : p≠q) (hd : 2≤d) (sm : a+1≤16*(d+1)^2)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    k+1≤512*(d+1)^4 := by
  have odd := ((hp.odd_of_ne_two (by omega)).pow (n:=a)).mul
    ((hq.odd_of_ne_two (by omega)).pow (n:=d))
  have big := Nat.one_lt_pow (by omega : d≠0) hq.one_lt
  have first := Nat.one_le_pow a p hp.pos
  have size : 1<p^a*q^d := by nlinarith only [big,Nat.mul_le_mul_right (q^d) first]
  rw [mul_assoc] at eqn
  have core := (OMA.DivisorHeight245212.effective_box odd size eqn).1
  have cp := (((Nat.coprime_primes hp hq).mpr pq).pow_left a).pow_right d
  have card : (p^a*q^d).divisors.card=(a+1)*(d+1) := by
    rw [←sigma_zero_apply,isMultiplicative_sigma.map_mul_of_coprime cp,
      sigma_zero_apply_prime_pow hp,sigma_zero_apply_prime_pow hq]
  rw [card] at core
  exact (show k+1≤_ from core).trans (limit (by omega)
    (by nlinarith only [Nat.mul_le_mul_right (d+1) sm]))
end OMA.ComplementarySmall245212
end
section
namespace OMA.ComplementaryFinish245212
open ArithmeticFunction OMA.DivisorHeight245212
open scoped ArithmeticFunction.sigma
theorem exponents {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (hd : 2≤d) (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    k+1≤512*(d+1)^4 ∧ a+1≤32768*(d+1)^6 := by
  have cut : k+1≤512*(d+1)^4 := by
    by_cases lo : a+1≤16*(d+1)^2
    · exact OMA.ComplementarySmall245212.small hp hq op oq pq hd lo eqn
    · exact OMA.ComplementaryCut245212.large hp hq op oq pq hd
        (by nlinarith only [Nat.lt_of_not_ge lo,hd,Nat.zero_le (d^2)]) eqn
  have cap := OMA.ComplementaryExp245212.exponent hp hq op oq pq (by omega) eqn
  exact ⟨cut,cap.trans (by nlinarith only [Nat.mul_le_mul_left (64*(d+1)^2) cut])⟩
end OMA.ComplementaryFinish245212
end
end
section
namespace OMA.SmallCaps245212
open scoped ArithmeticFunction.sigma
def smallCore (d a p q _K b : ℕ) := 3*(d+1)*b*p^a*q^d
def highCore (d p q K b : ℕ) := 1+2*(d+1)*b*K*p^2*q^d+
    6*(d+1)^2*b*(K+p)*(q^d)^2
def caps (d l t : ℕ) (few reversed : Bool) : Bool :=
  let h:=d+1
  let z:=2^(min l 4096)
  let b:=if few then 2*d+4 else 64*h^2*t
  let s:=5*t
  let (test,p,q):=if reversed then
    (decide (t*b*h*s^d<z),6*b*t*h*s^d,s)
    else (decide (4*t*h*b*s<z ∧ (6*h*t*b*(4*h*t))^h<z),s,6*h*t*b*s^2)
  test && decide ((if few then smallCore d (2*d+3) p q t b else highCore d p q t b)<z)
theorem retain {p q a d k l t : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (oq : 3≤q) (pq : p≠q) (hd : 2≤d) (order : d≤a)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ))
    (lk : l≤k+1) (hk : k+1≤t) :
    caps d l t (decide (a<2*d+4)) (decide (q<p))=false := by
  let h:=d+1
  let K:=k+1
  let z:ℕ:=2^(min l 4096)
  let b:=if a<2*d+4 then 2*d+4 else 64*h^2*t
  let s:=5*t
  have kz : z≤2^K := Nat.pow_le_pow_right (by decide) ((min_le_left _ _).trans lk)
  have ba : a+1≤b := by
    dsimp only [b];split
    · omega
    · exact (OMA.ComplementaryExp245212.exponent hp hq op oq pq (by omega) eqn).trans
        (Nat.mul_le_mul_left _ hk)
  have many : 5≤(a+1)*(d+1) := by nlinarith only [hd,order,Nat.zero_le (a*d)]
  have small := OMA.ComplementaryBase245212.small_prime hp hq op oq pq many eqn
  have flip : OeisA245212.a (2^k*q^d*p^a)=(σ 1 (2^k*q^d*p^a):ℤ) := by rwa [mul_right_comm]
  have denial (P Q : ℕ) (pmax : p≤P) (qmax : q≤Q) :
      ¬ (if a<2*d+4 then smallCore d (2*d+3) P Q t b else highCore d P Q t b)<z := by
    apply not_lt_of_ge
    apply kz.trans
    split
    · rename_i low
      apply (OMA.ComplementaryDyad245212.level hp hq op oq pq (by omega) eqn).trans
      unfold smallCore
      gcongr <;> omega
    · rename_i high
      apply (OMA.SmallLength245212.complement hp hq op oq pq (by omega) (by omega) eqn).trans
      unfold highCore
      gcongr
  by_contra! yes
  have yes' : caps d l t (decide (a<2*d+4)) (decide (q<p))=true := by simpa using yes
  unfold caps at yes'
  by_cases rev : q<p
  · simp only [if_pos rev,Bool.and_eq_true,decide_eq_true_eq] at yes'
    change t*b*h*s^d<z ∧ _ at yes'
    have qs : q ≤ s := by dsimp [s];omega
    have lim : K*(a+1)*h*q^d<2^K := calc
      _ ≤ t*b*h*s^d := by gcongr
      _ < _ := yes'.1
      _ ≤ _ := kz
    have ps : p≤6*b*t*h*s^d := (OMA.ComplementaryDyad245212.near hq hp oq op pq.symm (by omega) flip lim).trans
      (by change 6*(a+1)*K*h*q^d≤_;gcongr)
    exact denial _ _ ps qs yes'.2
  · simp only [if_neg rev,Bool.and_eq_true,decide_eq_true_eq] at yes'
    change (4*t*h*b*s<z ∧ (6*h*t*b*(4*h*t))^h<z) ∧ _ at yes'
    have ps : p ≤ s := by dsimp [s];omega
    have gc : 4*K*h*(a+1)*p<2^K := calc
      _ ≤ 4*t*h*b*s := by gcongr
      _ < _ := yes'.1.1
      _ ≤ _ := kz
    have pc : 4*h*K≤p^a := by
      by_contra! low
      have pow := OMA.ComplementaryDyad245212.power_floor hp hq op oq pq (by omega) eqn
      change 2^K≤(6*h*K*(a+1)*p^a)^h at pow
      have cmp : (6*h*K*(a+1)*p^a)^h≤(6*h*t*b*(4*h*t))^h := by
        gcongr
        exact low.le.trans (Nat.mul_le_mul_left _ hk)
      exact (not_lt_of_ge (kz.trans (pow.trans cmp))) yes'.1.2
    have qs : q≤6*h*t*b*s^2 :=
      (OMA.ComplementaryFar245212.far hp hq op oq pq (by omega) (by omega) eqn gc pc).trans
        (by change 6*h*K*(a+1)*p^2≤_;gcongr)
    exact denial _ _ ps qs yes'.2
def search : ℕ → ℕ → ℕ → ℕ → Bool → Bool → Bool
  | 0,_,_,_,_,_ => false
  | n+1,d,l,t,f,r =>
    if caps d l t f r then true else
    let mid:=(l+t)/2
    search n d l mid f r && search n d (mid+1) t f r
theorem stays {K d : ℕ} {f r : Bool}
    (keep : ∀ l t, l≤K → K≤t → caps d l t f r=false)
    (n l t : ℕ) (lt : l≤K) (ut : K≤t) : search n d l t f r=false := by
  induction n generalizing l t with
  | zero => rfl
  | succ n ih =>
    rw [search,keep l t lt ut];simp only [Bool.false_eq_true,↓reduceIte]
    by_cases lower : K≤(l+t)/2
    · simp [ih l _ lt lower]
    · simp [ih ((l+t)/2+1) t (by omega) ut]
def ceiling (d : ℕ) (few reversed : Bool) :=
  match d,few,reversed with
  | 2,false,false => 230 | 2,false,true => 137 | 2,true,false => 138 | 2,true,true => 280
  | 3,false,false => 354 | 3,false,true => 174 | 3,true,false => 203 | 3,true,true => 497
  | _,false,false => 485 | _,false,true => 212 | _,true,false => 271 | _,true,true => 779
set_option maxRecDepth 4096 in
set_option maxHeartbeats 16000000 in
private theorem checked {d : ℕ} (lo : 2≤d) (hi : d≤4) (f r : Bool) :
    search 32 d (ceiling d f r+1) (512*(d+1)^4) f r=true := by
  interval_cases d <;> cases f <;> cases r <;> decide +kernel
theorem dyadic {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (oq : 3≤q) (pq : p≠q) (hd : 2≤d) (small : d≤4) (order : d≤a)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    k+1≤ceiling d (decide (a<2*d+4)) (decide (q<p)) := by
  by_contra! big
  have upper := (OMA.ComplementaryFinish245212.exponents hp hq op oq pq hd eqn).1
  have ok := checked hd small (decide (a<2*d+4)) (decide (q<p))
  have no := stays (fun l t => retain hp hq op oq pq hd order eqn (l:=l) (t:=t))
    32 (ceiling d (decide (a<2*d+4)) (decide (q<p))+1) _ big upper
  grind
end OMA.SmallCaps245212
end
section
namespace OMA.OddBox245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryLocal245212 OMA.ComplementaryPole245212
open scoped ArithmeticFunction.sigma
theorem ratio {K G F u D E S T W V : ℤ} (u12 : 12≤u) (gg : 0<G)
    (ff : 0<F) (kg : F≤K*G) (dd : 0<D) (ee : 0<E)
    (wl : D≤W) (vl : E≤V) (wu : u*W≤(u+1)*D) (vu : u*V≤(u+1)*E)
    (ss : 16*S*T≤D*E) (eqn : F*W*V+G*S*T=(F+G)*D*E) : 4*u<9*K := by
  have ww := mul_le_mul wu vu (mul_nonneg (by omega) (ee.le.trans vl))
    (mul_nonneg (by omega) dd.le)
  have sur := mul_le_mul wl vl ee.le (dd.le.trans wl)
  have wz : 0≤W*V-D*E := sub_nonneg.mpr sur
  have upper : u^2*(W*V-D*E)≤(2*u+1)*D*E := by nlinarith only [ww]
  have fst : 15*G*D*E≤16*F*(W*V-D*E) := by
    nlinarith only [eqn,mul_le_mul_of_nonneg_left ss gg.le]
  have limit : (15*u^2)*(G*D*E)≤(16*K*(2*u+1))*(G*D*E) := by
    nlinarith only [mul_le_mul_of_nonneg_left fst (sq_nonneg u),
      mul_le_mul_of_nonneg_left upper (show 0≤16*F by omega),
      mul_le_mul_of_nonneg_right kg (show 0≤16*(2*u+1)*D*E by positivity)]
  have cap := (mul_le_mul_iff_left₀ (mul_pos (mul_pos gg dd) ee)).mp limit
  have kp : 0<K := pos_of_mul_pos_left (ff.trans_le kg) gg.le
  have bound : (180*u)*u≤(400*K)*u := by
    nlinarith only [cap,mul_le_mul_of_nonneg_left (show 12*(2*u+1)≤25*u by omega) (show 0≤16*K by omega)]
  have := (mul_le_mul_iff_left₀ (show 0<u by omega)).mp bound
  omega
theorem prime_bound {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 13≤p)
    (pq : p<q) (ha : 5≤a) (hd : 5≤d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    4*(p-1)<9*(k+1) := by
  let P : ℤ := (p:ℤ)^a
  let Q : ℤ := (q:ℤ)^d
  let D : ℤ := (a+1)*P
  let E : ℤ := (d+1)*Q
  let W : ℤ := OMA.Smooth245212.W (p^a)
  let V : ℤ := OMA.Smooth245212.W (q^d)
  let S : ℤ := σ 1 (p^a)
  let T : ℤ := σ 1 (q^d)
  let u : ℤ := (p:ℤ)-1
  let v : ℤ := (q:ℤ)-1
  have up : 12≤u := by dsimp [u];omega
  have uv : u≤v := by dsimp [u,v];omega
  have pw := OMA.PrimePowerDiv245212.weighted hp a
  have qw := OMA.PrimePowerDiv245212.weighted hq d
  zify [Nat.cast_sub hp.pos] at pw
  zify [Nat.cast_sub hq.pos] at qw
  change u*W+S=(p:ℤ)*D at pw
  change v*V+T=(q:ℤ)*E at qw
  have wl : D≤W := by dsimp [D,P,W];exact_mod_cast (bounds hp (by omega) a).2.2.1
  have vl : E≤V := by dsimp [E,Q,V];exact_mod_cast (bounds hq (by omega) d).2.2.1
  have ss : 2*S≤3*P := by dsimp [S,P];exact_mod_cast (bounds hp (by omega) a).1
  have tt : 2*T≤3*Q := by dsimp [T,Q];exact_mod_cast (bounds hq (by omega) d).1
  have s0 : 0 ≤ S := by dsimp [S];positivity
  have t0 : 0≤T := by dsimp [T];positivity
  have p0 : 0<P := by dsimp [P];positivity
  have q0 : 0<Q := pow_pos (by omega : (0:ℤ)<q) _
  have vu : u*V≤(u+1)*E := by
    have scale := mul_le_mul_of_nonneg_right uv (sub_nonneg.mpr vl)
    dsimp only [v] at qw scale
    nlinarith only [scale,qw,t0]
  have st := mul_le_mul ss tt (by positivity : 0≤2*T) (by positivity : 0≤3*P)
  have bc := mul_le_mul (show (6:ℤ)≤a+1 by omega) (show (6:ℤ)≤d+1 by omega) (by decide) (by positivity)
  have sm : 16*S*T≤D*E := by dsimp only [D,E];nlinarith only [st,mul_le_mul_of_nonneg_right bc (mul_nonneg p0.le q0.le)]
  have eq := physical hp hq (by omega) (by omega) pq.ne a d k eqn
  change F k*W*V+G k*S*T=z k*(k+1)*(a+1)*(d+1)*P*Q at eq
  rw [←(dyad k).2.2.2] at eq
  have r := ratio up (dyad k).1 (dyad k).2.1 (dyad k).2.2.1
    (by dsimp [D];positivity : 0<D) (by dsimp [E];positivity : 0<E) wl vl
    (by dsimp [u] at pw ⊢;nlinarith only [pw,s0]) vu sm (by dsimp [D,E];linear_combination eq)
  dsimp only [u] at r;zify [Nat.cast_sub hp.pos];exact r
theorem prime_window {p q a d k kl kh bl pl ph : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 13≤p) (pq : p<q) (ha : 5≤a) (hd : 5≤d) (lk : kl≤k+1) (uk : k+1≤kh)
    (lb : 1≤bl) (ba : bl≤a+1) (plp : pl≤p) (php : p≤ph)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    lowPrime kl bl pl≤p ∧ p≤highPrime kh ph ∧ lowPrime kl bl pl+2≤q := by
  have lo := OMA.TwoOddParameters245212.floor hp hq (by omega) (by omega) pq.ne (by omega) lb ba eqn
  unfold OMA.TwoOddEffectiveTable245212.floorPrime at lo
  have le : (kl-1)*(bl-1)/bl≤k*(bl-1)/bl :=
    Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega))
  obtain ⟨i,po⟩ := hp.odd_of_ne_two (by omega)
  obtain ⟨j,qo⟩ := hq.odd_of_ne_two (by omega)
  have small : lowPrime kl bl pl≤p := by
    unfold lowPrime
    simp only [Nat.add_sub_cancel] at lo
    generalize h : max 13 (max pl (1+(kl-1)*(bl-1)/bl))=b
    have b0 : b≤p := by rw [←h];omega
    change b+(1-b%2)≤p
    omega
  have pb := prime_bound hp hq op pq ha hd eqn
  exact ⟨small,by unfold highPrime;omega,by omega⟩
end OMA.OddBox245212
end
section
namespace OMA.SmallFacts245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryLocal245212 OMA.ComplementaryPole245212
open OMA.OddBox245212 (ratio)
open scoped ArithmeticFunction.sigma
private theorem ordered {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 13≤p)
    (pq : p<q) (bc : 36≤(a+1)*(d+1))
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    4*(p-1)<9*(k+1) := by
  let P : ℤ := (p:ℤ)^a
  let Q : ℤ := (q:ℤ)^d
  let D : ℤ := (a+1)*P
  let E : ℤ := (d+1)*Q
  let W : ℤ := OMA.Smooth245212.W (p^a)
  let V : ℤ := OMA.Smooth245212.W (q^d)
  let S : ℤ := σ 1 (p^a)
  let T : ℤ := σ 1 (q^d)
  let u : ℤ := (p:ℤ)-1
  let v : ℤ := (q:ℤ)-1
  have up : 12≤u := by dsimp [u];omega
  have uv : u≤v := by dsimp [u,v];omega
  have pw := OMA.PrimePowerDiv245212.weighted hp a
  have qw := OMA.PrimePowerDiv245212.weighted hq d
  zify [Nat.cast_sub hp.pos] at pw
  zify [Nat.cast_sub hq.pos] at qw
  change u*W+S=(p:ℤ)*D at pw
  change v*V+T=(q:ℤ)*E at qw
  have wl : D≤W := by dsimp [D,P,W];exact_mod_cast (bounds hp (by omega) a).2.2.1
  have vl : E≤V := by dsimp [E,Q,V];exact_mod_cast (bounds hq (by omega) d).2.2.1
  have ss : 2*S≤3*P := by dsimp [S,P];exact_mod_cast (bounds hp (by omega) a).1
  have tt : 2*T≤3*Q := by dsimp [T,Q];exact_mod_cast (bounds hq (by omega) d).1
  have s0 : 0 ≤ S := by dsimp [S];positivity
  have t0 : 0≤T := by dsimp [T];positivity
  have p0 : 0<P := by dsimp [P];positivity
  have q0 : 0<Q := pow_pos (by omega : (0:ℤ)<q) _
  have vu : u*V≤(u+1)*E := by
    have scale := mul_le_mul_of_nonneg_right uv (sub_nonneg.mpr vl)
    dsimp only [v] at qw scale
    nlinarith only [scale,qw,t0]
  have st := mul_le_mul ss tt (by positivity : 0≤2*T) (by positivity : 0≤3*P)
  have bc : (36:ℤ) ≤ ((a:ℤ)+1)*(d+1) := by exact_mod_cast bc
  have sm : 16*S*T≤D*E := by dsimp only [D,E];nlinarith only [st,mul_le_mul_of_nonneg_right bc (mul_nonneg p0.le q0.le)]
  have eq := physical hp hq (by omega) (by omega) pq.ne a d k eqn
  change F k*W*V+G k*S*T=z k*(k+1)*(a+1)*(d+1)*P*Q at eq
  rw [←(dyad k).2.2.2] at eq
  have r := OMA.OddBox245212.ratio up (dyad k).1 (dyad k).2.1 (dyad k).2.2.1
    (by dsimp [D];positivity : 0<D) (by dsimp [E];positivity : 0<E) wl vl
    (by dsimp [u] at pw ⊢;nlinarith only [pw,s0]) vu sm (by dsimp [D,E];linear_combination eq)
  dsimp only [u] at r;zify [Nat.cast_sub hp.pos];exact r
theorem either {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (pq : p≠q)
    (op : 13 ≤ min p q) (bc : 36≤(a+1)*(d+1))
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    4*(min p q-1)<9*(k+1) := by
  rcases lt_or_gt_of_ne pq with h|h
  · rw [min_eq_left h.le];exact ordered hp hq (op.trans (min_le_left ..)) h bc eqn
  · rw [min_eq_right h.le]
    exact ordered hq hp (op.trans (min_le_right ..)) h (by rwa [Nat.mul_comm])
      (by rwa [mul_right_comm])
theorem square_factors {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (oq : 3≤q) (pq : p≠q) (ea : Even a) (ed : Even d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) : 4∣a := by
  obtain ⟨e,rfl⟩:=ea
  obtain ⟨s,rfl⟩:=ed
  let u:=p^e*q^s
  have ue : p^(e+e)*q^(s+s)=u^2 := by dsimp [u];rw [mul_pow,←pow_mul,←pow_mul];congr 2 <;> omega
  have ou := ((hp.odd_of_ne_two (by omega)).pow (n:=e)).mul ((hq.odd_of_ne_two (by omega)).pow (n:=s))
  rw [mul_assoc,ue] at eqn
  obtain ⟨v,hv⟩:=OMA.DyadicPower245212.square_root_is_square ou eqn
  have notq : ¬p∣q^s := fun div => pq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow div))
  have exactp : u.factorization p=e := by
    unfold u
    rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero),
      Finsupp.add_apply,Nat.factorization_pow_self hp,Nat.factorization_eq_zero_of_not_dvd notq,add_zero]
  change u = v*v at hv
  rw [hv,←pow_two,Nat.factorization_pow] at exactp
  simp only [Finsupp.smul_apply,smul_eq_mul] at exactp
  omega
theorem parity {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    (d=2 → a%2=1) ∧ (d=3 → a%4=2) ∧ (d=4 → a%4=0) := by
  let primes : Fin 2 → ℕ := ![p,q]
  let exps : Fin 2 → ℕ := ![a,d]
  have pr : ∀ i, (primes i).Prime := by intro i;fin_cases i <;> assumption
  have odd : ∀ i, Odd (primes i) := fun i => (pr i).odd_of_ne_two (by fin_cases i <;> dsimp [primes] <;> omega)
  have inj : Function.Injective primes := by
    intro i j h;fin_cases i <;> fin_cases j <;> simp_all [primes]
  have total : OMA.Smooth245212.total primes exps=p^a*q^d := by
    simp [OMA.Smooth245212.total,Fin.prod_univ_two,primes,exps]
  have eq := OMA.ExponentParity245212.exponent_product primes exps pr odd inj k (by
    rw [total,←mul_assoc];exact eqn)
  simp [Fin.prod_univ_two,exps] at eq
  have flip : OeisA245212.a (2^k*q^d*p^a)=(σ 1 (2^k*q^d*p^a):ℤ) := by rwa [mul_right_comm]
  refine ⟨fun v => ?_,fun v => ?_,fun v => ?_⟩ <;> subst d
  · by_contra! bad
    have ea : Even a := Nat.even_iff.mpr (by omega)
    have := square_factors hq hp oq op pq.symm (by decide : Even 2) ea flip
    omega
  · change 4 ∣ (a+2)*(3+2) at eq
    omega
  · change 4 ∣ (a+2)*(4+2) at eq
    have even : Even a := Nat.even_iff.mpr (by omega)
    exact Nat.dvd_iff_mod_eq_zero.mp (square_factors hp hq op oq pq even (by decide) eqn)
end OMA.SmallFacts245212
end
section
namespace OMA.RankTwoSieve8_245212
open OMA.ComplementaryLocal245212 OMA.Smooth245212
open scoped ArithmeticFunction.sigma
private def moments (p : ZMod 8) : ℕ → ZMod 8 × ZMod 8 × ZMod 8
  | 0 => (1,1,1)
  | e+1 => let (v,s,w) := moments p e
           let next:=v*p
           (next,s+next,w+((e+2:ℕ):ZMod 8)*next)
private theorem actual {p : ℕ} (hp : p.Prime) (op : 3≤p) (e : ℕ) :
    moments p e = ((p:ZMod 8)^e,(σ 1 (p^e):ZMod 8),(W (p^e):ZMod 8)) := by
  induction e with
  | zero => simp [moments,W]
  | succ e ih =>
    rw [moments,ih,(last hp op e).1,(last hp op e).2.1]
    push_cast
    simp only [pow_succ]
    congr 2 <;> ring
private theorem period (t : ZMod 8) (e : ℕ) : moments (2*t+1) (e+16)=moments (2*t+1) e := by
  induction e with
  | zero => exact (by decide : ∀ t : ZMod 8, moments (2*t+1) 16=moments (2*t+1) 0) t
  | succ e ih =>
    change moments (2*t+1) ((e+16)+1)=moments (2*t+1) (e+1)
    conv_lhs => unfold moments
    conv_rhs => unfold moments
    rw [ih]
    have h : (((e+16+2:ℕ):ZMod 8))=((e+2:ℕ):ZMod 8) := by push_cast; rw [show (16:ZMod 8)=0 by decide,add_zero]
    rw [h]
private theorem reduce (r : ZMod 8) (e : ℕ) : moments (2*r+1) (e%16)=moments (2*r+1) e := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases he : e<16
    · rw [Nat.mod_eq_of_lt he]
    · rw [show e%16=(e-16)%16 by omega,ih (e-16) (by omega),←period r (e-16)]
      congr 1;omega
def compatible (p e f : ℕ) : Bool :=
  if e%4=0 ∧ f%4=0 then decide (e%16=f%16)
  else if f%4=2 then
    if e%4=1 then decide ((p+f/2)%8=6)
    else if e%8=3 then decide ((p+f/2)%4=2) else true
  else true
private theorem table (p q : Fin 4) (e f : Fin 16)
    (h : (moments (2*p.val+1) e.val).2.2*(moments (2*q.val+1) f.val).2.2 =
         (moments (2*p.val+1) e.val).2.1*(moments (2*q.val+1) f.val).2.1) :
    compatible (2*p.val+1) e.val f.val=true := by
  revert h f e q p
  decide +kernel
theorem necessary {p q e f k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 2<p) (oq : 2<q) (pq : p≠q) (hk : 2≤k)
    (eqn : OeisA245212.a (2^k*p^e*q^f)=(σ 1 (2^k*p^e*q^f):ℤ)) :
    compatible p e f=true := by
  have eq:=congrArg (fun z : ℤ => (z:ZMod 8))
    (physical hp hq (by omega) (by omega) pq e f k eqn)
  have zero : (2:ZMod 8)^(k+1)=0 := by
    rw [show k+1=3+(k-2) by omega,pow_add,show (2:ZMod 8)^3=0 by decide,zero_mul]
  push_cast at eq
  rw [zero] at eq
  have mw : (W (p^e):ZMod 8)*(W (q^f):ZMod 8)=(σ 1 (p^e):ZMod 8)*(σ 1 (q^f):ZMod 8) := by linear_combination eq
  let P : Fin 4 := ⟨(p/2)%4,by omega⟩
  let Q : Fin 4 := ⟨(q/2)%4,by omega⟩
  let E : Fin 16 := ⟨e%16,by omega⟩
  let F : Fin 16 := ⟨f%16,by omega⟩
  have po := hp.odd_of_ne_two (by omega : p≠2)
  have qo := hq.odd_of_ne_two (by omega : q≠2)
  have pp : 2*P.val+1 = p%8 := by dsimp [P]; obtain ⟨t,ht⟩:=po;omega
  have qq : 2*Q.val+1 = q%8 := by dsimp [Q]; obtain ⟨t,ht⟩:=qo;omega
  have pp' : 2*(P.val:ZMod 8)+1=(p:ZMod 8) := by exact_mod_cast (show ((2*P.val+1:ℕ):ZMod 8)=(p:ZMod 8) by rw [pp,ZMod.natCast_mod])
  have qq' : 2*(Q.val:ZMod 8)+1=(q:ZMod 8) := by exact_mod_cast (show ((2*Q.val+1:ℕ):ZMod 8)=(q:ZMod 8) by rw [qq,ZMod.natCast_mod])
  have h := table P Q E F (by
    dsimp only [E,F]
    rw [reduce (P.val:ZMod 8) e,reduce (Q.val:ZMod 8) f,pp',qq',actual hp op,actual hq (by omega : 3≤q)]
    exact mw)
  change compatible (2*P.val+1) (e%16) (f%16)=true at h
  rw [pp] at h
  unfold compatible at *
  split_ifs at * <;> simp_all <;> omega
end OMA.RankTwoSieve8_245212
end
section
namespace OMA.RankTwoPrimeBook245212
private def book (i : ℕ) := (0x2348c22d89a2588a1b862148460d82a06809fe7e5f67c5eb79de2781de765d4739cd725c4701bd6e9b76cdaf6b5a8695a16759965191635865fd7d5e5775c56f5b1685955e565565454d525465113e4e1354c52b4a5254851b465164490d42105408fb3dcf23bce9390de370d9358cf32cc6308be2ecb52c4ac29ca22749a2589122c872087e1e4731bc6919061170561404c118420f4360c02b0941f0601202c00 >>> (10*min i 128))%1024
private def primeAt (i : ℕ) := (0xffdffbfeffe9fd9fd3fd1fbbfb5fb3fadfa7fa3fa1f95f7ff6bf67f5bf59f53f4ff4df47f43f31f29f25f17f0df0bf07ef9eefeededbed5ed1ec3eb9eb7eb1e9be95e8fe87e7de75e71e6be5de59e57e4be3be35e2fe27e21e1de17e09dffdfddf3de7de5ddbdd5dd3dcddc9dc7dbddb7dabda3d8dd8bd87d85d81d79d69d55d4fd3fd3dd2dd2bd21d1fd13d0fd03d01cfbcf7cf1cebce5ce3cc7cbbcb9cb5cb3c9dc95c91c89c83c77c73c6dc61c5fc5bc41c31c2fc25c11c0bc07bfbbf5be9be1bddbcfbcbbc3bb9bb7b9bb99b93b8db89b7bb6fb65b5db57b51b47b3fb2db29b23b1bb15b11b03af3af1aedae7ae5ad9acfac1abdab5aabaa9a9fa99a97a93a8ba85a81a7fa7ba75a6fa67a63a61a57a49a3da39a31a21a1fa139fd9f79f59ef9eb9e39d99c79ad9a99a399b98f98998597797196b95f95995594f94d94994393592f92b92592391d9079058f98f58ef8e98e18dd8db8cb8c38bf8bd8ad8a589f89b88387186985f85d85985385184183f83382982782382181580f8057f77ed7eb7e17db7d37cf7cd7c97c37bb7b579f79d78d78b77977376d76175775575174f74b74573772771f7137096fd6fb6f76f16df6d96d36cd6c56bb6b96ad6a36a169d68568367f67966565b65565364d64964764163d62f62b62361f61761160d6075fb5f35e75db5d55d15cf5cb5c95bf5b35ad5ab5a759f59959559358f58157756555d55755152f52952751b51751551150b5095034ff4fd4eb4e14d54cf4cd4c74c14bd4b14a94a349d49348b48147f46946345d45544f44944544343f42d42742541b41940f4094073fd3fb3f53f13e53df3d73d13cb3c73b93b33ad3a93a139738f38b37737337136d35f35b35935534733d33b33733532b32931d3133053012f92f52ef2e72e32dd2d72cf2c52bd2b32ab2a52a129529328d28728328127726b26926525f25925725124b24123b23923322d22321d20b2091fd1f71f31eb1e71df1d31cf1cd1c91c11bb1b71b11af1a51a319919118d18517f17b17516f16716115d15b15114b13d13913713312511b11911510f10d1071010fb0f10ef0e90e50e30df0d30c70c50c10bf0b50b30ad0a70a309d09709508b08908307f07106d06b06706506105905304f04904704303d03b03502f02b02902501f01d01701301100d00b007005003002 >>> (12*i))%4096
private def interval (i j : ℕ) := List.range' i (j-i)
private theorem mono : Monotone book := by
  apply monotone_nat_of_le_succ
  intro i
  by_cases h : i<128
  · have all : (List.range 128).all (fun i => decide (book i≤book (i+1))) = true := by decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp all i (List.mem_range.mpr h))
  · have big : 128 ≤ i := by omega
    have bigger : 128 ≤ i+1 := by omega
    simp [book,min_eq_right big,min_eq_right bigger]
private def composite (n : ℕ) := decide (n<2) ||
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61].any fun a => decide (1<a ∧ a<n ∧ n%a=0)
private theorem not_composite {n : ℕ} (h : n.Prime) : composite n=false := by
  have two:=h.two_le
  simp only [composite,not_lt_of_ge two,decide_false,Bool.false_or,Bool.eq_false_iff]
  intro bad
  obtain ⟨a,_,v⟩:=List.any_eq_true.mp bad
  obtain ⟨one,lt,rem⟩:=of_decide_eq_true v
  have div := Nat.dvd_iff_mod_eq_zero.mpr rem
  rcases (Nat.dvd_prime h).mp div with one'|eq <;> omega
private def present (n : ℕ) := composite n ||
  (interval (book (n/32)) (book (n/32+1))).any fun i => decide (primeAt i=n)
set_option maxRecDepth 10000 in
private theorem coverage (b : Fin 32) : (List.range' (128*b.val) 128).all present=true := by
  fin_cases b <;> decide +kernel
def scan (lo hi : ℕ) (f : ℕ→Bool) : Bool :=
  if hi<4096 then (interval (book (lo/32)) (book (hi/32+1))).all fun i =>
    let p:=primeAt i
    decide (p<lo ∨ hi<p) || f p
  else OMA.RankTwoReplay245212.allIn lo hi fun p => !decide p.Prime || f p
theorem member {lo hi p : ℕ} {f : ℕ→Bool} (check : scan lo hi f=true)
    (pr : p.Prime) (l : lo≤p) (u : p≤hi) : f p=true := by
  unfold scan at check
  split at check
  · rename_i h
    let b : Fin 32:=⟨p/128,by omega⟩
    have ok:=List.all_eq_true.mp (coverage b) p (List.mem_range'_1.mpr (by dsimp [b];omega))
    simp only [present,not_composite pr,Bool.false_or,List.any_eq_true,decide_eq_true_eq] at ok
    obtain ⟨i,mem,rfl⟩:=ok
    simp only [interval,List.mem_range'_1] at mem
    have bl:=mono (Nat.div_le_div_right (c:=32) l)
    have bh:=mono (Nat.succ_le_succ (Nat.div_le_div_right (c:=32) u))
    change book (lo/32)≤book (primeAt i/32) at bl
    change book (primeAt i/32+1)≤book (hi/32+1) at bh
    have seen:=List.all_eq_true.mp check i (List.mem_range'_1.mpr (by omega))
    simpa [not_lt_of_ge l,not_lt_of_ge u] using seen
  · have seen:=List.all_eq_true.mp check p (List.mem_range'_1.mpr ⟨l,by omega⟩)
    simpa [pr] using seen
end OMA.RankTwoPrimeBook245212
end
section
namespace OMA.RankTwoMoment245212
open OMA.Smooth245212 OMA.LastDigit245212 OMA.Large245212
open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma
open OMA.Large245212 (force)
open OMA.PairExtension245212 (fit)
def raw (p f A S T : ℕ) :=
  let D:=denom A S T f
  let U:=A*f+S
  if D=0 ∨ U≤p*D then true else
    let q:=(U-1)/D+1
    !OMA.PairExtension245212.permitted A S T q f
def check (k p e f : ℕ) :=
  let x:=2^k
  let y:=p^e
  let v:=p-1
  let A:=(2*k*x+1)*(p*((e+1)*v-1)*y+1)
  let S:=(2*x-1)*v*(p*y-1)
  let T:=(k+1)*x*(e+1)*y*v^2
  raw p f A S T
private theorem scaled {p e k : ℕ} (hp : p.Prime) (op : 2<p) :
    let u:=2^k*p^e; let c:=(p-1)^2
    (2*k*2^k+1)*(p*((e+1)*(p-1)-1)*p^e+1)=c*W u ∧
    (2*2^k-1)*(p-1)*(p*p^e-1)=c*(σ 1 u) ∧
    (k+1)*2^k*(e+1)*p^e*(p-1)^2=c*(u*(σ 0 u)) := by
  dsimp only
  have cop := (((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)).pow_left k).pow_right e
  rw [w_mult.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
    isMultiplicative_sigma.map_mul_of_coprime cop,sigma_zero_apply_prime_pow hp,
    sigma_zero_apply_prime_pow Nat.prime_two]
  obtain ⟨s,w⟩:=OMA.ComplementaryLocal245212.moments hp e
  obtain ⟨s2,w2⟩:=OMA.ComplementaryLocal245212.moments Nat.prime_two k
  norm_num at s2 w2
  have ev : 1≤(e+1)*(p-1) := Nat.mul_pos (by omega) (by omega)
  have py : 1≤p*p^e := Nat.mul_pos hp.pos (pow_pos hp.pos _)
  have tx : 1≤2*2^k := Nat.mul_pos (by decide) (by positivity)
  have pp : 1≤p := hp.one_le
  zify [ev,py,tx,pp] at *
  constructor
  · calc
      _ = (W (2^k):ℤ)*(((p:ℤ)-1)^2*(W (p^e):ℤ)) := by rw [w,w2]
      _ = _ := by ring
  constructor
  · calc
      _ = (σ 1 (2^k):ℤ)*((p:ℤ)-1)*(((p:ℤ)-1)*(σ 1 (p^e):ℤ)) := by rw [s,s2]
      _ = _ := by ring
  · ring
private theorem raw_sound {u p q f c : ℕ} (pos : 0<u) (hc : 0<c)
    (hq : q.Prime) (pq : p<q) (cop : u.Coprime q) (fp : 0<f)
    (eqn : OeisA245212.a (u*q^f)=(σ 1 (u*q^f):ℤ)) :
    raw p f (c*W u) (c*σ 1 u) (c*(u*(σ 0 u)))=false := by
  let A:=W u; let S:=σ 1 u; let T:=u*(σ 0 u)
  obtain ⟨hd,lo,hi,_⟩:=balance_digits pos hq cop fp eqn
  have D : denom (c*A) (c*S) (c*T) f=c*denom A S T f := by
    unfold denom
    rw [Nat.mul_sub]
    congr 1 <;> ring
  have num : (c*A)*f+c*S=c*(A*f+S) := by ring
  have dp : 0<denom (c*A) (c*S) (c*T) f := D ▸ Nat.mul_pos hc hd
  have l : denom (c*A) (c*S) (c*T) f*(q-1)<(c*A)*f+c*S := by
    rw [D,num,mul_assoc];exact Nat.mul_lt_mul_of_pos_left lo hc
  have h : (c*A)*f+c*S≤denom (c*A) (c*S) (c*T) f*q := by
    rw [D,num,mul_assoc];exact Nat.mul_le_mul_left _ hi
  have choose := OMA.Large245212.force (Nat.mul_pos hc (sigma_pos 1 u pos.ne')) hq.one_lt dp l h
  have above : ¬(c*A)*f+c*S≤p*denom (c*A) (c*S) (c*T) f := by
    have := Nat.mul_le_mul_left (denom (c*A) (c*S) (c*T) f) (by omega : p≤q-1)
    rw [mul_comm p];omega
  have fit := OMA.PairExtension245212.fit pos hq cop fp eqn
  change OMA.PairExtension245212.permitted A S T q f=true at fit
  simp only [OMA.PairExtension245212.permitted,Bool.and_eq_true,decide_eq_true_eq] at fit
  change raw p f (c*A) (c*S) (c*T)=false
  unfold raw
  simp only [dp.ne',above,false_or,if_false]
  change (!OMA.PairExtension245212.permitted (c*A) (c*S) (c*T) (candidate (c*A) (c*S) (c*T) f) f)=false
  rw [choose]
  simp only [Bool.not_eq_false',OMA.PairExtension245212.permitted,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rw [←Nat.mul_add];exact dvd_mul_of_dvd_right fit.1 c
  · linear_combination c*fit.2
theorem point {k p e q f : ℕ} (hp : p.Prime) (op : 2<p) (hq : q.Prime)
    (pq : p<q) (fp : 0<f) (ok : check k p e f=true) :
    OeisA245212.a (2^k*p^e*q^f)≠(σ 1 (2^k*p^e*q^f):ℤ) := by
  intro eqn
  obtain ⟨a,s,t⟩:=scaled (k:=k) (e:=e) hp op
  unfold check at ok
  dsimp only at ok
  rw [a,s,t] at ok
  have c : (2^k*p^e).Coprime q :=
    (((Nat.coprime_primes Nat.prime_two hq).mpr (by omega)).pow_left k).mul_left
      (((Nat.coprime_primes hp hq).mpr pq.ne).pow_left e)
  have no := raw_sound (p:=p) (c:=(p-1)^2) (Nat.mul_pos (pow_pos (by decide) _) (pow_pos hp.pos _))
    (pow_pos (by omega) _) hq pq c fp eqn
  simp [no] at ok
end OMA.RankTwoMoment245212
end
section
namespace OMA.RankTwoFiltered245212
open OMA.RankTwoReplay245212 OMA.Large245212
open scoped ArithmeticFunction.sigma
open OMA.RankTwoReplay245212 (member)
open OMA.SmallFacts245212 (square_factors)
def allowed (e f : ℕ) : Bool :=
  decide (4 ∣ (e+2)*(f+2)) &&
    (decide (e%2=1 ∨ f%2=1) || decide (e%4=0 ∧ f%4=0))
theorem necessary {p q e f k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 2<p) (pq : p<q)
    (eqn : OeisA245212.a (2^k*p^e*q^f)=(σ 1 (2^k*p^e*q^f):ℤ)) : allowed e f=true := by
  let primes : Fin 2 → ℕ := ![p,q]
  let exps : Fin 2 → ℕ := ![e,f]
  have pr : ∀ i, (primes i).Prime := by intro i; fin_cases i <;> assumption
  have odd : ∀ i, Odd (primes i) := fun i => (pr i).odd_of_ne_two (by fin_cases i <;> dsimp [primes] <;> omega)
  have inj : Function.Injective primes := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all [primes]
  have total : OMA.Smooth245212.total primes exps=p^e*q^f := by
    simp [OMA.Smooth245212.total,Fin.prod_univ_two,primes,exps]
  have prod:=OMA.ExponentParity245212.exponent_product primes exps pr odd inj k (by
    rw [total,←mul_assoc];exact eqn)
  have prod' : 4 ∣ (e+2)*(f+2) := by simpa [Fin.prod_univ_two,exps] using prod
  simp only [allowed,Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true]
  refine ⟨prod',?_⟩
  by_cases h : e%2=1 ∨ f%2=1
  · exact Or.inl h
  have he : Even e := Nat.even_iff.mpr (by omega)
  have hf : Even f := Nat.even_iff.mpr (by omega)
  have flip : OeisA245212.a (2^k*q^f*p^e)=(σ 1 (2^k*q^f*p^e):ℤ) := by rwa [mul_right_comm]
  exact Or.inr ⟨Nat.dvd_iff_mod_eq_zero.mp (OMA.SmallFacts245212.square_factors hp hq op (by omega) pq.ne he hf eqn),
    Nat.dvd_iff_mod_eq_zero.mp (OMA.SmallFacts245212.square_factors hq hp (by omega) op pq.ne' hf he flip)⟩
def slice (kl kh pl ph el eh fl fh : ℕ) : Bool :=
  allIn el eh fun e => allIn fl fh fun f => !allowed e f || OMA.RankTwoPrimeBook245212.scan pl ph fun p =>
    !OMA.RankTwoSieve8_245212.compatible p e f || allIn kl kh fun k => OMA.RankTwoMoment245212.check k p e f
theorem of_slice {kl kh pl ph el eh fl fh k p e q f : ℕ}
    (hp : p.Prime) (po : 2<p) (hq : q.Prime) (pq : p<q) (fp : 0<f) (hk : 2≤k)
    (p₀ : pl≤p) (p₁ : p≤ph) (k₀ : kl≤k) (k₁ : k≤kh)
    (e₀ : el≤e) (e₁ : e≤eh) (f₀ : fl≤f) (f₁ : f≤fh)
    (ok : slice kl kh pl ph el eh fl fh=true) :
    OeisA245212.a (2^k*p^e*q^f)≠(σ 1 (2^k*p^e*q^f):ℤ) := by
  intro eqn
  have exp := OMA.RankTwoReplay245212.member (OMA.RankTwoReplay245212.member ok e₀ e₁) f₀ f₁
  simp only [necessary hp hq po pq eqn,Bool.not_true,Bool.false_or] at exp
  have pp := OMA.RankTwoPrimeBook245212.member exp hp p₀ p₁
  simp only [OMA.RankTwoSieve8_245212.necessary hp hq po (by omega) pq.ne hk eqn,Bool.not_true,Bool.false_or] at pp
  have point := OMA.RankTwoReplay245212.member pp k₀ k₁
  exact OMA.RankTwoMoment245212.point hp po hq pq fp point eqn
end OMA.RankTwoFiltered245212
end
section
namespace OMA.RankTwoInteriorWalk245212
open OMA.RankTwoInteriorBox245212
def trim (t : Cell) : Cell :=
  {t with pl:=max t.pl (1+(t.kl-1)*(t.bl-1)/t.bl), ph:=min t.ph (3*t.kh)}
def exact (t : Cell) : Bool := OMA.RankTwoFiltered245212.slice (t.kl-1) (t.kh-1)
  t.pl t.ph (t.bl-1) (t.bh-1) (t.cl-1) (t.ch-1)
def cut (a b : ℕ) := if 2*a≤b then Nat.sqrt (a*b) else (a+b)/2
def halves (t : Cell) : Cell × Cell :=
  let wk := t.kh-t.kl
  let wb := t.bh-t.bl
  let wc := t.ch-t.cl
  let wp := (t.ph-t.pl)/7
  if 3*t.kl<t.kh || (wk≥max wp (max wb wc) && 0<wk) then
    let j := cut t.kl t.kh
    ({t with kh:=j},{t with kl:=j+1})
  else if 3*t.bl<t.bh || (wb≥max wp wc && 0<wb) then
    let j := cut t.bl t.bh
    ({t with bh:=j},{t with bl:=j+1})
  else if 3*t.cl<t.ch || (wc≥wp && 0<wc) then
    let j := cut t.cl t.ch
    ({t with ch:=j},{t with cl:=j+1})
  else
    let j := (t.pl+t.ph)/2
    ({t with ph:=j},{t with pl:=j+1})
def easy (t : Cell) : Bool :=
  decide (t.ph<t.pl) || OMA.OddBox245212.veto t.kl t.kh t.bl t.bh t.cl t.ch t.pl t.ph ||
    veto t
def root (m kl kh : ℕ) (swap : Bool) : Cell :=
  if swap then ⟨kl,kh,m,m,m+1,225,13,3*kh⟩ else ⟨kl,kh,m,225,m,m,13,3*kh⟩
def Good (t : Cell) := 0<t.kl ∧ 0<t.bl ∧ 0<t.pl
theorem split_covers {t : Cell} {K B C p : ℕ} (h : Fits t K B C p) (g : Good t) :
    (Fits (halves t).1 K B C p ∧ Good (halves t).1) ∨
    (Fits (halves t).2 K B C p ∧ Good (halves t).2) := by
  unfold halves
  dsimp only
  split
  · simp only [Fits,Good] at *;omega
  · split
    · simp only [Fits,Good] at *;omega
    · split <;> simp only [Fits,Good] at * <;> omega
theorem trim_fits {t : Cell} {k B C p : ℕ} (h : Fits t (k+1) B C p) (g : Good t)
    (floor : ∀ j, 0<j → j≤B → 1+k*(j-1)/j≤p) (upper : p≤3*(k+1)) :
    Fits (trim t) (k+1) B C p ∧ Good (trim t) := by
  obtain ⟨k₀,k₁,b₀,b₁,c₀,c₁,p₀,p₁⟩ := h
  have a := Nat.div_le_div_right (c:=t.bl) (Nat.mul_le_mul_right (t.bl-1) (show t.kl-1≤k by omega))
  have b := floor t.bl g.2.1 b₀
  have ceil : p≤3*t.kh := upper.trans (Nat.mul_le_mul_left 3 k₁)
  refine ⟨⟨k₀,k₁,b₀,b₁,c₀,c₁,max_le p₀ ?_,le_min p₁ ceil⟩,g.1,g.2.1,lt_of_lt_of_le g.2.2 (le_max_left ..)⟩
  exact (Nat.add_le_add_left a 1).trans b
open ArithmeticFunction
open scoped ArithmeticFunction.sigma
theorem solution_facts {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 13≤p) (pq : p+2≤q) (dk : 5≤k) (ea : 5≤a) (ed : 4≤d) (upper : p≤3*(k+1))
    (generic : ∀ s, Fits s (k+1) (a+1) (d+2) p →
      OeisA245212.a (2^k*p^a*q^(d+1))=(σ 1 (2^k*p^a*q^(d+1)):ℤ) →
      OMA.OddBox245212.veto s.kl s.kh s.bl s.bh s.cl s.ch s.pl s.ph=false)
    (eqn : OeisA245212.a (2^k*p^a*q^(d+1))=(σ 1 (2^k*p^a*q^(d+1)):ℤ)) :
    (∀ j, 0<j → j≤a+1 → 1+k*(j-1)/j≤p) ∧
    (∀ s, Fits s (k+1) (a+1) (d+2) p → Good s → easy s=false) ∧
    (∀ s, Fits s (k+1) (a+1) (d+2) p → exact s=false) := by
  have po : 3≤p := by omega
  have qo : 3≤q := by omega
  have plq : p<q := by omega
  have pos : (p:ℤ)-1<(k:ℤ)*(d+1) := by
    have ub : (p:ℤ)≤3*(k+1) := by exact_mod_cast upper
    nlinarith only [ub,mul_nonneg (by positivity : (0:ℤ)≤k) (by omega : (0:ℤ)≤d-4),
      (show (5:ℤ)≤k by exact_mod_cast dk)]
  have small : (p:ℤ)-1≤((d:ℤ)+2)*k := by nlinarith only [pos,Int.natCast_nonneg k]
  have sep := OMA.OddBox245212.separations hp hq po plq (by omega : 1≤a)
    (by omega : 1≤d+1) (by omega : 2≤k) (by exact_mod_cast pos) eqn
  have bd := OMA.SimultaneousBound245212.of_separations hp hq po qo plq.ne eqn sep.1 sep.2
  have floor (j : ℕ) (j0 : 0<j) (jb : j≤a+1) : 1+k*(j-1)/j≤p := by
    have f := OMA.TwoOddParameters245212.floor hp hq po qo plq.ne (by omega : 1≤a) j0 jb eqn
    exact (le_max_right _ _).trans (by simpa [OMA.TwoOddEffectiveTable245212.floorPrime] using f)
  have noEasy (s : Cell) (fs : Fits s (k+1) (a+1) (d+2) p) (gs : Good s) : easy s=false := by
    have order : ¬s.ph<s.pl := by obtain ⟨_,_,_,_,_,_,l,r⟩:=fs;omega
    have v := veto_false hp hq po pq (by omega : 2≤a) gs.1 gs.2.2 fs small eqn bd.1 bd.2
    simp [easy,order,generic s fs eqn,v]
  have noExact (s : Cell) (fs : Fits s (k+1) (a+1) (d+2) p) : exact s=false := by
    obtain ⟨k₀,k₁,b₀,b₁,c₀,c₁,p₀,p₁⟩ := fs
    by_contra! bad
    have checked := Bool.eq_true_of_not_eq_false bad
    exact OMA.RankTwoFiltered245212.of_slice hp (by omega) hq plq (by omega : 0<d+1) (by omega) p₀ p₁
      (by omega : s.kl-1 ≤ k) (by omega : k ≤ s.kh-1) (by omega : s.bl-1 ≤ a)
      (by omega : a ≤ s.bh-1) (by omega : s.cl-1 ≤ d+1) (by omega : d+1 ≤ s.ch-1) checked eqn
  exact ⟨floor,noEasy,noExact⟩
end OMA.RankTwoInteriorWalk245212
end
section
namespace OMA.RankTwoInteriorCover245212
open OMA.RankTwoInteriorBox245212 OMA.RankTwoInteriorWalk245212
open OMA.RankTwoInteriorWalk245212 (split_covers)
deriving instance DecidableEq for OMA.RankTwoInteriorBox245212.Cell
structure World where
  k : ℕ
  B : ℕ
  C : ℕ
  p : ℕ
  floor : ∀ j, 0<j → j≤B → 1+k*(j-1)/j≤p
  upper : p≤3*(k+1)
  noEasy : ∀ t, Fits t (k+1) B C p → Good t → easy t=false
  noExact : ∀ t, Fits t (k+1) B C p → exact t=false
def Closed (t : Cell) := ∀ w : World, Fits t (w.k+1) w.B w.C w.p → Good t → False
inductive Reason where
  | empty | pole | exterior | arithmetic
  deriving Repr
def certificate (r : Reason) (t : Cell) : Bool :=
  match r with
  | .empty => decide (t.ph<t.pl)
  | .pole => OMA.RankTwoInteriorBox245212.veto t
  | .exterior => OMA.OddBox245212.veto t.kl t.kh t.bl t.bh t.cl t.ch t.pl t.ph
  | .arithmetic => exact t
theorem certify {r : Reason} (raw t : Cell) (same : trim raw=t)
    (ok : certificate r t=true) : Closed raw := by
  intro w ft gt
  obtain ⟨f,g⟩ := trim_fits ft gt w.floor w.upper
  rw [same] at f g
  have e := w.noEasy t f g
  have a := w.noExact t f
  cases r <;> simp_all [certificate,easy]
  exact (Nat.not_lt_of_ge e.1.1) ok
theorem join (t : Cell) {l r : Cell} (left : Closed l) (right : Closed r)
    (ident : halves (trim t)=(l,r)) : Closed t := by
  intro w ft gt
  obtain ⟨f,g⟩ := trim_fits ft gt w.floor w.upper
  have sub := OMA.RankTwoInteriorWalk245212.split_covers f g
  rw [ident] at sub
  exact sub.elim (fun h => left w h.1 h.2) (fun h => right w h.1 h.2)
inductive Script where
  | leaf : Reason → Script
  | fork : Script → Script → Script
def verify : Script → Cell → Bool
  | .leaf r, t => certificate r (trim t)
  | .fork l r, t =>
    let (a,b) := halves (trim t)
    verify l a && verify r b
theorem of_script (s : Script) (t : Cell) (ok : verify s t=true) : Closed t := by
  induction s generalizing t with
  | leaf r => exact certify t _ rfl ok
  | fork l r il ir =>
    simp only [verify,Bool.and_eq_true] at ok
    exact join t (il _ ok.1) (ir _ ok.2) rfl
end OMA.RankTwoInteriorCover245212
end
section
namespace OMA.RankTwoPacked245212
open OMA.RankTwoInteriorBox245212 OMA.RankTwoInteriorWalk245212 OMA.RankTwoInteriorCover245212
def unpackCell (n : ℕ) : Cell :=
  ⟨n%2048,(n/2^11)%2048,(n/2^22)%256,(n/2^30)%256,
    (n/2^38)%256,(n/2^46)%256,(n/2^54)%4096,(n/2^66)%4096⟩
private def read : ℕ → ℕ → List Script → Option (List Script)
  | 0,n,stack => if n=1 then some stack else none
  | k+1,n,stack =>
    let tail:=n/8
    match n%8 with
    | 0 => read k tail (.leaf .empty::stack)
    | 1 => read k tail (.leaf .pole::stack)
    | 2 => read k tail (.leaf .exterior::stack)
    | 3 => read k tail (.leaf .arithmetic::stack)
    | 4 =>
      match stack with
      | left::right::rest => read k tail (.fork left right::rest)
      | _ => none
    | _ => none
def decode (n : ℕ) : Option Script := do
  let [s] ← read (Nat.log 2 n / 3) n [] | none
  return s
def rowOK (rows : ℕ→ℕ) (i : ℕ) : Bool :=
  let row := rows i
  let t := unpackCell row
  let op := row/2^78
  let raw := op/2
  if op%2=0 then
    match decode raw with
    | some s => verify s t
    | none => false
  else
    decide (0 < raw ∧ raw ≤ i ∧ halves (trim t)=(unpackCell (rows (i-raw)),unpackCell (rows (i-1))))
def block (rows : ℕ→ℕ) (i n : ℕ) := (List.range' i n).all (rowOK rows)
def Ready (rows : ℕ→ℕ) (n : ℕ) := ∀ i<n,rowOK rows i=true
theorem start (rows : ℕ→ℕ) : Ready rows 0 := by simp [Ready]
theorem extend {rows : ℕ→ℕ} {off last : ℕ} (prev : Ready rows off)
    (next : block rows off (last-off)=true) : Ready rows last := by
  intro i h
  by_cases small : i<off
  · exact prev i small
  · exact List.all_eq_true.mp next i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
theorem atRow {rows : ℕ→ℕ} {n : ℕ} (valid : Ready rows n)
    (i : ℕ) (lim : i<n) : Closed (unpackCell (rows i)) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    have got := valid i lim
    unfold rowOK at got
    dsimp only at got
    split at got
    · split at got
      · exact of_script _ _ got
      · contradiction
    · obtain ⟨pos,fit,edges⟩:=of_decide_eq_true got
      exact join _ (ih _ (by omega) (by omega)) (ih (i-1) (by omega) (by omega)) edges
theorem atRoot {rows : ℕ→ℕ} {n i m kl kh : ℕ} {dir : Bool}
    (valid : Ready rows n)
    (hit : decide (i<n ∧ unpackCell (rows i)=root m kl kh dir)=true) :
    Closed (root m kl kh dir) := by
  obtain ⟨lt,ident⟩:=of_decide_eq_true hit
  rw [←ident];exact atRow valid i lt
end OMA.RankTwoPacked245212
end
section
namespace OMA.RankTwoCursor245212
def Before (ok : ℕ → Bool) (last : ℕ) := ∀ i < last, ok i=true
structure Cursor (ok : ℕ → Bool) where
  pos : ℕ
  checked : Before ok pos
def Cursor.start (ok : ℕ → Bool) : Cursor ok := ⟨0,by intro i h; omega⟩
def Cursor.step {ok : ℕ → Bool} (prev : Cursor ok) (lo hi : ℕ) (atLo : prev.pos=lo)
    (pass : (List.range' lo (hi-lo)).all ok=true) : Cursor ok := by
  refine ⟨hi,?_⟩
  intro i lt
  by_cases old : i < lo
  · exact prev.checked i (by omega)
  · exact List.all_eq_true.mp pass i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
theorem splice {ok : ℕ → Bool} {a b : ℕ} (low : Before ok a)
    (high : Before (fun i => ok (a+i)) b) : Before ok (a+b) := by
  intro i h
  by_cases early : i<a
  · exact low i early
  · have h₁ := high (i-a) (by omega)
    change ok (a+(i-a))=true at h₁
    rwa [show a+(i-a)=i by omega] at h₁
end OMA.RankTwoCursor245212
end
section
namespace OMA.OddBox245212
noncomputable abbrev L (n : ℕ) := logSize (n:ℝ)
theorem lmono {a b : ℕ} (ha : 0<a) (hab : a≤b) : L a≤L b :=
  mono (by exact_mod_cast ha) (by exact_mod_cast hab)
theorem lreflect {a b : ℕ} (ha : 0<a) (hb : 0<b) : L a≤L b ↔ a≤b := by
  simpa [L] using reflect (x:=(a:ℝ)) (y:=(b:ℝ)) (by exact_mod_cast ha) (by exact_mod_cast hb)
theorem lmul {a b : ℕ} (ha : 0<a) (hb : 0<b) : L (a*b)=L a+L b := by
  push_cast [L];exact mul (by exact_mod_cast ha) (by exact_mod_cast hb)
theorem lpow (a n : ℕ) : L (a^n)=n*L a := by simp only [L,Nat.cast_pow,pow]
@[simp] theorem ltwo : L 2=16 := by norm_num [L]
@[simp] theorem lone : L 1=0 := by norm_num [L]
@[simp] theorem lfour : L 4=32 := by rw [show (4:ℕ)=2*2 by decide,lmul (by decide) (by decide),ltwo];norm_num
theorem le_up {a b : ℕ} (ha : 0<a) (h : a≤b) : L a≤up b := (lmono ha h).trans (enclosed b (ha.trans_le h)).2
theorem down_le {a b : ℕ} (ha : 0<a) (h : a≤b) : (down a:ℝ)≤L b := (enclosed a ha).1.trans (lmono ha h)
theorem lmax {a b : ℕ} (ha : 0<a) (hb : 0<b) : L (max a b)=max (L a) (L b) := by
  rcases le_total a b with h|h
  · rw [max_eq_right h,max_eq_right (lmono ha h)]
  · rw [max_eq_left h,max_eq_left (lmono hb h)]
theorem sum_three {x a b c : ℕ} (hx : 0<x) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (ub : x≤a+b+c) : L x≤L 3+max (L a) (max (L b) (L c)) := by
  have h : x≤3*(max a (max b c)) := by omega
  have z := lmono hx h
  rwa [lmul (by decide) (by omega),lmax ha (by omega),lmax hb hc] at z
theorem sum_four {x a b c d : ℕ} (hx : 0<x) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d)
    (ub : x≤a+b+c+d) : L x≤32+max (max (L a) (max (L b) (L c))) (L d) := by
  have h : x≤4*(max (max a (max b c)) d) := by omega
  have z := lmono hx h
  rwa [lmul (by decide) (by omega),lmax (by omega) hd,lmax ha (by omega),lmax hb hc,lfour] at z
theorem increasing_gap {e lo q a b : ℕ} (he : 1≤e) (hl : 0<lo) (lq : lo≤q)
    (positive : 0<a+b*lo) : L (a+b*q)-e*L q≤L (a+b*lo)-e*L lo := by
  have h : (a+b*q)*lo≤(a+b*lo)*q := by nlinarith only [Nat.mul_le_mul_left a lq]
  have posq : 0<a+b*q := positive.trans_le (by gcongr)
  have h' := lmono (Nat.mul_pos posq hl) h
  rw [lmul posq hl,lmul positive (by omega)] at h'
  have := mul_nonneg (sub_nonneg.mpr (show (1:ℝ)≤e by exact_mod_cast he))
    (sub_nonneg.mpr (lmono hl lq))
  nlinarith only [h',this]
end OMA.OddBox245212
end
section
namespace OMA.OddBox245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryPole245212 OMA.ComplementaryLocal245212
open OMA.QuadraticPowerGap245212
open scoped ArithmeticFunction.sigma
open OMA.ComplementaryHeight245212 (gap)
theorem complement {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (oq : 3≤q) (pq : p≠q)
    (hd : 2≤d) (ha : 2*d+4≤a)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    2^(k+1)≤1+2*(d+1)*(a+1)*(k+1)*p^2*q^d+
      6*(d+1)^2*(a+1)*(k+1+p)*(q^d)^2 := by
  let h : ℤ := (d:ℤ)+1
  let b : ℤ := (a:ℤ)+1
  let K : ℤ := (k:ℤ)+1
  let Q : ℤ := (q:ℤ)^d
  let P : ℤ := (p:ℤ)^a
  let U : ℤ := p-1
  let V : ℤ := W (q^d)
  let S : ℤ := σ 1 (q^d)
  let J : ℤ := h*Q
  let H0 := H p b J V
  let A0 := A p b J S
  have op' : (3:ℤ)≤p := by omega
  have oq' : (3:ℤ)≤q := by omega
  have pz : (0:ℤ)≤p := by omega
  have uz : 0≤U := by dsimp [U];omega
  have hh : 3≤h := by dsimp [h];omega
  have bh : 3≤b := by dsimp [b];omega
  have b0 : 0≤b := by omega
  have u : U≤(p:ℤ) := by dsimp [U];omega
  have ppos : 0<P := by dsimp [P];positivity
  have qp : 0<Q := by dsimp [Q];positivity
  have v0 : 0≤V := by dsimp [V];positivity
  have s0 : 0 ≤ S := by dsimp [S];positivity
  have j0 : 0≤J := by dsimp [J];positivity
  have bd := bounds hq oq d
  have jv : J≤V := by dsimp [J,V,h,Q];exact_mod_cast bd.2.2.1
  have vh : 2*V≤3*h*Q := by dsimp [V,h,Q];exact_mod_cast bd.2.1
  have sh : 2*S≤3*Q := by dsimp [S,Q];exact_mod_cast bd.1
  have bu : p≤b*U := by dsimp [U];nlinarith only [bh,op',mul_nonneg (show 0≤b-3 by omega) uz]
  have Hpos : 0≤H0 := by
    change 0≤b*U*(p*V-U*J)-p*V
    have id : b*U*(p*V-U*J)-p*V=(b*U-p)*V+b*U^2*(V-J) := by dsimp [U];ring
    rw [id];exact add_nonneg (mul_nonneg (sub_nonneg.mpr bu) v0)
      (mul_nonneg (mul_nonneg b0 (sq_nonneg _)) (sub_nonneg.mpr jv))
  have Hub : H0≤b*(p:ℤ)^2*V := by
    change b*U*(p*V-U*J)-p*V≤_
    nlinarith only [mul_nonneg (mul_nonneg b0 (sq_nonneg U)) j0,mul_nonneg pz v0,
      mul_le_mul_of_nonneg_right u (mul_nonneg (mul_nonneg b0 pz) v0)]
  have raw := OMA.ComplementaryNonres245212.cleared hp hq op oq pq eqn
  change P*(G k*(A0-k*H0)-K*H0)=G k*C p k V S+K*V at raw
  have clr : P*(G k*(A0-k*H0)-(k+1)*H0)=F k*V-G k*(p-1)*S := by
    dsimp only [K,C] at raw
    have fg : F k=(k:ℤ)*G k+(k+1) := by dsimp [F,G];ring
    rw [fg];linear_combination raw
  have nz : A0-k*H0≠0 := sub_ne_zero.mpr
    (OMA.ComplementaryNonres245212.original hp hq op oq pq hd ha eqn)
  have lev := OMA.ComplementaryDyad245212.level hp hq op oq pq (by omega) eqn
  have zz : z k≤3*h*b*P*Q := by dsimp [z,h,b,P,Q];exact_mod_cast lev
  have lev' : G k≤P*(3*h*b*Q) := by dsimp [G];linarith only [zz]
  have g := OMA.ComplementaryHeight245212.gap ppos v0 s0 (by omega) Hpos nz clr lev'
  change G k≤K*H0+(3*h*b*Q)*(K*V+p*S) at g
  have vr : V≤2*h*Q := by nlinarith only [vh,mul_nonneg (by omega : 0≤h) qp.le]
  have sr : S≤2*h*Q := by nlinarith only [sh,mul_nonneg (show 0≤h-1 by omega) qp.le,qp.le]
  have Hcap := Hub.trans (mul_le_mul_of_nonneg_left vr (mul_nonneg b0 (sq_nonneg _)))
  have Fcap := mul_le_mul_of_nonneg_left Hcap (by dsimp [K];positivity : 0≤K)
  have Ecap : K*V+p*S≤2*h*(K+p)*Q := by
    nlinarith only [mul_le_mul_of_nonneg_left vr (by dsimp [K];positivity : 0≤K),mul_le_mul_of_nonneg_left sr pz]
  have Rcap := mul_le_mul_of_nonneg_left Ecap (show 0≤3*h*b*Q by positivity)
  have result : z k≤1+2*h*b*K*p^2*Q+6*h^2*b*(K+p)*Q^2 := by
    dsimp only [G] at g
    nlinarith only [g,Rcap,Fcap]
  dsimp only [z,h,b,K,Q] at result
  exact_mod_cast result
end OMA.OddBox245212
end
section
namespace OMA.OddBox245212
open ArithmeticFunction
open scoped ArithmeticFunction.sigma
def rest (K B C p : ℕ) := 6*C*B*K*p^2
noncomputable def terms (K B C p q : ℕ) :=
  max (L (K*C+p)+2*L q-(B-1:ℕ)*L p)
    (max (2*L p+L (K*B+q)-(C-1:ℕ)*L q)
      (L (K+p*q)-(B-1:ℕ)*L p-(C-1:ℕ)*L q))
noncomputable def compLimit (K B C : ℕ) (x y : ℝ) :=
  L 3+max 0 (max (L (2*C*B*K)+2*x+(C-1:ℕ)*y)
    (L (6*C^2*B)+16+max (L K) x+2*(C-1:ℕ)*y))
structure Model (K B C p q : ℕ) : Prop where
  co : (C-2:ℕ)*L q≤16*K+L (3*K*B)+(B-1:ℕ)*L p
  rev : (B-2:ℕ)*L p≤16*K+L (3*K*C)+(C-1:ℕ)*L q
  level : 16*(K:ℝ)≤L (3*B*C)+(B-1:ℕ)*L p+(C-1:ℕ)*L q
  near : 16*K+L (2*C*K)≤(B-1:ℕ)*L p → L q≤16*K+L (rest K B C p)
  far : L (C*K*B*p)+32≤16*(K-1:ℕ) → L (C*K)+32≤(B-1:ℕ)*L p → L q≤L (rest K B C p)
  exactInt : 0≤L 3+16*K+terms K B C p q
  limiting : 0≤32+max (terms K B C p q) (L (3*K*B*C)+2*L p+2*L q-16*(K-1:ℕ))
  comp : 2*C+3≤B → 16*(K:ℝ)≤compLimit K B C (L p) (L q)
  revComp : 2*B+3≤C → 16*(K:ℝ)≤compLimit K C B (L q) (L p)
private theorem comp_log {K B C x y : ℕ} (k0 : 0<K) (b0 : 0<B) (c0 : 0<C) (x0 : 0<x) (y0 : 0<y)
    (ub : 2^K≤1+2*C*B*K*x^2*y^(C-1)+6*C^2*B*(K+x)*(y^(C-1))^2) :
    16*(K:ℝ)≤compLimit K B C (L x) (L y) := by
  let U:=2*C*B*K;let V:=6*C^2*B
  have u : 0<U := by dsimp [U];positivity
  have v : 0<V := by dsimp [V];positivity
  change 2^K≤1+U*x^2*y^(C-1)+V*(K+x)*(y^(C-1))^2 at ub
  have h := sum_three (by positivity) (by decide : 0<1) (by positivity) (by positivity) ub
  rw [lpow,ltwo,lone,lmul (a:=U*x^2) (by positivity) (by positivity),lmul u (by positivity),
    lmul (a:=V*(K+x)) (by positivity) (by positivity),lmul v (by positivity),lpow,lpow,lpow] at h
  have plus : L (K+x)≤16+max (L K) (L x) := by
    simpa only [L,Nat.cast_add] using max_sum (by exact_mod_cast k0 : 0<(K:ℝ)) (by exact_mod_cast x0 : 0<(x:ℝ))
  unfold compLimit
  simp only [lpow,Nat.cast_ofNat] at h
  rw [mul_comm (K:ℝ)] at h
  refine h.trans ?_
  simp only [U,V] at *
  exact add_le_add le_rfl (max_le_max le_rfl (max_le_max le_rfl (by nlinarith only [plus])))
private theorem cofactor_log {x y a d k : ℕ} (xp : 0<x) (yp : 0<y)
    (h : y^(d-1)≤3*2^(k+1)*(k+1)*(a+1)*x^a) :
    (d-1:ℕ)*L y≤16*(k+1:ℕ)+L (3*(k+1)*(a+1))+a*L x := by
  rw [show 3*2^(k+1)*(k+1)*(a+1)*x^a=2^(k+1)*(3*(k+1)*(a+1))*x^a by ring] at h
  have g:=lmono (by positivity) h
  rw [lmul (by positivity) (by positivity),lmul (by positivity) (by positivity),lpow,lpow,lpow,ltwo] at g
  linarith only [g]
private theorem exact_logs {p q K B C : ℕ} (p0 : 0<p) (q0 : 0<q) (k0 : 0<K) (b0 : 0<B) (c0 : 0<C)
    (first : p^(B-1)*q^(C-1)≤(2^K-1)*OMA.SimultaneousBound245212.error p q K B C (p^(B-1)) (q^(C-1)))
    (second : 4*(2^K-1)*(p^(B-1)*q^(C-1))≤4*(2^K-1)*OMA.SimultaneousBound245212.error p q K B C (p^(B-1)) (q^(C-1))+
      9*K*p^2*q^2*B*C*p^(B-1)*q^(C-1)) :
    0≤L 3+16*K+terms K B C p q ∧
    0≤32+max (terms K B C p q) (L (3*K*B*C)+2*L p+2*L q-16*(K-1:ℕ)) := by
  let P:=p^(B-1);let Q:=q^(C-1);let G:=2^K-1
  let A:=(K*C+p)*q^2*Q;let D:=p^2*(K*B+q)*P;let E:=K+p*q;let H:=3*K*B*C
  have pp : 0<P := pow_pos p0 _
  have qq : 0<Q := pow_pos q0 _
  have gp : 0<G := by dsimp [G]; have:=Nat.one_lt_pow (by omega : K≠0) (by decide : 1<(2:ℕ));omega
  have ap : 0<A := by dsimp [A];positivity
  have dp : 0<D := by dsimp [D];positivity
  have ep : 0<E := by dsimp [E];positivity
  have hp : 0<H := by dsimp [H];positivity
  have err : OMA.SimultaneousBound245212.error p q K B C P Q=A+D+E := by
    dsimp [OMA.SimultaneousBound245212.error,A,D,E];ring
  change P*Q≤G*OMA.SimultaneousBound245212.error p q K B C P Q at first
  change 4*G*(P*Q)≤4*G*OMA.SimultaneousBound245212.error p q K B C P Q+9*K*p^2*q^2*B*C*P*Q at second
  rw [err] at first second
  have second' : G*P*Q≤G*A+G*D+G*E+H*p^2*q^2*P*Q := by
    dsimp [H];nlinarith only [second,Nat.zero_le (K*p^2*q^2*B*C*P*Q)]
  have fst : L (P*Q)≤L 3+max (L (G*A)) (max (L (G*D)) (L (G*E))) := by
    apply sum_three <;> first | positivity | nlinarith only [first]
  have snd := sum_four (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) second'
  have gmax : L G≤K*16 := by simpa only [lpow,ltwo] using lmono gp (Nat.sub_le (2^K) 1)
  have gmin : (K-1:ℕ)*16≤L G := by
    have tw : 0<(2:ℕ)^(K-1) := by positivity
    have sm : 2^(K-1)≤G := by dsimp [G];have:=pow_succ (2:ℕ) (K-1);rw [Nat.sub_add_cancel k0] at this;omega
    simpa only [lpow,ltwo] using lmono tw sm
  dsimp only [A,D,E] at fst snd
  simp (disch:=positivity) only [lmul,lpow,Nat.cast_ofNat] at fst snd
  dsimp [P,Q] at fst snd
  simp only [lpow] at fst snd
  dsimp only [H] at snd
  let t:=terms K B C p q
  let lp:=(B-1:ℕ)*L p
  let lq:=(C-1:ℕ)*L q
  have t1 : L (K*C+p)+2*L q-lp≤t := le_max_left _ _
  have t2 : 2*L p+L (K*B+q)-lq≤t := (le_max_left _ _).trans (le_max_right _ _)
  have t3 : L (K+p*q)-lp-lq≤t := (le_max_right _ _).trans (le_max_right _ _)
  have cap : max (L G+(L (K*C+p)+2*L q+lq))
      (max (L G+(2*L p+L (K*B+q)+lp)) (L G+L (K+p*q))) ≤ L G+lp+lq+t := by
    exact max_le (by linarith only [t1]) (max_le (by linarith only [t2]) (by linarith only [t3]))
  change lp+lq ≤ L 3+_ at fst
  change L G+lp+lq ≤ 32+_ at snd
  constructor
  · change 0≤L 3+16*K+t
    linarith only [fst,cap,gmax]
  · let h:=L (3*K*B*C)+2*L p+2*L q-16*(K-1:ℕ)
    have th : t ≤ max t h := le_max_left _ _
    have hh : h ≤ max t h := le_max_right _ _
    change 0≤32+max t h
    have all := max_le (cap.trans (by linarith only [th] : L G+lp+lq+t≤L G+lp+lq+max t h))
      (show L (3*K*B*C)+2*L p+2*L q+lp+lq≤L G+lp+lq+max t h by dsimp only [h] at hh;linarith only [gmin,hh])
    linarith only [snd,all]
theorem model {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 13≤p) (pq : p<q)
    (ha : 5≤a) (hd : 5≤d) (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    Model (k+1) (a+1) (d+1) p q := by
  let K:=k+1;let B:=a+1;let C:=d+1
  have k0 : 0<K := Nat.succ_pos _
  have b0 : 0<B := Nat.succ_pos _
  have c0 : 0<C := Nat.succ_pos _
  have p0:=hp.pos;have q0:=hq.pos
  have flip : OeisA245212.a (2^k*q^d*p^a)=(σ 1 (2^k*q^d*p^a):ℤ) := by rwa [mul_right_comm]
  have a2 : B-2=a-1 := by dsimp [B];omega
  have d2 : C-2=d-1 := by dsimp [C];omega
  have a1 : B-1=a := Nat.add_sub_cancel _ _
  have d1 : C-1=d := Nat.add_sub_cancel _ _
  have k1 : K-1=k := Nat.add_sub_cancel _ _
  have lx := OMA.TwoOddParameters245212.cofactor hp hq (by omega) (by omega) pq.ne (by omega) eqn
  have ly := OMA.TwoOddParameters245212.cofactor hq hp (by omega) (by omega) pq.ne.symm (by omega) flip
  have zc := OMA.ComplementaryDyad245212.level hp hq (by omega) (by omega) pq.ne (by omega) eqn
  change 2^K≤3*C*B*p^a*q^d at zc
  rw [show 3*C*B=3*B*C by ring] at zc
  have zl := lmono (by positivity : 0<(2:ℕ)^K) zc
  rw [lmul (a:=3*B*C*p^a) (by positivity) (by positivity),lmul (a:=3*B*C) (by positivity) (by positivity),
    lpow,lpow,lpow,ltwo] at zl
  have pb := prime_bound hp hq op pq ha hd eqn
  have kd := Nat.mul_le_mul_left k hd
  have sm : p-1<k*d := by omega
  have sm' : (p:ℤ)-1<(k:ℤ)*d := by zify [Nat.cast_sub hp.pos] at sm;exact sm
  have sep := separations hp hq (by omega) pq (by omega) (by omega) (by omega) sm' eqn
  obtain ⟨fi,se⟩ := OMA.SimultaneousBound245212.of_separations hp hq (by omega) (by omega) pq.ne eqn sep.1 sep.2
  have er := exact_logs (K:=K) (B:=B) (C:=C) p0 q0 k0 b0 c0 (by rw [a1,d1];exact fi)
    (by rw [a1,d1];simpa only [Nat.mul_assoc] using se)
  change Model K B C p q
  refine ⟨?_,?_,?_,?_,?_,er.1,er.2,?_,?_⟩
  · rw [d2,a1];exact cofactor_log p0 q0 lx
  · rw [a2,d1];exact cofactor_log q0 p0 ly
  · rw [a1,d1];linarith only [zl]
  · rw [a1]
    intro pole
    obtain ⟨s,succ⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
    have raw := OMA.ComplementaryPole245212.alternative hp hq (by omega) (by omega) pq.ne a s k (by omega) (by simpa [succ] using eqn)
    change p^a≤2*2^K*(s+2)*K ∨ q≤6*(s+2)*K*B*2^K*p^2 at raw
    have Cs : C=s+2 := by dsimp [C];omega
    rw [←Cs] at raw
    have poles : 2^K*(2*C*K)≤p^a := (lreflect (by positivity) (by positivity)).mp (by
      rw [lmul (by positivity) (by positivity),lpow,lpow,ltwo];linarith only [pole])
    rcases raw with le|qt
    · have equal : p^a=2*(2^K*C*K) := by nlinarith only [le,poles]
      obtain ⟨i,hi⟩ := (hp.odd_of_ne_two (by omega)).pow (n:=a)
      omega
    · have qt' : q≤2^K*rest K B C p := by dsimp [rest];nlinarith only [qt]
      have tmp := lmono q0 qt'
      rw [lmul (by positivity) (by dsimp [rest];positivity),lpow,ltwo] at tmp
      linarith only [tmp]
  · rw [a1,k1];intro first second
    have g : 4*(C*K*B*p)≤2^k := (lreflect (by positivity) (by positivity)).mp (by
      rw [lmul (by decide) (by positivity),lfour,lpow,ltwo];linarith only [first])
    have s : 4*(C*K)≤p^a := (lreflect (by positivity) (by positivity)).mp (by
      rw [lmul (by decide) (by positivity),lfour,lpow];linarith only [second])
    have longer : 2^k<2^K := by dsimp [K];rw [pow_succ];have:=Nat.two_pow_pos k;omega
    have qcap := OMA.ComplementaryFar245212.far hp hq (by omega) (by omega) pq.ne (by omega) (by omega) eqn
      (by change 4*K*C*B*p<2^K;nlinarith only [g,longer]) (by change 4*C*K≤p^a;nlinarith only [s])
    apply lmono q0
    dsimp [rest,K,B,C];nlinarith only [qcap]
  · intro med
    apply comp_log k0 b0 c0 p0 q0
    rw [d1];apply complement hp hq (by omega) (by omega) pq.ne (by omega) (by dsimp [C,B] at med;omega) eqn
  · intro med
    apply comp_log k0 c0 b0 q0 p0
    rw [a1];apply complement hq hp (by omega) (by omega) pq.ne.symm (by omega) (by dsimp [C,B] at med;omega) flip
end OMA.OddBox245212
end
section
namespace OMA.OddBox245212
structure Fits (f : Frame) (K B C p q : ℕ) : Prop where
  kl0 : 6≤f.kl
  bl0 : 6≤f.bl
  cl0 : 6≤f.cl
  lo0 : 1≤f.lo
  lk : f.kl≤K
  hk : K≤f.kh
  lb : f.bl≤B
  hb : B≤f.bh
  lc : f.cl≤C
  hc : C≤f.ch
  lp : f.lo≤p
  hp : p≤f.hi
  lq : f.qlo≤q
  pq : p≤q
namespace Fits
variable {f : Frame} {K B C p q : ℕ} (t : Fits f K B C p q)
include t
theorem pos : 0<K ∧ 0<B ∧ 0<C ∧ 0<p ∧ 0<q := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩:=t;omega
theorem xp_lower : (f.xp:ℝ)≤(B-1:ℕ)*L p := by
  have lo:=down_le t.lo0 t.lp
  have l0 : 0≤(down f.lo:ℝ) := by unfold down;positivity
  have b : (f.bl-1:ℕ)≤B-1 := Nat.sub_le_sub_right t.lb 1
  simp only [Frame.xp,Int.cast_mul,Int.cast_natCast]
  exact mul_le_mul (by exact_mod_cast b) lo l0 (by positivity)
theorem xp_upper : (B-1:ℕ)*L p≤((f.bh-1:ℕ)*up f.hi:ℤ) := by
  have u:=le_up t.pos.2.2.2.1 t.hp
  have b := Nat.sub_le_sub_right t.hb 1
  push_cast
  exact mul_le_mul (by exact_mod_cast b) u (nat_nonneg _ t.pos.2.2.2.1) (by positivity)
theorem rhs : 16*(K:ℝ)+L (3*K*B)≤f.cap := by
  obtain ⟨k,b,c,p',q'⟩:=t.pos
  have ha := le_up (by positivity : 0<3*K*B) (show 3*K*B≤3*f.kh*f.bh by gcongr <;> first | exact t.hk | exact t.hb)
  have hK : (K:ℝ)≤f.kh := by exact_mod_cast t.hk
  simp only [Frame.cap,Frame.dz,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat]
  linarith
theorem caps (model : Model K B C p q) :
    (f.cl-2:ℕ)*L q≤(f.capY:ℝ) ∧
    ((f.cl:ℝ)-f.bh-1)*L q≤f.cap ∧
    L q≤f.y ∧ 2*L q-(B-1:ℕ)*L p≤f.normalized := by
  obtain ⟨kp,bp,cp,pp,qp⟩:=t.pos
  have qn:=nat_nonneg q qp
  have pn:=nat_nonneg p pp
  have kU : (K:ℝ)≤f.kh := by exact_mod_cast t.hk
  have kL : (f.kl-1:ℕ)≤K-1 := Nat.sub_le_sub_right t.lk _
  have c0:=t.cl0
  have clc : (f.cl-2:ℕ)≤C-2 := Nat.sub_le_sub_right t.lc _
  have bt := t.xp_upper
  have bi := t.xp_lower
  have co := model.co
  have right := t.rhs
  have cc := mul_le_mul_of_nonneg_right (show ((f.cl-2:ℕ):ℝ)≤(C-2:ℕ) by exact_mod_cast clc) qn
  have reduced : (f.cl-2:ℕ)*L q≤(f.cap:ℝ)+(B-1:ℕ)*L p := by linarith only [cc,co,right]
  have cY : (f.cl-2:ℕ)*L q≤(f.capY:ℝ) := by
    simp only [Frame.capY,Int.cast_add,Int.cast_mul,Int.cast_natCast] at bt ⊢
    linarith only [reduced,bt]
  have ordered : ((f.cl:ℝ)-f.bh-1)*L q≤f.cap := by
    have cb := Nat.sub_le_sub_right t.hb 1
    have mul := mul_le_mul (show ((B-1:ℕ):ℝ)≤(f.bh-1:ℕ) by exact_mod_cast cb)
      (lmono pp t.pq) pn (by positivity : (0:ℝ)≤(f.bh-1:ℕ))
    have bhp : 1≤f.bh := bp.trans_le t.hb
    simp only [Nat.cast_sub (by omega : 2≤f.cl),Nat.cast_sub bhp,Nat.cast_ofNat,Nat.cast_one] at reduced mul
    nlinarith only [reduced,mul]
  have y₁ := over_bound (show 0<f.cl-2 by omega) cY
  have rest : L (rest K B C p)≤f.residue := by
    unfold Frame.residue
    apply le_up (by dsimp [rest];positivity)
    unfold OddBox245212.rest
    gcongr <;> first | exact t.hk | exact t.hc | exact t.hb | exact t.hp
  have kdz : 16*(K:ℝ)≤f.dz := by
    simp only [Frame.dz,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
    linarith only [kU]
  have dgl : (f.dg:ℝ)≤16*(K-1:ℕ) := by
    simp only [Frame.dg,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast kL) (by norm_num)
  have y₂ : f.dz+up (2*f.ch*f.kh)≤f.xp → L q≤(f.dz+f.residue:ℤ) := by
    intro pre
    have pre' : (f.dz:ℝ)+up (2*f.ch*f.kh)≤f.xp := by exact_mod_cast pre
    have cv:=le_up (by positivity : 0<2*C*K) (show 2*C*K≤2*f.ch*f.kh by gcongr <;> first | exact t.hc | exact t.hk)
    have nz := model.near (by linarith only [pre',cv,kdz,bi])
    push_cast;linarith only [nz,kdz,rest]
  have y₃ : max (up (f.ch*f.kh*f.bh*f.hi)-f.dg) (up (f.ch*f.kh)-f.xp)≤ -32 → L q≤f.residue := by
    intro pre
    obtain ⟨u,v⟩:=max_le_iff.mp pre
    have wt:=le_up (by positivity : 0<C*K*B*p) (show C*K*B*p≤f.ch*f.kh*f.bh*f.hi by gcongr <;> first | exact t.hc | exact t.hk | exact t.hb | exact t.hp)
    have kt:=le_up (by positivity : 0<C*K) (show C*K≤f.ch*f.kh by gcongr <;> first | exact t.hc | exact t.hk)
    have u' : (up (f.ch*f.kh*f.bh*f.hi):ℝ)-f.dg≤ -32 := by exact_mod_cast u
    have v' : (up (f.ch*f.kh):ℝ)-f.xp≤ -32 := by exact_mod_cast v
    exact (model.far (by linarith only [wt,u',dgl]) (by linarith only [kt,v',bi])).trans rest
  have bound : L q≤f.y := by
    simp only [Int.cast_add] at y₂
    unfold Frame.y
    split <;> split <;> push_cast <;> try simp only [le_min_iff]
    all_goals tauto
  have ratio : (f.cl-2:ℕ)*(2*L q-(B-1:ℕ)*L p)≤(2*f.cap-(f.cl-4:ℕ)*f.xp:ℤ) := by
    have factor := mul_le_mul_of_nonneg_left bi (show (0:ℝ)≤(f.cl-4:ℕ) by positivity)
    simp only [Int.cast_sub,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,Nat.cast_sub (by omega : 4≤f.cl),
      Nat.cast_sub (by omega : 2≤f.cl),Nat.cast_ofNat] at factor reduced ⊢
    nlinarith only [reduced,factor]
  have y₄ := over_bound (show 0<f.cl-2 by omega) ratio
  refine ⟨cY,ordered,bound,?_⟩
  simp only [Frame.normalized,Int.cast_min,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,le_min_iff]
  exact ⟨y₄,by linarith only [bound,bi]⟩
end Fits
end OMA.OddBox245212
end
section
namespace OMA.OddBox245212
open scoped ArithmeticFunction.sigma
set_option maxHeartbeats 1400000 in
private theorem down_nonneg (n : ℕ) : 0≤(down n:ℝ) := by
  simp only [down,Int.cast_natCast,Nat.cast_nonneg]
set_option maxHeartbeats 1400000 in
private theorem comp_false {kl kh bl bh ch K B C : ℕ} {x y : ℝ} {X Y : ℤ}
    (kp : 0<K) (bp : 0<B) (cp : 0<C) (klK : kl≤K) (Kkh : K≤kh)
    (blB : bl≤B) (Bbh : B≤bh) (Cch : C≤ch) (y0 : 0≤y) (lx : x≤X) (ly : y≤Y)
    (hit : 2*C+3≤B → 16*(K:ℝ)≤compLimit K B C x y) : compVeto kl kh bl bh ch X Y=false := by
  unfold compVeto
  simp only [decide_eq_false_iff_not,not_and]
  intro big fail
  have bound:=hit (by omega)
  have low : 16*(kl:ℝ)≤16*K := by gcongr
  have cut := le_up (a:=2*C*B*K) (by positivity)
    (show 2*C*B*K≤2*ch*bh*kh by gcongr)
  have cut' := le_up (a:=6*C^2*B) (by positivity)
    (show 6*C^2*B≤6*ch^2*bh by gcongr)
  have Y0 : 0≤(Y:ℝ) := y0.trans ly
  have cy : (C-1:ℕ)*y≤(ch-1:ℕ)*(Y:ℝ) :=
    mul_le_mul (by exact_mod_cast Nat.sub_le_sub_right Cch 1) ly y0 (by positivity)
  have mk := max_le_max (le_up kp Kkh) lx
  have a := (enclosed 3 (by decide)).2
  have z : 16*(kl:ℤ) ≤ max 0 (max (up (2*ch*bh*kh)+2*X+(ch-1:ℕ)*Y)
      (up (6*ch^2*bh)+16+max (up kh) X+2*(ch-1:ℕ)*Y))+up 3 := by
    apply Int.cast_le (R:=ℝ) |>.mp
    push_cast
    unfold compLimit at bound
    have le := max_le_max (a:= (0:ℝ)) le_rfl (max_le_max
      (show L (2*C*B*K)+2*x+(C-1:ℕ)*y≤(up (2*ch*bh*kh):ℝ)+2*X+(ch-1:ℕ)*(Y:ℝ) by linarith only [cut,lx,cy])
      (show L (6*C^2*B)+16+max (L K) x+2*(C-1:ℕ)*y≤(up (6*ch^2*bh):ℝ)+16+max (up kh:ℝ) (X:ℝ)+2*(ch-1:ℕ)*(Y:ℝ)
        by nlinarith only [cut',mk,cy]))
    linarith only [low,bound,le,a]
  omega
set_option maxHeartbeats 6000000 in
theorem Fits.retain {f : Frame} {K B C p q : ℕ} (t : Fits f K B C p q) (m : Model K B C p q) :
    f.reject=false := by
  obtain ⟨kp,bp,cp,pp,qp⟩:=t.pos
  obtain ⟨co,ord,y,norm⟩:=t.caps m
  have lo:=t.lo0
  have lq0 : 0<f.qlo := by dsimp [Frame.qlo];omega
  have dl := down_le lo t.lp
  have dq := down_le lq0 t.lq
  have dqn := down_nonneg f.qlo
  have hp := le_up pp t.hp
  have pn := nat_nonneg p pp
  have qn := nat_nonneg q qp
  have ch : ((C-1:ℕ):ℝ)≤(f.ch-1:ℕ) := by exact_mod_cast Nat.sub_le_sub_right t.hc 1
  have yd : (C-1:ℕ)*L q≤(f.ch-1:ℕ)*(f.y:ℝ) :=
    mul_le_mul ch y qn (Nat.cast_nonneg (α:=ℝ) _)
  have xp := t.xp_lower
  have pU := t.xp_upper
  have kmin : 16*(f.kl:ℝ)≤16*K := mul_le_mul_of_nonneg_left (by exact_mod_cast t.lk) (by norm_num)
  have kmax : 16*(K:ℝ)≤f.dz := by
    simp only [Frame.dz,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast t.hk) (by norm_num)
  have dg : (f.dg:ℝ)≤16*(K-1:ℕ) := by
    simp only [Frame.dg,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le_sub_right t.lk 1) (by norm_num)
  have rev : (f.bl-2:ℕ)*down f.lo≤f.dz+up (3*f.kh*f.ch)+(f.ch-1:ℕ)*f.y := by
    apply Int.cast_le (R:=ℝ) |>.mp
    push_cast
    have scale:= mul_le_mul (show ((f.bl-2:ℕ):ℝ)≤(B-2:ℕ) by exact_mod_cast Nat.sub_le_sub_right t.lb 2)
      dl (down_nonneg f.lo) (Nat.cast_nonneg (α:=ℝ) _)
    have u:=le_up (by positivity : 0<3*K*C) (show 3*K*C≤3*f.kh*f.ch by with_reducible gcongr <;> first | exact t.hk | exact t.hc)
    linarith only [scale,m.rev,yd,kmax,u]
  have z : 16*(f.kl:ℤ)≤up (3*f.bh*f.ch)+(f.bh-1:ℕ)*up f.hi+(f.ch-1:ℕ)*f.y := by
    apply Int.cast_le (R:=ℝ) |>.mp
    push_cast at pU ⊢
    have u:=le_up (by positivity : 0<3*B*C) (show 3*B*C≤3*f.bh*f.ch by with_reducible gcongr <;> first | exact t.hb | exact t.hc)
    linarith only [kmin,m.level,yd,pU,u]
  have yl : (f.cl-1:ℕ)*(down f.qlo:ℝ)≤(C-1:ℕ)*L f.qlo :=
    mul_le_mul (by exact_mod_cast Nat.sub_le_sub_right t.lc 1) (enclosed _ lq0).1 dqn (Nat.cast_nonneg (α:=ℝ) (C-1))
  have termle : terms K B C p q≤f.largest := by
    have c2 : 1≤C-1 := by have := t.cl0;have := t.lc;omega
    have nr := increasing_gap (a:=K*B) (b:=1) c2 lq0 t.lq (by positivity)
    simp only [one_mul] at nr
    have ns := increasing_gap (a:=K) (b:=p) c2 lq0 t.lq (by positivity)
    have u1:=le_up (by positivity : 0<K*C+p) (show K*C+p≤f.kh*f.ch+f.hi by with_reducible gcongr <;> first | exact t.hk | exact t.hc | exact t.hp)
    have u2:=le_up (by positivity : 0<K*B+f.qlo) (show K*B+f.qlo≤f.kh*f.bh+f.qlo by with_reducible gcongr <;> first | exact t.hk | exact t.hb)
    have u3:=le_up (by positivity : 0<K+p*f.qlo) (show K+p*f.qlo≤f.kh+f.hi*f.qlo by with_reducible gcongr <;> first | exact t.hk | exact t.hp)
    unfold terms Frame.largest Frame.e1 Frame.e2 Frame.e3 Frame.yq
    push_cast
    exact max_le_max (by linarith only [norm,u1]) (max_le_max (by linarith only [nr,hp,yl,u2]) (by linarith only [ns,xp,yl,u3]))
  have drift : L (3*K*B*C)+2*L p+2*L q-16*(K-1:ℕ)≤f.drift := by
    have u:=le_up (by positivity : 0<3*K*B*C) (show 3*K*B*C≤3*f.kh*f.bh*f.ch by with_reducible gcongr <;> first | exact t.hk | exact t.hb | exact t.hc)
    unfold Frame.drift;push_cast;linarith only [dg,hp,y,u]
  have ex : 0≤f.largest+up 3+f.dz := by
    apply Int.cast_le (R:=ℝ) |>.mp
    push_cast
    linarith only [m.exactInt,kmax,termle,(enclosed 3 (by decide)).2]
  have lim : 0 ≤ max f.largest f.drift+32 := by
    apply Int.cast_le (R:=ℝ) |>.mp
    push_cast
    linarith only [m.limiting,max_le_max termle drift]
  have pl : f.lo≤f.hi := t.lp.trans t.hp
  have qco : (f.cl-2:ℕ)*down f.qlo≤f.capY := by
    apply Int.cast_le (R:=ℝ) |>.mp
    push_cast;exact (mul_le_mul_of_nonneg_left dq (Nat.cast_nonneg (α:=ℝ) (f.cl-2))).trans co
  have order : ((f.cl:ℤ)-f.bh-1)*down f.qlo≤f.cap := by
    apply Int.cast_le (R:=ℝ) |>.mp
    push_cast
    by_cases h : 0≤(f.cl:ℝ)-f.bh-1
    · exact (mul_le_mul_of_nonneg_left dq h).trans ord
    · have plus := t.rhs
      have c0:=nat_nonneg _ (by positivity : 0<3*K*B)
      nlinarith only [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) dqn,plus,c0,(Nat.cast_nonneg (α:=ℝ) K)]
  have qcut : down f.qlo≤f.y := by exact_mod_cast dq.trans y
  have cmp := comp_false kp bp cp t.lk t.hk t.lb t.hb t.hc qn hp y m.comp
  have swp := comp_false kp cp bp t.lk t.hk t.lc t.hc t.hb pn y hp m.revComp
  unfold Frame.reject
  rw [cmp,swp]
  simp only [Bool.or_false,decide_eq_false_iff_not,not_or,not_lt]
  exact ⟨pl,qco,order,qcut,rev,z,ex,lim⟩
set_option maxHeartbeats 1400000 in
theorem veto_false {p q a d k kl kh bl bh cl ch pl ph : ℕ}
    (hp : p.Prime) (hq : q.Prime) (op : 13≤p) (pq : p<q) (ha : 5≤a) (hd : 5≤d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ))
    (lk : kl≤k+1) (uk : k+1≤kh) (lb : bl≤a+1) (ub : a+1≤bh)
    (lc : cl≤d+1) (uc : d+1≤ch) (plp : pl≤p) (php : p≤ph) :
    veto kl kh bl bh cl ch pl ph=false := by
  unfold veto;split
  · rename_i cond
    obtain ⟨L,U,Q⟩:=prime_window hp hq op pq ha hd lk uk (by omega) lb plp php eqn
    have pos : 0<lowPrime kl bl pl := by dsimp [lowPrime];omega
    apply Fits.retain _ (model hp hq op pq ha hd eqn)
    exact ⟨cond.1,cond.2.1,cond.2.2,pos,lk,uk,lb,ub,lc,uc,L,U,Q,pq.le⟩
  · rfl
end OMA.OddBox245212
end
section
namespace OMA.OddBox245212
def scan : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool → Bool
  | 0,_,_,_,_,_,_ => false
  | f+1,m,kl,kh,ml,mh,swap =>
    let top := min mh (min (64*m^2*kh) (32768*m^6))
    if kh < kl ∨ top < ml then true else
    let out := if swap then veto kl kh m m ml top 13 (3*kh)
      else veto kl kh ml top m m 13 (3*kh)
    if out then true else
    if kh*ml ≥ top*kl ∧ kl < kh then
      let mid := Nat.sqrt (kl*kh)
      scan f m kl mid ml top swap && scan f m (mid+1) kh ml top swap
    else
      let mid := Nat.sqrt (ml*top)
      scan f m kl kh ml mid swap && scan f m kl kh (mid+1) top swap
theorem scan_misses {K m M : ℕ} (swap : Bool) (fit : M ≤ 64*m^2*K) (global : M ≤ 32768*m^6)
    (retain : ∀ kl kh ml mh, kl ≤ K → K ≤ kh → ml ≤ M → M ≤ mh →
      (if swap then veto kl kh m m ml mh 13 (3*kh) else veto kl kh ml mh m m 13 (3*kh))=false)
    (fuel kl kh ml mh : ℕ) (lk : kl ≤ K) (hk : K ≤ kh) (lm : ml ≤ M) (hm : M ≤ mh) :
    scan fuel m kl kh ml mh swap=false := by
  induction fuel generalizing kl kh ml mh with
  | zero => rfl
  | succ f ih =>
    let top := min mh (min (64*m^2*kh) (32768*m^6))
    have ht : M ≤ top := le_min hm (le_min (fit.trans (Nat.mul_le_mul_left _ hk)) global)
    change (if kh < kl ∨ top < ml then _ else _) = false
    rw [if_neg (by omega),retain kl kh ml top lk hk lm ht]
    simp only [Bool.false_eq_true,↓reduceIte]
    split
    · let mid := Nat.sqrt (kl*kh)
      change (scan f m kl mid ml top swap && scan f m (mid+1) kh ml top swap)=false
      by_cases h : K ≤ mid
      · simp [ih kl mid ml top lk h lm ht]
      · simp [ih (mid+1) kh ml top (by omega) hk lm ht]
    · let mid := Nat.sqrt (ml*top)
      change (scan f m kl kh ml mid swap && scan f m kl kh (mid+1) top swap)=false
      by_cases h : M ≤ mid
      · simp [ih kl kh ml mid lk hk lm h]
      · simp [ih kl kh (mid+1) top lk hk (by omega) ht]
def exterior (m : ℕ) : Bool :=
  [false,true].all fun swap =>
    let ml := if swap then m+1 else m
    scan 40 m 1251 (512*m^4) ml (32768*m^6) swap &&
      scan 40 m 6 1250 (max 226 ml) (32768*m^6) swap
set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
theorem table {m : ℕ} (lo : 6 ≤ m) (hi : m ≤ 32) : exterior m=true := by
  interval_cases m <;> decide +kernel
theorem rectangle {m M K : ℕ} (swap : Bool) (hm : 6 ≤ m) (small : m ≤ 32)
    (order : (if swap then m+1 else m) ≤ M) (hk : 6 ≤ K) (kb : K ≤ 512*m^4)
    (mb : M ≤ 64*m^2*K) (mg : M ≤ 32768*m^6)
    (retain : ∀ kl kh ml mh, kl ≤ K → K ≤ kh → ml ≤ M → M ≤ mh →
      (if swap then veto kl kh m m ml mh 13 (3*kh) else veto kl kh ml mh m m 13 (3*kh))=false) :
    K ≤ 1250 ∧ M ≤ 225 := by
  have h := table hm small
  unfold exterior at h
  have member : swap∈[false,true] := by cases swap <;> simp
  have both := List.all_eq_true.mp h swap member
  simp only [Bool.and_eq_true] at both
  obtain ⟨one,two⟩ := both
  have bound : K ≤ 1250 := by
    by_contra! large
    have := scan_misses swap mb mg retain 40 _ _ _ _ (by omega : 1251 ≤ K) kb order mg
    grind
  refine ⟨bound,?_⟩
  by_contra! large
  have := scan_misses swap mb mg retain 40 _ _ _ _ hk bound (max_le (by omega : 226 ≤ M) order) mg
  grind
end OMA.OddBox245212
end
section
namespace OMA.TwoOddErrorCells245212
open OMA.SimultaneousBound245212
theorem alternatives {p q K B C P Q G R h u : ℕ}
    (rpos : 0<R) (rP : R≤P) (rQ : R≤Q) (qR : q*R≤h*Q) (ph : p≤h) (bu : B≤u) (cu : C≤u)
    (necessary : P*Q≤G*error p q K B C P Q) :
    P≤3*G*(K*u+h)*q^2 ∨ R≤3*G*h^2*(K*u+h) ∨ R^2≤3*G*(K+h^2) := by
  by_contra! no
  have A : 3*G*q^2*(K*C+p)<P := calc
    _ ≤ 3*G*q^2*(K*u+h) := by gcongr
    _ = _ := by ring
    _ < _ := no.1
  have second : 3*G*p^2*(K*B+q)<Q := by
    apply (mul_lt_mul_iff_left₀ rpos).mp
    calc
      _ = 3*G*p^2*(K*B*R+q*R) := by ring
      _ ≤ 3*G*h^2*(K*u*Q+h*Q) := by gcongr
      _ = (3*G*h^2*(K*u+h))*Q := by ring
      _ < R*Q := Nat.mul_lt_mul_of_pos_right no.2.1 (lt_of_lt_of_le rpos rQ)
      _ = _ := by ring
  have third : 3*G*(K+p*q)<P*Q := by
    apply (mul_lt_mul_iff_left₀ rpos).mp
    calc
      _ = 3*G*(K*R+p*(q*R)) := by ring
      _ ≤ 3*G*(K*Q+h*(h*Q)) := by gcongr
      _ = 3*G*(K+h^2)*Q := by ring
      _ < R^2*Q := Nat.mul_lt_mul_of_pos_right no.2.2 (lt_of_lt_of_le rpos rQ)
      _ ≤ (P*Q)*R := by nlinarith only [Nat.mul_le_mul_right (R*Q) rP]
  unfold error at necessary
  nlinarith only [necessary,Nat.mul_lt_mul_of_pos_right A (rpos.trans_le rQ),
    Nat.mul_lt_mul_of_pos_right second (rpos.trans_le rP),third]
theorem first_excluded {m G K u h q R P v : ℕ} (hm : 4 ≤ m) (rP : R≤P) (pp : 0<P)
    (qcap : q^(m-2)≤v*P)
    (test : (3*G*(K*u+h))^(m-2)*v^2<R^(m-4)) :
    3*G*(K*u+h)*q^2<P := by
  let a:=3*G*(K*u+h)
  change a^(m-2)*v^2<R^(m-4) at test
  change a*q^2<P
  apply lt_of_not_ge
  intro bad
  have hw := Nat.pow_le_pow_left bad (m-2)
  rw [mul_pow,←pow_mul,mul_comm 2 (m-2),pow_mul] at hw
  have qq := Nat.pow_le_pow_left qcap 2
  rw [mul_pow] at qq
  have big := hw.trans (Nat.mul_le_mul_left (a^(m-2)) qq)
  have tight := Nat.mul_lt_mul_of_pos_right (test.trans_le (Nat.pow_le_pow_left rP (m-4)))
    (pow_pos pp 2)
  rw [←pow_add,show m-4+2=m-2 by omega] at tight
  rw [←mul_assoc] at big
  exact (not_lt_of_ge big) tight
theorem second_excluded {p q K B C P Q G R h y u t : ℕ} (rpos : 0<R) (rP : R≤P) (rQ : R≤Q)
    (ph : p≤h) (qy : q≤y) (bu : B≤u) (cu : C≤u) (prod : B*C≤t)
    (necessary : 4*G*P*Q≤4*G*error p q K B C P Q+9*K*p^2*q^2*B*C*P*Q)
    (test : 4*G*((y^2*(K*u+h)+h^2*(K*u+y))*R+(K+h*y))+
      9*K*h^2*y^2*t*R^2 < 4*G*R^2) : False := by
  let a:=y^2*(K*u+h)
  let b:=h^2*(K*u+y)
  let c:=K+h*y
  have aa : q^2*(K*C+p)≤a := by dsimp [a];gcongr
  have bb : p^2*(K*B+q)≤b := by dsimp [b];gcongr
  have cc : K+p*q≤c := by dsimp [c];gcongr
  have re : R^2*error p q K B C P Q≤((a+b)*R+c)*(P*Q) := by
    have lo1 := Nat.mul_le_mul aa (Nat.mul_le_mul_right (R*Q) rP)
    have lo2 := Nat.mul_le_mul bb (Nat.mul_le_mul_right (R*P) rQ)
    have lo3 := Nat.mul_le_mul cc (Nat.mul_le_mul rP rQ)
    dsimp [error];nlinarith only [lo1,lo2,lo3]
  have tr : 9*K*p^2*q^2*B*C≤9*K*h^2*y^2*t := calc
    _ = 9*K*p^2*q^2*(B*C) := by ring
    _ ≤ _ := by gcongr
  change 4*G*((a+b)*R+c)+9*K*h^2*y^2*t*R^2<4*G*R^2 at test
  have cmp := Nat.mul_lt_mul_of_pos_right test (Nat.mul_pos (rpos.trans_le rP) (rpos.trans_le rQ))
  nlinarith only [cmp,Nat.mul_le_mul_left (R^2) necessary,Nat.mul_le_mul_left (4*G) re,
    Nat.mul_le_mul_right (P*Q*R^2) tr]
end OMA.TwoOddErrorCells245212
end
section
namespace OMA.TwoOddCoarse245212
open OMA.SimultaneousBound245212 OMA.TwoOddErrorCells245212
theorem coarse {p q K B C P Q G R m u : ℕ} (hK : 1≤K) (hu : 1≤u)
    (rpos : 0<R) (rP : R≤P) (rQ : R≤Q) (qR : q*R≤(5*K)*Q) (ph : p≤5*K)
    (bu : B≤u) (cu : C≤u) (uB : u≤64*m^2*K) (gz : G≤2^K)
    (necessary : P*Q≤G*error p q K B C P Q) (fourth : q^4≤3*2^K*K*u*P) :
    R≤2^(37+3*K)*K^10*m^8 := by
  let z:ℕ:=2^K
  change q^4≤3*z*K*u*P at fourth
  have zp : 1≤z := Nat.one_le_pow _ _ (by decide)
  have KK : K*u+5*K≤6*K*u := by nlinarith only [Nat.mul_le_mul_left K hu]
  have target : R≤6400*z^3*K^6*u^4 := by
    rcases alternatives rpos rP rQ qR ph bu cu necessary with x|x|x
    · have w : P≤3*z*(6*K*u)*q^2 := x.trans (by gcongr)
      have sq := Nat.pow_le_pow_left w 2
      simp only [mul_pow] at sq
      rw [←pow_mul q 2 2] at sq
      have sq' := sq.trans (Nat.mul_le_mul_left _ fourth)
      have shrink : P≤972*z^3*K^3*u^3 := by
        apply (mul_le_mul_iff_left₀ (rpos.trans_le rP)).mp
        nlinarith only [sq']
      have gain := Nat.mul_le_mul (Nat.pow_le_pow_right hK (show 3≤6 by decide))
        (Nat.pow_le_pow_right hu (show 3≤4 by decide))
      have gain' := Nat.mul_le_mul (Nat.mul_le_mul_right (z^3) (show 972≤6400 by decide)) gain
      exact rP.trans (shrink.trans (by nlinarith only [gain']))
    · have z3 : z≤z^3 := by simpa using (Nat.pow_le_pow_right zp (show 1≤3 by decide))
      have ub : u≤u^4 := by simpa using (Nat.pow_le_pow_right hu (show 1≤4 by decide))
      have w : R≤3*z*(5*K)^2*(6*K*u) := x.trans (by gcongr)
      have lo := Nat.mul_le_mul (Nat.mul_le_mul z3 (Nat.pow_le_pow_right hK (show 3≤6 by decide))) ub
      nlinarith only [w,Nat.mul_le_mul (show 450≤6400 by decide) lo]
    · have rr : R≤R^2 := by simpa using (Nat.pow_le_pow_right rpos (show 1≤2 by decide))
      have zz : z≤z^3 := by simpa using (Nat.pow_le_pow_right zp (show 1≤3 by decide))
      have k2 : K≤K^2 := by simpa using (Nat.pow_le_pow_right hK (show 1≤2 by decide))
      have w : R≤3*z*(26*K^2) := rr.trans (x.trans
        (Nat.mul_le_mul (Nat.mul_le_mul_left 3 gz) (by nlinarith only [k2])))
      have lower := Nat.mul_le_mul (Nat.mul_le_mul zz (Nat.pow_le_pow_right hK (show 2≤6 by decide)))
        (Nat.one_le_pow 4 u hu)
      nlinarith only [w,Nat.mul_le_mul (show 78≤6400 by decide) lower]
  have scale := target.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left uB 4))
  have eqn : 6400*z^3*K^6*(64*m^2*K)^4 = (6400*64^4)*(2^(3*K))*K^10*m^8 := by
    dsimp [z];rw [pow_mul 2 3 K,←pow_mul 2 K 3,mul_comm K 3,pow_mul];ring
  rw [eqn] at scale
  rw [pow_add]
  exact scale.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_right _ (show 6400*64^4≤(2:ℕ)^37 by decide))))
end OMA.TwoOddCoarse245212
end
section
namespace OMA.TwoOddGrowth245212
private theorem step {t c j n : ℕ} (ht : 0<t) (s : (t+1)^j≤c*t^j) (h : t≤n) :
    (n+1)^j≤c*n^j := by
  have spread : (n+1)*t≤(t+1)*n := by nlinarith only [h]
  have w := Nat.pow_le_pow_left spread j
  rw [mul_pow,mul_pow] at w
  exact (mul_le_mul_iff_left₀ (pow_pos ht j)).mp
    (by nlinarith only [w,Nat.mul_le_mul_right (n^j) s])
private theorem exponential {t c j : ℕ} (ht : 0<t) (s : (t+1)^j≤2*t^j)
    (base : c*t^j≤2^t) (n : ℕ) (hn : t≤n) : c*n^j≤2^n := by
  induction n,hn using Nat.le_induction with
  | base => exact base
  | succ n hn ih =>
    have hp := Nat.mul_le_mul_left c (step ht s hn)
    rw [pow_succ]
    nlinarith only [hp,ih]
theorem at256 {n : ℕ} (hn : 256≤n) :
    n^20≤2^n ∧ n^16≤2^n ∧ 2^65*n^21≤2^n := by
  refine ⟨?_,?_,exponential (by decide : 0<256) (by decide) (by decide) n hn⟩
  · simpa using exponential (c:=1) (j:=20) (by decide : 0<256) (by decide) (by decide) n hn
  · simpa using exponential (c:=1) (j:=16) (by decide : 0<256) (by decide) (by decide) n hn
theorem table_tail {K p m : ℕ} (klo : 3≤K) (khi : K≤255) (ml : 119 ≤ m)
    (least : OMA.TwoOddEffectiveTable245212.floorPrime K 119≤p) (p3 : 3≤p) :
    2^(37+3*K)*K^10*m^8<p^(m-1) := by
  have tail := (OMA.TwoOddEffectiveTable245212.ranges (m:=33) klo khi (by decide) (by decide)).1
  change decide (_ < _) = true at tail
  have t := of_decide_eq_true tail
  have ini := t.trans_le (Nat.pow_le_pow_left least 118)
  induction m,ml using Nat.le_induction with
  | base => exact ini
  | succ n hn ih =>
    have sf := step (j:=8) (c:=3) (by decide : 0<119) (by decide) hn
    calc
      _ ≤ 2^(37+3*K)*K^10*(3*n^8) := Nat.mul_le_mul_left _ sf
      _ = (2^(37+3*K)*K^10*n^8)*3 := by ring
      _ < p^(n-1)*p := Nat.mul_lt_mul_of_lt_of_le ih p3 (by omega)
      _ = p^((n+1)-1) := by rw [←pow_succ];congr 1;omega
theorem m_large {K m p : ℕ} (big : 256≤K) (pp : 3≤p)
    (input : p^(m-1)≤2^(37+3*K)*K^10*m^8) : m≤5*K := by
  by_cases sm : m<256
  · omega
  have mm := (at256 (by omega : 256 ≤ m)).2.1
  have kk := (at256 big).1
  have power := Nat.pow_le_pow_left input 2
  simp only [mul_pow,←pow_mul] at power
  have bound : (p^(m-1))^2≤2^(74+7*K+m) := calc
    _ ≤ (2^((37+3*K)*2))*K^20*m^16 := by rw [←pow_mul];exact power
    _ ≤ (2^((37+3*K)*2))*2^K*2^m := by gcongr
    _ = _ := by rw [←pow_add,←pow_add];congr 1;ring
  have nine : 8≤p^2 := (show 8≤(3:ℕ)^2 by decide).trans (Nat.pow_le_pow_left pp 2)
  have lo : 2^(3*(m-1)) ≤ (p^(m-1))^2 := by
    rw [pow_mul 2 3 (m-1),←pow_mul p (m-1) 2,mul_comm (m-1) 2,pow_mul p 2 (m-1)]
    exact Nat.pow_le_pow_left nine _
  have cut := (pow_le_pow_iff_right₀ (a:=(2:ℕ)) (by decide)).mp (lo.trans bound)
  omega
end OMA.TwoOddGrowth245212
end
section
namespace OMA.TwoOddLargeScale245212
open OMA.TwoOddGrowth245212
theorem estimates {K m p : ℕ} (big : 256≤K) (ml : 33 ≤ m) (ms : m≤5*K) (least : K≤3*p) :
    let h:=5*K; let u:=64*m^2*K; let t:=m*u; let R:=p^(m-1); let g:=2^K-1
    let y:=6*t*K*h^2
    4*K*t*h<2^K ∧ 4*u*K≤R ∧
      4*g*((y^2*(K*u+h)+h^2*(K*u+y))*R+(K+h*y))+
      9*K*h^2*y^2*t*R^2 < 4*g*R^2 := by
  let h:=5*K
  let u:=64*m^2*K
  let t:=m*u
  let R:=p^(m-1)
  let g:=2^K-1
  let y:=6*t*K*h^2
  change 4*K*t*h<2^K ∧ 4*u*K≤R ∧
    4*g*((y^2*(K*u+h)+h^2*(K*u+y))*R+(K+h*y))+9*K*h^2*y^2*t*R^2<4*g*R^2
  have kp : 1≤K := by omega
  have pp : 64≤p := by omega
  have r0 : 1≤R := Nat.one_le_pow _ _ (by omega)
  have zk := (at256 big).2.2
  have ub : u≤2^11*K^3 := calc
    _ ≤ 64*(5*K)^2*K := by dsimp [u];gcongr
    _ ≤ _ := by nlinarith only [Nat.zero_le (K^3)]
  have tb : t≤2^13*K^4 := calc
    _ ≤ (5*K)*(1600*K^3) := Nat.mul_le_mul ms
      (by dsimp [u];nlinarith only [Nat.mul_le_mul_right (64*K) (Nat.pow_le_pow_left ms 2)])
    _ ≤ _ := by nlinarith only [Nat.zero_le (K^4)]
  have yb : y≤2^21*K^7 := calc
    _ ≤ 6*(2^13*K^4)*K*(5*K)^2 := by dsimp only [y,h];gcongr
    _ ≤ _ := by nlinarith only [Nat.zero_le (K^7)]
  have high (c e : ℕ) (cc : c<2^65) (ee : e≤21) : c*K^e<2^K :=
    (Nat.mul_lt_mul_of_lt_of_le cc (Nat.pow_le_pow_right kp ee) (Nat.pow_pos kp)).trans_le zk
  have gc : 4*K*t*h<2^K := calc
    _ ≤ 4*K*(2^13*K^4)*(5*K) := by dsimp only [h];gcongr
    _ = 163840*K^6 := by ring
    _ < _ := high _ _ (by decide) (by decide)
  have p5 : K^4≤p^5 := by
    have lo := Nat.pow_le_pow_left least 5
    have w := Nat.mul_le_mul_right (K^4) (show 243≤K by omega)
    rw [mul_pow] at lo
    nlinarith only [lo,w]
  have p32 : K^24*p^2≤R := calc
    _ = (K^4)^6*p^2 := by ring
    _ ≤ (p^5)^6*p^2 := by gcongr
    _ = p^32 := by ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have room : 2^57*K^18≤R := calc
    _ ≤ (K^6*p^2)*K^18 := Nat.mul_le_mul_right _ ((show 2^57≤(256:ℕ)^6*64^2 by decide).trans
      (Nat.mul_le_mul (Nat.pow_le_pow_left big 6) (Nat.pow_le_pow_left pp 2)))
    _ = K^24*p^2 := by ring
    _ ≤ R := p32
  have pack {v c e : ℕ} (vb : v≤c*K^e) (cb : 2*c≤2^57) (eb : e≤18) : 2*v≤R := by
    have ext := Nat.mul_le_mul cb (Nat.pow_le_pow_right kp eb)
    nlinarith only [room,ext,vb]
  have pc : 4*u*K≤R := (show 4*u*K≤2*(4*u*K) by omega).trans
    (pack (c:=8192) (e:=4) (by nlinarith only [Nat.mul_le_mul_right (4*K) ub]) (by decide) (by decide))
  let aa:=y^2*(K*u+h)+h^2*(K*u+y)
  let bb:=K+h*y
  have sum : aa+bb≤2^56*K^18 := by
    have X (n : ℕ) (hn : n≤18) := Nat.pow_le_pow_right kp hn
    have M : aa+bb≤(2^21*K^7)^2*(K*(2^11*K^3)+5*K)+(5*K)^2*(K*(2^11*K^3)+2^21*K^7)+(K+(5*K)*(2^21*K^7)) := by
      dsimp only [aa,bb,h];gcongr
    nlinarith only [M,X 15 (by decide),X 6 (by decide),X 9 (by decide),X 8 (by decide),
      (show K≤K^18 by simpa using X 1 (by decide)),Nat.zero_le (K^18)]
  have ab := pack sum (by decide) (by decide)
  have drift : 9*K*h^2*y^2*t≤g := by
    have drift0 : 9*K*h^2*y^2*t≤9*K*(5*K)^2*(2^21*K^7)^2*(2^13*K^4) := by
      dsimp only [h];gcongr
    have iso : 9*K*(5*K)^2*(2^21*K^7)^2*(2^13*K^4)=8106479329266892800*K^21 := by ring
    rw [iso] at drift0
    have lt:=drift0.trans_lt (high _ _ (by decide) (by decide))
    dsimp [g];omega
  have gp : 0<g := by dsimp [g];have := Nat.one_lt_pow (by omega : K≠0) (by decide : 1<2);omega
  refine ⟨gc,pc,?_⟩
  change 4*g*(aa*R+bb)+(9*K*h^2*y^2*t)*R^2<4*g*R^2
  have margin := Nat.mul_le_mul_left (2*g*R) ab
  have br := Nat.mul_le_mul_left bb r0
  have plus := Nat.mul_le_mul_left (4*g) br
  nlinarith only [margin,plus,Nat.mul_le_mul_right (R^2) drift,Nat.mul_pos gp (pow_pos r0 2)]
end OMA.TwoOddLargeScale245212
end
section
namespace OMA.TwoOddEffectiveOriginal245212
open ArithmeticFunction OMA.TwoOddEffectiveTable245212
open scoped ArithmeticFunction.sigma
theorem bound {p q k a d : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p) (pq : p<q)
    (hk : 2≤k) (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    min (a+1) (d+1)≤32 := by
  by_contra! outside
  let K:=k+1
  let B:=a+1
  let C:=d+1
  let m:=min B C
  let u:=64*m^2*K
  let t:=m*u
  let h:=5*K
  let y:=6*t*K*h^2
  let z:ℕ:=2^K
  let g:=z-1
  let P:=p^a
  let Q:=q^d
  let R:=p^(m-1)
  have ml : 33 ≤ m := outside
  have mb : m≤B := min_le_left _ _
  have mc : m≤C := min_le_right _ _
  have a32 : 32≤a := by dsimp [B] at mb;omega
  have d32 : 32≤d := by dsimp [C] at mc;omega
  have k3 : 3≤K := by dsimp [K];omega
  have many : 5≤(a+1)*(d+1) := by nlinarith only [a32,d32,Nat.zero_le (a*d)]
  have sm := OMA.ComplementaryBase245212.small_prime hp hq op (by omega) pq.ne many eqn
  have ph : p≤h := sm.elim id (fun z=>pq.le.trans z)
  have swap : OeisA245212.a (2^k*q^d*p^a)=(σ 1 (2^k*q^d*p^a):ℤ) := by rwa [mul_right_comm]
  have both : B≤u ∧ C≤u ∧ B*C≤t := by
    have easy : m≤u := by
      dsimp [u];nlinarith only [Nat.mul_le_mul_left (64*m^2) (show 1≤K by omega),Nat.mul_le_mul_left m ml]
    by_cases ord : B≤C
    · have me : m=B := min_eq_left ord
      have c : C≤u := by
        dsimp [u];rw [me]
        exact OMA.ComplementaryExp245212.exponent hq hp (by omega) op pq.ne' (by omega) swap
      exact ⟨me ▸ easy,c,by dsimp only [t];rw [me];exact Nat.mul_le_mul_left _ c⟩
    · have me : m=C := min_eq_right (by omega)
      have b : B≤u := by
        dsimp [u];rw [me]
        exact OMA.ComplementaryExp245212.exponent hp hq op (by omega) pq.ne (by omega) eqn
      exact ⟨b,me ▸ easy,by dsimp only [t];rw [me,mul_comm C u];exact Nat.mul_le_mul_right _ b⟩
  obtain ⟨bu,cu,bc⟩:=both
  have r0 : 0<R := pow_pos hp.pos _
  have rP : R≤P := Nat.pow_le_pow_right hp.pos (by dsimp [B] at mb;omega)
  have rQ : R≤Q := (Nat.pow_le_pow_left pq.le _).trans (Nat.pow_le_pow_right hq.pos (by dsimp [C] at mc;omega))
  have eqm : m-1=m-2+1 := by omega
  have qR : q*R≤h*Q := calc
    _ = p*(p^(m-2)*q) := by dsimp [R];rw [eqm,pow_succ];ring
    _ ≤ h*(q^(m-2)*q) := Nat.mul_le_mul ph (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left pq.le _))
    _ = h*q^(m-1) := by rw [eqm,pow_succ]
    _ ≤ h*Q := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq.pos (by dsimp [C] at mc;omega))
  have co := OMA.TwoOddParameters245212.cofactor hp hq op (by omega) pq.ne (by omega) eqn
  have qcap : q^(m-2)≤3*z*K*u*P := calc
    _ ≤ q^(d-1) := Nat.pow_le_pow_right hq.pos (by dsimp [C] at mc;omega)
    _ ≤ 3*z*K*B*P := co
    _ ≤ _ := by gcongr
  have errs := OMA.SimultaneousBound245212.original hp hq op pq (by omega) (by omega) hk ph eqn
  change P*Q≤g*OMA.SimultaneousBound245212.error p q K B C P Q ∧
    4*g*P*Q≤4*g*OMA.SimultaneousBound245212.error p q K B C P Q+9*K*p^2*q^2*B*C*P*Q at errs
  have cg := OMA.TwoOddCoarse245212.coarse (m:=m) (by omega : 1≤K)
    (by dsimp [u];exact Nat.mul_pos (Nat.mul_pos (by decide) (pow_pos (by omega) _)) (by omega))
    r0 rP rQ qR ph bu cu (le_refl _) (Nat.sub_le z 1) errs.1
    ((Nat.pow_le_pow_right hq.pos (show 4 ≤ m-2 by omega)).trans qcap)
  have near {r : ℕ} (pr : 0<r) (lower : r≤R) (box : 2*(K*t*h*r+g*u*K)≤g*r) : q≤y := by
    have actu : K*C*B*p*r+g*C*K≤K*t*h*r+g*u*K := calc
      _ = K*(B*C)*p*r+g*C*K := by ring
      _ ≤ _ := by gcongr
    have sm' : p-1≤(d+1)*k := by
      dsimp [h,K] at ph;nlinarith only [ph,hk,Nat.mul_le_mul_left k d32,Nat.sub_le p 1]
    have hq':=OMA.TwoOddJoint245212.near hp hq op (by omega) pq.ne (by omega) (by omega) eqn
      sm' pr (lower.trans rP) ((Nat.mul_le_mul_left _ actu).trans box)
    change q≤6*C*K*B*p^2 at hq'
    exact hq'.trans (calc
      _ = 6*(B*C)*K*p^2 := by ring
      _ ≤ y := Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ bc)) (Nat.pow_le_pow_left ph _))
  by_cases big : 256≤K
  · have ms := OMA.TwoOddGrowth245212.m_large big op cg
    have lo := OMA.TwoOddParameters245212.reciprocal hp hq op (by omega) pq.ne (by omega) eqn
    have least : K≤3*p := by
      dsimp [K];by_contra! bad
      nlinarith only [lo,Nat.mul_le_mul_right a (show 2*p≤k by omega),Nat.mul_le_mul_left p a32]
    obtain ⟨gc,pc,fin⟩:=OMA.TwoOddLargeScale245212.estimates big ml ms least
    change 4*K*t*h<z at gc
    change 4*u*K≤R at pc
    have gc' : 4*K*C*B*p<z := (show 4*K*C*B*p≤4*K*t*h by
      nlinarith only [Nat.mul_le_mul_left (4*K) (Nat.mul_le_mul bc ph)]).trans_lt gc
    have qsmall := OMA.ComplementaryFar245212.far hp hq op (by omega) pq.ne (by omega) (by omega)
      eqn gc' (((Nat.mul_le_mul_right K (Nat.mul_le_mul_left 4 cu)).trans pc).trans rP)
    have qy : q≤y := qsmall.trans (calc
      _ = 6*(B*C)*K*p^2 := by dsimp [B,C,K];ring
      _ ≤ y := Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ bc)) (Nat.pow_le_pow_left ph 2))
    exact OMA.TwoOddErrorCells245212.second_excluded r0 rP rQ ph qy bu cu bc errs.2 fin
  · have klow : K≤255 := by omega
    have mmax : m≤118 := by
      by_contra! tail
      have pmin := OMA.TwoOddParameters245212.floor hp hq op (by omega) pq.ne (by omega) (by decide : 1≤119)
        (show 119≤a+1 by dsimp [B] at mb;omega) eqn
      exact (not_lt_of_ge cg) (OMA.TwoOddGrowth245212.table_tail k3 klow tail pmin op)
    let rr:=(floorPrime K m)^(m-1)
    have lp : floorPrime K m≤p := OMA.TwoOddParameters245212.floor hp hq op (by omega) pq.ne
      (by omega) (by omega) mb eqn
    have rr0 : 0<rr := pow_pos (lt_of_lt_of_le (by decide : 0<3) (le_max_left _ _)) _
    have rrR : rr≤R := Nat.pow_le_pow_left lp _
    have data := of_decide_eq_true (ranges k3 klow ml mmax).2
    change (3*g*h^2*(K*u+h)<rr ∧ 3*g*(K+h^2)<rr^2 ∧ (3*g*(K*u+h))^(m-2)*(3*z*K*u)^2<rr^(m-4)) ∨
      (2*(K*t*h*rr+g*u*K)≤g*rr ∧ 4*g*((y^2*(K*u+h)+h^2*(K*u+y))*rr+(K+h*y))+
        9*K*h^2*y^2*t*rr^2<4*g*rr^2) at data
    rcases data with ⟨l1,l2,l3⟩|⟨j,jt⟩
    · have first := OMA.TwoOddErrorCells245212.first_excluded (by omega : 4 ≤ m) (rrR.trans rP)
        (r0.trans_le rP) qcap l3
      rcases OMA.TwoOddErrorCells245212.alternatives r0 rP rQ qR ph bu cu errs.1 with bad|bad|bad
      · omega
      · omega
      · exact (not_lt_of_ge (bad.trans' (Nat.pow_le_pow_left rrR 2))) l2
    · exact OMA.TwoOddErrorCells245212.second_excluded rr0 (rrR.trans rP) (rrR.trans rQ)
        ph (near rr0 rrR j) bu cu bc errs.2 jt
end OMA.TwoOddEffectiveOriginal245212
end
section
namespace OMA.OddBox245212
open scoped ArithmeticFunction.sigma
theorem original {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 13≤p)
    (pq : p<q) (ha : 5≤a) (hd : 5≤d)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    6≤k+1 ∧ k+1≤1250 ∧ max (a+1) (d+1)≤225 := by
  have prime := prime_bound hp hq op pq ha hd eqn
  have leanK : 6≤k+1 := by omega
  have minBound := OMA.TwoOddEffectiveOriginal245212.bound hp hq (by omega) pq (by omega) eqn
  refine ⟨leanK,?_⟩
  have small := OMA.ComplementaryExp245212.exponent hp hq (by omega) (by omega) pq.ne (by omega) eqn
  have flip : OeisA245212.a (2^k*q^d*p^a)=(σ 1 (2^k*q^d*p^a):ℤ) := by rwa [mul_right_comm]
  by_cases h : d≤a
  · have ⟨kb,mg⟩ := OMA.ComplementaryFinish245212.exponents hp hq (by omega) (by omega) pq.ne (by omega) eqn
    rw [max_eq_left (by omega)]
    apply rectangle (m:=d+1) (M:=a+1) false (by omega) (by omega) (by simp;omega) leanK kb small mg
    intro kl kh ml mh lk uk lm hm
    exact veto_false hp hq op pq ha hd eqn lk uk lm hm le_rfl le_rfl op (by omega)
  · have ⟨kb,mg⟩ := OMA.ComplementaryFinish245212.exponents hq hp (by omega) (by omega) pq.ne.symm (by omega) flip
    have ms := OMA.ComplementaryExp245212.exponent hq hp (by omega) (by omega) pq.ne.symm (by omega) flip
    rw [max_eq_right (by omega)]
    apply rectangle (m:=a+1) (M:=d+1) true (by omega) (by omega) (by simp;omega) leanK kb ms mg
    intro kl kh ml mh lk uk lm hm
    exact veto_false hp hq op pq ha hd eqn lk uk le_rfl le_rfl lm hm op (by omega)
end OMA.OddBox245212
end
section
namespace OMA.RankTwoOriginalCover245212
open OMA.RankTwoInteriorBox245212 OMA.RankTwoInteriorWalk245212 OMA.RankTwoInteriorCover245212
open scoped ArithmeticFunction.sigma
theorem of_roots
    (closed : ∀ m : ℕ, 6 ≤ m → m ≤ 32 → ∀ swap : Bool, Closed (root m 6 1250 swap))
    {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 13 ≤ p)
    (pq : p<q) (ha : 5≤a) (hd : 5≤d) :
    OeisA245212.a (2^k*p^a*q^d)≠(σ 1 (2^k*p^a*q^d):ℤ) := by
  intro eqn
  obtain ⟨e,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
  obtain ⟨K0,K1,exp⟩:=OMA.OddBox245212.original hp hq op pq ha hd eqn
  have minb := OMA.TwoOddEffectiveOriginal245212.bound hp hq (by omega) pq (by omega) eqn
  have pbound := OMA.OddBox245212.prime_bound hp hq op pq ha hd eqn
  have upper : p≤3*(k+1) := by omega
  obtain ⟨i,pi⟩ := hp.odd_of_ne_two (by omega)
  obtain ⟨j,qj⟩ := hq.odd_of_ne_two (by omega)
  have gap : p+2≤q := by omega
  have generic (s : Cell) (fit : Fits s (k+1) (a+1) (e+2) p)
      (balance : OeisA245212.a (2^k*p^a*q^(e+1))=(σ 1 (2^k*p^a*q^(e+1)):ℤ)) :
      OMA.OddBox245212.veto s.kl s.kh s.bl s.bh s.cl s.ch s.pl s.ph=false := by
    obtain ⟨lK,hK,lB,hB,lC,hC,lp,rp⟩:=fit
    exact OMA.OddBox245212.veto_false hp hq op pq ha hd balance lK hK lB hB lC hC lp rp
  obtain ⟨floor,easy,exactS⟩:=solution_facts hp hq op gap (by omega) ha (by omega) upper generic eqn
  let w : World := ⟨k,a+1,e+2,p,floor,upper,easy,exactS⟩
  have cover (m : ℕ) (dir : Bool) (lo : 6 ≤ m) (hi : m≤32) (fit : Fits (root m 6 1250 dir) (k+1) (a+1) (e+2) p) : False :=
    closed m lo hi dir w fit (by cases dir <;> simp [Good,root] <;> omega)
  by_cases h : e+2≤a+1
  · apply cover (e+2) false (by omega) (by omega)
    simp only [root,Bool.false_eq_true,↓reduceIte,Fits];omega
  · apply cover (a+1) true (by omega) (by omega)
    simp only [root,↓reduceIte,Fits];omega
end OMA.RankTwoOriginalCover245212
end
section
namespace OMA.RankTwoJoined245212
open OMA.RankTwoPacked245212 OMA.RankTwoCursor245212
open OMA.RankTwoInteriorCover245212 OMA.RankTwoInteriorWalk245212
private def rows6 (i : ℕ) : ℕ := (if i < 34 then (if i < 17 then (if i < 8 then ([0x648dc91b71c6e491c6e3690108034181b841805806,0x6492371b91b8dc9238dc6e48db8dc9236e37238dc8db92491b8e37237234e48dc6e46e352491c6a25246d46a291a522490108034181b84180b00c,0x14408034181b84180b006,0x649236e372371b9246e372371b91b8d821004c1818381816017,0x649248dc6e37246db9226e469c9246db8dc92371b8dc89c6a49246e371b9236dc91469c91b4e491b7246e371b91b9146a469021004c1818903c16017,0x1421004c1818901816017,0x192492351a4a49234a34949144949124a491249021004c181b849416017,0x1440804c181b841816017] : List ℕ).getD (i-0) 0 else ([0x192491b71b91b8cc91b8dc8cc66444830c094181838182082d,0x19249246e371b9237097246599248db6648d98cc8899249236dc66491b8dc8d46e46cc9198cc91b32366488c44830c0941818903c2082d,0x14408094181890182082d,0x649248dc6637213099246dc6e426126492491b3199196649197232cc9248cb7246cc64c91b324663648408094181890182b042,0x14408094181890182b02d,0x649249234a46549198ca4a49248ca8d192368a290408094181b84942b02d,0x1440804c181b84182b02d,0x44408034181b84182b017,0x77a98034181b84182b006] : List ℕ).getD (i-8) 0) else (if i < 25 then ([0x19249246e372331992371991b8cc3099248dc6646e326491b8cc8db86126492492465b3114649233199236646ca2887ec1201818901840057,0x649249236e372130992371b9098c99248dc6e42633246e37233192507ec1201818901854881,0x147ec1201818901854857,0x649249248cc46466231488a2914907ec120181b849454857,0x14f6c120181b841854857,0x192492371b9198cc91b8cc8db86132491b8cc8db8613248dc6646dc84c2486f023418183818688aa,0x192492371991b8cc3099246e33236e42612649244e331390984c91389c84c2486f0234181838187c8d2,0x146f0234181838187c8aa] : List ℕ).getD (i-17) 0 else ([0x48bac6f4181838187c8aa,0x14bac234181838187c8aa,0x50bac2341818903c7c8aa,0x14f6c234181890187c8aa,0x649249244e272131192271391188992489c4e44623244d488a26488a250f6c23418189018a48fa,0x14f6c23418189018a48aa,0x1890f6c234181b8494a48aa,0x14f6c120181b8418a48aa,0x67a98120181b8418a4857] : List ℕ).getD (i-25) 0)) else (if i < 51 then (if i < 42 then ([0x64922294892912893a98120181b841a7114a,0x17a98034181b841a71057,0xa7a98034181b841a71006,0x192469492371b4a49248db8dc91b8dc71b91489a4a492491b7236e46e372230992251152492371b90b8dc91b8dc6cc914892493a98037841c18182b006,0x649249246dc6e46e372130992471b8dc84c2648dc6e42612649248d24923249248db90b72371b86132491b71b91b8dc309290f6c123841c181854857,0x6492491c6e46e372132366491b8dc84c2648dc6e42612649246e372130992371b9098499248dc6e42617246e372130b250f6c2349c1c18187c8aa,0x192492491b71b9236e370c2649236e37246dc6e42632649248db7236e42642cc92371b8e37242cc8d9250f6c2349c1c1818a48fa,0x14f6c2349c1c1818a48aa] : List ℕ).getD (i-34) 0 else ([0x50f6c23784a01818a48aa,0x14f6c123841c1818a48aa,0x37a98123841c1818a4857,0x6492491b72371b9236646cc92371b90985c91389c84c4cc92489c4e42617244e272171332491389c85c4e451b8a3648d8844c401c1818cc14a,0x6492491389c84c4e489c4e44e26649226e44e27227146c992492271391389c91372271332491389c89c4e451b8a3648d8844c401c1818f3199,0x14d8844c401c1818f314a,0x496c8d8c401c1818f314a,0x156c844c401c1818f314a,0x516c844c9c441818f314a] : List ℕ).getD (i-42) 0) else (if i < 59 then ([0x156c844c9c1c1818f314a,0x516c844f84a01818f314a,0x15e1844f841c1818f314a,0x192492489b91389c91371b90990b32491371b9146e27233193249244dc6e46e37233199246e37226e4663249238658401c18191a1e7,0x6492491b7236e49098499213093248db89c91b32264c92451a5246ca449238658401c181941235,0x15238658401c1819411e7,0x49e1923c401c1819411e7,0x15e18658401c1819411e7] : List ℕ).getD (i-51) 0 else ([0x51e186589c441819411e7,0x15e186589c1c1819411e7,0x51e1865b84a01819411e7,0x15e1844f841c1819411e7,0x57a9844f841c18194114a,0x19249224514a4493a9844f841c181a71283,0x17a98123841c181a7114a,0xb7a98037841c181a71057,0xf7a98037841c181a71006] : List ℕ).getD (i-59) 0)))
private def rows7 (i : ℕ) : ℕ := (if i < 60 then (if i < 30 then (if i < 15 then ([0x648e37237236e49236e46dc91a4901080341c1f841c05806,0x6492371c6e46e46e372471b91b8dc91c6e46e372371b92491c6e37246e371b9238db92371b8dc9246dc8dc6a48db91a8d49224a46944901080341c1f841c0b00c,0x144080341c1f841c0b006,0x6492372371b91b8dc8e272351c6a491b91b8dc8dc71b92371b91a8d021004c1c1c401c16017,0x19248e371c6e46e38d492371b91b8dc8e271c6a49238dc6e46e38d491b72351b9248dc6e38dc8e371b92389c8da91a8d021004c1c1c9c4416017,0x1421004c1c1c9c1c16017,0x19249248dc6e352369451292491b5129236d25248a25225125248929124a49224a249021004c1c1f84a016017,0x1440804c1c1f841c16017,0x192491b91b8dc8dc6e48dc8dc6e132466471b3246cc8d991424830c0981c1c401c2082d,0x192492371b8e37238c99238d99198cc88992492371b8e37238c99246dc6e46cc9236646cc91b32366488c44830c0981c1c9c442082d,0x144080981c1c9c1c2082d,0x649248cc8d99198e32649198e332331c6499249233198e32648e331c64c9248cc6638c992465c6cc9238cc7193246e36484080981c1c9c1c2b042,0x144080981c1c9c1c2b02d,0x649249248dc6d44a49196625248d99236cc88c4622a492491b31191988992466465c8cc64a2904080981c1f84a02b02d,0x1440804c1c1f841c2b02d] : List ℕ).getD (i-0) 0 else ([0x444080341c1f841c2b017,0x77a980341c1f841c2b006,0x19249248dc8db91b8d19233234646646899248cc8d991991a2649198cc8cc64992492471b32265192491b32366466331488a2887ec1281c1c9c1c40057,0x19249248cc6638d192466352331a26492466352331a3248cc6a38d12507ec1281c1c9c1c54881,0x147ec1281c1c9c1c54857,0x19249249246cc8d992366332445488a3224514907ec1281c1f84a054857,0x14f6c1281c1f841c54857,0x649249198d471a32466468c8cc64c92466468c8cc8d13248cc6646632486f82441c1c401c688aa,0x19249233234646632649198cc8cc64992491991a3233193248cc6646634486f82441c1c401c7c8d2,0x146f82441c1c401c7c8aa,0x48bac6fc1c1c401c7c8aa,0x14bac2441c1c401c7c8aa,0x50bac2441c1c9c447c8aa,0x14f6c2441c1c9c1c7c8aa,0x192492492331a9196649198d48db2649238d46cc9138992649248a35133244e264c9244e270c26489c4e1859250f6c2441c1c9c1ca48fa] : List ℕ).getD (i-15) 0) else (if i < 45 then ([0x14f6c2441c1c9c1ca48aa,0x50f6c2441c1f84a0a48aa,0x14f6c1281c1f841ca48aa,0x67a981281c1f841ca4857,0x19249249249227128615228ca32228a28a5224a4892893a981281c1f841e7114a,0x17a980341c1f841e71057,0xa7a980341c1f841e71006,0x19248e369292491b91b72351a9246dc6e46a349040803784201c1c0b006,0x6492491b8dc8d471a92371b8e372451b8a35246d46a49246e372371b92371b91a8dc91b91b72371c6e491b8d48d46a48da91b52249040804f84201c1c16017,0x649249246e37234a48db5248dc2646a35099248db3246d95228499224949249246e36549236ca32491b3236628d129040804f84201c1c2b02d,0x1440803784201c1c2b017,0x27a9803784201c1c2b006,0x19249249198cc8d46a48db8d19248db3246d992346468992492371b3246a346491b66468992491b6648db32468c8d12507ec128a8201c1c40057,0x649249246cc8d99198c99248d991b3246cc7192649248d991b3246cc71932491b31991c6638c92644887ec128a8201c1c54881,0x147ec128a8201c1c54857] : List ℕ).getD (i-30) 0 else ([0x507ec12b84ac1c1c54857,0x14f6c12b84201c1c54857,0x649249236646d99238cc71b32491b6648db32471b32364c92491b6648db32471b3238d93249236cc91b6648e366471b2486f824448201c1c688aa,0x19249248db3246d99238d991b2649246d991b3246cc8d926492491b6646cc91b32364c9248db3236648d991b2486f824448201c1c7c8d2,0x146f824448201c1c7c8aa,0x48bac6fc48201c1c7c8aa,0x14bac24448201c1c7c8aa,0x50bac244a84c1c1c7c8aa,0x14f6c244a8201c1c7c8aa,0x19249248d991b7246cc8d93249236dc8db9238d98e324c92491b85c71b9236638c992471b8e37238cc71924896035848201c1c908fa,0x19249248dc6e46dc91b31c64c9246e37236e47198e324c92491b7236e47198e37099246e36648e331b24896035848201c1ca4922,0x1496035848201c1ca48fa,0x48f6c96448201c1ca48fa,0x14f6c35848201c1ca48fa,0x50f6c358a84c1c1ca48fa] : List ℕ).getD (i-45) 0)) else (if i < 90 then (if i < 75 then ([0x14f6c244a8201c1ca48fa,0x44f6c244a8201c1ca48aa,0x50f6c24784ac1c1ca48aa,0x14f6c12b84201c1ca48aa,0x97a9812b84201c1ca4857,0x192492471b91b6648e331b32491b6646cc91b32364c92491b6648db3246cc8d93249236cc8dc2e48d991b24890046c48201c1cb894a,0x192492489b3236648d991b2649244dc2646e37246cc8d926492491370b91b8dc91b32364c92489b8dc89c2648d991b24890046c48201c1ccc172,0x1490046c48201c1ccc14a,0x48d9890448201c1ccc14a,0x14d9846c48201c1ccc14a,0x649249244d99226e17246cc8d93249226e17244dc6e48e36646c932492489b8dc8dc6e48e36646e12649244dc6e44e13246e1323709248d9857848201c1cdf999,0x6492491484a5246cc8dc24c8a48dc2646e124c92292370991b84991491b84c8dc261248d9857848201c1cf31c0,0x14d9846c48201c1cf3199,0x24d9846c48201c1cf314a,0x496c8d9c48201c1cf314a] : List ℕ).getD (i-60) 0 else ([0x156c846c48201c1cf314a,0x516c846ca84c1c1cf314a,0x156c846ca8201c1cf314a,0x516c846f84ac1c1cf314a,0x15e1846f84201c1cf314a,0x192491491b84c8dc6613229237098e33113248a47198e37118a48e331b248c6868448201c1d069e7,0x649245246dc71b88c8a471b8e37143093248a471b8e37143098a48e371b909648c6868448201c1d1a20e,0x14c6868448201c1d1a1e7,0x4924cc6c48201c1d1a1e7,0x1524c68448201c1d1a1e7,0x649245246dc71b88c52471b8a370c24c92291389c50c2629226e4261248cec79048201c1d2da35,0x192491489c4e286131491384c89c26132452451b84c8a37098a489c2644e130c248cec79048201c1d4125c,0x14cec79048201c1d41235,0x4924ccf048201c1d41235,0x1524c68448201c1d41235] : List ℕ).getD (i-75) 0) else (if i < 105 then ([0x3524c68448201c1d411e7,0x49e1925048201c1d411e7,0x15e1868448201c1d411e7,0x51e18684a84c1c1d411e7,0x15e18684a8201c1d411e7,0x51e1868784ac1c1d411e7,0x15e1846f84201c1d411e7,0x97a9846f84201c1d4114a,0x649229228dc4e426131491389c84c26184c91491384c89c26132292270991384c248d1089c48201c1d54283,0x649229228dc26451b84c26452451b84c89c26126491491384c89c461314448d1089c48201c1d672a9,0x14d1089c48201c1d67283,0x49188d1448201c1d67283,0x1518889c48201c1d67283,0x6491145118889c48201c1d8d2cf,0x1518889c48201c1d8d283] : List ℕ).getD (i-90) 0 else ([0x49a7918c48201c1d8d283,0x15a7889c48201c1d8d283,0x51a7889c48201c1dd931b,0x15a7889c48201c1dd9283,0x4ac59a7c48201c1dd9283,0x16c5889c48201c1dd9283,0x52c5889ca84c1c1dd9283,0x16c5889ca8201c1dd9283,0x52c5889f84ac1c1dd9283,0x17a9889f84201c1dd9283,0x64493a9889f84201c1e713b3,0x17a9846f84201c1e71283,0xa7a9812b84201c1e7114a,0x1b7a9803784201c1e71057,0x277a9803784201c1e71006] : List ℕ).getD (i-105) 0)))
private def rows8 (i : ℕ) : ℕ := (if i < 46 then (if i < 23 then (if i < 11 then ([0x19237244dc8db92489b9137246e34901080342023842005806,0x6491b8dc8dc6e491c6e37246dc6e491b8dc8dc6e48db8d81080342020a8200b00c,0x192491c6e37246dc6e48e371b92371b8dc9246e372371b92371b91a8d492371391a8d4912523512924892490108034202384ac0b00c,0x14108034202384200b00c,0x24408034202384200b006,0x649236e372371b9246e372371b91b8d82100502020482016017,0x192492371b8dc91b6e489b91a72491b8dc6e48db72451b7246d39248dc6e46e37248db71b9248dc6e37236e48dc8da8d82100502020a84c16017,0x142100502020a82016017,0x6492492371b7236e291a52489251292491b8dc6a46dc5246929125249128949135234949246d44a48da4a49248929124a2522490210050202384ac16017,0x144080502023842016017,0x192491b71b9236e132466332331991424830c09c202048202082d] : List ℕ).getD (i-0) 0 else ([0x6492491b8dc6e48dc65c9197099246cc6648d98cc88992491b8dc8d99246db8dc9236646cc8cc66488c44830c09c2020a84c2082d,0x1440809c2020a8202082d,0x649248cc66366491971b26492491b3199196649197232cc9248cc6636649196cc92371b32364840809c2020a8202b042,0x1440809c2020a8202b02d,0x649249248dc6e46a351a92370b8d49236646cc8cc6645093244929249246cc66465992466371b32231129040809c202384ac2b02d,0x14408050202384202b02d,0x44408034202384202b017,0x77a98034202384202b006,0x649249236e34648cc6519248ca9194649198ca26492492465b32468c65192491b32366466332445488a2887ec1302020a82040057,0x6492491a8d19236899248da3246d12507ec1302020a82054881,0x147ec1302020a82054857,0x6492492491b3199236633244548ca3249114a488a4514907ec130202384ac54857] : List ℕ).getD (i-11) 0) else (if i < 34 then ([0x14f6c1302023842054857,0x192492491b2a48cc6519248cc6519246632899249233194649196899248da3246d1250f6c2502020a8207c8aa,0x192492491b4648da26492368c91b44992492368c91b44c9246d19232d1250f6c2502020a820a48fa,0x14f6c2502020a820a48aa,0x50f6c250202384aca48aa,0x14f6c13020238420a48aa,0x37a9813020238420a4857,0x6492492492465491948c91232244c92448c89132489191224c92491228a28a5224a4892893a98130202384227114a,0x17a980342023842271057,0x77a980342023842271006,0x6491a4a492371b9236a46a3490408037842420200b006] : List ℕ).getD (i-23) 0 else ([0x192492371b92351a91a8d492371b92371a91b8dc8dc8d48d29124a492491b8cc91a5234648cc65491188992249492491968c9232d1290408037842420202b017,0x17a98037842420202b006,0x192492491b2a48cc6519248cc6519246632895249248da3246e289132491b91a8d19236648d4689290f6c1338424202054857,0x649248d992351a32465c91a32344c92466332468c8d13248cc6648d191a2486fc25050242020688aa,0x192492331992346468992465c8cc6499248dc8cc8d13246e48d191b2486fc250502420207c8d2,0x146fc250502420207c8aa,0x48bac700502420207c8aa,0x14bac250502420207c8aa,0x50bac250b45420207c8aa,0x14f6c250b42420207c8aa,0x192492491b91b8d992372371b26492372371b3246cc91b8d92649248dc8dc6cc91b3246e364c9246cc91b8d99232e48d98c9250f6c250b4242020a48fa,0x14f6c250b4242020a48aa] : List ℕ).getD (i-34) 0)) else (if i < 69 then (if i < 57 then ([0x50f6c25384b82020a48aa,0x14f6c13384242020a48aa,0x67a9813384242020a4857,0x19249246648dc6cc8dc8cc8d93249197246cc8d93246e466324c9248dc91b32364c91b9236646c932491b9236646c9923723319248da448050242020cc14a,0x192492465c91b32364c91b9236646c932491b9236646c9923723319248da459850242020df999,0x649248dc91b32364c91b9198e124c9248db9236646e126491b7246e131b248da459850242020f31c0,0x14da448050242020f3199,0x24da448050242020f314a,0x496c8da850242020f314a,0x156c848050242020f314a,0x516c8480b4542020f314a] : List ℕ).getD (i-46) 0 else ([0x156c8480b4242020f314a,0x516c848384b82020f314a,0x15e1848384242020f314a,0x6492492372371b84c91b91b8dc24c92291b8dc26292371b24c9248a46e37098a48dc6c992292371b31491b70b2492606a8502420211a1e7,0x192492452371b84c5246d932452366291b86124c9245236629236646e12648a48dc2646e131491b84c6e12492606a85024202141235,0x152606a850242021411e7,0x49e1926450242021411e7,0x15e186a850242021411e7,0x51e186a8b4542021411e7,0x15e186a8b4242021411e7,0x51e186ab84b82021411e7,0x15e1848384242021411e7] : List ℕ).getD (i-57) 0) else (if i < 80 then ([0x57a98483842420214114a,0x19248a48dc6e184c5246e131b3245246e13237093229236e44dc248d388c85024202154283,0x6492292270991384c2645244e131b8499245244e13226e132291b8dc248d388c850242021672a9,0x14d388c85024202167283,0x491acd3c5024202167283,0x151ac8c85024202167283,0x192492292270991370991491371b8499245244dc6e132291b8dc2499249148dc6e132291b8dc24c92291b8dc2645236e12491ac8c8502420218d2cf,0x151ac8c8502420218d283,0x49a911b0502420218d283,0x15a908c8502420218d283,0x19249248a47098e23099148e231384992284a262251a908c850242021d931b] : List ℕ).getD (i-69) 0 else ([0x15a908c850242021d9283,0x4ac59a9450242021d9283,0x16c588c850242021d9283,0x52c588c8b4542021d9283,0x16c588c8b4242021d9283,0x52c588cb84b82021d9283,0x17a988cb84242021d9283,0x64493a988cb84242022713b3,0x17a984838424202271283,0xa7a98133842420227114a,0x157a980378424202271057,0x1c7a980378424202271006] : List ℕ).getD (i-80) 0)))
private def rows9 (i : ℕ) : ℕ := (if i < 15 then ([0x192389c8e34a492371b7248db91b71c91b71b92472371b72491b7236dc9236e469b9249224a34e3490408034242784240b006,0x6492371b7248db7236e49246db8dc9236e46dc9137234e472371b8e48db8d82100502424b42416017,0x19248e48db8948e46a351a72492449a8d35249234d469a9249248d349a91c8925224d0210050242784b816017,0x144080502427842416017,0x649246e32e48cc65c9116649248db91b71b9232e465c89992391b8dc72331991c4c84080a02424b4242082d,0x649248cb6648db2649248cb9196649196cc8e49196cc7236484080a02424b4242b042,0x144080a02424b4242b02d,0x649248e48da8d472331991a2e49239198c991c8cb2cc4904080a0242784b82b02d,0x14408050242784242b02d,0x34408034242784242b017,0x57a98034242784242b006,0x6492492331972466328c92466328c9232d132492491b66465c48c91c8cc6639114519249246d19236899248da3246ca2507ec1342424b42454857,0x19249248e466331c8ca2d14907ec134242784b854857,0x14f6c1342427842454857,0x649249246ca9232d19248cc65192465a2649248cc6519236899248da3246d1250f6c25c2424b4247c8aa] : List ℕ).getD (i-0) 0 else ([0x649249246d19236899248da3246ca2649248da3246ca32491b2a46d1250f6c25c2424b424a48fa,0x14f6c25c2424b424a48aa,0x50f6c25c242784b8a48aa,0x14f6c13424278424a48aa,0x37a9813424278424a4857,0x6492492491952368c92465a3246d132492465a3246d13249232d191224c92491232244c92246448932492246448992448c449291e1849424278424f314a,0x192492488a28a291e1849424278425411e7,0x17a98494242784254114a,0x64892893a984942427842671283,0x17a98134242784267114a,0x37a980342427842671057,0x87a980342427842671006,0x6491a5234a48e4492923922494693a98037842824242b006,0x19248d48ca5248ca9246594a49248cc8cc64a5249246598c94a49249199198c99246632648ca25292488a293a980378428242671057,0x17a980378428242671006] : List ℕ).getD (i-15) 0)
private def rows10 (i : ℕ) : ℕ := (if i < 42 then (if i < 21 then (if i < 10 then ([0x1922290108034282b842805806,0x19246e37244e27236649146e27246cc66491389c8cc6648dc6e46c81080342828bc280b00c,0x19248dc66471b91b3246e37233199248e331b9236633246e37233199246e372331992371b9198c810803428299cc00b00c,0x19249236e33228d48d9922519894912490108034282b85a00b00c,0x14108034282b84c00b00c,0x24108034282b84280b00c,0x34408034282b84280b006,0x19246e37246e370c6e491b8dc91b8dc6e46e46e46d02100502828542816017,0x649248dc6e37236e191b72491b8dc6e46dc9146dc91b4e492371b8637246e370c6e492371b8dc8dc6e491b8dc6e46e46d02100502828bc5816017,0x142100502828bc2816017] : List ℕ).getD (i-0) 0 else ([0x19249236e17248dc6e370c6a491b7246e371b91b52491b71a8549234a34a492491351a50a9246a34a24a49246a34a25248d469449021005828299cc016017,0x649249234d44a491b492924694912494924494892512922490210058282b85a016017,0x14210050282b84c016017,0x24408050282b842816017,0x19248dc6648dc6e46cc9198cc91b32366488c44830c0a0282854282082d,0x19249246e372371b91b7246e13199246cc8d99198cc8a12649246e372371b92371b91b8dc9236646cc91b3236648a131424830c0a02828bc582082d,0x144080a02828bc282082d,0x19249232e48cc66366491152371b26492491b3199196649198dc6cc9248cc6636649198cc6cc92371b3246e36484080a02828bc282b042,0x144080a02828bc282b02d,0x19249248dc6e491b8dc8d46a46e35246633246cc8d992268c9246948d29233194a49248cb9236632648dc8cc6cc92465468c91b44c4904080a0282b84c02b02d,0x14408050282b84282b02d] : List ℕ).getD (i-10) 0) else (if i < 31 then ([0x44408034282b84282b017,0x87a98034282b84282b006,0x192491491b32265192451946491968992492491b6633246cc66488a9114649246cc8d99236646cc9115246ca2887ec1382828bc2840057,0x19249246d19236899248da3246ca2507ec1382828bc2854881,0x147ec1382828bc2854857,0x19249249233199236646cc9195246ca3249195232a48ca4519122907ec138282b84c054857,0x14f6c138282b842854857,0x192492491b2a48cc6519248cc65192465a2649248cc6519236899248da3248cc651250f6c2642828bc287c8aa,0x649249246d19236899248da3246ca2649248da3246ca32491b2a46d1250f6c2642828bc28a48fa,0x14f6c2642828bc28a48aa] : List ℕ).getD (i-21) 0 else ([0x50f6c264282b84c0a48aa,0x14f6c138282b8428a48aa,0x37a98138282b8428a4857,0x649249232a48cb46491b4648da2649246d19246632899248da3246d126492491b4648da26492368c91b44992492348c891324891912248db44a428285428f314a,0x496c8db828285428f314a,0x156c84a428285428f314a,0x516c84a42828bc58f314a,0x156c84a42828bc28f314a,0x516c84a4282b84c0f314a,0x15e184a4282b8428f314a,0x6492492491232244c92246244c924891451311291e184a4282b8429411e7] : List ℕ).getD (i-31) 0)) else (if i < 63 then (if i < 52 then ([0x17a984a4282b84294114a,0x64892893a984a4282b842a71283,0x17a98138282b842a7114a,0x67a98034282b842a71057,0xc7a98034282b842a71006,0x649125248dc6d292491c6e46dc91b8dc8dc6d29249238cc8d46a46d48e226489252488a293a98037842c28282b006,0x6492245492452328c9232a4651290f6c13b842c282854857,0x649249248ca91b46491b4648da2649246d19236899248da3246d12549249248da3246ca3248ca91944c9248ca9194649198cc8dc6c9290f6c13b842c2828a48aa,0x17a9813b842c2828a4857,0x649249198cc8dc6cc92371b3246e364c9248dc6cc91b8d932491b8d991b248db44a45c2c2828cc14a] : List ℕ).getD (i-42) 0 else ([0x19249246e36648dc6c99248dc6cc91b64992492371b3246e364c9246e36648db248db44a45c2c2828f3199,0x14db44a45c2c2828f314a,0x496c8db85c2c2828f314a,0x156c84a45c2c2828f314a,0x516c84a4c4602828f314a,0x156c84a4c42c2828f314a,0x516c84a784c82828f314a,0x15e184a7842c2828f314a,0x6492492491b6648d98c992466332331926492466331c64c91c6638c92649248e331c64c9233199198c932492331991b8d99228dc4c9251e186d8c42c2829411e7,0x51e186db84c82829411e7,0x15e184a7842c2829411e7] : List ℕ).getD (i-52) 0) else (if i < 73 then ([0x27a984a7842c28294114a,0x649248a33146cc9146cc8a364c92451b3228d93248a366451b2491dc9085c2c282967283,0x649248a466366451b2649146cc8a36499249146cc8a364c9228dc2644e12491dc9085c2c28298d2cf,0x151dc9085c2c28298d283,0x49ab11e05c2c28298d283,0x15ab09085c2c28298d283,0x649249146cc8993248a37099138493249228dc2644e12649146e1322709249ab0b2c5c2c2829b331b,0x192492451b84c8a37093248a37099146e124c9248a370991384992451b84c519249ab0b2c5c2c2829d9367,0x15ab09085c2c2829d931b,0x25ab09085c2c2829d9283] : List ℕ).getD (i-63) 0 else ([0x4ac59ab45c2c2829d9283,0x16c589085c2c2829d9283,0x52c58908c4602829d9283,0x16c58908c42c2829d9283,0x52c5890b84c82829d9283,0x17a9890b842c2829d9283,0x649249249228cc51b32451b8a364c91144c44a293a9890b842c282a713b3,0x17a984a7842c282a71283,0x97a9813b842c282a7114a,0x107a98037842c282a71057,0x127a98037842c282a71006] : List ℕ).getD (i-73) 0)))
private def rows11 (i : ℕ) : ℕ := (if i < 63 then (if i < 31 then (if i < 15 then ([0x501080342c2f842c05806,0x648dc5232e45246cc8d192289471991c4a46c81080342c2cc42c0b00c,0x6492251991291b3244a25246cc8d99247128e33238947199244a252331991c4a38c81080342c2da8c80b00c,0x192491c4a46cc8946648948d991291b3245234625224901080342c2f85ac0b00c,0x141080342c2f84c80b00c,0x241080342c2f842c0b00c,0x344080342c2f842c0b006,0x19246e17248db8d99237246dc8db91b8a46982100542c2c5c2c16017,0x649248db8dc8dc6cc9246e371c6e46e372431b8637246d48da9248e371b3246e366491c6e38dc8e171c6a491b8dc6e46e46d02100542c2cc46016017,0x142100542c2cc42c16017,0x6492366491b71b3248dc6e48dc6e37242e35218d48d29248dc8cb91b8d99246a46948dc6902100582c2d20c816017,0x6492471a4648e348c9124a49238d232471a4902100582c2da92416017,0x142100582c2da8c816017,0x19249246d291a4a49246d25246925249224948d25248929124a48944902100582c2f85ac16017,0x142100542c2f84c816017] : List ℕ).getD (i-0) 0 else ([0x344080542c2f842c16017,0x19248dc8d99246dc8db91b84c9198cc91b32366471424830c0a42c2c5c2c2082d,0x192491b91b8dc8dc8dc6e48dc2646e13248d991b3246cc8d991424830c0ac2c2c88602082d,0x192491c6e46e372371c6648dc8db91b8dc92366471b3246cc8d99228613146c830c0ac2c2cc48c2082d,0x1430c0a42c2cc4602082d,0x244080a42c2cc42c2082d,0x19249232e48cc6646599119246633132649248cc6646632649199197233193249233198e32649198cc6cc9238cc7193246e36484080a42c2cc42c2b042,0x144080a42c2cc42c2b02d,0x6492471b8e37246e46e37237232e48cc6648d991b3244e284992491b5236a48dc4a46949236646cc9123224504080b02c2d20c82082d,0x649248cc6646632649198dc8cc8cb32491988c8cc44c9233232e46632484080b02c2d20c82b042,0x144080b02c2d20c82b02d,0x649224929224504080b02c2da9242b02d,0x144080b02c2da8c82b02d,0x504080b02c2f85ac2b02d,0x144080a42c2f84c82b02d,0x444080542c2f842c2b02d] : List ℕ).getD (i-15) 0) else (if i < 47 then ([0x844080342c2f842c2b017,0xd7a980342c2f842c2b006,0x192492292266228a32492492371b32366491a6646cc91152228c92491b8d991b3248db3236649132a48d94519224507ec13c2c2cc42c54857,0x19249249246cc66491b8d991b32465491b28c9248d992331a3246cc8d99246ca9234622519248915122907ec13c2c2f84c854857,0x14f6c13c2c2f842c54857,0x192492291b4649232d192465a2649248cb4648da26492465a3246d1250f6c2682c2cc42c7c8aa,0x192492491b4648d946492365491b2899249236548ca32491b2a48cc651250f6c2682c2cc42ca48fa,0x14f6c2682c2cc42ca48aa,0x50f6c2682c2f84c8a48aa,0x14f6c13c2c2f842ca48aa,0x37a9813c2c2f842ca4857,0x6492491952465a3248da3246d132492465a3246d132491b4648da248dbc4b02c2c5c2ccc14a,0x19249248cc6519246632899248da3248cb44992492465a3246d132491b4648da248dbc4b02c2c5c2cf3199,0x14dbc4b02c2c5c2cf314a,0x496c8dc02c2c5c2cf314a,0x156c84b02c2c5c2cf314a] : List ℕ).getD (i-31) 0 else ([0x516c84b02c2cc460f314a,0x156c84b02c2cc42cf314a,0x516c84b02c2f84c8f314a,0x15e184b02c2f842cf314a,0x19249249248da32328c9222a244c9244a24648944893249244a2464894489922289291e184b02c2f842d411e7,0x17a984b02c2f842d4114a,0x649244514a4493a984b02c2f842e71283,0x17a9813c2c2f842e7114a,0x77a980342c2f842e71057,0xc7a980342c2f842e71006,0x18a492291a3246d98a489949040803784302c2c0b006,0x192492466372371b8642cc9246634a46d292491b72371b91b91b7248dc6e46d48e371c4e48a35246da9226a48da49040805784302c2c16017,0x649249246e37234e48dc6cc9246d25248dc6e24a492348c45491188992249491229040805784302c2c2b02d,0x1440803784302c2c2b017,0x27a9803784302c2c2b006,0x64490f6c13f84302c2c54857] : List ℕ).getD (i-47) 0)) else (if i < 94 then (if i < 78 then ([0x192489192489192489991b2899249246999234ca3249234cc91a651250f6c268cc302c2c7c8aa,0x6492492491b3236519248d98c94649246646c952491b3234ca26492492469991b2549233234ca3249233234ca9248d3323651250f6c268cc302c2ca48fa,0x14f6c268cc302c2ca48aa,0x50f6c26b84d02c2ca48aa,0x14f6c13f84302c2ca48aa,0x37a9813f84302c2ca4857,0x649249246cc8d32a49234cc8d94649246cc8d94649246d991b2899249248db3246d94649246d991b2899249246d991b28c9246cc8d94489344b060302c2ccc14a,0x48dbc93860302c2ccc14a,0x14dbc4b060302c2ccc14a,0x649249246d99236ca3249236cc8d98a244c92491b3236648d19194649236633246548ca248dbc5cc60302c2cdf999,0x192492491b6646cc91a32328c9248db32366491b2a46513249246cc8d99232a46519248d991b3246548ca248dbc5cc60302c2cf31c0,0x14dbc4b060302c2cf3199,0x24dbc4b060302c2cf314a,0x496c8dc060302c2cf314a,0x156c84b060302c2cf314a] : List ℕ).getD (i-63) 0 else ([0x516c84b0cc642c2cf314a,0x156c84b0cc302c2cf314a,0x516c84b384d02c2cf314a,0x15e184b384302c2cf314a,0x19249248d991b3246548ca32491b3236cc9232a46513249246cc6cc9232a46519246e366491951a248cb46e860302c2d069e7,0x192492466366491952328c9246dc89b3248ca91b44c9248d46cc9232a346491b6648d3248cb46e860302c2d1a20e,0x14cb46e860302c2d1a1e7,0x49280cb860302c2d1a1e7,0x152806e860302c2d1a1e7,0x19249246a34648d468c92351b3246a344c9248d23246a34648a266491b51a248d4080460302c2d2da35,0x6492491a9136649198cc8dc6cc91188c92371b3246e364c9244623248dc6cc91b8d932488c46491b8d991b248d4080460302c2d4125c,0x14d4080460302c2d41235,0x49280d4460302c2d41235,0x152806e860302c2d41235,0x352806e860302c2d411e7,0x49e1928460302c2d411e7] : List ℕ).getD (i-78) 0) else (if i < 110 then ([0x15e186e860302c2d411e7,0x51e186e8cc642c2d411e7,0x15e186e8cc302c2d411e7,0x51e186eb84d02c2d411e7,0x15e184b384302c2d411e7,0x97a984b384302c2d4114a,0x6492292466332371b31492371b32364c9244623248dc6cc8d9322923664663248d8492060302c2d54283,0x19248a491b8d991b2645246cc8cc6499245248dc6cc91b32364c8a48cc664663248d8492060302c2d672a9,0x14d8492060302c2d67283,0x491ecd8860302c2d67283,0x151ec92060302c2d67283,0x192491492371b32364c8a48d98a324c92292266446326452466331b2491eca3460302c2d7a2cf,0x192491491b3233193229146628c93248a45198a32645244633223194491eca3460302c2d8d2f5,0x151ec92060302c2d8d2cf,0x251ec92060302c2d8d283,0x49abd1f060302c2d8d283] : List ℕ).getD (i-94) 0 else ([0x15abc92060302c2d8d283,0x649249149146cc89a3229226a28c93248a489c2628c99148a33146493249229227098a32645228cc4c99245228cc5193229146628ca249abcb4860302c2db331b,0x192492232291446288a3248a45236628ca9148a33146513249128919225148a2889249abcb4860302c2dd9367,0x15abc92060302c2dd931b,0x25abc92060302c2dd9283,0x4ac59ac060302c2dd9283,0x16c5892060302c2dd9283,0x52c58920cc642c2dd9283,0x16c58920cc302c2dd9283,0x52c5892384d02c2dd9283,0x17a9892384302c2dd9283,0x19249249248a48a228a3228a244c92451246224c924451889311293a9892384302c2e713b3,0x17a984b384302c2e71283,0xc7a9813f84302c2e7114a,0x1c7a9803784302c2e71057,0x207a9803784302c2e71006] : List ℕ).getD (i-110) 0)))
private def rows12 (i : ℕ) : ℕ := (if i < 16 then ([0x629245198948948944a49225128949128948a446231488c46492288c51191446288c9144629133228cc4a4912490408034303384300b006,0x649246d992371b3248dc6e48cc6646dc85a9248e251c6cc9233236638da9249128946cc9225128d99248cc6636a49198cc6e18d82100543030cc3016017,0x6492489332451b8d992465c91b31b90b8646cc9244dc6cc92371a8dc31a92492288c4a46d19244a248c9248d252249292491268c91b4502100583031b0d016017,0x19249234648922a491a32449152491a3244915248d192248a9249123224544a4490210058303385b416017,0x14210054303384d016017,0x244080543033843016017,0x649246dc6e48dc6e46e13246633246cc8d992231424830c0a4303060302082d,0x192491b92371b9198dc8dc8dc6648cc6648d991b3228612649248dc6e372371b92371b91b8dc9236646cc91b3236648a37146c830c0a43030cc642082d,0x144080a43030cc302082d,0x649248ca9233199196629237132649248cc8d98e32648dc8cc64c9248cc6636649198cc6cc92371b3246e36484080a43030cc302b042,0x144080a43030cc302b02d,0x192491b8dc92371b91b8dc8dc6e48cc6648d991b3244e28499248dc6a46e35246633233198884080b0303128d02082d,0x649248cb9236632648dc8cc6cc92466331b3246e36484080b0303128d02b042,0x144080b0303128d02b02d,0x6492492249449491191149292492248a9244914504080b03031b12c2b02d,0x144080b03031b0d02b02d] : List ℕ).getD (i-0) 0 else ([0x504080b0303385b42b02d,0x144080a4303384d02b02d,0x44408054303384302b02d,0x74408034303384302b017,0xa7a98034303384302b006,0x649248a445228c9249233236646646cc91152228c9248d991b3246cc8d99246ca9236514507ec13c3030cc3054857,0x649249248cc6648d991b32465491b28c92466332331992331191988946492492449188a92448c88a4548922907ec13c303384d054857,0x14f6c13c3033843054857,0x6492245492488a311290f6c13c30338430a48aa,0x17a9813c30338430a4857,0x192492448a294922452924452893a9813c303384327114a,0x17a980343033843271057,0x47a980343033843271006,0x6452489c4929249236648d33246e46a372170c6929249246dc91a5234a4694911891922494912293a98037843430302b006,0x19244948a48a488a25292492488a32228a5249114529248914a4493a980378434303271057,0x17a980378434303271006] : List ℕ).getD (i-16) 0)
private def rows13 (i : ℕ) : ℕ := ([0x629244928a48a449c912712923894690408034343784340b006,0x6492365c9232d99248917248cb6649122e491c6636582100543434d83416017,0x19248e448c8e465991c89191c8cc64c91c8918e23239122a48e49122d492448b52448a9247224548d2912890210054343784dc16017,0x144080543437843416017,0x6492491b71b7246632e484932492331b7246632e132492371b8db9233197119249232998999249232d99236c992491c66365c92371b2c84080a43434d8342b02d,0x649248e46e371c8cc6623247246d46a39198cc46492391966471b32472331932391964c9246a349492351a2904080a4343784dc2b02d,0x14408054343784342b02d,0x24408034343784342b017,0x47a98034343784342b006,0x6492492268a3249248cc65c4cc9246632e48ca65152492491c8cc6639198899239198cc72331131448c9248d468a9222914a4493a9814034378434a4857,0x64892893a98140343784367114a,0x17a980343437843671057,0x27a980343437843671006,0x192291a5246948e24a48948929244944a4493a980378438343671006] : List ℕ).getD (i-0) 0
private def rows14 (i : ℕ) : ℕ := (if i < 13 then ([0x50408034383b84380b006,0x19249122a492366468991232292289c4cc52451b8a36649149146cc8a36629227146cc8a48a35123129244a2522512922512912890408054383b843816017,0x19249246e371b8613248db32366491b3226648d99198cc26492445192466331b3149134484080a4383870382b02d,0x19249236646cc9236cc66491b32366466330992491b3236648d991b3248d991b3246cc8d98484080ac3838e0742082d,0x192492466331b3248cb66491b8d991b2649248cc6636649198cc6cc92371b3246e36484080ac3838e0742b042,0x144080a43838e0742b02d,0x244080a43838e0382b02d,0x19249236646cc91b32366491b3236648d991b3099248cc6648d991b3246633246cc8d98484080b0383954e42082d,0x192492466331b3248cc66466326491b8d992371b2649248cb9196649198cc6cc91b3246e36484080b0383954e42b042,0x144080b0383954e42b02d,0x6492491a3234549234622929249244522a48914504080b03839c5582b02d,0x144080b03839c4e42b02d,0x504080b0383b85c82b02d] : List ℕ).getD (i-0) 0 else ([0x144080a4383b84e42b02d,0x44408054383b84382b02d,0x74408034383b84382b017,0x87a98034383b84382b006,0x192491228c9249246cc4646633148ca3249236646cc91b32366491b2a48d98894507ec1403838e03854857,0x6492492491b3236648d991b3248d988c91b3113249198cc91b3236648cc4648d98898a44519249244622a49123234515244522907ec140383b84e454857,0x14f6c140383b843854857,0x50f6c140383b8438a48aa,0x17a98140383b8438a4857,0x1893a98140383b843a7114a,0x17a98034383b843a71057,0x47a98034383b843a71006,0x648a252492448a9236644ca5249248db91a5234a12a24a44a4493a98037843c383a71006] : List ℕ).getD (i-13) 0)
private def rows15 (i : ℕ) : ℕ := (if i < 14 then ([0x504080343c3f843c0b006,0x648a48a46515225129244a25225129244a25225129225129128904080543c3f843c16017,0x6492491b4648cb3149196649236cc8999246d991b30992491445192465c88b3149134484080a83c3c743c2b02d,0x649244648cb3223246599246cc8d99236646c99245246598a47133248d99236cc91b3236484080ac3c3ce8782082d,0x649249198cc8cb3248cc6646599248cb9116649197232c99249232e465992466331c64c92465c6cc91c6636484080ac3c3ce8782b042,0x144080a83c3ce8782b02d,0x244080a83c3ce83c2b02d,0x6492446471332232366491b3236648d991b2649223238d991191b3248d991b3246cc6484080b03c3d5cec2082d,0x649249198cc7193248cc6638c99247198d992371b2649248cc6638c992465c6cc9238cc6cc91b6484080b03c3d5cec2b042,0x144080b03c3d5cec2b02d,0x19249223246d991188c92366468c48c46492491988c8ca3119248ca8d14504080b03c3dcd602b02d,0x144080b03c3dccec2b02d,0x504080b03c3f85d02b02d,0x144080a83c3f84ec2b02d] : List ℕ).getD (i-0) 0 else ([0x444080543c3f843c2b02d,0x744080343c3f843c2b017,0x87a980343c3f843c2b006,0x6492228c9249244ca9236646cc5244ca3249246d98cc91b32366491b2a48d98894507ec1443c3ce83c54857,0x649249248e36646cc91b32366491b3119236622649246cc8d99198cc92366232331932445488a32492491a32345492346468a2a488a4507ec1543c3dccec54857,0x507ec1543c3f85d054857,0x147ec1443c3f84ec54857,0x24f6c1443c3f843c54857,0x50f6c1443c3f843ca48aa,0x17a981443c3f843ca4857,0x53a981443c3f843e7114a,0x17a980343c3f843e71057,0x57a980343c3f843e71006,0x19149229229224514949249249197133246518949114a12a24a4493a9803784403c3e71006] : List ℕ).getD (i-14) 0)
private def rows16 (i : ℕ) : ℕ := (if i < 16 then ([0x50408034404384400b006,0x19225225129244a25225129244a25225129225129128904080544043844016017,0x6492491346468a92468c8999118c992491445192465b3144484080a8404078402b02d,0x649225129148d98a46c991491191b3223236484080ac4040f07c2082d,0x192492466331b3248cc66366491b89992371b2649248cc6636649198cc6cc92371b3246e36484080ac4040f07c2b042,0x144080a84040f07c2b02d,0x244080a84040f0402b02d,0x19245129223236644646c99244a25244633223236484080b0404164f42082d,0x192492466331b3248cc66466326491b8d992371b2649248cb9196649198cc6cc91b3246e36484080b0404164f42b042,0x144080b0404164f42b02d,0x19249128949226646cc91a32344c92249192492466332331932488a91146491b8d99225122644884080b04041d5682b02d,0x144080b04041d4f42b02d,0x644904080b0404385d82b02d,0x144080a8404384f42b02d,0x44408054404384402b02d,0x74408034404384402b017] : List ℕ).getD (i-0) 0 else ([0x87a98034404384402b006,0x6491232492488a9236644cc52228c9248d991b3246cc8d99246cc4648d98894507ec1444040f04054857,0x649249236646cc91b32366491b3119236622649233199236646cc9198cc91b32364c911522288600154404164f440057,0x649249236646cc88c46491b32366489191a2623244544886001544041d56840057,0x147ec1544041d4f440057,0x507ec1544041d4f454881,0x147ec1544041d4f454857,0x644907ec154404385d854857,0x147ec144404384f454857,0x44f6c1444043844054857,0x50f6c14440438440a48aa,0x17a9814440438440a4857,0x53a98144404384427114a,0x17a980344043844271057,0x77a980344043844271006,0x191492249492492468c8d15244522a24a4493a980378444404271006] : List ℕ).getD (i-16) 0)
private def rows17 (i : ℕ) : ℕ := ([0x50408034444784440b006,0x19224904080544447844416017,0x649244949198ca32488b89992448c89192492465b2e48d96649248cb65c91b2c84080a84444f4442b02d,0x6492448c8a26649249196cb92365992491c66365c9236cb3248a449991468c92491c6638c97248db2cc91a8d19224904080a8444784f82b02d,0x14408054444784442b02d,0x24408034444784442b017,0x37a98034444784442b006,0x6491232492488a68c9246632e48cc4598a24507ec1444444f44454857,0x649249248cc65c91988b3249198cb92331966488a9114649249198cb9233196648d468c91152448a2a44907ec144444784f854857,0x14f6c1444447844454857,0x50f6c14444478444a48aa,0x17a9814444478444a4857,0x53a98144444784467114a,0x17a980344447844671057,0x47a980344447844671006,0x6452489252492351a2a24a4493a980378448444671006] : List ℕ).getD (i-0) 0
private def rows18 (i : ℕ) : ℕ := (if i < 12 then ([0x50408034484b84480b006,0x50408054484b844816017,0x649148a448a32488c8918a226488a92488c8919244d192371b26492246448c92371b3246e36484080a84848fc482b02d,0x192446232492246448c92371b32364c92448c8919246e36648dc6c992232246492448c8919246e36646c992489188c92351a2884080b04849e1002b02d,0x6492448a4904080b0484b85e42b02d,0x144080a8484b85002b02d,0x24408054484b84482b02d,0x34408034484b84482b017,0x47a98034484b84482b006,0x192232492292266228c9248d991b3246cc8d99244ca9236622629114507ec1484848fc4854857,0x649249236646cc8cc66491b3226646632649246cc8d99236646cc9236646cc91b32364c9115222886001544849710040057,0x649249236646cc8cc66491b32366466326492468c8d15248d191a28c9115248922886001544849e17440057] : List ℕ).getD (i-0) 0 else ([0x147ec1544849e10040057,0x507ec1544849e10054881,0x147ec1544849e10054857,0x649114907ec154484b85e454857,0x147ec148484b850054857,0x44f6c148484b844854857,0x50f6c148484b8448a48aa,0x17a98148484b8448a4857,0x53a98148484b844a7114a,0x17a98034484b844a71057,0x77a98034484b844a71006,0x19145249148922a24a4493a98037844c484a71006] : List ℕ).getD (i-12) 0)
private def rows19 (i : ℕ) : ℕ := ([0x18a292489192445231491491232244c8a48919122648a48a489191226452448c89131491491232244c8a48a38899122648a4892293a980344c4f844c2b006,0x19149248a48a34523249238d99133246cc8d99222a48d99132629114507ec1484c4d044c54857,0x649249238d991b3246cc66491b3236646632649248db32366491b6646cc9236646cc91b32364c9115222886001544c4d750840057,0x649249246d991b3248db32366491b3236648d991b26492471b3236644623248d991b3223113248a245492445488a2886001544c4de57840057,0x147ec1544c4de50840057,0x507ec1544c4de50854881,0x147ec1544c4de50854857,0x6492488a8914907ec1544c4f85e854857,0x147ec1484c4f850854857,0x44f6c1484c4f844c54857,0x50f6c1484c4f844ca48aa,0x17a981484c4f844ca4857,0x53a981484c4f844e7114a,0x17a980344c4f844e71057,0x77a980344c4f844e71006,0x19145249122a24a4493a9803784504c4e71006] : List ℕ).getD (i-0) 0
private def rows20 (i : ℕ) : ℕ := ([0x628a48a448c5144648a48919123149123224648a4892293a98034505384502b006,0x19149248a248c9229133148d99129226622629114507ec14850510c5054857,0x19249228cc5236648cc6648d991b2649148d98a46cc9236646cc91b32364c91152228860015450517d1040057,0x649248a33148d99233199236646c992452366291a3248d991b32468c8d132491291145492445488a2886001545051ed8040057,0x147ec1545051ed1040057,0x507ec1545051ed1054881,0x147ec1545051ed1054857,0x192492448a9222914907ec154505385f054857,0x147ec1485053851054857,0x44f6c1485053845054857,0x50f6c14850538450a48aa,0x17a9814850538450a4857,0x53a98148505384527114a,0x17a980345053845271057,0x77a980345053845271006,0x19145244a24a4493a980378454505271006] : List ℕ).getD (i-0) 0
private def rows21 (i : ℕ) : ℕ := ([0x628a48a448c4a48944a4894493a98034545784542b006,0x649229248917132a49249148a32cc8a451966488a9226519248a45196645228cb3249222995249114ca2a492491468a92468a452493a980345457845671057,0x17a980345457845671006,0x19145244a24a4493a980378458545671006] : List ℕ).getD (i-0) 0
private def rows22 (i : ℕ) : ℕ := ([0x628a48944a48944a4894493a98034585b84582b006,0x6492292489191228a92492448c8919222a48a445146492246448c92488a91145492445488a28a92492448c46492445448a452493a98034585b845a71057,0x17a98034585b845a71006,0x645149124a4493a98037845c585a71006] : List ℕ).getD (i-0) 0
private def rows23 (i : ℕ) : ℕ := ([0x645149124a49229122a49229222a445191491152228a9248a49225122a445188a493a980345c5f845e71006,0x645149124a4493a9803784605c5e71006] : List ℕ).getD (i-0) 0
private def rows24 (i : ℕ) : ℕ := ([0x19144a49229122a492291289191489448a9248a44a246448a493a980346063846271006,0x19144a4493a980378464606271006] : List ℕ).getD (i-0) 0
private def rows25 (i : ℕ) : ℕ := ([0x645129248a448a9248919122a492246448a493a980346467846671006,0x19144a4493a980378468646671006] : List ℕ).getD (i-0) 0
private def rows26 (i : ℕ) : ℕ := ([0x19144a49224a44a44a2493a98034686b846a71006,0x19144a4493a98037846c686a71006] : List ℕ).getD (i-0) 0
private def rows27 (i : ℕ) : ℕ := ([0x644a49224a44a44a2493a980346c6f846e71006,0x19144a4493a9803784706c6e71006] : List ℕ).getD (i-0) 0
private def rows28 (i : ℕ) : ℕ := ([0x19129244a44a44a2493a980347073847271006,0x644a4493a980378474707271006] : List ℕ).getD (i-0) 0
private def rows29 (i : ℕ) : ℕ := ([0x19129244a44a44a2493a980347477847671006,0x644a4493a980378478747671006] : List ℕ).getD (i-0) 0
private def rows30 (i : ℕ) : ℕ := ([0x19129244a44a44a2493a98034787b847a71006,0x644a4493a98037847c787a71006] : List ℕ).getD (i-0) 0
private def rows31 (i : ℕ) : ℕ := ([0x19129244a44a44a2493a980347c7f847e71006,0x644a4493a9803784807c7e71006] : List ℕ).getD (i-0) 0
private def rows32 (i : ℕ) : ℕ := ([0x629244a44a44a2493a980348083848271006,0x1912893a980378484808271006] : List ℕ).getD (i-0) 0
private def tests (i : ℕ) : Bool :=
  if i<68 then rowOK rows6 (i-0) else
  if i<188 then rowOK rows7 (i-68) else
  if i<280 then rowOK rows8 (i-188) else
  if i<310 then rowOK rows9 (i-280) else
  if i<394 then rowOK rows10 (i-310) else
  if i<520 then rowOK rows11 (i-394) else
  if i<552 then rowOK rows12 (i-520) else
  if i<566 then rowOK rows13 (i-552) else
  if i<592 then rowOK rows14 (i-566) else
  if i<620 then rowOK rows15 (i-592) else
  if i<652 then rowOK rows16 (i-620) else
  if i<668 then rowOK rows17 (i-652) else
  if i<692 then rowOK rows18 (i-668) else
  if i<708 then rowOK rows19 (i-692) else
  if i<724 then rowOK rows20 (i-708) else
  if i<728 then rowOK rows21 (i-724) else
  if i<732 then rowOK rows22 (i-728) else
  if i<734 then rowOK rows23 (i-732) else
  if i<736 then rowOK rows24 (i-734) else
  if i<738 then rowOK rows25 (i-736) else
  if i<740 then rowOK rows26 (i-738) else
  if i<742 then rowOK rows27 (i-740) else
  if i<744 then rowOK rows28 (i-742) else
  if i<746 then rowOK rows29 (i-744) else
  if i<748 then rowOK rows30 (i-746) else
  if i<750 then rowOK rows31 (i-748) else
  rowOK rows32 (i-750)
private def g0 (i : ℕ) := tests i
private abbrev C0 := Cursor g0
private def c0_0 := Cursor.start g0
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_2:C0:=c0_0.step 0 2 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_5:C0:=c0_2.step 2 5 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_10:C0:=c0_5.step 5 10 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_18:C0:=c0_10.step 10 18 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_23:C0:=c0_18.step 18 23 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_38:C0:=c0_23.step 23 38 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_40:C0:=c0_38.step 38 40 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_46:C0:=c0_40.step 40 46 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_55:C0:=c0_46.step 46 55 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_70:C0:=c0_55.step 55 70 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_73:C0:=c0_70.step 70 73 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_78:C0:=c0_73.step 73 78 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_82:C0:=c0_78.step 78 82 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_87:C0:=c0_82.step 82 87 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_92:C0:=c0_87.step 87 92 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_106:C0:=c0_92.step 92 106 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_107:C0:=c0_106.step 106 107 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_111:C0:=c0_107.step 107 111 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_116:C0:=c0_111.step 111 116 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_123:C0:=c0_116.step 116 123 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_134:C0:=c0_123.step 123 134 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_139:C0:=c0_134.step 134 139 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_150:C0:=c0_139.step 139 150 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_167:C0:=c0_150.step 150 167 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_190:C0:=c0_167.step 167 190 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_194:C0:=c0_190.step 190 194 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_195:C0:=c0_194.step 194 195 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_200:C0:=c0_195.step 195 200 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_204:C0:=c0_200.step 200 204 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_211:C0:=c0_204.step 204 211 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_219:C0:=c0_211.step 211 219 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_223:C0:=c0_219.step 219 223 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_227:C0:=c0_223.step 223 227 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_238:C0:=c0_227.step 227 238 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_243:C0:=c0_238.step 238 243 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_250:C0:=c0_243.step 243 250 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_264:C0:=c0_250.step 250 264 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_281:C0:=c0_264.step 264 281 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_283:C0:=c0_281.step 281 283 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_286:C0:=c0_283.step 283 286 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_292:C0:=c0_286.step 286 292 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_296:C0:=c0_292.step 292 296 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_309:C0:=c0_296.step 296 309 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_313:C0:=c0_309.step 309 313 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_319:C0:=c0_313.step 313 319 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_322:C0:=c0_319.step 319 322 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_326:C0:=c0_322.step 322 326 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_330:C0:=c0_326.step 326 330 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c0_337:C0:=c0_330.step 330 337 rfl (by decide +kernel)
private theorem pass0 : Before g0 337 := c0_337.checked
private def g1 (i : ℕ) := tests (337+i)
private abbrev C1 := Cursor g1
private def c1_0 := Cursor.start g1
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_8:C1:=c1_0.step 0 8 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_23:C1:=c1_8.step 8 23 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_26:C1:=c1_23.step 23 26 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_38:C1:=c1_26.step 26 38 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_44:C1:=c1_38.step 38 44 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_60:C1:=c1_44.step 44 60 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_66:C1:=c1_60.step 60 66 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_71:C1:=c1_66.step 66 71 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_76:C1:=c1_71.step 71 76 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_81:C1:=c1_76.step 76 81 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_91:C1:=c1_81.step 81 91 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_94:C1:=c1_91.step 91 94 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_101:C1:=c1_94.step 94 101 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_116:C1:=c1_101.step 101 116 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_122:C1:=c1_116.step 116 122 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_130:C1:=c1_122.step 122 130 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_140:C1:=c1_130.step 130 140 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_145:C1:=c1_140.step 140 145 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_158:C1:=c1_145.step 145 158 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_164:C1:=c1_158.step 158 164 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_170:C1:=c1_164.step 164 170 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_185:C1:=c1_170.step 170 185 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_187:C1:=c1_185.step 185 187 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_191:C1:=c1_187.step 187 191 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_195:C1:=c1_191.step 191 195 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_205:C1:=c1_195.step 195 205 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_213:C1:=c1_205.step 205 213 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_218:C1:=c1_213.step 213 218 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_221:C1:=c1_218.step 218 221 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_231:C1:=c1_221.step 221 231 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_233:C1:=c1_231.step 231 233 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_237:C1:=c1_233.step 233 237 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_247:C1:=c1_237.step 237 247 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_255:C1:=c1_247.step 247 255 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_259:C1:=c1_255.step 255 259 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_263:C1:=c1_259.step 259 263 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_266:C1:=c1_263.step 263 266 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_274:C1:=c1_266.step 266 274 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_287:C1:=c1_274.step 274 287 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_292:C1:=c1_287.step 287 292 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_302:C1:=c1_292.step 292 302 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_318:C1:=c1_302.step 302 318 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_324:C1:=c1_318.step 318 324 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_335:C1:=c1_324.step 324 335 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_342:C1:=c1_335.step 335 342 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_356:C1:=c1_342.step 342 356 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_358:C1:=c1_356.step 356 358 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_372:C1:=c1_358.step 358 372 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_375:C1:=c1_372.step 372 375 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_392:C1:=c1_375.step 375 392 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_398:C1:=c1_392.step 392 398 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_414:C1:=c1_398.step 398 414 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c1_415:C1:=c1_414.step 414 415 rfl (by decide +kernel)
private theorem pass1 : Before g1 415 := c1_415.checked
private theorem valid : Before tests 752 := by
  have h0 : Before tests 337 := pass0
  have h1 : Before tests 752 := splice (a:=337) (b:=415) h0 pass1
  exact h1
namespace M6
private theorem ready : Ready rows6 68 := by
  intro i hi
  have got := valid (0+i) (by omega)
  unfold tests at got
  rw [if_pos (by omega)] at got
  simpa only [show 0+i-0=i by omega] using got
theorem normal : Closed (root 6 6 1250 false) := atRoot (i:=36) ready (by decide +kernel)
theorem reverse : Closed (root 6 6 1250 true) := atRoot (i:=67) ready (by decide +kernel)
end M6
namespace M7
private theorem ready : Ready rows7 120 := by
  intro i hi
  have got := valid (68+i) (by omega)
  unfold tests at got
  iterate 1 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 68+i-68=i by omega] using got
theorem normal : Closed (root 7 6 1250 false) := atRoot (i:=36) ready (by decide +kernel)
theorem reverse : Closed (root 7 6 1250 true) := atRoot (i:=119) ready (by decide +kernel)
end M7
namespace M8
private theorem ready : Ready rows8 92 := by
  intro i hi
  have got := valid (188+i) (by omega)
  unfold tests at got
  iterate 2 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 188+i-188=i by omega] using got
theorem normal : Closed (root 8 6 1250 false) := atRoot (i:=32) ready (by decide +kernel)
theorem reverse : Closed (root 8 6 1250 true) := atRoot (i:=91) ready (by decide +kernel)
end M8
namespace M9
private theorem ready : Ready rows9 30 := by
  intro i hi
  have got := valid (280+i) (by omega)
  unfold tests at got
  iterate 3 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 280+i-280=i by omega] using got
theorem normal : Closed (root 9 6 1250 false) := atRoot (i:=26) ready (by decide +kernel)
theorem reverse : Closed (root 9 6 1250 true) := atRoot (i:=29) ready (by decide +kernel)
end M9
namespace M10
private theorem ready : Ready rows10 84 := by
  intro i hi
  have got := valid (310+i) (by omega)
  unfold tests at got
  iterate 4 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 310+i-310=i by omega] using got
theorem normal : Closed (root 10 6 1250 false) := atRoot (i:=46) ready (by decide +kernel)
theorem reverse : Closed (root 10 6 1250 true) := atRoot (i:=83) ready (by decide +kernel)
end M10
namespace M11
private theorem ready : Ready rows11 126 := by
  intro i hi
  have got := valid (394+i) (by omega)
  unfold tests at got
  iterate 5 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 394+i-394=i by omega] using got
theorem normal : Closed (root 11 6 1250 false) := atRoot (i:=56) ready (by decide +kernel)
theorem reverse : Closed (root 11 6 1250 true) := atRoot (i:=125) ready (by decide +kernel)
end M11
namespace M12
private theorem ready : Ready rows12 32 := by
  intro i hi
  have got := valid (520+i) (by omega)
  unfold tests at got
  iterate 6 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 520+i-520=i by omega] using got
theorem normal : Closed (root 12 6 1250 false) := atRoot (i:=28) ready (by decide +kernel)
theorem reverse : Closed (root 12 6 1250 true) := atRoot (i:=31) ready (by decide +kernel)
end M12
namespace M13
private theorem ready : Ready rows13 14 := by
  intro i hi
  have got := valid (552+i) (by omega)
  unfold tests at got
  iterate 7 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 552+i-552=i by omega] using got
theorem normal : Closed (root 13 6 1250 false) := atRoot (i:=12) ready (by decide +kernel)
theorem reverse : Closed (root 13 6 1250 true) := atRoot (i:=13) ready (by decide +kernel)
end M13
namespace M14
private theorem ready : Ready rows14 26 := by
  intro i hi
  have got := valid (566+i) (by omega)
  unfold tests at got
  iterate 8 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 566+i-566=i by omega] using got
theorem normal : Closed (root 14 6 1250 false) := atRoot (i:=24) ready (by decide +kernel)
theorem reverse : Closed (root 14 6 1250 true) := atRoot (i:=25) ready (by decide +kernel)
end M14
namespace M15
private theorem ready : Ready rows15 28 := by
  intro i hi
  have got := valid (592+i) (by omega)
  unfold tests at got
  iterate 9 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 592+i-592=i by omega] using got
theorem normal : Closed (root 15 6 1250 false) := atRoot (i:=26) ready (by decide +kernel)
theorem reverse : Closed (root 15 6 1250 true) := atRoot (i:=27) ready (by decide +kernel)
end M15
namespace M16
private theorem ready : Ready rows16 32 := by
  intro i hi
  have got := valid (620+i) (by omega)
  unfold tests at got
  iterate 10 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 620+i-620=i by omega] using got
theorem normal : Closed (root 16 6 1250 false) := atRoot (i:=30) ready (by decide +kernel)
theorem reverse : Closed (root 16 6 1250 true) := atRoot (i:=31) ready (by decide +kernel)
end M16
namespace M17
private theorem ready : Ready rows17 16 := by
  intro i hi
  have got := valid (652+i) (by omega)
  unfold tests at got
  iterate 11 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 652+i-652=i by omega] using got
theorem normal : Closed (root 17 6 1250 false) := atRoot (i:=14) ready (by decide +kernel)
theorem reverse : Closed (root 17 6 1250 true) := atRoot (i:=15) ready (by decide +kernel)
end M17
namespace M18
private theorem ready : Ready rows18 24 := by
  intro i hi
  have got := valid (668+i) (by omega)
  unfold tests at got
  iterate 12 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 668+i-668=i by omega] using got
theorem normal : Closed (root 18 6 1250 false) := atRoot (i:=22) ready (by decide +kernel)
theorem reverse : Closed (root 18 6 1250 true) := atRoot (i:=23) ready (by decide +kernel)
end M18
namespace M19
private theorem ready : Ready rows19 16 := by
  intro i hi
  have got := valid (692+i) (by omega)
  unfold tests at got
  iterate 13 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 692+i-692=i by omega] using got
theorem normal : Closed (root 19 6 1250 false) := atRoot (i:=14) ready (by decide +kernel)
theorem reverse : Closed (root 19 6 1250 true) := atRoot (i:=15) ready (by decide +kernel)
end M19
namespace M20
private theorem ready : Ready rows20 16 := by
  intro i hi
  have got := valid (708+i) (by omega)
  unfold tests at got
  iterate 14 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 708+i-708=i by omega] using got
theorem normal : Closed (root 20 6 1250 false) := atRoot (i:=14) ready (by decide +kernel)
theorem reverse : Closed (root 20 6 1250 true) := atRoot (i:=15) ready (by decide +kernel)
end M20
namespace M21
private theorem ready : Ready rows21 4 := by
  intro i hi
  have got := valid (724+i) (by omega)
  unfold tests at got
  iterate 15 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 724+i-724=i by omega] using got
theorem normal : Closed (root 21 6 1250 false) := atRoot (i:=2) ready (by decide +kernel)
theorem reverse : Closed (root 21 6 1250 true) := atRoot (i:=3) ready (by decide +kernel)
end M21
namespace M22
private theorem ready : Ready rows22 4 := by
  intro i hi
  have got := valid (728+i) (by omega)
  unfold tests at got
  iterate 16 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 728+i-728=i by omega] using got
theorem normal : Closed (root 22 6 1250 false) := atRoot (i:=2) ready (by decide +kernel)
theorem reverse : Closed (root 22 6 1250 true) := atRoot (i:=3) ready (by decide +kernel)
end M22
namespace M23
private theorem ready : Ready rows23 2 := by
  intro i hi
  have got := valid (732+i) (by omega)
  unfold tests at got
  iterate 17 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 732+i-732=i by omega] using got
theorem normal : Closed (root 23 6 1250 false) := atRoot (i:=0) ready (by decide +kernel)
theorem reverse : Closed (root 23 6 1250 true) := atRoot (i:=1) ready (by decide +kernel)
end M23
namespace M24
private theorem ready : Ready rows24 2 := by
  intro i hi
  have got := valid (734+i) (by omega)
  unfold tests at got
  iterate 18 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 734+i-734=i by omega] using got
theorem normal : Closed (root 24 6 1250 false) := atRoot (i:=0) ready (by decide +kernel)
theorem reverse : Closed (root 24 6 1250 true) := atRoot (i:=1) ready (by decide +kernel)
end M24
namespace M25
private theorem ready : Ready rows25 2 := by
  intro i hi
  have got := valid (736+i) (by omega)
  unfold tests at got
  iterate 19 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 736+i-736=i by omega] using got
theorem normal : Closed (root 25 6 1250 false) := atRoot (i:=0) ready (by decide +kernel)
theorem reverse : Closed (root 25 6 1250 true) := atRoot (i:=1) ready (by decide +kernel)
end M25
namespace M26
private theorem ready : Ready rows26 2 := by
  intro i hi
  have got := valid (738+i) (by omega)
  unfold tests at got
  iterate 20 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 738+i-738=i by omega] using got
theorem normal : Closed (root 26 6 1250 false) := atRoot (i:=0) ready (by decide +kernel)
theorem reverse : Closed (root 26 6 1250 true) := atRoot (i:=1) ready (by decide +kernel)
end M26
namespace M27
private theorem ready : Ready rows27 2 := by
  intro i hi
  have got := valid (740+i) (by omega)
  unfold tests at got
  iterate 21 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 740+i-740=i by omega] using got
theorem normal : Closed (root 27 6 1250 false) := atRoot (i:=0) ready (by decide +kernel)
theorem reverse : Closed (root 27 6 1250 true) := atRoot (i:=1) ready (by decide +kernel)
end M27
namespace M28
private theorem ready : Ready rows28 2 := by
  intro i hi
  have got := valid (742+i) (by omega)
  unfold tests at got
  iterate 22 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 742+i-742=i by omega] using got
theorem normal : Closed (root 28 6 1250 false) := atRoot (i:=0) ready (by decide +kernel)
theorem reverse : Closed (root 28 6 1250 true) := atRoot (i:=1) ready (by decide +kernel)
end M28
namespace M29
private theorem ready : Ready rows29 2 := by
  intro i hi
  have got := valid (744+i) (by omega)
  unfold tests at got
  iterate 23 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 744+i-744=i by omega] using got
theorem normal : Closed (root 29 6 1250 false) := atRoot (i:=0) ready (by decide +kernel)
theorem reverse : Closed (root 29 6 1250 true) := atRoot (i:=1) ready (by decide +kernel)
end M29
namespace M30
private theorem ready : Ready rows30 2 := by
  intro i hi
  have got := valid (746+i) (by omega)
  unfold tests at got
  iterate 24 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 746+i-746=i by omega] using got
theorem normal : Closed (root 30 6 1250 false) := atRoot (i:=0) ready (by decide +kernel)
theorem reverse : Closed (root 30 6 1250 true) := atRoot (i:=1) ready (by decide +kernel)
end M30
namespace M31
private theorem ready : Ready rows31 2 := by
  intro i hi
  have got := valid (748+i) (by omega)
  unfold tests at got
  iterate 25 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 748+i-748=i by omega] using got
theorem normal : Closed (root 31 6 1250 false) := atRoot (i:=0) ready (by decide +kernel)
theorem reverse : Closed (root 31 6 1250 true) := atRoot (i:=1) ready (by decide +kernel)
end M31
namespace M32
private theorem ready : Ready rows32 2 := by
  intro i hi
  have got := valid (750+i) (by omega)
  unfold tests at got
  iterate 26 (rw [if_neg (by omega)] at got)
  simpa only [show 750+i-750=i by omega] using got
theorem normal : Closed (root 32 6 1250 false) := atRoot (i:=0) ready (by decide +kernel)
theorem reverse : Closed (root 32 6 1250 true) := atRoot (i:=1) ready (by decide +kernel)
end M32
end OMA.RankTwoJoined245212
namespace OMA.RankTwoJoined245212
open OMA.RankTwoInteriorCover245212 OMA.RankTwoInteriorWalk245212
theorem roots (m : ℕ) (lo : 6 ≤ m) (hi : m ≤ 32) (swap : Bool) : Closed (root m 6 1250 swap) := by
  interval_cases m
  · cases swap
    · exact M6.normal
    · exact M6.reverse
  · cases swap
    · exact M7.normal
    · exact M7.reverse
  · cases swap
    · exact M8.normal
    · exact M8.reverse
  · cases swap
    · exact M9.normal
    · exact M9.reverse
  · cases swap
    · exact M10.normal
    · exact M10.reverse
  · cases swap
    · exact M11.normal
    · exact M11.reverse
  · cases swap
    · exact M12.normal
    · exact M12.reverse
  · cases swap
    · exact M13.normal
    · exact M13.reverse
  · cases swap
    · exact M14.normal
    · exact M14.reverse
  · cases swap
    · exact M15.normal
    · exact M15.reverse
  · cases swap
    · exact M16.normal
    · exact M16.reverse
  · cases swap
    · exact M17.normal
    · exact M17.reverse
  · cases swap
    · exact M18.normal
    · exact M18.reverse
  · cases swap
    · exact M19.normal
    · exact M19.reverse
  · cases swap
    · exact M20.normal
    · exact M20.reverse
  · cases swap
    · exact M21.normal
    · exact M21.reverse
  · cases swap
    · exact M22.normal
    · exact M22.reverse
  · cases swap
    · exact M23.normal
    · exact M23.reverse
  · cases swap
    · exact M24.normal
    · exact M24.reverse
  · cases swap
    · exact M25.normal
    · exact M25.reverse
  · cases swap
    · exact M26.normal
    · exact M26.reverse
  · cases swap
    · exact M27.normal
    · exact M27.reverse
  · cases swap
    · exact M28.normal
    · exact M28.reverse
  · cases swap
    · exact M29.normal
    · exact M29.reverse
  · cases swap
    · exact M30.normal
    · exact M30.reverse
  · cases swap
    · exact M31.normal
    · exact M31.reverse
  · cases swap
    · exact M32.normal
    · exact M32.reverse
open scoped ArithmeticFunction.sigma
theorem original {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 13 ≤ p) (pq : p < q) (ha : 5 ≤ a) (hd : 5 ≤ d) :
    OeisA245212.a (2^k*p^a*q^d) ≠ (σ 1 (2^k*p^a*q^d):ℤ) :=
  OMA.RankTwoOriginalCover245212.of_roots roots hp hq op pq ha hd
end OMA.RankTwoJoined245212
end
section
namespace OMA.SmallLinear245212
open ArithmeticFunction
open scoped ArithmeticFunction.sigma
theorem exponential {C s start : ℕ} (nz : 0<start)
    (first : C*start^s < 2^start) (ratio : (start+1)^s≤2*start^s) :
    ∀ K, start≤K → C*K^s<2^K := by
  intro K hk
  induction K,hk using Nat.le_induction with
  | base => exact first
  | succ n hn ih =>
    have comp : (n+1)*start ≤ (start+1)*n := by nlinarith only [hn]
    have step := Nat.pow_le_pow_left comp s
    simp only [mul_pow] at step
    have limit : (n+1)^s*start^s ≤ (2*n^s)*start^s := calc
      _ ≤ (start+1)^s*n^s := step
      _ ≤ (2*start^s)*n^s := Nat.mul_le_mul_right _ ratio
      _ = _ := by ring
    have r := Nat.le_of_mul_le_mul_right limit (pow_pos nz s)
    rw [pow_succ];nlinarith only [Nat.mul_le_mul_left C r,ih]
theorem parity {p q a k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (oq : 3≤q) (pq : p≠q)
    (eqn : OeisA245212.a (2^k*p^a*q)=(σ 1 (2^k*p^a*q):ℤ)) : a%4=2 := by
  let primes : Fin 2 → ℕ := ![p,q]
  let exp : Fin 2 → ℕ := ![a,1]
  have pr : ∀ i, (primes i).Prime := by intro i;fin_cases i <;> assumption
  have odd : ∀ i, Odd (primes i) := fun i => (pr i).odd_of_ne_two (by fin_cases i <;> dsimp [primes] <;> omega)
  have inj : Function.Injective primes := by
    intro i j h;fin_cases i <;> fin_cases j <;> simp_all [primes]
  have total : OMA.Smooth245212.total primes exp = p^a*q := by
    simp [OMA.Smooth245212.total,Fin.prod_univ_two,primes,exp]
  have eq := OMA.ExponentParity245212.exponent_product primes exp pr odd inj k (by
    rw [total,←mul_assoc];exact eqn)
  simp [Fin.prod_univ_two, exp] at eq
  omega
theorem dyadic {p q a k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (oq : 3≤q) (pq : p≠q) (ha : 6≤a)
    (eqn : OeisA245212.a (2^k*p^a*q)=(σ 1 (2^k*p^a*q):ℤ)) : k+1<160 := by
  let K:=k+1
  let b:=a+1
  have eq' : OeisA245212.a (2^k*p^a*q^1)=(σ 1 (2^k*p^a*q^1):ℤ) := by simpa
  have flip : OeisA245212.a (2^k*q^1*p^a)=(σ 1 (2^k*q^1*p^a):ℤ) := by rwa [mul_right_comm]
  have cap := OMA.ComplementaryExp245212.exponent hp hq op oq pq (by decide : 1≤1) eq'
  have bnd : b≤256*K := by simpa [b,K] using cap
  have small := OMA.ComplementaryBase245212.small_prime hp hq op oq pq (by omega : 5≤(a+1)*(1+1)) eq'
  change p≤5*K ∨ q≤5*K at small
  have fin := OMA.SmallLength245212.complement hp hq op oq pq (by decide : 1≤1) (by omega) eq'
  change 2^K≤1+2*(1+1)*b*K*p^2*q^1+6*(1+1)^2*b*(K+p)*(q^1)^2 at fin
  norm_num only [pow_one,show (1+1:ℕ)=2 by rfl,show (2*2:ℕ)=4 by rfl,show (6*2^2:ℕ)=24 by rfl] at fin
  by_contra! h
  change 160≤K at h
  have fast : 2^56*K^12 < 2^K := exponential (by decide : 0<160) (by decide) (by decide) K h
  have hk : 1 ≤ K := by omega
  have cmp {i c : ℕ} (hi : i≤12) (hc : c≤2^56) : c*K^i<2^K :=
    (Nat.mul_le_mul hc (Nat.pow_le_pow_right hk hi)).trans_lt fast
  rcases small with ps | qs
  · have gc : 4*K*2*b*p<2^K := calc
      _ ≤ 4*K*2*(256*K)*(5*K) := by gcongr
      _ = 10240*K^3 := by ring
      _ < _ := cmp (by decide) (by decide)
    have pc : 8*K≤p^a := by
      by_contra! below
      have low := OMA.ComplementaryDyad245212.power_floor hp hq op oq pq (by decide : 1≤1) eq'
      change 2^K≤(6*2*K*b*p^a)^2 at low
      have limit : (6*2*K*b*p^a)^2 ≤ (6*2*K*(256*K)*(8*K))^2 := by gcongr
      have th : (6*2*K*(256*K)*(8*K))^2=603979776*K^6 := by ring
      exact (not_lt_of_ge (low.trans (limit.trans_eq th))) (cmp (by decide) (by decide))
    have qlim := OMA.ComplementaryFar245212.far hp hq op oq pq (by omega) (by decide : 1≤1) eq' gc pc
    have qmax : q ≤ 76800*K^4 := calc
      _ ≤ 6*2*K*b*p^2 := qlim
      _ ≤ 6*2*K*(256*K)*(5*K)^2 := by gcongr
      _ = _ := by ring
    have upper : 1+4*b*K*p^2*q+24*b*(K+p)*q^2 ≤
        1+4*(256*K)*K*(5*K)^2*(76800*K^4)+24*(256*K)*(K+5*K)*(76800*K^4)^2 := by gcongr
    have growth : 1+4*(256*K)*K*(5*K)^2*(76800*K^4)+24*(256*K)*(K+5*K)*(76800*K^4)^2
        ≤ 2^56*K^12 := by
      nlinarith only [Nat.one_le_pow 12 K (by omega),Nat.pow_le_pow_right hk (show 8≤12 by decide),
        Nat.pow_le_pow_right hk (show 10≤12 by decide)]
    exact (not_lt_of_ge (fin.trans (upper.trans growth))) fast
  · have gate : K*(a+1)*(1+1)*q^1<2^K := calc
      _ ≤ K*(256*K)*2*(5*K) := by rw [pow_one];change K*b*2*q≤_;gcongr
      _ = 2560*K^3 := by ring
      _ < _ := cmp (by decide) (by decide)
    have pbound := OMA.ComplementaryDyad245212.near hq hp oq op pq.symm (by omega) flip gate
    have pmax : p≤15360*K^3 := calc
      _ ≤ 6*b*K*2*q^1 := pbound
      _ ≤ 6*(256*K)*K*2*(5*K) := by rw [pow_one];gcongr
      _ = _ := by ring
    have upper : 1+4*b*K*p^2*q+24*b*(K+p)*q^2 ≤
        1+4*(256*K)*K*(15360*K^3)^2*(5*K)+24*(256*K)*(K+15360*K^3)*(5*K)^2 := by gcongr
    have growth : 1+4*(256*K)*K*(15360*K^3)^2*(5*K)+24*(256*K)*(K+15360*K^3)*(5*K)^2
        ≤ 2^56*K^12 := by
      nlinarith only [Nat.one_le_pow 12 K (by omega),Nat.pow_le_pow_right hk (show 9≤12 by decide),
        Nat.pow_le_pow_right hk (show 4≤12 by decide),Nat.pow_le_pow_right hk (show 6≤12 by decide)]
    exact (not_lt_of_ge (fin.trans (upper.trans growth))) fast
def limit (K : ℕ) := 4194304*(2^K)^2*K^5
theorem box {p q a k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (oq : 3≤q) (pq : p≠q)
    (eqn : OeisA245212.a (2^k*p^a*q)=(σ 1 (2^k*p^a*q):ℤ)) :
    k+1<160 ∧ a%4=2 ∧ p^(a-1)≤limit (k+1) ∧ a≤240 ∧ min p q≤5*(k+1) := by
  let K:=k+1
  let z:ℕ:=2^K
  have res := parity hp hq op oq pq eqn
  have ha : 2≤a := by omega
  have eq' : OeisA245212.a (2^k*p^a*q^1)=(σ 1 (2^k*p^a*q^1):ℤ) := by simpa
  have dy : K<160 := by
    by_cases big : 6≤a
    · exact dyadic hp hq op oq pq big eqn
    have a2 : a=2 := by omega
    subst a
    have odd := ((hp.odd_of_ne_two (by omega)).pow (n:=2)).mul (hq.odd_of_ne_two (by omega))
    have size : 1<p^2*q := by nlinarith only [hp.pos,hq.pos,op,oq,Nat.mul_le_mul_left (p^2) oq]
    have t := (OMA.DivisorHeight245212.effective_box odd size (by simpa only [←mul_assoc] using eqn)).1
    have cp := ((Nat.coprime_primes hp hq).mpr pq).pow_left 2
    have card : (p^2*q).divisors.card=6 := by
      have one : (σ 0) (q^1) = 1+1 := sigma_zero_apply_prime_pow hq
      simp only [pow_one] at one
      rw [←sigma_zero_apply,isMultiplicative_sigma.map_mul_of_coprime cp,
        sigma_zero_apply_prime_pow hp,one]
      decide
    rw [card] at t
    exact lt_of_le_of_lt t (by decide)
  have hk : 1≤K := by dsimp [K];omega
  have hz : 1≤z := Nat.one_le_pow _ _ (by decide)
  have bnd := OMA.ComplementaryExp245212.exponent hp hq op oq pq (by decide : 1≤1) eq'
  change a+1≤256*K at bnd
  have small := OMA.ComplementaryBase245212.small_prime hp hq op oq pq (by omega : 5≤(a+1)*(1+1)) eq'
  change p≤5*K ∨ q≤5*K at small
  have orig := OMA.ComplementaryBase245212.cofactor hp hq op oq pq eq'
  simp only [pow_one] at orig
  change p^a≤4*z*(K+p)*q at orig
  have power : p^(a-1)≤limit K := by
    change p^(a-1)≤4194304*z^2*K^5
    rcases small with ps | qs
    · have alt := OMA.ComplementaryPole245212.alternative hp hq op oq pq a 0 k ha eq'
      change p^a≤2*z*2*K ∨ q≤12*K*(a+1)*z*p^2 at alt
      apply (Nat.pow_le_pow_right hp.pos (Nat.sub_le _ _)).trans
      rcases alt with smallP | upper
      · have cf : 4*z*K^1≤4194304*z^2*K^5 :=
          Nat.mul_le_mul (Nat.mul_le_mul (by decide) (by simpa using Nat.pow_le_pow_right hz (show 1≤2 by decide)))
            (Nat.pow_le_pow_right hk (by decide))
        rw [pow_one] at cf
        exact smallP.trans (by nlinarith only [cf])
      · have bound : 4*z*(K+p)*q≤4*z*(K+5*K)*(12*K*(256*K)*z*(5*K)^2) := by
          apply Nat.mul_le_mul (by gcongr) (upper.trans (by gcongr))
        exact orig.trans (bound.trans (by nlinarith only [Nat.zero_le (z^2*K^5)]))
    · have kp : K+p≤2*K*p := by nlinarith only [Nat.mul_le_mul_left K hp.pos,Nat.mul_le_mul_right p hk]
      have bound : 4*z*(K+p)*q≤4*z*(2*K*p)*(5*K) := by gcongr
      have cancel : p^(a-1)≤40*z*K^2 := by
        apply Nat.le_of_mul_le_mul_right _ hp.pos
        rw [←pow_succ,show a-1+1=a by omega]
        exact orig.trans (bound.trans_eq (by ring))
      exact cancel.trans (Nat.mul_le_mul (Nat.mul_le_mul (by decide)
        (by simpa using Nat.pow_le_pow_right hz (show 1≤2 by decide))) (Nat.pow_le_pow_right hk (by decide)))
  refine ⟨dy,res,power,?_,by omega⟩
  by_contra! big
  have bigger : 3^240≤p^(a-1) :=
    (Nat.pow_le_pow_left op 240).trans (Nat.pow_le_pow_right hp.pos (by omega))
  have cut : limit K≤limit 160 := by unfold limit;gcongr;omega
  exact (not_le_of_gt (by decide : limit 160<3^240)) (bigger.trans (power.trans cut))
end OMA.SmallLinear245212
end
section
namespace OMA.SmallLinearReplay245212
open OMA.Large245212 OMA.RankTwoReplay245212
open scoped ArithmeticFunction.sigma
def row (r k : ℕ) : Bool :=
  let K:=k+1
  let w:=wt 2 k
  let s:=sig 2 k
  let t:=OMA.Large245212.tax 2 k
  let oneA:=w*wt r 1
  let oneS:=s*sig r 1
  let oneT:=t*OMA.Large245212.tax r 1
  let top:=min 59 (Nat.log r (OMA.SmallLinear245212.limit K)/4)
  (List.range (top+1)).all fun j =>
    let a:=4*j+2
    excluded r a oneA oneS oneT &&
      excluded r 1 (w*wt r a) (s*sig r a) (t*OMA.Large245212.tax r a)
def stripe (lo hi : ℕ) := (List.range' lo (hi+1-lo)).all fun r =>
  !decide r.Prime || (List.range' ((r+4)/5-1) (min 159 (2*r)+1-(r+4)/5)).all (row r)
theorem use_stripe {p q a k lo hi : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3 ≤ p) (oq : 3 ≤ q) (pq : p≠q) (lower : lo ≤ min p q) (upper : min p q≤hi)
    (ok : stripe lo hi=true) :
    OeisA245212.a (2^k*p^a*q)≠(σ 1 (2^k*p^a*q):ℤ) := by
  intro eqn
  obtain ⟨K,res,power,endA,small⟩:=OMA.SmallLinear245212.box hp hq op oq pq eqn
  have ha : 1≤a := by omega
  have eq' : OeisA245212.a (2^k*p^a*q^1)=(σ 1 (2^k*p^a*q^1):ℤ) := by simpa
  have flip : OeisA245212.a (2^k*q^1*p^a)=(σ 1 (2^k*q^1*p^a):ℤ) := by rwa [mul_right_comm]
  let r:=min p q
  have r3 : 3≤r := le_min op oq
  have pr : r.Prime := by rcases le_total p q with l|l <;> simp_all [r]
  have Kbound : k<2*r := by
    have pBound := OMA.TwoOddParameters245212.reciprocal hp hq op oq pq ha eq'
    have qBound := OMA.TwoOddParameters245212.reciprocal hq hp oq op pq.symm (by decide : 1≤1) flip
    have pk : k<2*p := by
      by_contra! fail
      nlinarith only [pBound,Nat.mul_le_mul_right a fail,Nat.mul_le_mul_left p ha]
    dsimp [r];omega
  have rpass:=List.all_eq_true.mp ok r (List.mem_range'_1.mpr ⟨lower,by omega⟩)
  simp only [pr,decide_true,Bool.not_true,Bool.false_or] at rpass
  have step:=List.all_eq_true.mp rpass k (List.mem_range'_1.mpr ⟨by dsimp [r] at *;omega,by dsimp [r] at *;omega⟩)
  have rg : r^(a-1)≤OMA.SmallLinear245212.limit (k+1) :=
    (Nat.pow_le_pow_left (min_le_left p q) _).trans power
  have alog := Nat.le_log_of_pow_le (by omega : 1<r) rg
  let j:=a/4
  have ja : 4*j+2=a := by dsimp [j];omega
  have part:=List.all_eq_true.mp step j (List.mem_range.mpr (by dsimp [j];omega))
  simp only [ja,Bool.and_eq_true] at part
  rcases lt_or_gt_of_ne pq with less|more
  · have ln : r=p := min_eq_left less.le
    rw [ln] at part
    exact leaf hp (by omega) hq less (by decide : 0<1) part.2 eq'
  · have ln : r=q := min_eq_right more.le
    rw [ln] at part
    exact leaf hq (by omega) hp more ha part.1 flip
end OMA.SmallLinearReplay245212
end
section
namespace OMA.SmallLinear245212
open OMA.SmallLinearReplay245212
open scoped ArithmeticFunction.sigma
set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
private theorem tables {j : ℕ} (bound : j≤24) :
    stripe (3+32*j) (34+32*j)=true := by
  interval_cases j <;> decide +kernel
theorem closed {p q a k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (oq : 3≤q) (pq : p≠q) :
    OeisA245212.a (2^k*p^a*q)≠(σ 1 (2^k*p^a*q):ℤ) := by
  intro eqn
  have info := box hp hq op oq pq eqn
  let j := (min p q-3)/32
  have r3 : 3 ≤ min p q := le_min op oq
  have rmax : min p q≤795 := by omega
  exact use_stripe hp hq op oq pq (by dsimp [j];omega : 3+32*j ≤ min p q)
    (by dsimp [j];omega : min p q≤34+32*j) (tables (by dsimp [j];omega)) eqn
end OMA.SmallLinear245212
end
section
namespace OMA.RankTwoStride245212
open scoped ArithmeticFunction.sigma
def step (d k : ℕ) := if d=2 then 2 else if d=4 ∧ 2≤k then 16 else 4
def offset (d k : ℕ) := if d=2 then 1 else if d=3 then 2 else if 2≤k then 4 else 0
theorem index {p q a d k b H : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (oq : 3≤q) (pq : p≠q) (lo : 2≤d) (hi : d≤4)
    (ba : b≤a) (aH : a≤H)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    (b+step d k-1-offset d k)/step d k≤a/step d k ∧
    a/step d k≤(H-offset d k)/step d k ∧ step d k*(a/step d k)+offset d k=a := by
  have par := OMA.SmallFacts245212.parity hp hq op oq pq eqn
  rcases (show d=2 ∨ d=3 ∨ d=4 by omega) with rfl|rfl|rfl
  · simp [step,offset] at *; omega
  · simp [step,offset] at *; omega
  · have pa := par.2.2 rfl
    by_cases hk : 2≤k
    · have h := OMA.RankTwoSieve8_245212.necessary hp hq op oq pq hk eqn
      simp [OMA.RankTwoSieve8_245212.compatible,pa] at h
      simp [step,offset,hk] at *; omega
    · simp [step,offset,hk] at *; omega
end OMA.RankTwoStride245212
end
section
namespace OMA.SmallExponent245212
open scoped ArithmeticFunction.sigma
def cap (d K r : ℕ) (rev : Bool) : ℕ :=
  let h:=d+1
  let z:=2^K
  let b:=64*h^2*K
  let factor:=3*z*K*h
  if rev then factor*r^d else
  let R:=6*h*K*b*r^2
  if 4*K*h*b*r<z then max (4*h*K) (factor*R^d)
  else max (2*z*h*K) (factor*(z*R)^d)
theorem power {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (oq : 3≤q) (pq : p≠q) (hd : 2≤d) (order : d≤a)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    (min p q)^(a-1)≤cap d (k+1) (min p q) (decide (q<p)) := by
  let K:=k+1
  let h:=d+1
  let z:ℕ:=2^K
  let b:=64*h^2*K
  let R:=6*h*K*b*p^2
  have rle := Nat.pow_le_pow_left (min_le_left p q) (a-1)
  have flip : OeisA245212.a (2^k*q^d*p^a)=(σ 1 (2^k*q^d*p^a):ℤ) := by rwa [mul_right_comm]
  have cp := OMA.TwoOddParameters245212.cofactor hq hp oq op pq.symm (by omega) flip
  change p^(a-1)≤3*z*K*h*q^d at cp
  have ab : a+1≤b := OMA.ComplementaryExp245212.exponent hp hq op oq pq (by omega) eqn
  by_cases rev : q<p
  · simpa [cap,rev,min_eq_right rev.le,h,K,z] using rle.trans cp
  · have le : p≤q := by omega
    simp only [min_eq_left le,cap,decide_eq_true_eq,if_neg rev]
    change p^(a-1) ≤ if 4*K*h*b*p<z then max (4*h*K) (3*z*K*h*R^d) else
        max (2*z*h*K) (3*z*K*h*(z*R)^d)
    split
    · rename_i cut
      by_cases small : p^a<4*h*K
      · exact le_max_of_le_left ((Nat.pow_le_pow_right hp.pos (Nat.sub_le _ _)).trans small.le)
      · have gc : 4*K*h*(a+1)*p<z := lt_of_le_of_lt (by gcongr) cut
        have pc : 4*h*K≤p^a := le_of_not_gt small
        have ub := OMA.ComplementaryFar245212.far hp hq op oq pq (by omega) (by omega) eqn gc pc
        have qr : q≤R := ub.trans (by dsimp [R,K,h];gcongr)
        exact le_max_of_le_right (cp.trans (by gcongr))
    · obtain ⟨e,de⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
      have alt := OMA.ComplementaryPole245212.alternative hp hq op oq pq a e k (by omega) (by simpa [de] using eqn)
      have eh : e+2=h := by dsimp [h];omega
      rw [eh] at alt
      rcases alt with direct|upper
      · exact le_max_of_le_left ((Nat.pow_le_pow_right hp.pos (Nat.sub_le _ _)).trans direct)
      · have qr : q≤z*R := by
          apply upper.trans
          calc
            _ ≤ 6*h*K*b*z*p^2 := by dsimp [K,z];gcongr
            _ = _ := by dsimp [R];ring
        exact le_max_of_le_right (cp.trans (by gcongr))
end OMA.SmallExponent245212
end
section
namespace OMA.SmallReplay245212
open OMA.Large245212 OMA.RankTwoReplay245212 OMA.SmallCaps245212
open scoped ArithmeticFunction.sigma
def first (d : ℕ) (few : Bool) := if few then d else 2*d+4
def stride (d : ℕ) := if d=2 then 2 else 4
def offset (d : ℕ) := if d=2 then 1 else if d=3 then 2 else 0
theorem index_fits {d a b H : ℕ} (lo : 2≤d) (hi : d≤4) (ba : b≤a) (aH : a≤H)
    (par : (d=2 → a%2=1) ∧ (d=3 → a%4=2) ∧ (d=4 → a%4=0)) :
    (b+stride d-1-offset d)/stride d≤a/stride d ∧
    a/stride d≤(H-offset d)/stride d ∧ stride d*(a/stride d)+offset d=a := by
  rcases (show d=2 ∨ d=3 ∨ d=4 by omega) with rfl|rfl|rfl <;> simp [stride,offset] at * <;> omega
def row (d r k : ℕ) (few rev : Bool) : Bool :=
  let K:=k+1
  let low:=first d few
  let baseLen:=(if rev then d else low)+1
  if r<OMA.TwoOddEffectiveTable245212.floorPrime K baseLen ||
      decide (13≤r ∧ 36≤(low+1)*(d+1) ∧ 9*K≤4*(r-1)) then true else
  let high:=if few then 2*d+3 else 1+Nat.log r (OMA.SmallExponent245212.cap d K r rev)
  let start:=(low+(OMA.RankTwoStride245212.step d k)-1-(OMA.RankTwoStride245212.offset d k))/(OMA.RankTwoStride245212.step d k)
  let hi:=(high-(OMA.RankTwoStride245212.offset d k))/(OMA.RankTwoStride245212.step d k)
  (List.range' start (hi+1-start)).all fun j =>
    let a:=(OMA.RankTwoStride245212.step d k)*j+(OMA.RankTwoStride245212.offset d k)
    let e:=if rev then d else a
    let f:=if rev then a else d
    (decide (2≤k) && !OMA.RankTwoSieve8_245212.compatible r e f) || OMA.RankTwoMoment245212.check k r e f
end OMA.SmallReplay245212
end
section
namespace OMA.SmallLeast245212
open ArithmeticFunction OMA.Smooth245212 OMA.ComplementaryLocal245212 OMA.ComplementaryPole245212
open scoped ArithmeticFunction.sigma
private theorem local_upper {p : ℕ} (hp : p.Prime) (op : 3≤p) (a : ℕ) {r : ℤ}
    (rp : r≤p) :
    (r-1)*(σ 1 (p^a):ℤ) ≤ r*p^a ∧
    (r-1)*(W (p^a):ℤ) ≤ (((a:ℤ)+1)*r-1)*p^a := by
  let P:ℤ:=(p:ℤ)^a
  let S:ℤ:=σ 1 (p^a)
  let V:ℤ:=W (p^a)
  let b:ℤ:=(a:ℤ)+1
  have geo : ((p:ℤ)-1)*S=p*P-1 := (moments hp a).1
  have w := OMA.PrimePowerDiv245212.weighted hp a
  zify [Nat.cast_sub hp.pos] at w
  change ((p:ℤ)-1)*V+S=p*(b*P) at w
  have positive : 0<P := pow_pos (by omega : (0:ℤ)<p) a
  have sl : P≤S := by
    apply (mul_le_mul_iff_right₀ (by omega : 0<(p:ℤ)-1)).mp
    nlinarith only [geo,positive]
  have wl : b*P≤V := by dsimp [b,P,V];exact_mod_cast (bounds hp op a).2.2.1
  change (r-1)*S≤r*P ∧ (r-1)*V≤(b*r-1)*P
  constructor
  · nlinarith only [geo,mul_nonneg (sub_nonneg.mpr rp) (sub_nonneg.mpr sl)]
  · nlinarith only [w,sl,mul_nonneg (sub_nonneg.mpr rp) (sub_nonneg.mpr wl)]
private theorem scalar {r b h m K F G : ℤ} (rr : 1≤r) (bb : 1≤b) (hh : 1≤h)
    (mm : 1 ≤ m) (mb : m≤b) (kk : 0≤K) (gg : 0<G) (fk : F≤K*G)
    (eqn : (F+G)*b*h*(r-1)^2 ≤ F*(b*r-1)*(h*r-1)+G*r^2) :
    (m*h-1)*r ≤ m*(2*h+K*(2*h-1)) := by
  have diff : 0 ≤ (b*r-1)*(h*r-1)-b*h*(r-1)^2 := by
    have u:=mul_le_mul (show b*(r-1)≤b*r-1 by nlinarith only [bb])
      (show h*(r-1)≤h*r-1 by nlinarith only [hh])
      (mul_nonneg (by omega) (by omega)) (by nlinarith only [mul_nonneg (by omega : 0≤b) (by omega : 0≤r-1),bb])
    nlinarith only [u]
  have limit : b*h*(r-1)^2-r^2 ≤ K*((b*r-1)*(h*r-1)-b*h*(r-1)^2) := by
    apply (mul_le_mul_iff_right₀ gg).mp
    nlinarith only [eqn,mul_le_mul_of_nonneg_right fk diff]
  have large : (b*h-1)*r ≤ b*(2*h+K*(2*h-1)) := by
    apply (mul_le_mul_iff_left₀ (by omega : 0<r)).mp
    have bh : 1≤b*h := by nlinarith only [mul_nonneg (show 0≤b-1 by omega) (show 0≤h-1 by omega),bb,hh]
    nlinarith only [limit, mul_nonneg kk (by omega : 0≤b*h-1),
      mul_nonneg (mul_nonneg kk (by omega : 0≤h)) (by omega : 0≤r),bh]
  apply (mul_le_mul_iff_right₀ (by omega : 0<b)).mp
  nlinarith only [mul_le_mul_of_nonneg_left large (by omega : 0 ≤ m),
    mul_nonneg (sub_nonneg.mpr mb) (by omega : 0≤r)]
theorem bound {p q a d k M : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (oq : 3≤q) (pq : p≠q) (mh : 1≤M) (mb : M≤a+1)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) :
    (M*(d+1)-1)*min p q ≤ M*(2*(d+1)+(k+1)*(2*(d+1)-1)) := by
  let r:ℤ:=min p q
  let b:ℤ:=(a:ℤ)+1
  let h:ℤ:=(d:ℤ)+1
  let P:ℤ:=(p:ℤ)^a
  let Q:ℤ:=(q:ℤ)^d
  have rr : 3≤r := by dsimp [r];exact_mod_cast le_min op oq
  have r₁ : r≤p := by dsimp [r];exact_mod_cast min_le_left p q
  have r₂ : r≤q := by dsimp [r];exact_mod_cast min_le_right p q
  have up:=local_upper hp op a r₁
  have uq:=local_upper hq oq d r₂
  have gp := (dyad k).1
  have fp := (dyad k).2.1
  have Ppos : 0<P := pow_pos (by omega : (0:ℤ)<p) _
  have Qpos : 0<Q := pow_pos (by omega : (0:ℤ)<q) _
  have b1 : 1≤b := by dsimp [b];omega
  have h1 : 1≤h := by dsimp [h];omega
  have wu := mul_le_mul up.2 uq.2 (mul_nonneg (by omega) (by positivity))
    (mul_nonneg (by nlinarith only [mul_nonneg (by omega : 0≤b) (by omega : 0≤r-1),b1] : 0≤b*r-1) Ppos.le)
  have su := mul_le_mul up.1 uq.1 (mul_nonneg (by omega) (by positivity)) (mul_nonneg (by omega : 0≤r) Ppos.le)
  have phy := physical hp hq (by omega) (by omega) pq a d k eqn
  change F k*_*_+G k*_*_=z k*(k+1)*b*h*P*Q at phy
  rw [←(dyad k).2.2.2] at phy
  have ratio : (F k+G k)*b*h*(r-1)^2 ≤ F k*(b*r-1)*(h*r-1)+G k*r^2 := by
    apply (mul_le_mul_iff_left₀ (mul_pos Ppos Qpos)).mp
    change (r-1)*_*((r-1)*_) ≤ ((b*r-1)*P)*((h*r-1)*Q) at wu
    change (r-1)*_*((r-1)*_) ≤ (r*P)*(r*Q) at su
    nlinarith only [congrArg (fun x:ℤ=>x*(r-1)^2) phy,
      mul_le_mul_of_nonneg_left wu fp.le,mul_le_mul_of_nonneg_left su gp.le]
  have ans := scalar (by omega : 1≤r) b1 h1 (by exact_mod_cast mh : (1:ℤ)≤M)
    (by dsimp [b];exact_mod_cast mb) (by positivity : (0:ℤ)≤k+1) gp (dyad k).2.2.1 ratio
  dsimp [b,h,r] at ans
  zify [show 1≤M*(d+1) by nlinarith only [mh,Nat.zero_le (M*d)],show 1≤2*(d+1) by omega]
  exact ans
end OMA.SmallLeast245212
end
section
namespace OMA.SmallFastReplay245212
open OMA.Large245212 OMA.RankTwoReplay245212 OMA.SmallCaps245212 OMA.SmallReplay245212
open OMA.SmallReplay245212 (index_fits)
open scoped ArithmeticFunction.sigma
def beginAt (d b r : ℕ) := ((b*(d+1)-1)*r-2*b*(d+1)-1)/(b*(2*(d+1)-1))
private theorem enter {d b r k : ℕ} (_r3 : 3≤r) (bh : 1≤b) (_hd : 2≤d)
    (h : (b*(d+1)-1)*r≤b*(2*(d+1)+(k+1)*(2*(d+1)-1))) : beginAt d b r≤k := by
  have hp : 0<b*(2*(d+1)-1) := Nat.mul_pos (by omega) (by omega)
  have h' : (b*(d+1)-1)*r≤2*b*(d+1)+(k+1)*(b*(2*(d+1)-1)) := by nlinarith only [h]
  unfold beginAt
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hp).mpr
  change (b*(d+1)-1)*r-2*b*(d+1)-1 < (k+1)*(b*(2*(d+1)-1))
  have pos : 0<(k+1)*(b*(2*(d+1)-1)) := Nat.mul_pos (Nat.succ_pos _) hp
  omega
private theorem leave {e K r : ℕ} (he : 0<e)
    (h : OMA.TwoOddEffectiveTable245212.floorPrime (K+1) (e+1)≤r) : K<r*(e+1)/e+1 := by
  unfold OMA.TwoOddEffectiveTable245212.floorPrime at h
  simp only [Nat.add_sub_cancel,max_le_iff] at h
  have ht := (Nat.div_lt_iff_lt_mul (Nat.succ_pos e)).mp (by omega : K*e/(e+1)<r)
  have cut := (Nat.le_div_iff_mul_le he).mpr ht.le
  exact Nat.lt_succ_of_le cut
def stripe (d : ℕ) (few rev : Bool) (lo hi : ℕ) :=
  OMA.RankTwoPrimeBook245212.scan lo hi fun r =>
    let b:=first d few
    let e:=if rev then d else b
    let start:=beginAt d (b+1) r
    let top:=min (ceiling d few rev) (r*(e+1)/e+1)
    (List.range' start (top-start)).all (fun k => row d r k few rev)
theorem use_stripe {p q a d k lo hi : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3 ≤ p) (oq : 3 ≤ q) (pq : p≠q) (hd : 2≤d) (ed : d≤4) (order : d≤a)
    (lower : lo ≤ min p q) (upper : min p q≤hi)
    (ok : stripe d (decide (a<2*d+4)) (decide (q<p)) lo hi=true)
    (eqn : OeisA245212.a (2^k*p^a*q^d)=(σ 1 (2^k*p^a*q^d):ℤ)) : False := by
  let r:=min p q
  let f:=decide (a<2*d+4)
  let v:=decide (q<p)
  let b:=first d f
  let low:=(if v then d else b)+1
  have r3 : 3≤r := le_min op oq
  have pr : r.Prime := by rcases le_total p q with l|l <;> simp_all [r]
  have ba : b≤a := by by_cases c : a<2*d+4 <;> simp [b,first,f,c] <;> omega
  have small := OMA.ComplementaryBase245212.small_prime hp hq op oq pq (by nlinarith only [hd,order,Nat.zero_le (a*d)] : 5≤(a+1)*(d+1)) eqn
  have dy := OMA.SmallCaps245212.dyadic hp hq op oq pq hd ed order eqn
  have par := OMA.SmallFacts245212.parity hp hq op oq pq eqn
  have flip : OeisA245212.a (2^k*q^d*p^a)=(σ 1 (2^k*q^d*p^a):ℤ) := by rwa [mul_right_comm]
  have cut : OMA.TwoOddEffectiveTable245212.floorPrime (k+1) low≤r := by
    dsimp [low,v,r]
    split
    · rename_i rev
      have smaller : q<p := by simpa using rev
      rw [min_eq_right smaller.le]
      exact OMA.TwoOddParameters245212.floor hq hp oq op pq.symm (by omega) (by omega) le_rfl flip
    · rename_i rev
      have smaller : p≤q := by simpa using rev
      rw [min_eq_left smaller]
      exact OMA.TwoOddParameters245212.floor hp hq op oq pq (by omega) (by omega) (by omega) eqn
  have wide : ¬(13≤r ∧ 36≤(b+1)*(d+1) ∧ 9*(k+1)≤4*(r-1)) := by
    rintro ⟨room,size,bad⟩
    have h:=OMA.SmallFacts245212.either hp hq pq room (size.trans (Nat.mul_le_mul_right _ (by omega))) eqn
    omega
  have rpass := OMA.RankTwoPrimeBook245212.member ok pr lower upper
  have bh : 1≤b := by dsimp [b,first];split <;> omega
  have nh := OMA.SmallLeast245212.bound hp hq op oq pq (Nat.succ_pos b) (Nat.add_le_add_right ba 1) eqn
  change ((b+1)*(d+1)-1)*r ≤ (b+1)*(2*(d+1)+(k+1)*(2*(d+1)-1)) at nh
  have lowerK := enter (d:=d) r3 (Nat.succ_pos b) (by omega) nh
  have ul := leave (K:=k) (e:=if v then d else b) (r:=r) (by split <;> omega) cut
  have ur : k < min (ceiling d f v) (r*((if v then d else b)+1)/(if v then d else b)+1) := lt_min (by exact dy) ul
  have rowpass := List.all_eq_true.mp rpass k (List.mem_range'_1.mpr ⟨lowerK,by change k<beginAt d (b+1) r+(min (ceiling d f v) (r*((if v then d else b)+1)/(if v then d else b)+1)-beginAt d (b+1) r);omega⟩)
  change row d r k f v=true at rowpass
  unfold row at rowpass
  have rn : ¬r<OMA.TwoOddEffectiveTable245212.floorPrime (k+1) low := not_lt_of_ge cut
  change (if (decide (r<OMA.TwoOddEffectiveTable245212.floorPrime (k+1) low) || decide (13≤r ∧ 36≤(b+1)*(d+1) ∧ 9*(k+1)≤4*(r-1))) then _ else _)=true at rowpass
  simp only [rn,wide,decide_false,Bool.false_or,Bool.false_eq_true,↓reduceIte] at rowpass
  let H:=if f then 2*d+3 else 1+Nat.log r (OMA.SmallExponent245212.cap d (k+1) r v)
  let j:=a/(OMA.RankTwoStride245212.step d k)
  have aH : a≤H := by
    by_cases few : a<2*d+4
    · simp [H,f,few];omega
    · simp only [H,f,few,decide_false,Bool.false_eq_true,↓reduceIte]
      have pw:=OMA.SmallExponent245212.power hp hq op oq pq hd order eqn
      have e:=Nat.le_log_of_pow_le (by omega : 1<r) pw
      change a-1≤Nat.log r (OMA.SmallExponent245212.cap d (k+1) r v) at e
      omega
  have idx : (b+(OMA.RankTwoStride245212.step d k)-1-(OMA.RankTwoStride245212.offset d k))/(OMA.RankTwoStride245212.step d k)≤j ∧ j≤(H-(OMA.RankTwoStride245212.offset d k))/(OMA.RankTwoStride245212.step d k) ∧ (OMA.RankTwoStride245212.step d k)*j+(OMA.RankTwoStride245212.offset d k)=a := by
    exact OMA.RankTwoStride245212.index hp hq op oq pq hd ed ba aH eqn
  have point:=List.all_eq_true.mp rowpass j (List.mem_range'_1.mpr ⟨idx.1,by dsimp [H,b] at *;omega⟩)
  simp only [idx.2.2] at point
  by_cases rev : q<p
  · have qv : v=true := by simp [v,rev]
    have rq : r=q := min_eq_right rev.le
    simp only [qv,↓reduceIte,rq] at point
    have ok : OMA.RankTwoMoment245212.check k q d a=true := by
      by_cases hk : 2≤k
      · simpa [hk,OMA.RankTwoSieve8_245212.necessary hq hp oq op pq.symm hk flip] using point
      · simpa [hk] using point
    exact OMA.RankTwoMoment245212.point hq (by omega) hp rev (by omega) ok flip
  · have qv : v=false := by simp [v,rev]
    have rp : r=p := min_eq_left (by omega)
    simp only [qv,Bool.false_eq_true,↓reduceIte,rp] at point
    have ok : OMA.RankTwoMoment245212.check k p a d=true := by
      by_cases hk : 2≤k
      · simpa [hk,OMA.RankTwoSieve8_245212.necessary hp hq op oq pq hk eqn] using point
      · simpa [hk] using point
    exact OMA.RankTwoMoment245212.point hp (by omega) hq (by omega) (by omega) ok eqn
end OMA.SmallFastReplay245212
end
section
namespace OMA.SmallFastDegree245212
open OMA.SmallCaps245212 OMA.SmallFastReplay245212
open scoped ArithmeticFunction.sigma
def lastPrime (d : ℕ) (f v : Bool) :=
  let m:=OMA.SmallReplay245212.first d f+1
  m*(2*(d+1)+ceiling d f v*(2*(d+1)-1))/(m*(d+1)-1)
def Checked (d : ℕ) (f v : Bool) : Prop :=
  ∀ j : ℕ, j≤(lastPrime d f v-3)/32 → stripe d f v (3+32*j) (34+32*j)=true
theorem of_tables {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (oq : 3≤q) (pq : p≠q) (hd : 2≤d) (ed : d≤4) (order : d≤a)
    (tables : ∀ f v, Checked d f v) :
    OeisA245212.a (2^k*p^a*q^d)≠(σ 1 (2^k*p^a*q^d):ℤ) := by
  intro eqn
  let f:=decide (a<2*d+4)
  let v:=decide (q<p)
  let b:=OMA.SmallReplay245212.first d f
  have ba : b≤a := by by_cases c : a<2*d+4 <;> simp [b,OMA.SmallReplay245212.first,f,c] <;> omega
  have dy : k+1≤ceiling d f v := OMA.SmallCaps245212.dyadic hp hq op oq pq hd ed order eqn
  have sep := OMA.SmallLeast245212.bound hp hq op oq pq (Nat.succ_pos b) (Nat.add_le_add_right ba 1) eqn
  have factor : 2≤(b+1)*(d+1) := by nlinarith only [hd,Nat.zero_le b,Nat.zero_le (b*d)]
  have pos : 0<(b+1)*(d+1)-1 := by omega
  have upper : min p q≤lastPrime d f v := by
    apply (Nat.le_div_iff_mul_le pos).mpr
    rw [Nat.mul_comm]
    exact sep.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ dy) _))
  let j:=(min p q-3)/32
  have size : j≤(lastPrime d f v-3)/32 := by dsimp [j];omega
  have lb : 3+32*j ≤ min p q := by dsimp [j];omega
  have ub : min p q≤34+32*j := by dsimp [j];omega
  exact use_stripe hp hq op oq pq hd ed order lb ub (tables f v j size) eqn
end OMA.SmallFastDegree245212
end
section
namespace OMA.RankTwoLowTape245212
open OMA.RankTwoCursor245212 OMA.SmallFastReplay245212 OMA.SmallFastDegree245212
private def test (i : ℕ) : Bool :=
  if i<13 then (let j:=i-0; stripe 2 false false (3+32*j) (34+32*j)) else
  if i<21 then (let j:=i-13; stripe 2 false true (3+32*j) (34+32*j)) else
  if i<30 then (let j:=i-21; stripe 2 true false (3+32*j) (34+32*j)) else
  if i<47 then (let j:=i-30; stripe 2 true true (3+32*j) (34+32*j)) else
  if i<67 then (let j:=i-47; stripe 3 false false (3+32*j) (34+32*j)) else
  if i<77 then (let j:=i-67; stripe 3 false true (3+32*j) (34+32*j)) else
  if i<89 then (let j:=i-77; stripe 3 true false (3+32*j) (34+32*j)) else
  if i<118 then (let j:=i-89; stripe 3 true true (3+32*j) (34+32*j)) else
  if i<146 then (let j:=i-118; stripe 4 false false (3+32*j) (34+32*j)) else
  if i<159 then (let j:=i-146; stripe 4 false true (3+32*j) (34+32*j)) else
  if i<175 then (let j:=i-159; stripe 4 true false (3+32*j) (34+32*j)) else
  let j:=i-175; stripe 4 true true (3+32*j) (34+32*j)
private abbrev C := Cursor test
private def c0 := Cursor.start test
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c2:C:=c0.step 0 2 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c4:C:=c2.step 2 4 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c6:C:=c4.step 4 6 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c8:C:=c6.step 6 8 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c10:C:=c8.step 8 10 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c12:C:=c10.step 10 12 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c14:C:=c12.step 12 14 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c16:C:=c14.step 14 16 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c18:C:=c16.step 16 18 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c20:C:=c18.step 18 20 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c22:C:=c20.step 20 22 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c24:C:=c22.step 22 24 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c26:C:=c24.step 24 26 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c28:C:=c26.step 26 28 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c30:C:=c28.step 28 30 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c32:C:=c30.step 30 32 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c34:C:=c32.step 32 34 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c36:C:=c34.step 34 36 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c38:C:=c36.step 36 38 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c40:C:=c38.step 38 40 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c42:C:=c40.step 40 42 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c44:C:=c42.step 42 44 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c46:C:=c44.step 44 46 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c48:C:=c46.step 46 48 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c50:C:=c48.step 48 50 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c52:C:=c50.step 50 52 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c54:C:=c52.step 52 54 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c56:C:=c54.step 54 56 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c58:C:=c56.step 56 58 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c60:C:=c58.step 58 60 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c62:C:=c60.step 60 62 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c64:C:=c62.step 62 64 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c66:C:=c64.step 64 66 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c68:C:=c66.step 66 68 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c70:C:=c68.step 68 70 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c72:C:=c70.step 70 72 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c74:C:=c72.step 72 74 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c76:C:=c74.step 74 76 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c78:C:=c76.step 76 78 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c80:C:=c78.step 78 80 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c82:C:=c80.step 80 82 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c84:C:=c82.step 82 84 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c86:C:=c84.step 84 86 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c88:C:=c86.step 86 88 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c90:C:=c88.step 88 90 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c92:C:=c90.step 90 92 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c94:C:=c92.step 92 94 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c96:C:=c94.step 94 96 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c98:C:=c96.step 96 98 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c100:C:=c98.step 98 100 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c102:C:=c100.step 100 102 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c104:C:=c102.step 102 104 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c106:C:=c104.step 104 106 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c108:C:=c106.step 106 108 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c110:C:=c108.step 108 110 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c112:C:=c110.step 110 112 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c114:C:=c112.step 112 114 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c116:C:=c114.step 114 116 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c118:C:=c116.step 116 118 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c120:C:=c118.step 118 120 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c122:C:=c120.step 120 122 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c124:C:=c122.step 122 124 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c126:C:=c124.step 124 126 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c128:C:=c126.step 126 128 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c130:C:=c128.step 128 130 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c132:C:=c130.step 130 132 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c134:C:=c132.step 132 134 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c136:C:=c134.step 134 136 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c138:C:=c136.step 136 138 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c140:C:=c138.step 138 140 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c142:C:=c140.step 140 142 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c144:C:=c142.step 142 144 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c146:C:=c144.step 144 146 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c148:C:=c146.step 146 148 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c150:C:=c148.step 148 150 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c152:C:=c150.step 150 152 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c154:C:=c152.step 152 154 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c156:C:=c154.step 154 156 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c158:C:=c156.step 156 158 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c160:C:=c158.step 158 160 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c162:C:=c160.step 160 162 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c164:C:=c162.step 162 164 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c166:C:=c164.step 164 166 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c168:C:=c166.step 166 168 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c170:C:=c168.step 168 170 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c172:C:=c170.step 170 172 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c174:C:=c172.step 172 174 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c176:C:=c174.step 174 176 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c178:C:=c176.step 176 178 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c180:C:=c178.step 178 180 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c182:C:=c180.step 180 182 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c184:C:=c182.step 182 184 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c186:C:=c184.step 184 186 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c188:C:=c186.step 186 188 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c190:C:=c188.step 188 190 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c192:C:=c190.step 190 192 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c194:C:=c192.step 192 194 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c196:C:=c194.step 194 196 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c198:C:=c196.step 196 198 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c200:C:=c198.step 198 200 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c202:C:=c200.step 200 202 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c204:C:=c202.step 202 204 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c206:C:=c204.step 204 206 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c208:C:=c206.step 206 208 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c210:C:=c208.step 208 210 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c212:C:=c210.step 210 212 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c214:C:=c212.step 212 214 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c216:C:=c214.step 214 216 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c218:C:=c216.step 216 218 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c220:C:=c218.step 218 220 rfl (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private def c221:C:=c220.step 220 221 rfl (by decide +kernel)
private theorem valid : Before test 221 := c221.checked
theorem part2_00 : Checked 2 false false := by
  intro i lim
  have bound : i<13 := by change i≤12 at lim; omega
  have got:=valid (0+i) (by omega)
  unfold test at got
  rw [if_pos (by omega)] at got
  simpa only [show 0+i-0=i by omega] using got
theorem part2_01 : Checked 2 false true := by
  intro i lim
  have bound : i<8 := by change i≤7 at lim; omega
  have got:=valid (13+i) (by omega)
  unfold test at got
  iterate 1 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 13+i-13=i by omega] using got
theorem part2_10 : Checked 2 true false := by
  intro i lim
  have bound : i<9 := by change i≤8 at lim; omega
  have got:=valid (21+i) (by omega)
  unfold test at got
  iterate 2 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 21+i-21=i by omega] using got
theorem part2_11 : Checked 2 true true := by
  intro i lim
  have bound : i<17 := by change i≤16 at lim; omega
  have got:=valid (30+i) (by omega)
  unfold test at got
  iterate 3 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 30+i-30=i by omega] using got
theorem part3_00 : Checked 3 false false := by
  intro i lim
  have bound : i<20 := by change i≤19 at lim; omega
  have got:=valid (47+i) (by omega)
  unfold test at got
  iterate 4 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 47+i-47=i by omega] using got
theorem part3_01 : Checked 3 false true := by
  intro i lim
  have bound : i<10 := by change i≤9 at lim; omega
  have got:=valid (67+i) (by omega)
  unfold test at got
  iterate 5 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 67+i-67=i by omega] using got
theorem part3_10 : Checked 3 true false := by
  intro i lim
  have bound : i<12 := by change i≤11 at lim; omega
  have got:=valid (77+i) (by omega)
  unfold test at got
  iterate 6 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 77+i-77=i by omega] using got
theorem part3_11 : Checked 3 true true := by
  intro i lim
  have bound : i<29 := by change i≤28 at lim; omega
  have got:=valid (89+i) (by omega)
  unfold test at got
  iterate 7 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 89+i-89=i by omega] using got
theorem part4_00 : Checked 4 false false := by
  intro i lim
  have bound : i<28 := by change i≤27 at lim; omega
  have got:=valid (118+i) (by omega)
  unfold test at got
  iterate 8 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 118+i-118=i by omega] using got
theorem part4_01 : Checked 4 false true := by
  intro i lim
  have bound : i<13 := by change i≤12 at lim; omega
  have got:=valid (146+i) (by omega)
  unfold test at got
  iterate 9 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 146+i-146=i by omega] using got
theorem part4_10 : Checked 4 true false := by
  intro i lim
  have bound : i<16 := by change i≤15 at lim; omega
  have got:=valid (159+i) (by omega)
  unfold test at got
  iterate 10 (rw [if_neg (by omega)] at got)
  rw [if_pos (by omega)] at got
  simpa only [show 159+i-159=i by omega] using got
theorem part4_11 : Checked 4 true true := by
  intro i lim
  have bound : i<46 := by change i≤45 at lim; omega
  have got:=valid (175+i) (by omega)
  unfold test at got
  iterate 11 (rw [if_neg (by omega)] at got)
  simpa only [show 175+i-175=i by omega] using got
end OMA.RankTwoLowTape245212
end
section
namespace OMA.SmallSecondBlocks245212
open OMA.SmallFastReplay245212 OMA.SmallFastDegree245212
open scoped ArithmeticFunction.sigma
theorem closed {p q a k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (oq : 3≤q) (pq : p≠q) (ha : 2≤a) :
    OeisA245212.a (2^k*p^a*q^2)≠(σ 1 (2^k*p^a*q^2):ℤ) := by
  apply of_tables hp hq op oq pq (by decide) (by decide) ha
  intro f v
  cases f <;> cases v
  · exact OMA.RankTwoLowTape245212.part2_00
  · exact OMA.RankTwoLowTape245212.part2_01
  · exact OMA.RankTwoLowTape245212.part2_10
  · exact OMA.RankTwoLowTape245212.part2_11
end OMA.SmallSecondBlocks245212
end
section
namespace OMA.SmallThirdBlocks245212
open OMA.SmallFastReplay245212 OMA.SmallFastDegree245212
open scoped ArithmeticFunction.sigma
theorem closed {p q a k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (oq : 3≤q) (pq : p≠q) (ha : 3≤a) :
    OeisA245212.a (2^k*p^a*q^3)≠(σ 1 (2^k*p^a*q^3):ℤ) := by
  apply of_tables hp hq op oq pq (by decide) (by decide) ha
  intro f v
  cases f <;> cases v
  · exact OMA.RankTwoLowTape245212.part3_00
  · exact OMA.RankTwoLowTape245212.part3_01
  · exact OMA.RankTwoLowTape245212.part3_10
  · exact OMA.RankTwoLowTape245212.part3_11
end OMA.SmallThirdBlocks245212
end
section
namespace OMA.SmallFourthBlocks245212
open OMA.SmallFastReplay245212 OMA.SmallFastDegree245212
open scoped ArithmeticFunction.sigma
theorem closed {p q a k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (oq : 3≤q) (pq : p≠q) (ha : 4≤a) :
    OeisA245212.a (2^k*p^a*q^4)≠(σ 1 (2^k*p^a*q^4):ℤ) := by
  apply of_tables hp hq op oq pq (by decide) (by decide) ha
  intro f v
  cases f <;> cases v
  · exact OMA.RankTwoLowTape245212.part4_00
  · exact OMA.RankTwoLowTape245212.part4_01
  · exact OMA.RankTwoLowTape245212.part4_10
  · exact OMA.RankTwoLowTape245212.part4_11
end OMA.SmallFourthBlocks245212
end
section
namespace OMA.SmallOriginal245212
open scoped ArithmeticFunction.sigma
private theorem ordered {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (oq : 3≤q) (pq : p≠q) (hd : 1≤d) (small : d≤4) (order : d≤a) :
    OeisA245212.a (2^k*p^a*q^d)≠(σ 1 (2^k*p^a*q^d):ℤ) := by
  interval_cases d
  · simpa using OMA.SmallLinear245212.closed (a:=a) (k:=k) hp hq op oq pq
  · exact OMA.SmallSecondBlocks245212.closed hp hq op oq pq order
  · exact OMA.SmallThirdBlocks245212.closed hp hq op oq pq order
  · exact OMA.SmallFourthBlocks245212.closed hp hq op oq pq order
theorem closed {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (oq : 3≤q) (pq : p≠q) (ha : 1≤a) (hd : 1≤d) (small : min a d≤4) :
    OeisA245212.a (2^k*p^a*q^d)≠(σ 1 (2^k*p^a*q^d):ℤ) := by
  rcases le_total d a with da|ad
  · exact ordered hp hq op oq pq hd (by omega) da
  · rw [mul_right_comm (2^k)]
    exact ordered hq hp oq op pq.symm ha (by omega) ad
end OMA.SmallOriginal245212
end
section
namespace OMA.Least7Pair245212
open Nat Finset ArithmeticFunction OMA.PairSweep245212
open scoped ArithmeticFunction.sigma
set_option maxHeartbeats 50000000 in
theorem at_0 {q e f : ℕ} (hq : q.Prime) (pq : 7<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^0*7^e*q^f)≠(σ 1 (2^0*7^e*q^f):ℤ) := by
  by_cases big : 8≤q
  · exact OMA.DyadicEuler245212.pair_small (by decide) hq (by decide) pq ep (u:=7) (v:=8)
      (by decide) (by decide) le_rfl big (by decide +kernel)
  interval_cases q <;> norm_num at *
set_option maxHeartbeats 50000000 in
theorem at_1 {q e f : ℕ} (hq : q.Prime) (pq : 7<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^1*7^e*q^f)≠(σ 1 (2^1*7^e*q^f):ℤ) := by
  by_cases big : 8≤q
  · exact OMA.DyadicEuler245212.pair_small (by decide) hq (by decide) pq ep (u:=7) (v:=8)
      (by decide) (by decide) le_rfl big (by decide +kernel)
  interval_cases q <;> norm_num at *
end OMA.Least7Pair245212
end
section
namespace OMA.Least11Pair245212
open Nat Finset ArithmeticFunction OMA.PairSweep245212
open scoped ArithmeticFunction.sigma
set_option maxHeartbeats 50000000 in
theorem at_0 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^0*11^e*q^f)≠(σ 1 (2^0*11^e*q^f):ℤ) := by
  by_cases big : 12≤q
  · exact OMA.DyadicEuler245212.pair_small (by decide) hq (by decide) pq ep (u:=11) (v:=12)
      (by decide) (by decide) le_rfl big (by decide +kernel)
  interval_cases q <;> norm_num at *
set_option maxHeartbeats 50000000 in
theorem at_1 {q e f : ℕ} (hq : q.Prime) (pq : 11<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^1*11^e*q^f)≠(σ 1 (2^1*11^e*q^f):ℤ) := by
  by_cases big : 12≤q
  · exact OMA.DyadicEuler245212.pair_small (by decide) hq (by decide) pq ep (u:=11) (v:=12)
      (by decide) (by decide) le_rfl big (by decide +kernel)
  interval_cases q <;> norm_num at *
end OMA.Least11Pair245212
end
section
namespace OMA.RankTwoLeastCap245212
open OMA.RankTwoReplay245212
open scoped ArithmeticFunction.sigma
open OMA.RankTwoReplay245212 (member)
def line (p k d : ℕ) (reverse : Bool) :=
  allIn d (1+Nat.log p (OMA.SmallExponent245212.cap d (k+1) p reverse)) fun a =>
    let e:=if reverse then d else a
    let f:=if reverse then a else d
    !OMA.RankTwoFiltered245212.allowed e f || !OMA.RankTwoSieve8_245212.compatible p e f ||
      OMA.RankTwoMoment245212.check k p e f
def audit (p k : ℕ) := allIn 5 31 fun d => line p k d false && line p k d true
theorem sound {p q k e f : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 2<p)
    (pq : p<q) (hk : 2≤k) (ep : 5≤e) (fp : 5≤f) (checked : audit p k=true) :
    OeisA245212.a (2^k*p^e*q^f)≠(σ 1 (2^k*p^e*q^f):ℤ) := by
  intro eqn
  have small:=OMA.TwoOddEffectiveOriginal245212.bound hp hq op pq hk eqn
  have he:=OMA.RankTwoFiltered245212.necessary hp hq op pq eqn
  have hc:=OMA.RankTwoSieve8_245212.necessary hp hq op (by omega) pq.ne hk eqn
  by_cases le : f≤e
  · have hf:=OMA.SmallExponent245212.power hp hq op (by omega) pq.ne (by omega) le eqn
    simp only [min_eq_left pq.le,not_lt_of_ge pq.le,decide_false] at hf
    have hi:=Nat.le_log_of_pow_le (by omega : 1<p) hf
    have passes:=OMA.RankTwoReplay245212.member checked fp (by omega : f≤31)
    change (line p k f false && line p k f true)=true at passes
    simp only [Bool.and_eq_true] at passes
    have out:=OMA.RankTwoReplay245212.member passes.1 le (by omega : e≤1+Nat.log p (OMA.SmallExponent245212.cap f (k+1) p false))
    simp only [Bool.false_eq_true,↓reduceIte,he,hc,Bool.not_true,Bool.false_or] at out
    exact OMA.RankTwoMoment245212.point hp op hq pq (by omega) out eqn
  · have flip : OeisA245212.a (2^k*q^f*p^e)=(σ 1 (2^k*q^f*p^e):ℤ) := by rwa [mul_right_comm]
    have hf:=OMA.SmallExponent245212.power hq hp (by omega) op pq.ne' (by omega) (by omega : e≤f) flip
    simp only [min_eq_right pq.le,pq,decide_true] at hf
    have hi:=Nat.le_log_of_pow_le (by omega : 1<p) hf
    have passes:=OMA.RankTwoReplay245212.member checked ep (by omega : e≤31)
    change (line p k e false && line p k e true)=true at passes
    simp only [Bool.and_eq_true] at passes
    have out:=OMA.RankTwoReplay245212.member passes.2 (by omega : e≤f) (by omega : f≤1+Nat.log p (OMA.SmallExponent245212.cap e (k+1) p true))
    simp only [↓reduceIte,he,hc,Bool.not_true,Bool.false_or] at out
    exact OMA.RankTwoMoment245212.point hp op hq pq (by omega) out eqn
set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
theorem table {p k : ℕ} (prime : p=3 ∨ p=5 ∨ p=7 ∨ p=11) (lo : 2≤k) (hi : k<2*p) :
    audit p k=true := by
  rcases prime with rfl|rfl|rfl|rfl <;> interval_cases k <;> decide +kernel
end OMA.RankTwoLeastCap245212
end
section
namespace OMA.Least3Pair245212
open Nat Finset ArithmeticFunction OMA.PairSweep245212
open scoped ArithmeticFunction.sigma
set_option maxHeartbeats 50000000 in
theorem at_0 {q e f : ℕ} (hq : q.Prime) (pq : 3<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^0*3^e*q^f)≠(σ 1 (2^0*3^e*q^f):ℤ) := by
  by_cases big : 5≤q
  · exact OMA.DyadicEuler245212.pair_small (by decide) hq (by decide) pq ep (u:=3) (v:=5)
      (by decide) (by decide) le_rfl big (by decide +kernel)
  interval_cases q <;> norm_num at *
set_option maxHeartbeats 50000000 in
theorem at_1 {q e f : ℕ} (hq : q.Prime) (pq : 3<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^1*3^e*q^f)≠(σ 1 (2^1*3^e*q^f):ℤ) := by
  by_cases big : 17≤q
  · exact OMA.DyadicEuler245212.pair_small (by decide) hq (by decide) pq ep (u:=3) (v:=17)
      (by decide) (by decide) le_rfl big (by decide +kernel)
  have cases : q=5 ∨ q=7 ∨ q=11 ∨ q=13 := by
    interval_cases q <;> norm_num at *
  rcases cases with rfl|rfl|rfl|rfl
  · apply known_case (B:=3) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=6) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=18) (by decide) hq (by decide) pq ep fp <;> decide +kernel
  · apply known_case (B:=36) (by decide) hq (by decide) pq ep fp <;> decide +kernel
end OMA.Least3Pair245212
end
section
namespace OMA.Least5Pair245212
open Nat Finset ArithmeticFunction OMA.PairSweep245212
open scoped ArithmeticFunction.sigma
set_option maxHeartbeats 50000000 in
theorem at_0 {q e f : ℕ} (hq : q.Prime) (pq : 5<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^0*5^e*q^f)≠(σ 1 (2^0*5^e*q^f):ℤ) := by
  by_cases big : 6≤q
  · exact OMA.DyadicEuler245212.pair_small (by decide) hq (by decide) pq ep (u:=5) (v:=6)
      (by decide) (by decide) le_rfl big (by decide +kernel)
  interval_cases q <;> norm_num at *
set_option maxHeartbeats 50000000 in
theorem at_1 {q e f : ℕ} (hq : q.Prime) (pq : 5<q) (ep : 0<e) (fp : 0<f) :
    OeisA245212.a (2^1*5^e*q^f)≠(σ 1 (2^1*5^e*q^f):ℤ) := by
  by_cases big : 6≤q
  · exact OMA.DyadicEuler245212.pair_small (by decide) hq (by decide) pq ep (u:=5) (v:=6)
      (by decide) (by decide) le_rfl big (by decide +kernel)
  interval_cases q <;> norm_num at *
end OMA.Least5Pair245212
end
section
namespace OMA.RankTwoAll245212
open Finset
open scoped ArithmeticFunction.sigma
open OMA.DyadicPower245212 (dyadic_balance)
theorem dyadic (k : ℕ) : OeisA245212.a (2^k)=(σ 1 (2^k):ℤ) :=
  OMA.Abundance245212.eq_of_balance (by positivity) (OMA.DyadicPower245212.dyadic_balance k)
theorem one {p e k : ℕ} (hp : p.Prime) (op : 3≤p) (ep : 0<e) :
    OeisA245212.a (2^k*p^e)≠(σ 1 (2^k*p^e):ℤ) := by
  intro eqn
  have nd : ¬p∣2^k := fun h => (by omega : p≠2) ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have eq0 : OeisA245212.a (2^k*p^0)=(σ 1 (2^k*p^0):ℤ) := by simpa using dyadic k
  have := OMA.Abundance245212.unique_exponent (by positivity) hp nd eqn eq0
  omega
private theorem ordered {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (op : 3≤p) (pq : p<q) (ha : 0<a) (hd : 0<d) :
    OeisA245212.a (2^k*p^a*q^d)≠(σ 1 (2^k*p^a*q^d):ℤ) := by
  by_cases wide : 13≤p
  · by_cases small : min a d≤4
    · exact OMA.SmallOriginal245212.closed hp hq op (by omega) pq.ne ha hd small
    · exact OMA.RankTwoJoined245212.original hp hq wide pq (by omega) (by omega)
  have choice : p=3 ∨ p=5 ∨ p=7 ∨ p=11 := by interval_cases p <;> norm_num at *
  by_cases small : min a d≤4
  · exact OMA.SmallOriginal245212.closed hp hq op (by omega) pq.ne ha hd small
  by_cases hk : 2≤k
  · intro eqn
    have odd : Odd (p^a*q^d) := ((hp.odd_of_ne_two (by omega)).pow).mul ((hq.odd_of_ne_two (by omega)).pow)
    have mem : p∈(p^a*q^d).primeFactors := Nat.mem_primeFactors.mpr
      ⟨hp,dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') _,by have := hp.pos;have := hq.pos;positivity⟩
    have top := OMA.DyadicLeast245212.exponent_lt_twice_prime odd mem (by simpa [mul_assoc] using eqn)
    exact OMA.RankTwoLeastCap245212.sound hp hq op pq hk (by omega) (by omega)
      (OMA.RankTwoLeastCap245212.table choice hk top) eqn
  have kt : k≤1 := by omega
  rcases choice with rfl|rfl|rfl|rfl
  · interval_cases k
    · exact OMA.Least3Pair245212.at_0 hq pq ha hd
    · exact OMA.Least3Pair245212.at_1 hq pq ha hd
  · interval_cases k
    · exact OMA.Least5Pair245212.at_0 hq pq ha hd
    · exact OMA.Least5Pair245212.at_1 hq pq ha hd
  · interval_cases k
    · exact OMA.Least7Pair245212.at_0 hq pq ha hd
    · exact OMA.Least7Pair245212.at_1 hq pq ha hd
  · interval_cases k
    · exact OMA.Least11Pair245212.at_0 hq pq ha hd
    · exact OMA.Least11Pair245212.at_1 hq pq ha hd
theorem two {p q a d k : ℕ} (hp : p.Prime) (hq : q.Prime) (op : 3≤p)
    (oq : 3≤q) (pq : p≠q) (ha : 0<a) (hd : 0<d) :
    OeisA245212.a (2^k*p^a*q^d)≠(σ 1 (2^k*p^a*q^d):ℤ) := by
  rcases lt_or_gt_of_ne pq with lt|gt
  · exact ordered hp hq op lt ha hd
  · rw [mul_right_comm (2^k)]
    exact ordered hq hp oq gt hd ha
end OMA.RankTwoAll245212
end
section
open Finset
open scoped ArithmeticFunction.sigma
theorem OMA.solution : OMA.R_OeisA245212_conjecture_R1_H2_R3.H2 := by
  intro k _
  dsimp only
  intro m _ odd hm rank eqn
  let e := m.factorization
  let s := m.primeFactors
  have fac : (∏ p ∈ s, p ^ e p) = m :=
    (Nat.prod_primeFactors_pow_factorization (by omega : m ≠ 0)).symm
  have each {p} (h : p ∈ s) : p.Prime ∧ 3 ≤ p ∧ 0 < e p := by
    have pr := Nat.prime_of_mem_primeFactors h
    have ne : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors h))
    exact ⟨pr, by have := pr.two_le; omega, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp h)⟩
  change s.card ≤ 2 at rank
  have cases : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
  rcases cases with empty | single | pair
  · rw [card_eq_zero.mp empty, prod_empty] at fac
    omega
  · obtain ⟨p, hs⟩ := card_eq_one.mp single
    obtain ⟨hp, op, ep⟩ := each (p := p) (by simp [hs])
    rw [hs, prod_singleton] at fac
    rw [← fac] at eqn
    exact OMA.RankTwoAll245212.one hp op ep eqn
  · obtain ⟨p, q, pq, hs⟩ := card_eq_two.mp pair
    obtain ⟨hp, op, ep⟩ := each (p := p) (by simp [hs])
    obtain ⟨hq, oq, eq⟩ := each (p := q) (by simp [hs])
    rw [hs, prod_insert (by simpa using pq), prod_singleton] at fac
    rw [← fac, ← mul_assoc] at eqn
    exact OMA.RankTwoAll245212.two hp hq op oq pq ep eq eqn
end
