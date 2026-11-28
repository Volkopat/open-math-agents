import OMAReductions.R_OeisA245212_conjecture_R2_H2_R1




/-! Uniform divisor-count height at large rank or dyadic order. -/

section

/- Exact interval certificates for the mixed 7-smooth A245212 family.
An absent upper endpoint represents the limit at an unbounded exponent. -/
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

/- Identification of the interval score with the original weighted sum. -/
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

/- A uniform abundancy obstruction and the exclusion of constant
prime-exponent families in the A245212 divisor equality. -/
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

/- Every prime-power divisor of an A245212 solution divides a nonzero
combination of the two divisor moments of its coprime cofactor. -/
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

/- Simultaneous integer separation after rounding both odd prime powers.
The coefficient pair (f,g) denotes t=f/g, permitting t=k and t=γ. -/
namespace OMA.TwoOddGlobalGap245212

def defect (f g p q B C : ℤ) :=
  (f+g)*B*C*(p-1)^2*(q-1)^2 -
    p*q*(f*(B*(p-1)-1)*(C*(q-1)-1)+g*(p-1)*(q-1))

def alpha (f g p q C : ℤ) := q*(f*(C*(q-1)-1)-g*(p-1)*(q-1))
def beta (f g p q B : ℤ) := p*(f*(B*(p-1)-1)-g*(p-1)*(q-1))

/-- The simultaneous finite-tail formula is a polynomial identity. The
four moment identities input here are the ordinary geometric sums. -/
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

/-- A nonpositive finite-balance residual forces a nonzero integer after
both local prime-power factors are replaced by their rational limits. -/
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

/-- The coarser range used in the original two-prime finiteness theorem. -/
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

/- Local exact divisor identities, taken directly from the formal OEIS
equality; these are the arithmetic inputs of the complementary-exponent bound. -/
namespace OMA.ComplementaryLocal245212
open Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma

/-- Ordinary and weighted finite geometric sums, in a form that keeps
the two small residuals exactly. -/
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

theorem binary (k : ℕ) :
    (σ 1 (2^k):ℤ)=(2:ℤ)^(k+1)-1 ∧ (W (2^k):ℤ)=1+k*(2:ℤ)^(k+1) := by
  have h := moments Nat.prime_two k
  norm_num at h
  rw [pow_succ]; constructor <;> nlinarith only [h.1,h.2]

/-- Starting at the actual OEIS hypothesis, both odd factors and the power
of two separate with no asymptotic or arithmetic assumptions. -/
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

/-- The ordinary OEIS equality directly implies both nonzero integer
defects used in the unrestricted rank-two finiteness proof. -/
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

/- The divisor score strictly increases in one prime exponent as soon as
one other prime exponent is sufficiently large. -/
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

private theorem x_one {q : ℕ} (hq : 1<q) (e : ℕ) : 1≤X q (some e) := by
  have q1 : (1:ℚ)<q := by exact_mod_cast hq
  exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (y_one hq _)) (by linarith))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def otherFactors (f : ι → ℚ) (i : ι) : ℚ := ∏ j∈univ.erase i,f j
private theorem update_value (p e : ι → ℕ) (i : ι) (t : ℕ) :
    normalized p (Function.update e i t) =
      otherFactors (fun j => X (p j) (some (e j))) i*X (p i) (some t) +
      otherFactors (fun j => Y (p j) (some (e j))) i*Y (p i) (some t) := by
  have prod_update (F : ι → ℕ → ℚ) :
      (∏ j,F j (Function.update e i t j))=otherFactors (fun j => F j (e j)) i * F i t := by
    rw [←prod_erase_mul _ _ (mem_univ i),Function.update_self]
    congr 1
    exact prod_congr rfl fun j hj => by rw [Function.update_of_ne (mem_erase.mp hj).1]
  exact congrArg₂ (·+·) (prod_update (fun j v => X (p j) (some v)))
    (prod_update (fun j v => Y (p j) (some v)))

theorem upward (p : ι → ℕ) (hp : ∀ i,Nat.Prime (p i)) (e : ι → ℕ)
    {i j : ι} (ij : j≠i) (high : 2*p i≤e j) {t : ℕ} (lt : e i<t) :
    normalized p e<normalized p (Function.update e i t) := by
  let xx := otherFactors (fun j => X (p j) (some (e j))) i
  let yy := otherFactors (fun j => Y (p j) (some (e j))) i
  have hj : j∈(univ:Finset ι).erase i := mem_erase.mpr ⟨ij,mem_univ j⟩
  have yl : yy≤Y (p j) (some (e j)) := by
    dsimp [yy,otherFactors]
    rw [←prod_erase_mul _ _ hj]
    exact mul_le_of_le_one_left (y_nonneg (hp j).one_lt _)
      (prod_le_one (fun h _ => y_nonneg (hp h).one_lt _) (fun h _ => y_one (hp h).one_lt _))
  have xl : 1≤xx := one_le_prod (fun h _ => x_one (hp h).one_lt _)
  have yr := y_short (hp j) (e j)
  have yp := y_nonneg (hp j).one_lt (some (e j))
  have pp : (1:ℚ)<p i := by exact_mod_cast (hp i).one_lt
  have ht : (2:ℚ)*p i≤e j := by exact_mod_cast high
  have cap : yy*((p i:ℚ)-1)<xx := by
    have bound := mul_le_mul_of_nonneg_right yl (show 0≤(p i:ℚ)-1 by linarith)
    have dual := mul_nonneg yp (show 0≤(e j:ℚ)+1-2*((p i:ℚ)-1) by linarith only [ht])
    linarith only [yr,bound,dual,xl]
  have dec := y_strict (hp i).one_lt lt
  have old : normalized p e=xx*X (p i) (some (e i))+yy*Y (p i) (some (e i)) := by
    simpa [xx,yy] using update_value p e i (e i)
  rw [old,update_value]
  change xx*X _ _+yy*Y _ _ < xx*X _ _+yy*Y _ _
  unfold X
  have positive := mul_pos (sub_pos.mpr cap) (sub_pos.mpr dec)
  apply sub_pos.mp
  have difference (a b : ℚ) :
      (xx*(1+(1-b)/((p i:ℚ)-1))+yy*b) - (xx*(1+(1-a)/((p i:ℚ)-1))+yy*a) =
      ((xx-yy*((p i:ℚ)-1))*(a-b))/((p i:ℚ)-1) := by
    field_simp [sub_ne_zero.mpr pp.ne']; ring
  rw [difference]
  exact div_pos positive (by linarith)

theorem nondecrease (p : ι → ℕ) (hp : ∀ i,Nat.Prime (p i)) {e f : ι → ℕ}
    (ef : e≤f) (witness : ∀ i,e i<f i → ∃ j,j≠i ∧ 2*p i≤e j) :
    normalized p e≤normalized p f := by
  let mix (s : Finset ι) (i : ι) := if i∈s then f i else e i
  have h (s : Finset ι) : normalized p e≤normalized p (mix s) := by
    induction s using Finset.induction_on with
    | empty => simp [mix]
    | @insert i s his ih =>
      have update : mix (insert i s)=Function.update (mix s) i (f i) := by
        funext j
        by_cases ji : j=i <;> simp [mix,ji]
      rw [update]
      have old : mix s i=e i := by simp [mix,his]
      rcases (ef i).eq_or_lt with same|lt
      · simpa [←same,←old] using ih
      · obtain ⟨j,ij,high⟩ := witness i lt
        have hj : e j ≤ mix s j := by by_cases js : j∈s <;> simp [mix,js,ef _]
        exact ih.trans (upward p hp (mix s) ij (high.trans hj) (old ▸ lt)).le
  simpa [mix] using h univ

theorem strict_of_changes (p : ι → ℕ) (hp : ∀ i,Nat.Prime (p i)) {e f : ι → ℕ}
    (ef : e≤f) {i : ι} (lt : e i<f i) (witness : ∀ i,e i<f i → ∃ j,j≠i ∧ 2*p i≤e j) :
    normalized p e<normalized p f := by
  let g := Function.update e i (f i)
  have eg (j : ι) : e j≤g j := by by_cases ji : j=i <;> simp [g,ji,ef _]
  have gf : g≤f := by intro j; by_cases ji : j=i <;> simp [g,ji,ef _]
  obtain ⟨j,ij,high⟩ := witness i lt
  refine (upward p hp e ij high lt).trans_le (nondecrease p hp (e:=g) gf ?_)
  intro l hl
  obtain ⟨r,rl,hr⟩ := witness l ((eg l).trans_lt hl)
  exact ⟨r,rl,hr.trans (eg r)⟩

end OMA.CapOrder245212

end

section

/- Cleared rational proxies for three independently moving odd prime powers. -/
namespace OMA.ThreeMovingLocal245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212
open scoped ArithmeticFunction.sigma

def den (p e : ℕ) (round : Bool) := if round then (e+1)*(p-1)^2 else e+1
def xn (p e : ℕ) (round : Bool) := if round then p*((e+1)*(p-1)-1) else e+1
def yn (p _e : ℕ) (round : Bool) := if round then p*(p-1) else 1
def xx (p e : ℕ) (b : Bool) : ℚ := (xn p e b:ℚ)/den p e b
def yy (p e : ℕ) (b : Bool) : ℚ := (yn p e b:ℚ)/den p e b

theorem den_pos {p : ℕ} (hp : 2≤p) (e) (b) : 0<den p e b := by
  have:0<p-1:=by omega
  cases b <;> simp [den]
  positivity

theorem quotients {p e : ℕ} (hp : p.Prime) :
    let u:ℚ:=(p:ℚ)-1
    let B:ℚ:=(e:ℚ)+1
    let P:ℚ:=(p:ℚ)^e
    let δ : ℚ:=1/(B*u^2*P)
    X p (some e) = xx p e true+δ ∧
    Y p (some e) = yy p e true-u*δ := by
  have p2:=hp.two_le
  have pp : (1:ℚ)<p:=by exact_mod_cast hp.one_lt
  have Bp : (0:ℚ)<(e:ℚ)+1:=by positivity
  have uu : (p-1)*(e+1)≥1:=Nat.mul_pos (by omega) (by omega)
  have uu' : 1≤(e+1)*(p-1):=by simpa [mul_comm] using uu
  have id:=OMA.ComplementaryLocal245212.moments hp e
  have w:((p:ℚ)-1)^2*W (p^e)=p*(((e:ℚ)+1)*(p-1)-1)*(p:ℚ)^e+1 := by exact_mod_cast id.2
  have s:((p:ℚ)-1)*σ 1 (p^e)=p*(p:ℚ)^e-1 := by exact_mod_cast id.1
  have x:=x_factor hp e
  have y:=y_factor hp e
  dsimp [xx,yy,xn,yn,den]
  push_cast [Nat.cast_sub hp.one_le,Nat.cast_sub uu']
  constructor
  · field_simp [sub_ne_zero.mpr pp.ne',Bp.ne',(show (0:ℚ)<p by positivity).ne']
    linear_combination ((p:ℚ)-1)^2*x+w
  · field_simp [sub_ne_zero.mpr pp.ne',Bp.ne',(show (0:ℚ)<p by positivity).ne']
    linear_combination ((p:ℚ)-1)*y+s

theorem bounds {p e m : ℕ} (hp : p.Prime) (pe : 0<e) (mp : 0 < m) (sl : m≤e+1) (b : Bool) :
    1≤X p (some e) ∧ X p (some e)≤2 ∧ 0≤Y p (some e) ∧ Y p (some e)≤2/(m:ℚ) ∧
    1≤xx p e b ∧ xx p e b≤2 ∧ 0≤yy p e b ∧ yy p e b≤2/(m:ℚ) := by
  have pp : (2:ℚ)≤p := by exact_mod_cast hp.two_le
  have ep : (1:ℚ)≤e := by exact_mod_cast pe
  have md : (0:ℚ) < m := by exact_mod_cast mp
  have hl : (m:ℚ)≤(e:ℚ)+1 := by exact_mod_cast sl
  have bpos : (0:ℚ)<(e:ℚ)+1:=by positivity
  have ypos := y_nonneg hp.one_lt (some e)
  have ysm := y_one hp.one_lt (some e)
  have ub : Y p (some e)≤2/(m:ℚ) := (le_div_iff₀ md).mpr <|
    (mul_le_mul_of_nonneg_left hl ypos).trans (OMA.CapOrder245212.y_short hp e).le
  have xb : 1≤X p (some e) := le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr ysm) (by linarith))
  have xb' : X p (some e)≤2 := by
    dsimp [X]
    suffices (1-Y p (some e))/((p:ℚ)-1)≤1 by linarith
    apply (div_le_one₀ (by linarith)).mpr;linarith
  refine ⟨xb,xb',ypos,ub,?_⟩
  cases b with
  | false =>
    have a0 : xx p e false=1 := by simp [xx,xn,den,bpos.ne']
    have b0 : yy p e false=1/((e:ℚ)+1) := by simp [yy,yn,den]
    rw [a0,b0]
    refine ⟨by norm_num,by norm_num,by positivity,(div_le_div_iff₀ bpos md).mpr ?_⟩
    linarith
  | true =>
    have u : (0:ℚ)<(p:ℚ)-1:=by linarith
    have yw : yy p e true=(p:ℚ)/(((e:ℚ)+1)*(p-1)) := by
      dsimp [yy,yn,den];push_cast [Nat.cast_sub hp.one_le];field_simp
    have yw2 : yy p e true≤2/(m:ℚ) := by
      rw [yw,div_le_div_iff₀ (mul_pos bpos u) md]
      nlinarith only [mul_le_mul_of_nonneg_left hl (show (0:ℚ)≤p by positivity),
        mul_nonneg bpos.le (sub_nonneg.mpr pp)]
    have d0 : 0≤1/(((e:ℚ)+1)*((p:ℚ)-1)^2*(p:ℚ)^e) := by positivity
    have one : 1≤xx p e true := by
      dsimp [xx,xn,den]
      push_cast [Nat.cast_sub hp.one_le,Nat.cast_sub (Nat.mul_pos (by omega : 0<e+1) (by have:=hp.two_le;omega : 0<p-1))]
      rw [le_div_iff₀ (mul_pos bpos (sq_pos_of_pos u)),one_mul]
      nlinarith only [mul_nonneg (sub_nonneg.mpr ep) u.le,pp]
    exact ⟨one,(by linarith only [(quotients hp (e:=e)).1,xb',d0]),by rw [yw];positivity,yw2⟩

theorem move {p e f g m k : ℕ} (hp : p.Prime) (pe : 0<e) (mp : 0 < m)
    (ku : 0<k) (gu : 0<g) (fk : k*g≤f) (b : Bool)
    (small : b=true → 4*(p-1)<k*m^2)
    (x x' y y' : ℚ) (x0 : 1≤x) (x1 : 1≤x') (y0 : 0≤y) (y1 : 0≤y')
    (yl : y≤2/(m:ℚ)) (yl' : y'≤2/(m:ℚ)) :
    (f:ℚ)*xx p e b*x*x'+g*yy p e b*y*y' < f*X p (some e)*x*x'+g*Y p (some e)*y*y' := by
  have pp : (1:ℚ)<p:=by exact_mod_cast hp.one_lt
  have fg : (k:ℚ)*g≤f:=by exact_mod_cast fk
  have g0 : (0:ℚ)<g:=by exact_mod_cast gu
  have kp : (0:ℚ)<k:=by exact_mod_cast ku
  have fm : (0:ℚ)<f := lt_of_lt_of_le (mul_pos kp g0) fg
  have xl : (1:ℚ)≤x*x' := one_le_mul_of_one_le_of_one_le x0 x1
  have ylo := mul_nonneg y0 y1
  cases b with
  | false =>
    have ysum : 1/((e:ℚ)+1)≤Y p (some e) := by
      have id:=y_factor hp e
      have big : (p:ℚ)^e ≤ σ 1 (p^e) := by
        exact_mod_cast (show p^e ≤ σ 1 (p^e) by rw [sigma_one_apply_prime_pow hp,Finset.sum_range_succ];omega)
      apply (div_le_iff₀ (by positivity : (0:ℚ)<(e:ℚ)+1)).mpr
      apply le_of_mul_le_mul_right (a:=(p:ℚ)^e) _ (by positivity)
      nlinarith only [id,big]
    have ylt := y_strict hp.one_lt (show 0<e from pe)
    have xstrict : 1<X p (some e) := by
      dsimp [X];apply lt_add_of_pos_right;apply _root_.div_pos _ (by linarith)
      exact sub_pos.mpr (ylt.trans_le (y_one hp.one_lt _))
    have minus : 0<(f:ℚ)*(X p (some e)-1)*(x*x') := by positivity
    have plus := mul_nonneg (mul_nonneg g0.le (sub_nonneg.mpr ysum)) ylo
    have xx0 : xx p e false=1 := by simp [xx,xn,den,show (e:ℚ)+1≠0 by positivity]
    have yy0 : yy p e false=1/((e:ℚ)+1) := by simp [yy,yn,den]
    rw [xx0,yy0]
    nlinarith only [minus,plus]
  | true =>
    let u:ℚ:=(p:ℚ)-1
    let d:ℚ:=1/(((e:ℚ)+1)*u^2*(p:ℚ)^e)
    have dp : 0<d := by dsimp [d,u];positivity
    have us : (0:ℚ)≤u:=by dsimp [u];linarith
    have cap0 := mul_le_mul yl yl' y1 (by positivity)
    have cap : (y*y')*(m:ℚ)^2≤4 := by
      apply (le_div_iff₀ (sq_pos_of_pos (show (0:ℚ) < m by exact_mod_cast mp))).mp
      convert cap0 using 1; ring
    have gate : 4*u < (k:ℚ)*m^2 := by
      have sc : (4:ℚ)*((p-1:ℕ):ℚ)<k*(m:ℚ)^2 := by exact_mod_cast small rfl
      simpa [u,Nat.cast_sub hp.one_le] using sc
    have unc : u*(y*y')<(k:ℚ) := by
      apply lt_of_mul_lt_mul_right (a:=(m:ℚ)^2) _ (by positivity)
      nlinarith only [gate,mul_le_mul_of_nonneg_left cap us]
    have diff : 0<(f:ℚ)*x*x'-g*u*y*y' := by
      nlinarith only [mul_lt_mul_of_pos_left unc g0,mul_le_mul_of_nonneg_left xl fm.le,fg]
    have q:=quotients hp (e:=e)
    change X p (some e)=xx p e true+d ∧ Y p (some e)=yy p e true-u*d at q
    rw [q.1,q.2]
    nlinarith only [mul_pos dp diff]

/-- A rounded factor costs at most 2/p^e; a base omitted to infinity
costs at most 2/p. Both local moments obey the same estimate. -/
theorem error {p e N : ℕ} (hp : p.Prime) (he : 0<e) (hN : 0<N) (b : Bool)
    (space : N ≤ (if b then p^e else p)) :
    |X p (some e)-xx p e b|≤2/(N:ℚ) ∧ |Y p (some e)-yy p e b|≤2/(N:ℚ) := by
  let u:ℚ:=(p:ℚ)-1
  let B:ℚ:=(e:ℚ)+1
  let P:ℚ:=(p:ℚ)^e
  have ulo : 1≤u := by dsimp [u];linarith only [show (2:ℚ)≤p by exact_mod_cast hp.two_le]
  have blo : 1≤B := by dsimp [B];linarith only [Nat.cast_nonneg (α:=ℚ) e]
  have up : 0<u := by linarith
  have bp : 0<B := by linarith
  have pp : 0<P := pow_pos (by exact_mod_cast hp.pos) _
  have np : (0:ℚ)<N := by exact_mod_cast hN
  let d:=1/(B*u^2*P)
  have dp : 0≤d := by dsimp [d];positivity
  have pairs:=quotients hp (e:=e)
  change X p (some e)=xx p e true+d ∧ Y p (some e)=yy p e true-u*d at pairs
  cases b with
  | true =>
    change N≤p^e at space
    have sg : (N:ℚ)≤P:=by dsimp [P];exact_mod_cast space
    have du : u*d=1/(B*u*P) := by dsimp [d];field_simp
    have ud : u*d≤2/(N:ℚ) := by
      rw [du,div_le_div_iff₀ (by positivity) np]
      have big : P≤B*u*P := le_mul_of_one_le_left pp.le (one_le_mul_of_one_le_of_one_le blo ulo)
      linarith
    rw [pairs.1,pairs.2,add_sub_cancel_left,sub_sub_cancel_left,abs_neg,abs_of_nonneg dp,abs_of_nonneg (mul_nonneg up.le dp)]
    exact ⟨(le_mul_of_one_le_left dp ulo).trans ud,ud⟩
  | false =>
    change N≤p at space
    have small : (N:ℚ)≤2*u := by
      have pp : (2:ℚ)≤p:=by exact_mod_cast hp.two_le
      dsimp [u];linarith only [pp,show (N:ℚ)≤p by exact_mod_cast space]
    have frac : 1/u ≤ 2/(N:ℚ):= (div_le_div_iff₀ up np).mpr (by linarith)
    have xr:= (bounds hp he (by decide : 0<1) (by omega) false).1
    have xe : X p (some e)-1≤1/u := by dsimp [X,u];rw [add_sub_cancel_left];gcongr;exact sub_le_self _ (y_nonneg hp.one_lt _)
    have yupper : yy p e true-1/B=1/(B*u) := by
      dsimp [yy,yn,den,u,B];push_cast [Nat.cast_sub hp.one_le];field_simp [show (p:ℚ)-1≠0 from up.ne'];ring
    have lower : 1/B≤Y p (some e) := by
      apply (div_le_iff₀ bp).mpr
      apply le_of_mul_le_mul_right (a:=P) _ pp
      have big : (p:ℚ)^e ≤ σ 1 (p^e) := by
        exact_mod_cast (show p^e ≤ σ 1 (p^e) by rw [sigma_one_apply_prime_pow hp,Finset.sum_range_succ];omega)
      dsimp [B,P];nlinarith only [y_factor hp e,big]
    have pre : Y p (some e)-1/B≤1/(B*u) := by
      nlinarith only [pairs.2,yupper,mul_nonneg up.le dp]
    have s : 1/(B*u) ≤ 1/u := one_div_le_one_div_of_le up (le_mul_of_one_le_left up.le blo)
    have xx0 : xx p e false=1 := by simp [xx,xn,den,show (e:ℚ)+1≠0 by positivity]
    have yy0 : yy p e false=1/B := by simp [yy,yn,den,B]
    rw [xx0,yy0,abs_of_nonneg (sub_nonneg.mpr xr),abs_of_nonneg (sub_nonneg.mpr lower)]
    exact ⟨xe.trans frac,pre.trans (s.trans frac)⟩

end OMA.ThreeMovingLocal245212

end

section

/- Local rounding with one exactly retained prime allowed. -/
namespace OMA.TwoTallLocal245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212 OMA.ThreeMovingLocal245212
open scoped ArithmeticFunction.sigma
open OMA.ThreeMovingLocal245212 (quotients)

def Dn (p e : ℕ) : Option Bool → ℕ
  | none => (e+1)*p^e
  | some b => den p e b
def Nx (p e : ℕ) : Option Bool → ℕ
  | none => W (p^e)
  | some b => xn p e b
def Ny (p e : ℕ) : Option Bool → ℕ
  | none => σ 1 (p^e)
  | some b => yn p e b
def xx' (p e : ℕ) : Option Bool → ℚ
  | none => X p (some e)
  | some b => xx p e b
def yy' (p e : ℕ) : Option Bool → ℚ
  | none => Y p (some e)
  | some b => yy p e b
theorem Dpos {p : ℕ} (hp : p.Prime) (e : ℕ) (mode : Option Bool) : 0<Dn p e mode := by
  cases mode with
  | none =>exact Nat.mul_pos (Nat.succ_pos _) (pow_pos hp.pos _)
  | some b=>exact den_pos hp.two_le e b

theorem moments {p : ℕ} (hp : p.Prime) (e : ℕ) (mode : Option Bool) :
    xx' p e mode*(Dn p e mode:ℕ)=Nx p e mode ∧ yy' p e mode*(Dn p e mode:ℕ)=Ny p e mode := by
  cases mode with
  | none =>simpa [xx',yy',Dn,Nx,Ny,mul_assoc] using And.intro (x_factor hp e) (y_factor hp e)
  | some b=>
    have dp : (den p e b:ℚ)≠0:=by exact_mod_cast (den_pos hp.two_le e b).ne'
    simp [xx',yy',Dn,Nx,Ny,xx,yy,div_mul_cancel₀ _ dp]

theorem ranges {p e : ℕ} (hp : p.Prime) (pe : 0<e) (mode : Option Bool) :
    1≤xx' p e mode ∧ xx' p e mode≤2 ∧ 0≤yy' p e mode ∧ yy' p e mode≤2/((e:ℚ)+1) := by
  have a (b : Bool):=bounds hp pe (Nat.succ_pos e) (le_refl (e+1)) b
  cases mode with
  | none =>simpa [xx',yy'] using And.intro (a false).1 (And.intro (a false).2.1
      (And.intro (a false).2.2.1 (a false).2.2.2.1))
  | some b=>simpa [xx',yy'] using (a b).2.2.2.2

theorem move {p e f g m k : ℕ} (hp : p.Prime) (pe : 0<e) (mp : 0 < m)
    (ku : 0<k) (gu : 0<g) (fk : k*g≤f) (b : Bool)
    (small : b=true → 4*(p-1)<k*m)
    (x x' y y' : ℚ) (x0 : 1≤x) (x1 : 1≤x') (y0 : 0≤y) (y1 : 0≤y')
    (cap : (y*y')*(m:ℚ)≤4) :
    (f:ℚ)*xx p e b*x*x'+g*yy p e b*y*y' < f*X p (some e)*x*x'+g*Y p (some e)*y*y' := by
  have pp : (1:ℚ)<p:=by exact_mod_cast hp.one_lt
  have fg : (k:ℚ)*g≤f:=by exact_mod_cast fk
  have g0 : (0:ℚ)<g:=by exact_mod_cast gu
  have kp : (0:ℚ)<k:=by exact_mod_cast ku
  have fm : (0:ℚ)<f := lt_of_lt_of_le (mul_pos kp g0) fg
  have xl : (1:ℚ)≤x*x' := one_le_mul_of_one_le_of_one_le x0 x1
  have ylo := mul_nonneg y0 y1
  cases b with
  | false =>
    have ysum : 1/((e:ℚ)+1)≤Y p (some e) := by
      have id:=y_factor hp e
      have big : (p:ℚ)^e ≤ σ 1 (p^e) := by
        exact_mod_cast (show p^e ≤ σ 1 (p^e) by rw [sigma_one_apply_prime_pow hp,Finset.sum_range_succ];omega)
      apply (div_le_iff₀ (by positivity : (0:ℚ)<(e:ℚ)+1)).mpr
      apply le_of_mul_le_mul_right (a:=(p:ℚ)^e) _ (by positivity)
      nlinarith only [id,big]
    have ylt := y_strict hp.one_lt (show 0<e from pe)
    have xstrict : 1<X p (some e) := by
      dsimp [X];apply lt_add_of_pos_right;apply _root_.div_pos _ (by linarith)
      exact sub_pos.mpr (ylt.trans_le (y_one hp.one_lt _))
    have minus : 0<(f:ℚ)*(X p (some e)-1)*(x*x') := by positivity
    have plus := mul_nonneg (mul_nonneg g0.le (sub_nonneg.mpr ysum)) ylo
    have xx0 : xx p e false=1 := by simp [xx,xn,den,show (e:ℚ)+1≠0 by positivity]
    have yy0 : yy p e false=1/((e:ℚ)+1) := by simp [yy,yn,den]
    rw [xx0,yy0]
    nlinarith only [minus,plus]
  | true =>
    let u:ℚ:=(p:ℚ)-1
    let d:ℚ:=1/(((e:ℚ)+1)*u^2*(p:ℚ)^e)
    have dp : 0<d := by dsimp [d,u];positivity
    have us : (0:ℚ)≤u:=by dsimp [u];linarith
    have gate : 4*u < (k:ℚ)*m := by
      have sc : (4:ℚ)*((p-1:ℕ):ℚ)<k*(m:ℚ) := by exact_mod_cast small rfl
      simpa [u,Nat.cast_sub hp.one_le] using sc
    have unc : u*(y*y')<(k:ℚ) := by
      apply lt_of_mul_lt_mul_right (a:=(m:ℚ)) _ (by positivity)
      nlinarith only [gate,mul_le_mul_of_nonneg_left cap us]
    have diff : 0<(f:ℚ)*x*x'-g*u*y*y' := by
      nlinarith only [mul_lt_mul_of_pos_left unc g0,mul_le_mul_of_nonneg_left xl fm.le,fg]
    have q:=OMA.ThreeMovingLocal245212.quotients hp (e:=e)
    change X p (some e)=xx p e true+d ∧ Y p (some e)=yy p e true-u*d at q
    rw [q.1,q.2]
    nlinarith only [mul_pos dp diff]

end OMA.TwoTallLocal245212

end

section

/- Cleared moments and the restriction on every retained prime. -/
namespace OMA.FixedRankGap245212
open Nat Finset OMA.Smooth245212 OMA.TwoTallLocal245212

structure Family (r : ℕ) where
  p : Fin r→ℕ
  e : Fin r→ℕ
  k : ℕ
  L : ℕ
  prime : ∀i,(p i).Prime
  positive : ∀i,0<e i
  kp : 8≤k
  longest : ∃i,e i+1=L
  cap : ∀i,e i+1≤L
  inj : p.Injective

variable {r : ℕ}

def exactX (c : Family r) (i : Fin r) := X (c.p i) (some (c.e i))
def exactY (c : Family r) (i : Fin r) := Y (c.p i) (some (c.e i))
def x' (c : Family r) (b : Fin r→Option Bool) (i : Fin r) := xx' (c.p i) (c.e i) (b i)
def y' (c : Family r) (b : Fin r→Option Bool) (i : Fin r) := yy' (c.p i) (c.e i) (b i)
def dust (c : Family r) (b : Fin r→Option Bool) := ∏i,Dn (c.p i) (c.e i) (b i)
def NX (c : Family r) (b : Fin r→Option Bool) := ∏i,Nx (c.p i) (c.e i) (b i)
def NY (c : Family r) (b : Fin r→Option Bool) := ∏i,Ny (c.p i) (c.e i) (b i)
def score (f g : ℕ) (x y : Fin r→ℚ) := (f:ℚ)*(∏i,x i)+(g:ℚ)*(∏i,y i)

theorem dust_pos (c : Family r) (b : Fin r→Option Bool) : 0<dust c b :=
  prod_pos (fun i _=>Dpos (c.prime i) _ _)

theorem clear (c : Family r) (b : Fin r→Option Bool) (f g : ℕ) :
    score f g (x' c b) (y' c b)*dust c b=(f*NX c b+g*NY c b:ℕ) := by
  have w : (∏i,x' c b i)*(dust c b:ℚ)=NX c b := by
    dsimp [dust,NX,x'];push_cast;rw [←prod_mul_distrib]
    exact prod_congr rfl (fun i _=>(moments (c.prime i) (c.e i) (b i)).1)
  have s : (∏i,y' c b i)*(dust c b:ℚ)=NY c b := by
    dsimp [dust,NY,y'];push_cast;rw [←prod_mul_distrib]
    exact prod_congr rfl (fun i _=>(moments (c.prime i) (c.e i) (b i)).2)
  dsimp [score];push_cast
  linear_combination (f:ℚ)*w+(g:ℚ)*s


private theorem largest {c : Family r} {b : Fin r→Option Bool} {f g l : ℕ} (frac : f+g=(c.k+1)*l)
    (unit : ∀i,¬c.p i∣l) (hit : (f+g)*dust c b=f*NX c b+g*NY c b) :
    ∀i,b i=some true → c.p i≤ max (c.k+1) c.L := by
  classical
  let s:=univ.filter (fun j=>b j=some true)
  intro i hi
  have im : i∈s:=mem_filter.mpr ⟨mem_univ _,hi⟩
  obtain ⟨j,jm,top⟩:=s.exists_max_image c.p ⟨i,im⟩
  have sh: b j=some true := (mem_filter.mp jm).2
  let q:=c.p j
  have pr:=c.prime j
  have dn : q∣NX c b := by
    apply dvd_trans (b:=Nx (c.p j) (c.e j) (b j)) _ (dvd_prod_of_mem (fun i=>Nx (c.p i) (c.e i) (b i)) (mem_univ j))
    simp [Nx,OMA.ThreeMovingLocal245212.xn,sh,q]
  have ds : q∣NY c b := by
    apply dvd_trans (b:=Ny (c.p j) (c.e j) (b j)) _ (dvd_prod_of_mem (fun i=>Ny (c.p i) (c.e i) (b i)) (mem_univ j))
    simp [Ny,OMA.ThreeMovingLocal245212.yn,sh,q]
  have total : q∣(f+g)*dust c b := hit ▸ dvd_add (dvd_mul_of_dvd_right dn f) (dvd_mul_of_dvd_right ds g)
  apply (top _ im).trans
  by_contra! no
  change max (c.k+1) c.L < q at no
  rw [frac] at total
  rcases pr.dvd_mul.mp total with h|h
  · rcases pr.dvd_mul.mp h with small|bad
    · exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) small
    · exact unit j bad
  · obtain ⟨i',_,v⟩:=(pr.prime.dvd_finsetProd_iff _).mp h
    have le0:=c.cap i'
    have absent := Nat.not_dvd_of_pos_of_lt (by omega : 0<c.e i'+1) (by omega : c.e i'+1<q)
    change q∣Dn (c.p i') (c.e i') (b i') at v
    cases which : b i' with
    | none =>
      rw [which] at v
      rcases pr.dvd_mul.mp v with hit|hit
      · exact absent hit
      have same:=c.inj ((prime_dvd_prime_iff_eq pr (c.prime i')).mp (pr.dvd_of_dvd_pow hit))
      exact (by rw [←same,sh] at which; contradiction)
    | some bit =>
      cases bit with
      | false => rw [which] at v;exact absent v
      | true =>
        have mt : i'∈s:=mem_filter.mpr ⟨mem_univ _,which⟩
        have sz:=top i' mt
        rw [which] at v
        rcases pr.dvd_mul.mp v with bad|bad
        · exact absent bad
        · exact Nat.not_dvd_of_pos_of_lt (by have:=(c.prime i').two_le;omega : 0<c.p i'-1)
            (by omega) (pr.dvd_of_dvd_pow bad)


theorem retained {c : Family r} {b : Fin r→Option Bool} {f g l : ℕ} (frac : f+g=(c.k+1)*l)
    (unit : ∀i,¬c.p i∣l) (hit : (f+g)*dust c b=f*NX c b+g*NY c b) :
    ∀i,b i=some true → c.p i≤ max (c.k+1) c.L := largest frac unit hit

end OMA.FixedRankGap245212

end

section

/- Cleared moments and the restriction on every retained prime. -/
namespace OMA.SingleMovingGap245212
open Nat Finset OMA.Smooth245212 OMA.TwoTallLocal245212

structure Family where
  p : Fin 3→ℕ
  e : Fin 3→ℕ
  k : ℕ
  L : ℕ
  prime : ∀i,(p i).Prime
  positive : ∀i,0<e i
  kp : 8≤k
  longest : ∃i,e i+1=L
  cap : ∀i,e i+1≤L
  inj : p.Injective

def exactX (c : Family) (i : Fin 3) := X (c.p i) (some (c.e i))
def exactY (c : Family) (i : Fin 3) := Y (c.p i) (some (c.e i))
def x' (c : Family) (b : Fin 3→Option Bool) (i : Fin 3) := xx' (c.p i) (c.e i) (b i)
def y' (c : Family) (b : Fin 3→Option Bool) (i : Fin 3) := yy' (c.p i) (c.e i) (b i)
def dust (c : Family) (b : Fin 3→Option Bool) := ∏i,Dn (c.p i) (c.e i) (b i)
def NX (c : Family) (b : Fin 3→Option Bool) := ∏i,Nx (c.p i) (c.e i) (b i)
def NY (c : Family) (b : Fin 3→Option Bool) := ∏i,Ny (c.p i) (c.e i) (b i)
def score (f g : ℕ) (x y : Fin 3→ℚ) := (f:ℚ)*(∏i,x i)+(g:ℚ)*(∏i,y i)

theorem dust_pos (c : Family) (b : Fin 3→Option Bool) : 0<dust c b :=
  prod_pos (fun i _=>Dpos (c.prime i) _ _)

theorem clear (c : Family) (b : Fin 3→Option Bool) (f g : ℕ) :
    score f g (x' c b) (y' c b)*dust c b=(f*NX c b+g*NY c b:ℕ) := by
  have w : (∏i,x' c b i)*(dust c b:ℚ)=NX c b := by
    dsimp [dust,NX,x'];push_cast;rw [←prod_mul_distrib]
    exact prod_congr rfl (fun i _=>(moments (c.prime i) (c.e i) (b i)).1)
  have s : (∏i,y' c b i)*(dust c b:ℚ)=NY c b := by
    dsimp [dust,NY,y'];push_cast;rw [←prod_mul_distrib]
    exact prod_congr rfl (fun i _=>(moments (c.prime i) (c.e i) (b i)).2)
  dsimp [score];push_cast
  linear_combination (f:ℚ)*w+(g:ℚ)*s


private theorem largest {c : Family} {b : Fin 3→Option Bool} {f g l : ℕ} (frac : f+g=(c.k+1)*l)
    (unit : ∀i,¬c.p i∣l) (hit : (f+g)*dust c b=f*NX c b+g*NY c b) :
    ∀i,b i=some true → c.p i≤ max (c.k+1) c.L := by
  classical
  let s:=univ.filter (fun j=>b j=some true)
  intro i hi
  have im : i∈s:=mem_filter.mpr ⟨mem_univ _,hi⟩
  obtain ⟨j,jm,top⟩:=s.exists_max_image c.p ⟨i,im⟩
  have sh: b j=some true := (mem_filter.mp jm).2
  let q:=c.p j
  have pr:=c.prime j
  have dn : q∣NX c b := by
    apply dvd_trans (b:=Nx (c.p j) (c.e j) (b j)) _ (dvd_prod_of_mem (fun i=>Nx (c.p i) (c.e i) (b i)) (mem_univ j))
    simp [Nx,OMA.ThreeMovingLocal245212.xn,sh,q]
  have ds : q∣NY c b := by
    apply dvd_trans (b:=Ny (c.p j) (c.e j) (b j)) _ (dvd_prod_of_mem (fun i=>Ny (c.p i) (c.e i) (b i)) (mem_univ j))
    simp [Ny,OMA.ThreeMovingLocal245212.yn,sh,q]
  have total : q∣(f+g)*dust c b := hit ▸ dvd_add (dvd_mul_of_dvd_right dn f) (dvd_mul_of_dvd_right ds g)
  apply (top _ im).trans
  by_contra! no
  change max (c.k+1) c.L < q at no
  rw [frac] at total
  rcases pr.dvd_mul.mp total with h|h
  · rcases pr.dvd_mul.mp h with small|bad
    · exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) small
    · exact unit j bad
  · obtain ⟨i',_,v⟩:=(pr.prime.dvd_finsetProd_iff _).mp h
    have le0:=c.cap i'
    have absent := Nat.not_dvd_of_pos_of_lt (by omega : 0<c.e i'+1) (by omega : c.e i'+1<q)
    change q∣Dn (c.p i') (c.e i') (b i') at v
    cases which : b i' with
    | none =>
      rw [which] at v
      rcases pr.dvd_mul.mp v with hit|hit
      · exact absent hit
      have same:=c.inj ((prime_dvd_prime_iff_eq pr (c.prime i')).mp (pr.dvd_of_dvd_pow hit))
      exact (by rw [←same,sh] at which; contradiction)
    | some bit =>
      cases bit with
      | false => rw [which] at v;exact absent v
      | true =>
        have mt : i'∈s:=mem_filter.mpr ⟨mem_univ _,which⟩
        have sz:=top i' mt
        rw [which] at v
        rcases pr.dvd_mul.mp v with bad|bad
        · exact absent bad
        · exact Nat.not_dvd_of_pos_of_lt (by have:=(c.prime i').two_le;omega : 0<c.p i'-1)
            (by omega) (pr.dvd_of_dvd_pow bad)


theorem retained {c : Family} {b : Fin 3→Option Bool} {f g l : ℕ} (frac : f+g=(c.k+1)*l)
    (unit : ∀i,¬c.p i∣l) (hit : (f+g)*dust c b=f*NX c b+g*NY c b) :
    ∀i,b i=some true → c.p i≤ max (c.k+1) c.L := largest frac unit hit

end OMA.SingleMovingGap245212

end

section

/- Every prefix of three signed, rounded local moments is separated if
its shortest length squared dominates its longest length relative to k. -/
namespace OMA.ThreeMovingGap245212
open Nat Finset OMA.Smooth245212 OMA.ThreeMovingLocal245212

structure Family where
  p : Fin 3→ℕ
  e : Fin 3→ℕ
  k : ℕ
  m : ℕ
  L : ℕ
  prime : ∀i,(p i).Prime
  positive : ∀i,0<e i
  kp : 0<k
  mp : 0 < m
  lengths : ∀i,m≤e i+1 ∧ e i+1≤L
  comparable : 4*max k L < k*m^2

def exactX (c : Family) (i : Fin 3) := X (c.p i) (some (c.e i))
def exactY (c : Family) (i : Fin 3) := Y (c.p i) (some (c.e i))
def x' (c : Family) (b : Fin 3→Bool) (i : Fin 3) := xx (c.p i) (c.e i) (b i)
def y' (c : Family) (b : Fin 3→Bool) (i : Fin 3) := yy (c.p i) (c.e i) (b i)
def dust (c : Family) (b : Fin 3→Bool) := ∏i,den (c.p i) (c.e i) (b i)
def NX (c : Family) (b : Fin 3→Bool) := ∏i,xn (c.p i) (c.e i) (b i)
def NY (c : Family) (b : Fin 3→Bool) := ∏i,yn (c.p i) (c.e i) (b i)
def score (f g : ℕ) (x y : Fin 3→ℚ) := (f:ℚ)*(∏i,x i)+(g:ℚ)*(∏i,y i)

theorem dust_pos (c : Family) (b : Fin 3→Bool) : 0<dust c b :=
  prod_pos (fun i _=>den_pos (c.prime i).two_le _ _)

theorem clear (c : Family) (b : Fin 3→Bool) (f g : ℕ) :
    score f g (x' c b) (y' c b)*dust c b=(f*NX c b+g*NY c b:ℕ) := by
  have w : (∏i,x' c b i)*(dust c b:ℚ)=NX c b := by
    dsimp [dust,NX,x',xx];push_cast;rw [←prod_mul_distrib]
    apply prod_congr rfl;intro i _
    exact div_mul_cancel₀ _ (by exact_mod_cast (den_pos (c.prime i).two_le (c.e i) (b i)).ne')
  have s : (∏i,y' c b i)*(dust c b:ℚ)=NY c b := by
    dsimp [dust,NY,y',yy];push_cast;rw [←prod_mul_distrib]
    apply prod_congr rfl;intro i _
    exact div_mul_cancel₀ _ (by exact_mod_cast (den_pos (c.prime i).two_le (c.e i) (b i)).ne')
  dsimp [score];push_cast
  linear_combination (f:ℚ)*w+(g:ℚ)*s

private theorem descend (c : Family) (b : Fin 3→Bool) (f g : ℕ) (gp : 0<g) (fg : c.k*g≤f)
    (small : ∀i,b i=true → c.p i≤ max (c.k+1) c.L) :
    score f g (x' c b) (y' c b)<score f g (exactX c) (exactY c) := by
  let mix (s : Finset (Fin 3)) (i : Fin 3) := if i∈s then exactX c i else x' c b i
  let miy (s : Finset (Fin 3)) (i : Fin 3) := if i∈s then exactY c i else y' c b i
  have adv (s : Finset (Fin 3)) {i} (fresh : i∉s) :
      score f g (mix s) (miy s)<score f g (mix (insert i s)) (miy (insert i s)) := by
    let all j:=bounds (c.prime j) (c.positive j) c.mp (c.lengths j).1 (b j)
    have xpos s j : 1≤ mix s j := by
      dsimp [mix];split <;> first | exact (all j).1 | exact (all j).2.2.2.2.1
    have ylo s j : 0≤ miy s j := by
      dsimp [miy];split <;> first | exact (all j).2.2.1 | exact (all j).2.2.2.2.2.2.1
    have yhi s j : miy s j≤2/(c.m:ℚ) := by
      dsimp [miy];split <;> first | exact (all j).2.2.2.1 | exact (all j).2.2.2.2.2.2.2
    have single {j l : Fin 3} (n : j≠i) (n' : l≠i) :
        (f:ℚ)*mix s i*mix s j*mix s l+g*miy s i*miy s j*miy s l <
        f*mix (insert i s) i*mix (insert i s) j*mix (insert i s) l+
          g*miy (insert i s) i*miy (insert i s) j*miy (insert i s) l := by
      have size (inb : b i=true) : 4*(c.p i-1)<c.k*c.m^2 := by
        have lim:=small i inb
        have before : c.p i-1≤ max c.k c.L := by omega
        exact (Nat.mul_le_mul_left _ before).trans_lt c.comparable
      have step:=move (c.prime i) (c.positive i) c.mp c.kp gp fg (b i) size
        (mix s j) (mix s l) (miy s j) (miy s l) (xpos s j) (xpos s l) (ylo s j) (ylo s l) (yhi s j) (yhi s l)
      simpa [mix,miy,exactX,exactY,x',y',fresh,n,n'] using step
    dsimp [score]
    simp only [Fin.prod_univ_three]
    have choice : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases choice with rfl|rfl|rfl
    · simpa only [mul_comm,mul_left_comm,mul_assoc] using single (j:=1) (l:=2) (by decide) (by decide)
    · simpa only [mul_comm,mul_left_comm,mul_assoc] using single (j:=0) (l:=2) (by decide) (by decide)
    · simpa only [mul_comm,mul_left_comm,mul_assoc] using single (j:=0) (l:=1) (by decide) (by decide)
  have a:=adv ∅ (i:=0) (by decide)
  have b1:=adv {0} (i:=1) (by decide)
  have d:=adv {1,0} (i:=2) (by decide)
  have endset : insert (2:Fin 3) ({1,0}:Finset (Fin 3))=univ := by decide
  simpa [mix,miy,endset] using (a.trans b1).trans d

private theorem largest {c : Family} {b : Fin 3→Bool} {f g l : ℕ} (frac : f+g=(c.k+1)*l)
    (unit : ∀i,¬c.p i∣l) (hit : (f+g)*dust c b=f*NX c b+g*NY c b) :
    ∀i,b i=true → c.p i≤ max (c.k+1) c.L := by
  classical
  let s:=univ.filter (fun j=>b j=true)
  intro i hi
  have im : i∈s:=mem_filter.mpr ⟨mem_univ _,hi⟩
  obtain ⟨j,jm,top⟩:=s.exists_max_image c.p ⟨i,im⟩
  have sh: b j=true := (mem_filter.mp jm).2
  let q:=c.p j
  have pr:=c.prime j
  have dn : q∣NX c b := by
    apply dvd_trans (b:=xn (c.p j) (c.e j) (b j)) _ (dvd_prod_of_mem (fun i=>xn (c.p i) (c.e i) (b i)) (mem_univ j))
    simp [xn,sh,q]
  have ds : q∣NY c b := by
    apply dvd_trans (b:=yn (c.p j) (c.e j) (b j)) _ (dvd_prod_of_mem (fun i=>yn (c.p i) (c.e i) (b i)) (mem_univ j))
    simp [yn,sh,q]
  have total : q∣(f+g)*dust c b := hit ▸ dvd_add (dvd_mul_of_dvd_right dn f) (dvd_mul_of_dvd_right ds g)
  apply (top _ im).trans
  by_contra! no
  change max (c.k+1) c.L < q at no
  rw [frac] at total
  rcases pr.dvd_mul.mp total with h|h
  · rcases pr.dvd_mul.mp h with small|bad
    · exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) small
    · exact unit j bad
  · obtain ⟨i',_,v⟩:=(pr.prime.dvd_finsetProd_iff _).mp h
    have le0:= (c.lengths i').2
    have absent := Nat.not_dvd_of_pos_of_lt (by omega : 0<c.e i'+1) (by omega : c.e i'+1<q)
    dsimp [den] at v
    split at v
    next on =>
      have mt : i'∈s:=mem_filter.mpr ⟨mem_univ _,on⟩
      have sz:=top i' mt
      rcases pr.dvd_mul.mp v with bad|bad
      · exact absent bad
      · exact Nat.not_dvd_of_pos_of_lt (by have:=(c.prime i').two_le;omega : 0<c.p i'-1)
          (by omega) (pr.dvd_of_dvd_pow bad)
    next off => exact absent v

theorem nonzero (c : Family) (b : Fin 3→Bool) (f g l : ℕ) (gp : 0<g) (fg : c.k*g≤f)
    (frac : f+g=(c.k+1)*l) (unit : ∀i,¬c.p i∣l)
    (actual : score f g (exactX c) (exactY c)≤(f+g:ℕ)) :
    (f+g)*dust c b ≠ f*NX c b+g*NY c b := by
  intro hit
  have less:=(descend c b f g gp fg (largest frac unit hit)).trans_le actual
  have val:=clear c b f g
  have id : ((f+g:ℕ):ℚ)*dust c b=((f*NX c b+g*NY c b:ℕ):ℚ) := by exact_mod_cast hit
  exact (ne_of_lt (mul_lt_mul_of_pos_right less (show (0:ℚ)<dust c b by exact_mod_cast dust_pos c b))) (val.trans id.symm)

end OMA.ThreeMovingGap245212

end

section

/- Integer size comparisons for the general complementary-exponent bound. -/
namespace OMA.ComplementarySize245212

/-- An elementary integer substitute for d log b ≤ b/2 when
b≥16(d+1)². -/
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

/-- Common last step, using the integer-only growth estimate above. -/
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

/- Integer growth estimates and an empty multiplicative interval for three bases. -/
namespace OMA.ThreeMovingScalar245212

def cut (x j : ℕ) := x^(16^j)

theorem cut_succ (x i : ℕ) : cut x (i+1)=(cut x i)^16 := by
  rw [cut,cut,pow_succ,pow_mul]

theorem cut_mono {x : ℕ} (pos : 1≤x) : Monotone (cut x) :=
  fun _ _ le=>Nat.pow_le_pow_right pos (Nat.pow_le_pow_right (by decide) le)

theorem empty_interval (x : ℕ) (hx : 1≤x) (p : Fin 3→ℕ) :
    ∃j : Fin 4,∀i, p i ≤ cut x j.val ∨ cut x (j.val+1) < p i := by
  by_contra! no
  choose f above below using no
  have inj:Function.Injective f := by
    intro j k eqn
    rcases lt_trichotomy j k with lt|eq|gt
    · have h := cut_mono hx (show j.val+1≤k.val from lt)
      have impossible:=(below j).trans h
      rw [eqn] at impossible
      exact False.elim ((above k).not_ge impossible)
    · exact eq
    · have h := cut_mono hx (show k.val+1≤j.val from gt)
      have impossible:=(below k).trans h
      rw [←eqn] at impossible
      exact False.elim ((above j).not_ge impossible)
  have:=Fintype.card_le_of_injective _ inj
  norm_num at this

def budget := 16^4

def base (k L : ℕ) := 128*(k+2)*(L+1)

-- The larger exponent covers substitution of the exact dyadic numerator.
def degree := (budget+4)*budget

def minimumCut := 64*(degree+1)^2

private theorem square_product (p m F : ℕ) : ((p^14*m^2)^F)^2=p^(28*F)*m^(4*F) := by
  rw [←pow_mul,mul_pow,←pow_mul,←pow_mul,show 14*(F*2)=28*F by ring,show 2*(F*2)=4*F by ring]

theorem scale {m k L p e : ℕ} (hp : 3≤p) (hk : k<2*p) (hm : minimumCut ≤ m)
    (comparable : L ≤ k*m^2) (low : m≤e+1) :
    (base k L)^degree ≤ p^e := by
  let F:=degree
  have fp : 1≤F := by decide
  change 64*(F+1)^2≤ m at hm
  have mp : 1≤ m:=by nlinarith only [hm,Nat.zero_le (F^2),Nat.zero_le F]
  have pp : 1≤p:=by omega
  have kcap : k+2≤4*p := by omega
  have Lcap : L+1≤3*p*m^2 := by
    have mpos:=Nat.mul_pos (show 0<p by omega) (pow_pos mp 2)
    nlinarith only [comparable,Nat.mul_le_mul_right (m^2) hk.le,mpos]
  have scale : base k L≤p^14*m^2 := by
    have sixteen : 1536≤p^12 := (by decide : 1536≤3^12).trans (Nat.pow_le_pow_left hp _)
    have b:=Nat.mul_le_mul kcap Lcap
    dsimp [base]
    nlinarith only [Nat.mul_le_mul_left 128 b,Nat.mul_le_mul_right (p^2*m^2) sixteen]
  have grow := OMA.ComplementarySize245212.absorb (d:=2*F) (b:=m) (by nlinarith only [hm,Nat.zero_le F])
  have poly : m^(4*F)≤p^m := (by convert grow using 1; ring : m^(4*F)≤2^m).trans (Nat.pow_le_pow_left (by omega) _)
  have gain : 28*F+m≤2*e := by
    nlinarith only [hm,low,Nat.zero_le (F^2)]
  apply (pow_le_pow_iff_left₀ (show 0≤(base k L)^degree from Nat.zero_le _) (Nat.zero_le _) (by decide : 2≠0)).mp
  change ((base k L)^F)^2≤(p^e)^2
  calc
    _ ≤ ((p^14*m^2)^F)^2 := Nat.pow_le_pow_left (Nat.pow_le_pow_left scale _) _
    _ = p^(28*F)*m^(4*F) := square_product p m F
    _ ≤ p^(28*F)*p^m := Nat.mul_le_mul_left _ poly
    _ = p^(28*F+m) := (pow_add ..).symm
    _ ≤ p^(2*e) := Nat.pow_le_pow_right pp gain
    _ = (p^e)^2 := by rw [mul_comm,pow_mul]

end OMA.ThreeMovingScalar245212

end

section

/- An explicit uniform distance from a rational target to Euler products
of bounded length, provided none of their subproducts hits the target. -/
namespace OMA.CofactorEulerSeparation245212
open Finset Nat

def num (s : Finset ℕ) := ∏p∈s,p
def den (s : Finset ℕ) := ∏p∈s,(p-1)
def gap (A H : ℕ) (s : Finset ℕ) := ((A:ℤ)*num s-(H:ℤ)*den s).natAbs
def miss (A H : ℕ) (s : Finset ℕ) := ∀t⊆s,A*num t≠H*den t

def budget (A : ℕ) : ℕ→ℕ
  | 0=>1
  | r+1=>let b:=budget A r;max (2*b) ((2+2*A*2^r*b)^(r+1))

private theorem budget_pos (A r : ℕ) : 0<budget A r := by
  induction r with
  | zero=>simp [budget]
  | succ r ih=>exact (Nat.mul_pos (by decide) ih).trans_le (le_max_left _ _)

private theorem gap_pos {A H : ℕ} {s : Finset ℕ} (m : A*num s≠H*den s) : 0<gap A H s := by
  apply Int.natAbs_pos.mpr
  intro z
  exact m (by exact_mod_cast sub_eq_zero.mp z)

private theorem size {s : Finset ℕ} (positive : ∀p∈s,2≤p) : num s≤2^s.card*den s := by
  calc
    num s ≤ ∏p∈s,(2*(p-1)) := by
      apply prod_le_prod'
      intro p mem;have:=positive p mem;omega
    _ = _ := by simp [den,prod_mul_distrib]

private theorem spread {u x z : ℤ} (u0 : 0≤u) (x0 : 0≤x) (large : 2*x≤u*|z|) :
    u*|z|≤2*|u*z+x| := by
  have tri:=abs_add_le (u*z+x) (-x)
  rw [add_neg_cancel_right,abs_mul,abs_of_nonneg u0,abs_neg,abs_of_nonneg x0] at tri
  linarith

theorem separated (A H K : ℕ) (s : Finset ℕ) (card : s.card≤K)
    (positive : ∀p∈s,2≤p) (apart : miss A H s) : den s≤budget A K*gap A H s := by
  classical
  induction K generalizing s with
  | zero=>
    have empty : s=∅:=card_eq_zero.mp (by omega)
    subst s
    simpa [den,budget] using Nat.succ_le_of_lt (gap_pos (apart ∅ (by simp)))
  | succ K ih=>
    by_cases empty : s=∅
    · subst s
      simpa [den] using Nat.succ_le_of_lt (Nat.mul_pos (budget_pos A (K+1)) (gap_pos (apart ∅ (by simp))))
    have nonempty:=nonempty_iff_ne_empty.mpr empty
    let q:=s.max' nonempty
    have mem : q∈s:=s.max'_mem _
    have qp:=positive q mem
    let t:=s.erase q
    have sub : t⊆s:=erase_subset _ _
    have oldBound:=ih t (by dsimp [t];rw [card_erase_of_mem mem];omega)
      (fun p hp=>positive p (sub hp)) (fun z hz=>apart z (hz.trans sub))
    have scale:=size (s:=t) (fun p hp=>positive p (sub hp))
    have tc : t.card≤K := by dsimp [t];rw [card_erase_of_mem mem];omega
    let B:=budget A K
    have U : num s=q*num t := (mul_prod_erase s (fun p=>p) mem).symm
    have V : den s=(q-1)*den t := (mul_prod_erase s (fun p=>p-1) mem).symm
    by_cases large : 2*A*2^K*B≤q-1
    · have twice : 2*A*num t≤(q-1)*gap A H t := by
        calc
          _ ≤ 2*A*(2^K*(B*gap A H t)) := Nat.mul_le_mul_left _ (scale.trans
            (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) tc) oldBound))
          _ = (2*A*2^K*B)*gap A H t := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ large
      have twiceInt : 2*((A:ℤ)*num t)≤((q-1:ℕ):ℤ)*|(A:ℤ)*num t-(H:ℤ)*den t| := by
        have cast:=Int.ofNat_le.mpr twice
        simpa only [gap,Nat.cast_mul,Nat.cast_ofNat,Int.natCast_natAbs,mul_assoc] using cast
      have pre:=spread (u:=((q-1:ℕ):ℤ)) (x:=(A:ℤ)*num t) (z:=(A:ℤ)*num t-(H:ℤ)*den t)
        (by positivity) (by positivity) twiceInt
      have id : ((q-1:ℕ):ℤ)*((A:ℤ)*num t-(H:ℤ)*den t)+A*num t=(A:ℤ)*num s-(H:ℤ)*den s := by
        rw [U,V];push_cast [Nat.cast_sub (show 1≤q by omega)];ring
      rw [id] at pre
      have control : (q-1)*gap A H t≤2*gap A H s := by
        apply Int.ofNat_le.mp
        simpa [gap,Int.natCast_natAbs] using pre
      calc
        den s ≤ (q-1)*(B*gap A H t) := V ▸ Nat.mul_le_mul_left _ oldBound
        _ = B*((q-1)*gap A H t) := by ring
        _ ≤ B*(2*gap A H s) := Nat.mul_le_mul_left _ control
        _ = (2*B)*gap A H s := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (le_max_left _ _)
    · let J:=2+2*A*2^K*B
      have lo : 0<J := by dsimp [J];omega
      have modest : den s≤J^(K+1) := by
        refine (prod_le_pow_card s (fun p=>p-1) J ?_).trans (Nat.pow_le_pow_right lo card)
        intro p hp
        have below : p≤q:=s.le_max' p hp
        dsimp [J];omega
      have nonzero := gap_pos (apart s (Subset.rfl))
      exact modest.trans ((le_max_right _ _).trans (Nat.le_mul_of_pos_right _ nonzero))


theorem miss_odd {A H : ℕ} {s : Finset ℕ} (oa : Odd A) (eh : Even H)
    (pr : ∀p∈s,Odd p) : miss A H s := by
  intro t ht eqn
  have all (u : Finset ℕ) (ho : ∀p∈u,Odd p) : Odd (num u) := by
    induction u using Finset.induction_on with
    | empty=>simp [num]
    | @insert p u fresh ih=>
      rw [num,prod_insert fresh]
      exact (ho p (mem_insert_self ..)).mul (ih (fun q hq=>ho q (mem_insert_of_mem hq)))
  have left:=oa.mul (all t (fun p hp=>pr p (ht hp)))
  rw [eqn] at left
  exact (Nat.not_even_iff_odd.mpr left) (eh.mul_right _)

theorem miss_avoids {A H : ℕ} {s : Finset ℕ} (different : A≠H)
    (pr : ∀p∈s,p.Prime) (avoid : ∀p∈s,¬p∣H) : miss A H s := by
  intro t ht eqn
  by_cases empty : t=∅
  · exact different (by simpa [empty,num,den] using eqn)
  have nonempty:=nonempty_iff_ne_empty.mpr empty
  let q:=t.max' nonempty
  have mq : q∈t:=t.max'_mem _
  have pq:=pr q (ht mq)
  have dvd : q∣H*den t := eqn ▸ dvd_mul_of_dvd_right (dvd_prod_of_mem (fun p=>p) mq) A
  rcases pq.dvd_mul.mp dvd with bad|denom
  · exact avoid q (ht mq) bad
  obtain ⟨p,mp,dv⟩:=(pq.prime.dvd_finsetProd_iff (fun j=>j-1)).mp denom
  have upper : p≤q:=t.le_max' _ mp
  have lower:=(pr p (ht mp)).one_lt
  have:=Nat.le_of_dvd (show 0<p-1 by omega) dv
  omega

/-- A computable absolute gap, uniform over all allowed support sets. -/
theorem rational_gap {A H K : ℕ} {s : Finset ℕ} (card : s.card≤K)
    (positive : ∀p∈s,2≤p) (apart : miss A H s) :
    1 ≤ (budget A K:ℚ)*|(A:ℚ)*((num s:ℚ)/den s)-H| := by
  have n:=separated A H K s card positive apart
  have dp : 0<den s := prod_pos (fun p hp=>by have:=positive p hp;omega)
  have v : (0:ℚ)<den s := by exact_mod_cast dp
  let u : ℤ:=(A:ℤ)*num s-(H:ℤ)*den s
  have cast : (den s:ℚ)≤(budget A K:ℚ)*|(u:ℚ)| := by
    have intBound:=Int.ofNat_le.mpr n
    simp only [gap,Nat.cast_mul,Int.natCast_natAbs] at intBound
    dsimp [u]
    exact_mod_cast intBound
  have eqn : ((A:ℚ)*((num s:ℚ)/den s)-H)*(den s:ℚ)=(u:ℚ) := by
    dsimp [u];push_cast;field_simp
  apply (mul_le_mul_iff_of_pos_right v).mp
  have ab:=congrArg (fun z:ℚ=>|z|) eqn
  rw [abs_mul,abs_of_pos v] at ab
  simpa only [one_mul,mul_assoc,ab] using cast

end OMA.CofactorEulerSeparation245212

end

section

/- Congruences for complete dyadic blocks in the weighted geometric sum. -/
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

/- Limits of the weighted divisor factors on odd fourth powers have odd
numerators. Finite products of them stay uniformly away from two. -/
namespace OMA.SquareCompact245212
open Finset Filter Topology OMA.Smooth245212

def OddNum (x : ℚ) := ∃ A B : ℕ, Odd A ∧ 0<B ∧ x=(A:ℚ)/B

theorem one : OddNum 1 := ⟨1,1,by decide,by decide,by norm_num⟩
theorem mul {x y : ℚ} (hx : OddNum x) (hy : OddNum y) : OddNum (x*y) := by
  obtain ⟨a,b,ha,hb,rfl⟩ := hx
  obtain ⟨c,d,hc,hd,rfl⟩ := hy
  exact ⟨a*c,b*d,ha.mul hc,Nat.mul_pos hb hd,by push_cast; ring⟩
theorem ne_two {x : ℚ} (h : OddNum x) : x≠2 := by
  obtain ⟨a,b,ha,hb,rfl⟩ := h
  intro eq
  have div := (div_eq_iff (by positivity : (b:ℚ)≠0)).mp eq
  have same : a=2*b := by exact_mod_cast div
  obtain ⟨t,ht⟩ := ha
  omega

theorem quotient {p e : ℕ} (hp : Nat.Prime p) (odd : Odd (W (p^e))) :
    OddNum (X p (some e)) := by
  refine ⟨W (p^e),(e+1)*p^e,odd,by have := hp.pos; positivity,?_⟩
  apply (eq_div_iff (by have := hp.pos; positivity)).2
  simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow] using x_factor hp e

private theorem finite_factor {p e : ℕ} (hp : Nat.Prime p) (po : Odd p) (e4 : 4∣e) :
    OddNum (X p (some e)) := by
  obtain ⟨a,rfl⟩ := e4
  have hh := (OMA.DyadicBlocks245212.prime_block p 0 (2*a) hp po).2.2.2
  apply quotient hp
  rw [Nat.odd_iff]
  simpa [Nat.ModEq,show 2*a*2=4*a by ring,Nat.add_mod] using hh

theorem infinite_factor {p : ℕ} (hp : Nat.Prime p) (po : Odd p) :
    OddNum (X p none) := by
  refine ⟨p,p-1,po,by have := hp.one_lt; omega,?_⟩
  have pp : (1:ℚ)<p := by exact_mod_cast hp.one_lt
  simp only [X,Y,sub_zero,Nat.cast_sub hp.one_le,Nat.cast_one]
  field_simp [show (p:ℚ)-1≠0 by linarith]; ring

private theorem dichotomy {v : ℕ → ℕ} (inc : Monotone v) :
    (∃ M, ∀ᶠ n in atTop,v n=M) ∨ Tendsto v atTop atTop := by
  by_cases h : BddAbove (Set.range v)
  · obtain ⟨n,hn⟩ := Nat.sSup_mem (Set.range_nonempty v) h
    refine Or.inl ⟨v n,eventually_atTop.mpr ⟨n,fun m hm => le_antisymm ?_ (inc hm)⟩⟩
    rw [hn]; exact le_csSup h ⟨m,rfl⟩
  · exact Or.inr (tendsto_atTop_atTop_of_monotone' inc h)

/-- A moving prime or exponent has an odd-numerator limit automatically.
Only pairs stabilizing in both coordinates need a local arithmetic check. -/
theorem factor_limit_restricted (s : ℚ → Prop) (p e : ℕ → ℕ) (pm : Monotone p) (em : Monotone e)
    (hp : ∀ n,Nat.Prime (p n)) (po : ∀ n,Odd (p n)) (atOne : s 1)
    (atCap : ∀ P : ℕ,Nat.Prime P → Odd P → (∀ᶠ n in atTop,p n=P) → s (X P none))
    (stable : ∀ P E, (∀ᶠ n in atTop,p n=P) → (∀ᶠ n in atTop,e n=E) →
      s (X P (some E))) :
    ∃ x : ℚ,s x ∧ Tendsto (fun n => X (p n) (some (e n))) atTop (𝓝 x) := by
  rcases dichotomy pm with ⟨P,hP⟩|hP
  · obtain ⟨n,hn⟩ := hP.exists
    have pr : Nat.Prime P := hn ▸ hp n
    have od : Odd P := hn ▸ po n
    rcases dichotomy em with ⟨E,hE⟩|hE
    · refine ⟨X P (some E),stable P E hP hE,?_⟩
      apply tendsto_const_nhds.congr'
      filter_upwards [hP,hE] with n a b; rw [a,b]
    · have upper : Tendsto (fun n : ℕ => (2:ℚ)/(e n+1)) atTop (𝓝 0) := by
        simpa only [Function.comp_apply,div_eq_mul_inv,one_mul,mul_zero] using
          ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℚ)).comp hE).const_mul 2
      have yl : Tendsto (fun n => Y P (some (e n))) atTop (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds upper
          (fun n => y_nonneg pr.one_lt _) (fun n => ((lt_div_iff₀ (by positivity)).mpr
            (OMA.CapOrder245212.y_short pr (e n))).le)
      have pp : (1:ℚ)<P := by exact_mod_cast pr.one_lt
      refine ⟨X P none,atCap P pr od hP,?_⟩
      have lim := (tendsto_const_nhds (x:=(1:ℚ))).add
        (((tendsto_const_nhds (x:=(1:ℚ))).sub yl).div_const ((P:ℚ)-1))
      apply lim.congr'
      filter_upwards [hP] with n pn; rw [pn]; rfl
  · have pt : Tendsto (fun n => (p n:ℚ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hP
    have den : Tendsto (fun n => (p n:ℚ)-1) atTop atTop := by
      apply tendsto_atTop.mpr
      intro x
      filter_upwards [tendsto_atTop.mp pt (x+1)] with n hn
      linarith
    have inv : Tendsto (fun n => ((p n:ℚ)-1)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp den
    refine ⟨1,atOne,tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun n => 1+((p n:ℚ)-1)⁻¹) atTop (𝓝 1) by simpa using inv.const_add 1) ?_ ?_⟩
    · intro n
      have pp : (1:ℚ)<p n := by exact_mod_cast (hp n).one_lt
      exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (y_one (hp n).one_lt _)) (by linarith))
    · intro n
      have pp : (1:ℚ)<p n := by exact_mod_cast (hp n).one_lt
      simp only [X,←one_div]
      exact add_le_add_right (div_le_div_of_nonneg_right (sub_le_self _ (y_nonneg (hp n).one_lt _))
        (by linarith)) _

theorem factor_limit_by (s : ℚ → Prop) (p e : ℕ → ℕ) (pm : Monotone p) (em : Monotone e)
    (hp : ∀ n,Nat.Prime (p n)) (po : ∀ n,Odd (p n)) (atOne : s 1)
    (atCap : ∀ P : ℕ,Nat.Prime P → Odd P → s (X P none))
    (stable : ∀ P E, (∀ᶠ n in atTop,p n=P) → (∀ᶠ n in atTop,e n=E) →
      s (X P (some E))) :
    ∃ x : ℚ,s x ∧ Tendsto (fun n => X (p n) (some (e n))) atTop (𝓝 x) :=
  factor_limit_restricted s p e pm em hp po atOne (fun P pr op _ => atCap P pr op) stable

theorem factor_limit_of_stable (p e : ℕ → ℕ) (pm : Monotone p) (em : Monotone e)
    (hp : ∀ n,Nat.Prime (p n)) (po : ∀ n,Odd (p n))
    (stable : ∀ P E, (∀ᶠ n in atTop,p n=P) → (∀ᶠ n in atTop,e n=E) →
      OddNum (X P (some E))) :
    ∃ x : ℚ,OddNum x ∧ Tendsto (fun n => X (p n) (some (e n))) atTop (𝓝 x) :=
  factor_limit_by OddNum p e pm em hp po one (fun _ => infinite_factor) stable

theorem factor_limit (p e : ℕ → ℕ) (pm : Monotone p) (em : Monotone e)
    (hp : ∀ n,Nat.Prime (p n)) (po : ∀ n,Odd (p n)) (ed : ∀ n,4∣e n) :
    ∃ x : ℚ,OddNum x ∧ Tendsto (fun n => X (p n) (some (e n))) atTop (𝓝 x) := by
  apply factor_limit_of_stable p e pm em hp po
  intro P E pP eE
  obtain ⟨n,pn,en⟩ := (pP.and eE).exists
  exact finite_factor (pn ▸ hp n) (pn ▸ po n) (en ▸ ed n)

theorem uniform_gap (K : ℕ) (c : ℚ) (hc : OddNum c) :
    ∃ δ : ℚ, 0<δ ∧ ∀ p e : Fin K → ℕ, (∀ i,Nat.Prime (p i)) → (∀ i,Odd (p i)) →
      (∀ i,4∣e i) → δ≤|c*(∏ i,X (p i) (some (e i)))-2| := by
  by_contra! bad
  have pick (n : ℕ) := bad (1/((n:ℚ)+1)) (by positivity)
  choose p e hp ho he close using pick
  let seq (n : ℕ) := (p n,e n)
  obtain ⟨g,sorted⟩ := wellQuasiOrdered_le.exists_monotone_subseq seq
  have points (i : Fin K) := factor_limit (fun n => p (g n) i) (fun n => e (g n) i)
    (fun _ _ le => (sorted _ _ le).1 i) (fun _ _ le => (sorted _ _ le).2 i)
    (fun n => hp (g n) i) (fun n => ho (g n) i) (fun n => he (g n) i)
  choose x ox conv using points
  have prod (s : Finset (Fin K)) : OddNum (∏ i∈s,x i) := by
    induction s using Finset.induction_on with
    | empty => simpa using one
    | @insert i s mem ih => simpa only [prod_insert mem] using mul (ox i) ih
  have unequal := ne_two (mul hc (prod univ))
  have limit := (tendsto_finsetProd univ (fun i _ => conv i)).const_mul c
  have t2 : Tendsto (fun n => c*∏ i,X (p n i) (some (e n i))) atTop (𝓝 2) := by
    have hz := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℚ)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun n : ℕ => 2-1/((n:ℚ)+1)) atTop (𝓝 2) by simpa using tendsto_const_nhds.sub hz)
      (show Tendsto (fun n : ℕ => 2+1/((n:ℚ)+1)) atTop (𝓝 2) by simpa using hz.const_add 2)
    · intro n; linarith only [(abs_lt.mp (close n)).1]
    · intro n; linarith only [(abs_lt.mp (close n)).2]
  exact unequal (tendsto_nhds_unique limit (t2.comp g.strictMono.tendsto_atTop))

end OMA.SquareCompact245212

end

section

/- In an equality whose odd part is a power of 2 in its exponent,
the divisor count of the square root of the odd part is 1 modulo that power. -/
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

private theorem dyadic_balance (k : ℕ) :
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

/-- If the odd part of a solution is a square, it is a fourth power. -/
theorem square_root_is_square {k u : ℕ} (ou : Odd u)
    (eq : OeisA245212.a (2^k*u^2)=(σ 1 (2^k*u^2):ℤ)) : IsSquare u := by
  have v := tau_root (h:=0) ou eq
  apply square_of_odd_tau
  simpa [Nat.odd_iff,Nat.ModEq] using v

private theorem merge (a b H : ℕ) (even : Even H) :
    (1+a*H)*(1+b*H) ≡ 1+(a+b)*H [MOD 2*H] := by
  obtain ⟨c,hc⟩ := even
  rw [show (1+a*H)*(1+b*H)=(2*H)*(a*b*c)+(1+(a+b)*H) by rw [hc]; ring]
  exact Nat.ModEq.modulus_mul_add

private theorem tau_linear (u H : ℕ) (even : Even H) (nz : u≠0) :
    σ 0 (u^H) ≡ 1+Ω u*H [MOD 2*H] := by
  induction u using Nat.recOnPrimeCoprime with
  | zero => contradiction
  | prime_pow p a hp =>
    simp only [←pow_mul,sigma_zero_apply_prime_pow hp,cardFactors_apply_prime_pow hp,add_comm 1]
    rfl
  | coprime a b ha hb hab ia ib =>
    have a0 : a≠0 := by omega
    have b0 : b≠0 := by omega
    rw [mul_pow,isMultiplicative_sigma.map_mul_of_coprime ((hab.pow_left H).pow_right H),
      cardFactors_mul a0 b0]
    exact ((ia a0).mul (ib b0)).trans (merge _ _ H even)

/-- A perfect-power odd part must have a root with even total prime multiplicity. -/
theorem even_multiplicity {k h u : ℕ} (ou : Odd u)
    (eq : OeisA245212.a (2^k*u^(2^(h+1)))=(σ 1 (2^k*u^(2^(h+1))):ℤ)) :
    Even (Ω u) := by
  cases h with
  | zero =>
    obtain ⟨v,eqv⟩ := square_root_is_square ou eq
    rw [eqv,←sq,cardFactors_pow]; exact even_two_mul _
  | succ h =>
    let H : ℕ := 2^(h+1)
    have hh : Even H := even_iff_two_dvd.mpr (dvd_pow_self _ (by omega))
    have root := tau_root ou eq
    rw [pow_succ' (2:ℕ) (h+1)] at root
    have lin := tau_linear u H hh ou.pos.ne'
    have m : 1+Ω u*H ≡ 1+0 [MOD 2*H] := lin.symm.trans root
    have z : Ω u*H ≡ 0*H [MOD 2*H] := by simpa only [zero_mul] using m.add_left_cancel' 1
    exact even_iff_two_dvd.mpr (Nat.modEq_zero_iff_dvd.mp (z.mul_right_cancel' (by dsimp [H]; positivity)))

end OMA.DyadicPower245212

end

section

/- For a fixed positive exponent vector there are finitely many choices of
prime bases at which a fixed positive combination of the two divisor products
can equal a given number. The products decrease when bases increase. -/
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

private theorem y_strict_prime {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (pq : p<q) {e : ℕ} (ep : 0<e) : Y q (some e)<Y p (some e) := by
  rw [y_avg hq.one_lt,y_avg hp.one_lt]
  apply div_lt_div_of_pos_right _ (by positivity)
  apply sum_lt_sum
  · intro i _
    gcongr
    exact_mod_cast hp.pos
  · refine ⟨1,mem_range.mpr (by omega),?_⟩
    simp only [pow_one]
    apply inv_lt_inv₀ (by exact_mod_cast hq.pos) (by exact_mod_cast hp.pos) |>.mpr
    exact_mod_cast pq

private theorem x_le_prime {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (pq : p≤q) (e : ℕ) : X q (some e)≤X p (some e) := by
  rw [x_avg hp,x_avg hq]
  gcongr
  exact_mod_cast hp.pos

theorem y_pos {p : ℕ} (hp : Nat.Prime p) (e : ℕ) : 0<Y p (some e) := by
  rw [y_avg hp.one_lt]
  apply div_pos _ (by positivity)
  exact sum_pos' (fun _ _ => by positivity) ⟨0,by simp,by simp⟩

theorem finite_bases {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ)
    (ep : ∀ i,0<e i) (a b t : ℚ) (ha : 0≤a) (hb : 0<b) :
    {p : ι → ℕ | (∀ i,Nat.Prime (p i)) ∧
      a*(∏ i,X (p i) (some (e i)))+b*(∏ i,Y (p i) (some (e i)))=t}.Finite := by
  apply WellQuasiOrderedLE.finite_of_isAntichain
  intro p hp q hq diff pq
  obtain ⟨i,lt⟩ : ∃ i,p i<q i := by
    by_contra! h; exact diff (funext fun j => Nat.le_antisymm (pq j) (h j))
  have yp (j) := y_pos (hq.1 j) (e j)
  have xp := prod_le_prod (s:=univ) (fun j _ => x_nonneg (hq.1 j).one_lt (some (e j)))
    (fun j _ => x_le_prime (hp.1 j) (hq.1 j) (pq j) (e j))
  have ys (j) : Y (q j) (some (e j))≤Y (p j) (some (e j)) := by
    rcases (pq j).eq_or_lt with h|l
    · rw [h]
    · exact (y_strict_prime (hp.1 j) (hq.1 j) l (ep j)).le
  have strict := Finset.prod_lt_prod (s:=univ) (fun j _ => yp j) (fun j _ => ys j)
    ⟨i,mem_univ i,y_strict_prime (hp.1 i) (hq.1 i) lt (ep i)⟩
  linarith only [hp.2,hq.2,mul_le_mul_of_nonneg_left xp ha,mul_lt_mul_of_pos_left strict hb]

end OMA.FixedExponents245212

end

section

/- Finitely many solutions at fixed dyadic exponent and bounded number of odd
prime factors, whenever the odd part is a square. -/
namespace OMA.SquareFinite245212
open Finset OMA.Smooth245212 OMA.SquareCompact245212
open scoped ArithmeticFunction.sigma

def Config (K : ℕ) (c d : ℚ) (p e : Fin K → ℕ) :=
  (∀ i,Nat.Prime (p i)) ∧ (∀ i,Odd (p i)) ∧ (∀ i,4∣e i) ∧ (∀ i,0<e i) ∧
  c*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2

private theorem bounded {K : ℕ} {c d : ℚ} (hc : OddNum c) (d0 : 0<d) (d1 : d≤1) :
    ∃ L : ℕ, ∀ p e, Config K c d p e → ∀ i,e i<L := by
  obtain ⟨δ,hδ,sep⟩ := uniform_gap K c hc
  obtain ⟨L,hL⟩ := exists_nat_gt (2/δ)
  refine ⟨L,fun p e he i => ?_⟩
  obtain ⟨hp,ho,ed,_,eq⟩ := he
  have bound := sep p e hp ho ed
  have y0 (j) := y_nonneg (hp j).one_lt (some (e j))
  have z : 0≤d*(∏ j,Y (p j) (some (e j))) := mul_nonneg d0.le (prod_nonneg (fun j _ => y0 j))
  have act : |c*(∏ j,X (p j) (some (e j)))-2|=d*(∏ j,Y (p j) (some (e j))) := by
    rw [abs_of_nonpos (by linarith only [eq,z])]; linarith only [eq]
  rw [act] at bound
  have upper : δ≤Y (p i) (some (e i)) := by
    apply bound.trans
    rw [←prod_erase_mul _ _ (mem_univ i)]
    exact (mul_le_of_le_one_left (mul_nonneg (prod_nonneg (fun j _ => y0 j)) (y0 i)) d1).trans
      (mul_le_of_le_one_left (y0 i) (prod_le_one (fun j _ => y0 j)
        (fun j _ => y_one (hp j).one_lt _)))
  have hh := OMA.CapOrder245212.y_short (hp i) (e i)
  have m := mul_le_mul_of_nonneg_right upper (show 0≤(e i:ℚ)+1 by positivity)
  have qq : (e i:ℚ)<2/δ := (lt_div_iff₀ hδ).mpr (by linarith only [hh,m,hδ])
  exact_mod_cast qq.trans hL

theorem configs (K : ℕ) (c d : ℚ) (hc : OddNum c) (d0 : 0<d) (d1 : d≤1) :
    {v : (Fin K → ℕ) × (Fin K → ℕ) | Config K c d v.1 v.2}.Finite := by
  obtain ⟨L,size⟩ := bounded hc d0 d1
  have c0 : 0≤c := by obtain ⟨A,B,_,_,rfl⟩ := hc; positivity
  apply Set.Finite.of_finite_fibers Prod.snd
  · apply (Set.Finite.pi' (fun _ : Fin K => Set.finite_Iio L)).subset
    rintro e ⟨⟨p,v⟩,h,rfl⟩
    exact size _ _ h
  · rintro e ⟨⟨p,v⟩,conf,rfl⟩
    have finite := OMA.FixedExponents245212.finite_bases v conf.2.2.2.1 c d 2 c0 d0
    apply (finite.image (fun q => (q,v))).subset
    rintro ⟨q,f⟩ ⟨hf,hv⟩
    have same : f=v := hv
    subst f
    exact ⟨q,⟨hf.1,hf.2.2.2.2⟩,rfl⟩

private theorem square_rank (k K : ℕ) :
    {u : ℕ | Odd u ∧ IsSquare u ∧ u.primeFactors.card=K ∧
      OeisA245212.a (2^k*u)=(σ 1 (2^k*u):ℤ)}.Finite := by
  let c := X 2 (some k)
  let d := Y 2 (some k)
  have hc : OddNum c := quotient Nat.prime_two (OMA.DyadicPower245212.dyadic_odd k)
  have d0 : 0<d := by
    dsimp [d]; rw [y_avg (by decide : 1<2)]
    exact div_pos (sum_pos' (fun i _ => by positivity) ⟨0,by simp,by simp⟩) (by positivity)
  apply ((configs K c d hc d0 (y_one (by decide) _)).image (fun v => total v.1 v.2)).subset
  rintro u ⟨odd,sq,card,eq⟩
  let S := u.primeFactors
  let p := S.orderEmbOfFin card
  let e (i : Fin K) := u.factorization (p i)
  have mem (i) : p i∈u.primeFactors := orderEmbOfFin_mem S card i
  have hp (i) := Nat.prime_of_mem_primeFactors (mem i)
  have op (i) : Odd (p i) := Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right
    (Nat.dvd_of_mem_primeFactors (mem i)))
  have ep (i) : 0<e i := (hp i).factorization_pos_of_dvd odd.pos.ne' (Nat.dvd_of_mem_primeFactors (mem i))
  have fourth : ∃ t,u=t^4 := by
    obtain ⟨w,hw⟩ := sq
    have wo : Odd w := (Nat.odd_mul.mp (hw ▸ odd)).1
    have eq' : OeisA245212.a (2^k*w^2)=(σ 1 (2^k*w^2):ℤ) := by simpa only [sq,hw] using eq
    obtain ⟨t,ht⟩ := OMA.DyadicPower245212.square_root_is_square wo eq'
    exact ⟨t,by rw [hw,ht]; ring⟩
  have ed (i) : 4∣e i := by
    obtain ⟨t,ht⟩ := fourth
    change 4∣u.factorization (p i)
    have f (q : ℕ) : 4∣u.factorization q := by
      rw [ht,Nat.factorization_pow]; simp
    apply f
  have repr : total p e=u := by
    exact (Fintype.prod_equiv (S.orderIsoOfFin card).toEquiv _
      (fun j : S => j.val^(u.factorization j.val)) (fun _ => rfl)).trans
      (Nat.prod_primeFactors_coe_pow_factorization odd.pos.ne').symm
  let P : Fin (K+1) → ℕ := Fin.cons 2 (p : Fin K → ℕ)
  let E : Fin (K+1) → ℕ := Fin.cons k e
  have prime : ∀ i,Nat.Prime (P i) := Fin.cases Nat.prime_two hp
  have inj : P.Injective := Fin.cons_injective_of_injective (by
    rintro ⟨i,hi⟩; have h := op i; rw [hi] at h; norm_num [Nat.odd_iff] at h) p.injective
  have entire : total P E=2^k*u := by
    rw [total,Fin.prod_univ_succ]; simp only [P,E,Fin.cons_zero,Fin.cons_succ]
    exact congrArg (2^k*·) repr
  have norm := normalized_of_eq P prime inj E (by rw [entire]; exact eq)
  unfold normalized at norm
  rw [Fin.prod_univ_succ (fun i => X (P i) (some (E i))),
    Fin.prod_univ_succ (fun i => Y (P i) (some (E i)))] at norm
  exact ⟨(p,e),⟨hp,op,ed,ep,by simpa only [P,E,c,d,Fin.cons_zero,Fin.cons_succ] using norm⟩,repr⟩

theorem square_finite (k K : ℕ) :
    {u : ℕ | Odd u ∧ IsSquare u ∧ u.primeFactors.card≤K ∧
      OeisA245212.a (2^k*u)=(σ 1 (2^k*u):ℤ)}.Finite := by
  apply ((Set.finite_Iic K).biUnion (fun j _ => square_rank k j)).subset
  rintro u ⟨ho,hs,hc,he⟩
  exact Set.mem_iUnion.mpr ⟨u.primeFactors.card,Set.mem_iUnion.mpr ⟨hc,ho,hs,rfl,he⟩⟩

end OMA.SquareFinite245212

end

section

/- Exact power of two in a weighted sum of divisors of an odd prime power. -/
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

/-- The valuation depends only on the exponent, even when the odd prime varies. -/
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

/- A base-independent two-adic obstruction for every number of odd primes. -/
namespace OMA.ExponentParity245212
open Finset Nat ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212
  OMA.WeightVal245212
open scoped ArithmeticFunction.sigma Function

/-- In an equality with r distinct odd prime factors, the product of their
exponents plus two is divisible by 2^r. The power of two in n is unrestricted. -/
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

/-- A solution whose odd part is not square has an exponent equal to 2 mod 4. -/
theorem two_mod_four {ι : Type*} [Fintype ι] (p e : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (odd : ∀ i, Odd (p i)) (inj : Function.Injective p)
    (a : ℕ) (eq : OeisA245212.a (2^a*total p e) = (σ 1 (2^a*total p e) : ℤ))
    (nonsquare : ∃ i, Odd (e i)) : ∃ i, e i % 4 = 2 := by
  classical
  by_contra! no
  have lower := (Nat.prime_two.pow_dvd_iff_le_factorization
    (prod_ne_zero_iff.mpr (fun i _ => by omega : ∀ i ∈ univ, e i+2≠0))).mp
      (exponent_product p e hp odd inj a eq)
  rw [Nat.factorization_prod_apply (fun i _ => by omega : ∀ i ∈ univ, e i+2≠0)] at lower
  have upper (i : ι) : (e i+2).factorization 2 ≤ 1 := by
    have d : ¬ 2^2 ∣ e i+2 := by have := no i; norm_num; omega
    have := mt (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : e i+2≠0)).mpr d
    omega
  obtain ⟨j,hj⟩ := nonsquare
  have zero : WeightVal245212.val (e j+2)=0 := val_odd (by
    rw [Nat.odd_iff] at hj ⊢; omega)
  have lt := Finset.sum_lt_sum (s:=univ) (fun i _ => upper i)
    ⟨j,mem_univ j,show (e j+2).factorization 2 < 1 by rw [show (e j+2).factorization 2=0 from zero]; decide⟩
  simpa using (not_lt_of_ge lower (by simpa using lt))

end OMA.ExponentParity245212

end

section

/- A bounded exceptional odd prime power in nonsquare A245212 solutions.
The rank of the odd part and the dyadic exponent are fixed, not its primes. -/
namespace OMA.BoundedAtom245212
open Finset Filter Topology Nat OMA.Smooth245212 OMA.SquareCompact245212
open OMA.WeightVal245212 (weight_local)
open scoped ArithmeticFunction.sigma

/-- Away from exponents 2 mod 4 the factors of two in the numerator
can all be cancelled against the local divisor count. -/
theorem good_factor {p e : ℕ} (pr : Nat.Prime p) (op : Odd p) (good : e%4≠2) :
    OddNum (X p (some e)) := by
  let N := W (p^e)
  have np : 0<N := by
    dsimp [N]; rw [w_pow pr]
    exact sum_pos' (fun i _ => Nat.zero_le _) ⟨0,mem_range.mpr (Nat.succ_pos _),by simp⟩
  have small : OMA.WeightVal245212.val (e+2)<2 := by
    by_contra! hi
    have x := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : e+2≠0)).mpr hi
    change 4 ∣ e+2 at x
    omega
  have vals := weight_local pr op e
  change OMA.WeightVal245212.val N+1=OMA.WeightVal245212.val (e+1)+OMA.WeightVal245212.val (e+2) at vals
  obtain ⟨B,hB⟩ := (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.succ_ne_zero e)).mpr
    (show OMA.WeightVal245212.val N≤OMA.WeightVal245212.val (e+1) by omega)
  let A := ordCompl[2] N
  have rep : 2^(OMA.WeightVal245212.val N)*A=N := Nat.ordProj_mul_ordCompl_eq_self N 2
  have oa : Odd A := Nat.not_even_iff_odd.mp (fun h => Nat.not_dvd_ordCompl Nat.prime_two np.ne'
    (even_iff_two_dvd.mp h))
  have bp : 0<B := by
    by_contra! z
    have z' : B=0 := by omega
    simp [z'] at hB
  have raw := x_factor pr e
  change X p (some e)*(((e:ℚ)+1)*p^e)=(N:ℚ) at raw
  have br := congrArg (Nat.cast : ℕ → ℚ) hB
  have nr := congrArg (Nat.cast : ℕ → ℚ) rep
  push_cast at br nr
  refine ⟨A,B*p^e,oa,Nat.mul_pos bp (Nat.pow_pos pr.pos),?_⟩
  apply (eq_div_iff (by exact_mod_cast (Nat.mul_pos bp (Nat.pow_pos pr.pos)).ne')).mpr
  push_cast
  apply (mul_left_cancel₀ (by positivity : (2:ℚ)^(OMA.WeightVal245212.val N)≠0))
  linear_combination raw - nr - (X p (some e)*(p:ℚ)^e)*br

private theorem product_odd {K : ℕ} (x : Fin K → ℚ) (ox : ∀ i,OddNum (x i)) :
    OddNum (∏ i,x i) := by
  have aux (s : Finset (Fin K)) : OddNum (∏ i∈s,x i) := by
    induction s using Finset.induction_on with
    | empty => simpa using OMA.SquareCompact245212.one
    | @insert i s hi ih => simpa only [prod_insert hi] using OMA.SquareCompact245212.mul (ox i) ih
  exact aux univ

/-- If some exponent grows past every bound, a prime and an exponent
2 mod 4 must both stay bounded in at least one coordinate. -/
theorem bounded_or_atom (K : ℕ) (c d : ℚ) (hc : OddNum c) (d0 : 0≤d) (d1 : d≤1) :
    ∃ B : ℕ, ∀ p e : Fin K → ℕ, (∀ i,Nat.Prime (p i)) → (∀ i,Odd (p i)) →
      c*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2 →
      (∀ i,e i≤B) ∨ ∃ i,e i%4=2 ∧ p i≤B ∧ e i≤B := by
  by_contra! bad
  choose p e hp ho eq large avoid using bad
  let seq (n : ℕ) := (p n,e n)
  obtain ⟨g,sorted⟩ := wellQuasiOrdered_le.exists_monotone_subseq seq
  have points (i : Fin K) : ∃ x : ℚ,OddNum x ∧
      Tendsto (fun n => X (p (g n) i) (some (e (g n) i))) atTop (𝓝 x) := by
    apply factor_limit_of_stable _ _ (fun _ _ le => (sorted _ _ le).1 i)
      (fun _ _ le => (sorted _ _ le).2 i) (fun n => hp (g n) i) (fun n => ho (g n) i)
    intro P E pP eE
    have eventuallyLarge := g.strictMono.tendsto_atTop.eventually (eventually_ge_atTop (max P E))
    obtain ⟨n,pn,en,gn⟩ := (pP.and (eE.and eventuallyLarge)).exists
    change p (g n) i=P at pn
    change e (g n) i=E at en
    apply good_factor (pn ▸ hp (g n) i) (pn ▸ ho (g n) i)
    intro badE
    have stop := avoid (g n) i
    rw [pn,en] at stop
    exact (not_lt_of_ge ((le_max_right P E).trans gn)) (stop badE ((le_max_left P E).trans gn))
  choose x ox conv using points
  have limit := (tendsto_finsetProd univ (fun i _ => conv i)).const_mul c
  have notTwo := ne_two (OMA.SquareCompact245212.mul hc (product_odd x ox))
  apply notTwo
  apply tendsto_nhds_unique limit
  suffices total : Tendsto (fun n => c*∏ i,X (p n i) (some (e n i))) atTop (𝓝 2) from
    total.comp g.strictMono.tendsto_atTop
  have error (n : ℕ) : 0 ≤ d*∏ i,Y (p n i) (some (e n i)) ∧
      d*(∏ i,Y (p n i) (some (e n i))) ≤ 2/((n:ℚ)+1) := by
    have y0 (j) := y_nonneg (hp n j).one_lt (some (e n j))
    have pos := prod_nonneg (s:=univ) (fun j _ => y0 j)
    refine ⟨mul_nonneg d0 pos,?_⟩
    obtain ⟨i,gi⟩ := large n
    calc
      _ ≤ ∏ j,Y (p n j) (some (e n j)) := mul_le_of_le_one_left pos d1
      _ ≤ Y (p n i) (some (e n i)) := by
        rw [←prod_erase_mul _ _ (mem_univ i)]
        exact mul_le_of_le_one_left (y0 i) (prod_le_one (fun j _ => y0 j) (fun j _ => y_one (hp n j).one_lt _))
      _ ≤ 2/((e n i:ℚ)+1) := ((lt_div_iff₀ (by positivity)).mpr (OMA.CapOrder245212.y_short (hp n i) _)).le
      _ ≤ _ := by gcongr
  have zero : Tendsto (fun n : ℕ => 2/((n:ℚ)+1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℚ)).const_mul 2
  have err := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds zero
    (fun n => (error n).1) (fun n => (error n).2)
  apply (show Tendsto (fun n => 2-d*∏ i,Y (p n i) (some (e n i))) atTop (𝓝 2) by
    simpa using (tendsto_const_nhds (x:=(2:ℚ))).sub err).congr
  intro n; linarith only [eq n]

private theorem atom_in_box (K : ℕ) (c d : ℚ) (hc : OddNum c) (d0 : 0<d) (d1 : d≤1) :
    ∃ B : ℕ, ∀ p e : Fin K → ℕ, (∀ i,Nat.Prime (p i)) → (∀ i,Odd (p i)) →
      (∀ i,0<e i) → (∃ i,e i%4=2) →
      c*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2 →
      ∃ i,e i%4=2 ∧ p i≤B ∧ e i≤B := by
  classical
  obtain ⟨L,alt⟩ := bounded_or_atom K c d hc d0.le d1
  let F : Set (Fin K → ℕ) := {e | ∀ i,0<e i ∧ e i≤L}
  let bases (e : Fin K → ℕ) : Set (Fin K → ℕ) := {p | (∀ i,Nat.Prime (p i)) ∧
    c*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2}
  have cf : F.Finite := (Set.Finite.pi' (fun _ : Fin K => Set.finite_Iic L)).subset
    (fun _ h i => (h i).2)
  have c0 : 0≤c := by obtain ⟨A,B,_,_,rfl⟩ := hc; positivity
  have bf := cf.biUnion (fun e he => (show (bases e).Finite from
    OMA.FixedExponents245212.finite_bases e (fun i => (he i).1) c d 2 c0 d0))
  have vals := bf.biUnion (fun p _ => Set.finite_range p)
  obtain ⟨M,cap⟩ := vals.bddAbove
  refine ⟨max L M,?_⟩
  intro p e hp ho ep has eq
  rcases alt p e hp ho eq with low | ⟨i,good,pi,ei⟩
  · obtain ⟨i,good⟩ := has
    have ef : e∈F := fun j => ⟨ep j,low j⟩
    have member : p∈⋃ t∈F,bases t := Set.mem_iUnion₂.mpr ⟨e,ef,hp,eq⟩
    have pm := cap (Set.mem_iUnion₂.mpr ⟨p,member,i,rfl⟩)
    exact ⟨i,good,pm.trans (le_max_right _ _),(low i).trans (le_max_left _ _)⟩
  · exact ⟨i,good,pi.trans (le_max_left _ _),ei.trans (le_max_left _ _)⟩

/-- Include the dyadic prime in the normalized equality and then separate
it back out; p and e describe only the odd factors. -/
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

private theorem exact_rank (k K : ℕ) :
    ∃ L : ℕ, ∀ m : ℕ, Odd m → ¬IsSquare m → m.primeFactors.card=K →
    OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ) →
    ∃ q∈m.primeFactors,m.factorization q%4=2 ∧ q≤L ∧ m.factorization q≤L := by
  classical
  let c := X 2 (some k)
  let d := Y 2 (some k)
  have hc : OddNum c := quotient Nat.prime_two (OMA.DyadicPower245212.dyadic_odd k)
  have dp : 0<d := by
    dsimp [d]; rw [y_avg (by decide : 1<2)]
    exact div_pos (sum_pos' (fun i _ => by positivity) ⟨0,by simp,by simp⟩) (by positivity)
  obtain ⟨L,cap⟩ := atom_in_box K c d hc dp (y_one (by decide) _)
  refine ⟨L,?_⟩
  intro m odd nonsq card eq
  let S := m.primeFactors
  let p := S.orderEmbOfFin card
  let e (i : Fin K) := m.factorization (p i)
  have mem (i) : p i∈m.primeFactors := orderEmbOfFin_mem S card i
  have hp (i) := Nat.prime_of_mem_primeFactors (mem i)
  have op (i) := Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right
    (Nat.dvd_of_mem_primeFactors (mem i)))
  have ep (i) : 0<e i := (hp i).factorization_pos_of_dvd odd.pos.ne' (Nat.dvd_of_mem_primeFactors (mem i))
  have repr : total p e=m := by
    exact (Fintype.prod_equiv (S.orderIsoOfFin card).toEquiv _
      (fun j : S => j.val^(m.factorization j.val)) (fun _ => rfl)).trans
      (Nat.prod_primeFactors_coe_pow_factorization odd.pos.ne').symm
  have ex : ∃ i,Odd (e i) := by
    by_contra! no
    have even (i) := Nat.not_odd_iff_even.mp (no i)
    choose f hf using even
    apply nonsq
    refine ⟨∏ i,p i^f i,?_⟩
    rw [←repr,total,←prod_mul_distrib]
    exact prod_congr rfl fun i _ => by rw [hf i,pow_add]
  have has := OMA.ExponentParity245212.two_mod_four p e hp op p.injective k (by rw [repr];exact eq) ex
  have norm := normalized_dyadic k p e hp op p.injective (by rw [repr]; exact eq)
  obtain ⟨i,bad,pi,ei⟩ := cap p e hp op ep has norm
  exact ⟨p i,mem i,bad,pi,ei⟩

/-- Fixing the power of two and the number of distinct odd primes, every
nonsquare odd core at equality is divisible exactly by one of a finite list
of prime powers whose exponents are 2 mod 4. Other exponents are unrestricted. -/
theorem bounded_atom (k K : ℕ) :
    ∃ B : ℕ, ∀ m : ℕ, Odd m → ¬IsSquare m → m.primeFactors.card≤K →
    OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ) →
    ∃ q∈m.primeFactors,m.factorization q%4=2 ∧ q≤B ∧ m.factorization q≤B := by
  choose L hL using exact_rank k
  refine ⟨∑ j∈range (K+1),L j,?_⟩
  intro m om ns hc eq
  obtain ⟨q,hq,pq,ql,el⟩ := hL m.primeFactors.card m om ns rfl eq
  have bound := single_le_sum (f:=L) (fun j _ => Nat.zero_le (L j)) (mem_range.mpr (Nat.lt_succ_of_le hc))
  exact ⟨q,hq,pq,ql.trans bound,el.trans bound⟩

end OMA.BoundedAtom245212

end

section

/- Finiteness at bounded rank when the finite odd prime-power factors
cannot cancel the full dyadic denominator of the weighted factor at two. -/
namespace OMA.ParityBudget245212
open Nat Finset Filter Topology OMA.Smooth245212 OMA.SquareCompact245212
open scoped ArithmeticFunction.sigma
open OMA.SquareCompact245212 (infinite_factor)

private theorem odd_fraction {N D : ℕ} (nz : 0<N) (dz : 0<D) (dv : 2^(OMA.WeightVal245212.val N)∣D) :
    OddNum ((N:ℚ)/D) := by
  obtain ⟨B,db⟩ := dv
  let A := ordCompl[2] N
  have na : 2^(OMA.WeightVal245212.val N)*A=N := Nat.ordProj_mul_ordCompl_eq_self N 2
  have oa : Odd A := Nat.not_even_iff_odd.mp (fun h =>
    Nat.not_dvd_ordCompl Nat.prime_two nz.ne' (even_iff_two_dvd.mp h))
  have bp : 0<B := by
    by_contra! neg
    have zero : B=0 := by omega
    rw [db,zero,mul_zero] at dz
    omega
  refine ⟨A,B,oa,bp,?_⟩
  rw [←na,db]
  push_cast; field_simp

private theorem scale_down {x : ℚ} (ox : OddNum x) (w : ℕ) : OddNum (x/(2:ℚ)^w) := by
  obtain ⟨A,B,odd,bp,rfl⟩ := ox
  exact ⟨A,B*2^w,odd,Nat.mul_pos bp (Nat.two_pow_pos _),by push_cast; ring⟩

/-- Each odd prime contributes at most this many factors of two to the
reduced numerator of the local weighted ratio. -/
def excess (e : ℕ) := OMA.WeightVal245212.val (e+2)-1

private theorem scale_local {p e w : ℕ} (pr : p.Prime) (op : Odd p) (hw : excess e≤w) :
    OddNum (X p (some e)/(2:ℚ)^w) := by
  let N := W (p^e)
  let D := (e+1)*p^e*2^w
  have np : 0<N := by
    dsimp [N]; rw [w_pow pr]
    exact sum_pos' (fun i _ => Nat.zero_le _) ⟨0,mem_range.mpr (Nat.succ_pos _),by simp⟩
  have dp : 0<D := by dsimp [D]; have := pr.pos; positivity
  have ord := OMA.WeightVal245212.weight_local pr op e
  change OMA.WeightVal245212.val N+1=OMA.WeightVal245212.val (e+1)+OMA.WeightVal245212.val (e+2) at ord
  have inc : OMA.WeightVal245212.val N≤OMA.WeightVal245212.val (e+1)+w := by unfold excess at hw; omega
  have divides : 2^(OMA.WeightVal245212.val N)∣D := by
    apply (pow_dvd_pow 2 inc).trans
    rw [pow_add]
    have dv := Nat.ordProj_dvd (e+1) 2
    exact mul_dvd_mul (dvd_mul_of_dvd_left dv (p^e)) (dvd_refl _)
  have ofrac := odd_fraction np dp divides
  have fx := x_factor pr e
  have eqx : X p (some e)=(N:ℚ)/(((e:ℚ)+1)*p^e) := by
    apply (eq_div_iff (by
      have pos : (0:ℚ)<p := by exact_mod_cast pr.pos
      positivity)).mpr
    exact fx
  rw [eqx,div_div]
  simpa [D] using ofrac

private theorem scaled_coefficient {k b : ℕ} (low : b≤k+OMA.WeightVal245212.val (k+1)) :
    OddNum (X 2 (some k)*(2:ℚ)^b) := by
  let D := (k+1)*2^k
  have dv : 2^b∣D := by
    apply (pow_dvd_pow 2 low).trans
    rw [pow_add,Nat.mul_comm]
    exact mul_dvd_mul (Nat.ordProj_dvd (k+1) 2) (dvd_refl _)
  obtain ⟨B,db⟩ := dv
  have dp : 0<D := by dsimp [D]; positivity
  have bp : 0<B := by
    by_contra! neg
    have z : B=0 := by omega
    rw [db,z,mul_zero] at dp
    omega
  have fx := x_factor Nat.prime_two k
  have bd := congrArg (Nat.cast : ℕ → ℚ) db
  dsimp only [D] at bd
  push_cast at bd
  refine ⟨W (2^k),B,OMA.DyadicPower245212.dyadic_odd k,bp,?_⟩
  apply (eq_div_iff (by exact_mod_cast bp.ne' : (B:ℚ)≠0)).mpr
  linear_combination fx - X 2 (some k)*bd

/-- Only count dyadic excess carried by an exactly bounded base and exponent. -/
def visible (B p e : ℕ) := if p≤B ∧ e≤B then excess e else 0

private theorem visible_gap (k K : ℕ) :
    ∃ B : ℕ, ∃ δ : ℚ, 0<δ ∧ ∀ p e : Fin K → ℕ, (∀ i,Nat.Prime (p i)) → (∀ i,Odd (p i)) →
      (∑ i,visible B (p i) (e i))≤k+OMA.WeightVal245212.val (k+1) →
      δ≤|X 2 (some k)*(∏ i,X (p i) (some (e i)))-2| := by
  by_contra! bad
  have pick (n : ℕ) := bad n (1/((n:ℚ)+1)) (by positivity)
  choose p e hp ho he close using pick
  let seq (n : ℕ) := (p n,e n)
  obtain ⟨g,sorted⟩ := wellQuasiOrdered_le.exists_monotone_subseq seq
  let Capture (i : Fin K) (x : ℚ) := ∃ w : ℕ, OddNum (x/(2:ℚ)^w) ∧
    ∀ᶠ n in atTop,w≤visible (g n) (p (g n) i) (e (g n) i)
  have points (i : Fin K) : ∃ x : ℚ,Capture i x ∧
      Tendsto (fun n => X (p (g n) i) (some (e (g n) i))) atTop (𝓝 x) := by
    have trivialWeight (x : ℚ) (hx : OddNum x) : Capture i x :=
      ⟨0,by simpa using hx,Eventually.of_forall fun _ => Nat.zero_le _⟩
    apply factor_limit_by (Capture i) _ _
      (fun _ _ le => (sorted _ _ le).1 i) (fun _ _ le => (sorted _ _ le).2 i)
      (fun n => hp (g n) i) (fun n => ho (g n) i) (trivialWeight _ OMA.SquareCompact245212.one)
      (fun _ pr op => trivialWeight _ (OMA.SquareCompact245212.infinite_factor pr op))
    intro P E pP eE
    obtain ⟨n,pn,en⟩ := (pP.and eE).exists
    change p (g n) i=P at pn
    refine ⟨excess E,scale_local (pn ▸ hp (g n) i) (pn ▸ ho (g n) i) le_rfl,?_⟩
    have large := g.strictMono.tendsto_atTop.eventually (eventually_ge_atTop (max P E))
    filter_upwards [pP,eE,large] with j pj ej big
    change p (g j) i=P at pj
    change e (g j) i=E at ej
    simp [visible,pj,ej,(le_max_left P E).trans big,(le_max_right P E).trans big]
  choose x capture conv using points
  choose w ox see using capture
  obtain ⟨n,hn⟩ := (Filter.eventually_all.mpr see).exists
  have low := (sum_le_sum (s:=univ) (fun i _ => hn i)).trans (he (g n))
  have prod (s : Finset (Fin K)) : OddNum (∏ i∈s,x i/(2:ℚ)^(w i)) := by
    induction s using Finset.induction_on with
    | empty => simpa using OMA.SquareCompact245212.one
    | @insert i s hi ih => simpa only [prod_insert hi] using OMA.SquareCompact245212.mul (ox i) ih
  have od := OMA.SquareCompact245212.mul (scaled_coefficient low) (prod univ)
  rw [prod_div_distrib,prod_pow_eq_pow_sum] at od
  let c := X 2 (some k)
  have distinct := ne_two (show OddNum (c*∏ i,x i) by
    dsimp only [c]; convert od using 1; field_simp)
  have limit := (tendsto_finsetProd univ (fun i _ => conv i)).const_mul c
  have t2 : Tendsto (fun n => c*∏ i,X (p n i) (some (e n i))) atTop (𝓝 2) := by
    have hz := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℚ)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun n : ℕ => 2-1/((n:ℚ)+1)) atTop (𝓝 2) by simpa using tendsto_const_nhds.sub hz)
      (show Tendsto (fun n : ℕ => 2+1/((n:ℚ)+1)) atTop (𝓝 2) by simpa using hz.const_add 2)
    · intro n; linarith only [(abs_lt.mp (close n)).1]
    · intro n; linarith only [(abs_lt.mp (close n)).2]
  exact distinct (tendsto_nhds_unique limit (t2.comp g.strictMono.tendsto_atTop))

private def Config {K : ℕ} (c d : ℚ) (B H : ℕ)
    (v : (Fin K → ℕ) × (Fin K → ℕ)) :=
  (∀ i,Nat.Prime (v.1 i)) ∧ (∀ i,Odd (v.1 i)) ∧ (∀ i,0<v.2 i) ∧
  (∑ i,visible B (v.1 i) (v.2 i))≤H ∧
  c*(∏ i,X (v.1 i) (some (v.2 i)))+d*(∏ i,Y (v.1 i) (some (v.2 i)))=2

private theorem configs (K k : ℕ) (d : ℚ) (d0 : 0<d) (d1 : d≤1) :
    ∃ B, {v | Config (K:=K) (X 2 (some k)) d B (k+OMA.WeightVal245212.val (k+1)) v}.Finite := by
  let c := X 2 (some k)
  have c0 := x_nonneg (by decide : 1<2) (some k)
  obtain ⟨B,δ,hδ,sep⟩ := visible_gap k K
  refine ⟨B,?_⟩
  obtain ⟨L,hL⟩ := exists_nat_gt (2/δ)
  have size (p e : Fin K → ℕ) (cfg : Config c d B (k+OMA.WeightVal245212.val (k+1)) (p,e)) (i : Fin K) : e i<L := by
    obtain ⟨hp,ho,_,he,eq⟩ := cfg
    have bound := sep p e hp ho he
    change δ≤|c*(∏ j,X (p j) (some (e j)))-2| at bound
    have y0 (j) := y_nonneg (hp j).one_lt (some (e j))
    have yp := prod_nonneg (s:=univ) (fun j _ => y0 j)
    have z := mul_nonneg d0.le yp
    change c*(∏ j,X (p j) (some (e j)))+d*(∏ j,Y (p j) (some (e j)))=2 at eq
    rw [abs_of_nonpos (by linarith only [eq,z])] at bound
    have upper : δ≤Y (p i) (some (e i)) := by
      apply (show δ≤d*∏ j,Y (p j) (some (e j)) by linarith only [eq,bound]).trans
      apply (mul_le_of_le_one_left yp d1).trans
      rw [←prod_erase_mul _ _ (mem_univ i)]
      exact mul_le_of_le_one_left (y0 i) (prod_le_one (fun j _ => y0 j)
        (fun j _ => y_one (hp j).one_lt _))
    have hh := OMA.CapOrder245212.y_short (hp i) (e i)
    have mult := mul_le_mul_of_nonneg_right upper (show 0≤(e i:ℚ)+1 by positivity)
    have le : (e i:ℚ)<2/δ := (lt_div_iff₀ hδ).mpr (by linarith only [hh,mult,hδ])
    exact_mod_cast le.trans hL
  apply Set.Finite.of_finite_fibers Prod.snd
  · apply (Set.Finite.pi' (fun _ : Fin K => Set.finite_Iio L)).subset
    rintro e ⟨⟨p,v⟩,h,rfl⟩
    exact size _ _ h
  · rintro e ⟨⟨p,v⟩,cfg,rfl⟩
    have finite := OMA.FixedExponents245212.finite_bases v cfg.2.2.1 c d 2 c0 d0
    apply (finite.image (fun q => (q,v))).subset
    rintro ⟨q,f⟩ ⟨hf,hv⟩
    have same : f=v := hv
    subst f
    exact ⟨q,⟨hf.1,hf.2.2.2.2⟩,rfl⟩

private theorem rank_finite (k K : ℕ) :
    ∃ B : ℕ,{m : ℕ | Odd m ∧ m.primeFactors.card=K ∧
      (∑ q∈m.primeFactors,visible B q (m.factorization q))≤k+OMA.WeightVal245212.val (k+1) ∧
      OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)}.Finite := by
  classical
  let c := X 2 (some k)
  let d := Y 2 (some k)
  have dp : 0<d := by
    dsimp [d]; rw [y_avg (by decide : 1<2)]
    exact div_pos (sum_pos' (fun i _ => by positivity) ⟨0,by simp,by simp⟩) (by positivity)
  obtain ⟨B,fin⟩ := configs K k d dp (y_one (by decide) _)
  refine ⟨B,?_⟩
  apply (fin.image (fun v => total v.1 v.2)).subset
  rintro m ⟨om,card,budget,eq⟩
  let S := m.primeFactors
  let p := S.orderEmbOfFin card
  let e (i : Fin K) := m.factorization (p i)
  have mem (i) : p i∈m.primeFactors := orderEmbOfFin_mem S card i
  have hp (i) := Nat.prime_of_mem_primeFactors (mem i)
  have op (i) := Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr om).of_dvd_right
    (Nat.dvd_of_mem_primeFactors (mem i)))
  have ep (i) := (hp i).factorization_pos_of_dvd om.pos.ne' (Nat.dvd_of_mem_primeFactors (mem i))
  have repr : total p e=m := by
    exact (Fintype.prod_equiv (S.orderIsoOfFin card).toEquiv _
      (fun j : S => j.val^(m.factorization j.val)) (fun _ => rfl)).trans
      (Nat.prod_primeFactors_coe_pow_factorization om.pos.ne').symm
  let w (i : Fin K) := visible B (p i) (e i)
  have wsum : ∑ i,w i = ∑ q∈m.primeFactors,visible B q (m.factorization q) := by
    exact (Fintype.sum_equiv (S.orderIsoOfFin card).toEquiv _
      (fun j : S => visible B j.val (m.factorization j.val)) (fun _ => rfl)).trans
      (Finset.sum_coe_sort S (fun q => visible B q (m.factorization q)))
  have norm := OMA.BoundedAtom245212.normalized_dyadic k p e hp op p.injective (by rw [repr];exact eq)
  exact ⟨(p,e),⟨hp,op,ep,wsum.le.trans budget,norm⟩,repr⟩

/-- Apart from finitely many solutions, bounded exceptional prime powers
must together supply enough powers of two for the fixed dyadic coefficient.
Large primes and large exponents do not count towards the required sum. -/
theorem finite_visible_budget (k K : ℕ) :
    ∃ B : ℕ,{m : ℕ | Odd m ∧ m.primeFactors.card≤K ∧
      (∑ q∈m.primeFactors,visible B q (m.factorization q))≤k+OMA.WeightVal245212.val (k+1) ∧
      OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)}.Finite := by
  choose L fin using rank_finite k
  let B := ∑ j∈range (K+1),L j
  refine ⟨B,((Set.finite_Iic K).biUnion (fun j _ => fin j)).subset ?_⟩
  rintro m ⟨om,card,v,eq⟩
  refine Set.mem_iUnion₂.mpr ⟨m.primeFactors.card,card,om,rfl,?_,eq⟩
  have less : L m.primeFactors.card≤B := single_le_sum (fun j _ => Nat.zero_le (L j))
    (mem_range.mpr (Nat.lt_succ_of_le card))
  apply (sum_le_sum (s:=m.primeFactors) (f:=fun q => visible (L m.primeFactors.card) q (m.factorization q))
    (g:=fun q => visible B q (m.factorization q)) ?_).trans v
  intro q hq
  unfold visible
  split_ifs <;> omega

/-- No upper bound on any prime or any individual exponent: only finitely
many positive odd parts with bounded rank and bounded total dyadic excess
can satisfy the original equality, for each fixed power of two. -/
theorem finite_budget (k K : ℕ) :
    {m : ℕ | Odd m ∧ m.primeFactors.card≤K ∧
      (∑ q∈m.primeFactors,excess (m.factorization q))≤k+OMA.WeightVal245212.val (k+1) ∧
      OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)}.Finite := by
  obtain ⟨B,fin⟩ := finite_visible_budget k K
  apply fin.subset
  rintro m ⟨om,card,v,eq⟩
  exact ⟨om,card,(sum_le_sum (fun q _ => show visible B q (m.factorization q)≤_ by
    unfold visible; split_ifs <;> omega)).trans v,eq⟩

end OMA.ParityBudget245212

end

section

/- A single bounded odd factor supplying the dyadic excess prevents
resonance with any coprime product of Euler numerators. -/
namespace OMA.RankThreeAnchor245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma

private theorem dyadic_weight (k : ℕ) : W (2^k)=k*2^(k+1)+1 := by
  rw [w_pow Nat.prime_two]
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [sum_range_succ _ (k+1),ih,pow_succ (2:ℕ) (k+1)]
    ring

private theorem weight_unit {r : ℕ} (pr : r.Prime) (a : ℕ) : r.Coprime (W (r^a)) := by
  apply pr.coprime_iff_not_dvd.mpr
  intro dv
  let : Fact r.Prime := ⟨pr⟩
  have zero := (ZMod.natCast_eq_zero_iff (W (r^a)) r).mpr dv
  rw [w_pow pr,sum_range_succ'] at zero
  push_cast at zero
  simp [pow_succ] at zero

theorem high {k r a : ℕ} (hr : 2 ≤ r)
    (hex : k + OMA.WeightVal245212.val (k+1) < OMA.ParityBudget245212.excess a) :
    W (2^k) < r^a := by
  have hv : k+2 ≤ (a+2).factorization 2 := by
    unfold OMA.ParityBudget245212.excess OMA.WeightVal245212.val at hex; omega
  have dv : 2^(k+2) ∣ a+2 := (pow_dvd_pow _ hv).trans (Nat.ordProj_dvd (a+2) 2)
  have bound := Nat.le_of_dvd (by omega : 0 < a+2) dv
  have size (j : ℕ) : 2*j+4 ≤ 2^(j+2) := by
    induction j with
    | zero => decide
    | succ j ih => rw [pow_succ 2 (j+2)]; omega
  have exp : 2*(k+1) ≤ a := by have := size k; omega
  have power := (Nat.pow_le_pow_right (by decide : 0<2) exp).trans (Nat.pow_le_pow_left hr a)
  apply lt_of_lt_of_le _ power
  rw [dyadic_weight,show 2*(k+1)=(k+1)+(k+1) by omega,pow_add 2 (k+1) (k+1)]
  have inc : k+1 < 2^(k+1) := Nat.lt_two_pow_self
  have gap := Nat.mul_le_mul_right (2^(k+1)) inc
  have nz := Nat.two_pow_pos (k+1)
  nlinarith only [gap,nz,inc]

/-- The Euler numerator U may contain any number of other primes. -/
theorem no_resonance {k r a U V : ℕ} (pr : r.Prime) (odd : r≠2)
    (cop : r.Coprime U) (large : W (2^k) < r^a) :
    W (2^k*r^a)*U ≠ 2*(2^k*r^a)*(σ 0 (2^k*r^a))*V := by
  intro eq
  have base := ((Nat.coprime_primes Nat.prime_two pr).mpr odd.symm).pow_left k
  rw [w_mult.map_mul_of_coprime (base.pow_right a),mul_assoc] at eq
  have d : r^a ∣ 2*(2^k*r^a)*(σ 0 (2^k*r^a))*V := by
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) _) _
  have fac := ((weight_unit pr a).mul_right cop).pow_left a
  have divides : r^a ∣ W (2^k) := fac.dvd_of_dvd_mul_right (eq ▸ d)
  have pos : 0 < W (2^k) := by rw [dyadic_weight]; omega
  exact large.not_ge (Nat.le_of_dvd pos divides)

end OMA.RankThreeAnchor245212

end

section

/- A cofactor whose prime-power denominator survives in the weighted
moment forces another bounded prime and exponent in any fixed-rank extension. -/
namespace OMA.CohortAtom245212
open Nat Finset Filter Topology OMA.Smooth245212 OMA.SquareCompact245212
open scoped ArithmeticFunction.sigma

private def UnitNum (r : ℕ) (x : ℚ) := ∃ U V : ℕ, r.Coprime U ∧ 0<V ∧ x=(U:ℚ)/V

private theorem one (r : ℕ) : UnitNum r 1 := ⟨1,1,by simp,by decide,by norm_num⟩

private theorem mul {r : ℕ} {x y : ℚ} (ux : UnitNum r x) (uy : UnitNum r y) : UnitNum r (x*y) := by
  obtain ⟨A,B,ca,hb,rfl⟩ := ux
  obtain ⟨U,V,cu,hv,rfl⟩ := uy
  exact ⟨A*U,B*V,ca.mul_right cu,Nat.mul_pos hb hv,by push_cast; ring⟩

private theorem cap {r p : ℕ} (pr : p.Prime) (cop : r.Coprime p) : UnitNum r (X p none) := by
  refine ⟨p,p-1,cop,by have := pr.one_lt; omega,?_⟩
  have pp : (1:ℚ)<p := by exact_mod_cast pr.one_lt
  simp only [X,Y,sub_zero,Nat.cast_sub pr.one_le,Nat.cast_one]
  field_simp [show (p:ℚ)-1≠0 by linarith]; ring

private theorem product {K r : ℕ} (x : Fin K → ℚ) (unit : ∀ i,UnitNum r (x i)) :
    UnitNum r (∏ i,x i) := by
  have aux (s : Finset (Fin K)) : UnitNum r (∏ i∈s,x i) := by
    induction s using Finset.induction_on with
    | empty => simpa using one r
    | @insert i s hi ih => simpa only [prod_insert hi] using mul (unit i) ih
  exact aux univ

theorem at_two {K : ℕ} (c d : ℚ) (d0 : 0≤d) (d1 : d≤1)
    (p e : ℕ → Fin K → ℕ) (hp : ∀ n i,Nat.Prime (p n i)) (large : ∀ n,∃ i,n<e n i)
    (eqn : ∀ n,c*(∏ i,X (p n i) (some (e n i)))+d*(∏ i,Y (p n i) (some (e n i)))=2) :
    Tendsto (fun n => c*∏ i,X (p n i) (some (e n i))) atTop (𝓝 2) := by
  have error (n : ℕ) : 0 ≤ d*∏ i,Y (p n i) (some (e n i)) ∧
      d*(∏ i,Y (p n i) (some (e n i))) ≤ 2/((n:ℚ)+1) := by
    have y0 (j) := y_nonneg (hp n j).one_lt (some (e n j))
    have pos := prod_nonneg (s:=univ) (fun j _ => y0 j)
    obtain ⟨i,gi⟩ := large n
    refine ⟨mul_nonneg d0 pos,(mul_le_of_le_one_left pos d1).trans ?_⟩
    calc
      _ ≤ Y (p n i) (some (e n i)) := by
        rw [←prod_erase_mul _ _ (mem_univ i)]
        exact mul_le_of_le_one_left (y0 i) (prod_le_one (fun j _ => y0 j) (fun j _ => y_one (hp n j).one_lt _))
      _ ≤ 2/((e n i:ℚ)+1) := ((lt_div_iff₀ (by positivity)).mpr (OMA.CapOrder245212.y_short (hp n i) _)).le
      _ ≤ _ := by gcongr
  have zero : Tendsto (fun n : ℕ => 2/((n:ℚ)+1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℚ)).const_mul 2
  have err := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds zero
    (fun n => (error n).1) (fun n => (error n).2)
  apply (show Tendsto (fun n => 2-d*∏ i,Y (p n i) (some (e n i))) atTop (𝓝 2) by
    simpa using (tendsto_const_nhds (x:=(2:ℚ))).sub err).congr
  intro n; linarith only [eqn n]

/-- Either all exponents are bounded, or at least one entire prime-power
factor has its base and exponent simultaneously bounded. -/
theorem alternative (K r : ℕ) (c d : ℚ) (d0 : 0≤d) (d1 : d≤1)
    (miss : ∀ U V : ℕ,r.Coprime U → 0<V → c*((U:ℚ)/V)≠2) :
    ∃ B : ℕ, ∀ p e : Fin K → ℕ, (∀ i,Nat.Prime (p i)) → (∀ i,Odd (p i)) → (∀ i,r.Coprime (p i)) →
      c*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2 →
      (∀ i,e i≤B) ∨ ∃ i,p i≤B ∧ e i≤B := by
  by_contra! bad
  choose p e hp ho cop eqn large avoid using bad
  let seq (n : ℕ) := (p n,e n)
  obtain ⟨g,sorted⟩ := wellQuasiOrdered_le.exists_monotone_subseq seq
  have points (i : Fin K) : ∃ x : ℚ,UnitNum r x ∧
      Tendsto (fun n => X (p (g n) i) (some (e (g n) i))) atTop (𝓝 x) := by
    apply factor_limit_restricted _ _ _ (fun _ _ le => (sorted _ _ le).1 i)
      (fun _ _ le => (sorted _ _ le).2 i) (fun n => hp (g n) i) (fun n => ho (g n) i) (one r)
    · intro P pr _ hP
      obtain ⟨n,hn⟩ := hP.exists
      exact cap pr (hn ▸ cop (g n) i)
    · intro P E hP hE
      have big := g.strictMono.tendsto_atTop.eventually (eventually_ge_atTop (max P E))
      obtain ⟨n,pn,en,gn⟩ := (hP.and (hE.and big)).exists
      change p (g n) i=P at pn
      change e (g n) i=E at en
      have a := avoid (g n) i
      rw [pn,en] at a
      exact False.elim ((not_lt_of_ge ((le_max_right P E).trans gn)) (a ((le_max_left P E).trans gn)))
  choose x ox conv using points
  obtain ⟨U,V,unit,vpos,prod⟩ := product x ox
  have limit := (tendsto_finsetProd univ (fun i _ => conv i)).const_mul c
  have two := (at_two c d d0 d1 p e hp large eqn).comp g.strictMono.tendsto_atTop
  exact miss U V unit vpos (prod ▸ tendsto_nhds_unique limit two)


/-- Positive exponents on a nonempty support turn the alternative into a
bounded pair: for bounded exponent vectors, only finitely many bases work. -/
theorem atom {K : ℕ} (pos : 0<K) (r : ℕ) (c d : ℚ) (c0 : 0≤c) (d0 : 0<d) (d1 : d≤1)
    (miss : ∀ U V : ℕ,r.Coprime U → 0<V → c*((U:ℚ)/V)≠2) :
    ∃ B : ℕ, ∀ p e : Fin K → ℕ, (∀ i,Nat.Prime (p i)) → (∀ i,Odd (p i)) → (∀ i,r.Coprime (p i)) →
      (∀ i,0<e i) → c*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2 →
      ∃ i,p i≤B ∧ e i≤B := by
  classical
  obtain ⟨L,alt⟩ := alternative K r c d d0.le d1 miss
  let F : Set (Fin K → ℕ) := {e | ∀ i,0<e i ∧ e i≤L}
  let bases (e : Fin K → ℕ) : Set (Fin K → ℕ) := {p | (∀ i,Nat.Prime (p i)) ∧
    c*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2}
  have cf : F.Finite := (Set.Finite.pi' (fun _ : Fin K => Set.finite_Iic L)).subset
    (fun _ h i => (h i).2)
  have bf := cf.biUnion (fun e he => (show (bases e).Finite from
    OMA.FixedExponents245212.finite_bases e (fun i => (he i).1) c d 2 c0 d0))
  obtain ⟨M,cap⟩ := (bf.biUnion (fun p _ => Set.finite_range p)).bddAbove
  refine ⟨max L M,?_⟩
  intro p e hp ho cop ep eq
  rcases alt p e hp ho cop eq with low | ⟨i,pi,ei⟩
  · let i : Fin K := ⟨0,pos⟩
    have ef : e∈F := fun j => ⟨ep j,low j⟩
    have member : p∈⋃ t∈F,bases t := Set.mem_iUnion₂.mpr ⟨e,ef,hp,eq⟩
    have pm := cap (Set.mem_iUnion₂.mpr ⟨p,member,i,rfl⟩)
    exact ⟨i,pm.trans (le_max_right _ _),(low i).trans (le_max_left _ _)⟩
  · exact ⟨i,pi.trans (le_max_left _ _),ei.trans (le_max_left _ _)⟩

theorem miss_core {k r a : ℕ} (pr : r.Prime) (odd : r≠2) (large : W (2^k)<r^a)
    (U V : ℕ) (unit : r.Coprime U) (vpos : 0<V) :
    (X 2 (some k)*X r (some a))*((U:ℚ)/V)≠2 := by
  intro eq
  let d2 := (k+1)*2^k
  let dr := (a+1)*r^a
  have fx : X 2 (some k)*(d2:ℚ)=W (2^k) := by simpa [d2] using x_factor Nat.prime_two k
  have fy : X r (some a)*(dr:ℚ)=W (r^a) := by simpa [dr] using x_factor pr a
  have diff := OMA.RankThreeAnchor245212.no_resonance pr odd unit large (V:=V)
  apply diff
  have cp := ((Nat.coprime_primes Nat.prime_two pr).mpr odd.symm).pow_left k
  rw [w_mult.map_mul_of_coprime (cp.pow_right a),ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
      (cp.pow_right a),ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_two,
      ArithmeticFunction.sigma_zero_apply_prime_pow pr]
  have rhs : 2*(2^k*r^a)*((k+1)*(a+1))*V=2*d2*dr*V := by unfold d2 dr; ring
  rw [rhs]
  have eq' : (X 2 (some k)*X r (some a))*U=2*V := by
    rw [←mul_div_assoc] at eq
    exact (div_eq_iff (by exact_mod_cast vpos.ne')).mp eq
  exact_mod_cast (show (W (2^k):ℚ)*W (r^a)*U=2*d2*dr*V by
    rw [←fx,←fy]; linear_combination ((d2:ℚ)*dr)*eq')

end OMA.CohortAtom245212

end

section

/- The largest prime in a nonempty Euler resonance must divide the
target numerator. Thus a fixed cofactor forces a bounded prime power
unless a remaining prime divides the cofactor's divisor count. -/
namespace OMA.CofactorPrimeChain245212
open Finset Nat Filter Topology OMA.Smooth245212 OMA.SquareCompact245212
open OMA.CohortAtom245212 (at_two)
open scoped ArithmeticFunction.sigma

private def EulerTerm (H u v : ℕ) : Prop :=
  (u=1 ∧ v=1) ∨ (u.Prime ∧ ¬u∣H ∧ v=u-1)

private theorem no_product {K A H : ℕ} (below : A<H) (u v : Fin K→ℕ)
    (terms : ∀i,EulerTerm H (u i) (v i)) :
    A*(∏ i,u i)≠H*(∏ i,v i) := by
  classical
  by_cases one : ∀i,u i=1
  · have neutral (i) : v i=1 := by
      rcases terms i with z|z
      · exact z.2
      · have := z.1.one_lt; rw [one i] at this; omega
    simpa [one,neutral] using below.ne
  push Not at one
  obtain ⟨j,hj⟩:=one
  obtain ⟨m,_,maxim⟩:=univ.exists_max_image u ⟨j,mem_univ _⟩
  have far : 1<u j := by rcases terms j with z|z; exact False.elim (hj z.1); exact z.1.one_lt
  have big := far.trans_le (maxim j (mem_univ _))
  rcases terms m with z|⟨pr,avoid,_⟩
  · omega
  intro eqn
  have dvd : u m∣H*(∏ i,v i) := eqn ▸ dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem u (mem_univ m)) A
  obtain target|rest:=pr.dvd_mul.mp dvd
  · exact avoid target
  obtain ⟨i,_,iv⟩:= (pr.prime.dvd_finsetProd_iff v).mp rest
  have upper := maxim i (mem_univ _)
  rcases terms i with z|z
  · rw [z.2] at iv
    exact (not_le_of_gt big) (Nat.le_of_dvd (by decide) iv)
  · have pos := z.1.one_lt
    have gap : 0<v i ∧ v i<u m := by rw [z.2.2];omega
    exact gap.2.not_ge (Nat.le_of_dvd gap.1 iv)

private theorem no_limit {K A T : ℕ} (tpos : 0<T) (below : A<2*T) (x : Fin K→ℚ)
    (repr : ∀i,∃ u v : ℕ,EulerTerm (2*T) u v ∧ x i=(u:ℚ)/v) :
    ((A:ℚ)/T)*(∏ i,x i)≠2 := by
  classical
  choose u v uv frac using repr
  have pos (i) : 0<v i := by
    rcases uv i with z|z
    · rw [z.2];decide
    · rw [z.2.2];have := z.1.one_lt;omega
  have nonzero : (∏ i,(v i:ℚ))≠0 := (prod_pos (fun i _=>by exact_mod_cast pos i)).ne'
  have original := no_product below u v uv
  intro bad
  simp only [frac,prod_div_distrib] at bad
  field_simp [nonzero,show (T:ℚ)≠0 by exact_mod_cast tpos.ne'] at bad
  apply original
  exact_mod_cast (show (A:ℚ)*(∏ i,(u i:ℚ))=(2*T)*(∏ i,(v i:ℚ)) by linarith only [bad])

private theorem cap_repr {p H : ℕ} (pr : p.Prime) (avoid : ¬p∣H) :
    ∃ u v : ℕ,EulerTerm H u v ∧ X p none=(u:ℚ)/v := by
  refine ⟨p,p-1,Or.inr ⟨pr,avoid,rfl⟩,?_⟩
  have pp : (1:ℚ)<p := by exact_mod_cast pr.one_lt
  simp only [X,Y,sub_zero,Nat.cast_sub pr.one_le,Nat.cast_one]
  field_simp [show (p:ℚ)-1≠0 by linarith];ring

theorem alternative (K A T : ℕ) (tpos : 0<T) (below : A<2*T)
    (d : ℚ) (d0 : 0≤d) (d1 : d≤1) :
    ∃ B : ℕ, ∀ p e : Fin K→ℕ, (∀i,(p i).Prime) → (∀i,Odd (p i)) → (∀i,¬p i∣2*T) →
      ((A:ℚ)/T)*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2 →
      (∀i,e i≤B) ∨ ∃i,p i≤B ∧ e i≤B := by
  by_contra! bad
  choose p e hp ho avoid eqn large leave using bad
  let seq (n : ℕ) := (p n,e n)
  obtain ⟨g,sorted⟩ := wellQuasiOrdered_le.exists_monotone_subseq seq
  have points (i : Fin K) : ∃ x : ℚ,(∃ u v : ℕ,EulerTerm (2*T) u v ∧ x=(u:ℚ)/v) ∧
      Tendsto (fun n => X (p (g n) i) (some (e (g n) i))) atTop (𝓝 x) := by
    apply factor_limit_restricted _ _ _ (fun _ _ le => (sorted _ _ le).1 i)
      (fun _ _ le => (sorted _ _ le).2 i) (fun n=>hp (g n) i) (fun n=>ho (g n) i)
      ⟨1,1,Or.inl ⟨rfl,rfl⟩,by norm_num⟩
    · intro P pr _ fixed
      obtain ⟨n,same⟩:=fixed.exists
      exact cap_repr pr (same ▸ avoid (g n) i)
    · intro P E hP hE
      have big:=g.strictMono.tendsto_atTop.eventually (eventually_ge_atTop (max P E))
      obtain ⟨n,pn,en,gn⟩:=(hP.and (hE.and big)).exists
      change p (g n) i=P at pn
      change e (g n) i=E at en
      have both:=leave (g n) i
      rw [pn,en] at both
      exact False.elim ((not_lt_of_ge ((le_max_right P E).trans gn)) (both ((le_max_left P E).trans gn)))
  choose x ox conv using points
  have limit:=(tendsto_finsetProd univ (fun i _=>conv i)).const_mul ((A:ℚ)/T)
  have two:=(OMA.CohortAtom245212.at_two _ d d0 d1 p e hp large eqn).comp g.strictMono.tendsto_atTop
  exact no_limit tpos below x ox (tendsto_nhds_unique limit two)

end OMA.CofactorPrimeChain245212

end

section

/- A fixed-rank family with no cross divisibility between its prime
bases and its exponent lengths is finite. The induction absorbs one
bounded prime power into the cofactor. -/
namespace OMA.CofactorCrossCount245212
open Finset Nat OMA.Smooth245212
open OMA.FixedExponents245212 (y_pos)
open scoped ArithmeticFunction.sigma

def balance {K : ℕ} (A T : ℕ) (d : ℚ) (p e : Fin K→ℕ) : Prop :=
  ((A:ℚ)/T)*(∏ i,X (p i) (some (e i)))+d*(∏ i,Y (p i) (some (e i)))=2

structure Admissible {K : ℕ} (T : ℕ) (p e : Fin K→ℕ) : Prop where
  prime (i) : (p i).Prime
  odd (i) : Odd (p i)
  positive (i) : 0<e i
  distinct : Function.Injective p
  avoid (i) : ¬p i∣2*T
  cross (i j) : i≠j → ¬p i∣e j+1

private theorem below {K A T : ℕ} {d : ℚ} {p e : Fin K→ℕ}
    (tp : 0<T) (dp : 0<d) (ok : Admissible T p e) (eqn : balance A T d p e) : A<2*T := by
  have one (i) : 1≤X (p i) (some (e i)) :=
    le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (y_one (ok.prime i).one_lt _))
      (sub_nonneg.mpr (by exact_mod_cast (ok.prime i).one_le)))
  have all : 1≤∏i,X (p i) (some (e i)) := by
    calc
      1 = ∏ _i : Fin K,(1:ℚ) := by simp
      _ ≤ _ := prod_le_prod (fun _ _=>by norm_num) (fun i _=>one i)
  have yp := prod_pos (s:=univ) (fun i _=>OMA.FixedExponents245212.y_pos (ok.prime i) (e i))
  have c0 : 0≤(A:ℚ)/T := by positivity
  have small : (A:ℚ)/T<2 := by unfold balance at eqn;nlinarith only [eqn,mul_pos dp yp,mul_nonneg c0 (sub_nonneg.mpr all)]
  exact_mod_cast (div_lt_iff₀ (by exact_mod_cast tp : (0:ℚ)<T)).mp small

private theorem atom {K A T : ℕ} {d : ℚ} (kp : 0<K) (tp : 0<T) (cut : A<2*T)
    (dp : 0<d) (ds : d≤1) :
    ∃ B : ℕ, ∀ p e : Fin K→ℕ, Admissible T p e → balance A T d p e → ∃i,p i≤B ∧ e i≤B := by
  classical
  obtain ⟨L,alt⟩:=OMA.CofactorPrimeChain245212.alternative K A T tp cut d dp.le ds
  let F : Set (Fin K→ℕ) := {e | ∀i,0<e i ∧ e i≤L}
  let bases (e : Fin K→ℕ) : Set (Fin K→ℕ) := {p | (∀i,(p i).Prime) ∧ balance A T d p e}
  have cf : F.Finite := (Set.Finite.pi' (fun _ : Fin K=>Set.finite_Iic L)).subset
    (fun _ h i=>(h i).2)
  have bf := cf.biUnion (fun e he=>(show (bases e).Finite from
    OMA.FixedExponents245212.finite_bases e (fun i=>(he i).1) ((A:ℚ)/T) d 2 (by positivity) dp))
  obtain ⟨M,cap⟩:=(bf.biUnion (fun p _=>Set.finite_range p)).bddAbove
  refine ⟨max L M,?_⟩
  intro p e ok eqn
  rcases alt p e ok.prime ok.odd ok.avoid eqn with low|⟨i,pi,ei⟩
  · let i : Fin K:=⟨0,kp⟩
    have ef : e∈F:=fun j=>⟨ok.positive j,low j⟩
    have mem : p∈⋃ t∈F,bases t:=Set.mem_iUnion₂.mpr ⟨e,ef,ok.prime,eqn⟩
    have pm:=cap (Set.mem_iUnion₂.mpr ⟨p,mem,i,rfl⟩)
    exact ⟨i,pm.trans (le_max_right _ _),(low i).trans (le_max_left _ _)⟩
  · exact ⟨i,pi.trans (le_max_left _ _),ei.trans (le_max_left _ _)⟩

private def scale (p e : ℕ) := (e+1)*p^e

private theorem peel {K A T : ℕ} {d : ℚ} {p e : Fin (K+1)→ℕ} (j : Fin (K+1))
    (tp : 0<T) (ok : Admissible T p e) (eqn : balance A T d p e) :
    Admissible (T*scale (p j) (e j)) (p ∘ j.succAbove) (e ∘ j.succAbove) ∧
    balance (A*W (p j^e j)) (T*scale (p j) (e j)) (d*Y (p j) (some (e j)))
      (p ∘ j.succAbove) (e ∘ j.succAbove) := by
  constructor
  · refine ⟨fun i=>ok.prime _,fun i=>ok.odd _,fun i=>ok.positive _,ok.distinct.comp j.succAbove_right_injective,?_,?_⟩
    · intro i dv
      let l:=j.succAbove i
      change p l∣2*(T*scale (p j) (e j)) at dv
      rw [←mul_assoc] at dv
      rcases (ok.prime l).dvd_mul.mp dv with a|a
      · exact ok.avoid l a
      rcases (ok.prime l).dvd_mul.mp a with b|b
      · exact ok.cross l j (Fin.succAbove_ne _ _) b
      exact Fin.succAbove_ne j i (ok.distinct ((prime_dvd_prime_iff_eq (ok.prime l) (ok.prime j)).mp
        ((ok.prime l).dvd_of_dvd_pow b)))
    · intro i k neq
      exact ok.cross _ _ (fun same=>neq (j.succAbove_right_injective same))
  · have hscale : 0<scale (p j) (e j) := by unfold scale;have:= (ok.prime j).pos;positivity
    have fx:=x_factor (ok.prime j) (e j)
    have val : ((A*W (p j^e j):ℕ):ℚ)/(T*scale (p j) (e j):ℕ)=((A:ℚ)/T)*X (p j) (some (e j)) := by
      push_cast
      field_simp [show (scale (p j) (e j):ℚ)≠0 by exact_mod_cast hscale.ne',
        show (T:ℚ)≠0 by exact_mod_cast tp.ne']
      unfold scale
      push_cast
      linear_combination -(A:ℚ)*fx
    unfold balance at eqn ⊢
    rw [Fin.prod_univ_succAbove (fun i=>X (p i) (some (e i))) j,
      Fin.prod_univ_succAbove (fun i=>Y (p i) (some (e i))) j] at eqn
    simpa only [val,Function.comp_apply,mul_assoc] using eqn

theorem bounded (K : ℕ) : ∀ (A T : ℕ) (d : ℚ), 0<T → 0<d → d≤1 →
    ∃ B : ℕ,∀ p e : Fin K→ℕ, Admissible T p e → balance A T d p e → total p e≤B := by
  classical
  induction K with
  | zero =>
    intro A T d _ _ _
    exact ⟨1,fun p e _ _=>by simp [total]⟩
  | succ K ih =>
    intro A T d tp dp ds
    by_cases cut : A<2*T
    · obtain ⟨L,cap⟩:=atom (K:=K+1) (Nat.succ_pos _) tp cut dp ds
      let bound (r z : ℕ) : ℕ := if good : r.Prime then
        Classical.choose (ih (A*W (r^z)) (T*scale r z) (d*Y r (some z))
          (by unfold scale;have:=good.pos;positivity) (mul_pos dp (OMA.FixedExponents245212.y_pos good z))
          ((mul_le_of_le_one_right dp.le (y_one good.one_lt _)).trans ds)) else 0
      let maxRest:=((range (L+1)).product (range (L+1))).sup (fun k=>bound k.1 k.2)
      refine ⟨(L+1)^L*maxRest,?_⟩
      intro p e ok eqn
      obtain ⟨j,pj,ej⟩:=cap p e ok eqn
      have rest:=peel j tp ok eqn
      have rule : total (p ∘ j.succAbove) (e ∘ j.succAbove)≤bound (p j) (e j) := by
        unfold bound
        rw [dif_pos (ok.prime j)]
        exact Classical.choose_spec (ih (A*W (p j^e j)) (T*scale (p j) (e j)) (d*Y (p j) (some (e j)))
          (by unfold scale;have:=(ok.prime j).pos;positivity)
          (mul_pos dp (OMA.FixedExponents245212.y_pos (ok.prime j) _))
          ((mul_le_of_le_one_right dp.le (y_one (ok.prime j).one_lt _)).trans ds))
          _ _ rest.1 rest.2
      have member : (p j,e j)∈(range (L+1)).product (range (L+1)) :=
        mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩
      have hi : bound (p j) (e j) ≤ maxRest := le_sup (f:=fun k : ℕ×ℕ=>bound k.1 k.2) member
      have pw : p j^e j≤(L+1)^L := (Nat.pow_le_pow_left (pj.trans (Nat.le_succ L)) _).trans
        (Nat.pow_le_pow_right (Nat.succ_pos _) ej)
      rw [total,Fin.prod_univ_succAbove _ j]
      exact Nat.mul_le_mul pw (rule.trans hi)
    · exact ⟨0,fun p e ok eqn=>False.elim (cut (below tp dp ok eqn))⟩

end OMA.CofactorCrossCount245212

end

section

/- Finite original A245212 solutions of bounded odd-prime rank
when no odd prime divides another exponent length or the divisor count
of the fixed cofactor. -/
namespace OMA.CofactorCrossOriginal245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.CofactorCrossCount245212
open scoped ArithmeticFunction.sigma

theorem sigma_bound {h : ℕ} (pos : 0<h) : σ 1 h≤h*σ 0 h := by
  rw [sigma_one_apply,sigma_zero_apply,mul_comm]
  simpa using (sum_le_card_nsmul h.divisors (fun d : ℕ=>d) h (fun d hd=>
    Nat.le_of_dvd pos (Nat.mem_divisors.mp hd).1))

theorem normalized_extension {ι : Type*} [Fintype ι] {h : ℕ} {p e : ι→ℕ} (hh : 0<h) (pr : ∀i,(p i).Prime)
    (unique : Function.Injective p) (cop : ∀i,h.Coprime (p i))
    (eqn : OeisA245212.a (h*total p e)=(σ 1 (h*total p e):ℤ)) :
    ((W h:ℚ)/(h*σ 0 h:ℕ))*(∏i,X (p i) (some (e i)))+
      ((σ 1 h:ℚ)/(h*σ 0 h:ℕ))*(∏i,Y (p i) (some (e i)))=2 := by
  classical
  let z (i : ι):=p i^e i
  have pair : (↑(univ : Finset ι) : Set ι).Pairwise (fun i j=>(z i).Coprime (z j)) := by
    intro i _ j _ different
    exact (((coprime_primes (pr i) (pr j)).mpr (fun same=>different (unique same))).pow_left _).pow_right _
  have hc : h.Coprime (total p e) := coprime_prod_right_iff.mpr (fun i _=>(cop i).pow_right _)
  have nz : total p e≠0 := prod_ne_zero_iff.mpr (fun i _=>pow_ne_zero _ (pr i).ne_zero)
  have bal:=OMA.Abundance245212.balance (mul_ne_zero hh.ne' nz) eqn
  rw [w_mult.map_mul_of_coprime hc,isMultiplicative_sigma.map_mul_of_coprime hc,
    isMultiplicative_sigma.map_mul_of_coprime hc] at bal
  have wp:=IsMultiplicative.map_prod z w_mult univ pair
  have sp:=IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=1)) univ pair
  have tp:=IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=0)) univ pair
  change W (total p e)=_ at wp
  change σ 1 (total p e)=_ at sp
  change σ 0 (total p e)=_ at tp
  simp only [z,sigma_zero_apply_prime_pow (pr _)] at tp
  let mass : ℚ:=∏ i,(((e i:ℕ):ℚ)+1)*(p i:ℚ)^e i
  have tax : mass = (total p e:ℚ)*(σ 0 (total p e):ℚ) := by
    rw [tp,total];push_cast;dsimp [mass];rw [prod_mul_distrib];ring
  have positive : 0 < mass := by
    apply prod_pos
    intro i _
    have := (pr i).pos
    positivity
  have wprod : (∏ i,X (p i) (some (e i)))*mass=(W (total p e):ℚ) := by
    rw [wp,←prod_mul_distrib];push_cast
    exact prod_congr rfl (fun i _=>x_factor (pr i) (e i))
  have sprod : (∏ i,Y (p i) (some (e i)))*mass=(σ 1 (total p e):ℚ) := by
    rw [sp,←prod_mul_distrib];push_cast
    exact prod_congr rfl (fun i _=>y_factor (pr i) (e i))
  have D : 0<h*σ 0 h := Nat.mul_pos hh (sigma_pos 0 h hh.ne')
  have rat:=congrArg ((↑):ℕ→ℚ) bal
  push_cast at rat
  apply mul_right_cancel₀ (b:=mass) positive.ne'
  rw [add_mul,mul_assoc,mul_assoc,wprod,sprod,tax]
  field_simp [show ((h*σ 0 h:ℕ):ℚ)≠0 by exact_mod_cast D.ne']
  push_cast
  linear_combination rat

theorem original (h K : ℕ) (hh : 0<h) :
    ∃ B : ℕ,∀ p e : Fin K→ℕ, (∀i,(p i).Prime) → (∀i,Odd (p i)) → (∀i,h.Coprime (p i)) →
      Function.Injective p → (∀i,0<e i) → (∀i,¬p i∣σ 0 h) → (∀i j,i≠j → ¬p i∣e j+1) →
      OeisA245212.a (h*total p e)=(σ 1 (h*total p e):ℤ) → h*total p e≤B := by
  let T:=h*σ 0 h
  have tp : 0<T:=mul_pos hh (sigma_pos 0 h hh.ne')
  have dp : (0:ℚ)<(σ 1 h:ℚ)/T := div_pos (by exact_mod_cast sigma_pos 1 h hh.ne') (by exact_mod_cast tp)
  have ds : (σ 1 h:ℚ)/T≤1 := (div_le_one (by exact_mod_cast tp)).mpr (by exact_mod_cast sigma_bound hh)
  obtain ⟨L,cap⟩:=bounded K (W h) T _ tp dp ds
  refine ⟨h*L,?_⟩
  intro p e pr odd cop inj ep avoid cross eqn
  apply Nat.mul_le_mul_left h
  apply cap p e ⟨pr,odd,ep,inj,?_,cross⟩ (normalized_extension hh pr inj cop eqn)
  intro i dv
  rcases (pr i).dvd_mul.mp dv with two|rhs
  · have same:=(prime_dvd_prime_iff_eq (pr i) prime_two).mp two
    obtain ⟨k,hk⟩:=odd i
    omega
  rcases (pr i).dvd_mul.mp rhs with divides|divides
  · exact ((pr i).coprime_iff_not_dvd.mp (cop i).symm) divides
  · exact avoid i divides

end OMA.CofactorCrossOriginal245212

end

section

/- An explicit whole-prime-power bound in the nonresonant case.
Replace large bases by 1 and small bases with large exponents by their
Euler limits. The explicitly separated subproduct cannot approximate a
solution this closely. -/
namespace OMA.CofactorEffectiveAtom245212
open Finset Nat OMA.Smooth245212 OMA.CofactorEulerSeparation245212

theorem product_error {ι : Type*} [DecidableEq ι] (s : Finset ι) (x z : ι→ℚ)
    {w : ℚ} (wp : 0≤w) (bounds : ∀i∈s,0≤x i ∧ x i≤2 ∧ 0≤z i ∧ z i≤2 ∧ |x i-z i|≤w) :
    |(∏i∈s,x i)-(∏i∈s,z i)| ≤ s.card*(2:ℚ)^s.card*w := by
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s fresh ih=>
    let X:=∏j∈s,x j
    let Z:=∏j∈s,z j
    have b:=bounds i (mem_insert_self ..)
    have bs (j) (hj:j∈s):=bounds j (mem_insert_of_mem hj)
    have z0 : 0≤Z:=prod_nonneg (fun j hj=>(bs j hj).2.2.1)
    have z2 : Z≤(2:ℚ)^s.card := by
      simpa [Z] using prod_le_prod (fun j hj=>(bs j hj).2.2.1) (fun j hj=>(bs j hj).2.2.2.1)
    have old:=ih bs
    change |X-Z|≤_ at old
    rw [prod_insert fresh,prod_insert fresh,card_insert_of_notMem fresh,Nat.cast_add,Nat.cast_one,pow_succ]
    change |x i*X-z i*Z|≤_
    have tri:=abs_add_le (x i*(X-Z)) ((x i-z i)*Z)
    rw [show x i*(X-Z)+(x i-z i)*Z=x i*X-z i*Z by ring,abs_mul,abs_of_nonneg b.1,
      abs_mul,abs_of_nonneg z0] at tri
    have l:=mul_le_mul b.2.1 old (abs_nonneg _) (by decide : (0:ℚ)≤2)
    have r:=mul_le_mul b.2.2.2.2 z2 z0 wp
    nlinarith only [tri,l,r,mul_nonneg (pow_nonneg (by decide : (0:ℚ)≤2) s.card) wp]

private def factor (p : ℕ) : ℚ := (p:ℚ)/(p-1:ℕ)

private theorem local_factor {p e : ℕ} (hp : p.Prime) :
    1≤X p (some e) ∧ X p (some e)≤factor p ∧ factor p≤2 ∧
    factor p-X p (some e)=Y p (some e)/((p:ℚ)-1) := by
  have hi : (1:ℚ)<p := by exact_mod_cast hp.one_lt
  have den : (0:ℚ)<p-1 := by linarith
  have two : (2:ℚ)≤p := by exact_mod_cast hp.two_le
  have y0:=y_nonneg hp.one_lt (some e)
  have y1:=y_one hp.one_lt (some e)
  have diff : factor p-X p (some e)=Y p (some e)/((p:ℚ)-1) := by
    unfold factor X;push_cast [Nat.cast_sub hp.one_le];field_simp;ring
  refine ⟨le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr y1) den.le),?_,?_,diff⟩
  · linarith only [diff,div_nonneg y0 den.le]
  · unfold factor;push_cast [Nat.cast_sub hp.one_le];apply (div_le_iff₀ den).mpr;linarith

private theorem near {p e M : ℕ} (hp : p.Prime) (avoid : p≤M+1 → M<e) :
    |X p (some e)-(if p≤M+1 then factor p else 1)|≤2/((M:ℚ)+1) := by
  obtain ⟨low,hi,_,diff⟩:=local_factor (e:=e) hp
  have h2 : (2:ℚ)≤p:=by exact_mod_cast hp.two_le
  have den : (0:ℚ)<p-1:=by linarith
  split
  next small=>
    rw [abs_of_nonpos (sub_nonpos.mpr hi),neg_sub,diff]
    have ye:=OMA.CapOrder245212.y_short hp e
    have big : (M:ℚ)+1≤e+1 := by exact_mod_cast (by have:=avoid small;omega : M+1≤e+1)
    have y0:=y_nonneg hp.one_lt (some e)
    calc
      Y p (some e)/((p:ℚ)-1) ≤ Y p (some e) := div_le_self y0 (by linarith)
      _ ≤ _ := (le_div_iff₀ (by positivity)).mpr ((mul_le_mul_of_nonneg_left big y0).trans ye.le)
  next large=>
    rw [abs_of_nonneg (sub_nonneg.mpr low)]
    unfold X
    have bound : (M:ℚ)+1≤p-1 := by
      have strong : (M:ℚ)+2≤p:=by exact_mod_cast (show M+2≤p by omega)
      linarith
    have y0:=y_nonneg hp.one_lt (some e)
    rw [add_sub_cancel_left]
    calc
      _ ≤ 1/((p:ℚ)-1) := div_le_div_of_nonneg_right (sub_le_self _ y0) den.le
      _ ≤ 1/((M:ℚ)+1) := one_div_le_one_div_of_le (by positivity) bound
      _ ≤ _ := by gcongr; norm_num

def threshold (A S K : ℕ) := budget A K*(2*A*K*2^K+2*S)

theorem alternative (A S H : ℕ) (s : Finset ℕ) (e : ℕ→ℕ) (pr : ∀p∈s,p.Prime)
    (apart : miss A H s)
    (bal : (A:ℚ)*(∏p∈s,X p (some (e p)))+S*(∏p∈s,Y p (some (e p)))=H) :
    let M:=threshold A S s.card
    (∀p∈s,e p≤M) ∨ ∃p∈s,p≤M+1 ∧ e p≤M := by
  classical
  let K:=s.card
  let M:=threshold A S K
  change (∀p∈s,e p≤M) ∨ ∃p∈s,p≤M+1 ∧ e p≤M
  by_cases allSmall : ∀p∈s,e p≤M
  · exact Or.inl allSmall
  right
  by_contra no
  push Not at allSmall
  obtain ⟨j,hj,large⟩:=allSmall
  have avoid (p) (hp:p∈s) (low:p≤M+1) : M<e p := by
    by_contra! short
    exact no ⟨p,hp,low,short⟩
  let z (p : ℕ) : ℚ:=if p≤M+1 then factor p else 1
  let t:=s.filter (fun p=>p≤M+1)
  have sub : t⊆s:=filter_subset _ _
  have proxy : (∏p∈s,z p)=(num t:ℚ)/den t := by
    rw [show (∏p∈s,z p)=∏p∈t,factor p by simp [z,t,prod_filter]]
    unfold factor num den
    push_cast
    rw [prod_div_distrib]
  have sep:=rational_gap (A:=A) (H:=H) (K:=K) (s:=t) (card_le_card sub)
    (fun p hp=>(pr p (sub hp)).two_le) (fun u hu=>apart u (hu.trans sub))
  rw [←proxy] at sep
  have feat:=product_error s (fun p=>X p (some (e p))) z (w:=2/((M:ℚ)+1)) (by positivity)
    (fun p hp=>by
      have loc:=local_factor (e:=e p) (pr p hp)
      refine ⟨zero_le_one.trans loc.1,loc.2.1.trans loc.2.2.1,?_,?_,near (pr p hp) (avoid p hp)⟩
      · dsimp [z];split <;> first | exact (zero_le_one.trans loc.1).trans loc.2.1 | norm_num
      · dsimp [z];split <;> first | exact loc.2.2.1 | norm_num)
  let PX:=∏p∈s,X p (some (e p))
  let PY:=∏p∈s,Y p (some (e p))
  let Z:=∏p∈s,z p
  have y0 : 0≤PY:=prod_nonneg (fun p hp=>y_nonneg (pr p hp).one_lt _)
  have ylow : PY≤Y j (some (e j)) := by
    dsimp [PY];rw [←prod_erase_mul _ _ hj]
    exact mul_le_of_le_one_left (y_nonneg (pr j hj).one_lt _) (prod_le_one
      (fun p hp=>y_nonneg (pr p (mem_of_mem_erase hp)).one_lt _)
      (fun p hp=>y_one (pr p (mem_of_mem_erase hp)).one_lt _))
  have ycut := OMA.CapOrder245212.y_short (pr j hj) (e j)
  let L:ℚ:=M+1
  have lp : 0<L:=by dsimp [L];positivity
  have yl : PY*L≤2 := (mul_le_mul ylow (show L≤(e j:ℚ)+1 by dsimp [L];exact_mod_cast Nat.succ_le_succ large.le)
    lp.le (y_nonneg (pr j hj).one_lt _)).trans ycut.le
  change |PX-Z|≤K*(2:ℚ)^K*(2/L) at feat
  have xl : |PX-Z| * L≤K*2^K*2 := by
    apply (le_div_iff₀ lp).mp
    simpa [div_eq_mul_inv,mul_assoc] using feat
  change (A:ℚ)*PX+S*PY=H at bal
  change 1≤(budget A K:ℚ)*|(A:ℚ)*Z-H| at sep
  have tri:=abs_add_le ((A:ℚ)*(PX-Z)) ((S:ℚ)*PY)
  rw [show (A:ℚ)*(PX-Z)+S*PY=H-A*Z by linarith only [bal],abs_sub_comm (H:ℚ)] at tri
  simp only [abs_mul,abs_of_nonneg (Nat.cast_nonneg A : (0:ℚ)≤A),
    abs_of_nonneg (Nat.cast_nonneg S : (0:ℚ)≤S),abs_of_nonneg y0] at tri
  have distance : |(A:ℚ)*Z-H| * L≤2*A*K*2^K+2*S := by
    nlinarith only [mul_le_mul_of_nonneg_right tri lp.le,
      mul_le_mul_of_nonneg_left xl (Nat.cast_nonneg A : (0:ℚ)≤A),
      mul_le_mul_of_nonneg_left yl (Nat.cast_nonneg S : (0:ℚ)≤S)]
  have bad : L≤(budget A K:ℚ)*(2*A*K*2^K+2*S) := by
    nlinarith only [mul_le_mul_of_nonneg_right sep lp.le,
      mul_le_mul_of_nonneg_left distance (Nat.cast_nonneg (budget A K) : (0:ℚ)≤_)]
  change ((threshold A S K:ℕ):ℚ)+1≤_ at bad
  unfold threshold at bad
  push_cast at bad
  linarith

end OMA.CofactorEffectiveAtom245212

end

section

/- A missing interval among four ordered cutoffs makes the local tail
smaller than a nonzero integer's reciprocal denominator. -/
namespace OMA.ThreeMovingStep245212
open Nat Finset OMA.ThreeMovingLocal245212 OMA.ThreeMovingGap245212 OMA.ThreeMovingScalar245212
open OMA.CofactorEffectiveAtom245212 (product_error)

private theorem integer_gap (c : Family) (bits : Fin 3→Bool) (f g : ℕ)
    (different : (f+g)*dust c bits ≠ f*NX c bits+g*NY c bits) :
    (1:ℚ)≤|score f g (x' c bits) (y' c bits)-(f+g:ℕ)| * dust c bits := by
  let B:=dust c bits
  let T:=f*NX c bits+g*NY c bits
  let L:ℤ:=(T:ℤ)-((f+g)*B:ℕ)
  have nz : L≠0 := fun h => different (by exact_mod_cast (sub_eq_zero.mp h).symm)
  have la : (1:ℤ)≤|L| := by have:=abs_pos.mpr nz;omega
  have raw : (1:ℚ)≤|(T:ℚ)-((f+g)*B:ℕ)| := by dsimp [L] at la;exact_mod_cast la
  have ab:=congrArg (fun w:ℚ=>|w|) (show (score f g (x' c bits) (y' c bits)-(f+g:ℕ))*B =
      (T:ℚ)-((f+g)*B:ℕ) by rw [sub_mul];push_cast;rw [show score f g (x' c bits) (y' c bits)*B=(T:ℚ) from clear ..])
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg B : (0:ℚ)≤B)] at ab
  exact ab.trans_ge raw

private theorem difference (c : Family) (b : Fin 3→Bool) (f g N : ℕ) (n0 : 0<N)
    (space : ∀i,N ≤ (if b i then (c.p i)^(c.e i) else c.p i)) :
    |score f g (x' c b) (y' c b)-score f g (exactX c) (exactY c)|≤48*((f:ℚ)+g)/N := by
  have bp (i) := bounds (c.prime i) (c.positive i) c.mp (c.lengths i).1 (b i)
  have er (i) := error (c.prime i) (c.positive i) n0 (b i) (space i)
  have eps : (0:ℚ)≤2/N := by positivity
  have one : 2/(c.m:ℚ)≤2 := div_le_self (by decide) (by exact_mod_cast c.mp)
  have x:=OMA.CofactorEffectiveAtom245212.product_error (univ:Finset (Fin 3)) (exactX c) (x' c b) eps
    (fun i _=>⟨zero_le_one.trans (bp i).1,(bp i).2.1,zero_le_one.trans (bp i).2.2.2.2.1,
      (bp i).2.2.2.2.2.1,(er i).1⟩)
  have y:=OMA.CofactorEffectiveAtom245212.product_error (univ:Finset (Fin 3)) (exactY c) (y' c b) eps
    (fun i _=>⟨(bp i).2.2.1,(bp i).2.2.2.1.trans one,(bp i).2.2.2.2.2.2.1,
      (bp i).2.2.2.2.2.2.2.trans one,(er i).2⟩)
  norm_num at x y
  dsimp [score]
  rw [abs_sub_comm]
  calc
    _ = |(f:ℚ)*((∏i,exactX c i)-∏i,x' c b i)+(g:ℚ)*((∏i,exactY c i)-∏i,y' c b i)| := by congr 1;ring
    _ ≤ _ := (abs_add_le ..).trans (by
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg f : (0:ℚ)≤f),abs_mul,
        abs_of_nonneg (Nat.cast_nonneg g : (0:ℚ)≤g)]
      simp only [div_eq_mul_inv] at x y ⊢
      nlinarith only [mul_le_mul_of_nonneg_left x (Nat.cast_nonneg f : (0:ℚ)≤f),
        mul_le_mul_of_nonneg_left y (Nat.cast_nonneg g : (0:ℚ)≤g)])

theorem contradiction (c : Family) (f g l x : ℕ) (gp : 0<g) (fg : c.k*g≤f)
    (frac : f+g=(c.k+1)*l) (unit : ∀i,¬c.p i∣l)
    (big : 128≤x) (cf : f+g≤x) (cl : c.L≤x)
    (powers : ∀i,x^budget≤(c.p i)^(c.e i))
    (actual : score f g (exactX c) (exactY c)≤(f+g:ℕ))
    (close : |score f g (exactX c) (exactY c)-(f+g:ℕ)| ≤ 1/((x^budget:ℕ):ℚ)) : False := by
  obtain ⟨j,band⟩:=empty_interval x (by omega) c.p
  let Q:=cut x j.val
  let N:=cut x (j.val+1)
  let b (i:Fin 3):Bool:=decide (c.p i≤Q)
  have next : N=Q^16 := cut_succ x _
  have xQ : x≤Q := by
    have old:=cut_mono (show 1≤x by omega) (Nat.zero_le j.val)
    simpa [cut,Q] using old
  have np : 0<N := by rw [next];exact pow_pos (by omega) _
  have nb : N≤x^budget:=cut_mono (by omega) (show j.val+1≤4 by omega)
  have space (i) : N ≤ (if b i then c.p i^c.e i else c.p i) := by
    dsimp [b];split
    · exact nb.trans (powers i)
    next h=>exact ((band i).resolve_left (by simpa using h)).le
  have ds : dust c b≤Q^9 := by
    have per i : den (c.p i) (c.e i) (b i)≤Q^3 := by
      have el := (c.lengths i).2.trans (cl.trans xQ)
      dsimp [den,b]
      split
      next h =>
        have small : c.p i≤Q:=by simpa using h
        exact (Nat.mul_le_mul el (Nat.pow_le_pow_left (show c.p i-1≤Q by omega) 2)).trans_eq (by ring)
      next=>exact el.trans (Nat.le_self_pow (by decide : 3≠0) Q)
    dsimp [dust]
    exact (prod_le_prod' (fun i _=>per i)).trans_eq (by simp;ring)
  have nz:=nonzero c b f g l gp fg frac unit actual
  have iga:=integer_gap c b f g nz
  let orig:=score f g (exactX c) (exactY c)
  let approx:=score f g (x' c b) (y' c b)
  let W:ℚ:=(f+g:ℕ)
  have lite : |orig-W|≤1/(N:ℚ) := close.trans (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast nb))
  have diff:=difference c b f g N np space
  change |approx-orig|≤_ at diff
  change (1:ℚ)≤|approx-W| * dust c b at iga
  have err : |approx-W| * (N:ℚ)≤48*((f:ℚ)+g)+1 := by
    have t:=abs_sub_le approx orig W
    have wn : (0:ℚ)<N:=by exact_mod_cast np
    nlinarith only [mul_le_mul_of_nonneg_right t wn.le,(le_div_iff₀ wn).mp diff,(le_div_iff₀ wn).mp lite]
  have sep : N≤(48*(f+g)+1)*dust c b := by
    have z : (N:ℚ)≤(48*((f:ℚ)+g)+1)*dust c b := by
      nlinarith only [mul_le_mul_of_nonneg_right iga (Nat.cast_nonneg N : (0:ℚ)≤N),
        mul_le_mul_of_nonneg_right err (Nat.cast_nonneg (dust c b) : (0:ℚ)≤_)]
    exact_mod_cast z
  have qr : 128≤Q:=big.trans xQ
  have cfq : f+g≤Q:=cf.trans xQ
  have cf' : 48*(f+g)+1<Q^2 := by
    nlinarith only [cfq,Nat.mul_le_mul_left Q qr,qr]
  have bad : N<Q^11 := sep.trans_lt ((Nat.mul_lt_mul_of_lt_of_le cf' ds (pow_pos (by omega) 9)).trans_eq (by ring))
  have natural : Q^11≤N:=next ▸ Nat.pow_le_pow_right (by omega) (by decide)
  omega

end OMA.ThreeMovingStep245212

end

section

/- Divisibility constraints on a single prime extension. -/
namespace OMA.OddCofactor245212
open Finset ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212
open scoped ArithmeticFunction.sigma

/-- Each new prime divides the sum of the two divisor moments of the remaining cofactor. -/
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

theorem last_le {m p d : ℕ} (hm : 0 < m) (hp : Nat.Prime p) (cop : m.Coprime p)
    (hd : 0<d) (eq : OeisA245212.a (m*p^d)=(σ 1 (m*p^d):ℤ)) : p≤W m+σ 1 m := by
  apply Nat.le_of_dvd _ (last_dvd hm hp cop hd eq)
  have pos : 0<σ 1 m := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact sum_pos' (fun _ _ => Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr hm.ne',by decide⟩
  omega

end OMA.OddCofactor245212

end

section

/- Finiteness for a fixed dyadic exponent and at most two distinct odd primes. -/
namespace OMA.TwoOddFinite245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma

/-- A bound on every odd prime power that can extend this positive cofactor
at equality. The extra one also permits the empty extension. -/
def lastBound (a : ℕ) : ℕ := 1+∑ q∈(W a+σ 1 a).divisors,
  ((W a:ℤ)-((q:ℤ)-1)*(σ 1 a:ℤ)).natAbs

theorem last_power_le {a q f : ℕ} (ha : 0<a) (hq : q.Prime) (odd : q≠2)
    (cop : a.Coprime q) (hf : 0<f) (eq : OeisA245212.a (a*q^f)=(σ 1 (a*q^f):ℤ)) :
    q^f≤lastBound a := by
  have divides := OMA.OddCofactor245212.last_dvd ha hq cop hf eq
  have spos := sigma_pos 1 a ha.ne'
  have member := mem_divisors.mpr ⟨divides,by omega⟩
  have bound := OMA.PrimePowerDiv245212.cofactor_bound ha hq odd cop f eq
  have part := single_le_sum (f:=fun q : ℕ =>
    ((W a:ℤ)-((q:ℤ)-1)*(σ 1 a:ℤ)).natAbs) (fun i _ => Nat.zero_le _) member
  unfold lastBound
  omega

private theorem extend {k m r : ℕ} (om : Odd m) (hr : r∈m.primeFactors)
    (rank : m.primeFactors.card≤2) (eq : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) :
    m≤r^(m.factorization r)*lastBound (2^k*r^(m.factorization r)) := by
  let F := m.primeFactors.erase r
  have card : F.card≤1 := by dsimp [F]; rw [card_erase_of_mem hr]; omega
  have repr : m=r^(m.factorization r)*∏ q∈F,q^(m.factorization q) := by
    calc
      m = ∏ q∈m.primeFactors,q^(m.factorization q) := Nat.prod_primeFactors_pow_factorization om.pos.ne'
      _ = _ := (prod_erase_mul _ _ hr).symm.trans (mul_comm _ _)
  have rpr := prime_of_mem_primeFactors hr
  rcases F.eq_empty_or_nonempty with empty|⟨q,hq⟩
  · rw [empty,prod_empty,mul_one] at repr
    exact repr.trans_le (Nat.le_mul_of_pos_right _ (by unfold lastBound; omega))
  · have singleton : F={q} := by
      ext x
      simpa only [mem_singleton] using
        (show x∈F ↔ x=q from ⟨fun hx => card_le_one.mp card x hx q hq,fun h => h ▸ hq⟩)
    rw [singleton,prod_singleton] at repr
    have qmem := (mem_erase.mp hq).2
    have qp := prime_of_mem_primeFactors qmem
    have qodd := Nat.coprime_two_left.mp
      ((Nat.coprime_two_left.mpr om).of_dvd_right (dvd_of_mem_primeFactors qmem))
    have nottwo : q≠2 := by intro z; rw [z] at qodd; exact (by decide : ¬Odd 2) qodd
    have cb : (2^k*r^(m.factorization r)).Coprime q :=
      ((Nat.coprime_two_left.mpr qodd).pow_left k).mul_left
        (((Nat.coprime_primes rpr qp).mpr (mem_erase.mp hq).1.symm).pow_left _)
    have ep := qp.factorization_pos_of_dvd om.pos.ne' (dvd_of_mem_primeFactors qmem)
    have pos : 0<2^k*r^(m.factorization r) := by have := rpr.pos; positivity
    have target : 2^k*m=2^k*r^(m.factorization r)*q^(m.factorization q) := by
      exact (congrArg (2^k*·) repr).trans (mul_assoc _ _ _).symm
    rw [target] at eq
    exact repr.trans_le (Nat.mul_le_mul_left _ (last_power_le pos qp nottwo cb ep eq))

/-- Both odd primes and their exponents are free; only the power of two is fixed. -/
theorem finite_two (k : ℕ) : {m : ℕ | Odd m ∧ m.primeFactors.card≤2 ∧
    OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)}.Finite := by
  obtain ⟨B,atom⟩ := OMA.BoundedAtom245212.bounded_atom k 2
  let F := ⋃ r∈Set.Iic B, ⋃ e∈Set.Iic B, Set.Iic (r^e*lastBound (2^k*r^e))
  have fin : F.Finite := (Set.finite_Iic B).biUnion fun r _ =>
    (Set.finite_Iic B).biUnion fun e _ => Set.finite_Iic _
  apply ((OMA.SquareFinite245212.square_finite k 2).union fin).subset
  rintro m ⟨om,rank,eq⟩
  by_cases sq : IsSquare m
  · exact Or.inl ⟨om,sq,rank,eq⟩
  · obtain ⟨r,hr,_,rb,eb⟩ := atom m om sq rank eq
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨r,rb,Set.mem_iUnion₂.mpr
      ⟨m.factorization r,eb,extend om hr rank eq⟩⟩)

end OMA.TwoOddFinite245212

end

section

/- An upper bound on the power of two in terms of each odd prime divisor. -/
namespace OMA.DyadicLeast245212
open Finset Nat ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
open OMA.FixedExponents245212 (x_avg)
open OMA.FixedExponents245212 (y_pos)

def term (p e : ℕ) : ℚ := (e:ℚ)/(((e:ℚ)+1)*p)

theorem x_two_terms {p e : ℕ} (hp : p.Prime) (he : 0<e) :
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

/-- The first two terms of each weighted prime factor already constrain
all odd prime reciprocals, independently of the divisor count. -/
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

/-- Now the dyadic exponent can vary as well: only one of the odd primes is fixed. -/
theorem finite_with_prime (q : ℕ) : {n : ℕ | ∃ k m : ℕ, n=2^k*m ∧ Odd m ∧
    q∈m.primeFactors ∧ m.primeFactors.card≤2 ∧ OeisA245212.a n=(σ 1 n:ℤ)}.Finite := by
  apply ((Set.finite_Iio (2*q)).biUnion (fun k _ =>
    (OMA.TwoOddFinite245212.finite_two k).image (fun m => 2^k*m))).subset
  rintro n ⟨k,m,rfl,om,hq,rank,eq⟩
  exact Set.mem_iUnion₂.mpr ⟨k,exponent_lt_twice_prime om hq eq,⟨m,⟨om,rank,eq⟩,rfl⟩⟩

end OMA.DyadicLeast245212

end

section

/- Absolute bounds for the shortest of three moving odd prime exponents
if the longest is not too large. The dyadic exponent is unrestricted. -/
namespace OMA.ThreeMovingOriginal245212
open Nat Finset ArithmeticFunction OMA.ThreeMovingGap245212 OMA.ThreeMovingScalar245212
open OMA.Smooth245212 (total W)
open scoped ArithmeticFunction.sigma
open OMA.ComplementaryLocal245212 (binary)

def F (k : ℕ) := 1+k*2^(k+1)
def G (k : ℕ) := 2^(k+1)-1

private theorem identities (k : ℕ) : 0<G k ∧ F k+G k=(k+1)*2^(k+1) ∧ F k=k*G k+(k+1) := by
  have g:=Nat.two_pow_pos k
  dsimp [F,G];rw [pow_succ]
  have sub:=Nat.sub_add_cancel (show 1≤2^k*2 by omega)
  exact ⟨by omega,by nlinarith only [sub],by nlinarith only [congrArg (k*·) sub]⟩

theorem physical (c : Family) (k : ℕ) (op : ∀i,Odd (c.p i)) (inj : c.p.Injective)
    (eqn : OeisA245212.a (2^k*total c.p c.e)=(σ 1 (2^k*total c.p c.e):ℤ)) :
    score (F k) (G k) (exactX c) (exactY c)=(F k+G k:ℕ) := by
  let t:=2^k*σ 0 (2^k)
  have t0 : 0<t := Nat.mul_pos (Nat.two_pow_pos k) (sigma_pos 0 _ (Nat.two_pow_pos k).ne')
  have norm:=OMA.CofactorCrossOriginal245212.normalized_extension (p:=c.p) (e:=c.e) (Nat.two_pow_pos k)
    c.prime inj (fun i=>(Nat.coprime_two_left.mpr (op i)).pow_left k) eqn
  change ((W (2^k):ℚ)/t)*(∏i,exactX c i)+((σ 1 (2^k):ℚ)/t)*(∏i,exactY c i)=2 at norm
  field_simp [show (t:ℚ)≠0 by exact_mod_cast t0.ne'] at norm
  have z0:=Nat.two_pow_pos (k+1)
  have gold : σ 1 (2^k)=G k := by
    dsimp [G];zify [Nat.cast_sub (show 1≤2^(k+1) from z0)]
    exact (OMA.ComplementaryLocal245212.binary k).1
  have fold : W (2^k)=F k := by exact_mod_cast (OMA.ComplementaryLocal245212.binary k).2
  have ht : 2*t=F k+G k := by
    dsimp [t];rw [sigma_zero_apply_prime_pow Nat.prime_two,(identities k).2.1,pow_succ];ring
  rw [gold,fold] at norm
  dsimp [score];rw [←ht];push_cast;linarith only [norm]

private theorem small_case (c : Family) (hp : ∀i,3≤c.p i) (hk : ∀i,c.k<2*c.p i) (high : minimumCut≤c.m)
    (exact : score (F c.k) (G c.k) (exactX c) (exactY c)=(F c.k+G c.k:ℕ)) : False := by
  let x:=base c.k c.L
  have big : 128≤x := by dsimp [base,x];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
  have cf : c.k+1≤x := by dsimp [base,x];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
  have cl : c.L≤x := by dsimp [base,x];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
  have comp : c.L≤c.k*c.m^2 := by have:=c.comparable;omega
  have powers i : x^degree≤c.p i^c.e i := scale (hp i) (hk i) high comp (c.lengths i).1
  have dx : 1≤x:=by omega
  have r0 := (identities c.k).1
  let PX:=∏i,exactX c i
  let PY:=∏i,exactY c i
  have xb i := OMA.ThreeMovingLocal245212.bounds (c.prime i) (c.positive i) c.mp (c.lengths i).1 true
  have low : (1:ℚ)≤PX:=one_le_prod (fun i _=>(xb i).1)
  have top : PX≤8 := calc
    _ ≤ ∏_i:Fin 3,(2:ℚ) := prod_le_prod (fun i _=>zero_le_one.trans (xb i).1) (fun i _=>(xb i).2.1)
    _ = _ := by norm_num
  have id : (G c.k:ℚ)*((c.k:ℚ)+1-score c.k 1 (exactX c) (exactY c))=((c.k:ℚ)+1)*(PX-1) := by
    change (F c.k:ℚ)*PX+(G c.k:ℚ)*PY=(F c.k+G c.k:ℕ) at exact
    change _*((c.k:ℚ)+1-((c.k:ℚ)*PX+(1:ℕ)*PY))=_
    have f : (F c.k:ℚ)=(c.k:ℚ)*G c.k+(c.k+1:ℕ) := by exact_mod_cast (identities c.k).2.2
    push_cast at f exact ⊢
    linear_combination -exact+(PX-1)*f
  have gp : (0:ℚ)<G c.k := by exact_mod_cast r0
  by_cases ample : 8*(c.k+1)*x^budget≤G c.k
  · have below : score c.k 1 (exactX c) (exactY c)≤(c.k+1:ℕ):=by
      push_cast
      exact sub_nonneg.mp (nonneg_of_mul_nonneg_right (id ▸ mul_nonneg (by positivity) (sub_nonneg.mpr low)) gp)
    have close : |score c.k 1 (exactX c) (exactY c)-(c.k+1:ℕ)|≤1/((x^budget:ℕ):ℚ) := by
      rw [abs_of_nonpos (sub_nonpos.mpr below),neg_sub]
      have h : (((c.k+1:ℕ):ℚ)-score c.k 1 (exactX c) (exactY c))*(x^budget:ℕ)≤1 := by
        apply le_of_mul_le_mul_left (a:=(G c.k:ℚ)) _ gp
        have g0 : (8:ℚ)*(c.k+1)*(x^budget:ℕ)≤G c.k:=by exact_mod_cast ample
        push_cast at g0 ⊢
        nlinarith only [congrArg (·*(x:ℚ)^budget) id,g0,
          mul_le_mul_of_nonneg_right (show PX-1≤8 by linarith) (show 0≤((c.k:ℚ)+1)*x^budget by positivity)]
      exact (le_div_iff₀ (by exact_mod_cast pow_pos dx budget : (0:ℚ)<(x^budget:ℕ))).mpr h
    apply OMA.ThreeMovingStep245212.contradiction c c.k 1 1 x (by decide) (by simp) (by simp) _ big cf cl
      (fun i=>(Nat.pow_le_pow_right dx (show budget≤degree by decide)).trans (powers i)) below close
    intro i; exact Nat.not_dvd_of_pos_of_lt (by decide) (c.prime i).one_lt
  · let x':=x^(budget+4)
    have lift : x≤x':=Nat.le_self_pow (by omega : budget+4≠0) _
    have fcap : F c.k+G c.k≤x' := by
      have gcap : G c.k+1≤8*(c.k+1)*x^budget:=by omega
      have zid : 2^(c.k+1)=G c.k+1 := by dsimp [G];have:=Nat.two_pow_pos (c.k+1);omega
      rw [(identities c.k).2.1,zid]
      calc
        _ ≤ (c.k+1)*(8*(c.k+1)*x^budget) := Nat.mul_le_mul_left _ gcap
        _ = (c.k+1)*(8*((c.k+1)*x^budget)) := by ring
        _ ≤ x*(x*(x*x^budget)) := Nat.mul_le_mul cf (Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right _ cf))
        _ = x^(budget+3) := by rw [pow_add];ring
        _ ≤ x' := Nat.pow_le_pow_right dx (by omega)
    apply OMA.ThreeMovingStep245212.contradiction c (F c.k) (G c.k) (2^(c.k+1)) x' r0
      (by have:=(identities c.k).2.2;omega) (identities c.k).2.1 _ (big.trans lift) fcap (cl.trans lift)
      (fun i=>by dsimp [x'];rw [←pow_mul];exact powers i) exact.le (by rw [exact,sub_self,abs_zero];positivity)
    intro i d
    have dv:=(c.prime i).dvd_of_dvd_pow d
    exact (Nat.not_dvd_of_pos_of_lt (by decide) (hp i)) dv

theorem shortest {k m L : ℕ} (p e : Fin 3→ℕ) (hp : ∀i,(p i).Prime) (op : ∀i,Odd (p i)) (inj : p.Injective)
    (ep : ∀i,0<e i) (mp : 0 < m) (lengths : ∀i,m≤e i+1 ∧ e i+1≤L)
    (comparable : 4*max (max 1 k) L < max 1 k*m^2)
    (eqn : OeisA245212.a (2^k*total p e)=(σ 1 (2^k*total p e):ℤ)) : m < minimumCut := by
  by_contra! high
  let c : Family := ⟨p,e,max 1 k,m,L,hp,ep,by omega,mp,lengths,comparable⟩
  have p3 i : 3≤p i := by have:=(hp i).two_le;obtain ⟨j,ju⟩:=op i;omega
  have odd : Odd (total p e) := Nat.coprime_two_left.mp (Coprime.prod_right (fun i _=>(Nat.coprime_two_left.mpr (op i)).pow_right _))
  have inF i : p i∈(total p e).primeFactors := Nat.mem_primeFactors.mpr ⟨hp i,
    (dvd_pow_self _ (ep i).ne').trans (dvd_prod_of_mem (fun j=>p j^e j) (mem_univ i)),odd.pos.ne'⟩
  have dk i := OMA.DyadicLeast245212.exponent_lt_twice_prime odd (inF i) eqn
  have norm:=physical c k op inj eqn
  by_cases kp : 0<k
  · have ck : c.k=k:=max_eq_right kp
    apply small_case c p3 (fun i=>by rw [ck];exact dk i) high
    rw [ck];exact norm
  · have zero : k=0:=by omega
    subst k
    have ck : c.k=1:=rfl
    let x:=base 1 L
    have big : 128≤x := by dsimp [x,base];omega
    have cf : 2≤x:=by omega
    have cl : c.L≤x:=by change L≤128*(1+2)*(L+1);omega
    have limits i := scale (k:=1) (p:=p i) (e:=e i) (p3 i) (by have:=p3 i;omega) high
      (show L≤1*m^2 by norm_num at comparable ⊢;omega) (lengths i).1
    change score 1 1 (exactX c) (exactY c)=(1+1:ℕ) at norm
    exact OMA.ThreeMovingStep245212.contradiction c 1 1 1 x (by decide) (by rw [ck]) (by rw [ck])
      (fun i=>Nat.not_dvd_of_pos_of_lt (by decide) (hp i).one_lt) big cf cl
      (fun i=>(Nat.pow_le_pow_right (by omega : 0<x) (show budget≤degree by decide)).trans (limits i))
      norm.le (by rw [norm,sub_self,abs_zero];positivity)

end OMA.ThreeMovingOriginal245212

end

section

/- A negative contribution when a retained coordinate returns to its true
moment is dominated by the deficit of the dyadic linearization. -/
namespace OMA.SingleMovingLoss245212
open Nat Finset OMA.Smooth245212 OMA.TwoTallLocal245212 OMA.SingleMovingGap245212
open OMA.ThreeMovingLocal245212 (xx yy)
open OMA.ThreeMovingLocal245212 (quotients)
open OMA.DyadicLeast245212 (x_two_terms)

theorem single_lb {p e : ℕ} (hp : p.Prime) (he : 0<e) :
    1≤(2*(p:ℚ))*(X p (some e)-1) := by
  have r:=OMA.DyadicLeast245212.x_two_terms hp he
  change 1+(e:ℚ)/((e+1)*p)≤_ at r
  have z : 0<((e:ℚ)+1)*p := by have:=hp.pos;positivity
  have z' := (div_le_iff₀ z).mp (by linarith only [r] : (e:ℚ)/((e+1)*p)≤X p (some e)-1)
  have q : (1:ℚ)≤e:=by exact_mod_cast he
  by_contra! bad
  have mul:=mul_lt_mul_of_pos_right bad (by positivity : 0<(e:ℚ)+1)
  nlinarith only [z',q,mul]

theorem scalar {k p e : ℕ} (hk : 8≤k) (kp : k+1<p) (len : p≤e+1) :
    8*p*(2^(k+1)-1)≤p^e := by
  have k4 : 4≤k:=by omega
  have c : 16≤2^k := (by decide : 16≤2^4).trans (Nat.pow_le_pow_right (by decide) k4)
  have ep : k+1≤e:=by omega
  calc
    _ ≤ 8*p*(2^(k+1)) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = p*(2^k*16) := by rw [pow_succ];ring
    _ ≤ p*(2^k*2^k) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ c)
    _ = p*(2*2)^k := by rw [mul_pow]
    _ ≤ p*p^k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = p^(k+1) := (pow_succ' ..).symm
    _ ≤ p^e := Nat.pow_le_pow_right (by omega) ep

/-- Returns a coordinate from any of the three proxy choices. The comparison
tests u*y*y' against k, keeping the product of the *other* ordinary factors. -/
theorem restore {p e k : ℕ} (hp : p.Prime) (ep : 0<e) (kp : 0<k) (mode : Option Bool)
    (x x' y y' allowance : ℚ) (xp : 1≤x) (xp' : 1≤x') (yp : 0≤y) (yp' : 0≤y')
    (yl : y*y'≤1) (dl : 0≤allowance)
    (bad : mode=some true → (k:ℚ)<((p:ℚ)-1)*(y*y') → 1/(p:ℚ)^e≤allowance) :
    (k:ℚ)*xx' p e mode*x*x'+yy' p e mode*y*y' ≤
    (k:ℚ)*X p (some e)*x*x'+Y p (some e)*y*y'+allowance := by
  cases mode with
  | none=> dsimp [xx',yy'];linarith
  | some t=>
    cases t with
    | false=>
      have v:=OMA.TwoTallLocal245212.move hp ep (by decide : 0 < (1:ℕ)) kp (by decide : 0<(1:ℕ))
        (le_refl (k*1)) false (by simp) x x' y y' xp xp' yp yp' (by norm_num;linarith)
      dsimp [xx',yy'];push_cast at v;linarith only [v,dl]
    | true=>
      let u:ℚ:=(p:ℚ)-1
      let H:ℚ:=(e:ℚ)+1
      let d:ℚ:=1/(H*u^2*(p:ℚ)^e)
      have u1 : 1≤u:=by dsimp [u];have z:=(by exact_mod_cast hp.two_le : (2:ℚ)≤p);linarith
      have h1 : 1≤H:=by dsimp [H];have z:=Nat.cast_nonneg (α:=ℚ) e;linarith
      have po : (0:ℚ)<(p:ℚ)^e:=pow_pos (by exact_mod_cast hp.pos) _
      have dpos : 0<d:=by dsimp [d];positivity
      have vk : 0≤(k:ℚ)*(x*x'):=mul_nonneg (by positivity) (mul_nonneg (by linarith) (by linarith))
      have xy : 1≤x*x':=one_le_mul_of_one_le_of_one_le xp xp'
      have m:=OMA.ThreeMovingLocal245212.quotients hp (e:=e)
      change X p (some e)=xx p e true+d ∧ Y p (some e)=yy p e true-u*d at m
      change _*xx p e true*x*x'+yy p e true*y*y'≤_
      rw [m.1,m.2]
      by_cases good : u*(y*y')≤k
      · have more:=(mul_le_mul_of_nonneg_left xy (Nat.cast_nonneg (α:=ℚ) k))
        have dif : 0≤(k:ℚ)*x*x'-u*(y*y'):=by linarith [good,more]
        nlinarith only [mul_nonneg dpos.le dif,dl]
      · have limit:=bad rfl (lt_of_not_ge good)
        have ud : u*d=1/((H*u)*(p:ℚ)^e) := by dsimp [d];field_simp
        have abd : u*d≤1/(p:ℚ)^e := by
          rw [ud]
          exact one_div_le_one_div_of_le po (le_mul_of_one_le_left po.le (one_le_mul_of_one_le_of_one_le h1 u1))
        have loss:=mul_le_mul_of_nonneg_left yl (mul_nonneg (by linarith : 0≤u) dpos.le)
        nlinarith only [loss,abd,limit,mul_nonneg dpos.le vk]

end OMA.SingleMovingLoss245212

end

section

/- The actual dyadic deficit exceeds the total possible loss caused by
all risky rounded coordinates, without any comparability assumption. -/
namespace OMA.SingleMovingProxy245212
open Nat Finset OMA.SingleMovingGap245212 OMA.TwoTallLocal245212
open OMA.ThreeMovingOriginal245212 (G)
def deficit (c : Family) : ℚ := (c.k:ℚ)+1-score c.k 1 (exactX c) (exactY c)

theorem lower (c : Family) (link : deficit c*(G c.k:ℕ)=((c.k:ℚ)+1)*((∏i,exactX c i)-1)) (i) :
    1≤(2*(c.p i:ℚ))*(G c.k)*(deficit c) := by
  have xb j : 1≤exactX c j:=(ranges (c.prime j) (c.positive j) none).1
  have xi : exactX c i≤∏j,exactX c j := by
    rw [←prod_erase_mul (univ : Finset (Fin 3)) (exactX c) (mem_univ i)]
    exact le_mul_of_one_le_left (zero_le_one.trans (xb _)) (one_le_prod (fun j _=>xb j))
  have localBound:=OMA.SingleMovingLoss245212.single_lb (c.prime i) (c.positive i)
  change 1≤(2*(c.p i:ℚ))*(exactX c i-1) at localBound
  have xm : 0≤(∏j,exactX c j)-1:=by linarith only [xi,xb i]
  have more:=mul_nonneg (Nat.cast_nonneg (α:=ℚ) c.k) xm
  have cc : 0≤2*(c.p i:ℚ):=by positivity
  nlinarith only [localBound,mul_le_mul_of_nonneg_left xi cc,mul_nonneg cc more,
    congrArg (fun z:ℚ=>2*(c.p i:ℚ)*z) link]

theorem positive (c : Family) (link : deficit c*(G c.k:ℕ)=((c.k:ℚ)+1)*((∏i,exactX c i)-1)) : 0<deficit c := by
  have h:=lower c link 0
  by_contra! n
  have t:=mul_nonpos_of_nonneg_of_nonpos (show 0≤2*(c.p 0:ℚ)*(G c.k:ℕ) by positivity) n
  linarith

theorem separated (c : Family) (b : Fin 3→Option Bool)
    (link : deficit c*(G c.k:ℕ)=((c.k:ℚ)+1)*((∏i,exactX c i)-1)) :
    (c.k+1)*dust c b ≠ c.k*NX c b+NY c b := by
  intro hit
  have gd : 0<deficit c:=positive c link
  have scale:=retained (b:=b) (f:=c.k) (g:=1) (l:=1) (by simp)
    (fun i=>Nat.not_dvd_of_pos_of_lt (by decide) (c.prime i).one_lt) (by simpa using hit)
  let mix (s : Finset (Fin 3)) (i : Fin 3) := if i∈s then exactX c i else x' c b i
  let miy (s : Finset (Fin 3)) (i : Fin 3) := if i∈s then exactY c i else y' c b i
  have adv (s : Finset (Fin 3)) {i} (fresh : i∉s) :
      score c.k 1 (mix s) (miy s)≤ score c.k 1 (mix (insert i s)) (miy (insert i s))+deficit c/4 := by
    have bound j : 1≤ mix s j ∧ 0≤ miy s j ∧ miy s j≤2/((c.e j:ℚ)+1) := by
      by_cases mem : j∈s
      · have v:=ranges (c.prime j) (c.positive j) none
        simpa only [mix,miy,if_pos mem,exactX,exactY,xx',yy'] using And.intro v.1 v.2.2
      · have v:=ranges (c.prime j) (c.positive j) (b j)
        simpa only [mix,miy,if_neg mem,x',y'] using And.intro v.1 v.2.2
    have size j : miy s j≤1:= (bound j).2.2.trans ((div_le_iff₀ (by positivity)).mpr (by
      have:= (by exact_mod_cast c.positive j : (1:ℚ)≤c.e j);linarith))
    have single {j l : Fin 3} (n : j≠i) (n' : l≠i) (jl : j≠l) :
        (c.k:ℚ)*mix s i*mix s j*mix s l+miy s i*miy s j*miy s l ≤
        c.k*mix (insert i s) i*mix (insert i s) j*mix (insert i s) l+
          miy (insert i s) i*miy (insert i s) j*miy (insert i s) l+deficit c/4 := by
      have prod : miy s j*miy s l≤1:=mul_le_one₀ (size j) (bound l).2.1 (size l)
      have step:=OMA.SingleMovingLoss245212.restore (c.prime i) (c.positive i) (by have:=c.kp;omega : 0<c.k)
        (b i) (mix s j) (mix s l) (miy s j) (miy s l) (deficit c/4)
        (bound j).1 (bound l).1 (bound j).2.1 (bound l).2.1 prod (by positivity)
      suffices bad : b i=some true → (c.k:ℚ)<((c.p i:ℚ)-1)*(miy s j*miy s l) →
          1/(c.p i:ℚ)^(c.e i)≤deficit c/4 by
        simpa [mix,miy,exactX,exactY,x',y',fresh,n,n'] using step bad
      intro bit risk
      have pk : c.k+1<c.p i := by
        have h:=mul_le_mul_of_nonneg_left prod (show (0:ℚ)≤(c.p i:ℚ)-1 by have:= (by exact_mod_cast (c.prime i).one_le : (1:ℚ)≤c.p i);linarith)
        exact_mod_cast (show (c.k:ℚ)+1<c.p i by linarith only [h,risk])
      have pL : c.p i≤c.L:=by have:=scale i bit;omega
      have excluded (z z' : Fin 3) (prod' : miy s j*miy s l=miy s z*miy s z') (maximal : c.e z+1=c.L) : False := by
        have up:=mul_le_mul_of_nonneg_left (size z') (bound z).2.1
        have Y:= (le_div_iff₀ (by positivity)).mp (bound z).2.2
        have PL : (c.p i:ℚ)-1≤(c.e z:ℚ)+1:=by
          have hh : c.p i≤c.e z+1:=by omega
          have v : (c.p i:ℚ)≤c.e z+1:=by exact_mod_cast hh
          linarith
        have cp:=mul_nonneg (bound z).2.1 (bound z').2.1
        have t1:=mul_le_mul_of_nonneg_right PL cp
        have t2:=mul_le_mul_of_nonneg_right up (show (0:ℚ)≤(c.e z:ℚ)+1 by positivity)
        rw [prod'] at risk
        have k8 : (8:ℚ)≤c.k:=by exact_mod_cast c.kp
        nlinarith only [risk,Y,t1,t2,k8]
      obtain ⟨v,vbig⟩:=c.longest
      have caseV : v=i ∨ v=j ∨ v=l:=by omega
      have len : c.p i≤c.e i+1 := by
        rcases caseV with rfl|rfl|rfl
        · omega
        · exact False.elim (excluded _ _ rfl vbig)
        · exact False.elim (excluded _ _ (mul_comm _ _) vbig)
      have pw:=OMA.SingleMovingLoss245212.scalar c.kp pk len
      have more:=lower c link i
      have pwq : 8*(c.p i:ℚ)*(G c.k)≤(c.p i:ℚ)^(c.e i):=by exact_mod_cast pw
      apply (div_le_iff₀ (by have:=(c.prime i).pos;positivity : (0:ℚ)<(c.p i:ℚ)^(c.e i))).mpr
      nlinarith only [more,mul_le_mul_of_nonneg_right pwq gd.le]
    dsimp [score];simp only [Fin.prod_univ_three,one_mul]
    have choice : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases choice with rfl|rfl|rfl
    · simpa only [mul_comm,mul_left_comm,mul_assoc] using single (j:=1) (l:=2) (by decide) (by decide) (by decide)
    · simpa only [mul_comm,mul_left_comm,mul_assoc] using single (j:=0) (l:=2) (by decide) (by decide) (by decide)
    · simpa only [mul_comm,mul_left_comm,mul_assoc] using single (j:=0) (l:=1) (by decide) (by decide) (by decide)
  have a:=adv ∅ (i:=0) (by decide)
  have b1:=adv {0} (i:=1) (by decide)
  have d:=adv {1,0} (i:=2) (by decide)
  have un : insert (2:Fin 3) ({1,0}:Finset (Fin 3))=univ:=by decide
  rw [un] at d
  have a' : score c.k 1 (x' c b) (y' c b)≤ score c.k 1 (mix {0}) (miy {0})+deficit c/4:=by simpa only [mix,miy,notMem_empty,if_false,Finset.insert_empty] using a
  have d' : score c.k 1 (mix {1,0}) (miy {1,0}) ≤ score c.k 1 (exactX c) (exactY c)+deficit c/4:=by simpa only [mix,miy,mem_univ,if_true] using d
  have eq:=clear c b c.k 1
  simp only [one_mul] at eq
  rw [←hit] at eq
  push_cast at eq
  have dp : (0:ℚ)<dust c b:=by exact_mod_cast dust_pos c b
  have eq' : score c.k 1 (x' c b) (y' c b)=(c.k:ℚ)+1:=mul_right_cancel₀ dp.ne' eq
  dsimp only [deficit] at a' b1 d' gd
  linarith only [a',b1,d',eq',gd]

end OMA.SingleMovingProxy245212

end

section

/- Integer growth estimates and an empty multiplicative interval for three bases and the third prime power. -/
namespace OMA.TwoTallScalar245212

def cut (x j : ℕ) := x^(16^j)

theorem cut_succ (x i : ℕ) : cut x (i+1)=(cut x i)^16 := by
  rw [cut,cut,pow_succ,pow_mul]

theorem cut_mono {x : ℕ} (pos : 1≤x) : Monotone (cut x) :=
  fun _ _ le=>Nat.pow_le_pow_right pos (Nat.pow_le_pow_right (by decide) le)

theorem empty_interval (x : ℕ) (hx : 1≤x) (p : Fin 4→ℕ) :
    ∃j : Fin 5,∀i, p i ≤ cut x j.val ∨ cut x (j.val+1) < p i := by
  by_contra! no
  choose f above below using no
  have inj:Function.Injective f := by
    intro j k eqn
    rcases lt_trichotomy j k with lt|eq|gt
    · have h := cut_mono hx (show j.val+1≤k.val from lt)
      have impossible:=(below j).trans h
      rw [eqn] at impossible
      exact False.elim ((above k).not_ge impossible)
    · exact eq
    · have h := cut_mono hx (show k.val+1≤j.val from gt)
      have impossible:=(below k).trans h
      rw [←eqn] at impossible
      exact False.elim ((above j).not_ge impossible)
  have:=Fintype.card_le_of_injective _ inj
  norm_num at this

def budget := 16^5

def base (k L : ℕ) := 128*(k+2)*(L+1)

-- The larger exponent covers substitution of the exact dyadic numerator.
def degree := (budget+4)*budget

def minimumCut := 64*(degree+1)^2

private theorem square_product (p m F : ℕ) : ((p^14*m^2)^F)^2=p^(28*F)*m^(4*F) := by
  rw [←pow_mul,mul_pow,←pow_mul,←pow_mul,show 14*(F*2)=28*F by ring,show 2*(F*2)=4*F by ring]

theorem scale {m k L p e : ℕ} (hp : 3≤p) (hk : k<2*p) (hm : minimumCut ≤ m)
    (comparable : L ≤ k*m^2) (low : m≤e+1) :
    (base k L)^degree ≤ p^e := by
  let F:=degree
  have fp : 1≤F := by decide
  change 64*(F+1)^2≤ m at hm
  have mp : 1≤ m:=by nlinarith only [hm,Nat.zero_le (F^2),Nat.zero_le F]
  have pp : 1≤p:=by omega
  have kcap : k+2≤4*p := by omega
  have Lcap : L+1≤3*p*m^2 := by
    have mpos:=Nat.mul_pos (show 0<p by omega) (pow_pos mp 2)
    nlinarith only [comparable,Nat.mul_le_mul_right (m^2) hk.le,mpos]
  have scale : base k L≤p^14*m^2 := by
    have sixteen : 1536≤p^12 := (by decide : 1536≤3^12).trans (Nat.pow_le_pow_left hp _)
    have b:=Nat.mul_le_mul kcap Lcap
    dsimp [base]
    nlinarith only [Nat.mul_le_mul_left 128 b,Nat.mul_le_mul_right (p^2*m^2) sixteen]
  have grow := OMA.ComplementarySize245212.absorb (d:=2*F) (b:=m) (by nlinarith only [hm,Nat.zero_le F])
  have poly : m^(4*F)≤p^m := (by convert grow using 1; ring : m^(4*F)≤2^m).trans (Nat.pow_le_pow_left (by omega) _)
  have gain : 28*F+m≤2*e := by
    nlinarith only [hm,low,Nat.zero_le (F^2)]
  apply (pow_le_pow_iff_left₀ (show 0≤(base k L)^degree from Nat.zero_le _) (Nat.zero_le _) (by decide : 2≠0)).mp
  change ((base k L)^F)^2≤(p^e)^2
  calc
    _ ≤ ((p^14*m^2)^F)^2 := Nat.pow_le_pow_left (Nat.pow_le_pow_left scale _) _
    _ = p^(28*F)*m^(4*F) := square_product p m F
    _ ≤ p^(28*F)*p^m := Nat.mul_le_mul_left _ poly
    _ = p^(28*F+m) := (pow_add ..).symm
    _ ≤ p^(2*e) := Nat.pow_le_pow_right pp gain
    _ = (p^e)^2 := by rw [mul_comm,pow_mul]

end OMA.TwoTallScalar245212

end

section

/- A missing interval among six local scales makes the local tail
smaller than a nonzero integer's reciprocal denominator. -/
namespace OMA.SingleMovingStep245212
open Nat Finset OMA.TwoTallLocal245212 OMA.ThreeMovingLocal245212 OMA.SingleMovingGap245212
open OMA.TwoTallScalar245212 (cut cut_mono cut_succ)
open OMA.CofactorEffectiveAtom245212 (product_error)

theorem empty_six (x : ℕ) (hx : 1≤x) (p : Fin 6→ℕ) :
    ∃j : Fin 7,∀i, p i ≤ cut x j.val ∨ cut x (j.val+1) < p i := by
  by_contra! no
  choose f above below using no
  have inj:Function.Injective f := by
    intro j k eqn
    rcases lt_trichotomy j k with lt|eq|gt
    · have h := cut_mono hx (show j.val+1≤k.val from lt)
      have impossible:=(below j).trans h
      rw [eqn] at impossible
      exact False.elim ((above k).not_ge impossible)
    · exact eq
    · have h := cut_mono hx (show k.val+1≤j.val from gt)
      have impossible:=(below k).trans h
      rw [←eqn] at impossible
      exact False.elim ((above j).not_ge impossible)
  have:=Fintype.card_le_of_injective _ inj
  norm_num at this

def degree : ℕ := 16^7

theorem integer_gap (c : Family) (bits : Fin 3→Option Bool) (f g : ℕ)
    (different : (f+g)*dust c bits ≠ f*NX c bits+g*NY c bits) :
    (1:ℚ)≤|score f g (x' c bits) (y' c bits)-(f+g:ℕ)| * dust c bits := by
  let B:=dust c bits
  let T:=f*NX c bits+g*NY c bits
  let L:ℤ:=(T:ℤ)-((f+g)*B:ℕ)
  have nz : L≠0 := fun h => different (by exact_mod_cast (sub_eq_zero.mp h).symm)
  have la : (1:ℤ)≤|L| := by have:=abs_pos.mpr nz;omega
  have raw : (1:ℚ)≤|(T:ℚ)-((f+g)*B:ℕ)| := by dsimp [L] at la;exact_mod_cast la
  have ab:=congrArg (fun w:ℚ=>|w|) (show (score f g (x' c bits) (y' c bits)-(f+g:ℕ))*B =
      (T:ℚ)-((f+g)*B:ℕ) by rw [sub_mul];push_cast;rw [show score f g (x' c bits) (y' c bits)*B=(T:ℚ) from clear ..])
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg B : (0:ℚ)≤B)] at ab
  exact ab.trans_ge raw

theorem difference (c : Family) (b : Fin 3→Option Bool) (f g N : ℕ) (n0 : 0<N)
    (space : ∀ i t, b i=some t → N ≤ (if t then (c.p i)^(c.e i) else c.p i)) :
    |score f g (x' c b) (y' c b)-score f g (exactX c) (exactY c)|≤48*((f:ℚ)+g)/N := by
  have bp i := ranges (c.prime i) (c.positive i) (b i)
  have ex i := ranges (c.prime i) (c.positive i) none
  have er (i) : |exactX c i-x' c b i|≤2/(N:ℚ) ∧ |exactY c i-y' c b i|≤2/(N:ℚ) := by
    cases h:b i with
    | none=>simp [exactX,x',exactY,y',h,xx',yy'];positivity
    | some t=>simpa [exactX,x',exactY,y',h,xx',yy'] using error (c.prime i) (c.positive i) n0 t (space i t h)
  have eps : (0:ℚ)≤2/N := by positivity
  have one i : 2/((c.e i:ℚ)+1)≤2 := div_le_self (by decide) (by have:=Nat.cast_nonneg (α:=ℚ) (c.e i);linarith)
  have x:=OMA.CofactorEffectiveAtom245212.product_error (univ:Finset (Fin 3)) (exactX c) (x' c b) eps
    (fun i _=>⟨zero_le_one.trans (ex i).1,(ex i).2.1,zero_le_one.trans (bp i).1,(bp i).2.1,(er i).1⟩)
  have y:=OMA.CofactorEffectiveAtom245212.product_error (univ:Finset (Fin 3)) (exactY c) (y' c b) eps
    (fun i _=>⟨(ex i).2.2.1,(ex i).2.2.2.trans (one i),(bp i).2.2.1,(bp i).2.2.2.trans (one i),(er i).2⟩)
  norm_num at x y
  dsimp [score]
  rw [abs_sub_comm]
  calc
    _ = |(f:ℚ)*((∏i,exactX c i)-∏i,x' c b i)+(g:ℚ)*((∏i,exactY c i)-∏i,y' c b i)| := by congr 1;ring
    _ ≤ _ := (abs_add_le ..).trans (by
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg f : (0:ℚ)≤f),abs_mul,
        abs_of_nonneg (Nat.cast_nonneg g : (0:ℚ)≤g)]
      simp only [div_eq_mul_inv] at x y ⊢
      nlinarith only [mul_le_mul_of_nonneg_left x (Nat.cast_nonneg f : (0:ℚ)≤f),
        mul_le_mul_of_nonneg_left y (Nat.cast_nonneg g : (0:ℚ)≤g)])

theorem contradiction (c : Family) (f g x : ℕ) (big : 128≤x) (cf : f+g≤x) (cl : c.L≤x)
    (separated : ∀ b, (f+g)*dust c b ≠ f*NX c b+g*NY c b)
    (close : |score f g (exactX c) (exactY c)-(f+g:ℕ)| ≤ 1/((x^degree:ℕ):ℚ)) : False := by
  let point : Fin 6 → ℕ := ![c.p 0,c.p 1,c.p 2,c.p 0^c.e 0,c.p 1^c.e 1,c.p 2^c.e 2]
  obtain ⟨j,band⟩:=empty_six x (by omega) point
  have bp (i:Fin 3) : c.p i≤cut x j.val ∨ cut x (j.val+1)<c.p i := by
    fin_cases i <;> first | exact band 0 | exact band 1 | exact band 2
  have bd (i:Fin 3) : c.p i^c.e i≤cut x j.val ∨ cut x (j.val+1)<c.p i^c.e i := by
    fin_cases i <;> first | exact band 3 | exact band 4 | exact band 5
  let Q:=cut x j.val
  let N:=cut x (j.val+1)
  let b (i:Fin 3) : Option Bool := if c.p i^c.e i≤Q then none else some (decide (c.p i≤Q))
  have next : N=Q^16 := cut_succ x _
  have xQ : x≤Q := by
    have old:=cut_mono (show 1≤x by omega) (Nat.zero_le j.val)
    simpa [cut,Q] using old
  have np : 0<N := by rw [next];exact pow_pos (by omega) _
  have nb : N≤x^degree:=cut_mono (by omega) (show j.val+1≤7 by omega)
  have space (i) (t:Bool) (mode:b i=some t) : N ≤ (if t then c.p i^c.e i else c.p i) := by
    dsimp [b] at mode
    split at mode
    next=>contradiction
    next off=>
      obtain rfl:=Option.some.inj mode
      by_cases lo : c.p i≤Q
      · simp [lo]
        exact ((bd i).resolve_left off).le
      · simpa [lo] using ((bp i).resolve_left lo).le
  have ds : dust c b≤Q^9 := by
    have per i : Dn (c.p i) (c.e i) (b i)≤Q^3 := by
      have el := (c.cap i).trans (cl.trans xQ)
      by_cases exactMode : c.p i^c.e i≤Q
      · rw [show b i=none from if_pos exactMode]
        change (c.e i+1)*(c.p i^c.e i)≤Q^3
        exact
          (Nat.mul_le_mul el exactMode).trans (show Q*Q≤Q^3 by rw [←sq];exact Nat.pow_le_pow_right (by omega) (by decide))
      · by_cases keep:c.p i≤Q
        · simpa [b,exactMode,keep,Dn,den] using
            (Nat.mul_le_mul el (Nat.pow_le_pow_left (show c.p i-1≤Q by omega) 2)).trans_eq (by ring : Q*Q^2=Q^3)
        · simpa [b,exactMode,keep,Dn,den] using el.trans (Nat.le_self_pow (by decide : 3≠0) Q)
    dsimp [dust]
    exact (prod_le_prod' (fun i _=>per i)).trans_eq (by simp;ring)
  have nz:=separated b
  have iga:=integer_gap c b f g nz
  let orig:=score f g (exactX c) (exactY c)
  let approx:=score f g (x' c b) (y' c b)
  let W:ℚ:=(f+g:ℕ)
  have lite : |orig-W|≤1/(N:ℚ) := close.trans (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast nb))
  have diff:=difference c b f g N np space
  change |approx-orig|≤_ at diff
  change (1:ℚ)≤|approx-W| * dust c b at iga
  have err : |approx-W| * (N:ℚ)≤48*((f:ℚ)+g)+1 := by
    have t:=abs_sub_le approx orig W
    have wn : (0:ℚ)<N:=by exact_mod_cast np
    nlinarith only [mul_le_mul_of_nonneg_right t wn.le,(le_div_iff₀ wn).mp diff,(le_div_iff₀ wn).mp lite]
  have sep : N≤(48*(f+g)+1)*dust c b := by
    have z : (N:ℚ)≤(48*((f:ℚ)+g)+1)*dust c b := by
      nlinarith only [mul_le_mul_of_nonneg_right iga (Nat.cast_nonneg N : (0:ℚ)≤N),
        mul_le_mul_of_nonneg_right err (Nat.cast_nonneg (dust c b) : (0:ℚ)≤_)]
    exact_mod_cast z
  have qr : 128≤Q:=big.trans xQ
  have cfq : f+g≤Q:=cf.trans xQ
  have cf' : 48*(f+g)+1<Q^2 := by
    nlinarith only [cfq,Nat.mul_le_mul_left Q qr,qr]
  have bad : N<Q^11 := sep.trans_lt ((Nat.mul_lt_mul_of_lt_of_le cf' ds (pow_pos (by omega) 9)).trans_eq (by ring))
  have natural : Q^11≤N:=next ▸ Nat.pow_le_pow_right (by omega) (by decide)
  omega

end OMA.SingleMovingStep245212

end

section

/- Uniform integer separation for a finite list of odd prime powers. -/
namespace OMA.FixedRankStep245212
open Nat Finset OMA.TwoTallLocal245212 OMA.ThreeMovingLocal245212 OMA.FixedRankGap245212
open OMA.CofactorEffectiveAtom245212 (product_error)
variable {r : ℕ}

def cut (r x j : ℕ) := x^((3*r+4)^j)
def degree (r : ℕ) := (3*r+4)^(2*r+1)

theorem cut_succ (r x j : ℕ) : cut r x (j+1)=(cut r x j)^(3*r+4) := by
  simp only [cut,pow_succ (3*r+4),←pow_mul]

theorem cut_mono (r : ℕ) {x : ℕ} (hx : 1≤x) : Monotone (cut r x) :=
  fun _ _ z=>Nat.pow_le_pow_right hx (Nat.pow_le_pow_right (by omega) z)

theorem empty_band (x : ℕ) (hx : 1≤x) (p : Fin r ⊕ Fin r →ℕ) :
    ∃j : Fin (2*r+1),∀i, p i ≤ cut r x j.val ∨ cut r x (j.val+1) < p i := by
  by_contra! no
  choose f above below using no
  have inj:Function.Injective f := by
    intro j k eqn
    rcases lt_trichotomy j k with lt|eq|gt
    · have h := cut_mono r hx (show j.val+1≤k.val from lt)
      have impossible:=(below j).trans h
      rw [eqn] at impossible
      exact False.elim ((above k).not_ge impossible)
    · exact eq
    · have h := cut_mono r hx (show k.val+1≤j.val from gt)
      have impossible:=(below k).trans h
      rw [←eqn] at impossible
      exact False.elim ((above j).not_ge impossible)
  have h:=Fintype.card_le_of_injective _ inj
  simp only [Fintype.card_fin,Fintype.card_sum] at h
  omega

theorem integer_gap (c : Family r) (bits : Fin r→Option Bool) (f g : ℕ)
    (different : (f+g)*dust c bits ≠ f*NX c bits+g*NY c bits) :
    (1:ℚ)≤|score f g (x' c bits) (y' c bits)-(f+g:ℕ)| * dust c bits := by
  let B:=dust c bits
  let T:=f*NX c bits+g*NY c bits
  let L:ℤ:=(T:ℤ)-((f+g)*B:ℕ)
  have nz : L≠0 := fun h => different (by exact_mod_cast (sub_eq_zero.mp h).symm)
  have la : (1:ℤ)≤|L| := by have:=abs_pos.mpr nz;omega
  have raw : (1:ℚ)≤|(T:ℚ)-((f+g)*B:ℕ)| := by dsimp [L] at la;exact_mod_cast la
  have ab:=congrArg (fun w:ℚ=>|w|) (show (score f g (x' c bits) (y' c bits)-(f+g:ℕ))*B =
      (T:ℚ)-((f+g)*B:ℕ) by rw [sub_mul];push_cast;rw [show score f g (x' c bits) (y' c bits)*B=(T:ℚ) from clear ..])
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg B : (0:ℚ)≤B)] at ab
  exact ab.trans_ge raw

theorem difference (c : Family r) (b : Fin r→Option Bool) (f g N : ℕ) (n0 : 0<N)
    (space : ∀ i t, b i=some t → N ≤ (if t then (c.p i)^(c.e i) else c.p i)) :
    |score f g (x' c b) (y' c b)-score f g (exactX c) (exactY c)|≤(2*r*2^r:ℕ)*((f:ℚ)+g)/N := by
  have bp i := ranges (c.prime i) (c.positive i) (b i)
  have ex i := ranges (c.prime i) (c.positive i) none
  have er (i) : |exactX c i-x' c b i|≤2/(N:ℚ) ∧ |exactY c i-y' c b i|≤2/(N:ℚ) := by
    cases h:b i with
    | none=>simp [exactX,x',exactY,y',h,xx',yy'];positivity
    | some t=>simpa [exactX,x',exactY,y',h,xx',yy'] using error (c.prime i) (c.positive i) n0 t (space i t h)
  have eps : (0:ℚ)≤2/N := by positivity
  have one i : 2/((c.e i:ℚ)+1)≤2 := div_le_self (by decide) (by have:=Nat.cast_nonneg (α:=ℚ) (c.e i);linarith)
  have x:=OMA.CofactorEffectiveAtom245212.product_error (univ:Finset (Fin r)) (exactX c) (x' c b) eps
    (fun i _=>⟨zero_le_one.trans (ex i).1,(ex i).2.1,zero_le_one.trans (bp i).1,(bp i).2.1,(er i).1⟩)
  have y:=OMA.CofactorEffectiveAtom245212.product_error (univ:Finset (Fin r)) (exactY c) (y' c b) eps
    (fun i _=>⟨(ex i).2.2.1,(ex i).2.2.2.trans (one i),(bp i).2.2.1,(bp i).2.2.2.trans (one i),(er i).2⟩)
  have cards : (univ:Finset (Fin r)).card=r:=Finset.card_fin _
  rw [cards] at x y
  change |(∏i,exactX c i)-(∏i,x' c b i)| ≤ (r:ℚ)*2^r*(2/N) at x
  change |(∏i,exactY c i)-(∏i,y' c b i)| ≤ (r:ℚ)*2^r*(2/N) at y
  dsimp [score]
  rw [abs_sub_comm]
  calc
    _ = |(f:ℚ)*((∏i,exactX c i)-∏i,x' c b i)+(g:ℚ)*((∏i,exactY c i)-∏i,y' c b i)| := by congr 1;ring
    _ ≤ _ := (abs_add_le ..).trans (by
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg f : (0:ℚ)≤f),abs_mul,
        abs_of_nonneg (Nat.cast_nonneg g : (0:ℚ)≤g)]
      push_cast
      simp only [div_eq_mul_inv] at x y ⊢
      nlinarith only [mul_le_mul_of_nonneg_left x (Nat.cast_nonneg f : (0:ℚ)≤f),
        mul_le_mul_of_nonneg_left y (Nat.cast_nonneg g : (0:ℚ)≤g)])

theorem contradiction (c : Family r) (f g x : ℕ) (big : 128≤x) (cf : f+g≤x) (cl : c.L≤x) (errorCap : 2*r*2^r≤x)
    (separated : ∀ b, (f+g)*dust c b ≠ f*NX c b+g*NY c b)
    (close : |score f g (exactX c) (exactY c)-(f+g:ℕ)| ≤ 1/((x^(degree r):ℕ):ℚ)) : False := by
  let point : Fin r ⊕ Fin r → ℕ := Sum.elim c.p (fun i=>c.p i^c.e i)
  obtain ⟨j,band⟩:=empty_band x (by omega) point
  have bp (i:Fin r) := band (Sum.inl i)
  have bd (i:Fin r) := band (Sum.inr i)
  let Q:=cut r x j.val
  let N:=cut r x (j.val+1)
  let b (i:Fin r) : Option Bool := if c.p i^c.e i≤Q then none else some (decide (c.p i≤Q))
  have next : N=Q^(3*r+4) := cut_succ ..
  have xQ : x≤Q := by
    have old:=cut_mono r (show 1≤x by omega) (Nat.zero_le j.val)
    simpa [cut,Q] using old
  have np : 0<N := by rw [next];exact pow_pos (by omega) _
  have nb : N≤x^(degree r):=cut_mono r (by omega) (show j.val+1≤2*r+1 by omega)
  have space (i) (t:Bool) (mode:b i=some t) : N ≤ (if t then c.p i^c.e i else c.p i) := by
    dsimp [b] at mode
    split at mode
    next=>contradiction
    next off=>
      obtain rfl:=Option.some.inj mode
      by_cases lo : c.p i≤Q
      · simp [lo]
        exact ((bd i).resolve_left off).le
      · simp [lo]
        exact ((bp i).resolve_left lo).le
  have ds : dust c b≤Q^(3*r) := by
    have per i : Dn (c.p i) (c.e i) (b i)≤Q^3 := by
      have el := (c.cap i).trans (cl.trans xQ)
      by_cases exactMode : c.p i^c.e i≤Q
      · rw [show b i=none from if_pos exactMode]
        change (c.e i+1)*(c.p i^c.e i)≤Q^3
        exact
          (Nat.mul_le_mul el exactMode).trans (show Q*Q≤Q^3 by rw [←sq];exact Nat.pow_le_pow_right (by omega) (by decide))
      · by_cases keep:c.p i≤Q
        · simpa [b,exactMode,keep,Dn,den] using
            (Nat.mul_le_mul el (Nat.pow_le_pow_left (show c.p i-1≤Q by omega) 2)).trans_eq (by ring : Q*Q^2=Q^3)
        · simpa [b,exactMode,keep,Dn,den] using el.trans (Nat.le_self_pow (by decide : 3≠0) Q)
    dsimp [dust]
    exact (prod_le_prod' (fun i _=>per i)).trans_eq (by simp [←pow_mul])
  have nz:=separated b
  have iga:=integer_gap c b f g nz
  let orig:=score f g (exactX c) (exactY c)
  let approx:=score f g (x' c b) (y' c b)
  let W:ℚ:=(f+g:ℕ)
  have lite : |orig-W|≤1/(N:ℚ) := close.trans (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast nb))
  have diff:=difference c b f g N np space
  change |approx-orig|≤_ at diff
  change (1:ℚ)≤|approx-W| * dust c b at iga
  have err : |approx-W| * (N:ℚ)≤(2*r*2^r:ℕ)*((f:ℚ)+g)+1 := by
    have t:=abs_sub_le approx orig W
    have wn : (0:ℚ)<N:=by exact_mod_cast np
    nlinarith only [mul_le_mul_of_nonneg_right t wn.le,(le_div_iff₀ wn).mp diff,(le_div_iff₀ wn).mp lite]
  have sep : N≤((2*r*2^r)*(f+g)+1)*dust c b := by
    have z : (N:ℚ)≤((2*r*2^r:ℕ)*((f:ℚ)+g)+1)*dust c b := by
      nlinarith only [mul_le_mul_of_nonneg_right iga (Nat.cast_nonneg N : (0:ℚ)≤N),
        mul_le_mul_of_nonneg_right err (Nat.cast_nonneg (dust c b) : (0:ℚ)≤_)]
    exact_mod_cast z
  have qr : 128≤Q:=big.trans xQ
  have cfq : f+g≤Q:=cf.trans xQ
  have rate : 2*r*2^r≤Q := errorCap.trans xQ
  have cf' : (2*r*2^r)*(f+g)+1<Q^3 := by
    have m:=Nat.mul_le_mul rate cfq
    have grow:=Nat.mul_le_mul_left (Q*Q) (show 2≤Q by omega)
    nlinarith only [m,grow,qr,Nat.mul_self_le_mul_self (show 2≤Q by omega)]
  have bad : N < Q^(3+3*r) := sep.trans_lt ((Nat.mul_lt_mul_of_lt_of_le cf' ds
    (pow_pos (by omega) _)).trans_eq (by rw [pow_add]))
  have natural : Q^(3+3*r)≤N:=next ▸ Nat.pow_le_pow_right (by omega) (by omega)
  omega

end OMA.FixedRankStep245212

end

section

/- A polynomial-width empty interval producing an exact mixed equality at any rank. -/
namespace OMA.FixedModeWitness245212
open Nat Finset OMA.TwoTallLocal245212 OMA.ThreeMovingLocal245212 OMA.FixedRankGap245212 OMA.FixedRankStep245212
open OMA.FixedRankStep245212 (integer_gap)
open OMA.FixedRankStep245212 (difference)
variable {r : ℕ}

theorem witness (c : Family r) (f g x : ℕ) (big : 128≤x) (cf : f+g≤x) (cl : c.L≤x) (errorCap : 2*r*2^r≤x)
    (actual : score f g (exactX c) (exactY c)=(f+g:ℕ)) :
    ∃ (b : Fin r→Option Bool) (Q : ℕ), x≤Q ∧ Q≤x^(degree r) ∧
      (∀i,b i=if c.p i^c.e i≤Q then none else some (decide (c.p i≤Q))) ∧
      (f+g)*dust c b=f*NX c b+g*NY c b := by
  have close : |score f g (exactX c) (exactY c)-(f+g:ℕ)| ≤ 1/((x^(degree r):ℕ):ℚ):=by
    rw [actual,sub_self,abs_zero];positivity
  let point : Fin r ⊕ Fin r → ℕ := Sum.elim c.p (fun i=>c.p i^c.e i)
  obtain ⟨j,band⟩:=empty_band x (by omega) point
  have bp (i:Fin r) := band (Sum.inl i)
  have bd (i:Fin r) := band (Sum.inr i)
  let Q:=cut r x j.val
  let N:=cut r x (j.val+1)
  let b (i:Fin r) : Option Bool := if c.p i^c.e i≤Q then none else some (decide (c.p i≤Q))
  have next : N=Q^(3*r+4) := cut_succ ..
  have xQ : x≤Q := by
    have old:=cut_mono r (show 1≤x by omega) (Nat.zero_le j.val)
    simpa [cut,Q] using old
  have np : 0<N := by rw [next];exact pow_pos (by omega) _
  have nb : N≤x^(degree r):=cut_mono r (by omega) (show j.val+1≤2*r+1 by omega)
  have space (i) (t:Bool) (mode:b i=some t) : N ≤ (if t then c.p i^c.e i else c.p i) := by
    dsimp [b] at mode
    split at mode
    next=>contradiction
    next off=>
      obtain rfl:=Option.some.inj mode
      by_cases lo : c.p i≤Q
      · simp [lo]
        exact ((bd i).resolve_left off).le
      · simp [lo]
        exact ((bp i).resolve_left lo).le
  have ds : dust c b≤Q^(3*r) := by
    have per i : Dn (c.p i) (c.e i) (b i)≤Q^3 := by
      have el := (c.cap i).trans (cl.trans xQ)
      by_cases exactMode : c.p i^c.e i≤Q
      · rw [show b i=none from if_pos exactMode]
        change (c.e i+1)*(c.p i^c.e i)≤Q^3
        exact
          (Nat.mul_le_mul el exactMode).trans (show Q*Q≤Q^3 by rw [←sq];exact Nat.pow_le_pow_right (by omega) (by decide))
      · by_cases keep:c.p i≤Q
        · simpa [b,exactMode,keep,Dn,den] using
            (Nat.mul_le_mul el (Nat.pow_le_pow_left (show c.p i-1≤Q by omega) 2)).trans_eq (by ring : Q*Q^2=Q^3)
        · simpa [b,exactMode,keep,Dn,den] using el.trans (Nat.le_self_pow (by decide : 3≠0) Q)
    dsimp [dust]
    exact (prod_le_prod' (fun i _=>per i)).trans_eq (by simp [←pow_mul])
  have below:=cut_mono r (show 1≤x by omega) (show j.val≤2*r+1 by omega)
  refine ⟨b,Q,xQ,below,fun _=>rfl,?_⟩
  by_contra nz
  have iga:=OMA.FixedRankStep245212.integer_gap c b f g nz
  let orig:=score f g (exactX c) (exactY c)
  let approx:=score f g (x' c b) (y' c b)
  let W:ℚ:=(f+g:ℕ)
  have lite : |orig-W|≤1/(N:ℚ) := close.trans (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast nb))
  have diff:=OMA.FixedRankStep245212.difference c b f g N np space
  change |approx-orig|≤_ at diff
  change (1:ℚ)≤|approx-W| * dust c b at iga
  have err : |approx-W| * (N:ℚ)≤(2*r*2^r:ℕ)*((f:ℚ)+g)+1 := by
    have t:=abs_sub_le approx orig W
    have wn : (0:ℚ)<N:=by exact_mod_cast np
    nlinarith only [mul_le_mul_of_nonneg_right t wn.le,(le_div_iff₀ wn).mp diff,(le_div_iff₀ wn).mp lite]
  have sep : N≤((2*r*2^r)*(f+g)+1)*dust c b := by
    have z : (N:ℚ)≤((2*r*2^r:ℕ)*((f:ℚ)+g)+1)*dust c b := by
      nlinarith only [mul_le_mul_of_nonneg_right iga (Nat.cast_nonneg N : (0:ℚ)≤N),
        mul_le_mul_of_nonneg_right err (Nat.cast_nonneg (dust c b) : (0:ℚ)≤_)]
    exact_mod_cast z
  have qr : 128≤Q:=big.trans xQ
  have cfq : f+g≤Q:=cf.trans xQ
  have rate : 2*r*2^r≤Q := errorCap.trans xQ
  have cf' : (2*r*2^r)*(f+g)+1<Q^3 := by
    have m:=Nat.mul_le_mul rate cfq
    have grow:=Nat.mul_le_mul_left (Q*Q) (show 2≤Q by omega)
    nlinarith only [m,grow,qr,Nat.mul_self_le_mul_self (show 2≤Q by omega)]
  have bad : N < Q^(3+3*r) := sep.trans_lt ((Nat.mul_lt_mul_of_lt_of_le cf' ds
    (pow_pos (by omega) _)).trans_eq (by rw [pow_add]))
  have natural : Q^(3+3*r)≤N:=next ▸ Nat.pow_le_pow_right (by omega) (by omega)
  omega

end OMA.FixedModeWitness245212

end

section

/- A polynomial-width interval around all six scales furnishes an exact mixed equality. -/
namespace OMA.MiddleWitness245212
open Nat Finset OMA.SingleMovingGap245212 OMA.TwoTallLocal245212 OMA.ThreeMovingLocal245212
open OMA.TwoTallScalar245212 (cut cut_mono cut_succ)
open OMA.SingleMovingStep245212 (empty_six degree)
open OMA.SingleMovingStep245212 (integer_gap)
open OMA.SingleMovingStep245212 (difference)
theorem witness (c : Family) (f g x : ℕ) (big : 128≤x) (cf : f+g≤x) (cl : c.L≤x)
    (actual : score f g (exactX c) (exactY c)=(f+g:ℕ)) :
    ∃ (b : Fin 3→Option Bool) (Q : ℕ), x≤Q ∧ Q≤x^degree ∧
    (∀ i,b i=if c.p i^c.e i≤Q then none else some (decide (c.p i≤Q))) ∧
    (f+g)*dust c b=f*NX c b+g*NY c b := by
  have close : |score f g (exactX c) (exactY c)-(f+g:ℕ)| ≤ 1/((x^degree:ℕ):ℚ):=by
    rw [actual,sub_self,abs_zero];positivity
  let point : Fin 6 → ℕ := ![c.p 0,c.p 1,c.p 2,c.p 0^c.e 0,c.p 1^c.e 1,c.p 2^c.e 2]
  obtain ⟨j,band⟩:=empty_six x (by omega) point
  have bp (i:Fin 3) : c.p i≤cut x j.val ∨ cut x (j.val+1)<c.p i := by
    fin_cases i <;> first | exact band 0 | exact band 1 | exact band 2
  have bd (i:Fin 3) : c.p i^c.e i≤cut x j.val ∨ cut x (j.val+1)<c.p i^c.e i := by
    fin_cases i <;> first | exact band 3 | exact band 4 | exact band 5
  let Q:=cut x j.val
  let N:=cut x (j.val+1)
  let b (i:Fin 3) : Option Bool := if c.p i^c.e i≤Q then none else some (decide (c.p i≤Q))
  have next : N=Q^16 := cut_succ x _
  have xQ : x≤Q := by
    have old:=cut_mono (show 1≤x by omega) (Nat.zero_le j.val)
    simpa [cut,Q] using old
  have np : 0<N := by rw [next];exact pow_pos (by omega) _
  have nb : N≤x^degree:=cut_mono (by omega) (show j.val+1≤7 by omega)
  have space (i) (t:Bool) (mode:b i=some t) : N ≤ (if t then c.p i^c.e i else c.p i) := by
    dsimp [b] at mode
    split at mode
    next=>contradiction
    next off=>
      obtain rfl:=Option.some.inj mode
      by_cases lo : c.p i≤Q
      · simp [lo]
        exact ((bd i).resolve_left off).le
      · simpa [lo] using ((bp i).resolve_left lo).le
  have ds : dust c b≤Q^9 := by
    have per i : Dn (c.p i) (c.e i) (b i)≤Q^3 := by
      have el := (c.cap i).trans (cl.trans xQ)
      by_cases exactMode : c.p i^c.e i≤Q
      · rw [show b i=none from if_pos exactMode]
        change (c.e i+1)*(c.p i^c.e i)≤Q^3
        exact
          (Nat.mul_le_mul el exactMode).trans (show Q*Q≤Q^3 by rw [←sq];exact Nat.pow_le_pow_right (by omega) (by decide))
      · by_cases keep:c.p i≤Q
        · simpa [b,exactMode,keep,Dn,den] using
            (Nat.mul_le_mul el (Nat.pow_le_pow_left (show c.p i-1≤Q by omega) 2)).trans_eq (by ring : Q*Q^2=Q^3)
        · simpa [b,exactMode,keep,Dn,den] using el.trans (Nat.le_self_pow (by decide : 3≠0) Q)
    dsimp [dust]
    exact (prod_le_prod' (fun i _=>per i)).trans_eq (by simp;ring)
  have maxcut : Q≤x^degree:=cut_mono (by omega) (show j.val≤7 by omega)
  refine ⟨b,Q,xQ,maxcut,(fun i=>rfl),?_⟩
  by_contra nz
  have iga:=OMA.SingleMovingStep245212.integer_gap c b f g nz
  let orig:=score f g (exactX c) (exactY c)
  let approx:=score f g (x' c b) (y' c b)
  let W:ℚ:=(f+g:ℕ)
  have lite : |orig-W|≤1/(N:ℚ) := close.trans (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast nb))
  have diff:=OMA.SingleMovingStep245212.difference c b f g N np space
  change |approx-orig|≤_ at diff
  change (1:ℚ)≤|approx-W| * dust c b at iga
  have err : |approx-W| * (N:ℚ)≤48*((f:ℚ)+g)+1 := by
    have t:=abs_sub_le approx orig W
    have wn : (0:ℚ)<N:=by exact_mod_cast np
    nlinarith only [mul_le_mul_of_nonneg_right t wn.le,(le_div_iff₀ wn).mp diff,(le_div_iff₀ wn).mp lite]
  have sep : N≤(48*(f+g)+1)*dust c b := by
    have z : (N:ℚ)≤(48*((f:ℚ)+g)+1)*dust c b := by
      nlinarith only [mul_le_mul_of_nonneg_right iga (Nat.cast_nonneg N : (0:ℚ)≤N),
        mul_le_mul_of_nonneg_right err (Nat.cast_nonneg (dust c b) : (0:ℚ)≤_)]
    exact_mod_cast z
  have qr : 128≤Q:=big.trans xQ
  have cfq : f+g≤Q:=cf.trans xQ
  have cf' : 48*(f+g)+1<Q^2 := by
    nlinarith only [cfq,Nat.mul_le_mul_left Q qr,qr]
  have bad : N<Q^11 := sep.trans_lt ((Nat.mul_lt_mul_of_lt_of_le cf' ds (pow_pos (by omega) 9)).trans_eq (by ring))
  have natural : Q^11≤N:=next ▸ Nat.pow_le_pow_right (by omega) (by decide)
  omega



end OMA.MiddleWitness245212

end

section

/- The dyadic factor of every solution with three distinct odd primes
is polynomially bounded in the largest odd exponent length. -/
namespace OMA.SingleMovingOriginal245212
open Nat Finset ArithmeticFunction OMA.SingleMovingGap245212 OMA.SingleMovingStep245212
open OMA.ThreeMovingOriginal245212 (F G)
open OMA.TwoTallScalar245212 (base)
open OMA.Smooth245212 (total W)
open scoped ArithmeticFunction.sigma
open OMA.ComplementaryLocal245212 (binary)
private theorem identities (k : ℕ) : 0<G k ∧ F k+G k=(k+1)*2^(k+1) ∧ F k=k*G k+(k+1) := by
  have g:=Nat.two_pow_pos k
  dsimp [F,G];rw [pow_succ]
  have sub:=Nat.sub_add_cancel (show 1≤2^k*2 by omega)
  exact ⟨by omega,by nlinarith only [sub],by nlinarith only [congrArg (k*·) sub]⟩


theorem physical (c : Family) (k : ℕ) (op : ∀i,Odd (c.p i)) (inj : c.p.Injective)
    (eqn : OeisA245212.a (2^k*total c.p c.e)=(σ 1 (2^k*total c.p c.e):ℤ)) :
    score (F k) (G k) (exactX c) (exactY c)=(F k+G k:ℕ) := by
  let t:=2^k*σ 0 (2^k)
  have t0 : 0<t := Nat.mul_pos (Nat.two_pow_pos k) (sigma_pos 0 _ (Nat.two_pow_pos k).ne')
  have norm:=OMA.CofactorCrossOriginal245212.normalized_extension (p:=c.p) (e:=c.e) (Nat.two_pow_pos k)
    c.prime inj (fun i=>(Nat.coprime_two_left.mpr (op i)).pow_left k) eqn
  change ((W (2^k):ℚ)/t)*(∏i,exactX c i)+((σ 1 (2^k):ℚ)/t)*(∏i,exactY c i)=2 at norm
  field_simp [show (t:ℚ)≠0 by exact_mod_cast t0.ne'] at norm
  have z0:=Nat.two_pow_pos (k+1)
  have gold : σ 1 (2^k)=G k := by
    dsimp [G];zify [Nat.cast_sub (show 1≤2^(k+1) from z0)]
    exact (OMA.ComplementaryLocal245212.binary k).1
  have fold : W (2^k)=F k := by exact_mod_cast (OMA.ComplementaryLocal245212.binary k).2
  have ht : 2*t=F k+G k := by
    dsimp [t];rw [sigma_zero_apply_prime_pow Nat.prime_two,(identities k).2.1,pow_succ];ring
  rw [gold,fold] at norm
  dsimp [score];rw [←ht];push_cast;linarith only [norm]


theorem coarse (c : Family) (op : ∀i,Odd (c.p i))
    (eqn : OeisA245212.a (2^c.k*total c.p c.e)=(σ 1 (2^c.k*total c.p c.e):ℤ)) :
    G c.k < 8*(c.k+1)*(base c.k c.L)^degree := by
  have exact:=physical c c.k op c.inj eqn
  let x:=base c.k c.L
  have big : 128≤x := by dsimp [base,x];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
  have cf : c.k+1≤x := by dsimp [base,x];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
  have cl : c.L≤x := by dsimp [base,x];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
  have dx : 1≤x:=by omega
  have r0 := (identities c.k).1
  let PX:=∏i,exactX c i
  let PY:=∏i,exactY c i
  have xb i := OMA.TwoTallLocal245212.ranges (c.prime i) (c.positive i) none
  have low : (1:ℚ)≤PX:=one_le_prod (fun i _=>(xb i).1)
  have top : PX≤8 := calc
    _ ≤ ∏_i:Fin 3,(2:ℚ) := prod_le_prod (fun i _=>zero_le_one.trans (xb i).1) (fun i _=>(xb i).2.1)
    _ = _ := by norm_num
  have id : (G c.k:ℚ)*((c.k:ℚ)+1-score c.k 1 (exactX c) (exactY c))=((c.k:ℚ)+1)*(PX-1) := by
    change (F c.k:ℚ)*PX+(G c.k:ℚ)*PY=(F c.k+G c.k:ℕ) at exact
    change _*((c.k:ℚ)+1-((c.k:ℚ)*PX+(1:ℕ)*PY))=_
    have f : (F c.k:ℚ)=(c.k:ℚ)*G c.k+(c.k+1:ℕ) := by exact_mod_cast (identities c.k).2.2
    push_cast at f exact ⊢
    linear_combination -exact+(PX-1)*f
  have gp : (0:ℚ)<G c.k := by exact_mod_cast r0
  by_contra! ample
  have below : score c.k 1 (exactX c) (exactY c)≤(c.k+1:ℕ):=by
    push_cast
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right (id ▸ mul_nonneg (by positivity) (sub_nonneg.mpr low)) gp)
  have close : |score c.k 1 (exactX c) (exactY c)-(c.k+1:ℕ)|≤1/((x^degree:ℕ):ℚ) := by
    rw [abs_of_nonpos (sub_nonpos.mpr below),neg_sub]
    have h : (((c.k+1:ℕ):ℚ)-score c.k 1 (exactX c) (exactY c))*(x^degree:ℕ)≤1 := by
      apply le_of_mul_le_mul_left (a:=(G c.k:ℚ)) _ gp
      have g0 : (8:ℚ)*(c.k+1)*(x^degree:ℕ)≤G c.k:=by exact_mod_cast ample
      push_cast at g0 ⊢
      nlinarith only [congrArg (·*(x:ℚ)^degree) id,g0,
        mul_le_mul_of_nonneg_right (show PX-1≤8 by linarith) (show 0≤((c.k:ℚ)+1)*x^degree by positivity)]
    exact (le_div_iff₀ (by exact_mod_cast pow_pos dx degree : (0:ℚ)<(x^degree:ℕ))).mpr h

  apply OMA.SingleMovingStep245212.contradiction c c.k 1 x big cf cl _ close
  intro b
  have link : OMA.SingleMovingProxy245212.deficit c*(G c.k:ℕ)=((c.k:ℚ)+1)*((∏i,exactX c i)-1) := by
    simpa only [OMA.SingleMovingProxy245212.deficit,mul_comm] using id
  simpa only [one_mul] using OMA.SingleMovingProxy245212.separated c b link

end OMA.SingleMovingOriginal245212

end

section

/- Explicit polynomial control on the dyadic prime power in terms of
the largest odd exponent length alone. -/
namespace OMA.SingleMovingHeight245212
open Nat Finset ArithmeticFunction
open OMA.ThreeMovingOriginal245212 (G)
open OMA.TwoTallScalar245212 (base)
open OMA.SingleMovingStep245212 (degree)
open OMA.SingleMovingGap245212 (Family)
open OMA.Smooth245212 (total)
open scoped ArithmeticFunction.sigma

def constant (D : ℕ) := 2^(16*(D+2)^2+8)+(16*128^D)^2

private theorem eliminate {k L D : ℕ}
    (h : 2^k ≤ 8*(k+1)*(base k L)^D) :
    2^k ≤ constant D*(L+1)^(2*D) := by
  have pos : 1≤(L+1)^(2*D):=Nat.one_le_pow _ _ (by omega)
  by_cases large : 16*(D+2)^2≤k+2
  · have grow:=OMA.ComplementarySize245212.absorb (b:=k+2) (d:=D+1) (by simpa [Nat.add_assoc] using large)
    let C : ℕ := 8*128^D
    have e : 2^k≤C*(k+2)^(D+1)*(L+1)^D := calc
      _ ≤ _ := h
      _ ≤ 8*(k+2)*(base k L)^D := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by simp only [base,mul_pow,C,pow_succ];ring
    have z:=Nat.pow_le_pow_left e 2
    have powers : ((k+2)^(D+1))^2 ≤ 2^k*4 := by
      rw [←pow_mul,mul_comm (D+1) 2,←show (2:ℕ)^(k+2)=2^k*4 by rw [pow_add];rfl]
      exact grow
    have w : 2^k*2^k ≤ 2^k*((16*128^D)^2*(L+1)^(2*D)) := calc
      _ = (2^k)^2 := (sq _).symm
      _ ≤ _ := z
      _ = C^2*((k+2)^(D+1))^2*((L+1)^D)^2 := by ring
      _ ≤ C^2*(2^k*4)*((L+1)^D)^2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ powers)
      _ = _ := by rw [←pow_mul,mul_comm D 2];dsimp [C];ring
    exact (Nat.le_of_mul_le_mul_left w (Nat.two_pow_pos k)).trans
      (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))
  · have top : k≤16*(D+2)^2+8:=by omega
    have bounded := Nat.pow_le_pow_right (by decide : 1≤2) top
    exact bounded.trans ((Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_right _ pos))

theorem all_k {k L D : ℕ}
    (coarse : 8≤k → G k < 8*(k+1)*(base k L)^D) :
    2^k ≤constant D*(L+1)^(2*D) := by
  by_cases hk : 8≤k
  · have h := coarse hk
    have ge : 2^k≤G k:=by
      have := Nat.two_pow_pos k
      dsimp [G];rw [pow_succ];omega
    exact eliminate (ge.trans h.le)
  · have : 2^k≤(2:ℕ)^8:=Nat.pow_le_pow_right (by decide) (by omega)
    have high : (2:ℕ)^8≤2^(16*(D+2)^2+8):=Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _)
    exact this.trans (high.trans ((Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_right _
      (pow_pos (by omega) _))))

theorem original (k L : ℕ) (p e : Fin 3→ℕ) (prime : ∀ i,(p i).Prime)
    (odd : ∀ i,Odd (p i)) (distinct : p.Injective) (positive : ∀i,0<e i)
    (longest : ∃ i,e i+1=L) (cap : ∀i,e i+1≤L)
    (eqn : OeisA245212.a (2^k*total p e)=(σ 1 (2^k*total p e):ℤ)) :
    2^k≤constant degree*(L+1)^(2*degree) := by
  apply all_k
  intro hk
  let c : Family := ⟨p,e,k,L,prime,positive,hk,longest,cap,distinct⟩
  exact OMA.SingleMovingOriginal245212.coarse c odd eqn

end OMA.SingleMovingHeight245212

end

section

/- The ordinary moments at the other two primes can never reverse the sign
for the smallest base when it carries the longest exponent. -/
namespace OMA.LeastTallFactor245212
open Nat Finset OMA.TwoTallLocal245212 OMA.SingleMovingGap245212
open OMA.Smooth245212 (X Y y_nonneg)
open OMA.ThreeMovingLocal245212 (yy yn den)
open OMA.ThreeMovingLocal245212 (quotients)

theorem localY {p e : ℕ} (hp : p.Prime) (he : 0<e) (big : 33≤p) (mode : Option Bool) :
    yy' p e mode≤33/64 := by
  have pr : (33:ℚ)≤p:=by exact_mod_cast big
  have ep : (1:ℚ)≤e:=by exact_mod_cast he
  have B : (0:ℚ)<(e:ℚ)+1:=by positivity
  have u : (0:ℚ)<(p:ℚ)-1:=by linarith
  have yn : yy p e true = (p:ℚ)/(((e:ℚ)+1)*(p-1)) := by
    dsimp [yy,OMA.ThreeMovingLocal245212.yn,den]
    push_cast [Nat.cast_sub hp.one_le];field_simp
  have yb : yy p e true≤33/64 := by
    rw [yn,div_le_iff₀ (mul_pos B u)]
    nlinarith only [pr,mul_nonneg (sub_nonneg.mpr ep) u.le]
  rcases mode with _|b
  · have q:=(OMA.ThreeMovingLocal245212.quotients (e:=e) hp).2
    change Y p (some e)≤33/64
    have pw : 0< (p:ℚ)^e := by positivity
    have dn : 0≤1/(((e:ℚ)+1)*((p:ℚ)-1)^2*(p:ℚ)^e):=by positivity
    linarith only [q,mul_nonneg u.le dn,yb]
  · cases b
    · change yy p e false≤_
      simp [yy,OMA.ThreeMovingLocal245212.yn,den]
      rw [←one_div];apply (div_le_iff₀ B).mpr;linarith only [ep]
    · exact yb

private theorem localX {z p e : ℕ} (zp : 33≤z) (le : z≤p) (hp : p.Prime) (ep : 0<e) :
    1≤X p (some e) ∧ X p (some e)≤33/32 ∧ ((z:ℚ)-1)*(X p (some e)-1)≤1 := by
  have low : 1≤X p (some e):=(ranges hp ep none).1
  have zlow : (32:ℚ)≤(z:ℚ)-1:=by
    have h : (33:ℚ)≤z:=by exact_mod_cast zp
    linarith
  have v : (z:ℚ)≤p:=by exact_mod_cast le
  have den : (0:ℚ)<(p:ℚ)-1:=by linarith
  have eq : ((p:ℚ)-1)*(X p (some e)-1) = 1-Y p (some e) := by
    dsimp [X];field_simp;ring
  have Y0:=y_nonneg hp.one_lt (some e)
  have h : ((z:ℚ)-1)*(X p (some e)-1)≤1 := by
    nlinarith only [eq,Y0,mul_nonneg (sub_nonneg.mpr v) (sub_nonneg.mpr low)]
  refine ⟨low,?_,h⟩
  nlinarith only [h,mul_nonneg (sub_nonneg.mpr zlow) (sub_nonneg.mpr low)]

theorem margin (c : Family) {f g : ℕ} {v : Fin 3} (long : c.e v+1=c.L)
    (least : ∀i,c.p v≤c.p i) (large : 33≤c.p v) (tall : 32≤c.L) (gp : 0<g)
    (actual : score f g (exactX c) (exactY c)=(f+g:ℕ)) :
    (g:ℚ)*((c.p v:ℚ)-1)*(33/64)^2 < f := by
  let P:=∏i,exactX c i
  let S:=∏i,exactY c i
  let u:ℚ:=(c.p v:ℚ)-1
  have loc i := localX large (least i) (c.prime i) (c.positive i)
  change ∀i, 1≤exactX c i ∧ exactX c i≤33/32 ∧ u*(exactX c i-1)≤1 at loc
  have p0 i := (zero_le_one.trans (loc i).1)
  have Xprod : u*(P-1) ≤ 13/4 := by
    let x:=exactX c
    have a:=mul_le_mul_of_nonneg_right (loc 0).2.2 (mul_nonneg (p0 1) (p0 2))
    have b:=mul_le_mul_of_nonneg_right (loc 1).2.2 (p0 2)
    have d:=mul_le_mul (loc 1).2.1 (loc 2).2.1 (p0 2) (by norm_num : (0:ℚ)≤33/32)
    dsimp only [P];rw [Fin.prod_univ_three]
    nlinarith only [a,b,d,(loc 2).2.2,(loc 2).2.1]
  have nonY i : 0≤exactY c i := (ranges (c.prime i) (c.positive i) none).2.2.1
  have bound i : exactY c i≤1 := (localY (c.prime i) (c.positive i) (large.trans (least i)) none).trans (by norm_num)
  have s := (ranges (c.prime v) (c.positive v) none).2.2.2
  change exactY c v≤2/((c.e v:ℚ)+1) at s
  have T : (32:ℚ)≤(c.e v:ℚ)+1:=by exact_mod_cast (long ▸ tall : 32≤c.e v+1)
  have lowS : S≤1/16 := by
    calc
      _ = (∏ i∈univ.erase v,exactY c i)*exactY c v := (prod_erase_mul _ _ (mem_univ v)).symm
      _ ≤ exactY c v := mul_le_of_le_one_left (nonY v) (prod_le_one (fun j _=>nonY j) (fun j _=>bound j))
      _ ≤ _ := s.trans ((div_le_iff₀ (by positivity)).mpr (by linarith only [T]))
  change (f:ℚ)*P+(g:ℚ)*S=(f+g:ℕ) at actual
  push_cast at actual
  have m : 0≤P-1:=sub_nonneg.mpr (one_le_prod (fun i _=>(loc i).1))
  have g0 : (0:ℚ)<g:=by exact_mod_cast gp
  by_contra! neg
  change (f:ℚ)≤(g:ℚ)*u*(33/64)^2 at neg
  nlinarith only [actual,mul_le_mul_of_nonneg_right neg m,mul_le_mul_of_nonneg_left Xprod g0.le,
    mul_le_mul_of_nonneg_left lowS g0.le,g0]

end OMA.LeastTallFactor245212

end

section

/- Exact and one-sided changes on restoring one coordinate, with arbitrary
values of the other two moments already multiplied together. -/
namespace OMA.MiddleChange245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.TwoTallLocal245212
open OMA.ThreeMovingLocal245212 (xx yy xn yn den)
open scoped ArithmeticFunction.sigma
open OMA.ThreeMovingLocal245212 (quotients)

def inc (p e f g : ℕ) (b : Option Bool) (x y : ℚ) :=
  (f:ℚ)*(X p (some e)-xx' p e b)*x+(g:ℚ)*(Y p (some e)-yy' p e b)*y

theorem exact_inc (p e f g : ℕ) (x y : ℚ) : inc p e f g none x y=0 := by
  simp [inc,xx',yy']

theorem dropped {p e f g : ℕ} (hp : p.Prime) (ep : 0<e) {x y : ℚ} (xo : 1≤x) (yo : 0≤y) :
    (f:ℚ)/(2*p)≤ inc p e f g (some false) x y := by
  have ps : (0:ℚ)<p:=by exact_mod_cast hp.pos
  have B : (0:ℚ)<(e:ℚ)+1:=by positivity
  have low:=OMA.SingleMovingLoss245212.single_lb hp ep
  have low' : 1/(2*(p:ℚ))≤X p (some e)-1 :=
    (div_le_iff₀ (by positivity)).mpr (by linarith only [low])
  have xx : xx' p e (some false)=1:=by simp [xx',OMA.ThreeMovingLocal245212.xx,xn,den,B.ne']
  have yy : yy' p e (some false)=1/((e:ℚ)+1):=by simp [yy',OMA.ThreeMovingLocal245212.yy,yn,den]
  have ys : 1/((e:ℚ)+1)≤Y p (some e):=by
    have id:=y_factor hp e
    have high : (p:ℚ)^e≤σ 1 (p^e):=by
      exact_mod_cast (show p^e ≤ σ 1 (p^e) by rw [sigma_one_apply_prime_pow hp,sum_range_succ];omega)
    apply (div_le_iff₀ B).mpr
    apply le_of_mul_le_mul_right (a:=(p:ℚ)^e) _ (by positivity)
    nlinarith only [id,high]
  rw [inc,xx,yy]
  have dy:=mul_nonneg (mul_nonneg (Nat.cast_nonneg (α:=ℚ) g) (sub_nonneg.mpr ys)) yo
  have dx : (f:ℚ)*(X p (some e)-1)≥f/(2*p):=by
    rw [div_eq_mul_inv,←one_div]
    exact mul_le_mul_of_nonneg_left low' (by positivity)
  nlinarith only [dx,dy,mul_nonneg (mul_nonneg (Nat.cast_nonneg (α:=ℚ) f)
    (le_trans (by positivity) low')) (sub_nonneg.mpr xo)]

theorem retained {p e f g : ℕ} (hp : p.Prime) (x y : ℚ) :
    inc p e f g (some true) x y =
      ((f:ℚ)*x-g*((p:ℚ)-1)*y)/(((e:ℚ)+1)*((p:ℚ)-1)^2*(p:ℚ)^e) := by
  have z:=OMA.ThreeMovingLocal245212.quotients (e:=e) hp
  rw [inc,z.1,z.2]; dsimp [xx',yy'];ring

theorem retained_loss {p e f g : ℕ} (hp : p.Prime) {x y : ℚ} (xo : 0≤x) (yo : y≤1) :
    -(g:ℚ)/(p:ℚ)^e ≤ inc p e f g (some true) x y := by
  have pp : (2:ℚ)≤p:=by exact_mod_cast hp.two_le
  let u:ℚ:=(p:ℚ)-1
  have up : 1≤u:=by dsimp [u];linarith
  have ppw : 0<(p:ℚ)^e:=by positivity
  rw [retained hp]
  change _≤(_-g*u*y)/(((e:ℚ)+1)*u^2*(p:ℚ)^e)
  apply (div_le_div_iff₀ ppw (by positivity)).mpr
  have sz : u ≤ ((e:ℚ)+1)*u^2 := by
    nlinarith only [mul_nonneg (zero_le_one.trans up) (sub_nonneg.mpr up),mul_nonneg (Nat.cast_nonneg (α:=ℚ) e) (sq_nonneg u),up]
  have v := mul_le_mul_of_nonneg_left yo (mul_nonneg (Nat.cast_nonneg (α:=ℚ) g) (by linarith : 0≤u))
  nlinarith only [mul_le_mul_of_nonneg_right v ppw.le,
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left sz (Nat.cast_nonneg (α:=ℚ) g)) ppw.le,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg (α:=ℚ) f) xo) ppw.le]

theorem retained_gain {p e f g k L : ℕ} (hp : p.Prime) (hk : 8≤k) (fg : k*g≤f)
    (base : p≤L) (len : e+1≤L) {x y : ℚ} (xo : 1≤x) (yo : 0≤y) (short : y*L≤2) :
    (g:ℚ)/((L:ℚ)^3*(p:ℚ)^e) ≤ inc p e f g (some true) x y := by
  have pp : (1:ℚ)<p:=by exact_mod_cast hp.one_lt
  have lp : (0:ℚ)<L:=by exact_mod_cast (hp.pos.trans_le base)
  let u:ℚ:=(p:ℚ)-1
  have up : 0<u:=by dsimp [u];linarith
  have ub : u≤L:=by
    have v : (p:ℚ)≤L:=by exact_mod_cast base
    dsimp [u];linarith
  have ecap : (e:ℚ)+1≤L:=by exact_mod_cast len
  have dx : ((e:ℚ)+1)*u^2 ≤(L:ℚ)^3:=by
    calc
      _ ≤ (L:ℚ)*(L:ℚ)^2:=mul_le_mul ecap (pow_le_pow_left₀ up.le ub _) (sq_nonneg _) lp.le
      _ = _ := by ring
  have fk : (k:ℚ)*g≤f:=by exact_mod_cast fg
  have k8 : (8:ℚ)≤k:=by exact_mod_cast hk
  have ft : (g:ℚ)≤(f:ℚ)*x-g*u*y:=by
    nlinarith only [mul_le_mul_of_nonneg_left xo (Nat.cast_nonneg (α:=ℚ) f),
      mul_le_mul_of_nonneg_left short (Nat.cast_nonneg (α:=ℚ) g),
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ub yo) (Nat.cast_nonneg (α:=ℚ) g),
      mul_le_mul_of_nonneg_right k8 (Nat.cast_nonneg (α:=ℚ) g),fk,Nat.cast_nonneg (α:=ℚ) g]
  rw [retained hp]
  exact (div_le_div_of_nonneg_left (Nat.cast_nonneg g) (by dsimp [u] at *;positivity)
    (mul_le_mul_of_nonneg_right dx (by positivity))).trans (div_le_div_of_nonneg_right ft (by dsimp [u] at *;positivity))

end OMA.MiddleChange245212

end

section

/- Mixed score changes at an arbitrary rank, in any order of restoration. -/
namespace OMA.FixedModeRestore245212
open Nat Finset OMA.FixedRankGap245212 OMA.MiddleChange245212 OMA.TwoTallLocal245212
variable {r : ℕ} (c : Family r) (b : Fin r→Option Bool) (f g : ℕ)

def tag (s : Finset (Fin r)) (j : Fin r) := if j∈s then none else b j
def xx (s : Finset (Fin r)) (j : Fin r) := xx' (c.p j) (c.e j) (tag b s j)
def yy (s : Finset (Fin r)) (j : Fin r) := yy' (c.p j) (c.e j) (tag b s j)
def val (s : Finset (Fin r)) := score f g (xx c b s) (yy c b s)
def ox (s : Finset (Fin r)) (i : Fin r) := ∏j∈univ.erase i,xx c b s j
def oy (s : Finset (Fin r)) (i : Fin r) := ∏j∈univ.erase i,yy c b s j

theorem caps (s : Finset (Fin r)) (i : Fin r) : 1≤ox c b s i ∧ 0≤oy c b s i ∧ oy c b s i≤1 := by
  have range j:=ranges (c.prime j) (c.positive j) (tag b s j)
  have one j : yy c b s j≤1:=(range j).2.2.2.trans ((div_le_iff₀ (by positivity)).mpr (by
    have ep : (1:ℚ)≤c.e j:=by exact_mod_cast c.positive j
    linarith))
  exact ⟨one_le_prod (fun j _=>(range j).1),prod_nonneg (fun j _=>(range j).2.2.1),
    prod_le_one (fun j _=>(range j).2.2.1) (fun j _=>one j)⟩

theorem other_length (s : Finset (Fin r)) {i z : Fin r} (ne : z≠i) :
    oy c b s i*((c.e z:ℚ)+1)≤2 := by
  have range j:=ranges (c.prime j) (c.positive j) (tag b s j)
  have one j : yy c b s j≤1:=(range j).2.2.2.trans ((div_le_iff₀ (by positivity)).mpr (by
    have ep : (1:ℚ)≤c.e j:=by exact_mod_cast c.positive j
    linarith))
  let t:=(univ:Finset (Fin r)).erase i
  have zm : z∈t:=mem_erase.mpr ⟨ne,mem_univ _⟩
  have rest : ∏j∈t.erase z,yy c b s j≤1:=prod_le_one (fun j _=>(range j).2.2.1) (fun j _=>one j)
  have h : oy c b s i ≤ yy c b s z := by
    change ∏j∈t, yy c b s j≤ _
    rw [←prod_erase_mul t (yy c b s) zm]
    have h0 : 0≤yy c b s z:=(range z).2.2.1
    simpa only [one_mul] using mul_le_mul_of_nonneg_right rest h0
  exact (mul_le_mul_of_nonneg_right h (by positivity)).trans ((le_div_iff₀ (by positivity)).mp (range z).2.2.2)

theorem change (s : Finset (Fin r)) {i} (fresh : i∉s) :
    val c b f g (insert i s)-val c b f g s =
      inc (c.p i) (c.e i) f g (b i) (ox c b s i) (oy c b s i) := by
  have same (j : Fin r) (ji : j≠i) : tag b (insert i s) j=tag b s j:=by simp [tag,ji]
  have eqX : ox c b (insert i s) i=ox c b s i:=by
    apply prod_congr rfl;intro j hj;dsimp only [xx];rw [same j (ne_of_mem_erase hj)]
  have eqY : oy c b (insert i s) i=oy c b s i:=by
    apply prod_congr rfl;intro j hj;dsimp only [yy];rw [same j (ne_of_mem_erase hj)]
  have expand (t) : val c b f g t=(f:ℚ)*(ox c b t i*xx c b t i)+g*(oy c b t i*yy c b t i) := by
    dsimp only [val,score,ox,oy];rw [prod_erase_mul _ _ (mem_univ i),prod_erase_mul _ _ (mem_univ i)]
  rw [expand,expand,eqX,eqY]
  dsimp only [xx,yy,tag,inc];simp only [mem_insert_self,if_true,if_neg fresh]
  simp only [xx',yy']
  ring

theorem same (hit : (f+g)*dust c b=f*NX c b+g*NY c b)
    (actual : score f g (exactX c) (exactY c)=(f+g:ℕ)) :
    val c b f g (∅:Finset (Fin r))=val c b f g univ := by
  have clr:=clear c b f g
  rw [←hit] at clr
  push_cast at clr
  have dp : (0:ℚ)<dust c b:=by exact_mod_cast dust_pos c b
  have z:=mul_right_cancel₀ dp.ne' clr
  have eq : score f g (x' c b) (y' c b)=score f g (exactX c) (exactY c):=z.trans (by simpa only [Nat.cast_add] using actual.symm)
  have a : xx c b ∅=x' c b:=by funext j;simp [xx,tag,x']
  have d : yy c b ∅=y' c b:=by funext j;simp [yy,tag,y']
  have u : xx c b univ=exactX c:=by funext j;simp [xx,tag,xx',exactX]
  have w : yy c b univ=exactY c:=by funext j;simp [yy,tag,yy',exactY]
  simpa only [val,a,d,u,w] using eq

end OMA.FixedModeRestore245212

end

section

/- Absorb all polynomial scales into a single sufficiently long prime power. -/
namespace OMA.LeastTallScale245212
open Nat
open OMA.ThreeMovingOriginal245212 (F G)

def cutoff (C E D : ℕ) :=
  2*(512*(C+1)^2)^D+16*((2*E+1)*D+1)^2+64

theorem scale {C E D k L p e : ℕ} (dyadic : 2^k≤C*(L+1)^E)
    (large : cutoff C E D≤L) (hp : 2≤p) (long : e+1=L) :
    (128*(F k+G k+1)*(L+1))^D<p^e := by
  let w:=2^k
  have wp : 0<w:=Nat.two_pow_pos _
  have kw : k+1≤w:=Nat.lt_pow_self (by decide)
  have id : F k+G k=(k+1)*(2*w) := by
    have sub:=Nat.sub_add_cancel (show 1≤2*w by omega)
    dsimp [F,G];rw [pow_succ,←show w=2^k by rfl]
    nlinarith only [sub,Nat.sub_add_cancel (by omega : 1≤w*2)]
  have v : F k+G k+1≤4*w^2:=by
    rw [id]
    nlinarith only [Nat.mul_le_mul_right (2*w) kw,Nat.one_le_pow 2 w wp]
  let A := (512*(C+1)^2)^D
  let B := (2*E+1)*D
  have pre : 128*(F k+G k+1)*(L+1) ≤ 512*(C+1)^2*(L+1)^(2*E+1) := calc
    _ ≤ 128*(4*w^2)*(L+1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ v)
    _ ≤ 128*(4*((C+1)*(L+1)^E)^2)*(L+1) := by
      apply Nat.mul_le_mul_right
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_left (dyadic.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))) _
    _ = _ := by rw [pow_succ (L+1) (2*E),mul_comm 2 E,pow_mul];ring
  have upper : (128*(F k+G k+1)*(L+1))^D ≤ A*(L+1)^B := by
    simpa only [A,B,mul_pow,pow_mul] using Nat.pow_le_pow_left pre D
  change 2*A+16*(B+1)^2+64≤L at large
  have absorb:=OMA.ComplementarySize245212.absorb (d:=B) (b:=L+1) (by omega)
  have grow : A^2≤2^(2*A) := by
    rw [mul_comm 2 A,pow_mul]
    exact Nat.pow_le_pow_left (Nat.lt_pow_self (by decide : 1<2)).le 2
  have small : 2*A+(L+1)<e*2:=by omega
  have sq : (A*(L+1)^B)^2<(p^e)^2 := calc
    _ = A^2*(L+1)^(2*B) := by rw [mul_pow,mul_comm 2 B,pow_mul (L+1) B 2]
    _ ≤ 2^(2*A)*2^(L+1) := Nat.mul_le_mul grow absorb
    _ = 2^(2*A+(L+1)) := (pow_add ..).symm
    _ < 2^(e*2) := Nat.pow_lt_pow_right (by decide) small
    _ ≤ _ := by rw [pow_mul];exact Nat.pow_le_pow_left (Nat.pow_le_pow_left hp e) 2
  exact upper.trans_lt ((pow_lt_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 2≠0)).mp sq)

end OMA.LeastTallScale245212

end

section

/- A retained short right-hand power cannot offset the loss at the unique
long coordinate, whether the middle base is larger or smaller than sqrt L. -/
namespace OMA.MiddlePower245212
open Nat

theorem left {L q a b : ℕ} (qp : 2≤q) (head : L^6 < q^b) (sep : 2*a≤b) :
    L^3*q^a<q^b := by
  apply (pow_lt_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 2≠0)).mp
  calc
    (L^3*q^a)^2 = L^6*q^(2*a) := by rw [mul_pow,←pow_mul,←pow_mul,mul_comm a 2]
    _ < q^b*q^b := Nat.mul_lt_mul_of_lt_of_le head (Nat.pow_le_pow_right (by omega) sep) (pow_pos (by omega) _)
    _ = (q^b)^2 := (sq _).symm

theorem right {k L q r b d : ℕ} (k0 : 256≤k) (q0 : 2≤q) (rb : r≤L)
    (slope : k*(d+1)<4*q) (sep : 16*(d+1)<b+1) (long : b+1=L) :
    L^3*r^d<q^b := by
  have qp : 1≤q:=by omega
  have high : L^3*r^d≤L^(d+3):=by
    rw [pow_add,mul_comm (L^d)]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left rb d)
  apply high.trans_lt
  by_cases near : L≤q^2
  · calc
      _ ≤ (q^2)^(d+3) := Nat.pow_le_pow_left near _
      _ = q^(2*(d+3)) := (pow_mul ..).symm
      _ < _ := Nat.pow_lt_pow_right (by omega) (by omega)
  · have qle : 4*(d+4)≤q:=by
      have := Nat.mul_le_mul_right (d+1) k0
      omega
    have h0 : 16*((d+3)+1)^2≤L:=by
      have h:=Nat.pow_le_pow_left qle 2
      nlinarith only [h,Nat.lt_of_not_ge near]
    have grow := OMA.ComplementarySize245212.absorb (b:=L) (d:=d+3) h0
    apply (pow_lt_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 2≠0)).mp
    calc
      _ = L^(2*(d+3)):=by rw [mul_comm 2 (d+3),pow_mul]
      _ ≤ 2^L:=grow
      _ ≤ q^L:=Nat.pow_le_pow_left q0 _
      _ < q^(b*2):=Nat.pow_lt_pow_right (by omega) (by omega)
      _ = _ := pow_mul .. 

end OMA.MiddlePower245212

end

section

/- In a mixed exact equality at large dyadic order, only the longest odd
prime can be retained: every other local moment must be exact or dropped. -/
namespace OMA.FixedModeForce245212
open Nat Finset OMA.FixedRankGap245212 OMA.FixedModeRestore245212 OMA.MiddleChange245212
variable {r : ℕ}

theorem force (c : Family r) (b : Fin r→Option Bool) {f g : ℕ} (gp : 0<g)
    (fg : c.k*g≤f) (k0 : 256≤c.k) (v : Fin r) (long : c.e v+1=c.L) (move : b v≠none)
    (small : ∀i,b i=some true → c.p i≤c.L)
    (hit : (f+g)*dust c b=f*NX c b+g*NY c b)
    (actual : score f g (exactX c) (exactY c)=(f+g:ℕ)) :
    b v=some true ∧ (∀i,i≠v → b i≠some true) ∧
    (f:ℚ)*ox c b ∅ v≤(g:ℚ)*((c.p v:ℚ)-1)*oy c b ∅ v := by
  classical
  let V:=val c b f g
  have endEq : V ∅=V univ:=same c b f g hit actual
  have gain (s : Finset (Fin r)) {i} (iv : i≠v) (fr : i∉s) (keep : b i=some true) :
      (g:ℚ)/((c.L:ℚ)^3*(c.p i:ℚ)^c.e i)≤V (insert i s)-V s := by
    have bounds:=caps c b s i
    have ey:=other_length c b s iv.symm
    have len : (c.e v:ℚ)+1=c.L:=by exact_mod_cast long
    rw [len] at ey
    have z:=retained_gain (g:=g) (c.prime i) c.kp fg (small i keep) (c.cap i) bounds.1 bounds.2.1 ey
    change _≤val c b f g (insert i s)-val c b f g s
    rw [change c b f g s fr,keep]
    exact z
  have advance (s : Finset (Fin r)) {i} (iv : i≠v) (fr : i∉s) : V s≤V (insert i s) := by
    cases bi : b i with
    | none=>
      have diff:=change c b f g s fr
      rw [bi,exact_inc] at diff
      exact (sub_eq_zero.mp diff).symm.le
    | some tag=>
      cases tag with
      | true=>exact sub_nonneg.mp ((by positivity : (0:ℚ)≤g/((c.L:ℚ)^3*(c.p i:ℚ)^c.e i)).trans (gain s iv fr bi))
      | false=>
        have bounds:=caps c b s i
        have h:=dropped (f:=f) (g:=g) (c.prime i) (c.positive i) bounds.1 bounds.2.1
        have diff:=change c b f g s fr
        rw [bi] at diff
        change val c b f g s≤val c b f g (insert i s)
        apply sub_nonneg.mp
        rw [diff]
        exact (by positivity : (0:ℚ)≤ f/(2*(c.p i:ℚ))).trans h
  have endBound (s : Finset (Fin r)) (sv : v∈s) : V s≤V univ := by
    have h (t : Finset (Fin r)) : V s≤V (t∪s) := by
      induction t using Finset.induction_on with
      | empty=>simp
      | @insert i t fresh ih=>
        by_cases it : i∈t∪s
        · simpa only [insert_union,insert_eq_of_mem it] using ih
        · have iv : i≠v:=fun h=>it (h ▸ mem_union_right _ sv)
          simpa only [insert_union] using ih.trans (advance (t∪s) iv it)
    have union : (univ:Finset (Fin r))∪s=univ:=Finset.union_eq_left.mpr (subset_univ _)
    simpa only [union] using h univ
  have initial : V {v}≤V ∅:=(endBound _ (mem_singleton_self v)).trans_eq endEq.symm
  have base:=caps c b ∅ v
  have changeV : V {v}-V ∅=inc (c.p v) (c.e v) f g (b v) (ox c b ∅ v) (oy c b ∅ v):=by
    simpa only [insert_empty] using change c b f g ∅ (notMem_empty v)
  have fp : 0<f:=(Nat.mul_pos (show 0<c.k by omega) gp).trans_le fg
  have vv : b v=some true := by
    rcases Option.ne_none_iff_exists'.mp move with ⟨flag,fl⟩
    cases flag with
    | true=>exact fl
    | false=>
      have z:=dropped (f:=f) (g:=g) (c.prime v) (c.positive v) base.1 base.2.1
      rw [fl] at changeV
      have nz : 0<(f:ℚ)/(2*c.p v):=by have:=(c.prime v).pos;positivity
      linarith only [changeV,initial,z,nz]
  rw [vv] at changeV
  have p2 : (1:ℚ)<c.p v:=by exact_mod_cast (c.prime v).one_lt
  have den : 0<((c.e v:ℚ)+1)*((c.p v:ℚ)-1)^2*(c.p v:ℚ)^c.e v:=by positivity
  have formula:=retained (f:=f) (g:=g) (e:=c.e v) (c.prime v) (ox c b ∅ v) (oy c b ∅ v)
  have gap : (f:ℚ)*ox c b ∅ v≤g*((c.p v:ℚ)-1)*oy c b ∅ v:=by
    have low:=sub_nonpos.mpr initial
    rw [changeV,formula] at low
    exact sub_nonpos.mp (by simpa only [zero_mul] using (div_le_iff₀ den).mp low)
  refine ⟨vv,?_,gap⟩
  intro i iv keep
  have fr : i∉({v}:Finset (Fin r)):=by simpa
  have perk:=gain {v} iv fr keep
  have up:=(endBound (insert i {v}) (mem_insert_of_mem (mem_singleton_self v))).trans_eq endEq.symm
  have gl : 0<(g:ℚ)/((c.L:ℚ)^3*(c.p i:ℚ)^c.e i):=by
    have lp : 0<c.L:=by omega
    have pi:=(c.prime i).pos
    positivity
  have loss : V {v}-V ∅<0:=by linarith only [perk,up,gl]
  have neg : (f:ℚ)*ox c b ∅ v<g*((c.p v:ℚ)-1)*oy c b ∅ v:=by
    rw [changeV,formula] at loss
    exact sub_neg.mp (by simpa only [zero_mul] using (div_lt_iff₀ den).mp loss)
  have fk : (c.k:ℚ)*g≤f:=by exact_mod_cast fg
  have risk : (c.k:ℚ)<((c.p v:ℚ)-1)*oy c b ∅ v := by
    apply lt_of_mul_lt_mul_right (a:=(g:ℚ)) _ (by positivity)
    nlinarith only [neg,mul_le_mul_of_nonneg_left base.1 (Nat.cast_nonneg (α:=ℚ) f),fk]
  have ey:=other_length c b ∅ iv
  have ep : 0<(c.e i:ℚ)+1:=by positivity
  have slope : c.k*(c.e i+1)<4*c.p v:=by
    exact_mod_cast (show (c.k:ℚ)*((c.e i:ℚ)+1)<4*(c.p v:ℚ) by
      nlinarith only [mul_lt_mul_of_pos_right risk ep,
        mul_le_mul_of_nonneg_left ey (show 0≤(c.p v:ℚ)-1 by linarith),p2])
  have vl:=small v vv
  have sep : 16*(c.e i+1)<c.e v+1:=by
    have ks:=Nat.mul_le_mul_right (c.e i+1) k0
    omega
  have powers:=OMA.MiddlePower245212.right k0 (c.prime v).two_le (small i keep) slope sep long
  have powerq : (c.L:ℚ)^3*(c.p i:ℚ)^c.e i < (c.p v:ℚ)^c.e v:=by exact_mod_cast powers
  have cost:=retained_loss (f:=f) (g:=g) (e:=c.e v) (c.prime v) (zero_le_one.trans base.1) base.2.2
  have comp : (g:ℚ)/(c.p v:ℚ)^c.e v < g/((c.L:ℚ)^3*(c.p i:ℚ)^c.e i):=by
    apply div_lt_div_of_pos_left (by positivity) _ powerq
    have lp : 0<c.L:=by omega
    have pi:=(c.prime i).pos
    positivity
  rw [←changeV] at cost
  let P:ℚ:=g/(c.p v:ℚ)^c.e v
  let Q:ℚ:=g/((c.L:ℚ)^3*(c.p i:ℚ)^c.e i)
  have d : -P≤V {v}-V ∅:=by simpa only [P,neg_div] using cost
  change P<Q at comp
  change Q≤V (insert i {v})-V {v} at perk
  linarith only [d,comp,perk,up]

end OMA.FixedModeForce245212

end

section

/- The actual dyadic deficit exceeds the total possible loss caused by
all risky rounded coordinates, without any comparability assumption. -/
namespace OMA.FixedRankProxy245212
open Nat Finset OMA.FixedRankGap245212 OMA.TwoTallLocal245212
open OMA.ThreeMovingOriginal245212 (G)
variable {r : ℕ}

def deficit (c : Family r) : ℚ := (c.k:ℚ)+1-score c.k 1 (exactX c) (exactY c)

theorem lower (c : Family r) (link : deficit c*(G c.k:ℕ)=((c.k:ℚ)+1)*((∏i,exactX c i)-1)) (i) :
    1≤(2*(c.p i:ℚ))*(G c.k)*(deficit c) := by
  have xb j : 1≤exactX c j:=(ranges (c.prime j) (c.positive j) none).1
  have xi : exactX c i≤∏j,exactX c j := by
    rw [←prod_erase_mul (univ : Finset (Fin r)) (exactX c) (mem_univ i)]
    exact le_mul_of_one_le_left (zero_le_one.trans (xb _)) (one_le_prod (fun j _=>xb j))
  have localBound:=OMA.SingleMovingLoss245212.single_lb (c.prime i) (c.positive i)
  change 1≤(2*(c.p i:ℚ))*(exactX c i-1) at localBound
  have xm : 0≤(∏j,exactX c j)-1:=by linarith only [xi,xb i]
  have more:=mul_nonneg (Nat.cast_nonneg (α:=ℚ) c.k) xm
  have cc : 0≤2*(c.p i:ℚ):=by positivity
  nlinarith only [localBound,mul_le_mul_of_nonneg_left xi cc,mul_nonneg cc more,
    congrArg (fun z:ℚ=>2*(c.p i:ℚ)*z) link]


set_option maxHeartbeats 1200000 in
/-- All coordinates apart from one longest coordinate have nonnegative
restoration, regardless of how many other coordinates there are. -/
theorem separated (c : Family r) (b : Fin r→Option Bool)
    (link : deficit c*(G c.k:ℕ)=((c.k:ℚ)+1)*((∏i,exactX c i)-1)) :
    (c.k+1)*dust c b ≠ c.k*NX c b+NY c b := by
  classical
  obtain ⟨v,vbig⟩:=c.longest
  have gd : 0<deficit c := by
    have h:=lower c link v
    by_contra! n
    have t:=mul_nonpos_of_nonneg_of_nonpos (show 0≤2*(c.p v:ℚ)*(G c.k:ℕ) by positivity) n
    linarith
  intro hit
  have scale:=retained (b:=b) (f:=c.k) (g:=1) (l:=1) (by simp)
    (fun i=>Nat.not_dvd_of_pos_of_lt (by decide) (c.prime i).one_lt) (by simpa using hit)
  let mix (s : Finset (Fin r)) (i : Fin r) := if i∈s then exactX c i else x' c b i
  let miy (s : Finset (Fin r)) (i : Fin r) := if i∈s then exactY c i else y' c b i
  let val (s : Finset (Fin r)):=score c.k 1 (mix s) (miy s)
  have adv (s : Finset (Fin r)) {i} (fresh : i∉s) :
      val s ≤ val (insert i s)+(if i=v then deficit c/4 else 0) := by
    have bound j : 1≤ mix s j ∧ 0≤ miy s j ∧ miy s j≤2/((c.e j:ℚ)+1) := by
      by_cases mem : j∈s
      · have w:=ranges (c.prime j) (c.positive j) none
        simpa only [mix,miy,if_pos mem,exactX,exactY,xx',yy'] using And.intro w.1 w.2.2
      · have w:=ranges (c.prime j) (c.positive j) (b j)
        simpa only [mix,miy,if_neg mem,x',y'] using And.intro w.1 w.2.2
    have size j : miy s j≤1 := (bound j).2.2.trans ((div_le_iff₀ (by positivity)).mpr (by
      have:= (by exact_mod_cast c.positive j : (1:ℚ)≤c.e j);linarith))
    let t:=(univ:Finset (Fin r)).erase i
    let xx:=∏j∈t,mix s j
    let yy:=∏j∈t,miy s j
    have x1 : 1≤xx:=one_le_prod (fun j _=>(bound j).1)
    have y0 : 0≤yy:=prod_nonneg (fun j _=>(bound j).2.1)
    have y1 : yy≤1:=prod_le_one (fun j _=>(bound j).2.1) (fun j _=>size j)
    have sameX : ∏j∈t,mix (insert i s) j=xx := Finset.prod_congr rfl (by
      intro j hj
      have ji:=ne_of_mem_erase hj
      simp [mix,Finset.mem_insert,ji])
    have sameY : ∏j∈t,miy (insert i s) j=yy := Finset.prod_congr rfl (by
      intro j hj
      have ji:=ne_of_mem_erase hj
      simp [miy,Finset.mem_insert,ji])
    have step:=OMA.SingleMovingLoss245212.restore (c.prime i) (c.positive i)
      (by have:=c.kp;omega : 0<c.k) (b i) xx 1 yy 1
      (if i=v then deficit c/4 else 0) x1 le_rfl y0 zero_le_one
      (by simpa only [mul_one] using y1) (by split <;> positivity)
    have bad (bit : b i=some true) (risk : (c.k:ℚ)<((c.p i:ℚ)-1)*(yy*1)) :
        1/(c.p i:ℚ)^(c.e i) ≤ if i=v then deficit c/4 else 0 := by
      simp only [mul_one] at risk
      have u0 : 0≤(c.p i:ℚ)-1:=by have z:=(by exact_mod_cast (c.prime i).one_le : (1:ℚ)≤c.p i);linarith
      have pk : c.k+1<c.p i := by
        have up:=mul_le_mul_of_nonneg_left y1 u0
        exact_mod_cast (show (c.k:ℚ)+1<c.p i by linarith only [up,risk])
      have pL : c.p i≤c.L:=by have:=scale i bit;omega
      have unique : i=v := by
        by_contra iv
        have vm : v∈t:=mem_erase.mpr ⟨Ne.symm iv,mem_univ _⟩
        have rest : ∏j∈t.erase v,miy s j≤1:=prod_le_one (fun j _=>(bound j).2.1) (fun j _=>size j)
        have yv : yy ≤ miy s v := by
          dsimp [yy];rw [←prod_erase_mul t (miy s) vm]
          simpa only [one_mul] using mul_le_mul_of_nonneg_right rest (bound v).2.1
        have base : c.p i≤c.e v+1:=by omega
        have base' : (c.p i:ℚ)-1≤(c.e v:ℚ)+1:=by
          have u:(c.p i:ℚ)≤c.e v+1:=by exact_mod_cast base
          linarith
        have M:=(le_div_iff₀ (by positivity)).mp (bound v).2.2
        have g:=mul_le_mul_of_nonneg_left yv u0
        have h:=mul_le_mul_of_nonneg_right base' (bound v).2.1
        have k8 : (8:ℚ)≤c.k:=by exact_mod_cast c.kp
        nlinarith only [risk,g,h,M,k8]
      rw [if_pos unique]
      have len : c.p i≤c.e i+1:=by simpa [unique,vbig] using pL
      have pw:=OMA.SingleMovingLoss245212.scalar c.kp pk len
      have more:=lower c link i
      have pwq : 8*(c.p i:ℚ)*(G c.k)≤(c.p i:ℚ)^(c.e i):=by exact_mod_cast pw
      apply (div_le_iff₀ (by have:=(c.prime i).pos;positivity : (0:ℚ)<(c.p i:ℚ)^(c.e i))).mpr
      nlinarith only [more,mul_le_mul_of_nonneg_right pwq gd.le]
    have h:=step bad
    dsimp only [val,score];simp only [Nat.cast_one,one_mul]
    rw [←prod_erase_mul univ (mix s) (mem_univ i),←prod_erase_mul univ (miy s) (mem_univ i),
        ←prod_erase_mul univ (mix (insert i s)) (mem_univ i),←prod_erase_mul univ (miy (insert i s)) (mem_univ i)]
    change (c.k:ℚ)*(xx*mix s i)+yy*miy s i≤ _*(_*mix (insert i s) i)+_*miy (insert i s) i+_
    change (c.k:ℚ)*(xx*mix s i)+yy*miy s i≤
      c.k*((∏j∈t,mix (insert i s) j)*mix (insert i s) i)+
      (∏j∈t,miy (insert i s) j)*miy (insert i s) i+_
    rw [sameX,sameY]
    simpa only [mix,miy,if_neg fresh,mem_insert_self,if_true,exactX,exactY,x',y',mul_one,one_mul,
      mul_comm,mul_left_comm,mul_assoc] using h
  have sum (s : Finset (Fin r)) : val ∅ ≤ val s+(if v∈s then deficit c/4 else 0) := by
    induction s using Finset.induction_on with
    | empty=>simp
    | @insert i s fresh ih=>
      have h:=adv s fresh
      by_cases iv : i=v
      · subst i
        simpa [fresh] using ih.trans (by simpa [fresh] using h : val s+(if v∈s then deficit c/4 else 0) ≤ val (insert v s)+deficit c/4)
      · have adv0 : val s≤val (insert i s):=by simpa only [if_neg iv,add_zero] using h
        simpa only [Finset.mem_insert,Ne.symm iv,false_or] using ih.trans
          (add_le_add_left adv0 (if v∈s then deficit c/4 else 0))
  have a:=sum univ
  simp only [val,mix,miy,notMem_empty,if_false,mem_univ,if_true] at a
  have eq:=clear c b c.k 1
  simp only [one_mul] at eq
  rw [←hit] at eq
  push_cast at eq
  have dp : (0:ℚ)<dust c b:=by exact_mod_cast dust_pos c b
  have eq' : score c.k 1 (x' c b) (y' c b)=(c.k:ℚ)+1:=mul_right_cancel₀ dp.ne' eq
  dsimp only [deficit] at a gd
  linarith only [a,eq',gd]

end OMA.FixedRankProxy245212

end

section

/- The dyadic factor of every solution with three distinct odd primes
is polynomially bounded in the largest odd exponent length. -/
namespace OMA.FixedRankHeight245212
open Nat Finset ArithmeticFunction OMA.FixedRankGap245212 OMA.FixedRankStep245212
open OMA.ThreeMovingOriginal245212 (F G)
open OMA.TwoTallScalar245212 (base)
open OMA.Smooth245212 (total W)
open scoped ArithmeticFunction.sigma
open OMA.ComplementaryLocal245212 (binary)
variable {r : ℕ}

theorem identities (k : ℕ) : 0<G k ∧ F k+G k=(k+1)*2^(k+1) ∧ F k=k*G k+(k+1) := by
  have g:=Nat.two_pow_pos k
  dsimp [F,G];rw [pow_succ]
  have sub:=Nat.sub_add_cancel (show 1≤2^k*2 by omega)
  exact ⟨by omega,by nlinarith only [sub],by nlinarith only [congrArg (k*·) sub]⟩


theorem physical (c : Family r) (k : ℕ) (op : ∀i,Odd (c.p i)) (inj : c.p.Injective)
    (eqn : OeisA245212.a (2^k*total c.p c.e)=(σ 1 (2^k*total c.p c.e):ℤ)) :
    score (F k) (G k) (exactX c) (exactY c)=(F k+G k:ℕ) := by
  let t:=2^k*σ 0 (2^k)
  have t0 : 0<t := Nat.mul_pos (Nat.two_pow_pos k) (sigma_pos 0 _ (Nat.two_pow_pos k).ne')
  have norm:=OMA.CofactorCrossOriginal245212.normalized_extension (p:=c.p) (e:=c.e) (Nat.two_pow_pos k)
    c.prime inj (fun i=>(Nat.coprime_two_left.mpr (op i)).pow_left k) eqn
  change ((W (2^k):ℚ)/t)*(∏i,exactX c i)+((σ 1 (2^k):ℚ)/t)*(∏i,exactY c i)=2 at norm
  field_simp [show (t:ℚ)≠0 by exact_mod_cast t0.ne'] at norm
  have z0:=Nat.two_pow_pos (k+1)
  have gold : σ 1 (2^k)=G k := by
    dsimp [G];zify [Nat.cast_sub (show 1≤2^(k+1) from z0)]
    exact (OMA.ComplementaryLocal245212.binary k).1
  have fold : W (2^k)=F k := by exact_mod_cast (OMA.ComplementaryLocal245212.binary k).2
  have ht : 2*t=F k+G k := by
    dsimp [t];rw [sigma_zero_apply_prime_pow Nat.prime_two,(identities k).2.1,pow_succ];ring
  rw [gold,fold] at norm
  dsimp [score];rw [←ht];push_cast;linarith only [norm]


theorem coarse (c : Family r) (op : ∀i,Odd (c.p i))
    (eqn : OeisA245212.a (2^c.k*total c.p c.e)=(σ 1 (2^c.k*total c.p c.e):ℤ)) :
    G c.k < 2^r*(c.k+1)*((base c.k c.L)^(r+2))^(degree r) := by
  have exact:=physical c c.k op c.inj eqn
  let x:=(base c.k c.L)^(r+2)
  have toX : base c.k c.L≤x:=Nat.le_self_pow (by omega) _
  have big : 128≤x := by apply le_trans _ toX; dsimp [base];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
  have cf : c.k+1≤x := by apply le_trans _ toX; dsimp [base];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
  have cl : c.L≤x := by apply le_trans _ toX; dsimp [base];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
  have dx : 1≤x:=by omega
  have r0 := (identities c.k).1
  let PX:=∏i,exactX c i
  let PY:=∏i,exactY c i
  have xb i := OMA.TwoTallLocal245212.ranges (c.prime i) (c.positive i) none
  have low : (1:ℚ)≤PX:=one_le_prod (fun i _=>(xb i).1)
  have top : PX≤(2:ℚ)^r := calc
    _ ≤ ∏_i:Fin r,(2:ℚ) := prod_le_prod (fun i _=>zero_le_one.trans (xb i).1) (fun i _=>(xb i).2.1)
    _ = _ := by norm_num
  have id : (G c.k:ℚ)*((c.k:ℚ)+1-score c.k 1 (exactX c) (exactY c))=((c.k:ℚ)+1)*(PX-1) := by
    change (F c.k:ℚ)*PX+(G c.k:ℚ)*PY=(F c.k+G c.k:ℕ) at exact
    change _*((c.k:ℚ)+1-((c.k:ℚ)*PX+(1:ℕ)*PY))=_
    have f : (F c.k:ℚ)=(c.k:ℚ)*G c.k+(c.k+1:ℕ) := by exact_mod_cast (identities c.k).2.2
    push_cast at f exact ⊢
    linear_combination -exact+(PX-1)*f
  have gp : (0:ℚ)<G c.k := by exact_mod_cast r0
  by_contra! ample
  have below : score c.k 1 (exactX c) (exactY c)≤(c.k+1:ℕ):=by
    push_cast
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right (id ▸ mul_nonneg (by positivity) (sub_nonneg.mpr low)) gp)
  have close : |score c.k 1 (exactX c) (exactY c)-(c.k+1:ℕ)|≤1/((x^(degree r):ℕ):ℚ) := by
    rw [abs_of_nonpos (sub_nonpos.mpr below),neg_sub]
    have h : (((c.k+1:ℕ):ℚ)-score c.k 1 (exactX c) (exactY c))*(x^(degree r):ℕ)≤1 := by
      apply le_of_mul_le_mul_left (a:=(G c.k:ℚ)) _ gp
      have g0 : (2:ℚ)^r*(c.k+1)*(x^(degree r):ℕ)≤G c.k:=by exact_mod_cast ample
      push_cast at g0 ⊢
      nlinarith only [congrArg (·*(x:ℚ)^(degree r)) id,g0,
        mul_le_mul_of_nonneg_right (show PX-1≤(2:ℚ)^r by linarith) (show 0≤((c.k:ℚ)+1)*x^(degree r) by positivity)]
    exact (le_div_iff₀ (by exact_mod_cast pow_pos dx (degree r) : (0:ℚ)<(x^(degree r):ℕ))).mpr h

  apply OMA.FixedRankStep245212.contradiction c c.k 1 x big cf cl ?_ ?_ close
  · have B : 4≤base c.k c.L := by dsimp [base];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
    calc
      2*r*2^r ≤ 2*(2^r)*2^r := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ((Nat.lt_two_pow_self).le))
      _ = 2*4^r := by rw [show (4:ℕ)=2*2 by decide,mul_pow];ring
      _ ≤ 4^r*4^2 := by nlinarith only [Nat.zero_le (4^r)]
      _ = 4^(r+2) := (pow_add ..).symm
      _ ≤ x := Nat.pow_le_pow_left B _
  intro b
  have link : OMA.FixedRankProxy245212.deficit c*(G c.k:ℕ)=((c.k:ℚ)+1)*((∏i,exactX c i)-1) := by
    simpa only [OMA.FixedRankProxy245212.deficit,mul_comm] using id
  simpa only [one_mul] using OMA.FixedRankProxy245212.separated c b link


/-- The explicit polynomial degree depends only on the number of odd primes. -/
def exponent (r : ℕ) := (r+2)*degree r+r

open OMA.SingleMovingHeight245212 (all_k)

/-- The full A245212 equality bounds its dyadic prime power polynomially in
the largest odd exponent length at every fixed positive support size. -/
theorem original {r : ℕ} (k L : ℕ) (p e : Fin r→ℕ) (prime : ∀i,(p i).Prime)
    (odd : ∀i,Odd (p i)) (distinct : p.Injective) (positive : ∀i,0<e i)
    (longest : ∃i,e i+1=L) (cap : ∀i,e i+1≤L)
    (eqn : OeisA245212.a (2^k*total p e)=(σ 1 (2^k*total p e):ℤ)) :
    2^k≤OMA.SingleMovingHeight245212.constant (exponent r)*(L+1)^(2*exponent r) := by
  apply OMA.SingleMovingHeight245212.all_k
  intro hk
  let c : Family r := ⟨p,e,k,L,prime,positive,hk,longest,cap,distinct⟩
  have z:=coarse c odd eqn
  change G k < 2^r*(k+1)*((base k L)^(r+2))^(degree r) at z
  apply z.trans_le
  let b:=base k L
  have hb : 2≤b := by dsimp [base,b];nlinarith only [Nat.zero_le (k*L),Nat.zero_le k,Nat.zero_le L]
  have h:=Nat.pow_le_pow_left hb r
  calc
    _ ≤ b^r*(k+1)*(b^(r+2))^(degree r) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h)
    _ = (k+1)*b^(exponent r) := by rw [exponent,pow_add b ((r+2)*degree r) r,pow_mul];ring
    _ ≤ 8*(k+1)*b^(exponent r) := Nat.mul_le_mul_right _ (by omega)

end OMA.FixedRankHeight245212

end

section

/- Explicit thresholds for the exact dyadic coefficient and a long prime
power; all parameters outside the exponents are the rank and a ratio bound. -/
namespace OMA.FixedTallScalar245212
open Nat OMA.FixedRankHeight245212 OMA.FixedRankStep245212
open OMA.ThreeMovingOriginal245212 (F G)

def h (r : ℕ) := 12*exponent r+4
def threshold (r C : ℕ) := 128 + 2*r*2^r + OMA.SingleMovingHeight245212.constant (exponent r) +
  (C+1) + 16*(h r*degree r+2)^2

theorem scale {r C m k L : ℕ} (large : threshold r C ≤ m) (width : L≤C*m)
    (dyad : 2^k≤OMA.SingleMovingHeight245212.constant (exponent r)*(L+1)^(2*exponent r)) :
    let x:=m^h r
    128≤x ∧ F k+G k≤x ∧ L≤x ∧ 2*r*2^r≤x ∧
      ∀ p e : ℕ, 2≤p → m≤e+1 → x^(degree r)<p^e := by
  dsimp only
  have raw:=large
  dsimp only [threshold] at raw
  have three : 3 ≤ m:=by omega
  have m0 : 0 < m:=by omega
  have mh : m ≤ m^h r:=Nat.le_self_pow (by dsimp [h];omega) _
  have mc : C < m:=by omega
  have Len : L+1 ≤ m^3 := by
    have prod:=Nat.mul_lt_mul_of_pos_right mc m0
    exact (show L+1 ≤ m^2 by nlinarith only [width,prod]).trans
      (Nat.pow_le_pow_right m0 (by decide))
  have c0 : OMA.SingleMovingHeight245212.constant (exponent r) ≤ m:=by omega
  have kd : 2^k ≤ m^(6*exponent r+1) := by
    calc
      _ ≤ _ := dyad
      _ ≤ m*(m^3)^(2*exponent r) := Nat.mul_le_mul c0 (Nat.pow_le_pow_left Len _)
      _ = _ := by rw [←pow_mul,pow_succ,show 3*(2*exponent r)=6*exponent r by ring];ring
  have km : k+1≤2^k:=Nat.lt_two_pow_self
  have fg : F k+G k=(k+1)*2^(k+1) := by
    dsimp [F,G];have:=Nat.two_pow_pos (k+1)
    nlinarith only [Nat.sub_add_cancel (show 1≤2^(k+1) by omega)]
  refine ⟨(by omega : 128 ≤ m).trans mh,?_,(Nat.le_succ L).trans (Len.trans
    (Nat.pow_le_pow_right m0 (by dsimp [h];omega))),(by omega : 2*r*2^r ≤ m).trans mh,?_⟩
  · rw [fg,pow_succ]
    calc
      _ ≤ m^(6*exponent r+1)*(m^(6*exponent r+1)*m) :=
        Nat.mul_le_mul (km.trans kd) (Nat.mul_le_mul kd (by omega))
      _ = m^((6*exponent r+1)+(6*exponent r+1)+1) := by rw [pow_succ,pow_add];ring
      _ ≤ m^h r := Nat.pow_le_pow_right m0 (by dsimp [h];omega)
  · intro p e pp ell
    let J:=h r*degree r
    have cutoff : 16*((J+1)+1)^2 ≤ m:=by change 16*(h r*degree r+2)^2 ≤ m;omega
    have pwr:=OMA.ComplementarySize245212.absorb cutoff
    have bigger : 2*m^J < m^(2*(J+1)) := by
      have more:=Nat.pow_le_pow_right m0 (show J+1≤2*(J+1) by omega)
      exact (show 2*m^J < m^(J+1) by rw [_root_.pow_succ'];exact Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos m0 _)).trans_le more
    have z:=bigger.trans_le (pwr.trans (Nat.pow_le_pow_right (by decide) ell))
    rw [_root_.pow_succ'] at z
    have le:=Nat.lt_of_mul_lt_mul_left z
    exact (by simpa only [←pow_mul,J] using le : (m^h r)^degree r<2^e).trans_le (Nat.pow_le_pow_left pp e)

end OMA.FixedTallScalar245212

end

section

/- Every solution with large dyadic exponent and large maximum length has
an exact mixed equality with precisely one retained base, at the longest slot. -/
namespace OMA.FixedModeOriginal245212
open Nat Finset OMA.FixedRankGap245212 OMA.FixedModeRestore245212
open OMA.FixedTallScalar245212 (threshold h)
open OMA.FixedRankStep245212 (degree)
open OMA.ThreeMovingOriginal245212 (F G)
open scoped ArithmeticFunction.sigma
open OMA.Smooth245212 (total)
open OMA.FixedRankHeight245212 (identities)

def exponent (r : ℕ):=h r*degree r

theorem original {r : ℕ} (c : Family r) (odd : ∀i,Odd (c.p i))
    (klarge : 256≤c.k) (large : threshold r 1≤c.L)
    (v : Fin r) (long : c.e v+1=c.L)
    (eqn : OeisA245212.a (2^c.k*total c.p c.e)=(σ 1 (2^c.k*total c.p c.e):ℤ)) :
    ∃ (b : Fin r→Option Bool) (Q : ℕ), c.L≤Q ∧ Q≤c.L^exponent r ∧
    (∀i,b i=if c.p i^c.e i≤Q then none else some (decide (c.p i≤Q))) ∧
    (F c.k+G c.k)*dust c b=F c.k*NX c b+G c.k*NY c b ∧
    b v=some true ∧ (∀i,i≠v → b i≠some true) ∧
    (F c.k:ℚ)*ox c b ∅ v≤(G c.k:ℚ)*((c.p v:ℚ)-1)*oy c b ∅ v := by
  have dyad:=OMA.FixedRankHeight245212.original c.k c.L c.p c.e c.prime odd c.inj c.positive c.longest c.cap eqn
  have actual:=OMA.FixedRankHeight245212.physical c c.k odd c.inj eqn
  obtain ⟨big,coef,lc,rate,pow⟩:=OMA.FixedTallScalar245212.scale large (by simp only [one_mul,le_refl] : c.L≤1*c.L) dyad
  let x:=c.L^h r
  have post : x^(degree r)<c.p v^c.e v:=pow _ _ (c.prime v).two_le long.ge
  obtain ⟨b,Q,xQ,Qcap,rule,hit⟩:=OMA.FixedModeWitness245212.witness c (F c.k) (G c.k) x big coef lc rate actual
  have id:=OMA.FixedRankHeight245212.identities c.k
  have Fcap : c.k*G c.k≤F c.k:=by omega
  have unit (i) : ¬c.p i∣2^(c.k+1):=by
    intro dv
    have two:=(c.prime i).dvd_of_dvd_pow dv
    have g:=(c.prime i).odd_iff.mp (odd i)
    exact Nat.not_dvd_of_pos_of_lt (by decide) g two
  have kL : c.k+1≤c.L := by
    have dpos : 0<degree r:=pow_pos (by omega) _
    have xp : x≤x^(degree r):=Nat.le_self_pow dpos.ne' _
    have two : x^(degree r)<2^(c.e v):=pow 2 _ (by decide) long.ge
    have mul : 2^(c.k+1)≤F c.k+G c.k:=by rw [id.2.1];exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    have less:=((mul.trans coef).trans xp).trans_lt two
    have exp : c.k+1<c.e v := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp less
    omega
  have base i (keep : b i=some true) : c.p i≤c.L:=by simpa [max_eq_right kL] using retained id.2.1 unit hit i keep
  have mv : b v≠none:=by rw [rule];simp [(Qcap.trans_lt post).not_ge]
  obtain ⟨keep,unique,negative⟩:=OMA.FixedModeForce245212.force c b id.1 Fcap klarge v long mv base hit actual
  exact ⟨b,Q,lc.trans xQ,by simpa only [x,exponent,pow_mul] using Qcap,rule,hit,keep,unique,negative⟩

end OMA.FixedModeOriginal245212

end

section

/- Natural-number coefficient factors for the uniquely retained prime:
the selected exact prefix, dropped divisor-count product, and the score. -/
namespace OMA.FixedModeProduct245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.FixedRankGap245212
open OMA.TwoTallLocal245212 OMA.ThreeMovingLocal245212
open OMA.ThreeMovingOriginal245212 (F G)
open scoped ArithmeticFunction.sigma Function
open OMA.ComplementaryLocal245212 (binary)
open OMA.FixedRankHeight245212 (identities)
variable {r : ℕ}

def exactSet (b : Fin r→Option Bool) := univ.filter (fun i=>b i=none)
def dropped (b : Fin r→Option Bool) := univ.filter (fun i=>b i=some false)
def pref (c : Family r) (b : Fin r→Option Bool) := 2^c.k*∏i∈exactSet b,c.p i^c.e i
def mult (c : Family r) (b : Fin r→Option Bool) := ∏i∈dropped b,(c.e i+1)

theorem partition {b : Fin r→Option Bool} {v : Fin r} (keep : b v=some true) (only : ∀i,i≠v → b i≠some true) :
    Disjoint (exactSet b) (dropped b) ∧ exactSet b∪dropped b=univ.erase v := by
  constructor
  · refine disjoint_left.mpr ?_;intro i h1 h2
    have a:=(mem_filter.mp h1).2;have z:=(mem_filter.mp h2).2
    simp_all
  · ext i
    by_cases iv : i=v
    · subst i;simp [exactSet,dropped,keep]
    · have n:=only i iv
      cases h : b i with
      | none=>simp [exactSet,dropped,h,iv]
      | some t=>cases t <;> simp_all [exactSet,dropped]

theorem prefix_moments (c : Family r) (odd : ∀i,Odd (c.p i)) (b : Fin r→Option Bool) :
    W (pref c b)=F c.k*(∏i∈exactSet b,W (c.p i^c.e i)) ∧
    σ 1 (pref c b)=G c.k*(∏i∈exactSet b,σ 1 (c.p i^c.e i)) ∧
    2*(pref c b)*(σ 0 (pref c b))=(F c.k+G c.k)*(∏i∈exactSet b,((c.e i+1)*c.p i^c.e i)) := by
  let s:=exactSet b
  let a i:=c.p i^c.e i
  have cop : (2^c.k).Coprime (∏i∈s,a i):=Nat.coprime_prod_right_iff.mpr (fun i _=>
    ((Nat.coprime_two_left.mpr (odd i)).pow_left _).pow_right _)
  have pw : (s:Set (Fin r)).Pairwise (Nat.Coprime on a):=fun i _ j _ ij=>
    (((Nat.coprime_primes (c.prime i) (c.prime j)).mpr (c.inj.ne ij)).pow_left _).pow_right _
  have Wp:=IsMultiplicative.map_prod a w_mult s pw
  have Sp:=IsMultiplicative.map_prod a (isMultiplicative_sigma (k:=1)) s pw
  have Tp:=IsMultiplicative.map_prod a (isMultiplicative_sigma (k:=0)) s pw
  have gf : σ 1 (2^c.k)=G c.k := by
    dsimp [G];zify [Nat.cast_sub (show 1≤2^(c.k+1) from Nat.two_pow_pos _)]
    exact (OMA.ComplementaryLocal245212.binary c.k).1
  have ff : W (2^c.k)=F c.k := by exact_mod_cast (OMA.ComplementaryLocal245212.binary c.k).2
  change W (2^c.k*∏i∈s,a i)=_ ∧ σ 1 (2^c.k*∏i∈s,a i)=_ ∧ 2*(2^c.k*∏i∈s,a i)*σ 0 (2^c.k*∏i∈s,a i)=_
  rw [w_mult.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
    isMultiplicative_sigma.map_mul_of_coprime cop,ff,gf,Wp,Sp,Tp]
  refine ⟨rfl,rfl,?_⟩
  simp only [a,sigma_zero_apply_prime_pow (c.prime _),sigma_zero_apply_prime_pow Nat.prime_two,
    (OMA.FixedRankHeight245212.identities c.k).2.1,pow_succ 2,prod_mul_distrib,s]
  ring

theorem others (c : Family r) {b : Fin r→Option Bool} {v : Fin r} (keep : b v=some true)
    (only : ∀i,i≠v → b i≠some true) :
    (∏i∈univ.erase v,Dn (c.p i) (c.e i) (b i))=(∏i∈exactSet b,((c.e i+1)*c.p i^c.e i))*mult c b ∧
    (∏i∈univ.erase v,Nx (c.p i) (c.e i) (b i))=(∏i∈exactSet b,W (c.p i^c.e i))*mult c b ∧
    (∏i∈univ.erase v,Ny (c.p i) (c.e i) (b i))=∏i∈exactSet b,σ 1 (c.p i^c.e i) := by
  have ⟨dis,part⟩:=partition keep only
  have ed i (hi : i∈exactSet b) := (mem_filter.mp hi).2
  have dd i (hi : i∈dropped b) := (mem_filter.mp hi).2
  rw [←part]
  simp only [prod_union dis]
  have denE : (∏i∈exactSet b,Dn (c.p i) (c.e i) (b i))=_ :=
    prod_congr rfl (fun i hi=>show Dn (c.p i) (c.e i) (b i)=(c.e i+1)*c.p i^c.e i by rw [ed i hi];rfl)
  have denD : (∏i∈dropped b,Dn (c.p i) (c.e i) (b i))=mult c b:=
    prod_congr rfl (fun i hi=>by rw [dd i hi];rfl)
  have wxE : (∏i∈exactSet b,Nx (c.p i) (c.e i) (b i))=_ :=
    prod_congr rfl (fun i hi=>show Nx (c.p i) (c.e i) (b i)=W (c.p i^c.e i) by rw [ed i hi];rfl)
  have wxD : (∏i∈dropped b,Nx (c.p i) (c.e i) (b i))=mult c b:=
    prod_congr rfl (fun i hi=>by rw [dd i hi];rfl)
  have syE : (∏i∈exactSet b,Ny (c.p i) (c.e i) (b i))=_ :=
    prod_congr rfl (fun i hi=>show Ny (c.p i) (c.e i) (b i)=σ 1 (c.p i^c.e i) by rw [ed i hi];rfl)
  have syD : (∏i∈dropped b,Ny (c.p i) (c.e i) (b i))=1:=
    Finset.prod_eq_one (fun i hi=>by rw [dd i hi];rfl)
  rw [denE,denD,wxE,wxD,syE,syD,mul_one]
  exact ⟨rfl,rfl,rfl⟩

theorem equation (c : Family r) (odd : ∀i,Odd (c.p i)) {b : Fin r→Option Bool} {v : Fin r}
    (keep : b v=some true) (only : ∀i,i≠v → b i≠some true)
    (hit : (F c.k+G c.k)*dust c b=F c.k*NX c b+G c.k*NY c b) :
    let H:=2*(pref c b)*σ 0 (pref c b)
    let B:=c.e v+1; let C:=mult c b; let q:=c.p v; let u:=q-1
    H*B*C*u^2=q*(W (pref c b)*C*(B*u-1)+σ 1 (pref c b)*u) := by
  obtain ⟨av,sv,hv⟩:=prefix_moments c odd b
  obtain ⟨d,x,y⟩:=others c keep only
  dsimp only
  rw [av,sv,hv]
  unfold dust NX NY at hit
  rw [←prod_erase_mul _ _ (mem_univ v),←prod_erase_mul _ (fun i=>Nx _ _ _) (mem_univ v),
    ←prod_erase_mul _ (fun i=>Ny _ _ _) (mem_univ v)] at hit
  rw [d,x,y,keep] at hit
  simp only [Dn,Nx,Ny,den,xn,yn,if_true] at hit
  linear_combination hit

end OMA.FixedModeProduct245212

end

section

/- The restoration sign is strict. A dropped coordinate forces a strict
score increase; if none is dropped, equality is the excluded last-prime pole. -/
namespace OMA.FixedModeSign245212
open Finset Nat ArithmeticFunction OMA.Smooth245212 OMA.FixedRankGap245212 OMA.FixedModeRestore245212
open OMA.FixedModeProduct245212 OMA.TwoTallLocal245212
open OMA.ThreeMovingOriginal245212 (F G)
open scoped ArithmeticFunction.sigma

theorem drop_sign {r : ℕ} (c : Family r) {b : Fin r→Option Bool} {v : Fin r}
    {f g : ℕ} (fp : 0<f) (keep : b v=some true) (only : ∀i,i≠v → b i≠some true)
    (d : (dropped b).Nonempty) (hit : (f+g)*dust c b=f*NX c b+g*NY c b)
    (actual : score f g (exactX c) (exactY c)=(f+g:ℕ)) :
    (f:ℚ)*ox c b ∅ v<g*((c.p v:ℚ)-1)*oy c b ∅ v := by
  let V:=val c b f g
  have same:=OMA.FixedModeRestore245212.same c b f g hit actual
  have step (s : Finset (Fin r)) {i} (fr : i∉s) (drop : b i=some false) : V s<V (insert i s):=by
    have x:=caps c b s i
    have inc:=OMA.MiddleChange245212.dropped (f:=f) (g:=g) (c.prime i) (c.positive i) x.1 x.2.1
    have z:=change c b f g s fr
    rw [drop] at z
    have ni : 0<(f:ℚ)/(2*(c.p i:ℚ)):=by have:=(c.prime i).pos;positivity
    exact sub_pos.mp (z ▸ ni.trans_le inc)
  have adv (s : Finset (Fin r)) {i} (iv : i≠v) (fr : i∉s): V s≤V (insert i s):=by
    cases tag : b i with
    | none=>have q:=change c b f g s fr;rw [tag,OMA.MiddleChange245212.exact_inc] at q;exact (sub_eq_zero.mp q).symm.le
    | some t=>cases t with
      | false=>exact (step s fr tag).le
      | true=>exact False.elim (only i iv tag)
  have finish (s : Finset (Fin r)) (hv : v∈s) : V s≤V univ:=by
    have grow (t : Finset (Fin r)) : V s≤V (t∪s):=by
      induction t using Finset.induction_on with
      | empty=>simp
      | @insert i t fresh ih=>
        by_cases it : i∈t∪s
        · simpa only [insert_union,insert_eq_of_mem it] using ih
        · have iv : i≠v:=fun h=>it (h ▸ mem_union_right _ hv)
          simpa only [insert_union] using ih.trans (adv (t∪s) iv it)
    have union : (univ:Finset (Fin r))∪s=univ:=Finset.union_eq_left.mpr (subset_univ _)
    simpa only [union] using grow univ
  obtain ⟨i,im⟩:=d
  have fl : b i=some false:=(mem_filter.mp im).2
  have iv : i≠v:=by rintro rfl;simp_all
  have plus:=step {v} (by simpa using iv : i∉({v}:Finset (Fin r))) fl
  have minus : V {v}-V ∅<0:=sub_neg.mpr ((plus.trans_le
    (finish (insert i {v}) (mem_insert_of_mem (mem_singleton_self v)))).trans_eq same.symm)
  have formula:=change c b f g ∅ (notMem_empty v)
  rw [insert_empty,keep,OMA.MiddleChange245212.retained (c.prime v)] at formula
  have den : 0<((c.e v:ℚ)+1)*((c.p v:ℚ)-1)^2*(c.p v:ℚ)^c.e v:=by
    have : (1:ℚ)<c.p v:=by exact_mod_cast (c.prime v).one_lt
    positivity
  change val c b f g {v}-val c b f g ∅<0 at minus
  rw [formula] at minus
  exact sub_neg.mp (by simpa only [zero_mul] using (div_lt_iff₀ den).mp minus)

theorem side {r : ℕ} (c : Family r) (odd : ∀i,Odd (c.p i)) {b : Fin r→Option Bool} {v : Fin r}
    (keep : b v=some true) (only : ∀i,i≠v → b i≠some true)
    (weak : (F c.k:ℚ)*ox c b ∅ v≤(G c.k:ℚ)*((c.p v:ℚ)-1)*oy c b ∅ v)
    (hit : (F c.k+G c.k)*dust c b=F c.k*NX c b+G c.k*NY c b)
    (actual : score (F c.k) (G c.k) (exactX c) (exactY c)=(F c.k+G c.k:ℕ))
    (original : OeisA245212.a (2^c.k*total c.p c.e)=(σ 1 (2^c.k*total c.p c.e):ℤ)) :
    mult c b*W (pref c b)<(c.p v-1)*σ 1 (pref c b) := by
  let t:=(univ:Finset (Fin r)).erase v
  let de i:=Dn (c.p i) (c.e i) (b i)
  let D:=∏i∈t,de i
  have pos : (0:ℚ)<D:=by exact_mod_cast prod_pos (fun i _=>Dpos (c.prime i) _ (b i))
  have oxD : ox c b ∅ v*(D:ℚ)=((∏i∈t,Nx (c.p i) (c.e i) (b i)):ℕ) := by
    dsimp only [ox,xx,tag,notMem_empty,if_false,D];push_cast;rw [←prod_mul_distrib]
    exact prod_congr rfl (fun i _=>(moments (c.prime i) (c.e i) (b i)).1)
  have oyD : oy c b ∅ v*(D:ℚ)=((∏i∈t,Ny (c.p i) (c.e i) (b i)):ℕ) := by
    dsimp only [oy,yy,tag,notMem_empty,if_false,D];push_cast;rw [←prod_mul_distrib]
    exact prod_congr rfl (fun i _=>(moments (c.prime i) (c.e i) (b i)).2)
  have ⟨wp,sp,_⟩:=prefix_moments c odd b
  have ⟨_,x,y⟩:=others c keep only
  change (∏i∈t,_) = _ at x y
  rw [x] at oxD
  rw [y] at oyD
  have left : ((F c.k:ℚ)*ox c b ∅ v)*D=(mult c b*W (pref c b):ℕ):=by
    rw [mul_assoc,oxD,wp];push_cast;ring
  have right : ((G c.k:ℚ)*((c.p v:ℚ)-1)*oy c b ∅ v)*D=((c.p v-1)*σ 1 (pref c b):ℕ):=by
    rw [mul_assoc,oyD,sp];push_cast [Nat.cast_sub (c.prime v).pos];ring
  by_cases drop : (dropped b).Nonempty
  · have fp : 0<F c.k:=by dsimp [F];omega
    have sign:=drop_sign c fp keep only drop hit actual
    have z:=mul_lt_mul_of_pos_right sign pos
    rwa [left,right,Nat.cast_lt] at z
  · have emp : dropped b=∅:=not_nonempty_iff_eq_empty.mp drop
    have C : mult c b=1:=by simp [mult,emp]
    rw [C,one_mul]
    have le:=mul_le_mul_of_nonneg_right weak pos.le
    rw [left,right,C,one_mul,Nat.cast_le] at le
    refine lt_of_le_of_ne le ?_
    intro eq
    have part:=(partition keep only).2
    rw [emp,union_empty] at part
    have joined : pref c b*(c.p v)^c.e v=2^c.k*total c.p c.e:=by
      dsimp [pref,total];rw [part,mul_assoc,prod_erase_mul _ _ (mem_univ v)]
    have eqn : OeisA245212.a (pref c b*(c.p v)^c.e v)=(σ 1 (pref c b*(c.p v)^c.e v):ℤ):=by rwa [joined]
    have cop : (pref c b).Coprime (c.p v):=by
      dsimp only [pref];apply Nat.Coprime.mul_left
      · exact (Nat.coprime_two_left.mpr (odd v)).pow_left _
      · apply Nat.coprime_prod_left_iff.mpr
        intro i im
        have iv:=ne_of_mem_erase (part ▸ im)
        exact (((Nat.coprime_primes (c.prime i) (c.prime v)).mpr (c.inj.ne iv)).pow_left _)
    have pp : 0<pref c b:=mul_pos (Nat.two_pow_pos _) (prod_pos (fun i _=>pow_pos (c.prime i).pos _))
    have pn : c.p v≠2:=by have:=(c.prime v).odd_iff.mp (odd v);omega
    have no:=OMA.PrimePowerDiv245212.nonzero pp (c.prime v) pn cop (c.e v) eqn
    apply no
    have ez:=congrArg (fun x:ℕ=>(x:ℤ)) eq
    push_cast [Nat.cast_sub (c.prime v).pos] at ez
    exact sub_eq_zero.mpr ez

end OMA.FixedModeSign245212

end

section

/- The original equality produces the integer pole equation, strict side,
and a polynomially bounded exact cofactor at every fixed rank for k≥256. -/
namespace OMA.FixedModeArithmetic245212
open Nat Finset ArithmeticFunction OMA.FixedRankGap245212 OMA.FixedModeProduct245212
open OMA.Smooth245212 (W total)
open OMA.ThreeMovingOriginal245212 (F G)
open scoped ArithmeticFunction.sigma

def exponent (r : ℕ) := 2*OMA.FixedRankHeight245212.exponent r+1+
  OMA.FixedModeOriginal245212.exponent r*r

theorem rank_pref {r} (c : Family r) (b : Fin r→Option Bool) :
    (pref c b).primeFactors.card≤r+1 := by
  let s:=(univ : Finset (Fin r)).image c.p
  have cover : (pref c b).primeFactors⊆insert 2 s:=by
    intro z zm
    have pr:=prime_of_mem_primeFactors zm
    have dv:=dvd_of_mem_primeFactors zm
    obtain two|prod:=pr.dvd_mul.mp dv
    · have same:=(Nat.prime_dvd_prime_iff_eq pr Nat.prime_two).mp (pr.dvd_of_dvd_pow two)
      exact mem_insert.mpr (Or.inl same)
    · obtain ⟨i,_,di⟩:=(pr.prime.dvd_finsetProd_iff _).mp prod
      have :=(Nat.prime_dvd_prime_iff_eq pr (c.prime i)).mp (pr.dvd_of_dvd_pow di)
      exact mem_insert_of_mem (mem_image.mpr ⟨i,mem_univ _,this.symm⟩)
  have card : s.card=r:=by dsimp [s];rw [card_image_of_injective _ c.inj];simp
  exact (card_le_card cover).trans ((card_insert_le _ _).trans_eq (by rw [card]))

theorem small {r} (c : Family r) (odd : ∀i,Odd (c.p i)) (b : Fin r→Option Bool) {Q : ℕ}
    (large : OMA.FixedTallScalar245212.threshold r 1≤c.L)
    (Qcap : Q≤c.L^OMA.FixedModeOriginal245212.exponent r)
    (rule : ∀i,b i=if c.p i^c.e i≤Q then none else some (decide (c.p i≤Q)))
    (eqn : OeisA245212.a (2^c.k*total c.p c.e)=(σ 1 (2^c.k*total c.p c.e):ℤ)) :
    pref c b≤(c.L+1)^exponent r := by
  let E:=OMA.FixedRankHeight245212.exponent r
  let D:=OMA.FixedModeOriginal245212.exponent r
  let t:=c.L+1
  have e:=OMA.FixedRankHeight245212.original c.k c.L c.p c.e c.prime odd c.inj c.positive c.longest c.cap eqn
  have C : OMA.SingleMovingHeight245212.constant E≤t:=by
    dsimp only [OMA.FixedTallScalar245212.threshold] at large
    dsimp only [t,E];omega
  have two : 2^c.k≤t^(2*E+1):=e.trans (by rw [pow_succ'];exact Nat.mul_le_mul_right _ C)
  have per i (mem:i∈exactSet b) : c.p i^c.e i≤t^D:=by
    have none:=(mem_filter.mp mem).2
    rw [rule] at none
    have v : c.p i^c.e i≤Q:=by split at none <;> simp_all
    exact (v.trans Qcap).trans (Nat.pow_le_pow_left (Nat.le_succ _) _)
  have ec : (exactSet b).card≤r:=by simpa using card_le_card (subset_univ (exactSet b))
  have powers : (∏i∈exactSet b,c.p i^c.e i)≤t^(D*r):=by
    calc
      _ ≤ ∏_i∈exactSet b,t^D:=prod_le_prod' per
      _ = t^(D*(exactSet b).card):=by simp [←pow_mul]
      _ ≤ _:=Nat.pow_le_pow_right (by dsimp [t];omega) (Nat.mul_le_mul_left _ ec)
  rw [exponent,pow_add]
  exact Nat.mul_le_mul two powers

theorem original {r} (c : Family r) (odd : ∀i,Odd (c.p i))
    (klarge : 256≤c.k) (large : OMA.FixedTallScalar245212.threshold r 1≤c.L)
    (v : Fin r) (long : c.e v+1=c.L)
    (eqn : OeisA245212.a (2^c.k*total c.p c.e)=(σ 1 (2^c.k*total c.p c.e):ℤ)) :
    ∃ h q C : ℕ, 0<h ∧ h.primeFactors.card≤r+1 ∧ 2≤q ∧ 0<c.L ∧ 0<C ∧
      h≤(c.L+1)^exponent r ∧ C*W h<(q-1)*σ 1 h ∧
      (2*h*σ 0 h)*c.L*C*(q-1)^2=q*(W h*C*(c.L*(q-1)-1)+σ 1 h*(q-1)) := by
  obtain ⟨b,Q,_,Qcap,rule,hit,keep,only,weak⟩:=OMA.FixedModeOriginal245212.original c odd klarge large v long eqn
  have actual:=OMA.FixedRankHeight245212.physical c c.k odd c.inj eqn
  have hp : 0<pref c b:=mul_pos (Nat.two_pow_pos _) (prod_pos (fun i _=>pow_pos (c.prime i).pos _))
  have Cp : 0 < mult c b:=prod_pos (fun _ _=>Nat.succ_pos _)
  refine ⟨pref c b,c.p v,mult c b,hp,rank_pref c b,(c.prime v).two_le,by omega,Cp,
    small c odd b large Qcap rule eqn,OMA.FixedModeSign245212.side c odd keep only weak hit actual eqn,?_⟩
  simpa only [long] using equation c odd keep only hit

end OMA.FixedModeArithmetic245212

end

section

/- The fixed-support dyadic estimate directly on the original integer, without
an ordered factorization as input. The nonempty hypothesis removes pure powers of two. -/
namespace OMA.FixedRankInteger245212
open Nat Finset OMA.Smooth245212 OMA.FixedRankHeight245212
open scoped ArithmeticFunction.sigma

def support (n : ℕ) := n.primeFactors.erase 2
def longest (n : ℕ) := (support n).sup (fun p=>n.factorization p+1)
def polynomial (r L : ℕ) := OMA.SingleMovingHeight245212.constant (exponent r)*(L+1)^(2*exponent r)

/-- A single explicit function works simultaneously for every nonempty odd
support, even when the number of primes is itself allowed to vary. -/
theorem original {n : ℕ} (pos : 0<n) (nonempty : (support n).Nonempty)
    (eqn : OeisA245212.a n=(σ 1 n:ℤ)) :
    2^(n.factorization 2)≤polynomial (support n).card (longest n) := by
  let s:=support n
  let P : Fin s.card ↪o ℕ:=s.orderEmbOfFin rfl
  let e (i : Fin s.card):=n.factorization (P i)
  have mem (i : Fin s.card) : P i∈s:=s.orderEmbOfFin_mem rfl i
  have prime i := prime_of_mem_primeFactors (mem_erase.mp (mem i)).2
  have odd i := (prime i).odd_of_ne_two (mem_erase.mp (mem i)).1
  have ep (i) : 0<e i:=Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (mem_erase.mp (mem i)).2)
  have lift : univ.map P.toEmbedding=s:=s.map_orderEmbOfFin_univ rfl
  have fac : 2^(n.factorization 2)*(∏ p∈s,p^(n.factorization p))=n := by
    by_cases h : 2∈n.primeFactors
    · exact (mul_prod_erase n.primeFactors (fun p => p^(n.factorization p)) h).trans
        (Nat.prod_primeFactors_pow_factorization pos.ne').symm
    · have z : n.factorization 2=0:=Finsupp.notMem_support_iff.mp h
      simpa [z,s,support,erase_eq_of_notMem h] using (Nat.prod_primeFactors_pow_factorization pos.ne').symm
  rw [←lift,prod_map] at fac
  change 2^(n.factorization 2)*total P e=n at fac
  obtain ⟨z,zm,zt⟩:=Finset.exists_mem_eq_sup s nonempty (fun p=>n.factorization p+1)
  obtain ⟨i,_,zi⟩:=Finset.mem_map.mp (lift.symm ▸ zm)
  change P i=z at zi
  have zmax : ∃ i,e i+1=longest n:=⟨i,by change n.factorization (P i)+1=longest n;rw [zi];exact zt.symm⟩
  have cap i : e i+1≤longest n := Finset.le_sup (f:=fun p=>n.factorization p+1) (mem i)
  exact OMA.FixedRankHeight245212.original (n.factorization 2) (longest n) P e prime odd P.injective ep zmax cap (by rwa [fac])

/-- In rank four the exponent of (L+1) is exactly 824633720840. -/
theorem four {n : ℕ} (pos : 0<n) (rank : (support n).card=4)
    (eqn : OeisA245212.a n=(σ 1 n:ℤ)) :
    2^(n.factorization 2)≤OMA.SingleMovingHeight245212.constant 412316860420*(longest n+1)^824633720840 := by
  have ne:=Finset.card_pos.mp (show 0<(support n).card by omega)
  simpa only [rank,polynomial,show exponent 4=412316860420 by decide,show 2*412316860420=824633720840 by decide]
    using original pos ne eqn

end OMA.FixedRankInteger245212

end

section

/- A uniform one-sided integer gap for any number of factors of the form
g*z+1. The multiplier depends on the coefficients and the number of factors,
but not on the positive variables z or the numerator U. -/
namespace OMA.PositiveProductGap245212
open Finset
variable {ι : Type*} [DecidableEq ι]

def cost : ℕ → ℕ → ℕ
  | 0,_ => 1
  | n+1,A => 2*(A+1)*cost n (2*(A+1)^2)

private theorem cost_pos (n A : ℕ) : 0<cost n A := by
  induction n generalizing A with
  | zero => simp [cost]
  | succ n ih => exact Nat.mul_pos (by positivity) (ih _)

private theorem error {s : Finset ι} (g z : ι→ℕ) (m : ℕ)
    (lower : ∀i∈s, m≤z i) (positive : ∀i∈s, 0<z i) :
    let P:=∏i∈s,z i
    let Q:=∏i∈s,(g i*z i+1)
    let c:=∏i∈s,g i
    let A:=∏i∈s,(g i+1)
    c*P ≤ Q ∧ Q ≤ A*P ∧ m*Q ≤ m*(c*P)+A*P := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have lo:=lower i (mem_insert_self ..)
    have po:=positive i (mem_insert_self ..)
    obtain ⟨lb,ub,err⟩:=ih (fun j hj=>lower j (mem_insert_of_mem hj))
      (fun j hj=>positive j (mem_insert_of_mem hj))
    simp only [prod_insert hi]
    refine ⟨?_,?_,?_⟩
    · have h:=Nat.mul_le_mul (Nat.le_succ (g i*z i)) lb
      simpa only [mul_comm,mul_assoc,mul_left_comm] using h
    · have h:=Nat.mul_le_mul (show g i*z i+1≤(g i+1)*z i by nlinarith only [po]) ub
      simpa only [mul_comm,mul_assoc,mul_left_comm] using h
    · have h:=Nat.mul_le_mul_left (g i*z i) err
      have small:=Nat.mul_le_mul lo ub
      nlinarith only [h,small]

theorem gap (n A : ℕ) (s : Finset ι) (g z : ι→ℕ) {U V R : ℕ}
    (count : s.card=n) (pos : ∀i∈s,0<z i) (rp : 0<R)
    (budget : V*(∏i∈s,(g i+1))≤A)
    (eqn : U*(∏i∈s,z i)=R+V*(∏i∈s,(g i*z i+1))) :
    (∏i∈s,z i)≤cost n A*R := by
  induction n generalizing A s U V with
  | zero =>
    have empty:=Finset.card_eq_zero.mp count
    simpa [empty,cost] using (show 1≤R from rp)
  | succ n ih =>
    by_cases small : ∃i∈s,z i≤2*(A+1)
    · obtain ⟨i,mem,lim⟩:=small
      let t:=s.erase i
      have mult (x : ι→ℕ) : x i*(∏j∈t,x j)=∏j∈s,x j := by
        rw [mul_comm];exact prod_erase_mul _ _ mem
      have zp:=pos i mem
      have cb : (V*(g i*z i+1))*(∏j∈t,(g j+1))≤2*(A+1)^2 := calc
        _ ≤ z i*(V*(∏j∈s,(g j+1))) := by
          rw [←mult (fun j=>g j+1)]
          have h:=Nat.mul_le_mul_left (V*(∏j∈t,(g j+1)))
            (show g i*z i+1≤z i*(g i+1) by nlinarith only [zp])
          simpa only [mul_comm,mul_assoc,mul_left_comm] using h
        _ ≤ 2*(A+1)*(A+1) := Nat.mul_le_mul lim (budget.trans (Nat.le_succ _))
        _ = _ := by ring
      have eq : (U*z i)*(∏j∈t,z j)=R+(V*(g i*z i+1))*(∏j∈t,(g j*z j+1)) := by
        rw [Nat.mul_assoc,Nat.mul_assoc,mult z,mult (fun j=>g j*z j+1)]
        exact eqn
      have smaller:=ih (2*(A+1)^2) t (by dsimp [t];rw [card_erase_of_mem mem,count];omega)
        (fun j hj=>pos j (mem_of_mem_erase hj)) cb eq
      rw [←mult z]
      exact (Nat.mul_le_mul lim smaller).trans_eq (by simp only [cost,Nat.mul_assoc])
    · have lo i (mem:i∈s) : 2*(A+1)≤z i:=by
        have no : ¬z i≤2*(A+1):=fun h=>small ⟨i,mem,h⟩
        omega
      obtain ⟨lb,_,err⟩:=error g z (2*(A+1)) lo pos
      let P:=∏i∈s,z i
      let Q:=∏i∈s,(g i*z i+1)
      let c:=∏i∈s,g i
      let B:=∏i∈s,(g i+1)
      change c*P≤Q at lb
      change 2*(A+1)*Q≤2*(A+1)*(c*P)+B*P at err
      change U*P=R+V*Q at eqn
      have uc : V*c<U := by
        by_contra! rev
        have h:=Nat.mul_le_mul_right P rev
        have l:=Nat.mul_le_mul_left V lb
        nlinarith only [h,l,eqn,rp]
      have h:=Nat.mul_le_mul_right P (Nat.succ_le_of_lt uc)
      have extra:=Nat.mul_le_mul_left V err
      have cap:=Nat.mul_le_mul_right P budget
      change V*B*P≤A*P at cap
      have joined:=Nat.mul_le_mul_left (2*(A+1)) h
      have id:=congrArg (2*(A+1)*·) eqn
      have pr : P≤2*R := by
        by_contra! bad
        have worse:=Nat.mul_lt_mul_of_pos_left bad (Nat.succ_pos A)
        nlinarith only [extra,cap,joined,id,worse,Nat.zero_le P]
      change P≤cost (n+1) A*R
      have big : 2≤cost (n+1) A:=
        calc
          2 ≤ 2*(A+1) := by omega
          _ ≤ _ := Nat.le_mul_of_pos_right _ (cost_pos n _)
      exact pr.trans (Nat.mul_le_mul_right R big)

end OMA.PositiveProductGap245212

end

section

/- Quantitative separation below rational targets for products of normalized
weighted divisor sums. The bound does not contain any prime power. -/
namespace OMA.WeightedUpperGap245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
variable {ι : Type*} [DecidableEq ι]

def mass (p e : ℕ) := (e+1)*p^e
def coeff (p e : ℕ) := p*((e+1)*(p-1)-1)
def boundedCost (r V T B : ℕ) :=
  (T^r*(B^2)^r)*OMA.PositiveProductGap245212.cost r (V*(B*(T*B)+1)^r)

theorem local_moment {p : ℕ} (pr : p.Prime) (e : ℕ) :
    (p-1)^2*W (p^e)=coeff p e*p^e+1 := by
  have base : 1≤(e+1)*(p-1):=Nat.mul_pos (Nat.succ_pos _) (Nat.sub_pos_of_lt pr.one_lt)
  unfold coeff
  zify [Nat.cast_sub pr.pos,Nat.cast_sub base]
  exact (OMA.ComplementaryLocal245212.moments pr e).2

theorem bounded {s : Finset ι} (p e : ι→ℕ) (V U R T B : ℕ)
    (pr : ∀i∈s,(p i).Prime) (base : ∀i∈s,p i≤B) (len : ∀i∈s,e i+1≤T) (rp : 0<R)
    (eqn : U*(∏i∈s,mass (p i) (e i))=R+V*(∏i∈s,W ((p i)^(e i)))) :
    (∏i∈s,mass (p i) (e i))≤boundedCost s.card V T B*R := by
  let z i:=p i^e i
  let g i:=coeff (p i) (e i)
  let L:=∏i∈s,(p i-1)^2
  let M:=∏i∈s,(e i+1)
  let P:=∏i∈s,z i
  let Wp:=∏i∈s,W (p i^e i)
  have mass_eq : (∏i∈s,mass (p i) (e i))=M*P:=by simp only [mass,prod_mul_distrib,M,P,z]
  have weights : L*Wp=∏i∈s,(g i*z i+1):=by
    dsimp only [L,Wp]
    rw [←prod_mul_distrib]; exact prod_congr rfl (fun i hi=>local_moment (pr i hi) _)
  have lpos : 0<L:=prod_pos fun i hi=>pow_pos (Nat.sub_pos_of_lt (pr i hi).one_lt) _
  have gb : V*(∏i∈s,(g i+1))≤V*(B*(T*B)+1)^s.card:=by
    apply Nat.mul_le_mul_left
    calc
      _ ≤ ∏_i∈s,(B*(T*B)+1) := by
        apply prod_le_prod'
        intro i hi
        exact Nat.succ_le_succ (Nat.mul_le_mul (base i hi) ((Nat.sub_le _ _).trans
          (Nat.mul_le_mul (len i hi) ((Nat.sub_le _ _).trans (base i hi)))))
      _ = _ := by simp
  have gap : (U*L*M)*P=L*R+V*(∏i∈s,(g i*z i+1)):=by
    rw [←weights]
    rw [mass_eq] at eqn
    change U*(M*P)=R+V*Wp at eqn
    nlinarith only [congrArg (L*·) eqn]
  have res:=OMA.PositiveProductGap245212.gap _ _ s g z rfl
    (fun i hi=>pow_pos (pr i hi).pos _) (Nat.mul_pos lpos rp) gb gap
  have lcap : L≤(B^2)^s.card:=calc
    L ≤ ∏_i∈s,B^2 := prod_le_prod' fun i hi=>Nat.pow_le_pow_left ((Nat.sub_le _ _).trans (base i hi)) _
    _ = _ := by simp
  have mcap : M≤T^s.card:=calc
    M ≤ ∏_i∈s,T := prod_le_prod' len
    _ = _ := by simp
  rw [mass_eq]
  have out:=Nat.mul_le_mul mcap res
  let C:=OMA.PositiveProductGap245212.cost s.card (V*(B*(T*B)+1)^s.card)
  change M*P≤T^s.card*(C*(L*R)) at out
  exact out.trans (by
    have h:=Nat.mul_le_mul_left (T^s.card*C*R) lcap
    simpa only [boundedCost,C,mul_assoc,mul_comm,mul_left_comm] using h)

theorem local_range {p : ℕ} (pr : p.Prime) (e : ℕ) :
    mass p e≤W (p^e) ∧ (p-1)*W (p^e)≤p*mass p e ∧ W (p^e)≤2*mass p e := by
  have identity:=OMA.PrimePowerDiv245212.weighted pr e
  have lower : mass p e≤W (p^e):=by
    rw [w_pow pr];unfold mass
    simpa only [mul_comm] using single_le_sum (f:=fun i=>p^i*(i+1)) (fun i _=>Nat.zero_le _)
      (mem_range.mpr (Nat.lt_succ_self e))
  have upper : (p-1)*W (p^e)≤p*mass p e:=by dsimp [mass];omega
  have nz : 0<p-1:=Nat.sub_pos_of_lt pr.one_lt
  have p2 : p≤(p-1)*2:=by omega
  have h:=upper.trans (Nat.mul_le_mul_right (mass p e) p2)
  exact ⟨lower,upper,Nat.le_of_mul_le_mul_left (by simpa only [mul_assoc] using h) nz⟩

-- The rank-r target gap survives adding one sufficiently large prime.
theorem large_step {U V A T x y p K E R : ℕ}
    (left : U*T=E+V*A) (coarse : A≤T*(2^p))
    (old : T≤K*E) {prime : ℕ} (strong : 2*K*V*2^p≤prime-1)
    (massbound : (prime-1)*y≤prime*x) (pr : 2≤prime)
    (full : U*(T*x)=R+V*(A*y)) : T*x≤(2*K)*R := by
  have den : 0<prime-1:=by omega
  have add:=Nat.sub_add_cancel (show 1≤prime by omega)
  have localDiff : (prime-1)*y≤(prime-1)*x+x:=by nlinarith only [massbound,congrArg (·*x) add]
  have rem:=Nat.mul_le_mul_left (V*A) localDiff
  have e:=congrArg (·*((prime-1)*x)) left
  have f:=congrArg ((prime-1)*·) full
  have gap : (prime-1)*E*x ≤ (prime-1)*R + V*A*x:=by nlinarith only [rem,e,f]
  have h:=Nat.mul_le_mul_left ((prime-1)*x) old
  have b:=Nat.mul_le_mul_left K gap
  have err:=Nat.mul_le_mul_left (2*K*V*x) coarse
  have top:=Nat.mul_le_mul_right (T*x) strong
  have goal : (prime-1)*(T*x)≤(prime-1)*((2*K)*R) := by
    nlinarith only [h,b,err,top]
  exact Nat.le_of_mul_le_mul_left goal den

end OMA.WeightedUpperGap245212

end

section

/- A rational strictly above the normalized weighted moment is separated
from it independently of all the prime bases and prime powers. -/
namespace OMA.WeightedUniformGap245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.WeightedUpperGap245212
open scoped ArithmeticFunction.sigma
variable {ι : Type*} [DecidableEq ι]

def cutoff (r x K : ℕ) := 2*K*x*2^r+2
def constant : ℕ→ℕ→ℕ
  | 0,_ => 1
  | r+1,x => let K:=constant r x; 2*K+boundedCost (r+1) x x (cutoff r x K)

theorem cost_mono (n : ℕ) : Monotone (OMA.PositiveProductGap245212.cost n) := by
  induction n with
  | zero => intro _ _ _;rfl
  | succ n ih =>
    intro a b le
    dsimp only [OMA.PositiveProductGap245212.cost]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.succ_le_succ le))
      (ih (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.succ_le_succ le) 2)))

theorem bound (n x : ℕ) (s : Finset ι) (p e : ι→ℕ) {U V R : ℕ}
    (count : s.card=n) (pr : ∀i∈s,(p i).Prime) (len : ∀i∈s,e i+1≤x)
    (vx : V≤x) (rp : 0<R)
    (eqn : U*(∏i∈s,mass (p i) (e i))=R+V*(∏i∈s,W ((p i)^(e i)))) :
    (∏i∈s,mass (p i) (e i))≤constant n x*R := by
  induction n generalizing s R with
  | zero =>
    have empty:=card_eq_zero.mp count
    simpa [empty,constant] using (show 1≤R from rp)
  | succ n ih =>
    let K:=constant n x
    let B:=cutoff n x K
    by_cases low : ∀i∈s,p i≤B
    · have h:=bounded p e V U R x B pr low len rp eqn
      rw [count] at h
      have c : boundedCost (n+1) V x B ≤ boundedCost (n+1) x x B := by
        unfold boundedCost
        exact Nat.mul_le_mul_left _ (cost_mono _ (Nat.mul_le_mul_right _ vx))
      exact h.trans (Nat.mul_le_mul_right R (c.trans (Nat.le_add_left _ _)))
    push Not at low
    obtain ⟨i,mem,high⟩:=low
    let t:=s.erase i
    have card : t.card=n:=by dsimp [t];rw [card_erase_of_mem mem,count];omega
    let M j:=mass (p j) (e j)
    let A j:=W ((p j)^(e j))
    let P:=∏j∈t,M j
    let Q:=∏j∈t,A j
    have combine (f : ι→ℕ) : (∏j∈t,f j)*f i=∏j∈s,f j := prod_erase_mul _ _ mem
    change U*(∏j∈s,M j)=R+V*(∏j∈s,A j) at eqn
    rw [←combine M,←combine A] at eqn
    change U*(P*M i)=R+V*(Q*A i) at eqn
    have loc:=local_range (pr i mem) (e i)
    change M i≤A i ∧ (p i-1)*A i≤p i*M i ∧ _ at loc
    have pv : V*Q<U*P:=by
      by_contra! bad
      have h:=Nat.mul_le_mul bad loc.1
      nlinarith only [h,eqn,rp]
    let E:=U*P-V*Q
    have ep : 0<E:=Nat.sub_pos_of_lt pv
    have prev : U*P=E+V*Q:=(Nat.sub_add_cancel pv.le).symm
    have old : P≤K*E:=ih t card (fun j mj=>pr j (mem_of_mem_erase mj))
      (fun j mj=>len j (mem_of_mem_erase mj)) ep prev
    have coarse : Q≤P*2^n:=calc
      Q ≤ ∏j∈t,(2*M j) := prod_le_prod' fun j hj=>(local_range (pr j (mem_of_mem_erase hj)) (e j)).2.2
      _ = _ := by simp [prod_mul_distrib,card,P,mul_comm]
    have strong : 2*K*V*2^n≤p i-1:=by
      change 2*K*x*2^n+2<p i at high
      have h:=Nat.mul_le_mul_right (2^n) (Nat.mul_le_mul_left (2*K) vx)
      omega
    have lift:=large_step prev coarse old strong loc.2.1 (pr i mem).two_le eqn
    change (∏j∈s,M j)≤_
    rw [←combine M]
    exact lift.trans (Nat.mul_le_mul_right R (Nat.le_add_right _ _))

end OMA.WeightedUniformGap245212

end

section

/- A single polynomial controls every cofactor of bounded rank, without
fixing its bases, exponents, or numerator of the rational target. -/
namespace OMA.WeightedGapPolynomial245212
noncomputable section
open Nat Finset ArithmeticFunction Polynomial OMA.WeightedUpperGap245212
open OMA.Smooth245212 (W w_mult)
open scoped ArithmeticFunction.sigma Function

def localCost : ℕ→Polynomial ℕ→Polynomial ℕ
  | 0,_ => 1
  | n+1,A => 2*(A+1)*localCost n (2*(A+1)^2)

def fixed : ℕ→Polynomial ℕ
  | 0 => 1
  | r+1 => let K:=fixed r; let B:=2*K*X*2^r+2
           2*K+(X^(r+1)*(B^2)^(r+1))*localCost (r+1) (X*(B*(X*B)+1)^(r+1))

def envelope (r : ℕ) : Polynomial ℕ := ∑j∈range (r+1),fixed j

theorem evaluate_local (n x : ℕ) (A : Polynomial ℕ) :
    (localCost n A).eval x=OMA.PositiveProductGap245212.cost n (A.eval x) := by
  induction n generalizing A with
  | zero => simp [localCost,OMA.PositiveProductGap245212.cost]
  | succ n ih => simp [localCost,OMA.PositiveProductGap245212.cost,ih]

theorem evaluate_fixed (r x : ℕ) : (fixed r).eval x=OMA.WeightedUniformGap245212.constant r x := by
  induction r with
  | zero => simp [fixed,OMA.WeightedUniformGap245212.constant]
  | succ r ih => simp [fixed,evaluate_local,ih,OMA.WeightedUniformGap245212.constant,
      OMA.WeightedUniformGap245212.cutoff,boundedCost]

theorem monotone_eval (P : Polynomial ℕ) : Monotone P.eval := by
  intro a b le
  simp only [eval_eq_sum,Polynomial.sum]
  exact sum_le_sum (fun i _=>Nat.mul_le_mul_left _ (Nat.pow_le_pow_left le i))

theorem eval_height (P : Polynomial ℕ) (x : ℕ) :
    P.eval x≤P.eval 1*(x+1)^P.natDegree := by
  rw [eval_eq_sum,eval_eq_sum]
  simp only [Polynomial.sum,one_pow,mul_one,sum_mul]
  refine sum_le_sum fun i hi=>Nat.mul_le_mul_left _ ?_
  exact (Nat.pow_le_pow_left (Nat.le_succ _) i).trans
    (Nat.pow_le_pow_right (Nat.succ_pos _) (P.le_natDegree_of_mem_supp i hi))

theorem original {h U V R r x : ℕ} (hp : 0<h) (rank : h.primeFactors.card≤r)
    (len : ∀p∈h.primeFactors,h.factorization p+1≤x) (vx : V≤x) (rp : 0<R)
    (eqn : U*(h*σ 0 h)=R+V*W h) : h*σ 0 h≤(envelope r).eval x*R := by
  let s:=h.primeFactors
  let z (p:ℕ):=p^h.factorization p
  have repr : h=∏p∈s,z p:=Nat.prod_primeFactors_pow_factorization hp.ne'
  have pr (p) (mp:p∈s) := prime_of_mem_primeFactors mp
  have pair : (s:Set ℕ).Pairwise (Coprime on z):=by
    intro p mp q mq ne
    exact (((coprime_primes (pr p mp) (pr q mq)).mpr ne).pow_left _).pow_right _
  have weight:=IsMultiplicative.map_prod z w_mult s pair
  have tau:=IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=0)) s pair
  rw [←repr] at weight tau
  have lengths : (∏p∈s,(h.factorization p+1))=σ 0 h := by
    rw [tau]
    exact prod_congr rfl (fun p mp=>(sigma_zero_apply_prime_pow (pr p mp)).symm)
  have mass_eq : (∏p∈s,mass p (h.factorization p))=h*σ 0 h := by
    simp only [mass,prod_mul_distrib]
    change (∏p∈s,(h.factorization p+1))*(∏p∈s,z p)=_
    rw [lengths,←repr,mul_comm]
  have ineq:=OMA.WeightedUniformGap245212.bound s.card x s id (fun p=>h.factorization p)
    (U:=U) rfl pr len vx rp (by
      change U*(∏i∈s,mass i (h.factorization i))=R+V*(∏i∈s,W (z i))
      rwa [mass_eq,←weight])
  change (∏p∈s,mass p (h.factorization p))≤_ at ineq
  rw [mass_eq] at ineq
  have inc : (fixed s.card).eval x≤(envelope r).eval x:=by
    simp only [envelope,eval_finsetSum]
    exact single_le_sum (f:=fun j=>(fixed j).eval x) (fun _ _=>Nat.zero_le _)
      (mem_range.mpr (Nat.lt_succ_of_le rank))
  rw [evaluate_fixed] at inc
  exact ineq.trans (Nat.mul_le_mul_right R inc)

end
end OMA.WeightedGapPolynomial245212

end

section

/- Removal of all cofactor prime bases from the pole bound of a retained
prime. The remaining exponent is polynomially bounded in log of the cofactor. -/
namespace OMA.ArbitraryMixedGap245212
noncomputable section
open Nat Finset ArithmeticFunction Polynomial OMA.WeightedGapPolynomial245212
open OMA.Smooth245212 (W)
open scoped ArithmeticFunction.sigma
open OMA.CofactorCrossOriginal245212 (sigma_bound)

def poly (r : ℕ) : Polynomial ℕ :=
  let K:=2*envelope r
  2*K+2*K*(2*(envelope r).comp (X+2*K))

private theorem equations {H A S B C q u : ℕ} (qv : q=u+1) (up : 0<u)
    (bp : 0<B) (cp : 0<C) (ss : S≤H) (side : C*A<u*S)
    (hit : H*B*C*u^2=q*(A*C*(B*u-1)+S*u)) :
    ∃ E Δ : ℕ, 0<E ∧ 0<Δ ∧ E+q*A=u*H ∧ Δ+A=H ∧ B*E≤q*H ∧ q*Δ=E+H := by
  have qp : 0<q:=by omega
  have bu:=Nat.sub_add_cancel (show 1≤B*u from Nat.mul_pos bp up)
  have raw : B*u*C*(H*u)+q*(A*C)=B*u*C*(A*q)+q*(u*S):=by
    nlinarith only [hit,congrArg (fun z : ℕ=>q*(A*C)*z) bu]
  have strict : A*q<H*u:=by
    by_contra! no
    have low:=Nat.mul_le_mul_left (B*u*C) no
    have sign:=Nat.mul_lt_mul_of_pos_left side qp
    nlinarith only [raw,low,sign]
  have ah : A<H:=by
    by_contra! no
    have bad:=Nat.mul_le_mul_right u no
    rw [qv,Nat.mul_add,Nat.mul_one] at strict
    omega
  let E:=H*u-A*q
  let Δ:=H-A
  have ee : E+q*A=u*H:=by
    dsimp only [E];rw [Nat.mul_comm q A,Nat.mul_comm u H,Nat.sub_add_cancel strict.le]
  have de : Δ+A=H:=Nat.sub_add_cancel ah.le
  have prod : B*u*C*E+q*(A*C)=q*(u*S):=by
    nlinarith only [raw,congrArg (fun z : ℕ=>B*u*C*z) ee]
  have main : (B*E*C)*u≤(q*S)*u:=by nlinarith only [prod,Nat.zero_le (q*(A*C))]
  have bare:=Nat.le_of_mul_le_mul_right main up
  refine ⟨E,Δ,Nat.sub_pos_of_lt strict,Nat.sub_pos_of_lt ah,ee,de,
    (Nat.le_mul_of_pos_right _ cp).trans (bare.trans (Nat.mul_le_mul_left q ss)),?_⟩
  nlinarith only [ee,congrArg (q*·) de,congrArg (·*H) qv]

theorem mixed {h q B C r : ℕ} (pos : 0<h) (rank : h.primeFactors.card≤r)
    (qg : 2≤q) (bp : 0<B) (cp : 0<C)
    (side : C*W h<(q-1)*σ 1 h)
    (hit : (2*h*σ 0 h)*B*C*(q-1)^2=q*(W h*C*(B*(q-1)-1)+σ 1 h*(q-1))) :
    B≤(poly r).eval (Nat.log 2 h+2) := by
  let x:=Nat.log 2 h+2
  let H:=2*(h*σ 0 h)
  let K:=2*(envelope r).eval x
  have lengths (p) (mem:p∈h.primeFactors) : h.factorization p+1≤x:=by
    have pow : 2^h.factorization p≤h:=(Nat.pow_le_pow_left (prime_of_mem_primeFactors mem).two_le _).trans
      (Nat.le_of_dvd pos (Nat.ordProj_dvd h p))
    have log:=Nat.le_log_of_pow_le (by decide : 1<(2:ℕ)) pow
    dsimp [x];omega
  have ss : σ 1 h≤H:=(OMA.CofactorCrossOriginal245212.sigma_bound pos).trans (by dsimp [H];omega)
  obtain ⟨E,Δ,ep,dp,ee,de,sb,id⟩:=equations (H:=H) (u:=q-1) (q:=q) (by omega) (by omega)
    bp cp ss side (by simpa only [H,mul_assoc] using hit)
  have rel (v t y z : ℕ) (yp : 0<y) (vz : v≤z) (xz : x≤z) (eqn : y+v*W h=t*H) :
      H≤(2*(envelope r).eval z)*y:=by
    have e : (t*2)*(h*σ 0 h)=y+v*W h:=by
      simpa only [H,mul_assoc] using eqn.symm
    have g:=OMA.WeightedGapPolynomial245212.original pos rank (fun p m=>(lengths p m).trans xz) vz yp e
    simpa only [H,mul_assoc] using Nat.mul_le_mul_left 2 g
  have first : H≤K*Δ:=rel 1 1 Δ x dp (by dsimp [x];omega) le_rfl (by simpa using de)
  change B≤(poly r).eval x
  simp only [poly,eval_add,eval_mul,eval_ofNat,eval_comp,eval_X]
  change B≤2*K+2*K*(2*(envelope r).eval (x+2*K))
  by_cases large : 2*K≤q
  · have high:=Nat.mul_le_mul_right Δ large
    have bound : q*Δ≤2*E:=by nlinarith only [high,id,first]
    have hq:=Nat.mul_le_mul_left q first
    have b:=Nat.mul_le_mul_left K bound
    have fin : B*E≤(2*K)*E:=by nlinarith only [sb,hq,b]
    exact (Nat.le_of_mul_le_mul_right fin ep).trans (Nat.le_add_right _ _)
  · have qz : q≤x+2*K:=by omega
    have close:=rel q (q-1) E (x+2*K) ep qz (Nat.le_add_right _ _) ee
    have hq:=Nat.mul_le_mul_left q close
    have fin : B*E≤(q*(2*(envelope r).eval (x+2*K)))*E:=by
      simpa only [mul_assoc] using sb.trans hq
    exact (Nat.le_of_mul_le_mul_right fin ep).trans
      ((Nat.mul_le_mul_right _ (by omega : q≤2*K)).trans (Nat.le_add_left _ _))

end
end OMA.ArbitraryMixedGap245212

end

section

/- Absolute length bound for an exact physical rounding with one retained
prime, any number of exact primes, and any number of discarded primes. -/
namespace OMA.ArbitraryMixedFinite245212
noncomputable section
open Nat ArithmeticFunction OMA.ArbitraryMixedGap245212 OMA.WeightedGapPolynomial245212
open OMA.Smooth245212 (W)
open scoped ArithmeticFunction.sigma

def cutoff (r D : ℕ) :=
  let F:=poly r
  let a:=F.eval 1+1
  let d:=F.natDegree
  a*(16*(d*D+1)^2+2*(a*D)+6)^d

theorem bounded {h q B C r D : ℕ} (pos : 0<h) (rank : h.primeFactors.card≤r)
    (qg : 2≤q) (bp : 0<B) (cp : 0<C) (small : h≤(B+1)^D)
    (side : C*W h<(q-1)*σ 1 h)
    (hit : (2*h*σ 0 h)*B*C*(q-1)^2=q*(W h*C*(B*(q-1)-1)+σ 1 h*(q-1))) :
    B≤cutoff r D := by
  let l:=Nat.log 2 h
  let F:=poly r
  let d:=F.natDegree
  let a:=F.eval 1+1
  let y:=l+3
  have base : B≤F.eval 1*y^d:=(mixed pos rank qg bp cp side hit).trans (eval_height _ _)
  have plus : B+1≤a*y^d:=by
    have one:=Nat.one_le_pow d y (by dsimp [y];omega)
    dsimp only [a];nlinarith only [base,one]
  have pot : 2^l≤2^(a*D)*y^(d*D):=calc
    _ ≤ h := Nat.pow_log_le_self 2 pos.ne'
    _ ≤ (B+1)^D := small
    _ ≤ (a*y^d)^D := Nat.pow_le_pow_left plus _
    _ = a^D*y^(d*D) := by rw [mul_pow,pow_mul]
    _ ≤ _ := by
      rw [pow_mul (2:ℕ) a D]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.lt_pow_self (by decide : 1<(2:ℕ))).le _)
  have bound : y≤16*(d*D+1)^2+2*(a*D)+6:=by
    by_cases big : 16*(d*D+1)^2≤y
    · have absorb:=OMA.ComplementarySize245212.absorb big
      have square:=Nat.pow_le_pow_left pot 2
      have hsq : (2^(a*D)*y^(d*D))^2=2^(2*(a*D))*y^(2*(d*D)):=by
        rw [mul_pow,←pow_mul,←pow_mul,Nat.mul_comm (a*D) 2,Nat.mul_comm (d*D) 2]
      have joined : 2^(2*l)≤2^(2*(a*D)+y):=by
        rw [pow_add]
        rw [hsq,←pow_mul,Nat.mul_comm l 2] at square
        exact square.trans (Nat.mul_le_mul_left _ absorb)
      have exp:=(pow_le_pow_iff_right₀ (a:=(2:ℕ)) (by decide)).mp joined
      dsimp only [y] at exp ⊢;omega
    · omega
  exact (Nat.le_succ B).trans (plus.trans (Nat.mul_le_mul_left a (Nat.pow_le_pow_left bound d)))

end
end OMA.ArbitraryMixedFinite245212

end

section

/- At each fixed rank all solutions with large dyadic valuation have bounded
odd exponent lengths. Consequently the dyadic valuation is always bounded;
the independently established fixed-dyadic-order height closes rank four. -/
namespace OMA.FixedModeClose245212
open Nat Finset OMA.FixedRankGap245212 OMA.FixedRankInteger245212
open OMA.Smooth245212 (total)
open scoped ArithmeticFunction.sigma

noncomputable section

def lengthCap (r : ℕ) := OMA.FixedTallScalar245212.threshold r 1+
  OMA.ArbitraryMixedFinite245212.cutoff (r+1) (OMA.FixedModeArithmetic245212.exponent r)
def kCap (r : ℕ) := 256+polynomial r (lengthCap r)

theorem high {r : ℕ} (c : Family r) (odd : ∀i,Odd (c.p i)) (klarge : 256≤c.k)
    (eqn : OeisA245212.a (2^c.k*total c.p c.e)=(σ 1 (2^c.k*total c.p c.e):ℤ)) : c.L≤lengthCap r := by
  by_cases big : OMA.FixedTallScalar245212.threshold r 1≤c.L
  · obtain ⟨v,vl⟩:=c.longest
    obtain ⟨h,q,C,hp,rank,qg,bp,cp,small,side,hit⟩:=OMA.FixedModeArithmetic245212.original c odd klarge big v vl eqn
    exact (OMA.ArbitraryMixedFinite245212.bounded hp rank qg bp cp small side hit).trans (Nat.le_add_left _ _)
  · exact (le_of_lt (lt_of_not_ge big)).trans (Nat.le_add_right _ _)

theorem orderBound {r k L : ℕ} (p e : Fin r→ℕ) (pr : ∀i,(p i).Prime) (odd : ∀i,Odd (p i))
    (inj : p.Injective) (ep : ∀i,0<e i) (longest : ∃i,e i+1=L) (cap : ∀i,e i+1≤L)
    (eqn : OeisA245212.a (2^k*total p e)=(σ 1 (2^k*total p e):ℤ)) :
    (256≤k → L≤lengthCap r) ∧ k≤kCap r := by
  have H (large : 256≤k) : L≤lengthCap r :=
    high (⟨p,e,k,L,pr,ep,by omega,longest,cap,inj⟩ : Family r) odd large eqn
  refine ⟨H,?_⟩
  by_cases large : 256≤k
  · have limit:=H large
    have b:=OMA.FixedRankHeight245212.original k L p e pr odd inj ep longest cap eqn
    have mono : polynomial r L≤polynomial r (lengthCap r):=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ limit) _)
    exact Nat.lt_two_pow_self.le.trans (b.trans (mono.trans (Nat.le_add_left _ _)))
  · exact (le_of_lt (lt_of_not_ge large)).trans (Nat.le_add_right _ _)

end
end OMA.FixedModeClose245212

end

section

/- Prefix identities with any physical dyadic order k. The numerical
state used to label local odd moments is independent of this k. -/
namespace OMA.FixedModeAnyProduct245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.FixedRankGap245212
open OMA.FixedModeProduct245212 (exactSet dropped mult others partition)
open OMA.TwoTallLocal245212 OMA.ThreeMovingLocal245212
open OMA.ThreeMovingOriginal245212 (F G)
open scoped ArithmeticFunction.sigma Function
open OMA.ComplementaryLocal245212 (binary)
open OMA.FixedRankHeight245212 (identities)
variable {r : ℕ}
def pref (k : ℕ) (c : Family r) (b : Fin r→Option Bool) := 2^k*∏i∈exactSet b,c.p i^c.e i

theorem prefix_moments (k : ℕ) (c : Family r) (odd : ∀i,Odd (c.p i)) (b : Fin r→Option Bool) :
    W (pref k c b)=F k*(∏i∈exactSet b,W (c.p i^c.e i)) ∧
    σ 1 (pref k c b)=G k*(∏i∈exactSet b,σ 1 (c.p i^c.e i)) ∧
    2*(pref k c b)*(σ 0 (pref k c b))=(F k+G k)*(∏i∈exactSet b,((c.e i+1)*c.p i^c.e i)) := by
  let s:=exactSet b
  let a i:=c.p i^c.e i
  have cop : (2^k).Coprime (∏i∈s,a i):=Nat.coprime_prod_right_iff.mpr (fun i _=>
    ((Nat.coprime_two_left.mpr (odd i)).pow_left _).pow_right _)
  have pw : (s:Set (Fin r)).Pairwise (Nat.Coprime on a):=fun i _ j _ ij=>
    (((Nat.coprime_primes (c.prime i) (c.prime j)).mpr (c.inj.ne ij)).pow_left _).pow_right _
  have Wp:=IsMultiplicative.map_prod a w_mult s pw
  have Sp:=IsMultiplicative.map_prod a (isMultiplicative_sigma (k:=1)) s pw
  have Tp:=IsMultiplicative.map_prod a (isMultiplicative_sigma (k:=0)) s pw
  have gf : σ 1 (2^k)=G k := by
    dsimp [G];zify [Nat.cast_sub (show 1≤2^(k+1) from Nat.two_pow_pos _)]
    exact (OMA.ComplementaryLocal245212.binary k).1
  have ff : W (2^k)=F k := by exact_mod_cast (OMA.ComplementaryLocal245212.binary k).2
  change W (2^k*∏i∈s,a i)=_ ∧ σ 1 (2^k*∏i∈s,a i)=_ ∧ 2*(2^k*∏i∈s,a i)*σ 0 (2^k*∏i∈s,a i)=_
  rw [w_mult.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
    isMultiplicative_sigma.map_mul_of_coprime cop,ff,gf,Wp,Sp,Tp]
  refine ⟨rfl,rfl,?_⟩
  simp only [a,sigma_zero_apply_prime_pow (c.prime _),sigma_zero_apply_prime_pow Nat.prime_two,
    (OMA.FixedRankHeight245212.identities k).2.1,pow_succ 2,prod_mul_distrib,s]
  ring

theorem equation (k : ℕ) (c : Family r) (odd : ∀i,Odd (c.p i)) {b : Fin r→Option Bool} {v : Fin r}
    (keep : b v=some true) (only : ∀i,i≠v → b i≠some true)
    (hit : (F k+G k)*dust c b=F k*NX c b+G k*NY c b) :
    let H:=2*(pref k c b)*σ 0 (pref k c b)
    let B:=c.e v+1; let C:=mult c b; let q:=c.p v; let u:=q-1
    H*B*C*u^2=q*(W (pref k c b)*C*(B*u-1)+σ 1 (pref k c b)*u) := by
  obtain ⟨av,sv,hv⟩:=prefix_moments k c odd b
  obtain ⟨d,x,y⟩:=others c keep only
  dsimp only
  rw [av,sv,hv]
  unfold dust NX NY at hit
  rw [←prod_erase_mul _ _ (mem_univ v),←prod_erase_mul _ (fun i=>Nx _ _ _) (mem_univ v),
    ←prod_erase_mul _ (fun i=>Ny _ _ _) (mem_univ v)] at hit
  rw [d,x,y,keep] at hit
  simp only [Dn,Nx,Ny,den,xn,yn,if_true] at hit
  linear_combination hit

end OMA.FixedModeAnyProduct245212

end

section

/- Strictness, without a restriction on the physical power of two. -/
namespace OMA.FixedModeAnySign245212
open Finset Nat ArithmeticFunction OMA.Smooth245212 OMA.FixedRankGap245212 OMA.FixedModeRestore245212
open OMA.FixedModeProduct245212 (exactSet dropped mult others partition)
open OMA.FixedModeSign245212 (drop_sign)
open OMA.FixedModeAnyProduct245212 OMA.TwoTallLocal245212
open OMA.ThreeMovingOriginal245212 (F G)
open scoped ArithmeticFunction.sigma
theorem side {r : ℕ} (k : ℕ) (c : Family r) (odd : ∀i,Odd (c.p i)) {b : Fin r→Option Bool} {v : Fin r}
    (keep : b v=some true) (only : ∀i,i≠v → b i≠some true)
    (weak : (F k:ℚ)*ox c b ∅ v≤(G k:ℚ)*((c.p v:ℚ)-1)*oy c b ∅ v)
    (hit : (F k+G k)*dust c b=F k*NX c b+G k*NY c b)
    (actual : score (F k) (G k) (exactX c) (exactY c)=(F k+G k:ℕ))
    (original : OeisA245212.a (2^k*total c.p c.e)=(σ 1 (2^k*total c.p c.e):ℤ)) :
    mult c b*W (pref k c b)<(c.p v-1)*σ 1 (pref k c b) := by
  let t:=(univ:Finset (Fin r)).erase v
  let de i:=Dn (c.p i) (c.e i) (b i)
  let D:=∏i∈t,de i
  have pos : (0:ℚ)<D:=by exact_mod_cast prod_pos (fun i _=>Dpos (c.prime i) _ (b i))
  have oxD : ox c b ∅ v*(D:ℚ)=((∏i∈t,Nx (c.p i) (c.e i) (b i)):ℕ) := by
    dsimp only [ox,xx,tag,notMem_empty,if_false,D];push_cast;rw [←prod_mul_distrib]
    exact prod_congr rfl (fun i _=>(moments (c.prime i) (c.e i) (b i)).1)
  have oyD : oy c b ∅ v*(D:ℚ)=((∏i∈t,Ny (c.p i) (c.e i) (b i)):ℕ) := by
    dsimp only [oy,yy,tag,notMem_empty,if_false,D];push_cast;rw [←prod_mul_distrib]
    exact prod_congr rfl (fun i _=>(moments (c.prime i) (c.e i) (b i)).2)
  have ⟨wp,sp,_⟩:=prefix_moments k c odd b
  have ⟨_,x,y⟩:=others c keep only
  change (∏i∈t,_) = _ at x y
  rw [x] at oxD
  rw [y] at oyD
  have left : ((F k:ℚ)*ox c b ∅ v)*D=(mult c b*W (pref k c b):ℕ):=by
    rw [mul_assoc,oxD,wp];push_cast;ring
  have right : ((G k:ℚ)*((c.p v:ℚ)-1)*oy c b ∅ v)*D=((c.p v-1)*σ 1 (pref k c b):ℕ):=by
    rw [mul_assoc,oyD,sp];push_cast [Nat.cast_sub (c.prime v).pos];ring
  by_cases drop : (dropped b).Nonempty
  · have fp : 0<F k:=by dsimp [F];omega
    have sign:=drop_sign c fp keep only drop hit actual
    have z:=mul_lt_mul_of_pos_right sign pos
    rwa [left,right,Nat.cast_lt] at z
  · have emp : dropped b=∅:=not_nonempty_iff_eq_empty.mp drop
    have C : mult c b=1:=by simp [mult,emp]
    rw [C,one_mul]
    have le:=mul_le_mul_of_nonneg_right weak pos.le
    rw [left,right,C,one_mul,Nat.cast_le] at le
    refine lt_of_le_of_ne le ?_
    intro eq
    have part:=(partition keep only).2
    rw [emp,union_empty] at part
    have joined : pref k c b*(c.p v)^c.e v=2^k*total c.p c.e:=by
      dsimp [pref,total];rw [part,mul_assoc,prod_erase_mul _ _ (mem_univ v)]
    have eqn : OeisA245212.a (pref k c b*(c.p v)^c.e v)=(σ 1 (pref k c b*(c.p v)^c.e v):ℤ):=by rwa [joined]
    have cop : (pref k c b).Coprime (c.p v):=by
      dsimp only [pref];apply Nat.Coprime.mul_left
      · exact (Nat.coprime_two_left.mpr (odd v)).pow_left _
      · apply Nat.coprime_prod_left_iff.mpr
        intro i im
        have iv:=ne_of_mem_erase (part ▸ im)
        exact (((Nat.coprime_primes (c.prime i) (c.prime v)).mpr (c.inj.ne iv)).pow_left _)
    have pp : 0<pref k c b:=mul_pos (Nat.two_pow_pos _) (prod_pos (fun i _=>pow_pos (c.prime i).pos _))
    have pn : c.p v≠2:=by have:=(c.prime v).odd_iff.mp (odd v);omega
    have no:=OMA.PrimePowerDiv245212.nonzero pp (c.prime v) pn cop (c.e v) eqn
    apply no
    have ez:=congrArg (fun x:ℕ=>(x:ℤ)) eq
    push_cast [Nat.cast_sub (c.prime v).pos] at ez
    exact sub_eq_zero.mpr ez


end OMA.FixedModeAnySign245212

end

section

/- The exponents in a small-dyadic-order restoration can be compared
without taking roots near the moving largest length L. -/
namespace OMA.FixedModeSmallPower245212
open Nat

private theorem bern (L j : ℕ) :
    (L+1)*(L+1)^j≤(L+1)*L^j+j*(L+1)^j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h:=Nat.mul_le_mul_right L ih
    rw [pow_succ,pow_succ]
    nlinarith only [h,Nat.zero_le (j*(L+1)^j)]

private theorem step (m L : ℕ) (h : m≤L) : (L+1)^m≤(m+1)*L^m := by
  have coeff : L+1+(m+1)*m≤(m+1)*(L+1):=by nlinarith only [Nat.mul_le_mul_left m h]
  have left:=Nat.mul_le_mul_right ((L+1)^m) coeff
  have right:=Nat.mul_le_mul_left (m+1) (bern L m)
  have out : (L+1)*(L+1)^m≤(L+1)*((m+1)*L^m):=by nlinarith only [left,right]
  exact Nat.le_of_mul_le_mul_left out (Nat.succ_pos _)

theorem compare {q L : ℕ} (qp : 1≤q) (le : q≤L) : L^(q-1)≤q^(L-1) := by
  obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le le
  clear le
  induction d with
  | zero => simp
  | succ d ih =>
    have eq : q+(d+1)-1=(q+d-1)+1:=by omega
    rw [eq,pow_succ]
    have s:=step (q-1) (q+d) (by omega)
    rw [Nat.sub_add_cancel qp] at s
    exact s.trans ((Nat.mul_le_mul_left q ih).trans_eq (Nat.mul_comm ..))

theorem slope {L q r b d : ℕ} (q0 : 2≤q) (qL : q≤L) (rL : r≤L)
    (long : b+1=L) (short : 32*(d+1)≤27*q) (big : 16*140^2≤L) :
    32*L^3*r^d<q^b := by
  have up : 32*L^3*r^d≤L^(d+4):=calc
    _ ≤ L*L^3*L^d := Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) (Nat.pow_le_pow_left rL _)
    _ = _ := by rw [pow_add];ring
  apply up.trans_lt
  by_cases large : 64≤q
  · have hp:=Nat.pow_lt_pow_right (by omega : 1<L) (show d+4<q-1 by omega)
    exact hp.trans_le (by simpa only [show L-1=b by omega] using compare (by omega : 1≤q) qL)
  · have tall : 16*((d+4)+1)^2≤L:= (Nat.mul_le_mul_left 16
        (Nat.pow_le_pow_left (by omega : d+4+1≤140) 2)).trans big
    have grow:=OMA.ComplementarySize245212.absorb tall
    apply (pow_lt_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : (2:ℕ)≠0)).mp
    calc
      (L^(d+4))^2=L^(2*(d+4)):=by rw [mul_comm 2 (d+4),pow_mul]
      _ ≤ 2^L:=grow
      _ ≤ q^L:=Nat.pow_le_pow_left q0 _
      _ < q^(b*2):=Nat.pow_lt_pow_right (by omega) (by omega)
      _ = (q^b)^2:=pow_mul ..

end OMA.FixedModeSmallPower245212

end

section

/- At bounded physical dyadic order, small exact dyadic coefficients replace
the dyadic proxy. The auxiliary state's k field need not equal physical k. -/
namespace OMA.FixedModeSmallSetup245212
open Nat Finset ArithmeticFunction OMA.FixedRankGap245212
open OMA.Smooth245212 (total)
open OMA.FixedRankStep245212 (degree)
open OMA.FixedTallScalar245212 (threshold h)
open OMA.ThreeMovingOriginal245212 (F G)
open scoped ArithmeticFunction.sigma
open OMA.FixedRankHeight245212 (identities)

def headroom := (2:ℕ)^270
def limit (r : ℕ) := threshold r 1+headroom+16*140^2

theorem scales {r k : ℕ} (c : Family r) (small : k<256) (large : limit r≤c.L)
    (v : Fin r) (long : c.e v+1=c.L) :
    let x:=c.L^h r
    128≤x ∧ c.L≤x ∧ 2*r*2^r≤x ∧ 8*(F k+G k)≤c.L ∧ F k+G k≤x ∧
      x^(degree r)<c.p v^c.e v := by
  have cutoff : threshold r 1≤c.L:=by dsimp only [limit] at large;omega
  have p0:=OMA.FixedTallScalar245212.scale (k:=0) cutoff (by simp only [one_mul,le_refl] : c.L≤1*c.L)
    (by rw [pow_zero];apply Nat.one_le_iff_ne_zero.mpr;dsimp only [OMA.SingleMovingHeight245212.constant];positivity)
  obtain ⟨big,_,cl,ec,p⟩:=p0
  have cf : 8*(F k+G k)≤c.L := by
    rw [(OMA.FixedRankHeight245212.identities k).2.1]
    have a : k+1≤2^8 := by norm_num;omega
    have b : 2^(k+1)≤2^256:=Nat.pow_le_pow_right (by decide) (by omega)
    have last : headroom≤c.L:=by dsimp only [limit] at large;omega
    apply le_trans _ last
    apply (Nat.mul_le_mul_left 8 (Nat.mul_le_mul a b)).trans
    decide +kernel
  exact ⟨big,cl,ec,cf,(by omega : F k+G k≤c.L).trans cl,p _ _ (c.prime v).two_le long.ge⟩

/-- One may exclude large retained primes using solely a bound on f+g. It is
convenient to rescale by eight so the metadata of the earlier proxy state can
be reused even for dyadic orders zero and one. -/
theorem base_le {r f g : ℕ} (c : Family r) {b : Fin r→Option Bool} (sum : 2≤f+g)
    (size : 8*(f+g)≤c.L) (hit : (f+g)*dust c b=f*NX c b+g*NY c b) :
    ∀i,b i=some true → c.p i≤c.L := by
  let aux : Family r:={c with k:=8*(f+g)-1,kp:=by omega}
  have frac : 8*f+8*g=(aux.k+1)*1:=by dsimp [aux];omega
  have other : (8*f+8*g)*dust aux b=(8*f)*NX aux b+(8*g)*NY aux b:=by
    change (8*f+8*g)*dust c b=(8*f)*NX c b+(8*g)*NY c b
    calc
      _ = 8*((f+g)*dust c b):=by ring
      _ = _:=by rw [hit];ring
  have sz : aux.k+1≤aux.L:=by dsimp [aux];omega
  intro i bit
  have yes:=retained (c:=aux) (f:=8*f) (g:=8*g) (l:=1) frac
    (fun i=>Nat.not_dvd_of_pos_of_lt (by decide) (c.prime i).one_lt) other i bit
  simpa only [max_eq_right sz] using yes

end OMA.FixedModeSmallSetup245212

end

section

/- Force a single retained prime using the uniform gain and slope at odd rank
at least five. These two numeric inequalities are applied separately. -/
namespace OMA.FixedModeSmallForce245212
open Nat Finset OMA.FixedRankGap245212 OMA.FixedModeRestore245212 OMA.MiddleChange245212
variable {r : ℕ}

theorem force (c : Family r) (b : Fin r→Option Bool) {f g : ℕ} (gp : 0<g)
    (fg : g≤f) (big : 16*140^2≤c.L) (v : Fin r) (long : c.e v+1=c.L) (move : b v≠none)
    (small : ∀i,b i=some true → c.p i≤c.L)
    (hit : (f+g)*dust c b=f*NX c b+g*NY c b)
    (actual : score f g (exactX c) (exactY c)=(f+g:ℕ))
    (gain : ∀ (s : Finset (Fin r)) {i}, i≠v → i∉s → b i=some true →
      (g:ℚ)/(32*(c.L:ℚ)^3*(c.p i:ℚ)^c.e i)≤
        val c b f g (insert i s)-val c b f g s)
    (risk : ∀ {i : Fin r}, i≠v →
      (f:ℚ)*ox c b ∅ v < g*((c.p v:ℚ)-1)*oy c b ∅ v →
      32*(c.e i+1)≤27*c.p v) :
    b v=some true ∧ (∀i,i≠v → b i≠some true) ∧
    (f:ℚ)*ox c b ∅ v≤(g:ℚ)*((c.p v:ℚ)-1)*oy c b ∅ v := by
  classical
  let V:=val c b f g
  have endEq : V ∅=V univ:=same c b f g hit actual
  have advance (s : Finset (Fin r)) {i} (iv : i≠v) (fr : i∉s) : V s≤V (insert i s) := by
    cases bi : b i with
    | none=>
      have diff:=change c b f g s fr
      rw [bi,exact_inc] at diff
      exact (sub_eq_zero.mp diff).symm.le
    | some tag=>
      cases tag with
      | true=>exact sub_nonneg.mp ((by positivity : (0:ℚ)≤g/(32*(c.L:ℚ)^3*(c.p i:ℚ)^c.e i)).trans (gain s iv fr bi))
      | false=>
        have bounds:=caps c b s i
        have h:=dropped (f:=f) (g:=g) (c.prime i) (c.positive i) bounds.1 bounds.2.1
        have diff:=change c b f g s fr
        rw [bi] at diff
        change val c b f g s≤val c b f g (insert i s)
        apply sub_nonneg.mp
        rw [diff]
        exact (by positivity : (0:ℚ)≤ f/(2*(c.p i:ℚ))).trans h
  have endBound (s : Finset (Fin r)) (sv : v∈s) : V s≤V univ := by
    have h (t : Finset (Fin r)) : V s≤V (t∪s) := by
      induction t using Finset.induction_on with
      | empty=>simp
      | @insert i t fresh ih=>
        by_cases it : i∈t∪s
        · simpa only [insert_union,insert_eq_of_mem it] using ih
        · have iv : i≠v:=fun h=>it (h ▸ mem_union_right _ sv)
          simpa only [insert_union] using ih.trans (advance (t∪s) iv it)
    have union : (univ:Finset (Fin r))∪s=univ:=Finset.union_eq_left.mpr (subset_univ _)
    simpa only [union] using h univ
  have initial : V {v}≤V ∅:=(endBound _ (mem_singleton_self v)).trans_eq endEq.symm
  have base:=caps c b ∅ v
  have changeV : V {v}-V ∅=inc (c.p v) (c.e v) f g (b v) (ox c b ∅ v) (oy c b ∅ v):=by
    simpa only [insert_empty] using change c b f g ∅ (notMem_empty v)
  have fp : 0<f:=gp.trans_le fg
  have vv : b v=some true := by
    rcases Option.ne_none_iff_exists'.mp move with ⟨flag,fl⟩
    cases flag with
    | true=>exact fl
    | false=>
      have z:=dropped (f:=f) (g:=g) (c.prime v) (c.positive v) base.1 base.2.1
      rw [fl] at changeV
      have nz : 0<(f:ℚ)/(2*c.p v):=by have:=(c.prime v).pos;positivity
      linarith only [changeV,initial,z,nz]
  rw [vv] at changeV
  have p2 : (1:ℚ)<c.p v:=by exact_mod_cast (c.prime v).one_lt
  have den : 0<((c.e v:ℚ)+1)*((c.p v:ℚ)-1)^2*(c.p v:ℚ)^c.e v:=by positivity
  have formula:=retained (f:=f) (g:=g) (e:=c.e v) (c.prime v) (ox c b ∅ v) (oy c b ∅ v)
  have gap : (f:ℚ)*ox c b ∅ v≤g*((c.p v:ℚ)-1)*oy c b ∅ v:=by
    have low:=sub_nonpos.mpr initial
    rw [changeV,formula] at low
    exact sub_nonpos.mp (by simpa only [zero_mul] using (div_le_iff₀ den).mp low)
  refine ⟨vv,?_,gap⟩
  intro i iv keep
  have fr : i∉({v}:Finset (Fin r)):=by simpa
  have perk:=gain {v} iv fr keep
  have up:=(endBound (insert i {v}) (mem_insert_of_mem (mem_singleton_self v))).trans_eq endEq.symm
  have gl : 0<(g:ℚ)/(32*(c.L:ℚ)^3*(c.p i:ℚ)^c.e i):=by
    have lp : 0<c.L:=by omega
    have pi:=(c.prime i).pos
    positivity
  have loss : V {v}-V ∅<0:=by linarith only [perk,up,gl]
  have neg : (f:ℚ)*ox c b ∅ v<g*((c.p v:ℚ)-1)*oy c b ∅ v:=by
    rw [changeV,formula] at loss
    exact sub_neg.mp (by simpa only [zero_mul] using (div_lt_iff₀ den).mp loss)
  have slope:=risk iv neg
  have powers:=OMA.FixedModeSmallPower245212.slope (c.prime v).two_le (small v vv) (small i keep) long slope big
  have powerq : (32:ℚ)*(c.L:ℚ)^3*(c.p i:ℚ)^c.e i < (c.p v:ℚ)^c.e v:=by exact_mod_cast powers
  have cost:=retained_loss (f:=f) (g:=g) (e:=c.e v) (c.prime v) (zero_le_one.trans base.1) base.2.2
  have comp : (g:ℚ)/(c.p v:ℚ)^c.e v < g/(32*(c.L:ℚ)^3*(c.p i:ℚ)^c.e i):=by
    apply div_lt_div_of_pos_left (by positivity) _ powerq
    have lp : 0<c.L:=by omega
    have pi:=(c.prime i).pos
    positivity
  rw [←changeV] at cost
  let P:ℚ:=g/(c.p v:ℚ)^c.e v
  let Q:ℚ:=g/(32*(c.L:ℚ)^3*(c.p i:ℚ)^c.e i)
  have d : -P≤V {v}-V ∅:=by simpa only [P,neg_div] using cost
  change P<Q at comp
  change Q≤V (insert i {v})-V {v} at perk
  linarith only [d,comp,perk,up]

end OMA.FixedModeSmallForce245212

end

section

/- Arithmetic conclusion for bounded physical k and large rank, using
only the two local strength estimates for a family with at least five slots. -/
namespace OMA.FixedModeShortArithmetic245212
open Nat Finset ArithmeticFunction OMA.FixedRankGap245212 OMA.FixedModeRestore245212
open OMA.FixedModeProduct245212 (dropped exactSet mult)
open OMA.FixedModeAnyProduct245212
open OMA.ThreeMovingOriginal245212 (F G)
open OMA.Smooth245212 (total W)
open scoped ArithmeticFunction.sigma
open OMA.FixedRankHeight245212 (identities)

def fixedExp (r : ℕ) := 1+OMA.FixedModeOriginal245212.exponent r*r

theorem weights (k : ℕ) : 0<G k ∧ G k≤F k := by
  refine ⟨(OMA.FixedRankHeight245212.identities k).1,?_⟩
  cases k with
  | zero=>decide
  | succ k=>
    rw [(OMA.FixedRankHeight245212.identities (k+1)).2.2]
    exact (Nat.le_mul_of_pos_left _ (Nat.succ_pos k)).trans (Nat.le_add_right _ _)

theorem rank_pref {r} (k : ℕ) (c : Family r) (b : Fin r→Option Bool) :
    (pref k c b).primeFactors.card≤r+1 := by
  let s:=(univ : Finset (Fin r)).image c.p
  have cover : (pref k c b).primeFactors⊆insert 2 s:=by
    intro z zm
    have pr:=prime_of_mem_primeFactors zm
    have dv:=dvd_of_mem_primeFactors zm
    obtain two|prod:=pr.dvd_mul.mp dv
    · have same:=(Nat.prime_dvd_prime_iff_eq pr Nat.prime_two).mp (pr.dvd_of_dvd_pow two)
      exact mem_insert.mpr (Or.inl same)
    · obtain ⟨i,_,di⟩:=(pr.prime.dvd_finsetProd_iff _).mp prod
      have :=(Nat.prime_dvd_prime_iff_eq pr (c.prime i)).mp (pr.dvd_of_dvd_pow di)
      exact mem_insert_of_mem (mem_image.mpr ⟨i,mem_univ _,this.symm⟩)
  have card : s.card=r:=by dsimp [s];rw [card_image_of_injective _ c.inj];simp
  exact (card_le_card cover).trans ((card_insert_le _ _).trans_eq (by rw [card]))

theorem small {r k} (c : Family r) (b : Fin r→Option Bool) {Q : ℕ}
    (two : 2^k≤c.L) (Qcap : Q≤c.L^OMA.FixedModeOriginal245212.exponent r)
    (rule : ∀i,b i=if c.p i^c.e i≤Q then none else some (decide (c.p i≤Q))) :
    pref k c b≤(c.L+1)^fixedExp r := by
  let D:=OMA.FixedModeOriginal245212.exponent r
  let t:=c.L+1
  have two : 2^k≤t^1:=by simpa only [pow_one] using two.trans (Nat.le_succ _)
  have per i (mem:i∈exactSet b) : c.p i^c.e i≤t^D:=by
    have none:=(mem_filter.mp mem).2
    rw [rule] at none
    have v : c.p i^c.e i≤Q:=by split at none <;> simp_all
    exact (v.trans Qcap).trans (Nat.pow_le_pow_left (Nat.le_succ _) _)
  have ec : (exactSet b).card≤r:=by simpa using card_le_card (subset_univ (exactSet b))
  have powers : (∏i∈exactSet b,c.p i^c.e i)≤t^(D*r):=by
    calc
      _ ≤ ∏_i∈exactSet b,t^D:=prod_le_prod' per
      _ = t^(D*(exactSet b).card):=by simp [←pow_mul]
      _ ≤ _:=Nat.pow_le_pow_right (by dsimp [t];omega) (Nat.mul_le_mul_left _ ec)
  rw [fixedExp,pow_add]
  exact Nat.mul_le_mul two powers

theorem bounded {r k} (c : Family r) (smallK : k<256)
    (odd : ∀i,Odd (c.p i)) (large : OMA.FixedModeSmallSetup245212.limit r≤c.L)
    (v : Fin r) (long : c.e v+1=c.L)
    (eqn : OeisA245212.a (2^k*total c.p c.e)=(σ 1 (2^k*total c.p c.e):ℤ))
    (localGain : ∀ (b : Fin r→Option Bool), (∀j,b j=some true → c.p j≤c.L) →
      ∀ (s : Finset (Fin r)) {i}, i≠v → i∉s → b i=some true →
        (G k:ℚ)/(32*(c.L:ℚ)^3*(c.p i:ℚ)^c.e i)≤
        val c b (F k) (G k) (insert i s)-val c b (F k) (G k) s)
    (localRisk : ∀ (b : Fin r→Option Bool) {i : Fin r}, i≠v →
      (F k:ℚ)*ox c b ∅ v<(G k:ℚ)*((c.p v:ℚ)-1)*oy c b ∅ v →
      32*(c.e i+1)≤27*c.p v) :
    c.L≤OMA.ArbitraryMixedFinite245212.cutoff (r+1) (fixedExp r) := by
  let x:=c.L^OMA.FixedTallScalar245212.h r
  obtain ⟨big,cl,rate,f8,coef,power⟩:=OMA.FixedModeSmallSetup245212.scales c smallK large v long
  have actual:=OMA.FixedRankHeight245212.physical c k odd c.inj eqn
  obtain ⟨b,Q,xQ,Qcap,rule,hit⟩:=OMA.FixedModeWitness245212.witness c (F k) (G k) x big coef cl rate actual
  have id:=OMA.FixedRankHeight245212.identities k
  have fg := (weights k).2
  have sum : 2≤F k+G k:=by omega
  have kept:=OMA.FixedModeSmallSetup245212.base_le c sum f8 hit
  have mv : b v≠none:=by rw [rule];simp [(Qcap.trans_lt power).not_ge]
  have tall : 16*140^2≤c.L:=by dsimp only [OMA.FixedModeSmallSetup245212.limit] at large;omega
  obtain ⟨keep,only,weak⟩:=OMA.FixedModeSmallForce245212.force c b id.1 fg tall v long mv kept hit actual
    (localGain b kept) (localRisk b)
  have hp : 0<pref k c b:=mul_pos (Nat.two_pow_pos _) (prod_pos (fun i _=>pow_pos (c.prime i).pos _))
  have cp : 0 < mult c b:=prod_pos (fun _ _=>Nat.succ_pos _)
  have two : 2^k≤c.L:=by
    have pow:=Nat.pow_le_pow_right (by decide : 0<2) (show k≤k+1 by omega)
    have mul : 2^(k+1)≤F k+G k:=by rw [id.2.1];exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    exact pow.trans (mul.trans (by omega))
  have qsmall : Q≤c.L^OMA.FixedModeOriginal245212.exponent r:=by simpa only [x,OMA.FixedModeOriginal245212.exponent,pow_mul] using Qcap
  apply OMA.ArbitraryMixedFinite245212.bounded hp (rank_pref k c b) (c.prime v).two_le (by omega) cp
    (small c b two qsmall rule) (OMA.FixedModeAnySign245212.side k c odd keep only weak hit actual eqn)
  simpa only [long] using equation k c odd keep only hit

end OMA.FixedModeShortArithmetic245212

end

section

/- With at least five odd factors the other ordinary moments make
every restoration away from the longest coordinate profitable, even at k=0. -/
namespace OMA.FixedModeSmallGain245212
open Nat Finset OMA.FixedRankGap245212 OMA.FixedModeRestore245212 OMA.MiddleChange245212
open OMA.TwoTallLocal245212
open OMA.Smooth245212 (Y)
open OMA.ThreeMovingLocal245212 (den)
open OMA.ThreeMovingLocal245212 (quotients)
variable {r : ℕ}

private theorem localY {p e : ℕ} (hp : p.Prime) (he : 0<e) (odd : Odd p) (mode : Option Bool) :
    yy' p e mode≤3/4 := by
  have pt:=hp.two_le
  obtain ⟨j,hj⟩:=odd
  have pr : (3:ℚ)≤p:=by exact_mod_cast (show 3≤p by omega)
  have ep : (1:ℚ)≤e:=by exact_mod_cast he
  have B : (0:ℚ)<(e:ℚ)+1:=by positivity
  have u : (0:ℚ)<(p:ℚ)-1:=by linarith
  have yn : ThreeMovingLocal245212.yy p e true = (p:ℚ)/(((e:ℚ)+1)*(p-1)) := by
    dsimp [ThreeMovingLocal245212.yy,OMA.ThreeMovingLocal245212.yn,den]
    push_cast [Nat.cast_sub hp.one_le];field_simp
  have yb : ThreeMovingLocal245212.yy p e true≤3/4 := by
    rw [yn,div_le_iff₀ (mul_pos B u)]
    nlinarith only [pr,mul_nonneg (sub_nonneg.mpr ep) u.le]
  rcases mode with _|b
  · have q:=(OMA.ThreeMovingLocal245212.quotients (e:=e) hp).2
    change Y p (some e)≤3/4
    have pw : 0<(p:ℚ)^e := by positivity
    have dn : 0≤1/(((e:ℚ)+1)*((p:ℚ)-1)^2*(p:ℚ)^e):=by positivity
    linarith only [q,mul_nonneg u.le dn,yb]
  · cases b
    · change ThreeMovingLocal245212.yy p e false≤_
      simp [ThreeMovingLocal245212.yy,OMA.ThreeMovingLocal245212.yn,den]
      rw [←one_div];apply (div_le_iff₀ B).mpr;linarith only [ep]
    · exact yb

theorem other_short (c : Family r) (odd : ∀i,Odd (c.p i)) (many : 5≤r)
    (b : Fin r→Option Bool) (s : Finset (Fin r)) {i z : Fin r} (ne : z≠i) :
    oy c b s i*((c.e z:ℚ)+1)≤27/32 := by
  let t:=(univ:Finset (Fin r)).erase i
  have zm : z∈t:=mem_erase.mpr ⟨ne,mem_univ _⟩
  have card : 3≤(t.erase z).card:=by
    rw [card_erase_of_mem zm];dsimp [t];rw [card_erase_of_mem (mem_univ _)]
    have count : (univ : Finset (Fin r)).card=r:=by simp
    rw [count];omega
  have nn (j) : 0≤FixedModeRestore245212.yy c b s j := (ranges (c.prime j) (c.positive j) (tag b s j)).2.2.1
  have rest : ∏j∈t.erase z,FixedModeRestore245212.yy c b s j≤27/64:=calc
    _ ≤ ∏ _j∈t.erase z,(3/4:ℚ) := prod_le_prod (fun j _=>nn j)
      (fun j _=>localY (c.prime j) (c.positive j) (odd j) (tag b s j))
    _ = (3/4:ℚ)^(t.erase z).card := by rw [prod_const]
    _ ≤ (3/4:ℚ)^3 := pow_le_pow_of_le_one (by norm_num) (by norm_num) card
    _ = _ := by norm_num
  have ex := (le_div_iff₀ (by positivity)).mp (ranges (c.prime z) (c.positive z) (tag b s z)).2.2.2
  change FixedModeRestore245212.yy c b s z*((c.e z:ℚ)+1)≤2 at ex
  change (∏j∈t,FixedModeRestore245212.yy c b s j)*_≤_
  rw [←prod_erase_mul t _ zm,mul_assoc]
  exact (mul_le_mul rest ex (mul_nonneg (nn z) (by positivity)) (by norm_num)).trans_eq (by norm_num)

theorem gain (c : Family r) (odd : ∀i,Odd (c.p i)) (many : 5≤r)
    (b : Fin r→Option Bool) {f g : ℕ} (fg : g≤f) (v : Fin r) (long : c.e v+1=c.L)
    (small : ∀i,b i=some true → c.p i≤c.L) (s : Finset (Fin r)) {i : Fin r}
    (iv : i≠v) (fr : i∉s) (keep : b i=some true) :
    (g:ℚ)/(32*(c.L:ℚ)^3*(c.p i:ℚ)^c.e i) ≤ val c b f g (insert i s)-val c b f g s := by
  have pp : (1:ℚ)<c.p i:=by exact_mod_cast (c.prime i).one_lt
  have base : (c.p i:ℚ)≤c.L:=by exact_mod_cast small i keep
  have lp : (0:ℚ)<c.L:=by linarith
  have el : (c.e i:ℚ)+1≤c.L:=by exact_mod_cast c.cap i
  have eqL : (c.e v:ℚ)+1=c.L:=by exact_mod_cast long
  have ey:=other_short c odd many b s iv.symm
  rw [eqL] at ey
  have bounds:=caps c b s i
  let u:ℚ:=(c.p i:ℚ)-1
  have up : 0<u:=by dsimp [u];linarith
  have ub : u≤c.L:=by dsimp [u];linarith
  have y : u*oy c b s i≤27/32:=by
    rw [mul_comm];exact (mul_le_mul_of_nonneg_left ub bounds.2.1).trans ey
  have gf : (g:ℚ)≤f:=by exact_mod_cast fg
  have num : (g:ℚ)/32≤f*ox c b s i-g*u*oy c b s i:=by
    nlinarith only [mul_le_mul_of_nonneg_left y (Nat.cast_nonneg (α:=ℚ) g),
      mul_le_mul_of_nonneg_left bounds.1 (Nat.cast_nonneg (α:=ℚ) f),gf,Nat.cast_nonneg (α:=ℚ) g]
  have den : ((c.e i:ℚ)+1)*u^2 ≤(c.L:ℚ)^3:=by
    calc
      _ ≤ (c.L:ℚ)*(c.L:ℚ)^2:=mul_le_mul el (pow_le_pow_left₀ up.le ub _) (sq_nonneg _) lp.le
      _ = _ := by ring
  rw [change c b f g s fr,keep,retained (c.prime i)]
  change _≤(_-g*u*_)/(((c.e i:ℚ)+1)*u^2*(c.p i:ℚ)^c.e i)
  calc
    _ = ((g:ℚ)/32)/((c.L:ℚ)^3*(c.p i:ℚ)^c.e i) := by ring
    _ ≤ _ := (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_right den (by positivity))).trans (div_le_div_of_nonneg_right num (by positivity))

theorem risk (c : Family r) (odd : ∀i,Odd (c.p i)) (many : 5≤r)
    (b : Fin r→Option Bool) {f g : ℕ} (gp : 0<g) (fg : g≤f) (v : Fin r) {i : Fin r}
    (iv : i≠v) (neg : (f:ℚ)*ox c b ∅ v < g*((c.p v:ℚ)-1)*oy c b ∅ v) :
    32*(c.e i+1)≤27*c.p v := by
  have p2 : (1:ℚ)<c.p v:=by exact_mod_cast (c.prime v).one_lt
  have ey:=other_short c odd many b ∅ iv
  have gf : (g:ℚ)≤f:=by exact_mod_cast fg
  have x:=mul_le_mul_of_nonneg_left (caps c b ∅ v).1 (Nat.cast_nonneg (α:=ℚ) f)
  have one : (1:ℚ)<((c.p v:ℚ)-1)*oy c b ∅ v:=by
    apply lt_of_mul_lt_mul_left (a:=(g:ℚ)) _ (by positivity)
    linarith only [gf,x,neg,mul_assoc (g:ℚ) ((c.p v:ℚ)-1) (oy c b ∅ v)]
  exact_mod_cast (show 32*((c.e i:ℚ)+1)≤27*(c.p v:ℚ) by
    nlinarith only [mul_lt_mul_of_pos_right one (by positivity : (0:ℚ)<(c.e i:ℚ)+1),
      mul_le_mul_of_nonneg_left ey (show 0≤(c.p v:ℚ)-1 by linarith),p2])

end OMA.FixedModeSmallGain245212

end

section

/- Every fixed positive number of distinct odd prime divisors gives only
finitely many possible solutions to the original divisor balance. -/
namespace OMA.FixedRankAbsolute245212
open Nat Finset ArithmeticFunction OMA.FixedRankGap245212 OMA.FixedRankInteger245212
open OMA.Smooth245212 (total)
open OMA.ThreeMovingOriginal245212 (F G)
open scoped ArithmeticFunction.sigma Function

noncomputable section

def lengthCap (r : ℕ) := OMA.FixedModeClose245212.lengthCap r +
  OMA.FixedModeSmallSetup245212.limit r +
  OMA.ArbitraryMixedFinite245212.cutoff (r+1) (OMA.FixedModeShortArithmetic245212.fixedExp r)

theorem lengths {r k L : ℕ} (many : 5≤r) (p e : Fin r→ℕ)
    (pr : ∀i,(p i).Prime) (odd : ∀i,Odd (p i)) (inj : p.Injective)
    (ep : ∀i,0<e i) (longest : ∃i,e i+1=L) (cap : ∀i,e i+1≤L)
    (eqn : OeisA245212.a (2^k*total p e)=(σ 1 (2^k*total p e):ℤ)) :
    L≤lengthCap r := by
  by_cases hi : 256≤k
  · have bound:=(OMA.FixedModeClose245212.orderBound p e pr odd inj ep longest cap eqn).1 hi
    dsimp only [lengthCap];omega
  by_cases big : OMA.FixedModeSmallSetup245212.limit r≤L
  · let c : Family r:=⟨p,e,8,L,pr,ep,by decide,longest,cap,inj⟩
    obtain ⟨v,vl⟩:=longest
    obtain ⟨gp,fg⟩:=OMA.FixedModeShortArithmetic245212.weights k
    have bound:=OMA.FixedModeShortArithmetic245212.bounded c (lt_of_not_ge hi) odd big v vl eqn
      (fun b small s _ iv fr bi=>OMA.FixedModeSmallGain245212.gain c odd many b fg v vl small s iv fr bi)
      (fun b _ iv neg=>OMA.FixedModeSmallGain245212.risk c odd many b gp fg v iv neg)
    change L≤_ at bound
    dsimp only [lengthCap];omega
  · dsimp only [lengthCap];omega

end
end OMA.FixedRankAbsolute245212

end

section

/- Convert the positive-coefficient gap expansion and mode separation to
a primitive recursive integer cap on the odd divisor count. -/
open Nat Finset ArithmeticFunction Polynomial
open OMA.Smooth245212 (total)
open scoped ArithmeticFunction.sigma

private theorem degree_eval (P : Polynomial ℕ) : P.natDegree≤P.eval 2 := by
  by_cases z : P=0
  · simp [z]
  have mem:=P.natDegree_mem_support_of_nonzero z
  have pos : 0<P.coeff P.natDegree:=Nat.pos_of_ne_zero (Polynomial.mem_support_iff.mp mem)
  rw [eval_eq_sum]
  change P.natDegree≤∑i∈P.support,P.coeff i*2^i
  exact Nat.lt_two_pow_self.le.trans ((Nat.le_mul_of_pos_left (2^P.natDegree) pos).trans
    (single_le_sum (f:=fun i=>P.coeff i*2^i) (fun _ _=>Nat.zero_le _) mem))

private theorem cost_rec (i A : ℕ) :
    Nat.rec (motive:=fun _=>ℕ→ℕ) (fun _=>1) (fun _ f u=>2*(u+1)*f (2*(u+1)^2)) i A =
    OMA.PositiveProductGap245212.cost i A := by
  induction i generalizing A with
  | zero=>rfl
  | succ i ih=>simp only [OMA.PositiveProductGap245212.cost,ih]

private theorem dir_count {k m : ℕ} (odd : Odd m) (big : 1 < m)
    (regime : 5 ≤ m.primeFactors.card ∨ 256≤k)
    (eqn : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) :
    m.divisors.card≤(OMA.FixedRankAbsolute245212.lengthCap m.primeFactors.card)^m.primeFactors.card := by
  classical
  let s:=m.primeFactors
  let P : Fin s.card ↪o ℕ:=s.orderEmbOfFin rfl
  let e (i : Fin s.card):=m.factorization (P i)
  let L:=s.sup (fun p=>m.factorization p+1)
  have mem (i : Fin s.card) : P i∈s:=s.orderEmbOfFin_mem rfl i
  have pr i := Nat.prime_of_mem_primeFactors (mem i)
  have op i : Odd (P i) := (pr i).odd_of_ne_two (fun h=>(Nat.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr (h ▸ Nat.dvd_of_mem_primeFactors (mem i))))
  have ep i : 0<e i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (mem i))
  have lift : univ.map P.toEmbedding=s:=s.map_orderEmbOfFin_univ rfl
  have fac : (∏ q∈s,q^(m.factorization q))=m:=(Nat.prod_primeFactors_pow_factorization odd.pos.ne').symm
  rw [←lift,prod_map] at fac
  change total P e=m at fac
  have nonempty : s.Nonempty:=Nat.nonempty_primeFactors.mpr big
  obtain ⟨z,zm,zt⟩:=Finset.exists_mem_eq_sup s nonempty (fun q=>m.factorization q+1)
  obtain ⟨i,_,zi⟩:=Finset.mem_map.mp (lift.symm ▸ zm)
  change P i=z at zi
  have hit : ∃ j,e j+1=L:=⟨i,by change m.factorization (P i)+1=L;rw [zi];exact zt.symm⟩
  have cap i : e i+1≤L := Finset.le_sup (f:=fun q=>m.factorization q+1) (mem i)
  have actual : OeisA245212.a (2^k*total P e)=(σ 1 (2^k*total P e):ℤ):=by rwa [fac]
  have len : L≤OMA.FixedRankAbsolute245212.lengthCap s.card := by
    rcases regime with many|hi
    · exact OMA.FixedRankAbsolute245212.lengths many P e pr op P.injective ep hit cap actual
    · have a:=(OMA.FixedModeClose245212.orderBound P e pr op P.injective ep hit cap actual).1 hi
      exact a.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  rw [Nat.card_divisors odd.pos.ne']
  calc
    _ ≤ ∏_q∈s,OMA.FixedRankAbsolute245212.lengthCap s.card :=
      prod_le_prod' (fun q qm=>(Finset.le_sup (f:=fun t=>m.factorization t+1) qm).trans len)
    _ = _ := by simp [s]

theorem OMA.solution : OMA.R_OeisA245212_conjecture_R2_H2_R1.H1 := by
  unfold OMA.R_OeisA245212_conjecture_R2_H2_R1.H1
  intro cost fixed envelope poly cut length k m odd big regime eqn
  have fx (j x : ℕ) : fixed j x=OMA.WeightedUniformGap245212.constant j x := by
    induction j generalizing x with
    | zero=>rfl
    | succ j ih=>
      let B:=2*fixed j x*x*2^j+2
      change 2*fixed j x+(x^(j+1)*(B^2)^(j+1))*cost (j+1) (x*(B*(x*B)+1)^(j+1))=_
      have co : cost (j+1)=OMA.PositiveProductGap245212.cost (j+1):=funext (cost_rec (j+1))
      simp only [B,ih,co,OMA.WeightedUniformGap245212.constant,OMA.WeightedUniformGap245212.cutoff,
        OMA.WeightedUpperGap245212.boundedCost]
  have env (j x : ℕ) : (OMA.WeightedGapPolynomial245212.envelope j).eval x=envelope j x := by
    simp [envelope,OMA.WeightedGapPolynomial245212.envelope,eval_finsetSum,
      OMA.WeightedGapPolynomial245212.evaluate_fixed,fx]
  have form (j x : ℕ) : (OMA.ArbitraryMixedGap245212.poly j).eval x=poly j x := by
    simp [poly,OMA.ArbitraryMixedGap245212.poly,eval_comp,env]
  have cutBig (j D : ℕ) : OMA.ArbitraryMixedFinite245212.cutoff j D≤cut j D := by
    let P:=OMA.ArbitraryMixedGap245212.poly j
    let a:=P.eval 1+1
    have de : P.natDegree≤poly j 2 := (degree_eval P).trans_eq (form j 2)
    have ao : a=poly j 1+1:=congrArg (·+1) (form j 1)
    change a*(16*(P.natDegree*D+1)^2+2*(a*D)+6)^P.natDegree≤_
    dsimp only [cut]
    rw [←ao]
    apply Nat.mul_le_mul_left
    exact (Nat.pow_le_pow_left (by gcongr) _).trans
      (Nat.pow_le_pow_right (by positivity) de)
  have lengths (r : ℕ) : OMA.FixedRankAbsolute245212.lengthCap r≤length r := by
    have one:=cutBig (r+1) (OMA.FixedModeArithmetic245212.exponent r)
    have two:=cutBig (r+1) (OMA.FixedModeShortArithmetic245212.fixedExp r)
    exact Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add_left one _) _) two
  exact (dir_count odd big regime eqn).trans (Nat.pow_le_pow_left (lengths _) _)

end
