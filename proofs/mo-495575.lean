import OMAStatements.S_mo_495575
namespace OMA.S_mo_495575
open Finset
/-- The two positive fractions with denominator offset c=0 and c=1. -/
def piece (k m c : ℕ) : ℚ := 1/((m:ℚ)*((k+c-m:ℕ):ℚ)^m)
def magnitude (k m : ℕ) : ℚ := piece k m 0 + piece k m 1
def partialSum (k t : ℕ) : ℚ := ∑ i ∈ range t,(-1:ℚ)^i*magnitude k (i+2)
private lemma reciprocal_mid (a b c : ℚ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hh : a*c ≤ b^2) :
    2/b ≤ 1/a+1/c := by
  have hsq : (1/b)^2 ≤ 1/a*(1/c) := by
    rw [div_pow,div_mul_div_comm,div_le_div_iff₀ (by positivity) (by positivity)]
    norm_num;linarith
  have hpos : 0 ≤ 1/a+1/c := by positivity
  rw [show 2/b=2*(1/b) by ring]
  generalize (1/a:ℚ) = A at hsq hpos ⊢
  generalize (1/b:ℚ) = B at hsq ⊢
  generalize (1/c:ℚ) = C at hsq hpos ⊢
  apply le_of_sq_le_sq _ hpos
  nlinarith only [hsq,sq_nonneg (A-C)]

private lemma middle {m y : ℕ} (hm : 0 < m) (hy : 0 < y) :
    2/(((m:ℚ)+1)*((y:ℚ)+1)^(m+1)) ≤
      1/((m:ℚ)*((y:ℚ)+2)^m) + 1/(((m:ℚ)+2)*(y:ℚ)^(m+2)) := by
  apply reciprocal_mid <;> try positivity
  have h₁ : (m:ℚ)*((m:ℚ)+2) ≤ ((m:ℚ)+1)^2 := by nlinarith
  have h₂ : ((y:ℚ)+2)*(y:ℚ) ≤ ((y:ℚ)+1)^2 := by nlinarith
  calc
    _ = ((m:ℚ)*(m+2))*(((y:ℚ)+2)*y)^m*(y:ℚ)^2 := by rw [mul_pow,pow_add];ring
    _ ≤ ((m:ℚ)+1)^2*(((y:ℚ)+1)^2)^m*((y:ℚ)+1)^2 := by gcongr <;> linarith
    _ = _ := by rw [mul_pow,mul_assoc,←pow_succ,←pow_mul,←pow_mul,Nat.mul_comm 2 (m+1)]

private lemma convex_piece (k m c : ℕ) (hm : 0 < m) (hk : m+2 < k) :
    2*piece k (m+1) c ≤ piece k m c + piece k (m+2) c := by
  let y := k+c-(m+2)
  have hy : 0 < y := by dsimp [y];omega
  have h := middle hm hy
  simpa only [piece,show k+c-m=y+2 by dsimp [y];omega,show k+c-(m+1)=y+1 by dsimp [y];omega,
    Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,mul_div_assoc',mul_one] using h
private lemma convex_mag (k m : ℕ) (hm : 0 < m) (hk : m+2 < k) :
    2*magnitude k (m+1) ≤ magnitude k m+magnitude k (m+2) := by
  dsimp [magnitude]
  linarith only [convex_piece k m 0 hm hk,convex_piece k m 1 hm hk]

private lemma mag_nonneg (k m : ℕ) : 0 ≤ magnitude k m := by unfold magnitude piece;positivity

private lemma partial_succ (k t : ℕ) :
    partialSum k (t+1)=partialSum k t+(-1:ℚ)^t*magnitude k (t+2) := by simp [partialSum,sum_range_succ]

private lemma middle_block (k s : ℕ) (hk : 2*s+4 < k) :
    magnitude k 2 - magnitude k 3 + (magnitude k 4 + magnitude k (2*s+4))/2 ≤ partialSum k (2*s+3) := by
  induction s with
  | zero => norm_num [partialSum,sum_range_succ]
  | succ s ih =>
    have cv := convex_mag k (2*s+4) (by omega) (by omega)
    have hh := ih (by omega)
    rw [show 2*(s+1)+3=(2*s+3+1)+1 by omega,partial_succ,partial_succ k (2*s+3)]
    rw [show (-1:ℚ)^(2*s+3) = -1 by rw [pow_add,pow_mul];norm_num,
      show (-1:ℚ)^(2*s+3+1) = 1 by rw [pow_add,pow_add,pow_mul];norm_num]
    convert_to magnitude k 2-magnitude k 3+(magnitude k 4+magnitude k (2*s+6))/2 ≤
      partialSum k (2*s+3)+(-1)*magnitude k (2*s+5)+1*magnitude k (2*s+6) using 2 <;>
      try congr 2 <;> try omega
    linarith only [cv,hh]
private lemma pow2_big (t : ℕ) : ((t+10:ℕ):ℚ)^2 ≤ (2:ℚ)^(t+9) := by
  induction t with
  | zero => norm_num
  | succ t h =>
    rw [show t+1+9=(t+9)+1 by omega,pow_succ (2:ℚ)]
    push_cast at h ⊢
    nlinarith [Nat.cast_nonneg (α:=ℚ) t,sq_nonneg (t:ℚ)]

private lemma head_gap {k : ℕ} (hk : 10 ≤ k) :
    1/((k:ℚ)*(k-1)) + 1/((k:ℚ)^2*(k-1)) < magnitude k 2-magnitude k 3 := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hk
  simp only [magnitude,piece]
  rw [show 10+t+0-2=t+8 by omega,show 10+t+1-2=t+9 by omega,show 10+t+0-3=t+7 by omega,
    show 10+t+1-3=t+8 by omega]
  push_cast
  have ht : 0 ≤ (t:ℚ) := Nat.cast_nonneg _
  rw [show (10:ℚ)+t-1=t+9 by ring]
  field_simp
  apply sub_pos.mp
  ring_nf
  positivity

private lemma end_terms {k : ℕ} (hk : 10 ≤ k) :
    magnitude k (k-1) = 1/((k:ℚ)-1) + 1/(((k:ℚ)-1)*(2:ℚ)^(k-1)) ∧
    magnitude k (k-2) ≤ 1/((k:ℚ)*(k-1)) ∧
    1/(((k:ℚ)-1)*(2:ℚ)^(k-1)) ≤ 1/((k:ℚ)^2*(k-1)) := by
  have hK : (10:ℚ) ≤ k := by exact_mod_cast hk
  have b0 : 0 < (k:ℚ)-1 := by linarith
  have b1 : 0 < (k:ℚ)-2 := by linarith
  obtain ⟨t,he⟩ := Nat.exists_eq_add_of_le hk
  have h2 : (k:ℚ)^2 ≤ (2:ℚ)^(k-1) := by
    convert pow2_big t using 1 <;> congr 2 <;> omega
  refine ⟨?_,?_,?_⟩
  · simp only [magnitude,piece,show k+0-(k-1)=1 by omega,show k+1-(k-1)=2 by omega,
      Nat.cast_one,Nat.cast_ofNat,one_pow,mul_one,Nat.cast_sub (show 1 ≤ k by omega)]
  · have e : (2:ℚ)^(k-2) ≤ (3:ℚ)^(k-2) := by gcongr <;> norm_num
    have e₂ : (k:ℚ)^2 ≤ 2*(2:ℚ)^(k-2) := by
      rwa [show k-1=(k-2)+1 by omega,pow_succ (2:ℚ),mul_comm ((2:ℚ)^(k-2)) 2] at h2
    simp only [magnitude,piece,show k+0-(k-2)=2 by omega,show k+1-(k-2)=3 by omega,
      Nat.cast_sub (show 2 ≤ k by omega),Nat.cast_ofNat]
    calc
      _ ≤ 1/(((k:ℚ)-2)*(2:ℚ)^(k-2))+1/(((k:ℚ)-2)*(2:ℚ)^(k-2)) := by gcongr
      _ ≤ _ := by
        rw [←two_mul,mul_div_assoc',mul_one,div_le_div_iff₀ (by positivity) (by positivity)]
        have hA : 4*((k:ℚ)-1) ≤ (k:ℚ)*(k-2) := by nlinarith [sq_nonneg ((k:ℚ)-5)]
        nlinarith only [mul_le_mul_of_nonneg_left e₂ b1.le,mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg (α:=ℚ) k)]
  · apply one_div_le_one_div_of_le (by positivity)
    simpa [mul_comm] using mul_le_mul_of_nonneg_left h2 b0.le
private lemma even_combine {A B D E F X P : ℚ} (hD : A-B=D) (hE : E≤F)
    (hF : D+F<X) (hX : X≤P) : -B<P+ -(A+E) := by linarith
private lemma odd_combine {A B D E H P : ℚ} (hD : A-B=D) (hE : 0≤E)
    (hH : H≤D) (hP : 0<P) : B<P+ -H+(A+E) := by linarith

private lemma large {k : ℕ} (hk : 10 ≤ k) : (-1:ℚ)^(k-1)/k < partialSum k (k-2) := by
  let s := (k-6)/2
  have hshape : k=2*s+6 ∨ k=2*s+7 := by dsimp [s];omega
  have pref := middle_block k s (by omega)
  have hp : magnitude k 2-magnitude k 3 ≤ partialSum k (2*s+3) := by
    linarith [mag_nonneg k 4,mag_nonneg k (2*s+4)]
  obtain ⟨hend,hbefore,htiny⟩ := end_terms hk
  have head := head_gap hk
  have hp0 : 0 < (k:ℚ) := by exact_mod_cast (show 0 < k by omega)
  have hK : (10:ℚ) ≤ k := by exact_mod_cast hk
  have hp1 : 0 < (k:ℚ)-1 := by linarith
  have hd : 1/((k:ℚ)-1) - 1/(k:ℚ) = 1/(k*(k-1:ℚ)) := by field_simp;ring
  have neg3 : (-1:ℚ)^(2*s+3) = -1 := by rw [pow_add,pow_mul];norm_num
  have pos4 : (-1:ℚ)^(2*s+4) = 1 := by rw [pow_add,pow_mul];norm_num
  rcases hshape with he|he
  · have hsign : (-1:ℚ)^(k-1) = -1 := by rw [show k-1=2*s+5 by omega,pow_add,pow_mul];norm_num
    rw [show k-2=(2*s+3)+1 by omega,partial_succ,neg3,show 2*s+3+2=k-1 by omega,hend,
      hsign]
    simp only [neg_one_mul]
    rw [neg_div]
    exact even_combine hd htiny head hp
  · have hsign : (-1:ℚ)^(k-1) = 1 := by rw [show k-1=2*s+6 by omega,pow_add,pow_mul];norm_num
    rw [show k-2=(2*s+4)+1 by omega,partial_succ,pos4,
      show 2*s+4+2=k-1 by omega,hend,show 2*s+4=(2*s+3)+1 by omega,partial_succ,neg3,
      show 2*s+3+2=k-2 by omega,hsign]
    simp only [neg_one_mul,one_mul]
    have hn : 0 ≤ 1/((k:ℚ)^2*(k-1)) := by positivity
    have hnt : 0 ≤ 1/(((k:ℚ)-1)*(2:ℚ)^(k-1)) := by positivity
    apply odd_combine hd hnt hbefore
    apply lt_of_lt_of_le _ hp
    apply lt_of_le_of_lt _ head
    positivity

private lemma all_k (k : ℕ) (hk : 4 ≤ k) : (-1:ℚ)^(k-1)/k < partialSum k (k-2) := by
  by_cases h : 10 ≤ k
  · exact large h
  · interval_cases k <;> norm_num [partialSum,magnitude,piece,Finset.sum_range_succ]

private lemma original (k : ℕ) (hk : 4 ≤ k) :
    (-1:ℚ)^(k-1)/k <
      ∑ m ∈ Ico 2 k, ((-1:ℚ)^m/m)*
        (1/((k-m:ℕ):ℚ)^m + 1/((k-m+1:ℕ):ℚ)^m) := by
  apply (all_k k hk).trans_le
  apply le_of_eq
  rw [sum_Ico_eq_sum_range,partialSum]
  apply sum_congr rfl
  intro l hl
  have h := mem_range.mp hl
  have h₂ : 2+l=l+2 := by omega
  rw [h₂,pow_add (-1:ℚ) l 2]
  norm_num only [neg_one_sq,mul_one]
  unfold magnitude piece
  rw [show k+0-(l+2)=k-(l+2) by omega,show k+1-(l+2)=k-(l+2)+1 by omega]
  ring
end OMA.S_mo_495575
open OMA.S_mo_495575
theorem OMA.solution : type_of% @OMA.S_mo_495575.main := original
