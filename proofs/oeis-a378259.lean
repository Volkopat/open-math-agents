import OMAStatements.S_oeis_a378259

-- Credit: @Aryan-Poonacha. The mod-8 strategy was suggested by @wtho704.
namespace S378
open PowerSeries OMA.S_oeis_a378259
noncomputable section
private abbrev red (q : ℕ) := PowerSeries.map (Int.castRingHom (ZMod q))
private lemma red_coeff (q n : ℕ) (B : PowerSeries ℤ) :
    coeff n (red q B) = (↑(coeff n B) : ZMod q) := rfl

private lemma ratio8 (B : PowerSeries ℤ) (b0 : constantCoeff B=0) (b1 : coeff 1 B=1) :
    red 8 (scaledRatio B) = red 8 B - C (4:ZMod 8)*X^2 := by
  ext n
  rw [map_sub, coeff_C_mul,coeff_X_pow,red_coeff,red_coeff]
  simp only [scaledRatio,coeff_mk,Int.cast_sum,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
  rcases n with _|_|_|n
  · simp [coeff_zero_eq_constantCoeff,b0]
  · simp
  · have d : Nat.divisors 2 = {1,2} := by decide
    simp [d,b1,ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 2)]; ring
  · have hne : n+1+1+1 ≠ 2 := by omega
    rw [if_neg hne,mul_zero,sub_zero]
    rw [Finset.sum_eq_single (n+1+1+1)]
    · simp
    · intro d hd hne'
      obtain ⟨j,hj⟩ := Nat.dvd_of_mem_divisors hd
      have dj : 2 ≤ j := by
        by_contra! h; interval_cases j <;> simp_all
      have q : d*2 ≤ n+1+1+1 := hj ▸ Nat.mul_le_mul_left d dj
      have h2 : 2 ≤ n+1+1+1-d := by omega
      rw [show n+1+1+1-d=2+(n+1+1+1-d-2) by omega,pow_add]
      rw [show (4:ZMod 8)^2=0 by decide];simp
    · simp

private lemma square8 (B : PowerSeries ℤ) (b1 : coeff 1 B=1) :
    red 8 (scaledSquareSubstitution B) = X^2 + C (4*(↑(coeff 2 B) : ZMod 8))*X^4 := by
  ext n
  rw [map_add,coeff_C_mul,coeff_X_pow,coeff_X_pow,red_coeff]
  simp only [scaledSquareSubstitution,coeff_mk]
  by_cases h : 0 < n ∧ 2∣n
  · obtain ⟨hp,k,rfl⟩ := h
    rw [if_pos ⟨hp,dvd_mul_right ..⟩,Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    rcases k with _|_|_|k
    · omega
    · simp [b1]
    · norm_num
    · rw [show k+1+1+1-1=2+k by omega,pow_add,Int.cast_mul,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
      have h2 : 2*(k+1+1+1) ≠ 2 := by omega
      have h4 : 2*(k+1+1+1) ≠ 4 := by omega
      simp [h2,h4,show (4:ZMod 8)^2=0 by decide]
  · rw [if_neg h]
    have h2 : n≠2 := by rintro rfl;exact h (by decide)
    have h4 : n≠4 := by rintro rfl;exact h (by decide)
    simp [h2,h4]

private lemma bin_mod (B : PowerSeries ℤ) (b0 : constantCoeff B=0) (b1 : coeff 1 B=1)
    (he : B*scaledRatio B = scaledSquareSubstitution B) :
    red 8 B*(red 8 B - C (4:ZMod 8)*X^2) = X^2 + C (4*(↑(coeff 2 B):ZMod 8))*X^4 := by
  simpa only [map_mul,ratio8 B b0 b1,square8 B b1] using congrArg (red 8) he

private lemma parity (B : PowerSeries ℤ) (h :
    red 8 B*(red 8 B-C (4:ZMod 8)*X^2) = X^2+C (4*(↑(coeff 2 B):ZMod 8))*X^4) :
    red 2 B = X := by
  let f := ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)
  have hf : PowerSeries.map f (red 8 B) = red 2 B := by
    ext i;change f ((↑(coeff i B):ZMod 8))=↑(coeff i B); exact map_intCast f _
  have h4 : f 4=0 := by change (4:ZMod 2)=0;decide
  have v := congrArg (PowerSeries.map f) h
  simp only [map_mul,map_add,map_sub,map_pow,PowerSeries.map_X,PowerSeries.map_C,hf,h4,zero_mul,
    map_zero,add_zero,sub_zero] at v
  have sq : (red 2 B - X)^2=0 := by
    rw [sub_sq,show (2:PowerSeries (ZMod 2))=0 by exact (map_ofNat C 2).symm.trans (by rw [show (2:ZMod 2)=0 by decide,map_zero])]
    simp only [zero_mul,sub_zero,pow_two] at *
    rw [v,←two_mul,show (2:PowerSeries (ZMod 2))=0 by exact (map_ofNat C 2).symm.trans (by rw [show (2:ZMod 2)=0 by decide,map_zero]),zero_mul]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (by decide : 2 ≠ 0)).mp sq)

private lemma lift_series (B : PowerSeries ℤ) (b0 : constantCoeff B=0) (hb : red 2 B = X) :
    ∃ D : PowerSeries ℤ, B = X + C (2:ℤ)*(X*D) := by
  let D : PowerSeries ℤ := PowerSeries.mk fun i => (coeff (i+1) B - coeff (i+1) X)/2
  refine ⟨D,?_⟩
  ext i
  cases i with
  | zero => simp [coeff_zero_eq_constantCoeff,b0]
  | succ i =>
    rw [map_add,coeff_C_mul,coeff_succ_X_mul,coeff_mk]
    have eq := congrArg (coeff (i+1)) hb
    have eqX : red 2 (X : PowerSeries ℤ)=X := PowerSeries.map_X _
    rw [← eqX,red_coeff,red_coeff] at eq
    have dvd := (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp eq
    omega

private lemma normalized (B D : PowerSeries ℤ) (hb : B = X + C (2:ℤ)*(X*D))
    (hp : red 2 B=X)
    (h : red 8 B*(red 8 B-C (4:ZMod 8)*X^2)=X^2+C (4*(↑(coeff 2 B):ZMod 8))*X^4) :
    red 2 D+(red 2 D)^2=X := by
  have even := congrArg (coeff 2) hp
  rw [red_coeff,coeff_X] at even
  norm_num at even
  obtain ⟨k,hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (coeff 2 B) 2).mp even
  have m8 : 4*(↑(coeff 2 B):ZMod 8)=0 := by
    rw [hk,Int.cast_mul];change 4*(2*(k:ZMod 8))=0; rw [←mul_assoc,show (4:ZMod 8)*2=0 by decide,zero_mul]
  rw [m8,map_zero,zero_mul,add_zero,hb] at h
  simp only [map_add,map_mul,red,PowerSeries.map_X,PowerSeries.map_C] at h
  let R := red 8 D
  change (X + C (2:ZMod 8)*(X*R))*((X+C (2:ZMod 8)*(X*R))-C 4*X^2)=X^2 at h
  have nums (j : ℕ) : (C (j:ZMod 8) : PowerSeries (ZMod 8)) = j := map_natCast _ _
  rw [show (C (2:ZMod 8):PowerSeries (ZMod 8))=2 from nums 2,
    show (C (4:ZMod 8):PowerSeries (ZMod 8))=4 from nums 4] at h
  have z8 : (8 : PowerSeries (ZMod 8))=0 := (map_ofNat C 8).symm.trans (by rw [show (8:ZMod 8)=0 by decide,map_zero])
  have he : X^2*(4*(R+R^2-X))=0 := by
    linear_combination (norm := ring_nf) h + (X^3*R)*z8
  have hd8 : (4:PowerSeries (ZMod 8))*(R+R^2-X)=0 := by
    ext i
    have hi := congrArg (coeff (i+2)) he
    simpa [coeff_X_pow_mul,add_comm] using hi
  have co (i : ℕ) : (2:ℤ) ∣ coeff i (D+D^2-X) := by
    have hr : red 8 (D+D^2-X)= R+R^2-X := by simp [red,R]
    rw [←hr,←show (C (4:ZMod 8):PowerSeries (ZMod 8))=4 from nums 4] at hd8
    have hi := congrArg (coeff i) hd8
    simp only [coeff_C_mul,red_coeff,map_zero] at hi
    have hv : ((↑(4*coeff i (D+D^2-X):ℤ)):ZMod 8)=0 := by push_cast;exact hi
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp hv
    omega
  have hz : red 2 (D+D^2-X)=0 := by
    ext i; rw [red_coeff,map_zero];exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr (co i)
  simpa [red,sub_eq_zero] using hz
open scoped Classical in
private lemma powers (D : PowerSeries (ZMod 2)) (eqn : D+D^2=X) (n : ℕ) (hn : 0 < n) :
    coeff n D = if (∃ k : ℕ, n=2^k) then 1 else 0 := by
  classical
  have hfr : PowerSeries.map (frobenius (ZMod 2) 2) (PowerSeries.expand 2 (by decide) D) = D^2 :=
    MvPowerSeries.map_frobenius_expand 2 (by decide)
  have hfk (i : ℕ) : coeff i (D^2)=if 2∣i then coeff (i/2) D else 0 := by
    rw [← hfr,coeff_map,frobenius_def,ZMod.pow_card,PowerSeries.coeff_expand]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have e := congrArg (coeff n) eqn
    rw [map_add,hfk,coeff_X] at e
    by_cases h1 : n=1
    · subst n; rw [if_pos ⟨0,by decide⟩]; simpa using e
    rw [if_neg h1] at e
    by_cases he : 2∣n
    · obtain ⟨j,rfl⟩ := he
      have hj : 0 < j := by omega
      rw [if_pos (dvd_mul_right ..),Nat.mul_div_cancel_left _ (by decide : 0 < 2)] at e
      have hc : coeff (2*j) D=coeff j D := by
        have hsum := congrArg (fun x : ZMod 2 => x+coeff j D) e
        simpa [add_assoc,CharTwo.add_self_eq_zero] using hsum
      rw [hc,ih j (by omega) hj]
      have ex : (∃ k : ℕ, 2*j=2^k) ↔ ∃ k : ℕ, j=2^k := by
        constructor
        · rintro ⟨_ | k,hk⟩
          · simp at hk
          · rw [pow_succ] at hk; exact ⟨k,by omega⟩
        · rintro ⟨k,rfl⟩;exact ⟨k+1,by rw [pow_succ];omega⟩
      simp_rw [ex]
    · rw [if_neg he,add_zero] at e
      have no : ¬∃ k : ℕ,n=2^k := by
        rintro ⟨_ | k,rfl⟩
        · simp at h1
        · exact he (by simp [pow_succ])
      simpa [no] using e

theorem solution (B : PowerSeries ℤ) (b0 : constantCoeff B=0) (b1 : coeff 1 B=1)
    (h : B*scaledRatio B=scaledSquareSubstitution B) (n : ℕ) (hn : 1 < n) :
    ((coeff n B ≡ 2 [ZMOD 4]) ↔ specialIndex n) ∧
      (¬specialIndex n → (4:ℤ)∣coeff n B) := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h8 := bin_mod B b0 b1 h
  have h2 := parity B h8
  obtain ⟨D,hd⟩ := lift_series B b0 h2
  have power := powers _ (normalized B D hd h2 h8) i (by omega)
  rw [red_coeff] at power
  have c : coeff (i+1) B=2*coeff i D := by
    rw [hd,map_add,coeff_X,if_neg (by omega),coeff_C_mul,coeff_succ_X_mul,zero_add]
  have eqv : specialIndex (i+1) ↔ ∃ k : ℕ, i=2^k := by simp [specialIndex]
  rw [eqv,c]
  by_cases hpow : ∃ k : ℕ, i=2^k
  · rw [if_pos hpow] at power
    have eq := (ZMod.intCast_eq_intCast_iff (coeff i D) 1 2).mp (by simpa using power)
    simp only [Int.ModEq] at eq ⊢
    exact ⟨⟨fun _ => hpow,fun _ => by omega⟩,fun hno => (hno hpow).elim⟩
  · rw [if_neg hpow] at power
    obtain ⟨k,hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp power
    constructor
    · simp only [Int.ModEq,hpow,iff_false];omega
    · intro _;exact ⟨k,by omega⟩

end
end S378

theorem OMA.solution : type_of% @OMA.S_oeis_a378259.main := S378.solution
