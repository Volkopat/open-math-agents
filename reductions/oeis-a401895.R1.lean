import OMAStatements.S_oeis_a401895

-- Credit: @physbuzz; endpoint classification and the modulo 11 argument follow
-- the project note of Cornelius Lytollis (@con123-gif).
namespace OMA.R_oeis_a401895_R1

open OMA.S_oeis_a401895

/-- Exclude products with an odd number of identical digits. -/
def H1 : Prop := ∀ n d j : ℕ, 3 < n → 0 < d → d < 10 →
    Nat.digits 10 (n * R n) ≠ List.replicate (2*j+1) d

/-- Exclude fives for factors ending in 5 and 9, at the permitted lengths. -/
def H2 : Prop := ∀ n : ℕ, let l := (Nat.digits 10 n).length
    3 < n → 11 ∣ l → ((n%10 = 5 ∧ R n%10 = 9) ∨ (n%10 = 9 ∧ R n%10 = 5)) →
    Nat.digits 10 (n * R n) ≠ List.replicate (2*l) 5

/-- Exclude sixes for factors ending in 7 and 8, at the permitted lengths. -/
def H3 : Prop := ∀ n : ℕ, let l := (Nat.digits 10 n).length
    3 < n → l % 297 ∈ ([0,66,165,264] : List ℕ) →
    ((n%10 = 7 ∧ R n%10 = 8) ∨ (n%10 = 8 ∧ R n%10 = 7)) →
    Nat.digits 10 (n * R n) ≠ List.replicate (2*l) 6

lemma word_period (d t q : ℕ) (zero : (Nat.ofDigits 10 (List.replicate (2*t) d)) ≡ 0 [MOD q])
    (one : (10:ℕ)^(2*t) ≡ 1 [MOD q]) (l : ℕ) :
    (Nat.ofDigits 10 (List.replicate (2*l) d)) ≡ (Nat.ofDigits 10 (List.replicate (2*(l%t)) d)) [MOD q] := by
  have shift (j : ℕ) : (Nat.ofDigits 10 (List.replicate (2*(j+t)) d)) ≡ (Nat.ofDigits 10 (List.replicate (2*j) d)) [MOD q] := by
    rw [show 2*(j+t) = 2*t+2*j by omega, List.replicate_add, Nat.ofDigits_append, List.length_replicate]
    simpa only [zero_add, one_mul] using zero.add (one.mul_right ((Nat.ofDigits 10 (List.replicate (2*j) d))))
  have repeatShift (a b : ℕ) : (Nat.ofDigits 10 (List.replicate (2*(a+t*b)) d)) ≡ (Nat.ofDigits 10 (List.replicate (2*a) d)) [MOD q] := by
    induction b with
    | zero => simpa only [Nat.mul_zero,Nat.add_zero] using (Nat.ModEq.refl ((Nat.ofDigits 10 (List.replicate (2*a) d))) : (Nat.ofDigits 10 (List.replicate (2*a) d)) ≡ (Nat.ofDigits 10 (List.replicate (2*a) d)) [MOD q])
    | succ b ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc]
      exact (shift _).trans ih
  simpa only [Nat.mod_add_div] using repeatShift (l%t) (l/t)

lemma rev9 (n : ℕ) : R n ≡ n [MOD 9] := by
  have h := Nat.ofDigits_modEq 10 9 (Nat.digits 10 n).reverse
  exact (show R n ≡ (Nat.digits 10 n).sum [MOD 9] by simpa [R, Nat.ofDigits_one] using h).trans
    (Nat.modEq_nine_digits_sum n).symm

lemma sixes_length (n l : ℕ) (h : n * R n = (Nat.ofDigits 10 (List.replicate (2*l) 6))) :
    l % 27 ∈ ([0,3,12,21] : List ℕ) := by
  let ok (r : ℕ) := r%3 = 1 ∨ r ∈ ([0,9,36,63] : List ℕ)
  have product_table : ∀ a b : Fin 81, a.val%9 = b.val%9 → ok (a.val*b.val%81) := by decide +kernel
  have length_table : ∀ j : Fin 27, ok ((Nat.ofDigits 10 (List.replicate (2*j.val) 6)) % 81) → j.val ∈ ([0,3,12,21] : List ℕ) := by decide +kernel
  apply length_table ⟨l%27,Nat.mod_lt _ (by decide)⟩
  have same : (Nat.ofDigits 10 (List.replicate (2*l) 6)) % 81 = (Nat.ofDigits 10 (List.replicate (2*(l%27)) 6)) % 81 :=
    word_period 6 27 81 (by decide +kernel) (by decide +kernel) l
  rw [← same, ← h, Nat.mul_mod]
  apply product_table ⟨n%81,Nat.mod_lt _ (by decide)⟩ ⟨R n%81,Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.mod_mod_of_dvd _ (by decide : 9 ∣ 81)] using (show n%9 = R n%9 from (rev9 n).symm)

lemma rev11_list (ds : List ℕ) :
    ((Nat.ofDigits 10 ds.reverse : ℕ) : ZMod 11) =
      -(-1 : ZMod 11)^ds.length * (Nat.ofDigits 10 ds : ℕ) := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    have ten : (10 : ZMod 11) = -1 := by decide
    rw [Nat.ofDigits_reverse_cons, Nat.ofDigits_cons]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [ih, ten, List.length_cons, pow_succ]
    ring

lemma even_length (n d l : ℕ) (hd : 0 < d) (hd' : d < 10) (h : n * R n = (Nat.ofDigits 10 (List.replicate (2*l) d))) : 11 ∣ l := by
  have start : ∀ d : Fin 10, (Nat.ofDigits 10 (List.replicate (2*11) d.val)) ≡ 0 [MOD 121] := by decide +kernel
  have rem : (Nat.ofDigits 10 (List.replicate (2*l) d)) ≡ (Nat.ofDigits 10 (List.replicate (2*(l%11)) d)) [MOD 121] :=
    word_period d 11 121 (start ⟨d,hd'⟩) (by decide +kernel) l
  have tab : ∀ d : Fin 10, ∀ j : Fin 11, 11 ∣ (Nat.ofDigits 10 (List.replicate (2*j.val) d.val)) ∧
      (0 < d.val → 121 ∣ (Nat.ofDigits 10 (List.replicate (2*j.val) d.val)) → j.val = 0) := by decide +kernel
  have ⟨div11, recover⟩ := tab ⟨d,hd'⟩ ⟨l%11,Nat.mod_lt _ (by decide)⟩
  have eleven : Nat.Prime 11 := by decide
  have product : 11 ∣ n*R n := by
    rw [h]
    exact Nat.modEq_zero_iff_dvd.mp ((rem.of_dvd (by decide : 11 ∣ 121)).trans div11.modEq_zero_nat)
  have revSign :=  rev11_list (Nat.digits 10 n)
  rw [Nat.ofDigits_digits] at revSign
  change (R n : ZMod 11) = _ at revSign
  have iff11 : 11 ∣ R n ↔ 11 ∣ n := by
    rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff, revSign]
    simp
  have dn : 11 ∣ n := (eleven.dvd_mul.mp product).elim id iff11.mp
  have full : 121 ∣ n*R n := Nat.mul_dvd_mul dn (iff11.mpr dn)
  rw [h] at full
  apply Nat.dvd_of_mod_eq_zero
  exact recover hd (Nat.modEq_zero_iff_dvd.mp (rem.symm.trans full.modEq_zero_nat))

lemma sixes_digit_lengths (n l : ℕ)
    (h : Nat.digits 10 (n * R n) = List.replicate (2*l) 6) :
    l % 297 ∈ ([0,66,165,264] : List ℕ) := by
  have number : n * R n = (Nat.ofDigits 10 (List.replicate (2*l) 6)) := by
    simpa only [Nat.ofDigits_digits] using congrArg (Nat.ofDigits (10 : ℕ)) h
  have h27 := sixes_length n l number
  have h11 := even_length n 6 l (by decide) (by decide) number
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h27 ⊢
  omega

lemma last_bounds (u : List ℕ) (a : ℕ) (small : ∀ x ∈ u, x < 10) :
    a * 10^u.length ≤ Nat.ofDigits 10 (u++[a]) ∧ Nat.ofDigits 10 (u++[a]) < (a+1)*10^u.length := by
  rw [Nat.ofDigits_append, Nat.ofDigits_singleton, Nat.mul_comm _ a, Nat.add_mul, one_mul]
  have h := Nat.ofDigits_lt_base_pow_length (by decide : 1 < 10) small
  omega

lemma even_endpoints (n d l : ℕ) (hn : 0 < n) (hl : 0 < l) (hd : 0 < d) (hd' : d < 10)
    (he : Nat.digits 10 (n*R n) = List.replicate (2*l) d) :
    l = (Nat.digits 10 n).length ∧
      ((d = 5 ∧ ((n%10 = 5 ∧ R n%10 = 9) ∨ (n%10 = 9 ∧ R n%10 = 5))) ∨
       (d = 6 ∧ ((n%10 = 7 ∧ R n%10 = 8) ∨ (n%10 = 8 ∧ R n%10 = 7)))) := by
  obtain ⟨a,u,hu⟩ := List.exists_cons_of_ne_nil (Nat.digits_ne_nil_iff_ne_zero.mpr hn.ne' : Nat.digits 10 n ≠ [])
  have ne : (Nat.digits 10 n).reverse ≠ [] := by simp [hu]
  obtain ⟨b,v,hv⟩ := List.exists_cons_of_ne_nil ne
  have hbds : Nat.digits 10 n = v.reverse ++ [b] := by simpa using congrArg List.reverse hv
  have hrds : (Nat.digits 10 n).reverse = u.reverse ++ [a] := by simp [hu]
  have len : v.length = u.length := by
    have e := congrArg List.length hv
    simpa [hu] using e.symm
  have small : ∀ x ∈ Nat.digits 10 n, x < 10 := fun _ h => Nat.digits_lt_base (by decide) h
  have nval := Nat.ofDigits_digits 10 n
  have nunit : n%10 = a := by
    rw [← nval, hu, Nat.ofDigits_cons]
    simpa [Nat.add_mul_mod_self_left] using Nat.mod_eq_of_lt (small a (hu ▸ List.mem_cons_self))
  have runit : R n%10 = b := by
    have hb : b < 10 := small b (by simp [hbds])
    simp [R,hv,Nat.ofDigits_cons,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hb]
  let P := 10^u.length
  have N : b*P ≤ n ∧ n < (b+1)*P := by
    have := last_bounds v.reverse b (fun x hx => small x (by rw [hbds]; exact List.mem_append_left _ hx))
    simpa only [← hbds, nval, List.length_reverse, len, P] using this
  have M : a*P ≤ R n ∧ R n < (a+1)*P := by
    have := last_bounds u.reverse a (fun x hx => small x (by rw [hu]; exact List.mem_cons_of_mem _ (List.mem_reverse.mp hx)))
    simpa only [← hrds, R, List.length_reverse,P] using this
  have v := Nat.ofDigits_digits 10 (n*R n)
  have units : (a*b)%10 = d := by
    have hm : 2*l = (2*l-1)+1 := by omega
    rw [he, hm, List.replicate_succ, Nat.ofDigits_cons] at v
    have eq := congrArg (· % 10) v
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd', Nat.mul_mod, nunit, runit] at eq
    exact eq.symm
  have ha : a < 10 := nunit ▸ Nat.mod_lt _ (by decide)
  have hb : b < 10 := runit ▸ Nat.mod_lt _ (by decide)
  have apos : 0 < a := by by_contra! hz; simp [show a = 0 by omega] at units; omega
  have bpos : 0 < b := by by_contra! hz; simp [show b = 0 by omega] at units; omega
  have boundlo : (b*a)*(P*P) ≤ n*R n := by simpa only [Nat.mul_mul_mul_comm] using Nat.mul_le_mul N.1 M.1
  have boundhi : n*R n < ((b+1)*(a+1))*(P*P) := by
    convert Nat.mul_lt_mul_of_lt_of_lt N.2 M.2 using 1; ring
  have lo : 10^(2*u.length) ≤ n*R n := by
    rw [Nat.mul_comm 2, pow_mul, pow_two]
    dsimp only [P] at boundlo
    exact (Nat.le_mul_of_pos_left _ (Nat.mul_pos bpos apos)).trans boundlo
  have hi : n*R n < 10^(2*(u.length+1)) := by
    have cap : (b+1)*(a+1) ≤ 100 := by exact Nat.mul_le_mul (by omega : b+1 ≤ 10) (by omega : a+1 ≤ 10)
    calc
      _ < _ := boundhi
      _ ≤ 100 * (P*P) := Nat.mul_le_mul_right _ cap
      _ = _ := by rw [Nat.mul_comm 2, pow_mul, pow_succ (10:ℕ) u.length]; dsimp only [P]; ring
  have lowLen := (Nat.lt_digits_length_iff (by decide : 1<10) _).mpr lo
  have highLen := (Nat.digits_length_le_iff (by decide : 1<10) _).mpr hi
  rw [he, List.length_replicate] at lowLen highLen
  have lengths : l = u.length+1 := by omega
  have split : List.replicate (2*l) d = List.replicate (2*u.length) d ++ [d,d] := by
    rw [show 2*l = 2*u.length+2 by omega, List.replicate_add]; rfl
  have rv := Nat.ofDigits_lt_base_pow_length (b:=10) (l:=List.replicate (2*u.length) d)
    (by decide) (by intro x hx; exact (List.eq_of_mem_replicate hx) ▸ hd')
  have power : (10:ℕ)^(2*u.length) = P*P := by rw [Nat.mul_comm 2, pow_mul, pow_two]
  rw [he,split,Nat.ofDigits_append,List.length_replicate,power] at v
  rw [List.length_replicate,power] at rv
  have two : Nat.ofDigits 10 [d,d] = 11*d := by simp [Nat.ofDigits_cons]; ring
  rw [two] at v
  have pp : 0 < P*P := by dsimp [P]; positivity
  have leftBound : a*b < 11*d+1 := by
    apply (Nat.mul_lt_mul_right pp).mp
    rw [Nat.mul_comm a b, Nat.add_mul, one_mul]
    nlinarith only [boundlo,v,rv]
  have rightBound : 11*d < (a+1)*(b+1) := by
    apply (Nat.mul_lt_mul_right pp).mp
    rw [Nat.mul_comm (a+1) (b+1)]
    nlinarith only [v,boundhi,Nat.zero_le (Nat.ofDigits 10 (List.replicate (2*u.length) d))]
  have casesTable : ∀ a b : Fin 10, let d := a.val*b.val%10
      0 < d → a.val*b.val < 11*d+1 → 11*d < (a.val+1)*(b.val+1) →
      ((d=5 ∧ ((a.val=5 ∧ b.val=9) ∨ (a.val=9 ∧ b.val=5))) ∨
       (d=6 ∧ ((a.val=7 ∧ b.val=8) ∨ (a.val=8 ∧ b.val=7)))) := by decide +kernel
  refine ⟨by simpa [hu] using lengths, ?_⟩
  rw [nunit,runit]
  have cert := casesTable ⟨a,ha⟩ ⟨b,hb⟩
  dsimp only at cert
  rw [units] at cert
  exact cert hd leftBound rightBound
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a401895.main := by
  intro odd fives sixes n hn
  constructor
  · intro ha
    by_contra! h
    have big : 3 < n := by omega
    change (Nat.digits 10 (n*R n)).toFinset.card = 1 at ha
    obtain ⟨d,hd⟩ := Finset.card_eq_one.mp ha
    have mem : d ∈ Nat.digits 10 (n*R n) := by
      apply List.mem_toFinset.mp
      rw [hd]
      exact Finset.mem_singleton_self _
    have small : d < 10 := Nat.digits_lt_base (by decide) mem
    have eq : Nat.digits 10 (n*R n) =
        List.replicate (Nat.digits 10 (n*R n)).length d := by
      apply List.eq_replicate_length.mpr
      intro x hx
      have m := List.mem_toFinset.mpr hx
      rw [hd] at m
      exact Finset.mem_singleton.mp m
    have nz : n*R n ≠ 0 := by
      intro z
      simp [z] at mem
    have pos : 0 < d := by
      by_contra! h0
      have v := congrArg (Nat.ofDigits (10:ℕ)) eq
      rw [show d=0 by omega, Nat.ofDigits_digits] at v
      exact nz (by simpa using v)
    let k := (Nat.digits 10 (n*R n)).length
    have pk : 0 < k := List.length_pos_of_mem mem
    let l := k/2
    change Nat.digits 10 (n*R n) = List.replicate k d at eq
    rcases (show k = 2*l+1 ∨ k = 2*l by dsimp [l]; omega) with ho | he
    · rw [ho] at eq
      exact odd n d l big pos small eq
    · rw [he] at eq
      have lp : 0 < l := by omega
      obtain ⟨len, cases⟩ := even_endpoints n d l (by omega) lp pos small eq
      rcases cases with ⟨rfl, ends⟩ | ⟨rfl, ends⟩
      · have nv := congrArg (Nat.ofDigits (10:ℕ)) eq
        rw [Nat.ofDigits_digits] at nv
        have valid := even_length n 5 l (by decide) (by decide) nv
        rw [len] at valid eq
        exact fives n big valid ends eq
      · have valid := sixes_digit_lengths n l eq
        rw [len] at valid eq
        exact sixes n big valid ends eq
  · rintro (rfl | rfl | rfl) <;> decide +kernel

end OMA.R_oeis_a401895_R1
