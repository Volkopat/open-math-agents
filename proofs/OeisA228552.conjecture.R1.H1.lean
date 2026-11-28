import OMAReductions.R_OeisA228552_conjecture_R1

/-!
Proof of `OMA.R_OeisA228552_conjecture_R1.H1` by block reduction and mod-1009 LU certificates.
-/

namespace OeisA228552Proof

def primeMask : Nat :=
  3414857705457999460412504620046701081877659478655663738144263752647377262338666202686165793860328372677976272531356905852572269417635151151376588168753244723096253039896329897481818371252044830430050797102376871271380460975402971499352111589548

def isPrimeAux (n : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, d =>
    if d * d > n then true
    else if n % d == 0 then false
    else isPrimeAux n fuel (d + 1)

def isPrimeBool (n : Nat) : Bool :=
  if n < 2 then false else isPrimeAux n 30 2

theorem mask_eq_isPrimeBool :
    ∀ k : Fin 805, primeMask.testBit k.1 = isPrimeBool k.1 := by
  decide +kernel

theorem isPrimeAux_true_iff :
    ∀ (fuel d n : Nat), 2 ≤ d → n < (d + fuel) * (d + fuel) →
      (isPrimeAux n fuel d = true ↔ ∀ m, d ≤ m → m * m ≤ n → ¬ m ∣ n)
  | 0, d, n, _, hn => by
    simp only [isPrimeAux, Nat.add_zero] at *
    constructor
    · intro _ m hm1 hm2
      have : d * d ≤ m * m := Nat.mul_le_mul hm1 hm1
      omega
    · intro _; trivial
  | fuel + 1, d, n, hd, hn => by
    simp only [isPrimeAux]
    by_cases hgt : d * d > n
    · simp only [hgt, ↓reduceIte, true_iff]
      intro m hm1 hm2
      have : d * d ≤ m * m := Nat.mul_le_mul hm1 hm1
      omega
    · simp only [hgt, ↓reduceIte]
      by_cases hmod : n % d = 0
      · have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero hmod
        have hbeq : (n % d == 0) = true := beq_iff_eq.mpr hmod
        simp only [hbeq, ↓reduceIte, Bool.false_eq_true, false_iff, not_forall, not_not]
        exact ⟨d, le_rfl, Nat.le_of_not_lt hgt, hdvd⟩
      · have hbeq : (n % d == 0) = false := beq_false_of_ne hmod
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
        have hn' : n < (d + 1 + fuel) * (d + 1 + fuel) := by
          have : d + 1 + fuel = d + (fuel + 1) := by omega
          rw [this]; exact hn
        rw [isPrimeAux_true_iff fuel (d + 1) n (by omega) hn']
        constructor
        · intro h m hm1 hm2 hm_dvd
          rcases Nat.eq_or_lt_of_le hm1 with rfl | hlt
          · exact hmod (Nat.mod_eq_zero_of_dvd hm_dvd)
          · exact h m hlt hm2 hm_dvd
        · intro h m hm1 hm2
          exact h m (by omega) hm2

theorem isPrimeBool_iff_prime {n : Nat} (hn : n < 805) :
    isPrimeBool n = true ↔ Nat.Prime n := by
  simp only [isPrimeBool]
  by_cases hn2 : n < 2
  · simp only [hn2, ↓reduceIte, Bool.false_eq_true, false_iff]
    intro hp
    have := hp.two_le
    omega
  · simp only [hn2, ↓reduceIte]
    have hn_bound : n < (2 + 30) * (2 + 30) := by omega
    rw [isPrimeAux_true_iff 30 2 n le_rfl hn_bound]
    constructor
    · intro h
      by_contra hnp
      have hne1 : n ≠ 1 := by omega
      have hmf_p : n.minFac.Prime := Nat.minFac_prime hne1
      have hmf_sq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
      have hmf_dvd : n.minFac ∣ n := Nat.minFac_dvd n
      have hmf_sq' : n.minFac * n.minFac ≤ n := by simpa [sq] using hmf_sq
      exact h n.minFac hmf_p.two_le hmf_sq' hmf_dvd
    · intro hp m hm2 hmsq hdvd
      rcases hp.eq_one_or_self_of_dvd m hdvd with rfl | rfl
      · omega
      · have : 2 * m ≤ m * m := Nat.mul_le_mul_right m hm2
        omega

theorem primeMask_testBit_iff {k : Nat} (hk : k < 805) :
    primeMask.testBit k = true ↔ Nat.Prime k := by
  have h := mask_eq_isPrimeBool ⟨k, hk⟩
  simp only at h
  rw [h, isPrimeBool_iff_prime hk]

def base18 : Nat := 262144

def packPoly : List Nat → Nat
  | [] => 0
  | x :: xs => x + base18 * packPoly xs

theorem packPoly_eq_sum :
    ∀ xs : List Nat, packPoly xs = ∑ i ∈ Finset.range xs.length, xs.getD i 0 * base18 ^ i
  | [] => by simp [packPoly]
  | x :: xs => by
    simp only [packPoly, List.length_cons, Finset.sum_range_succ', pow_zero, mul_one,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [packPoly_eq_sum xs, Finset.mul_sum, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ']
    ring

theorem sum_lt_pow {B : Nat} (hB : 0 < B) (f : Nat → Nat) (hf : ∀ i, f i < B) :
    ∀ d : Nat, ∑ i ∈ Finset.range d, f i * B ^ i < B ^ d
  | 0 => by simp
  | d + 1 => by
    rw [Finset.sum_range_succ]
    have ih := sum_lt_pow hB f hf d
    have hfd : f d + 1 ≤ B := hf d
    calc ∑ i ∈ Finset.range d, f i * B ^ i + f d * B ^ d
        < B ^ d + f d * B ^ d := Nat.add_lt_add_right ih _
      _ = (f d + 1) * B ^ d := by ring
      _ ≤ B * B ^ d := Nat.mul_le_mul_right _ hfd
      _ = B ^ (d + 1) := by ring

theorem extract_coeff {B : Nat} (hB : 0 < B) (f : Nat → Nat) (hf : ∀ i, f i < B)
    (M d : Nat) (hd : d < M) :
    ((∑ i ∈ Finset.range M, f i * B ^ i) / B ^ d) % B = f d := by
  have hsplit : M = d + (M - d) := by omega
  have hsplit2 : M - d = 1 + (M - d - 1) := by omega
  have hsum : ∑ i ∈ Finset.range M, f i * B ^ i =
      (∑ i ∈ Finset.range d, f i * B ^ i) +
        B ^ d * (f d + B * ∑ j ∈ Finset.range (M - d - 1), f (d + 1 + j) * B ^ j) := by
    conv_lhs => rw [hsplit, Finset.sum_range_add]
    congr 1
    conv_lhs => rw [hsplit2, Finset.sum_range_add, Finset.sum_range_one]
    simp only [Nat.add_zero, pow_add, pow_one, Finset.mul_sum]
    rw [mul_add]
    congr 1
    · ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have : d + (1 + j) = d + 1 + j := by omega
      rw [this]
      ring
  rw [hsum]
  have hlow := sum_lt_pow hB f hf d
  have hpow : 0 < B ^ d := Nat.pow_pos hB
  rw [Nat.add_mul_div_left _ _ hpow, Nat.div_eq_of_lt hlow, Nat.zero_add]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hf d)]

theorem packPoly_mul_extract (n r : Nat) (hrn : r < n) (hn : n ≤ 200)
    (u : List Nat) (hu_len : u.length = r + 1) (hu_lt : ∀ x ∈ u, x < 1009)
    (v : Nat → Bool) :
    let colList := (List.range n).map fun j => if v (n - 1 - j) then 1 else 0
    ((packPoly u * packPoly colList) / base18 ^ (n - 1)) % base18 =
      ∑ i ∈ Finset.range (r + 1), u.getD i 0 * (if v i then 1 else 0) := by
  intro colList
  have hB : 0 < base18 := by decide
  let U : Nat → Nat := fun k => u.getD k 0
  let V : Nat → Nat := fun j => if j < n then (if v j then 1 else 0) else 0
  have hu_sum : packPoly u = ∑ k ∈ Finset.range n, U k * base18 ^ k := by
    rw [packPoly_eq_sum u, hu_len]
    have hsplit : n = (r + 1) + (n - (r + 1)) := by omega
    conv_rhs => rw [hsplit, Finset.sum_range_add]
    have hzero : ∑ j ∈ Finset.range (n - (r + 1)), U (r + 1 + j) * base18 ^ (r + 1 + j) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have hge : u.length ≤ r + 1 + j := by omega
      simp only [U]
      rw [List.getD_eq_default u 0 hge, zero_mul]
    rw [hzero, add_zero]
  have hcol_len : colList.length = n := by simp [colList]
  have hv_sum : packPoly colList = ∑ j ∈ Finset.range n, V j * base18 ^ (n - 1 - j) := by
    rw [packPoly_eq_sum colList, hcol_len]
    have hcongr : ∑ j ∈ Finset.range n, colList.getD j 0 * base18 ^ j =
        ∑ j ∈ Finset.range n, (if v (n - 1 - j) then 1 else 0) * base18 ^ j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j < n := Finset.mem_range.mp hj
      have hjd : j < colList.length := by rw [hcol_len]; exact hj'
      rw [List.getD_eq_getElem _ _ hjd]
      simp [colList]
    rw [hcongr]
    have href : ∑ j ∈ Finset.range n, (if v (n - 1 - j) then 1 else 0) * base18 ^ j =
        ∑ j ∈ Finset.range n, (if v j then 1 else 0) * base18 ^ (n - 1 - j) := by
      rw [← Finset.sum_range_reflect (fun j => (if v (n - 1 - j) then 1 else 0) * base18 ^ j) n]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j < n := Finset.mem_range.mp hj
      have : n - 1 - (n - 1 - j) = j := by omega
      rw [this]
    rw [href]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < n := Finset.mem_range.mp hj
    simp [V, hj']
  let coeff : Nat → Nat := fun m =>
    ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range n,
      if k + (n - 1 - j) = m then U k * V j else 0
  have hmul : packPoly u * packPoly colList =
      ∑ m ∈ Finset.range (2 * n), coeff m * base18 ^ m := by
    rw [hu_sum, hv_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    have hswap : ∑ m ∈ Finset.range (2 * n), coeff m * base18 ^ m =
        ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range n, (U k * V j) * base18 ^ (k + (n - 1 - j)) := by
      simp only [coeff, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      have hk' : k < n := Finset.mem_range.mp hk
      have hj' : j < n := Finset.mem_range.mp hj
      have hm : k + (n - 1 - j) ∈ Finset.range (2 * n) := by
        rw [Finset.mem_range]; omega
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_eq_single (k + (n - 1 - j))]
      · simp
      · intro m _ hmne
        rw [if_neg (Ne.symm hmne)]
      · intro hnot; exact absurd hm hnot
    rw [hswap]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_add]
    ring
  have hcoeff_lt : ∀ m, coeff m < base18 := by
    intro m
    have hle : coeff m ≤ ∑ k ∈ Finset.range n, U k := by
      apply Finset.sum_le_sum
      intro k _
      have hcard : ({j ∈ Finset.range n | k + (n - 1 - j) = m}).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro j1 hj1 j2 hj2
        simp only [Finset.mem_filter, Finset.mem_range] at hj1 hj2
        omega
      calc ∑ j ∈ Finset.range n, (if k + (n - 1 - j) = m then U k * V j else 0)
          = ∑ j ∈ {j ∈ Finset.range n | k + (n - 1 - j) = m}, U k * V j := by
            rw [← Finset.sum_filter]
        _ ≤ ∑ _j ∈ {j ∈ Finset.range n | k + (n - 1 - j) = m}, U k := by
            apply Finset.sum_le_sum
            intro j _
            have hv1 : V j ≤ 1 := by
              simp only [V]
              split_ifs <;> omega
            calc U k * V j ≤ U k * 1 := Nat.mul_le_mul_left _ hv1
              _ = U k := mul_one _
        _ = ({j ∈ Finset.range n | k + (n - 1 - j) = m}).card * U k := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ 1 * U k := Nat.mul_le_mul_right _ hcard
        _ = U k := one_mul _
    have hU_sum : ∑ k ∈ Finset.range n, U k ≤ 200 * 1008 := by
      have hU_le : ∀ k ∈ Finset.range n, U k ≤ if k < r + 1 then 1008 else 0 := by
        intro k _
        by_cases hk : k < r + 1
        · have hk' : k < u.length := by omega
          have hx := hu_lt u[k] (List.getElem_mem hk')
          simp only [U, List.getD_eq_getElem u 0 hk', hk, ↓reduceIte]
          omega
        · have hge : u.length ≤ k := by omega
          simp only [U, hk, ↓reduceIte]
          rw [List.getD_eq_default u 0 hge]
      calc ∑ k ∈ Finset.range n, U k
          ≤ ∑ k ∈ Finset.range n, (if k < r + 1 then 1008 else 0) := Finset.sum_le_sum hU_le
        _ = ∑ k ∈ Finset.range (r + 1), 1008 := by
            have hsp : n = (r + 1) + (n - (r + 1)) := by omega
            conv_lhs => rw [hsp, Finset.sum_range_add]
            have hz : ∑ j ∈ Finset.range (n - (r + 1)), (if r + 1 + j < r + 1 then 1008 else 0) = 0 := by
              apply Finset.sum_eq_zero; intro j _; simp [show ¬ (r + 1 + j < r + 1) by omega]
            rw [hz, add_zero]
            apply Finset.sum_congr rfl; intro k hk
            rw [Finset.mem_range] at hk; simp [hk]
        _ = (r + 1) * 1008 := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        _ ≤ 200 * 1008 := Nat.mul_le_mul_right _ (by omega)
    have hbase : 200 * 1008 < base18 := by decide
    omega
  rw [hmul, extract_coeff hB coeff hcoeff_lt (2 * n) (n - 1) (by omega)]
  have hdiag_k : ∀ k ∈ Finset.range n,
      (∑ j ∈ Finset.range n, if k + (n - 1 - j) = n - 1 then U k * V j else 0) = U k * V k := by
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    rw [Finset.sum_eq_single k]
    · simp [show k + (n - 1 - k) = n - 1 by omega]
    · intro j hj hjk
      have hj' : j < n := Finset.mem_range.mp hj
      rw [if_neg (by omega)]
    · intro hnot; exact absurd hk hnot
  simp only [coeff]
  rw [Finset.sum_congr rfl hdiag_k]
  have hsp : n = (r + 1) + (n - (r + 1)) := by omega
  conv_lhs => rw [hsp, Finset.sum_range_add]
  have hz : ∑ j ∈ Finset.range (n - (r + 1)), U (r + 1 + j) * V (r + 1 + j) = 0 := by
    apply Finset.sum_eq_zero; intro j _
    have hge : u.length ≤ r + 1 + j := by omega
    simp only [U]
    rw [List.getD_eq_default u 0 hge, zero_mul]
  rw [hz, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < r + 1 := Finset.mem_range.mp hi
  simp [U, V, show i < n by omega]

def checkRow (pow bNat r : Nat) : List Nat → Nat → Bool
  | [], _ => true
  | colNat :: cols, c =>
    if c < r then
      if (((bNat * colNat) / pow) % base18) % 1009 != 0 then false
      else checkRow pow bNat r cols (c + 1)
    else if c == r then
      (((bNat * colNat) / pow) % base18) % 1009 != 0
    else true

def checkAll (n : Nat) (cols : List Nat) : List (List Nat) → Nat → Bool
  | [], r => r == n
  | bRow :: rest, r =>
    if bRow.length == r + 1 && bRow.all (· < 1009) &&
        checkRow (base18 ^ (n - 1)) (packPoly bRow) r cols 0
    then checkAll n cols rest (r + 1)
    else false

theorem checkRow_sound (pow bNat r : Nat) :
    ∀ (cols : List Nat) (c0 : Nat),
      checkRow pow bNat r cols c0 = true →
      ∀ j, c0 ≤ j → ∀ hj : j - c0 < cols.length,
        (j < r → (((bNat * cols[j - c0]) / pow) % base18) % 1009 = 0) ∧
        (j = r → (((bNat * cols[j - c0]) / pow) % base18) % 1009 ≠ 0)
  | [], c0, _, j, _, hj => by simp at hj
  | col :: cols, c0, h, j, hcj, hj => by
    simp only [checkRow] at h
    by_cases hc_lt : c0 < r
    · simp only [hc_lt, ↓reduceIte] at h
      by_cases hbad : (((bNat * col) / pow) % base18) % 1009 != 0
      · simp [hbad] at h
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte] at h
        have hcol0 : (((bNat * col) / pow) % base18) % 1009 = 0 := by
          simpa [bne_iff_ne] using hbad
        rcases Nat.eq_or_lt_of_le hcj with rfl | hlt
        · simp only [Nat.sub_self, List.getElem_cons_zero]
          exact ⟨fun _ => hcol0, fun heq => by omega⟩
        · have hj1 : j - (c0 + 1) < cols.length := by simp at hj; omega
          have hsub : (col :: cols)[j - c0]'hj = cols[j - (c0 + 1)]'hj1 := by
            have hd : j - c0 = (j - (c0 + 1)) + 1 := by omega
            simp [hd]
          rw [hsub]
          exact checkRow_sound pow bNat r cols (c0 + 1) h j (by omega) hj1
    · simp only [hc_lt, ↓reduceIte] at h
      by_cases hc_eq : c0 = r
      · subst hc_eq
        simp only [beq_self_eq_true, ↓reduceIte, bne_iff_ne, ne_eq] at h
        rcases Nat.eq_or_lt_of_le hcj with rfl | hlt
        · simp only [Nat.sub_self, List.getElem_cons_zero]
          exact ⟨fun hlt => by omega, fun _ => h⟩
        · exact ⟨fun hlt => by omega, fun heq => by omega⟩
      · exact ⟨fun hlt => by omega, fun heq => by omega⟩

theorem checkAll_sound (n : Nat) (cols : List Nat) :
    ∀ (bMat : List (List Nat)) (r0 : Nat),
      checkAll n cols bMat r0 = true →
      r0 + bMat.length = n ∧
      ∀ (i : Nat) (hi : i < bMat.length),
        (bMat[i]).length = r0 + i + 1 ∧
        (∀ x ∈ bMat[i], x < 1009) ∧
        (∀ c (hc : c < cols.length), c < r0 + i →
          (((packPoly bMat[i] * cols[c]) / base18 ^ (n - 1)) % base18) % 1009 = 0) ∧
        (∀ hlt : r0 + i < cols.length,
          (((packPoly bMat[i] * cols[r0 + i]) / base18 ^ (n - 1)) % base18) % 1009 ≠ 0)
  | [], r0, h => by
    simp only [checkAll, beq_iff_eq] at h
    exact ⟨by omega, fun i hi => by simp at hi⟩
  | bRow :: rest, r0, h => by
    simp only [checkAll] at h
    split_ifs at h with hcond
    · simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hcond
      rcases hcond with ⟨⟨hlen, hlt⟩, hrow⟩
      have ih := checkAll_sound n cols rest (r0 + 1) h
      constructor
      · simp; omega
      · intro i hi
        cases i with
        | zero =>
          simp only [Nat.add_zero, List.getElem_cons_zero]
          refine ⟨hlen, hlt, ?_, ?_⟩
          · intro c hc hcr
            have hs := checkRow_sound (base18 ^ (n - 1)) (packPoly bRow) r0 cols 0 hrow c
              (Nat.zero_le _) (by simpa using hc)
            simpa using hs.1 hcr
          · intro hcr
            have hs := checkRow_sound (base18 ^ (n - 1)) (packPoly bRow) r0 cols 0 hrow r0
              (Nat.zero_le _) (by simpa using hcr)
            simpa using hs.2 rfl
        | succ i' =>
          simp only [List.getElem_cons_succ]
          have hi' : i' < rest.length := by simp at hi; omega
          have hih := ih.2 i' hi'
          have hadd : r0 + 1 + i' = r0 + (i' + 1) := by omega
          simpa [hadd] using hih

theorem det_submatrix_of_checkAll (n : Nat) (_hn1 : 1 ≤ n) (hn200 : n ≤ 200)
    (f : Nat → Nat → Bool) (bMat : List (List Nat))
    (hcheck : checkAll n ((List.range n).map fun c =>
        packPoly ((List.range n).map fun j => if f (n - 1 - j) c then 1 else 0)) bMat 0 = true)
    (k : Nat) (_hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (Matrix.of fun (i j : Fin k) => if f i.1 j.1 then (1 : ZMod 1009) else 0).det ≠ 0 := by
  have : Fact (Nat.Prime 1009) := ⟨by norm_num⟩
  let cols : List Nat := (List.range n).map fun c =>
    packPoly ((List.range n).map fun j => if f (n - 1 - j) c then 1 else 0)
  have hcols_len : cols.length = n := by simp [cols]
  have hsound := checkAll_sound n cols bMat 0 hcheck
  have hblen : bMat.length = n := by omega
  let B : Matrix (Fin k) (Fin k) (ZMod 1009) := Matrix.of fun r c =>
    if c.1 ≤ r.1 then ((bMat.getD r.1 [] |>.getD c.1 0 : Nat) : ZMod 1009) else 0
  let M : Matrix (Fin k) (Fin k) (ZMod 1009) := Matrix.of fun i j =>
    if f i.1 j.1 then (1 : ZMod 1009) else 0
  have hprod_entry : ∀ (r c : Fin k) (hcr : c.1 ≤ r.1),
      (B * M) r c = ((((packPoly (bMat[r.1]'(by omega)) * cols[c.1]'(by rw [hcols_len]; omega)) /
        base18 ^ (n - 1)) % base18 : Nat) : ZMod 1009) := by
    intro r c hcr
    let row := bMat[r.1]'(by omega)
    have hrow_spec := hsound.2 r.1 (by omega)
    have hrlen : row.length = r.1 + 1 := by simpa using hrow_spec.1
    have hrlt : ∀ x ∈ row, x < 1009 := hrow_spec.2.1
    have hmul := packPoly_mul_extract n r.1 (by omega) hn200 row hrlen hrlt (fun i => f i c.1)
    have hcol_eq : cols[c.1]'(by rw [hcols_len]; omega) =
        packPoly ((List.range n).map fun j => if f (n - 1 - j) c.1 then 1 else 0) := by
      simp [cols]
    rw [hcol_eq]
    have hmul' : ((packPoly row * packPoly ((List.range n).map fun j => if f (n - 1 - j) c.1 then 1 else 0)) /
        base18 ^ (n - 1)) % base18 = ∑ i ∈ Finset.range (r.1 + 1), row.getD i 0 * (if f i c.1 then 1 else 0) :=
      hmul
    rw [hmul', Nat.cast_sum]
    simp only [Matrix.mul_apply, B, M, Matrix.of_apply]
    have hsplit_sum : ∑ i : Fin k,
        (if i.1 ≤ r.1 then ((bMat.getD r.1 [] |>.getD i.1 0 : Nat) : ZMod 1009) else 0) *
          (if f i.1 c.1 then (1 : ZMod 1009) else 0) =
        ∑ i ∈ Finset.range (r.1 + 1),
          ((row.getD i 0 : Nat) : ZMod 1009) *
            (if f i c.1 then (1 : ZMod 1009) else 0) := by
      rw [Fin.sum_univ_eq_sum_range (fun x =>
        (if x ≤ r.1 then ((bMat.getD r.1 [] |>.getD x 0 : Nat) : ZMod 1009) else 0) *
          (if f x c.1 then (1 : ZMod 1009) else 0))]
      have hsp : Finset.range k = Finset.range ((r.1 + 1) + (k - (r.1 + 1))) := by
        congr 1; omega
      rw [hsp, Finset.sum_range_add]
      have hz : ∑ j ∈ Finset.range (k - (r.1 + 1)),
          (if r.1 + 1 + j ≤ r.1 then ((bMat.getD r.1 [] |>.getD (r.1 + 1 + j) 0 : Nat) : ZMod 1009) else 0) *
            (if f (r.1 + 1 + j) c.1 then (1 : ZMod 1009) else 0) = 0 := by
        apply Finset.sum_eq_zero; intro j _
        simp [show ¬ (r.1 + 1 + j ≤ r.1) by omega]
      rw [hz, add_zero]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      have hr_mem : r.1 < bMat.length := by omega
      simp only [show i ≤ r.1 by omega, ↓reduceIte]
      rw [List.getD_eq_getElem bMat [] hr_mem]
    rw [hsplit_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [mul_ite, mul_one, mul_zero, Nat.cast_ite, Nat.cast_zero]
  have hut : (B * M).IsUpperTriangular := by
    intro r c hcr
    have hcr' : c.1 < r.1 := hcr
    rw [hprod_entry r c (by omega)]
    have h0 := (hsound.2 r.1 (by omega)).2.2.1 c.1 (by rw [hcols_len]; omega) (by simpa using hcr')
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero h0
  have hdiag : ∀ r : Fin k, (B * M) r r ≠ 0 := by
    intro r
    rw [hprod_entry r r le_rfl]
    have hne := (hsound.2 r.1 (by omega)).2.2.2 (by rw [hcols_len]; simp; omega)
    intro hdvd
    rw [ZMod.natCast_eq_zero_iff] at hdvd
    exact hne (by simpa using Nat.mod_eq_zero_of_dvd hdvd)
  have hdet_bm : (B * M).det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular hut, Finset.prod_ne_zero_iff]
    intro r _
    exact hdiag r
  rw [Matrix.det_mul] at hdet_bm
  exact right_ne_zero_of_mul hdet_bm

def perm8A : Nat → Nat
  | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 6 | 4 => 5 | 5 => 3 | 6 => 7 | 7 => 1 | n => n

def invPerm8A : Nat → Nat
  | 0 => 2 | 1 => 7 | 2 => 0 | 3 => 5 | 4 => 1 | 5 => 4 | 6 => 3 | 7 => 6 | n => n

def perm8C : Nat → Nat
  | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 5 | 4 => 6 | 5 => 7 | 6 => 3 | 7 => 1 | n => n

def invPerm8C : Nat → Nat
  | 0 => 0 | 1 => 7 | 2 => 1 | 3 => 6 | 4 => 2 | 5 => 3 | 6 => 4 | 7 => 5 | n => n

def ePermA (k : Nat) (hk : 8 ≤ k) : Fin k ≃ Fin k where
  toFun i := ⟨perm8A i.1, by rcases i with ⟨i, hi⟩; match i with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp [perm8A]; omega | n + 8 => simp [perm8A]; omega⟩
  invFun i := ⟨invPerm8A i.1, by rcases i with ⟨i, hi⟩; match i with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp [invPerm8A]; omega | n + 8 => simp [invPerm8A]; omega⟩
  left_inv i := by rcases i with ⟨i, hi⟩; match i with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl | n + 8 => rfl
  right_inv i := by rcases i with ⟨i, hi⟩; match i with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl | n + 8 => rfl

def ePermC (k : Nat) (hk : 8 ≤ k) : Fin k ≃ Fin k where
  toFun i := ⟨perm8C i.1, by rcases i with ⟨i, hi⟩; match i with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp [perm8C]; omega | n + 8 => simp [perm8C]; omega⟩
  invFun i := ⟨invPerm8C i.1, by rcases i with ⟨i, hi⟩; match i with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp [invPerm8C]; omega | n + 8 => simp [invPerm8C]; omega⟩
  left_inv i := by rcases i with ⟨i, hi⟩; match i with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl | n + 8 => rfl
  right_inv i := by rcases i with ⟨i, hi⟩; match i with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl | n + 8 => rfl

def eEvenOdd (k : Nat) : Fin k ⊕ Fin k ≃ Fin (2 * k) where
  toFun
    | Sum.inl r => ⟨2 * r.1, by omega⟩
    | Sum.inr r => ⟨2 * r.1 + 1, by omega⟩
  invFun i :=
    if i.1 % 2 = 0 then Sum.inl ⟨i.1 / 2, by omega⟩
    else Sum.inr ⟨i.1 / 2, by omega⟩
  left_inv x := by
    rcases x with r | r
    · simp only [Nat.mul_mod_right, ↓reduceIte]; congr 1; ext; dsimp; omega
    · simp only [show (2 * r.1 + 1) % 2 ≠ 0 by omega, ↓reduceIte]; congr 1; ext; dsimp; omega
  right_inv i := by
    ext
    dsimp only []
    split_ifs <;> dsimp <;> omega

def eOddRow (k : Nat) : (Unit ⊕ Fin k) ⊕ Fin k ≃ Fin (2 * k + 1) where
  toFun
    | Sum.inl (Sum.inl ()) => ⟨0, by omega⟩
    | Sum.inl (Sum.inr r) => ⟨2 * r.1 + 1, by omega⟩
    | Sum.inr r => ⟨2 * r.1 + 2, by omega⟩
  invFun i :=
    if h1 : i.1 = 0 then Sum.inl (Sum.inl ())
    else if h2 : i.1 % 2 = 1 then Sum.inl (Sum.inr ⟨i.1 / 2, by have := i.isLt; omega⟩)
    else Sum.inr ⟨i.1 / 2 - 1, by have := i.isLt; omega⟩
  left_inv x := by
    rcases x with ⟨⟨⟩ | r⟩ | r
    · simp
    · dsimp only []
      rw [dif_neg (by omega), dif_pos (by omega)]
      congr 2; ext; dsimp; omega
    · dsimp only []
      rw [dif_neg (by omega), dif_neg (by omega)]
      congr 1; ext; dsimp; omega
  right_inv i := by
    ext
    dsimp only []
    split_ifs <;> dsimp <;> omega

def swapTail (k : Nat) : (Unit ⊕ Fin k) ⊕ Fin k ≃ (Unit ⊕ Fin k) ⊕ Fin k where
  toFun
    | Sum.inl (Sum.inl ()) => Sum.inl (Sum.inl ())
    | Sum.inl (Sum.inr r) => Sum.inr r
    | Sum.inr r => Sum.inl (Sum.inr r)
  invFun
    | Sum.inl (Sum.inl ()) => Sum.inl (Sum.inl ())
    | Sum.inl (Sum.inr r) => Sum.inr r
    | Sum.inr r => Sum.inl (Sum.inr r)
  left_inv x := by rcases x with ⟨⟨⟩ | r⟩ | r <;> rfl
  right_inv x := by rcases x with ⟨⟨⟩ | r⟩ | r <;> rfl

theorem not_prime_two_mul_ge_two {m : Nat} (hm : 2 ≤ m) : ¬ Nat.Prime (2 * m) := by
  intro hp
  rcases hp.eq_one_or_self_of_dvd 2 (dvd_mul_right 2 m) with h | h <;> omega

theorem det_primeMatrix_even (k : Nat) (hk : 8 ≤ k) (hk200 : k ≤ 200)
    (hA : (Matrix.of fun (i j : Fin k) =>
        if Nat.Prime (2 * i.1 + 2 * j.1 + 3) then (1 : ZMod 1009) else 0).det ≠ 0) :
    (OeisA69191.primeMatrix (ZMod 1009) (2 * k)).det ≠ 0 := by
  have : Fact (Nat.Prime 1009) := ⟨by norm_num⟩
  let A : Matrix (Fin k) (Fin k) (ZMod 1009) :=
    Matrix.of fun i j => if Nat.Prime (2 * i.1 + 2 * j.1 + 3) then 1 else 0
  let M := OeisA69191.primeMatrix (ZMod 1009) (2 * k)
  let e1 := eEvenOdd k
  let e2 := (Equiv.sumComm (Fin k) (Fin k)).trans (eEvenOdd k)
  let B := Matrix.of fun (r c : Fin k) => M (e1 (Sum.inl r)) (e2 (Sum.inr c))
  have hsub : M.submatrix e1 e2 = Matrix.fromBlocks A.transpose B 0 A := by
    ext x y
    rcases x with r | r <;> rcases y with c | c
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, Matrix.transpose_apply,
        M, A, e1, e2, eEvenOdd, Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.sumComm_apply,
        Sum.swap_inl, OeisA69191.primeMatrix, Matrix.of_apply]
      have hidx : 2 * r.1 + (2 * c.1 + 1) + 2 = 2 * c.1 + 2 * r.1 + 3 := by omega
      simp only [hidx]
    · simp [B]
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,
        M, e1, e2, eEvenOdd, Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.sumComm_apply,
        Sum.swap_inl, OeisA69191.primeMatrix]
      have hnp : ¬ Nat.Prime (2 * r.1 + 1 + (2 * c.1 + 1) + 2) := by
        have hidx : 2 * r.1 + 1 + (2 * c.1 + 1) + 2 = 2 * (r.1 + c.1 + 2) := by omega
        rw [hidx]
        exact not_prime_two_mul_ge_two (by omega)
      simp [hnp]
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂,
        M, A, e1, e2, eEvenOdd, Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.sumComm_apply,
        Sum.swap_inr, OeisA69191.primeMatrix, Matrix.of_apply]
      have hidx : 2 * r.1 + 1 + 2 * c.1 + 2 = 2 * r.1 + 2 * c.1 + 3 := by omega
      simp only [hidx]
  have hdet_sub : (M.submatrix e1 e2).det ≠ 0 := by
    rw [hsub, Matrix.det_fromBlocks_zero₂₁, Matrix.det_transpose]
    exact mul_ne_zero hA hA
  have hperm : M.submatrix e1 e2 = (M.submatrix e1 e1).submatrix id (Equiv.sumComm (Fin k) (Fin k)) := by
    ext x y; rfl
  rw [hperm, Matrix.det_permute', Matrix.det_submatrix_equiv_self] at hdet_sub
  exact right_ne_zero_of_mul hdet_sub

theorem det_primeMatrix_odd (k : Nat) (hk : 8 ≤ k) (hk199 : k ≤ 199)
    (hC : (Matrix.of fun (i j : Fin k) =>
        if Nat.Prime (2 * i.1 + 2 * j.1 + 5) then (1 : ZMod 1009) else 0).det ≠ 0) :
    (OeisA69191.primeMatrix (ZMod 1009) (2 * k + 1)).det ≠ 0 := by
  have : Fact (Nat.Prime 1009) := ⟨by norm_num⟩
  let C : Matrix (Fin k) (Fin k) (ZMod 1009) :=
    Matrix.of fun i j => if Nat.Prime (2 * i.1 + 2 * j.1 + 5) then 1 else 0
  let M := OeisA69191.primeMatrix (ZMod 1009) (2 * k + 1)
  let e1 := eOddRow k
  let e2 := (swapTail k).trans (eOddRow k)
  let v : Matrix (Fin k) Unit (ZMod 1009) := Matrix.of fun r _ => M (e1 (Sum.inl (Sum.inr r))) (e2 (Sum.inl (Sum.inl ())))
  let TL : Matrix (Unit ⊕ Fin k) (Unit ⊕ Fin k) (ZMod 1009) := Matrix.fromBlocks 1 0 v C
  let TR : Matrix (Unit ⊕ Fin k) (Fin k) (ZMod 1009) := Matrix.of fun x c => M (e1 (Sum.inl x)) (e2 (Sum.inr c))
  have hsub : M.submatrix e1 e2 = Matrix.fromBlocks TL TR 0 C.transpose := by
    ext x y
    rcases x with ⟨⟨⟩ | r⟩ | r <;> rcases y with ⟨⟨⟩ | c⟩ | c
    · simp [TL, M, e1, e2, eOddRow, swapTail, OeisA69191.primeMatrix, Nat.prime_two]
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.zero_apply, TL, M, e1, e2, eOddRow, swapTail, Equiv.trans_apply, Equiv.coe_fn_mk,
        OeisA69191.primeMatrix]
      have hnp : ¬ Nat.Prime (0 + (2 * c.1 + 2) + 2) := by
        have hidx : 0 + (2 * c.1 + 2) + 2 = 2 * (c.1 + 2) := by omega
        rw [hidx]
        exact not_prime_two_mul_ge_two (by omega)
      simpa using hnp
    · simp [TR]
    · simp [TL, v]
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂,
        TL, M, C, e1, e2, eOddRow, swapTail, Equiv.trans_apply, Equiv.coe_fn_mk,
        OeisA69191.primeMatrix, Matrix.of_apply]
      have hidx : 2 * r.1 + 1 + (2 * c.1 + 2) + 2 = 2 * r.1 + 2 * c.1 + 5 := by omega
      simp only [hidx]
    · simp [TR]
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,
        M, e1, e2, eOddRow, swapTail, Equiv.trans_apply, Equiv.coe_fn_mk,
        OeisA69191.primeMatrix]
      have hnp : ¬ Nat.Prime (2 * r.1 + 2 + 0 + 2) := by
        have hidx : 2 * r.1 + 2 + 0 + 2 = 2 * (r.1 + 2) := by omega
        rw [hidx]
        exact not_prime_two_mul_ge_two (by omega)
      simpa using hnp
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,
        M, e1, e2, eOddRow, swapTail, Equiv.trans_apply, Equiv.coe_fn_mk,
        OeisA69191.primeMatrix]
      have hnp : ¬ Nat.Prime (2 * r.1 + 2 + (2 * c.1 + 2) + 2) := by
        have hidx : 2 * r.1 + 2 + (2 * c.1 + 2) + 2 = 2 * (r.1 + c.1 + 3) := by omega
        rw [hidx]
        exact not_prime_two_mul_ge_two (by omega)
      simp [hnp]
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply,
        M, C, e1, e2, eOddRow, swapTail, Equiv.trans_apply, Equiv.coe_fn_mk,
        OeisA69191.primeMatrix, Matrix.of_apply]
      have hidx : 2 * r.1 + 2 + (2 * c.1 + 1) + 2 = 2 * c.1 + 2 * r.1 + 5 := by omega
      simp only [hidx]
  have hdet_tl : TL.det = C.det := by
    simp only [TL, Matrix.det_fromBlocks_zero₁₂]
    have h1 : (1 : Matrix Unit Unit (ZMod 1009)).det = 1 := by simp
    rw [h1, one_mul]
  have hdet_sub : (M.submatrix e1 e2).det ≠ 0 := by
    rw [hsub, Matrix.det_fromBlocks_zero₂₁, hdet_tl, Matrix.det_transpose]
    exact mul_ne_zero hC hC
  have hperm : M.submatrix e1 e2 = (M.submatrix e1 e1).submatrix id (swapTail k) := by
    ext x y; rfl
  rw [hperm, Matrix.det_permute', Matrix.det_submatrix_equiv_self] at hdet_sub
  exact right_ne_zero_of_mul hdet_sub

theorem a_pos_of_det_zmod_ne_zero (n : Nat)
    (hdet : (OeisA69191.primeMatrix (ZMod 1009) n).det ≠ 0) :
    OeisA228552.a n > 0 := by
  have hmap : OeisA69191.primeMatrix (ZMod 1009) n =
      (Int.castRingHom (ZMod 1009)).mapMatrix (OeisA69191.primeMatrix ℤ n) := by
    ext i j
    simp only [OeisA69191.primeMatrix, RingHom.mapMatrix_apply, Matrix.map_apply]
    split_ifs <;> simp
  rw [hmap, ← RingHom.map_det] at hdet
  have hne : OeisA69191.a n ≠ 0 := by
    intro h0
    apply hdet
    rw [OeisA69191.a] at h0
    rw [h0, map_zero]
  rw [OeisA228552.a]
  exact Nat.sqrt_pos.mpr (Int.natAbs_pos.mpr hne)

def bRowA_0 : List Nat := List.flatten [[1]]
def bRowA_1 : List Nat := List.flatten [[0,1]]
def bRowA_2 : List Nat := List.flatten [[1008,1008,1]]
def bRowA_3 : List Nat := List.flatten [[1,1,1007,1]]
def bRowA_4 : List Nat := List.flatten [[504,505,1008,505,1]]
def bRowA_5 : List Nat := List.flatten [[1008,1,1007,0,2,1]]
def bRowA_6 : List Nat := List.flatten [[504,504,0,0,0,505,1]]
def bRowA_7 : List Nat := List.flatten [[673,672,0,0,0,336,672,1]]
def bRowA_8 : List Nat := List.flatten [[503,0,1008,0,1,505,0,505,1]]
def bRowA_9 : List Nat := List.flatten [[1007,1008,671,1,338,672,0,674,338,1]]
def bRowA_10 : List Nat := List.flatten [[917,459,91,551,917,642,1,732,918,551,1]]
def bRowA_11 : List Nat := List.flatten [[252,0,2,755,252,757,756,1,1008,756,756,1]]
def bRowA_12 : List Nat := List.flatten [[707,337,739,236,706,975,773,538,471,437,774,201,1]]
def bRowA_13 : List Nat := List.flatten [[567,756,253,819,190,64,190,756,756,820,567,1,377,1]]
def bRowA_14 : List Nat := List.flatten [[3,4,1004,3,1008,1008,1006,1007,0,1007,2,1005,5,1,1]]
def bRowA_15 : List Nat := List.flatten [[651,197,811,718,294,260,293,193,195,455,651,747,359,750,1,1]]
def bRowA_16 : List Nat := List.flatten [[72,937,721,577,648,144,432,792,505,792,217,576,289,360,361,504],[1]]
def bRowA_17 : List Nat := List.flatten [[848,603,321,493,773,910,688,256,432,330,851,934,248,184,88,85],[3,1]]
def bRowA_18 : List Nat := List.flatten [[265,726,674,0,448,885,335,647,697,158,682,687,461,237,530,114],[921,813,1]]
def bRowA_19 : List Nat := List.flatten [[766,916,836,0,1008,771,173,837,345,993,629,812,151,64,698,705],[433,790,879,1]]
def bRowA_20 : List Nat := List.flatten [[270,13,248,1008,43,949,761,654,107,25,182,285,709,352,204,237],[423,234,954,967,1]]
def bRowA_21 : List Nat := List.flatten [[302,122,365,144,232,348,643,450,194,953,912,353,600,105,56,965],[168,164,512,634,866,1]]
def bRowA_22 : List Nat := List.flatten [[396,540,577,291,542,693,658,1008,432,721,301,291,942,138,281,241],[340,736,420,960,493,784,1]]
def bRowA_23 : List Nat := List.flatten [[845,582,648,156,49,1002,490,782,636,965,939,131,311,404,377,490],[216,53,46,628,677,833,962,1]]
def bRowA_24 : List Nat := List.flatten [[672,567,864,395,241,991,840,717,508,687,717,471,742,516,374,619],[403,213,196,763,1004,390,76,147,1]]
def bRowA_25 : List Nat := List.flatten [[625,753,414,311,680,357,605,629,383,352,794,38,510,382,933,191],[683,579,126,880,551,862,872,280,199,1]]
def bRowA_26 : List Nat := List.flatten [[64,374,709,339,281,517,815,387,339,177,201,864,791,465,421,416],[604,895,655,683,965,295,810,227,252,663,1]]
def bRowA_27 : List Nat := List.flatten [[460,228,216,856,668,966,131,211,257,206,926,209,802,145,753,416],[421,350,180,353,608,456,803,478,882,954,596,1]]
def bRowA_28 : List Nat := List.flatten [[392,850,916,730,548,149,415,586,644,269,762,199,855,697,289,208],[120,975,170,540,602,12,335,463,55,529,523,698,1]]
def bRowA_29 : List Nat := List.flatten [[689,963,917,533,163,914,283,795,307,995,731,830,655,631,492,755],[117,384,670,909,908,356,585,587,381,285,845,933,38,1]]
def bRowA_30 : List Nat := List.flatten [[765,39,370,151,535,792,691,231,666,828,245,76,503,189,966,56],[931,332,621,152,881,489,645,654,506,501,194,466,104,760,1]]
def bRowA_31 : List Nat := List.flatten [[434,648,212,354,382,200,689,946,688,596,181,170,573,380,725,520],[424,702,540,893,403,834,784,854,647,714,137,77,58,242,817,1]]
def bRowA_32 : List Nat := List.flatten [[228,987,763,373,364,847,891,663,204,288,527,343,315,418,284,328],[245,411,623,529,536,326,632,280,375,937,652,426,670,36,369,342],[1]]
def bRowA_33 : List Nat := List.flatten [[713,785,492,193,949,968,892,471,187,959,810,87,772,422,324,561],[338,925,351,580,539,654,657,698,829,454,19,931,637,909,342,824],[353,1]]
def bRowA_34 : List Nat := List.flatten [[912,891,281,1001,613,503,609,281,535,505,974,111,173,890,928,296],[41,28,533,873,282,112,238,342,346,140,815,847,245,16,774,258],[344,691,1]]
def bRowA_35 : List Nat := List.flatten [[417,62,264,972,158,12,242,415,956,569,19,226,363,17,866,970],[960,260,881,486,97,656,731,156,648,317,783,597,578,817,147,264],[39,774,321,1]]
def bRowA_36 : List Nat := List.flatten [[1004,312,634,454,501,59,916,881,174,895,199,332,629,829,787,804],[331,641,676,395,891,782,413,267,777,460,171,239,100,183,759,961],[801,44,176,802,1]]
def bRowA_37 : List Nat := List.flatten [[950,992,278,213,449,953,169,942,849,353,620,934,910,841,390,1005],[629,432,467,117,609,491,707,865,635,113,26,632,34,108,272,1004],[544,446,992,963,265,1]]
def bRowA_38 : List Nat := List.flatten [[930,839,26,50,740,722,270,232,66,319,885,996,623,935,635,15],[669,305,472,147,18,123,510,111,254,930,646,920,824,625,821,735],[810,76,506,865,733,339,1]]
def bRowA_39 : List Nat := List.flatten [[209,474,363,911,327,872,823,800,802,212,335,252,16,186,551,433],[273,245,644,233,662,85,149,270,332,941,40,881,235,917,448,241],[168,818,947,351,348,743,372,1]]
def bRowA_40 : List Nat := List.flatten [[799,734,969,321,782,425,997,538,70,402,300,561,72,786,360,29],[538,45,542,141,859,684,119,16,769,12,958,63,290,525,951,486],[439,635,14,559,803,187,751,497,1]]
def bRowA_41 : List Nat := List.flatten [[33,367,125,0,23,433,304,25,357,990,642,560,458,798,822,995],[193,827,604,504,609,478,863,583,211,491,372,408,215,970,940,730],[728,905,638,540,259,748,870,956,348,1]]
def bRowA_42 : List Nat := List.flatten [[628,282,592,411,44,34,680,562,771,295,640,843,732,289,90,655],[377,720,799,627,64,817,821,979,667,1007,702,1,863,119,766,123],[989,264,985,283,114,877,367,821,685,624,1]]
def bRowA_43 : List Nat := List.flatten [[817,682,636,865,442,672,191,532,207,971,821,975,917,678,576,887],[517,401,515,724,695,190,734,724,716,65,155,429,404,105,441,121],[970,159,942,464,822,482,705,630,316,683,135,1]]
def bRowA_44 : List Nat := List.flatten [[749,241,725,41,685,849,840,1,836,68,503,829,976,824,34,140],[160,397,86,814,676,475,906,977,640,73,910,665,760,593,806,924],[501,55,368,842,551,443,719,469,653,944,675,377,1]]
def bRowA_45 : List Nat := List.flatten [[483,987,721,808,292,45,60,189,750,667,439,768,824,707,863,918],[220,602,738,230,187,909,403,524,199,534,111,133,153,748,602,712],[449,400,840,510,103,487,340,389,394,291,681,218,609,1]]
def bRowA_46 : List Nat := List.flatten [[749,859,316,15,487,97,577,731,380,714,268,854,747,826,358,285],[217,675,291,780,263,226,351,772,521,279,492,466,168,441,224,331],[887,952,359,604,158,363,944,302,881,86,231,934,923,959,1]]
def bRowA_47 : List Nat := List.flatten [[488,741,32,518,316,169,25,326,49,939,558,691,1,518,629,746],[255,232,367,481,922,434,371,528,143,110,836,943,298,322,195,753],[499,767,162,169,221,367,569,943,459,238,812,804,356,762,96,1]]
def bRowA_48 : List Nat := List.flatten [[595,914,303,451,803,2,915,319,269,653,45,355,968,152,546,335],[981,42,342,983,258,454,635,873,674,723,901,659,44,747,515,781],[747,346,273,430,547,50,826,976,988,524,475,668,342,554,392,892],[1]]
def bRowA_49 : List Nat := List.flatten [[371,672,71,341,354,676,230,907,976,607,50,478,815,476,999,249],[122,457,263,282,937,155,364,645,806,745,64,528,139,758,258,849],[922,40,391,947,244,354,490,937,796,621,12,950,822,774,732,841],[693,1]]
def bRowA_50 : List Nat := List.flatten [[820,547,185,783,557,685,389,712,839,324,739,612,883,785,172,582],[290,264,656,476,415,5,408,377,621,674,884,615,906,283,46,651],[342,858,654,42,26,498,786,846,180,91,481,465,462,659,629,990],[161,486,1]]
def bRowA_51 : List Nat := List.flatten [[197,84,748,869,128,437,67,239,638,992,653,500,428,857,561,218],[307,725,337,953,893,920,441,758,726,683,916,962,672,843,452,546],[425,660,761,694,481,796,602,42,122,185,609,676,298,303,466,544],[723,933,996,1]]
def bRowA_52 : List Nat := List.flatten [[754,166,187,801,576,299,977,932,606,13,986,519,562,209,121,559],[914,823,990,144,576,483,297,693,970,609,640,576,462,795,744,401],[169,950,737,219,26,465,578,59,172,468,368,990,553,129,853,789],[299,873,378,435,1]]
def bRowA_53 : List Nat := List.flatten [[720,877,197,242,751,941,124,831,593,844,306,116,660,644,364,575],[592,595,751,666,308,380,471,492,23,621,475,952,966,400,560,550],[830,411,176,703,893,211,461,745,303,418,33,58,832,400,628,960],[171,673,171,482,356,1]]
def bRowA_54 : List Nat := List.flatten [[163,787,619,934,714,856,77,742,640,725,408,3,924,800,921,210],[1000,253,452,819,32,727,530,597,610,584,904,200,555,749,675,871],[31,45,700,368,657,902,588,637,264,192,235,743,247,188,237,796],[250,991,503,186,262,496,1]]
def bRowA_55 : List Nat := List.flatten [[531,468,294,741,473,683,728,592,412,121,100,57,582,640,463,347],[256,395,897,242,631,835,705,679,579,775,30,386,669,441,529,638],[774,25,166,960,601,630,574,111,116,786,607,329,66,536,315,266],[975,854,553,66,680,294,346,1]]
def bRowA_56 : List Nat := List.flatten [[890,123,893,297,981,843,304,657,251,402,417,85,286,693,174,561],[9,609,773,814,85,85,824,716,492,612,599,164,973,609,902,372],[551,353,822,303,556,255,563,475,126,362,380,665,333,748,735,451],[410,212,718,399,345,80,551,390,1]]
def bRowA_57 : List Nat := List.flatten [[164,722,915,345,43,538,647,746,854,189,884,229,273,625,515,653],[16,88,944,247,890,406,727,674,801,519,897,320,732,29,108,90],[465,5,985,466,467,291,488,342,788,329,124,746,77,730,410,835],[913,1007,406,302,800,242,391,578,148,1]]
def bRowA_58 : List Nat := List.flatten [[503,882,555,878,872,745,331,380,600,808,81,1007,702,697,142,666],[189,934,88,655,293,365,522,669,182,405,862,881,972,857,944,231],[956,938,762,759,670,644,213,352,999,610,484,2,359,628,642,69],[330,39,242,623,564,675,216,174,774,760,1]]
def bRowA_59 : List Nat := List.flatten [[598,240,390,166,361,42,654,489,129,297,695,826,750,945,271,313],[650,54,972,261,777,530,122,304,159,410,644,446,797,636,178,879],[788,749,304,103,821,125,662,209,814,116,654,197,669,738,1004,11],[76,758,116,351,938,730,291,876,63,606,507,1]]
def bRowA_60 : List Nat := List.flatten [[535,702,279,930,106,558,101,145,739,673,916,656,95,917,818,442],[954,457,316,867,981,85,373,587,33,360,933,1000,473,406,884,161],[42,26,775,771,864,734,806,965,521,306,826,644,7,568,931,949],[368,331,338,932,4,437,954,342,273,875,937,1008,1]]
def bRowA_61 : List Nat := List.flatten [[1005,660,658,912,724,142,355,286,803,509,260,627,835,52,77,855],[469,488,59,410,175,123,972,847,53,576,659,543,242,17,725,997],[580,368,791,837,962,958,363,263,856,632,236,744,877,706,981,177],[778,814,513,527,18,196,77,477,393,874,706,950,285,1]]
def bRowA_62 : List Nat := List.flatten [[476,194,716,726,769,40,478,126,491,494,397,991,586,550,760,528],[892,105,452,77,222,875,544,179,557,892,477,686,228,94,277,624],[814,996,129,576,273,664,806,821,253,232,884,844,440,103,945,181],[671,688,148,601,809,116,629,633,578,625,29,706,454,6,1]]
def bRowA_63 : List Nat := List.flatten [[419,204,111,670,150,1003,872,415,487,258,192,807,890,567,152,430],[864,293,995,2,475,286,322,728,453,960,641,699,20,766,372,861],[998,783,793,304,803,620,277,114,673,785,938,395,639,255,667,630],[57,408,664,319,487,981,128,1006,856,305,325,475,319,650,103,1]]
def bRowA_64 : List Nat := List.flatten [[265,752,740,644,750,117,877,735,280,111,6,307,626,305,956,399],[288,174,149,226,1008,42,13,152,139,307,295,385,245,291,152,439],[895,351,883,733,644,788,652,255,64,56,734,329,449,878,97,919],[924,189,868,446,843,175,778,472,416,20,45,726,693,873,182,145],[1]]
def bRowA_65 : List Nat := List.flatten [[964,540,506,636,372,657,35,688,518,212,824,279,611,723,86,665],[675,1007,893,526,134,159,477,522,865,238,14,453,555,376,275,614],[166,982,506,627,903,405,780,190,165,148,629,993,736,964,71,842],[411,685,210,95,517,549,803,193,901,206,631,338,199,685,379,817],[963,1]]
def bRowA_66 : List Nat := List.flatten [[294,900,48,359,940,171,621,222,282,37,623,637,83,830,478,680],[851,467,958,145,436,170,565,33,797,874,222,101,598,494,153,303],[103,743,260,655,322,403,24,634,94,642,106,420,666,922,178,415],[838,202,39,440,81,742,576,646,758,225,739,823,685,731,428,730],[191,909,1]]
def bRowA_67 : List Nat := List.flatten [[745,290,937,456,595,41,631,518,764,440,22,958,110,981,783,841],[333,629,445,388,586,361,294,1004,607,656,896,877,812,935,248,12],[357,277,145,263,526,396,864,761,460,749,842,789,591,716,444,635],[312,540,673,445,641,75,289,159,667,680,564,504,945,93,850,813],[135,718,897,1]]
def bRowA_68 : List Nat := List.flatten [[215,597,860,181,898,460,362,940,301,828,639,954,33,776,785,267],[755,258,129,926,505,546,163,927,415,456,84,738,754,21,366,803],[735,739,243,427,819,683,514,941,239,344,976,691,365,891,181,700],[690,807,780,34,707,1005,134,770,919,999,5,685,271,469,356,144],[655,864,226,76,1]]
def bRowA_69 : List Nat := List.flatten [[306,361,912,404,455,829,333,774,500,801,813,35,730,62,907,106],[992,219,1001,991,13,616,83,934,866,33,39,646,469,391,612,962],[746,333,987,858,572,148,695,80,200,550,196,675,197,955,478,694],[813,873,12,596,219,329,938,985,793,55,374,685,437,813,218,89],[619,899,554,305,107,1]]
def bRowA_70 : List Nat := List.flatten [[225,96,806,769,892,69,124,272,627,344,806,172,364,433,513,123],[63,397,913,456,523,816,239,28,125,191,822,315,778,240,472,963],[380,379,812,899,883,879,554,536,15,404,638,469,668,705,958,689],[532,590,888,841,984,657,522,836,678,389,349,384,98,326,509,525],[935,68,31,894,433,880,1]]
def bRowA_71 : List Nat := List.flatten [[456,808,901,312,922,631,23,28,558,980,908,146,256,742,755,873],[452,568,136,920,157,841,499,877,777,800,94,104,211,548,421,968],[38,998,353,968,778,219,564,714,595,247,683,371,1006,775,661,496],[555,415,207,319,897,214,157,275,300,866,97,385,743,706,375,839],[866,431,982,574,141,529,367,1]]
def bRowA_72 : List Nat := List.flatten [[11,708,84,701,375,607,32,520,703,793,207,835,534,241,74,344],[346,921,521,238,321,605,949,772,531,948,413,84,372,656,813,973],[846,588,388,10,780,729,335,735,711,392,401,746,143,142,602,614],[699,957,193,262,927,261,342,297,942,83,202,710,47,763,172,879],[217,284,803,187,914,619,564,677,1]]
def bRowA_73 : List Nat := List.flatten [[523,125,141,546,639,663,449,983,34,409,500,246,103,500,901,504],[975,145,489,993,416,290,433,159,91,262,354,211,403,201,144,836],[157,680,577,776,63,600,933,341,370,311,379,708,210,504,330,532],[120,94,19,735,982,325,145,370,940,711,977,562,549,207,761,982],[790,879,218,883,218,792,720,351,663,1]]
def bRowA_74 : List Nat := List.flatten [[350,799,854,727,813,364,586,137,298,345,353,179,103,689,286,414],[520,549,488,317,524,838,515,935,941,397,825,685,67,680,983,895],[505,227,18,576,498,417,639,528,276,572,7,766,296,657,367,791],[1006,213,443,454,327,790,718,216,654,908,535,25,579,575,456,515],[203,10,68,49,328,179,500,400,976,324,1]]
def bRowA_75 : List Nat := List.flatten [[770,13,436,292,752,981,239,544,269,709,908,558,310,529,644,790],[932,812,84,234,554,193,50,868,121,314,279,563,208,35,477,218],[541,980,392,916,662,479,919,991,158,342,90,696,780,782,414,88],[390,476,865,423,265,18,920,913,743,1002,71,446,44,417,481,851],[297,721,343,566,288,888,799,445,313,219,735,1]]
def bRowA_76 : List Nat := List.flatten [[879,524,97,279,311,972,532,983,790,941,251,336,160,577,445,119],[27,362,629,887,98,374,817,806,840,446,807,166,370,518,197,813],[850,513,442,219,459,561,19,992,235,417,731,179,145,681,794,814],[760,415,793,930,720,94,466,609,260,585,224,687,258,92,844,480],[491,768,979,390,667,271,880,732,277,457,28,966,1]]
def bRowA_77 : List Nat := List.flatten [[614,384,801,193,636,945,731,950,676,694,924,468,943,23,697,627],[590,564,788,582,591,233,932,947,830,479,325,881,614,63,994,227],[1002,512,0,56,597,464,582,295,566,457,84,200,35,193,292,68],[456,397,719,778,927,864,637,159,352,445,597,675,612,840,927,125],[835,398,213,654,330,649,567,7,815,485,138,996,788,1]]
def bRowA_78 : List Nat := List.flatten [[349,624,936,517,928,769,101,463,221,557,336,436,361,4,175,996],[881,814,187,921,816,528,446,613,1008,690,393,698,159,523,215,206],[935,664,401,328,216,310,16,1,421,45,897,589,147,299,748,981],[609,714,875,820,629,992,956,203,97,591,228,704,127,620,774,953],[103,920,699,221,275,954,830,804,525,383,836,629,101,989,1]]
def bRowA_79 : List Nat := List.flatten [[953,869,582,435,738,49,419,109,551,558,892,959,49,844,755,669],[315,478,675,287,648,305,899,67,876,318,367,61,624,337,219,145],[368,382,70,573,552,589,963,904,791,474,390,406,912,377,104,309],[68,982,248,68,705,332,951,840,230,316,840,300,990,139,723,561],[366,860,71,461,99,865,617,339,486,522,264,127,479,855,907,1]]
def bRowA_80 : List Nat := List.flatten [[799,559,423,926,331,609,850,841,239,132,556,772,628,590,987,344],[292,593,987,834,715,401,640,45,930,397,810,90,927,699,685,809],[113,672,176,23,522,643,424,799,855,912,132,309,541,806,507,489],[269,699,537,456,313,566,55,493,821,503,839,465,598,497,223,715],[649,120,484,893,867,553,600,503,596,138,965,621,883,467,254,425],[1]]
def bRowA_81 : List Nat := List.flatten [[516,925,727,990,194,86,892,546,259,936,200,801,96,30,266,471],[540,808,571,289,906,776,642,484,137,500,731,597,846,481,249,870],[925,115,631,863,910,253,944,511,714,993,427,696,883,471,636,942],[634,289,235,462,535,762,284,340,573,443,559,851,906,137,516,800],[21,318,756,962,29,119,769,564,368,490,309,350,292,1001,574,734],[958,1]]
def bRowA_82 : List Nat := List.flatten [[436,282,626,795,558,456,28,413,1002,596,423,771,692,360,32,385],[888,911,544,964,178,572,28,113,501,227,853,860,808,982,389,649],[582,874,78,591,293,731,634,491,676,55,315,713,364,336,824,925],[657,514,894,364,414,473,677,660,995,788,206,770,699,892,58,600],[469,901,340,118,192,2,61,809,427,604,533,243,126,307,579,477],[468,623,1]]
def bRowA_83 : List Nat := List.flatten [[482,886,128,108,940,454,645,911,945,233,180,887,748,435,926,640],[460,489,708,784,766,176,889,303,951,704,80,60,826,534,954,781],[777,382,315,228,446,446,342,361,449,181,256,825,738,611,584,505],[278,341,850,200,421,671,796,669,232,433,910,248,848,464,50,583],[390,242,134,9,706,413,436,616,320,101,884,18,725,105,456,330],[533,813,548,1]]
def bRowA_84 : List Nat := List.flatten [[195,859,333,78,461,177,977,1005,82,361,219,758,727,520,56,79],[668,330,379,184,450,981,730,104,634,312,29,705,804,977,708,555],[238,946,836,202,337,947,39,842,369,721,635,788,189,574,252,881],[792,125,413,586,104,152,110,58,997,451,643,631,191,701,327,27],[553,867,892,120,961,580,436,441,483,278,297,443,361,105,141,48],[774,138,30,311,1]]
def bRowA_85 : List Nat := List.flatten [[34,726,875,931,764,431,313,168,252,45,232,728,694,631,434,218],[95,67,777,908,163,12,624,588,136,446,285,680,659,592,195,180],[69,546,32,206,519,334,951,452,152,16,767,740,497,224,675,8],[817,695,269,531,1001,488,1,415,45,48,817,641,300,926,611,27],[889,340,345,720,183,795,402,539,554,705,183,45,642,980,207,214],[449,202,527,634,724,1]]
def bRowA_86 : List Nat := List.flatten [[342,898,272,691,928,571,947,1003,548,713,130,1005,444,48,180,864],[907,322,343,367,272,745,455,6,89,1002,688,289,676,433,287,630],[683,988,632,236,542,313,757,631,591,194,601,247,225,194,133,979],[312,170,575,600,307,411,106,171,774,160,176,993,113,245,221,107],[360,185,485,4,92,522,577,421,188,589,945,707,433,64,363,129],[503,255,766,868,292,36,1]]
def bRowA_87 : List Nat := List.flatten [[574,716,113,652,860,73,377,439,24,947,789,852,17,616,220,584],[53,189,42,143,342,317,283,854,145,132,634,661,166,149,764,706],[164,171,487,19,443,358,410,596,643,151,531,427,157,891,864,580],[5,975,190,558,25,574,535,48,917,709,83,603,524,770,775,766],[747,825,309,89,921,264,796,1003,78,198,784,152,116,727,720,371],[346,293,584,477,856,299,571,1]]
def bRowA_88 : List Nat := List.flatten [[413,325,78,183,93,380,548,74,481,92,305,356,667,695,876,687],[405,901,746,619,803,407,614,48,376,638,59,175,288,863,382,542],[752,375,989,7,487,678,964,37,593,276,726,396,809,14,464,671],[155,907,2,520,973,604,422,646,590,483,133,638,900,281,490,8],[599,438,304,296,180,231,608,486,622,912,109,554,959,886,106,980],[835,216,705,346,842,58,905,904,1]]
def bRowA_89 : List Nat := List.flatten [[641,779,359,90,580,401,780,264,170,206,701,1006,464,781,939,638],[287,730,473,869,363,33,276,643,144,458,299,616,217,128,529,249],[786,167,270,580,755,524,969,277,48,718,575,978,234,680,259,266],[874,910,23,175,628,874,637,23,439,421,162,405,683,197,84,459],[266,506,751,759,13,142,239,839,997,997,135,304,658,169,543,631],[998,837,79,848,393,996,456,900,293,1]]
def bRowA_90 : List Nat := List.flatten [[10,127,327,20,708,675,221,861,678,183,698,888,433,899,633,1002],[441,938,337,915,669,878,857,272,378,726,388,876,664,308,609,10],[55,496,718,483,277,887,327,710,850,118,945,747,618,713,241,298],[462,139,265,994,222,186,131,423,641,247,315,1000,303,288,973,110],[243,168,43,881,220,971,5,949,176,268,727,735,193,189,928,49],[758,176,851,824,972,850,56,237,579,707,1]]
def bRowA_91 : List Nat := List.flatten [[207,776,841,126,535,793,608,544,178,626,852,253,805,656,288,723],[112,297,503,21,851,938,90,917,514,525,803,421,761,20,343,38],[549,354,665,853,977,103,317,191,983,52,52,528,943,52,331,171],[315,302,334,62,915,227,501,289,121,184,668,280,154,735,535,611],[915,865,124,784,588,180,835,31,777,8,873,426,51,260,155,9],[122,311,65,436,652,478,353,160,57,303,49,1]]
def bRowA_92 : List Nat := List.flatten [[621,744,375,675,918,395,450,513,700,135,240,1008,743,528,827,85],[968,780,211,270,316,609,606,62,825,371,528,643,16,758,211,629],[86,750,310,462,977,398,929,188,407,978,708,35,697,601,83,871],[832,441,498,128,491,282,588,920,675,370,808,957,709,171,286,278],[304,65,393,404,57,355,699,554,570,842,988,653,436,867,693,351],[858,288,117,512,295,388,53,639,858,455,942,0,1]]
def bRowA_93 : List Nat := List.flatten [[721,558,934,207,407,954,692,49,870,235,84,310,1008,931,473,755],[124,321,629,987,759,88,1005,838,108,9,302,938,773,142,873,748],[898,933,355,553,878,897,387,889,397,54,533,455,428,948,825,266],[891,85,445,432,204,511,615,940,911,185,441,478,41,424,239,167],[948,147,32,311,382,841,22,534,607,369,108,961,607,529,1001,558],[107,746,821,499,233,777,966,72,440,947,780,398,531,1]]
def bRowA_94 : List Nat := List.flatten [[667,475,355,187,767,100,144,606,293,787,775,32,814,700,810,53],[927,360,163,141,106,968,153,228,358,934,204,70,514,194,923,369],[738,65,588,327,871,849,722,640,456,931,887,921,856,785,466,139],[684,3,32,655,533,683,261,407,303,334,196,223,522,435,916,187],[990,184,923,148,660,849,838,745,703,640,452,385,141,382,872,415],[191,206,68,467,131,95,825,452,329,756,237,335,217,142,1]]
def bRowA_95 : List Nat := List.flatten [[85,375,923,820,831,440,17,694,39,859,806,760,281,24,64,862],[122,115,191,788,762,877,798,340,430,842,966,865,613,652,590,973],[178,957,105,962,795,738,89,765,778,358,151,623,916,764,259,211],[111,408,106,682,99,900,230,434,376,542,303,266,505,303,718,224],[399,145,682,217,594,493,401,82,764,142,691,818,491,248,335,492],[499,106,642,376,477,799,859,710,551,112,970,376,696,987,237,1]]
def bRowA_96 : List Nat := List.flatten [[9,536,922,392,208,253,148,52,523,660,152,210,345,705,121,327],[689,322,959,422,306,768,138,662,644,286,470,928,754,592,383,145],[303,353,713,372,608,544,501,893,216,29,500,989,368,473,705,253],[900,972,528,683,634,306,498,866,246,476,266,355,107,141,388,481],[867,317,522,936,302,531,244,172,408,374,623,688,828,332,383,948],[238,956,869,934,1001,649,473,267,506,292,99,728,85,99,31,924],[1]]
def bRowA_97 : List Nat := List.flatten [[1000,622,716,245,849,719,815,977,120,735,84,340,621,416,977,505],[274,263,655,50,60,99,396,373,825,605,530,967,433,163,837,348],[86,41,389,530,447,2,628,93,945,337,928,22,1,911,97,833],[591,345,321,366,58,821,967,190,869,482,469,264,7,338,905,948],[277,68,849,387,512,341,476,819,193,915,942,617,335,841,418,861],[306,556,253,902,118,207,539,442,93,470,177,387,22,586,598,768],[575,1]]
def bRowA_98 : List Nat := List.flatten [[393,816,553,806,752,598,780,684,113,385,937,227,477,49,38,966],[129,680,10,353,324,601,1007,687,477,217,667,30,397,741,481,269],[400,644,35,299,380,783,663,724,491,807,467,542,586,472,956,920],[222,873,1007,692,874,818,313,611,820,586,888,940,712,386,759,417],[210,658,232,770,784,899,789,321,0,854,935,382,764,32,312,729],[763,19,272,491,296,937,398,347,329,409,145,249,308,1003,433,740],[992,630,1]]
def bRowA_99 : List Nat := List.flatten [[301,368,277,91,219,763,853,249,781,472,683,497,305,390,178,438],[200,104,919,247,125,693,166,328,537,491,210,244,681,282,325,763],[970,641,759,712,435,523,741,483,90,584,105,404,751,804,535,333],[901,115,47,762,991,414,538,483,802,254,788,647,961,769,145,165],[379,249,194,914,725,108,74,466,224,248,260,636,492,771,221,234],[252,574,10,517,67,872,249,279,627,537,581,578,599,210,324,803],[607,856,3,1]]
def bRowA_100 : List Nat := List.flatten [[646,450,903,485,981,974,474,654,482,201,300,295,872,51,512,560],[926,33,879,351,479,253,891,592,111,454,197,284,307,342,337,992],[26,914,352,26,667,171,152,58,674,840,924,345,488,676,80,416],[816,567,895,769,387,113,297,773,742,171,569,193,421,43,787,493],[247,869,124,885,624,609,969,577,973,863,594,681,163,896,208,707],[719,154,560,190,553,39,474,977,42,7,647,525,398,397,155,706],[432,735,294,244,1]]
def bRowA_101 : List Nat := List.flatten [[285,657,860,94,31,850,606,1007,236,57,640,460,454,630,203,256],[877,462,117,415,667,48,714,348,709,74,626,510,651,881,477,368],[622,911,360,550,220,903,768,763,239,482,27,524,483,710,862,876],[54,655,120,124,34,839,771,34,412,483,767,550,686,394,473,166],[107,695,864,615,159,239,1000,896,555,159,925,91,220,575,736,580],[838,426,457,375,835,163,864,123,288,598,794,105,48,890,401,787],[818,490,523,726,851,1]]
def bRowA_102 : List Nat := List.flatten [[345,313,145,352,557,564,345,434,163,848,1002,611,207,90,465,421],[708,948,52,53,258,505,953,404,791,994,473,444,286,591,510,344],[728,58,258,825,644,1008,645,991,349,339,485,498,204,356,150,855],[340,387,338,959,614,967,994,662,738,299,71,254,459,134,492,44],[696,333,32,253,397,319,324,890,845,617,570,709,460,336,221,107],[373,413,477,357,313,564,290,616,605,323,38,943,991,81,589,812],[1004,333,702,224,77,303,1]]
def bRowA_103 : List Nat := List.flatten [[872,226,521,627,375,144,189,648,384,334,938,72,117,55,43,145],[697,902,778,255,26,434,717,103,978,104,835,843,801,1006,199,220],[256,335,84,481,767,251,330,587,65,129,151,684,954,817,879,58],[453,346,137,303,781,857,817,30,306,269,591,437,318,536,878,553],[891,489,728,807,231,719,627,876,806,752,373,407,637,847,214,973],[134,881,101,583,547,625,518,91,643,719,585,288,476,665,127,811],[136,461,618,616,409,896,665,1]]
def bRowA_104 : List Nat := List.flatten [[843,177,648,531,534,17,18,40,651,501,230,954,859,748,71,729],[761,1003,893,736,104,891,506,460,464,700,639,362,318,736,318,205],[543,614,140,545,540,728,3,279,545,410,27,77,664,395,158,563],[980,11,558,554,823,645,560,1006,471,269,552,38,457,463,771,233],[786,758,554,672,469,582,0,271,950,685,798,988,973,648,554,358],[898,290,219,90,790,858,892,354,130,110,993,409,356,824,839,462],[943,233,97,540,59,752,762,873,1]]
def bRowA_105 : List Nat := List.flatten [[934,224,983,247,991,467,682,565,430,781,416,685,183,592,763,443],[790,46,146,38,620,991,692,108,576,183,937,677,617,152,917,101],[904,58,583,676,738,541,439,889,432,351,523,293,188,114,680,39],[554,108,137,898,484,598,617,967,771,99,587,446,472,852,431,527],[613,380,929,662,481,400,468,588,745,412,977,309,318,796,729,996],[276,738,249,306,747,217,889,913,98,439,430,877,880,934,630,924],[522,624,666,134,212,37,345,992,124,1]]
def bRowA_106 : List Nat := List.flatten [[100,148,348,263,95,91,378,743,590,975,446,491,800,111,254,757],[171,971,539,663,776,496,483,367,443,799,265,179,252,263,515,891],[77,984,849,967,912,190,877,494,659,879,75,128,796,210,912,448],[563,39,993,469,483,880,199,974,374,645,114,50,226,746,326,566],[147,996,484,812,574,121,701,131,58,45,222,701,12,121,711,423],[648,777,50,917,341,986,46,867,777,704,267,800,968,980,751,65],[226,562,192,755,70,252,418,14,422,19,1]]
def bRowA_107 : List Nat := List.flatten [[16,740,424,273,551,965,678,388,425,63,400,694,419,808,122,155],[1005,772,1008,434,328,508,356,362,839,501,208,327,973,639,513,296],[193,576,725,584,249,45,442,488,244,441,472,347,565,690,225,301],[907,704,405,0,383,197,492,200,906,255,274,503,507,859,603,858],[691,1001,810,18,607,108,184,943,33,970,920,433,863,491,126,841],[130,327,994,36,954,432,315,757,945,312,363,888,158,867,846,560],[412,661,169,831,875,122,648,48,578,775,898,1]]
def bRowA_108 : List Nat := List.flatten [[897,285,248,510,247,26,679,411,336,310,103,150,92,131,575,594],[955,930,62,436,427,457,197,186,221,305,367,6,773,296,2,753],[1005,468,161,545,786,190,282,729,228,161,11,748,631,485,851,198],[686,969,705,831,618,712,163,581,539,34,280,239,549,632,878,574],[821,497,865,430,263,853,755,265,934,57,214,605,460,460,1003,817],[266,824,332,646,853,959,292,75,741,93,629,352,725,852,111,350],[738,641,958,979,687,666,249,562,596,707,195,185,1]]
def bRowA_109 : List Nat := List.flatten [[539,954,742,5,483,495,985,722,444,966,919,675,124,562,151,338],[297,776,989,758,158,959,490,169,801,232,539,642,848,834,815,216],[67,271,942,130,903,477,904,613,398,668,1004,860,893,59,232,655],[522,458,908,745,172,375,493,819,104,447,519,262,41,656,807,164],[171,964,78,714,32,482,154,464,664,47,718,72,697,678,829,726],[391,822,687,815,611,557,265,16,30,764,346,67,581,902,403,253],[610,262,877,603,757,29,580,828,549,305,596,602,865,1]]
def bRowA_110 : List Nat := List.flatten [[350,527,143,17,170,637,313,109,1,520,881,432,649,943,381,799],[501,606,705,847,423,375,286,380,177,6,33,214,251,806,526,501],[529,730,990,106,554,23,800,483,143,302,844,7,344,351,308,501],[881,208,805,740,379,899,451,219,682,421,258,686,469,295,488,729],[22,875,797,552,693,675,805,133,757,893,310,843,241,386,779,1008],[998,431,402,679,203,119,586,529,370,838,1007,242,7,457,896,458],[776,958,672,745,300,748,447,605,513,664,319,844,960,253,1]]
def bRowA_111 : List Nat := List.flatten [[892,728,46,26,770,816,755,790,133,560,572,815,239,151,794,580],[703,304,593,20,765,38,502,386,925,149,823,620,13,831,107,241],[799,56,807,204,543,942,663,795,399,64,812,729,840,809,367,711],[972,599,495,377,45,817,175,416,884,343,694,800,899,802,44,645],[610,412,545,198,790,662,548,927,33,999,620,534,678,623,153,662],[834,473,549,320,780,413,179,765,693,553,714,174,485,677,236,181],[335,509,788,223,615,245,46,242,631,328,934,900,561,723,46,1]]
def bRowA_112 : List Nat := List.flatten [[986,467,334,72,390,625,747,652,66,964,815,884,292,477,854,711],[368,116,536,65,923,736,51,746,230,55,508,36,29,377,917,953],[782,115,930,641,426,346,53,145,159,698,697,77,791,3,558,93],[893,63,955,993,904,769,222,912,118,338,398,396,241,906,750,3],[409,559,169,487,604,577,355,979,63,323,732,291,705,379,798,987],[277,680,666,822,840,410,266,479,5,526,390,340,321,68,338,221],[695,150,60,909,361,834,544,859,653,4,451,885,491,196,456,795],[1]]
def bRowA_113 : List Nat := List.flatten [[554,560,673,297,88,47,325,721,80,217,256,328,676,827,257,35],[975,768,521,683,69,190,445,646,486,969,564,414,682,1008,383,1005],[221,139,576,541,782,699,672,656,777,990,935,383,814,666,959,691],[406,400,971,760,396,221,305,423,652,560,595,751,162,477,754,701],[116,804,570,941,1,463,35,478,10,748,275,829,994,454,828,168],[878,305,89,945,763,135,123,519,681,785,296,273,104,315,92,1002],[898,231,550,765,442,247,912,217,435,826,217,738,854,60,187,381],[624,1]]
def bRowA_114 : List Nat := List.flatten [[948,847,989,411,902,913,257,130,913,543,52,590,131,755,163,615],[615,92,766,506,234,626,569,860,84,756,366,674,321,545,721,635],[241,230,41,348,57,904,636,707,371,539,936,768,57,980,321,452],[590,213,996,739,835,787,467,894,850,29,388,709,348,629,934,803],[53,289,460,180,73,360,7,863,868,894,589,691,346,633,282,529],[624,482,979,272,696,109,666,107,58,288,547,315,802,771,997,55],[899,335,546,25,562,535,753,381,111,66,65,910,177,193,840,616],[803,563,1]]
def bRowA_115 : List Nat := List.flatten [[872,995,527,141,269,300,801,583,713,70,801,929,498,352,839,125],[837,612,642,661,659,996,47,947,808,821,342,651,759,135,643,911],[539,503,77,872,516,902,212,447,739,132,174,233,172,27,884,473],[728,484,789,226,744,21,641,118,156,618,687,320,877,301,935,710],[490,116,400,422,396,957,508,223,757,201,13,742,930,203,779,29],[764,802,610,512,343,357,686,1004,917,326,193,707,222,72,636,208],[203,728,864,353,552,293,878,245,692,331,199,840,942,189,377,988],[843,504,181,1]]
def bRowA_116 : List Nat := List.flatten [[783,197,165,635,412,188,700,265,915,687,2,858,129,618,615,687],[49,537,721,931,769,507,1007,653,852,41,284,959,73,436,374,7],[223,558,377,263,317,819,286,602,108,840,698,729,809,84,443,488],[877,463,574,130,395,30,705,345,368,772,289,238,909,980,742,771],[454,540,146,515,393,451,126,646,704,895,230,865,847,426,217,280],[638,753,829,528,366,37,714,753,337,481,958,731,504,80,399,165],[995,147,294,274,912,82,518,242,215,674,312,893,721,981,123,219],[243,12,822,867,1]]
def bRowA_117 : List Nat := List.flatten [[142,553,878,831,451,756,603,162,37,262,943,200,64,242,954,787],[99,522,271,52,215,758,863,513,7,646,243,315,362,487,678,630],[87,203,401,324,257,872,429,41,263,345,135,738,697,737,342,875],[482,643,462,415,2,900,993,624,307,65,463,206,988,868,197,131],[570,569,738,993,872,115,797,163,652,979,865,358,672,536,32,71],[982,284,691,754,928,574,723,363,162,874,26,385,190,409,39,528],[767,738,843,934,204,445,725,8,212,704,590,742,82,688,352,186],[277,816,870,274,537,1]]
def bRowA_118 : List Nat := List.flatten [[344,128,188,895,174,18,919,264,214,168,703,41,721,240,633,867],[394,516,208,515,570,657,455,889,551,550,667,929,615,186,460,633],[16,579,11,540,88,827,180,55,508,339,35,776,831,115,21,972],[144,552,10,430,248,989,606,979,206,663,995,577,355,991,460,806],[47,59,208,763,547,173,923,819,168,1000,395,606,215,787,182,435],[376,146,687,270,933,322,267,302,276,399,740,124,257,320,262,36],[793,91,531,185,477,404,480,774,757,476,446,323,789,306,627,905],[554,592,290,702,647,108,1]]
def bRowA_119 : List Nat := List.flatten [[229,940,141,2,293,697,834,630,378,656,64,976,682,616,524,250],[202,11,980,661,750,23,738,889,270,599,305,595,825,582,18,444],[293,683,159,1000,240,69,557,148,857,66,518,109,331,511,195,741],[25,487,787,700,397,570,204,641,618,247,91,358,833,123,415,440],[708,651,208,40,312,252,364,327,501,594,371,330,615,656,933,700],[673,104,5,403,539,601,609,611,849,363,433,14,185,35,14,169],[351,675,669,763,876,687,604,963,148,342,758,979,903,871,223,674],[310,884,852,763,330,995,369,1]]
def bRowA_120 : List Nat := List.flatten [[153,285,984,704,735,651,993,713,648,106,248,731,78,321,481,350],[401,610,448,355,74,686,38,809,873,688,673,656,192,670,612,1003],[458,689,530,967,98,382,234,778,780,619,52,854,639,815,913,735],[102,3,618,200,418,389,744,161,82,475,921,991,561,30,649,303],[853,970,797,436,425,676,780,890,207,212,402,799,867,411,612,371],[221,956,442,758,549,798,473,628,195,789,19,857,727,286,140,855],[229,437,18,1002,974,341,685,73,658,767,32,775,354,329,884,357],[113,984,496,743,387,57,879,355,1]]
def bRowA_121 : List Nat := List.flatten [[560,676,616,39,279,967,394,278,246,990,881,238,839,150,842,736],[640,495,732,876,200,154,500,557,805,599,571,243,689,888,341,994],[678,305,914,902,521,710,873,661,172,603,704,35,762,917,193,213],[559,646,3,696,876,728,263,178,724,683,906,720,110,125,175,113],[661,992,598,713,934,157,622,592,363,733,667,82,461,992,615,876],[769,606,951,519,409,1004,363,338,170,209,741,862,721,824,296,101],[923,480,493,452,333,900,941,539,635,950,791,621,586,549,453,168],[101,69,962,843,382,786,510,906,480,1]]
def bRowA_122 : List Nat := List.flatten [[799,753,864,964,413,74,58,792,56,298,318,526,196,816,448,543],[892,237,115,280,490,280,592,849,728,192,131,830,273,145,174,992],[174,768,565,685,941,387,583,0,986,585,339,393,811,683,160,405],[228,538,94,344,940,170,186,516,250,141,629,151,24,470,368,60],[501,774,7,600,250,491,729,0,915,9,887,845,627,68,110,580],[572,937,844,36,393,287,566,959,369,920,915,681,160,475,699,482],[747,287,42,740,497,318,505,583,410,581,754,164,428,560,492,803],[565,667,416,13,622,413,91,209,258,855,1]]
def bRowA_123 : List Nat := List.flatten [[418,926,454,674,945,115,777,522,804,296,292,427,886,414,454,859],[826,973,566,371,507,621,635,187,659,887,414,571,152,521,446,80],[872,1000,509,34,179,733,626,383,261,910,243,203,823,692,684,849],[262,204,230,525,812,113,511,329,345,897,411,127,755,658,922,254],[131,964,970,367,1002,239,690,211,240,820,133,865,416,692,364,921],[32,968,178,179,834,1004,739,430,383,753,577,8,220,570,147,569],[123,303,9,511,687,96,555,784,912,250,300,287,998,353,645,872],[877,553,948,888,779,1001,236,593,569,956,201,1]]
def bRowA_124 : List Nat := List.flatten [[90,347,597,312,998,418,163,395,879,368,604,634,189,115,167,41],[360,856,292,31,193,113,319,441,54,596,36,576,134,4,407,731],[513,200,865,140,929,787,773,168,949,715,98,579,921,539,453,857],[817,76,890,704,742,951,594,21,347,79,410,213,156,711,725,947],[703,854,890,507,582,154,206,248,678,198,575,403,688,97,102,678],[917,489,542,275,996,491,270,811,1002,777,954,57,258,769,528,595],[188,995,775,702,661,497,307,111,832,922,385,486,771,762,321,113],[210,837,511,443,374,705,228,518,897,428,829,811,1]]
def bRowA_125 : List Nat := List.flatten [[453,259,655,74,603,680,422,311,885,545,441,802,323,967,45,319],[800,266,3,856,207,456,187,350,612,644,267,724,386,640,920,38],[564,900,648,355,660,924,503,168,242,1001,803,865,654,550,839,185],[231,411,33,643,555,358,961,474,602,770,405,850,502,516,471,923],[233,937,1006,13,372,445,634,385,212,673,871,960,500,88,122,225],[544,22,963,851,164,46,727,918,40,43,364,809,250,470,275,971],[122,467,668,357,507,260,146,507,168,117,150,464,10,872,406,207],[861,18,400,260,36,302,506,733,250,384,483,839,97,1]]
def bRowA_126 : List Nat := List.flatten [[264,824,599,902,558,749,527,231,658,404,302,822,446,861,635,844],[463,67,992,385,92,15,49,866,6,22,211,210,626,61,38,757],[622,156,402,593,848,877,926,737,873,638,306,433,597,776,205,41],[961,68,661,461,5,971,234,47,665,553,477,825,494,550,218,374],[931,141,126,370,208,166,189,857,408,269,440,343,910,514,299,388],[487,1003,336,124,524,89,898,838,836,34,960,909,348,669,856,778],[609,517,475,691,819,941,403,260,963,858,510,643,771,982,549,527],[599,15,149,44,589,584,893,473,203,190,130,592,919,659,1]]
def bRowA_127 : List Nat := List.flatten [[379,581,78,865,887,502,145,748,510,689,214,930,345,565,851,631],[12,630,206,298,111,585,197,897,547,229,807,579,566,971,918,944],[692,496,172,255,726,786,867,69,641,411,626,924,341,1000,540,816],[639,366,9,940,259,490,503,520,426,706,991,658,70,772,856,196],[281,746,488,778,171,130,828,229,622,757,598,408,232,835,338,523],[304,218,701,885,413,92,518,214,530,990,159,95,992,421,194,231],[31,493,868,254,515,658,133,993,855,780,616,741,989,373,745,141],[815,381,703,654,860,279,762,338,937,533,861,916,42,149,719,1]]
def bRowA_128 : List Nat := List.flatten [[279,372,105,264,14,155,893,837,417,509,432,309,953,792,755,573],[521,490,695,346,661,603,650,500,424,703,670,855,212,618,15,508],[538,597,590,367,182,303,350,346,312,280,346,758,48,278,467,652],[683,31,968,148,312,944,429,358,117,783,313,474,850,309,784,448],[634,586,170,452,455,174,96,647,672,701,434,835,668,635,499,148],[795,265,940,765,61,827,869,870,821,960,51,35,601,518,864,563],[144,436,112,910,760,559,287,649,580,223,999,388,255,770,128,318],[585,300,574,103,558,584,126,763,445,579,1,130,422,50,646,76],[1]]
def bRowA_129 : List Nat := List.flatten [[36,484,499,360,867,558,777,10,106,382,96,995,36,716,169,78],[934,674,38,701,757,727,839,190,283,268,725,678,924,971,323,383],[416,263,285,574,202,362,791,493,834,593,830,273,139,700,291,539],[113,505,927,948,913,740,606,747,935,156,321,169,621,265,346,217],[283,456,427,205,426,914,827,596,845,712,128,129,651,39,360,821],[793,457,348,425,869,869,496,226,70,133,788,906,810,670,559,38],[260,175,539,800,420,341,986,642,483,411,61,411,465,344,914,177],[456,255,919,315,762,550,864,362,873,168,698,813,586,1001,949,907],[785,1]]
def bRowA_130 : List Nat := List.flatten [[629,2,359,483,928,679,40,559,552,222,699,487,707,858,44,698],[835,225,42,391,593,954,303,648,472,568,828,635,398,596,134,978],[942,109,349,760,595,501,921,254,900,294,130,328,203,224,619,17],[251,522,879,433,34,892,429,929,979,962,705,855,937,702,774,183],[420,882,318,247,65,165,164,948,503,820,698,127,394,585,984,904],[834,658,5,605,146,667,819,318,677,490,188,609,73,790,672,928],[563,571,969,541,624,819,68,312,752,101,363,698,399,690,600,492],[195,252,879,881,450,543,148,29,642,752,534,995,269,496,373,486],[840,896,1]]
def bRowA_131 : List Nat := List.flatten [[121,432,282,864,487,343,535,72,521,933,1006,790,934,717,103,471],[925,799,944,681,689,349,127,718,742,93,197,355,360,631,607,447],[656,358,493,69,15,364,150,388,415,887,921,912,387,103,695,695],[324,609,840,854,243,11,347,31,431,91,333,420,185,462,756,875],[696,996,364,656,886,516,648,262,578,281,892,509,961,297,35,654],[941,468,813,204,539,209,283,820,711,876,878,21,382,942,433,888],[1007,987,660,69,603,836,349,866,533,82,387,141,837,104,139,649],[375,584,425,256,530,882,574,538,657,577,815,587,717,241,536,604],[58,32,170,1]]
def bRowA_132 : List Nat := List.flatten [[393,710,449,991,6,861,491,868,319,753,639,218,632,31,684,237],[328,140,554,609,732,211,105,855,932,830,517,147,836,96,33,729],[780,937,666,626,839,252,532,756,901,581,346,235,916,375,370,320],[436,997,980,759,688,631,449,31,185,920,793,794,44,185,244,769],[874,870,354,700,771,268,194,226,180,552,666,520,432,573,135,315],[479,308,300,2,445,8,181,826,776,885,727,450,477,882,352,445],[182,758,529,717,810,399,221,663,23,703,441,75,30,46,741,939],[697,998,547,169,398,570,611,508,978,8,637,454,742,220,402,293],[866,536,242,312,1]]
def bRowA_133 : List Nat := List.flatten [[694,439,450,156,688,150,785,252,940,189,477,106,282,679,963,603],[235,271,723,308,295,816,546,626,936,543,859,130,366,306,197,299],[804,345,808,642,249,758,843,287,407,50,76,318,256,299,137,603],[741,946,37,706,126,40,849,259,980,73,40,1001,989,308,851,577],[387,797,595,779,236,93,797,129,581,767,427,98,602,480,100,771],[971,589,153,739,926,316,160,296,761,140,774,418,537,548,808,139],[824,208,968,233,652,328,187,883,905,95,658,248,872,517,637,450],[267,506,862,95,281,263,507,838,12,529,861,937,39,557,68,750],[764,906,481,938,686,1]]
def bRowA_134 : List Nat := List.flatten [[446,206,428,652,669,617,4,564,620,620,62,450,396,575,611,319],[454,995,813,216,649,638,675,571,173,740,533,274,850,626,697,231],[504,466,343,255,444,278,228,391,676,271,217,627,679,718,296,909],[953,496,264,772,416,42,561,991,781,619,443,944,101,664,18,400],[739,937,667,642,383,541,343,16,108,536,1,411,617,309,606,886],[341,288,192,308,440,741,1000,123,791,414,393,579,291,182,538,978],[825,526,522,28,508,231,74,987,888,486,906,69,936,482,18,769],[927,146,898,815,271,464,870,638,964,127,706,9,510,813,793,834],[993,768,327,209,232,929,1]]
def bRowA_135 : List Nat := List.flatten [[412,176,132,308,698,558,814,822,120,84,230,460,211,473,623,859],[159,456,704,608,280,840,257,852,350,793,522,214,546,562,727,818],[35,950,556,802,272,410,481,63,710,960,344,967,434,806,435,630],[196,737,335,462,260,288,650,708,131,471,440,119,995,146,997,929],[956,351,114,610,319,706,299,98,739,58,799,585,773,301,192,465],[508,772,99,46,168,113,405,48,879,1001,889,616,459,771,61,569],[471,77,475,335,516,587,574,941,188,884,636,720,535,692,777,552],[650,668,221,983,1008,743,346,716,308,208,484,671,225,529,717,741],[238,855,172,555,303,591,871,1]]
def bRowA_136 : List Nat := List.flatten [[286,636,336,160,548,243,313,279,169,762,298,345,477,173,736,269],[228,293,565,841,557,186,96,699,659,998,636,634,371,767,70,467],[406,677,153,944,556,789,837,560,869,377,280,804,46,968,234,971],[845,728,948,221,220,187,16,507,600,472,438,100,603,737,632,415],[203,540,742,15,929,336,268,714,507,531,842,610,45,324,401,584],[705,55,111,607,142,745,993,592,810,458,986,376,11,631,378,726],[217,477,136,275,986,190,649,581,59,394,187,844,954,193,971,463],[430,102,740,368,952,47,714,649,157,169,612,488,44,284,194,831],[422,608,282,584,127,699,819,583,1]]
def bRowA_137 : List Nat := List.flatten [[565,351,559,540,253,804,636,822,723,860,121,926,222,59,449,1007],[329,355,786,33,793,574,710,234,225,540,915,834,740,162,952,508],[861,585,521,952,883,190,412,684,541,606,841,973,759,940,811,700],[322,353,96,156,83,355,171,424,669,608,182,163,648,37,570,106],[909,715,557,719,624,1002,193,891,927,502,293,181,550,83,553,899],[369,601,700,958,112,518,374,487,884,894,147,773,8,1007,488,393],[568,1002,405,340,97,667,538,762,140,309,716,182,766,848,190,518],[396,18,133,153,866,296,119,657,93,46,628,310,264,216,377,438],[473,312,881,637,666,377,114,885,93,1]]
def bRowA_138 : List Nat := List.flatten [[403,1004,134,4,188,27,77,171,702,471,970,271,607,462,934,131],[977,181,903,22,740,408,655,594,480,575,328,152,701,491,435,665],[710,990,311,311,730,656,598,239,327,25,87,110,305,688,535,199],[201,136,629,39,570,206,367,556,937,854,349,373,662,705,660,341],[1006,544,57,157,652,921,215,30,837,548,855,850,205,641,151,24],[89,444,836,547,432,226,251,218,435,997,940,721,37,21,961,185],[67,495,979,444,215,800,775,532,555,927,476,923,282,370,308,35],[460,244,1006,1002,543,598,883,412,678,124,307,452,16,234,233,839],[173,639,789,21,82,696,549,843,886,722,1]]
def bRowA_139 : List Nat := List.flatten [[348,91,564,297,70,644,244,734,114,708,309,875,961,422,128,98],[589,196,53,604,992,286,139,705,732,712,246,110,780,903,394,764],[537,276,155,235,254,637,23,927,688,501,449,750,387,905,408,123],[963,762,954,834,195,867,995,588,469,157,7,925,897,809,973,738],[914,337,828,715,893,516,378,635,421,681,504,570,600,113,323,784],[309,383,95,403,675,250,138,797,329,134,459,537,528,310,250,222],[0,410,859,1003,254,86,225,912,128,402,770,850,61,573,43,850],[580,86,223,1003,158,799,532,274,477,635,406,27,40,362,137,537],[627,73,637,888,278,940,609,831,352,955,79,1]]
def bRowA_140 : List Nat := List.flatten [[683,823,651,570,513,661,196,398,352,672,218,6,200,171,735,179],[675,893,244,793,68,37,235,540,80,395,670,991,1,773,544,999],[93,137,359,256,859,581,788,605,214,109,457,359,803,910,557,362],[697,122,967,112,741,715,90,168,590,979,21,255,81,925,661,9],[953,749,497,138,843,308,570,49,467,590,299,926,991,200,867,21],[635,651,582,440,949,750,945,958,45,447,528,645,860,835,869,766],[30,63,722,836,121,992,538,252,775,659,992,338,565,895,287,966],[724,562,423,378,557,80,706,739,261,225,644,273,457,48,230,527],[450,796,305,620,510,641,602,565,335,898,709,54,1]]
def bRowA_141 : List Nat := List.flatten [[918,918,20,420,98,159,89,810,630,161,956,783,76,485,649,272],[136,866,953,229,224,579,223,35,656,745,956,587,473,641,289,50],[820,617,848,986,942,377,535,259,922,316,93,233,555,812,235,991],[166,364,322,795,695,606,576,9,842,445,695,874,387,190,893,105],[598,344,194,174,172,929,376,809,956,952,956,194,73,808,97,371],[938,507,287,571,880,752,212,788,865,654,213,236,455,761,100,508],[376,873,282,530,17,351,275,9,210,369,679,19,825,570,700,231],[156,490,190,131,240,856,156,326,200,230,296,512,179,129,158,463],[34,798,875,363,472,934,939,888,846,998,782,582,41,1]]
def bRowA_142 : List Nat := List.flatten [[566,952,460,882,437,857,827,844,559,584,269,318,704,389,346,4],[672,812,960,761,869,910,237,555,617,458,338,875,991,694,985,607],[877,962,62,752,729,444,528,901,754,141,599,647,515,687,813,394],[982,502,802,791,548,75,678,869,269,657,54,891,340,779,387,356],[894,326,676,528,838,327,826,922,765,911,269,163,254,441,795,54],[649,277,644,397,137,596,78,200,279,95,912,238,293,851,364,881],[297,729,1006,7,663,242,806,383,499,80,877,61,367,616,466,959],[567,781,378,95,164,84,583,574,851,708,437,1004,740,207,379,805],[367,659,405,497,257,322,1,883,719,148,696,78,441,451,1]]
def bRowA_143 : List Nat := List.flatten [[116,142,757,872,791,961,304,158,301,332,593,886,581,917,411,647],[875,34,646,426,389,236,35,875,458,97,932,392,953,198,212,951],[1001,964,322,316,557,260,189,779,15,342,813,153,111,285,384,975],[388,819,433,244,352,265,373,16,208,613,881,959,107,243,578,367],[458,177,435,990,485,876,968,24,106,296,920,562,853,844,307,230],[350,1000,710,325,225,181,923,334,121,623,707,1006,138,977,12,459],[984,971,930,403,766,330,865,159,443,383,495,420,567,235,936,510],[929,478,877,392,64,639,776,755,32,810,861,594,461,291,742,46],[291,110,806,411,262,871,874,822,31,261,181,560,267,470,370,1]]
def bRowA_144 : List Nat := List.flatten [[23,964,882,291,634,825,400,741,250,512,183,481,260,264,625,777],[884,859,987,345,441,977,171,941,590,799,935,837,666,475,497,947],[821,413,997,597,877,384,1,478,772,437,284,756,591,91,617,800],[188,785,702,206,1,300,327,330,267,932,662,851,998,750,755,123],[542,1,730,379,597,341,706,239,504,675,279,193,148,166,738,482],[55,649,955,123,669,995,663,97,886,210,389,1000,247,400,792,55],[711,879,32,605,337,965,881,381,358,852,58,907,496,300,680,100],[373,340,250,197,763,459,804,979,256,927,312,132,539,861,928,515],[566,707,510,375,610,221,727,181,94,775,97,896,538,913,391,500],[1]]
def bRowA_145 : List Nat := List.flatten [[248,713,1000,936,197,152,836,195,483,976,415,330,846,207,642,120],[191,210,567,630,1003,121,401,787,747,236,682,392,373,449,968,484],[185,642,155,450,409,554,346,217,933,383,662,928,50,345,200,695],[121,212,503,322,843,450,91,226,902,152,246,591,770,829,341,425],[32,900,686,817,309,954,137,263,200,828,680,637,567,402,181,480],[943,620,668,1002,911,738,77,679,467,687,996,192,982,781,827,683],[48,268,54,801,985,220,274,429,339,269,999,669,639,926,409,368],[321,602,586,744,757,826,621,800,719,987,601,859,516,755,954,428],[334,569,636,962,468,885,110,855,680,938,795,547,474,369,1002,210],[645,1]]
def bRowA_146 : List Nat := List.flatten [[680,466,86,55,421,273,476,946,323,314,329,502,374,723,805,69],[636,274,369,943,773,757,229,625,59,223,476,693,726,5,170,124],[716,211,893,132,819,125,513,102,164,84,606,144,744,236,245,510],[243,36,150,540,781,190,336,523,985,359,597,932,357,877,611,490],[909,727,41,592,104,663,687,814,810,184,85,909,912,506,480,513],[288,1,521,356,913,1000,833,788,258,334,636,927,926,489,132,479],[734,37,619,69,150,351,119,459,22,785,172,120,643,877,21,793],[459,107,958,692,603,355,299,487,955,911,872,791,563,227,275,114],[979,683,895,9,745,948,628,426,698,86,306,963,878,345,228,935],[752,242,1]]
def bRowA_147 : List Nat := List.flatten [[20,484,407,965,953,384,286,208,293,396,325,939,820,163,833,458],[665,336,679,635,742,641,86,38,515,68,525,2,513,482,201,919],[904,147,129,503,884,995,755,341,27,371,141,583,555,258,146,220],[103,597,234,894,634,583,313,148,649,417,639,336,715,557,36,675],[822,96,72,632,541,746,596,685,298,13,742,66,676,348,822,642],[960,38,101,515,852,735,782,179,615,598,513,98,880,30,469,469],[598,338,552,17,451,286,690,459,993,144,547,83,210,700,727,181],[200,387,433,50,198,983,873,325,310,427,41,426,3,653,524,770],[942,386,523,512,499,44,148,126,195,177,814,993,478,763,298,794],[736,430,802,1]]
def bRowA_148 : List Nat := List.flatten [[147,921,974,174,944,555,854,299,899,470,324,982,742,952,842,927],[161,753,731,402,265,641,160,194,887,737,985,333,293,936,971,886],[953,806,610,368,322,849,925,957,900,428,4,472,191,481,176,544],[565,838,618,30,474,539,249,943,860,524,266,468,644,974,579,941],[477,624,680,397,753,612,170,500,47,917,794,581,110,41,394,895],[895,47,225,393,400,652,218,107,448,409,538,521,776,332,946,14],[814,903,824,79,317,357,585,0,899,564,19,401,540,797,895,2],[167,841,125,688,768,468,922,610,340,275,940,834,449,445,165,546],[711,484,585,20,960,851,579,357,562,585,226,787,621,282,75,569],[147,157,211,515,1]]
def bRowA_149 : List Nat := List.flatten [[974,250,62,461,737,611,929,827,400,34,283,922,950,810,244,202],[140,756,494,900,426,381,115,726,503,62,960,336,181,99,559,589],[105,453,396,4,936,923,607,95,581,777,776,86,217,902,822,347],[104,377,309,346,581,551,699,511,549,651,1006,310,381,610,12,890],[651,169,332,626,659,813,48,631,10,816,13,153,657,989,465,691],[262,975,377,857,204,652,425,687,445,1004,58,487,180,726,354,646],[344,608,784,347,901,582,441,937,107,525,439,351,907,153,636,70],[735,321,819,885,916,519,629,548,329,854,75,625,301,434,469,526],[228,14,352,148,588,734,342,341,377,490,205,251,148,355,317,640],[140,848,240,493,786,1]]
def bRowA_150 : List Nat := List.flatten [[872,541,251,795,695,166,921,599,137,835,319,200,688,986,244,1003],[180,539,654,215,680,892,32,43,278,378,468,401,333,885,512,251],[26,223,796,59,911,498,997,162,859,625,684,419,25,299,759,572],[215,292,965,520,779,971,912,844,685,714,66,186,487,965,733,108],[874,981,17,200,526,673,855,841,645,425,357,582,547,741,505,210],[840,809,348,775,824,96,974,607,380,311,407,22,83,940,76,796],[771,469,830,933,134,783,732,29,94,70,478,310,888,848,312,956],[128,762,197,314,194,339,111,48,676,810,699,610,743,164,620,434],[268,321,944,57,161,53,391,919,883,415,352,549,918,855,45,64],[285,855,57,480,522,63,1]]
def bRowA_151 : List Nat := List.flatten [[537,509,610,92,927,861,172,957,423,846,998,544,288,306,613,18],[496,756,572,855,818,944,268,3,124,411,473,785,345,395,579,659],[445,96,1005,172,118,657,398,562,14,352,718,497,234,762,627,644],[695,100,613,556,164,396,730,708,207,177,611,942,406,982,135,884],[16,799,68,862,70,412,832,730,70,968,996,538,189,912,221,599],[209,773,436,827,603,886,901,456,622,1000,86,914,368,570,647,198],[722,466,194,241,275,149,69,271,112,908,396,317,749,348,747,393],[761,616,565,695,176,351,420,686,372,366,815,635,496,64,780,723],[206,97,151,984,13,823,86,629,928,63,789,471,406,993,458,338],[839,350,975,286,529,441,671,1]]
def bRowA_152 : List Nat := List.flatten [[739,958,798,804,709,590,158,817,119,200,715,427,664,133,168,655],[740,622,535,94,20,510,571,800,143,463,350,733,698,846,45,639],[116,891,90,463,420,827,931,221,848,69,279,155,919,974,658,203],[43,713,103,542,513,54,826,592,969,189,318,336,425,926,811,459],[666,604,185,82,364,526,324,25,941,831,758,267,323,912,780,812],[834,33,736,562,40,720,406,679,828,240,108,307,183,367,553,708],[508,323,831,36,82,208,77,734,433,822,167,263,313,38,965,806],[661,975,50,893,8,15,588,659,826,55,335,994,209,961,276,87],[191,918,947,230,541,687,107,910,105,315,184,176,258,776,560,985],[793,721,441,695,229,257,208,1006,1]]
def bRowA_153 : List Nat := List.flatten [[213,390,383,569,105,884,603,881,509,112,442,315,269,482,751,446],[1008,851,51,372,614,31,0,350,171,111,272,156,285,735,238,420],[233,919,250,455,805,328,871,862,638,770,70,42,967,32,640,660],[356,801,251,339,492,479,573,415,58,131,640,755,359,129,448,993],[977,955,723,88,479,574,341,263,540,709,370,743,924,478,485,779],[539,374,717,923,426,543,932,502,829,882,893,942,113,681,355,364],[53,612,507,354,437,749,910,870,998,837,958,666,718,921,983,317],[801,631,385,821,957,148,871,57,789,270,384,77,441,219,147,126],[548,405,1000,827,154,979,392,643,626,121,509,419,296,570,157,424],[786,196,406,312,539,107,268,440,945,1]]
def bRowA_154 : List Nat := List.flatten [[692,983,574,753,44,517,640,268,655,232,936,720,212,972,681,773],[293,831,273,532,1005,499,541,45,970,794,86,952,714,155,169,182],[951,996,325,697,809,942,546,28,400,453,364,977,248,308,931,308],[251,674,354,513,894,690,658,618,204,345,486,200,125,362,653,374],[240,779,271,659,782,506,336,880,901,939,991,525,421,956,375,203],[716,973,218,853,464,80,758,593,98,926,138,799,764,272,760,607],[197,313,340,238,745,44,890,283,780,585,722,672,363,974,1000,909],[350,466,866,488,729,84,19,845,454,645,633,391,167,759,41,447],[170,458,179,194,342,696,776,862,303,458,277,595,854,420,494,554],[995,239,478,936,290,933,359,498,235,264,1]]
def bRowA_155 : List Nat := List.flatten [[802,712,551,752,450,979,633,181,471,117,902,65,151,69,406,828],[147,3,281,370,353,563,352,192,572,91,729,606,969,253,16,639],[728,402,519,436,590,190,519,865,392,993,496,99,68,270,328,880],[477,250,549,759,23,895,767,760,946,46,775,733,873,509,368,575],[550,952,224,363,870,74,267,235,196,63,876,634,268,195,878,140],[127,790,666,420,830,913,751,750,129,67,946,273,467,820,659,343],[499,499,323,149,52,632,651,546,126,709,445,760,236,467,432,803],[651,553,281,278,473,96,498,296,334,545,432,808,994,134,93,639],[666,997,93,547,768,946,354,794,580,199,830,702,851,649,641,719],[245,111,542,800,765,625,326,335,883,926,25,1]]
def bRowA_156 : List Nat := List.flatten [[762,322,346,997,196,359,520,477,39,742,975,250,817,872,757,388],[637,340,767,808,965,18,328,381,952,224,585,703,533,759,968,211],[392,557,954,496,377,649,485,99,443,159,219,916,233,765,707,284],[810,481,432,790,790,314,752,726,561,490,52,264,67,237,270,757],[474,709,715,499,271,886,757,768,405,262,120,490,588,260,297,176],[984,40,283,381,195,710,669,457,888,438,310,291,169,343,3,686],[361,688,770,456,428,883,39,473,51,932,793,501,497,285,124,409],[249,86,495,115,520,626,732,294,584,735,122,358,282,340,351,409],[270,372,565,443,954,668,958,35,982,822,890,333,656,56,239,852],[962,755,428,634,414,919,901,129,56,114,411,171,1]]
def bRowA_157 : List Nat := List.flatten [[87,356,569,366,691,74,25,606,861,25,356,424,587,166,494,294],[341,212,159,655,602,89,451,958,365,230,823,211,271,466,10,996],[141,807,829,239,725,633,421,413,364,1008,748,705,719,707,159,137],[625,849,994,412,11,15,571,331,54,87,329,602,15,411,871,287],[584,192,988,486,545,258,207,558,469,16,788,883,292,24,449,199],[44,769,355,13,671,186,336,391,465,513,260,739,671,328,701,24],[697,854,8,568,118,776,779,400,843,565,172,244,429,508,597,348],[559,923,979,131,996,2,679,737,740,490,862,521,162,402,710,532],[26,740,357,643,688,594,793,663,532,822,319,696,247,672,595,111],[131,820,607,367,966,774,157,598,71,520,36,54,768,1]]
def bRowA_158 : List Nat := List.flatten [[424,466,68,401,116,234,908,327,859,121,473,229,692,530,452,904],[956,204,400,635,70,211,769,854,549,509,858,38,578,609,10,1002],[266,332,841,285,618,629,703,280,1001,485,287,618,815,128,587,937],[889,296,307,947,881,481,396,321,997,561,99,47,544,201,100,125],[72,747,833,442,839,884,400,579,559,291,159,935,862,284,298,388],[524,559,871,653,528,973,496,528,696,147,900,513,986,69,937,660],[968,467,211,80,379,544,704,516,890,802,574,439,85,491,740,919],[769,677,770,687,893,84,965,566,95,83,360,919,574,943,175,604],[15,381,653,976,325,887,510,710,875,67,269,155,750,71,373,205],[400,286,349,965,447,590,394,639,131,131,414,718,279,656,1]]
def bRowA_159 : List Nat := List.flatten [[425,755,521,139,981,903,271,700,252,521,490,248,801,355,547,879],[568,846,740,930,606,923,229,554,247,498,327,594,87,53,68,165],[937,233,296,995,791,607,313,116,658,837,212,720,673,90,207,755],[815,364,674,649,963,401,532,623,303,1003,686,137,217,930,279,790],[722,62,593,692,393,877,788,228,884,612,493,542,955,289,706,664],[154,915,491,238,509,158,193,339,121,335,580,811,658,166,883,848],[325,676,873,893,771,451,922,617,577,276,872,177,224,272,850,851],[524,558,496,824,326,388,916,280,51,874,904,43,448,606,239,331],[993,641,600,567,812,54,8,219,603,561,428,568,677,162,882,442],[437,498,307,244,17,75,658,939,295,770,469,112,980,892,346,1]]
def bRowA_160 : List Nat := List.flatten [[519,330,601,236,771,489,799,899,840,928,261,198,929,590,1006,143],[679,239,413,780,757,28,117,20,870,15,603,581,953,397,310,651],[291,948,479,511,610,816,628,605,445,524,64,221,857,82,327,548],[856,723,655,248,200,684,121,951,727,67,337,55,551,728,595,94],[211,459,1006,814,162,252,135,725,102,740,375,414,565,1004,228,988],[31,396,35,485,839,43,116,501,25,244,859,465,224,1003,692,413],[410,494,546,367,151,57,821,549,907,235,891,681,226,272,176,281],[227,529,663,114,277,284,364,952,687,746,390,996,865,311,568,430],[341,798,701,850,640,237,372,61,813,650,628,351,830,884,521,171],[383,175,911,573,428,732,535,754,107,252,620,745,95,302,853,781],[1]]
def bRowA_161 : List Nat := List.flatten [[15,18,955,494,765,776,69,604,386,218,700,242,932,943,447,922],[730,417,235,714,353,212,987,707,241,3,460,904,727,153,328,985],[652,250,94,190,493,466,224,576,42,449,721,185,775,920,246,150],[551,529,523,430,389,812,332,100,541,578,787,705,667,282,460,446],[775,659,815,387,11,642,853,322,779,993,554,490,364,328,434,757],[459,919,548,396,264,927,231,356,73,882,923,243,2,707,631,368],[52,85,529,76,225,36,341,361,90,617,69,169,307,283,387,923],[120,401,740,552,27,806,962,929,488,649,175,363,157,827,830,29],[14,517,232,732,81,633,163,8,136,446,801,569,590,959,476,932],[184,28,327,908,517,149,457,188,28,194,809,841,537,130,108,823],[986,1]]
def bRowA_162 : List Nat := List.flatten [[523,698,262,923,351,514,606,80,906,23,1003,624,753,306,321,495],[312,765,18,82,138,349,389,1005,160,181,690,883,517,867,859,377],[777,998,222,243,889,39,352,283,895,719,106,28,663,122,211,187],[949,981,883,434,59,564,360,552,426,17,639,15,36,431,556,331],[619,104,605,410,772,697,675,310,440,549,342,167,438,826,112,447],[823,781,276,583,176,948,560,109,10,190,913,479,404,948,555,196],[261,779,80,482,536,92,552,928,334,293,938,835,235,594,995,92],[582,153,472,162,532,644,3,720,183,640,489,958,344,111,854,711],[244,212,307,200,271,730,611,961,1001,963,411,667,404,854,278,954],[430,548,3,738,419,19,304,464,573,198,548,608,427,656,381,970],[713,834,1]]
def bRowA_163 : List Nat := List.flatten [[439,303,34,695,386,440,353,947,111,59,348,842,805,435,159,705],[34,729,731,51,896,242,215,326,122,57,670,47,635,116,714,619],[293,516,550,511,709,188,958,9,256,964,731,25,689,927,634,257],[482,62,668,257,207,399,108,915,436,413,905,24,118,413,244,256],[258,582,207,778,112,283,270,131,961,858,621,4,606,239,52,494],[771,157,218,939,168,956,696,61,599,446,70,992,153,445,351,346],[496,310,226,414,846,192,764,684,427,612,675,167,159,945,390,709],[756,349,606,479,794,838,660,371,101,936,52,110,404,80,772,296],[453,807,875,727,35,527,816,626,202,787,507,566,78,127,321,464],[288,548,105,376,764,920,631,292,678,244,871,715,376,20,229,188],[234,636,71,1]]
def bRowA_164 : List Nat := List.flatten [[163,443,500,258,138,191,325,107,341,1004,9,48,619,9,975,263],[668,679,246,321,443,772,358,3,627,861,650,898,561,373,971,505],[970,469,555,584,966,814,215,904,91,47,222,900,13,928,353,546],[854,577,226,369,685,237,110,466,218,323,912,855,303,644,458,289],[266,690,756,927,122,763,968,553,430,767,269,161,330,95,491,375],[766,658,827,112,896,59,686,979,637,211,185,937,971,407,410,522],[34,525,909,240,72,666,57,956,270,648,718,178,662,452,464,909],[652,931,552,225,622,782,158,274,522,890,388,31,159,719,862,587],[2,78,46,272,36,516,628,861,263,188,811,314,387,712,562,1008],[206,871,515,895,277,285,814,958,914,653,485,704,345,59,803,82],[833,164,943,248,1]]
def bRowA_165 : List Nat := List.flatten [[203,436,403,696,308,186,930,118,840,929,57,326,84,717,574,730],[817,555,503,555,707,35,228,280,476,472,694,579,213,686,25,461],[854,641,279,622,380,95,218,120,954,773,426,835,19,56,947,924],[159,49,994,728,658,558,965,159,972,848,205,856,973,699,322,722],[342,77,220,356,144,648,305,503,114,249,305,988,896,611,831,39],[55,828,199,400,233,236,375,857,557,113,959,660,670,385,613,703],[402,134,1000,123,282,381,486,100,134,882,772,472,792,360,878,443],[914,904,316,753,809,586,698,873,570,308,98,182,292,105,267,314],[215,959,481,250,376,273,231,952,721,51,149,125,230,884,348,651],[8,136,726,967,168,195,154,866,291,497,588,958,1,759,925,211],[352,696,354,323,351,1]]
def bRowA_166 : List Nat := List.flatten [[467,27,728,410,945,278,383,20,171,235,760,390,114,621,777,871],[421,655,907,312,267,832,473,246,713,160,684,927,445,724,370,460],[668,732,523,749,946,878,814,354,822,160,387,46,197,733,123,850],[821,411,998,211,477,247,772,560,339,761,472,502,612,87,472,951],[830,683,398,778,758,268,699,121,80,719,94,280,571,604,391,928],[779,104,305,686,49,579,468,502,743,953,627,808,346,615,60,688],[305,605,416,683,291,210,805,22,505,3,934,1001,684,814,923,714],[774,523,40,674,928,584,410,979,289,52,299,480,972,563,704,603],[871,58,611,429,937,126,80,245,423,184,130,532,349,708,133,118],[614,561,655,139,778,310,166,815,643,130,522,363,882,139,996,946],[264,204,364,550,359,667,1]]
def bRowA_167 : List Nat := List.flatten [[194,638,251,630,699,1007,791,431,707,15,507,643,419,592,952,860],[930,403,456,547,514,433,293,893,585,602,769,676,452,220,724,834],[657,915,724,186,506,699,906,917,332,577,750,819,711,388,215,704],[486,786,439,303,320,135,367,842,12,519,904,644,345,802,312,764],[926,230,978,637,196,462,809,740,450,616,998,576,966,683,643,669],[646,299,9,1002,430,569,598,244,574,747,551,74,241,11,78,539],[925,980,83,771,97,439,905,272,612,400,711,882,135,984,48,558],[549,471,537,988,750,833,486,259,663,656,496,274,902,281,769,21],[808,843,651,0,602,1000,537,410,686,967,317,725,710,808,792,35],[398,56,430,908,160,1,108,226,193,192,502,897,414,765,549,74],[415,682,984,562,748,984,12,1]]
def bRowA_168 : List Nat := List.flatten [[904,587,456,46,507,939,644,562,814,281,312,664,430,951,251,85],[618,941,929,648,296,437,209,242,243,328,920,62,298,827,886,360],[122,781,910,332,745,715,462,928,927,705,872,621,796,659,445,922],[805,2,116,901,59,62,89,571,509,878,574,356,365,855,35,139],[243,233,127,769,369,916,735,221,590,413,874,221,783,535,97,782],[701,797,684,436,173,56,410,40,990,756,74,917,70,903,283,193],[846,944,976,690,663,700,53,508,723,411,673,169,831,354,509,748],[90,462,202,950,902,300,580,307,289,789,895,393,595,99,874,5],[868,441,457,748,589,846,272,889,593,642,921,461,1001,577,689,19],[365,697,1001,800,6,664,470,120,319,270,874,395,271,957,827,290],[309,765,263,539,926,207,544,794,1]]
def bRowA_169 : List Nat := List.flatten [[554,745,166,327,809,981,293,87,658,211,110,366,142,125,10,934],[54,979,400,397,418,361,624,92,491,359,849,502,734,230,473,8],[313,881,628,278,83,691,778,906,375,383,188,848,419,112,185,971],[745,991,560,512,85,331,181,217,476,342,272,870,749,497,473,466],[438,965,478,906,536,378,118,983,218,685,660,518,354,996,507,589],[151,39,640,729,420,252,924,44,103,118,901,745,662,201,235,233],[72,81,638,421,309,58,444,375,742,541,314,61,449,609,933,572],[429,249,520,618,432,736,635,755,804,358,572,978,500,561,487,258],[148,963,775,163,149,695,229,777,719,727,851,712,794,851,617,88],[115,370,48,709,6,821,316,437,337,205,536,838,704,32,378,409],[964,888,916,150,633,608,279,682,424,1]]
def bRowA_170 : List Nat := List.flatten [[145,566,328,978,944,729,421,46,423,469,805,119,549,409,268,904],[145,893,15,522,722,242,378,301,817,666,827,406,466,48,885,500],[73,18,249,853,200,988,505,840,612,1003,587,742,263,615,354,86],[89,331,797,500,541,355,395,180,94,335,452,527,603,352,434,735],[521,853,270,228,372,87,304,737,61,683,444,598,704,497,742,235],[637,723,10,12,876,917,991,188,909,470,954,353,151,501,662,437],[652,759,752,232,983,1007,311,432,722,544,767,27,971,104,628,189],[213,295,175,811,234,825,78,311,958,881,683,304,242,647,646,65],[710,508,596,96,499,543,773,240,502,1003,594,990,815,500,8,891],[240,582,409,167,987,779,198,117,202,774,186,463,484,759,741,349],[713,174,19,900,317,539,938,597,9,113,1]]
def bRowA_171 : List Nat := List.flatten [[248,968,11,959,781,127,619,173,178,555,243,622,589,72,795,22],[495,967,748,878,173,411,418,160,197,921,546,326,422,636,26,758],[340,835,653,315,528,57,992,276,977,936,568,248,337,753,302,660],[542,265,179,850,935,309,503,838,468,514,791,403,682,632,0,189],[791,472,599,110,776,423,109,950,413,772,326,156,1004,555,829,887],[581,686,87,977,360,185,151,522,294,388,574,668,46,338,157,455],[539,890,57,318,529,946,915,587,487,974,15,631,316,514,902,953],[651,959,774,736,799,88,636,25,712,275,903,868,403,14,652,740],[1003,218,182,902,495,633,373,697,785,84,214,300,432,917,735,382],[2,14,582,76,255,625,984,343,517,773,423,585,267,200,944,652],[656,718,617,819,400,809,824,968,864,27,286,1]]
def bRowA_172 : List Nat := List.flatten [[588,909,925,155,285,934,564,415,296,879,933,390,781,128,263,779],[792,302,765,456,134,661,943,605,246,900,246,529,829,935,916,809],[328,948,720,186,524,562,304,634,924,119,325,405,314,98,30,894],[885,450,240,747,942,336,155,668,501,871,87,578,872,618,898,462],[618,999,985,297,718,790,229,181,716,253,583,127,504,941,120,264],[387,292,296,530,299,691,892,949,956,56,24,643,116,229,247,373],[656,176,877,620,620,231,498,702,184,887,653,334,240,968,896,877],[418,355,495,853,335,782,359,886,887,408,434,701,936,493,41,972],[79,749,862,954,229,389,493,219,897,602,877,915,598,986,728,82],[569,280,94,736,154,785,36,592,1001,449,392,124,171,3,1001,138],[214,18,232,535,629,418,313,616,245,1000,168,843,1]]
def bRowA_173 : List Nat := List.flatten [[69,4,553,297,607,185,320,923,752,663,333,654,571,221,121,961],[451,93,590,39,395,146,812,488,640,89,141,195,181,52,605,250],[168,831,255,626,598,96,608,294,18,695,464,630,761,343,236,588],[834,316,731,940,525,75,680,558,25,934,724,450,664,622,864,485],[229,574,335,750,309,998,655,327,827,574,655,930,420,270,875,494],[149,325,502,635,531,621,998,876,429,270,636,344,373,602,688,183],[123,859,877,955,270,568,388,180,525,316,64,709,471,758,511,449],[561,314,678,934,562,364,218,672,660,100,562,676,816,226,436,310],[220,64,649,331,892,919,701,796,127,304,755,643,277,593,206,471],[95,931,456,271,16,897,583,271,889,39,193,490,302,24,352,20],[364,391,981,430,142,552,1007,905,275,734,130,123,459,1]]
def bRowA_174 : List Nat := List.flatten [[373,84,1001,155,664,7,557,471,93,674,134,161,149,652,661,915],[734,877,558,920,671,398,320,305,626,257,41,829,795,996,878,291],[312,216,638,355,194,173,80,540,994,696,692,727,142,313,231,208],[979,496,756,507,865,174,338,480,415,853,279,107,92,931,626,435],[100,56,653,866,744,291,175,627,410,141,879,468,232,298,963,215],[561,135,664,576,505,228,757,398,137,514,834,504,209,792,174,397],[539,483,969,436,289,376,846,670,939,827,321,282,769,651,587,694],[646,658,363,1004,301,593,415,357,623,646,210,808,652,2,394,366],[903,548,923,651,941,424,644,314,359,561,779,798,788,485,517,344],[326,839,321,586,743,237,347,733,916,239,327,340,733,369,117,375],[242,118,154,524,216,93,594,321,680,243,228,432,701,150,1]]
def bRowA_175 : List Nat := List.flatten [[678,253,430,820,413,103,490,902,944,755,591,850,725,157,15,788],[259,399,825,623,661,22,484,417,881,41,782,752,696,137,722,200],[509,870,653,436,279,851,815,725,492,50,295,196,921,606,101,129],[647,142,44,917,890,663,280,988,458,331,337,950,826,929,896,555],[267,132,589,524,1002,350,451,202,670,661,999,735,527,171,993,825],[572,552,845,451,978,289,726,342,534,680,801,284,910,172,499,989],[695,520,864,506,518,377,344,342,662,112,501,52,695,715,143,561],[957,817,137,122,249,971,995,309,812,166,440,797,675,239,110,709],[307,782,466,804,958,905,435,893,344,586,595,200,146,671,242,844],[361,344,705,956,933,478,379,328,532,366,176,434,295,318,721,44],[568,238,284,422,65,608,291,474,931,988,569,96,771,899,22,1]]
def bRowA_176 : List Nat := List.flatten [[852,309,663,626,531,723,52,435,974,912,271,416,268,28,116,670],[349,624,191,53,558,386,521,686,262,501,559,514,856,908,440,432],[45,881,146,615,674,474,540,580,310,12,952,539,773,425,993,811],[834,754,101,772,180,602,903,651,486,698,770,298,182,413,38,795],[5,746,146,569,212,415,353,765,368,34,872,46,513,503,112,29],[994,97,15,311,448,814,464,221,977,164,660,969,792,218,128,557],[700,557,408,590,530,375,867,212,820,829,832,331,620,152,666,59],[223,239,684,176,647,815,556,285,576,2,709,224,43,812,103,234],[330,604,318,332,842,531,728,29,845,566,468,84,801,965,338,530],[592,259,539,406,82,588,917,477,675,797,291,15,335,706,474,458],[895,926,67,792,269,286,414,116,895,862,875,855,390,644,202,242],[1]]
def bRowA_177 : List Nat := List.flatten [[268,936,359,130,651,897,478,907,454,74,707,238,162,848,805,330],[458,224,879,114,352,765,61,714,610,441,324,494,240,965,238,533],[545,266,661,305,327,523,279,589,819,143,484,226,632,858,751,821],[714,892,235,706,949,794,527,219,740,703,133,789,205,704,745,292],[329,285,972,268,113,616,460,217,630,585,24,1007,425,16,374,850],[530,511,32,970,38,105,479,1007,199,841,935,10,233,882,263,265],[170,227,831,768,779,593,634,596,9,408,6,403,332,910,901,828],[929,755,829,582,619,932,70,142,939,532,661,318,716,323,63,529],[940,187,998,849,28,404,130,866,92,663,311,29,315,305,805,84],[207,571,621,5,210,218,266,152,685,931,833,410,402,711,515,292],[231,257,312,966,365,598,797,168,544,348,189,852,559,89,129,806],[893,1]]
def bRowA_178 : List Nat := List.flatten [[627,187,335,340,635,347,448,761,521,773,677,451,916,13,553,276],[694,341,306,606,800,204,406,441,829,182,127,109,400,833,107,660],[918,531,619,518,367,38,377,452,666,413,383,833,980,861,174,553],[852,523,568,918,264,696,454,913,521,439,461,25,722,460,889,316],[670,528,833,139,77,473,643,73,856,5,761,284,826,293,373,720],[479,607,300,798,371,324,733,974,123,494,442,755,668,544,183,86],[932,790,630,256,60,828,266,801,488,640,354,435,387,835,516,239],[581,18,862,865,149,639,564,418,704,998,805,463,530,985,963,39],[921,658,407,841,127,367,57,937,147,436,218,490,932,642,1000,946],[427,724,256,440,173,697,310,1005,624,434,921,288,857,299,696,383],[537,910,587,333,552,289,1006,878,35,132,347,264,428,444,778,423],[802,102,1]]
def bRowA_179 : List Nat := List.flatten [[740,103,999,873,655,288,802,674,705,885,17,145,514,127,25,516],[570,31,547,892,449,504,186,676,227,36,192,397,1002,449,580,86],[202,961,260,277,448,306,208,772,91,228,456,731,605,605,111,555],[387,406,635,733,335,908,208,759,829,558,409,16,690,218,910,697],[721,457,297,58,845,909,174,888,577,832,349,552,911,403,362,799],[957,152,386,984,517,261,289,639,602,535,837,336,291,121,649,360],[168,392,952,559,385,694,401,271,186,755,459,955,841,282,196,901],[677,654,635,765,514,813,960,335,981,443,758,102,836,723,139,494],[430,950,325,725,583,4,726,720,813,270,813,485,826,947,224,152],[641,242,479,802,309,482,535,956,952,453,60,713,663,887,1004,347],[818,835,804,849,960,728,192,150,481,263,870,617,846,978,795,392],[488,779,943,1]]
def bRowA_180 : List Nat := List.flatten [[623,148,321,116,364,953,338,913,884,643,709,878,73,323,268,477],[464,305,844,359,387,768,395,778,806,370,441,570,200,330,434,728],[220,20,655,627,844,540,109,993,493,235,801,52,2,998,312,770],[290,29,330,694,524,477,994,896,966,928,447,487,179,411,93,750],[841,487,120,484,729,911,204,897,635,699,752,999,428,897,20,627],[164,88,63,624,668,958,710,67,400,272,923,883,356,237,418,122],[344,982,1,742,443,636,535,937,542,775,399,560,931,155,413,870],[589,862,833,668,141,592,48,308,932,5,436,915,974,860,747,160],[890,961,566,809,328,84,224,387,536,915,858,189,758,404,523,483],[442,938,49,596,725,233,13,2,45,661,297,766,335,713,605,629],[728,574,398,437,53,257,629,116,134,249,428,929,845,196,906,745],[813,422,989,350,1]]
def bRowA_181 : List Nat := List.flatten [[88,841,634,636,274,757,485,118,75,167,577,42,842,862,360,398],[276,862,483,887,796,78,288,211,1004,444,70,27,154,438,33,923],[922,170,392,760,60,267,596,278,365,316,63,945,977,740,145,51],[184,530,780,338,922,954,224,682,447,98,265,476,989,413,150,304],[188,703,645,770,50,388,44,649,938,839,4,378,949,821,90,751],[46,119,146,361,834,325,595,125,283,454,218,543,571,312,302,592],[43,178,217,853,784,264,691,924,864,544,944,604,895,313,968,21],[112,456,466,718,834,978,430,584,698,547,90,597,847,473,265,360],[846,331,371,749,842,646,594,611,108,249,999,136,792,422,836,494],[423,664,469,947,887,23,675,2,258,118,582,592,557,335,555,371],[175,523,740,1005,735,903,100,811,735,479,981,840,738,125,708,125],[919,563,776,562,442,1]]
def bRowA_182 : List Nat := List.flatten [[601,466,240,219,164,624,470,972,294,309,20,661,98,689,290,304],[691,313,56,605,706,47,472,48,429,9,650,882,852,7,466,432],[178,232,791,905,374,750,359,694,489,872,171,954,803,189,573,394],[712,759,666,449,308,500,389,742,246,439,641,286,529,341,1007,669],[209,506,864,463,439,308,531,651,741,541,652,977,118,412,53,569],[539,912,454,865,945,470,796,360,111,136,840,236,624,257,404,578],[823,552,763,428,484,113,30,233,597,232,347,678,324,105,171,945],[393,23,823,836,26,522,302,282,334,21,545,759,915,507,540,833],[664,473,691,603,804,602,974,611,182,135,684,751,284,364,414,743],[5,766,349,334,569,84,642,213,838,229,527,899,57,911,530,250],[747,240,687,36,980,873,359,594,940,701,452,178,202,823,972,43],[957,161,6,550,988,670,1]]
def bRowA_183 : List Nat := List.flatten [[178,714,668,633,5,576,993,77,57,690,900,479,57,20,122,590],[544,349,358,192,136,981,509,753,37,320,371,349,109,865,643,148],[221,952,890,966,642,862,902,653,536,520,920,683,22,858,221,273],[709,12,362,520,179,402,338,916,201,757,176,741,804,525,947,992],[477,396,749,65,437,375,470,213,542,338,480,970,877,424,380,306],[123,70,983,263,734,938,656,503,471,780,457,679,22,55,369,928],[801,183,954,923,7,887,277,253,679,384,367,630,674,329,503,467],[413,734,627,53,897,200,234,475,723,684,635,27,268,137,903,526],[859,1008,956,229,967,41,404,608,879,544,549,747,161,476,964,572],[462,962,632,864,595,892,971,135,540,368,608,525,353,18,452,274],[560,993,752,265,785,925,521,748,585,46,528,711,684,964,576,70],[548,103,77,698,733,894,134,1]]
def bRowA_184 : List Nat := List.flatten [[398,655,601,164,688,241,675,336,488,995,660,119,258,873,810,850],[890,304,677,195,457,283,364,847,359,575,214,645,351,655,1007,145],[781,561,823,868,643,561,549,375,104,814,953,936,80,8,548,724],[587,982,202,38,999,264,307,598,954,533,400,732,255,148,560,473],[493,670,206,173,752,131,987,635,603,618,539,976,51,744,1008,523],[98,220,515,545,165,569,349,771,1004,74,950,994,253,392,715,242],[445,478,456,112,971,301,913,558,61,514,383,84,972,33,862,244],[246,539,917,547,711,884,627,986,632,177,167,781,696,40,263,153],[525,399,914,797,581,574,121,543,484,49,1004,644,746,610,566,850],[475,225,149,806,40,772,742,446,794,11,917,832,434,948,302,650],[367,91,301,735,607,536,609,927,384,219,221,712,747,99,914,326],[854,0,450,16,413,22,778,1000,1]]
def bRowA_185 : List Nat := List.flatten [[673,200,935,785,920,561,871,1008,278,196,770,90,455,274,234,457],[375,588,167,129,509,465,74,136,116,82,685,523,267,210,37,368],[1004,217,442,995,450,887,140,473,217,695,918,810,543,795,991,513],[153,985,553,669,863,801,311,716,880,829,128,209,412,697,547,47],[11,567,202,996,67,435,78,913,282,216,117,715,137,949,717,301],[209,182,40,781,297,252,973,615,707,615,183,195,405,409,157,320],[446,721,936,62,452,118,569,96,96,930,347,680,65,771,610,617],[688,245,719,111,881,335,141,214,433,354,13,660,264,680,657,276],[448,228,133,532,795,386,747,247,968,816,361,519,318,254,886,980],[232,1,739,826,333,806,434,267,385,351,384,969,964,401,840,954],[54,575,450,934,425,659,446,634,979,615,49,948,109,59,666,318],[893,445,342,750,97,418,784,534,194,1]]
def bRowA_186 : List Nat := List.flatten [[267,662,411,350,283,729,549,774,16,1000,866,444,20,507,155,425],[109,278,698,870,60,804,21,121,638,864,123,485,824,462,859,23],[150,488,499,356,410,178,849,781,371,802,403,153,122,959,835,504],[323,563,987,917,399,922,70,326,118,849,516,220,792,819,3,385],[167,92,905,260,979,975,849,5,535,657,257,507,578,131,171,54],[422,874,692,374,720,116,24,17,749,994,727,239,408,104,958,824],[457,418,175,392,549,223,955,780,691,647,998,748,2,930,593,337],[912,116,477,306,1005,657,264,975,924,715,551,1001,233,632,545,995],[290,822,852,737,621,717,486,1004,830,250,321,274,738,237,834,141],[36,57,854,935,152,820,498,554,950,817,461,632,367,803,956,306],[72,230,238,44,87,564,919,391,640,618,81,615,868,82,850,570],[978,31,264,341,4,713,400,96,189,607,1]]
def bRowA_187 : List Nat := List.flatten [[890,635,144,341,605,149,532,367,52,846,636,372,1002,465,850,734],[991,973,895,239,1,577,236,538,75,300,269,720,378,870,812,54],[315,729,593,490,522,810,668,129,634,791,489,906,975,890,110,143],[17,709,760,936,357,964,971,540,189,242,332,992,225,119,446,164],[1000,547,178,723,996,432,95,170,228,524,998,910,738,918,243,292],[257,296,7,450,686,47,183,824,627,833,689,86,25,283,410,590],[574,248,788,226,429,843,25,658,888,781,741,98,268,18,707,395],[240,540,178,785,171,922,501,139,508,565,755,244,538,269,341,724],[580,554,545,142,753,192,407,726,906,849,612,531,338,290,223,317],[556,890,253,761,107,490,616,656,967,732,800,178,58,965,704,330],[604,421,79,916,238,9,309,946,866,383,954,699,719,418,805,182],[450,68,313,995,800,632,167,775,145,989,251,1]]
def bRowA_188 : List Nat := List.flatten [[578,359,11,240,557,140,100,544,142,859,17,720,198,841,734,766],[996,334,839,30,420,788,885,582,699,782,462,116,151,33,371,368],[838,707,639,138,279,462,294,41,13,352,790,419,595,144,666,914],[913,197,389,547,899,260,130,90,392,645,731,427,50,735,548,394],[477,32,583,720,256,356,456,896,82,284,882,518,185,662,240,448],[944,196,716,919,402,935,203,347,584,91,75,630,73,273,65,11],[371,213,99,673,959,790,540,11,831,211,920,970,792,929,415,203],[368,970,54,747,754,470,645,359,441,812,268,405,538,788,354,138],[142,663,401,59,620,485,1008,77,666,886,846,470,80,725,136,528],[534,360,506,166,696,878,988,73,596,1004,434,206,698,117,675,80],[33,571,450,959,530,991,372,627,764,500,714,751,844,993,299,859],[237,620,21,582,729,612,587,835,161,695,259,604,1]]
def bRowA_189 : List Nat := List.flatten [[297,601,238,174,331,254,509,573,758,84,62,531,87,206,371,54],[856,755,346,620,622,677,734,301,425,952,63,709,112,53,625,672],[446,498,192,613,664,165,910,982,569,160,745,91,719,110,780,354],[370,611,56,846,779,845,681,976,50,391,531,773,884,659,806,776],[102,503,968,391,813,724,41,200,47,260,337,675,901,672,410,834],[568,145,842,647,255,370,444,435,414,90,528,83,989,50,13,757],[777,513,666,706,289,364,331,894,937,376,1008,19,884,651,902,176],[173,297,672,233,905,955,339,307,44,49,977,696,220,486,793,530],[605,507,168,300,247,349,601,930,555,471,33,468,444,70,636,865],[797,200,746,344,124,197,150,555,84,560,708,317,670,81,124,392],[770,709,943,702,978,260,401,356,720,221,984,777,1003,406,511,99],[416,239,796,875,936,439,436,908,215,990,92,8,572,1]]
def bRowA_190 : List Nat := List.flatten [[550,210,847,95,415,364,184,935,246,706,632,868,577,461,403,484],[859,699,710,616,589,251,940,780,712,863,491,135,705,318,553,39],[251,382,481,693,262,545,506,128,88,240,668,359,636,62,674,988],[854,512,492,63,119,756,988,545,656,932,237,881,841,918,709,841],[491,512,351,533,858,472,551,996,43,236,85,985,851,157,337,648],[841,751,395,900,174,853,718,745,858,274,484,154,244,781,804,48],[817,516,991,85,535,944,194,766,464,634,219,871,457,946,970,114],[291,612,422,216,243,519,713,615,633,275,283,496,37,455,675,897],[763,850,40,50,604,842,169,323,977,232,557,685,635,946,650,962],[898,832,29,200,995,433,601,399,157,898,270,568,304,416,455,176],[806,117,539,851,396,739,8,411,864,753,949,627,378,302,1007,628],[974,159,336,986,597,1001,102,914,409,981,936,500,85,516,1]]
def bRowA_191 : List Nat := List.flatten [[900,573,796,568,455,580,48,536,192,554,672,256,917,558,957,121],[814,366,633,994,427,115,483,252,682,115,985,577,772,302,474,5],[467,279,732,674,397,820,202,240,846,977,882,355,811,465,628,713],[987,538,223,276,835,956,383,157,272,689,342,569,247,727,359,785],[90,885,89,722,220,385,710,39,991,421,244,618,658,375,458,173],[335,549,368,290,30,275,261,290,981,234,15,692,473,338,211,928],[454,812,328,423,362,26,524,156,998,105,594,287,54,305,489,1003],[555,995,349,495,965,128,847,111,261,980,843,162,956,882,628,468],[804,587,150,255,516,900,188,348,555,843,658,931,487,61,198,673],[187,970,967,724,327,696,815,258,201,884,431,435,433,222,128,816],[386,710,171,941,892,927,183,179,714,840,292,555,4,613,865,708],[940,207,304,947,869,900,474,721,254,120,236,595,215,830,414,1]]
def bRowA_192 : List Nat := List.flatten [[17,637,874,548,200,222,451,68,90,16,301,63,743,647,516,856],[699,616,701,688,103,361,212,294,392,535,586,421,151,377,820,270],[506,720,405,519,589,315,697,256,517,876,351,932,423,458,692,386],[86,185,291,869,559,240,750,887,20,885,183,585,274,514,352,42],[895,39,255,220,258,531,700,425,669,507,562,783,504,800,537,962],[272,708,9,23,261,80,956,901,275,1005,805,306,893,244,978,16],[960,50,300,743,477,313,725,77,535,819,673,752,11,427,290,760],[765,182,566,29,251,397,146,607,551,173,662,205,686,284,1005,704],[299,178,997,701,381,908,218,809,405,496,26,295,111,960,446,96],[694,52,105,745,640,514,19,880,951,201,532,17,913,862,256,429],[862,432,112,338,992,307,20,91,890,462,774,425,245,120,268,914],[26,397,288,538,515,869,899,167,95,768,238,1006,996,763,424,579],[1]]
def bRowA_193 : List Nat := List.flatten [[196,856,953,658,539,770,26,45,737,972,443,27,794,98,611,401],[495,169,540,986,725,610,679,483,533,970,266,281,913,374,999,345],[145,296,59,107,960,900,380,884,274,340,765,843,218,930,459,745],[224,445,700,0,765,597,257,511,248,273,685,858,482,492,278,664],[457,236,739,973,255,804,205,722,804,854,977,141,490,863,529,735],[394,711,943,309,985,200,658,930,144,629,384,662,176,322,130,989],[90,806,649,498,723,699,652,864,997,532,854,456,624,402,179,908],[781,193,531,988,926,469,48,804,724,948,955,267,367,855,1,635],[979,238,432,938,363,716,543,731,196,435,785,513,353,531,979,249],[367,49,435,577,440,798,234,372,551,162,519,769,239,914,344,351],[129,647,668,461,391,108,342,94,337,399,701,981,225,330,544,217],[870,462,425,28,844,260,694,744,778,699,372,518,466,621,591,665],[620,1]]
def bRowA_194 : List Nat := List.flatten [[44,99,930,436,60,867,533,990,520,864,854,984,377,848,840,519],[581,34,698,215,210,983,954,556,560,176,70,877,264,412,933,942],[647,257,1006,111,261,586,683,80,963,900,555,35,374,630,361,390],[914,336,8,628,149,87,813,487,749,948,808,767,897,363,806,236],[371,956,182,568,531,474,728,861,839,699,631,698,938,686,983,980],[482,179,901,446,52,875,278,260,190,112,182,880,896,234,597,211],[103,63,281,969,749,66,164,621,612,774,743,112,140,658,991,97],[655,661,41,618,80,68,577,825,546,627,819,321,612,148,623,712],[970,686,874,715,518,975,941,336,180,980,929,193,668,173,538,882],[281,485,113,3,343,502,334,884,720,506,705,392,970,646,532,690],[508,766,96,812,951,277,151,1001,581,41,730,122,973,513,985,298],[481,209,152,29,468,662,564,627,375,355,990,668,975,650,120,970],[24,736,1]]
def bRowA_195 : List Nat := List.flatten [[495,577,529,200,535,85,36,436,53,489,35,515,673,224,836,668],[913,716,360,113,57,128,965,886,608,98,821,803,415,433,10,518],[464,129,743,802,330,915,898,932,291,928,683,439,691,708,267,976],[711,626,916,610,356,9,416,979,925,128,850,827,626,464,863,133],[471,955,97,1003,521,851,625,907,885,710,124,630,778,533,659,819],[242,766,290,467,346,626,253,373,88,187,229,342,55,17,956,292],[184,305,665,521,499,236,965,103,715,119,308,272,916,951,616,651],[230,895,203,671,689,996,487,112,59,771,850,305,58,284,451,651],[558,379,410,83,549,380,767,546,267,855,96,379,600,208,209,308],[517,173,210,391,293,225,654,85,106,266,661,135,155,249,521,803],[734,65,183,30,108,583,282,290,431,250,418,113,938,556,204,336],[799,706,738,782,66,483,796,68,362,515,349,986,52,146,607,528],[526,310,843,1]]
def bRowA_196 : List Nat := List.flatten [[246,931,308,758,12,190,869,315,262,430,181,54,991,478,215,429],[120,861,5,250,804,903,243,110,733,250,493,913,524,835,1,242],[251,212,166,430,546,691,94,59,799,292,791,987,367,894,32,470],[683,958,149,201,352,442,381,149,837,346,583,316,996,760,522,302],[323,888,921,494,118,703,273,568,699,855,228,953,730,58,708,498],[720,234,783,393,228,340,1002,997,229,408,9,435,438,155,8,252],[773,490,393,604,752,950,763,885,889,688,52,627,845,618,411,815],[336,338,220,993,464,602,514,644,630,307,809,273,707,742,941,176],[420,6,830,274,761,873,470,184,861,984,756,805,360,144,407,468],[374,563,430,587,369,922,609,897,193,80,62,238,894,986,702,639],[741,794,629,5,735,804,972,911,543,622,831,990,271,422,326,832],[768,453,101,987,305,769,65,435,317,285,29,551,934,752,897,317],[512,447,178,475,1]]
def bRowA_197 : List Nat := List.flatten [[380,344,717,620,352,51,216,234,479,400,545,87,960,881,262,788],[93,720,594,576,757,166,892,328,352,31,121,547,930,7,94,910],[625,231,107,566,975,511,726,938,592,407,127,843,95,28,667,515],[750,551,114,116,105,209,34,444,605,414,330,16,653,784,204,175],[571,954,755,253,945,666,495,82,741,36,201,110,884,110,512,802],[569,11,690,964,821,753,920,207,205,898,625,845,330,64,160,281],[344,771,927,151,272,83,347,47,411,89,601,167,248,378,436,680],[460,770,742,64,716,326,159,386,515,671,903,14,551,716,2,944],[3,983,844,54,641,991,301,370,550,492,183,161,89,923,301,250],[790,527,432,372,139,361,252,882,944,732,870,118,458,537,679,773],[404,267,132,608,712,6,547,87,536,618,482,870,860,45,102,651],[189,989,334,943,544,650,175,720,857,286,418,68,822,645,324,810],[780,678,179,105,567,1]]
def bRowA_198 : List Nat := List.flatten [[6,881,758,629,137,40,314,27,84,357,988,531,172,656,201,740],[661,568,87,564,652,551,859,469,619,409,0,831,530,34,128,687],[425,575,952,899,120,927,905,947,277,773,30,218,16,194,371,98],[883,437,588,608,515,494,1007,259,1002,757,708,207,245,663,298,114],[186,854,512,726,79,590,539,327,778,972,247,865,569,468,243,558],[988,734,363,2,30,101,328,412,396,803,369,788,654,95,921,849],[165,377,13,16,247,810,132,339,773,226,343,431,413,7,695,941],[942,104,823,109,489,577,455,337,213,152,30,875,114,201,876,211],[912,240,673,44,582,74,508,851,687,202,165,629,375,959,612,926],[340,630,411,769,769,231,175,569,452,18,872,901,676,136,18,728],[135,994,108,889,921,458,635,964,699,249,848,699,920,412,89,404],[935,474,898,696,917,198,150,756,795,607,83,508,541,42,479,201],[155,954,635,50,630,378,1]]
def bRowA_199 : List Nat := List.flatten [[165,355,249,809,97,876,20,361,623,912,433,587,817,158,724,714],[420,795,964,466,992,431,782,413,339,51,945,455,472,132,300,928],[628,298,511,408,204,457,372,612,812,568,597,164,201,236,403,964],[957,49,310,942,883,205,248,341,250,1003,884,701,409,1006,939,373],[786,534,253,215,490,17,881,822,971,930,27,572,231,460,466,500],[265,530,309,652,507,963,100,801,355,464,421,805,63,272,731,957],[854,215,974,144,628,778,38,680,64,546,27,946,892,65,177,154],[491,694,812,774,11,12,0,482,278,773,153,195,214,517,286,678],[218,642,965,565,86,709,196,34,123,738,286,705,847,544,816,812],[2,790,809,154,689,587,519,833,698,76,428,633,461,213,701,278],[178,628,164,302,101,11,287,227,52,255,360,98,927,100,276,392],[801,481,230,702,522,858,841,1008,165,61,731,382,918,578,544,698],[688,999,387,300,894,903,618,1]]

def bMatA : List (List Nat) := List.flatten [
  [bRowA_0,bRowA_1,bRowA_2,bRowA_3,bRowA_4,bRowA_5,bRowA_6,bRowA_7,bRowA_8,bRowA_9,bRowA_10,bRowA_11,bRowA_12,bRowA_13,bRowA_14,bRowA_15,bRowA_16,bRowA_17,bRowA_18,bRowA_19],
  [bRowA_20,bRowA_21,bRowA_22,bRowA_23,bRowA_24,bRowA_25,bRowA_26,bRowA_27,bRowA_28,bRowA_29,bRowA_30,bRowA_31,bRowA_32,bRowA_33,bRowA_34,bRowA_35,bRowA_36,bRowA_37,bRowA_38,bRowA_39],
  [bRowA_40,bRowA_41,bRowA_42,bRowA_43,bRowA_44,bRowA_45,bRowA_46,bRowA_47,bRowA_48,bRowA_49,bRowA_50,bRowA_51,bRowA_52,bRowA_53,bRowA_54,bRowA_55,bRowA_56,bRowA_57,bRowA_58,bRowA_59],
  [bRowA_60,bRowA_61,bRowA_62,bRowA_63,bRowA_64,bRowA_65,bRowA_66,bRowA_67,bRowA_68,bRowA_69,bRowA_70,bRowA_71,bRowA_72,bRowA_73,bRowA_74,bRowA_75,bRowA_76,bRowA_77,bRowA_78,bRowA_79],
  [bRowA_80,bRowA_81,bRowA_82,bRowA_83,bRowA_84,bRowA_85,bRowA_86,bRowA_87,bRowA_88,bRowA_89,bRowA_90,bRowA_91,bRowA_92,bRowA_93,bRowA_94,bRowA_95,bRowA_96,bRowA_97,bRowA_98,bRowA_99],
  [bRowA_100,bRowA_101,bRowA_102,bRowA_103,bRowA_104,bRowA_105,bRowA_106,bRowA_107,bRowA_108,bRowA_109,bRowA_110,bRowA_111,bRowA_112,bRowA_113,bRowA_114,bRowA_115,bRowA_116,bRowA_117,bRowA_118,bRowA_119],
  [bRowA_120,bRowA_121,bRowA_122,bRowA_123,bRowA_124,bRowA_125,bRowA_126,bRowA_127,bRowA_128,bRowA_129,bRowA_130,bRowA_131,bRowA_132,bRowA_133,bRowA_134,bRowA_135,bRowA_136,bRowA_137,bRowA_138,bRowA_139],
  [bRowA_140,bRowA_141,bRowA_142,bRowA_143,bRowA_144,bRowA_145,bRowA_146,bRowA_147,bRowA_148,bRowA_149,bRowA_150,bRowA_151,bRowA_152,bRowA_153,bRowA_154,bRowA_155,bRowA_156,bRowA_157,bRowA_158,bRowA_159],
  [bRowA_160,bRowA_161,bRowA_162,bRowA_163,bRowA_164,bRowA_165,bRowA_166,bRowA_167,bRowA_168,bRowA_169,bRowA_170,bRowA_171,bRowA_172,bRowA_173,bRowA_174,bRowA_175,bRowA_176,bRowA_177,bRowA_178,bRowA_179],
  [bRowA_180,bRowA_181,bRowA_182,bRowA_183,bRowA_184,bRowA_185,bRowA_186,bRowA_187,bRowA_188,bRowA_189,bRowA_190,bRowA_191,bRowA_192,bRowA_193,bRowA_194,bRowA_195,bRowA_196,bRowA_197,bRowA_198,bRowA_199]
]

def bRowC_0 : List Nat := List.flatten [[1]]
def bRowC_1 : List Nat := List.flatten [[0,1]]
def bRowC_2 : List Nat := List.flatten [[1008,1008,1]]
def bRowC_3 : List Nat := List.flatten [[0,1008,0,1]]
def bRowC_4 : List Nat := List.flatten [[504,505,504,0,1]]
def bRowC_5 : List Nat := List.flatten [[1,1008,0,0,1007,1]]
def bRowC_6 : List Nat := List.flatten [[503,505,0,0,1,504,1]]
def bRowC_7 : List Nat := List.flatten [[3,1008,0,0,1007,0,1007,1]]
def bRowC_8 : List Nat := List.flatten [[505,503,0,1,0,0,1008,505,1]]
def bRowC_9 : List Nat := List.flatten [[603,202,1008,202,1,0,808,606,202,1]]
def bRowC_10 : List Nat := List.flatten [[1005,0,1008,0,2,1,1,1008,1,2,1]]
def bRowC_11 : List Nat := List.flatten [[673,252,420,252,924,336,337,421,588,925,336,1]]
def bRowC_12 : List Nat := List.flatten [[864,361,433,360,649,648,216,0,0,216,649,576,1]]
def bRowC_13 : List Nat := List.flatten [[1002,762,593,418,591,1004,1008,756,756,755,339,164,344,1]]
def bRowC_14 : List Nat := List.flatten [[474,905,939,801,210,195,644,734,736,370,300,161,105,365,1]]
def bRowC_15 : List Nat := List.flatten [[603,41,679,83,281,680,467,501,864,646,315,42,645,543,686,1]]
def bRowC_16 : List Nat := List.flatten [[382,566,234,516,665,627,775,676,456,725,567,959,333,627,899,393],[1]]
def bRowC_17 : List Nat := List.flatten [[757,1008,252,1008,0,252,252,251,757,756,505,0,253,757,253,0],[506,1]]
def bRowC_18 : List Nat := List.flatten [[786,826,614,0,0,223,773,87,809,831,906,687,797,349,866,114],[584,252,1]]
def bRowC_19 : List Nat := List.flatten [[5,532,444,1008,0,1004,982,849,387,203,580,698,922,808,52,338],[270,616,566,1]]
def bRowC_20 : List Nat := List.flatten [[944,62,67,711,1008,65,823,580,904,636,198,179,303,423,783,469],[674,418,232,299,1]]
def bRowC_21 : List Nat := List.flatten [[656,71,800,138,164,352,32,958,276,341,988,809,594,726,540,666],[814,885,917,708,846,1]]
def bRowC_22 : List Nat := List.flatten [[276,528,862,88,468,275,383,430,533,886,63,715,611,294,347,726],[148,676,50,912,1000,459,1]]
def bRowC_23 : List Nat := List.flatten [[347,664,512,187,523,669,800,218,73,474,969,1000,650,544,302,115],[815,471,262,774,961,475,482,1]]
def bRowC_24 : List Nat := List.flatten [[853,744,39,395,707,560,166,303,212,9,506,701,387,964,504,595],[540,957,115,154,549,247,651,682,1]]
def bRowC_25 : List Nat := List.flatten [[214,337,803,462,493,909,130,707,8,674,175,678,230,790,803,514],[832,176,765,560,13,506,620,16,459,1]]
def bRowC_26 : List Nat := List.flatten [[530,975,386,979,516,380,578,385,172,990,710,80,278,370,433,533],[389,248,199,92,63,579,480,902,382,516,1]]
def bRowC_27 : List Nat := List.flatten [[831,649,219,538,65,96,780,534,666,460,303,892,325,403,275,35],[425,752,706,79,881,947,865,687,183,163,264,1]]
def bRowC_28 : List Nat := List.flatten [[237,810,478,809,122,169,925,605,577,856,427,688,842,358,278,812],[103,57,505,779,930,297,704,153,532,805,351,254,1]]
def bRowC_29 : List Nat := List.flatten [[160,388,28,474,535,782,863,838,333,794,738,527,950,488,877,239],[648,815,364,409,824,212,580,788,704,17,950,871,435,1]]
def bRowC_30 : List Nat := List.flatten [[890,8,130,562,124,710,822,432,487,886,121,23,59,766,537,76],[10,206,795,220,532,169,512,188,776,304,759,522,761,511,1]]
def bRowC_31 : List Nat := List.flatten [[390,32,674,898,177,831,768,427,180,975,407,780,383,735,227,737],[426,945,699,937,913,666,281,488,1004,573,87,585,412,546,10,1]]
def bRowC_32 : List Nat := List.flatten [[788,644,668,939,656,595,741,160,526,855,773,393,249,892,208,828],[738,588,629,602,297,912,249,570,310,314,774,968,981,71,499,355],[1]]
def bRowC_33 : List Nat := List.flatten [[658,106,475,335,239,57,174,433,390,819,412,536,448,866,880,213],[642,634,189,210,809,841,333,941,377,556,264,802,795,148,337,46],[996,1]]
def bRowC_34 : List Nat := List.flatten [[151,17,469,326,230,518,119,404,231,472,865,459,750,127,656,487],[503,786,603,166,619,274,25,840,523,757,128,434,91,594,413,574],[825,654,1]]
def bRowC_35 : List Nat := List.flatten [[794,764,198,46,503,844,423,530,270,54,997,514,62,710,783,227],[781,219,191,788,980,729,351,505,165,515,250,256,2,62,327,822],[616,116,104,1]]
def bRowC_36 : List Nat := List.flatten [[648,316,102,972,318,82,69,166,438,746,120,857,869,290,140,869],[848,317,504,874,616,284,958,985,602,403,976,579,954,423,137,823],[484,135,188,220,1]]
def bRowC_37 : List Nat := List.flatten [[427,132,894,168,501,110,768,921,903,210,386,625,174,780,117,269],[388,167,695,128,215,139,756,710,571,992,948,966,898,948,358,55],[811,435,20,534,818,1]]
def bRowC_38 : List Nat := List.flatten [[976,28,784,601,158,191,519,497,454,902,938,593,443,650,340,363],[372,341,936,954,735,14,389,977,220,878,222,373,69,201,729,191],[145,635,33,243,861,164,1]]
def bRowC_39 : List Nat := List.flatten [[729,724,768,174,718,264,436,608,720,298,939,96,56,682,174,443],[917,499,995,843,307,847,421,258,919,9,880,138,387,614,343,691],[853,930,581,316,797,300,1003,1]]
def bRowC_40 : List Nat := List.flatten [[445,626,701,877,771,828,895,638,985,66,169,683,984,938,455,613],[337,532,314,897,93,352,633,470,24,591,731,869,971,2,483,208],[493,934,395,372,954,316,365,225,1]]
def bRowC_41 : List Nat := List.flatten [[40,639,936,411,669,622,126,504,611,796,451,815,134,120,463,141],[242,578,476,344,886,116,470,822,966,38,119,208,449,108,621,883],[135,942,914,639,757,767,959,845,926,1]]
def bRowC_42 : List Nat := List.flatten [[460,840,422,403,524,40,829,715,470,897,867,676,88,902,681,896],[991,427,439,299,369,636,279,688,708,478,612,929,693,368,432,337],[39,586,794,495,542,263,532,555,858,318,1]]
def bRowC_43 : List Nat := List.flatten [[797,102,527,129,443,205,609,530,876,730,65,808,746,691,663,797],[208,500,820,980,471,9,983,763,762,535,571,401,697,32,794,693],[126,465,110,385,709,120,84,572,919,88,993,1]]
def bRowC_44 : List Nat := List.flatten [[458,392,919,738,4,627,231,164,797,540,780,19,383,928,236,882],[441,665,243,411,541,948,997,829,1000,723,425,775,843,481,45,12],[60,950,992,1008,592,23,425,485,968,636,731,878,1]]
def bRowC_45 : List Nat := List.flatten [[560,777,415,341,811,278,975,312,591,63,15,530,859,394,31,66],[803,344,668,286,845,611,394,389,949,824,682,462,533,352,888,721],[494,608,575,257,547,252,911,1005,111,768,977,372,862,1]]
def bRowC_46 : List Nat := List.flatten [[699,57,305,95,503,432,935,757,177,467,17,730,230,18,781,795],[368,31,683,972,922,361,552,384,516,684,717,0,801,134,298,307],[760,330,491,205,624,384,95,638,638,150,901,965,154,875,1]]
def bRowC_47 : List Nat := List.flatten [[70,136,964,402,899,278,803,767,496,374,276,927,103,991,19,616],[620,430,433,798,822,559,414,865,249,931,338,943,662,592,178,468],[178,694,564,567,138,704,655,331,856,480,1001,881,591,492,851,1]]
def bRowC_48 : List Nat := List.flatten [[749,539,339,222,615,207,621,478,777,499,881,92,154,931,4,22],[607,43,45,417,335,758,880,42,156,399,287,152,543,800,323,707],[555,357,753,612,965,413,675,721,42,267,597,602,158,114,279,120],[1]]
def bRowC_49 : List Nat := List.flatten [[253,700,132,804,415,186,544,976,533,964,745,10,909,127,189,839],[807,326,736,91,198,28,757,212,495,163,973,18,667,198,940,455],[29,900,772,115,73,973,522,735,363,535,704,125,106,896,234,757],[995,1]]
def bRowC_50 : List Nat := List.flatten [[709,858,952,272,474,180,703,863,571,163,938,872,301,51,41,198],[83,668,621,824,518,733,919,844,374,876,957,74,86,386,270,373],[87,42,546,5,915,571,232,785,537,884,623,688,191,748,659,492],[806,512,1]]
def bRowC_51 : List Nat := List.flatten [[620,442,544,836,708,951,145,957,774,66,394,455,247,233,0,585],[894,149,158,605,253,439,1008,284,186,411,840,294,332,631,769,315],[785,799,550,158,266,932,553,646,674,468,821,983,810,232,653,875],[892,129,687,1]]
def bRowC_52 : List Nat := List.flatten [[556,135,646,364,298,451,605,530,458,368,384,505,958,652,121,541],[219,539,892,203,87,811,949,172,778,22,847,598,933,46,829,857],[921,646,332,121,142,219,235,629,648,50,855,789,140,215,895,374],[908,512,450,792,1]]
def bRowC_53 : List Nat := List.flatten [[574,327,992,947,92,134,413,185,762,266,668,776,943,607,662,323],[89,730,688,232,122,351,982,507,830,400,543,265,537,580,75,701],[705,526,510,1001,659,717,898,618,31,833,571,250,985,671,489,230],[39,483,879,598,667,1]]
def bRowC_54 : List Nat := List.flatten [[577,459,173,374,755,584,875,64,978,361,556,906,855,288,971,777],[772,741,254,236,343,406,89,806,377,727,692,156,245,805,891,549],[447,228,958,910,658,505,793,641,434,8,144,454,864,385,152,853],[887,808,734,536,730,176,1]]
def bRowC_55 : List Nat := List.flatten [[163,481,392,507,351,139,946,873,134,429,334,598,568,391,643,968],[51,921,278,80,387,505,71,844,705,199,735,125,783,239,610,321],[356,963,620,951,936,309,4,261,981,695,987,462,328,571,604,527],[597,744,528,23,196,310,713,1]]
def bRowC_56 : List Nat := List.flatten [[231,255,518,748,679,668,257,417,72,981,769,250,220,374,181,548],[99,335,492,421,946,442,59,959,371,429,709,622,40,734,554,523],[467,806,551,260,902,919,392,164,314,164,816,590,437,806,139,372],[870,694,344,677,38,449,88,95,1]]
def bRowC_57 : List Nat := List.flatten [[126,551,879,371,319,82,14,999,346,835,223,371,963,789,303,262],[831,359,836,696,830,875,591,242,818,351,323,528,674,680,11,492],[141,148,741,89,269,926,525,306,30,293,757,395,301,873,158,901],[156,707,109,178,644,45,667,188,197,1]]
def bRowC_58 : List Nat := List.flatten [[931,882,430,858,885,880,2,190,111,529,282,993,837,553,854,599],[843,692,837,762,928,846,652,222,589,11,945,823,661,660,144,498],[608,723,715,432,736,76,98,112,560,123,741,444,24,62,617,35],[267,355,295,978,692,521,781,719,481,779,1]]
def bRowC_59 : List Nat := List.flatten [[517,559,523,982,549,670,996,309,608,380,3,257,435,368,1002,489],[170,195,657,495,482,472,354,253,610,612,386,516,277,648,254,301],[212,542,317,331,761,53,994,156,549,265,961,95,9,42,685,562],[301,581,580,699,70,24,507,779,457,877,984,1]]
def bRowC_60 : List Nat := List.flatten [[859,844,955,64,775,919,762,962,900,143,248,271,99,32,695,530],[770,424,329,628,946,595,251,420,85,303,76,121,7,405,158,405],[596,757,147,389,254,368,110,535,366,494,415,7,21,297,427,590],[612,450,7,674,225,138,61,769,87,1006,786,449,1]]
def bRowC_61 : List Nat := List.flatten [[971,643,248,577,472,341,126,189,943,890,321,714,245,483,73,489],[813,397,738,418,367,664,159,576,851,85,43,943,557,80,772,51],[157,127,343,180,284,365,268,122,173,664,749,50,813,954,16,493],[66,884,828,587,53,352,804,776,272,739,761,975,330,1]]
def bRowC_62 : List Nat := List.flatten [[263,202,920,611,936,215,2,69,607,642,108,103,400,68,754,861],[839,722,806,15,800,931,448,726,957,498,432,802,44,198,877,993],[110,253,474,810,844,634,549,576,377,288,546,909,387,536,764,721],[555,21,619,456,777,170,867,431,528,274,312,460,883,310,1]]
def bRowC_63 : List Nat := List.flatten [[659,157,759,886,445,733,401,835,409,744,981,74,561,279,223,582],[575,915,549,532,826,557,680,146,970,394,770,448,902,699,753,632],[176,305,388,672,18,487,504,286,204,871,50,225,187,359,755,544],[496,141,1,287,698,261,492,427,341,569,250,248,912,168,811,1]]
def bRowC_64 : List Nat := List.flatten [[799,547,650,272,987,272,773,551,237,689,939,652,419,774,264,249],[119,63,486,661,223,689,129,260,898,944,367,592,387,891,322,713],[652,314,783,539,837,236,2,743,906,258,149,219,380,411,849,810],[973,860,150,216,143,451,672,622,765,123,147,246,718,320,77,436],[1]]
def bRowC_65 : List Nat := List.flatten [[404,336,135,187,510,859,773,725,316,489,790,711,901,753,589,440],[531,634,466,184,127,436,482,360,321,783,740,1000,570,434,835,845],[598,212,771,687,560,289,608,868,951,158,932,321,344,933,714,803],[480,382,427,690,327,105,524,178,696,727,97,371,0,408,820,654],[877,1]]
def bRowC_66 : List Nat := List.flatten [[851,802,996,490,49,178,631,177,1000,452,400,739,208,491,852,96],[825,873,101,231,616,637,549,289,958,220,524,700,667,982,971,7],[887,535,741,0,496,900,703,601,703,1001,410,581,81,711,753,560],[843,227,96,258,179,144,119,795,513,159,225,459,685,483,899,926],[568,394,1]]
def bRowC_67 : List Nat := List.flatten [[849,221,998,919,892,794,137,425,478,117,513,450,890,552,951,192],[652,119,67,1002,878,984,587,322,668,472,843,475,34,77,610,795],[404,13,149,263,368,744,221,240,826,719,866,193,138,103,493,717],[194,130,24,908,51,615,483,870,825,15,651,964,739,643,942,754],[247,682,144,1]]
def bRowC_68 : List Nat := List.flatten [[223,130,446,855,226,988,873,78,350,783,985,160,234,98,264,426],[349,57,957,463,633,478,791,27,779,973,924,12,120,69,209,342],[502,734,729,93,367,164,429,383,387,766,22,772,700,929,69,269],[693,757,926,849,765,458,802,513,136,838,686,159,142,765,537,863],[560,136,93,1007,1]]
def bRowC_69 : List Nat := List.flatten [[743,945,23,350,925,548,828,552,280,280,338,511,64,404,78,213],[542,212,140,527,307,575,393,81,434,834,669,379,826,117,250,920],[171,650,154,50,226,535,483,387,418,155,211,651,766,717,204,6],[781,426,93,120,603,733,751,922,794,76,750,931,809,188,630,815],[267,900,755,854,337,1]]
def bRowC_70 : List Nat := List.flatten [[773,475,353,723,971,632,240,386,290,7,810,793,114,999,902,836],[153,704,240,510,49,178,375,626,763,780,6,821,137,319,63,144],[185,930,778,10,820,145,906,254,211,776,539,417,892,206,35,98],[792,1007,304,120,615,600,710,829,162,975,131,1004,627,979,3,463],[365,210,834,522,31,277,1]]
def bRowC_71 : List Nat := List.flatten [[766,313,980,271,162,128,888,702,322,689,388,621,706,437,14,137],[578,851,393,331,138,216,333,799,337,374,277,424,858,692,829,315],[131,102,875,264,563,101,954,389,472,708,474,477,969,1004,215,458],[495,354,398,952,988,352,623,839,196,838,561,737,191,800,971,330],[395,782,185,351,582,401,902,1]]
def bRowC_72 : List Nat := List.flatten [[975,545,478,54,107,908,378,973,195,621,466,576,636,993,359,178],[581,155,89,706,824,822,737,533,977,922,70,211,253,473,464,827],[702,214,543,51,61,695,873,654,662,823,681,6,626,833,150,280],[902,668,79,471,1004,652,412,584,896,710,163,362,692,184,984,678],[114,780,461,918,798,494,620,337,1]]
def bRowC_73 : List Nat := List.flatten [[502,642,807,125,686,364,92,653,308,552,63,481,888,17,324,454],[415,725,464,738,570,762,294,168,134,978,323,968,536,669,25,513],[538,960,5,739,454,76,359,282,48,624,63,763,567,236,696,408],[989,836,575,512,768,584,222,342,745,829,285,517,502,212,700,134],[826,966,576,217,470,948,13,245,504,1]]
def bRowC_74 : List Nat := List.flatten [[682,729,422,332,299,606,236,62,703,586,46,782,52,446,581,572],[820,988,325,36,389,392,764,789,272,484,244,84,418,495,685,269],[590,690,362,162,656,399,315,355,955,318,709,187,560,548,627,4],[639,15,652,970,92,811,453,135,451,632,972,885,407,631,184,855],[326,684,144,449,376,220,789,103,538,191,1]]
def bRowC_75 : List Nat := List.flatten [[899,1006,551,501,458,103,292,953,8,734,235,216,295,672,457,625],[385,527,747,146,500,468,761,621,353,252,131,694,980,843,260,121],[332,975,404,520,628,849,149,908,290,910,487,351,308,3,563,863],[846,103,56,182,937,502,149,583,89,354,722,637,955,332,816,779],[397,58,1000,29,490,126,552,978,119,649,172,1]]
def bRowC_76 : List Nat := List.flatten [[655,564,866,448,946,248,353,148,621,318,710,818,865,507,1007,159],[92,202,362,73,130,73,2,426,572,672,436,388,352,241,254,401],[395,979,484,333,814,914,529,477,415,112,407,710,197,996,378,619],[798,131,619,869,223,336,976,275,524,422,359,978,642,646,759,546],[807,804,34,408,658,384,318,504,664,999,935,62,1]]
def bRowC_77 : List Nat := List.flatten [[702,481,763,881,868,236,334,85,653,458,524,64,612,789,286,509],[325,706,513,953,63,604,334,707,323,342,122,904,302,652,723,399],[950,401,580,380,380,617,824,950,588,266,480,809,663,44,278,643],[987,579,285,260,844,291,414,672,71,392,210,863,364,405,2,329],[693,144,137,751,343,859,331,661,43,448,66,620,489,1]]
def bRowC_78 : List Nat := List.flatten [[953,43,963,120,699,834,481,432,244,295,869,840,945,381,593,110],[347,604,83,63,520,557,158,94,83,957,28,855,678,855,806,13],[1004,862,783,961,849,358,677,70,349,589,900,840,107,829,611,58],[344,396,593,191,155,874,164,409,356,543,923,413,659,591,156,192],[883,820,744,232,233,890,460,373,355,184,622,759,350,680,1]]
def bRowC_79 : List Nat := List.flatten [[871,641,710,407,197,187,900,330,517,459,101,660,91,121,19,786],[308,460,589,88,559,980,480,699,790,226,727,99,116,375,636,168],[592,510,912,100,657,291,298,795,89,119,430,107,558,369,176,334],[599,596,521,794,824,326,465,477,627,811,455,565,526,98,999,435],[764,448,844,561,356,344,189,378,726,149,45,228,943,661,55,1]]
def bRowC_80 : List Nat := List.flatten [[434,492,751,262,786,82,625,376,15,907,643,851,87,924,364,62],[867,220,845,710,707,396,514,757,92,262,657,455,947,33,64,664],[563,412,542,249,9,554,371,275,592,515,902,571,672,974,259,477],[755,593,766,71,803,657,1005,784,442,782,152,632,132,1001,604,790],[398,406,212,607,824,160,563,429,582,616,764,208,976,407,681,286],[1]]
def bRowC_81 : List Nat := List.flatten [[981,697,867,73,627,754,117,873,849,960,939,304,491,50,121,219],[336,44,847,300,799,208,343,662,56,379,339,668,89,770,412,417],[199,849,88,567,255,182,738,565,456,397,927,621,72,776,397,533],[397,743,767,564,168,370,463,571,469,259,820,821,44,495,730,258],[877,816,350,285,488,22,43,285,53,167,426,123,3,193,117,548],[661,1]]
def bRowC_82 : List Nat := List.flatten [[833,148,539,703,520,724,564,986,311,706,436,974,990,639,687,820],[422,874,84,620,217,764,267,336,87,344,545,390,114,839,226,413],[300,183,4,183,606,899,151,314,476,111,705,122,120,509,880,408],[713,967,593,807,181,116,173,799,807,639,342,286,662,728,499,62],[580,490,275,1002,332,488,644,684,864,991,771,667,284,718,687,750],[302,3,1]]
def bRowC_83 : List Nat := List.flatten [[46,872,2,270,442,753,304,155,551,539,429,263,957,469,432,701],[863,965,793,18,397,853,979,643,1003,956,139,815,581,386,486,274],[504,387,271,233,843,647,699,943,258,978,573,492,427,57,994,53],[507,803,381,404,448,404,911,961,436,467,175,129,629,528,615,910],[64,906,136,86,81,90,415,155,906,299,475,753,628,279,971,152],[238,780,537,1]]
def bRowC_84 : List Nat := List.flatten [[127,984,192,217,994,588,702,267,466,711,930,326,916,1008,271,888],[927,878,776,235,734,539,645,76,617,330,591,828,264,389,67,995],[657,529,763,694,203,594,506,655,91,465,745,164,558,231,714,863],[715,214,988,49,28,624,505,931,887,597,298,492,796,179,556,251],[398,407,941,700,686,835,771,712,23,957,802,54,795,391,706,815],[103,330,38,482,1]]
def bRowC_85 : List Nat := List.flatten [[79,723,762,111,739,171,941,155,970,872,28,663,109,820,674,889],[458,610,418,889,679,50,808,350,567,634,585,583,204,728,649,808],[3,456,112,210,494,67,163,764,106,923,213,14,980,961,935,359],[888,609,202,351,754,605,411,22,905,223,999,481,197,392,463,11],[333,101,80,599,690,384,988,168,243,443,964,938,728,738,970,556],[153,390,408,346,535,1]]
def bRowC_86 : List Nat := List.flatten [[716,114,59,198,885,286,291,929,150,505,364,708,418,991,47,726],[122,519,521,229,397,298,577,913,287,823,604,909,507,463,882,752],[636,907,559,982,202,945,894,97,612,196,291,364,343,946,956,736],[526,719,101,146,266,350,730,499,49,366,669,184,390,494,703,271],[188,957,577,37,381,560,906,816,417,39,641,474,463,610,974,163],[124,199,428,156,655,693,1]]
def bRowC_87 : List Nat := List.flatten [[146,785,303,483,511,393,54,999,992,439,259,941,118,742,900,547],[208,592,431,558,590,249,280,517,154,425,442,352,653,944,644,487],[757,885,610,208,38,806,206,926,395,797,512,906,783,323,226,473],[359,987,492,545,181,142,470,591,574,165,445,324,821,339,899,887],[440,180,306,839,272,380,508,336,186,934,333,870,911,493,965,239],[487,918,615,394,307,493,564,1]]
def bRowC_88 : List Nat := List.flatten [[208,877,346,606,638,815,124,383,300,552,273,641,855,167,309,635],[839,972,646,328,734,684,34,923,57,118,729,599,593,349,57,326],[265,776,302,441,120,594,249,281,1000,571,242,249,124,426,140,484],[60,376,136,328,526,454,25,647,410,934,4,111,857,804,862,549],[120,930,535,504,49,597,853,799,525,707,212,914,153,81,53,557],[619,909,368,683,134,262,25,974,1]]
def bRowC_89 : List Nat := List.flatten [[851,484,472,888,8,748,151,452,802,37,590,446,449,70,137,25],[467,235,798,403,120,21,240,556,143,155,180,694,242,352,528,438],[268,295,247,944,806,726,646,573,473,885,22,655,993,407,823,169],[395,868,888,718,902,512,17,525,361,263,870,881,13,236,299,768],[317,649,600,166,614,875,879,1002,85,11,326,642,496,380,843,338],[580,290,639,659,904,956,845,759,470,1]]
def bRowC_90 : List Nat := List.flatten [[181,751,908,775,666,82,508,27,359,396,413,74,618,1002,849,246],[566,491,704,917,269,808,57,773,574,882,797,917,530,480,867,568],[507,858,231,27,281,485,528,818,955,195,199,918,335,29,861,71],[827,609,332,955,915,161,747,691,783,43,442,754,596,174,649,577],[868,359,61,664,864,745,102,636,229,904,313,613,894,604,136,604],[170,891,739,309,313,354,939,734,694,31,1]]
def bRowC_91 : List Nat := List.flatten [[430,57,905,704,654,773,314,20,199,340,834,648,695,605,852,209],[488,559,443,648,937,915,217,639,660,897,844,39,154,346,894,861],[351,407,330,329,718,33,272,385,13,752,637,874,645,984,550,400],[1007,703,879,101,86,391,466,855,60,209,573,296,172,273,795,923],[176,886,136,865,973,707,425,917,1004,252,703,712,78,48,281,806],[784,172,260,381,482,895,852,751,789,673,777,1]]
def bRowC_92 : List Nat := List.flatten [[757,24,187,342,782,1,505,38,262,132,108,753,633,33,772,923],[477,873,32,15,8,319,245,273,285,4,663,978,899,108,672,108],[74,417,40,468,573,371,523,882,855,271,462,971,261,438,642,452],[375,141,54,504,971,329,115,37,259,199,64,990,660,498,828,807],[160,716,190,797,912,969,443,721,941,911,688,896,97,736,830,884],[400,239,1005,292,451,573,1007,208,29,363,398,733,1]]
def bRowC_93 : List Nat := List.flatten [[98,176,810,965,527,375,291,111,554,769,154,742,129,560,936,774],[265,46,575,268,241,874,24,62,573,759,3,675,328,212,748,818],[647,923,792,520,857,334,72,788,783,921,384,393,429,335,120,260],[69,793,480,86,142,145,484,310,537,669,333,447,693,971,103,634],[678,200,342,921,861,404,851,11,974,156,965,458,128,296,231,832],[441,658,71,763,544,756,591,730,328,902,739,107,214,1]]
def bRowC_94 : List Nat := List.flatten [[531,180,653,132,248,488,149,167,629,809,475,788,222,985,926,537],[188,978,825,890,580,602,958,710,28,32,683,891,753,410,619,479],[788,796,919,952,145,28,110,1005,359,670,650,103,741,460,455,956],[602,830,997,933,335,964,183,799,279,197,897,964,181,758,545,852],[272,502,34,896,909,442,163,147,496,323,826,528,62,893,422,406],[983,667,978,540,552,732,342,301,568,152,514,939,416,638,1]]
def bRowC_95 : List Nat := List.flatten [[312,66,435,548,166,683,755,99,976,768,896,49,493,901,112,284],[147,449,188,638,925,152,13,209,584,9,182,216,214,889,463,76],[476,290,619,144,79,892,694,743,230,7,699,685,451,267,239,424],[395,937,40,264,428,148,732,288,397,112,696,523,996,436,184,874],[886,888,869,100,44,906,793,386,465,405,189,695,832,619,638,707],[356,243,976,319,486,789,722,852,648,948,770,1000,966,460,747,1]]
def bRowC_96 : List Nat := List.flatten [[164,586,624,15,131,539,81,413,739,36,433,990,512,36,30,853],[2,777,554,282,122,140,695,303,674,594,196,248,454,185,196,840],[673,748,147,255,733,576,820,983,912,717,878,1000,443,193,700,413],[516,526,1000,973,34,438,660,632,491,385,205,876,559,39,743,906],[21,100,888,98,14,930,924,489,850,108,28,817,152,775,243,815],[201,191,76,864,480,71,517,836,484,783,104,420,183,482,370,734],[1]]
def bRowC_97 : List Nat := List.flatten [[844,30,543,590,741,522,733,438,746,517,545,399,996,198,459,777],[374,771,103,24,106,36,840,388,219,35,240,250,935,332,547,979],[439,108,676,163,773,550,259,811,131,872,432,581,962,471,791,294],[157,411,880,584,749,523,670,511,194,561,629,677,714,270,722,843],[318,23,853,242,203,427,262,44,315,261,324,98,872,240,460,242],[266,16,17,715,911,730,155,873,77,269,332,198,91,470,936,135],[625,1]]
def bRowC_98 : List Nat := List.flatten [[160,281,605,231,663,42,14,865,624,2,584,150,391,117,746,285],[818,425,769,667,870,63,898,382,63,759,780,442,606,376,995,381],[510,39,471,834,992,75,436,656,271,444,65,660,896,328,290,226],[174,953,76,597,163,9,166,654,163,106,625,296,468,387,956,95],[839,34,209,741,497,852,349,224,842,485,129,487,401,145,949,700],[39,901,74,176,191,566,492,922,916,481,789,317,910,930,571,236],[4,559,1]]
def bRowC_99 : List Nat := List.flatten [[742,960,329,39,662,912,110,335,72,667,110,996,590,194,265,478],[244,677,726,199,194,277,947,240,121,332,585,961,235,618,978,73],[245,912,772,298,291,268,873,876,783,487,893,178,328,496,558,170],[713,709,394,952,235,787,579,681,46,499,681,246,177,664,527,851],[957,537,896,9,246,440,300,108,590,617,225,191,743,278,425,881],[523,134,162,524,23,562,796,373,136,516,320,711,532,75,1006,606],[997,368,605,1]]
def bRowC_100 : List Nat := List.flatten [[240,547,394,545,587,834,805,919,298,66,131,104,149,340,59,908],[863,433,369,403,768,442,601,315,26,54,720,743,267,108,192,357],[521,265,285,834,596,383,948,510,691,156,772,787,883,978,672,430],[115,661,785,242,347,344,499,378,176,129,174,237,305,252,225,112],[492,842,637,862,668,942,875,301,250,71,19,305,58,634,243,922],[952,260,146,981,270,845,682,248,255,370,614,726,608,878,499,839],[799,243,878,802,1]]
def bRowC_101 : List Nat := List.flatten [[493,714,147,606,630,264,607,514,680,284,158,940,676,26,941,566],[436,132,423,257,98,70,228,560,829,168,534,757,331,60,587,541],[931,737,744,208,99,187,176,866,246,193,175,586,600,955,238,765],[740,834,328,620,937,952,668,692,681,147,173,402,619,160,192,62],[515,778,777,247,836,85,692,112,467,21,547,24,22,707,150,877],[963,617,898,401,296,27,519,181,844,831,368,584,60,363,298,80],[4,913,1005,702,778,1]]
def bRowC_102 : List Nat := List.flatten [[870,386,1004,914,863,21,507,537,154,316,166,925,845,425,365,185],[815,786,496,609,46,786,398,634,645,54,368,845,476,976,661,368],[732,667,996,478,18,274,429,662,414,148,683,54,18,514,500,971],[716,189,761,565,152,349,908,730,315,990,88,311,479,488,715,610],[385,112,225,913,380,444,392,936,226,1004,128,863,433,248,679,269],[246,252,17,828,867,485,341,348,303,358,45,318,367,140,315,989],[357,726,340,188,865,898,1]]
def bRowC_103 : List Nat := List.flatten [[917,324,850,123,484,797,841,628,134,450,603,667,606,492,905,264],[894,884,628,734,541,416,84,489,193,226,919,323,120,483,646,304],[116,235,92,963,135,160,66,102,664,426,274,806,322,35,28,159],[90,773,212,421,377,487,103,745,345,824,304,168,877,779,438,100],[266,32,900,478,230,601,541,300,46,367,139,264,681,772,29,497],[914,105,401,772,712,637,541,653,767,33,14,558,483,346,166,280],[382,868,564,966,420,421,742,1]]
def bRowC_104 : List Nat := List.flatten [[741,340,919,969,963,671,801,809,362,419,443,532,49,470,220,506],[625,241,653,674,270,295,114,196,236,318,50,200,767,500,1003,468],[338,190,47,87,919,654,704,812,137,440,430,688,843,568,700,830],[560,776,914,271,409,54,752,220,879,796,815,263,64,191,745,439],[890,945,390,123,741,468,166,889,399,654,822,765,822,745,755,393],[1005,809,702,187,158,576,49,670,923,965,255,832,120,891,737,837],[842,891,492,68,117,469,999,532,1]]
def bRowC_105 : List Nat := List.flatten [[699,210,475,542,891,369,352,338,407,969,268,300,506,66,710,422],[112,708,85,692,876,897,105,391,299,776,237,904,978,215,1001,612],[208,425,934,467,989,466,673,620,532,245,557,751,494,234,970,527],[786,343,458,131,812,851,179,914,573,54,276,800,585,196,91,435],[261,267,514,958,197,911,162,250,204,337,568,698,918,456,249,539],[332,511,511,715,553,225,203,614,293,46,896,328,209,568,402,305],[842,258,841,191,592,534,485,607,110,1]]
def bRowC_106 : List Nat := List.flatten [[167,483,702,776,461,460,954,706,232,854,954,894,464,462,636,66],[308,792,670,32,298,359,170,566,61,523,654,492,133,535,289,18],[908,630,496,286,347,742,466,856,553,485,423,407,121,262,567,453],[65,900,310,386,215,957,463,56,165,657,848,452,356,229,122,999],[205,719,374,128,842,884,737,635,776,232,124,744,216,895,430,767],[946,330,612,179,576,27,988,555,730,490,354,985,566,882,504,357],[301,283,491,349,650,707,750,261,1007,804,1]]
def bRowC_107 : List Nat := List.flatten [[660,185,572,693,568,887,271,564,197,859,715,894,972,180,332,786],[250,272,106,159,731,103,850,606,31,74,957,261,303,235,142,835],[588,270,1003,964,830,290,158,447,379,782,526,34,881,15,555,917],[443,411,831,908,711,770,959,980,970,253,554,24,853,373,1005,1007],[159,277,686,936,371,457,1008,58,175,742,485,850,268,777,782,209],[766,455,149,295,40,736,527,55,158,74,537,842,402,35,803,992],[64,783,17,575,271,384,572,296,406,298,984,1]]
def bRowC_108 : List Nat := List.flatten [[542,108,338,253,231,643,321,809,543,977,926,695,48,945,888,247],[516,299,788,516,560,934,117,34,776,393,87,480,697,630,689,437],[368,680,672,846,55,44,279,497,406,491,282,543,97,721,502,634],[122,776,57,520,100,46,49,192,329,853,857,213,718,312,546,408],[901,281,290,425,786,442,672,34,324,94,109,525,506,375,324,2],[277,247,591,915,137,498,646,604,738,181,804,617,794,730,166,957],[1005,45,351,272,982,250,302,914,997,216,138,268,1]]
def bRowC_109 : List Nat := List.flatten [[764,562,372,322,867,851,199,941,924,436,238,141,919,511,228,456],[519,494,671,980,352,915,599,606,32,624,25,520,221,800,560,580],[108,939,973,142,868,449,543,205,690,539,1008,331,923,334,96,435],[903,698,780,781,567,254,737,972,445,638,524,952,960,274,643,363],[148,510,719,627,816,109,185,901,733,721,190,380,375,898,898,633],[123,940,953,141,799,607,496,182,19,924,293,133,993,254,756,653],[796,692,195,63,499,512,663,705,98,351,233,248,314,1]]
def bRowC_110 : List Nat := List.flatten [[889,978,45,458,993,930,1003,349,301,465,41,884,17,742,704,436],[984,465,58,890,249,410,546,734,895,890,657,278,480,594,983,650],[682,799,939,139,102,575,308,353,616,477,254,560,54,656,444,865],[899,356,901,417,930,418,402,587,892,484,664,353,820,515,474,991],[568,84,218,179,840,409,983,989,366,485,411,36,520,481,874,139],[920,81,659,122,410,54,616,955,481,129,329,10,657,985,958,290],[222,593,696,582,82,128,125,847,820,909,565,859,564,843,1]]
def bRowC_111 : List Nat := List.flatten [[268,798,897,629,661,548,928,1002,232,961,143,794,258,90,97,177],[497,705,183,896,153,793,400,138,26,16,667,812,134,842,256,552],[849,949,432,300,657,635,295,596,672,241,443,702,841,1008,151,372],[671,344,493,665,847,750,743,894,41,53,71,601,391,606,277,981],[770,862,848,220,245,763,697,964,264,354,11,871,725,389,655,758],[141,979,692,397,526,414,452,764,459,163,963,660,329,116,179,149],[227,875,913,458,766,210,67,239,123,513,141,673,123,122,700,1]]
def bRowC_112 : List Nat := List.flatten [[670,857,432,19,720,666,915,839,643,949,166,1006,751,379,569,451],[208,21,404,345,151,164,176,663,112,60,275,542,197,514,997,621],[732,853,56,987,316,103,965,79,369,458,394,927,234,318,416,966],[409,675,37,381,475,625,265,813,320,796,231,773,174,717,269,751],[19,450,434,808,113,374,762,19,650,812,294,374,364,942,309,341],[258,40,630,883,626,161,155,970,716,640,754,294,613,861,457,709],[829,991,30,926,222,269,628,240,250,858,432,780,88,108,927,480],[1]]
def bRowC_113 : List Nat := List.flatten [[3,706,128,69,586,668,141,891,446,277,90,331,934,448,697,593],[767,747,117,338,927,26,269,992,374,909,289,881,485,494,395,384],[498,295,520,563,466,596,716,577,408,532,541,465,580,348,543,734],[1006,734,934,379,930,605,40,619,332,773,364,987,997,769,485,959],[97,354,136,133,897,89,282,459,369,945,990,455,630,521,519,836],[620,265,468,62,137,983,977,558,974,145,551,988,500,463,644,293],[69,249,520,848,220,987,284,986,185,977,794,967,766,961,269,910],[623,1]]
def bRowC_114 : List Nat := List.flatten [[477,192,527,225,964,605,56,425,807,355,836,267,823,644,943,646],[211,747,978,670,439,561,401,398,158,1006,148,994,622,319,238,684],[5,1006,759,454,910,423,864,778,360,218,88,110,625,110,477,635],[93,396,679,296,528,788,367,860,20,619,487,764,378,220,226,928],[315,413,120,352,353,642,311,220,450,45,132,58,789,844,498,457],[83,324,818,117,858,174,746,730,650,430,683,872,561,118,396,836],[222,217,255,932,12,590,43,943,153,146,98,6,280,313,672,359],[759,56,1]]
def bRowC_115 : List Nat := List.flatten [[362,6,121,610,880,395,636,106,510,182,772,513,391,180,443,974],[85,49,456,645,266,326,435,308,747,803,221,561,455,31,53,979],[569,485,595,569,931,413,351,70,881,431,702,893,895,687,719,247],[277,842,827,993,885,713,825,233,276,296,582,868,118,612,273,224],[362,576,111,516,496,773,356,534,430,471,805,81,619,222,740,753],[253,728,473,205,446,392,117,339,781,888,255,894,561,780,994,179],[526,12,376,900,624,806,127,858,601,198,787,876,604,49,373,115],[352,840,187,1]]
def bRowC_116 : List Nat := List.flatten [[617,679,454,265,853,580,263,782,147,223,74,38,751,525,672,621],[930,24,889,850,867,574,530,23,12,921,153,316,931,235,128,527],[114,896,490,154,660,387,256,734,645,96,638,49,767,284,761,579],[448,667,29,71,190,452,531,6,629,350,291,664,209,462,46,588],[906,646,240,652,204,842,682,471,650,803,739,470,544,614,171,345],[625,915,366,338,371,978,704,931,253,224,574,370,870,686,659,762],[286,948,167,818,186,910,671,505,224,269,124,844,678,468,48,580],[532,587,944,177,1]]
def bRowC_117 : List Nat := List.flatten [[535,610,698,809,190,606,860,594,544,331,251,990,595,323,533,952],[156,543,166,39,343,1008,570,407,522,569,503,87,546,62,790,965],[439,987,73,711,330,580,653,431,449,429,441,907,233,481,125,751],[874,596,109,351,925,791,827,377,479,119,87,787,288,11,994,141],[606,882,948,50,546,95,637,449,464,42,881,517,139,821,560,499],[646,454,759,293,622,673,330,547,5,61,276,961,699,757,994,438],[765,54,863,893,619,989,177,576,408,561,194,976,423,593,394,189],[238,699,687,555,664,1]]
def bRowC_118 : List Nat := List.flatten [[432,179,667,592,397,722,844,980,530,798,693,898,436,806,861,411],[633,824,527,827,287,649,979,109,691,57,655,616,947,682,726,281],[501,403,595,174,710,422,359,476,64,744,536,969,677,936,12,926],[73,275,882,211,585,254,159,968,2,606,682,819,641,70,340,925],[859,52,729,154,879,933,974,375,853,327,380,706,318,292,626,391],[499,751,705,596,864,661,889,642,316,887,930,749,804,322,142,513],[859,523,372,266,384,244,887,337,994,928,989,59,137,5,752,399],[440,130,741,97,914,116,1]]
def bRowC_119 : List Nat := List.flatten [[288,381,193,46,46,393,788,487,208,381,489,707,466,624,838,537],[18,908,830,529,182,405,938,835,372,219,647,188,902,744,223,925],[989,687,901,849,888,619,518,338,94,151,308,712,190,325,115,958],[211,1008,961,975,533,222,153,578,941,243,253,952,932,329,839,1000],[699,977,393,695,506,86,261,854,532,432,192,332,513,391,123,784],[37,815,350,802,833,903,400,367,424,840,287,402,879,579,749,785],[342,888,207,335,334,742,72,398,248,882,555,922,326,165,591,32],[740,690,957,789,627,558,26,1]]
def bRowC_120 : List Nat := List.flatten [[209,904,631,394,363,997,30,415,817,857,330,864,835,828,279,471],[794,591,744,974,348,952,674,37,923,929,505,52,42,770,604,178],[694,49,190,837,315,948,781,422,478,48,50,928,415,7,565,126],[841,822,579,803,788,191,553,0,279,231,559,251,57,991,637,611],[475,944,801,307,710,872,929,701,387,563,558,312,464,35,775,1008],[188,420,348,779,406,838,798,737,35,967,63,553,243,315,181,673],[633,654,1006,76,867,61,239,18,355,853,546,389,745,400,166,383],[462,914,706,312,455,132,774,545,1]]
def bRowC_121 : List Nat := List.flatten [[140,775,441,241,593,851,329,197,495,52,926,631,907,905,559,204],[840,438,650,275,64,559,225,241,885,955,594,617,603,993,882,101],[314,541,573,53,885,931,475,902,971,793,986,345,681,230,958,964],[903,116,403,301,800,433,476,178,441,210,386,158,714,306,216,976],[313,20,111,709,297,918,978,550,3,397,101,308,616,584,950,830],[336,755,815,29,923,201,747,943,771,295,612,66,800,179,550,789],[780,294,355,921,864,679,836,358,821,837,682,353,550,787,17,633],[164,744,141,60,123,804,799,751,526,1]]
def bRowC_122 : List Nat := List.flatten [[274,632,408,46,555,868,201,178,60,223,884,101,770,966,903,404],[379,265,691,58,941,735,869,482,674,852,943,464,975,789,493,206],[148,434,961,822,887,1004,383,523,1002,198,508,885,896,2,447,955],[963,914,774,589,19,147,198,919,914,265,732,350,42,766,755,127],[263,978,332,567,656,370,211,565,542,426,101,556,49,778,719,974],[165,566,76,130,323,521,517,84,363,902,498,547,248,81,255,256],[631,57,636,246,27,988,153,804,914,441,42,334,993,919,60,802],[18,991,38,625,464,340,976,1008,780,58,1]]
def bRowC_123 : List Nat := List.flatten [[482,269,651,88,797,4,165,496,81,989,537,673,184,579,16,834],[850,50,261,782,721,593,304,332,912,105,503,832,259,145,408,322],[703,109,482,118,741,541,400,488,194,643,781,890,318,567,494,188],[110,592,287,541,129,511,244,909,733,983,66,450,148,206,653,893],[342,379,400,749,362,321,115,718,671,429,379,421,885,499,327,586],[314,908,473,126,322,225,210,225,398,882,731,631,864,48,858,713],[541,272,619,271,513,904,578,984,291,435,702,601,989,933,931,188],[761,669,591,672,31,940,785,151,251,358,643,1]]
def bRowC_124 : List Nat := List.flatten [[241,938,490,619,904,742,338,552,748,500,894,430,589,935,465,187],[804,526,991,722,883,437,936,66,896,912,954,937,39,56,943,422],[111,86,509,572,478,647,151,176,274,709,392,759,33,631,825,827],[91,3,812,564,496,0,598,681,756,856,378,270,390,764,653,300],[262,976,268,205,9,457,456,756,689,999,697,46,901,436,769,241],[459,752,649,856,687,15,902,335,595,808,569,332,206,654,112,127],[48,7,322,326,504,181,730,276,324,69,595,959,903,860,634,83],[636,54,41,851,573,555,92,934,653,285,823,199,1]]
def bRowC_125 : List Nat := List.flatten [[857,674,766,879,614,642,239,355,930,424,600,32,465,771,104,78],[557,732,528,314,855,659,130,443,40,278,694,806,762,352,827,174],[858,746,769,152,508,47,303,416,995,670,805,421,196,476,488,112],[772,828,902,337,887,358,336,287,750,692,479,38,226,767,428,245],[327,386,925,256,614,401,451,533,128,292,890,291,623,152,59,427],[778,623,364,773,811,113,989,60,7,356,753,543,632,566,708,462],[740,431,21,266,942,194,716,529,808,627,117,577,411,341,749,645],[473,461,45,496,981,763,177,398,207,648,863,248,236,1]]
def bRowC_126 : List Nat := List.flatten [[221,108,1003,633,703,79,29,65,820,237,732,105,527,455,575,799],[879,188,765,980,957,605,983,494,371,793,742,754,264,246,143,579],[127,657,230,971,943,423,790,497,493,950,967,617,872,579,622,54],[438,56,63,383,153,454,273,774,698,309,938,415,286,612,592,970],[5,384,873,688,9,672,899,45,567,411,237,602,667,892,459,879],[271,760,126,493,483,994,211,881,17,760,642,945,61,32,758,201],[803,540,36,848,586,441,378,925,264,147,947,737,107,436,699,737],[753,564,938,534,838,105,364,321,200,49,59,837,550,542,1]]
def bRowC_127 : List Nat := List.flatten [[451,333,23,225,659,429,172,739,86,532,687,605,924,502,849,272],[30,961,721,628,320,346,806,425,744,321,192,71,902,642,91,305],[395,48,373,757,642,774,680,885,76,978,756,792,717,361,873,793],[4,529,823,235,362,334,667,863,764,182,442,911,434,175,417,605],[746,134,957,186,1008,68,688,378,885,638,441,899,714,44,647,541],[282,268,311,320,936,715,970,418,93,31,334,197,611,370,58,762],[44,263,180,416,527,302,981,244,182,325,904,670,850,561,167,70],[214,365,154,875,92,963,308,930,366,45,294,55,742,105,812,1]]
def bRowC_128 : List Nat := List.flatten [[616,446,935,345,646,690,417,238,548,897,622,773,671,665,699,870],[27,675,796,364,773,825,24,901,79,664,939,224,225,540,400,867],[424,412,771,77,104,473,588,908,944,925,207,228,753,253,823,980],[79,872,802,987,136,960,612,206,788,544,165,137,901,118,375,912],[996,532,959,618,606,1005,135,73,225,218,437,292,817,45,675,186],[591,157,393,877,994,825,704,310,904,315,67,558,159,143,178,527],[563,74,175,652,894,362,479,129,341,589,710,118,48,815,136,847],[559,680,527,157,792,467,32,584,674,847,3,906,379,339,123,934],[1]]
def bRowC_129 : List Nat := List.flatten [[111,502,832,499,949,41,315,227,665,636,307,305,262,343,836,159],[98,963,467,380,67,856,208,507,266,636,127,170,684,395,569,669],[31,698,68,21,831,1001,971,668,567,279,811,837,143,901,893,839],[96,113,946,97,28,725,155,460,229,652,145,561,938,610,955,455],[835,763,144,353,385,851,683,989,605,614,200,692,654,1000,649,219],[768,155,736,364,885,998,485,568,182,806,582,109,35,652,840,14],[803,836,16,979,879,493,206,908,52,859,649,756,212,820,29,148],[936,875,895,13,119,590,359,479,894,139,493,452,249,34,616,987],[44,1]]
def bRowC_130 : List Nat := List.flatten [[32,650,278,167,987,301,51,872,11,530,340,952,726,802,690,775],[819,6,357,226,232,423,372,627,861,876,972,216,101,305,803,807],[278,98,585,180,274,770,433,495,375,372,986,562,818,324,988,436],[50,380,601,829,606,856,136,92,468,732,496,784,928,623,824,397],[469,325,521,107,867,685,279,107,466,102,27,570,349,257,981,477],[235,365,482,978,784,154,781,390,359,379,546,97,788,560,679,205],[679,208,431,793,707,512,961,555,517,352,360,1007,838,865,760,56],[1,974,424,570,863,632,563,445,599,997,227,427,599,614,849,469],[874,484,1]]
def bRowC_131 : List Nat := List.flatten [[324,848,923,517,709,867,473,712,94,998,191,526,1004,130,378,290],[45,933,845,347,489,715,363,595,800,486,716,134,934,716,715,308],[138,865,441,53,753,744,403,344,718,114,71,10,830,276,226,6],[768,351,809,870,660,630,21,404,793,295,984,440,394,586,324,324],[744,855,228,355,69,343,825,970,559,541,486,122,347,319,755,208],[808,884,815,857,559,285,236,449,993,932,964,842,155,668,126,85],[700,251,532,290,585,499,286,144,644,544,355,769,45,924,632,218],[61,475,477,878,969,198,367,50,245,309,167,706,305,164,326,652],[70,415,865,1]]
def bRowC_132 : List Nat := List.flatten [[445,968,873,610,621,854,469,199,704,504,101,934,794,864,343,931],[888,988,419,667,427,252,250,748,237,824,122,245,239,710,74,638],[143,154,100,725,456,766,390,104,643,318,669,920,258,110,716,731],[576,320,397,823,493,399,374,462,524,443,594,664,799,975,240,765],[379,411,837,297,957,52,707,77,634,782,660,805,490,731,898,437],[332,322,128,689,899,864,203,808,689,151,167,614,500,226,911,718],[709,294,647,402,18,779,641,437,750,634,38,788,590,782,646,737],[335,743,429,781,685,7,21,906,103,490,473,383,950,355,535,559],[616,207,468,885,1]]
def bRowC_133 : List Nat := List.flatten [[849,138,342,396,87,578,210,342,77,133,690,787,418,583,28,948],[809,946,228,346,696,788,294,655,237,3,397,327,900,115,413,116],[676,440,909,113,871,785,127,836,784,351,338,440,900,511,618,746],[677,462,105,54,856,332,359,544,137,248,983,703,676,536,488,492],[457,415,502,746,466,872,270,681,959,568,690,457,996,623,785,274],[822,329,363,214,714,220,698,991,236,908,307,574,33,635,931,844],[521,848,784,861,650,802,340,386,149,473,878,721,358,318,341,256],[454,984,478,793,317,38,841,401,449,923,360,446,494,966,457,800],[135,883,429,167,798,1]]
def bRowC_134 : List Nat := List.flatten [[252,396,784,701,445,438,848,133,402,60,821,4,654,510,440,151],[234,623,862,193,2,294,393,787,131,37,667,331,831,248,445,964],[844,950,233,682,494,637,65,907,933,758,387,102,660,372,774,317],[386,197,884,226,954,609,855,984,629,690,818,2,441,850,353,134],[939,889,412,50,492,693,640,866,53,959,760,611,300,288,965,582],[438,549,894,947,620,983,557,305,647,202,428,605,630,376,654,292],[490,248,779,67,214,306,448,1008,951,300,661,963,119,630,494,647],[821,623,213,981,317,304,887,171,348,436,93,96,448,463,993,705],[637,24,698,90,908,22,1]]
def bRowC_135 : List Nat := List.flatten [[755,382,881,385,259,47,188,338,273,905,550,582,987,893,926,924],[233,791,761,945,341,726,640,135,814,408,181,724,162,54,678,959],[552,664,95,414,204,163,950,988,410,872,544,42,384,44,835,713],[870,187,54,292,96,196,998,450,649,327,164,180,824,846,160,980],[839,727,572,117,190,149,648,277,842,551,772,554,842,4,868,54],[750,868,123,173,916,329,745,774,937,99,826,402,503,131,837,394],[281,578,523,865,989,839,112,406,437,953,112,326,633,736,709,610],[970,1003,159,129,82,934,661,382,832,389,798,572,772,20,229,550],[1000,578,272,273,754,253,397,1]]
def bRowC_136 : List Nat := List.flatten [[529,679,50,466,857,607,410,912,331,412,325,14,597,714,88,274],[333,840,817,548,715,262,1008,513,255,974,566,354,955,289,683,648],[789,816,919,979,544,542,425,858,192,207,248,208,795,728,541,751],[319,717,470,738,155,769,76,896,87,156,369,861,970,984,860,298],[213,794,649,661,443,624,586,579,42,736,25,340,589,27,528,106],[8,182,816,122,741,785,415,131,102,927,700,293,753,742,32,228],[794,443,402,877,453,200,405,201,152,516,952,350,620,31,39,71],[551,43,790,123,413,823,319,33,939,799,387,395,236,817,596,858],[838,574,266,746,142,328,855,761,1]]
def bRowC_137 : List Nat := List.flatten [[927,818,649,972,522,137,826,930,32,6,40,848,67,117,247,57],[780,720,126,151,413,844,139,547,534,735,212,159,176,714,462,213],[357,363,590,975,735,918,927,228,192,750,180,679,654,920,968,696],[851,106,72,801,805,539,180,477,905,892,0,411,577,897,247,752],[443,39,833,784,318,120,820,548,693,5,442,593,872,365,350,885],[901,596,478,999,452,757,224,622,604,486,283,582,137,909,598,420],[901,696,904,643,456,850,732,507,158,317,457,250,627,387,261,699],[209,355,200,765,583,35,648,329,483,207,634,848,823,565,660,991],[705,141,408,805,19,1000,972,537,664,1]]
def bRowC_138 : List Nat := List.flatten [[451,440,107,491,447,864,353,218,849,940,397,635,631,22,902,46],[398,966,662,558,903,123,253,805,852,10,419,977,1005,807,224,666],[868,608,688,344,165,774,915,908,200,128,31,549,976,626,189,117],[295,686,203,597,768,128,311,4,207,285,349,716,191,695,628,264],[487,61,762,227,284,211,72,151,16,98,426,957,427,79,939,85],[728,281,194,438,112,708,271,742,561,644,695,809,824,949,618,727],[706,413,339,87,544,984,480,307,461,649,715,621,356,855,25,692],[821,582,159,764,541,475,76,63,595,665,760,816,612,843,364,441],[290,57,393,219,390,497,852,945,657,632,1]]
def bRowC_139 : List Nat := List.flatten [[914,25,400,941,494,1004,777,496,48,339,107,191,124,759,828,344],[173,317,654,254,469,198,483,974,24,590,381,904,627,744,890,509],[441,325,237,276,259,477,968,343,266,352,878,308,386,129,322,310],[391,263,899,210,310,718,26,741,567,716,996,60,383,402,778,746],[623,400,209,569,657,767,105,609,24,898,150,599,32,360,168,756],[912,789,957,508,923,88,666,422,346,551,52,959,767,33,177,30],[266,820,961,547,882,391,423,799,356,758,119,135,561,232,747,76],[452,654,503,965,419,49,412,918,281,594,215,969,242,571,943,0],[116,992,282,436,565,527,910,401,5,913,874,1]]
def bRowC_140 : List Nat := List.flatten [[246,1002,882,170,658,334,203,229,238,1002,90,183,410,8,282,371],[138,14,961,442,846,828,223,497,23,255,648,862,656,15,196,673],[433,248,679,105,370,331,507,421,339,282,642,132,643,982,549,887],[399,128,976,370,257,271,785,300,883,792,178,617,811,727,579,3],[104,808,379,174,670,126,699,999,410,223,195,134,915,354,468,748],[487,669,201,747,901,541,120,208,989,778,909,7,678,126,827,947],[155,638,836,672,801,694,164,1003,434,120,331,648,620,344,657,281],[155,270,868,987,697,342,232,829,981,580,764,368,639,836,639,527],[679,458,392,89,51,20,711,1000,197,117,399,430,1]]
def bRowC_141 : List Nat := List.flatten [[376,227,201,303,798,195,18,641,917,479,471,974,333,554,811,571],[65,230,539,762,710,153,759,664,476,548,491,202,77,392,466,179],[897,738,272,252,854,331,998,737,945,478,333,867,173,453,808,191],[202,459,668,707,263,547,662,74,512,213,969,520,445,28,968,257],[486,250,562,918,149,250,477,975,204,479,746,593,19,582,602,264],[724,97,381,77,453,247,238,564,188,49,864,927,501,82,296,730],[830,574,934,272,241,535,176,714,674,395,633,563,623,510,691,6],[610,44,109,698,576,22,139,287,463,692,327,659,267,781,246,594],[467,460,220,500,29,602,639,432,401,872,818,507,428,1]]
def bRowC_142 : List Nat := List.flatten [[945,518,425,4,371,888,102,584,494,56,525,721,358,583,579,550],[356,470,606,751,910,42,521,59,383,231,652,250,508,620,722,218],[754,277,649,272,784,294,597,314,972,720,253,437,714,689,331,847],[357,925,923,117,1008,955,378,680,543,972,947,381,117,53,369,395],[689,42,86,365,362,43,494,218,953,383,818,571,410,918,321,416],[327,861,639,923,139,606,970,423,17,338,996,202,636,887,617,980],[686,981,284,594,252,280,711,32,32,721,392,382,862,77,351,371],[318,505,795,303,220,955,78,700,882,495,679,998,808,353,487,106],[6,984,34,938,442,857,946,925,772,457,243,842,875,353,1]]
def bRowC_143 : List Nat := List.flatten [[285,657,880,316,455,799,452,429,665,745,555,780,951,550,519,415],[978,221,827,289,794,798,472,175,634,161,191,470,159,230,744,793],[760,106,694,304,285,158,682,320,625,607,787,475,584,952,681,537],[120,704,51,224,723,119,386,995,555,214,676,868,87,760,903,127],[116,739,817,781,380,58,323,875,702,472,142,611,93,299,278,271],[113,413,756,952,115,362,257,805,877,341,485,730,288,834,148,119],[746,260,502,1000,102,377,433,395,679,277,359,967,618,929,876,93],[1004,797,560,987,173,493,90,368,735,803,193,639,366,498,676,71],[83,304,300,518,747,759,31,707,175,226,838,968,540,677,1008,1]]
def bRowC_144 : List Nat := List.flatten [[357,459,883,105,37,362,311,588,34,839,860,478,951,844,200,756],[888,505,685,503,306,516,45,300,378,290,1008,874,320,901,401,389],[430,855,940,37,352,624,922,632,789,912,215,890,418,196,106,926],[498,922,77,112,103,187,147,462,944,644,54,739,466,359,313,367],[169,817,234,799,906,659,111,61,804,549,814,342,136,518,279,89],[431,791,890,228,882,753,402,579,545,166,717,27,991,32,838,951],[452,878,488,834,96,5,402,981,10,979,565,294,579,766,925,88],[276,465,15,981,285,135,532,248,389,563,222,17,980,634,320,278],[360,147,276,536,774,416,723,578,462,518,412,706,924,728,977,923],[1]]
def bRowC_145 : List Nat := List.flatten [[455,268,846,927,953,566,104,247,335,707,292,386,683,213,543,331],[599,742,909,43,680,249,858,134,348,42,627,30,820,563,825,690],[628,244,396,467,598,568,606,671,941,93,379,437,842,26,985,166],[268,472,702,428,454,645,104,411,354,257,189,876,166,394,403,430],[246,430,439,366,698,875,188,591,24,753,45,276,984,640,391,330],[432,738,177,425,989,784,998,236,172,736,71,668,1001,523,503,520],[692,126,660,257,211,495,186,907,889,637,795,695,196,678,834,163],[366,952,402,213,288,179,620,314,925,673,703,785,939,310,392,583],[963,582,681,172,660,558,524,357,865,167,248,26,844,49,251,525],[700,1]]
def bRowC_146 : List Nat := List.flatten [[776,277,873,341,591,536,719,744,576,610,417,411,179,414,941,72],[236,235,173,99,895,680,377,928,620,830,817,550,517,382,778,871],[615,326,418,563,861,310,46,166,959,347,582,718,901,852,763,795],[849,275,638,47,904,647,782,481,912,782,806,187,642,277,69,122],[140,359,740,260,342,360,329,923,292,328,375,1006,863,146,197,958],[45,721,989,180,672,559,650,403,918,929,533,299,426,384,795,691],[597,849,500,492,725,514,645,138,594,742,923,675,785,874,687,386],[127,76,858,383,441,948,707,941,750,91,918,917,224,431,559,732],[122,734,575,669,626,508,81,36,779,938,671,570,151,885,276,955],[106,809,1]]
def bRowC_147 : List Nat := List.flatten [[897,650,783,552,415,354,799,709,95,880,24,577,790,336,478,181],[710,539,588,128,592,155,51,728,428,98,591,885,556,666,375,525],[598,98,679,341,52,447,550,347,864,31,4,147,466,848,672,735],[158,534,330,531,71,266,864,834,840,968,425,51,179,178,233,570],[900,887,196,921,991,370,73,147,576,657,14,540,537,487,975,628],[913,137,234,327,621,196,1000,72,867,121,46,279,166,907,984,263],[109,393,254,983,927,803,689,853,978,961,9,387,287,841,144,742],[314,487,75,76,141,531,157,979,872,175,293,836,935,158,994,140],[837,449,483,755,473,500,467,492,211,296,741,734,836,175,77,245],[132,751,644,1]]
def bRowC_148 : List Nat := List.flatten [[290,441,766,135,222,61,786,629,290,511,903,650,882,986,518,627],[389,261,286,463,421,975,3,604,618,831,234,873,85,607,54,813],[497,900,973,901,63,660,320,878,555,293,605,613,82,759,244,240],[593,856,255,354,295,650,913,631,945,670,303,311,548,980,20,314],[496,960,868,292,571,205,796,641,826,497,375,996,831,817,835,406],[597,199,573,336,625,840,127,835,806,175,891,315,997,646,469,431],[795,168,141,713,609,180,937,777,25,415,110,278,527,780,333,1002],[427,608,547,1008,512,792,43,643,188,587,315,318,934,473,686,392],[93,91,760,703,137,301,368,623,229,663,319,585,105,594,293,804],[809,239,108,413,1]]
def bRowC_149 : List Nat := List.flatten [[457,931,6,312,659,438,603,379,795,817,243,520,864,135,706,134],[896,607,640,713,147,787,554,992,127,585,896,951,175,804,389,496],[521,983,173,344,65,639,347,769,67,602,852,660,781,979,876,152],[442,186,291,689,26,149,777,692,601,485,949,751,188,66,248,761],[248,398,888,641,132,205,158,930,474,223,402,605,171,136,228,235],[849,498,479,584,516,474,511,450,673,42,280,168,442,75,36,485],[644,976,228,83,217,688,1004,621,402,377,728,1008,668,276,933,391],[325,836,816,66,500,380,531,467,933,314,765,745,425,365,290,712],[720,886,239,775,792,48,43,24,254,645,135,91,378,503,142,239],[807,843,909,725,596,1]]
def bRowC_150 : List Nat := List.flatten [[659,140,54,596,615,685,159,275,690,275,271,35,181,623,117,553],[439,880,839,697,352,749,807,582,228,823,727,400,423,203,49,16],[957,988,712,726,512,596,916,471,634,531,142,326,369,716,287,679],[327,330,48,932,14,817,908,508,504,531,900,947,699,653,111,730],[252,292,589,472,911,346,475,22,514,655,16,749,289,465,161,475],[37,748,652,124,311,974,26,406,409,938,551,512,195,402,181,613],[295,625,486,82,851,99,297,579,762,581,247,223,482,644,763,667],[151,846,559,2,307,102,903,317,118,885,660,849,385,640,625,829],[350,719,548,888,453,193,96,989,783,26,998,394,507,220,291,677],[873,539,438,997,915,150,1]]
def bRowC_151 : List Nat := List.flatten [[713,294,545,988,502,965,967,804,883,693,506,231,745,385,691,723],[116,670,795,647,380,98,806,391,276,287,285,379,627,194,948,1006],[74,82,807,656,123,718,336,876,773,706,140,378,480,903,482,424],[913,320,645,841,846,268,999,374,543,531,202,228,872,72,209,698],[184,321,797,504,341,979,476,72,749,732,334,701,718,213,1001,243],[570,599,198,237,474,190,582,54,222,280,117,919,498,838,95,943],[246,210,518,632,506,215,267,657,620,959,897,802,734,441,583,165],[189,171,265,360,717,419,13,561,787,956,246,192,80,827,524,603],[103,240,180,567,315,279,150,952,441,753,109,61,744,467,652,453],[412,373,258,278,130,541,1008,1]]
def bRowC_152 : List Nat := List.flatten [[609,879,689,699,995,89,570,335,59,530,1004,537,250,989,449,711],[555,893,337,306,249,893,138,794,851,936,774,433,420,554,64,61],[920,882,186,391,911,256,82,494,111,213,682,335,571,395,359,501],[718,481,266,462,51,566,581,674,651,586,222,877,600,672,382,407],[129,901,36,322,142,800,887,780,625,603,869,793,761,581,584,207],[673,78,542,819,554,330,539,993,213,37,452,120,276,718,358,100],[481,423,405,385,371,935,60,182,488,606,450,741,134,248,618,308],[751,624,993,632,926,695,402,782,432,270,308,653,151,538,1006,230],[192,744,312,500,691,964,755,18,315,97,332,157,324,614,390,480],[797,274,708,443,387,899,688,526,1]]
def bRowC_153 : List Nat := List.flatten [[228,541,266,111,387,751,222,191,267,948,377,233,492,222,534,608],[151,352,396,314,824,541,785,582,135,171,244,740,700,874,61,204],[85,277,650,493,540,629,928,221,63,512,864,361,318,122,262,110],[609,1000,682,291,146,774,54,96,449,686,499,48,87,793,369,230],[636,560,182,238,307,884,773,313,593,476,568,962,727,968,5,443],[207,379,700,471,565,797,876,294,571,354,715,484,674,934,973,655],[252,57,727,314,215,796,681,209,279,643,754,209,442,109,945,285],[474,671,177,965,887,102,43,133,351,753,352,494,386,150,108,89],[17,996,11,264,56,394,117,877,685,373,789,442,472,480,182,610],[48,731,529,17,525,695,131,215,958,1]]
def bRowC_154 : List Nat := List.flatten [[655,154,573,495,771,628,410,535,949,675,977,285,493,865,260,989],[652,425,573,617,926,970,249,119,155,98,332,259,113,970,735,520],[251,258,848,673,576,807,26,226,356,688,193,853,122,431,732,55],[162,392,198,550,760,726,332,599,483,987,650,695,833,657,107,854],[997,500,256,717,984,289,677,261,647,46,290,734,666,344,868,294],[139,404,626,476,678,164,963,724,500,919,7,493,21,949,641,614],[21,81,585,323,755,433,30,105,441,216,804,494,759,17,340,758],[67,638,358,791,606,253,21,640,353,23,227,62,490,414,398,545],[30,387,860,394,415,597,406,762,241,710,783,991,172,325,479,160],[481,273,573,796,596,848,764,508,655,968,1]]
def bRowC_155 : List Nat := List.flatten [[226,94,135,913,562,668,221,447,262,198,656,301,977,980,639,422],[871,54,713,888,787,74,59,287,187,466,2,516,135,773,306,96],[72,998,984,880,982,529,845,206,354,228,277,161,123,241,658,483],[335,741,936,825,316,296,40,509,560,3,853,211,529,830,623,960],[710,3,174,893,867,593,994,791,314,795,709,601,469,317,740,256],[628,112,55,800,871,408,19,514,189,258,180,90,187,611,857,901],[219,428,595,551,748,240,251,155,300,856,824,900,206,913,271,450],[94,791,889,494,465,86,218,171,336,911,96,654,851,668,504,99],[266,882,398,675,616,49,322,724,730,486,480,942,912,688,981,940],[222,507,974,613,554,81,902,961,558,800,348,1]]
def bRowC_156 : List Nat := List.flatten [[746,723,427,794,313,479,643,152,467,896,252,372,680,401,245,492],[866,382,761,826,456,524,486,380,649,138,26,768,638,127,197,622],[448,100,374,732,356,612,918,35,382,0,995,817,665,504,434,996],[510,721,151,759,251,320,671,225,436,156,267,316,30,322,194,831],[802,375,514,633,609,114,409,150,425,544,223,509,168,955,312,263],[15,15,550,779,424,691,908,72,26,975,450,361,875,594,109,602],[195,124,448,324,225,397,10,33,957,813,537,192,433,883,559,759],[210,477,738,275,209,805,341,427,509,883,533,194,47,299,743,486],[589,49,314,968,312,594,760,486,765,191,927,393,20,479,1002,462],[462,813,625,326,957,982,33,428,490,512,9,396,1]]
def bRowC_157 : List Nat := List.flatten [[439,594,287,109,866,139,998,520,79,1005,1,957,574,510,289,706],[90,819,140,108,344,536,415,743,728,444,410,42,149,195,257,352],[631,538,166,409,736,924,353,672,971,1008,39,495,595,1006,949,848],[363,534,497,580,254,365,895,987,657,636,85,317,237,574,894,786],[263,949,352,327,612,698,812,659,587,611,622,210,728,28,538,329],[155,880,389,329,378,658,194,722,52,665,563,787,83,284,95,241],[122,359,498,544,774,485,853,846,660,729,917,454,808,181,294,516],[95,215,588,148,121,914,579,668,67,163,972,544,308,193,356,496],[954,699,259,945,777,550,363,627,139,621,923,779,395,786,745,301],[321,984,187,156,783,776,603,940,670,71,708,361,170,1]]
def bRowC_158 : List Nat := List.flatten [[910,683,389,702,21,600,360,975,321,442,645,366,538,467,719,247],[292,821,264,40,716,584,510,507,649,193,748,199,981,852,827,1006],[835,40,132,3,76,135,879,838,519,313,941,1002,237,621,357,488],[767,325,26,816,173,703,968,573,993,981,593,85,948,47,500,111],[912,517,837,182,158,869,822,919,623,447,189,731,962,55,6,472],[950,569,176,737,968,132,567,605,559,510,872,671,127,485,124,743],[763,666,102,820,319,217,106,732,393,65,894,834,828,344,858,879],[965,324,1006,918,516,897,662,436,520,876,50,650,73,842,867,151],[645,538,805,58,781,641,388,591,567,934,612,955,78,57,370,518],[117,22,225,554,926,874,183,879,345,235,101,252,258,828,1]]
def bRowC_159 : List Nat := List.flatten [[413,528,629,4,804,100,195,296,327,728,735,739,12,681,781,965],[61,274,19,515,745,918,235,465,955,892,134,169,882,799,695,70],[472,827,440,81,507,846,905,755,949,995,413,162,106,584,413,737],[551,902,152,255,51,801,579,606,469,789,966,138,976,64,641,269],[341,626,864,65,15,816,584,405,96,641,424,147,812,349,896,812],[640,435,683,33,556,302,995,999,1006,341,614,534,980,53,101,833],[607,577,67,962,110,596,579,590,914,989,930,353,210,739,777,434],[476,728,401,633,522,541,354,297,710,362,133,110,69,699,451,404],[229,861,194,722,655,845,523,772,396,204,637,876,120,958,827,365],[106,522,369,298,752,845,399,522,121,476,304,20,69,878,714,1]]
def bRowC_160 : List Nat := List.flatten [[945,370,292,166,720,809,4,525,570,799,839,171,123,759,176,744],[786,670,314,327,327,927,645,571,461,306,11,497,234,376,884,658],[540,728,523,620,358,497,214,176,439,119,408,439,464,544,671,319],[3,6,872,778,306,865,78,608,673,45,30,876,245,129,760,20],[346,118,487,316,668,939,597,261,717,905,821,126,848,938,923,262],[95,944,406,791,491,275,720,500,731,379,315,922,322,302,803,799],[168,249,250,665,162,722,778,608,393,233,984,10,247,245,960,728],[880,400,804,480,531,439,803,679,758,984,706,1007,771,280,714,874],[263,985,115,115,201,826,727,340,449,65,389,35,842,778,301,712],[999,429,847,401,705,312,474,1008,220,905,45,747,1,188,319,882],[1]]
def bRowC_161 : List Nat := List.flatten [[133,542,363,816,156,275,449,820,707,737,976,641,210,696,185,640],[546,635,295,468,107,357,474,694,644,717,822,382,264,694,709,166],[903,267,978,964,992,953,387,314,730,54,664,873,176,844,130,558],[558,543,876,900,94,476,514,846,766,683,857,731,566,583,888,829],[237,598,606,788,897,815,228,931,434,414,788,784,661,835,906,23],[8,431,150,560,737,896,902,850,97,421,649,40,417,739,823,887],[444,666,776,955,603,39,811,98,1007,488,347,865,547,182,609,940],[828,998,598,663,257,485,145,159,575,927,477,22,947,135,478,723],[964,461,164,664,550,206,514,465,511,934,27,987,873,420,842,239],[497,20,958,162,144,877,554,522,205,624,914,566,203,905,516,863],[652,1]]
def bRowC_162 : List Nat := List.flatten [[875,381,171,167,413,910,482,271,341,757,684,430,765,980,764,964],[545,513,179,570,836,773,935,987,1004,49,564,876,42,849,986,300],[425,552,595,817,52,843,57,964,216,232,807,395,10,545,795,536],[289,176,270,53,295,793,620,658,95,229,515,691,126,349,59,609],[892,167,409,628,362,167,861,565,263,515,560,10,101,153,798,333],[564,575,717,615,910,192,871,590,275,560,460,193,399,356,775,362],[517,154,182,969,311,469,656,530,651,638,929,452,814,1008,828,434],[514,383,535,517,662,960,732,239,360,520,55,498,81,407,766,637],[818,296,547,901,879,367,871,411,223,238,672,118,771,878,9,910],[862,405,519,286,802,761,278,465,873,176,975,698,35,996,324,904],[289,171,1]]
def bRowC_163 : List Nat := List.flatten [[722,546,931,899,713,786,676,414,77,886,842,592,853,358,935,168],[820,595,580,799,715,520,610,198,735,709,741,7,329,561,305,163],[656,242,251,36,186,965,831,481,412,571,473,30,472,704,31,532],[971,77,863,15,364,243,780,157,897,186,324,467,209,609,679,864],[678,86,110,671,934,796,51,483,198,277,577,796,735,854,292,230],[842,292,904,206,601,422,260,375,181,402,178,739,273,590,182,159],[477,197,918,273,454,811,453,282,729,288,393,45,859,664,988,574],[903,9,600,460,151,186,516,936,361,751,372,806,967,430,92,700],[259,236,205,649,838,736,380,82,307,62,656,427,803,649,832,897],[350,336,648,22,110,853,47,796,804,259,398,98,121,403,463,953],[723,255,352,1]]
def bRowC_164 : List Nat := List.flatten [[171,26,895,258,214,660,646,114,257,863,925,136,514,444,964,997],[599,672,714,917,672,113,885,796,559,271,392,340,569,770,730,52],[713,205,6,453,121,862,134,471,834,800,715,959,874,160,44,516],[712,493,477,903,930,614,635,203,65,487,742,529,75,530,818,172],[994,321,636,195,479,445,362,393,214,740,832,852,262,631,998,491],[673,156,116,988,699,149,861,203,623,598,266,406,398,222,28,532],[64,677,91,676,494,882,847,98,392,609,381,771,367,278,120,558],[309,646,723,457,549,946,971,904,862,988,716,69,480,892,303,282],[545,4,281,573,406,80,30,955,295,579,554,582,520,4,113,855],[558,321,175,871,157,180,671,640,679,187,326,964,213,78,940,510],[136,161,559,889,1]]
def bRowC_165 : List Nat := List.flatten [[588,951,649,357,721,281,997,914,705,299,745,125,823,684,366,540],[43,96,709,780,248,647,619,439,414,895,174,581,982,97,148,948],[876,19,374,227,446,290,658,10,33,659,816,716,404,235,971,13],[1006,960,979,395,248,526,761,178,824,655,518,319,647,346,493,82],[609,619,200,921,497,799,319,167,139,194,25,352,672,680,825,582],[789,271,354,572,706,409,386,876,163,164,462,698,245,873,720,718],[70,595,591,400,368,220,948,979,623,939,246,67,717,53,760,197],[257,706,160,85,925,93,769,724,765,480,672,770,829,775,524,743],[604,686,726,746,414,867,706,97,515,642,176,259,55,611,960,567],[771,678,638,800,804,18,520,573,111,599,32,750,851,985,337,214],[151,50,292,441,535,1]]
def bRowC_166 : List Nat := List.flatten [[474,293,965,1007,555,217,242,744,268,123,977,765,565,655,866,473],[550,943,7,634,2,755,312,554,946,827,197,652,364,6,814,277],[269,789,636,421,266,739,770,384,921,119,817,176,400,429,9,889],[812,264,908,387,212,816,28,85,793,708,8,450,535,116,942,188],[639,522,998,514,231,647,647,622,497,292,169,327,569,626,848,656],[119,917,358,384,149,797,617,103,223,436,1004,884,72,207,202,824],[515,372,171,874,386,870,622,941,356,802,663,193,817,973,176,296],[536,623,520,929,676,863,699,124,566,483,297,772,432,870,258,814],[665,98,771,649,161,709,180,536,959,92,658,300,514,523,995,810],[909,577,551,521,163,364,717,516,976,918,618,595,408,67,998,579],[717,354,231,864,955,670,1]]
def bRowC_167 : List Nat := List.flatten [[185,613,427,827,425,20,654,238,708,215,537,115,583,41,14,858],[36,591,8,331,386,545,505,752,581,142,269,317,363,845,87,259],[594,869,380,485,635,826,58,557,919,24,930,654,336,175,648,312],[986,34,849,760,878,379,593,447,719,612,392,96,411,441,564,840],[390,119,673,29,547,423,770,283,930,90,272,837,874,979,857,54],[93,133,304,642,984,11,461,715,428,86,871,2,678,889,267,271],[253,379,238,330,618,254,448,588,26,531,657,638,315,261,892,785],[551,959,554,54,873,87,146,395,763,14,659,307,497,96,401,393],[626,625,748,842,388,20,116,412,859,124,583,696,102,633,679,663],[744,461,481,861,827,921,634,499,287,971,301,150,536,513,244,351],[941,224,326,761,168,482,957,1]]
def bRowC_168 : List Nat := List.flatten [[263,679,27,266,448,105,164,101,299,793,319,844,509,401,580,68],[455,199,108,859,286,632,473,761,275,638,683,953,252,0,408,897],[964,518,759,126,28,955,816,396,830,260,529,855,620,231,538,182],[769,801,392,599,512,392,403,481,757,125,705,594,438,624,172,708],[327,507,303,946,611,262,668,313,247,510,203,215,133,839,561,33],[364,391,765,388,90,819,649,194,958,759,867,964,868,101,1008,3],[233,265,515,373,51,615,491,200,325,277,473,27,666,938,282,529],[426,296,104,201,733,831,984,4,562,109,742,40,671,337,712,664],[444,498,882,355,626,307,980,481,95,529,1000,673,371,822,1006,969],[696,936,701,349,774,614,234,243,505,386,380,893,759,400,507,971],[729,984,861,765,838,435,331,313,1]]
def bRowC_169 : List Nat := List.flatten [[798,371,549,186,924,764,650,886,356,770,186,779,782,540,882,403],[77,805,625,589,173,1005,180,248,139,511,338,49,250,230,314,111],[976,783,948,36,814,74,460,722,927,252,197,359,29,341,465,173],[245,894,704,835,479,475,432,126,960,182,984,594,148,788,495,932],[867,760,857,18,884,83,837,542,144,234,158,41,547,810,919,910],[573,265,468,192,103,697,174,280,249,438,437,399,116,1000,317,996],[137,549,786,105,163,78,542,119,326,25,879,874,323,377,7,581],[812,193,64,280,866,197,667,427,125,501,268,725,973,170,625,296],[64,487,90,314,276,746,589,686,1001,736,580,12,642,41,863,341],[556,302,79,343,105,923,299,691,296,841,655,260,15,529,173,498],[717,920,944,987,529,253,380,241,342,1]]
def bRowC_170 : List Nat := List.flatten [[153,161,897,797,85,696,20,843,44,902,658,789,289,503,287,81],[491,566,1002,561,569,473,73,105,105,669,983,351,659,387,409,396],[213,457,997,792,110,246,174,9,807,576,57,442,354,850,491,942],[823,666,501,963,374,419,672,471,149,419,130,25,128,250,352,389],[145,350,976,702,780,591,147,211,826,791,905,1005,646,638,390,655],[591,302,226,23,225,773,528,162,403,905,690,770,515,264,265,431],[560,81,261,979,903,34,794,875,562,866,707,508,732,278,476,690],[743,1005,515,785,168,295,153,120,550,957,341,561,303,415,624,124],[41,888,948,629,704,344,812,479,964,877,396,297,568,907,872,117],[419,799,135,791,725,196,336,824,261,386,954,583,879,227,588,346],[423,521,998,657,794,811,182,553,943,812,1]]
def bRowC_171 : List Nat := List.flatten [[85,161,195,507,888,738,229,739,806,312,370,509,953,922,947,536],[73,423,6,813,956,99,84,191,228,196,817,199,655,289,1002,356],[720,845,390,520,80,908,265,221,754,443,556,686,528,43,889,621],[1006,231,817,10,219,327,96,314,118,532,445,26,124,898,988,54],[17,239,128,865,718,511,556,109,186,871,401,741,868,580,800,696],[669,410,836,388,1003,394,624,541,634,463,57,559,150,70,1004,736],[368,395,480,165,392,514,323,509,528,951,291,1002,215,721,908,436],[707,535,878,199,445,79,710,637,490,817,725,803,233,617,202,767],[304,509,779,982,453,773,680,12,51,218,821,503,100,195,339,676],[20,961,766,175,421,212,276,913,940,320,647,834,613,46,714,1004],[89,449,460,840,817,1,945,55,931,334,392,1]]
def bRowC_172 : List Nat := List.flatten [[544,448,213,897,1006,10,691,913,648,169,699,79,391,423,624,620],[904,329,14,100,882,882,519,746,969,247,62,5,742,245,615,982],[9,959,337,348,937,255,600,47,49,1006,17,642,820,938,924,354],[756,293,56,168,269,271,247,44,530,540,51,687,150,890,1004,766],[340,177,435,159,313,565,930,832,642,373,673,711,495,656,214,931],[902,769,929,61,41,480,481,1005,975,794,457,464,512,212,32,742],[336,8,328,652,323,135,261,391,690,411,49,33,404,692,589,454],[549,153,916,329,299,143,619,25,768,224,330,924,865,790,655,656],[34,438,53,802,537,331,472,735,63,895,865,346,862,290,170,898],[420,234,744,189,95,820,805,500,52,83,970,671,296,972,424,932],[5,154,841,331,445,461,588,963,927,227,880,886,1]]
def bRowC_173 : List Nat := List.flatten [[384,464,140,256,693,9,792,478,981,553,893,316,418,889,491,850],[185,52,760,965,6,766,916,898,875,782,29,544,110,0,145,787],[998,368,167,95,12,742,110,144,613,82,238,642,484,634,357,274],[933,991,402,962,332,627,364,804,695,284,46,576,35,186,515,273],[754,417,428,951,362,75,993,484,839,779,611,915,665,452,879,700],[147,726,972,655,164,828,64,395,881,398,852,645,392,870,500,112],[167,812,968,656,12,910,242,27,255,550,659,389,620,224,456,52],[741,298,846,893,445,659,239,399,184,802,389,797,653,882,750,492],[777,770,716,412,638,614,955,640,892,217,592,376,510,655,973,997],[150,313,121,548,593,620,268,865,79,182,296,710,581,872,888,94],[713,243,959,125,933,240,75,923,0,31,5,215,327,1]]
def bRowC_174 : List Nat := List.flatten [[741,227,788,827,411,141,732,799,154,226,675,914,896,481,276,865],[367,43,632,151,730,531,919,727,990,211,158,797,195,996,454,126],[372,135,94,112,312,70,489,947,127,157,678,986,529,157,210,548],[568,319,673,213,430,790,554,314,18,955,395,726,268,742,477,597],[115,625,153,632,604,524,354,5,420,570,665,889,549,34,21,708],[493,211,132,122,436,298,41,78,560,728,131,288,364,266,382,153],[1004,732,734,160,407,916,535,431,924,854,579,912,139,163,26,869],[365,225,610,536,809,851,579,749,78,124,840,405,851,603,706,159],[976,384,228,330,488,744,113,217,722,845,210,123,758,31,163,226],[792,49,670,257,352,616,628,326,852,347,547,595,224,199,777,963],[22,994,335,576,814,435,827,148,680,716,109,360,385,328,1]]
def bRowC_175 : List Nat := List.flatten [[485,590,272,488,634,382,766,290,182,174,396,429,511,175,877,426],[579,409,620,400,338,474,510,633,595,137,983,163,976,791,546,769],[267,831,581,157,727,46,741,429,545,767,570,965,387,314,713,890],[169,5,881,990,990,659,972,404,251,952,335,673,771,468,960,248],[458,512,343,319,110,378,416,649,885,160,919,97,772,789,247,755],[452,648,336,57,0,898,759,454,148,380,808,1008,760,140,142,743],[248,174,495,684,378,942,750,935,126,381,401,663,610,354,853,153],[291,752,185,12,531,770,895,272,924,758,870,680,474,872,63,394],[182,402,871,36,391,421,649,920,113,454,198,299,510,819,890,263],[334,285,63,523,921,457,220,615,824,916,444,150,746,552,362,573],[315,915,972,861,794,146,366,790,174,826,829,1001,884,154,515,1]]
def bRowC_176 : List Nat := List.flatten [[918,122,400,902,252,24,408,213,612,577,448,860,183,68,57,998],[539,631,621,721,174,552,61,946,398,417,899,90,589,887,363,233],[279,725,77,968,869,571,940,15,867,72,794,183,602,122,983,582],[642,611,533,710,118,522,145,801,774,512,270,423,733,347,834,967],[225,27,628,123,93,905,967,971,282,503,419,97,430,741,918,634],[982,937,899,497,448,558,551,959,982,395,960,594,245,250,910,698],[872,222,377,804,11,475,606,714,647,426,866,742,327,723,688,930],[376,728,438,640,999,991,184,376,989,723,43,956,209,896,521,670],[977,4,27,715,153,1002,934,960,842,295,52,210,341,345,109,273],[726,180,957,785,379,433,679,41,921,228,306,770,592,861,9,416],[967,991,318,787,364,550,440,729,560,849,978,882,938,881,608,617],[1]]
def bRowC_177 : List Nat := List.flatten [[755,103,792,407,120,429,64,346,718,956,465,332,419,541,58,899],[829,239,494,702,249,647,483,212,386,977,969,58,593,121,632,772],[606,5,714,683,781,156,546,180,184,1005,965,483,496,693,720,894],[160,107,366,854,624,485,273,980,421,1003,843,556,264,458,808,630],[248,356,867,143,806,492,798,715,811,525,640,851,472,395,770,985],[459,658,677,670,805,227,321,16,128,497,993,563,952,792,339,942],[744,26,776,640,210,422,658,904,664,295,340,822,295,569,169,695],[834,614,187,957,219,212,367,47,139,191,363,216,1004,848,723,86],[669,347,60,188,94,124,157,924,475,355,373,357,838,988,120,914],[995,708,559,126,235,385,183,783,192,970,965,940,875,845,875,788],[569,546,924,158,799,400,235,67,746,2,967,817,746,14,233,261],[933,1]]
def bRowC_178 : List Nat := List.flatten [[516,208,433,341,469,329,214,578,637,489,294,707,534,418,464,410],[1005,270,383,503,992,168,900,568,689,753,84,20,760,282,181,380],[510,158,428,218,21,912,409,141,662,106,33,318,706,824,948,51],[15,411,911,373,733,839,470,453,797,483,333,320,804,801,345,741],[533,608,529,772,893,901,845,211,290,191,440,770,728,87,444,896],[140,154,44,257,858,341,397,184,866,549,223,326,77,790,724,241],[521,263,657,944,538,424,822,562,1000,831,215,461,578,362,622,860],[519,224,836,910,561,766,227,746,21,270,161,897,903,484,706,81],[51,804,976,135,783,803,251,215,27,187,846,899,168,796,120,970],[866,577,529,525,804,228,986,308,225,720,571,794,158,829,1006,322],[64,942,874,856,74,719,628,723,282,790,655,663,675,5,751,527],[14,431,1]]
def bRowC_179 : List Nat := List.flatten [[754,915,705,190,50,812,730,161,295,952,992,832,61,566,493,599],[392,947,942,573,197,917,885,727,113,752,903,278,516,890,58,852],[699,929,135,897,878,530,751,488,289,909,411,756,743,949,928,302],[550,29,310,683,161,406,943,233,476,358,597,130,144,43,623,879],[728,270,126,106,728,139,948,692,365,755,758,511,10,743,949,311],[124,951,326,817,356,805,298,755,797,245,166,717,186,970,579,490],[650,492,423,189,110,391,656,55,290,906,441,785,328,247,632,829],[61,532,504,900,758,594,467,235,402,350,355,163,155,63,277,567],[177,404,370,174,616,927,292,702,501,15,118,635,230,45,519,939],[836,189,308,453,772,538,16,536,370,205,749,731,631,949,366,550],[639,376,346,599,217,940,895,540,922,103,252,355,109,696,413,132],[102,283,483,1]]
def bRowC_180 : List Nat := List.flatten [[53,635,58,168,861,127,731,184,739,500,153,965,881,79,248,422],[49,592,552,522,598,608,969,814,169,274,476,878,220,474,491,104],[646,846,144,169,2,365,99,394,864,763,770,621,680,104,215,23],[413,562,913,478,804,876,616,29,390,410,564,406,912,749,1001,831],[791,474,383,449,679,56,405,916,524,345,140,440,577,566,135,115],[599,31,279,992,322,340,307,722,470,391,773,770,504,564,65,360],[948,39,956,632,64,307,623,243,827,552,815,653,975,102,547,206],[388,515,876,961,538,967,246,278,666,175,176,14,761,487,132,839],[803,523,25,980,829,73,337,555,837,634,800,65,149,570,285,449],[185,828,804,989,927,379,655,320,513,184,459,458,555,828,408,752],[260,526,912,382,562,137,343,90,553,472,954,669,552,880,703,492],[113,300,820,264,1]]
def bRowC_181 : List Nat := List.flatten [[765,382,299,61,175,342,641,173,93,470,365,314,716,924,478,908],[340,688,648,45,218,172,627,224,51,493,980,103,812,810,942,647],[139,719,786,816,598,579,993,319,711,736,348,500,259,464,467,184],[291,358,181,777,263,492,452,411,421,407,631,718,121,94,16,854],[68,66,754,471,72,317,17,857,634,816,331,685,776,716,81,407],[746,386,531,833,678,975,440,615,588,697,301,828,941,678,634,568],[787,579,86,340,847,109,784,706,338,709,217,695,830,508,797,949],[557,758,4,923,260,779,10,700,250,199,11,327,729,306,458,35],[927,767,33,11,854,103,437,574,254,274,273,468,513,384,817,195],[747,407,819,612,18,65,295,317,22,173,955,696,520,78,326,859],[494,757,881,845,563,423,548,805,160,313,312,190,903,739,123,294],[37,543,385,948,711,1]]
def bRowC_182 : List Nat := List.flatten [[1004,50,423,982,862,954,56,910,284,508,35,356,238,492,282,521],[470,673,442,828,867,137,14,306,749,748,13,361,526,994,560,970],[239,925,381,980,288,525,773,638,380,999,752,629,786,291,219,678],[876,829,397,398,692,382,297,828,830,124,584,122,299,179,593,13],[972,564,273,510,594,556,974,548,228,616,790,784,219,552,858,254],[155,762,462,374,807,593,510,717,536,137,493,505,870,119,900,7],[261,327,808,207,892,698,933,884,680,427,660,983,289,582,107,984],[485,842,215,791,866,167,800,836,676,43,891,496,88,409,545,558],[11,933,720,949,148,81,135,137,925,865,557,245,1,518,337,364],[478,451,977,138,860,294,198,461,521,167,663,43,728,154,419,852],[325,202,972,748,160,144,810,323,836,548,451,559,170,494,438,760],[378,363,8,741,879,518,1]]
def bRowC_183 : List Nat := List.flatten [[667,188,395,605,200,982,789,259,921,388,907,752,710,522,582,896],[638,80,850,963,713,403,310,7,994,66,979,623,416,862,755,342],[67,128,159,153,296,967,653,377,612,518,465,607,381,109,63,5],[77,985,845,196,721,882,801,678,367,580,91,160,662,359,662,591],[66,307,400,167,354,688,463,928,184,663,638,925,719,938,148,155],[154,626,470,136,290,653,758,41,780,202,152,780,196,886,549,324],[46,652,712,359,589,623,60,228,815,873,499,423,530,849,928,462],[510,297,670,413,263,637,394,844,51,289,6,328,891,17,3,234],[54,791,91,217,593,259,431,30,55,717,55,796,363,176,426,443],[154,245,222,488,767,749,607,429,846,805,337,130,95,856,334,848],[625,428,341,11,817,752,683,409,954,761,820,621,718,861,260,222],[220,781,684,39,707,594,336,1]]
def bRowC_184 : List Nat := List.flatten [[769,819,815,320,526,51,650,492,248,769,657,794,635,829,471,817],[612,247,702,253,567,740,17,224,685,755,866,693,660,621,406,986],[872,268,798,368,533,263,954,119,122,117,937,390,477,397,995,279],[797,91,672,756,397,468,657,796,579,372,373,618,868,485,164,342],[673,590,930,445,525,448,140,781,371,133,261,380,636,0,953,854],[518,1,54,549,589,974,490,149,196,258,539,186,971,240,286,667],[387,972,655,449,9,349,618,446,174,510,368,779,216,147,1008,495],[261,340,818,114,511,695,876,536,129,690,642,850,99,545,1005,516],[764,630,887,655,272,730,104,900,634,812,145,430,727,81,994,774],[895,618,571,761,389,705,196,607,166,5,185,361,51,439,846,853],[237,341,222,765,542,202,362,850,234,93,898,938,412,154,981,748],[445,112,114,581,48,633,135,911,1]]
def bRowC_185 : List Nat := List.flatten [[673,886,375,933,737,851,682,637,616,943,453,570,938,582,168,651],[135,412,782,10,346,432,740,246,65,696,840,548,483,560,867,654],[207,745,960,455,973,863,122,90,367,293,234,479,534,26,858,641],[157,336,883,788,94,202,1003,206,831,327,140,26,586,764,87,269],[855,118,965,683,514,655,399,765,275,975,74,289,125,949,185,342],[85,696,553,447,343,424,583,517,551,39,763,953,44,671,856,98],[591,874,600,796,33,911,386,297,740,730,816,513,99,654,96,779],[645,448,418,185,186,379,391,261,145,855,58,663,700,308,619,133],[643,159,992,196,352,258,726,725,937,458,225,568,666,519,239,261],[158,827,614,488,497,945,278,484,953,903,628,867,944,31,805,481],[792,283,541,634,529,560,858,637,175,994,508,778,996,513,400,361],[580,500,416,720,553,882,553,612,708,1]]
def bRowC_186 : List Nat := List.flatten [[604,689,852,675,266,886,79,303,503,119,813,531,280,479,563,997],[581,702,435,606,612,700,665,286,940,248,145,951,988,813,370,314],[941,1000,380,452,755,400,857,423,974,937,683,19,554,878,180,331],[416,370,681,92,339,836,632,538,983,490,856,139,53,224,935,750],[802,811,654,189,930,836,809,998,338,142,725,344,305,706,332,308],[196,258,17,883,544,425,575,696,934,368,562,103,659,148,154,53],[595,955,479,163,485,994,451,204,326,546,241,120,819,212,682,355],[28,195,339,467,736,136,637,744,123,341,836,449,924,371,751,309],[266,55,90,204,611,767,87,26,511,65,435,212,914,56,982,919],[708,624,183,967,350,88,20,288,814,992,833,143,65,590,893,321],[554,629,687,863,651,915,264,929,56,5,594,54,404,463,380,726],[801,957,986,504,338,837,734,285,467,177,1]]
def bRowC_187 : List Nat := List.flatten [[551,514,728,263,704,110,822,496,416,557,103,668,322,599,780,619],[589,133,271,497,821,895,639,420,675,995,61,1005,429,337,490,877],[336,895,535,113,274,271,893,399,719,101,560,1004,62,55,826,204],[304,387,980,136,831,231,301,819,108,61,127,222,817,584,914,793],[782,163,896,264,323,708,869,485,272,35,967,507,718,789,734,553],[790,246,254,756,518,168,228,431,665,660,189,989,875,356,36,173],[138,235,922,695,116,447,227,595,817,464,444,239,297,368,348,686],[172,643,652,804,834,880,972,206,930,890,22,595,312,377,391,406],[943,997,903,79,134,59,484,807,674,547,997,881,857,154,721,968],[278,816,241,863,266,997,135,389,864,485,795,119,765,397,265,127],[700,479,861,694,675,958,821,852,730,515,88,712,891,735,747,581],[811,915,513,780,844,329,979,227,164,415,681,1]]
def bRowC_188 : List Nat := List.flatten [[177,894,571,118,822,254,80,633,119,428,363,848,447,267,817,220],[408,722,613,524,964,23,367,161,635,157,951,514,348,303,48,385],[703,951,379,498,259,236,737,196,616,897,565,412,480,221,208,796],[935,537,752,132,448,987,955,833,745,125,707,536,992,140,415,697],[361,462,223,686,910,540,260,566,261,333,16,17,383,354,864,415],[32,944,668,363,320,363,724,345,506,6,945,602,289,166,519,455],[766,542,179,637,516,205,656,844,764,457,129,901,1006,637,95,558],[407,54,765,460,509,693,795,42,734,40,97,229,773,105,296,101],[655,848,858,775,404,164,273,1005,197,441,22,89,69,537,540,67],[116,897,238,567,463,54,168,214,393,674,538,978,760,471,37,56],[4,838,41,518,466,516,916,609,777,212,30,537,477,4,134,58],[767,892,941,665,498,669,545,951,996,267,607,0,1]]
def bRowC_189 : List Nat := List.flatten [[528,291,157,188,717,338,653,413,229,352,195,119,84,62,826,899],[772,547,843,156,839,880,332,713,502,890,253,69,990,139,259,385],[509,688,203,95,581,888,966,1001,917,5,599,481,86,569,203,843],[682,174,376,344,390,256,336,300,45,573,59,722,383,96,38,128],[1007,764,655,962,685,138,581,677,201,874,215,167,377,243,885,66],[324,10,289,780,842,503,473,453,844,801,7,790,425,550,470,693],[738,164,184,11,895,945,374,8,661,549,655,338,24,965,556,714],[475,642,10,257,177,842,205,239,249,753,868,85,506,316,554,895],[25,95,941,823,698,612,159,456,188,766,622,420,44,642,50,228],[417,45,697,435,1008,542,887,689,745,718,894,175,929,904,977,974],[235,121,252,536,704,866,984,379,471,118,503,340,519,880,246,918],[1000,1005,810,471,418,509,947,89,188,846,887,8,186,1]]
def bRowC_190 : List Nat := List.flatten [[1007,363,227,686,404,317,409,999,560,140,49,476,419,969,531,787],[512,559,782,755,140,854,796,568,8,246,904,798,1005,513,234,492],[711,193,940,202,10,172,707,95,213,639,238,199,234,265,124,51],[388,473,25,473,971,803,356,269,211,647,102,580,529,305,109,360],[735,132,152,213,26,789,299,131,746,562,89,791,262,781,330,668],[664,540,452,586,368,27,525,974,808,425,639,638,862,275,977,258],[582,688,741,761,317,680,980,799,542,250,20,1004,556,260,741,789],[863,990,211,141,847,713,928,718,525,228,332,216,863,245,690,679],[740,359,264,544,204,844,951,186,239,617,348,904,312,315,604,389],[474,387,760,607,108,903,350,88,77,76,174,407,983,109,323,410],[388,490,65,35,273,23,31,587,915,483,123,516,627,905,256,631],[54,647,398,28,51,452,603,146,680,687,685,533,600,394,1]]
def bRowC_191 : List Nat := List.flatten [[382,366,139,188,449,82,487,484,77,273,725,915,876,350,893,581],[853,44,58,884,146,318,788,784,320,587,439,287,953,548,480,949],[330,879,575,110,449,100,246,734,541,62,707,179,817,834,62,171],[583,576,353,314,32,692,418,345,562,421,267,558,778,295,724,639],[885,966,274,417,557,250,45,922,27,720,505,897,406,602,156,216],[559,330,95,512,531,819,973,108,743,426,109,579,314,759,650,857],[857,959,347,546,396,535,575,73,184,396,698,261,120,648,508,868],[603,89,639,421,728,405,224,414,973,753,955,478,1004,138,180,770],[616,234,312,864,366,42,290,508,587,419,46,385,495,690,110,476],[432,359,883,248,485,952,617,312,1005,472,125,937,96,587,395,930],[991,231,509,114,899,643,546,608,427,930,528,413,641,274,380,155],[10,948,961,689,327,627,179,673,763,60,771,945,308,659,621,1]]
def bRowC_192 : List Nat := List.flatten [[966,364,755,483,392,27,91,174,61,647,539,426,151,240,599,362],[915,167,155,473,677,464,518,916,337,576,211,955,539,472,233,974],[670,900,385,910,433,487,434,792,156,14,1002,917,456,157,839,1003],[443,86,656,279,49,58,16,875,18,923,279,899,361,416,669,11],[601,409,807,574,651,961,172,235,554,131,18,550,718,665,321,42],[507,872,576,944,690,964,773,441,100,648,266,979,303,823,78,925],[860,973,130,996,472,426,705,364,125,814,17,313,621,694,518,800],[551,214,535,67,252,690,612,189,368,217,892,785,72,481,911,414],[67,863,565,48,728,617,515,28,446,692,428,150,357,936,837,834],[872,952,978,324,667,981,717,448,258,246,747,660,392,903,330,616],[266,345,261,413,601,969,273,491,454,649,431,86,56,672,518,777],[245,171,44,593,916,777,884,477,358,64,878,8,880,161,806,500],[1]]
def bRowC_193 : List Nat := List.flatten [[404,33,687,769,172,183,477,272,718,175,27,374,962,933,656,189],[210,729,806,971,663,879,253,727,213,956,895,976,497,839,149,1001],[416,148,915,204,974,219,923,108,60,683,89,607,291,236,330,598],[483,534,628,277,452,0,649,255,689,184,962,181,750,594,20,429],[551,671,835,910,565,637,383,930,251,532,409,499,928,507,826,755],[203,886,929,230,737,611,930,131,576,361,847,936,32,810,23,949],[980,933,807,684,179,37,267,701,528,295,766,557,199,252,762,328],[659,391,17,107,37,221,916,894,659,715,611,833,113,27,627,688],[98,697,653,96,37,193,548,408,24,236,172,152,523,256,801,502],[542,166,180,443,133,112,143,249,818,135,154,795,762,335,357,308],[592,523,504,994,485,137,472,520,361,660,666,61,588,650,118,587],[314,111,494,935,79,630,154,827,468,249,694,714,837,25,158,807],[140,1]]
def bRowC_194 : List Nat := List.flatten [[296,207,924,67,246,61,563,713,642,964,437,477,206,228,350,627],[701,883,582,914,733,188,522,539,970,434,149,714,548,459,874,505],[164,774,664,660,241,567,778,430,709,1002,750,526,252,909,982,11],[181,497,511,498,119,87,319,921,422,909,637,438,749,270,385,337],[830,907,515,79,998,838,82,960,550,1003,144,839,171,255,446,979],[598,397,567,145,329,71,377,479,375,30,666,550,626,841,466,465],[663,452,598,495,563,952,749,445,193,366,460,142,542,802,994,861],[455,452,339,535,966,915,668,471,346,459,15,797,100,740,693,961],[17,796,94,914,395,797,101,425,482,250,739,424,102,31,275,304],[879,724,360,112,419,566,704,738,755,439,793,558,973,405,736,866],[558,200,384,371,75,67,709,145,499,274,534,301,300,452,620,201],[228,849,146,275,369,13,652,523,210,209,810,67,156,376,931,278],[104,160,1]]
def bRowC_195 : List Nat := List.flatten [[23,707,61,550,993,893,452,942,769,750,931,170,689,516,824,462],[76,236,415,664,447,652,359,585,27,406,764,496,869,596,793,616],[320,483,726,1,143,48,18,456,13,565,369,617,642,279,20,105],[872,165,172,345,473,917,382,884,899,708,586,910,116,916,648,600],[702,134,137,343,383,632,553,384,722,543,96,607,997,63,292,993],[406,885,432,635,254,416,488,420,940,13,604,179,662,386,473,622],[980,105,829,677,866,163,455,549,201,216,667,861,194,739,703,904],[618,695,53,595,333,734,245,609,272,934,763,122,487,28,64,324],[863,0,672,634,276,197,383,99,902,414,653,745,412,230,632,361],[262,817,140,145,688,171,405,446,772,545,703,531,162,927,490,18],[121,923,781,98,682,598,4,458,362,477,146,587,207,356,644,381],[82,625,93,196,751,4,445,667,153,110,696,1001,358,185,454,530],[730,391,30,1]]
def bRowC_196 : List Nat := List.flatten [[74,467,442,251,175,426,768,207,598,389,492,825,430,361,474,993],[619,127,433,733,380,192,144,300,897,287,836,824,720,606,707,994],[812,343,764,25,144,422,876,26,579,510,678,325,679,907,4,323],[673,727,110,727,497,369,48,324,991,162,368,51,430,83,422,471],[551,95,931,821,389,20,306,434,899,902,699,305,545,777,501,924],[757,4,380,513,276,363,117,409,931,188,576,588,722,220,153,592],[410,343,645,867,145,520,126,520,204,991,329,27,977,996,234,962],[278,374,953,160,805,987,171,195,451,412,548,304,227,501,246,126],[19,6,91,799,980,799,741,449,809,808,649,771,994,831,733,568],[209,630,234,384,213,279,42,878,323,326,894,100,869,899,16,412],[168,309,141,675,991,774,361,68,238,156,223,370,183,529,837,904],[855,587,778,309,868,158,451,712,910,131,669,764,231,493,665,584],[499,505,136,70,1]]
def bRowC_197 : List Nat := List.flatten [[358,746,954,566,930,740,143,716,414,599,667,107,1001,425,35,702],[267,772,525,606,277,189,657,427,759,943,74,940,764,994,741,451],[449,435,682,322,740,509,894,321,551,878,492,698,87,741,184,107],[962,801,453,366,380,805,292,672,256,528,290,164,694,95,202,58],[884,834,588,756,135,269,374,649,402,596,805,362,408,881,304,219],[728,537,210,316,791,560,666,9,38,395,694,474,427,742,604,436],[782,975,484,649,673,860,772,824,1003,749,982,186,76,182,937,49],[693,510,441,924,124,460,952,299,795,363,317,639,636,508,63,360],[988,763,198,691,359,619,374,387,484,799,266,143,639,723,331,276],[526,634,933,418,401,221,730,304,536,214,378,151,210,198,765,465],[298,36,7,74,363,887,91,957,554,952,41,84,204,492,691,465],[118,991,732,712,669,238,455,511,451,864,104,643,424,394,493,922],[309,996,910,229,194,1]]
def bRowC_198 : List Nat := List.flatten [[633,980,655,830,231,236,224,786,24,782,555,457,451,843,620,726],[52,383,318,871,451,392,18,334,509,945,194,841,624,431,898,724],[784,161,122,516,42,707,249,725,358,675,529,848,135,964,8,24],[378,628,303,204,884,41,409,30,146,505,432,37,510,503,64,866],[131,777,690,90,542,668,865,774,632,871,803,96,466,896,740,614],[824,42,859,585,822,751,56,981,332,775,634,149,519,704,541,274],[388,806,791,463,866,583,956,863,730,717,654,755,285,975,179,115],[359,732,452,677,705,174,551,630,361,231,452,914,636,142,823,773],[257,495,74,792,296,306,834,93,456,715,726,813,414,591,798,886],[410,465,539,65,784,974,698,57,930,879,554,806,163,546,960,529],[589,243,999,74,1000,929,110,255,297,345,301,292,364,911,837,205],[99,345,90,81,162,222,552,214,832,745,492,912,889,175,817,82],[856,20,430,514,675,217,1]]

def bMatC : List (List Nat) := List.flatten [
  [bRowC_0,bRowC_1,bRowC_2,bRowC_3,bRowC_4,bRowC_5,bRowC_6,bRowC_7,bRowC_8,bRowC_9,bRowC_10,bRowC_11,bRowC_12,bRowC_13,bRowC_14,bRowC_15,bRowC_16,bRowC_17,bRowC_18,bRowC_19],
  [bRowC_20,bRowC_21,bRowC_22,bRowC_23,bRowC_24,bRowC_25,bRowC_26,bRowC_27,bRowC_28,bRowC_29,bRowC_30,bRowC_31,bRowC_32,bRowC_33,bRowC_34,bRowC_35,bRowC_36,bRowC_37,bRowC_38,bRowC_39],
  [bRowC_40,bRowC_41,bRowC_42,bRowC_43,bRowC_44,bRowC_45,bRowC_46,bRowC_47,bRowC_48,bRowC_49,bRowC_50,bRowC_51,bRowC_52,bRowC_53,bRowC_54,bRowC_55,bRowC_56,bRowC_57,bRowC_58,bRowC_59],
  [bRowC_60,bRowC_61,bRowC_62,bRowC_63,bRowC_64,bRowC_65,bRowC_66,bRowC_67,bRowC_68,bRowC_69,bRowC_70,bRowC_71,bRowC_72,bRowC_73,bRowC_74,bRowC_75,bRowC_76,bRowC_77,bRowC_78,bRowC_79],
  [bRowC_80,bRowC_81,bRowC_82,bRowC_83,bRowC_84,bRowC_85,bRowC_86,bRowC_87,bRowC_88,bRowC_89,bRowC_90,bRowC_91,bRowC_92,bRowC_93,bRowC_94,bRowC_95,bRowC_96,bRowC_97,bRowC_98,bRowC_99],
  [bRowC_100,bRowC_101,bRowC_102,bRowC_103,bRowC_104,bRowC_105,bRowC_106,bRowC_107,bRowC_108,bRowC_109,bRowC_110,bRowC_111,bRowC_112,bRowC_113,bRowC_114,bRowC_115,bRowC_116,bRowC_117,bRowC_118,bRowC_119],
  [bRowC_120,bRowC_121,bRowC_122,bRowC_123,bRowC_124,bRowC_125,bRowC_126,bRowC_127,bRowC_128,bRowC_129,bRowC_130,bRowC_131,bRowC_132,bRowC_133,bRowC_134,bRowC_135,bRowC_136,bRowC_137,bRowC_138,bRowC_139],
  [bRowC_140,bRowC_141,bRowC_142,bRowC_143,bRowC_144,bRowC_145,bRowC_146,bRowC_147,bRowC_148,bRowC_149,bRowC_150,bRowC_151,bRowC_152,bRowC_153,bRowC_154,bRowC_155,bRowC_156,bRowC_157,bRowC_158,bRowC_159],
  [bRowC_160,bRowC_161,bRowC_162,bRowC_163,bRowC_164,bRowC_165,bRowC_166,bRowC_167,bRowC_168,bRowC_169,bRowC_170,bRowC_171,bRowC_172,bRowC_173,bRowC_174,bRowC_175,bRowC_176,bRowC_177,bRowC_178,bRowC_179],
  [bRowC_180,bRowC_181,bRowC_182,bRowC_183,bRowC_184,bRowC_185,bRowC_186,bRowC_187,bRowC_188,bRowC_189,bRowC_190,bRowC_191,bRowC_192,bRowC_193,bRowC_194,bRowC_195,bRowC_196,bRowC_197,bRowC_198]
]

def fA (i j : Nat) : Bool :=
  primeMask.testBit (2 * perm8A i + 2 * perm8A j + 3)

def fC (i j : Nat) : Bool :=
  primeMask.testBit (2 * perm8C i + 2 * perm8C j + 5)

def colsA : List Nat :=
  (List.range 200).map fun c =>
    packPoly ((List.range 200).map fun j => if fA (200 - 1 - j) c then 1 else 0)

def colsC : List Nat :=
  (List.range 199).map fun c =>
    packPoly ((List.range 199).map fun j => if fC (199 - 1 - j) c then 1 else 0)

theorem checkA_ok : checkAll 200 colsA bMatA 0 = true := by decide +kernel

theorem checkC_ok : checkAll 199 colsC bMatC 0 = true := by decide +kernel

theorem det_A_ne_zero (k : Nat) (hk : 8 ≤ k) (hk200 : k ≤ 200) :
    (Matrix.of fun (i j : Fin k) =>
      if Nat.Prime (2 * i.1 + 2 * j.1 + 3) then (1 : ZMod 1009) else 0).det ≠ 0 := by
  have h1 := det_submatrix_of_checkAll 200 (by decide) (by decide) fA bMatA checkA_ok k (by omega) hk200
  let A : Matrix (Fin k) (Fin k) (ZMod 1009) :=
    Matrix.of fun i j => if Nat.Prime (2 * i.1 + 2 * j.1 + 3) then 1 else 0
  have heq : (Matrix.of fun (i j : Fin k) => if fA i.1 j.1 then (1 : ZMod 1009) else 0) =
      A.submatrix (ePermA k hk) (ePermA k hk) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, fA, A, ePermA, Equiv.coe_fn_mk]
    have hi_lt : perm8A i.1 < k := by
      rcases i with ⟨i, hi⟩
      match i with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp [perm8A]; omega | n + 8 => simp [perm8A]; omega
    have hj_lt : perm8A j.1 < k := by
      rcases j with ⟨j, hj⟩
      match j with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp [perm8A]; omega | n + 8 => simp [perm8A]; omega
    have hlt : 2 * perm8A i.1 + 2 * perm8A j.1 + 3 < 805 := by omega
    by_cases hp : Nat.Prime (2 * perm8A i.1 + 2 * perm8A j.1 + 3)
    · have ht := (primeMask_testBit_iff hlt).mpr hp
      simp [ht, hp]
    · have hf : primeMask.testBit (2 * perm8A i.1 + 2 * perm8A j.1 + 3) = false := by
        cases hb : primeMask.testBit (2 * perm8A i.1 + 2 * perm8A j.1 + 3)
        · rfl
        · exact absurd ((primeMask_testBit_iff hlt).mp hb) hp
      simp [hf, hp]
  rw [heq, Matrix.det_submatrix_equiv_self] at h1
  exact h1

theorem det_C_ne_zero (k : Nat) (hk : 8 ≤ k) (hk199 : k ≤ 199) :
    (Matrix.of fun (i j : Fin k) =>
      if Nat.Prime (2 * i.1 + 2 * j.1 + 5) then (1 : ZMod 1009) else 0).det ≠ 0 := by
  have h1 := det_submatrix_of_checkAll 199 (by decide) (by decide) fC bMatC checkC_ok k (by omega) hk199
  let C : Matrix (Fin k) (Fin k) (ZMod 1009) :=
    Matrix.of fun i j => if Nat.Prime (2 * i.1 + 2 * j.1 + 5) then 1 else 0
  have heq : (Matrix.of fun (i j : Fin k) => if fC i.1 j.1 then (1 : ZMod 1009) else 0) =
      C.submatrix (ePermC k hk) (ePermC k hk) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, fC, C, ePermC, Equiv.coe_fn_mk]
    have hi_lt : perm8C i.1 < k := by
      rcases i with ⟨i, hi⟩
      match i with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp [perm8C]; omega | n + 8 => simp [perm8C]; omega
    have hj_lt : perm8C j.1 < k := by
      rcases j with ⟨j, hj⟩
      match j with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp [perm8C]; omega | n + 8 => simp [perm8C]; omega
    have hlt : 2 * perm8C i.1 + 2 * perm8C j.1 + 5 < 805 := by omega
    by_cases hp : Nat.Prime (2 * perm8C i.1 + 2 * perm8C j.1 + 5)
    · have ht := (primeMask_testBit_iff hlt).mpr hp
      simp [ht, hp]
    · have hf : primeMask.testBit (2 * perm8C i.1 + 2 * perm8C j.1 + 5) = false := by
        cases hb : primeMask.testBit (2 * perm8C i.1 + 2 * perm8C j.1 + 5)
        · rfl
        · exact absurd ((primeMask_testBit_iff hlt).mp hb) hp
      simp [hf, hp]
  rw [heq, Matrix.det_submatrix_equiv_self] at h1
  exact h1

end OeisA228552Proof

theorem OMA.solution : OMA.R_OeisA228552_conjecture_R1.H1 := by
  intro n hn15 hn400
  by_cases hpar : n % 2 = 0
  · have hk_eq : n = 2 * (n / 2) := by omega
    rw [hk_eq]
    exact OeisA228552Proof.a_pos_of_det_zmod_ne_zero (2 * (n / 2))
      (OeisA228552Proof.det_primeMatrix_even (n / 2) (by omega) (by omega)
        (OeisA228552Proof.det_A_ne_zero (n / 2) (by omega) (by omega)))
  · have hk_eq : n = 2 * (n / 2) + 1 := by omega
    rw [hk_eq]
    exact OeisA228552Proof.a_pos_of_det_zmod_ne_zero (2 * (n / 2) + 1)
      (OeisA228552Proof.det_primeMatrix_odd (n / 2) (by omega) (by omega)
        (OeisA228552Proof.det_C_ne_zero (n / 2) (by omega) (by omega)))
