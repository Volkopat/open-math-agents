import OMAStatements.S_oeis_a225894

namespace OMA.P_oeis_a225894

open OMA.S_oeis_a225894

private def nfaStep (q : Fin 40) (a b : Fin 4) : Option (Fin 40) :=
  let cc := q.1 % 2
  let bu := (q.1 / 2) % 2
  let pm := q.1 / 4
  let a0 := a.1 % 2
  let a1 := a.1 / 2
  let b0 := b.1 % 2
  let b1 := b.1 / 2
  let nbu := bu + b0 + b1
  if hbu : nbu ≤ 1 then
    let m0 := a0 + b0
    let m1 := a1 + b1
    let mcode := 3 * m0 + m1
    if (pm == 9 || pm ≤ mcode) && (cc == 1 || m0 ≤ m1) then
      let ncc := if cc == 1 || m0 < m1 then 1 else 0
      some ⟨(mcode * 2 + nbu) * 2 + ncc, by
        have := a.2; have := b.2
        have hncc : ncc ≤ 1 := by dsimp [ncc]; split_ifs <;> omega
        omega⟩
    else none
  else none

private def nfaPre (a : Fin 4) (q : Fin 40) : ℕ :=
  match a.1 with
  | 0 => (if q.1 < 20 then (if q.1 < 10 then (if q.1 < 5 then (if q.1 < 2 then (if q.1 < 1 then 68719476737 else 137438953474) else (if q.1 < 3 then 274877906948 else (if q.1 < 4 then 549755813896 else 0))) else (if q.1 < 7 then (if q.1 < 6 then 0 else 0) else (if q.1 < 8 then 206158430259 else (if q.1 < 9 then 0 else 0)))) else (if q.1 < 15 then (if q.1 < 12 then (if q.1 < 11 then 0 else 0) else (if q.1 < 13 then 0 else (if q.1 < 14 then 0 else 0))) else (if q.1 < 17 then (if q.1 < 16 then 137438962210 else 0) else (if q.1 < 18 then 0 else (if q.1 < 19 then 0 else 0))))) else (if q.1 < 30 then (if q.1 < 25 then (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else (if q.1 < 24 then 0 else 0))) else (if q.1 < 27 then (if q.1 < 26 then 0 else 0) else (if q.1 < 28 then 0 else (if q.1 < 29 then 0 else 0)))) else (if q.1 < 35 then (if q.1 < 32 then (if q.1 < 31 then 0 else 0) else (if q.1 < 33 then 0 else (if q.1 < 34 then 0 else 0))) else (if q.1 < 37 then (if q.1 < 36 then 0 else 0) else (if q.1 < 38 then 0 else (if q.1 < 39 then 0 else 0))))))
  | 1 => (if q.1 < 20 then (if q.1 < 10 then (if q.1 < 5 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else (if q.1 < 4 then 0 else 0))) else (if q.1 < 7 then (if q.1 < 6 then 0 else 0) else (if q.1 < 8 then 0 else (if q.1 < 9 then 0 else 0)))) else (if q.1 < 15 then (if q.1 < 12 then (if q.1 < 11 then 0 else 0) else (if q.1 < 13 then 0 else (if q.1 < 14 then 137438962210 else 0))) else (if q.1 < 17 then (if q.1 < 16 then 549755848840 else 0) else (if q.1 < 18 then 0 else (if q.1 < 19 then 68719546641 else 137439093282))))) else (if q.1 < 30 then (if q.1 < 25 then (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else (if q.1 < 24 then 0 else 0))) else (if q.1 < 27 then (if q.1 < 26 then 0 else 0) else (if q.1 < 28 then 137474744866 else (if q.1 < 29 then 0 else 0)))) else (if q.1 < 35 then (if q.1 < 32 then (if q.1 < 31 then 0 else 0) else (if q.1 < 33 then 0 else (if q.1 < 34 then 0 else 0))) else (if q.1 < 37 then (if q.1 < 36 then 0 else 0) else (if q.1 < 38 then 0 else (if q.1 < 39 then 0 else 0))))))
  | 2 => (if q.1 < 20 then (if q.1 < 10 then (if q.1 < 5 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else (if q.1 < 4 then 0 else 0))) else (if q.1 < 7 then (if q.1 < 6 then 206158430259 else 0) else (if q.1 < 8 then 824633721036 else (if q.1 < 9 then 0 else 0)))) else (if q.1 < 15 then (if q.1 < 12 then (if q.1 < 11 then 0 else 206158431027) else (if q.1 < 13 then 0 else (if q.1 < 14 then 0 else 0))) else (if q.1 < 17 then (if q.1 < 16 then 0 else 0) else (if q.1 < 18 then 0 else (if q.1 < 19 then 68719546641 else 137439093282))))) else (if q.1 < 30 then (if q.1 < 25 then (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else (if q.1 < 24 then 0 else 0))) else (if q.1 < 27 then (if q.1 < 26 then 0 else 0) else (if q.1 < 28 then 0 else (if q.1 < 29 then 0 else 0)))) else (if q.1 < 35 then (if q.1 < 32 then (if q.1 < 31 then 0 else 0) else (if q.1 < 33 then 0 else (if q.1 < 34 then 0 else 0))) else (if q.1 < 37 then (if q.1 < 36 then 0 else 0) else (if q.1 < 38 then 0 else (if q.1 < 39 then 0 else 0))))))
  | 3 => (if q.1 < 20 then (if q.1 < 10 then (if q.1 < 5 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else (if q.1 < 4 then 0 else 0))) else (if q.1 < 7 then (if q.1 < 6 then 0 else 0) else (if q.1 < 8 then 0 else (if q.1 < 9 then 0 else 0)))) else (if q.1 < 15 then (if q.1 < 12 then (if q.1 < 11 then 0 else 0) else (if q.1 < 13 then 0 else (if q.1 < 14 then 0 else 0))) else (if q.1 < 17 then (if q.1 < 16 then 0 else 68719546641) else (if q.1 < 18 then 137439093282 else (if q.1 < 19 then 274878186564 else 549756373128))))) else (if q.1 < 30 then (if q.1 < 25 then (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else (if q.1 < 24 then 206161785651 else 0))) else (if q.1 < 27 then (if q.1 < 26 then 0 else 0) else (if q.1 < 28 then 0 else (if q.1 < 29 then 0 else 0)))) else (if q.1 < 35 then (if q.1 < 32 then (if q.1 < 31 then 0 else 138011615778) else (if q.1 < 33 then 0 else (if q.1 < 34 then 0 else 0))) else (if q.1 < 37 then (if q.1 < 36 then 0 else 0) else (if q.1 < 38 then 0 else (if q.1 < 39 then 0 else 0))))))
  | _ => 0

private lemma nfaPre_testBit_0 : ∀ q' q : Fin 40,
    (nfaPre ⟨0, by omega⟩ q').testBit q.1 = decide (∃ b : Fin 4, nfaStep q ⟨0, by omega⟩ b = some q') := by decide
private lemma nfaPre_testBit_1 : ∀ q' q : Fin 40,
    (nfaPre ⟨1, by omega⟩ q').testBit q.1 = decide (∃ b : Fin 4, nfaStep q ⟨1, by omega⟩ b = some q') := by decide
private lemma nfaPre_testBit_2 : ∀ q' q : Fin 40,
    (nfaPre ⟨2, by omega⟩ q').testBit q.1 = decide (∃ b : Fin 4, nfaStep q ⟨2, by omega⟩ b = some q') := by decide
private lemma nfaPre_testBit_3 : ∀ q' q : Fin 40,
    (nfaPre ⟨3, by omega⟩ q').testBit q.1 = decide (∃ b : Fin 4, nfaStep q ⟨3, by omega⟩ b = some q') := by decide

private lemma nfaPre_testBit (a : Fin 4) (q' q : Fin 40) :
    (nfaPre a q').testBit q.1 = decide (∃ b : Fin 4, nfaStep q a b = some q') := by
  fin_cases a
  · exact nfaPre_testBit_0 q' q
  · exact nfaPre_testBit_1 q' q
  · exact nfaPre_testBit_2 q' q
  · exact nfaPre_testBit_3 q' q

private def dfaMask (s : Fin 20) : ℕ :=
  (if s.1 < 10 then (if s.1 < 5 then (if s.1 < 2 then (if s.1 < 1 then 68719476736 else 129) else (if s.1 < 3 then 262144 else (if s.1 < 4 then 264224 else 8454144))) else (if s.1 < 7 then (if s.1 < 6 then 294912 else 264352) else (if s.1 < 8 then 8978432 else (if s.1 < 9 then 0 else 32896)))) else (if s.1 < 15 then (if s.1 < 12 then (if s.1 < 11 then 134782976 else 526368) else (if s.1 < 13 then 2156789760 else (if s.1 < 14 then 32768 else 786432))) else (if s.1 < 17 then (if s.1 < 16 then 526496 else 128) else (if s.1 < 18 then 524288 else (if s.1 < 19 then 2156527616 else 134742016)))))

private def dfaTrans (s : Fin 20) (a : Fin 4) : Fin 20 :=
  match s.1 with
  | 0 => match a.1 with | 0 => ⟨1, by omega⟩ | 1 => ⟨2, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨4, by omega⟩
  | 1 => match a.1 with | 0 => ⟨1, by omega⟩ | 1 => ⟨5, by omega⟩ | 2 => ⟨6, by omega⟩ | _ => ⟨7, by omega⟩
  | 2 => match a.1 with | 0 => ⟨8, by omega⟩ | 1 => ⟨8, by omega⟩ | 2 => ⟨8, by omega⟩ | _ => ⟨2, by omega⟩
  | 3 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨10, by omega⟩ | 2 => ⟨11, by omega⟩ | _ => ⟨12, by omega⟩
  | 4 => match a.1 with | 0 => ⟨8, by omega⟩ | 1 => ⟨2, by omega⟩ | 2 => ⟨2, by omega⟩ | _ => ⟨4, by omega⟩
  | 5 => match a.1 with | 0 => ⟨8, by omega⟩ | 1 => ⟨13, by omega⟩ | 2 => ⟨8, by omega⟩ | _ => ⟨14, by omega⟩
  | 6 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨10, by omega⟩ | 2 => ⟨15, by omega⟩ | _ => ⟨12, by omega⟩
  | 7 => match a.1 with | 0 => ⟨8, by omega⟩ | 1 => ⟨2, by omega⟩ | 2 => ⟨2, by omega⟩ | _ => ⟨7, by omega⟩
  | 8 => match a.1 with | 0 => ⟨8, by omega⟩ | 1 => ⟨8, by omega⟩ | 2 => ⟨8, by omega⟩ | _ => ⟨8, by omega⟩
  | 9 => match a.1 with | 0 => ⟨8, by omega⟩ | 1 => ⟨13, by omega⟩ | 2 => ⟨16, by omega⟩ | _ => ⟨17, by omega⟩
  | 10 => match a.1 with | 0 => ⟨13, by omega⟩ | 1 => ⟨10, by omega⟩ | 2 => ⟨17, by omega⟩ | _ => ⟨18, by omega⟩
  | 11 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨10, by omega⟩ | 2 => ⟨11, by omega⟩ | _ => ⟨18, by omega⟩
  | 12 => match a.1 with | 0 => ⟨8, by omega⟩ | 1 => ⟨19, by omega⟩ | 2 => ⟨17, by omega⟩ | _ => ⟨12, by omega⟩
  | 13 => match a.1 with | 0 => ⟨8, by omega⟩ | 1 => ⟨13, by omega⟩ | 2 => ⟨8, by omega⟩ | _ => ⟨17, by omega⟩
  | 14 => match a.1 with | 0 => ⟨8, by omega⟩ | 1 => ⟨8, by omega⟩ | 2 => ⟨8, by omega⟩ | _ => ⟨14, by omega⟩
  | 15 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨10, by omega⟩ | 2 => ⟨15, by omega⟩ | _ => ⟨18, by omega⟩
  | 16 => match a.1 with | 0 => ⟨8, by omega⟩ | 1 => ⟨13, by omega⟩ | 2 => ⟨16, by omega⟩ | _ => ⟨17, by omega⟩
  | 17 => match a.1 with | 0 => ⟨8, by omega⟩ | 1 => ⟨8, by omega⟩ | 2 => ⟨8, by omega⟩ | _ => ⟨17, by omega⟩
  | 18 => match a.1 with | 0 => ⟨8, by omega⟩ | 1 => ⟨19, by omega⟩ | 2 => ⟨17, by omega⟩ | _ => ⟨18, by omega⟩
  | 19 => match a.1 with | 0 => ⟨8, by omega⟩ | 1 => ⟨8, by omega⟩ | 2 => ⟨8, by omega⟩ | _ => ⟨17, by omega⟩
  | _ => ⟨0, by omega⟩

private lemma dfaTrans_empty : ∀ a : Fin 4, dfaTrans ⟨8, by omega⟩ a = ⟨8, by omega⟩ := by decide

private lemma dfaTrans_not_empty (s : Fin 20) (a : Fin 4) (h : dfaTrans s a ≠ ⟨8, by omega⟩) :
    s ≠ ⟨8, by omega⟩ := by
  intro hs; subst hs; exact h (dfaTrans_empty a)

private lemma dfaMask_lt : ∀ s : Fin 20, dfaMask s < 2 ^ 40 := by decide

private lemma dfaMask_ne_zero_iff : ∀ s : Fin 20, dfaMask s ≠ 0 ↔ s.1 ≠ 8 := by decide

private lemma dfaMask_init : ∀ q : Fin 40,
    (dfaMask ⟨0, by omega⟩).testBit q.1 = true ↔ q.1 = 36 := by decide

private lemma dfaTrans_spec_bit_0_0 : ∀ i : Fin 16, ∀ q' : Fin 40,
    (dfaMask (dfaTrans ⟨0 + i.1, by omega⟩ ⟨0, by omega⟩)).testBit q'.1 = ((dfaMask ⟨0 + i.1, by omega⟩ &&& nfaPre ⟨0, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_0_16 : ∀ i : Fin 4, ∀ q' : Fin 40,
    (dfaMask (dfaTrans ⟨16 + i.1, by omega⟩ ⟨0, by omega⟩)).testBit q'.1 = ((dfaMask ⟨16 + i.1, by omega⟩ &&& nfaPre ⟨0, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_0 (s : Fin 20) (q' : Fin 40) :
    (dfaMask (dfaTrans s ⟨0, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨0, by omega⟩ q') != 0) := by
  if h0 : s.1 < 16 then
    have hs : s = ⟨0 + (s.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_0_0 ⟨s.1 - 0, by omega⟩ q'
  else
    have hs : s = ⟨16 + (s.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_0_16 ⟨s.1 - 16, by omega⟩ q'
private lemma dfaTrans_spec_bit_1_0 : ∀ i : Fin 16, ∀ q' : Fin 40,
    (dfaMask (dfaTrans ⟨0 + i.1, by omega⟩ ⟨1, by omega⟩)).testBit q'.1 = ((dfaMask ⟨0 + i.1, by omega⟩ &&& nfaPre ⟨1, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_1_16 : ∀ i : Fin 4, ∀ q' : Fin 40,
    (dfaMask (dfaTrans ⟨16 + i.1, by omega⟩ ⟨1, by omega⟩)).testBit q'.1 = ((dfaMask ⟨16 + i.1, by omega⟩ &&& nfaPre ⟨1, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_1 (s : Fin 20) (q' : Fin 40) :
    (dfaMask (dfaTrans s ⟨1, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨1, by omega⟩ q') != 0) := by
  if h0 : s.1 < 16 then
    have hs : s = ⟨0 + (s.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_1_0 ⟨s.1 - 0, by omega⟩ q'
  else
    have hs : s = ⟨16 + (s.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_1_16 ⟨s.1 - 16, by omega⟩ q'
private lemma dfaTrans_spec_bit_2_0 : ∀ i : Fin 16, ∀ q' : Fin 40,
    (dfaMask (dfaTrans ⟨0 + i.1, by omega⟩ ⟨2, by omega⟩)).testBit q'.1 = ((dfaMask ⟨0 + i.1, by omega⟩ &&& nfaPre ⟨2, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_2_16 : ∀ i : Fin 4, ∀ q' : Fin 40,
    (dfaMask (dfaTrans ⟨16 + i.1, by omega⟩ ⟨2, by omega⟩)).testBit q'.1 = ((dfaMask ⟨16 + i.1, by omega⟩ &&& nfaPre ⟨2, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_2 (s : Fin 20) (q' : Fin 40) :
    (dfaMask (dfaTrans s ⟨2, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨2, by omega⟩ q') != 0) := by
  if h0 : s.1 < 16 then
    have hs : s = ⟨0 + (s.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_2_0 ⟨s.1 - 0, by omega⟩ q'
  else
    have hs : s = ⟨16 + (s.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_2_16 ⟨s.1 - 16, by omega⟩ q'
private lemma dfaTrans_spec_bit_3_0 : ∀ i : Fin 16, ∀ q' : Fin 40,
    (dfaMask (dfaTrans ⟨0 + i.1, by omega⟩ ⟨3, by omega⟩)).testBit q'.1 = ((dfaMask ⟨0 + i.1, by omega⟩ &&& nfaPre ⟨3, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_3_16 : ∀ i : Fin 4, ∀ q' : Fin 40,
    (dfaMask (dfaTrans ⟨16 + i.1, by omega⟩ ⟨3, by omega⟩)).testBit q'.1 = ((dfaMask ⟨16 + i.1, by omega⟩ &&& nfaPre ⟨3, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_3 (s : Fin 20) (q' : Fin 40) :
    (dfaMask (dfaTrans s ⟨3, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨3, by omega⟩ q') != 0) := by
  if h0 : s.1 < 16 then
    have hs : s = ⟨0 + (s.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_3_0 ⟨s.1 - 0, by omega⟩ q'
  else
    have hs : s = ⟨16 + (s.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_3_16 ⟨s.1 - 16, by omega⟩ q'

private lemma dfaTrans_spec_bit (s : Fin 20) (a : Fin 4) (q' : Fin 40) :
    (dfaMask (dfaTrans s a)).testBit q'.1 = ((dfaMask s &&& nfaPre a q') != 0) := by
  fin_cases a
  · exact dfaTrans_spec_bit_0 s q'
  · exact dfaTrans_spec_bit_1 s q'
  · exact dfaTrans_spec_bit_2 s q'
  · exact dfaTrans_spec_bit_3 s q'

private lemma and_ne_zero_iff (x y : ℕ) (hx : x < 2 ^ 40) :
    ((x &&& y) != 0) = true ↔ ∃ q : Fin 40, x.testBit q.1 = true ∧ y.testBit q.1 = true := by
  simp only [bne_iff_ne, ne_eq]
  constructor
  · intro hne
    by_contra hall; push Not at hall
    apply hne; apply Nat.eq_of_testBit_eq; intro k
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hk : k < 40
    · have := hall ⟨k, hk⟩
      by_cases hx1 : x.testBit k = true
      · have hy1 : y.testBit k = false := by cases h' : y.testBit k <;> simp_all
        simp [hx1, hy1]
      · have hx0 : x.testBit k = false := by cases h' : x.testBit k <;> simp_all
        simp [hx0]
    · have hpow : 2 ^ 40 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      have hx0 : x.testBit k = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx hpow)
      simp [hx0]
  · rintro ⟨q, hxq, hyq⟩ h0
    have := congrArg (fun z => z.testBit q.1) h0
    rw [Nat.testBit_and, Nat.zero_testBit, hxq, hyq] at this
    exact absurd this (by decide)

private lemma dfaMask_empty_iff (s : Fin 20) :
    (∃ q : Fin 40, (dfaMask s).testBit q.1 = true) ↔ s.1 ≠ 8 := by
  rw [← dfaMask_ne_zero_iff s]
  have h := and_ne_zero_iff (dfaMask s) (dfaMask s) (dfaMask_lt s)
  simp only [Nat.and_self, bne_iff_ne, ne_eq, and_self] at h
  exact h.symm

private lemma dfaTrans_iff (s : Fin 20) (a : Fin 4) (q' : Fin 40) :
    (dfaMask (dfaTrans s a)).testBit q'.1 = true ↔
    ∃ q : Fin 40, (dfaMask s).testBit q.1 = true ∧ ∃ b : Fin 4, nfaStep q a b = some q' := by
  rw [dfaTrans_spec_bit, and_ne_zero_iff _ _ (dfaMask_lt s)]
  constructor
  · rintro ⟨q, hq, hpre⟩
    rw [nfaPre_testBit, decide_eq_true_eq] at hpre
    exact ⟨q, hq, hpre⟩
  · rintro ⟨q, hq, hb⟩
    refine ⟨q, hq, ?_⟩
    rw [nfaPre_testBit, decide_eq_true_eq]; exact hb

private def runDFA : (n : ℕ) → (Fin n → Fin 4) → Fin 20
  | 0, _ => ⟨0, by omega⟩
  | n + 1, A => dfaTrans (runDFA n (fun i => A i.castSucc)) (A (Fin.last n))

private def runNFA : (n : ℕ) → (Fin n → Fin 4) → (Fin n → Fin 4) → Option (Fin 40)
  | 0, _, _ => some ⟨36, by omega⟩
  | n + 1, A, B =>
    match runNFA n (fun i => A i.castSucc) (fun i => B i.castSucc) with
    | none => none
    | some q => nfaStep q (A (Fin.last n)) (B (Fin.last n))

private lemma runDFA_iff_runNFA (n : ℕ) (A : Fin n → Fin 4) (q : Fin 40) :
    (dfaMask (runDFA n A)).testBit q.1 = true ↔ ∃ B : Fin n → Fin 4, runNFA n A B = some q := by
  induction n generalizing q with
  | zero =>
    unfold runDFA; rw [dfaMask_init]
    constructor
    · intro hq; refine ⟨Fin.elim0, ?_⟩; unfold runNFA; congr 1; exact Fin.ext hq.symm
    · rintro ⟨_, h⟩; unfold runNFA at h; injection h with h'; exact (congrArg Fin.val h').symm
  | succ n ih =>
    unfold runDFA; rw [dfaTrans_iff]
    constructor
    · rintro ⟨q0, hq0, bLast, hstep⟩
      obtain ⟨B0, hB0⟩ := (ih (fun i => A i.castSucc) q0).mp hq0
      refine ⟨Fin.snoc B0 bLast, ?_⟩
      unfold runNFA
      have hcast : (fun i : Fin n => (Fin.snoc B0 bLast : Fin (n + 1) → Fin 4) i.castSucc) = B0 := by
        funext i; exact Fin.snoc_castSucc _ _ i
      rw [hcast, hB0, Fin.snoc_last]; exact hstep
    · rintro ⟨B, hB⟩
      unfold runNFA at hB
      cases hprev : runNFA n (fun i => A i.castSucc) (fun i => B i.castSucc) with
      | none => rw [hprev] at hB; simp at hB
      | some q0 =>
        rw [hprev] at hB
        exact ⟨q0, (ih (fun i => A i.castSucc) q0).mpr ⟨fun i => B i.castSucc, hprev⟩, B (Fin.last n), hB⟩

private def enc2 (r : Fin 2 → Fin 2) : Fin 4 :=
  ⟨(r 0).1 + 2 * (r 1).1, by have := (r 0).2; have := (r 1).2; omega⟩

private def dec2 (x : Fin 4) (c : Fin 2) : Fin 2 :=
  if c.1 = 0 then ⟨x.1 % 2, Nat.mod_lt _ (by omega)⟩ else ⟨x.1 / 2, by have := x.2; omega⟩

private lemma enc2_dec2 (x : Fin 4) : enc2 (dec2 x) = x := by
  apply Fin.ext; unfold enc2 dec2; dsimp; have := x.2; omega

private lemma dec2_enc2 (r : Fin 2 → Fin 2) : dec2 (enc2 r) = r := by
  funext c; fin_cases c <;> (apply Fin.ext; unfold dec2 enc2; dsimp; have := (r 0).2; have := (r 1).2; omega)

private lemma div2_add_le_two (x y : Fin 4) : x.1 / 2 + y.1 / 2 ≤ 2 := by
  have := x.2; have := y.2; omega

private lemma lexRow2_of_code (a0 a1 b0 b1 : ℕ) (ha1 : a1 ≤ 2) (hb1 : b1 ≤ 2) (h : 3 * a0 + a1 ≤ 3 * b0 + b1) :
    lexRow2 a0 a1 b0 b1 := by
  unfold lexRow2; by_cases hlt : a0 < b0
  · left; exact hlt
  · right; exact ⟨by omega, by omega⟩

private lemma runNFA_sound (n : ℕ) (A B : Fin n → Fin 4) (q : Fin 40) (h : runNFA n A B = some q) :
    (q.1 / 2) % 2 = (∑ r : Fin n, ((B r).1 % 2 + (B r).1 / 2)) ∧
    (∑ r : Fin n, ((B r).1 % 2 + (B r).1 / 2)) ≤ 1 ∧
    (n = 0 → q.1 / 4 = 9) ∧
    (∀ hn : 0 < n, q.1 / 4 =
      3 * ((A ⟨n - 1, by omega⟩).1 % 2 + (B ⟨n - 1, by omega⟩).1 % 2) +
          ((A ⟨n - 1, by omega⟩).1 / 2 + (B ⟨n - 1, by omega⟩).1 / 2)) ∧
    (q.1 % 2 = 0 → ∀ r : Fin n, (A r).1 % 2 + (B r).1 % 2 = (A r).1 / 2 + (B r).1 / 2) ∧
    (q.1 % 2 = 1 → ∃ r : Fin n, (∀ j : Fin n, j.1 < r.1 → (A j).1 % 2 + (B j).1 % 2 = (A j).1 / 2 + (B j).1 / 2) ∧
      (A r).1 % 2 + (B r).1 % 2 < (A r).1 / 2 + (B r).1 / 2) ∧
    (∀ r : Fin (n - 1), lexRow2 ((A ⟨r.1, by omega⟩).1 % 2 + (B ⟨r.1, by omega⟩).1 % 2)
                                ((A ⟨r.1, by omega⟩).1 / 2 + (B ⟨r.1, by omega⟩).1 / 2)
                                ((A ⟨r.1 + 1, by omega⟩).1 % 2 + (B ⟨r.1 + 1, by omega⟩).1 % 2)
                                ((A ⟨r.1 + 1, by omega⟩).1 / 2 + (B ⟨r.1 + 1, by omega⟩).1 / 2)) := by
  induction n generalizing q with
  | zero =>
    unfold runNFA at h; injection h with hq; subst hq
    refine ⟨by simp, by simp, fun _ => rfl, fun hn => by omega, fun _ r => r.elim0, fun h1 => by simp at h1, fun r => r.elim0⟩
  | succ n ih =>
    unfold runNFA at h
    cases hprev : runNFA n (fun i => A i.castSucc) (fun i => B i.castSucc) with
    | none => rw [hprev] at h; simp at h
    | some q0 =>
      rw [hprev] at h
      obtain ⟨hbu0, hle0, hpm0z, hpm0p, hcc00, hcc01, hrow0⟩ := ih (fun i => A i.castSucc) (fun i => B i.castSucc) q0 hprev
      unfold nfaStep at h; dsimp only at h
      by_cases hbu_le : (q0.1 / 2) % 2 + (B (Fin.last n)).1 % 2 + (B (Fin.last n)).1 / 2 ≤ 1
      · rw [dif_pos hbu_le] at h
        by_cases hcond : ((q0.1 / 4 == 9 || decide (q0.1 / 4 ≤ 3 * ((A (Fin.last n)).1 % 2 + (B (Fin.last n)).1 % 2) + ((A (Fin.last n)).1 / 2 + (B (Fin.last n)).1 / 2))) && (q0.1 % 2 == 1 || decide ((A (Fin.last n)).1 % 2 + (B (Fin.last n)).1 % 2 ≤ (A (Fin.last n)).1 / 2 + (B (Fin.last n)).1 / 2))) = true
        swap
        · rw [if_neg hcond] at h; simp at h
        rw [if_pos hcond] at h
        injection h with hq_eq
        have hsum_succ : (∑ r : Fin (n + 1), ((B r).1 % 2 + (B r).1 / 2)) =
            (∑ r : Fin n, ((B r.castSucc).1 % 2 + (B r.castSucc).1 / 2)) + ((B (Fin.last n)).1 % 2 + (B (Fin.last n)).1 / 2) :=
          Fin.sum_univ_castSucc _
        have hqval : q.1 = ((3 * ((A (Fin.last n)).1 % 2 + (B (Fin.last n)).1 % 2) +
            ((A (Fin.last n)).1 / 2 + (B (Fin.last n)).1 / 2)) * 2 +
            ((q0.1 / 2) % 2 + (B (Fin.last n)).1 % 2 + (B (Fin.last n)).1 / 2)) * 2 +
            (if (q0.1 % 2 == 1 || decide ((A (Fin.last n)).1 % 2 + (B (Fin.last n)).1 % 2 < (A (Fin.last n)).1 / 2 + (B (Fin.last n)).1 / 2)) = true then 1 else 0) := by
          have := congrArg Fin.val hq_eq; exact this.symm
        have ha2 := (A (Fin.last n)).2; have hb2 := (B (Fin.last n)).2
        have hcond' : (q0.1 / 4 = 9 ∨ q0.1 / 4 ≤ 3 * ((A (Fin.last n)).1 % 2 + (B (Fin.last n)).1 % 2) + ((A (Fin.last n)).1 / 2 + (B (Fin.last n)).1 / 2)) ∧
            (q0.1 % 2 = 1 ∨ (A (Fin.last n)).1 % 2 + (B (Fin.last n)).1 % 2 ≤ (A (Fin.last n)).1 / 2 + (B (Fin.last n)).1 / 2) := by
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond; exact hcond
        refine ⟨?_, ?_, fun h0 => by omega, ?_, ?_, ?_, ?_⟩
        · rw [hqval, hsum_succ, ← hbu0]; split_ifs <;> omega
        · rw [hsum_succ, ← hbu0]; omega
        · intro _
          have hlast : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp [Fin.last])
          rw [hlast, hqval]; split_ifs <;> omega
        · intro hq0 r
          have hbit0 : q0.1 % 2 = 0 ∧ ¬((A (Fin.last n)).1 % 2 + (B (Fin.last n)).1 % 2 < (A (Fin.last n)).1 / 2 + (B (Fin.last n)).1 / 2) := by
            rw [hqval] at hq0
            by_cases h1 : (q0.1 % 2 == 1 || decide ((A (Fin.last n)).1 % 2 + (B (Fin.last n)).1 % 2 < (A (Fin.last n)).1 / 2 + (B (Fin.last n)).1 / 2)) = true
            · rw [if_pos h1] at hq0; omega
            · simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at h1
              exact ⟨by omega, h1.2⟩
          refine Fin.lastCases ?_ ?_ r
          · rcases hcond'.2 with hc1 | hcle
            · omega
            · omega
          · intro j; exact hcc00 hbit0.1 j
        · intro hq1
          by_cases h01 : q0.1 % 2 = 1
          · obtain ⟨r, hr1, hr2⟩ := hcc01 h01
            refine ⟨r.castSucc, fun j hj => ?_, hr2⟩
            have hjlt : j.1 < n := by have := r.2; omega
            have hjeq : (⟨j.1, hjlt⟩ : Fin n).castSucc = j := Fin.ext rfl
            rw [← hjeq]; exact hr1 ⟨j.1, hjlt⟩ hj
          · have h00 : q0.1 % 2 = 0 := by omega
            have hlt : (A (Fin.last n)).1 % 2 + (B (Fin.last n)).1 % 2 < (A (Fin.last n)).1 / 2 + (B (Fin.last n)).1 / 2 := by
              rw [hqval] at hq1
              by_cases h1 : (q0.1 % 2 == 1 || decide ((A (Fin.last n)).1 % 2 + (B (Fin.last n)).1 % 2 < (A (Fin.last n)).1 / 2 + (B (Fin.last n)).1 / 2)) = true
              · simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
                rcases h1 with h1a | h1b
                · omega
                · exact h1b
              · rw [if_neg h1] at hq1; omega
            refine ⟨Fin.last n, fun j hj => ?_, hlt⟩
            have hjlt : j.1 < n := by simp [Fin.last] at hj; exact hj
            have hjeq : (⟨j.1, hjlt⟩ : Fin n).castSucc = j := Fin.ext rfl
            rw [← hjeq]; exact hcc00 h00 ⟨j.1, hjlt⟩
        · intro r
          by_cases hr : r.1 < n - 1
          · exact hrow0 ⟨r.1, hr⟩
          · have hreq : r.1 = n - 1 := by omega
            have hnpos : 0 < n := by omega
            have hpm_eq := hpm0p hnpos
            have hpm_le : q0.1 / 4 ≤ 3 * ((A (Fin.last n)).1 % 2 + (B (Fin.last n)).1 % 2) + ((A (Fin.last n)).1 / 2 + (B (Fin.last n)).1 / 2) := by
              rcases hcond'.1 with h9 | hle
              · have := (A ⟨n - 1, by omega⟩).2; have := (B ⟨n - 1, by omega⟩).2; omega
              · exact hle
            rw [hpm_eq] at hpm_le
            have e1 : (⟨r.1, by omega⟩ : Fin (n + 1)) = (⟨n - 1, by omega⟩ : Fin n).castSucc := by apply Fin.ext; dsimp; omega
            have e2 : (⟨r.1 + 1, by omega⟩ : Fin (n + 1)) = Fin.last n := by apply Fin.ext; simp [Fin.last]; omega
            rw [e1, e2]
            exact lexRow2_of_code _ _ _ _ (div2_add_le_two _ _) (div2_add_le_two _ _) hpm_le
      · rw [dif_neg hbu_le] at h; simp at h

private lemma runNFA_complete (n : ℕ) (A B : Fin n → Fin 4)
    (hsum : (∑ r : Fin n, ((B r).1 % 2 + (B r).1 / 2)) ≤ 1)
    (hrow : ∀ r : Fin (n - 1), lexRow2 ((A ⟨r.1, by omega⟩).1 % 2 + (B ⟨r.1, by omega⟩).1 % 2)
                                       ((A ⟨r.1, by omega⟩).1 / 2 + (B ⟨r.1, by omega⟩).1 / 2)
                                       ((A ⟨r.1 + 1, by omega⟩).1 % 2 + (B ⟨r.1 + 1, by omega⟩).1 % 2)
                                       ((A ⟨r.1 + 1, by omega⟩).1 / 2 + (B ⟨r.1 + 1, by omega⟩).1 / 2))
    (hcol : lexCol n (fun r => (A r).1 % 2 + (B r).1 % 2) (fun r => (A r).1 / 2 + (B r).1 / 2)) :
    ∃ q : Fin 40, runNFA n A B = some q := by
  induction n with
  | zero => exact ⟨⟨36, by omega⟩, rfl⟩
  | succ n ih =>
    have hsum_succ : (∑ r : Fin (n + 1), ((B r).1 % 2 + (B r).1 / 2)) =
        (∑ r : Fin n, ((B r.castSucc).1 % 2 + (B r.castSucc).1 / 2)) + ((B (Fin.last n)).1 % 2 + (B (Fin.last n)).1 / 2) :=
      Fin.sum_univ_castSucc _
    have hcol_prev : lexCol n (fun r => (A r.castSucc).1 % 2 + (B r.castSucc).1 % 2)
                              (fun r => (A r.castSucc).1 / 2 + (B r.castSucc).1 / 2) := by
      rcases hcol with heq | ⟨r, hr1, hr2⟩
      · left; funext i; exact congrFun heq i.castSucc
      · by_cases hr : r.1 < n
        · right; refine ⟨⟨r.1, hr⟩, fun j hj => hr1 j.castSucc hj, hr2⟩
        · left; funext i; exact hr1 i.castSucc (by have := i.2; simp [Fin.val_castSucc]; omega)
    obtain ⟨q0, hq0⟩ := ih (fun i => A i.castSucc) (fun i => B i.castSucc) (by omega)
      (fun r => hrow ⟨r.1, by omega⟩) hcol_prev
    obtain ⟨hbu0, _, hpm0z, hpm0p, hcc00, _, _⟩ := runNFA_sound n (fun i => A i.castSucc) (fun i => B i.castSucc) q0 hq0
    unfold runNFA; rw [hq0]; unfold nfaStep; dsimp only
    have hbu_ok : (q0.1 / 2) % 2 + (B (Fin.last n)).1 % 2 + (B (Fin.last n)).1 / 2 ≤ 1 := by omega
    have hpm_ok : (q0.1 / 4 == 9 || decide (q0.1 / 4 ≤ 3 * ((A (Fin.last n)).1 % 2 + (B (Fin.last n)).1 % 2) + ((A (Fin.last n)).1 / 2 + (B (Fin.last n)).1 / 2))) = true := by
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
      cases n with
      | zero => left; exact hpm0z rfl
      | succ m =>
        right; rw [hpm0p (by omega)]
        have hr := hrow ⟨m, by omega⟩
        unfold lexRow2 at hr
        have ha1 := (A (⟨m, by omega⟩ : Fin (m + 1)).castSucc).2
        have hb1 := (B (⟨m, by omega⟩ : Fin (m + 1)).castSucc).2
        have ha2 := (A (Fin.last (m + 1))).2
        have hb2 := (B (Fin.last (m + 1))).2
        have em : (⟨m + 1 - 1, by omega⟩ : Fin (m + 1)) = ⟨m, by omega⟩ := Fin.ext (by dsimp)
        have e1 : (⟨m, by omega⟩ : Fin (m + 2)) = (⟨m, by omega⟩ : Fin (m + 1)).castSucc := rfl
        have e2 : (⟨m + 1, by omega⟩ : Fin (m + 2)) = Fin.last (m + 1) := rfl
        rw [em]; rw [e1, e2] at hr; omega
    have hcc_ok : (q0.1 % 2 == 1 || decide ((A (Fin.last n)).1 % 2 + (B (Fin.last n)).1 % 2 ≤ (A (Fin.last n)).1 / 2 + (B (Fin.last n)).1 / 2)) = true := by
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
      by_cases h01 : q0.1 % 2 = 1
      · left; exact h01
      · right
        have h00 : q0.1 % 2 = 0 := by omega
        rcases hcol with heq | ⟨r, _, hr2⟩
        · have hlast := congrFun heq (Fin.last n); omega
        · change (A r).1 % 2 + (B r).1 % 2 < (A r).1 / 2 + (B r).1 / 2 at hr2
          by_cases hr : r.1 < n
          · have heqr := hcc00 h00 ⟨r.1, hr⟩
            have hreq : (⟨r.1, hr⟩ : Fin n).castSucc = r := Fin.ext rfl
            rw [hreq] at heqr; omega
          · have hreq : r = Fin.last n := Fin.ext (by simp [Fin.last]; omega)
            rw [hreq] at hr2; omega
    rw [dif_pos hbu_ok, if_pos (by simp [hpm_ok, hcc_ok])]
    exact ⟨_, rfl⟩

private lemma isValid_iff_runDFA (n : ℕ) (A : Fin n → Fin 2 → Fin 2) :
    isValid n A ↔ (runDFA n (fun r => enc2 (A r))).1 ≠ 8 := by
  rw [← dfaMask_empty_iff]
  simp only [runDFA_iff_runNFA]
  constructor
  · rintro ⟨B, hBsum, hBrow, hBcol⟩
    have hsum' : (∑ r : Fin n, ((enc2 (B r)).1 % 2 + (enc2 (B r)).1 / 2)) ≤ 1 := by
      have heq : ∀ r : Fin n, (enc2 (B r)).1 % 2 + (enc2 (B r)).1 / 2 = ∑ c : Fin 2, (B r c).1 := by
        intro r; rw [Fin.sum_univ_two]; unfold enc2; dsimp; have := (B r 0).2; have := (B r 1).2; omega
      simp_rw [heq]; exact hBsum
    have hm0 : ∀ r, (enc2 (A r)).1 % 2 + (enc2 (B r)).1 % 2 = (A r 0).1 + (B r 0).1 := by
      intro r; unfold enc2; dsimp; have := (A r 0).2; have := (A r 1).2; have := (B r 0).2; have := (B r 1).2; omega
    have hm1 : ∀ r, (enc2 (A r)).1 / 2 + (enc2 (B r)).1 / 2 = (A r 1).1 + (B r 1).1 := by
      intro r; unfold enc2; dsimp; have := (A r 0).2; have := (A r 1).2; have := (B r 0).2; have := (B r 1).2; omega
    have hrow' : ∀ r : Fin (n - 1), lexRow2 ((enc2 (A ⟨r.1, by omega⟩)).1 % 2 + (enc2 (B ⟨r.1, by omega⟩)).1 % 2)
                                            ((enc2 (A ⟨r.1, by omega⟩)).1 / 2 + (enc2 (B ⟨r.1, by omega⟩)).1 / 2)
                                            ((enc2 (A ⟨r.1 + 1, by omega⟩)).1 % 2 + (enc2 (B ⟨r.1 + 1, by omega⟩)).1 % 2)
                                            ((enc2 (A ⟨r.1 + 1, by omega⟩)).1 / 2 + (enc2 (B ⟨r.1 + 1, by omega⟩)).1 / 2) := by
      intro r; rw [hm0, hm1, hm0, hm1]; exact hBrow r
    have hcol' : lexCol n (fun r => (enc2 (A r)).1 % 2 + (enc2 (B r)).1 % 2)
                          (fun r => (enc2 (A r)).1 / 2 + (enc2 (B r)).1 / 2) := by
      have f0 : (fun r => (enc2 (A r)).1 % 2 + (enc2 (B r)).1 % 2) = fun r => (A r 0).1 + (B r 0).1 := funext hm0
      have f1 : (fun r => (enc2 (A r)).1 / 2 + (enc2 (B r)).1 / 2) = fun r => (A r 1).1 + (B r 1).1 := funext hm1
      rw [f0, f1]; exact hBcol
    obtain ⟨q, hq⟩ := runNFA_complete n _ (fun r => enc2 (B r)) hsum' hrow' hcol'
    exact ⟨q, fun r => enc2 (B r), hq⟩
  · rintro ⟨q, B, hrun⟩
    obtain ⟨_, hsum', _, _, hcc0, hcc1, hrow'⟩ := runNFA_sound n _ _ q hrun
    refine ⟨fun r => dec2 (B r), ?_, ?_, ?_⟩
    · have heq : ∀ r : Fin n, (∑ c : Fin 2, (dec2 (B r) c).1) = (B r).1 % 2 + (B r).1 / 2 := by
        intro r; rw [Fin.sum_univ_two]; unfold dec2; dsimp
      simp_rw [heq]; exact hsum'
    · intro r; dsimp only
      have hm0 : ∀ k : Fin n, (A k 0).1 + (dec2 (B k) 0).1 = (enc2 (A k)).1 % 2 + (B k).1 % 2 := by
        intro k; unfold enc2 dec2; dsimp; have := (A k 0).2; have := (A k 1).2; omega
      have hm1 : ∀ k : Fin n, (A k 1).1 + (dec2 (B k) 1).1 = (enc2 (A k)).1 / 2 + (B k).1 / 2 := by
        intro k; unfold enc2 dec2; dsimp; have := (A k 0).2; have := (A k 1).2; omega
      rw [hm0, hm1, hm0, hm1]; exact hrow' r
    · have hm0 : (fun k : Fin n => (A k 0).1 + (dec2 (B k) 0).1) = fun k => (enc2 (A k)).1 % 2 + (B k).1 % 2 := by
        funext k; unfold enc2 dec2; dsimp; have := (A k 0).2; have := (A k 1).2; omega
      have hm1 : (fun k : Fin n => (A k 1).1 + (dec2 (B k) 1).1) = fun k => (enc2 (A k)).1 / 2 + (B k).1 / 2 := by
        funext k; unfold enc2 dec2; dsimp; have := (A k 0).2; have := (A k 1).2; omega
      rw [hm0, hm1]
      by_cases h0 : q.1 % 2 = 0
      · left; funext r; exact hcc0 h0 r
      · right; exact hcc1 (by omega)

private def dp : ℕ → Fin 20 → ℕ
  | 0, s => if s.1 = 0 then 1 else 0
  | n + 1, s' => ∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then dp n s else 0

private lemma dp_succ_eq (n : ℕ) (s' : Fin 20) :
    dp (n + 1) s' = ∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then dp n s else 0 := rfl

private def tbl_0 (s : Fin 20) : ℕ :=
  (if s.1 < 10 then (if s.1 < 5 then (if s.1 < 2 then (if s.1 < 1 then 1 else 0) else (if s.1 < 3 then 0 else (if s.1 < 4 then 0 else 0))) else (if s.1 < 7 then (if s.1 < 6 then 0 else 0) else (if s.1 < 8 then 0 else (if s.1 < 9 then 0 else 0)))) else (if s.1 < 15 then (if s.1 < 12 then (if s.1 < 11 then 0 else 0) else (if s.1 < 13 then 0 else (if s.1 < 14 then 0 else 0))) else (if s.1 < 17 then (if s.1 < 16 then 0 else 0) else (if s.1 < 18 then 0 else (if s.1 < 19 then 0 else 0)))))
private def tbl_1 (s : Fin 20) : ℕ :=
  (if s.1 < 10 then (if s.1 < 5 then (if s.1 < 2 then (if s.1 < 1 then 0 else 1) else (if s.1 < 3 then 1 else (if s.1 < 4 then 1 else 1))) else (if s.1 < 7 then (if s.1 < 6 then 0 else 0) else (if s.1 < 8 then 0 else (if s.1 < 9 then 0 else 0)))) else (if s.1 < 15 then (if s.1 < 12 then (if s.1 < 11 then 0 else 0) else (if s.1 < 13 then 0 else (if s.1 < 14 then 0 else 0))) else (if s.1 < 17 then (if s.1 < 16 then 0 else 0) else (if s.1 < 18 then 0 else (if s.1 < 19 then 0 else 0)))))
private def tbl_2 (s : Fin 20) : ℕ :=
  (if s.1 < 10 then (if s.1 < 5 then (if s.1 < 2 then (if s.1 < 1 then 0 else 1) else (if s.1 < 3 then 3 else (if s.1 < 4 then 0 else 1))) else (if s.1 < 7 then (if s.1 < 6 then 1 else 1) else (if s.1 < 8 then 1 else (if s.1 < 9 then 4 else 1)))) else (if s.1 < 15 then (if s.1 < 12 then (if s.1 < 11 then 1 else 1) else (if s.1 < 13 then 1 else (if s.1 < 14 then 0 else 0))) else (if s.1 < 17 then (if s.1 < 16 then 0 else 0) else (if s.1 < 18 then 0 else (if s.1 < 19 then 0 else 0)))))
private def tbl_3 (s : Fin 20) : ℕ :=
  (if s.1 < 10 then (if s.1 < 5 then (if s.1 < 2 then (if s.1 < 1 then 0 else 1) else (if s.1 < 3 then 7 else (if s.1 < 4 then 0 else 1))) else (if s.1 < 7 then (if s.1 < 6 then 1 else 1) else (if s.1 < 8 then 2 else (if s.1 < 9 then 31 else 2)))) else (if s.1 < 15 then (if s.1 < 12 then (if s.1 < 11 then 3 else 1) else (if s.1 < 13 then 2 else (if s.1 < 14 then 3 else 1))) else (if s.1 < 17 then (if s.1 < 16 then 1 else 1) else (if s.1 < 18 then 3 else (if s.1 < 19 then 2 else 1)))))
private def tbl_4 (s : Fin 20) : ℕ :=
  (if s.1 < 10 then (if s.1 < 5 then (if s.1 < 2 then (if s.1 < 1 then 0 else 1) else (if s.1 < 3 then 13 else (if s.1 < 4 then 0 else 1))) else (if s.1 < 7 then (if s.1 < 6 then 1 else 1) else (if s.1 < 8 then 3 else (if s.1 < 9 then 178 else 3)))) else (if s.1 < 15 then (if s.1 < 12 then (if s.1 < 11 then 6 else 1) else (if s.1 < 13 then 3 else (if s.1 < 14 then 10 else 2))) else (if s.1 < 17 then (if s.1 < 16 then 2 else 3) else (if s.1 < 18 then 17 else (if s.1 < 19 then 7 else 4)))))
private def tbl_5 (s : Fin 20) : ℕ :=
  (if s.1 < 10 then (if s.1 < 5 then (if s.1 < 2 then (if s.1 < 1 then 0 else 1) else (if s.1 < 3 then 21 else (if s.1 < 4 then 0 else 1))) else (if s.1 < 7 then (if s.1 < 6 then 1 else 1) else (if s.1 < 8 then 4 else (if s.1 < 9 then 862 else 4)))) else (if s.1 < 15 then (if s.1 < 12 then (if s.1 < 11 then 10 else 1) else (if s.1 < 13 then 4 else (if s.1 < 14 then 23 else 3))) else (if s.1 < 17 then (if s.1 < 16 then 3 else 6) else (if s.1 < 18 then 53 else (if s.1 < 19 then 16 else 10)))))
private def tbl_6 (s : Fin 20) : ℕ :=
  (if s.1 < 10 then (if s.1 < 5 then (if s.1 < 2 then (if s.1 < 1 then 0 else 1) else (if s.1 < 3 then 31 else (if s.1 < 4 then 0 else 1))) else (if s.1 < 7 then (if s.1 < 6 then 1 else 1) else (if s.1 < 8 then 5 else (if s.1 < 9 then 3792 else 5)))) else (if s.1 < 15 then (if s.1 < 12 then (if s.1 < 11 then 15 else 1) else (if s.1 < 13 then 5 else (if s.1 < 14 then 44 else 4))) else (if s.1 < 17 then (if s.1 < 16 then 4 else 10) else (if s.1 < 18 then 126 else (if s.1 < 19 then 30 else 20)))))
private def tbl_7 (s : Fin 20) : ℕ :=
  (if s.1 < 10 then (if s.1 < 5 then (if s.1 < 2 then (if s.1 < 1 then 0 else 1) else (if s.1 < 3 then 43 else (if s.1 < 4 then 0 else 1))) else (if s.1 < 7 then (if s.1 < 6 then 1 else 1) else (if s.1 < 8 then 6 else (if s.1 < 9 then 15857 else 6)))) else (if s.1 < 15 then (if s.1 < 12 then (if s.1 < 11 then 21 else 1) else (if s.1 < 13 then 6 else (if s.1 < 14 then 75 else 5))) else (if s.1 < 17 then (if s.1 < 16 then 5 else 15) else (if s.1 < 18 then 255 else (if s.1 < 19 then 50 else 35)))))

private lemma dp_eq_tbl_0 (s : Fin 20) : dp 0 s = tbl_0 s := by revert s; decide
private lemma dp_step_ok_1 : ∀ s' : Fin 20,
    (∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_0 s else 0) = tbl_1 s' := by decide

private lemma dp_eq_tbl_1 (s' : Fin 20) : dp 1 s' = tbl_1 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then dp 0 s else 0) =
      ∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_0 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro a _
    rw [dp_eq_tbl_0]
  rw [h1]; exact dp_step_ok_1 s' 
private lemma dp_step_ok_2 : ∀ s' : Fin 20,
    (∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_1 s else 0) = tbl_2 s' := by decide

private lemma dp_eq_tbl_2 (s' : Fin 20) : dp 2 s' = tbl_2 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then dp 1 s else 0) =
      ∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_1 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro a _
    rw [dp_eq_tbl_1]
  rw [h1]; exact dp_step_ok_2 s' 
private lemma dp_step_ok_3 : ∀ s' : Fin 20,
    (∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_2 s else 0) = tbl_3 s' := by decide

private lemma dp_eq_tbl_3 (s' : Fin 20) : dp 3 s' = tbl_3 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then dp 2 s else 0) =
      ∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_2 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro a _
    rw [dp_eq_tbl_2]
  rw [h1]; exact dp_step_ok_3 s' 
private lemma dp_step_ok_4 : ∀ s' : Fin 20,
    (∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_3 s else 0) = tbl_4 s' := by decide

private lemma dp_eq_tbl_4 (s' : Fin 20) : dp 4 s' = tbl_4 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then dp 3 s else 0) =
      ∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_3 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro a _
    rw [dp_eq_tbl_3]
  rw [h1]; exact dp_step_ok_4 s' 
private lemma dp_step_ok_5 : ∀ s' : Fin 20,
    (∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_4 s else 0) = tbl_5 s' := by decide

private lemma dp_eq_tbl_5 (s' : Fin 20) : dp 5 s' = tbl_5 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then dp 4 s else 0) =
      ∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_4 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro a _
    rw [dp_eq_tbl_4]
  rw [h1]; exact dp_step_ok_5 s' 
private lemma dp_step_ok_6 : ∀ s' : Fin 20,
    (∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_5 s else 0) = tbl_6 s' := by decide

private lemma dp_eq_tbl_6 (s' : Fin 20) : dp 6 s' = tbl_6 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then dp 5 s else 0) =
      ∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_5 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro a _
    rw [dp_eq_tbl_5]
  rw [h1]; exact dp_step_ok_6 s' 
private lemma dp_step_ok_7 : ∀ s' : Fin 20,
    (∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_6 s else 0) = tbl_7 s' := by decide

private lemma dp_eq_tbl_7 (s' : Fin 20) : dp 7 s' = tbl_7 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then dp 6 s else 0) =
      ∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_6 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro a _
    rw [dp_eq_tbl_6]
  rw [h1]; exact dp_step_ok_7 s' 

private lemma dp_rec_tbl_ok : ∀ s : Fin 20, s.1 ≠ 8 → tbl_7 s + 10 * tbl_5 s + 5 * tbl_3 s = 5 * tbl_6 s + 10 * tbl_4 s + tbl_2 s := by decide

private lemma dp_rec_base : ∀ s : Fin 20, s.1 ≠ 8 → dp 7 s + 10 * dp 5 s + 5 * dp 3 s = 5 * dp 6 s + 10 * dp 4 s + dp 2 s := by
  intro s hs; rw [dp_eq_tbl_2, dp_eq_tbl_3, dp_eq_tbl_4, dp_eq_tbl_5, dp_eq_tbl_6, dp_eq_tbl_7]; exact dp_rec_tbl_ok s hs

private lemma sum_lin (f0 f1 f2 f3 f4 f5 : Fin 20 → ℕ) (s' : Fin 20) (hs' : s'.1 ≠ 8)
    (h : ∀ s : Fin 20, s.1 ≠ 8 → f5 s + 10 * f3 s + 5 * f1 s = 5 * f4 s + 10 * f2 s + f0 s) :
    (∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then f5 s else 0) + 10 * (∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then f3 s else 0) + 5 * (∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then f1 s else 0) = 5 * (∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then f4 s else 0) + 10 * (∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then f2 s else 0) + (∑ s : Fin 20, ∑ a : Fin 4, if dfaTrans s a = s' then f0 s else 0) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro a _
  by_cases htr : dfaTrans s a = s'
  · simp only [htr, ↓reduceIte]
    have hs : s.1 ≠ 8 := by
      intro heq
      have h1 : s = ⟨8, by omega⟩ := Fin.ext heq
      have h2 : dfaTrans s a = ⟨8, by omega⟩ := h1 ▸ dfaTrans_empty a
      rw [htr] at h2; exact hs' (congrArg Fin.val h2)
    exact h s hs
  · simp [htr]

private lemma dp_rec (m : ℕ) : ∀ s : Fin 20, s.1 ≠ 8 → dp (m + 7) s + 10 * dp (m + 5) s + 5 * dp (m + 3) s = 5 * dp (m + 6) s + 10 * dp (m + 4) s + dp (m + 2) s := by
  induction m with
  | zero => exact dp_rec_base
  | succ m ih =>
    intro s' hs'; rw [dp_succ_eq (m + 2), dp_succ_eq (m + 3), dp_succ_eq (m + 4), dp_succ_eq (m + 5), dp_succ_eq (m + 6), dp_succ_eq (m + 7)]
    exact sum_lin (dp (m + 2)) (dp (m + 3)) (dp (m + 4)) (dp (m + 5)) (dp (m + 6)) (dp (m + 7)) s' hs' ih

private lemma card_runDFA (n : ℕ) : ∀ s : Fin 20, Fintype.card {A : Fin n → Fin 4 // runDFA n A = s} = dp n s := by
  induction n with
  | zero =>
    intro s; unfold dp
    by_cases hs : s.1 = 0
    · rw [if_pos hs]
      refine Fintype.card_eq_one_iff.mpr ⟨⟨Fin.elim0, Fin.ext (by unfold runDFA; dsimp; omega)⟩, ?_⟩
      rintro ⟨A, _⟩; apply Subtype.ext; funext i; exact i.elim0
    · rw [if_neg hs, Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨_, h⟩ => hs (by unfold runDFA at h; exact (congrArg Fin.val h).symm)⟩
  | succ n ih =>
    intro s'; rw [dp_succ_eq]
    let φ : (Σ s : Fin 20, Σ a : Fin 4, {A : Fin n → Fin 4 // runDFA n A = s ∧ dfaTrans s a = s'}) →
        {A : Fin (n + 1) → Fin 4 // runDFA (n + 1) A = s'} :=
      fun ⟨s, a, ⟨A, hA, htr⟩⟩ =>
        ⟨Fin.snoc A a, by
          unfold runDFA
          have hc : (fun i : Fin n => (Fin.snoc A a : Fin (n + 1) → Fin 4) i.castSucc) = A := by
            funext i; exact Fin.snoc_castSucc _ _ i
          rw [hc, hA, Fin.snoc_last]; exact htr⟩
    have hbij : Function.Bijective φ := by
      constructor
      · rintro ⟨sa, aa, ⟨Aa, hAa, _⟩⟩ ⟨sb, ab, ⟨Ab, hAb, _⟩⟩ heq
        have hfun : (Fin.snoc Aa aa : Fin (n + 1) → Fin 4) = Fin.snoc Ab ab := congrArg Subtype.val heq
        have hAeq : Aa = Ab := by funext i; simpa using congrFun hfun i.castSucc
        have haeq : aa = ab := by simpa using congrFun hfun (Fin.last n)
        subst hAeq; subst haeq
        have hseq : sa = sb := hAa.symm.trans hAb
        subst hseq; rfl
      · rintro ⟨A, hA⟩
        let A0 : Fin n → Fin 4 := fun i => A i.castSucc
        let s := runDFA n A0
        let a := A (Fin.last n)
        refine ⟨⟨s, a, ⟨A0, rfl, hA⟩⟩, ?_⟩
        apply Subtype.ext; funext i; refine Fin.lastCases ?_ ?_ i
        · dsimp [φ, a]; rw [Fin.snoc_last]
        · intro j; dsimp [φ, A0]; rw [Fin.snoc_castSucc]
    rw [Fintype.card_congr (Equiv.ofBijective φ hbij).symm, Fintype.card_sigma]
    apply Finset.sum_congr rfl; intro s _
    rw [Fintype.card_sigma]
    apply Finset.sum_congr rfl; intro a _
    by_cases htr : dfaTrans s a = s'
    · rw [if_pos htr, ← ih s]
      refine Fintype.card_congr ⟨fun ⟨A, h1, _⟩ => ⟨A, h1⟩, fun ⟨A, h1⟩ => ⟨A, h1, htr⟩, fun ⟨_, _, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩
    · rw [if_neg htr, Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨_, _, h⟩ => htr h⟩

private lemma a_eq_sum_dp (n : ℕ) (hn : 1 ≤ n) :
    a n = ∑ s : Fin 20, if s.1 ≠ 8 then dp n s else 0 := by
  unfold a; rw [if_neg (by omega)]
  let φ : (Σ s : Fin 20, {A : Fin n → Fin 4 // runDFA n A = s ∧ s.1 ≠ 8}) →
      {A : Fin n → Fin 2 → Fin 2 // isValid n A} :=
    fun ⟨s, ⟨A, hA, hs⟩⟩ =>
      ⟨fun r => dec2 (A r), by
        rw [isValid_iff_runDFA]
        have h1 : (fun r => enc2 (dec2 (A r))) = A := funext fun r => enc2_dec2 (A r)
        rw [h1, hA]; exact hs⟩
  have hbij : Function.Bijective φ := by
    constructor
    · rintro ⟨sa, ⟨Aa, hAa, _⟩⟩ ⟨sb, ⟨Ab, hAb, _⟩⟩ heq
      have hfun := congrArg Subtype.val heq
      have hAeq : Aa = Ab := by
        funext r
        have := congrArg enc2 (congrFun hfun r)
        simpa [φ, enc2_dec2] using this
      subst hAeq
      have hseq : sa = sb := hAa.symm.trans hAb
      subst hseq; rfl
    · rintro ⟨A, hA⟩
      let A' : Fin n → Fin 4 := fun r => enc2 (A r)
      have hs : (runDFA n A').1 ≠ 8 := (isValid_iff_runDFA n A).mp hA
      refine ⟨⟨runDFA n A', ⟨A', rfl, hs⟩⟩, ?_⟩
      apply Subtype.ext; funext r; exact dec2_enc2 (A r)
  rw [Fintype.card_congr (Equiv.ofBijective φ hbij).symm, Fintype.card_sigma]
  apply Finset.sum_congr rfl; intro s _
  by_cases hs : s.1 ≠ 8
  · rw [if_pos hs, ← card_runDFA n s]
    refine Fintype.card_congr ⟨fun ⟨A, h1, _⟩ => ⟨A, h1⟩, fun ⟨A, h1⟩ => ⟨A, h1, hs⟩, fun ⟨_, _, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩
  · rw [if_neg hs, Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨_, _, h⟩ => hs h⟩

private lemma a_rec_m (m : ℕ) : a (m + 7) + 10 * a (m + 5) + 5 * a (m + 3) = 5 * a (m + 6) + 10 * a (m + 4) + a (m + 2) := by
  rw [a_eq_sum_dp (m + 2) (by omega), a_eq_sum_dp (m + 3) (by omega), a_eq_sum_dp (m + 4) (by omega), a_eq_sum_dp (m + 5) (by omega), a_eq_sum_dp (m + 6) (by omega), a_eq_sum_dp (m + 7) (by omega)]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s _
  by_cases hs : s.1 ≠ 8
  · simp only [if_pos hs]; exact dp_rec m s hs
  · simp only [if_neg hs, mul_zero, add_zero]

private lemma a_zero : a 0 = 0 := by unfold a; simp
private lemma a_sum_ok_1 : (∑ s : Fin 20, if s.1 ≠ 8 then tbl_1 s else 0) = 4 := by decide
private lemma a_val_1 : a 1 = 4 := by
  rw [a_eq_sum_dp 1 (by omega)]
  have h : (∑ s : Fin 20, if s.1 ≠ 8 then dp 1 s else 0) =
      ∑ s : Fin 20, if s.1 ≠ 8 then tbl_1 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_1]
  rw [h]; exact a_sum_ok_1
private lemma a_sum_ok_2 : (∑ s : Fin 20, if s.1 ≠ 8 then tbl_2 s else 0) = 12 := by decide
private lemma a_val_2 : a 2 = 12 := by
  rw [a_eq_sum_dp 2 (by omega)]
  have h : (∑ s : Fin 20, if s.1 ≠ 8 then dp 2 s else 0) =
      ∑ s : Fin 20, if s.1 ≠ 8 then tbl_2 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_2]
  rw [h]; exact a_sum_ok_2
private lemma a_sum_ok_3 : (∑ s : Fin 20, if s.1 ≠ 8 then tbl_3 s else 0) = 33 := by decide
private lemma a_val_3 : a 3 = 33 := by
  rw [a_eq_sum_dp 3 (by omega)]
  have h : (∑ s : Fin 20, if s.1 ≠ 8 then dp 3 s else 0) =
      ∑ s : Fin 20, if s.1 ≠ 8 then tbl_3 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_3]
  rw [h]; exact a_sum_ok_3
private lemma a_sum_ok_4 : (∑ s : Fin 20, if s.1 ≠ 8 then tbl_4 s else 0) = 78 := by decide
private lemma a_val_4 : a 4 = 78 := by
  rw [a_eq_sum_dp 4 (by omega)]
  have h : (∑ s : Fin 20, if s.1 ≠ 8 then dp 4 s else 0) =
      ∑ s : Fin 20, if s.1 ≠ 8 then tbl_4 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_4]
  rw [h]; exact a_sum_ok_4
private lemma a_sum_ok_5 : (∑ s : Fin 20, if s.1 ≠ 8 then tbl_5 s else 0) = 162 := by decide
private lemma a_val_5 : a 5 = 162 := by
  rw [a_eq_sum_dp 5 (by omega)]
  have h : (∑ s : Fin 20, if s.1 ≠ 8 then dp 5 s else 0) =
      ∑ s : Fin 20, if s.1 ≠ 8 then tbl_5 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_5]
  rw [h]; exact a_sum_ok_5
private lemma a_sum_ok_6 : (∑ s : Fin 20, if s.1 ≠ 8 then tbl_6 s else 0) = 304 := by decide
private lemma a_val_6 : a 6 = 304 := by
  rw [a_eq_sum_dp 6 (by omega)]
  have h : (∑ s : Fin 20, if s.1 ≠ 8 then dp 6 s else 0) =
      ∑ s : Fin 20, if s.1 ≠ 8 then tbl_6 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_6]
  rw [h]; exact a_sum_ok_6
private lemma a_sum_ok_7 : (∑ s : Fin 20, if s.1 ≠ 8 then tbl_7 s else 0) = 527 := by decide
private lemma a_val_7 : a 7 = 527 := by
  rw [a_eq_sum_dp 7 (by omega)]
  have h : (∑ s : Fin 20, if s.1 ≠ 8 then dp 7 s else 0) =
      ∑ s : Fin 20, if s.1 ≠ 8 then tbl_7 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_7]
  rw [h]; exact a_sum_ok_7

private lemma coeff_X_pow_mul_eq (f : PowerSeries ℚ) (j n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X ^ j * f) = if j ≤ n then PowerSeries.coeff (n - j) f else 0 := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_assoc]
    cases n with
    | zero => simp
    | succ m =>
      rw [PowerSeries.coeff_succ_X_mul, ih m]
      split_ifs with h1 h2
      · simp [Nat.succ_sub_succ]
      · omega
      · omega
      · rfl

private lemma coeff_mul_X_pow_eq (f : PowerSeries ℚ) (j n : ℕ) :
    PowerSeries.coeff n (f * PowerSeries.X ^ j) = if j ≤ n then PowerSeries.coeff (n - j) f else 0 := by
  rw [mul_comm]; exact coeff_X_pow_mul_eq f j n

theorem solution : type_of% @OMA.S_oeis_a225894.main := by
  have hrec : ∀ n : ℕ, 5 < n → (a n : ℤ) = 5 * (a (n - 1) : ℤ) - 10 * (a (n - 2) : ℤ) + 10 * (a (n - 3) : ℤ) - 5 * (a (n - 4) : ℤ) + (a (n - 5) : ℤ) := by
    intro n hn
    by_cases hn6 : n = 6
    · subst hn6; simp [a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6]
    · have h := a_rec_m (n - 7)
      simp only [show n - 7 + 7 = n by omega, show n - 7 + 6 = n - 1 by omega, show n - 7 + 5 = n - 2 by omega, show n - 7 + 4 = n - 3 by omega, show n - 7 + 3 = n - 4 by omega, show n - 7 + 2 = n - 5 by omega] at h
      omega
  refine ⟨?_, hrec⟩
  ext n
  have hexp : (1 - (PowerSeries.X : PowerSeries ℚ)) ^ 5 = 1 - PowerSeries.C 5 * PowerSeries.X ^ 1 + PowerSeries.C 10 * PowerSeries.X ^ 2 - PowerSeries.C 10 * PowerSeries.X ^ 3 + PowerSeries.C 5 * PowerSeries.X ^ 4 - PowerSeries.X ^ 5 := by
    simp only [map_ofNat]; ring
  rw [hexp]
  have hR : (PowerSeries.X : PowerSeries ℚ) * (4 - 8 * PowerSeries.X + 13 * PowerSeries.X ^ 2 - 7 * PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4) = PowerSeries.C 4 * PowerSeries.X ^ 1 - PowerSeries.C 8 * PowerSeries.X ^ 2 + PowerSeries.C 13 * PowerSeries.X ^ 3 - PowerSeries.C 7 * PowerSeries.X ^ 4 + PowerSeries.C 2 * PowerSeries.X ^ 5 := by
    simp only [map_ofNat]; ring
  rw [hR]
  have hc : ∀ (c : ℚ) (j : ℕ), PowerSeries.coeff n (PowerSeries.mk (fun m => (a m : ℚ)) * (PowerSeries.C c * PowerSeries.X ^ j)) =
      c * if j ≤ n then (a (n - j) : ℚ) else 0 := by
    intro c j
    rw [mul_comm (PowerSeries.C c), ← mul_assoc, mul_comm _ (PowerSeries.C c),
        PowerSeries.coeff_C_mul, coeff_mul_X_pow_eq, PowerSeries.coeff_mk]
  have hX : ∀ (j : ℕ), PowerSeries.coeff n (PowerSeries.mk (fun m => (a m : ℚ)) * PowerSeries.X ^ j) =
      if j ≤ n then (a (n - j) : ℚ) else 0 := by
    intro j; rw [coeff_mul_X_pow_eq, PowerSeries.coeff_mk]
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, PowerSeries.coeff_mk, hc, hX,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  rcases n with _ | _ | _ | _ | _ | _ | m
  · simp [a_zero]
  · simp [a_zero, a_val_1]
  · simp [a_zero, a_val_1, a_val_2]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5]; norm_num
  · simp only [Nat.add_assoc, Nat.reduceAdd, show 1 ≤ m + 6 by omega, show 2 ≤ m + 6 by omega, show 3 ≤ m + 6 by omega, show 4 ≤ m + 6 by omega, show 5 ≤ m + 6 by omega, ↓reduceIte,
      show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega, show ¬(m + 6 = 1) by omega, show ¬(m + 6 = 2) by omega, show ¬(m + 6 = 3) by omega, show ¬(m + 6 = 4) by omega, show ¬(m + 6 = 5) by omega]
    have hr := hrec (m + 6) (by omega)
    simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega] at hr
    have hrq : (a (m + 6) : ℚ) = 5 * (a (m + 5) : ℚ) - 10 * (a (m + 4) : ℚ) + 10 * (a (m + 3) : ℚ) - 5 * (a (m + 2) : ℚ) + (a (m + 1) : ℚ) := by exact_mod_cast hr
    linarith

end OMA.P_oeis_a225894

theorem OMA.solution : type_of% @OMA.S_oeis_a225894.main :=
  OMA.P_oeis_a225894.solution
