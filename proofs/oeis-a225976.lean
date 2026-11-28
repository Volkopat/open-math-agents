import OMAStatements.S_oeis_a225976

namespace OMA.P_oeis_a225976

open OMA.S_oeis_a225976

private def nfaStep (q : Fin 60) (a b : Fin 4) : Option (Fin 60) :=
  let cc := q.1 % 2
  let bu := (q.1 / 2) % 3
  let pm := q.1 / 6
  let a0 := a.1 % 2
  let a1 := a.1 / 2
  let b0 := b.1 % 2
  let b1 := b.1 / 2
  let nbu := bu + b0 + b1
  if hbu : nbu ≤ 2 then
    let m0 := a0 + b0
    let m1 := a1 + b1
    let mcode := 3 * m0 + m1
    if (pm == 9 || pm ≤ mcode) && (cc == 1 || m0 ≤ m1) then
      let ncc := if cc == 1 || m0 < m1 then 1 else 0
      some ⟨(mcode * 3 + nbu) * 2 + ncc, by
        have := a.2; have := b.2
        have hncc : ncc ≤ 1 := by dsimp [ncc]; split_ifs <;> omega
        omega⟩
    else none
  else none

private def nfaPre (a : Fin 4) (q : Fin 60) : ℕ :=
  match a.1 with
  | 0 => (if q.1 < 30 then (if q.1 < 15 then (if q.1 < 7 then (if q.1 < 3 then (if q.1 < 1 then 18014398509481985 else (if q.1 < 2 then 36028797018963970 else 72057594037927940)) else (if q.1 < 5 then (if q.1 < 4 then 144115188075855880 else 288230376151711760) else (if q.1 < 6 then 576460752303423520 else 0))) else (if q.1 < 11 then (if q.1 < 9 then (if q.1 < 8 then 0 else 0) else (if q.1 < 10 then 54043195528446147 else 0)) else (if q.1 < 13 then (if q.1 < 12 then 216172782113784588 else 0) else (if q.1 < 14 then 0 else 0)))) else (if q.1 < 22 then (if q.1 < 18 then (if q.1 < 16 then 0 else (if q.1 < 17 then 0 else 0)) else (if q.1 < 20 then (if q.1 < 19 then 0 else 0) else (if q.1 < 21 then 0 else 36028797019496578))) else (if q.1 < 26 then (if q.1 < 24 then (if q.1 < 23 then 0 else 144115188077986312) else (if q.1 < 25 then 0 else 0)) else (if q.1 < 28 then (if q.1 < 27 then 0 else 0) else (if q.1 < 29 then 18014398526525505 else 36028797053051010))))) else (if q.1 < 45 then (if q.1 < 37 then (if q.1 < 33 then (if q.1 < 31 then 0 else (if q.1 < 32 then 0 else 0)) else (if q.1 < 35 then (if q.1 < 34 then 0 else 0) else (if q.1 < 36 then 0 else 0))) else (if q.1 < 41 then (if q.1 < 39 then (if q.1 < 38 then 0 else 0) else (if q.1 < 40 then 0 else 0)) else (if q.1 < 43 then (if q.1 < 42 then 0 else 0) else (if q.1 < 44 then 0 else 0)))) else (if q.1 < 52 then (if q.1 < 48 then (if q.1 < 46 then 0 else (if q.1 < 47 then 0 else 0)) else (if q.1 < 50 then (if q.1 < 49 then 0 else 0) else (if q.1 < 51 then 0 else 0))) else (if q.1 < 56 then (if q.1 < 54 then (if q.1 < 53 then 0 else 0) else (if q.1 < 55 then 0 else 0)) else (if q.1 < 58 then (if q.1 < 57 then 0 else 0) else (if q.1 < 59 then 0 else 0))))))
  | 1 => (if q.1 < 30 then (if q.1 < 15 then (if q.1 < 7 then (if q.1 < 3 then (if q.1 < 1 then 0 else (if q.1 < 2 then 0 else 0)) else (if q.1 < 5 then (if q.1 < 4 then 0 else 0) else (if q.1 < 6 then 0 else 0))) else (if q.1 < 11 then (if q.1 < 9 then (if q.1 < 8 then 0 else 0) else (if q.1 < 10 then 0 else 0)) else (if q.1 < 13 then (if q.1 < 12 then 0 else 0) else (if q.1 < 14 then 0 else 0)))) else (if q.1 < 22 then (if q.1 < 18 then (if q.1 < 16 then 0 else (if q.1 < 17 then 0 else 0)) else (if q.1 < 20 then (if q.1 < 19 then 0 else 36028797019496578) else (if q.1 < 21 then 0 else 144115188077986312))) else (if q.1 < 26 then (if q.1 < 24 then (if q.1 < 23 then 0 else 576460752311945248) else (if q.1 < 25 then 0 else 0)) else (if q.1 < 28 then (if q.1 < 27 then 18014398526525505 else 36028797053051010) else (if q.1 < 29 then 72057594106102020 else 144115188212204040))))) else (if q.1 < 45 then (if q.1 < 37 then (if q.1 < 33 then (if q.1 < 31 then 0 else (if q.1 < 32 then 0 else 0)) else (if q.1 < 35 then (if q.1 < 34 then 0 else 0) else (if q.1 < 36 then 0 else 0))) else (if q.1 < 41 then (if q.1 < 39 then (if q.1 < 38 then 0 else 0) else (if q.1 < 40 then 36028936639488130 else 0)) else (if q.1 < 43 then (if q.1 < 42 then 144115746557952520 else 0) else (if q.1 < 44 then 0 else 0)))) else (if q.1 < 52 then (if q.1 < 48 then (if q.1 < 46 then 0 else (if q.1 < 47 then 0 else 36037732732510338)) else (if q.1 < 50 then (if q.1 < 49 then 0 else 0) else (if q.1 < 51 then 0 else 0))) else (if q.1 < 56 then (if q.1 < 54 then (if q.1 < 53 then 0 else 0) else (if q.1 < 55 then 0 else 0)) else (if q.1 < 58 then (if q.1 < 57 then 0 else 0) else (if q.1 < 59 then 0 else 0))))))
  | 2 => (if q.1 < 30 then (if q.1 < 15 then (if q.1 < 7 then (if q.1 < 3 then (if q.1 < 1 then 0 else (if q.1 < 2 then 0 else 0)) else (if q.1 < 5 then (if q.1 < 4 then 0 else 0) else (if q.1 < 6 then 0 else 0))) else (if q.1 < 11 then (if q.1 < 9 then (if q.1 < 8 then 54043195528446147 else 0) else (if q.1 < 10 then 216172782113784588 else 0)) else (if q.1 < 13 then (if q.1 < 12 then 864691128455138352 else 0) else (if q.1 < 14 then 0 else 0)))) else (if q.1 < 22 then (if q.1 < 18 then (if q.1 < 16 then 54043195528458435 else (if q.1 < 17 then 0 else 216172782113833740)) else (if q.1 < 20 then (if q.1 < 19 then 0 else 0) else (if q.1 < 21 then 0 else 0))) else (if q.1 < 26 then (if q.1 < 24 then (if q.1 < 23 then 0 else 0) else (if q.1 < 25 then 0 else 0)) else (if q.1 < 28 then (if q.1 < 27 then 18014398526525505 else 36028797053051010) else (if q.1 < 29 then 72057594106102020 else 144115188212204040))))) else (if q.1 < 45 then (if q.1 < 37 then (if q.1 < 33 then (if q.1 < 31 then 0 else (if q.1 < 32 then 0 else 0)) else (if q.1 < 35 then (if q.1 < 34 then 0 else 0) else (if q.1 < 36 then 54043198800801987 else 0))) else (if q.1 < 41 then (if q.1 < 39 then (if q.1 < 38 then 0 else 0) else (if q.1 < 40 then 0 else 0)) else (if q.1 < 43 then (if q.1 < 42 then 0 else 0) else (if q.1 < 44 then 0 else 0)))) else (if q.1 < 52 then (if q.1 < 48 then (if q.1 < 46 then 0 else (if q.1 < 47 then 0 else 0)) else (if q.1 < 50 then (if q.1 < 49 then 0 else 0) else (if q.1 < 51 then 0 else 0))) else (if q.1 < 56 then (if q.1 < 54 then (if q.1 < 53 then 0 else 0) else (if q.1 < 55 then 0 else 0)) else (if q.1 < 58 then (if q.1 < 57 then 0 else 0) else (if q.1 < 59 then 0 else 0))))))
  | 3 => (if q.1 < 30 then (if q.1 < 15 then (if q.1 < 7 then (if q.1 < 3 then (if q.1 < 1 then 0 else (if q.1 < 2 then 0 else 0)) else (if q.1 < 5 then (if q.1 < 4 then 0 else 0) else (if q.1 < 6 then 0 else 0))) else (if q.1 < 11 then (if q.1 < 9 then (if q.1 < 8 then 0 else 0) else (if q.1 < 10 then 0 else 0)) else (if q.1 < 13 then (if q.1 < 12 then 0 else 0) else (if q.1 < 14 then 0 else 0)))) else (if q.1 < 22 then (if q.1 < 18 then (if q.1 < 16 then 0 else (if q.1 < 17 then 0 else 0)) else (if q.1 < 20 then (if q.1 < 19 then 0 else 0) else (if q.1 < 21 then 0 else 0))) else (if q.1 < 26 then (if q.1 < 24 then (if q.1 < 23 then 0 else 0) else (if q.1 < 25 then 18014398526525505 else 36028797053051010)) else (if q.1 < 28 then (if q.1 < 27 then 72057594106102020 else 144115188212204040) else (if q.1 < 29 then 288230376424408080 else 576460752848816160))))) else (if q.1 < 45 then (if q.1 < 37 then (if q.1 < 33 then (if q.1 < 31 then 0 else (if q.1 < 32 then 0 else 0)) else (if q.1 < 35 then (if q.1 < 34 then 54043198800801987 else 0) else (if q.1 < 36 then 216172795203207948 else 0))) else (if q.1 < 41 then (if q.1 < 39 then (if q.1 < 38 then 0 else 0) else (if q.1 < 40 then 0 else 0)) else (if q.1 < 43 then (if q.1 < 42 then 0 else 0) else (if q.1 < 44 then 0 else 0)))) else (if q.1 < 52 then (if q.1 < 48 then (if q.1 < 46 then 36037732732510338 else (if q.1 < 47 then 0 else 144150930930041352)) else (if q.1 < 50 then (if q.1 < 49 then 0 else 0) else (if q.1 < 51 then 0 else 0))) else (if q.1 < 56 then (if q.1 < 54 then (if q.1 < 53 then 18300341342965825 else 36600682685931650) else (if q.1 < 55 then 0 else 0)) else (if q.1 < 58 then (if q.1 < 57 then 0 else 0) else (if q.1 < 59 then 0 else 0))))))
  | _ => 0

private lemma nfaPre_testBit_0 : ∀ q' q : Fin 60,
    (nfaPre ⟨0, by omega⟩ q').testBit q.1 = decide (∃ b : Fin 4, nfaStep q ⟨0, by omega⟩ b = some q') := by decide
private lemma nfaPre_testBit_1 : ∀ q' q : Fin 60,
    (nfaPre ⟨1, by omega⟩ q').testBit q.1 = decide (∃ b : Fin 4, nfaStep q ⟨1, by omega⟩ b = some q') := by decide
private lemma nfaPre_testBit_2 : ∀ q' q : Fin 60,
    (nfaPre ⟨2, by omega⟩ q').testBit q.1 = decide (∃ b : Fin 4, nfaStep q ⟨2, by omega⟩ b = some q') := by decide
private lemma nfaPre_testBit_3 : ∀ q' q : Fin 60,
    (nfaPre ⟨3, by omega⟩ q').testBit q.1 = decide (∃ b : Fin 4, nfaStep q ⟨3, by omega⟩ b = some q') := by decide

private lemma nfaPre_testBit (a : Fin 4) (q' q : Fin 60) :
    (nfaPre a q').testBit q.1 = decide (∃ b : Fin 4, nfaStep q a b = some q') := by
  fin_cases a
  · exact nfaPre_testBit_0 q' q
  · exact nfaPre_testBit_1 q' q
  · exact nfaPre_testBit_2 q' q
  · exact nfaPre_testBit_3 q' q

private def dfaMask (s : Fin 56) : ℕ :=
  (if s.1 < 28 then (if s.1 < 14 then (if s.1 < 7 then (if s.1 < 3 then (if s.1 < 1 then 18014398509481984 else (if s.1 < 2 then 268435969 else 67108864)) else (if s.1 < 5 then (if s.1 < 4 then 34426880128 else 4503608234082304) else (if s.1 < 6 then 276826625 else 2199629332480))) else (if s.1 < 10 then (if s.1 < 8 then 34963882624 else (if s.1 < 9 then 4644380484829184 else 0)) else (if s.1 < 12 then (if s.1 < 11 then 268435456 else 34426847232) else (if s.1 < 13 then 547357184 else 143487209570304)))) else (if s.1 < 21 then (if s.1 < 17 then (if s.1 < 15 then 35299426432 else (if s.1 < 16 then 9183164299739136 else 2199090364416)) else (if s.1 < 19 then (if s.1 < 18 then 4644380082176000 else 2199637721088) else (if s.1 < 20 then 34963884672 else 4644381021700096))) else (if s.1 < 24 then (if s.1 < 22 then 8388608 else (if s.1 < 23 then 2199830659072 else 805306368)) else (if s.1 < 26 then (if s.1 < 25 then 140772586291200 else 547359232) else (if s.1 < 27 then 143487217958912 else 35299426944))))) else (if s.1 < 42 then (if s.1 < 35 then (if s.1 < 31 then (if s.1 < 29 then 9183164836610048 else (if s.1 < 30 then 2199627235328 else 34963718144)) else (if s.1 < 33 then (if s.1 < 32 then 8390656 else 2199570612224) else (if s.1 < 34 then 537002496 else 140772519182336))) else (if s.1 < 38 then (if s.1 < 36 then 547356672 else (if s.1 < 37 then 143486941134848 else 35030827008)) else (if s.1 < 40 then (if s.1 < 39 then 9183165037936640 else 143486949523456) else (if s.1 < 41 then 35030990976 else 536870912)))) else (if s.1 < 49 then (if s.1 < 45 then (if s.1 < 43 then 143487206948864 else (if s.1 < 44 then 35299262464 else 2199839047680)) else (if s.1 < 47 then (if s.1 < 46 then 35299428992 else 2199562223616) else (if s.1 < 48 then 140772787617792 else 2199828561920))) else (if s.1 < 52 then (if s.1 < 50 then 537004544 else (if s.1 < 51 then 35030991488 else 2048)) else (if s.1 < 54 then (if s.1 < 53 then 2199560126464 else 9183164769501184) else (if s.1 < 55 then 143486938513408 else 35030993536))))))

private def dfaTrans (s : Fin 56) (a : Fin 4) : Fin 56 :=
  match s.1 with
  | 0 => match a.1 with | 0 => ⟨1, by omega⟩ | 1 => ⟨2, by omega⟩ | 2 => ⟨3, by omega⟩ | _ => ⟨4, by omega⟩
  | 1 => match a.1 with | 0 => ⟨5, by omega⟩ | 1 => ⟨6, by omega⟩ | 2 => ⟨7, by omega⟩ | _ => ⟨8, by omega⟩
  | 2 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨10, by omega⟩ | 2 => ⟨10, by omega⟩ | _ => ⟨11, by omega⟩
  | 3 => match a.1 with | 0 => ⟨12, by omega⟩ | 1 => ⟨13, by omega⟩ | 2 => ⟨14, by omega⟩ | _ => ⟨15, by omega⟩
  | 4 => match a.1 with | 0 => ⟨10, by omega⟩ | 1 => ⟨16, by omega⟩ | 2 => ⟨11, by omega⟩ | _ => ⟨17, by omega⟩
  | 5 => match a.1 with | 0 => ⟨5, by omega⟩ | 1 => ⟨18, by omega⟩ | 2 => ⟨19, by omega⟩ | _ => ⟨20, by omega⟩
  | 6 => match a.1 with | 0 => ⟨21, by omega⟩ | 1 => ⟨22, by omega⟩ | 2 => ⟨23, by omega⟩ | _ => ⟨24, by omega⟩
  | 7 => match a.1 with | 0 => ⟨25, by omega⟩ | 1 => ⟨26, by omega⟩ | 2 => ⟨27, by omega⟩ | _ => ⟨28, by omega⟩
  | 8 => match a.1 with | 0 => ⟨10, by omega⟩ | 1 => ⟨29, by omega⟩ | 2 => ⟨30, by omega⟩ | _ => ⟨8, by omega⟩
  | 9 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨9, by omega⟩ | 2 => ⟨9, by omega⟩ | _ => ⟨9, by omega⟩
  | 10 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨9, by omega⟩ | 2 => ⟨9, by omega⟩ | _ => ⟨10, by omega⟩
  | 11 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨10, by omega⟩ | 2 => ⟨10, by omega⟩ | _ => ⟨11, by omega⟩
  | 12 => match a.1 with | 0 => ⟨31, by omega⟩ | 1 => ⟨32, by omega⟩ | 2 => ⟨33, by omega⟩ | _ => ⟨34, by omega⟩
  | 13 => match a.1 with | 0 => ⟨35, by omega⟩ | 1 => ⟨36, by omega⟩ | 2 => ⟨37, by omega⟩ | _ => ⟨38, by omega⟩
  | 14 => match a.1 with | 0 => ⟨12, by omega⟩ | 1 => ⟨39, by omega⟩ | 2 => ⟨40, by omega⟩ | _ => ⟨38, by omega⟩
  | 15 => match a.1 with | 0 => ⟨41, by omega⟩ | 1 => ⟨42, by omega⟩ | 2 => ⟨43, by omega⟩ | _ => ⟨15, by omega⟩
  | 16 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨10, by omega⟩ | 2 => ⟨10, by omega⟩ | _ => ⟨11, by omega⟩
  | 17 => match a.1 with | 0 => ⟨10, by omega⟩ | 1 => ⟨16, by omega⟩ | 2 => ⟨11, by omega⟩ | _ => ⟨17, by omega⟩
  | 18 => match a.1 with | 0 => ⟨21, by omega⟩ | 1 => ⟨44, by omega⟩ | 2 => ⟨23, by omega⟩ | _ => ⟨24, by omega⟩
  | 19 => match a.1 with | 0 => ⟨25, by omega⟩ | 1 => ⟨26, by omega⟩ | 2 => ⟨45, by omega⟩ | _ => ⟨28, by omega⟩
  | 20 => match a.1 with | 0 => ⟨10, by omega⟩ | 1 => ⟨29, by omega⟩ | 2 => ⟨30, by omega⟩ | _ => ⟨20, by omega⟩
  | 21 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨21, by omega⟩ | 2 => ⟨9, by omega⟩ | _ => ⟨41, by omega⟩
  | 22 => match a.1 with | 0 => ⟨21, by omega⟩ | 1 => ⟨46, by omega⟩ | 2 => ⟨41, by omega⟩ | _ => ⟨47, by omega⟩
  | 23 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨9, by omega⟩ | 2 => ⟨9, by omega⟩ | _ => ⟨23, by omega⟩
  | 24 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨48, by omega⟩ | 2 => ⟨23, by omega⟩ | _ => ⟨24, by omega⟩
  | 25 => match a.1 with | 0 => ⟨31, by omega⟩ | 1 => ⟨32, by omega⟩ | 2 => ⟨49, by omega⟩ | _ => ⟨34, by omega⟩
  | 26 => match a.1 with | 0 => ⟨35, by omega⟩ | 1 => ⟨39, by omega⟩ | 2 => ⟨37, by omega⟩ | _ => ⟨38, by omega⟩
  | 27 => match a.1 with | 0 => ⟨25, by omega⟩ | 1 => ⟨39, by omega⟩ | 2 => ⟨50, by omega⟩ | _ => ⟨38, by omega⟩
  | 28 => match a.1 with | 0 => ⟨41, by omega⟩ | 1 => ⟨42, by omega⟩ | 2 => ⟨43, by omega⟩ | _ => ⟨28, by omega⟩
  | 29 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨10, by omega⟩ | 2 => ⟨10, by omega⟩ | _ => ⟨30, by omega⟩
  | 30 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨10, by omega⟩ | 2 => ⟨10, by omega⟩ | _ => ⟨30, by omega⟩
  | 31 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨21, by omega⟩ | 2 => ⟨51, by omega⟩ | _ => ⟨41, by omega⟩
  | 32 => match a.1 with | 0 => ⟨21, by omega⟩ | 1 => ⟨32, by omega⟩ | 2 => ⟨41, by omega⟩ | _ => ⟨34, by omega⟩
  | 33 => match a.1 with | 0 => ⟨31, by omega⟩ | 1 => ⟨32, by omega⟩ | 2 => ⟨33, by omega⟩ | _ => ⟨34, by omega⟩
  | 34 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨52, by omega⟩ | 2 => ⟨41, by omega⟩ | _ => ⟨34, by omega⟩
  | 35 => match a.1 with | 0 => ⟨21, by omega⟩ | 1 => ⟨32, by omega⟩ | 2 => ⟨41, by omega⟩ | _ => ⟨34, by omega⟩
  | 36 => match a.1 with | 0 => ⟨35, by omega⟩ | 1 => ⟨36, by omega⟩ | 2 => ⟨37, by omega⟩ | _ => ⟨53, by omega⟩
  | 37 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨52, by omega⟩ | 2 => ⟨41, by omega⟩ | _ => ⟨34, by omega⟩
  | 38 => match a.1 with | 0 => ⟨41, by omega⟩ | 1 => ⟨54, by omega⟩ | 2 => ⟨37, by omega⟩ | _ => ⟨38, by omega⟩
  | 39 => match a.1 with | 0 => ⟨35, by omega⟩ | 1 => ⟨39, by omega⟩ | 2 => ⟨37, by omega⟩ | _ => ⟨53, by omega⟩
  | 40 => match a.1 with | 0 => ⟨12, by omega⟩ | 1 => ⟨39, by omega⟩ | 2 => ⟨40, by omega⟩ | _ => ⟨53, by omega⟩
  | 41 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨9, by omega⟩ | 2 => ⟨9, by omega⟩ | _ => ⟨41, by omega⟩
  | 42 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨52, by omega⟩ | 2 => ⟨41, by omega⟩ | _ => ⟨47, by omega⟩
  | 43 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨52, by omega⟩ | 2 => ⟨41, by omega⟩ | _ => ⟨47, by omega⟩
  | 44 => match a.1 with | 0 => ⟨21, by omega⟩ | 1 => ⟨32, by omega⟩ | 2 => ⟨41, by omega⟩ | _ => ⟨47, by omega⟩
  | 45 => match a.1 with | 0 => ⟨25, by omega⟩ | 1 => ⟨39, by omega⟩ | 2 => ⟨55, by omega⟩ | _ => ⟨38, by omega⟩
  | 46 => match a.1 with | 0 => ⟨21, by omega⟩ | 1 => ⟨46, by omega⟩ | 2 => ⟨41, by omega⟩ | _ => ⟨34, by omega⟩
  | 47 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨52, by omega⟩ | 2 => ⟨41, by omega⟩ | _ => ⟨47, by omega⟩
  | 48 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨9, by omega⟩ | 2 => ⟨9, by omega⟩ | _ => ⟨23, by omega⟩
  | 49 => match a.1 with | 0 => ⟨31, by omega⟩ | 1 => ⟨32, by omega⟩ | 2 => ⟨49, by omega⟩ | _ => ⟨34, by omega⟩
  | 50 => match a.1 with | 0 => ⟨25, by omega⟩ | 1 => ⟨39, by omega⟩ | 2 => ⟨50, by omega⟩ | _ => ⟨53, by omega⟩
  | 51 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨21, by omega⟩ | 2 => ⟨51, by omega⟩ | _ => ⟨41, by omega⟩
  | 52 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨9, by omega⟩ | 2 => ⟨9, by omega⟩ | _ => ⟨41, by omega⟩
  | 53 => match a.1 with | 0 => ⟨41, by omega⟩ | 1 => ⟨54, by omega⟩ | 2 => ⟨37, by omega⟩ | _ => ⟨53, by omega⟩
  | 54 => match a.1 with | 0 => ⟨9, by omega⟩ | 1 => ⟨52, by omega⟩ | 2 => ⟨41, by omega⟩ | _ => ⟨34, by omega⟩
  | 55 => match a.1 with | 0 => ⟨25, by omega⟩ | 1 => ⟨39, by omega⟩ | 2 => ⟨55, by omega⟩ | _ => ⟨53, by omega⟩
  | _ => ⟨0, by omega⟩

private lemma dfaTrans_empty : ∀ a : Fin 4, dfaTrans ⟨9, by omega⟩ a = ⟨9, by omega⟩ := by decide

private lemma dfaTrans_not_empty (s : Fin 56) (a : Fin 4) (h : dfaTrans s a ≠ ⟨9, by omega⟩) :
    s ≠ ⟨9, by omega⟩ := by
  intro hs; subst hs; exact h (dfaTrans_empty a)

private lemma dfaMask_lt : ∀ s : Fin 56, dfaMask s < 2 ^ 60 := by decide

private lemma dfaMask_ne_zero_iff : ∀ s : Fin 56, dfaMask s ≠ 0 ↔ s.1 ≠ 9 := by decide

private lemma dfaMask_init : ∀ q : Fin 60,
    (dfaMask ⟨0, by omega⟩).testBit q.1 = true ↔ q.1 = 54 := by decide

private lemma dfaTrans_spec_bit_0_0 : ∀ i : Fin 16, ∀ q' : Fin 60,
    (dfaMask (dfaTrans ⟨0 + i.1, by omega⟩ ⟨0, by omega⟩)).testBit q'.1 = ((dfaMask ⟨0 + i.1, by omega⟩ &&& nfaPre ⟨0, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_0_16 : ∀ i : Fin 16, ∀ q' : Fin 60,
    (dfaMask (dfaTrans ⟨16 + i.1, by omega⟩ ⟨0, by omega⟩)).testBit q'.1 = ((dfaMask ⟨16 + i.1, by omega⟩ &&& nfaPre ⟨0, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_0_32 : ∀ i : Fin 16, ∀ q' : Fin 60,
    (dfaMask (dfaTrans ⟨32 + i.1, by omega⟩ ⟨0, by omega⟩)).testBit q'.1 = ((dfaMask ⟨32 + i.1, by omega⟩ &&& nfaPre ⟨0, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_0_48 : ∀ i : Fin 8, ∀ q' : Fin 60,
    (dfaMask (dfaTrans ⟨48 + i.1, by omega⟩ ⟨0, by omega⟩)).testBit q'.1 = ((dfaMask ⟨48 + i.1, by omega⟩ &&& nfaPre ⟨0, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_0 (s : Fin 56) (q' : Fin 60) :
    (dfaMask (dfaTrans s ⟨0, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨0, by omega⟩ q') != 0) := by
  if h0 : s.1 < 16 then
    have hs : s = ⟨0 + (s.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_0_0 ⟨s.1 - 0, by omega⟩ q'
  else
  if h16 : s.1 < 32 then
    have hs : s = ⟨16 + (s.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_0_16 ⟨s.1 - 16, by omega⟩ q'
  else
  if h32 : s.1 < 48 then
    have hs : s = ⟨32 + (s.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_0_32 ⟨s.1 - 32, by omega⟩ q'
  else
    have hs : s = ⟨48 + (s.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_0_48 ⟨s.1 - 48, by omega⟩ q'
private lemma dfaTrans_spec_bit_1_0 : ∀ i : Fin 16, ∀ q' : Fin 60,
    (dfaMask (dfaTrans ⟨0 + i.1, by omega⟩ ⟨1, by omega⟩)).testBit q'.1 = ((dfaMask ⟨0 + i.1, by omega⟩ &&& nfaPre ⟨1, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_1_16 : ∀ i : Fin 16, ∀ q' : Fin 60,
    (dfaMask (dfaTrans ⟨16 + i.1, by omega⟩ ⟨1, by omega⟩)).testBit q'.1 = ((dfaMask ⟨16 + i.1, by omega⟩ &&& nfaPre ⟨1, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_1_32 : ∀ i : Fin 16, ∀ q' : Fin 60,
    (dfaMask (dfaTrans ⟨32 + i.1, by omega⟩ ⟨1, by omega⟩)).testBit q'.1 = ((dfaMask ⟨32 + i.1, by omega⟩ &&& nfaPre ⟨1, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_1_48 : ∀ i : Fin 8, ∀ q' : Fin 60,
    (dfaMask (dfaTrans ⟨48 + i.1, by omega⟩ ⟨1, by omega⟩)).testBit q'.1 = ((dfaMask ⟨48 + i.1, by omega⟩ &&& nfaPre ⟨1, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_1 (s : Fin 56) (q' : Fin 60) :
    (dfaMask (dfaTrans s ⟨1, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨1, by omega⟩ q') != 0) := by
  if h0 : s.1 < 16 then
    have hs : s = ⟨0 + (s.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_1_0 ⟨s.1 - 0, by omega⟩ q'
  else
  if h16 : s.1 < 32 then
    have hs : s = ⟨16 + (s.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_1_16 ⟨s.1 - 16, by omega⟩ q'
  else
  if h32 : s.1 < 48 then
    have hs : s = ⟨32 + (s.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_1_32 ⟨s.1 - 32, by omega⟩ q'
  else
    have hs : s = ⟨48 + (s.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_1_48 ⟨s.1 - 48, by omega⟩ q'
private lemma dfaTrans_spec_bit_2_0 : ∀ i : Fin 16, ∀ q' : Fin 60,
    (dfaMask (dfaTrans ⟨0 + i.1, by omega⟩ ⟨2, by omega⟩)).testBit q'.1 = ((dfaMask ⟨0 + i.1, by omega⟩ &&& nfaPre ⟨2, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_2_16 : ∀ i : Fin 16, ∀ q' : Fin 60,
    (dfaMask (dfaTrans ⟨16 + i.1, by omega⟩ ⟨2, by omega⟩)).testBit q'.1 = ((dfaMask ⟨16 + i.1, by omega⟩ &&& nfaPre ⟨2, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_2_32 : ∀ i : Fin 16, ∀ q' : Fin 60,
    (dfaMask (dfaTrans ⟨32 + i.1, by omega⟩ ⟨2, by omega⟩)).testBit q'.1 = ((dfaMask ⟨32 + i.1, by omega⟩ &&& nfaPre ⟨2, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_2_48 : ∀ i : Fin 8, ∀ q' : Fin 60,
    (dfaMask (dfaTrans ⟨48 + i.1, by omega⟩ ⟨2, by omega⟩)).testBit q'.1 = ((dfaMask ⟨48 + i.1, by omega⟩ &&& nfaPre ⟨2, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_2 (s : Fin 56) (q' : Fin 60) :
    (dfaMask (dfaTrans s ⟨2, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨2, by omega⟩ q') != 0) := by
  if h0 : s.1 < 16 then
    have hs : s = ⟨0 + (s.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_2_0 ⟨s.1 - 0, by omega⟩ q'
  else
  if h16 : s.1 < 32 then
    have hs : s = ⟨16 + (s.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_2_16 ⟨s.1 - 16, by omega⟩ q'
  else
  if h32 : s.1 < 48 then
    have hs : s = ⟨32 + (s.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_2_32 ⟨s.1 - 32, by omega⟩ q'
  else
    have hs : s = ⟨48 + (s.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_2_48 ⟨s.1 - 48, by omega⟩ q'
private lemma dfaTrans_spec_bit_3_0 : ∀ i : Fin 16, ∀ q' : Fin 60,
    (dfaMask (dfaTrans ⟨0 + i.1, by omega⟩ ⟨3, by omega⟩)).testBit q'.1 = ((dfaMask ⟨0 + i.1, by omega⟩ &&& nfaPre ⟨3, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_3_16 : ∀ i : Fin 16, ∀ q' : Fin 60,
    (dfaMask (dfaTrans ⟨16 + i.1, by omega⟩ ⟨3, by omega⟩)).testBit q'.1 = ((dfaMask ⟨16 + i.1, by omega⟩ &&& nfaPre ⟨3, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_3_32 : ∀ i : Fin 16, ∀ q' : Fin 60,
    (dfaMask (dfaTrans ⟨32 + i.1, by omega⟩ ⟨3, by omega⟩)).testBit q'.1 = ((dfaMask ⟨32 + i.1, by omega⟩ &&& nfaPre ⟨3, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_3_48 : ∀ i : Fin 8, ∀ q' : Fin 60,
    (dfaMask (dfaTrans ⟨48 + i.1, by omega⟩ ⟨3, by omega⟩)).testBit q'.1 = ((dfaMask ⟨48 + i.1, by omega⟩ &&& nfaPre ⟨3, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_3 (s : Fin 56) (q' : Fin 60) :
    (dfaMask (dfaTrans s ⟨3, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨3, by omega⟩ q') != 0) := by
  if h0 : s.1 < 16 then
    have hs : s = ⟨0 + (s.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_3_0 ⟨s.1 - 0, by omega⟩ q'
  else
  if h16 : s.1 < 32 then
    have hs : s = ⟨16 + (s.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_3_16 ⟨s.1 - 16, by omega⟩ q'
  else
  if h32 : s.1 < 48 then
    have hs : s = ⟨32 + (s.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_3_32 ⟨s.1 - 32, by omega⟩ q'
  else
    have hs : s = ⟨48 + (s.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_3_48 ⟨s.1 - 48, by omega⟩ q'

private lemma dfaTrans_spec_bit (s : Fin 56) (a : Fin 4) (q' : Fin 60) :
    (dfaMask (dfaTrans s a)).testBit q'.1 = ((dfaMask s &&& nfaPre a q') != 0) := by
  fin_cases a
  · exact dfaTrans_spec_bit_0 s q'
  · exact dfaTrans_spec_bit_1 s q'
  · exact dfaTrans_spec_bit_2 s q'
  · exact dfaTrans_spec_bit_3 s q'

private lemma and_ne_zero_iff (x y : ℕ) (hx : x < 2 ^ 60) :
    ((x &&& y) != 0) = true ↔ ∃ q : Fin 60, x.testBit q.1 = true ∧ y.testBit q.1 = true := by
  simp only [bne_iff_ne, ne_eq]
  constructor
  · intro hne
    by_contra hall; push Not at hall
    apply hne; apply Nat.eq_of_testBit_eq; intro k
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hk : k < 60
    · have := hall ⟨k, hk⟩
      by_cases hx1 : x.testBit k = true
      · have hy1 : y.testBit k = false := by cases h' : y.testBit k <;> simp_all
        simp [hx1, hy1]
      · have hx0 : x.testBit k = false := by cases h' : x.testBit k <;> simp_all
        simp [hx0]
    · have hpow : 2 ^ 60 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      have hx0 : x.testBit k = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx hpow)
      simp [hx0]
  · rintro ⟨q, hxq, hyq⟩ h0
    have := congrArg (fun z => z.testBit q.1) h0
    rw [Nat.testBit_and, Nat.zero_testBit, hxq, hyq] at this
    exact absurd this (by decide)

private lemma dfaMask_empty_iff (s : Fin 56) :
    (∃ q : Fin 60, (dfaMask s).testBit q.1 = true) ↔ s.1 ≠ 9 := by
  rw [← dfaMask_ne_zero_iff s]
  have h := and_ne_zero_iff (dfaMask s) (dfaMask s) (dfaMask_lt s)
  simp only [Nat.and_self, bne_iff_ne, ne_eq, and_self] at h
  exact h.symm

private lemma dfaTrans_iff (s : Fin 56) (a : Fin 4) (q' : Fin 60) :
    (dfaMask (dfaTrans s a)).testBit q'.1 = true ↔
    ∃ q : Fin 60, (dfaMask s).testBit q.1 = true ∧ ∃ b : Fin 4, nfaStep q a b = some q' := by
  rw [dfaTrans_spec_bit, and_ne_zero_iff _ _ (dfaMask_lt s)]
  constructor
  · rintro ⟨q, hq, hpre⟩
    rw [nfaPre_testBit, decide_eq_true_eq] at hpre
    exact ⟨q, hq, hpre⟩
  · rintro ⟨q, hq, hb⟩
    refine ⟨q, hq, ?_⟩
    rw [nfaPre_testBit, decide_eq_true_eq]; exact hb

private def runDFA : (n : ℕ) → (Fin n → Fin 4) → Fin 56
  | 0, _ => ⟨0, by omega⟩
  | n + 1, A => dfaTrans (runDFA n (fun i => A i.castSucc)) (A (Fin.last n))

private def runNFA : (n : ℕ) → (Fin n → Fin 4) → (Fin n → Fin 4) → Option (Fin 60)
  | 0, _, _ => some ⟨54, by omega⟩
  | n + 1, A, B =>
    match runNFA n (fun i => A i.castSucc) (fun i => B i.castSucc) with
    | none => none
    | some q => nfaStep q (A (Fin.last n)) (B (Fin.last n))

private lemma runDFA_iff_runNFA (n : ℕ) (A : Fin n → Fin 4) (q : Fin 60) :
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

private lemma runNFA_sound (n : ℕ) (A B : Fin n → Fin 4) (q : Fin 60) (h : runNFA n A B = some q) :
    (q.1 / 2) % 3 = (∑ r : Fin n, ((B r).1 % 2 + (B r).1 / 2)) ∧
    (∑ r : Fin n, ((B r).1 % 2 + (B r).1 / 2)) ≤ 2 ∧
    (n = 0 → q.1 / 6 = 9) ∧
    (∀ hn : 0 < n, q.1 / 6 =
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
      by_cases hbu_le : (q0.1 / 2) % 3 + (B (Fin.last n)).1 % 2 + (B (Fin.last n)).1 / 2 ≤ 2
      · rw [dif_pos hbu_le] at h
        by_cases hcond : ((q0.1 / 6 == 9 || decide (q0.1 / 6 ≤ 3 * ((A (Fin.last n)).1 % 2 + (B (Fin.last n)).1 % 2) + ((A (Fin.last n)).1 / 2 + (B (Fin.last n)).1 / 2))) && (q0.1 % 2 == 1 || decide ((A (Fin.last n)).1 % 2 + (B (Fin.last n)).1 % 2 ≤ (A (Fin.last n)).1 / 2 + (B (Fin.last n)).1 / 2))) = true
        swap
        · rw [if_neg hcond] at h; simp at h
        rw [if_pos hcond] at h
        injection h with hq_eq
        have hsum_succ : (∑ r : Fin (n + 1), ((B r).1 % 2 + (B r).1 / 2)) =
            (∑ r : Fin n, ((B r.castSucc).1 % 2 + (B r.castSucc).1 / 2)) + ((B (Fin.last n)).1 % 2 + (B (Fin.last n)).1 / 2) :=
          Fin.sum_univ_castSucc _
        have hqval : q.1 = ((3 * ((A (Fin.last n)).1 % 2 + (B (Fin.last n)).1 % 2) +
            ((A (Fin.last n)).1 / 2 + (B (Fin.last n)).1 / 2)) * 3 +
            ((q0.1 / 2) % 3 + (B (Fin.last n)).1 % 2 + (B (Fin.last n)).1 / 2)) * 2 +
            (if (q0.1 % 2 == 1 || decide ((A (Fin.last n)).1 % 2 + (B (Fin.last n)).1 % 2 < (A (Fin.last n)).1 / 2 + (B (Fin.last n)).1 / 2)) = true then 1 else 0) := by
          have := congrArg Fin.val hq_eq; exact this.symm
        have ha2 := (A (Fin.last n)).2; have hb2 := (B (Fin.last n)).2
        have hcond' : (q0.1 / 6 = 9 ∨ q0.1 / 6 ≤ 3 * ((A (Fin.last n)).1 % 2 + (B (Fin.last n)).1 % 2) + ((A (Fin.last n)).1 / 2 + (B (Fin.last n)).1 / 2)) ∧
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
            have hpm_le : q0.1 / 6 ≤ 3 * ((A (Fin.last n)).1 % 2 + (B (Fin.last n)).1 % 2) + ((A (Fin.last n)).1 / 2 + (B (Fin.last n)).1 / 2) := by
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
    (hsum : (∑ r : Fin n, ((B r).1 % 2 + (B r).1 / 2)) ≤ 2)
    (hrow : ∀ r : Fin (n - 1), lexRow2 ((A ⟨r.1, by omega⟩).1 % 2 + (B ⟨r.1, by omega⟩).1 % 2)
                                       ((A ⟨r.1, by omega⟩).1 / 2 + (B ⟨r.1, by omega⟩).1 / 2)
                                       ((A ⟨r.1 + 1, by omega⟩).1 % 2 + (B ⟨r.1 + 1, by omega⟩).1 % 2)
                                       ((A ⟨r.1 + 1, by omega⟩).1 / 2 + (B ⟨r.1 + 1, by omega⟩).1 / 2))
    (hcol : lexCol n (fun r => (A r).1 % 2 + (B r).1 % 2) (fun r => (A r).1 / 2 + (B r).1 / 2)) :
    ∃ q : Fin 60, runNFA n A B = some q := by
  induction n with
  | zero => exact ⟨⟨54, by omega⟩, rfl⟩
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
    have hbu_ok : (q0.1 / 2) % 3 + (B (Fin.last n)).1 % 2 + (B (Fin.last n)).1 / 2 ≤ 2 := by omega
    have hpm_ok : (q0.1 / 6 == 9 || decide (q0.1 / 6 ≤ 3 * ((A (Fin.last n)).1 % 2 + (B (Fin.last n)).1 % 2) + ((A (Fin.last n)).1 / 2 + (B (Fin.last n)).1 / 2))) = true := by
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
    isValid n A ↔ (runDFA n (fun r => enc2 (A r))).1 ≠ 9 := by
  rw [← dfaMask_empty_iff]
  simp only [runDFA_iff_runNFA]
  constructor
  · rintro ⟨B, hBsum, hBrow, hBcol⟩
    have hsum' : (∑ r : Fin n, ((enc2 (B r)).1 % 2 + (enc2 (B r)).1 / 2)) ≤ 2 := by
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

private def dp : ℕ → Fin 56 → ℕ
  | 0, s => if s.1 = 0 then 1 else 0
  | n + 1, s' => ∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then dp n s else 0

private lemma dp_succ_eq (n : ℕ) (s' : Fin 56) :
    dp (n + 1) s' = ∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then dp n s else 0 := rfl

private def tbl_0 (s : Fin 56) : ℕ :=
  (if s.1 < 28 then (if s.1 < 14 then (if s.1 < 7 then (if s.1 < 3 then (if s.1 < 1 then 1 else (if s.1 < 2 then 0 else 0)) else (if s.1 < 5 then (if s.1 < 4 then 0 else 0) else (if s.1 < 6 then 0 else 0))) else (if s.1 < 10 then (if s.1 < 8 then 0 else (if s.1 < 9 then 0 else 0)) else (if s.1 < 12 then (if s.1 < 11 then 0 else 0) else (if s.1 < 13 then 0 else 0)))) else (if s.1 < 21 then (if s.1 < 17 then (if s.1 < 15 then 0 else (if s.1 < 16 then 0 else 0)) else (if s.1 < 19 then (if s.1 < 18 then 0 else 0) else (if s.1 < 20 then 0 else 0))) else (if s.1 < 24 then (if s.1 < 22 then 0 else (if s.1 < 23 then 0 else 0)) else (if s.1 < 26 then (if s.1 < 25 then 0 else 0) else (if s.1 < 27 then 0 else 0))))) else (if s.1 < 42 then (if s.1 < 35 then (if s.1 < 31 then (if s.1 < 29 then 0 else (if s.1 < 30 then 0 else 0)) else (if s.1 < 33 then (if s.1 < 32 then 0 else 0) else (if s.1 < 34 then 0 else 0))) else (if s.1 < 38 then (if s.1 < 36 then 0 else (if s.1 < 37 then 0 else 0)) else (if s.1 < 40 then (if s.1 < 39 then 0 else 0) else (if s.1 < 41 then 0 else 0)))) else (if s.1 < 49 then (if s.1 < 45 then (if s.1 < 43 then 0 else (if s.1 < 44 then 0 else 0)) else (if s.1 < 47 then (if s.1 < 46 then 0 else 0) else (if s.1 < 48 then 0 else 0))) else (if s.1 < 52 then (if s.1 < 50 then 0 else (if s.1 < 51 then 0 else 0)) else (if s.1 < 54 then (if s.1 < 53 then 0 else 0) else (if s.1 < 55 then 0 else 0))))))
private def tbl_1 (s : Fin 56) : ℕ :=
  (if s.1 < 28 then (if s.1 < 14 then (if s.1 < 7 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 1 else 1)) else (if s.1 < 5 then (if s.1 < 4 then 1 else 1) else (if s.1 < 6 then 0 else 0))) else (if s.1 < 10 then (if s.1 < 8 then 0 else (if s.1 < 9 then 0 else 0)) else (if s.1 < 12 then (if s.1 < 11 then 0 else 0) else (if s.1 < 13 then 0 else 0)))) else (if s.1 < 21 then (if s.1 < 17 then (if s.1 < 15 then 0 else (if s.1 < 16 then 0 else 0)) else (if s.1 < 19 then (if s.1 < 18 then 0 else 0) else (if s.1 < 20 then 0 else 0))) else (if s.1 < 24 then (if s.1 < 22 then 0 else (if s.1 < 23 then 0 else 0)) else (if s.1 < 26 then (if s.1 < 25 then 0 else 0) else (if s.1 < 27 then 0 else 0))))) else (if s.1 < 42 then (if s.1 < 35 then (if s.1 < 31 then (if s.1 < 29 then 0 else (if s.1 < 30 then 0 else 0)) else (if s.1 < 33 then (if s.1 < 32 then 0 else 0) else (if s.1 < 34 then 0 else 0))) else (if s.1 < 38 then (if s.1 < 36 then 0 else (if s.1 < 37 then 0 else 0)) else (if s.1 < 40 then (if s.1 < 39 then 0 else 0) else (if s.1 < 41 then 0 else 0)))) else (if s.1 < 49 then (if s.1 < 45 then (if s.1 < 43 then 0 else (if s.1 < 44 then 0 else 0)) else (if s.1 < 47 then (if s.1 < 46 then 0 else 0) else (if s.1 < 48 then 0 else 0))) else (if s.1 < 52 then (if s.1 < 50 then 0 else (if s.1 < 51 then 0 else 0)) else (if s.1 < 54 then (if s.1 < 53 then 0 else 0) else (if s.1 < 55 then 0 else 0))))))
private def tbl_2 (s : Fin 56) : ℕ :=
  (if s.1 < 28 then (if s.1 < 14 then (if s.1 < 7 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 0 else 0)) else (if s.1 < 5 then (if s.1 < 4 then 0 else 0) else (if s.1 < 6 then 1 else 1))) else (if s.1 < 10 then (if s.1 < 8 then 1 else (if s.1 < 9 then 1 else 1)) else (if s.1 < 12 then (if s.1 < 11 then 3 else 2) else (if s.1 < 13 then 1 else 1)))) else (if s.1 < 21 then (if s.1 < 17 then (if s.1 < 15 then 1 else (if s.1 < 16 then 1 else 1)) else (if s.1 < 19 then (if s.1 < 18 then 1 else 0) else (if s.1 < 20 then 0 else 0))) else (if s.1 < 24 then (if s.1 < 22 then 0 else (if s.1 < 23 then 0 else 0)) else (if s.1 < 26 then (if s.1 < 25 then 0 else 0) else (if s.1 < 27 then 0 else 0))))) else (if s.1 < 42 then (if s.1 < 35 then (if s.1 < 31 then (if s.1 < 29 then 0 else (if s.1 < 30 then 0 else 0)) else (if s.1 < 33 then (if s.1 < 32 then 0 else 0) else (if s.1 < 34 then 0 else 0))) else (if s.1 < 38 then (if s.1 < 36 then 0 else (if s.1 < 37 then 0 else 0)) else (if s.1 < 40 then (if s.1 < 39 then 0 else 0) else (if s.1 < 41 then 0 else 0)))) else (if s.1 < 49 then (if s.1 < 45 then (if s.1 < 43 then 0 else (if s.1 < 44 then 0 else 0)) else (if s.1 < 47 then (if s.1 < 46 then 0 else 0) else (if s.1 < 48 then 0 else 0))) else (if s.1 < 52 then (if s.1 < 50 then 0 else (if s.1 < 51 then 0 else 0)) else (if s.1 < 54 then (if s.1 < 53 then 0 else 0) else (if s.1 < 55 then 0 else 0))))))
private def tbl_3 (s : Fin 56) : ℕ :=
  (if s.1 < 28 then (if s.1 < 14 then (if s.1 < 7 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 0 else 0)) else (if s.1 < 5 then (if s.1 < 4 then 0 else 0) else (if s.1 < 6 then 1 else 0))) else (if s.1 < 10 then (if s.1 < 8 then 0 else (if s.1 < 9 then 1 else 16)) else (if s.1 < 12 then (if s.1 < 11 then 11 else 4) else (if s.1 < 13 then 1 else 0)))) else (if s.1 < 21 then (if s.1 < 17 then (if s.1 < 15 then 0 else (if s.1 < 16 then 1 else 1)) else (if s.1 < 19 then (if s.1 < 18 then 1 else 1) else (if s.1 < 20 then 1 else 1))) else (if s.1 < 24 then (if s.1 < 22 then 1 else (if s.1 < 23 then 1 else 1)) else (if s.1 < 26 then (if s.1 < 25 then 1 else 1) else (if s.1 < 27 then 1 else 1))))) else (if s.1 < 42 then (if s.1 < 35 then (if s.1 < 31 then (if s.1 < 29 then 1 else (if s.1 < 30 then 1 else 1)) else (if s.1 < 33 then (if s.1 < 32 then 1 else 1) else (if s.1 < 34 then 1 else 1))) else (if s.1 < 38 then (if s.1 < 36 then 1 else (if s.1 < 37 then 1 else 1)) else (if s.1 < 40 then (if s.1 < 39 then 2 else 1) else (if s.1 < 41 then 1 else 1)))) else (if s.1 < 49 then (if s.1 < 45 then (if s.1 < 43 then 1 else (if s.1 < 44 then 1 else 0)) else (if s.1 < 47 then (if s.1 < 46 then 0 else 0) else (if s.1 < 48 then 0 else 0))) else (if s.1 < 52 then (if s.1 < 50 then 0 else (if s.1 < 51 then 0 else 0)) else (if s.1 < 54 then (if s.1 < 53 then 0 else 0) else (if s.1 < 55 then 0 else 0))))))
private def tbl_4 (s : Fin 56) : ℕ :=
  (if s.1 < 28 then (if s.1 < 14 then (if s.1 < 7 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 0 else 0)) else (if s.1 < 5 then (if s.1 < 4 then 0 else 0) else (if s.1 < 6 then 1 else 0))) else (if s.1 < 10 then (if s.1 < 8 then 0 else (if s.1 < 9 then 1 else 118)) else (if s.1 < 12 then (if s.1 < 11 then 28 else 6) else (if s.1 < 13 then 1 else 0)))) else (if s.1 < 21 then (if s.1 < 17 then (if s.1 < 15 then 0 else (if s.1 < 16 then 1 else 1)) else (if s.1 < 19 then (if s.1 < 18 then 1 else 1) else (if s.1 < 20 then 1 else 2))) else (if s.1 < 24 then (if s.1 < 22 then 6 else (if s.1 < 23 then 0 else 3)) else (if s.1 < 26 then (if s.1 < 25 then 2 else 2) else (if s.1 < 27 then 1 else 0))))) else (if s.1 < 42 then (if s.1 < 35 then (if s.1 < 31 then (if s.1 < 29 then 2 else (if s.1 < 30 then 2 else 4)) else (if s.1 < 33 then (if s.1 < 32 then 3 else 5) else (if s.1 < 34 then 2 else 7))) else (if s.1 < 38 then (if s.1 < 36 then 3 else (if s.1 < 37 then 1 else 5)) else (if s.1 < 40 then (if s.1 < 39 then 4 else 4) else (if s.1 < 41 then 1 else 14)))) else (if s.1 < 49 then (if s.1 < 45 then (if s.1 < 43 then 2 else (if s.1 < 44 then 2 else 1)) else (if s.1 < 47 then (if s.1 < 46 then 1 else 1) else (if s.1 < 48 then 3 else 1))) else (if s.1 < 52 then (if s.1 < 50 then 1 else (if s.1 < 51 then 1 else 1)) else (if s.1 < 54 then (if s.1 < 53 then 4 else 3) else (if s.1 < 55 then 2 else 0))))))
private def tbl_5 (s : Fin 56) : ℕ :=
  (if s.1 < 28 then (if s.1 < 14 then (if s.1 < 7 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 0 else 0)) else (if s.1 < 5 then (if s.1 < 4 then 0 else 0) else (if s.1 < 6 then 1 else 0))) else (if s.1 < 10 then (if s.1 < 8 then 0 else (if s.1 < 9 then 1 else 674)) else (if s.1 < 12 then (if s.1 < 11 then 58 else 8) else (if s.1 < 13 then 1 else 0)))) else (if s.1 < 21 then (if s.1 < 17 then (if s.1 < 15 then 0 else (if s.1 < 16 then 1 else 1)) else (if s.1 < 19 then (if s.1 < 18 then 1 else 1) else (if s.1 < 20 then 1 else 3))) else (if s.1 < 24 then (if s.1 < 22 then 21 else (if s.1 < 23 then 0 else 7)) else (if s.1 < 26 then (if s.1 < 25 then 3 else 3) else (if s.1 < 27 then 1 else 0))))) else (if s.1 < 42 then (if s.1 < 35 then (if s.1 < 31 then (if s.1 < 29 then 3 else (if s.1 < 30 then 3 else 9)) else (if s.1 < 33 then (if s.1 < 32 then 6 else 15) else (if s.1 < 34 then 3 else 29))) else (if s.1 < 38 then (if s.1 < 36 then 6 else (if s.1 < 37 then 1 else 13)) else (if s.1 < 40 then (if s.1 < 39 then 6 else 8) else (if s.1 < 41 then 1 else 69)))) else (if s.1 < 49 then (if s.1 < 45 then (if s.1 < 43 then 3 else (if s.1 < 44 then 3 else 1)) else (if s.1 < 47 then (if s.1 < 46 then 1 else 1) else (if s.1 < 48 then 8 else 2))) else (if s.1 < 52 then (if s.1 < 50 then 3 else (if s.1 < 51 then 1 else 4)) else (if s.1 < 54 then (if s.1 < 53 then 21 else 10) else (if s.1 < 55 then 7 else 1))))))
private def tbl_6 (s : Fin 56) : ℕ :=
  (if s.1 < 28 then (if s.1 < 14 then (if s.1 < 7 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 0 else 0)) else (if s.1 < 5 then (if s.1 < 4 then 0 else 0) else (if s.1 < 6 then 1 else 0))) else (if s.1 < 10 then (if s.1 < 8 then 0 else (if s.1 < 9 then 1 else 3306)) else (if s.1 < 12 then (if s.1 < 11 then 105 else 10) else (if s.1 < 13 then 1 else 0)))) else (if s.1 < 21 then (if s.1 < 17 then (if s.1 < 15 then 0 else (if s.1 < 16 then 1 else 1)) else (if s.1 < 19 then (if s.1 < 18 then 1 else 1) else (if s.1 < 20 then 1 else 4))) else (if s.1 < 24 then (if s.1 < 22 then 55 else (if s.1 < 23 then 0 else 13)) else (if s.1 < 26 then (if s.1 < 25 then 4 else 4) else (if s.1 < 27 then 1 else 0))))) else (if s.1 < 42 then (if s.1 < 35 then (if s.1 < 31 then (if s.1 < 29 then 4 else (if s.1 < 30 then 4 else 16)) else (if s.1 < 33 then (if s.1 < 32 then 10 else 32) else (if s.1 < 34 then 4 else 81))) else (if s.1 < 38 then (if s.1 < 36 then 10 else (if s.1 < 37 then 1 else 26)) else (if s.1 < 40 then (if s.1 < 39 then 8 else 13) else (if s.1 < 41 then 1 else 227)))) else (if s.1 < 49 then (if s.1 < 45 then (if s.1 < 43 then 4 else (if s.1 < 44 then 4 else 1)) else (if s.1 < 47 then (if s.1 < 46 then 1 else 1) else (if s.1 < 48 then 15 else 3))) else (if s.1 < 52 then (if s.1 < 50 then 6 else (if s.1 < 51 then 1 else 10)) else (if s.1 < 54 then (if s.1 < 53 then 63 else 22) else (if s.1 < 55 then 16 else 2))))))
private def tbl_7 (s : Fin 56) : ℕ :=
  (if s.1 < 28 then (if s.1 < 14 then (if s.1 < 7 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 0 else 0)) else (if s.1 < 5 then (if s.1 < 4 then 0 else 0) else (if s.1 < 6 then 1 else 0))) else (if s.1 < 10 then (if s.1 < 8 then 0 else (if s.1 < 9 then 1 else 14768)) else (if s.1 < 12 then (if s.1 < 11 then 173 else 12) else (if s.1 < 13 then 1 else 0)))) else (if s.1 < 21 then (if s.1 < 17 then (if s.1 < 15 then 0 else (if s.1 < 16 then 1 else 1)) else (if s.1 < 19 then (if s.1 < 18 then 1 else 1) else (if s.1 < 20 then 1 else 5))) else (if s.1 < 24 then (if s.1 < 22 then 120 else (if s.1 < 23 then 0 else 21)) else (if s.1 < 26 then (if s.1 < 25 then 5 else 5) else (if s.1 < 27 then 1 else 0))))) else (if s.1 < 42 then (if s.1 < 35 then (if s.1 < 31 then (if s.1 < 29 then 5 else (if s.1 < 30 then 5 else 25)) else (if s.1 < 33 then (if s.1 < 32 then 15 else 58) else (if s.1 < 34 then 5 else 181))) else (if s.1 < 38 then (if s.1 < 36 then 15 else (if s.1 < 37 then 1 else 45)) else (if s.1 < 40 then (if s.1 < 39 then 10 else 19) else (if s.1 < 41 then 1 else 590)))) else (if s.1 < 49 then (if s.1 < 45 then (if s.1 < 43 then 5 else (if s.1 < 44 then 5 else 1)) else (if s.1 < 47 then (if s.1 < 46 then 1 else 1) else (if s.1 < 48 then 24 else 4))) else (if s.1 < 52 then (if s.1 < 50 then 10 else (if s.1 < 51 then 1 else 20)) else (if s.1 < 54 then (if s.1 < 53 then 146 else 40) else (if s.1 < 55 then 30 else 3))))))
private def tbl_8 (s : Fin 56) : ℕ :=
  (if s.1 < 28 then (if s.1 < 14 then (if s.1 < 7 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 0 else 0)) else (if s.1 < 5 then (if s.1 < 4 then 0 else 0) else (if s.1 < 6 then 1 else 0))) else (if s.1 < 10 then (if s.1 < 8 then 0 else (if s.1 < 9 then 1 else 62487)) else (if s.1 < 12 then (if s.1 < 11 then 266 else 14) else (if s.1 < 13 then 1 else 0)))) else (if s.1 < 21 then (if s.1 < 17 then (if s.1 < 15 then 0 else (if s.1 < 16 then 1 else 1)) else (if s.1 < 19 then (if s.1 < 18 then 1 else 1) else (if s.1 < 20 then 1 else 6))) else (if s.1 < 24 then (if s.1 < 22 then 231 else (if s.1 < 23 then 0 else 31)) else (if s.1 < 26 then (if s.1 < 25 then 6 else 6) else (if s.1 < 27 then 1 else 0))))) else (if s.1 < 42 then (if s.1 < 35 then (if s.1 < 31 then (if s.1 < 29 then 6 else (if s.1 < 30 then 6 else 36)) else (if s.1 < 33 then (if s.1 < 32 then 21 else 95) else (if s.1 < 34 then 6 else 351))) else (if s.1 < 38 then (if s.1 < 36 then 21 else (if s.1 < 37 then 1 else 71)) else (if s.1 < 40 then (if s.1 < 39 then 12 else 26) else (if s.1 < 41 then 1 else 1312)))) else (if s.1 < 49 then (if s.1 < 45 then (if s.1 < 43 then 6 else (if s.1 < 44 then 6 else 1)) else (if s.1 < 47 then (if s.1 < 46 then 1 else 1) else (if s.1 < 48 then 35 else 5))) else (if s.1 < 52 then (if s.1 < 50 then 15 else (if s.1 < 51 then 1 else 35)) else (if s.1 < 54 then (if s.1 < 53 then 290 else 65) else (if s.1 < 55 then 50 else 4))))))
private def tbl_9 (s : Fin 56) : ℕ :=
  (if s.1 < 28 then (if s.1 < 14 then (if s.1 < 7 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 0 else 0)) else (if s.1 < 5 then (if s.1 < 4 then 0 else 0) else (if s.1 < 6 then 1 else 0))) else (if s.1 < 10 then (if s.1 < 8 then 0 else (if s.1 < 9 then 1 else 256760)) else (if s.1 < 12 then (if s.1 < 11 then 388 else 16) else (if s.1 < 13 then 1 else 0)))) else (if s.1 < 21 then (if s.1 < 17 then (if s.1 < 15 then 0 else (if s.1 < 16 then 1 else 1)) else (if s.1 < 19 then (if s.1 < 18 then 1 else 1) else (if s.1 < 20 then 1 else 7))) else (if s.1 < 24 then (if s.1 < 22 then 406 else (if s.1 < 23 then 0 else 43)) else (if s.1 < 26 then (if s.1 < 25 then 7 else 7) else (if s.1 < 27 then 1 else 0))))) else (if s.1 < 42 then (if s.1 < 35 then (if s.1 < 31 then (if s.1 < 29 then 7 else (if s.1 < 30 then 7 else 49)) else (if s.1 < 33 then (if s.1 < 32 then 28 else 145) else (if s.1 < 34 then 7 else 617))) else (if s.1 < 38 then (if s.1 < 36 then 28 else (if s.1 < 37 then 1 else 105)) else (if s.1 < 40 then (if s.1 < 39 then 14 else 34) else (if s.1 < 41 then 1 else 2610)))) else (if s.1 < 49 then (if s.1 < 45 then (if s.1 < 43 then 7 else (if s.1 < 44 then 7 else 1)) else (if s.1 < 47 then (if s.1 < 46 then 1 else 1) else (if s.1 < 48 then 48 else 6))) else (if s.1 < 52 then (if s.1 < 50 then 21 else (if s.1 < 51 then 1 else 56)) else (if s.1 < 54 then (if s.1 < 53 then 519 else 98) else (if s.1 < 55 then 77 else 5))))))
private def tbl_10 (s : Fin 56) : ℕ :=
  (if s.1 < 28 then (if s.1 < 14 then (if s.1 < 7 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 0 else 0)) else (if s.1 < 5 then (if s.1 < 4 then 0 else 0) else (if s.1 < 6 then 1 else 0))) else (if s.1 < 10 then (if s.1 < 8 then 0 else (if s.1 < 9 then 1 else 1039575)) else (if s.1 < 12 then (if s.1 < 11 then 543 else 18) else (if s.1 < 13 then 1 else 0)))) else (if s.1 < 21 then (if s.1 < 17 then (if s.1 < 15 then 0 else (if s.1 < 16 then 1 else 1)) else (if s.1 < 19 then (if s.1 < 18 then 1 else 1) else (if s.1 < 20 then 1 else 8))) else (if s.1 < 24 then (if s.1 < 22 then 666 else (if s.1 < 23 then 0 else 57)) else (if s.1 < 26 then (if s.1 < 25 then 8 else 8) else (if s.1 < 27 then 1 else 0))))) else (if s.1 < 42 then (if s.1 < 35 then (if s.1 < 31 then (if s.1 < 29 then 8 else (if s.1 < 30 then 8 else 64)) else (if s.1 < 33 then (if s.1 < 32 then 36 else 210) else (if s.1 < 34 then 8 else 1009))) else (if s.1 < 38 then (if s.1 < 36 then 36 else (if s.1 < 37 then 1 else 148)) else (if s.1 < 40 then (if s.1 < 39 then 16 else 43) else (if s.1 < 41 then 1 else 4775)))) else (if s.1 < 49 then (if s.1 < 45 then (if s.1 < 43 then 8 else (if s.1 < 44 then 8 else 1)) else (if s.1 < 47 then (if s.1 < 46 then 1 else 1) else (if s.1 < 48 then 63 else 7))) else (if s.1 < 52 then (if s.1 < 50 then 28 else (if s.1 < 51 then 1 else 84)) else (if s.1 < 54 then (if s.1 < 53 then 861 else 140) else (if s.1 < 55 then 112 else 6))))))

private lemma dp_eq_tbl_0 (s : Fin 56) : dp 0 s = tbl_0 s := by revert s; decide
private lemma dp_step_ok_1 : ∀ s' : Fin 56,
    (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_0 s else 0) = tbl_1 s' := by decide

private lemma dp_eq_tbl_1 (s' : Fin 56) : dp 1 s' = tbl_1 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then dp 0 s else 0) =
      ∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_0 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro a _
    rw [dp_eq_tbl_0]
  rw [h1]; exact dp_step_ok_1 s' 
private lemma dp_step_ok_2 : ∀ s' : Fin 56,
    (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_1 s else 0) = tbl_2 s' := by decide

private lemma dp_eq_tbl_2 (s' : Fin 56) : dp 2 s' = tbl_2 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then dp 1 s else 0) =
      ∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_1 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro a _
    rw [dp_eq_tbl_1]
  rw [h1]; exact dp_step_ok_2 s' 
private lemma dp_step_ok_3 : ∀ s' : Fin 56,
    (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_2 s else 0) = tbl_3 s' := by decide

private lemma dp_eq_tbl_3 (s' : Fin 56) : dp 3 s' = tbl_3 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then dp 2 s else 0) =
      ∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_2 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro a _
    rw [dp_eq_tbl_2]
  rw [h1]; exact dp_step_ok_3 s' 
private lemma dp_step_ok_4 : ∀ s' : Fin 56,
    (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_3 s else 0) = tbl_4 s' := by decide

private lemma dp_eq_tbl_4 (s' : Fin 56) : dp 4 s' = tbl_4 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then dp 3 s else 0) =
      ∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_3 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro a _
    rw [dp_eq_tbl_3]
  rw [h1]; exact dp_step_ok_4 s' 
private lemma dp_step_ok_5 : ∀ s' : Fin 56,
    (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_4 s else 0) = tbl_5 s' := by decide

private lemma dp_eq_tbl_5 (s' : Fin 56) : dp 5 s' = tbl_5 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then dp 4 s else 0) =
      ∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_4 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro a _
    rw [dp_eq_tbl_4]
  rw [h1]; exact dp_step_ok_5 s' 
private lemma dp_step_ok_6 : ∀ s' : Fin 56,
    (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_5 s else 0) = tbl_6 s' := by decide

private lemma dp_eq_tbl_6 (s' : Fin 56) : dp 6 s' = tbl_6 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then dp 5 s else 0) =
      ∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_5 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro a _
    rw [dp_eq_tbl_5]
  rw [h1]; exact dp_step_ok_6 s' 
private lemma dp_step_ok_7 : ∀ s' : Fin 56,
    (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_6 s else 0) = tbl_7 s' := by decide

private lemma dp_eq_tbl_7 (s' : Fin 56) : dp 7 s' = tbl_7 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then dp 6 s else 0) =
      ∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_6 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro a _
    rw [dp_eq_tbl_6]
  rw [h1]; exact dp_step_ok_7 s' 
private lemma dp_step_ok_8 : ∀ s' : Fin 56,
    (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_7 s else 0) = tbl_8 s' := by decide

private lemma dp_eq_tbl_8 (s' : Fin 56) : dp 8 s' = tbl_8 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then dp 7 s else 0) =
      ∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_7 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro a _
    rw [dp_eq_tbl_7]
  rw [h1]; exact dp_step_ok_8 s' 
private lemma dp_step_ok_9 : ∀ s' : Fin 56,
    (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_8 s else 0) = tbl_9 s' := by decide

private lemma dp_eq_tbl_9 (s' : Fin 56) : dp 9 s' = tbl_9 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then dp 8 s else 0) =
      ∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_8 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro a _
    rw [dp_eq_tbl_8]
  rw [h1]; exact dp_step_ok_9 s' 
private lemma dp_step_ok_10 : ∀ s' : Fin 56,
    (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_9 s else 0) = tbl_10 s' := by decide

private lemma dp_eq_tbl_10 (s' : Fin 56) : dp 10 s' = tbl_10 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then dp 9 s else 0) =
      ∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then tbl_9 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro a _
    rw [dp_eq_tbl_9]
  rw [h1]; exact dp_step_ok_10 s' 

private lemma dp_rec_tbl_ok : ∀ s : Fin 56, s.1 ≠ 9 → tbl_10 s + 15 * tbl_8 s + 15 * tbl_6 s + tbl_4 s = 6 * tbl_9 s + 20 * tbl_7 s + 6 * tbl_5 s := by decide

private lemma dp_rec_base : ∀ s : Fin 56, s.1 ≠ 9 → dp 10 s + 15 * dp 8 s + 15 * dp 6 s + dp 4 s = 6 * dp 9 s + 20 * dp 7 s + 6 * dp 5 s := by
  intro s hs; rw [dp_eq_tbl_4, dp_eq_tbl_5, dp_eq_tbl_6, dp_eq_tbl_7, dp_eq_tbl_8, dp_eq_tbl_9, dp_eq_tbl_10]; exact dp_rec_tbl_ok s hs

private lemma sum_lin (f0 f1 f2 f3 f4 f5 f6 : Fin 56 → ℕ) (s' : Fin 56) (hs' : s'.1 ≠ 9)
    (h : ∀ s : Fin 56, s.1 ≠ 9 → f6 s + 15 * f4 s + 15 * f2 s + f0 s = 6 * f5 s + 20 * f3 s + 6 * f1 s) :
    (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then f6 s else 0) + 15 * (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then f4 s else 0) + 15 * (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then f2 s else 0) + (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then f0 s else 0) = 6 * (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then f5 s else 0) + 20 * (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then f3 s else 0) + 6 * (∑ s : Fin 56, ∑ a : Fin 4, if dfaTrans s a = s' then f1 s else 0) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro a _
  by_cases htr : dfaTrans s a = s'
  · simp only [htr, ↓reduceIte]
    have hs : s.1 ≠ 9 := by
      intro heq
      have h1 : s = ⟨9, by omega⟩ := Fin.ext heq
      have h2 : dfaTrans s a = ⟨9, by omega⟩ := h1 ▸ dfaTrans_empty a
      rw [htr] at h2; exact hs' (congrArg Fin.val h2)
    exact h s hs
  · simp [htr]

private lemma dp_rec (m : ℕ) : ∀ s : Fin 56, s.1 ≠ 9 → dp (m + 10) s + 15 * dp (m + 8) s + 15 * dp (m + 6) s + dp (m + 4) s = 6 * dp (m + 9) s + 20 * dp (m + 7) s + 6 * dp (m + 5) s := by
  induction m with
  | zero => exact dp_rec_base
  | succ m ih =>
    intro s' hs'; rw [dp_succ_eq (m + 4), dp_succ_eq (m + 5), dp_succ_eq (m + 6), dp_succ_eq (m + 7), dp_succ_eq (m + 8), dp_succ_eq (m + 9), dp_succ_eq (m + 10)]
    exact sum_lin (dp (m + 4)) (dp (m + 5)) (dp (m + 6)) (dp (m + 7)) (dp (m + 8)) (dp (m + 9)) (dp (m + 10)) s' hs' ih

private lemma card_runDFA (n : ℕ) : ∀ s : Fin 56, Fintype.card {A : Fin n → Fin 4 // runDFA n A = s} = dp n s := by
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
    let φ : (Σ s : Fin 56, Σ a : Fin 4, {A : Fin n → Fin 4 // runDFA n A = s ∧ dfaTrans s a = s'}) →
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
    a n = ∑ s : Fin 56, if s.1 ≠ 9 then dp n s else 0 := by
  unfold a; rw [if_neg (by omega)]
  let φ : (Σ s : Fin 56, {A : Fin n → Fin 4 // runDFA n A = s ∧ s.1 ≠ 9}) →
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
      have hs : (runDFA n A').1 ≠ 9 := (isValid_iff_runDFA n A).mp hA
      refine ⟨⟨runDFA n A', ⟨A', rfl, hs⟩⟩, ?_⟩
      apply Subtype.ext; funext r; exact dec2_enc2 (A r)
  rw [Fintype.card_congr (Equiv.ofBijective φ hbij).symm, Fintype.card_sigma]
  apply Finset.sum_congr rfl; intro s _
  by_cases hs : s.1 ≠ 9
  · rw [if_pos hs, ← card_runDFA n s]
    refine Fintype.card_congr ⟨fun ⟨A, h1, _⟩ => ⟨A, h1⟩, fun ⟨A, h1⟩ => ⟨A, h1, hs⟩, fun ⟨_, _, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩
  · rw [if_neg hs, Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨_, _, h⟩ => hs h⟩

private lemma a_rec_m (m : ℕ) : a (m + 10) + 15 * a (m + 8) + 15 * a (m + 6) + a (m + 4) = 6 * a (m + 9) + 20 * a (m + 7) + 6 * a (m + 5) := by
  rw [a_eq_sum_dp (m + 4) (by omega), a_eq_sum_dp (m + 5) (by omega), a_eq_sum_dp (m + 6) (by omega), a_eq_sum_dp (m + 7) (by omega), a_eq_sum_dp (m + 8) (by omega), a_eq_sum_dp (m + 9) (by omega), a_eq_sum_dp (m + 10) (by omega)]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s _
  by_cases hs : s.1 ≠ 9
  · simp only [if_pos hs]; exact dp_rec m s hs
  · simp only [if_neg hs, mul_zero, add_zero]

private lemma a_zero : a 0 = 0 := by unfold a; simp
private lemma a_sum_ok_1 : (∑ s : Fin 56, if s.1 ≠ 9 then tbl_1 s else 0) = 4 := by decide
private lemma a_val_1 : a 1 = 4 := by
  rw [a_eq_sum_dp 1 (by omega)]
  have h : (∑ s : Fin 56, if s.1 ≠ 9 then dp 1 s else 0) =
      ∑ s : Fin 56, if s.1 ≠ 9 then tbl_1 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_1]
  rw [h]; exact a_sum_ok_1
private lemma a_sum_ok_2 : (∑ s : Fin 56, if s.1 ≠ 9 then tbl_2 s else 0) = 15 := by decide
private lemma a_val_2 : a 2 = 15 := by
  rw [a_eq_sum_dp 2 (by omega)]
  have h : (∑ s : Fin 56, if s.1 ≠ 9 then dp 2 s else 0) =
      ∑ s : Fin 56, if s.1 ≠ 9 then tbl_2 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_2]
  rw [h]; exact a_sum_ok_2
private lemma a_sum_ok_3 : (∑ s : Fin 56, if s.1 ≠ 9 then tbl_3 s else 0) = 48 := by decide
private lemma a_val_3 : a 3 = 48 := by
  rw [a_eq_sum_dp 3 (by omega)]
  have h : (∑ s : Fin 56, if s.1 ≠ 9 then dp 3 s else 0) =
      ∑ s : Fin 56, if s.1 ≠ 9 then tbl_3 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_3]
  rw [h]; exact a_sum_ok_3
private lemma a_sum_ok_4 : (∑ s : Fin 56, if s.1 ≠ 9 then tbl_4 s else 0) = 138 := by decide
private lemma a_val_4 : a 4 = 138 := by
  rw [a_eq_sum_dp 4 (by omega)]
  have h : (∑ s : Fin 56, if s.1 ≠ 9 then dp 4 s else 0) =
      ∑ s : Fin 56, if s.1 ≠ 9 then tbl_4 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_4]
  rw [h]; exact a_sum_ok_4
private lemma a_sum_ok_5 : (∑ s : Fin 56, if s.1 ≠ 9 then tbl_5 s else 0) = 350 := by decide
private lemma a_val_5 : a 5 = 350 := by
  rw [a_eq_sum_dp 5 (by omega)]
  have h : (∑ s : Fin 56, if s.1 ≠ 9 then dp 5 s else 0) =
      ∑ s : Fin 56, if s.1 ≠ 9 then tbl_5 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_5]
  rw [h]; exact a_sum_ok_5
private lemma a_sum_ok_6 : (∑ s : Fin 56, if s.1 ≠ 9 then tbl_6 s else 0) = 790 := by decide
private lemma a_val_6 : a 6 = 790 := by
  rw [a_eq_sum_dp 6 (by omega)]
  have h : (∑ s : Fin 56, if s.1 ≠ 9 then dp 6 s else 0) =
      ∑ s : Fin 56, if s.1 ≠ 9 then tbl_6 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_6]
  rw [h]; exact a_sum_ok_6
private lemma a_sum_ok_7 : (∑ s : Fin 56, if s.1 ≠ 9 then tbl_7 s else 0) = 1616 := by decide
private lemma a_val_7 : a 7 = 1616 := by
  rw [a_eq_sum_dp 7 (by omega)]
  have h : (∑ s : Fin 56, if s.1 ≠ 9 then dp 7 s else 0) =
      ∑ s : Fin 56, if s.1 ≠ 9 then tbl_7 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_7]
  rw [h]; exact a_sum_ok_7
private lemma a_sum_ok_8 : (∑ s : Fin 56, if s.1 ≠ 9 then tbl_8 s else 0) = 3049 := by decide
private lemma a_val_8 : a 8 = 3049 := by
  rw [a_eq_sum_dp 8 (by omega)]
  have h : (∑ s : Fin 56, if s.1 ≠ 9 then dp 8 s else 0) =
      ∑ s : Fin 56, if s.1 ≠ 9 then tbl_8 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_8]
  rw [h]; exact a_sum_ok_8
private lemma a_sum_ok_9 : (∑ s : Fin 56, if s.1 ≠ 9 then tbl_9 s else 0) = 5384 := by decide
private lemma a_val_9 : a 9 = 5384 := by
  rw [a_eq_sum_dp 9 (by omega)]
  have h : (∑ s : Fin 56, if s.1 ≠ 9 then dp 9 s else 0) =
      ∑ s : Fin 56, if s.1 ≠ 9 then tbl_9 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_9]
  rw [h]; exact a_sum_ok_9
private lemma a_sum_ok_10 : (∑ s : Fin 56, if s.1 ≠ 9 then tbl_10 s else 0) = 9001 := by decide
private lemma a_val_10 : a 10 = 9001 := by
  rw [a_eq_sum_dp 10 (by omega)]
  have h : (∑ s : Fin 56, if s.1 ≠ 9 then dp 10 s else 0) =
      ∑ s : Fin 56, if s.1 ≠ 9 then tbl_10 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_10]
  rw [h]; exact a_sum_ok_10

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

theorem solution : type_of% @OMA.S_oeis_a225976.main := by
  have hrec : ∀ n : ℕ, 6 < n → (a n : ℤ) = 6 * (a (n - 1) : ℤ) - 15 * (a (n - 2) : ℤ) + 20 * (a (n - 3) : ℤ) - 15 * (a (n - 4) : ℤ) + 6 * (a (n - 5) : ℤ) - (a (n - 6) : ℤ) := by
    intro n hn
    by_cases hn7 : n = 7
    · subst hn7; simp [a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7]
    by_cases hn8 : n = 8
    · subst hn8; simp [a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8]
    by_cases hn9 : n = 9
    · subst hn9; simp [a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9]
    · have h := a_rec_m (n - 10)
      simp only [show n - 10 + 10 = n by omega, show n - 10 + 9 = n - 1 by omega, show n - 10 + 8 = n - 2 by omega, show n - 10 + 7 = n - 3 by omega, show n - 10 + 6 = n - 4 by omega, show n - 10 + 5 = n - 5 by omega, show n - 10 + 4 = n - 6 by omega] at h
      omega
  refine ⟨?_, hrec⟩
  ext n
  have hexp : (1 - (PowerSeries.X : PowerSeries ℚ)) ^ 6 = 1 - PowerSeries.C 6 * PowerSeries.X ^ 1 + PowerSeries.C 15 * PowerSeries.X ^ 2 - PowerSeries.C 20 * PowerSeries.X ^ 3 + PowerSeries.C 15 * PowerSeries.X ^ 4 - PowerSeries.C 6 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6 := by
    simp only [map_ofNat]; ring
  rw [hexp]
  have hR : (PowerSeries.X : PowerSeries ℚ) * (4 - 9 * PowerSeries.X + 18 * PowerSeries.X ^ 2 - 5 * PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4 + PowerSeries.X ^ 5) = PowerSeries.C 4 * PowerSeries.X ^ 1 - PowerSeries.C 9 * PowerSeries.X ^ 2 + PowerSeries.C 18 * PowerSeries.X ^ 3 - PowerSeries.C 5 * PowerSeries.X ^ 4 + PowerSeries.C 2 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6 := by
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
  rcases n with _ | _ | _ | _ | _ | _ | _ | m
  · simp [a_zero]
  · simp [a_zero, a_val_1]
  · simp [a_zero, a_val_1, a_val_2]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6]; norm_num
  · simp only [Nat.add_assoc, Nat.reduceAdd, show 1 ≤ m + 7 by omega, show 2 ≤ m + 7 by omega, show 3 ≤ m + 7 by omega, show 4 ≤ m + 7 by omega, show 5 ≤ m + 7 by omega, show 6 ≤ m + 7 by omega, ↓reduceIte,
      show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega, show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega, show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega, show ¬(m + 7 = 1) by omega, show ¬(m + 7 = 2) by omega, show ¬(m + 7 = 3) by omega, show ¬(m + 7 = 4) by omega, show ¬(m + 7 = 5) by omega, show ¬(m + 7 = 6) by omega]
    have hr := hrec (m + 7) (by omega)
    simp only [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega, show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega, show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega] at hr
    have hrq : (a (m + 7) : ℚ) = 6 * (a (m + 6) : ℚ) - 15 * (a (m + 5) : ℚ) + 20 * (a (m + 4) : ℚ) - 15 * (a (m + 3) : ℚ) + 6 * (a (m + 2) : ℚ) - (a (m + 1) : ℚ) := by exact_mod_cast hr
    linarith

end OMA.P_oeis_a225976

theorem OMA.solution : type_of% @OMA.S_oeis_a225976.main :=
  OMA.P_oeis_a225976.solution
