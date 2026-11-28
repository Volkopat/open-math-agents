import OMAStatements.S_oeis_a226988

namespace OMA.P_oeis_a226988

open OMA.S_oeis_a226988

private def lex3Val (r : Fin 8) : ℕ :=
  4 * (r.1 % 2) + 2 * ((r.1 / 2) % 2) + (r.1 / 4)

private def colUpd (cc : ℕ) (r : Fin 8) : Option ℕ :=
  let b0 := r.1 % 2
  let b1 := (r.1 / 2) % 2
  let b2 := r.1 / 4
  let c0 := cc % 2
  let c1 := cc / 2
  if (c0 == 1 || b0 ≤ b1) && (c1 == 1 || b1 ≤ b2) then
    let nc0 := if c0 == 1 || b0 < b1 then 1 else 0
    let nc1 := if c1 == 1 || b1 < b2 then 1 else 0
    some (nc0 + 2 * nc1)
  else none

private def symOf (r1 r2 : Fin 8) : ℕ :=
  let s0 := (r1.1 % 2) + ((r1.1 / 2) % 2) + (r2.1 % 2) + ((r2.1 / 2) % 2)
  let s1 := ((r1.1 / 2) % 2) + (r1.1 / 4) + ((r2.1 / 2) % 2) + (r2.1 / 4)
  s0 + 5 * s1

private def nfaStep (q : Fin 32) (sym : Fin 25) (r2 : Fin 8) : Option (Fin 32) :=
  let r1 : Fin 8 := ⟨q.1 / 4, by have := q.2; omega⟩
  let cc := q.1 % 4
  if lex3Val r1 ≤ lex3Val r2 && symOf r1 r2 == sym.1 then
    match colUpd cc r2 with
    | none => none
    | some ncc =>
      if h : r2.1 * 4 + ncc < 32 then some ⟨r2.1 * 4 + ncc, h⟩ else none
  else none

private def nfaPre (sym : Fin 25) (q : Fin 32) : ℕ :=
  match sym.1 with
  | 0 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 1 else 2) else (if q.1 < 3 then 4 else 8)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0)))))
  | 1 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 2) else (if q.1 < 7 then 0 else 8))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0)))))
  | 2 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 32) else (if q.1 < 7 then 0 else 128))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0)))))
  | 3 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0)))))
  | 4 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0)))))
  | 5 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 5 else 10)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0)))))
  | 6 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 131072) else (if q.1 < 7 then 0 else 524288))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 12)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 10))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0)))))
  | 7 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 512) else (if q.1 < 7 then 0 else 2048))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 4 else 8)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 160))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0)))))
  | 8 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 64 else 128)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0)))))
  | 9 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0)))))
  | 10 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 327680 else 655360)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0)))))
  | 11 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 786432)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 655360))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 3) else (if q.1 < 27 then 0 else 12)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0)))))
  | 12 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 33554432) else (if q.1 < 7 then 0 else 134217728))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 3072)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 262144 else 524288)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 10488320))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 1 else 2) else (if q.1 < 31 then 4 else 8)))))
  | 13 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 4195328 else 8390656)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 16 else 32) else (if q.1 < 31 then 64 else 128)))))
  | 14 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 16384 else 32768)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0)))))
  | 15 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0)))))
  | 16 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 196608) else (if q.1 < 27 then 0 else 786432)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0)))))
  | 17 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 167772160))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 768) else (if q.1 < 27 then 0 else 3072)) else (if q.1 < 30 then (if q.1 < 29 then 65536 else 131072) else (if q.1 < 31 then 262144 else 524288)))))
  | 18 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 67108864 else 134217728)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 1048832 else 2097664) else (if q.1 < 31 then 4195328 else 8390656)))))
  | 19 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 4096 else 8192) else (if q.1 < 31 then 16384 else 32768)))))
  | 20 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0)))))
  | 21 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0)))))
  | 22 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 50331648) else (if q.1 < 27 then 0 else 201326592)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0)))))
  | 23 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 16777216 else 33554432) else (if q.1 < 31 then 67108864 else 134217728)))))
  | 24 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 268435456 else 536870912) else (if q.1 < 31 then 1073741824 else 2147483648)))))
  | _ => 0

private lemma nfaPre_testBit_0 : ∀ q' q : Fin 32,
    (nfaPre ⟨0, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨0, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_1 : ∀ q' q : Fin 32,
    (nfaPre ⟨1, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨1, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_2 : ∀ q' q : Fin 32,
    (nfaPre ⟨2, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨2, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_3 : ∀ q' q : Fin 32,
    (nfaPre ⟨3, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨3, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_4 : ∀ q' q : Fin 32,
    (nfaPre ⟨4, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨4, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_5 : ∀ q' q : Fin 32,
    (nfaPre ⟨5, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨5, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_6 : ∀ q' q : Fin 32,
    (nfaPre ⟨6, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨6, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_7 : ∀ q' q : Fin 32,
    (nfaPre ⟨7, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨7, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_8 : ∀ q' q : Fin 32,
    (nfaPre ⟨8, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨8, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_9 : ∀ q' q : Fin 32,
    (nfaPre ⟨9, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨9, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_10 : ∀ q' q : Fin 32,
    (nfaPre ⟨10, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨10, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_11 : ∀ q' q : Fin 32,
    (nfaPre ⟨11, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨11, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_12 : ∀ q' q : Fin 32,
    (nfaPre ⟨12, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨12, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_13 : ∀ q' q : Fin 32,
    (nfaPre ⟨13, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨13, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_14 : ∀ q' q : Fin 32,
    (nfaPre ⟨14, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨14, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_15 : ∀ q' q : Fin 32,
    (nfaPre ⟨15, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨15, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_16 : ∀ q' q : Fin 32,
    (nfaPre ⟨16, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨16, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_17 : ∀ q' q : Fin 32,
    (nfaPre ⟨17, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨17, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_18 : ∀ q' q : Fin 32,
    (nfaPre ⟨18, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨18, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_19 : ∀ q' q : Fin 32,
    (nfaPre ⟨19, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨19, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_20 : ∀ q' q : Fin 32,
    (nfaPre ⟨20, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨20, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_21 : ∀ q' q : Fin 32,
    (nfaPre ⟨21, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨21, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_22 : ∀ q' q : Fin 32,
    (nfaPre ⟨22, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨22, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_23 : ∀ q' q : Fin 32,
    (nfaPre ⟨23, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨23, by omega⟩ r2 = some q') := by decide
private lemma nfaPre_testBit_24 : ∀ q' q : Fin 32,
    (nfaPre ⟨24, by omega⟩ q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q ⟨24, by omega⟩ r2 = some q') := by decide

private lemma nfaPre_testBit (sym : Fin 25) (q' q : Fin 32) :
    (nfaPre sym q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q sym r2 = some q') := by
  fin_cases sym
  · exact nfaPre_testBit_0 q' q
  · exact nfaPre_testBit_1 q' q
  · exact nfaPre_testBit_2 q' q
  · exact nfaPre_testBit_3 q' q
  · exact nfaPre_testBit_4 q' q
  · exact nfaPre_testBit_5 q' q
  · exact nfaPre_testBit_6 q' q
  · exact nfaPre_testBit_7 q' q
  · exact nfaPre_testBit_8 q' q
  · exact nfaPre_testBit_9 q' q
  · exact nfaPre_testBit_10 q' q
  · exact nfaPre_testBit_11 q' q
  · exact nfaPre_testBit_12 q' q
  · exact nfaPre_testBit_13 q' q
  · exact nfaPre_testBit_14 q' q
  · exact nfaPre_testBit_15 q' q
  · exact nfaPre_testBit_16 q' q
  · exact nfaPre_testBit_17 q' q
  · exact nfaPre_testBit_18 q' q
  · exact nfaPre_testBit_19 q' q
  · exact nfaPre_testBit_20 q' q
  · exact nfaPre_testBit_21 q' q
  · exact nfaPre_testBit_22 q' q
  · exact nfaPre_testBit_23 q' q
  · exact nfaPre_testBit_24 q' q

private def dfaMask (s : Fin 25) : ℕ :=
  (if s.1 < 12 then (if s.1 < 6 then (if s.1 < 3 then (if s.1 < 1 then 302252033 else (if s.1 < 2 then 1 else 0)) else (if s.1 < 4 then 262144 else (if s.1 < 5 then 33556480 else 268451872))) else (if s.1 < 9 then (if s.1 < 7 then 134217728 else (if s.1 < 8 then 1082130432 else 33554432)) else (if s.1 < 10 then 536870912 else (if s.1 < 11 then 268435456 else 2048)))) else (if s.1 < 18 then (if s.1 < 15 then (if s.1 < 13 then 16384 else (if s.1 < 14 then 1073741824 else 128)) else (if s.1 < 16 then 8390688 else (if s.1 < 17 then 32768 else 142606336))) else (if s.1 < 21 then (if s.1 < 19 then 2147483648 else (if s.1 < 20 then 32 else 8388608)) else (if s.1 < 23 then (if s.1 < 22 then 8390656 else 8388736) else (if s.1 < 24 then 536903680 else 2147516416)))))

private def dfaTransVal (s : Fin 25) (sym : Fin 25) : ℕ :=
  match s.1 with
  | 0 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 1 else (if sym.1 < 2 then 2 else 2)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 3))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 2 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 3 else 4)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 5 else (if sym.1 < 14 then 2 else 2)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 6 else 7))) else (if sym.1 < 21 then (if sym.1 < 19 then 2 else (if sym.1 < 20 then 2 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 8) else (if sym.1 < 24 then 9 else 10)))))
  | 1 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 1 else (if sym.1 < 2 then 2 else 2)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 3))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 2 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 8)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 10 else (if sym.1 < 14 then 2 else 2)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 2))) else (if sym.1 < 21 then (if sym.1 < 19 then 2 else (if sym.1 < 20 then 2 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 2) else (if sym.1 < 24 then 2 else 2)))))
  | 2 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 2)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 2 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 2)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 2 else (if sym.1 < 14 then 2 else 2)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 2))) else (if sym.1 < 21 then (if sym.1 < 19 then 2 else (if sym.1 < 20 then 2 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 2) else (if sym.1 < 24 then 2 else 2)))))
  | 3 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 2)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 2 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 3 else 11)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 12 else (if sym.1 < 14 then 2 else 2)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 6 else 13))) else (if sym.1 < 21 then (if sym.1 < 19 then 2 else (if sym.1 < 20 then 2 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 2) else (if sym.1 < 24 then 2 else 2)))))
  | 4 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 2)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 14 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 2)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 15 else (if sym.1 < 14 then 16 else 2)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 17))) else (if sym.1 < 21 then (if sym.1 < 19 then 18 else (if sym.1 < 20 then 2 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 8) else (if sym.1 < 24 then 9 else 2)))))
  | 5 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 19)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 20 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 2)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 2 else (if sym.1 < 14 then 9 else 12)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 2))) else (if sym.1 < 21 then (if sym.1 < 19 then 2 else (if sym.1 < 20 then 13 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 2) else (if sym.1 < 24 then 2 else 10)))))
  | 6 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 2)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 2 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 2)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 14 else (if sym.1 < 14 then 2 else 2)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 20))) else (if sym.1 < 21 then (if sym.1 < 19 then 16 else (if sym.1 < 20 then 2 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 6) else (if sym.1 < 24 then 18 else 2)))))
  | 7 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 2)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 2 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 2)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 20 else (if sym.1 < 14 then 16 else 2)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 2))) else (if sym.1 < 21 then (if sym.1 < 19 then 18 else (if sym.1 < 20 then 2 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 2) else (if sym.1 < 24 then 2 else 13)))))
  | 8 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 2)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 2 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 2)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 19 else (if sym.1 < 14 then 2 else 2)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 20))) else (if sym.1 < 21 then (if sym.1 < 19 then 2 else (if sym.1 < 20 then 2 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 8) else (if sym.1 < 24 then 9 else 2)))))
  | 9 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 2)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 2 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 2)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 2 else (if sym.1 < 14 then 2 else 2)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 2))) else (if sym.1 < 21 then (if sym.1 < 19 then 2 else (if sym.1 < 20 then 2 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 2) else (if sym.1 < 24 then 2 else 9)))))
  | 10 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 2)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 2 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 2)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 2 else (if sym.1 < 14 then 2 else 2)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 2))) else (if sym.1 < 21 then (if sym.1 < 19 then 2 else (if sym.1 < 20 then 2 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 2) else (if sym.1 < 24 then 2 else 10)))))
  | 11 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 2)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 14 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 2)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 21 else (if sym.1 < 14 then 16 else 2)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 6))) else (if sym.1 < 21 then (if sym.1 < 19 then 18 else (if sym.1 < 20 then 2 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 2) else (if sym.1 < 24 then 2 else 2)))))
  | 12 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 2)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 2 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 2)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 2 else (if sym.1 < 14 then 2 else 12)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 2))) else (if sym.1 < 21 then (if sym.1 < 19 then 2 else (if sym.1 < 20 then 13 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 2) else (if sym.1 < 24 then 2 else 2)))))
  | 13 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 2)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 2 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 2)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 2 else (if sym.1 < 14 then 2 else 2)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 2))) else (if sym.1 < 21 then (if sym.1 < 19 then 2 else (if sym.1 < 20 then 2 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 2) else (if sym.1 < 24 then 2 else 13)))))
  | 14 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 14)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 20 else 16)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 2)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 2 else (if sym.1 < 14 then 18 else 2)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 2))) else (if sym.1 < 21 then (if sym.1 < 19 then 2 else (if sym.1 < 20 then 2 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 2) else (if sym.1 < 24 then 2 else 2)))))
  | 15 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 19)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 22 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 2)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 21 else (if sym.1 < 14 then 23 else 2)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 6))) else (if sym.1 < 21 then (if sym.1 < 19 then 18 else (if sym.1 < 20 then 2 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 2) else (if sym.1 < 24 then 2 else 2)))))
  | 16 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 2)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 2 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 2)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 2 else (if sym.1 < 14 then 2 else 16)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 2))) else (if sym.1 < 21 then (if sym.1 < 19 then 2 else (if sym.1 < 20 then 18 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 2) else (if sym.1 < 24 then 2 else 2)))))
  | 17 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 2)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 2 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 2)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 22 else (if sym.1 < 14 then 16 else 2)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 20))) else (if sym.1 < 21 then (if sym.1 < 19 then 24 else (if sym.1 < 20 then 2 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 6) else (if sym.1 < 24 then 18 else 2)))))
  | 18 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 2)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 2 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 2)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 2 else (if sym.1 < 14 then 2 else 2)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 2))) else (if sym.1 < 21 then (if sym.1 < 19 then 2 else (if sym.1 < 20 then 2 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 2) else (if sym.1 < 24 then 2 else 18)))))
  | 19 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 19)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 20 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 2)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 2 else (if sym.1 < 14 then 9 else 2)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 2))) else (if sym.1 < 21 then (if sym.1 < 19 then 2 else (if sym.1 < 20 then 2 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 2) else (if sym.1 < 24 then 2 else 2)))))
  | 20 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 2)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 2 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 2)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 20 else (if sym.1 < 14 then 16 else 2)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 2))) else (if sym.1 < 21 then (if sym.1 < 19 then 18 else (if sym.1 < 20 then 2 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 2) else (if sym.1 < 24 then 2 else 2)))))
  | 21 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 2)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 14 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 2)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 21 else (if sym.1 < 14 then 16 else 2)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 6))) else (if sym.1 < 21 then (if sym.1 < 19 then 18 else (if sym.1 < 20 then 2 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 2) else (if sym.1 < 24 then 2 else 2)))))
  | 22 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 14)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 20 else 16)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 2)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 20 else (if sym.1 < 14 then 24 else 2)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 2))) else (if sym.1 < 21 then (if sym.1 < 19 then 18 else (if sym.1 < 20 then 2 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 2) else (if sym.1 < 24 then 2 else 2)))))
  | 23 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 2)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 2 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 2)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 2 else (if sym.1 < 14 then 2 else 16)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 2))) else (if sym.1 < 21 then (if sym.1 < 19 then 2 else (if sym.1 < 20 then 18 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 2) else (if sym.1 < 24 then 2 else 9)))))
  | 24 => (if sym.1 < 12 then (if sym.1 < 6 then (if sym.1 < 3 then (if sym.1 < 1 then 2 else (if sym.1 < 2 then 2 else 2)) else (if sym.1 < 4 then 2 else (if sym.1 < 5 then 2 else 2))) else (if sym.1 < 9 then (if sym.1 < 7 then 2 else (if sym.1 < 8 then 2 else 2)) else (if sym.1 < 10 then 2 else (if sym.1 < 11 then 2 else 2)))) else (if sym.1 < 18 then (if sym.1 < 15 then (if sym.1 < 13 then 2 else (if sym.1 < 14 then 2 else 16)) else (if sym.1 < 16 then 2 else (if sym.1 < 17 then 2 else 2))) else (if sym.1 < 21 then (if sym.1 < 19 then 2 else (if sym.1 < 20 then 18 else 2)) else (if sym.1 < 23 then (if sym.1 < 22 then 2 else 2) else (if sym.1 < 24 then 2 else 18)))))
  | _ => 0

private lemma dfaTransVal_lt : ∀ s : Fin 25, ∀ sym : Fin 25, dfaTransVal s sym < 25 := by decide

private def dfaTrans (s : Fin 25) (sym : Fin 25) : Fin 25 :=
  ⟨dfaTransVal s sym, dfaTransVal_lt s sym⟩

private lemma dfaTrans_empty : ∀ sym : Fin 25, dfaTrans ⟨2, by omega⟩ sym = ⟨2, by omega⟩ := by decide

private lemma dfaMask_empty_iff : ∀ s : Fin 25,
    (∃ q : Fin 32, (dfaMask s).testBit q.1 = true) ↔ s.1 ≠ 2 := by decide

private lemma dfaMask_init : ∀ q : Fin 32,
    (dfaMask ⟨0, by omega⟩).testBit q.1 = true ↔ colUpd 0 ⟨q.1 / 4, by have := q.2; omega⟩ = some (q.1 % 4) := by decide

private lemma dfaTrans_spec_bit_0 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨0, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨0, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_1 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨1, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨1, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_2 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨2, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨2, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_3 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨3, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨3, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_4 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨4, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨4, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_5 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨5, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨5, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_6 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨6, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨6, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_7 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨7, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨7, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_8 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨8, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨8, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_9 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨9, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨9, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_10 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨10, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨10, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_11 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨11, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨11, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_12 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨12, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨12, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_13 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨13, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨13, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_14 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨14, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨14, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_15 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨15, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨15, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_16 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨16, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨16, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_17 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨17, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨17, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_18 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨18, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨18, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_19 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨19, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨19, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_20 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨20, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨20, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_21 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨21, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨21, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_22 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨22, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨22, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_23 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨23, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨23, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_24 : ∀ s : Fin 25, ∀ q' : Fin 32,
    (dfaMask (dfaTrans s ⟨24, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨24, by omega⟩ q') != 0) := by decide

private lemma dfaTrans_spec_bit (s : Fin 25) (sym : Fin 25) (q' : Fin 32) :
    (dfaMask (dfaTrans s sym)).testBit q'.1 = ((dfaMask s &&& nfaPre sym q') != 0) := by
  fin_cases sym
  · exact dfaTrans_spec_bit_0 s q'
  · exact dfaTrans_spec_bit_1 s q'
  · exact dfaTrans_spec_bit_2 s q'
  · exact dfaTrans_spec_bit_3 s q'
  · exact dfaTrans_spec_bit_4 s q'
  · exact dfaTrans_spec_bit_5 s q'
  · exact dfaTrans_spec_bit_6 s q'
  · exact dfaTrans_spec_bit_7 s q'
  · exact dfaTrans_spec_bit_8 s q'
  · exact dfaTrans_spec_bit_9 s q'
  · exact dfaTrans_spec_bit_10 s q'
  · exact dfaTrans_spec_bit_11 s q'
  · exact dfaTrans_spec_bit_12 s q'
  · exact dfaTrans_spec_bit_13 s q'
  · exact dfaTrans_spec_bit_14 s q'
  · exact dfaTrans_spec_bit_15 s q'
  · exact dfaTrans_spec_bit_16 s q'
  · exact dfaTrans_spec_bit_17 s q'
  · exact dfaTrans_spec_bit_18 s q'
  · exact dfaTrans_spec_bit_19 s q'
  · exact dfaTrans_spec_bit_20 s q'
  · exact dfaTrans_spec_bit_21 s q'
  · exact dfaTrans_spec_bit_22 s q'
  · exact dfaTrans_spec_bit_23 s q'
  · exact dfaTrans_spec_bit_24 s q'

private lemma dfaMask_lt : ∀ s : Fin 25, dfaMask s < 2 ^ 32 := by decide

private lemma and_ne_zero_iff (x y : ℕ) (hx : x < 2 ^ 32) :
    ((x &&& y) != 0) = true ↔ ∃ q : Fin 32, x.testBit q.1 = true ∧ y.testBit q.1 = true := by
  simp only [bne_iff_ne, ne_eq]
  constructor
  · intro hne
    by_contra hall; push Not at hall
    apply hne; apply Nat.eq_of_testBit_eq; intro k
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hk : k < 32
    · have := hall ⟨k, hk⟩
      by_cases hx1 : x.testBit k = true
      · have hy1 : y.testBit k = false := by cases h' : y.testBit k <;> simp_all
        simp [hx1, hy1]
      · have hx0 : x.testBit k = false := by cases h' : x.testBit k <;> simp_all
        simp [hx0]
    · have hpow : 2 ^ 32 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      have hx0 : x.testBit k = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx hpow)
      simp [hx0]
  · rintro ⟨q, hxq, hyq⟩ h0
    have := congrArg (fun z => z.testBit q.1) h0
    rw [Nat.testBit_and, Nat.zero_testBit, hxq, hyq] at this
    exact absurd this (by decide)

private lemma dfaTrans_iff (s : Fin 25) (sym : Fin 25) (q' : Fin 32) :
    (dfaMask (dfaTrans s sym)).testBit q'.1 = true ↔
    ∃ q : Fin 32, (dfaMask s).testBit q.1 = true ∧ ∃ r2 : Fin 8, nfaStep q sym r2 = some q' := by
  rw [dfaTrans_spec_bit, and_ne_zero_iff _ _ (dfaMask_lt s)]
  constructor
  · rintro ⟨q, hq, hpre⟩
    rw [nfaPre_testBit, decide_eq_true_eq] at hpre
    exact ⟨q, hq, hpre⟩
  · rintro ⟨q, hq, hr2⟩
    refine ⟨q, hq, ?_⟩
    rw [nfaPre_testBit, decide_eq_true_eq]; exact hr2

private def runDFA : (n : ℕ) → (Fin n → Fin 25) → Fin 25
  | 0, _ => ⟨0, by omega⟩
  | n + 1, A => dfaTrans (runDFA n (fun i => A i.castSucc)) (A (Fin.last n))

private def runNFA : (n : ℕ) → (Fin n → Fin 25) → (Fin (n + 1) → Fin 8) → Option (Fin 32)
  | 0, _, M =>
    match colUpd 0 (M 0) with
    | none => none
    | some cc => if h : (M 0).1 * 4 + cc < 32 then some ⟨(M 0).1 * 4 + cc, h⟩ else none
  | n + 1, A, M =>
    match runNFA n (fun i => A i.castSucc) (fun i => M i.castSucc) with
    | none => none
    | some q => nfaStep q (A (Fin.last n)) (M (Fin.last (n + 1)))

private lemma runDFA_iff_runNFA (n : ℕ) (A : Fin n → Fin 25) (q : Fin 32) :
    (dfaMask (runDFA n A)).testBit q.1 = true ↔ ∃ M : Fin (n + 1) → Fin 8, runNFA n A M = some q := by
  induction n generalizing q with
  | zero =>
    unfold runDFA; rw [dfaMask_init]
    constructor
    · intro hcc
      refine ⟨fun _ => ⟨q.1 / 4, by have := q.2; omega⟩, ?_⟩
      unfold runNFA; rw [hcc]; dsimp only
      have hlt : q.1 / 4 * 4 + q.1 % 4 < 32 := by have := q.2; omega
      rw [dif_pos hlt]; congr 1; apply Fin.ext; dsimp; omega
    · rintro ⟨M, hM⟩
      unfold runNFA at hM
      cases hcc : colUpd 0 (M 0) with
      | none => rw [hcc] at hM; simp at hM
      | some cc =>
        rw [hcc] at hM; dsimp only at hM
        split_ifs at hM with hlt
        · injection hM with hq_eq
          have hqval : q.1 = (M 0).1 * 4 + cc := (congrArg Fin.val hq_eq).symm
          have hcc4 : cc < 4 := by
            unfold colUpd at hcc; dsimp only at hcc
            by_cases hcond : ((0 % 2 == 1 || decide ((M 0).1 % 2 ≤ ((M 0).1 / 2) % 2)) && (0 / 2 == 1 || decide (((M 0).1 / 2) % 2 ≤ (M 0).1 / 4))) = true
            · rw [if_pos hcond] at hcc; injection hcc with hc; rw [← hc]; split_ifs <;> omega
            · rw [if_neg hcond] at hcc; simp at hcc
          have hdiv : (⟨q.1 / 4, by have := q.2; omega⟩ : Fin 8) = M 0 := by apply Fin.ext; dsimp; omega
          have hmod : q.1 % 4 = cc := by omega
          rw [hdiv, hmod]; exact hcc
  | succ n ih =>
    unfold runDFA; rw [dfaTrans_iff]
    constructor
    · rintro ⟨q0, hq0, rLast, hstep⟩
      obtain ⟨M0, hM0⟩ := (ih (fun i => A i.castSucc) q0).mp hq0
      refine ⟨Fin.snoc M0 rLast, ?_⟩
      unfold runNFA
      have hcast : (fun i : Fin (n + 1) => (Fin.snoc M0 rLast : Fin (n + 2) → Fin 8) i.castSucc) = M0 := by
        funext i; exact Fin.snoc_castSucc _ _ i
      rw [hcast, hM0, Fin.snoc_last]; exact hstep
    · rintro ⟨M, hM⟩
      unfold runNFA at hM
      cases hprev : runNFA n (fun i => A i.castSucc) (fun i => M i.castSucc) with
      | none => rw [hprev] at hM; simp at hM
      | some q0 =>
        rw [hprev] at hM
        exact ⟨q0, (ih (fun i => A i.castSucc) q0).mpr ⟨fun i => M i.castSucc, hprev⟩, M (Fin.last (n + 1)), hM⟩

private def enc3 (r : Fin 3 → Fin 2) : Fin 8 :=
  ⟨(r 0).1 + 2 * (r 1).1 + 4 * (r 2).1, by have := (r 0).2; have := (r 1).2; have := (r 2).2; omega⟩

private def dec3 (x : Fin 8) (c : Fin 3) : Fin 2 :=
  if c.1 = 0 then ⟨x.1 % 2, Nat.mod_lt _ (by omega)⟩
  else if c.1 = 1 then ⟨(x.1 / 2) % 2, Nat.mod_lt _ (by omega)⟩
  else ⟨x.1 / 4, by have := x.2; omega⟩

private lemma enc3_dec3 (x : Fin 8) : enc3 (dec3 x) = x := by
  apply Fin.ext; unfold enc3 dec3; dsimp; have := x.2; omega

private lemma dec3_enc3 (r : Fin 3 → Fin 2) : dec3 (enc3 r) = r := by
  funext c; fin_cases c <;> (apply Fin.ext; unfold dec3 enc3; dsimp; have := (r 0).2; have := (r 1).2; have := (r 2).2; omega)

private def encSym (r : Fin 2 → Fin 5) : Fin 25 :=
  ⟨(r 0).1 + 5 * (r 1).1, by have := (r 0).2; have := (r 1).2; omega⟩

private def decSym (x : Fin 25) (c : Fin 2) : Fin 5 :=
  if c.1 = 0 then ⟨x.1 % 5, Nat.mod_lt _ (by omega)⟩ else ⟨x.1 / 5, by have := x.2; omega⟩

private lemma runNFA_sound (n : ℕ) (A : Fin n → Fin 25) (M : Fin (n + 1) → Fin 8) (q : Fin 32) (h : runNFA n A M = some q) :
    q.1 / 4 = (M (Fin.last n)).1 ∧
    ((q.1 % 4) % 2 = 0 → ∀ r : Fin (n + 1), (M r).1 % 2 = ((M r).1 / 2) % 2) ∧
    ((q.1 % 4) % 2 = 1 → ∃ r : Fin (n + 1), (∀ j : Fin (n + 1), j.1 < r.1 → (M j).1 % 2 = ((M j).1 / 2) % 2) ∧ (M r).1 % 2 < ((M r).1 / 2) % 2) ∧
    ((q.1 % 4) / 2 = 0 → ∀ r : Fin (n + 1), ((M r).1 / 2) % 2 = (M r).1 / 4) ∧
    ((q.1 % 4) / 2 = 1 → ∃ r : Fin (n + 1), (∀ j : Fin (n + 1), j.1 < r.1 → ((M j).1 / 2) % 2 = (M j).1 / 4) ∧ ((M r).1 / 2) % 2 < (M r).1 / 4) ∧
    (∀ r : Fin n, lex3Val (M ⟨r.1, by omega⟩) ≤ lex3Val (M ⟨r.1 + 1, by omega⟩) ∧
                  symOf (M ⟨r.1, by omega⟩) (M ⟨r.1 + 1, by omega⟩) = (A r).1) := by
  induction n generalizing q with
  | zero =>
    unfold runNFA at h
    cases hcc : colUpd 0 (M 0) with
    | none => rw [hcc] at h; simp at h
    | some cc =>
      rw [hcc] at h; dsimp only at h
      split_ifs at h with hlt
      · injection h with hq_eq
        have hqval : q.1 = (M 0).1 * 4 + cc := (congrArg Fin.val hq_eq).symm
        unfold colUpd at hcc; dsimp only at hcc
        by_cases hcond : ((0 % 2 == 1 || decide ((M 0).1 % 2 ≤ ((M 0).1 / 2) % 2)) && (0 / 2 == 1 || decide (((M 0).1 / 2) % 2 ≤ (M 0).1 / 4))) = true
        · rw [if_pos hcond] at hcc
          injection hcc with hcc_eq
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
          have hcc_val : cc = (if (M 0).1 % 2 < ((M 0).1 / 2) % 2 then 1 else 0) + 2 * (if ((M 0).1 / 2) % 2 < (M 0).1 / 4 then 1 else 0) := by
            rw [← hcc_eq]; simp
          have hl0 : (Fin.last 0 : Fin 1) = 0 := rfl
          refine ⟨by rw [hl0, hqval, hcc_val]; split_ifs <;> omega,
            fun h0 r => by fin_cases r; dsimp; rw [hqval, hcc_val] at h0; split_ifs at h0 <;> omega,
            fun h1 => ⟨0, fun j hj => by fin_cases j; simp at hj, by rw [hqval, hcc_val] at h1; split_ifs at h1 <;> omega⟩,
            fun h0 r => by fin_cases r; dsimp; rw [hqval, hcc_val] at h0; split_ifs at h0 <;> omega,
            fun h1 => ⟨0, fun j hj => by fin_cases j; simp at hj, by rw [hqval, hcc_val] at h1; split_ifs at h1 <;> omega⟩,
            fun r => r.elim0⟩
        · rw [if_neg hcond] at hcc; simp at hcc
  | succ n ih =>
    unfold runNFA at h
    cases hprev : runNFA n (fun i => A i.castSucc) (fun i => M i.castSucc) with
    | none => rw [hprev] at h; simp at h
    | some q0 =>
      rw [hprev] at h
      obtain ⟨hr0, hc00, hc01, hc10, hc11, hrows0⟩ := ih (fun i => A i.castSucc) (fun i => M i.castSucc) q0 hprev
      unfold nfaStep at h; dsimp only at h
      split_ifs at h with hstep_ok
      · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hstep_ok
        cases hcc : colUpd (q0.1 % 4) (M (Fin.last (n + 1))) with
        | none => rw [hcc] at h; simp at h
        | some ncc =>
          rw [hcc] at h; dsimp only at h
          split_ifs at h with hlt
          · injection h with hq_eq
            have hqval : q.1 = (M (Fin.last (n + 1))).1 * 4 + ncc := (congrArg Fin.val hq_eq).symm
            unfold colUpd at hcc; dsimp only at hcc
            by_cases hcond : (((q0.1 % 4) % 2 == 1 || decide ((M (Fin.last (n + 1))).1 % 2 ≤ ((M (Fin.last (n + 1))).1 / 2) % 2)) && ((q0.1 % 4) / 2 == 1 || decide (((M (Fin.last (n + 1))).1 / 2) % 2 ≤ (M (Fin.last (n + 1))).1 / 4))) = true
            swap
            · rw [if_neg hcond] at hcc; simp at hcc
            rw [if_pos hcond] at hcc
            injection hcc with hncc_eq
            simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
            have hncc_val : ncc = (if (q0.1 % 4) % 2 = 1 ∨ (M (Fin.last (n + 1))).1 % 2 < ((M (Fin.last (n + 1))).1 / 2) % 2 then 1 else 0) +
                2 * (if (q0.1 % 4) / 2 = 1 ∨ ((M (Fin.last (n + 1))).1 / 2) % 2 < (M (Fin.last (n + 1))).1 / 4 then 1 else 0) := by
              rw [← hncc_eq]; simp [Bool.or_eq_true]
            refine ⟨by rw [hqval, hncc_val]; split_ifs <;> omega, ?_, ?_, ?_, ?_, ?_⟩
            · intro h0 r
              rw [hqval, hncc_val] at h0
              have hbit0 : (q0.1 % 4) % 2 = 0 ∧ ¬((M (Fin.last (n + 1))).1 % 2 < ((M (Fin.last (n + 1))).1 / 2) % 2) := by
                split_ifs at h0 with ha hb <;> omega
              refine Fin.lastCases ?_ ?_ r
              · rcases hcond.1 with hc | hle <;> omega
              · intro j; exact hc00 hbit0.1 j
            · intro h1
              by_cases h01 : (q0.1 % 4) % 2 = 1
              · obtain ⟨r, hr1, hr2⟩ := hc01 h01
                refine ⟨r.castSucc, fun j hj => ?_, hr2⟩
                have hjlt : j.1 < n + 1 := by have := r.2; omega
                have hjeq : (⟨j.1, hjlt⟩ : Fin (n + 1)).castSucc = j := Fin.ext rfl
                rw [← hjeq]; exact hr1 ⟨j.1, hjlt⟩ hj
              · have h00 : (q0.1 % 4) % 2 = 0 := by omega
                rw [hqval, hncc_val] at h1
                have hlt_last : (M (Fin.last (n + 1))).1 % 2 < ((M (Fin.last (n + 1))).1 / 2) % 2 := by
                  split_ifs at h1 with ha hb <;> omega
                refine ⟨Fin.last (n + 1), fun j hj => ?_, hlt_last⟩
                have hjlt : j.1 < n + 1 := by simp [Fin.last] at hj; omega
                have hjeq : (⟨j.1, hjlt⟩ : Fin (n + 1)).castSucc = j := Fin.ext rfl
                rw [← hjeq]; exact hc00 h00 ⟨j.1, hjlt⟩
            · intro h0 r
              rw [hqval, hncc_val] at h0
              have hbit0 : (q0.1 % 4) / 2 = 0 ∧ ¬(((M (Fin.last (n + 1))).1 / 2) % 2 < (M (Fin.last (n + 1))).1 / 4) := by
                split_ifs at h0 with ha hb <;> omega
              refine Fin.lastCases ?_ ?_ r
              · rcases hcond.2 with hc | hle <;> omega
              · intro j; exact hc10 hbit0.1 j
            · intro h1
              by_cases h01 : (q0.1 % 4) / 2 = 1
              · obtain ⟨r, hr1, hr2⟩ := hc11 h01
                refine ⟨r.castSucc, fun j hj => ?_, hr2⟩
                have hjlt : j.1 < n + 1 := by have := r.2; omega
                have hjeq : (⟨j.1, hjlt⟩ : Fin (n + 1)).castSucc = j := Fin.ext rfl
                rw [← hjeq]; exact hr1 ⟨j.1, hjlt⟩ hj
              · have h00 : (q0.1 % 4) / 2 = 0 := by omega
                rw [hqval, hncc_val] at h1
                have hlt_last : ((M (Fin.last (n + 1))).1 / 2) % 2 < (M (Fin.last (n + 1))).1 / 4 := by
                  split_ifs at h1 with ha hb <;> omega
                refine ⟨Fin.last (n + 1), fun j hj => ?_, hlt_last⟩
                have hjlt : j.1 < n + 1 := by simp [Fin.last] at hj; omega
                have hjeq : (⟨j.1, hjlt⟩ : Fin (n + 1)).castSucc = j := Fin.ext rfl
                rw [← hjeq]; exact hc10 h00 ⟨j.1, hjlt⟩
            · intro r
              by_cases hr : r.1 < n
              · exact hrows0 ⟨r.1, hr⟩
              · have hreq : r.1 = n := by omega
                have e1 : (⟨r.1, by omega⟩ : Fin (n + 2)) = (Fin.last n).castSucc := by apply Fin.ext; simp [Fin.last, hreq]
                have e2 : (⟨r.1 + 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) := by apply Fin.ext; simp [Fin.last, hreq]
                have eA : r = Fin.last n := Fin.ext (by simp [Fin.last, hreq])
                have hr0' : (⟨q0.1 / 4, by have := q0.2; omega⟩ : Fin 8) = M (Fin.last n).castSucc := Fin.ext hr0
                rw [e1, e2, eA, ← hr0']
                exact hstep_ok

private lemma runNFA_complete (n : ℕ) (A : Fin n → Fin 25) (M : Fin (n + 1) → Fin 8)
    (hrow : ∀ r : Fin n, lex3Val (M ⟨r.1, by omega⟩) ≤ lex3Val (M ⟨r.1 + 1, by omega⟩) ∧
                         symOf (M ⟨r.1, by omega⟩) (M ⟨r.1 + 1, by omega⟩) = (A r).1)
    (hcol0 : lexCol (n + 1) (fun r => dec3 (M r) 0) (fun r => dec3 (M r) 1))
    (hcol1 : lexCol (n + 1) (fun r => dec3 (M r) 1) (fun r => dec3 (M r) 2)) :
    ∃ q : Fin 32, runNFA n A M = some q := by
  induction n with
  | zero =>
    unfold runNFA colUpd; dsimp only
    have hc0 : (M 0).1 % 2 ≤ ((M 0).1 / 2) % 2 := by
      rcases hcol0 with heq | ⟨r, _, hr2⟩
      · have := congrArg Fin.val (congrFun heq 0); unfold dec3 at this; dsimp at this; omega
      · fin_cases r; unfold dec3 at hr2; simp only [Fin.lt_def] at hr2; dsimp at hr2; omega
    have hc1 : ((M 0).1 / 2) % 2 ≤ (M 0).1 / 4 := by
      rcases hcol1 with heq | ⟨r, _, hr2⟩
      · have := congrArg Fin.val (congrFun heq 0); unfold dec3 at this; dsimp at this; omega
      · fin_cases r; unfold dec3 at hr2; simp only [Fin.lt_def] at hr2; dsimp at hr2; omega
    rw [if_pos (by simp [hc0, hc1])]
    dsimp only
    have hlt : (M 0).1 * 4 + ((if (0 == 1 || decide ((M 0).1 % 2 < ((M 0).1 / 2) % 2)) = true then 1 else 0) +
        2 * if (0 == 1 || decide (((M 0).1 / 2) % 2 < (M 0).1 / 4)) = true then 1 else 0) < 32 := by
      have := (M 0).2; split_ifs <;> omega
    rw [dif_pos hlt]; exact ⟨_, rfl⟩
  | succ n ih =>
    have hcol0_prev : lexCol (n + 1) (fun r => dec3 (M r.castSucc) 0) (fun r => dec3 (M r.castSucc) 1) := by
      rcases hcol0 with heq | ⟨r, hr1, hr2⟩
      · left; funext i; exact congrFun heq i.castSucc
      · by_cases hr : r.1 < n + 1
        · right; refine ⟨⟨r.1, hr⟩, fun j hj => hr1 j.castSucc hj, hr2⟩
        · left; funext i; exact hr1 i.castSucc (by have := i.2; simp [Fin.val_castSucc]; omega)
    have hcol1_prev : lexCol (n + 1) (fun r => dec3 (M r.castSucc) 1) (fun r => dec3 (M r.castSucc) 2) := by
      rcases hcol1 with heq | ⟨r, hr1, hr2⟩
      · left; funext i; exact congrFun heq i.castSucc
      · by_cases hr : r.1 < n + 1
        · right; refine ⟨⟨r.1, hr⟩, fun j hj => hr1 j.castSucc hj, hr2⟩
        · left; funext i; exact hr1 i.castSucc (by have := i.2; simp [Fin.val_castSucc]; omega)
    obtain ⟨q0, hq0⟩ := ih (fun i => A i.castSucc) (fun i => M i.castSucc)
      (fun r => hrow ⟨r.1, by omega⟩) hcol0_prev hcol1_prev
    obtain ⟨hr0, hc00, _, hc10, _, _⟩ := runNFA_sound n (fun i => A i.castSucc) (fun i => M i.castSucc) q0 hq0
    unfold runNFA; rw [hq0]; unfold nfaStep; dsimp only
    have hr0' : (⟨q0.1 / 4, by have := q0.2; omega⟩ : Fin 8) = M (Fin.last n).castSucc := Fin.ext hr0
    have hstep := hrow (Fin.last n)
    have e1 : (⟨(Fin.last n).1, by omega⟩ : Fin (n + 2)) = (Fin.last n).castSucc := rfl
    have e2 : (⟨(Fin.last n).1 + 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) := rfl
    rw [e1, e2] at hstep
    rw [hr0', if_pos (by simp [hstep.1, hstep.2])]
    unfold colUpd; dsimp only
    have hc0_ok : ((q0.1 % 4) % 2 == 1 || decide ((M (Fin.last (n + 1))).1 % 2 ≤ ((M (Fin.last (n + 1))).1 / 2) % 2)) = true := by
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
      by_cases h1 : (q0.1 % 4) % 2 = 1
      · left; exact h1
      · right
        have h0 : (q0.1 % 4) % 2 = 0 := by omega
        rcases hcol0 with heq | ⟨r, _, hr2⟩
        · have := congrArg Fin.val (congrFun heq (Fin.last (n + 1))); unfold dec3 at this; dsimp at this; omega
        · by_cases hr : r.1 < n + 1
          · have h0r := hc00 h0 ⟨r.1, hr⟩
            have hreq : (⟨r.1, hr⟩ : Fin (n + 1)).castSucc = r := Fin.ext rfl
            rw [hreq] at h0r; unfold dec3 at hr2; simp only [Fin.lt_def] at hr2; dsimp at hr2; omega
          · have hreq : r = Fin.last (n + 1) := Fin.ext (by simp [Fin.last]; omega)
            rw [hreq] at hr2; unfold dec3 at hr2; simp only [Fin.lt_def] at hr2; dsimp at hr2; omega
    have hc1_ok : ((q0.1 % 4) / 2 == 1 || decide (((M (Fin.last (n + 1))).1 / 2) % 2 ≤ (M (Fin.last (n + 1))).1 / 4)) = true := by
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
      by_cases h1 : (q0.1 % 4) / 2 = 1
      · left; exact h1
      · right
        have h0 : (q0.1 % 4) / 2 = 0 := by omega
        rcases hcol1 with heq | ⟨r, _, hr2⟩
        · have := congrArg Fin.val (congrFun heq (Fin.last (n + 1))); unfold dec3 at this; dsimp at this; omega
        · by_cases hr : r.1 < n + 1
          · have h0r := hc10 h0 ⟨r.1, hr⟩
            have hreq : (⟨r.1, hr⟩ : Fin (n + 1)).castSucc = r := Fin.ext rfl
            rw [hreq] at h0r; unfold dec3 at hr2; simp only [Fin.lt_def] at hr2; dsimp at hr2; omega
          · have hreq : r = Fin.last (n + 1) := Fin.ext (by simp [Fin.last]; omega)
            rw [hreq] at hr2; unfold dec3 at hr2; simp only [Fin.lt_def] at hr2; dsimp at hr2; omega
    rw [if_pos (by rw [hc0_ok, hc1_ok]; rfl)]; dsimp only
    have hlt : (M (Fin.last (n + 1))).1 * 4 + ((if ((q0.1 % 4) % 2 == 1 || decide ((M (Fin.last (n + 1))).1 % 2 < ((M (Fin.last (n + 1))).1 / 2) % 2)) = true then 1 else 0) +
        2 * if ((q0.1 % 4) / 2 == 1 || decide (((M (Fin.last (n + 1))).1 / 2) % 2 < (M (Fin.last (n + 1))).1 / 4)) = true then 1 else 0) < 32 := by
      have := (M (Fin.last (n + 1))).2; split_ifs <;> omega
    rw [dif_pos hlt]; exact ⟨_, rfl⟩

private lemma lexRow3_iff_lex3Val (r1 r2 : Fin 8) :
    lexRow3 (dec3 r1 0) (dec3 r1 1) (dec3 r1 2) (dec3 r2 0) (dec3 r2 1) (dec3 r2 2) ↔
    lex3Val r1 ≤ lex3Val r2 := by
  revert r1 r2; unfold lexRow3 dec3 lex3Val; decide

private lemma symOf_eq_subVal (r1 r2 : Fin 8) (s : Fin 25) :
    symOf r1 r2 = s.1 ↔
    (decSym s 0 = subVal (dec3 r1 0) (dec3 r1 1) (dec3 r2 0) (dec3 r2 1) ∧
     decSym s 1 = subVal (dec3 r1 1) (dec3 r1 2) (dec3 r2 1) (dec3 r2 2)) := by
  revert r1 r2 s; decide



private lemma isValid_iff_runDFA (n : ℕ) (A : Fin n → Fin 25) :
    isValid n (fun r => decSym (A r)) ↔ (runDFA n A).1 ≠ 2 := by
  rw [← dfaMask_empty_iff]
  simp only [runDFA_iff_runNFA]
  constructor
  · rintro ⟨M, ⟨hMrow, hMcol0, hMcol1⟩, hMA⟩
    let M' : Fin (n + 1) → Fin 8 := fun r => enc3 (M r)
    have hdec : ∀ r, dec3 (M' r) = M r := fun r => dec3_enc3 (M r)
    have hrow' : ∀ r : Fin n, lex3Val (M' ⟨r.1, by omega⟩) ≤ lex3Val (M' ⟨r.1 + 1, by omega⟩) ∧
                              symOf (M' ⟨r.1, by omega⟩) (M' ⟨r.1 + 1, by omega⟩) = (A r).1 := by
      intro r
      constructor
      · rw [← lexRow3_iff_lex3Val, hdec, hdec]; exact hMrow r
      · rw [symOf_eq_subVal, hdec, hdec]
        exact ⟨hMA r 0, hMA r 1⟩
    have hcol0' : lexCol (n + 1) (fun r => dec3 (M' r) 0) (fun r => dec3 (M' r) 1) := by
      simp_rw [hdec]; exact hMcol0
    have hcol1' : lexCol (n + 1) (fun r => dec3 (M' r) 1) (fun r => dec3 (M' r) 2) := by
      simp_rw [hdec]; exact hMcol1
    obtain ⟨q, hq⟩ := runNFA_complete n A M' hrow' hcol0' hcol1'
    exact ⟨q, M', hq⟩
  · rintro ⟨q, M, hrun⟩
    obtain ⟨_, hc00, hc01, hc10, hc11, hrows⟩ := runNFA_sound n A M q hrun
    refine ⟨fun r => dec3 (M r), ⟨?_, ?_, ?_⟩, ?_⟩
    · intro r; rw [lexRow3_iff_lex3Val]; exact (hrows r).1
    · by_cases h0 : (q.1 % 4) % 2 = 0
      · left; funext r; apply Fin.ext; unfold dec3; dsimp; exact hc00 h0 r
      · right; obtain ⟨r, hr1, hr2⟩ := hc01 (by omega)
        refine ⟨r, fun j hj => by apply Fin.ext; unfold dec3; dsimp; exact hr1 j hj, by unfold dec3; simp only [Fin.lt_def]; dsimp; exact hr2⟩
    · by_cases h0 : (q.1 % 4) / 2 = 0
      · left; funext r; apply Fin.ext; unfold dec3; dsimp; exact hc10 h0 r
      · right; obtain ⟨r, hr1, hr2⟩ := hc11 (by omega)
        refine ⟨r, fun j hj => by apply Fin.ext; unfold dec3; dsimp; exact hr1 j hj, by unfold dec3; simp only [Fin.lt_def]; dsimp; exact hr2⟩
    · intro r c
      have hsub := (symOf_eq_subVal (M ⟨r.1, by omega⟩) (M ⟨r.1 + 1, by omega⟩) (A r)).mp (hrows r).2
      fin_cases c
      · exact hsub.1
      · exact hsub.2

private def dp : ℕ → Fin 25 → ℕ
  | 0, s => if s.1 = 0 then 1 else 0
  | n + 1, s' => ∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then dp n s else 0

private lemma dp_succ_eq (n : ℕ) (s' : Fin 25) :
    dp (n + 1) s' = ∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then dp n s else 0 := rfl

private def tbl_0 (s : Fin 25) : ℕ :=
  (if s.1 < 12 then (if s.1 < 6 then (if s.1 < 3 then (if s.1 < 1 then 1 else (if s.1 < 2 then 0 else 0)) else (if s.1 < 4 then 0 else (if s.1 < 5 then 0 else 0))) else (if s.1 < 9 then (if s.1 < 7 then 0 else (if s.1 < 8 then 0 else 0)) else (if s.1 < 10 then 0 else (if s.1 < 11 then 0 else 0)))) else (if s.1 < 18 then (if s.1 < 15 then (if s.1 < 13 then 0 else (if s.1 < 14 then 0 else 0)) else (if s.1 < 16 then 0 else (if s.1 < 17 then 0 else 0))) else (if s.1 < 21 then (if s.1 < 19 then 0 else (if s.1 < 20 then 0 else 0)) else (if s.1 < 23 then (if s.1 < 22 then 0 else 0) else (if s.1 < 24 then 0 else 0)))))
private def tbl_1 (s : Fin 25) : ℕ :=
  (if s.1 < 12 then (if s.1 < 6 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 1 else 15)) else (if s.1 < 4 then 2 else (if s.1 < 5 then 1 else 1))) else (if s.1 < 9 then (if s.1 < 7 then 1 else (if s.1 < 8 then 1 else 1)) else (if s.1 < 10 then 1 else (if s.1 < 11 then 1 else 0)))) else (if s.1 < 18 then (if s.1 < 15 then (if s.1 < 13 then 0 else (if s.1 < 14 then 0 else 0)) else (if s.1 < 16 then 0 else (if s.1 < 17 then 0 else 0))) else (if s.1 < 21 then (if s.1 < 19 then 0 else (if s.1 < 20 then 0 else 0)) else (if s.1 < 23 then (if s.1 < 22 then 0 else 0) else (if s.1 < 24 then 0 else 0)))))
private def tbl_2 (s : Fin 25) : ℕ :=
  (if s.1 < 12 then (if s.1 < 6 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 1 else 583)) else (if s.1 < 4 then 3 else (if s.1 < 5 then 0 else 0))) else (if s.1 < 9 then (if s.1 < 7 then 3 else (if s.1 < 8 then 0 else 3)) else (if s.1 < 10 then 4 else (if s.1 < 11 then 3 else 2)))) else (if s.1 < 18 then (if s.1 < 15 then (if s.1 < 13 then 3 else (if s.1 < 14 then 4 else 2)) else (if s.1 < 16 then 1 else (if s.1 < 17 then 3 else 1))) else (if s.1 < 21 then (if s.1 < 19 then 3 else (if s.1 < 20 then 2 else 4)) else (if s.1 < 23 then (if s.1 < 22 then 0 else 0) else (if s.1 < 24 then 0 else 0)))))
private def tbl_3 (s : Fin 25) : ℕ :=
  (if s.1 < 12 then (if s.1 < 6 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 1 else 15505)) else (if s.1 < 4 then 4 else (if s.1 < 5 then 0 else 0))) else (if s.1 < 9 then (if s.1 < 7 then 10 else (if s.1 < 8 then 0 else 4)) else (if s.1 < 10 then 9 else (if s.1 < 11 then 4 else 3)))) else (if s.1 < 18 then (if s.1 < 15 then (if s.1 < 13 then 6 else (if s.1 < 14 then 10 else 7)) else (if s.1 < 16 then 0 else (if s.1 < 17 then 15 else 0))) else (if s.1 < 21 then (if s.1 < 19 then 19 else (if s.1 < 20 then 6 else 15)) else (if s.1 < 23 then (if s.1 < 22 then 3 else 2) else (if s.1 < 24 then 1 else 1)))))
private def tbl_4 (s : Fin 25) : ℕ :=
  (if s.1 < 12 then (if s.1 < 6 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 1 else 390312)) else (if s.1 < 4 then 5 else (if s.1 < 5 then 0 else 0))) else (if s.1 < 9 then (if s.1 < 7 then 20 else (if s.1 < 8 then 0 else 5)) else (if s.1 < 10 then 20 else (if s.1 < 11 then 5 else 4)))) else (if s.1 < 18 then (if s.1 < 15 then (if s.1 < 13 then 10 else (if s.1 < 14 then 20 else 25)) else (if s.1 < 16 then 0 else (if s.1 < 17 then 57 else 0))) else (if s.1 < 21 then (if s.1 < 19 then 77 else (if s.1 < 20 then 10 else 46)) else (if s.1 < 23 then (if s.1 < 22 then 6 else 0) else (if s.1 < 24 then 0 else 2)))))
private def tbl_5 (s : Fin 25) : ℕ :=
  (if s.1 < 12 then (if s.1 < 6 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 1 else 9764896)) else (if s.1 < 4 then 6 else (if s.1 < 5 then 0 else 0))) else (if s.1 < 9 then (if s.1 < 7 then 35 else (if s.1 < 8 then 0 else 6)) else (if s.1 < 10 then 35 else (if s.1 < 11 then 6 else 5)))) else (if s.1 < 18 then (if s.1 < 15 then (if s.1 < 13 then 15 else (if s.1 < 14 then 35 else 55)) else (if s.1 < 16 then 0 else (if s.1 < 17 then 160 else 0))) else (if s.1 < 21 then (if s.1 < 19 then 239 else (if s.1 < 20 then 15 else 106)) else (if s.1 < 23 then (if s.1 < 22 then 10 else 0) else (if s.1 < 24 then 0 else 0)))))
private def tbl_6 (s : Fin 25) : ℕ :=
  (if s.1 < 12 then (if s.1 < 6 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 1 else 244139069)) else (if s.1 < 4 then 7 else (if s.1 < 5 then 0 else 0))) else (if s.1 < 9 then (if s.1 < 7 then 56 else (if s.1 < 8 then 0 else 7)) else (if s.1 < 10 then 56 else (if s.1 < 11 then 7 else 6)))) else (if s.1 < 18 then (if s.1 < 15 then (if s.1 < 13 then 21 else (if s.1 < 14 then 56 else 105)) else (if s.1 < 16 then 0 else (if s.1 < 17 then 371 else 0))) else (if s.1 < 21 then (if s.1 < 19 then 610 else (if s.1 < 20 then 21 else 217)) else (if s.1 < 23 then (if s.1 < 22 then 15 else 0) else (if s.1 < 24 then 0 else 0)))))
private def tbl_7 (s : Fin 25) : ℕ :=
  (if s.1 < 12 then (if s.1 < 6 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 1 else 6103512526)) else (if s.1 < 4 then 8 else (if s.1 < 5 then 0 else 0))) else (if s.1 < 9 then (if s.1 < 7 then 84 else (if s.1 < 8 then 0 else 8)) else (if s.1 < 10 then 84 else (if s.1 < 11 then 8 else 7)))) else (if s.1 < 18 then (if s.1 < 15 then (if s.1 < 13 then 28 else (if s.1 < 14 then 84 else 182)) else (if s.1 < 16 then 0 else (if s.1 < 17 then 770 else 0))) else (if s.1 < 21 then (if s.1 < 19 then 1380 else (if s.1 < 20 then 28 else 406)) else (if s.1 < 23 then (if s.1 < 22 then 21 else 0) else (if s.1 < 24 then 0 else 0)))))
private def tbl_8 (s : Fin 25) : ℕ :=
  (if s.1 < 12 then (if s.1 < 6 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 1 else 152587884807)) else (if s.1 < 4 then 9 else (if s.1 < 5 then 0 else 0))) else (if s.1 < 9 then (if s.1 < 7 then 120 else (if s.1 < 8 then 0 else 9)) else (if s.1 < 10 then 120 else (if s.1 < 11 then 9 else 8)))) else (if s.1 < 18 then (if s.1 < 15 then (if s.1 < 13 then 36 else (if s.1 < 14 then 120 else 294)) else (if s.1 < 16 then 0 else (if s.1 < 17 then 1470 else 0))) else (if s.1 < 21 then (if s.1 < 19 then 2850 else (if s.1 < 20 then 36 else 708)) else (if s.1 < 23 then (if s.1 < 22 then 28 else 0) else (if s.1 < 24 then 0 else 0)))))
private def tbl_9 (s : Fin 25) : ℕ :=
  (if s.1 < 12 then (if s.1 < 6 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 1 else 3814697255241)) else (if s.1 < 4 then 10 else (if s.1 < 5 then 0 else 0))) else (if s.1 < 9 then (if s.1 < 7 then 165 else (if s.1 < 8 then 0 else 10)) else (if s.1 < 10 then 165 else (if s.1 < 11 then 10 else 9)))) else (if s.1 < 18 then (if s.1 < 15 then (if s.1 < 13 then 45 else (if s.1 < 14 then 165 else 450)) else (if s.1 < 16 then 0 else (if s.1 < 17 then 2628 else 0))) else (if s.1 < 21 then (if s.1 < 19 then 5478 else (if s.1 < 20 then 45 else 1167)) else (if s.1 < 23 then (if s.1 < 22 then 36 else 0) else (if s.1 < 24 then 0 else 0)))))
private def tbl_10 (s : Fin 25) : ℕ :=
  (if s.1 < 12 then (if s.1 < 6 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 1 else 95367431622881)) else (if s.1 < 4 then 11 else (if s.1 < 5 then 0 else 0))) else (if s.1 < 9 then (if s.1 < 7 then 220 else (if s.1 < 8 then 0 else 11)) else (if s.1 < 10 then 220 else (if s.1 < 11 then 11 else 10)))) else (if s.1 < 18 then (if s.1 < 15 then (if s.1 < 13 then 55 else (if s.1 < 14 then 220 else 660)) else (if s.1 < 16 then 0 else (if s.1 < 17 then 4455 else 0))) else (if s.1 < 21 then (if s.1 < 19 then 9933 else (if s.1 < 20 then 55 else 1837)) else (if s.1 < 23 then (if s.1 < 22 then 45 else 0) else (if s.1 < 24 then 0 else 0)))))
private def tbl_11 (s : Fin 25) : ℕ :=
  (if s.1 < 12 then (if s.1 < 6 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 1 else 2384185790986427)) else (if s.1 < 4 then 12 else (if s.1 < 5 then 0 else 0))) else (if s.1 < 9 then (if s.1 < 7 then 286 else (if s.1 < 8 then 0 else 12)) else (if s.1 < 10 then 286 else (if s.1 < 11 then 12 else 11)))) else (if s.1 < 18 then (if s.1 < 15 then (if s.1 < 13 then 66 else (if s.1 < 14 then 286 else 935)) else (if s.1 < 16 then 0 else (if s.1 < 17 then 7227 else 0))) else (if s.1 < 21 then (if s.1 < 19 then 17160 else (if s.1 < 20 then 66 else 2783)) else (if s.1 < 23 then (if s.1 < 22 then 55 else 0) else (if s.1 < 24 then 0 else 0)))))
private def tbl_12 (s : Fin 25) : ℕ :=
  (if s.1 < 12 then (if s.1 < 6 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 1 else 59604644775344136)) else (if s.1 < 4 then 13 else (if s.1 < 5 then 0 else 0))) else (if s.1 < 9 then (if s.1 < 7 then 364 else (if s.1 < 8 then 0 else 13)) else (if s.1 < 10 then 364 else (if s.1 < 11 then 13 else 12)))) else (if s.1 < 18 then (if s.1 < 15 then (if s.1 < 13 then 78 else (if s.1 < 14 then 364 else 1287)) else (if s.1 < 16 then 0 else (if s.1 < 17 then 11297 else 0))) else (if s.1 < 21 then (if s.1 < 19 then 28457 else (if s.1 < 20 then 78 else 4082)) else (if s.1 < 23 then (if s.1 < 22 then 66 else 0) else (if s.1 < 24 then 0 else 0)))))
private def tbl_13 (s : Fin 25) : ℕ :=
  (if s.1 < 12 then (if s.1 < 6 then (if s.1 < 3 then (if s.1 < 1 then 0 else (if s.1 < 2 then 1 else 1490116119384693718)) else (if s.1 < 4 then 14 else (if s.1 < 5 then 0 else 0))) else (if s.1 < 9 then (if s.1 < 7 then 455 else (if s.1 < 8 then 0 else 14)) else (if s.1 < 10 then 455 else (if s.1 < 11 then 14 else 13)))) else (if s.1 < 18 then (if s.1 < 15 then (if s.1 < 13 then 91 else (if s.1 < 14 then 455 else 1729)) else (if s.1 < 16 then 0 else (if s.1 < 17 then 17108 else 0))) else (if s.1 < 21 then (if s.1 < 19 then 45565 else (if s.1 < 20 then 91 else 5824)) else (if s.1 < 23 then (if s.1 < 22 then 78 else 0) else (if s.1 < 24 then 0 else 0)))))

private lemma dp_eq_tbl_0 (s : Fin 25) : dp 0 s = tbl_0 s := by revert s; decide
private lemma dp_step_ok_1 : ∀ s' : Fin 25,
    (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_0 s else 0) = tbl_1 s' := by decide

private lemma dp_eq_tbl_1 (s' : Fin 25) : dp 1 s' = tbl_1 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then dp 0 s else 0) =
      ∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_0 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_0]
  rw [h1]; exact dp_step_ok_1 s' 
private lemma dp_step_ok_2 : ∀ s' : Fin 25,
    (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_1 s else 0) = tbl_2 s' := by decide

private lemma dp_eq_tbl_2 (s' : Fin 25) : dp 2 s' = tbl_2 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then dp 1 s else 0) =
      ∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_1 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_1]
  rw [h1]; exact dp_step_ok_2 s' 
private lemma dp_step_ok_3 : ∀ s' : Fin 25,
    (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_2 s else 0) = tbl_3 s' := by decide

private lemma dp_eq_tbl_3 (s' : Fin 25) : dp 3 s' = tbl_3 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then dp 2 s else 0) =
      ∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_2 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_2]
  rw [h1]; exact dp_step_ok_3 s' 
private lemma dp_step_ok_4 : ∀ s' : Fin 25,
    (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_3 s else 0) = tbl_4 s' := by decide

private lemma dp_eq_tbl_4 (s' : Fin 25) : dp 4 s' = tbl_4 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then dp 3 s else 0) =
      ∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_3 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_3]
  rw [h1]; exact dp_step_ok_4 s' 
private lemma dp_step_ok_5 : ∀ s' : Fin 25,
    (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_4 s else 0) = tbl_5 s' := by decide

private lemma dp_eq_tbl_5 (s' : Fin 25) : dp 5 s' = tbl_5 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then dp 4 s else 0) =
      ∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_4 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_4]
  rw [h1]; exact dp_step_ok_5 s' 
private lemma dp_step_ok_6 : ∀ s' : Fin 25,
    (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_5 s else 0) = tbl_6 s' := by decide

private lemma dp_eq_tbl_6 (s' : Fin 25) : dp 6 s' = tbl_6 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then dp 5 s else 0) =
      ∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_5 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_5]
  rw [h1]; exact dp_step_ok_6 s' 
private lemma dp_step_ok_7 : ∀ s' : Fin 25,
    (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_6 s else 0) = tbl_7 s' := by decide

private lemma dp_eq_tbl_7 (s' : Fin 25) : dp 7 s' = tbl_7 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then dp 6 s else 0) =
      ∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_6 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_6]
  rw [h1]; exact dp_step_ok_7 s' 
private lemma dp_step_ok_8 : ∀ s' : Fin 25,
    (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_7 s else 0) = tbl_8 s' := by decide

private lemma dp_eq_tbl_8 (s' : Fin 25) : dp 8 s' = tbl_8 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then dp 7 s else 0) =
      ∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_7 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_7]
  rw [h1]; exact dp_step_ok_8 s' 
private lemma dp_step_ok_9 : ∀ s' : Fin 25,
    (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_8 s else 0) = tbl_9 s' := by decide

private lemma dp_eq_tbl_9 (s' : Fin 25) : dp 9 s' = tbl_9 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then dp 8 s else 0) =
      ∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_8 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_8]
  rw [h1]; exact dp_step_ok_9 s' 
private lemma dp_step_ok_10 : ∀ s' : Fin 25,
    (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_9 s else 0) = tbl_10 s' := by decide

private lemma dp_eq_tbl_10 (s' : Fin 25) : dp 10 s' = tbl_10 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then dp 9 s else 0) =
      ∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_9 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_9]
  rw [h1]; exact dp_step_ok_10 s' 
private lemma dp_step_ok_11 : ∀ s' : Fin 25,
    (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_10 s else 0) = tbl_11 s' := by decide

private lemma dp_eq_tbl_11 (s' : Fin 25) : dp 11 s' = tbl_11 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then dp 10 s else 0) =
      ∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_10 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_10]
  rw [h1]; exact dp_step_ok_11 s' 
private lemma dp_step_ok_12 : ∀ s' : Fin 25,
    (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_11 s else 0) = tbl_12 s' := by decide

private lemma dp_eq_tbl_12 (s' : Fin 25) : dp 12 s' = tbl_12 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then dp 11 s else 0) =
      ∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_11 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_11]
  rw [h1]; exact dp_step_ok_12 s' 
private lemma dp_step_ok_13 : ∀ s' : Fin 25,
    (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_12 s else 0) = tbl_13 s' := by decide

private lemma dp_eq_tbl_13 (s' : Fin 25) : dp 13 s' = tbl_13 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then dp 12 s else 0) =
      ∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then tbl_12 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_12]
  rw [h1]; exact dp_step_ok_13 s' 

private lemma dp_rec_tbl_ok : ∀ s : Fin 25, s.1 ≠ 2 → tbl_13 s + 28 * tbl_11 s + 70 * tbl_9 s + 28 * tbl_7 s + tbl_5 s = 8 * tbl_12 s + 56 * tbl_10 s + 56 * tbl_8 s + 8 * tbl_6 s := by decide

private lemma dp_rec_base : ∀ s : Fin 25, s.1 ≠ 2 → dp 13 s + 28 * dp 11 s + 70 * dp 9 s + 28 * dp 7 s + dp 5 s = 8 * dp 12 s + 56 * dp 10 s + 56 * dp 8 s + 8 * dp 6 s := by
  intro s hs; rw [dp_eq_tbl_5, dp_eq_tbl_6, dp_eq_tbl_7, dp_eq_tbl_8, dp_eq_tbl_9, dp_eq_tbl_10, dp_eq_tbl_11, dp_eq_tbl_12, dp_eq_tbl_13]; exact dp_rec_tbl_ok s hs

private lemma sum_lin (f0 f1 f2 f3 f4 f5 f6 f7 f8 : Fin 25 → ℕ) (s' : Fin 25) (hs' : s'.1 ≠ 2)
    (h : ∀ s : Fin 25, s.1 ≠ 2 → f8 s + 28 * f6 s + 70 * f4 s + 28 * f2 s + f0 s = 8 * f7 s + 56 * f5 s + 56 * f3 s + 8 * f1 s) :
    (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then f8 s else 0) + 28 * (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then f6 s else 0) + 70 * (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then f4 s else 0) + 28 * (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then f2 s else 0) + (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then f0 s else 0) = 8 * (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then f7 s else 0) + 56 * (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then f5 s else 0) + 56 * (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then f3 s else 0) + 8 * (∑ s : Fin 25, ∑ sym : Fin 25, if dfaTrans s sym = s' then f1 s else 0) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro sym _
  by_cases htr : dfaTrans s sym = s'
  · simp only [htr, ↓reduceIte]
    have hs : s.1 ≠ 2 := by
      intro heq
      have h1 : s = ⟨2, by omega⟩ := Fin.ext heq
      have h2 : dfaTrans s sym = ⟨2, by omega⟩ := h1 ▸ dfaTrans_empty sym
      rw [htr] at h2; exact hs' (congrArg Fin.val h2)
    exact h s hs
  · simp [htr]

private lemma dp_rec (m : ℕ) : ∀ s : Fin 25, s.1 ≠ 2 → dp (m + 13) s + 28 * dp (m + 11) s + 70 * dp (m + 9) s + 28 * dp (m + 7) s + dp (m + 5) s = 8 * dp (m + 12) s + 56 * dp (m + 10) s + 56 * dp (m + 8) s + 8 * dp (m + 6) s := by
  induction m with
  | zero => exact dp_rec_base
  | succ m ih =>
    intro s' hs'; rw [dp_succ_eq (m + 5), dp_succ_eq (m + 6), dp_succ_eq (m + 7), dp_succ_eq (m + 8), dp_succ_eq (m + 9), dp_succ_eq (m + 10), dp_succ_eq (m + 11), dp_succ_eq (m + 12), dp_succ_eq (m + 13)]
    exact sum_lin (dp (m + 5)) (dp (m + 6)) (dp (m + 7)) (dp (m + 8)) (dp (m + 9)) (dp (m + 10)) (dp (m + 11)) (dp (m + 12)) (dp (m + 13)) s' hs' ih

private lemma card_runDFA (n : ℕ) : ∀ s : Fin 25, Fintype.card {A : Fin n → Fin 25 // runDFA n A = s} = dp n s := by
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
    let φ : (Σ s : Fin 25, Σ sym : Fin 25, {A : Fin n → Fin 25 // runDFA n A = s ∧ dfaTrans s sym = s'}) →
        {A : Fin (n + 1) → Fin 25 // runDFA (n + 1) A = s'} :=
      fun ⟨s, sym, ⟨A, hA, htr⟩⟩ =>
        ⟨Fin.snoc A sym, by
          unfold runDFA
          have hc : (fun i : Fin n => (Fin.snoc A sym : Fin (n + 1) → Fin 25) i.castSucc) = A := by
            funext i; exact Fin.snoc_castSucc _ _ i
          rw [hc, hA, Fin.snoc_last]; exact htr⟩
    have hbij : Function.Bijective φ := by
      constructor
      · rintro ⟨sa, syma, ⟨Aa, hAa, _⟩⟩ ⟨sb, symb, ⟨Ab, hAb, _⟩⟩ heq
        have hfun : (Fin.snoc Aa syma : Fin (n + 1) → Fin 25) = Fin.snoc Ab symb := congrArg Subtype.val heq
        have hAeq : Aa = Ab := by funext i; simpa using congrFun hfun i.castSucc
        have hsymeq : syma = symb := by simpa using congrFun hfun (Fin.last n)
        subst hAeq; subst hsymeq
        have hseq : sa = sb := hAa.symm.trans hAb
        subst hseq; rfl
      · rintro ⟨A, hA⟩
        let A0 : Fin n → Fin 25 := fun i => A i.castSucc
        let s := runDFA n A0
        let sym := A (Fin.last n)
        refine ⟨⟨s, sym, ⟨A0, rfl, hA⟩⟩, ?_⟩
        apply Subtype.ext; funext i; refine Fin.lastCases ?_ ?_ i
        · dsimp [φ, sym]; rw [Fin.snoc_last]
        · intro j; dsimp [φ, A0]; rw [Fin.snoc_castSucc]
    rw [Fintype.card_congr (Equiv.ofBijective φ hbij).symm, Fintype.card_sigma]
    apply Finset.sum_congr rfl; intro s _
    rw [Fintype.card_sigma]
    apply Finset.sum_congr rfl; intro sym _
    by_cases htr : dfaTrans s sym = s'
    · rw [if_pos htr, ← ih s]
      refine Fintype.card_congr ⟨fun ⟨A, h1, _⟩ => ⟨A, h1⟩, fun ⟨A, h1⟩ => ⟨A, h1, htr⟩, fun ⟨_, _, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩
    · rw [if_neg htr, Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨_, _, h⟩ => htr h⟩

private lemma a_eq_sum_dp (n : ℕ) (hn : 1 ≤ n) :
    a n = ∑ s : Fin 25, if s.1 ≠ 2 then dp n s else 0 := by
  unfold a; rw [if_neg (by omega)]
  let φ : (Σ s : Fin 25, {A : Fin n → Fin 25 // runDFA n A = s ∧ s.1 ≠ 2}) →
      {A : Fin n → Fin 2 → Fin 5 // isValid n A} :=
    fun ⟨s, ⟨A, hA, hs⟩⟩ =>
      ⟨fun r => decSym (A r), (isValid_iff_runDFA n A).mpr (hA.symm ▸ hs)⟩
  have hbij : Function.Bijective φ := by
    constructor
    · rintro ⟨sa, ⟨Aa, hAa, _⟩⟩ ⟨sb, ⟨Ab, hAb, _⟩⟩ heq
      have hfun := congrArg Subtype.val heq
      have hAeq : Aa = Ab := by
        funext r
        have h := congrFun hfun r
        have h0 : (decSym (Aa r) 0) = decSym (Ab r) 0 := congrFun h 0
        have h1 : (decSym (Aa r) 1) = decSym (Ab r) 1 := congrFun h 1
        unfold decSym at h0 h1; simp only [Fin.ext_iff] at h0 h1; dsimp at h0 h1
        have ha := (Aa r).2; have hb := (Ab r).2
        apply Fin.ext; omega
      subst hAeq
      have hseq : sa = sb := hAa.symm.trans hAb
      subst hseq; rfl
    · rintro ⟨A, hA⟩
      have ⟨M, _, hMA⟩ := hA
      let A' : Fin n → Fin 25 := fun r => encSym (A r)
      have hdecA : (fun r => decSym (A' r)) = A := by
        funext r c
        fin_cases c <;> (apply Fin.ext; unfold A' encSym decSym; dsimp; have := (A r 0).2; have := (A r 1).2; omega)
      have hs : (runDFA n A').1 ≠ 2 := (isValid_iff_runDFA n A').mp (hdecA.symm ▸ hA)
      refine ⟨⟨runDFA n A', ⟨A', rfl, hs⟩⟩, ?_⟩
      apply Subtype.ext; exact hdecA
  rw [Fintype.card_congr (Equiv.ofBijective φ hbij).symm, Fintype.card_sigma]
  apply Finset.sum_congr rfl; intro s _
  by_cases hs : s.1 ≠ 2
  · rw [if_pos hs, ← card_runDFA n s]
    refine Fintype.card_congr ⟨fun ⟨A, h1, _⟩ => ⟨A, h1⟩, fun ⟨A, h1⟩ => ⟨A, h1, hs⟩, fun ⟨_, _, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩
  · rw [if_neg hs, Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨_, _, h⟩ => hs h⟩

private lemma a_rec_m (m : ℕ) : a (m + 13) + 28 * a (m + 11) + 70 * a (m + 9) + 28 * a (m + 7) + a (m + 5) = 8 * a (m + 12) + 56 * a (m + 10) + 56 * a (m + 8) + 8 * a (m + 6) := by
  rw [a_eq_sum_dp (m + 5) (by omega), a_eq_sum_dp (m + 6) (by omega), a_eq_sum_dp (m + 7) (by omega), a_eq_sum_dp (m + 8) (by omega), a_eq_sum_dp (m + 9) (by omega), a_eq_sum_dp (m + 10) (by omega), a_eq_sum_dp (m + 11) (by omega), a_eq_sum_dp (m + 12) (by omega), a_eq_sum_dp (m + 13) (by omega)]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s _
  by_cases hs : s.1 ≠ 2
  · simp only [if_pos hs]; exact dp_rec m s hs
  · simp only [if_neg hs, mul_zero, add_zero]

private lemma a_zero : a 0 = 0 := by unfold a; simp
private lemma a_sum_ok_1 : (∑ s : Fin 25, if s.1 ≠ 2 then tbl_1 s else 0) = 10 := by decide
private lemma a_val_1 : a 1 = 10 := by
  rw [a_eq_sum_dp 1 (by omega)]
  have h : (∑ s : Fin 25, if s.1 ≠ 2 then dp 1 s else 0) =
      ∑ s : Fin 25, if s.1 ≠ 2 then tbl_1 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_1]
  rw [h]; exact a_sum_ok_1
private lemma a_sum_ok_2 : (∑ s : Fin 25, if s.1 ≠ 2 then tbl_2 s else 0) = 42 := by decide
private lemma a_val_2 : a 2 = 42 := by
  rw [a_eq_sum_dp 2 (by omega)]
  have h : (∑ s : Fin 25, if s.1 ≠ 2 then dp 2 s else 0) =
      ∑ s : Fin 25, if s.1 ≠ 2 then tbl_2 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_2]
  rw [h]; exact a_sum_ok_2
private lemma a_sum_ok_3 : (∑ s : Fin 25, if s.1 ≠ 2 then tbl_3 s else 0) = 120 := by decide
private lemma a_val_3 : a 3 = 120 := by
  rw [a_eq_sum_dp 3 (by omega)]
  have h : (∑ s : Fin 25, if s.1 ≠ 2 then dp 3 s else 0) =
      ∑ s : Fin 25, if s.1 ≠ 2 then tbl_3 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_3]
  rw [h]; exact a_sum_ok_3
private lemma a_sum_ok_4 : (∑ s : Fin 25, if s.1 ≠ 2 then tbl_4 s else 0) = 313 := by decide
private lemma a_val_4 : a 4 = 313 := by
  rw [a_eq_sum_dp 4 (by omega)]
  have h : (∑ s : Fin 25, if s.1 ≠ 2 then dp 4 s else 0) =
      ∑ s : Fin 25, if s.1 ≠ 2 then tbl_4 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_4]
  rw [h]; exact a_sum_ok_4
private lemma a_sum_ok_5 : (∑ s : Fin 25, if s.1 ≠ 2 then tbl_5 s else 0) = 729 := by decide
private lemma a_val_5 : a 5 = 729 := by
  rw [a_eq_sum_dp 5 (by omega)]
  have h : (∑ s : Fin 25, if s.1 ≠ 2 then dp 5 s else 0) =
      ∑ s : Fin 25, if s.1 ≠ 2 then tbl_5 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_5]
  rw [h]; exact a_sum_ok_5
private lemma a_sum_ok_6 : (∑ s : Fin 25, if s.1 ≠ 2 then tbl_6 s else 0) = 1556 := by decide
private lemma a_val_6 : a 6 = 1556 := by
  rw [a_eq_sum_dp 6 (by omega)]
  have h : (∑ s : Fin 25, if s.1 ≠ 2 then dp 6 s else 0) =
      ∑ s : Fin 25, if s.1 ≠ 2 then tbl_6 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_6]
  rw [h]; exact a_sum_ok_6
private lemma a_sum_ok_7 : (∑ s : Fin 25, if s.1 ≠ 2 then tbl_7 s else 0) = 3099 := by decide
private lemma a_val_7 : a 7 = 3099 := by
  rw [a_eq_sum_dp 7 (by omega)]
  have h : (∑ s : Fin 25, if s.1 ≠ 2 then dp 7 s else 0) =
      ∑ s : Fin 25, if s.1 ≠ 2 then tbl_7 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_7]
  rw [h]; exact a_sum_ok_7
private lemma a_sum_ok_8 : (∑ s : Fin 25, if s.1 ≠ 2 then tbl_8 s else 0) = 5818 := by decide
private lemma a_val_8 : a 8 = 5818 := by
  rw [a_eq_sum_dp 8 (by omega)]
  have h : (∑ s : Fin 25, if s.1 ≠ 2 then dp 8 s else 0) =
      ∑ s : Fin 25, if s.1 ≠ 2 then tbl_8 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_8]
  rw [h]; exact a_sum_ok_8
private lemma a_sum_ok_9 : (∑ s : Fin 25, if s.1 ≠ 2 then tbl_9 s else 0) = 10384 := by decide
private lemma a_val_9 : a 9 = 10384 := by
  rw [a_eq_sum_dp 9 (by omega)]
  have h : (∑ s : Fin 25, if s.1 ≠ 2 then dp 9 s else 0) =
      ∑ s : Fin 25, if s.1 ≠ 2 then tbl_9 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_9]
  rw [h]; exact a_sum_ok_9
private lemma a_sum_ok_10 : (∑ s : Fin 25, if s.1 ≠ 2 then tbl_10 s else 0) = 17744 := by decide
private lemma a_val_10 : a 10 = 17744 := by
  rw [a_eq_sum_dp 10 (by omega)]
  have h : (∑ s : Fin 25, if s.1 ≠ 2 then dp 10 s else 0) =
      ∑ s : Fin 25, if s.1 ≠ 2 then tbl_10 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_10]
  rw [h]; exact a_sum_ok_10
private lemma a_sum_ok_11 : (∑ s : Fin 25, if s.1 ≠ 2 then tbl_11 s else 0) = 29198 := by decide
private lemma a_val_11 : a 11 = 29198 := by
  rw [a_eq_sum_dp 11 (by omega)]
  have h : (∑ s : Fin 25, if s.1 ≠ 2 then dp 11 s else 0) =
      ∑ s : Fin 25, if s.1 ≠ 2 then tbl_11 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_11]
  rw [h]; exact a_sum_ok_11
private lemma a_sum_ok_12 : (∑ s : Fin 25, if s.1 ≠ 2 then tbl_12 s else 0) = 46489 := by decide
private lemma a_val_12 : a 12 = 46489 := by
  rw [a_eq_sum_dp 12 (by omega)]
  have h : (∑ s : Fin 25, if s.1 ≠ 2 then dp 12 s else 0) =
      ∑ s : Fin 25, if s.1 ≠ 2 then tbl_12 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_12]
  rw [h]; exact a_sum_ok_12
private lemma a_sum_ok_13 : (∑ s : Fin 25, if s.1 ≠ 2 then tbl_13 s else 0) = 71907 := by decide
private lemma a_val_13 : a 13 = 71907 := by
  rw [a_eq_sum_dp 13 (by omega)]
  have h : (∑ s : Fin 25, if s.1 ≠ 2 then dp 13 s else 0) =
      ∑ s : Fin 25, if s.1 ≠ 2 then tbl_13 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_13]
  rw [h]; exact a_sum_ok_13

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

theorem solution : type_of% @OMA.S_oeis_a226988.main := by
  have hrec : ∀ n : ℕ, 12 < n → (a n : ℤ) = 8 * (a (n - 1) : ℤ) - 28 * (a (n - 2) : ℤ) + 56 * (a (n - 3) : ℤ) - 70 * (a (n - 4) : ℤ) + 56 * (a (n - 5) : ℤ) - 28 * (a (n - 6) : ℤ) + 8 * (a (n - 7) : ℤ) - (a (n - 8) : ℤ) := by
    intro n hn
    have h := a_rec_m (n - 13)
    simp only [show n - 13 + 13 = n by omega, show n - 13 + 12 = n - 1 by omega, show n - 13 + 11 = n - 2 by omega, show n - 13 + 10 = n - 3 by omega, show n - 13 + 9 = n - 4 by omega, show n - 13 + 8 = n - 5 by omega, show n - 13 + 7 = n - 6 by omega, show n - 13 + 6 = n - 7 by omega, show n - 13 + 5 = n - 8 by omega] at h
    omega
  refine ⟨?_, hrec⟩
  ext n
  have hexp : (1 - (PowerSeries.X : PowerSeries ℚ)) ^ 8 = 1 - PowerSeries.C 8 * PowerSeries.X ^ 1 + PowerSeries.C 28 * PowerSeries.X ^ 2 - PowerSeries.C 56 * PowerSeries.X ^ 3 + PowerSeries.C 70 * PowerSeries.X ^ 4 - PowerSeries.C 56 * PowerSeries.X ^ 5 + PowerSeries.C 28 * PowerSeries.X ^ 6 - PowerSeries.C 8 * PowerSeries.X ^ 7 + PowerSeries.X ^ 8 := by
    simp only [map_ofNat]; ring
  rw [hexp]
  have hR : (PowerSeries.X : PowerSeries ℚ) * (10 - 38 * PowerSeries.X + 64 * PowerSeries.X ^ 2 - 31 * PowerSeries.X ^ 3 - 67 * PowerSeries.X ^ 4 + 148 * PowerSeries.X ^ 5 - 137 * PowerSeries.X ^ 6 + 56 * PowerSeries.X ^ 7 + 12 * PowerSeries.X ^ 8 - 26 * PowerSeries.X ^ 9 + 12 * PowerSeries.X ^ 10 - 2 * PowerSeries.X ^ 11) = PowerSeries.C 10 * PowerSeries.X ^ 1 - PowerSeries.C 38 * PowerSeries.X ^ 2 + PowerSeries.C 64 * PowerSeries.X ^ 3 - PowerSeries.C 31 * PowerSeries.X ^ 4 - PowerSeries.C 67 * PowerSeries.X ^ 5 + PowerSeries.C 148 * PowerSeries.X ^ 6 - PowerSeries.C 137 * PowerSeries.X ^ 7 + PowerSeries.C 56 * PowerSeries.X ^ 8 + PowerSeries.C 12 * PowerSeries.X ^ 9 - PowerSeries.C 26 * PowerSeries.X ^ 10 + PowerSeries.C 12 * PowerSeries.X ^ 11 - PowerSeries.C 2 * PowerSeries.X ^ 12 := by
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
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m
  · simp [a_zero]
  · simp [a_zero, a_val_1]
  · simp [a_zero, a_val_1, a_val_2]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8]; norm_num
  · simp [a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9]; norm_num
  · simp [a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9, a_val_10]; norm_num
  · simp [a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9, a_val_10, a_val_11]; norm_num
  · simp [a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9, a_val_10, a_val_11, a_val_12]; norm_num
  · simp only [Nat.add_assoc, Nat.reduceAdd, show 1 ≤ m + 13 by omega, show 2 ≤ m + 13 by omega, show 3 ≤ m + 13 by omega, show 4 ≤ m + 13 by omega, show 5 ≤ m + 13 by omega, show 6 ≤ m + 13 by omega, show 7 ≤ m + 13 by omega, show 8 ≤ m + 13 by omega, ↓reduceIte,
      show m + 13 - 1 = m + 12 by omega, show m + 13 - 2 = m + 11 by omega, show m + 13 - 3 = m + 10 by omega, show m + 13 - 4 = m + 9 by omega, show m + 13 - 5 = m + 8 by omega, show m + 13 - 6 = m + 7 by omega, show m + 13 - 7 = m + 6 by omega, show m + 13 - 8 = m + 5 by omega, show ¬(m + 13 = 1) by omega, show ¬(m + 13 = 2) by omega, show ¬(m + 13 = 3) by omega, show ¬(m + 13 = 4) by omega, show ¬(m + 13 = 5) by omega, show ¬(m + 13 = 6) by omega, show ¬(m + 13 = 7) by omega, show ¬(m + 13 = 8) by omega, show ¬(m + 13 = 9) by omega, show ¬(m + 13 = 10) by omega, show ¬(m + 13 = 11) by omega, show ¬(m + 13 = 12) by omega]
    have hr := hrec (m + 13) (by omega)
    simp only [show m + 13 - 1 = m + 12 by omega, show m + 13 - 2 = m + 11 by omega, show m + 13 - 3 = m + 10 by omega, show m + 13 - 4 = m + 9 by omega, show m + 13 - 5 = m + 8 by omega, show m + 13 - 6 = m + 7 by omega, show m + 13 - 7 = m + 6 by omega, show m + 13 - 8 = m + 5 by omega] at hr
    have hrq : (a (m + 13) : ℚ) = 8 * (a (m + 12) : ℚ) - 28 * (a (m + 11) : ℚ) + 56 * (a (m + 10) : ℚ) - 70 * (a (m + 9) : ℚ) + 56 * (a (m + 8) : ℚ) - 28 * (a (m + 7) : ℚ) + 8 * (a (m + 6) : ℚ) - (a (m + 5) : ℚ) := by exact_mod_cast hr
    linarith

end OMA.P_oeis_a226988

theorem OMA.solution : type_of% @OMA.S_oeis_a226988.main :=
  OMA.P_oeis_a226988.solution
