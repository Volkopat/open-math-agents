import OMAStatements.S_mo_408235
import Mathlib

open OMA.S_mo_408235

def mo408235_tab : List (List ℕ) := [[1, 4, 9, 16, 25], [3, 8, 15, 24], [7, 14, 23], [1, 6, 13, 22], [5, 12, 21, 32], [4, 11, 20, 31], [3, 10, 19, 30], [2, 9, 18, 29], [1, 17, 28], [7, 16, 27], [6, 15, 26], [5, 14, 25], [4, 13, 24], [3, 12, 23], [2, 11, 22], [1, 10, 21], [9, 20], [8, 19, 32], [7, 31], [6, 17, 30], [5, 16, 29], [4, 15, 28], [3, 14, 27], [2, 13, 26], [1, 12, 25], [11, 24], [10, 23], [9, 22], [8, 21], [7, 20], [6, 19], [5, 18], [4, 17]]

def mo408235_nb (x : ℕ) : List ℕ := mo408235_tab.getD x []

def mo408235_B : Fin 32 → ℕ := ![32, 4, 21, 28, 8, 1, 15, 10, 26, 23, 2, 14, 22, 27, 9, 16, 20, 29, 7, 18, 31, 5, 11, 25, 24, 12, 13, 3, 6, 30, 19, 17]

def mo408235_B2 : Fin 32 → ℕ := ![32, 17, 19, 30, 6, 3, 13, 12, 24, 25, 11, 5, 31, 18, 7, 29, 20, 16, 9, 27, 22, 14, 2, 23, 26, 10, 15, 1, 8, 28, 21, 4]

def mo408235_L31 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 : ℕ) : Bool :=
  (mo408235_nb a30).all (fun a31 => !(decide (a31 ≠ a0) && decide (a31 ≠ a1) && decide (a31 ≠ a2) && decide (a31 ≠ a3) && decide (a31 ≠ a4) && decide (a31 ≠ a5) && decide (a31 ≠ a6) && decide (a31 ≠ a7) && decide (a31 ≠ a8) && decide (a31 ≠ a9) && decide (a31 ≠ a10) && decide (a31 ≠ a11) && decide (a31 ≠ a12) && decide (a31 ≠ a13) && decide (a31 ≠ a14) && decide (a31 ≠ a15) && decide (a31 ≠ a16) && decide (a31 ≠ a17) && decide (a31 ≠ a18) && decide (a31 ≠ a19) && decide (a31 ≠ a20) && decide (a31 ≠ a21) && decide (a31 ≠ a22) && decide (a31 ≠ a23) && decide (a31 ≠ a24) && decide (a31 ≠ a25) && decide (a31 ≠ a26) && decide (a31 ≠ a27) && decide (a31 ≠ a28) && decide (a31 ≠ a29) && decide (a31 ≠ a30)) || (!(decide (IsSquare (a31 + a0))) || decide ((![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31] : Fin 32 → ℕ) = mo408235_B ∨ (![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31] : Fin 32 → ℕ) = mo408235_B2)))

def mo408235_L30 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 : ℕ) : Bool :=
  (mo408235_nb a29).all (fun a30 => !(decide (a30 ≠ a0) && decide (a30 ≠ a1) && decide (a30 ≠ a2) && decide (a30 ≠ a3) && decide (a30 ≠ a4) && decide (a30 ≠ a5) && decide (a30 ≠ a6) && decide (a30 ≠ a7) && decide (a30 ≠ a8) && decide (a30 ≠ a9) && decide (a30 ≠ a10) && decide (a30 ≠ a11) && decide (a30 ≠ a12) && decide (a30 ≠ a13) && decide (a30 ≠ a14) && decide (a30 ≠ a15) && decide (a30 ≠ a16) && decide (a30 ≠ a17) && decide (a30 ≠ a18) && decide (a30 ≠ a19) && decide (a30 ≠ a20) && decide (a30 ≠ a21) && decide (a30 ≠ a22) && decide (a30 ≠ a23) && decide (a30 ≠ a24) && decide (a30 ≠ a25) && decide (a30 ≠ a26) && decide (a30 ≠ a27) && decide (a30 ≠ a28) && decide (a30 ≠ a29)) || mo408235_L31 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30)

def mo408235_L29 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 : ℕ) : Bool :=
  (mo408235_nb a28).all (fun a29 => !(decide (a29 ≠ a0) && decide (a29 ≠ a1) && decide (a29 ≠ a2) && decide (a29 ≠ a3) && decide (a29 ≠ a4) && decide (a29 ≠ a5) && decide (a29 ≠ a6) && decide (a29 ≠ a7) && decide (a29 ≠ a8) && decide (a29 ≠ a9) && decide (a29 ≠ a10) && decide (a29 ≠ a11) && decide (a29 ≠ a12) && decide (a29 ≠ a13) && decide (a29 ≠ a14) && decide (a29 ≠ a15) && decide (a29 ≠ a16) && decide (a29 ≠ a17) && decide (a29 ≠ a18) && decide (a29 ≠ a19) && decide (a29 ≠ a20) && decide (a29 ≠ a21) && decide (a29 ≠ a22) && decide (a29 ≠ a23) && decide (a29 ≠ a24) && decide (a29 ≠ a25) && decide (a29 ≠ a26) && decide (a29 ≠ a27) && decide (a29 ≠ a28)) || mo408235_L30 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29)

def mo408235_L28 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 : ℕ) : Bool :=
  (mo408235_nb a27).all (fun a28 => !(decide (a28 ≠ a0) && decide (a28 ≠ a1) && decide (a28 ≠ a2) && decide (a28 ≠ a3) && decide (a28 ≠ a4) && decide (a28 ≠ a5) && decide (a28 ≠ a6) && decide (a28 ≠ a7) && decide (a28 ≠ a8) && decide (a28 ≠ a9) && decide (a28 ≠ a10) && decide (a28 ≠ a11) && decide (a28 ≠ a12) && decide (a28 ≠ a13) && decide (a28 ≠ a14) && decide (a28 ≠ a15) && decide (a28 ≠ a16) && decide (a28 ≠ a17) && decide (a28 ≠ a18) && decide (a28 ≠ a19) && decide (a28 ≠ a20) && decide (a28 ≠ a21) && decide (a28 ≠ a22) && decide (a28 ≠ a23) && decide (a28 ≠ a24) && decide (a28 ≠ a25) && decide (a28 ≠ a26) && decide (a28 ≠ a27)) || mo408235_L29 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28)

def mo408235_L27 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 : ℕ) : Bool :=
  (mo408235_nb a26).all (fun a27 => !(decide (a27 ≠ a0) && decide (a27 ≠ a1) && decide (a27 ≠ a2) && decide (a27 ≠ a3) && decide (a27 ≠ a4) && decide (a27 ≠ a5) && decide (a27 ≠ a6) && decide (a27 ≠ a7) && decide (a27 ≠ a8) && decide (a27 ≠ a9) && decide (a27 ≠ a10) && decide (a27 ≠ a11) && decide (a27 ≠ a12) && decide (a27 ≠ a13) && decide (a27 ≠ a14) && decide (a27 ≠ a15) && decide (a27 ≠ a16) && decide (a27 ≠ a17) && decide (a27 ≠ a18) && decide (a27 ≠ a19) && decide (a27 ≠ a20) && decide (a27 ≠ a21) && decide (a27 ≠ a22) && decide (a27 ≠ a23) && decide (a27 ≠ a24) && decide (a27 ≠ a25) && decide (a27 ≠ a26)) || mo408235_L28 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27)

def mo408235_L26 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 : ℕ) : Bool :=
  (mo408235_nb a25).all (fun a26 => !(decide (a26 ≠ a0) && decide (a26 ≠ a1) && decide (a26 ≠ a2) && decide (a26 ≠ a3) && decide (a26 ≠ a4) && decide (a26 ≠ a5) && decide (a26 ≠ a6) && decide (a26 ≠ a7) && decide (a26 ≠ a8) && decide (a26 ≠ a9) && decide (a26 ≠ a10) && decide (a26 ≠ a11) && decide (a26 ≠ a12) && decide (a26 ≠ a13) && decide (a26 ≠ a14) && decide (a26 ≠ a15) && decide (a26 ≠ a16) && decide (a26 ≠ a17) && decide (a26 ≠ a18) && decide (a26 ≠ a19) && decide (a26 ≠ a20) && decide (a26 ≠ a21) && decide (a26 ≠ a22) && decide (a26 ≠ a23) && decide (a26 ≠ a24) && decide (a26 ≠ a25)) || mo408235_L27 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26)

def mo408235_L25 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 : ℕ) : Bool :=
  (mo408235_nb a24).all (fun a25 => !(decide (a25 ≠ a0) && decide (a25 ≠ a1) && decide (a25 ≠ a2) && decide (a25 ≠ a3) && decide (a25 ≠ a4) && decide (a25 ≠ a5) && decide (a25 ≠ a6) && decide (a25 ≠ a7) && decide (a25 ≠ a8) && decide (a25 ≠ a9) && decide (a25 ≠ a10) && decide (a25 ≠ a11) && decide (a25 ≠ a12) && decide (a25 ≠ a13) && decide (a25 ≠ a14) && decide (a25 ≠ a15) && decide (a25 ≠ a16) && decide (a25 ≠ a17) && decide (a25 ≠ a18) && decide (a25 ≠ a19) && decide (a25 ≠ a20) && decide (a25 ≠ a21) && decide (a25 ≠ a22) && decide (a25 ≠ a23) && decide (a25 ≠ a24)) || mo408235_L26 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25)

def mo408235_L24 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 : ℕ) : Bool :=
  (mo408235_nb a23).all (fun a24 => !(decide (a24 ≠ a0) && decide (a24 ≠ a1) && decide (a24 ≠ a2) && decide (a24 ≠ a3) && decide (a24 ≠ a4) && decide (a24 ≠ a5) && decide (a24 ≠ a6) && decide (a24 ≠ a7) && decide (a24 ≠ a8) && decide (a24 ≠ a9) && decide (a24 ≠ a10) && decide (a24 ≠ a11) && decide (a24 ≠ a12) && decide (a24 ≠ a13) && decide (a24 ≠ a14) && decide (a24 ≠ a15) && decide (a24 ≠ a16) && decide (a24 ≠ a17) && decide (a24 ≠ a18) && decide (a24 ≠ a19) && decide (a24 ≠ a20) && decide (a24 ≠ a21) && decide (a24 ≠ a22) && decide (a24 ≠ a23)) || mo408235_L25 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24)

def mo408235_L23 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 : ℕ) : Bool :=
  (mo408235_nb a22).all (fun a23 => !(decide (a23 ≠ a0) && decide (a23 ≠ a1) && decide (a23 ≠ a2) && decide (a23 ≠ a3) && decide (a23 ≠ a4) && decide (a23 ≠ a5) && decide (a23 ≠ a6) && decide (a23 ≠ a7) && decide (a23 ≠ a8) && decide (a23 ≠ a9) && decide (a23 ≠ a10) && decide (a23 ≠ a11) && decide (a23 ≠ a12) && decide (a23 ≠ a13) && decide (a23 ≠ a14) && decide (a23 ≠ a15) && decide (a23 ≠ a16) && decide (a23 ≠ a17) && decide (a23 ≠ a18) && decide (a23 ≠ a19) && decide (a23 ≠ a20) && decide (a23 ≠ a21) && decide (a23 ≠ a22)) || mo408235_L24 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23)

def mo408235_L22 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 : ℕ) : Bool :=
  (mo408235_nb a21).all (fun a22 => !(decide (a22 ≠ a0) && decide (a22 ≠ a1) && decide (a22 ≠ a2) && decide (a22 ≠ a3) && decide (a22 ≠ a4) && decide (a22 ≠ a5) && decide (a22 ≠ a6) && decide (a22 ≠ a7) && decide (a22 ≠ a8) && decide (a22 ≠ a9) && decide (a22 ≠ a10) && decide (a22 ≠ a11) && decide (a22 ≠ a12) && decide (a22 ≠ a13) && decide (a22 ≠ a14) && decide (a22 ≠ a15) && decide (a22 ≠ a16) && decide (a22 ≠ a17) && decide (a22 ≠ a18) && decide (a22 ≠ a19) && decide (a22 ≠ a20) && decide (a22 ≠ a21)) || mo408235_L23 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22)

def mo408235_L21 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 : ℕ) : Bool :=
  (mo408235_nb a20).all (fun a21 => !(decide (a21 ≠ a0) && decide (a21 ≠ a1) && decide (a21 ≠ a2) && decide (a21 ≠ a3) && decide (a21 ≠ a4) && decide (a21 ≠ a5) && decide (a21 ≠ a6) && decide (a21 ≠ a7) && decide (a21 ≠ a8) && decide (a21 ≠ a9) && decide (a21 ≠ a10) && decide (a21 ≠ a11) && decide (a21 ≠ a12) && decide (a21 ≠ a13) && decide (a21 ≠ a14) && decide (a21 ≠ a15) && decide (a21 ≠ a16) && decide (a21 ≠ a17) && decide (a21 ≠ a18) && decide (a21 ≠ a19) && decide (a21 ≠ a20)) || mo408235_L22 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21)

def mo408235_L20 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 : ℕ) : Bool :=
  (mo408235_nb a19).all (fun a20 => !(decide (a20 ≠ a0) && decide (a20 ≠ a1) && decide (a20 ≠ a2) && decide (a20 ≠ a3) && decide (a20 ≠ a4) && decide (a20 ≠ a5) && decide (a20 ≠ a6) && decide (a20 ≠ a7) && decide (a20 ≠ a8) && decide (a20 ≠ a9) && decide (a20 ≠ a10) && decide (a20 ≠ a11) && decide (a20 ≠ a12) && decide (a20 ≠ a13) && decide (a20 ≠ a14) && decide (a20 ≠ a15) && decide (a20 ≠ a16) && decide (a20 ≠ a17) && decide (a20 ≠ a18) && decide (a20 ≠ a19)) || mo408235_L21 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20)

def mo408235_L19 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 : ℕ) : Bool :=
  (mo408235_nb a18).all (fun a19 => !(decide (a19 ≠ a0) && decide (a19 ≠ a1) && decide (a19 ≠ a2) && decide (a19 ≠ a3) && decide (a19 ≠ a4) && decide (a19 ≠ a5) && decide (a19 ≠ a6) && decide (a19 ≠ a7) && decide (a19 ≠ a8) && decide (a19 ≠ a9) && decide (a19 ≠ a10) && decide (a19 ≠ a11) && decide (a19 ≠ a12) && decide (a19 ≠ a13) && decide (a19 ≠ a14) && decide (a19 ≠ a15) && decide (a19 ≠ a16) && decide (a19 ≠ a17) && decide (a19 ≠ a18)) || mo408235_L20 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19)

def mo408235_L18 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 : ℕ) : Bool :=
  (mo408235_nb a17).all (fun a18 => !(decide (a18 ≠ a0) && decide (a18 ≠ a1) && decide (a18 ≠ a2) && decide (a18 ≠ a3) && decide (a18 ≠ a4) && decide (a18 ≠ a5) && decide (a18 ≠ a6) && decide (a18 ≠ a7) && decide (a18 ≠ a8) && decide (a18 ≠ a9) && decide (a18 ≠ a10) && decide (a18 ≠ a11) && decide (a18 ≠ a12) && decide (a18 ≠ a13) && decide (a18 ≠ a14) && decide (a18 ≠ a15) && decide (a18 ≠ a16) && decide (a18 ≠ a17)) || mo408235_L19 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18)

def mo408235_L17 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 : ℕ) : Bool :=
  (mo408235_nb a16).all (fun a17 => !(decide (a17 ≠ a0) && decide (a17 ≠ a1) && decide (a17 ≠ a2) && decide (a17 ≠ a3) && decide (a17 ≠ a4) && decide (a17 ≠ a5) && decide (a17 ≠ a6) && decide (a17 ≠ a7) && decide (a17 ≠ a8) && decide (a17 ≠ a9) && decide (a17 ≠ a10) && decide (a17 ≠ a11) && decide (a17 ≠ a12) && decide (a17 ≠ a13) && decide (a17 ≠ a14) && decide (a17 ≠ a15) && decide (a17 ≠ a16)) || mo408235_L18 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17)

def mo408235_L16 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : ℕ) : Bool :=
  (mo408235_nb a15).all (fun a16 => !(decide (a16 ≠ a0) && decide (a16 ≠ a1) && decide (a16 ≠ a2) && decide (a16 ≠ a3) && decide (a16 ≠ a4) && decide (a16 ≠ a5) && decide (a16 ≠ a6) && decide (a16 ≠ a7) && decide (a16 ≠ a8) && decide (a16 ≠ a9) && decide (a16 ≠ a10) && decide (a16 ≠ a11) && decide (a16 ≠ a12) && decide (a16 ≠ a13) && decide (a16 ≠ a14) && decide (a16 ≠ a15)) || mo408235_L17 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16)

def mo408235_L15 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 : ℕ) : Bool :=
  (mo408235_nb a14).all (fun a15 => !(decide (a15 ≠ a0) && decide (a15 ≠ a1) && decide (a15 ≠ a2) && decide (a15 ≠ a3) && decide (a15 ≠ a4) && decide (a15 ≠ a5) && decide (a15 ≠ a6) && decide (a15 ≠ a7) && decide (a15 ≠ a8) && decide (a15 ≠ a9) && decide (a15 ≠ a10) && decide (a15 ≠ a11) && decide (a15 ≠ a12) && decide (a15 ≠ a13) && decide (a15 ≠ a14)) || mo408235_L16 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)

def mo408235_L14 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : ℕ) : Bool :=
  (mo408235_nb a13).all (fun a14 => !(decide (a14 ≠ a0) && decide (a14 ≠ a1) && decide (a14 ≠ a2) && decide (a14 ≠ a3) && decide (a14 ≠ a4) && decide (a14 ≠ a5) && decide (a14 ≠ a6) && decide (a14 ≠ a7) && decide (a14 ≠ a8) && decide (a14 ≠ a9) && decide (a14 ≠ a10) && decide (a14 ≠ a11) && decide (a14 ≠ a12) && decide (a14 ≠ a13)) || mo408235_L15 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14)

def mo408235_L13 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : ℕ) : Bool :=
  (mo408235_nb a12).all (fun a13 => !(decide (a13 ≠ a0) && decide (a13 ≠ a1) && decide (a13 ≠ a2) && decide (a13 ≠ a3) && decide (a13 ≠ a4) && decide (a13 ≠ a5) && decide (a13 ≠ a6) && decide (a13 ≠ a7) && decide (a13 ≠ a8) && decide (a13 ≠ a9) && decide (a13 ≠ a10) && decide (a13 ≠ a11) && decide (a13 ≠ a12)) || mo408235_L14 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13)

def mo408235_L12 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : ℕ) : Bool :=
  (mo408235_nb a11).all (fun a12 => !(decide (a12 ≠ a0) && decide (a12 ≠ a1) && decide (a12 ≠ a2) && decide (a12 ≠ a3) && decide (a12 ≠ a4) && decide (a12 ≠ a5) && decide (a12 ≠ a6) && decide (a12 ≠ a7) && decide (a12 ≠ a8) && decide (a12 ≠ a9) && decide (a12 ≠ a10) && decide (a12 ≠ a11)) || mo408235_L13 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12)

def mo408235_L11 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : ℕ) : Bool :=
  (mo408235_nb a10).all (fun a11 => !(decide (a11 ≠ a0) && decide (a11 ≠ a1) && decide (a11 ≠ a2) && decide (a11 ≠ a3) && decide (a11 ≠ a4) && decide (a11 ≠ a5) && decide (a11 ≠ a6) && decide (a11 ≠ a7) && decide (a11 ≠ a8) && decide (a11 ≠ a9) && decide (a11 ≠ a10)) || mo408235_L12 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11)

def mo408235_L10 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : ℕ) : Bool :=
  (mo408235_nb a9).all (fun a10 => !(decide (a10 ≠ a0) && decide (a10 ≠ a1) && decide (a10 ≠ a2) && decide (a10 ≠ a3) && decide (a10 ≠ a4) && decide (a10 ≠ a5) && decide (a10 ≠ a6) && decide (a10 ≠ a7) && decide (a10 ≠ a8) && decide (a10 ≠ a9)) || mo408235_L11 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10)

def mo408235_L9 (a0 a1 a2 a3 a4 a5 a6 a7 a8 : ℕ) : Bool :=
  (mo408235_nb a8).all (fun a9 => !(decide (a9 ≠ a0) && decide (a9 ≠ a1) && decide (a9 ≠ a2) && decide (a9 ≠ a3) && decide (a9 ≠ a4) && decide (a9 ≠ a5) && decide (a9 ≠ a6) && decide (a9 ≠ a7) && decide (a9 ≠ a8)) || mo408235_L10 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9)

def mo408235_L8 (a0 a1 a2 a3 a4 a5 a6 a7 : ℕ) : Bool :=
  (mo408235_nb a7).all (fun a8 => !(decide (a8 ≠ a0) && decide (a8 ≠ a1) && decide (a8 ≠ a2) && decide (a8 ≠ a3) && decide (a8 ≠ a4) && decide (a8 ≠ a5) && decide (a8 ≠ a6) && decide (a8 ≠ a7)) || mo408235_L9 a0 a1 a2 a3 a4 a5 a6 a7 a8)

def mo408235_L7 (a0 a1 a2 a3 a4 a5 a6 : ℕ) : Bool :=
  (mo408235_nb a6).all (fun a7 => !(decide (a7 ≠ a0) && decide (a7 ≠ a1) && decide (a7 ≠ a2) && decide (a7 ≠ a3) && decide (a7 ≠ a4) && decide (a7 ≠ a5) && decide (a7 ≠ a6)) || mo408235_L8 a0 a1 a2 a3 a4 a5 a6 a7)

def mo408235_L6 (a0 a1 a2 a3 a4 a5 : ℕ) : Bool :=
  (mo408235_nb a5).all (fun a6 => !(decide (a6 ≠ a0) && decide (a6 ≠ a1) && decide (a6 ≠ a2) && decide (a6 ≠ a3) && decide (a6 ≠ a4) && decide (a6 ≠ a5)) || mo408235_L7 a0 a1 a2 a3 a4 a5 a6)

def mo408235_L5 (a0 a1 a2 a3 a4 : ℕ) : Bool :=
  (mo408235_nb a4).all (fun a5 => !(decide (a5 ≠ a0) && decide (a5 ≠ a1) && decide (a5 ≠ a2) && decide (a5 ≠ a3) && decide (a5 ≠ a4)) || mo408235_L6 a0 a1 a2 a3 a4 a5)

def mo408235_L4 (a0 a1 a2 a3 : ℕ) : Bool :=
  (mo408235_nb a3).all (fun a4 => !(decide (a4 ≠ a0) && decide (a4 ≠ a1) && decide (a4 ≠ a2) && decide (a4 ≠ a3)) || mo408235_L5 a0 a1 a2 a3 a4)

def mo408235_L3 (a0 a1 a2 : ℕ) : Bool :=
  (mo408235_nb a2).all (fun a3 => !(decide (a3 ≠ a0) && decide (a3 ≠ a1) && decide (a3 ≠ a2)) || mo408235_L4 a0 a1 a2 a3)

def mo408235_L2 (a0 a1 : ℕ) : Bool :=
  (mo408235_nb a1).all (fun a2 => !(decide (a2 ≠ a0) && decide (a2 ≠ a1)) || mo408235_L3 a0 a1 a2)

def mo408235_L1 (a0 : ℕ) : Bool :=
  (mo408235_nb a0).all (fun a1 => !(decide (a1 ≠ a0)) || mo408235_L2 a0 a1)

lemma mo408235_top : mo408235_L1 32 = true := by decide +kernel

lemma mo408235_memF : ∀ x y : Fin 33, 1 ≤ (y : ℕ) → (x : ℕ) ≠ y → IsSquare ((x : ℕ) + y) →
    (y : ℕ) ∈ mo408235_nb x := by
  decide +kernel

lemma mo408235_mem (x y : ℕ) (hx : x ≤ 32) (hy1 : 1 ≤ y) (hy : y ≤ 32) (hne : x ≠ y)
    (hs : IsSquare (x + y)) : y ∈ mo408235_nb x :=
  mo408235_memF ⟨x, by omega⟩ ⟨y, by omega⟩ hy1 hne hs

lemma mo408235_hB2 : ∀ k : Fin 32, mo408235_B2 k = mo408235_B (-k) := by decide +kernel

lemma mo408235_S1 (a0 : ℕ) (h : mo408235_L1 a0 = true)
    (a1 : ℕ) (hm : a1 ∈ mo408235_nb a0) (h0 : a1 ≠ a0) :
    mo408235_L2 a0 a1 = true := by
  unfold mo408235_L1 at h
  rw [List.all_eq_true] at h
  have hh := h a1 hm
  simp only [h0, ne_eq, not_false_eq_true, decide_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S2 (a0 a1 : ℕ) (h : mo408235_L2 a0 a1 = true)
    (a2 : ℕ) (hm : a2 ∈ mo408235_nb a1) (h0 : a2 ≠ a0) (h1 : a2 ≠ a1) :
    mo408235_L3 a0 a1 a2 = true := by
  unfold mo408235_L2 at h
  rw [List.all_eq_true] at h
  have hh := h a2 hm
  simp only [h0, h1, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S3 (a0 a1 a2 : ℕ) (h : mo408235_L3 a0 a1 a2 = true)
    (a3 : ℕ) (hm : a3 ∈ mo408235_nb a2) (h0 : a3 ≠ a0) (h1 : a3 ≠ a1) (h2 : a3 ≠ a2) :
    mo408235_L4 a0 a1 a2 a3 = true := by
  unfold mo408235_L3 at h
  rw [List.all_eq_true] at h
  have hh := h a3 hm
  simp only [h0, h1, h2, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S4 (a0 a1 a2 a3 : ℕ) (h : mo408235_L4 a0 a1 a2 a3 = true)
    (a4 : ℕ) (hm : a4 ∈ mo408235_nb a3) (h0 : a4 ≠ a0) (h1 : a4 ≠ a1) (h2 : a4 ≠ a2) (h3 : a4 ≠ a3) :
    mo408235_L5 a0 a1 a2 a3 a4 = true := by
  unfold mo408235_L4 at h
  rw [List.all_eq_true] at h
  have hh := h a4 hm
  simp only [h0, h1, h2, h3, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S5 (a0 a1 a2 a3 a4 : ℕ) (h : mo408235_L5 a0 a1 a2 a3 a4 = true)
    (a5 : ℕ) (hm : a5 ∈ mo408235_nb a4) (h0 : a5 ≠ a0) (h1 : a5 ≠ a1) (h2 : a5 ≠ a2) (h3 : a5 ≠ a3) (h4 : a5 ≠ a4) :
    mo408235_L6 a0 a1 a2 a3 a4 a5 = true := by
  unfold mo408235_L5 at h
  rw [List.all_eq_true] at h
  have hh := h a5 hm
  simp only [h0, h1, h2, h3, h4, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S6 (a0 a1 a2 a3 a4 a5 : ℕ) (h : mo408235_L6 a0 a1 a2 a3 a4 a5 = true)
    (a6 : ℕ) (hm : a6 ∈ mo408235_nb a5) (h0 : a6 ≠ a0) (h1 : a6 ≠ a1) (h2 : a6 ≠ a2) (h3 : a6 ≠ a3) (h4 : a6 ≠ a4) (h5 : a6 ≠ a5) :
    mo408235_L7 a0 a1 a2 a3 a4 a5 a6 = true := by
  unfold mo408235_L6 at h
  rw [List.all_eq_true] at h
  have hh := h a6 hm
  simp only [h0, h1, h2, h3, h4, h5, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S7 (a0 a1 a2 a3 a4 a5 a6 : ℕ) (h : mo408235_L7 a0 a1 a2 a3 a4 a5 a6 = true)
    (a7 : ℕ) (hm : a7 ∈ mo408235_nb a6) (h0 : a7 ≠ a0) (h1 : a7 ≠ a1) (h2 : a7 ≠ a2) (h3 : a7 ≠ a3) (h4 : a7 ≠ a4) (h5 : a7 ≠ a5) (h6 : a7 ≠ a6) :
    mo408235_L8 a0 a1 a2 a3 a4 a5 a6 a7 = true := by
  unfold mo408235_L7 at h
  rw [List.all_eq_true] at h
  have hh := h a7 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S8 (a0 a1 a2 a3 a4 a5 a6 a7 : ℕ) (h : mo408235_L8 a0 a1 a2 a3 a4 a5 a6 a7 = true)
    (a8 : ℕ) (hm : a8 ∈ mo408235_nb a7) (h0 : a8 ≠ a0) (h1 : a8 ≠ a1) (h2 : a8 ≠ a2) (h3 : a8 ≠ a3) (h4 : a8 ≠ a4) (h5 : a8 ≠ a5) (h6 : a8 ≠ a6) (h7 : a8 ≠ a7) :
    mo408235_L9 a0 a1 a2 a3 a4 a5 a6 a7 a8 = true := by
  unfold mo408235_L8 at h
  rw [List.all_eq_true] at h
  have hh := h a8 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S9 (a0 a1 a2 a3 a4 a5 a6 a7 a8 : ℕ) (h : mo408235_L9 a0 a1 a2 a3 a4 a5 a6 a7 a8 = true)
    (a9 : ℕ) (hm : a9 ∈ mo408235_nb a8) (h0 : a9 ≠ a0) (h1 : a9 ≠ a1) (h2 : a9 ≠ a2) (h3 : a9 ≠ a3) (h4 : a9 ≠ a4) (h5 : a9 ≠ a5) (h6 : a9 ≠ a6) (h7 : a9 ≠ a7) (h8 : a9 ≠ a8) :
    mo408235_L10 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = true := by
  unfold mo408235_L9 at h
  rw [List.all_eq_true] at h
  have hh := h a9 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S10 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : ℕ) (h : mo408235_L10 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = true)
    (a10 : ℕ) (hm : a10 ∈ mo408235_nb a9) (h0 : a10 ≠ a0) (h1 : a10 ≠ a1) (h2 : a10 ≠ a2) (h3 : a10 ≠ a3) (h4 : a10 ≠ a4) (h5 : a10 ≠ a5) (h6 : a10 ≠ a6) (h7 : a10 ≠ a7) (h8 : a10 ≠ a8) (h9 : a10 ≠ a9) :
    mo408235_L11 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = true := by
  unfold mo408235_L10 at h
  rw [List.all_eq_true] at h
  have hh := h a10 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S11 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : ℕ) (h : mo408235_L11 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = true)
    (a11 : ℕ) (hm : a11 ∈ mo408235_nb a10) (h0 : a11 ≠ a0) (h1 : a11 ≠ a1) (h2 : a11 ≠ a2) (h3 : a11 ≠ a3) (h4 : a11 ≠ a4) (h5 : a11 ≠ a5) (h6 : a11 ≠ a6) (h7 : a11 ≠ a7) (h8 : a11 ≠ a8) (h9 : a11 ≠ a9) (h10 : a11 ≠ a10) :
    mo408235_L12 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = true := by
  unfold mo408235_L11 at h
  rw [List.all_eq_true] at h
  have hh := h a11 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S12 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : ℕ) (h : mo408235_L12 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = true)
    (a12 : ℕ) (hm : a12 ∈ mo408235_nb a11) (h0 : a12 ≠ a0) (h1 : a12 ≠ a1) (h2 : a12 ≠ a2) (h3 : a12 ≠ a3) (h4 : a12 ≠ a4) (h5 : a12 ≠ a5) (h6 : a12 ≠ a6) (h7 : a12 ≠ a7) (h8 : a12 ≠ a8) (h9 : a12 ≠ a9) (h10 : a12 ≠ a10) (h11 : a12 ≠ a11) :
    mo408235_L13 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = true := by
  unfold mo408235_L12 at h
  rw [List.all_eq_true] at h
  have hh := h a12 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S13 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : ℕ) (h : mo408235_L13 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = true)
    (a13 : ℕ) (hm : a13 ∈ mo408235_nb a12) (h0 : a13 ≠ a0) (h1 : a13 ≠ a1) (h2 : a13 ≠ a2) (h3 : a13 ≠ a3) (h4 : a13 ≠ a4) (h5 : a13 ≠ a5) (h6 : a13 ≠ a6) (h7 : a13 ≠ a7) (h8 : a13 ≠ a8) (h9 : a13 ≠ a9) (h10 : a13 ≠ a10) (h11 : a13 ≠ a11) (h12 : a13 ≠ a12) :
    mo408235_L14 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = true := by
  unfold mo408235_L13 at h
  rw [List.all_eq_true] at h
  have hh := h a13 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S14 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : ℕ) (h : mo408235_L14 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = true)
    (a14 : ℕ) (hm : a14 ∈ mo408235_nb a13) (h0 : a14 ≠ a0) (h1 : a14 ≠ a1) (h2 : a14 ≠ a2) (h3 : a14 ≠ a3) (h4 : a14 ≠ a4) (h5 : a14 ≠ a5) (h6 : a14 ≠ a6) (h7 : a14 ≠ a7) (h8 : a14 ≠ a8) (h9 : a14 ≠ a9) (h10 : a14 ≠ a10) (h11 : a14 ≠ a11) (h12 : a14 ≠ a12) (h13 : a14 ≠ a13) :
    mo408235_L15 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 = true := by
  unfold mo408235_L14 at h
  rw [List.all_eq_true] at h
  have hh := h a14 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S15 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 : ℕ) (h : mo408235_L15 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 = true)
    (a15 : ℕ) (hm : a15 ∈ mo408235_nb a14) (h0 : a15 ≠ a0) (h1 : a15 ≠ a1) (h2 : a15 ≠ a2) (h3 : a15 ≠ a3) (h4 : a15 ≠ a4) (h5 : a15 ≠ a5) (h6 : a15 ≠ a6) (h7 : a15 ≠ a7) (h8 : a15 ≠ a8) (h9 : a15 ≠ a9) (h10 : a15 ≠ a10) (h11 : a15 ≠ a11) (h12 : a15 ≠ a12) (h13 : a15 ≠ a13) (h14 : a15 ≠ a14) :
    mo408235_L16 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 = true := by
  unfold mo408235_L15 at h
  rw [List.all_eq_true] at h
  have hh := h a15 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S16 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : ℕ) (h : mo408235_L16 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 = true)
    (a16 : ℕ) (hm : a16 ∈ mo408235_nb a15) (h0 : a16 ≠ a0) (h1 : a16 ≠ a1) (h2 : a16 ≠ a2) (h3 : a16 ≠ a3) (h4 : a16 ≠ a4) (h5 : a16 ≠ a5) (h6 : a16 ≠ a6) (h7 : a16 ≠ a7) (h8 : a16 ≠ a8) (h9 : a16 ≠ a9) (h10 : a16 ≠ a10) (h11 : a16 ≠ a11) (h12 : a16 ≠ a12) (h13 : a16 ≠ a13) (h14 : a16 ≠ a14) (h15 : a16 ≠ a15) :
    mo408235_L17 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 = true := by
  unfold mo408235_L16 at h
  rw [List.all_eq_true] at h
  have hh := h a16 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S17 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 : ℕ) (h : mo408235_L17 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 = true)
    (a17 : ℕ) (hm : a17 ∈ mo408235_nb a16) (h0 : a17 ≠ a0) (h1 : a17 ≠ a1) (h2 : a17 ≠ a2) (h3 : a17 ≠ a3) (h4 : a17 ≠ a4) (h5 : a17 ≠ a5) (h6 : a17 ≠ a6) (h7 : a17 ≠ a7) (h8 : a17 ≠ a8) (h9 : a17 ≠ a9) (h10 : a17 ≠ a10) (h11 : a17 ≠ a11) (h12 : a17 ≠ a12) (h13 : a17 ≠ a13) (h14 : a17 ≠ a14) (h15 : a17 ≠ a15) (h16 : a17 ≠ a16) :
    mo408235_L18 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 = true := by
  unfold mo408235_L17 at h
  rw [List.all_eq_true] at h
  have hh := h a17 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S18 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 : ℕ) (h : mo408235_L18 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 = true)
    (a18 : ℕ) (hm : a18 ∈ mo408235_nb a17) (h0 : a18 ≠ a0) (h1 : a18 ≠ a1) (h2 : a18 ≠ a2) (h3 : a18 ≠ a3) (h4 : a18 ≠ a4) (h5 : a18 ≠ a5) (h6 : a18 ≠ a6) (h7 : a18 ≠ a7) (h8 : a18 ≠ a8) (h9 : a18 ≠ a9) (h10 : a18 ≠ a10) (h11 : a18 ≠ a11) (h12 : a18 ≠ a12) (h13 : a18 ≠ a13) (h14 : a18 ≠ a14) (h15 : a18 ≠ a15) (h16 : a18 ≠ a16) (h17 : a18 ≠ a17) :
    mo408235_L19 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 = true := by
  unfold mo408235_L18 at h
  rw [List.all_eq_true] at h
  have hh := h a18 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S19 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 : ℕ) (h : mo408235_L19 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 = true)
    (a19 : ℕ) (hm : a19 ∈ mo408235_nb a18) (h0 : a19 ≠ a0) (h1 : a19 ≠ a1) (h2 : a19 ≠ a2) (h3 : a19 ≠ a3) (h4 : a19 ≠ a4) (h5 : a19 ≠ a5) (h6 : a19 ≠ a6) (h7 : a19 ≠ a7) (h8 : a19 ≠ a8) (h9 : a19 ≠ a9) (h10 : a19 ≠ a10) (h11 : a19 ≠ a11) (h12 : a19 ≠ a12) (h13 : a19 ≠ a13) (h14 : a19 ≠ a14) (h15 : a19 ≠ a15) (h16 : a19 ≠ a16) (h17 : a19 ≠ a17) (h18 : a19 ≠ a18) :
    mo408235_L20 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 = true := by
  unfold mo408235_L19 at h
  rw [List.all_eq_true] at h
  have hh := h a19 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S20 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 : ℕ) (h : mo408235_L20 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 = true)
    (a20 : ℕ) (hm : a20 ∈ mo408235_nb a19) (h0 : a20 ≠ a0) (h1 : a20 ≠ a1) (h2 : a20 ≠ a2) (h3 : a20 ≠ a3) (h4 : a20 ≠ a4) (h5 : a20 ≠ a5) (h6 : a20 ≠ a6) (h7 : a20 ≠ a7) (h8 : a20 ≠ a8) (h9 : a20 ≠ a9) (h10 : a20 ≠ a10) (h11 : a20 ≠ a11) (h12 : a20 ≠ a12) (h13 : a20 ≠ a13) (h14 : a20 ≠ a14) (h15 : a20 ≠ a15) (h16 : a20 ≠ a16) (h17 : a20 ≠ a17) (h18 : a20 ≠ a18) (h19 : a20 ≠ a19) :
    mo408235_L21 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 = true := by
  unfold mo408235_L20 at h
  rw [List.all_eq_true] at h
  have hh := h a20 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S21 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 : ℕ) (h : mo408235_L21 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 = true)
    (a21 : ℕ) (hm : a21 ∈ mo408235_nb a20) (h0 : a21 ≠ a0) (h1 : a21 ≠ a1) (h2 : a21 ≠ a2) (h3 : a21 ≠ a3) (h4 : a21 ≠ a4) (h5 : a21 ≠ a5) (h6 : a21 ≠ a6) (h7 : a21 ≠ a7) (h8 : a21 ≠ a8) (h9 : a21 ≠ a9) (h10 : a21 ≠ a10) (h11 : a21 ≠ a11) (h12 : a21 ≠ a12) (h13 : a21 ≠ a13) (h14 : a21 ≠ a14) (h15 : a21 ≠ a15) (h16 : a21 ≠ a16) (h17 : a21 ≠ a17) (h18 : a21 ≠ a18) (h19 : a21 ≠ a19) (h20 : a21 ≠ a20) :
    mo408235_L22 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 = true := by
  unfold mo408235_L21 at h
  rw [List.all_eq_true] at h
  have hh := h a21 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S22 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 : ℕ) (h : mo408235_L22 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 = true)
    (a22 : ℕ) (hm : a22 ∈ mo408235_nb a21) (h0 : a22 ≠ a0) (h1 : a22 ≠ a1) (h2 : a22 ≠ a2) (h3 : a22 ≠ a3) (h4 : a22 ≠ a4) (h5 : a22 ≠ a5) (h6 : a22 ≠ a6) (h7 : a22 ≠ a7) (h8 : a22 ≠ a8) (h9 : a22 ≠ a9) (h10 : a22 ≠ a10) (h11 : a22 ≠ a11) (h12 : a22 ≠ a12) (h13 : a22 ≠ a13) (h14 : a22 ≠ a14) (h15 : a22 ≠ a15) (h16 : a22 ≠ a16) (h17 : a22 ≠ a17) (h18 : a22 ≠ a18) (h19 : a22 ≠ a19) (h20 : a22 ≠ a20) (h21 : a22 ≠ a21) :
    mo408235_L23 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 = true := by
  unfold mo408235_L22 at h
  rw [List.all_eq_true] at h
  have hh := h a22 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S23 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 : ℕ) (h : mo408235_L23 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 = true)
    (a23 : ℕ) (hm : a23 ∈ mo408235_nb a22) (h0 : a23 ≠ a0) (h1 : a23 ≠ a1) (h2 : a23 ≠ a2) (h3 : a23 ≠ a3) (h4 : a23 ≠ a4) (h5 : a23 ≠ a5) (h6 : a23 ≠ a6) (h7 : a23 ≠ a7) (h8 : a23 ≠ a8) (h9 : a23 ≠ a9) (h10 : a23 ≠ a10) (h11 : a23 ≠ a11) (h12 : a23 ≠ a12) (h13 : a23 ≠ a13) (h14 : a23 ≠ a14) (h15 : a23 ≠ a15) (h16 : a23 ≠ a16) (h17 : a23 ≠ a17) (h18 : a23 ≠ a18) (h19 : a23 ≠ a19) (h20 : a23 ≠ a20) (h21 : a23 ≠ a21) (h22 : a23 ≠ a22) :
    mo408235_L24 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 = true := by
  unfold mo408235_L23 at h
  rw [List.all_eq_true] at h
  have hh := h a23 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S24 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 : ℕ) (h : mo408235_L24 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 = true)
    (a24 : ℕ) (hm : a24 ∈ mo408235_nb a23) (h0 : a24 ≠ a0) (h1 : a24 ≠ a1) (h2 : a24 ≠ a2) (h3 : a24 ≠ a3) (h4 : a24 ≠ a4) (h5 : a24 ≠ a5) (h6 : a24 ≠ a6) (h7 : a24 ≠ a7) (h8 : a24 ≠ a8) (h9 : a24 ≠ a9) (h10 : a24 ≠ a10) (h11 : a24 ≠ a11) (h12 : a24 ≠ a12) (h13 : a24 ≠ a13) (h14 : a24 ≠ a14) (h15 : a24 ≠ a15) (h16 : a24 ≠ a16) (h17 : a24 ≠ a17) (h18 : a24 ≠ a18) (h19 : a24 ≠ a19) (h20 : a24 ≠ a20) (h21 : a24 ≠ a21) (h22 : a24 ≠ a22) (h23 : a24 ≠ a23) :
    mo408235_L25 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 = true := by
  unfold mo408235_L24 at h
  rw [List.all_eq_true] at h
  have hh := h a24 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S25 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 : ℕ) (h : mo408235_L25 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 = true)
    (a25 : ℕ) (hm : a25 ∈ mo408235_nb a24) (h0 : a25 ≠ a0) (h1 : a25 ≠ a1) (h2 : a25 ≠ a2) (h3 : a25 ≠ a3) (h4 : a25 ≠ a4) (h5 : a25 ≠ a5) (h6 : a25 ≠ a6) (h7 : a25 ≠ a7) (h8 : a25 ≠ a8) (h9 : a25 ≠ a9) (h10 : a25 ≠ a10) (h11 : a25 ≠ a11) (h12 : a25 ≠ a12) (h13 : a25 ≠ a13) (h14 : a25 ≠ a14) (h15 : a25 ≠ a15) (h16 : a25 ≠ a16) (h17 : a25 ≠ a17) (h18 : a25 ≠ a18) (h19 : a25 ≠ a19) (h20 : a25 ≠ a20) (h21 : a25 ≠ a21) (h22 : a25 ≠ a22) (h23 : a25 ≠ a23) (h24 : a25 ≠ a24) :
    mo408235_L26 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 = true := by
  unfold mo408235_L25 at h
  rw [List.all_eq_true] at h
  have hh := h a25 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S26 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 : ℕ) (h : mo408235_L26 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 = true)
    (a26 : ℕ) (hm : a26 ∈ mo408235_nb a25) (h0 : a26 ≠ a0) (h1 : a26 ≠ a1) (h2 : a26 ≠ a2) (h3 : a26 ≠ a3) (h4 : a26 ≠ a4) (h5 : a26 ≠ a5) (h6 : a26 ≠ a6) (h7 : a26 ≠ a7) (h8 : a26 ≠ a8) (h9 : a26 ≠ a9) (h10 : a26 ≠ a10) (h11 : a26 ≠ a11) (h12 : a26 ≠ a12) (h13 : a26 ≠ a13) (h14 : a26 ≠ a14) (h15 : a26 ≠ a15) (h16 : a26 ≠ a16) (h17 : a26 ≠ a17) (h18 : a26 ≠ a18) (h19 : a26 ≠ a19) (h20 : a26 ≠ a20) (h21 : a26 ≠ a21) (h22 : a26 ≠ a22) (h23 : a26 ≠ a23) (h24 : a26 ≠ a24) (h25 : a26 ≠ a25) :
    mo408235_L27 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 = true := by
  unfold mo408235_L26 at h
  rw [List.all_eq_true] at h
  have hh := h a26 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S27 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 : ℕ) (h : mo408235_L27 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 = true)
    (a27 : ℕ) (hm : a27 ∈ mo408235_nb a26) (h0 : a27 ≠ a0) (h1 : a27 ≠ a1) (h2 : a27 ≠ a2) (h3 : a27 ≠ a3) (h4 : a27 ≠ a4) (h5 : a27 ≠ a5) (h6 : a27 ≠ a6) (h7 : a27 ≠ a7) (h8 : a27 ≠ a8) (h9 : a27 ≠ a9) (h10 : a27 ≠ a10) (h11 : a27 ≠ a11) (h12 : a27 ≠ a12) (h13 : a27 ≠ a13) (h14 : a27 ≠ a14) (h15 : a27 ≠ a15) (h16 : a27 ≠ a16) (h17 : a27 ≠ a17) (h18 : a27 ≠ a18) (h19 : a27 ≠ a19) (h20 : a27 ≠ a20) (h21 : a27 ≠ a21) (h22 : a27 ≠ a22) (h23 : a27 ≠ a23) (h24 : a27 ≠ a24) (h25 : a27 ≠ a25) (h26 : a27 ≠ a26) :
    mo408235_L28 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 = true := by
  unfold mo408235_L27 at h
  rw [List.all_eq_true] at h
  have hh := h a27 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S28 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 : ℕ) (h : mo408235_L28 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 = true)
    (a28 : ℕ) (hm : a28 ∈ mo408235_nb a27) (h0 : a28 ≠ a0) (h1 : a28 ≠ a1) (h2 : a28 ≠ a2) (h3 : a28 ≠ a3) (h4 : a28 ≠ a4) (h5 : a28 ≠ a5) (h6 : a28 ≠ a6) (h7 : a28 ≠ a7) (h8 : a28 ≠ a8) (h9 : a28 ≠ a9) (h10 : a28 ≠ a10) (h11 : a28 ≠ a11) (h12 : a28 ≠ a12) (h13 : a28 ≠ a13) (h14 : a28 ≠ a14) (h15 : a28 ≠ a15) (h16 : a28 ≠ a16) (h17 : a28 ≠ a17) (h18 : a28 ≠ a18) (h19 : a28 ≠ a19) (h20 : a28 ≠ a20) (h21 : a28 ≠ a21) (h22 : a28 ≠ a22) (h23 : a28 ≠ a23) (h24 : a28 ≠ a24) (h25 : a28 ≠ a25) (h26 : a28 ≠ a26) (h27 : a28 ≠ a27) :
    mo408235_L29 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 = true := by
  unfold mo408235_L28 at h
  rw [List.all_eq_true] at h
  have hh := h a28 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S29 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 : ℕ) (h : mo408235_L29 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 = true)
    (a29 : ℕ) (hm : a29 ∈ mo408235_nb a28) (h0 : a29 ≠ a0) (h1 : a29 ≠ a1) (h2 : a29 ≠ a2) (h3 : a29 ≠ a3) (h4 : a29 ≠ a4) (h5 : a29 ≠ a5) (h6 : a29 ≠ a6) (h7 : a29 ≠ a7) (h8 : a29 ≠ a8) (h9 : a29 ≠ a9) (h10 : a29 ≠ a10) (h11 : a29 ≠ a11) (h12 : a29 ≠ a12) (h13 : a29 ≠ a13) (h14 : a29 ≠ a14) (h15 : a29 ≠ a15) (h16 : a29 ≠ a16) (h17 : a29 ≠ a17) (h18 : a29 ≠ a18) (h19 : a29 ≠ a19) (h20 : a29 ≠ a20) (h21 : a29 ≠ a21) (h22 : a29 ≠ a22) (h23 : a29 ≠ a23) (h24 : a29 ≠ a24) (h25 : a29 ≠ a25) (h26 : a29 ≠ a26) (h27 : a29 ≠ a27) (h28 : a29 ≠ a28) :
    mo408235_L30 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 = true := by
  unfold mo408235_L29 at h
  rw [List.all_eq_true] at h
  have hh := h a29 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S30 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 : ℕ) (h : mo408235_L30 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 = true)
    (a30 : ℕ) (hm : a30 ∈ mo408235_nb a29) (h0 : a30 ≠ a0) (h1 : a30 ≠ a1) (h2 : a30 ≠ a2) (h3 : a30 ≠ a3) (h4 : a30 ≠ a4) (h5 : a30 ≠ a5) (h6 : a30 ≠ a6) (h7 : a30 ≠ a7) (h8 : a30 ≠ a8) (h9 : a30 ≠ a9) (h10 : a30 ≠ a10) (h11 : a30 ≠ a11) (h12 : a30 ≠ a12) (h13 : a30 ≠ a13) (h14 : a30 ≠ a14) (h15 : a30 ≠ a15) (h16 : a30 ≠ a16) (h17 : a30 ≠ a17) (h18 : a30 ≠ a18) (h19 : a30 ≠ a19) (h20 : a30 ≠ a20) (h21 : a30 ≠ a21) (h22 : a30 ≠ a22) (h23 : a30 ≠ a23) (h24 : a30 ≠ a24) (h25 : a30 ≠ a25) (h26 : a30 ≠ a26) (h27 : a30 ≠ a27) (h28 : a30 ≠ a28) (h29 : a30 ≠ a29) :
    mo408235_L31 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 = true := by
  unfold mo408235_L30 at h
  rw [List.all_eq_true] at h
  have hh := h a30 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo408235_S31 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 : ℕ) (h : mo408235_L31 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 = true)
    (a31 : ℕ) (hm : a31 ∈ mo408235_nb a30) (h0 : a31 ≠ a0) (h1 : a31 ≠ a1) (h2 : a31 ≠ a2) (h3 : a31 ≠ a3) (h4 : a31 ≠ a4) (h5 : a31 ≠ a5) (h6 : a31 ≠ a6) (h7 : a31 ≠ a7) (h8 : a31 ≠ a8) (h9 : a31 ≠ a9) (h10 : a31 ≠ a10) (h11 : a31 ≠ a11) (h12 : a31 ≠ a12) (h13 : a31 ≠ a13) (h14 : a31 ≠ a14) (h15 : a31 ≠ a15) (h16 : a31 ≠ a16) (h17 : a31 ≠ a17) (h18 : a31 ≠ a18) (h19 : a31 ≠ a19) (h20 : a31 ≠ a20) (h21 : a31 ≠ a21) (h22 : a31 ≠ a22) (h23 : a31 ≠ a23) (h24 : a31 ≠ a24) (h25 : a31 ≠ a25) (h26 : a31 ≠ a26) (h27 : a31 ≠ a27) (h28 : a31 ≠ a28) (h29 : a31 ≠ a29) (h30 : a31 ≠ a30) :
    IsSquare (a31 + a0) → (![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31] : Fin 32 → ℕ) = mo408235_B ∨ (![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31] : Fin 32 → ℕ) = mo408235_B2 := by
  unfold mo408235_L31 at h
  rw [List.all_eq_true] at h
  have hh := h a31 hm
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  intro hl
  simp only [hl, decide_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hh
  exact hh

lemma mo408235_classify (c : Fin 32 → ℕ) (hc : IsSquareCircle 32 c) :
    ∃ k : Fin 32, (∀ i, c i = mo408235_B (i + k)) ∨ (∀ i, c i = mo408235_B (k - i)) := by
  obtain ⟨hinj, hrange, hsq⟩ := hc
  have hsub : Finset.univ.image c ⊆ Finset.Icc 1 32 := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    simp [Finset.mem_Icc, hrange i]
  have hcard : (Finset.univ.image c).card = 32 := by
    rw [Finset.card_image_of_injective _ hinj]; simp
  have heq := Finset.eq_of_subset_of_card_le hsub (by simp [hcard])
  have h32 : (32 : ℕ) ∈ Finset.univ.image c := by rw [heq]; simp
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at h32
  obtain ⟨j, hj⟩ := h32
  have hrot : ∀ i : Fin 32, finRotate 32 i = i + 1 := fun i => finRotate_apply i
  set a : Fin 32 → ℕ := fun k => c (j + k) with ha_def
  have ha : ∀ k : Fin 32, IsSquare (a k + a (k + 1)) := by
    intro k
    have := hsq (j + k)
    rw [hrot, add_assoc] at this
    exact this
  have hinjA : ∀ p q : Fin 32, p ≠ q → a p ≠ a q :=
    fun p q hpq h => hpq (add_left_cancel (hinj h))
  have hsucc : ∀ k : Fin 32, k + 1 ≠ k := by decide
  have hm : ∀ k : Fin 32, a (k + 1) ∈ mo408235_nb (a k) := by
    intro k
    apply mo408235_mem
    · exact (hrange _).2
    · exact (hrange _).1
    · exact (hrange _).2
    · exact fun h => hinjA k (k + 1) (hsucc k).symm h
    · exact ha k
  have h00 : a 0 = 32 := by simp [a, hj]
  have hfun : a = ![a 0, a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8, a 9, a 10, a 11, a 12, a 13, a 14, a 15, a 16, a 17, a 18, a 19, a 20, a 21, a 22, a 23, a 24, a 25, a 26, a 27, a 28, a 29, a 30, a 31] := by
    funext k
    fin_cases k <;> rfl
  have t1 : mo408235_L1 (a 0) = true := by rw [h00]; exact mo408235_top
  have t2 := mo408235_S1 (a 0) t1 (a 1) (hm 0) (hinjA 1 0 (by decide))
  have t3 := mo408235_S2 (a 0) (a 1) t2 (a 2) (hm 1) (hinjA 2 0 (by decide)) (hinjA 2 1 (by decide))
  have t4 := mo408235_S3 (a 0) (a 1) (a 2) t3 (a 3) (hm 2) (hinjA 3 0 (by decide)) (hinjA 3 1 (by decide)) (hinjA 3 2 (by decide))
  have t5 := mo408235_S4 (a 0) (a 1) (a 2) (a 3) t4 (a 4) (hm 3) (hinjA 4 0 (by decide)) (hinjA 4 1 (by decide)) (hinjA 4 2 (by decide)) (hinjA 4 3 (by decide))
  have t6 := mo408235_S5 (a 0) (a 1) (a 2) (a 3) (a 4) t5 (a 5) (hm 4) (hinjA 5 0 (by decide)) (hinjA 5 1 (by decide)) (hinjA 5 2 (by decide)) (hinjA 5 3 (by decide)) (hinjA 5 4 (by decide))
  have t7 := mo408235_S6 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) t6 (a 6) (hm 5) (hinjA 6 0 (by decide)) (hinjA 6 1 (by decide)) (hinjA 6 2 (by decide)) (hinjA 6 3 (by decide)) (hinjA 6 4 (by decide)) (hinjA 6 5 (by decide))
  have t8 := mo408235_S7 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) t7 (a 7) (hm 6) (hinjA 7 0 (by decide)) (hinjA 7 1 (by decide)) (hinjA 7 2 (by decide)) (hinjA 7 3 (by decide)) (hinjA 7 4 (by decide)) (hinjA 7 5 (by decide)) (hinjA 7 6 (by decide))
  have t9 := mo408235_S8 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) t8 (a 8) (hm 7) (hinjA 8 0 (by decide)) (hinjA 8 1 (by decide)) (hinjA 8 2 (by decide)) (hinjA 8 3 (by decide)) (hinjA 8 4 (by decide)) (hinjA 8 5 (by decide)) (hinjA 8 6 (by decide)) (hinjA 8 7 (by decide))
  have t10 := mo408235_S9 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) t9 (a 9) (hm 8) (hinjA 9 0 (by decide)) (hinjA 9 1 (by decide)) (hinjA 9 2 (by decide)) (hinjA 9 3 (by decide)) (hinjA 9 4 (by decide)) (hinjA 9 5 (by decide)) (hinjA 9 6 (by decide)) (hinjA 9 7 (by decide)) (hinjA 9 8 (by decide))
  have t11 := mo408235_S10 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) t10 (a 10) (hm 9) (hinjA 10 0 (by decide)) (hinjA 10 1 (by decide)) (hinjA 10 2 (by decide)) (hinjA 10 3 (by decide)) (hinjA 10 4 (by decide)) (hinjA 10 5 (by decide)) (hinjA 10 6 (by decide)) (hinjA 10 7 (by decide)) (hinjA 10 8 (by decide)) (hinjA 10 9 (by decide))
  have t12 := mo408235_S11 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) t11 (a 11) (hm 10) (hinjA 11 0 (by decide)) (hinjA 11 1 (by decide)) (hinjA 11 2 (by decide)) (hinjA 11 3 (by decide)) (hinjA 11 4 (by decide)) (hinjA 11 5 (by decide)) (hinjA 11 6 (by decide)) (hinjA 11 7 (by decide)) (hinjA 11 8 (by decide)) (hinjA 11 9 (by decide)) (hinjA 11 10 (by decide))
  have t13 := mo408235_S12 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) t12 (a 12) (hm 11) (hinjA 12 0 (by decide)) (hinjA 12 1 (by decide)) (hinjA 12 2 (by decide)) (hinjA 12 3 (by decide)) (hinjA 12 4 (by decide)) (hinjA 12 5 (by decide)) (hinjA 12 6 (by decide)) (hinjA 12 7 (by decide)) (hinjA 12 8 (by decide)) (hinjA 12 9 (by decide)) (hinjA 12 10 (by decide)) (hinjA 12 11 (by decide))
  have t14 := mo408235_S13 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) t13 (a 13) (hm 12) (hinjA 13 0 (by decide)) (hinjA 13 1 (by decide)) (hinjA 13 2 (by decide)) (hinjA 13 3 (by decide)) (hinjA 13 4 (by decide)) (hinjA 13 5 (by decide)) (hinjA 13 6 (by decide)) (hinjA 13 7 (by decide)) (hinjA 13 8 (by decide)) (hinjA 13 9 (by decide)) (hinjA 13 10 (by decide)) (hinjA 13 11 (by decide)) (hinjA 13 12 (by decide))
  have t15 := mo408235_S14 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) t14 (a 14) (hm 13) (hinjA 14 0 (by decide)) (hinjA 14 1 (by decide)) (hinjA 14 2 (by decide)) (hinjA 14 3 (by decide)) (hinjA 14 4 (by decide)) (hinjA 14 5 (by decide)) (hinjA 14 6 (by decide)) (hinjA 14 7 (by decide)) (hinjA 14 8 (by decide)) (hinjA 14 9 (by decide)) (hinjA 14 10 (by decide)) (hinjA 14 11 (by decide)) (hinjA 14 12 (by decide)) (hinjA 14 13 (by decide))
  have t16 := mo408235_S15 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) t15 (a 15) (hm 14) (hinjA 15 0 (by decide)) (hinjA 15 1 (by decide)) (hinjA 15 2 (by decide)) (hinjA 15 3 (by decide)) (hinjA 15 4 (by decide)) (hinjA 15 5 (by decide)) (hinjA 15 6 (by decide)) (hinjA 15 7 (by decide)) (hinjA 15 8 (by decide)) (hinjA 15 9 (by decide)) (hinjA 15 10 (by decide)) (hinjA 15 11 (by decide)) (hinjA 15 12 (by decide)) (hinjA 15 13 (by decide)) (hinjA 15 14 (by decide))
  have t17 := mo408235_S16 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) t16 (a 16) (hm 15) (hinjA 16 0 (by decide)) (hinjA 16 1 (by decide)) (hinjA 16 2 (by decide)) (hinjA 16 3 (by decide)) (hinjA 16 4 (by decide)) (hinjA 16 5 (by decide)) (hinjA 16 6 (by decide)) (hinjA 16 7 (by decide)) (hinjA 16 8 (by decide)) (hinjA 16 9 (by decide)) (hinjA 16 10 (by decide)) (hinjA 16 11 (by decide)) (hinjA 16 12 (by decide)) (hinjA 16 13 (by decide)) (hinjA 16 14 (by decide)) (hinjA 16 15 (by decide))
  have t18 := mo408235_S17 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) t17 (a 17) (hm 16) (hinjA 17 0 (by decide)) (hinjA 17 1 (by decide)) (hinjA 17 2 (by decide)) (hinjA 17 3 (by decide)) (hinjA 17 4 (by decide)) (hinjA 17 5 (by decide)) (hinjA 17 6 (by decide)) (hinjA 17 7 (by decide)) (hinjA 17 8 (by decide)) (hinjA 17 9 (by decide)) (hinjA 17 10 (by decide)) (hinjA 17 11 (by decide)) (hinjA 17 12 (by decide)) (hinjA 17 13 (by decide)) (hinjA 17 14 (by decide)) (hinjA 17 15 (by decide)) (hinjA 17 16 (by decide))
  have t19 := mo408235_S18 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) t18 (a 18) (hm 17) (hinjA 18 0 (by decide)) (hinjA 18 1 (by decide)) (hinjA 18 2 (by decide)) (hinjA 18 3 (by decide)) (hinjA 18 4 (by decide)) (hinjA 18 5 (by decide)) (hinjA 18 6 (by decide)) (hinjA 18 7 (by decide)) (hinjA 18 8 (by decide)) (hinjA 18 9 (by decide)) (hinjA 18 10 (by decide)) (hinjA 18 11 (by decide)) (hinjA 18 12 (by decide)) (hinjA 18 13 (by decide)) (hinjA 18 14 (by decide)) (hinjA 18 15 (by decide)) (hinjA 18 16 (by decide)) (hinjA 18 17 (by decide))
  have t20 := mo408235_S19 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) t19 (a 19) (hm 18) (hinjA 19 0 (by decide)) (hinjA 19 1 (by decide)) (hinjA 19 2 (by decide)) (hinjA 19 3 (by decide)) (hinjA 19 4 (by decide)) (hinjA 19 5 (by decide)) (hinjA 19 6 (by decide)) (hinjA 19 7 (by decide)) (hinjA 19 8 (by decide)) (hinjA 19 9 (by decide)) (hinjA 19 10 (by decide)) (hinjA 19 11 (by decide)) (hinjA 19 12 (by decide)) (hinjA 19 13 (by decide)) (hinjA 19 14 (by decide)) (hinjA 19 15 (by decide)) (hinjA 19 16 (by decide)) (hinjA 19 17 (by decide)) (hinjA 19 18 (by decide))
  have t21 := mo408235_S20 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) t20 (a 20) (hm 19) (hinjA 20 0 (by decide)) (hinjA 20 1 (by decide)) (hinjA 20 2 (by decide)) (hinjA 20 3 (by decide)) (hinjA 20 4 (by decide)) (hinjA 20 5 (by decide)) (hinjA 20 6 (by decide)) (hinjA 20 7 (by decide)) (hinjA 20 8 (by decide)) (hinjA 20 9 (by decide)) (hinjA 20 10 (by decide)) (hinjA 20 11 (by decide)) (hinjA 20 12 (by decide)) (hinjA 20 13 (by decide)) (hinjA 20 14 (by decide)) (hinjA 20 15 (by decide)) (hinjA 20 16 (by decide)) (hinjA 20 17 (by decide)) (hinjA 20 18 (by decide)) (hinjA 20 19 (by decide))
  have t22 := mo408235_S21 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) t21 (a 21) (hm 20) (hinjA 21 0 (by decide)) (hinjA 21 1 (by decide)) (hinjA 21 2 (by decide)) (hinjA 21 3 (by decide)) (hinjA 21 4 (by decide)) (hinjA 21 5 (by decide)) (hinjA 21 6 (by decide)) (hinjA 21 7 (by decide)) (hinjA 21 8 (by decide)) (hinjA 21 9 (by decide)) (hinjA 21 10 (by decide)) (hinjA 21 11 (by decide)) (hinjA 21 12 (by decide)) (hinjA 21 13 (by decide)) (hinjA 21 14 (by decide)) (hinjA 21 15 (by decide)) (hinjA 21 16 (by decide)) (hinjA 21 17 (by decide)) (hinjA 21 18 (by decide)) (hinjA 21 19 (by decide)) (hinjA 21 20 (by decide))
  have t23 := mo408235_S22 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) t22 (a 22) (hm 21) (hinjA 22 0 (by decide)) (hinjA 22 1 (by decide)) (hinjA 22 2 (by decide)) (hinjA 22 3 (by decide)) (hinjA 22 4 (by decide)) (hinjA 22 5 (by decide)) (hinjA 22 6 (by decide)) (hinjA 22 7 (by decide)) (hinjA 22 8 (by decide)) (hinjA 22 9 (by decide)) (hinjA 22 10 (by decide)) (hinjA 22 11 (by decide)) (hinjA 22 12 (by decide)) (hinjA 22 13 (by decide)) (hinjA 22 14 (by decide)) (hinjA 22 15 (by decide)) (hinjA 22 16 (by decide)) (hinjA 22 17 (by decide)) (hinjA 22 18 (by decide)) (hinjA 22 19 (by decide)) (hinjA 22 20 (by decide)) (hinjA 22 21 (by decide))
  have t24 := mo408235_S23 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) t23 (a 23) (hm 22) (hinjA 23 0 (by decide)) (hinjA 23 1 (by decide)) (hinjA 23 2 (by decide)) (hinjA 23 3 (by decide)) (hinjA 23 4 (by decide)) (hinjA 23 5 (by decide)) (hinjA 23 6 (by decide)) (hinjA 23 7 (by decide)) (hinjA 23 8 (by decide)) (hinjA 23 9 (by decide)) (hinjA 23 10 (by decide)) (hinjA 23 11 (by decide)) (hinjA 23 12 (by decide)) (hinjA 23 13 (by decide)) (hinjA 23 14 (by decide)) (hinjA 23 15 (by decide)) (hinjA 23 16 (by decide)) (hinjA 23 17 (by decide)) (hinjA 23 18 (by decide)) (hinjA 23 19 (by decide)) (hinjA 23 20 (by decide)) (hinjA 23 21 (by decide)) (hinjA 23 22 (by decide))
  have t25 := mo408235_S24 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) t24 (a 24) (hm 23) (hinjA 24 0 (by decide)) (hinjA 24 1 (by decide)) (hinjA 24 2 (by decide)) (hinjA 24 3 (by decide)) (hinjA 24 4 (by decide)) (hinjA 24 5 (by decide)) (hinjA 24 6 (by decide)) (hinjA 24 7 (by decide)) (hinjA 24 8 (by decide)) (hinjA 24 9 (by decide)) (hinjA 24 10 (by decide)) (hinjA 24 11 (by decide)) (hinjA 24 12 (by decide)) (hinjA 24 13 (by decide)) (hinjA 24 14 (by decide)) (hinjA 24 15 (by decide)) (hinjA 24 16 (by decide)) (hinjA 24 17 (by decide)) (hinjA 24 18 (by decide)) (hinjA 24 19 (by decide)) (hinjA 24 20 (by decide)) (hinjA 24 21 (by decide)) (hinjA 24 22 (by decide)) (hinjA 24 23 (by decide))
  have t26 := mo408235_S25 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) t25 (a 25) (hm 24) (hinjA 25 0 (by decide)) (hinjA 25 1 (by decide)) (hinjA 25 2 (by decide)) (hinjA 25 3 (by decide)) (hinjA 25 4 (by decide)) (hinjA 25 5 (by decide)) (hinjA 25 6 (by decide)) (hinjA 25 7 (by decide)) (hinjA 25 8 (by decide)) (hinjA 25 9 (by decide)) (hinjA 25 10 (by decide)) (hinjA 25 11 (by decide)) (hinjA 25 12 (by decide)) (hinjA 25 13 (by decide)) (hinjA 25 14 (by decide)) (hinjA 25 15 (by decide)) (hinjA 25 16 (by decide)) (hinjA 25 17 (by decide)) (hinjA 25 18 (by decide)) (hinjA 25 19 (by decide)) (hinjA 25 20 (by decide)) (hinjA 25 21 (by decide)) (hinjA 25 22 (by decide)) (hinjA 25 23 (by decide)) (hinjA 25 24 (by decide))
  have t27 := mo408235_S26 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) t26 (a 26) (hm 25) (hinjA 26 0 (by decide)) (hinjA 26 1 (by decide)) (hinjA 26 2 (by decide)) (hinjA 26 3 (by decide)) (hinjA 26 4 (by decide)) (hinjA 26 5 (by decide)) (hinjA 26 6 (by decide)) (hinjA 26 7 (by decide)) (hinjA 26 8 (by decide)) (hinjA 26 9 (by decide)) (hinjA 26 10 (by decide)) (hinjA 26 11 (by decide)) (hinjA 26 12 (by decide)) (hinjA 26 13 (by decide)) (hinjA 26 14 (by decide)) (hinjA 26 15 (by decide)) (hinjA 26 16 (by decide)) (hinjA 26 17 (by decide)) (hinjA 26 18 (by decide)) (hinjA 26 19 (by decide)) (hinjA 26 20 (by decide)) (hinjA 26 21 (by decide)) (hinjA 26 22 (by decide)) (hinjA 26 23 (by decide)) (hinjA 26 24 (by decide)) (hinjA 26 25 (by decide))
  have t28 := mo408235_S27 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) t27 (a 27) (hm 26) (hinjA 27 0 (by decide)) (hinjA 27 1 (by decide)) (hinjA 27 2 (by decide)) (hinjA 27 3 (by decide)) (hinjA 27 4 (by decide)) (hinjA 27 5 (by decide)) (hinjA 27 6 (by decide)) (hinjA 27 7 (by decide)) (hinjA 27 8 (by decide)) (hinjA 27 9 (by decide)) (hinjA 27 10 (by decide)) (hinjA 27 11 (by decide)) (hinjA 27 12 (by decide)) (hinjA 27 13 (by decide)) (hinjA 27 14 (by decide)) (hinjA 27 15 (by decide)) (hinjA 27 16 (by decide)) (hinjA 27 17 (by decide)) (hinjA 27 18 (by decide)) (hinjA 27 19 (by decide)) (hinjA 27 20 (by decide)) (hinjA 27 21 (by decide)) (hinjA 27 22 (by decide)) (hinjA 27 23 (by decide)) (hinjA 27 24 (by decide)) (hinjA 27 25 (by decide)) (hinjA 27 26 (by decide))
  have t29 := mo408235_S28 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) t28 (a 28) (hm 27) (hinjA 28 0 (by decide)) (hinjA 28 1 (by decide)) (hinjA 28 2 (by decide)) (hinjA 28 3 (by decide)) (hinjA 28 4 (by decide)) (hinjA 28 5 (by decide)) (hinjA 28 6 (by decide)) (hinjA 28 7 (by decide)) (hinjA 28 8 (by decide)) (hinjA 28 9 (by decide)) (hinjA 28 10 (by decide)) (hinjA 28 11 (by decide)) (hinjA 28 12 (by decide)) (hinjA 28 13 (by decide)) (hinjA 28 14 (by decide)) (hinjA 28 15 (by decide)) (hinjA 28 16 (by decide)) (hinjA 28 17 (by decide)) (hinjA 28 18 (by decide)) (hinjA 28 19 (by decide)) (hinjA 28 20 (by decide)) (hinjA 28 21 (by decide)) (hinjA 28 22 (by decide)) (hinjA 28 23 (by decide)) (hinjA 28 24 (by decide)) (hinjA 28 25 (by decide)) (hinjA 28 26 (by decide)) (hinjA 28 27 (by decide))
  have t30 := mo408235_S29 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) t29 (a 29) (hm 28) (hinjA 29 0 (by decide)) (hinjA 29 1 (by decide)) (hinjA 29 2 (by decide)) (hinjA 29 3 (by decide)) (hinjA 29 4 (by decide)) (hinjA 29 5 (by decide)) (hinjA 29 6 (by decide)) (hinjA 29 7 (by decide)) (hinjA 29 8 (by decide)) (hinjA 29 9 (by decide)) (hinjA 29 10 (by decide)) (hinjA 29 11 (by decide)) (hinjA 29 12 (by decide)) (hinjA 29 13 (by decide)) (hinjA 29 14 (by decide)) (hinjA 29 15 (by decide)) (hinjA 29 16 (by decide)) (hinjA 29 17 (by decide)) (hinjA 29 18 (by decide)) (hinjA 29 19 (by decide)) (hinjA 29 20 (by decide)) (hinjA 29 21 (by decide)) (hinjA 29 22 (by decide)) (hinjA 29 23 (by decide)) (hinjA 29 24 (by decide)) (hinjA 29 25 (by decide)) (hinjA 29 26 (by decide)) (hinjA 29 27 (by decide)) (hinjA 29 28 (by decide))
  have t31 := mo408235_S30 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) t30 (a 30) (hm 29) (hinjA 30 0 (by decide)) (hinjA 30 1 (by decide)) (hinjA 30 2 (by decide)) (hinjA 30 3 (by decide)) (hinjA 30 4 (by decide)) (hinjA 30 5 (by decide)) (hinjA 30 6 (by decide)) (hinjA 30 7 (by decide)) (hinjA 30 8 (by decide)) (hinjA 30 9 (by decide)) (hinjA 30 10 (by decide)) (hinjA 30 11 (by decide)) (hinjA 30 12 (by decide)) (hinjA 30 13 (by decide)) (hinjA 30 14 (by decide)) (hinjA 30 15 (by decide)) (hinjA 30 16 (by decide)) (hinjA 30 17 (by decide)) (hinjA 30 18 (by decide)) (hinjA 30 19 (by decide)) (hinjA 30 20 (by decide)) (hinjA 30 21 (by decide)) (hinjA 30 22 (by decide)) (hinjA 30 23 (by decide)) (hinjA 30 24 (by decide)) (hinjA 30 25 (by decide)) (hinjA 30 26 (by decide)) (hinjA 30 27 (by decide)) (hinjA 30 28 (by decide)) (hinjA 30 29 (by decide))
  have key := mo408235_S31 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30) t31 (a 31) (hm 30) (hinjA 31 0 (by decide)) (hinjA 31 1 (by decide)) (hinjA 31 2 (by decide)) (hinjA 31 3 (by decide)) (hinjA 31 4 (by decide)) (hinjA 31 5 (by decide)) (hinjA 31 6 (by decide)) (hinjA 31 7 (by decide)) (hinjA 31 8 (by decide)) (hinjA 31 9 (by decide)) (hinjA 31 10 (by decide)) (hinjA 31 11 (by decide)) (hinjA 31 12 (by decide)) (hinjA 31 13 (by decide)) (hinjA 31 14 (by decide)) (hinjA 31 15 (by decide)) (hinjA 31 16 (by decide)) (hinjA 31 17 (by decide)) (hinjA 31 18 (by decide)) (hinjA 31 19 (by decide)) (hinjA 31 20 (by decide)) (hinjA 31 21 (by decide)) (hinjA 31 22 (by decide)) (hinjA 31 23 (by decide)) (hinjA 31 24 (by decide)) (hinjA 31 25 (by decide)) (hinjA 31 26 (by decide)) (hinjA 31 27 (by decide)) (hinjA 31 28 (by decide)) (hinjA 31 29 (by decide)) (hinjA 31 30 (by decide)) (ha 31)
  rw [← hfun] at key
  rcases key with hk | hk
  · refine ⟨-j, Or.inl fun i => ?_⟩
    have := congrFun hk (i - j)
    simp only [a, add_sub_cancel] at this
    rw [this, sub_eq_add_neg]
  · refine ⟨j, Or.inr fun i => ?_⟩
    have := congrFun hk (i - j)
    simp only [a, add_sub_cancel] at this
    rw [this, mo408235_hB2, neg_sub]

theorem OMA.solution : type_of% @OMA.S_mo_408235.main := by
  intro c d hc hd
  obtain ⟨k1, hc1 | hc1⟩ := mo408235_classify c hc <;>
    obtain ⟨k2, hd2 | hd2⟩ := mo408235_classify d hd
  · have e : ∀ y, mo408235_B y = c (y - k1) := fun y => by rw [hc1]; congr 1; abel
    exact ⟨k2 - k1, Or.inl fun i => by rw [hd2, e]; congr 1; abel⟩
  · have e : ∀ y, mo408235_B y = c (y - k1) := fun y => by rw [hc1]; congr 1; abel
    exact ⟨k2 - k1, Or.inr fun i => by rw [hd2, e]; congr 1; abel⟩
  · have e : ∀ y, mo408235_B y = c (k1 - y) := fun y => by rw [hc1]; congr 1; abel
    exact ⟨k1 - k2, Or.inr fun i => by rw [hd2, e]; congr 1; abel⟩
  · have e : ∀ y, mo408235_B y = c (k1 - y) := fun y => by rw [hc1]; congr 1; abel
    exact ⟨k1 - k2, Or.inl fun i => by rw [hd2, e]; congr 1; abel⟩
