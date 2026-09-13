/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import PseudoPrime.PseudoSquare.Computation.SmallN
import PseudoPrime.PrimeTest.Selfridge.Nonempty

/-!
# Finite pure `-1` Selfridge certificate

This module keeps the finite `g_{-1}` certificate on the PrimeTest side.  The
explicit candidates are `5, 7, 11, 13, 15, 17, 19, 21, 23, 27, 29, 31`:
the composite possibilities are `15`, `21`, and `27`, and the other values are
primes at least `5`.
-/

namespace PseudoPrime.PrimeTest

/-- For `abs(D)=15`, reciprocity exposes the factors `3` and `5` in the Jacobi value. -/
lemma jacobi_selfridgeD_neg_fifteen_iff {n : ℕ} (hn : Odd n) :
    jacobiSym (selfridgeD 15) n = -1 ↔ jacobiSym n 3 * jacobiSym n 5 = -1 := by
  rw [jacobi_selfridgeD (by decide) hn]
  rw [show (15 : ℕ) = 3 * 5 by norm_num only, jacobiSym.mul_right]

/-- For `abs(D)=21`, reciprocity exposes the factors `3` and `7` in the Jacobi value. -/
lemma jacobi_selfridgeD_neg_twenty_one_iff {n : ℕ} (hn : Odd n) :
    jacobiSym (selfridgeD 21) n = -1 ↔ jacobiSym n 3 * jacobiSym n 7 = -1 := by
  rw [jacobi_selfridgeD (by decide) hn]
  rw [show (21 : ℕ) = 3 * 7 by norm_num only, jacobiSym.mul_right]

/-- For `abs(D)=27`, reciprocity exposes the cubic factor `3`. -/
lemma jacobi_selfridgeD_neg_twenty_seven_iff {n : ℕ} (hn : Odd n) :
    jacobiSym (selfridgeD 27) n = -1 ↔ (jacobiSym n 3) ^ 3 = -1 := by
  rw [jacobi_selfridgeD (by decide) hn]
  rw [show (27 : ℕ) = 3 * 9 by norm_num only, jacobiSym.mul_right]
  rw [show (9 : ℕ) = 3 * 3 by norm_num only, jacobiSym.mul_right]
  constructor <;> intro h <;> simpa only [pow_succ, pow_zero, one_mul, pow_two, mul_assoc] using h

def smallClassicalNegOneCheck (n : Fin 750) : Bool :=
  decide
    (n.val % 2 = 1 →
      (∀ k : Fin 28, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 5 = -1 ∨
        jacobiSym n.val 7 = -1 ∨
        jacobiSym n.val 11 = -1 ∨
        jacobiSym n.val 13 = -1 ∨
        jacobiSym n.val 15 = -1 ∨
        jacobiSym n.val 17 = -1 ∨
        jacobiSym n.val 19 = -1 ∨
        jacobiSym n.val 21 = -1 ∨
        jacobiSym n.val 23 = -1 ∨
        jacobiSym n.val 27 = -1 ∨ jacobiSym n.val 29 = -1 ∨ jacobiSym n.val 31 = -1)

-- BEGIN GENERATED smallClassicalNegOneCheckAll_valid
/-- Kernel-checked checker block restricted to [0, 16). -/
private theorem smallClassicalNegOneCheckAll_valid_block_0 :
    ∀ n : Fin 750, 0 ≤ n.val → n.val < 16 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num <;> decide

/-- Kernel-checked checker block restricted to [16, 32). -/
private theorem smallClassicalNegOneCheckAll_valid_block_16 :
    ∀ n : Fin 750, 16 ≤ n.val → n.val < 32 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [32, 48). -/
private theorem smallClassicalNegOneCheckAll_valid_block_32 :
    ∀ n : Fin 750, 32 ≤ n.val → n.val < 48 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [48, 64). -/
private theorem smallClassicalNegOneCheckAll_valid_block_48 :
    ∀ n : Fin 750, 48 ≤ n.val → n.val < 64 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [64, 80). -/
private theorem smallClassicalNegOneCheckAll_valid_block_64 :
    ∀ n : Fin 750, 64 ≤ n.val → n.val < 80 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [80, 96). -/
private theorem smallClassicalNegOneCheckAll_valid_block_80 :
    ∀ n : Fin 750, 80 ≤ n.val → n.val < 96 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [96, 112). -/
private theorem smallClassicalNegOneCheckAll_valid_block_96 :
    ∀ n : Fin 750, 96 ≤ n.val → n.val < 112 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [112, 128). -/
private theorem smallClassicalNegOneCheckAll_valid_block_112 :
    ∀ n : Fin 750, 112 ≤ n.val → n.val < 128 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [128, 144). -/
private theorem smallClassicalNegOneCheckAll_valid_block_128 :
    ∀ n : Fin 750, 128 ≤ n.val → n.val < 144 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [144, 160). -/
private theorem smallClassicalNegOneCheckAll_valid_block_144 :
    ∀ n : Fin 750, 144 ≤ n.val → n.val < 160 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [160, 176). -/
private theorem smallClassicalNegOneCheckAll_valid_block_160 :
    ∀ n : Fin 750, 160 ≤ n.val → n.val < 176 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [176, 192). -/
private theorem smallClassicalNegOneCheckAll_valid_block_176 :
    ∀ n : Fin 750, 176 ≤ n.val → n.val < 192 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [192, 208). -/
private theorem smallClassicalNegOneCheckAll_valid_block_192 :
    ∀ n : Fin 750, 192 ≤ n.val → n.val < 208 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [208, 224). -/
private theorem smallClassicalNegOneCheckAll_valid_block_208 :
    ∀ n : Fin 750, 208 ≤ n.val → n.val < 224 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [224, 240). -/
private theorem smallClassicalNegOneCheckAll_valid_block_224 :
    ∀ n : Fin 750, 224 ≤ n.val → n.val < 240 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [240, 256). -/
private theorem smallClassicalNegOneCheckAll_valid_block_240 :
    ∀ n : Fin 750, 240 ≤ n.val → n.val < 256 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [256, 272). -/
private theorem smallClassicalNegOneCheckAll_valid_block_256 :
    ∀ n : Fin 750, 256 ≤ n.val → n.val < 272 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [272, 288). -/
private theorem smallClassicalNegOneCheckAll_valid_block_272 :
    ∀ n : Fin 750, 272 ≤ n.val → n.val < 288 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [288, 304). -/
private theorem smallClassicalNegOneCheckAll_valid_block_288 :
    ∀ n : Fin 750, 288 ≤ n.val → n.val < 304 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [304, 320). -/
private theorem smallClassicalNegOneCheckAll_valid_block_304 :
    ∀ n : Fin 750, 304 ≤ n.val → n.val < 320 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [320, 336). -/
private theorem smallClassicalNegOneCheckAll_valid_block_320 :
    ∀ n : Fin 750, 320 ≤ n.val → n.val < 336 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [336, 352). -/
private theorem smallClassicalNegOneCheckAll_valid_block_336 :
    ∀ n : Fin 750, 336 ≤ n.val → n.val < 352 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [352, 368). -/
private theorem smallClassicalNegOneCheckAll_valid_block_352 :
    ∀ n : Fin 750, 352 ≤ n.val → n.val < 368 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [368, 384). -/
private theorem smallClassicalNegOneCheckAll_valid_block_368 :
    ∀ n : Fin 750, 368 ≤ n.val → n.val < 384 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [384, 400). -/
private theorem smallClassicalNegOneCheckAll_valid_block_384 :
    ∀ n : Fin 750, 384 ≤ n.val → n.val < 400 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [400, 416). -/
private theorem smallClassicalNegOneCheckAll_valid_block_400 :
    ∀ n : Fin 750, 400 ≤ n.val → n.val < 416 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [416, 432). -/
private theorem smallClassicalNegOneCheckAll_valid_block_416 :
    ∀ n : Fin 750, 416 ≤ n.val → n.val < 432 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [432, 448). -/
private theorem smallClassicalNegOneCheckAll_valid_block_432 :
    ∀ n : Fin 750, 432 ≤ n.val → n.val < 448 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [448, 464). -/
private theorem smallClassicalNegOneCheckAll_valid_block_448 :
    ∀ n : Fin 750, 448 ≤ n.val → n.val < 464 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [464, 480). -/
private theorem smallClassicalNegOneCheckAll_valid_block_464 :
    ∀ n : Fin 750, 464 ≤ n.val → n.val < 480 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [480, 496). -/
private theorem smallClassicalNegOneCheckAll_valid_block_480 :
    ∀ n : Fin 750, 480 ≤ n.val → n.val < 496 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [496, 512). -/
private theorem smallClassicalNegOneCheckAll_valid_block_496 :
    ∀ n : Fin 750, 496 ≤ n.val → n.val < 512 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [512, 528). -/
private theorem smallClassicalNegOneCheckAll_valid_block_512 :
    ∀ n : Fin 750, 512 ≤ n.val → n.val < 528 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [528, 544). -/
private theorem smallClassicalNegOneCheckAll_valid_block_528 :
    ∀ n : Fin 750, 528 ≤ n.val → n.val < 544 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [544, 560). -/
private theorem smallClassicalNegOneCheckAll_valid_block_544 :
    ∀ n : Fin 750, 544 ≤ n.val → n.val < 560 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [560, 576). -/
private theorem smallClassicalNegOneCheckAll_valid_block_560 :
    ∀ n : Fin 750, 560 ≤ n.val → n.val < 576 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [576, 592). -/
private theorem smallClassicalNegOneCheckAll_valid_block_576 :
    ∀ n : Fin 750, 576 ≤ n.val → n.val < 592 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [592, 608). -/
private theorem smallClassicalNegOneCheckAll_valid_block_592 :
    ∀ n : Fin 750, 592 ≤ n.val → n.val < 608 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [608, 624). -/
private theorem smallClassicalNegOneCheckAll_valid_block_608 :
    ∀ n : Fin 750, 608 ≤ n.val → n.val < 624 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [624, 640). -/
private theorem smallClassicalNegOneCheckAll_valid_block_624 :
    ∀ n : Fin 750, 624 ≤ n.val → n.val < 640 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [640, 656). -/
private theorem smallClassicalNegOneCheckAll_valid_block_640 :
    ∀ n : Fin 750, 640 ≤ n.val → n.val < 656 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [656, 672). -/
private theorem smallClassicalNegOneCheckAll_valid_block_656 :
    ∀ n : Fin 750, 656 ≤ n.val → n.val < 672 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [672, 688). -/
private theorem smallClassicalNegOneCheckAll_valid_block_672 :
    ∀ n : Fin 750, 672 ≤ n.val → n.val < 688 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [688, 704). -/
private theorem smallClassicalNegOneCheckAll_valid_block_688 :
    ∀ n : Fin 750, 688 ≤ n.val → n.val < 704 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [704, 720). -/
private theorem smallClassicalNegOneCheckAll_valid_block_704 :
    ∀ n : Fin 750, 704 ≤ n.val → n.val < 720 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [720, 736). -/
private theorem smallClassicalNegOneCheckAll_valid_block_720 :
    ∀ n : Fin 750, 720 ≤ n.val → n.val < 736 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [736, 750). -/
private theorem smallClassicalNegOneCheckAll_valid_block_736 :
    ∀ n : Fin 750, 736 ≤ n.val → n.val < 750 →
      smallClassicalNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallClassicalNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

theorem smallClassicalNegOneCheckAll_valid :
    (List.finRange 750).all smallClassicalNegOneCheck = true := by
  apply List.all_eq_true.mpr
  intro n hn
  by_cases h368 : n.val < 368
  · by_cases h176 : n.val < 176
    · by_cases h80 : n.val < 80
      · by_cases h32 : n.val < 32
        · by_cases h16 : n.val < 16
          · exact smallClassicalNegOneCheckAll_valid_block_0 n (by omega) (by omega)
          · exact smallClassicalNegOneCheckAll_valid_block_16 n (by omega) (by omega)
        · by_cases h48 : n.val < 48
          · exact smallClassicalNegOneCheckAll_valid_block_32 n (by omega) (by omega)
          · by_cases h64 : n.val < 64
            · exact smallClassicalNegOneCheckAll_valid_block_48 n (by omega) (by omega)
            · exact smallClassicalNegOneCheckAll_valid_block_64 n (by omega) (by omega)
      · by_cases h128 : n.val < 128
        · by_cases h96 : n.val < 96
          · exact smallClassicalNegOneCheckAll_valid_block_80 n (by omega) (by omega)
          · by_cases h112 : n.val < 112
            · exact smallClassicalNegOneCheckAll_valid_block_96 n (by omega) (by omega)
            · exact smallClassicalNegOneCheckAll_valid_block_112 n (by omega) (by omega)
        · by_cases h144 : n.val < 144
          · exact smallClassicalNegOneCheckAll_valid_block_128 n (by omega) (by omega)
          · by_cases h160 : n.val < 160
            · exact smallClassicalNegOneCheckAll_valid_block_144 n (by omega) (by omega)
            · exact smallClassicalNegOneCheckAll_valid_block_160 n (by omega) (by omega)
    · by_cases h272 : n.val < 272
      · by_cases h224 : n.val < 224
        · by_cases h192 : n.val < 192
          · exact smallClassicalNegOneCheckAll_valid_block_176 n (by omega) (by omega)
          · by_cases h208 : n.val < 208
            · exact smallClassicalNegOneCheckAll_valid_block_192 n (by omega) (by omega)
            · exact smallClassicalNegOneCheckAll_valid_block_208 n (by omega) (by omega)
        · by_cases h240 : n.val < 240
          · exact smallClassicalNegOneCheckAll_valid_block_224 n (by omega) (by omega)
          · by_cases h256 : n.val < 256
            · exact smallClassicalNegOneCheckAll_valid_block_240 n (by omega) (by omega)
            · exact smallClassicalNegOneCheckAll_valid_block_256 n (by omega) (by omega)
      · by_cases h320 : n.val < 320
        · by_cases h288 : n.val < 288
          · exact smallClassicalNegOneCheckAll_valid_block_272 n (by omega) (by omega)
          · by_cases h304 : n.val < 304
            · exact smallClassicalNegOneCheckAll_valid_block_288 n (by omega) (by omega)
            · exact smallClassicalNegOneCheckAll_valid_block_304 n (by omega) (by omega)
        · by_cases h336 : n.val < 336
          · exact smallClassicalNegOneCheckAll_valid_block_320 n (by omega) (by omega)
          · by_cases h352 : n.val < 352
            · exact smallClassicalNegOneCheckAll_valid_block_336 n (by omega) (by omega)
            · exact smallClassicalNegOneCheckAll_valid_block_352 n (by omega) (by omega)
  · by_cases h560 : n.val < 560
    · by_cases h464 : n.val < 464
      · by_cases h416 : n.val < 416
        · by_cases h384 : n.val < 384
          · exact smallClassicalNegOneCheckAll_valid_block_368 n (by omega) (by omega)
          · by_cases h400 : n.val < 400
            · exact smallClassicalNegOneCheckAll_valid_block_384 n (by omega) (by omega)
            · exact smallClassicalNegOneCheckAll_valid_block_400 n (by omega) (by omega)
        · by_cases h432 : n.val < 432
          · exact smallClassicalNegOneCheckAll_valid_block_416 n (by omega) (by omega)
          · by_cases h448 : n.val < 448
            · exact smallClassicalNegOneCheckAll_valid_block_432 n (by omega) (by omega)
            · exact smallClassicalNegOneCheckAll_valid_block_448 n (by omega) (by omega)
      · by_cases h512 : n.val < 512
        · by_cases h480 : n.val < 480
          · exact smallClassicalNegOneCheckAll_valid_block_464 n (by omega) (by omega)
          · by_cases h496 : n.val < 496
            · exact smallClassicalNegOneCheckAll_valid_block_480 n (by omega) (by omega)
            · exact smallClassicalNegOneCheckAll_valid_block_496 n (by omega) (by omega)
        · by_cases h528 : n.val < 528
          · exact smallClassicalNegOneCheckAll_valid_block_512 n (by omega) (by omega)
          · by_cases h544 : n.val < 544
            · exact smallClassicalNegOneCheckAll_valid_block_528 n (by omega) (by omega)
            · exact smallClassicalNegOneCheckAll_valid_block_544 n (by omega) (by omega)
    · by_cases h656 : n.val < 656
      · by_cases h608 : n.val < 608
        · by_cases h576 : n.val < 576
          · exact smallClassicalNegOneCheckAll_valid_block_560 n (by omega) (by omega)
          · by_cases h592 : n.val < 592
            · exact smallClassicalNegOneCheckAll_valid_block_576 n (by omega) (by omega)
            · exact smallClassicalNegOneCheckAll_valid_block_592 n (by omega) (by omega)
        · by_cases h624 : n.val < 624
          · exact smallClassicalNegOneCheckAll_valid_block_608 n (by omega) (by omega)
          · by_cases h640 : n.val < 640
            · exact smallClassicalNegOneCheckAll_valid_block_624 n (by omega) (by omega)
            · exact smallClassicalNegOneCheckAll_valid_block_640 n (by omega) (by omega)
      · by_cases h704 : n.val < 704
        · by_cases h672 : n.val < 672
          · exact smallClassicalNegOneCheckAll_valid_block_656 n (by omega) (by omega)
          · by_cases h688 : n.val < 688
            · exact smallClassicalNegOneCheckAll_valid_block_672 n (by omega) (by omega)
            · exact smallClassicalNegOneCheckAll_valid_block_688 n (by omega) (by omega)
        · by_cases h720 : n.val < 720
          · exact smallClassicalNegOneCheckAll_valid_block_704 n (by omega) (by omega)
          · by_cases h736 : n.val < 736
            · exact smallClassicalNegOneCheckAll_valid_block_720 n (by omega) (by omega)
            · exact smallClassicalNegOneCheckAll_valid_block_736 n (by omega) (by omega)

-- END GENERATED smallClassicalNegOneCheckAll_valid

/-- The finite certificate bounds the classical pure `-1` first stop.

Assumptions: `n` is odd, nonsquare, and below `750`, and the stopping set is nonempty.
Conclusion: the least classical candidate with Jacobi value `-1` is at most `31`.
The certificate permits exactly the relevant candidates `5, 7, 11, 13,
15, 17, 19, 21, 23, 27, 29, 31`; the composite candidates are `15`, `21`, and `27`.
Proof: reduce the `Fin 750` checker to its proposition and apply first-stop minimality.
Role: this is the finite `g_{-1}` branch before the analytic bound.
-/
theorem classicalFirstStopNegOne_le_31_of_lt_750 {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hn750 : n < 750) (hs : (FirstStopNegOneSet isClassicalCandidate n).Nonempty) :
    firstStopNegOne isClassicalCandidate n hs ≤ 31 := by
  have hall : ∀ m ∈ List.finRange 750, smallClassicalNegOneCheck m = true := by
    simpa only [smallClassicalNegOneCheck] using
      (List.all_eq_true.mp smallClassicalNegOneCheckAll_valid)
  have hncheck := hall ⟨n, hn750⟩ (by simp only [List.mem_finRange])
  have hdec :
    decide
        (n % 2 = 1 →
          (∀ k : Fin 28, n ≠ k.val ^ 2) →
          jacobiSym n 5 = -1 ∨
            jacobiSym n 7 = -1 ∨
            jacobiSym n 11 = -1 ∨
            jacobiSym n 13 = -1 ∨
            jacobiSym n 15 = -1 ∨
            jacobiSym n 17 = -1 ∨
            jacobiSym n 19 = -1 ∨
            jacobiSym n 21 = -1 ∨
            jacobiSym n 23 = -1 ∨ jacobiSym n 27 = -1 ∨ jacobiSym n 29 = -1 ∨ jacobiSym n 31 = -1) =
      true := by
    simpa only [smallClassicalNegOneCheck] using hncheck
  have hmem_of {i : ℕ} (hi : 5 ≤ i) (hiodd : Odd i) (hjacobi : jacobiSym n i = -1) :
    i ∈ FirstStopNegOneSet isClassicalCandidate n := by
    refine ⟨⟨hi, hiodd⟩, ?_⟩
    rw [jacobi_selfridgeD hiodd hn]
    exact hjacobi
  have hex : ∃ i : ℕ, i ≤ 31 ∧ i ∈ FirstStopNegOneSet isClassicalCandidate n := by
    rcases
      (of_decide_eq_true hdec) (Nat.odd_iff.mp hn)
        (PseudoSquare.SmallN.fin28_ne_sq_of_not_isSquare hns) with
      h5 | h7 | h11 | h13 | h15 | h17 | h19 | h21 | h23 | h27 | h29 | h31
    all_goals
      first
      | exact ⟨5, by norm_num only, hmem_of (by norm_num only) (by decide) h5⟩
      | exact ⟨7, by norm_num only, hmem_of (by norm_num only) (by decide) h7⟩
      | exact ⟨11, by norm_num only, hmem_of (by norm_num only) (by decide) h11⟩
      | exact ⟨13, by norm_num only, hmem_of (by norm_num only) (by decide) h13⟩
      | exact ⟨15, by norm_num only, hmem_of (by norm_num only) (by decide) h15⟩
      | exact ⟨17, by norm_num only, hmem_of (by norm_num only) (by decide) h17⟩
      | exact ⟨19, by norm_num only, hmem_of (by norm_num only) (by decide) h19⟩
      | exact ⟨21, by norm_num only, hmem_of (by norm_num only) (by decide) h21⟩
      | exact ⟨23, by norm_num only, hmem_of (by norm_num only) (by decide) h23⟩
      | exact ⟨27, by norm_num only, hmem_of (by norm_num only) (by decide) h27⟩
      | exact ⟨29, by norm_num only, hmem_of (by norm_num only) (by decide) h29⟩
      | exact ⟨31, by norm_num only, hmem_of (by norm_num only) (by decide) h31⟩
  obtain ⟨i, hi, hmem⟩ := hex
  exact (firstStopNegOne_le isClassicalCandidate n hs hmem).trans hi

/-- The finite certificate bounds the magnitude of the classical pure `-1` value.

Assumptions: `n` is odd, nonsquare, and below `750`, and the stopping set is nonempty.
Conclusion: the absolute value of the corresponding `g_{-1}` value is at most `31`.
Proof: transport the first-stop bound through `selfridgeD_natAbs`.
Role: this is the explicit finite `g_{-1}` bound before any analytic estimate.
-/
theorem classicalSelfridgeD_firstStopNegOne_natAbs_le_31_of_lt_750 {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hn750 : n < 750)
    (hs : (FirstStopNegOneSet isClassicalCandidate n).Nonempty) :
    (selfridgeD (firstStopNegOne isClassicalCandidate n hs)).natAbs ≤ 31 := by
  simpa only [selfridgeD_natAbs] using classicalFirstStopNegOne_le_31_of_lt_750 hn hns hn750 hs

end PseudoPrime.PrimeTest
