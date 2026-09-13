/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.LegendreSymbol
import PseudoPrime.PseudoSquare.Bounds.WitnessMaximum

/-!
# Kernel-checked finite bound below `750`

This file certifies the exceptional finite range in formula (5.4). The search is restricted to
ten explicit odd primes at most `31`; `norm_num` produces proofs of the fixed Jacobi values.
-/

namespace PseudoPrime.PseudoSquare

/-- The exact finite statement needed for character levels below `750`. -/
def SmallNegOneWitnessBound : Prop :=
  ∀ n : ℕ,
    (hn : Odd n) →
      (hns : ¬IsSquare n) →
      n < 750 →
        NumberTheory.primeNegOneWitness n
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns) ≤
          31

/-- The finite proposition checked by reduction before it is lifted to mathematical inputs. -/
def SmallNegOneCertificate : Prop :=
  ∀ n : Fin 750,
    n.val % 2 = 1 →
      (∀ k : Fin 28, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 = -1 ∨
        jacobiSym n.val 5 = -1 ∨
        jacobiSym n.val 7 = -1 ∨
        jacobiSym n.val 11 = -1 ∨
        jacobiSym n.val 13 = -1 ∨
        jacobiSym n.val 17 = -1 ∨
        jacobiSym n.val 19 = -1 ∨
        jacobiSym n.val 23 = -1 ∨ jacobiSym n.val 29 = -1 ∨ jacobiSym n.val 31 = -1

def smallNegOneCheck (n : Fin 750) : Bool :=
  decide
    (n.val % 2 = 1 →
      (∀ k : Fin 28, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 = -1 ∨
        jacobiSym n.val 5 = -1 ∨
        jacobiSym n.val 7 = -1 ∨
        jacobiSym n.val 11 = -1 ∨
        jacobiSym n.val 13 = -1 ∨
        jacobiSym n.val 17 = -1 ∨
        jacobiSym n.val 19 = -1 ∨
        jacobiSym n.val 23 = -1 ∨ jacobiSym n.val 29 = -1 ∨ jacobiSym n.val 31 = -1)

def smallNegOneCheckAll : Bool :=
  (List.finRange 750).all smallNegOneCheck

-- BEGIN GENERATED smallNegOneCheckAll_valid
/-- Kernel-checked checker block restricted to [0, 16). -/
private theorem smallNegOneCheckAll_valid_block_0 :
    ∀ n : Fin 750, 0 ≤ n.val → n.val < 16 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num <;> decide

/-- Kernel-checked checker block restricted to [16, 32). -/
private theorem smallNegOneCheckAll_valid_block_16 :
    ∀ n : Fin 750, 16 ≤ n.val → n.val < 32 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [32, 48). -/
private theorem smallNegOneCheckAll_valid_block_32 :
    ∀ n : Fin 750, 32 ≤ n.val → n.val < 48 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [48, 64). -/
private theorem smallNegOneCheckAll_valid_block_48 :
    ∀ n : Fin 750, 48 ≤ n.val → n.val < 64 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [64, 80). -/
private theorem smallNegOneCheckAll_valid_block_64 :
    ∀ n : Fin 750, 64 ≤ n.val → n.val < 80 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [80, 96). -/
private theorem smallNegOneCheckAll_valid_block_80 :
    ∀ n : Fin 750, 80 ≤ n.val → n.val < 96 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [96, 112). -/
private theorem smallNegOneCheckAll_valid_block_96 :
    ∀ n : Fin 750, 96 ≤ n.val → n.val < 112 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [112, 128). -/
private theorem smallNegOneCheckAll_valid_block_112 :
    ∀ n : Fin 750, 112 ≤ n.val → n.val < 128 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [128, 144). -/
private theorem smallNegOneCheckAll_valid_block_128 :
    ∀ n : Fin 750, 128 ≤ n.val → n.val < 144 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [144, 160). -/
private theorem smallNegOneCheckAll_valid_block_144 :
    ∀ n : Fin 750, 144 ≤ n.val → n.val < 160 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [160, 176). -/
private theorem smallNegOneCheckAll_valid_block_160 :
    ∀ n : Fin 750, 160 ≤ n.val → n.val < 176 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [176, 192). -/
private theorem smallNegOneCheckAll_valid_block_176 :
    ∀ n : Fin 750, 176 ≤ n.val → n.val < 192 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [192, 208). -/
private theorem smallNegOneCheckAll_valid_block_192 :
    ∀ n : Fin 750, 192 ≤ n.val → n.val < 208 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [208, 224). -/
private theorem smallNegOneCheckAll_valid_block_208 :
    ∀ n : Fin 750, 208 ≤ n.val → n.val < 224 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [224, 240). -/
private theorem smallNegOneCheckAll_valid_block_224 :
    ∀ n : Fin 750, 224 ≤ n.val → n.val < 240 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [240, 256). -/
private theorem smallNegOneCheckAll_valid_block_240 :
    ∀ n : Fin 750, 240 ≤ n.val → n.val < 256 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [256, 272). -/
private theorem smallNegOneCheckAll_valid_block_256 :
    ∀ n : Fin 750, 256 ≤ n.val → n.val < 272 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [272, 288). -/
private theorem smallNegOneCheckAll_valid_block_272 :
    ∀ n : Fin 750, 272 ≤ n.val → n.val < 288 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [288, 304). -/
private theorem smallNegOneCheckAll_valid_block_288 :
    ∀ n : Fin 750, 288 ≤ n.val → n.val < 304 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [304, 320). -/
private theorem smallNegOneCheckAll_valid_block_304 :
    ∀ n : Fin 750, 304 ≤ n.val → n.val < 320 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [320, 336). -/
private theorem smallNegOneCheckAll_valid_block_320 :
    ∀ n : Fin 750, 320 ≤ n.val → n.val < 336 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [336, 352). -/
private theorem smallNegOneCheckAll_valid_block_336 :
    ∀ n : Fin 750, 336 ≤ n.val → n.val < 352 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [352, 368). -/
private theorem smallNegOneCheckAll_valid_block_352 :
    ∀ n : Fin 750, 352 ≤ n.val → n.val < 368 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [368, 384). -/
private theorem smallNegOneCheckAll_valid_block_368 :
    ∀ n : Fin 750, 368 ≤ n.val → n.val < 384 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [384, 400). -/
private theorem smallNegOneCheckAll_valid_block_384 :
    ∀ n : Fin 750, 384 ≤ n.val → n.val < 400 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [400, 416). -/
private theorem smallNegOneCheckAll_valid_block_400 :
    ∀ n : Fin 750, 400 ≤ n.val → n.val < 416 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [416, 432). -/
private theorem smallNegOneCheckAll_valid_block_416 :
    ∀ n : Fin 750, 416 ≤ n.val → n.val < 432 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [432, 448). -/
private theorem smallNegOneCheckAll_valid_block_432 :
    ∀ n : Fin 750, 432 ≤ n.val → n.val < 448 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [448, 464). -/
private theorem smallNegOneCheckAll_valid_block_448 :
    ∀ n : Fin 750, 448 ≤ n.val → n.val < 464 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [464, 480). -/
private theorem smallNegOneCheckAll_valid_block_464 :
    ∀ n : Fin 750, 464 ≤ n.val → n.val < 480 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [480, 496). -/
private theorem smallNegOneCheckAll_valid_block_480 :
    ∀ n : Fin 750, 480 ≤ n.val → n.val < 496 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [496, 512). -/
private theorem smallNegOneCheckAll_valid_block_496 :
    ∀ n : Fin 750, 496 ≤ n.val → n.val < 512 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [512, 528). -/
private theorem smallNegOneCheckAll_valid_block_512 :
    ∀ n : Fin 750, 512 ≤ n.val → n.val < 528 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [528, 544). -/
private theorem smallNegOneCheckAll_valid_block_528 :
    ∀ n : Fin 750, 528 ≤ n.val → n.val < 544 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [544, 560). -/
private theorem smallNegOneCheckAll_valid_block_544 :
    ∀ n : Fin 750, 544 ≤ n.val → n.val < 560 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [560, 576). -/
private theorem smallNegOneCheckAll_valid_block_560 :
    ∀ n : Fin 750, 560 ≤ n.val → n.val < 576 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [576, 592). -/
private theorem smallNegOneCheckAll_valid_block_576 :
    ∀ n : Fin 750, 576 ≤ n.val → n.val < 592 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [592, 608). -/
private theorem smallNegOneCheckAll_valid_block_592 :
    ∀ n : Fin 750, 592 ≤ n.val → n.val < 608 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [608, 624). -/
private theorem smallNegOneCheckAll_valid_block_608 :
    ∀ n : Fin 750, 608 ≤ n.val → n.val < 624 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [624, 640). -/
private theorem smallNegOneCheckAll_valid_block_624 :
    ∀ n : Fin 750, 624 ≤ n.val → n.val < 640 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [640, 656). -/
private theorem smallNegOneCheckAll_valid_block_640 :
    ∀ n : Fin 750, 640 ≤ n.val → n.val < 656 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [656, 672). -/
private theorem smallNegOneCheckAll_valid_block_656 :
    ∀ n : Fin 750, 656 ≤ n.val → n.val < 672 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [672, 688). -/
private theorem smallNegOneCheckAll_valid_block_672 :
    ∀ n : Fin 750, 672 ≤ n.val → n.val < 688 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [688, 704). -/
private theorem smallNegOneCheckAll_valid_block_688 :
    ∀ n : Fin 750, 688 ≤ n.val → n.val < 704 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [704, 720). -/
private theorem smallNegOneCheckAll_valid_block_704 :
    ∀ n : Fin 750, 704 ≤ n.val → n.val < 720 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

/-- Kernel-checked checker block restricted to [720, 736). -/
private theorem smallNegOneCheckAll_valid_block_720 :
    ∀ n : Fin 750, 720 ≤ n.val → n.val < 736 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num
  decide

/-- Kernel-checked checker block restricted to [736, 750). -/
private theorem smallNegOneCheckAll_valid_block_736 :
    ∀ n : Fin 750, 736 ≤ n.val → n.val < 750 →
      smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num

theorem smallNegOneCheckAll_valid :
    (List.finRange 750).all smallNegOneCheck = true := by
  apply List.all_eq_true.mpr
  intro n hn
  by_cases h368 : n.val < 368
  · by_cases h176 : n.val < 176
    · by_cases h80 : n.val < 80
      · by_cases h32 : n.val < 32
        · by_cases h16 : n.val < 16
          · exact smallNegOneCheckAll_valid_block_0 n (by omega) (by omega)
          · exact smallNegOneCheckAll_valid_block_16 n (by omega) (by omega)
        · by_cases h48 : n.val < 48
          · exact smallNegOneCheckAll_valid_block_32 n (by omega) (by omega)
          · by_cases h64 : n.val < 64
            · exact smallNegOneCheckAll_valid_block_48 n (by omega) (by omega)
            · exact smallNegOneCheckAll_valid_block_64 n (by omega) (by omega)
      · by_cases h128 : n.val < 128
        · by_cases h96 : n.val < 96
          · exact smallNegOneCheckAll_valid_block_80 n (by omega) (by omega)
          · by_cases h112 : n.val < 112
            · exact smallNegOneCheckAll_valid_block_96 n (by omega) (by omega)
            · exact smallNegOneCheckAll_valid_block_112 n (by omega) (by omega)
        · by_cases h144 : n.val < 144
          · exact smallNegOneCheckAll_valid_block_128 n (by omega) (by omega)
          · by_cases h160 : n.val < 160
            · exact smallNegOneCheckAll_valid_block_144 n (by omega) (by omega)
            · exact smallNegOneCheckAll_valid_block_160 n (by omega) (by omega)
    · by_cases h272 : n.val < 272
      · by_cases h224 : n.val < 224
        · by_cases h192 : n.val < 192
          · exact smallNegOneCheckAll_valid_block_176 n (by omega) (by omega)
          · by_cases h208 : n.val < 208
            · exact smallNegOneCheckAll_valid_block_192 n (by omega) (by omega)
            · exact smallNegOneCheckAll_valid_block_208 n (by omega) (by omega)
        · by_cases h240 : n.val < 240
          · exact smallNegOneCheckAll_valid_block_224 n (by omega) (by omega)
          · by_cases h256 : n.val < 256
            · exact smallNegOneCheckAll_valid_block_240 n (by omega) (by omega)
            · exact smallNegOneCheckAll_valid_block_256 n (by omega) (by omega)
      · by_cases h320 : n.val < 320
        · by_cases h288 : n.val < 288
          · exact smallNegOneCheckAll_valid_block_272 n (by omega) (by omega)
          · by_cases h304 : n.val < 304
            · exact smallNegOneCheckAll_valid_block_288 n (by omega) (by omega)
            · exact smallNegOneCheckAll_valid_block_304 n (by omega) (by omega)
        · by_cases h336 : n.val < 336
          · exact smallNegOneCheckAll_valid_block_320 n (by omega) (by omega)
          · by_cases h352 : n.val < 352
            · exact smallNegOneCheckAll_valid_block_336 n (by omega) (by omega)
            · exact smallNegOneCheckAll_valid_block_352 n (by omega) (by omega)
  · by_cases h560 : n.val < 560
    · by_cases h464 : n.val < 464
      · by_cases h416 : n.val < 416
        · by_cases h384 : n.val < 384
          · exact smallNegOneCheckAll_valid_block_368 n (by omega) (by omega)
          · by_cases h400 : n.val < 400
            · exact smallNegOneCheckAll_valid_block_384 n (by omega) (by omega)
            · exact smallNegOneCheckAll_valid_block_400 n (by omega) (by omega)
        · by_cases h432 : n.val < 432
          · exact smallNegOneCheckAll_valid_block_416 n (by omega) (by omega)
          · by_cases h448 : n.val < 448
            · exact smallNegOneCheckAll_valid_block_432 n (by omega) (by omega)
            · exact smallNegOneCheckAll_valid_block_448 n (by omega) (by omega)
      · by_cases h512 : n.val < 512
        · by_cases h480 : n.val < 480
          · exact smallNegOneCheckAll_valid_block_464 n (by omega) (by omega)
          · by_cases h496 : n.val < 496
            · exact smallNegOneCheckAll_valid_block_480 n (by omega) (by omega)
            · exact smallNegOneCheckAll_valid_block_496 n (by omega) (by omega)
        · by_cases h528 : n.val < 528
          · exact smallNegOneCheckAll_valid_block_512 n (by omega) (by omega)
          · by_cases h544 : n.val < 544
            · exact smallNegOneCheckAll_valid_block_528 n (by omega) (by omega)
            · exact smallNegOneCheckAll_valid_block_544 n (by omega) (by omega)
    · by_cases h656 : n.val < 656
      · by_cases h608 : n.val < 608
        · by_cases h576 : n.val < 576
          · exact smallNegOneCheckAll_valid_block_560 n (by omega) (by omega)
          · by_cases h592 : n.val < 592
            · exact smallNegOneCheckAll_valid_block_576 n (by omega) (by omega)
            · exact smallNegOneCheckAll_valid_block_592 n (by omega) (by omega)
        · by_cases h624 : n.val < 624
          · exact smallNegOneCheckAll_valid_block_608 n (by omega) (by omega)
          · by_cases h640 : n.val < 640
            · exact smallNegOneCheckAll_valid_block_624 n (by omega) (by omega)
            · exact smallNegOneCheckAll_valid_block_640 n (by omega) (by omega)
      · by_cases h704 : n.val < 704
        · by_cases h672 : n.val < 672
          · exact smallNegOneCheckAll_valid_block_656 n (by omega) (by omega)
          · by_cases h688 : n.val < 688
            · exact smallNegOneCheckAll_valid_block_672 n (by omega) (by omega)
            · exact smallNegOneCheckAll_valid_block_688 n (by omega) (by omega)
        · by_cases h720 : n.val < 720
          · exact smallNegOneCheckAll_valid_block_704 n (by omega) (by omega)
          · by_cases h736 : n.val < 736
            · exact smallNegOneCheckAll_valid_block_720 n (by omega) (by omega)
            · exact smallNegOneCheckAll_valid_block_736 n (by omega) (by omega)

-- END GENERATED smallNegOneCheckAll_valid

theorem smallNegOneCertificate_valid_list : SmallNegOneCertificate := by
  intro n hodd hnsq
  have hall : ∀ m ∈ List.finRange 750, smallNegOneCheck m = true := by
    simpa only [smallNegOneCheckAll] using (List.all_eq_true.mp smallNegOneCheckAll_valid)
  have hn := hall n (by simp only [List.mem_finRange])
  have hdec :
    decide
        (n.val % 2 = 1 →
          (∀ k : Fin 28, n.val ≠ k.val ^ 2) →
          jacobiSym n.val 3 = -1 ∨
            jacobiSym n.val 5 = -1 ∨
            jacobiSym n.val 7 = -1 ∨
            jacobiSym n.val 11 = -1 ∨
            jacobiSym n.val 13 = -1 ∨
            jacobiSym n.val 17 = -1 ∨
            jacobiSym n.val 19 = -1 ∨
            jacobiSym n.val 23 = -1 ∨ jacobiSym n.val 29 = -1 ∨ jacobiSym n.val 31 = -1) =
      true := by
    simpa only [smallNegOneCheck] using hn
  exact (of_decide_eq_true hdec) hodd hnsq

theorem smallNegOneCertificate_valid : SmallNegOneCertificate :=
  smallNegOneCertificate_valid_list

namespace SmallN

/--
Input: `n < 105`.
Claim: the three Jacobi symbols at `3`, `5`, and `7` are all `1` exactly for
`1, 4, 16, 46, 64, 79`.
Content: this is the finite residue classification used when grouping the
small certificate cases.
Proof: reduce the `Fin 105` value to its 105 possible residues and normalize.
Role: a candidate common lemma for replacing repeated small Jacobi evaluations.
-/
lemma jacobi_three_five_seven_eq_one_iff (n : Fin 105) :
    (jacobiSym n.val 3 = 1 ∧ jacobiSym n.val 5 = 1 ∧ jacobiSym n.val 7 = 1) ↔
      n.val = 1 ∨ n.val = 4 ∨ n.val = 16 ∨ n.val = 46 ∨ n.val = 64 ∨ n.val = 79 := by
  have hnlt : n.val < 105 := n.isLt
  interval_cases n.val <;> norm_num only <;> simp only [false_and, true_and, false_or, true_or]

/-- The preceding classification is periodic modulo `105 = 3 * 5 * 7`. -/
lemma jacobi_three_five_seven_eq_one_iff_mod105 (n : Fin 750) :
    (jacobiSym n.val 3 = 1 ∧ jacobiSym n.val 5 = 1 ∧ jacobiSym n.val 7 = 1) ↔
      n.val % 105 = 1 ∨
        n.val % 105 = 4 ∨
        n.val % 105 = 16 ∨ n.val % 105 = 46 ∨ n.val % 105 = 64 ∨ n.val % 105 = 79 := by
  have h3 : n.val % 105 % 3 = n.val % 3 := Nat.mod_mod_of_dvd _ (by norm_num only)
  have h5 : n.val % 105 % 5 = n.val % 5 := Nat.mod_mod_of_dvd _ (by norm_num only)
  have h7 : n.val % 105 % 7 = n.val % 7 := Nat.mod_mod_of_dvd _ (by norm_num only)
  have hlt : n.val % 105 < 105 := Nat.mod_lt _ (by norm_num only)
  have hj3 : jacobiSym n.val 3 = jacobiSym (n.val % 105 : ℕ) 3 := by
    apply jacobiSym.mod_left'
    rw [← Int.natCast_mod, ← Int.natCast_mod, h3]
  have hj5 : jacobiSym n.val 5 = jacobiSym (n.val % 105 : ℕ) 5 := by
    apply jacobiSym.mod_left'
    rw [← Int.natCast_mod, ← Int.natCast_mod, h5]
  have hj7 : jacobiSym n.val 7 = jacobiSym (n.val % 105 : ℕ) 7 := by
    apply jacobiSym.mod_left'
    rw [← Int.natCast_mod, ← Int.natCast_mod, h7]
  rw [hj3, hj5, hj7]
  exact jacobi_three_five_seven_eq_one_iff ⟨n.val % 105, hlt⟩

end SmallN

/-- A square below `750` has a square root below `28`. -/
theorem square_root_lt_twenty_eight_of_lt_750 {n k : ℕ} (hn : n < 750) (hk : n = k ^ 2) :
    k < 28 := by
  by_contra h
  have hkge : 28 ≤ k := Nat.le_of_not_gt h
  have hsq := Nat.pow_le_pow_left hkge 2
  norm_num only at hsq
  omega

namespace SmallN

/-- A nonsquare natural number is different from every square indexed by `Fin 28`.

This common finite exclusion is used by both small-witness bounds below. -/
lemma fin28_ne_sq_of_not_isSquare {n : ℕ} (hns : ¬IsSquare n) : ∀ k : Fin 28, n ≠ k.val ^ 2 := by
  intro k hk
  exact hns ⟨k.val, by simpa only [pow_two] using hk⟩

end SmallN

/-- The finite certificate proves the exceptional small-witness statement used in formula (5.4). -/
theorem smallNegOneWitnessBound : SmallNegOneWitnessBound := by
  intro n hn hns hn750
  have hnosquare := SmallN.fin28_ne_sq_of_not_isSquare hns
  have hcertificate := smallNegOneCertificate_valid ⟨n, hn750⟩ (Nat.odd_iff.mp hn) hnosquare
  have hle (p : ℕ) (hp : p ∈ NumberTheory.PrimeNegOneWitnessSet n) (hp31 : p ≤ 31) :
    NumberTheory.primeNegOneWitness n
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns) ≤
      31 := by
    exact
      Nat.le_trans
        (NumberTheory.primeNegOneWitness_le n
          (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns) hp)
        hp31
  obtain hjacobi | hjacobi | hjacobi | hjacobi | hjacobi | hjacobi | hjacobi | hjacobi | hjacobi |
    hjacobi := hcertificate
  all_goals
    first
    | exact hle 3 ⟨by decide, by decide, hjacobi⟩ (by norm_num only)
    | exact hle 5 ⟨by decide, by decide, hjacobi⟩ (by norm_num only)
    | exact hle 7 ⟨by decide, by decide, hjacobi⟩ (by norm_num only)
    | exact hle 11 ⟨by decide, by decide, hjacobi⟩ (by norm_num only)
    | exact hle 13 ⟨by decide, by decide, hjacobi⟩ (by norm_num only)
    | exact hle 17 ⟨by decide, by decide, hjacobi⟩ (by norm_num only)
    | exact hle 19 ⟨by decide, by decide, hjacobi⟩ (by norm_num only)
    | exact hle 23 ⟨by decide, by decide, hjacobi⟩ (by norm_num only)
    | exact hle 29 ⟨by decide, by decide, hjacobi⟩ (by norm_num only)
    | exact hle 31 ⟨by decide, by decide, hjacobi⟩ (by norm_num only)

/-- The number `399` is not a square. -/
theorem not_isSquare_399 : ¬IsSquare 399 := by
  intro hsquare
  obtain ⟨k, hk⟩ := (isSquare_iff_exists_sq 399).mp hsquare
  have hk28 := square_root_lt_twenty_eight_of_lt_750 (n := 399) (by norm_num only) hk
  interval_cases k <;> norm_num only at hk

/-- The least odd-prime Jacobi `-1` witness for `399` is exactly `31`. -/
theorem primeNegOneWitness_399_eq_31
    (hw : (NumberTheory.PrimeNegOneWitnessSet 399).Nonempty) :
    NumberTheory.primeNegOneWitness 399 hw = 31 := by
  have hle : NumberTheory.primeNegOneWitness 399 hw ≤ 31 :=
    smallNegOneWitnessBound 399 (by decide) not_isSquare_399 (by norm_num only)
  have hmem := NumberTheory.primeNegOneWitness_mem 399 hw
  by_contra hne
  have hlt : NumberTheory.primeNegOneWitness 399 hw < 31 := by omega
  rcases hmem with ⟨_hprime, hodd, hjacobi⟩
  rcases hodd with ⟨k, hk⟩
  interval_cases NumberTheory.primeNegOneWitness 399 hw <;> try omega
  all_goals norm_num only at hjacobi

/-- Below `750`, the finite maximum of least Jacobi `-1` witnesses is at most `31`. -/
theorem QNegOne_le_thirty_one_of_lt_750 {B : ℕ} (hB : B < 750) : QNegOne B ≤ 31 := by
  have hreal : (QNegOne B : ℝ) ≤ 31 := by
    apply QNegOne_cast_le_of_forall (by norm_num only)
    intro n hn
    have hadm := NumberTheory.mem_admissibleFinset_iff.mp hn
    exact_mod_cast smallNegOneWitnessBound n hadm.odd hadm.not_isSquare (lt_of_le_of_lt hadm.le hB)
  exact_mod_cast hreal

/-- From `399` through `749`, the finite maximum is exactly the exceptional value `31`. -/
theorem QNegOne_eq_thirty_one_of_399_le_of_lt_750 {B : ℕ} (h399 : 399 ≤ B) (h750 : B < 750) :
    QNegOne B = 31 := by
  apply Nat.le_antisymm (QNegOne_le_thirty_one_of_lt_750 h750)
  have hadm : 399 ∈ NumberTheory.admissibleFinset B := by
    apply NumberTheory.mem_admissibleFinset_iff.mpr
    exact ⟨by norm_num only, h399, by decide, not_isSquare_399⟩
  have hw :=
    NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare (by decide)
      not_isSquare_399
  rw [← primeNegOneWitness_399_eq_31 hw]
  exact primeNegOneWitness_le_QNegOne hadm

/-- The finite maximum at `B = 399` already attains `31`. -/
theorem QNegOne_399_eq_31 : QNegOne 399 = 31 := by
  exact QNegOne_eq_thirty_one_of_399_le_of_lt_750 (by norm_num only) (by norm_num only)

end PseudoPrime.PseudoSquare
