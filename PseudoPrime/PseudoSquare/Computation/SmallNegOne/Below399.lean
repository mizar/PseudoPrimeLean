/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PseudoSquare.Computation.QThresholds

/-!
# Kernel-checked `-1` certificate below `399`

The generated blocks in this file certify the finite small-negative-one boundary.
-/

namespace PseudoPrime.PseudoSquare

/-- The finite certificate asserting a Jacobi `-1` witness at most `17` below `399`. -/
def Below399NegOneCertificate : Prop :=
  ∀ n : Fin 399,
    n.val % 2 = 1 →
      (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 = -1 ∨
        jacobiSym n.val 5 = -1 ∨
        jacobiSym n.val 7 = -1 ∨
        jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1

-- BEGIN GENERATED below399NegOneCertificate_valid
/-- Kernel-checked certificate restricted to [0, 16). -/
private theorem below399NegOneCertificate_valid_block_0 :
    ∀ n : Fin 399,
      0 ≤ n.val →
        n.val < 16 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [16, 32). -/
private theorem below399NegOneCertificate_valid_block_16 :
    ∀ n : Fin 399,
      16 ≤ n.val →
        n.val < 32 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [32, 48). -/
private theorem below399NegOneCertificate_valid_block_32 :
    ∀ n : Fin 399,
      32 ≤ n.val →
        n.val < 48 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [48, 64). -/
private theorem below399NegOneCertificate_valid_block_48 :
    ∀ n : Fin 399,
      48 ≤ n.val →
        n.val < 64 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [64, 80). -/
private theorem below399NegOneCertificate_valid_block_64 :
    ∀ n : Fin 399,
      64 ≤ n.val →
        n.val < 80 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [80, 96). -/
private theorem below399NegOneCertificate_valid_block_80 :
    ∀ n : Fin 399,
      80 ≤ n.val →
        n.val < 96 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [96, 112). -/
private theorem below399NegOneCertificate_valid_block_96 :
    ∀ n : Fin 399,
      96 ≤ n.val →
        n.val < 112 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [112, 128). -/
private theorem below399NegOneCertificate_valid_block_112 :
    ∀ n : Fin 399,
      112 ≤ n.val →
        n.val < 128 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [128, 144). -/
private theorem below399NegOneCertificate_valid_block_128 :
    ∀ n : Fin 399,
      128 ≤ n.val →
        n.val < 144 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [144, 160). -/
private theorem below399NegOneCertificate_valid_block_144 :
    ∀ n : Fin 399,
      144 ≤ n.val →
        n.val < 160 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [160, 176). -/
private theorem below399NegOneCertificate_valid_block_160 :
    ∀ n : Fin 399,
      160 ≤ n.val →
        n.val < 176 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [176, 192). -/
private theorem below399NegOneCertificate_valid_block_176 :
    ∀ n : Fin 399,
      176 ≤ n.val →
        n.val < 192 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [192, 208). -/
private theorem below399NegOneCertificate_valid_block_192 :
    ∀ n : Fin 399,
      192 ≤ n.val →
        n.val < 208 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [208, 224). -/
private theorem below399NegOneCertificate_valid_block_208 :
    ∀ n : Fin 399,
      208 ≤ n.val →
        n.val < 224 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [224, 240). -/
private theorem below399NegOneCertificate_valid_block_224 :
    ∀ n : Fin 399,
      224 ≤ n.val →
        n.val < 240 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [240, 256). -/
private theorem below399NegOneCertificate_valid_block_240 :
    ∀ n : Fin 399,
      240 ≤ n.val →
        n.val < 256 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [256, 272). -/
private theorem below399NegOneCertificate_valid_block_256 :
    ∀ n : Fin 399,
      256 ≤ n.val →
        n.val < 272 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [272, 288). -/
private theorem below399NegOneCertificate_valid_block_272 :
    ∀ n : Fin 399,
      272 ≤ n.val →
        n.val < 288 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [288, 304). -/
private theorem below399NegOneCertificate_valid_block_288 :
    ∀ n : Fin 399,
      288 ≤ n.val →
        n.val < 304 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [304, 320). -/
private theorem below399NegOneCertificate_valid_block_304 :
    ∀ n : Fin 399,
      304 ≤ n.val →
        n.val < 320 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [320, 336). -/
private theorem below399NegOneCertificate_valid_block_320 :
    ∀ n : Fin 399,
      320 ≤ n.val →
        n.val < 336 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [336, 352). -/
private theorem below399NegOneCertificate_valid_block_336 :
    ∀ n : Fin 399,
      336 ≤ n.val →
        n.val < 352 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [352, 368). -/
private theorem below399NegOneCertificate_valid_block_352 :
    ∀ n : Fin 399,
      352 ≤ n.val →
        n.val < 368 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [368, 384). -/
private theorem below399NegOneCertificate_valid_block_368 :
    ∀ n : Fin 399,
      368 ≤ n.val →
        n.val < 384 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked certificate restricted to [384, 399). -/
private theorem below399NegOneCertificate_valid_block_384 :
    ∀ n : Fin 399,
      384 ≤ n.val →
        n.val < 399 →
        n.val % 2 = 1 →
        (∀ k : Fin 20, n.val ≠ k.val ^ 2) →
        jacobiSym n.val 3 = -1 ∨
          jacobiSym n.val 5 = -1 ∨
          jacobiSym n.val 7 = -1 ∨
          jacobiSym n.val 11 = -1 ∨ jacobiSym n.val 13 = -1 ∨ jacobiSym n.val 17 = -1 := by
  intro n hlo hhi
  interval_cases n.val <;> norm_num only <;> decide

/-- Kernel-checked verification of the witness bound `17` below `399`. -/
theorem below399NegOneCertificate_valid : Below399NegOneCertificate := by
  intro n
  by_cases h192 : n.val < 192
  · by_cases h96 : n.val < 96
    · by_cases h48 : n.val < 48
      · by_cases h16 : n.val < 16
        · exact below399NegOneCertificate_valid_block_0 n (by omega) (by omega)
        · by_cases h32 : n.val < 32
          · exact below399NegOneCertificate_valid_block_16 n (by omega) (by omega)
          · exact below399NegOneCertificate_valid_block_32 n (by omega) (by omega)
      · by_cases h64 : n.val < 64
        · exact below399NegOneCertificate_valid_block_48 n (by omega) (by omega)
        · by_cases h80 : n.val < 80
          · exact below399NegOneCertificate_valid_block_64 n (by omega) (by omega)
          · exact below399NegOneCertificate_valid_block_80 n (by omega) (by omega)
    · by_cases h144 : n.val < 144
      · by_cases h112 : n.val < 112
        · exact below399NegOneCertificate_valid_block_96 n (by omega) (by omega)
        · by_cases h128 : n.val < 128
          · exact below399NegOneCertificate_valid_block_112 n (by omega) (by omega)
          · exact below399NegOneCertificate_valid_block_128 n (by omega) (by omega)
      · by_cases h160 : n.val < 160
        · exact below399NegOneCertificate_valid_block_144 n (by omega) (by omega)
        · by_cases h176 : n.val < 176
          · exact below399NegOneCertificate_valid_block_160 n (by omega) (by omega)
          · exact below399NegOneCertificate_valid_block_176 n (by omega) (by omega)
  · by_cases h288 : n.val < 288
    · by_cases h240 : n.val < 240
      · by_cases h208 : n.val < 208
        · exact below399NegOneCertificate_valid_block_192 n (by omega) (by omega)
        · by_cases h224 : n.val < 224
          · exact below399NegOneCertificate_valid_block_208 n (by omega) (by omega)
          · exact below399NegOneCertificate_valid_block_224 n (by omega) (by omega)
      · by_cases h256 : n.val < 256
        · exact below399NegOneCertificate_valid_block_240 n (by omega) (by omega)
        · by_cases h272 : n.val < 272
          · exact below399NegOneCertificate_valid_block_256 n (by omega) (by omega)
          · exact below399NegOneCertificate_valid_block_272 n (by omega) (by omega)
    · by_cases h336 : n.val < 336
      · by_cases h304 : n.val < 304
        · exact below399NegOneCertificate_valid_block_288 n (by omega) (by omega)
        · by_cases h320 : n.val < 320
          · exact below399NegOneCertificate_valid_block_304 n (by omega) (by omega)
          · exact below399NegOneCertificate_valid_block_320 n (by omega) (by omega)
      · by_cases h368 : n.val < 368
        · by_cases h352 : n.val < 352
          · exact below399NegOneCertificate_valid_block_336 n (by omega) (by omega)
          · exact below399NegOneCertificate_valid_block_352 n (by omega) (by omega)
        · by_cases h384 : n.val < 384
          · exact below399NegOneCertificate_valid_block_368 n (by omega) (by omega)
          · exact below399NegOneCertificate_valid_block_384 n (by omega) (by omega)

-- END GENERATED below399NegOneCertificate_valid

/-- A square below `399` has a square root below `20`. -/
theorem square_root_lt_twenty_of_lt_399 {n k : ℕ} (hn : n < 399) (hk : n = k ^ 2) : k < 20 := by
  by_contra hnot
  have hk20 : 20 ≤ k := by omega
  have h400 : 400 ≤ k ^ 2 := by simpa only [pow_two] using Nat.mul_self_le_mul_self hk20
  omega

/-- Every odd nonsquare below `399` has least odd-prime Jacobi `-1` witness at most `17`. -/
theorem primeNegOneWitness_le_seventeen_of_lt_399 {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hn399 : n < 399) :
    NumberTheory.primeNegOneWitness n
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns) ≤
      17 := by
  have hnosquare : ∀ k : Fin 20, n ≠ k.val ^ 2 := by
    intro k hk
    exact hns ⟨k.val, by simpa only [pow_two] using hk⟩
  have hcertificate := below399NegOneCertificate_valid ⟨n, hn399⟩ (Nat.odd_iff.mp hn) hnosquare
  obtain hjacobi | hjacobi | hjacobi | hjacobi | hjacobi | hjacobi := hcertificate
  all_goals
    exact
      (NumberTheory.primeNegOneWitness_le n _ ⟨by decide, by decide, hjacobi⟩).trans
        (by norm_num only)

/-- The number `91` is an admissible nonsquare attaining witness `17`. -/
theorem not_isSquare_91 : ¬IsSquare 91 := by
  intro hsquare
  obtain ⟨k, hk⟩ := (isSquare_iff_exists_sq 91).mp hsquare
  have hk20 := square_root_lt_twenty_of_lt_399 (n := 91) (by norm_num only) hk
  interval_cases k <;> norm_num only at hk

/-- The least odd-prime Jacobi `-1` witness for `91` is exactly `17`. -/
theorem primeNegOneWitness_91_eq_17 (hw : (NumberTheory.PrimeNegOneWitnessSet 91).Nonempty) :
    NumberTheory.primeNegOneWitness 91 hw = 17 := by
  have hle : NumberTheory.primeNegOneWitness 91 hw ≤ 17 :=
    primeNegOneWitness_le_seventeen_of_lt_399 (by decide) not_isSquare_91 (by norm_num only)
  have hmem := NumberTheory.primeNegOneWitness_mem 91 hw
  by_contra hne
  have hlt : NumberTheory.primeNegOneWitness 91 hw < 17 := by omega
  rcases hmem with ⟨_hprime, hodd, hjacobi⟩
  rcases hodd with ⟨k, hk⟩
  interval_cases NumberTheory.primeNegOneWitness 91 hw <;> try omega
  all_goals norm_num only at hjacobi

/-- Immediately before `399`, the finite maximum is `17`. -/
theorem QNegOne_398_eq_17 : QNegOne 398 = 17 := by
  apply Nat.le_antisymm
  · have hreal : (QNegOne 398 : ℝ) ≤ 17 := by
      apply QNegOne_cast_le_of_forall (by norm_num only)
      intro n hn
      have hadm : NumberTheory.Admissible 398 n := NumberTheory.mem_admissibleFinset_iff.mp hn
      exact_mod_cast
        primeNegOneWitness_le_seventeen_of_lt_399 hadm.odd hadm.not_isSquare
          (hadm.le.trans_lt (by norm_num only))
    exact_mod_cast hreal
  · have hadm : 91 ∈ NumberTheory.admissibleFinset 398 := by
      apply NumberTheory.mem_admissibleFinset_iff.mpr
      exact ⟨by norm_num only, by norm_num only, by decide, not_isSquare_91⟩
    have hw :=
      NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare (by decide) not_isSquare_91
    rw [← primeNegOneWitness_91_eq_17 hw]
    exact primeNegOneWitness_le_QNegOne hadm

end PseudoPrime.PseudoSquare
