/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import PseudoPrime.PseudoSquare.Bounds.WitnessMaximum

/-!
# Kernel-checked finite bound below `750`

This file certifies the exceptional finite range in formula (5.4). The search is restricted to
ten explicit odd primes at most `31`; `norm_num` produces proofs of the fixed Jacobi values.
-/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/--
The proposition that every odd nonsquare natural `n < 750` has least odd-prime Jacobi
`-1` witness at most `31`. Nonemptiness of the witness set is obtained from oddness and
nonsquareness. This is the exceptional finite-range input to the elementary GRH envelope.
-/
def SmallNegOneWitnessBound : Prop :=
  ∀ n : ℕ,
    (hn : Odd n) →
      (hns : ¬IsSquare n) →
      n < 750 →
        NumberTheory.primeNegOneWitness n
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns) ≤
          31

/--
For each odd `n : Fin 750` excluding all squares with roots in `Fin 28`, assert that
one of the ten odd primes `3, 5, 7, 11, 13, 17, 19, 23, 29, 31` has Jacobi value `-1`.
The root bound covers all squares below `750`. This finite proposition is checked in
blocks and then lifted to `SmallNegOneWitnessBound`.
-/
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

/--
The Boolean decision of the small `-1` certificate at `n : Fin 750`. It returns `true`
when oddness and all `Fin 28` square exclusions imply a Jacobi `-1` value at one of the
ten listed primes through `31`; even inputs and square inputs satisfy the implication
vacuously. The aggregate checker and block theorems use this executable predicate.
-/
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

/--
The Boolean conjunction of `smallNegOneCheck` over all `750` values of `Fin 750`,
implemented by `List.all` on `List.finRange 750`. A `true` result certifies every
individual implication and is converted to `SmallNegOneCertificate`.
-/
def smallNegOneCheckAll : Bool :=
  (List.finRange 750).all smallNegOneCheck

-- BEGIN GENERATED smallNegOneCheckAll_valid
/--
For `n : Fin 750` with `0 ≤ n.val < 16`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_0 :
    ∀ n : Fin 750, 0 ≤ n.val → n.val < 16 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `16 ≤ n.val < 32`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_16 :
    ∀ n : Fin 750, 16 ≤ n.val → n.val < 32 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `32 ≤ n.val < 48`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_32 :
    ∀ n : Fin 750, 32 ≤ n.val → n.val < 48 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `48 ≤ n.val < 64`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_48 :
    ∀ n : Fin 750, 48 ≤ n.val → n.val < 64 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `64 ≤ n.val < 80`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_64 :
    ∀ n : Fin 750, 64 ≤ n.val → n.val < 80 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `80 ≤ n.val < 96`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_80 :
    ∀ n : Fin 750, 80 ≤ n.val → n.val < 96 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `96 ≤ n.val < 112`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_96 :
    ∀ n : Fin 750, 96 ≤ n.val → n.val < 112 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `112 ≤ n.val < 128`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_112 :
    ∀ n : Fin 750, 112 ≤ n.val → n.val < 128 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `128 ≤ n.val < 144`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_128 :
    ∀ n : Fin 750, 128 ≤ n.val → n.val < 144 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `144 ≤ n.val < 160`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_144 :
    ∀ n : Fin 750, 144 ≤ n.val → n.val < 160 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `160 ≤ n.val < 176`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_160 :
    ∀ n : Fin 750, 160 ≤ n.val → n.val < 176 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `176 ≤ n.val < 192`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_176 :
    ∀ n : Fin 750, 176 ≤ n.val → n.val < 192 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `192 ≤ n.val < 208`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_192 :
    ∀ n : Fin 750, 192 ≤ n.val → n.val < 208 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `208 ≤ n.val < 224`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_208 :
    ∀ n : Fin 750, 208 ≤ n.val → n.val < 224 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `224 ≤ n.val < 240`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_224 :
    ∀ n : Fin 750, 224 ≤ n.val → n.val < 240 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `240 ≤ n.val < 256`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_240 :
    ∀ n : Fin 750, 240 ≤ n.val → n.val < 256 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `256 ≤ n.val < 272`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_256 :
    ∀ n : Fin 750, 256 ≤ n.val → n.val < 272 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `272 ≤ n.val < 288`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_272 :
    ∀ n : Fin 750, 272 ≤ n.val → n.val < 288 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `288 ≤ n.val < 304`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_288 :
    ∀ n : Fin 750, 288 ≤ n.val → n.val < 304 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `304 ≤ n.val < 320`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_304 :
    ∀ n : Fin 750, 304 ≤ n.val → n.val < 320 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `320 ≤ n.val < 336`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_320 :
    ∀ n : Fin 750, 320 ≤ n.val → n.val < 336 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `336 ≤ n.val < 352`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_336 :
    ∀ n : Fin 750, 336 ≤ n.val → n.val < 352 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `352 ≤ n.val < 368`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_352 :
    ∀ n : Fin 750, 352 ≤ n.val → n.val < 368 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `368 ≤ n.val < 384`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_368 :
    ∀ n : Fin 750, 368 ≤ n.val → n.val < 384 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `384 ≤ n.val < 400`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_384 :
    ∀ n : Fin 750, 384 ≤ n.val → n.val < 400 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `400 ≤ n.val < 416`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_400 :
    ∀ n : Fin 750, 400 ≤ n.val → n.val < 416 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `416 ≤ n.val < 432`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_416 :
    ∀ n : Fin 750, 416 ≤ n.val → n.val < 432 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `432 ≤ n.val < 448`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_432 :
    ∀ n : Fin 750, 432 ≤ n.val → n.val < 448 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `448 ≤ n.val < 464`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_448 :
    ∀ n : Fin 750, 448 ≤ n.val → n.val < 464 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `464 ≤ n.val < 480`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_464 :
    ∀ n : Fin 750, 464 ≤ n.val → n.val < 480 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `480 ≤ n.val < 496`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_480 :
    ∀ n : Fin 750, 480 ≤ n.val → n.val < 496 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `496 ≤ n.val < 512`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_496 :
    ∀ n : Fin 750, 496 ≤ n.val → n.val < 512 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `512 ≤ n.val < 528`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_512 :
    ∀ n : Fin 750, 512 ≤ n.val → n.val < 528 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `528 ≤ n.val < 544`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_528 :
    ∀ n : Fin 750, 528 ≤ n.val → n.val < 544 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `544 ≤ n.val < 560`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_544 :
    ∀ n : Fin 750, 544 ≤ n.val → n.val < 560 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `560 ≤ n.val < 576`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_560 :
    ∀ n : Fin 750, 560 ≤ n.val → n.val < 576 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `576 ≤ n.val < 592`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_576 :
    ∀ n : Fin 750, 576 ≤ n.val → n.val < 592 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `592 ≤ n.val < 608`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_592 :
    ∀ n : Fin 750, 592 ≤ n.val → n.val < 608 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `608 ≤ n.val < 624`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_608 :
    ∀ n : Fin 750, 608 ≤ n.val → n.val < 624 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `624 ≤ n.val < 640`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_624 :
    ∀ n : Fin 750, 624 ≤ n.val → n.val < 640 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `640 ≤ n.val < 656`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_640 :
    ∀ n : Fin 750, 640 ≤ n.val → n.val < 656 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `656 ≤ n.val < 672`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_656 :
    ∀ n : Fin 750, 656 ≤ n.val → n.val < 672 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `672 ≤ n.val < 688`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_672 :
    ∀ n : Fin 750, 672 ≤ n.val → n.val < 688 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `688 ≤ n.val < 704`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_688 :
    ∀ n : Fin 750, 688 ≤ n.val → n.val < 704 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `704 ≤ n.val < 720`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_704 :
    ∀ n : Fin 750, 704 ≤ n.val → n.val < 720 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `720 ≤ n.val < 736`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_720 :
    ∀ n : Fin 750, 720 ≤ n.val → n.val < 736 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
For `n : Fin 750` with `736 ≤ n.val < 750`, `smallNegOneCheck n = true`.
Unfolding the Boolean decision reduces the claim to the finite certificate implication;
case enumeration, Jacobi normalization, and decision verify every input in this block.
The aggregate list-checker theorem uses this local interval result.
-/
private theorem smallNegOneCheckAll_valid_block_736 :
    ∀ n : Fin 750, 736 ≤ n.val → n.val < 750 → smallNegOneCheck n = true := by
  intro n hlo hhi
  simp only [smallNegOneCheck, decide_eq_true_eq]
  interval_cases n.val <;> norm_num only <;> decide

/--
Every value in `List.finRange 750` passes `smallNegOneCheck`, so the aggregate list
check is `true`. The proof splits the input by a balanced tree of interval cutoffs and
applies the corresponding checked block. This assembles the local reductions into the
Boolean evidence consumed by `smallNegOneCertificate_valid_list`.
-/
theorem smallNegOneCheckAll_valid : (List.finRange 750).all smallNegOneCheck = true := by
  apply List.all_eq_true.mpr
  intro n hn
  by_cases h368 : n.val < 368
  · by_cases h176 : n.val < 176
    · by_cases h80 : n.val < 80
      · by_cases h32 : n.val < 32
        · by_cases h16 : n.val < 16
          · exact smallNegOneCheckAll_valid_block_0 n (Nat.zero_le _) h16
          · exact smallNegOneCheckAll_valid_block_16 n (Nat.le_of_not_lt h16) h32
        · by_cases h48 : n.val < 48
          · exact smallNegOneCheckAll_valid_block_32 n (Nat.le_of_not_lt h32) h48
          · by_cases h64 : n.val < 64
            · exact smallNegOneCheckAll_valid_block_48 n (Nat.le_of_not_lt h48) h64
            · exact smallNegOneCheckAll_valid_block_64 n (Nat.le_of_not_lt h64) h80
      · by_cases h128 : n.val < 128
        · by_cases h96 : n.val < 96
          · exact smallNegOneCheckAll_valid_block_80 n (Nat.le_of_not_lt h80) h96
          · by_cases h112 : n.val < 112
            · exact smallNegOneCheckAll_valid_block_96 n (Nat.le_of_not_lt h96) h112
            · exact smallNegOneCheckAll_valid_block_112 n (Nat.le_of_not_lt h112) h128
        · by_cases h144 : n.val < 144
          · exact smallNegOneCheckAll_valid_block_128 n (Nat.le_of_not_lt h128) h144
          · by_cases h160 : n.val < 160
            · exact smallNegOneCheckAll_valid_block_144 n (Nat.le_of_not_lt h144) h160
            · exact smallNegOneCheckAll_valid_block_160 n (Nat.le_of_not_lt h160) h176
    · by_cases h272 : n.val < 272
      · by_cases h224 : n.val < 224
        · by_cases h192 : n.val < 192
          · exact smallNegOneCheckAll_valid_block_176 n (Nat.le_of_not_lt h176) h192
          · by_cases h208 : n.val < 208
            · exact smallNegOneCheckAll_valid_block_192 n (Nat.le_of_not_lt h192) h208
            · exact smallNegOneCheckAll_valid_block_208 n (Nat.le_of_not_lt h208) h224
        · by_cases h240 : n.val < 240
          · exact smallNegOneCheckAll_valid_block_224 n (Nat.le_of_not_lt h224) h240
          · by_cases h256 : n.val < 256
            · exact smallNegOneCheckAll_valid_block_240 n (Nat.le_of_not_lt h240) h256
            · exact smallNegOneCheckAll_valid_block_256 n (Nat.le_of_not_lt h256) h272
      · by_cases h320 : n.val < 320
        · by_cases h288 : n.val < 288
          · exact smallNegOneCheckAll_valid_block_272 n (Nat.le_of_not_lt h272) h288
          · by_cases h304 : n.val < 304
            · exact smallNegOneCheckAll_valid_block_288 n (Nat.le_of_not_lt h288) h304
            · exact smallNegOneCheckAll_valid_block_304 n (Nat.le_of_not_lt h304) h320
        · by_cases h336 : n.val < 336
          · exact smallNegOneCheckAll_valid_block_320 n (Nat.le_of_not_lt h320) h336
          · by_cases h352 : n.val < 352
            · exact smallNegOneCheckAll_valid_block_336 n (Nat.le_of_not_lt h336) h352
            · exact smallNegOneCheckAll_valid_block_352 n (Nat.le_of_not_lt h352) h368
  · by_cases h560 : n.val < 560
    · by_cases h464 : n.val < 464
      · by_cases h416 : n.val < 416
        · by_cases h384 : n.val < 384
          · exact smallNegOneCheckAll_valid_block_368 n (Nat.le_of_not_lt h368) h384
          · by_cases h400 : n.val < 400
            · exact smallNegOneCheckAll_valid_block_384 n (Nat.le_of_not_lt h384) h400
            · exact smallNegOneCheckAll_valid_block_400 n (Nat.le_of_not_lt h400) h416
        · by_cases h432 : n.val < 432
          · exact smallNegOneCheckAll_valid_block_416 n (Nat.le_of_not_lt h416) h432
          · by_cases h448 : n.val < 448
            · exact smallNegOneCheckAll_valid_block_432 n (Nat.le_of_not_lt h432) h448
            · exact smallNegOneCheckAll_valid_block_448 n (Nat.le_of_not_lt h448) h464
      · by_cases h512 : n.val < 512
        · by_cases h480 : n.val < 480
          · exact smallNegOneCheckAll_valid_block_464 n (Nat.le_of_not_lt h464) h480
          · by_cases h496 : n.val < 496
            · exact smallNegOneCheckAll_valid_block_480 n (Nat.le_of_not_lt h480) h496
            · exact smallNegOneCheckAll_valid_block_496 n (Nat.le_of_not_lt h496) h512
        · by_cases h528 : n.val < 528
          · exact smallNegOneCheckAll_valid_block_512 n (Nat.le_of_not_lt h512) h528
          · by_cases h544 : n.val < 544
            · exact smallNegOneCheckAll_valid_block_528 n (Nat.le_of_not_lt h528) h544
            · exact smallNegOneCheckAll_valid_block_544 n (Nat.le_of_not_lt h544) h560
    · by_cases h656 : n.val < 656
      · by_cases h608 : n.val < 608
        · by_cases h576 : n.val < 576
          · exact smallNegOneCheckAll_valid_block_560 n (Nat.le_of_not_lt h560) h576
          · by_cases h592 : n.val < 592
            · exact smallNegOneCheckAll_valid_block_576 n (Nat.le_of_not_lt h576) h592
            · exact smallNegOneCheckAll_valid_block_592 n (Nat.le_of_not_lt h592) h608
        · by_cases h624 : n.val < 624
          · exact smallNegOneCheckAll_valid_block_608 n (Nat.le_of_not_lt h608) h624
          · by_cases h640 : n.val < 640
            · exact smallNegOneCheckAll_valid_block_624 n (Nat.le_of_not_lt h624) h640
            · exact smallNegOneCheckAll_valid_block_640 n (Nat.le_of_not_lt h640) h656
      · by_cases h704 : n.val < 704
        · by_cases h672 : n.val < 672
          · exact smallNegOneCheckAll_valid_block_656 n (Nat.le_of_not_lt h656) h672
          · by_cases h688 : n.val < 688
            · exact smallNegOneCheckAll_valid_block_672 n (Nat.le_of_not_lt h672) h688
            · exact smallNegOneCheckAll_valid_block_688 n (Nat.le_of_not_lt h688) h704
        · by_cases h720 : n.val < 720
          · exact smallNegOneCheckAll_valid_block_704 n (Nat.le_of_not_lt h704) h720
          · by_cases h736 : n.val < 736
            · exact smallNegOneCheckAll_valid_block_720 n (Nat.le_of_not_lt h720) h736
            · exact smallNegOneCheckAll_valid_block_736 n (Nat.le_of_not_lt h736) n.isLt

-- END GENERATED smallNegOneCheckAll_valid

/--
The verified list checker implies `SmallNegOneCertificate`. For each `n : Fin 750`,
extract its successful Boolean check, unfold the decision predicate, and apply the
resulting implication to oddness and finite square exclusions. This connects the
block verification to the proposition used by mathematical witness bounds.
-/
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

/--
The public proof of `SmallNegOneCertificate`, obtained directly from the verified
list-checker adapter. It supplies finite Jacobi `-1` alternatives to the exceptional
small-witness bound without an analytic assumption.
-/
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
  exact Nat.not_lt_of_ge (hk ▸ Nat.le_trans (by decide) hsq) hn

namespace SmallN

/-- A nonsquare natural number is different from every square indexed by `Fin 28`.

This common finite exclusion is used by both small-witness bounds below. -/
lemma fin28_ne_sq_of_not_isSquare {n : ℕ} (hns : ¬IsSquare n) : ∀ k : Fin 28, n ≠ k.val ^ 2 := by
  intro k hk
  exact hns ⟨k.val, by simpa only [pow_two] using hk⟩

end SmallN

/--
Every odd nonsquare `n < 750` has least odd-prime Jacobi `-1` witness at most `31`.
The proof converts nonsquareness to the `Fin 28` exclusions, uses the finite certificate,
and applies least-witness minimality to its concrete odd-prime alternatives.
This discharges the exceptional range in the elementary maximum bound.
-/
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

/--
The natural number `399` is not a square. A hypothetical root is below `28` because
`399 < 750`; enumerating these roots and evaluating their squares excludes the equality.
This supplies admissibility of the input attaining least negative-one witness `31`.
-/
theorem not_isSquare_399 : ¬IsSquare 399 := by
  intro hsquare
  obtain ⟨k, hk⟩ := (isSquare_iff_exists_sq 399).mp hsquare
  have hk28 := square_root_lt_twenty_eight_of_lt_750 (n := 399) (by norm_num only) hk
  interval_cases k <;> norm_num only at hk

/--
For any nonemptiness proof `hw`, the least odd-prime Jacobi `-1` witness of `399` is `31`.
The small-range theorem gives the upper bound, while enumerating all smaller odd
candidates excludes Jacobi value `-1`. This provides the attaining input for `QNegOne`
and the threshold lower bound beyond `399`.
-/
theorem primeNegOneWitness_399_eq_31 (hw : (NumberTheory.PrimeNegOneWitnessSet 399).Nonempty) :
    NumberTheory.primeNegOneWitness 399 hw = 31 := by
  have hle : NumberTheory.primeNegOneWitness 399 hw ≤ 31 :=
    smallNegOneWitnessBound 399 (by decide) not_isSquare_399 (by norm_num only)
  have hmem := NumberTheory.primeNegOneWitness_mem 399 hw
  by_contra hne
  have hlt : NumberTheory.primeNegOneWitness 399 hw < 31 := Nat.lt_of_le_of_ne hle hne
  rcases hmem with ⟨_hprime, hodd, hjacobi⟩
  have hpmod : NumberTheory.primeNegOneWitness 399 hw % 2 = 1 := Nat.odd_iff.mp hodd
  interval_cases NumberTheory.primeNegOneWitness 399 hw <;> norm_num only at hpmod
  all_goals norm_num only at hjacobi

/--
For `B < 750`, the finite maximum `QNegOne B` is at most `31`. Every admissible member
lies below `750`, so the small-witness theorem bounds it. The proof lifts these pointwise
bounds through the real-valued finite-maximum interface and casts back to naturals.
This is the upper half of the exact maximum on `399 ≤ B < 750`.
-/
theorem QNegOne_le_thirty_one_of_lt_750 {B : ℕ} (hB : B < 750) : QNegOne B ≤ 31 := by
  have hreal : (QNegOne B : ℝ) ≤ 31 := by
    apply QNegOne_cast_le_of_forall (by norm_num only)
    intro n hn
    have hadm := NumberTheory.mem_admissibleFinset_iff.mp hn
    exact_mod_cast smallNegOneWitnessBound n hadm.odd hadm.not_isSquare (lt_of_le_of_lt hadm.le hB)
  exact_mod_cast hreal

/--
For `399 ≤ B < 750`, the finite maximum `QNegOne B` is exactly `31`.
The small-range upper bound gives one inequality, and the admissible input `399` with
least Jacobi `-1` witness `31` gives the other. This identifies the exceptional plateau.
-/
theorem QNegOne_eq_thirty_one_of_399_le_of_lt_750 {B : ℕ} (h399 : 399 ≤ B) (h750 : B < 750) :
    QNegOne B = 31 := by
  apply Nat.le_antisymm (QNegOne_le_thirty_one_of_lt_750 h750)
  have hadm : 399 ∈ NumberTheory.admissibleFinset B := by
    apply NumberTheory.mem_admissibleFinset_iff.mpr
    exact ⟨by norm_num only, h399, by decide, not_isSquare_399⟩
  have hw :=
    NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare (by decide) not_isSquare_399
  rw [← primeNegOneWitness_399_eq_31 hw]
  exact primeNegOneWitness_le_QNegOne hadm

/--
The finite maximum `QNegOne 399` equals `31`, by specializing the exact plateau theorem
to its first endpoint. This records the threshold value attained by input `399`.
-/
theorem QNegOne_399_eq_31 : QNegOne 399 = 31 := by
  exact QNegOne_eq_thirty_one_of_399_le_of_lt_750 (by norm_num only) (by norm_num only)

end PseudoPrime.PseudoSquare
