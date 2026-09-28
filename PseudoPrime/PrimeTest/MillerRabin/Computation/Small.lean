/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTest.MillerRabin.Decomposition
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-!
# Finite Strong Miller–Rabin classification below `3000`

The certificate checks explicit decompositions and binary modular powers. Its blocks classify every
odd input below `3000` as rejected by base `2`, prime, or the exceptional value `2047`.
-/

namespace PseudoPrime.PrimeTest

/-- Split off at most `fuel` factors of two, returning their count and the remaining factor. -/
private def splitTwo (fuel m : ℕ) : ℕ × ℕ :=
  match fuel with
  | 0 => (0, m)
  | fuel + 1 =>
      if m % 2 = 0 then
        let (s, d) := splitTwo fuel (m / 2)
        (s + 1, d)
      else (0, m)

/--
Check a proposed decomposition and the binary modular-power inequalities that reject base `2`.
The list contains precisely the exponents below the supplied two-adic exponent.
-/
private def baseTwoRejectCheckData (n s d : ℕ) : Bool :=
  decide (n - 1 = 2 ^ s * d ∧ Odd d ∧ zmodPow n 2 d ≠ 1) &&
    (List.range s).all (fun j => decide (zmodPow n 2 (2 ^ j * d) ≠ -1))

/-- Run the finite certificate checker using a bounded, executable split of `n - 1`. -/
private def baseTwoRejectCheck (n : ℕ) : Bool :=
  let (s, d) := splitTwo 12 (n - 1)
  baseTwoRejectCheckData n s d

/-- A successful certificate is a proof that the existing base-`2` test rejects `n`. -/
private theorem baseTwoRejectCheckData_sound {n s d : ℕ} (hn : 1 < n)
    (hcheck : baseTwoRejectCheckData n s d = true) :
    strongMillerRabinWithBase n 2 = false := by
  rw [baseTwoRejectCheckData, Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨hbase, hsteps⟩
  have hbase := of_decide_eq_true hbase
  have hsteps := List.all_eq_true.mp hsteps
  obtain ⟨hdecomp, hdOdd, hodd⟩ := hbase
  have hdvd : ¬ 2 ∣ d := by
    intro hdiv
    exact (Nat.not_even_iff_odd.mpr hdOdd) (even_iff_two_dvd.mpr hdiv)
  have hmax := Nat.maxPowDvdDiv_of_pow_mul_eq
    (Nat.sub_ne_zero_of_lt hn) hdecomp.symm hdvd
  have hs : padicValNat 2 (n - 1) = s := by
    calc
      padicValNat 2 (n - 1) = (Nat.maxPowDvdDiv 2 (n - 1)).1 :=
        (Nat.fst_maxPowDvdDiv 2 (n - 1)).symm
      _ = s := congrArg Prod.fst hmax
  have hd : Nat.divMaxPow (n - 1) 2 = d := by
    calc
      Nat.divMaxPow (n - 1) 2 = (Nat.maxPowDvdDiv 2 (n - 1)).2 :=
        (Nat.snd_maxPowDvdDiv 2 (n - 1)).symm
      _ = d := congrArg Prod.snd hmax
  apply (strongMillerRabinWithBase_eq_false_iff_not_pass).2
  intro hpass
  have hpass' : (2 : ZMod n) ^ d = 1 ∨
      ∃ j : ℕ, j < s ∧ (2 : ZMod n) ^ (2 ^ j * d) = -1 := by
    simpa only [StrongMillerRabinPass, hs, hd, Nat.cast_ofNat] using hpass
  have hnot : ¬ ((2 : ZMod n) ^ d = 1 ∨
      ∃ j : ℕ, j < s ∧ (2 : ZMod n) ^ (2 ^ j * d) = -1) := by
    intro h
    rcases h with hone | ⟨j, hj, hminus⟩
    · have hodd' : (2 : ZMod n) ^ d ≠ 1 := by
        simpa only [zmodPow_eq_pow, Nat.cast_ofNat] using hodd
      exact hodd' hone
    · have hjmem : j ∈ List.range s := List.mem_range.mpr hj
      have hstep := of_decide_eq_true (hsteps j hjmem)
      have hstep' : (2 : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
        simpa only [zmodPow_eq_pow, Nat.cast_ofNat] using hstep
      exact hstep' hminus
  exact hnot hpass'

/-- The bounded checker inherits soundness from its verified decomposition and power checks. -/
private theorem baseTwoRejectCheck_sound {n : ℕ} (hn : 1 < n)
    (hcheck : baseTwoRejectCheck n = true) :
    strongMillerRabinWithBase n 2 = false := by
  simp only [baseTwoRejectCheck] at hcheck
  exact baseTwoRejectCheckData_sound hn hcheck

/-- The sole base-`2` composite exception below `3000` fails the base-`3` test. -/
private theorem baseThreeRejects_2047 : strongMillerRabinWithBase 2047 3 = false := by
  apply (strongMillerRabinWithBase_eq_false_iff_not_pass).2
  have hoddPart : padicValNat 2 1023 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by norm_num)
  have hs : padicValNat 2 (2047 - 1) = 1 := by
    calc
      padicValNat 2 (2047 - 1) = padicValNat 2 (2 * 1023) := by norm_num
      _ = padicValNat 2 1023 + 1 := padicValNat_base_mul (by norm_num) (by norm_num)
      _ = 1 := by rw [hoddPart]
  have hd : Nat.divMaxPow (2047 - 1) 2 = 1023 := by
    have hmul := Nat.pow_padicValNat_mul_divMaxPow 2 (2047 - 1)
    rw [hs] at hmul
    norm_num at hmul ⊢
    omega
  rw [not_strongMillerRabinPass_iff, hs, hd]
  have hpow : ((3 : ℕ) : ZMod 2047) ^ 1023 ≠ 1 ∧
      ((3 : ℕ) : ZMod 2047) ^ 1023 ≠ -1 := by
    rw [← zmodPow_eq_pow 2047 3 1023]
    decide
  constructor
  · exact hpow.1
  · intro j hj
    have hj0 : j = 0 := Nat.lt_one_iff.mp hj
    subst j
    exact hpow.2

-- BEGIN GENERATED baseTwoClassifyBelow3000
/-- Generated kernel-checked classification block for odd inputs. -/
private theorem baseTwoClassifyBelow3000_block_0 :
    ∀ i : Fin 128,
      let n := 2 * (128 * 0 + i.val) + 1
      n = 1 ∨ baseTwoRejectCheck n = true ∨ Nat.Prime n ∨ n = 2047 := by
  intro i
  fin_cases i <;> first | (norm_num; done) |
    (unfold baseTwoRejectCheck baseTwoRejectCheckData splitTwo; decide)

/-- Generated kernel-checked classification block for odd inputs. -/
private theorem baseTwoClassifyBelow3000_block_1 :
    ∀ i : Fin 128,
      let n := 2 * (128 * 1 + i.val) + 1
      n = 1 ∨ baseTwoRejectCheck n = true ∨ Nat.Prime n ∨ n = 2047 := by
  intro i
  fin_cases i <;> first | (norm_num; done) |
    (unfold baseTwoRejectCheck baseTwoRejectCheckData splitTwo; decide)

/-- Generated kernel-checked classification block for odd inputs. -/
private theorem baseTwoClassifyBelow3000_block_2 :
    ∀ i : Fin 128,
      let n := 2 * (128 * 2 + i.val) + 1
      n = 1 ∨ baseTwoRejectCheck n = true ∨ Nat.Prime n ∨ n = 2047 := by
  intro i
  fin_cases i <;> first | (norm_num; done) |
    (unfold baseTwoRejectCheck baseTwoRejectCheckData splitTwo; decide)

/-- Generated kernel-checked classification block for odd inputs. -/
private theorem baseTwoClassifyBelow3000_block_3 :
    ∀ i : Fin 128,
      let n := 2 * (128 * 3 + i.val) + 1
      n = 1 ∨ baseTwoRejectCheck n = true ∨ Nat.Prime n ∨ n = 2047 := by
  intro i
  fin_cases i <;> first | (norm_num; done) |
    (unfold baseTwoRejectCheck baseTwoRejectCheckData splitTwo; decide)

/-- Generated kernel-checked classification block for odd inputs. -/
private theorem baseTwoClassifyBelow3000_block_4 :
    ∀ i : Fin 128,
      let n := 2 * (128 * 4 + i.val) + 1
      n = 1 ∨ baseTwoRejectCheck n = true ∨ Nat.Prime n ∨ n = 2047 := by
  intro i
  fin_cases i <;> first | (norm_num; done) |
    (unfold baseTwoRejectCheck baseTwoRejectCheckData splitTwo; decide)

/-- Generated kernel-checked classification block for odd inputs. -/
private theorem baseTwoClassifyBelow3000_block_5 :
    ∀ i : Fin 128,
      let n := 2 * (128 * 5 + i.val) + 1
      n = 1 ∨ baseTwoRejectCheck n = true ∨ Nat.Prime n ∨ n = 2047 := by
  intro i
  fin_cases i <;> first | (norm_num; done) |
    (unfold baseTwoRejectCheck baseTwoRejectCheckData splitTwo; decide)

/-- Generated kernel-checked classification block for odd inputs. -/
private theorem baseTwoClassifyBelow3000_block_6 :
    ∀ i : Fin 128,
      let n := 2 * (128 * 6 + i.val) + 1
      n = 1 ∨ baseTwoRejectCheck n = true ∨ Nat.Prime n ∨ n = 2047 := by
  intro i
  fin_cases i <;> first | (norm_num; done) |
    (unfold baseTwoRejectCheck baseTwoRejectCheckData splitTwo; decide)

/-- Generated kernel-checked classification block for odd inputs. -/
private theorem baseTwoClassifyBelow3000_block_7 :
    ∀ i : Fin 128,
      let n := 2 * (128 * 7 + i.val) + 1
      n = 1 ∨ baseTwoRejectCheck n = true ∨ Nat.Prime n ∨ n = 2047 := by
  intro i
  fin_cases i <;> first | (norm_num; done) |
    (unfold baseTwoRejectCheck baseTwoRejectCheckData splitTwo; decide)

/-- Generated kernel-checked classification block for odd inputs. -/
private theorem baseTwoClassifyBelow3000_block_8 :
    ∀ i : Fin 128,
      let n := 2 * (128 * 8 + i.val) + 1
      n = 1 ∨ baseTwoRejectCheck n = true ∨ Nat.Prime n ∨ n = 2047 := by
  intro i
  fin_cases i <;> first | (norm_num; done) |
    (unfold baseTwoRejectCheck baseTwoRejectCheckData splitTwo; decide)

/-- Generated kernel-checked classification block for odd inputs. -/
private theorem baseTwoClassifyBelow3000_block_9 :
    ∀ i : Fin 128,
      let n := 2 * (128 * 9 + i.val) + 1
      n = 1 ∨ baseTwoRejectCheck n = true ∨ Nat.Prime n ∨ n = 2047 := by
  intro i
  fin_cases i <;> first | (norm_num; done) |
    (unfold baseTwoRejectCheck baseTwoRejectCheckData splitTwo; decide)

/-- Generated kernel-checked classification block for odd inputs. -/
private theorem baseTwoClassifyBelow3000_block_10 :
    ∀ i : Fin 128,
      let n := 2 * (128 * 10 + i.val) + 1
      n = 1 ∨ baseTwoRejectCheck n = true ∨ Nat.Prime n ∨ n = 2047 := by
  intro i
  fin_cases i <;> first | (norm_num; done) |
    (unfold baseTwoRejectCheck baseTwoRejectCheckData splitTwo; decide)

/-- Generated kernel-checked classification block for odd inputs. -/
private theorem baseTwoClassifyBelow3000_block_11 :
    ∀ i : Fin 92,
      let n := 2 * (128 * 11 + i.val) + 1
      n = 1 ∨ baseTwoRejectCheck n = true ∨ Nat.Prime n ∨ n = 2047 := by
  intro i
  fin_cases i <;> first | (norm_num; done) |
    (unfold baseTwoRejectCheck baseTwoRejectCheckData splitTwo; decide)

/-- The generated blocks cover all 1500 odd-index values below `3000`. -/
private theorem baseTwoClassifyBelow3000 :
    ∀ k : Fin 1500,
      let n := 2 * k.val + 1
      n = 1 ∨ baseTwoRejectCheck n = true ∨ Nat.Prime n ∨ n = 2047 := by
  intro k
  let b := k.val / 128
  let i := k.val % 128
  have hb : b < 12 := by
    dsimp only [b]
    omega
  have hi : i < 128 := by
    dsimp only [i]
    omega
  have hk : k.val = 128 * b + i := by
    dsimp only [b, i]
    omega
  have hblock :
      let n := 2 * (128 * b + i) + 1
      n = 1 ∨ baseTwoRejectCheck n = true ∨ Nat.Prime n ∨ n = 2047 := by
    interval_cases b
    · exact baseTwoClassifyBelow3000_block_0 ⟨i, hi⟩
    · exact baseTwoClassifyBelow3000_block_1 ⟨i, hi⟩
    · exact baseTwoClassifyBelow3000_block_2 ⟨i, hi⟩
    · exact baseTwoClassifyBelow3000_block_3 ⟨i, hi⟩
    · exact baseTwoClassifyBelow3000_block_4 ⟨i, hi⟩
    · exact baseTwoClassifyBelow3000_block_5 ⟨i, hi⟩
    · exact baseTwoClassifyBelow3000_block_6 ⟨i, hi⟩
    · exact baseTwoClassifyBelow3000_block_7 ⟨i, hi⟩
    · exact baseTwoClassifyBelow3000_block_8 ⟨i, hi⟩
    · exact baseTwoClassifyBelow3000_block_9 ⟨i, hi⟩
    · exact baseTwoClassifyBelow3000_block_10 ⟨i, hi⟩
    · have hiLast : i < 92 := by
        dsimp only [b, i] at *
        omega
      exact baseTwoClassifyBelow3000_block_11 ⟨i, hiLast⟩
  simpa only [hk] using hblock
-- END GENERATED baseTwoClassifyBelow3000

/--
For every odd composite `n` with `1 < n < 3000`, one of bases `2` and `3` is rejected by the
existing Strong Miller–Rabin test. The generated finite classification proves the only exception
to base `2` is `2047`, whose base-`3` failure is checked separately above.
-/
theorem base_two_or_three_rejects_of_lt_3000 {n : ℕ}
    (hn : 1 < n)
    (hnOdd : Odd n)
    (hnNotPrime : ¬ Nat.Prime n)
    (hlt : n < 3000) :
    strongMillerRabinWithBase n 2 = false ∨ strongMillerRabinWithBase n 3 = false := by
  obtain ⟨k, rfl⟩ := hnOdd
  have hk : k < 1500 := by omega
  have hclass := baseTwoClassifyBelow3000 ⟨k, hk⟩
  change 2 * k + 1 = 1 ∨ baseTwoRejectCheck (2 * k + 1) = true ∨
    Nat.Prime (2 * k + 1) ∨ 2 * k + 1 = 2047 at hclass
  rcases hclass with hone | hreject | hprime | hexception
  · omega
  · exact Or.inl (baseTwoRejectCheck_sound (by omega) hreject)
  · exact False.elim (hnNotPrime hprime)
  · exact Or.inr (by
      rw [hexception]
      exact baseThreeRejects_2047)

end PseudoPrime.PrimeTest
