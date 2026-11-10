/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquareCommon
import PseudoPrime.PrimeTestBounds.MillerRabin.SquareSeed89Stage414
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed373Count
import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeCountExtend
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849Count

/-! # Square-factor witnesses on logarithmic scales 63 to 68 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Prime labels through 991 used for the interior square-factor count. -/
private def seed991 : List ℕ :=
  primeSeed1849Extra.drop 116 ++ primeSeed373Primes

/-- Upper logarithm weights for the prime labels through 991. -/
private def weights991 : List ℕ :=
  List.replicate 93 76 ++ primeSeed373Weights

/-- The truncated prime labels are distinct, have the indicated weights, and
have positive weights. These facts transfer from the larger certified list. -/
private theorem labels991 :
    seed991.Nodup ∧
      seed991.map primeSeed1849Weight = weights991 ∧ ∀ p ∈ seed991, 0 < primeSeed1849Weight p := by
  have hsub : seed991.Sublist primeSeed1849Primes :=
    (List.drop_sublist 116 primeSeed1849Extra).append (List.Sublist.refl _)
  refine ⟨hsub.nodup primeSeed1849_labels.1, ?_, ?_⟩
  · decide +kernel
  · intro p hp
    exact primeSeed1849_labels.2.2 p (hsub.subset hp)

/-- Every label in the truncated list is prime and at most 991. -/
private theorem primes991 : ∀ p ∈ seed991, p.Prime ∧ p ≤ 991 := by
  intro p hp
  have hsub : seed991.Sublist primeSeed1849Primes :=
    (List.drop_sublist 116 primeSeed1849Extra).append (List.Sublist.refl _)
  have hp' := primeSeed1849_prime_supply p (hsub.subset hp)
  refine ⟨hp'.1, ?_⟩
  have hdrop : ∀ p ∈ primeSeed1849Extra.drop 116, p ≤ 991 := by decide +kernel
  rcases List.mem_append.mp hp with he | he
  · exact hdrop p he
  · exact ((primeSeed373_prime_supply p he).2).trans (by decide)

/-- The additional 93 labels provide a multichoose lower bound for the
weighted product count, starting from a certified budget through 500. -/
private theorem count991 (A k : ℕ) (hA : A ≤ 500) :
    Nat.choose (93 + k) k * primeSeed373Row14.getD A 0 ≤
      weightedPrimeCount id weights991 (A + k * 76) := by
  have hb := primeSeed373_count_lower A hA
  have hg := weightedPrimeCount_group_lower 76 A 93 k primeSeed373Weights (by decide)
  exact (Nat.mul_le_mul_left (Nat.choose (93 + k) k) hb).trans hg

/-- The truncated labels inherit the logarithmic weight bounds from the
certified supply through 1849. -/
private theorem seedweight991 : ∀ p ∈ seed991, Real.log p ≤ (primeSeed1849Weight p : ℝ) / 10 := by
  intro p hp
  have hs : seed991.Sublist primeSeed1849Primes :=
    (List.drop_sublist 116 primeSeed1849Extra).append (List.Sublist.refl _)
  exact primeSeed1849_weight_bounds p (hs.subset hp)

/-- A square divisor of an input of logarithmic scale at most 68 has base at most
600000000000000. A rational logarithm certificate bounds its square. -/
private theorem bound68 {n p : ℕ} (hn : 1 < n) (hdiv : p ^ 2 ∣ n) (hU : Real.log n ≤ (68 : ℝ)) :
    p ≤ 600000000000000 := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 360000000000000000000000000000 99 32 68 70 = true by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hcert
  have hnle : n ≤ 360000000000000000000000000000 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (360000000000000000000000000000 : ℝ) := hU.trans hcert
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 360000000000000000000000000000)).mp
        hlog
  have hpsq : p ^ 2 ≤ 360000000000000000000000000000 :=
    (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
  nlinarith only [hpsq]

/-- A base at least 1000000000001 has square logarithm above budget 552/10.
A rational logarithm certificate supplies the strict margin. -/
private theorem budget552 {p : ℕ} (hbig : 1000000000001 ≤ p) :
    (552 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1000000000001 40 32 (2761 / 100) 29 = true by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 1000000000001) (Nat.cast_le.mpr hbig)
  rw [Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [h, hl]

/-- A checked weighted count exceeding the square kernel yields a rejecting prime
at most 991. The budget ensures that the counted products are distinct modulo the square. -/
private theorem square991_count {n p H : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hcount : p - 1 < weightedPrimeCount id weights991 H)
    (hbudget : (H : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 991 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  let : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  let K := (powMonoidHom (n - 1) : (ZMod (p ^ 2))ˣ →* (ZMod (p ^ 2))ˣ).ker
  have hcard : Nat.card K < weightedPrimeCount id weights991 H := by
    change Nat.card (powMonoidHom (n - 1) : (ZMod (p ^ 2))ˣ →* (ZMod (p ^ 2))ˣ).ker < _
    rw [NumberTheory.card_local_fermat_kernel_prime_pow hn hp hp2 (by decide : 0 < 2) hdiv]
    exact (Nat.gcd_le_left (n - 1) (Nat.sub_pos_of_lt hp.one_lt)).trans_lt hcount
  exact
    exists_prime_reject_of_weight_list K seed991 weights991 991 H primeSeed1849Weight 10
      (by norm_num only) (pow_pos hp.pos 2) labels991.1 (fun r hr ↦ (primes991 r hr).1)
      (fun r hr ↦ (primes991 r hr).2) labels991.2.2 seedweight991 labels991.2.1 hbudget hcard
      (fun r hr ↦ PrimeTest.strongMR_local_divisorKernel hn ho hdiv hr)

/-- An odd input with a prime-square divisor and logarithm between 63 and 68 has
a quarter-square rejecting prime. Independent count stages cover the divisor sizes. -/
theorem quarter_square_63_68 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hdiv : p ^ 2 ∣ n)
    (hL : (63 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 68) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hB : (991 : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  by_cases hlow : p ≤ 1054033525
  · obtain ⟨r, hr, hb, hf⟩ := square_reject_le1054 hn ho hp hdiv hlow
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans ((by norm_num only : (89 : ℝ) ≤ 991).trans hB), hf⟩
  by_cases hmid : p ≤ 1000000000000
  · have hc := count991 414 0 (by decide)
    norm_num only [Nat.choose_zero_right, Nat.one_mul, Nat.zero_mul, Nat.add_zero] at hc
    rw [show primeSeed373Row14.getD 414 0 = 1488482619460 by decide +kernel] at hc
    have hcount : p - 1 < weightedPrimeCount id weights991 414 :=
      (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le
        (hmid.trans ((by norm_num only : 1000000000000 ≤ 1488482619460).trans hc))
    obtain ⟨r, hr, hb, hf⟩ :=
      square991_count hn ho hp hdiv hcount
        (square_factor_budget_414 (Nat.succ_le_of_lt (Nat.lt_of_not_ge hlow)))
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩
  · have hc := count991 476 1 (by decide)
    norm_num only [Nat.choose, Nat.add_zero, Nat.one_mul, Nat.zero_mul] at hc
    rw [show primeSeed373Row14.getD 476 0 = 24433960763174 by decide +kernel] at hc
    have hcount : p - 1 < weightedPrimeCount id weights991 552 :=
      (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le
        ((bound68 hn hdiv hU).trans
          ((by norm_num only : 600000000000000 ≤ 94 * 24433960763174).trans hc))
    obtain ⟨r, hr, hb, hf⟩ :=
      square991_count hn ho hp hdiv hcount (budget552 (Nat.succ_le_of_lt (Nat.lt_of_not_ge hmid)))
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
