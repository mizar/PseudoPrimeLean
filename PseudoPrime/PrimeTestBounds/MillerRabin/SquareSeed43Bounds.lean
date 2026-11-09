/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed43
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedCountWitness

/-! # Weighted square-divisor supply and factor bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A prime-square divisor of an input with logarithm at most 13.3 has base at
most 809. A rational logarithm bound limits the input and hence the square. -/
theorem square_factor_le_809 {n p : ℕ} (hn : 1 < n) (hdiv : p ^ 2 ∣ n)
    (hU : Real.log n ≤ (133 / 10 : ℝ)) : p ≤ 809 := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 654481 20 32 (133 / 10) 14 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hnle : n ≤ 654481 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (654481 : ℝ) := hU.trans hcert
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 654481)).mp
        hlog
  have hpsq : p ^ 2 ≤ 654481 := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
  nlinarith only [hpsq]

/-- A prime above 43 is at least 47. The finite intervening integers are
composite, as checked directly from primality. -/
theorem prime_ge_47_of_gt_43 {p : ℕ} (hp : p.Prime) (hbig : 43 < p) : 47 ≤ p := by
  by_contra h
  have hlo : 44 ≤ p := Nat.succ_le_of_lt hbig
  have hhi : p ≤ 46 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge h)
  interval_cases p <;> norm_num only [Nat.prime_def_lt] at hp

/-- For an integer at least 47, the logarithm of its square strictly exceeds
the weighted budget 77/10. A rational lower bound for `log 47` gives the
strict margin required by the local-kernel argument. -/
theorem square_factor_budget_77 {p : ℕ} (hbig : 47 ≤ p) :
    (77 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
  have h47 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 47 6 32 (38501 / 10000) 4 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h47
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 47) (Nat.cast_le.mpr hbig)
  rw [Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [h47, hl]

/-- An odd input with a prime-square divisor of base at most 809 has a
rejecting prime at most 43 when the budget is below the square's logarithm.
The checked count table is transferred directly to the original-input kernel. -/
theorem exists_prime_reject_square_seed43 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hbound : p ≤ 809) (hbudget : (77 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 43 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  let H := (powMonoidHom (n - 1) : (ZMod (p ^ 2))ˣ →* (ZMod (p ^ 2))ˣ).ker
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  have hcard : Nat.card H < primeSeed43Row.getD 77 0 := by
    change Nat.card (powMonoidHom (n - 1) : (ZMod (p ^ 2))ˣ →* (ZMod (p ^ 2))ˣ).ker < _
    rw [NumberTheory.card_local_fermat_kernel_prime_pow hn hp hp2 (by decide : 0 < 2) hdiv]
    have hg := Nat.gcd_le_left (n - 1) (Nat.sub_pos_of_lt hp.one_lt)
    change Nat.gcd (p - 1) (n - 1) < 809
    exact hg.trans_lt ((Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hbound)
  exact
    exists_prime_reject_of_weight_table H primeSeed43Primes primeSeed43Weights 43 77 77
      primeSeed43Weight 10 (by norm_num only) (pow_pos hp.pos 2) primeSeed43_labels.1
      (fun p hp ↦ (primeSeed43_prime_supply p hp).1) (fun p hp ↦ (primeSeed43_prime_supply p hp).2)
      primeSeed43_labels.2.2 primeSeed43_weight_bounds primeSeed43_labels.2.1 hbudget (by decide)
      primeSeed43Row primeSeed43Tail primeSeed43_checked hcard
      (fun r hr ↦ PrimeTest.strongMR_local_divisorKernel hn ho hdiv hr)

end PseudoPrime.PrimeTestBounds.MillerRabin
