/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeLocalCheck
public import PseudoPrime.PrimeTestBounds.MillerRabin.CountCandidateData

/-! # Uniform coefficient cells for semiprimes -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A semiprime logarithmic interval, its selected counting candidate and the rational
logarithm data needed to bound the local envelope at the interval's right endpoint. -/
structure SemiprimeUniformCell where
  /-- Index of the selected certified counting candidate. -/
  candidate : ℕ
  /-- Left logarithmic endpoint. -/
  lo : ℚ
  /-- Right logarithmic endpoint. -/
  hi : ℚ
  /-- Rational lower logarithm endpoint for the local scale. -/
  logLower : ℚ
  /-- Binary scale for the local logarithm check. -/
  logScale : ℕ

/-- Check that the candidate cutoff and the local envelope at the right endpoint fit
within `(409/1000) * lo²`. The check also enforces nonnegative and ordered endpoints. -/
def SemiprimeUniformCell.check (c : SemiprimeUniformCell) : Bool :=
  match allCountCandidates[c.candidate]? with
  | none => false
  | some d =>
    let tau := max d.candidate.upper (c.hi - d.candidate.lower)
    let budget := (409 / 1000 : ℚ) * c.lo ^ 2
    decide
      (0 ≤ c.lo ∧
        c.lo ≤ c.hi ∧
        0 ≤ d.candidate.upper ∧
        (d.candidate.bound : ℚ) ≤ budget ∧ localUpperCheck tau c.logLower budget c.logScale = true)

/-- Under GRH, a checked cell gives a rejecting-prime bound with coefficient `409/1000`
for odd products of distinct primes whose logarithm lies in the cell. Monotonicity of the
local envelope and of squaring transfers the rational endpoint check to the actual scale. -/
theorem SemiprimeUniformCell.sound {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (c : SemiprimeUniformCell)
    (hcheck : c.check = true) (hlo : (c.lo : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (c.hi : ℝ)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (409 / 1000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  cases heq : allCountCandidates[c.candidate]? with
  | none => simp only [SemiprimeUniformCell.check, heq, Bool.false_eq_true] at hcheck
  | some
    d =>
    have hc :
      0 ≤ c.lo ∧
        c.lo ≤ c.hi ∧
        0 ≤ d.candidate.upper ∧
        (d.candidate.bound : ℚ) ≤ (409 / 1000 : ℚ) * c.lo ^ 2 ∧
        localUpperCheck (max d.candidate.upper (c.hi - d.candidate.lower)) c.logLower
            ((409 / 1000 : ℚ) * c.lo ^ 2) c.logScale =
          true := by
      apply of_decide_eq_true
      simpa only [SemiprimeUniformCell.check, heq] using hcheck
    have hlo0 : (0 : ℝ) ≤ c.lo := by exact_mod_cast hc.1
    have hupper0 : (0 : ℝ) ≤ d.candidate.upper := by exact_mod_cast hc.2.2.1
    have htau0 : (0 : ℝ) ≤ max (d.candidate.upper : ℝ) (Real.log n - d.candidate.lower) :=
      hupper0.trans (le_max_left _ _)
    have htau :
      max (d.candidate.upper : ℝ) (Real.log n - d.candidate.lower) ≤
        (max d.candidate.upper (c.hi - d.candidate.lower) : ℚ) := by
      simp only [Rat.cast_max, Rat.cast_sub]
      exact max_le_max_left _ (sub_le_sub_right hhi _)
    have hlocal := (localFullEnvelope_mono htau0 htau).trans (localUpperCheck_sound hc.2.2.2.2)
    have hbound := (Rat.cast_le (K := ℝ)).mpr hc.2.2.2.1
    simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
      Rat.cast_natCast] at hbound hlocal
    have hsq : (c.lo : ℝ) ^ 2 ≤ (Real.log n) ^ 2 := pow_le_pow_left₀ hlo0 hlo 2
    obtain ⟨r, hr, hrB, hfail⟩ :=
      allCountCandidates_semiprime hn ho hp hq hpq hprod hGRH d (List.mem_of_getElem? heq)
    have hrB' : (r : ℝ) ≤ (409 / 1000 : ℝ) * (c.lo : ℝ) ^ 2 := by
      exact hrB.trans (max_le hbound hlocal)
    refine ⟨r, hr, ?_, hfail⟩
    nlinarith only [hrB', hsq]

end PseudoPrime.PrimeTestBounds.MillerRabin
