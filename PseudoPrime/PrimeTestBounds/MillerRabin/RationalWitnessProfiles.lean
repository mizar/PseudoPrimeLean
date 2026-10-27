/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RationalCutoffWitnessBounds
public import PseudoPrime.Analysis.LogarithmicShiftBounds

/-! # Prepared rational Miller–Rabin coefficient-and-start profiles -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The pure Miller–Rabin profile has rational tuple (1,0,0) and starting value three.
Its leading coefficient is positive. This is the finite- and small-input baseline. -/
def pureLogarithmicProfile : Analysis.RationalLogarithmicProfile :=
  ⟨1, 0, 0, by norm_num only, 3⟩

/-- The retained signed Miller–Rabin tuple is (1,-2,193/40), starting at 3000.
Its positive leading coefficient and signed correction use the common profile structure.
It improves the pointwise bound on an interval below 10^100. -/
def rationalPart2Profile : Analysis.RationalLogarithmicProfile :=
  ⟨1, -2, 193 / 40, by norm_num only, 3000⟩

/-- A Miller–Rabin profile bound gives a prime rejecting base for every odd
composite input above the profile's own starting value, under GRH.
The witness lies through the profile's rational cutoff. Nonunit bases are permitted. -/
def MillerRabinProfileBound (profile : Analysis.RationalLogarithmicProfile) : Prop :=
  ∀ n : ℕ,
    Odd n →
      ¬n.Prime →
      AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
      profile.startingValue ≤ n →
      ∃ p : ℕ,
        p.Prime ∧ (p : ℝ) ≤ profile.cutoff n ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)

/-- Under GRH, the pure profile bounds prime witnesses for every odd composite
from three. Apply the existing pure logarithmic witness and normalize the profile expression.
This proves the baseline coefficient-and-start pair. -/
theorem pureLogarithmicProfile_bound : MillerRabinProfileBound pureLogarithmicProfile := by
  intro n hnOdd hnComposite hGRH hn
  have hn1 : 1 < n := (by decide : (1 : ℕ) < 3).trans_le hn
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_millerRabin_witness_le_log_sq hGRH hn1 hnOdd hnComposite
  refine ⟨p, hp, ?_, PrimeTest.not_strongMillerRabinPass_iff.mpr hf⟩
  simpa only [Analysis.RationalLogarithmicProfile.cutoff, Analysis.logarithmicShiftCutoff,
    Analysis.logarithmicShiftRoot, pureLogarithmicProfile, Rat.cast_one, Rat.cast_zero, zero_mul,
    add_zero, one_mul] using hb

/-- Under GRH, the signed profile bounds prime witnesses for every odd composite
from 3000. Apply the rational minimum witness and retain its corrected-square branch.
This proves the signed coefficient-and-start pair. -/
theorem rationalPart2Profile_bound : MillerRabinProfileBound rationalPart2Profile := by
  intro n hnOdd hnComposite hGRH hn
  have hn1 : 1 < n := (by decide : (1 : ℕ) < 3000).trans_le hn
  obtain ⟨p, hp, hb, hf⟩ :=
    exists_prime_witness_le_rationalCutoff_of_large hn1 hnOdd hnComposite hn hGRH
  refine ⟨p, hp, ?_, hf⟩
  have hr := hb.trans (min_le_right _ _)
  simpa only [Analysis.RationalLogarithmicProfile.cutoff, Analysis.logarithmicShiftCutoff,
    Analysis.logarithmicShiftRoot, Analysis.rationalPart2CutoffRoot, rationalPart2Profile,
    Rat.cast_one, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_div, neg_mul, one_mul,
    sub_eq_add_neg] using hr

/-- For 3000 ≤ n ≤ m, the signed profile cutoff is nondecreasing.
The logarithmic root is positive and b=-2 is above the negative lower logarithmic input.
This gives the same expression for the pointwise and finite-range bounds. -/
theorem rationalPart2Profile_cutoff_le {n m : ℕ} (hn : 3000 ≤ n) (horder : n ≤ m) :
    rationalPart2Profile.cutoff n ≤ rationalPart2Profile.cutoff m := by
  have hL := Analysis.eight_lt_log_level hn
  have hL0 : 0 < Real.log n := by linarith only [hL]
  have hlog :=
    Real.log_le_log (Nat.cast_pos.mpr ((by decide : (0 : ℕ) < 3000).trans_le hn))
      (Nat.cast_le.mpr horder)
  have hb : -Real.log n ≤ ((-2 : ℚ) : ℝ) := by
    norm_num only [Rat.cast_neg, Rat.cast_ofNat]
    linarith only [hL]
  have hR := Analysis.eight_lt_rationalPart2CutoffRoot hL.le
  have hroot : 0 ≤ Analysis.logarithmicShiftRoot (Real.log n) (-2) (193 / 40) := by
    norm_num only [Analysis.logarithmicShiftRoot, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_div]
    unfold Analysis.rationalPart2CutoffRoot at hR
    linarith only [hR]
  exact Analysis.logarithmicShiftCutoff_le_of_le (by norm_num only : (0 : ℚ) < 1) hL0 hlog hb hroot

/-- Under GRH, every odd composite 3000 ≤ n ≤ B has a prime witness through
the signed profile cutoff evaluated at B. Apply the pointwise witness and cutoff monotonicity.
No larger coefficient or additional starting value is used for the envelope. -/
theorem exists_prime_witness_le_rationalPart2Profile_envelope {n B : ℕ} (hn : 3000 ≤ n)
    (hnB : n ≤ B) (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ rationalPart2Profile.cutoff B ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hf⟩ := rationalPart2Profile_bound n hnOdd hnComposite hGRH hn
  exact ⟨p, hp, hb.trans (rationalPart2Profile_cutoff_le hn hnB), hf⟩

/-- Any proved profile bound gives the least prime rejecting base through its
own cutoff for an odd composite above its entrance, under GRH.
Minimize the unbounded prime-rejection predicate on the natural numbers.
Minimality compares all rejecting prime bases and retains the pointwise upper bound. -/
theorem exists_least_prime_witness_of_profile_bound {profile : Analysis.RationalLogarithmicProfile}
    (hprofile : MillerRabinProfileBound profile) {n : ℕ} (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hn : profile.startingValue ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ profile.cutoff n ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, hf⟩ := hprofile n hnOdd hnComposite hGRH hn
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hf ↦
      Nat.find_min' hex ⟨hr, hf⟩⟩

/-- The retained Miller–Rabin catalog contains the pure and signed profiles.
Both have an improvement interval below 10^100 among the prepared candidates.
The old constant-five tuple and large-start tuples are omitted from this catalog. -/
def retainedRationalProfiles : List Analysis.RationalLogarithmicProfile :=
  [pureLogarithmicProfile, rationalPart2Profile]

end PseudoPrime.PrimeTestBounds.MillerRabin
