/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.EndpointFiniteCredits
public import PseudoPrime.Analysis.EndpointPrime79

/-! # Fourteen fixed-prime profiles for the tuned envelope -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The thirteen tuned finite-principal profiles and the additional fixed-79 profile. -/
inductive TunedPrimeProfile
  | finite (profile : FinitePrimeProfile)
  | p79
  deriving DecidableEq

/-- Every tuned cap extends the corresponding current sharp finite cap. -/
theorem finiteTuned_cap_extends (f : FinitePrimeProfile) : f.logCap ≤ f.tunedCap := by
  cases f <;> decide +kernel

namespace TunedPrimeProfile

/-- The fixed prime cutoff returned by each of the fourteen profiles. -/
def bound : TunedPrimeProfile → ℕ
  | .finite f => f.bound
  | .p79 => 79

/-- The certified upper logarithmic cap of each profile. -/
def logCap : TunedPrimeProfile → ℚ
  | .finite f => f.tunedCap
  | .p79 => prime79Cap

/-- The preceding tuned cap, with zero at the first fixed-prime profile. -/
def previousCap : TunedPrimeProfile → ℚ
  | .finite .p23 => 0
  | .finite .p29 => FinitePrimeProfile.p23.tunedCap
  | .finite .p31 => FinitePrimeProfile.p29.tunedCap
  | .finite .p37 => FinitePrimeProfile.p31.tunedCap
  | .finite .p41 => FinitePrimeProfile.p37.tunedCap
  | .finite .p43 => FinitePrimeProfile.p41.tunedCap
  | .finite .p47 => FinitePrimeProfile.p43.tunedCap
  | .finite .p53 => FinitePrimeProfile.p47.tunedCap
  | .finite .p59 => FinitePrimeProfile.p53.tunedCap
  | .finite .p61 => FinitePrimeProfile.p59.tunedCap
  | .finite .p67 => FinitePrimeProfile.p61.tunedCap
  | .finite .p71 => FinitePrimeProfile.p67.tunedCap
  | .finite .p73 => FinitePrimeProfile.p71.tunedCap
  | .p79 => FinitePrimeProfile.p73.tunedCap

/-- Every fixed cutoff in the tuned profile family is prime. -/
theorem prime (f : TunedPrimeProfile) : Nat.Prime f.bound := by
  cases f with
  | finite f => cases f <;> decide +kernel
  | p79 => decide +kernel

end TunedPrimeProfile

end PseudoPrime.Analysis
