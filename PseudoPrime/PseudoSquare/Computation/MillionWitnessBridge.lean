/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PseudoSquare.Computation.MillionCertificate
import PseudoPrime.PseudoSquare.Bounds.WitnessMaximum

/-!
# Adapter from the million-residue certificate to the Q witness API

The generated certificate above remains independent of witness maxima and GRH.  This leaf applies
the certificate to the existing least-prime witness only where a downstream Q bound needs it.
-/

namespace PseudoPrime.PseudoSquare

/-- The million CRT certificate bounds the existing least-prime witness. -/
theorem primeNeOneWitness_le_fortySeven_of_lt_million {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hB : n < 1000000) :
    NumberTheory.primeNeOneWitness n
        (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
          (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) ≤
      47 := by
  obtain ⟨p, hp, hj⟩ := qNeOneMillion_exists hn hns hB
  obtain ⟨hpprime, hpodd, hp47⟩ := qNeOneMillionPrimes_spec hp
  exact (NumberTheory.primeNeOneWitness_le n _ ⟨hpprime, hpodd, hj⟩).trans hp47

end PseudoPrime.PseudoSquare
