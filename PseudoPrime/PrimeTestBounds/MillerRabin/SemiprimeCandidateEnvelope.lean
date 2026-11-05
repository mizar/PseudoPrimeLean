/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeLocalCounting

/-! # Finite semiprime local and counting envelopes -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Parameters of a semiprime counting candidate. `bound` is the prime cutoff,
`count` a supplied prime-count lower bound, and `degree` the product degree.
The rational `upper` bounds the product-size logarithm and `lower` bounds the
multichoose logarithm. Their certificate is supplied separately when selecting
a finite family; this structure is used to build the semiprime envelope. -/
structure SemiprimeCandidate where
  /-- The prime cutoff. -/
  bound : ℕ
  /-- A lower bound on the number of available primes. -/
  count : ℕ
  /-- The maximum number of prime factors in a counted product. -/
  degree : ℕ
  /-- An upper bound for the logarithm of the product cutoff. -/
  upper : ℚ
  /-- A lower bound for the logarithm of the multichoose count. -/
  lower : ℚ

/-- The semiprime witness bound associated with a counting candidate at log
scale `L`. The maximum joins the prime cutoff to the local envelope at the
candidate's threshold. Validated candidates are combined by finite minimum. -/
noncomputable def semiprimeCandidateBound (c : SemiprimeCandidate) (L : ℝ) : ℝ :=
  max (c.bound : ℝ) (localFullEnvelope (max (c.upper : ℝ) (L - c.lower)))

/-- The minimum of the semiprime bounds for a nonempty finite candidate set at
scale `L`. The minimum is attained and preserves all candidates in the supplied
set; their prime-supply and logarithm certificates remain separate inputs. -/
noncomputable def semiprimeCandidateEnvelope (S : Finset SemiprimeCandidate) (hS : S.Nonempty)
    (L : ℝ) : ℝ :=
  S.inf' hS (fun c ↦ semiprimeCandidateBound c L)

/-- Under GRH, the finite semiprime candidate envelope bounds a rejecting prime
for every odd `n = p*q` with primes `p < q`, when each candidate has a valid
prime supply and logarithmic bounds. Select a minimising candidate and apply
its local-or-counting witness theorem. This is the consumer for the certified
finite supply and degree data. -/
theorem exists_prime_reject_semiprime_envelope {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (S : Finset SemiprimeCandidate)
    (hS : S.Nonempty)
    (hcert :
      ∀ c ∈ S,
        1 < c.bound ∧
          c.count ≤ c.bound.primeCounting ∧
          (c.degree : ℝ) * Real.log c.bound ≤ c.upper ∧
          (c.lower : ℝ) ≤ Real.log (Nat.choose (c.count + c.degree) c.degree : ℝ)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ semiprimeCandidateEnvelope S hS (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨c, hc, heq⟩ :=
    Finset.exists_mem_eq_inf' hS (fun c ↦ semiprimeCandidateBound c (Real.log n))
  obtain ⟨hB, hpi, hu, hv⟩ := hcert c hc
  rw [semiprimeCandidateEnvelope, heq]
  exact exists_prime_reject_semiprime_candidate hn ho hp hq hpq hprod hB hpi hGRH hu hv

end PseudoPrime.PrimeTestBounds.MillerRabin
