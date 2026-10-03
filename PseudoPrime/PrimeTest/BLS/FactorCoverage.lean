/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.BLS.FactorSupply
import PseudoPrime.NumberTheory.Factorization.PollardRho.Orbit

/-!
# Orbit conditions for complete BLS factor supply

`RhoFactorTreeCoverage` records prime leaves and, at each composite split, the exact condition
that lets the bounded rho routine return a proper factor. It is a sufficient coverage contract,
not an unconditional guarantee for fixed rho parameters.
-/

namespace PseudoPrime.PrimeTest.BLS

/-- A depth-bounded factor tree whose internal nodes are covered by executable rho conditions.
Even nodes use the immediate factor two branch. Odd nodes record a bounded comparison with all
earlier gcds equal to one and a proper gcd at the selected comparison. Both children have one less
split depth. -/
inductive RhoFactorTreeCoverage (params : NumberTheory.Factorization.PollardRho.Params) :
    ℕ → ℕ → Prop
  | prime {depth n} (hprime : Nat.Prime n) : RhoFactorTreeCoverage params depth n
  |
  even {fuel n} (hn : 2 < n) (heven : n % 2 = 0) (left : RhoFactorTreeCoverage params fuel 2)
    (right : RhoFactorTreeCoverage params fuel (n / 2)) : RhoFactorTreeCoverage params (fuel + 1) n
  |
  odd {fuel n} (hn : 2 < n) (hodd : n % 2 ≠ 0) (target : ℕ) (htarget : 0 < target)
    (htargetFuel : target ≤ fuel + 1)
    (hprior :
      ∀ i,
        1 ≤ i →
          i < target →
          NumberTheory.Factorization.PollardRho.orbitGcd n params.c (params.seed : ZMod n) i = 1)
    (hproper :
      1 < NumberTheory.Factorization.PollardRho.orbitGcd n params.c (params.seed : ZMod n) target ∧
        NumberTheory.Factorization.PollardRho.orbitGcd n params.c (params.seed : ZMod n) target < n)
    (left :
      RhoFactorTreeCoverage params fuel
        (NumberTheory.Factorization.PollardRho.orbitGcd n params.c (params.seed : ZMod n) target))
    (right :
      RhoFactorTreeCoverage params fuel
        (n /
          NumberTheory.Factorization.PollardRho.orbitGcd n params.c (params.seed : ZMod n)
            target)) :
    RhoFactorTreeCoverage params (fuel + 1) n

/-- Orbit coverage is sufficient for the bounded recursive supplier to return a prime list whose
product is the input. This connects the first-proper-gcd theorem at every odd internal node. -/
theorem primeFactorListFuel_of_coverage {params : NumberTheory.Factorization.PollardRho.Params}
    {depth n : ℕ} (hcoverage : RhoFactorTreeCoverage params depth n) :
    ∃ factors,
      primeFactorListFuel params depth n = some factors ∧
        (∀ p, p ∈ factors → Nat.Prime p) ∧ factors.prod = n := by
  induction hcoverage with
  | @prime depth n
    hprime =>
    refine
      ⟨[n], primeFactorListFuel_of_prime hprime, ?_, by
        simp only [List.prod_cons, List.prod_nil, mul_one]⟩
    intro p hp
    simp only [List.mem_singleton] at hp
    exact hp ▸ hprime
  | @even fuel n hn heven left right ihLeft
    ihRight =>
    rcases ihLeft with ⟨leftFactors, hleft, hleftPrime, hleftProduct⟩
    rcases ihRight with ⟨rightFactors, hright, hrightPrime, hrightProduct⟩
    by_cases hprime : Nat.Prime n
    · refine
        ⟨[n], primeFactorListFuel_of_prime hprime, ?_, by
          simp only [List.prod_cons, List.prod_nil, mul_one]⟩
      intro p hp
      simp only [List.mem_singleton] at hp
      exact hp ▸ hprime
    · refine ⟨leftFactors ++ rightFactors, ?_, ?_, ?_⟩
      · rw [primeFactorListFuel_even_eq_split hn hprime heven, hleft, hright]
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hleftPrime p hp
        · exact hrightPrime p hp
      · rw [List.prod_append, hleftProduct, hrightProduct]
        have hdvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero heven
        have hproduct : 2 * (n / 2) = n := Nat.mul_div_cancel' hdvd
        exact hproduct
  | @odd fuel n hn hodd target htarget htargetFuel hprior hproper left right ihLeft
    ihRight =>
    rcases ihLeft with ⟨leftFactors, hleft, hleftPrime, hleftProduct⟩
    rcases ihRight with ⟨rightFactors, hright, hrightPrime, hrightProduct⟩
    by_cases hprime : Nat.Prime n
    · refine
        ⟨[n], primeFactorListFuel_of_prime hprime, ?_, by
          simp only [List.prod_cons, List.prod_nil, mul_one]⟩
      intro p hp
      simp only [List.mem_singleton] at hp
      exact hp ▸ hprime
    · let divisor :=
        NumberTheory.Factorization.PollardRho.orbitGcd n params.c (params.seed : ZMod n) target
      have hfind :
        NumberTheory.Factorization.PollardRho.findFactor n params (fuel + 1) = some divisor := by
        dsimp only [divisor]
        exact
          NumberTheory.Factorization.PollardRho.findFactor_of_firstProper hn hodd htarget
            htargetFuel hprior hproper
      refine ⟨leftFactors ++ rightFactors, ?_, ?_, ?_⟩
      · simp only [primeFactorListFuel, NumberTheory.Factorization.PollardRho.primeFactorListFuel,
          ite_eq_right hprime, hfind, divisor, hleft, hright]
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hleftPrime p hp
        · exact hrightPrime p hp
      · rw [List.prod_append, hleftProduct, hrightProduct]
        have hdivisor : divisor ∣ n := Nat.gcd_dvd_right _ _
        exact Nat.mul_div_cancel' hdivisor

/-- Increasing the split-depth bound preserves a successful recursive factorization and its
returned list. Each node's local rho budget increases by the same amount. -/
theorem primeFactorListFuel_mono_depth {params : NumberTheory.Factorization.PollardRho.Params}
    {fuel fuel' n : ℕ} {factors : List ℕ} (hle : fuel ≤ fuel')
    (h : primeFactorListFuel params fuel n = some factors) :
    primeFactorListFuel params fuel' n = some factors := by
  induction fuel generalizing fuel' n factors with
  | zero =>
    by_cases hprime : Nat.Prime n
    · have hlist : factors = [n] := by
        exact
          Option.some.inj
            (by
              simpa only [primeFactorListFuel,
                NumberTheory.Factorization.PollardRho.primeFactorListFuel, hprime, ite_true] using
                h.symm)
      subst factors
      exact primeFactorListFuel_of_prime hprime
    · simp only [primeFactorListFuel, NumberTheory.Factorization.PollardRho.primeFactorListFuel,
        hprime, ite_false, reduceCtorEq] at h
  | succ fuel ih =>
    by_cases hprime : Nat.Prime n
    · have hlist : factors = [n] := by
        exact
          Option.some.inj
            (by
              simpa only [primeFactorListFuel,
                NumberTheory.Factorization.PollardRho.primeFactorListFuel, hprime, ite_true] using
                h.symm)
      subst factors
      exact primeFactorListFuel_of_prime hprime
    · cases fuel' with
      | zero => exact False.elim (Nat.not_succ_le_zero fuel hle)
      | succ fuel' =>
        cases hfind : NumberTheory.Factorization.PollardRho.findFactor n params (fuel + 1) with
        | none =>
          simp only [primeFactorListFuel, NumberTheory.Factorization.PollardRho.primeFactorListFuel,
            hprime, hfind, ite_false, reduceCtorEq] at h
        | some
          divisor =>
          simp only [primeFactorListFuel, NumberTheory.Factorization.PollardRho.primeFactorListFuel,
            ite_eq_right hprime, hfind] at h
          cases hleft : primeFactorListFuel params fuel divisor with
          | none => simp only [hleft, reduceCtorEq] at h
          | some left =>
            cases hright : primeFactorListFuel params fuel (n / divisor) with
            | none => simp only [hleft, hright, reduceCtorEq] at h
            | some
              right =>
              have hconcat : left ++ right = factors := by
                simpa only [hleft, hright, Option.some.injEq] using h
              subst factors
              have hle' : fuel ≤ fuel' := Nat.le_of_succ_le_succ hle
              have hfind' :
                NumberTheory.Factorization.PollardRho.findFactor n params (fuel' + 1) =
                  some divisor := by
                have hbudget : fuel' + 1 = (fuel + 1) + (fuel' - fuel) :=
                  (congrArg (fun k : ℕ => k + 1) (Nat.add_sub_of_le hle').symm).trans
                    (Nat.add_right_comm fuel (fuel' - fuel) 1)
                rw [hbudget]
                exact
                  NumberTheory.Factorization.PollardRho.findFactor_mono_fuel (fuel := fuel + 1)
                    (extra := fuel' - fuel) hfind
              simp only [primeFactorListFuel,
                NumberTheory.Factorization.PollardRho.primeFactorListFuel, ite_eq_right hprime,
                hfind']
              simp only [ih (fuel' := fuel') hle' hleft, ih (fuel' := fuel') hle' hright]

/-- A successful complete `n - 1` factor supply is unchanged by increasing split depth. -/
theorem partialFactorizationOfNMinusOne_mono_fuel {n fuel fuel' : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {data : PartialFactorizationData}
    (hle : fuel ≤ fuel') (h : partialFactorizationOfNMinusOne n params fuel = some data) :
    partialFactorizationOfNMinusOne n params fuel' = some data := by
  cases hlist : nMinusOnePrimeFactors n params fuel with
  | none => simp only [partialFactorizationOfNMinusOne, hlist, reduceCtorEq] at h
  | some
    factors =>
    have hdata : data = ⟨NumberTheory.Factorization.aggregatePrimeFactorList factors, 1⟩ := by
      exact Option.some.inj (by simpa only [partialFactorizationOfNMinusOne, hlist] using h.symm)
    subst data
    have hmono : nMinusOnePrimeFactors n params fuel' = some factors :=
      primeFactorListFuel_mono_depth hle hlist
    simp only [partialFactorizationOfNMinusOne, hmono]

/-- Increasing only the factor-supply depth preserves a completed square-certificate search and
the exact certificate returned; the base list and rho parameters stay fixed. -/
theorem findSquareCertificate_mono_factorFuel {n fuel fuel' : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {bases : List ℕ}
    {certificate : SquareCertificate} (hle : fuel ≤ fuel')
    (h : findSquareCertificate n params fuel bases = some certificate) :
    findSquareCertificate n params fuel' bases = some certificate := by
  unfold findSquareCertificate at h ⊢
  cases hdata : partialFactorizationOfNMinusOne n params fuel with
  | none =>
    simp only [hdata, Option.pure_def, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h
  | some data =>
    cases hwitnesses : findBLSWitnesses n data.factors bases with
    | none =>
      simp only [hdata, Option.pure_def, Option.bind_eq_bind, Option.bind_some, hwitnesses,
        Option.bind_none, reduceCtorEq] at h
    | some
      witnesses =>
      have hdata' : partialFactorizationOfNMinusOne n params fuel' = some data :=
        partialFactorizationOfNMinusOne_mono_fuel hle hdata
      simp only [hdata, hdata'] at h ⊢
      exact h

/-- If the complete factor tree for `n - 1` is covered, the exhaustive base search constructs a
square-root BLS certificate for prime `n ≥ 5`. -/
theorem exists_findSquareCertificate_of_coverage {n : ℕ} (hn : Nat.Prime n) (hn5 : 5 ≤ n)
    (params : NumberTheory.Factorization.PollardRho.Params) {fuel : ℕ}
    (hcoverage : RhoFactorTreeCoverage params fuel (n - 1)) :
    ∃ certificate, findSquareCertificate n params fuel (List.range n) = some certificate := by
  obtain ⟨factors, hfactors, _, _⟩ := primeFactorListFuel_of_coverage hcoverage
  let data : PartialFactorizationData :=
    ⟨NumberTheory.Factorization.aggregatePrimeFactorList factors, 1⟩
  have hdata : partialFactorizationOfNMinusOne n params fuel = some data := by
    simp only [partialFactorizationOfNMinusOne, nMinusOnePrimeFactors, hfactors, data]
  exact exists_findSquareCertificate_of_prime_factorSupply hn hn5 params fuel hdata

end PseudoPrime.PrimeTest.BLS
