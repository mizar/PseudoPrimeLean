/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.NumberTheory.PrimeIndexing
import PseudoPrime.NumberTheory.Fibonacci.Greatest
import PseudoPrime.NumberTheory.Fibonacci.Euclid
import PseudoPrime.NumberTheory.PrimeTable
import PseudoPrime.NumberTheory.PrimorialCertificates
import PseudoPrime.NumberTheory.JacobiCharacterCutoff
import PseudoPrime.NumberTheory.OddNonsquare
import PseudoPrime.NumberTheory.CharacterModulus
import PseudoPrime.NumberTheory.JacobiCharacter
import PseudoPrime.NumberTheory.JacobiCharacterArithmetic
import PseudoPrime.NumberTheory.JacobiCharacterPrimeEvaluation
import PseudoPrime.NumberTheory.PrimitiveJacobiCharacter
import PseudoPrime.NumberTheory.Jacobi.Basic
import PseudoPrime.NumberTheory.Jacobi.Prime
import PseudoPrime.NumberTheory.Factorization
import PseudoPrime.NumberTheory.Factorization.Basic
import PseudoPrime.NumberTheory.Factorization.PrimeLeafPolicy
import PseudoPrime.NumberTheory.Factorization.PollardRho.FactorSupply
import PseudoPrime.NumberTheory.Factorization.Partial
import PseudoPrime.NumberTheory.Factorization.PrimePowers
import PseudoPrime.NumberTheory.Factorization.PollardRho.Budget
import PseudoPrime.NumberTheory.Factorization.SmallInput
import PseudoPrime.NumberTheory.Factorization.PollardRho.Basic
import PseudoPrime.NumberTheory.Factorization.PollardRho.Orbit
import PseudoPrime.NumberTheory.Factorization.PollardRho.Search
import PseudoPrime.NumberTheory.JacobiCongruence
import PseudoPrime.NumberTheory.DirichletCharacter
import PseudoPrime.NumberTheory.Jacobi.Numerator
import PseudoPrime.NumberTheory.JacobiWitness.Basic
import PseudoPrime.NumberTheory.JacobiWitness.Existence
import PseudoPrime.NumberTheory.JacobiWitness.Smaller
import PseudoPrime.NumberTheory.MulCharParity

/-!
# General number theory umbrella

This module collects the Jacobi, factorization, and odd-nonsquare foundations
used by multiple developments.
-/
