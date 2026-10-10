/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.BLS.PartialFactorSupply
public import PseudoPrime.PrimeTest.BLS.Result
public import PseudoPrime.PrimeTest.BLS.CubeCertificate

/-!
# Bounded BLS certificate and composite searches
-/

@[expose] public section

namespace PseudoPrime.PrimeTest.BLS

/-- Build a square-root certificate from retained factors when factor supply, witness search, and
the verifier's size condition all succeed. The verifier is run before returning `some`. -/
def findSquareCertificateFromRetainedSupply (n : ℕ)
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ) :
    Option SquareCertificate :=
  match retainingPartialFactorizationOfNMinusOne n params fuel with
  | none => none
  | some data =>
    match findBLSWitnesses n data.factors bases with
    | none => none
    | some witnesses =>
      let certificate : SquareCertificate := ⟨n, data, witnesses⟩
      if verifySquareCertificate certificate then some certificate else none

/-- Any certificate returned from retained factors is accepted by the BLS verifier and proves
the embedded input prime. -/
theorem prime_of_findSquareCertificateFromRetainedSupply {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ} {bases : List ℕ}
    {certificate : SquareCertificate}
    (h : findSquareCertificateFromRetainedSupply n params fuel bases = some certificate) :
    Nat.Prime certificate.n := by
  unfold findSquareCertificateFromRetainedSupply at h
  cases hdata : retainingPartialFactorizationOfNMinusOne n params fuel with
  | none =>
    simp only [hdata] at h
    cases h
  | some data =>
    cases hwitnesses : findBLSWitnesses n data.factors bases with
    | none =>
      simp only [hdata, hwitnesses] at h
      cases h
    | some witnesses =>
      by_cases hverify : verifySquareCertificate ⟨n, data, witnesses⟩ = true
      · have hcertificate : (⟨n, data, witnesses⟩ : SquareCertificate) = certificate := by
          have hs : some (⟨n, data, witnesses⟩ : SquareCertificate) = some certificate := by
            simpa only [hdata, hwitnesses, hverify, ite_true] using h
          exact Option.some.inj hs
        rw [← hcertificate]
        exact prime_of_valid_square_certificate _ hverify
      · simp only [hdata, hwitnesses] at h
        rw [ite_eq_right hverify] at h
        cases h

/-- Valid retained factors, a sufficient square-root bound, and a base-list witness for every
factor key guarantee that the verified bounded certificate constructor succeeds. -/
theorem exists_findSquareCertificateFromRetainedSupply_of_coverage {n : ℕ} (hn5 : 5 ≤ n)
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ} {bases : List ℕ}
    {data : PartialFactorizationData}
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hbound : n < factorProduct data.factors ^ 2)
    (hcoverage : ∀ qe, qe ∈ data.factors → ∃ a, a ∈ bases ∧ IsBLSWitness n qe.1 a) :
    ∃ certificate,
      findSquareCertificateFromRetainedSupply n params fuel bases = some certificate := by
  have hsome : (findBLSWitnesses n data.factors bases).isSome = true :=
    (findBLSWitnesses_isSome_iff).mpr hcoverage
  cases hwitnesses : findBLSWitnesses n data.factors bases with
  | none =>
    rw [hwitnesses] at hsome
    exact False.elim (Bool.noConfusion hsome)
  | some
    witnesses =>
    have hfactor : ValidPartialFactorization n data :=
      retainingPartialFactorizationOfNMinusOne_sound hdata
    have hwitness : ValidWitnesses n data witnesses := by
      apply (checkWitnesses_eq_true_iff n data witnesses).mpr
      exact findBLSWitnesses_sound hwitnesses
    have hverify : verifySquareCertificate ⟨n, data, witnesses⟩ = true := by
      simp only [verifySquareCertificate, checkSquareCertificate, Bool.and_eq_true,
        decide_eq_true_eq]
      exact ⟨⟨⟨hn5, hbound⟩, hfactor⟩, hwitness⟩
    refine ⟨⟨n, data, witnesses⟩, ?_⟩
    simp only [findSquareCertificateFromRetainedSupply, hdata, hwitnesses, hverify]
    rfl

/-- Retain prime factors of `n - 1` using an explicit tree whose total rho-round budget is the
sum of its node allowances. -/
def retainingPartialFactorizationOfNMinusOneByTree (n : ℕ)
    (params : NumberTheory.Factorization.PollardRho.Params)
    (tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree) :
    Option PartialFactorizationData :=
  partialFactorizationDataOfSupply (partialPrimeFactorSupplyByTree params tree (n - 1))

/-- Every partial factorization returned by the explicit-budget supplier passes the BLS checker. -/
theorem retainingPartialFactorizationOfNMinusOneByTree_sound {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params}
    {tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree} {data : PartialFactorizationData}
    (h : retainingPartialFactorizationOfNMinusOneByTree n params tree = some data) :
    ValidPartialFactorization n data := by
  apply partialFactorizationDataOfSupply_sound
  · exact (partialPrimeFactorSupplyByTree_sound params tree (n - 1)).1
  · exact (partialPrimeFactorSupplyByTree_sound params tree (n - 1)).2
  · exact h

/-- Construct and verify a square-root BLS certificate using only the supplied budget tree. -/
def findSquareCertificateFromBudgetTree (n : ℕ)
    (params : NumberTheory.Factorization.PollardRho.Params)
    (tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree) (bases : List ℕ) :
    Option SquareCertificate :=
  match retainingPartialFactorizationOfNMinusOneByTree n params tree with
  | none => none
  | some data =>
    match findBLSWitnesses n data.factors bases with
    | none => none
    | some witnesses =>
      let certificate : SquareCertificate := ⟨n, data, witnesses⟩
      if verifySquareCertificate certificate then some certificate else none

/-- A certificate returned by the explicit-budget constructor is accepted and proves its input
prime. -/
theorem prime_of_findSquareCertificateFromBudgetTree {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params}
    {tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree} {bases : List ℕ}
    {certificate : SquareCertificate}
    (h : findSquareCertificateFromBudgetTree n params tree bases = some certificate) :
    Nat.Prime certificate.n := by
  unfold findSquareCertificateFromBudgetTree at h
  cases hdata : retainingPartialFactorizationOfNMinusOneByTree n params tree with
  | none =>
    simp only [hdata] at h
    cases h
  | some data =>
    cases hwitnesses : findBLSWitnesses n data.factors bases with
    | none =>
      simp only [hdata, hwitnesses] at h
      cases h
    | some witnesses =>
      by_cases hverify : verifySquareCertificate ⟨n, data, witnesses⟩ = true
      · have hcertificate : (⟨n, data, witnesses⟩ : SquareCertificate) = certificate := by
          have hs : some (⟨n, data, witnesses⟩ : SquareCertificate) = some certificate := by
            simpa only [hdata, hwitnesses, hverify, ite_true] using h
          exact Option.some.inj hs
        rw [← hcertificate]
        exact prime_of_valid_square_certificate _ hverify
      · simp only [hdata, hwitnesses] at h
        rw [ite_eq_right hverify] at h
        cases h

/-- Every certificate returned by the budget-tree constructor retains the constructor input. -/
theorem certificate_n_eq_input_of_findSquareCertificateFromBudgetTree {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params}
    {tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree} {bases : List ℕ}
    {certificate : SquareCertificate}
    (h : findSquareCertificateFromBudgetTree n params tree bases = some certificate) :
    certificate.n = n := by
  unfold findSquareCertificateFromBudgetTree at h
  cases hdata : retainingPartialFactorizationOfNMinusOneByTree n params tree with
  | none =>
    simp only [hdata] at h
    cases h
  | some data =>
    cases hwitnesses : findBLSWitnesses n data.factors bases with
    | none =>
      simp only [hdata, hwitnesses] at h
      cases h
    | some witnesses =>
      by_cases hverify : verifySquareCertificate ⟨n, data, witnesses⟩ = true
      · have hcertificate : (⟨n, data, witnesses⟩ : SquareCertificate) = certificate := by
          have hs : some (⟨n, data, witnesses⟩ : SquareCertificate) = some certificate := by
            simpa only [hdata, hwitnesses, hverify, ite_true] using h
          exact Option.some.inj hs
        rw [← hcertificate]
      · simp only [hdata, hwitnesses] at h
        rw [ite_eq_right hverify] at h
        cases h

/-- A successful budget-tree search returns a certificate whose cube-root criterion has the
branch-sensitive prime characterization. This carries the verified certificate result into the
alternative BLS arithmetic interface. -/
theorem prime_iff_cubeDiscriminantRootSearch_none_or_quotient_zero_of_budget_tree_search {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params}
    {tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree} {bases : List ℕ}
    {certificate : SquareCertificate}
    (h : findSquareCertificateFromBudgetTree n params tree bases = some certificate) :
    Nat.Prime certificate.n ↔
      cubeQuotient certificate.factorization.cofactor
            (factorProduct certificate.factorization.factors) =
          0 ∨
        findCubeDiscriminantSquareRoot certificate.factorization.cofactor
            (factorProduct certificate.factorization.factors) =
          none := by
  have hcheck : verifySquareCertificate certificate = true := by
    unfold findSquareCertificateFromBudgetTree at h
    cases hdata : retainingPartialFactorizationOfNMinusOneByTree n params tree with
    | none =>
      simp only [hdata] at h
      cases h
    | some data =>
      cases hwitnesses : findBLSWitnesses n data.factors bases with
      | none =>
        simp only [hdata, hwitnesses] at h
        cases h
      | some witnesses =>
        by_cases hverify : verifySquareCertificate ⟨n, data, witnesses⟩ = true
        · have hcertificate : (⟨n, data, witnesses⟩ : SquareCertificate) = certificate := by
            have hs : some (⟨n, data, witnesses⟩ : SquareCertificate) = some certificate := by
              simpa only [hdata, hwitnesses, hverify, ite_true] using h
            exact Option.some.inj hs
          rw [← hcertificate]
          exact hverify
        · simp only [hdata, hwitnesses] at h
          rw [ite_eq_right hverify] at h
          cases h
  exact
    prime_iff_cubeDiscriminantRootSearch_none_or_quotient_zero_of_valid_square_certificate
      certificate hcheck

/-- The budget-tree cube criterion characterizes the original input because every returned
certificate stores that input unchanged. -/
theorem prime_iff_cubeDiscriminantRootSearch_none_or_quotient_zero_of_budget_tree_search_input
    {n : ℕ} {params : NumberTheory.Factorization.PollardRho.Params}
    {tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree} {bases : List ℕ}
    {certificate : SquareCertificate}
    (h : findSquareCertificateFromBudgetTree n params tree bases = some certificate) :
    Nat.Prime n ↔
      cubeQuotient certificate.factorization.cofactor
            (factorProduct certificate.factorization.factors) =
          0 ∨
        findCubeDiscriminantSquareRoot certificate.factorization.cofactor
            (factorProduct certificate.factorization.factors) =
          none := by
  have hcriterion :=
    prime_iff_cubeDiscriminantRootSearch_none_or_quotient_zero_of_budget_tree_search h
  have hnumber := certificate_n_eq_input_of_findSquareCertificateFromBudgetTree h
  rw [hnumber] at hcriterion
  exact hcriterion

/-- A successful complete factor-supply search also exposes the branch-sensitive cube criterion.
The complete prime-power product is `n - 1`; for `n ≥ 5` this gives the cubic bound needed by
the cube-root characterization. -/
theorem prime_iff_cubeDiscriminantRootSearch_none_or_quotient_zero_of_findSquareCertificate {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {factorFuel : ℕ} {bases : List ℕ}
    {certificate : SquareCertificate} (hn5 : 5 ≤ n)
    (h : findSquareCertificate n params factorFuel bases = some certificate) :
    Nat.Prime certificate.n ↔
      cubeQuotient certificate.factorization.cofactor
            (factorProduct certificate.factorization.factors) =
          0 ∨
        findCubeDiscriminantSquareRoot certificate.factorization.cofactor
            (factorProduct certificate.factorization.factors) =
          none := by
  have hn2 : 2 < n := Nat.lt_of_lt_of_le (by decide : 2 < 5) hn5
  obtain ⟨hcn, hfull, hfactor, hwitnesses⟩ := findSquareCertificate_sound hn2 h
  have hn5c : 5 ≤ certificate.n := by
    rw [hcn]
    exact hn5
  have hbound : certificate.n < factorProduct certificate.factorization.factors ^ 2 := by
    rw [hcn, hfull]
    have hx : 3 < n - 1 := Nat.lt_sub_iff_add_lt.mpr (lt_of_lt_of_le (by decide : 4 < 5) hn5)
    have hpos : 0 < n - 1 := Nat.sub_pos_of_lt (lt_trans (by decide : 1 < 2) hn2)
    have hmul : 3 * (n - 1) < (n - 1) * (n - 1) := Nat.mul_lt_mul_of_pos_right hx hpos
    have hone : 1 ≤ n - 1 :=
      Nat.le_of_lt (Nat.lt_sub_iff_add_lt.mpr (lt_of_lt_of_le (by decide : 2 < 5) hn5))
    have hle : n ≤ 3 * (n - 1) := by
      calc
        n = (n - 1) + 1 := (Nat.sub_add_cancel (Nat.le_trans (by decide : 1 ≤ 5) hn5)).symm
        _ ≤ (n - 1) + (n - 1) := Nat.add_le_add_left hone (n - 1)
        _ = 2 * (n - 1) := (two_mul (n - 1)).symm
        _ ≤ 3 * (n - 1) := Nat.mul_le_mul_right (n - 1) (by decide : 2 ≤ 3)
    rw [pow_two]
    exact lt_of_le_of_lt hle hmul
  have hfactorc : ValidPartialFactorization certificate.n certificate.factorization := by
    change checkPartialFactorization certificate.n certificate.factorization = true
    rw [hcn]
    exact hfactor
  have hwitnessesc :
    ValidWitnesses certificate.n certificate.factorization certificate.witnesses := by
    change checkWitnesses certificate.n certificate.factorization certificate.witnesses = true
    rw [hcn]
    exact hwitnesses
  have hcheck : verifySquareCertificate certificate = true := by
    simp only [verifySquareCertificate, checkSquareCertificate, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hn5c, hbound⟩, hfactorc⟩, hwitnessesc⟩
  exact
    prime_iff_cubeDiscriminantRootSearch_none_or_quotient_zero_of_valid_square_certificate
      certificate hcheck

/-- The complete factor-supply constructor's cube criterion is a characterization of its input,
because its soundness theorem identifies the returned certificate's embedded number with `n`. -/
theorem prime_iff_cubeDiscriminantRootSearch_none_or_quotient_zero_of_findSquareCertificate_input
    {n : ℕ} {params : NumberTheory.Factorization.PollardRho.Params} {factorFuel : ℕ}
    {bases : List ℕ} {certificate : SquareCertificate} (hn5 : 5 ≤ n)
    (h : findSquareCertificate n params factorFuel bases = some certificate) :
    Nat.Prime n ↔
      cubeQuotient certificate.factorization.cofactor
            (factorProduct certificate.factorization.factors) =
          0 ∨
        findCubeDiscriminantSquareRoot certificate.factorization.cofactor
            (factorProduct certificate.factorization.factors) =
          none := by
  have hcriterion :=
    prime_iff_cubeDiscriminantRootSearch_none_or_quotient_zero_of_findSquareCertificate hn5 h
  have hn2 : 2 < n := Nat.lt_of_lt_of_le (by decide : 2 < 5) hn5
  obtain ⟨hcn, _, _, _⟩ := findSquareCertificate_sound hn2 h
  rw [hcn] at hcriterion
  exact hcriterion

/-- A successful complete factor-supply search with positive cube quotient and a found
discriminant square root certifies that the original input is composite. -/
theorem not_prime_of_findCubeDiscriminantSquareRoot_some_of_findSquareCertificate {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {factorFuel : ℕ} {bases : List ℕ}
    {certificate : SquareCertificate} (hn5 : 5 ≤ n)
    (h : findSquareCertificate n params factorFuel bases = some certificate)
    (hquotient :
      0 <
        cubeQuotient certificate.factorization.cofactor
          (factorProduct certificate.factorization.factors))
    {z : ℤ}
    (hroot :
      findCubeDiscriminantSquareRoot certificate.factorization.cofactor
          (factorProduct certificate.factorization.factors) =
        some z) :
    ¬Nat.Prime n := by
  intro hprime
  have hbranches :=
    (prime_iff_cubeDiscriminantRootSearch_none_or_quotient_zero_of_findSquareCertificate_input hn5
          h).mp
      hprime
  rcases hbranches with hzero | hnone
  · exact False.elim (Nat.ne_of_gt hquotient hzero)
  · rw [hroot] at hnone
    cases hnone

/-- The budget-tree constructor has the same composite conclusion when its cube-root search
finds a root and the corresponding quotient is positive. -/
theorem not_prime_of_findCubeDiscriminantSquareRoot_some_of_budget_tree_search {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params}
    {tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree} {bases : List ℕ}
    {certificate : SquareCertificate}
    (h : findSquareCertificateFromBudgetTree n params tree bases = some certificate)
    (hquotient :
      0 <
        cubeQuotient certificate.factorization.cofactor
          (factorProduct certificate.factorization.factors))
    {z : ℤ}
    (hroot :
      findCubeDiscriminantSquareRoot certificate.factorization.cofactor
          (factorProduct certificate.factorization.factors) =
        some z) :
    ¬Nat.Prime n := by
  intro hprime
  have hbranches :=
    (prime_iff_cubeDiscriminantRootSearch_none_or_quotient_zero_of_budget_tree_search_input h).mp
      hprime
  rcases hbranches with hzero | hnone
  · exact False.elim (Nat.ne_of_gt hquotient hzero)
  · rw [hroot] at hnone
    cases hnone

/-- Build a BLS certificate from one global rho-round allowance and a maximum split depth.
The balanced allocator makes the internal-node fuel sum stay within the supplied allowance. -/
def findSquareCertificateFromRoundBudget (n : ℕ)
    (params : NumberTheory.Factorization.PollardRho.Params) (maxDepth roundBudget : ℕ)
    (bases : List ℕ) : Option SquareCertificate :=
  findSquareCertificateFromBudgetTree n params
    (NumberTheory.Factorization.PollardRho.balancedRhoBudgetTree maxDepth roundBudget) bases

/-- Classify a BLS5 discriminant when the input decomposition and positive quotient are
already established. A square root yields a composite proof; an absent root stays unknown. -/
def bls5DiscriminantResult {n F R : ℕ} (hn : 1 < n) (hF : 0 < F) (hdecomp : n = F * R + 1)
    (hquotient : 0 < bls5Quotient R F) : BLSResult n :=
  match hroot : findBls5DiscriminantSquareRoot R F with
  | some z =>
    .composite
      (bls5NotPrime_of_positive_quotient_and_discriminant_square hn hF hdecomp hquotient z
        (findBls5DiscriminantSquareRoot_some_spec R F z hroot))
  | none => .unknown

/-- An absent BLS5 discriminant root leaves this partial classifier undecided. -/
theorem bls5DiscriminantResult_unknown_of_none {n F R : ℕ} (hn : 1 < n) (hF : 0 < F)
    (hdecomp : n = F * R + 1) (hquotient : 0 < bls5Quotient R F)
    (hroot : findBls5DiscriminantSquareRoot R F = none) :
    bls5DiscriminantResult hn hF hdecomp hquotient = .unknown := by
  unfold bls5DiscriminantResult
  split
  · rename_i z hfind
    rw [hroot] at hfind
    cases hfind
  · rfl

/-- A found discriminant root is carried by the composite branch of the common result type. -/
theorem bls5DiscriminantResult_composite_of_some {n F R : ℕ} (hn : 1 < n) (hF : 0 < F)
    (hdecomp : n = F * R + 1) (hquotient : 0 < bls5Quotient R F) {z : ℤ}
    (hroot : findBls5DiscriminantSquareRoot R F = some z) :
    ∃ hcomp : ¬Nat.Prime n, bls5DiscriminantResult hn hF hdecomp hquotient = .composite hcomp := by
  refine
    ⟨bls5NotPrime_of_positive_quotient_and_discriminant_square hn hF hdecomp hquotient z
        (findBls5DiscriminantSquareRoot_some_spec R F z hroot),
      ?_⟩
  unfold bls5DiscriminantResult
  split
  · rename_i z' hfind
    have heq : z' = z := Option.some.inj (hfind.symm.trans hroot)
    subst z'
    rfl
  · rename_i hfind
    rw [hroot] at hfind
    cases hfind

/-- With a valid positive-quotient decomposition, the discriminant classifier
returns a composite proof exactly when its finite square-root search succeeds.
This is the inverse specification of the composite branch. -/
theorem bls5DiscriminantResult_composite_iff_some {n F R : ℕ} (hn : 1 < n) (hF : 0 < F)
    (hdecomp : n = F * R + 1) (hquotient : 0 < bls5Quotient R F) :
    (∃ hcomp : ¬Nat.Prime n, bls5DiscriminantResult hn hF hdecomp hquotient = .composite hcomp) ↔
      ∃ z, findBls5DiscriminantSquareRoot R F = some z := by
  constructor
  · rintro ⟨hcomp, hresult⟩
    cases hroot : findBls5DiscriminantSquareRoot R F with
    | none =>
      have hunknown := bls5DiscriminantResult_unknown_of_none hn hF hdecomp hquotient hroot
      rw [hunknown] at hresult
      cases hresult
    | some z => exact ⟨z, rfl⟩
  · rintro ⟨z, hroot⟩
    exact bls5DiscriminantResult_composite_of_some hn hF hdecomp hquotient hroot

/-- With a valid positive-quotient decomposition, the discriminant classifier
is unknown exactly when its finite square-root search returns none. -/
theorem bls5DiscriminantResult_unknown_iff_none {n F R : ℕ} (hn : 1 < n) (hF : 0 < F)
    (hdecomp : n = F * R + 1) (hquotient : 0 < bls5Quotient R F) :
    bls5DiscriminantResult hn hF hdecomp hquotient = .unknown ↔
      findBls5DiscriminantSquareRoot R F = none := by
  constructor
  · intro hunknown
    cases hroot : findBls5DiscriminantSquareRoot R F with
    | none => rfl
    | some
      z =>
      obtain ⟨hcomp, hresult⟩ :=
        bls5DiscriminantResult_composite_of_some hn hF hdecomp hquotient hroot
      rw [hresult] at hunknown
      cases hunknown
  · exact bls5DiscriminantResult_unknown_of_none hn hF hdecomp hquotient

/-- Retained factor supply provides the decomposition and positive factor needed to turn a
found BLS5 discriminant root into a proof-carrying composite result. -/
theorem bls5DiscriminantResult_composite_of_retainedSupply {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ}
    {data : PartialFactorizationData} (hn : 1 < n)
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hquotient : 0 < bls5Quotient data.cofactor (factorProduct data.factors)) {z : ℤ}
    (hroot : findBls5DiscriminantSquareRoot data.cofactor (factorProduct data.factors) = some z) :
    ∃ (hF : 0 < factorProduct data.factors) (hdecomp :
      n = factorProduct data.factors * data.cofactor + 1) (hcomp : ¬Nat.Prime n),
      bls5DiscriminantResult hn hF hdecomp hquotient = .composite hcomp := by
  have hvalid := retainingPartialFactorizationOfNMinusOne_sound hdata
  have hspec := (checkPartialFactorization_eq_true_iff n data).mp hvalid
  have hF : 0 < factorProduct data.factors := Nat.zero_lt_of_lt hspec.1
  have hdecomp : n = factorProduct data.factors * data.cofactor + 1 := by
    calc
      n = n - 1 + 1 := (Nat.sub_add_cancel (Nat.le_of_lt hn)).symm
      _ = factorProduct data.factors * data.cofactor + 1 := by rw [hspec.2.1]
  obtain ⟨hcomp, hresult⟩ := bls5DiscriminantResult_composite_of_some hn hF hdecomp hquotient hroot
  exact ⟨hF, hdecomp, hcomp, hresult⟩

/-- Consume an optional cube-root certificate as a proof-carrying result. Inputs at most one
give `invalidInput`; above one, a matching accepted certificate gives `prime`, while missing,
mismatched, or rejected data gives `unknown`. -/
def boundedCubeResult (n : ℕ) (certificate : Option CubeCertificate) : BLSResult n :=
  if hinput : 1 < n then
    match certificate with
    | none => .unknown
    | some c =>
      if hmatch : c.n = n then
        if hcheck : checkCubeCertificate c = true then
          .prime (hmatch ▸ prime_of_valid_cube_certificate c hcheck)
        else .unknown
      else .unknown
  else .invalidInput (Nat.not_lt.mp hinput)

/-- An accepted matching cube-root certificate yields the prime result. -/
theorem boundedCubeResult_prime_case {n : ℕ} (certificate : CubeCertificate) (hinput : 1 < n)
    (hmatch : certificate.n = n) (hcheck : checkCubeCertificate certificate = true) :
    boundedCubeResult n (some certificate) =
      .prime (hmatch ▸ prime_of_valid_cube_certificate certificate hcheck) := by
  simp only [boundedCubeResult, dite_eq_left hinput, hmatch, hcheck, ↓reduceDIte]

/-- Search for cube-root data from retained factors of `n - 1` and finite witness bases.
The unresolved cofactor is permitted, and only a checker-accepted certificate is returned. -/
def findCubeCertificate (n : ℕ) (params : NumberTheory.Factorization.PollardRho.Params)
    (factorFuel : ℕ) (bases : List ℕ) : Option CubeCertificate :=
  match retainingPartialFactorizationOfNMinusOne n params factorFuel with
  | none => none
  | some data =>
    match findBLSWitnesses n data.factors bases with
    | none => none
    | some witnesses =>
      let certificate : CubeCertificate := ⟨n, data, witnesses⟩
      if checkCubeCertificate certificate then some certificate else none

/-- A returned cube-root certificate matches the input and passes its checker. -/
theorem findCubeCertificate_some_spec {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {factorFuel : ℕ} {bases : List ℕ}
    {certificate : CubeCertificate}
    (h : findCubeCertificate n params factorFuel bases = some certificate) :
    certificate.n = n ∧ checkCubeCertificate certificate = true := by
  unfold findCubeCertificate at h
  cases hdata : retainingPartialFactorizationOfNMinusOne n params factorFuel with
  | none => simp only [hdata, reduceCtorEq] at h
  | some data =>
    cases hwitness : findBLSWitnesses n data.factors bases with
    | none => simp only [hdata, hwitness, reduceCtorEq] at h
    | some witnesses =>
      simp only [hdata, hwitness] at h
      split at h
      · rename_i hvalid
        have heq := Option.some.inj h
        cases heq
        exact ⟨rfl, hvalid⟩
      · simp only [reduceCtorEq] at h

/-- Retained factors, a cube bound, an accepting arithmetic branch, and a witness in the
finite base list for each factor key guarantee that the bounded cube constructor succeeds. -/
theorem exists_findCubeCertificate_of_coverage {n : ℕ} (hn : 1 < n)
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ} {bases : List ℕ}
    {data : PartialFactorizationData}
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hbound : n < factorProduct data.factors ^ 3)
    (harithmetic :
      cubeQuotient data.cofactor (factorProduct data.factors) = 0 ∨
        cubeDiscriminantIsSquare data.cofactor (factorProduct data.factors) = false)
    (hcoverage : ∀ qe, qe ∈ data.factors → ∃ a, a ∈ bases ∧ IsBLSWitness n qe.1 a) :
    ∃ certificate, findCubeCertificate n params fuel bases = some certificate := by
  have hsome : (findBLSWitnesses n data.factors bases).isSome = true :=
    (findBLSWitnesses_isSome_iff).mpr hcoverage
  cases hwitnesses : findBLSWitnesses n data.factors bases with
  | none =>
    rw [hwitnesses] at hsome
    exact False.elim (Bool.noConfusion hsome)
  | some
    witnesses =>
    have hfactor : ValidPartialFactorization n data :=
      retainingPartialFactorizationOfNMinusOne_sound hdata
    have hdecomp : n = factorProduct data.factors * data.cofactor + 1 := by
      calc
        n = n - 1 + 1 := (Nat.sub_add_cancel (Nat.le_of_lt hn)).symm
        _ = factorProduct data.factors * data.cofactor + 1 := by
          rw [((checkPartialFactorization_eq_true_iff n data).mp hfactor).2.1]
    have hwitness : ValidWitnesses n data witnesses := by
      apply (checkWitnesses_eq_true_iff n data witnesses).mpr
      exact findBLSWitnesses_sound hwitnesses
    have hcheck : checkCubeCertificate ⟨n, data, witnesses⟩ = true := by
      exact
        (checkCubeCertificate_eq_true_iff _).mpr
          ⟨hn, hdecomp, hbound, hfactor, hwitness, harithmetic⟩
    refine ⟨⟨n, data, witnesses⟩, ?_⟩
    simp only [findCubeCertificate, hdata, hwitnesses, hcheck, ite_true]

/-- Reject out-of-range inputs first, then consume the bounded cube-root certificate search. -/
def boundedCubeSearch (n : ℕ) (params : NumberTheory.Factorization.PollardRho.Params)
    (factorFuel : ℕ) (bases : List ℕ) : BLSResult n :=
  if hinput : 1 < n then boundedCubeResult n (findCubeCertificate n params factorFuel bases)
  else .invalidInput (Nat.not_lt.mp hinput)

/-- A successful cube-root search returns a proof of primality for the original input. -/
theorem boundedCubeSearch_prime_case {n : ℕ} (params : NumberTheory.Factorization.PollardRho.Params)
    (factorFuel : ℕ) (bases : List ℕ) {certificate : CubeCertificate} (hinput : 1 < n)
    (hcertificate : findCubeCertificate n params factorFuel bases = some certificate) :
    boundedCubeSearch n params factorFuel bases =
      .prime
        ((findCubeCertificate_some_spec hcertificate).1 ▸
          prime_of_valid_cube_certificate certificate
            (findCubeCertificate_some_spec hcertificate).2) := by
  unfold boundedCubeSearch
  rw [dite_eq_left hinput, hcertificate]
  exact
    boundedCubeResult_prime_case certificate hinput (findCubeCertificate_some_spec hcertificate).1
      (findCubeCertificate_some_spec hcertificate).2

/-- Certificate search failure carries no assertion about primality. -/
theorem boundedCubeSearch_unknown_of_none {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (factorFuel : ℕ) (bases : List ℕ)
    (hinput : 1 < n) (hnone : findCubeCertificate n params factorFuel bases = none) :
    boundedCubeSearch n params factorFuel bases = .unknown := by
  unfold boundedCubeSearch boundedCubeResult
  simp only [dite_eq_left hinput, hnone]

/-- Out-of-range input is rejected before factor or witness search. -/
theorem boundedCubeSearch_invalidInput {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (factorFuel : ℕ) (bases : List ℕ)
    (hn : n ≤ 1) : boundedCubeSearch n params factorFuel bases = .invalidInput hn := by
  unfold boundedCubeSearch
  rw [dite_eq_right (Nat.not_lt.mpr hn)]

/-- Every result of the bounded cube-root search has the meaning stated by `BLSResult.sound`.
The prime branch carries a checked certificate; the other branches retain their stated scope. -/
theorem boundedCubeSearch_sound (n : ℕ) (params : NumberTheory.Factorization.PollardRho.Params)
    (factorFuel : ℕ) (bases : List ℕ) : (boundedCubeSearch n params factorFuel bases).sound :=
  BLSResult.sound_proof (boundedCubeSearch n params factorFuel bases)

/-- Under the explicit factor, arithmetic, and base-list coverage hypotheses, the bounded
cube search reaches the proof-carrying prime branch for its original input. -/
theorem exists_boundedCubeSearch_prime_of_coverage {n : ℕ} (hn : 1 < n)
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ} {bases : List ℕ}
    {data : PartialFactorizationData}
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hbound : n < factorProduct data.factors ^ 3)
    (harithmetic :
      cubeQuotient data.cofactor (factorProduct data.factors) = 0 ∨
        cubeDiscriminantIsSquare data.cofactor (factorProduct data.factors) = false)
    (hcoverage : ∀ qe, qe ∈ data.factors → ∃ a, a ∈ bases ∧ IsBLSWitness n qe.1 a) :
    ∃ hprime : Nat.Prime n, boundedCubeSearch n params fuel bases = .prime hprime := by
  obtain ⟨certificate, hcert⟩ :=
    exists_findCubeCertificate_of_coverage hn hdata hbound harithmetic hcoverage
  have hspec := findCubeCertificate_some_spec hcert
  let hprime : Nat.Prime n := hspec.1 ▸ prime_of_valid_cube_certificate certificate hspec.2
  exact ⟨hprime, boundedCubeSearch_prime_case params fuel bases hn hcert⟩

/-- Consume an optional BLS5 certificate through the shared result type. Inputs at most one
give `invalidInput`; above one, a matching accepted certificate proves primality, while missing,
mismatched, or rejected data returns `unknown`. -/
def boundedBLS5Result (n : ℕ) (certificate : Option BLS5Certificate) : BLSResult n :=
  if hinput : 1 < n then
    match certificate with
    | none => .unknown
    | some c =>
      if hmatch : c.n = n then
        if hcheck : checkBLS5Certificate c = true then
          .prime (hmatch ▸ prime_of_valid_bls5_certificate c hcheck)
        else .unknown
      else .unknown
  else .invalidInput (Nat.not_lt.mp hinput)

/-- A matching accepted BLS5 certificate is returned as the prime branch of `BLSResult`. -/
theorem boundedBLS5Result_prime_case {n : ℕ} (certificate : BLS5Certificate) (hinput : 1 < n)
    (hmatch : certificate.n = n) (hcheck : checkBLS5Certificate certificate = true) :
    boundedBLS5Result n (some certificate) =
      .prime (hmatch ▸ prime_of_valid_bls5_certificate certificate hcheck) := by
  simp only [boundedBLS5Result, dite_eq_left hinput, hmatch, hcheck, ↓reduceDIte]

/-- Every result obtained by consuming an optional BLS5 certificate has the
proof-carrying meaning specified by `BLSResult.sound`. -/
theorem boundedBLS5Result_sound (n : ℕ) (certificate : Option BLS5Certificate) :
    (boundedBLS5Result n certificate).sound := by
  exact BLSResult.sound_proof (boundedBLS5Result n certificate)

/-- Assemble a BLS5 certificate from already computed partial data, rechecking every condition. -/
def findBLS5CertificateFromSupply (n : ℕ) (supply : Option PartialFactorizationData)
    (bases : List ℕ) : Option BLS5Certificate :=
  match supply with
  | none => none
  | some data =>
    match findBLSWitnesses n data.factors bases with
    | none => none
    | some witnesses =>
      let certificate : BLS5Certificate := ⟨n, data, witnesses, data.cofactor⟩
      if checkBLS5Certificate certificate then some certificate else none

/-- Attempt to assemble a BLS5 certificate from bounded `n - 1` factor supply and the supplied
finite list of witness bases. Arithmetic or certificate-check failure returns `none`. -/
def findBLS5Certificate (n : ℕ) (params : NumberTheory.Factorization.PollardRho.Params)
    (factorFuel : ℕ) (bases : List ℕ) : Option BLS5Certificate :=
  findBLS5CertificateFromSupply n (retainingPartialFactorizationOfNMinusOne n params factorFuel)
    bases

/-- A returned BLS5 certificate embeds the requested input and passes its executable checker. -/
theorem findBLS5Certificate_some_spec {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {factorFuel : ℕ} {bases : List ℕ}
    {certificate : BLS5Certificate}
    (h : findBLS5Certificate n params factorFuel bases = some certificate) :
    certificate.n = n ∧ checkBLS5Certificate certificate = true := by
  unfold findBLS5Certificate findBLS5CertificateFromSupply at h
  cases hdata : retainingPartialFactorizationOfNMinusOne n params factorFuel with
  | none => simp only [hdata, reduceCtorEq] at h
  | some data =>
    cases hwitness : findBLSWitnesses n data.factors bases with
    | none => simp only [hdata, hwitness, reduceCtorEq] at h
    | some witnesses =>
      simp only [hdata, hwitness] at h
      split at h
      · rename_i hvalid
        have heq := Option.some.inj h
        cases heq
        exact ⟨rfl, hvalid⟩
      · simp only [reduceCtorEq] at h

/-- A composite input cannot produce a BLS5 certificate accepted by the bounded search. -/
theorem findBLS5Certificate_eq_none_of_not_prime {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ)
    (hcomp : ¬Nat.Prime n) : findBLS5Certificate n params fuel bases = none := by
  cases hcert : findBLS5Certificate n params fuel bases with
  | none => rfl
  | some certificate =>
    have hspec := findBLS5Certificate_some_spec hcert
    have hprime : Nat.Prime n := hspec.1 ▸ prime_of_valid_bls5_certificate certificate hspec.2
    exact False.elim (hcomp hprime)

/-- Any successful finite BLS5 certificate search satisfies the arithmetic
criterion for the retained factor data actually returned by factor supply.
This is the necessary direction of the search specification. -/
theorem findBLS5Certificate_some_arithmetic {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ} {bases : List ℕ}
    {data : PartialFactorizationData} {certificate : BLS5Certificate}
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hcert : findBLS5Certificate n params fuel bases = some certificate) :
    bls5PassesArithmeticCriterion data.cofactor (factorProduct data.factors) = true := by
  unfold findBLS5Certificate findBLS5CertificateFromSupply at hcert
  rw [hdata] at hcert
  cases hwitnesses : findBLSWitnesses n data.factors bases with
  | none => simp only [hwitnesses, reduceCtorEq] at hcert
  | some witnesses =>
    simp only [hwitnesses] at hcert
    split at hcert
    · rename_i hcheck
      rcases (checkBLS5Certificate_eq_true_iff _).mp hcheck with
        ⟨_, _, _, _, _, _, _, _, harithmetic⟩
      exact harithmetic
    · simp only [reduceCtorEq] at hcert

/-- Retained factors, the BLS5 arithmetic hypotheses, and a witness in the finite base list
for each factor key guarantee that the bounded certificate constructor succeeds. -/
theorem exists_findBLS5Certificate_of_coverage {n : ℕ} (hn5 : 5 ≤ n)
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ} {bases : List ℕ}
    {data : PartialFactorizationData}
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hEven : Even (factorProduct data.factors))
    (hcop : Nat.Coprime (factorProduct data.factors) data.cofactor)
    (hbound :
      n <
        (factorProduct data.factors + 1) *
          (2 * factorProduct data.factors ^ 2 +
            (data.cofactor % (2 * factorProduct data.factors) - 1) * factorProduct data.factors +
            1))
    (harithmetic : bls5PassesArithmeticCriterion data.cofactor (factorProduct data.factors) = true)
    (hcoverage : ∀ qe, qe ∈ data.factors → ∃ a, a ∈ bases ∧ IsBLSWitness n qe.1 a) :
    ∃ certificate, findBLS5Certificate n params fuel bases = some certificate := by
  have hsome : (findBLSWitnesses n data.factors bases).isSome = true :=
    (findBLSWitnesses_isSome_iff).mpr hcoverage
  cases hwitnesses : findBLSWitnesses n data.factors bases with
  | none =>
    rw [hwitnesses] at hsome
    exact False.elim (Bool.noConfusion hsome)
  | some
    witnesses =>
    have hfactor : ValidPartialFactorization n data :=
      retainingPartialFactorizationOfNMinusOne_sound hdata
    have hn : 1 < n := lt_of_lt_of_le (by decide : 1 < 5) hn5
    have hdecomp : n = factorProduct data.factors * data.cofactor + 1 := by
      calc
        n = n - 1 + 1 := (Nat.sub_add_cancel (Nat.le_of_lt hn)).symm
        _ = factorProduct data.factors * data.cofactor + 1 := by
          rw [((checkPartialFactorization_eq_true_iff n data).mp hfactor).2.1]
    have hwitness : ValidWitnesses n data witnesses := by
      apply (checkWitnesses_eq_true_iff n data witnesses).mpr
      exact findBLSWitnesses_sound hwitnesses
    have hcheck : checkBLS5Certificate ⟨n, data, witnesses, data.cofactor⟩ = true := by
      exact
        (checkBLS5Certificate_eq_true_iff _).mpr
          ⟨hn5, rfl, hdecomp, hEven, hcop, hbound, hfactor, hwitness, harithmetic⟩
    refine ⟨⟨n, data, witnesses, data.cofactor⟩, ?_⟩
    simp only [findBLS5Certificate, findBLS5CertificateFromSupply, hdata, hwitnesses, hcheck,
      ite_true]

/-- Under retained factor supply, BLS5 size and parity data, and explicit
witness-base coverage, finite certificate discovery is equivalent to the
executable arithmetic criterion for the retained cofactor. -/
theorem findBLS5Certificate_some_iff_arithmetic_of_coverage {n : ℕ} (hn5 : 5 ≤ n)
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ} {bases : List ℕ}
    {data : PartialFactorizationData}
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hEven : Even (factorProduct data.factors))
    (hcop : Nat.Coprime (factorProduct data.factors) data.cofactor)
    (hbound :
      n <
        (factorProduct data.factors + 1) *
          (2 * factorProduct data.factors ^ 2 +
            (data.cofactor % (2 * factorProduct data.factors) - 1) * factorProduct data.factors +
            1))
    (hcoverage : ∀ qe, qe ∈ data.factors → ∃ a, a ∈ bases ∧ IsBLSWitness n qe.1 a) :
    (∃ certificate, findBLS5Certificate n params fuel bases = some certificate) ↔
      bls5PassesArithmeticCriterion data.cofactor (factorProduct data.factors) = true := by
  constructor
  · rintro ⟨certificate, hcert⟩
    exact findBLS5Certificate_some_arithmetic hdata hcert
  · intro harithmetic
    exact exists_findBLS5Certificate_of_coverage hn5 hdata hEven hcop hbound harithmetic hcoverage

/-- Retained factor data and a finite witness for each factor key provide the
divisor restriction required by the BLS5 arithmetic equivalence. Under the
explicit parity, coprimality, and size hypotheses, arithmetic acceptance is
equivalent to primality of the original input. -/
theorem prime_iff_bls5Arithmetic_of_supply_coverage {n : ℕ} (hn5 : 5 ≤ n)
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ} {bases : List ℕ}
    {data : PartialFactorizationData}
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hEven : Even (factorProduct data.factors))
    (hcop : Nat.Coprime (factorProduct data.factors) data.cofactor)
    (hbound :
      n <
        (factorProduct data.factors + 1) *
          (2 * factorProduct data.factors ^ 2 +
            (data.cofactor % (2 * factorProduct data.factors) - 1) * factorProduct data.factors +
            1))
    (hcoverage : ∀ qe, qe ∈ data.factors → ∃ a, a ∈ bases ∧ IsBLSWitness n qe.1 a) :
    Nat.Prime n ↔
      bls5PassesArithmeticCriterion data.cofactor (factorProduct data.factors) = true := by
  have hn : 1 < n := lt_of_lt_of_le (by decide : 1 < 5) hn5
  have hfactor : ValidPartialFactorization n data :=
    retainingPartialFactorizationOfNMinusOne_sound hdata
  have hspec := (checkPartialFactorization_eq_true_iff n data).mp hfactor
  have hFpos : 0 < factorProduct data.factors := Nat.zero_lt_of_lt hspec.1
  have hdecomp : n = factorProduct data.factors * data.cofactor + 1 := by
    calc
      n = n - 1 + 1 := (Nat.sub_add_cancel (Nat.le_of_lt hn)).symm
      _ = factorProduct data.factors * data.cofactor + 1 := by rw [hspec.2.1]
  have hwitSome : (findBLSWitnesses n data.factors bases).isSome = true :=
    (findBLSWitnesses_isSome_iff).mpr hcoverage
  obtain ⟨witnesses, hwitnesses⟩ := Option.isSome_iff_exists.mp hwitSome
  have hwitness : ValidWitnesses n data witnesses := by
    apply (checkWitnesses_eq_true_iff n data witnesses).mpr
    exact findBLSWitnesses_sound hwitnesses
  have hlarge := primeDivisorsAbove_of_valid_bls_data hn data witnesses hfactor hwitness
  exact bls5_prime_iff_passesArithmeticCriterion hEven hFpos hn hcop hdecomp hbound hlarge

/-- Classify an optional partial factorization using its supplied validity proof. Inputs at most
one give `invalidInput`. For valid input, a positive BLS5 quotient and square discriminant give
`composite`; missing data, zero quotient, or nonsquare discriminant give `unknown`.
The decomposition extracted from validity justifies the composite proof without witness bases. -/
def bls5DiscriminantResultFromSupply (n : ℕ) (supply : Option PartialFactorizationData)
    (valid : ∀ data, supply = some data → ValidPartialFactorization n data) : BLSResult n :=
  if hinput : 1 < n then
    match (generalizing := false) hdata : supply with
    | none => .unknown
    | some data =>
      have hvalid := valid data hdata
      have hspec := (checkPartialFactorization_eq_true_iff n data).mp hvalid
      have hF : 0 < factorProduct data.factors := Nat.zero_lt_of_lt hspec.1
      have hdecomp : n = factorProduct data.factors * data.cofactor + 1 := by
        calc
          n = n - 1 + 1 := (Nat.sub_add_cancel (Nat.le_of_lt hinput)).symm
          _ = factorProduct data.factors * data.cofactor + 1 := by rw [hspec.2.1]
      if hq : 0 < bls5Quotient data.cofactor (factorProduct data.factors) then
        bls5DiscriminantResult hinput hF hdecomp hq
      else .unknown
  else .invalidInput (Nat.not_lt.mp hinput)

/-- Recheck retained factor data for a positive BLS5 quotient. A square discriminant gives
a composite result; missing data, a zero quotient, or a nonsquare leaves this search unknown. -/
def bls5DiscriminantResultFromRetainedSupply (n : ℕ)
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) : BLSResult n :=
  bls5DiscriminantResultFromSupply n (retainingPartialFactorizationOfNMinusOne n params fuel)
    (fun _ h ↦ retainingPartialFactorizationOfNMinusOne_sound h)

/-- Retained factors and a found square discriminant reach the common composite result. -/
theorem bls5DiscriminantResultFromRetainedSupply_composite_of_some {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ}
    {data : PartialFactorizationData} (hinput : 1 < n)
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hq : 0 < bls5Quotient data.cofactor (factorProduct data.factors)) {z : ℤ}
    (hroot : findBls5DiscriminantSquareRoot data.cofactor (factorProduct data.factors) = some z) :
    ∃ hcomp : ¬Nat.Prime n,
      bls5DiscriminantResultFromRetainedSupply n params fuel = .composite hcomp := by
  unfold bls5DiscriminantResultFromRetainedSupply bls5DiscriminantResultFromSupply
  rw [dite_eq_left hinput]
  split
  · rename_i hnone
    rw [hdata] at hnone
    cases hnone
  · rename_i data' hdata'
    have heq : data' = data := Option.some.inj (hdata'.symm.trans hdata)
    subst data'
    split
    · rename_i hq'
      exact bls5DiscriminantResult_composite_of_some _ _ _ _ hroot
    · rename_i hnot
      exact False.elim (hnot hq)

/-- With no retained factor data, the discriminant search has no justified conclusion. -/
theorem bls5DiscriminantResultFromRetainedSupply_unknown_of_none {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ} (hinput : 1 < n)
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = none) :
    bls5DiscriminantResultFromRetainedSupply n params fuel = .unknown := by
  unfold bls5DiscriminantResultFromRetainedSupply bls5DiscriminantResultFromSupply
  rw [dite_eq_left hinput]
  split
  · rfl
  · rename_i data hsome
    rw [hdata] at hsome
    cases hsome

/-- Retained factors with zero BLS5 quotient leave the discriminant classifier unknown. -/
theorem bls5DiscriminantResultFromRetainedSupply_unknown_of_zero {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ}
    {data : PartialFactorizationData} (hinput : 1 < n)
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hzero : bls5Quotient data.cofactor (factorProduct data.factors) = 0) :
    bls5DiscriminantResultFromRetainedSupply n params fuel = .unknown := by
  unfold bls5DiscriminantResultFromRetainedSupply bls5DiscriminantResultFromSupply
  rw [dite_eq_left hinput]
  split
  · rename_i hnone
    rw [hdata] at hnone
  · rename_i data' hdata'
    have heq : data' = data := Option.some.inj (hdata'.symm.trans hdata)
    subst data'
    split
    · rename_i hq
      rw [hzero] at hq
      exact False.elim (Nat.lt_irrefl 0 hq)
    · rfl

/-- A positive quotient without an integer square root of the BLS5 discriminant
also leaves the retained-factor classifier unknown. -/
theorem bls5DiscriminantResultFromRetainedSupply_unknown_of_root_none {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ}
    {data : PartialFactorizationData} (hinput : 1 < n)
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hq : 0 < bls5Quotient data.cofactor (factorProduct data.factors))
    (hroot : findBls5DiscriminantSquareRoot data.cofactor (factorProduct data.factors) = none) :
    bls5DiscriminantResultFromRetainedSupply n params fuel = .unknown := by
  unfold bls5DiscriminantResultFromRetainedSupply bls5DiscriminantResultFromSupply
  rw [dite_eq_left hinput]
  split
  · rename_i hnone
    rw [hdata] at hnone
  · rename_i data' hdata'
    have heq : data' = data := Option.some.inj (hdata'.symm.trans hdata)
    subst data'
    split
    · rename_i hq'
      exact bls5DiscriminantResult_unknown_of_none _ _ _ _ hroot
    · rename_i hnot
      exact False.elim (hnot hq)

/-- Given retained factors and a positive BLS5 quotient, the fallback proves
compositeness exactly when its finite discriminant square-root search succeeds.
The retained decomposition supplies the arithmetic hypotheses of the classifier. -/
theorem bls5DiscriminantResultFromRetainedSupply_composite_iff_some {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ}
    {data : PartialFactorizationData} (hinput : 1 < n)
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hq : 0 < bls5Quotient data.cofactor (factorProduct data.factors)) :
    (∃ hcomp : ¬Nat.Prime n,
        bls5DiscriminantResultFromRetainedSupply n params fuel = .composite hcomp) ↔
      ∃ z, findBls5DiscriminantSquareRoot data.cofactor (factorProduct data.factors) = some z := by
  unfold bls5DiscriminantResultFromRetainedSupply bls5DiscriminantResultFromSupply
  rw [dite_eq_left hinput]
  split
  · rename_i hnone
    rw [hdata] at hnone
    cases hnone
  · rename_i data' hdata'
    have heq : data' = data := Option.some.inj (hdata'.symm.trans hdata)
    subst data'
    split
    · rename_i hq'
      exact bls5DiscriminantResult_composite_iff_some _ _ _ _
    · rename_i hnot
      exact False.elim (hnot hq)

/-- Given retained factors and a positive BLS5 quotient, the fallback is
unknown exactly when the finite discriminant square-root search fails. -/
theorem bls5DiscriminantResultFromRetainedSupply_unknown_iff_none {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ}
    {data : PartialFactorizationData} (hinput : 1 < n)
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hq : 0 < bls5Quotient data.cofactor (factorProduct data.factors)) :
    bls5DiscriminantResultFromRetainedSupply n params fuel = .unknown ↔
      findBls5DiscriminantSquareRoot data.cofactor (factorProduct data.factors) = none := by
  unfold bls5DiscriminantResultFromRetainedSupply bls5DiscriminantResultFromSupply
  rw [dite_eq_left hinput]
  split
  · rename_i hnone
    rw [hdata] at hnone
    cases hnone
  · rename_i data' hdata'
    have heq : data' = data := Option.some.inj (hdata'.symm.trans hdata)
    subst data'
    split
    · rename_i hq'
      exact bls5DiscriminantResult_unknown_iff_none _ _ _ _
    · rename_i hnot
      exact False.elim (hnot hq)

/-- Reject inputs at most one before constructing a bounded BLS5 certificate; valid inputs
pass the certificate search result to the shared result type. -/
def boundedBLS5Search (n : ℕ) (params : NumberTheory.Factorization.PollardRho.Params)
    (factorFuel : ℕ) (bases : List ℕ) : BLSResult n :=
  if hinput : 1 < n then boundedBLS5Result n (findBLS5Certificate n params factorFuel bases)
  else .invalidInput (Nat.not_lt.mp hinput)

/-- A successful BLS5 factor-and-witness search returns its proof-carrying prime branch. -/
theorem boundedBLS5Search_prime_case {n : ℕ} (params : NumberTheory.Factorization.PollardRho.Params)
    (factorFuel : ℕ) (bases : List ℕ) {certificate : BLS5Certificate} (hinput : 1 < n)
    (hcertificate : findBLS5Certificate n params factorFuel bases = some certificate) :
    boundedBLS5Search n params factorFuel bases =
      .prime
        ((findBLS5Certificate_some_spec hcertificate).1 ▸
          prime_of_valid_bls5_certificate certificate
            (findBLS5Certificate_some_spec hcertificate).2) := by
  unfold boundedBLS5Search
  rw [dite_eq_left hinput, hcertificate]
  exact
    boundedBLS5Result_prime_case certificate hinput (findBLS5Certificate_some_spec hcertificate).1
      (findBLS5Certificate_some_spec hcertificate).2

/-- For an in-range input, the bounded BLS5 result is prime exactly when its
finite factor-and-witness search returns a checked certificate. -/
theorem boundedBLS5Search_prime_iff_certificate {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ)
    (hinput : 1 < n) :
    (∃ hprime : Nat.Prime n, boundedBLS5Search n params fuel bases = .prime hprime) ↔
      ∃ certificate, findBLS5Certificate n params fuel bases = some certificate := by
  constructor
  · rintro ⟨hprime, hresult⟩
    unfold boundedBLS5Search at hresult
    rw [dite_eq_left hinput] at hresult
    cases hcert : findBLS5Certificate n params fuel bases with
    | none =>
      simp only [boundedBLS5Result, dite_eq_left hinput, hcert] at hresult
      cases hresult
    | some certificate => exact ⟨certificate, rfl⟩
  · rintro ⟨certificate, hcert⟩
    have hspec := findBLS5Certificate_some_spec hcert
    let hprime : Nat.Prime n := hspec.1 ▸ prime_of_valid_bls5_certificate certificate hspec.2
    exact ⟨hprime, boundedBLS5Search_prime_case params fuel bases hinput hcert⟩

/-- Under explicit factor, arithmetic, and base-list coverage hypotheses, the bounded BLS5
search reaches its proof-carrying prime branch for the original input. -/
theorem exists_boundedBLS5Search_prime_of_coverage {n : ℕ} (hn5 : 5 ≤ n)
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ} {bases : List ℕ}
    {data : PartialFactorizationData}
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hEven : Even (factorProduct data.factors))
    (hcop : Nat.Coprime (factorProduct data.factors) data.cofactor)
    (hbound :
      n <
        (factorProduct data.factors + 1) *
          (2 * factorProduct data.factors ^ 2 +
            (data.cofactor % (2 * factorProduct data.factors) - 1) * factorProduct data.factors +
            1))
    (harithmetic : bls5PassesArithmeticCriterion data.cofactor (factorProduct data.factors) = true)
    (hcoverage : ∀ qe, qe ∈ data.factors → ∃ a, a ∈ bases ∧ IsBLSWitness n qe.1 a) :
    ∃ hprime : Nat.Prime n, boundedBLS5Search n params fuel bases = .prime hprime := by
  obtain ⟨certificate, hcert⟩ :=
    exists_findBLS5Certificate_of_coverage hn5 hdata hEven hcop hbound harithmetic hcoverage
  exact
    (boundedBLS5Search_prime_iff_certificate params fuel bases
          (lt_of_lt_of_le (by decide : 1 < 5) hn5)).mpr
      ⟨certificate, hcert⟩

/-- Exhausting the BLS5 certificate search returns `unknown`, with no compositeness claim. -/
theorem boundedBLS5Search_unknown_of_none {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (factorFuel : ℕ) (bases : List ℕ)
    (hinput : 1 < n) (hnone : findBLS5Certificate n params factorFuel bases = none) :
    boundedBLS5Search n params factorFuel bases = .unknown := by
  unfold boundedBLS5Search boundedBLS5Result
  simp only [dite_eq_left hinput, hnone]

/-- On an in-range input, `unknown` is exactly exhaustion of the finite BLS5
certificate search. A returned certificate cannot enter the unknown branch. -/
theorem boundedBLS5Search_unknown_iff_none {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ)
    (hinput : 1 < n) :
    boundedBLS5Search n params fuel bases = .unknown ↔
      findBLS5Certificate n params fuel bases = none := by
  constructor
  · intro hunknown
    cases hcert : findBLS5Certificate n params fuel bases with
    | none => rfl
    | some
      certificate =>
      have hprime := boundedBLS5Search_prime_case params fuel bases hinput hcert
      rw [hprime] at hunknown
      cases hunknown
  · exact boundedBLS5Search_unknown_of_none params fuel bases hinput

/-- An out-of-range input is rejected independently of factor fuel and witness bases. -/
theorem boundedBLS5Search_invalidInput {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (factorFuel : ℕ) (bases : List ℕ)
    (hn : n ≤ 1) : boundedBLS5Search n params factorFuel bases = .invalidInput hn := by
  unfold boundedBLS5Search
  rw [dite_eq_right (Nat.not_lt.mpr hn)]

/-- Every bounded BLS5 search result satisfies the shared result contract,
including its prime, unknown, and invalid-input branches. -/
theorem boundedBLS5Search_sound (n : ℕ) (params : NumberTheory.Factorization.PollardRho.Params)
    (fuel : ℕ) (bases : List ℕ) : (boundedBLS5Search n params fuel bases).sound := by
  exact BLSResult.sound_proof (boundedBLS5Search n params fuel bases)

/-- Search first for a checked BLS5 prime certificate, then use retained factors to detect
a positive-quotient square discriminant. Exhaustion without either proof remains unknown. -/
def boundedBLS5SearchWithComposite (n : ℕ) (params : NumberTheory.Factorization.PollardRho.Params)
    (fuel : ℕ) (bases : List ℕ) : BLSResult n :=
  if hinput : 1 < n then
    let supply := retainingPartialFactorizationOfNMinusOne n params fuel
    match findBLS5CertificateFromSupply n supply bases with
    | some certificate => boundedBLS5Result n (some certificate)
    | none =>
      bls5DiscriminantResultFromSupply n supply
        (fun _ h ↦ retainingPartialFactorizationOfNMinusOne_sound h)
  else .invalidInput (Nat.not_lt.mp hinput)

/-- Sharing retained data preserves the original two-branch search result exactly. -/
theorem boundedBLS5SearchWithComposite_eq (n : ℕ)
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ) :
    boundedBLS5SearchWithComposite n params fuel bases =
      if hinput : 1 < n then
        match findBLS5Certificate n params fuel bases with
        | some certificate => boundedBLS5Result n (some certificate)
        | none => bls5DiscriminantResultFromRetainedSupply n params fuel
      else .invalidInput (Nat.not_lt.mp hinput) := by
  rfl

/-- A successful certificate keeps its prime result in the combined BLS5 search. -/
theorem boundedBLS5SearchWithComposite_prime_case {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ)
    {certificate : BLS5Certificate} (hinput : 1 < n)
    (hcert : findBLS5Certificate n params fuel bases = some certificate) :
    boundedBLS5SearchWithComposite n params fuel bases =
      .prime
        ((findBLS5Certificate_some_spec hcert).1 ▸
          prime_of_valid_bls5_certificate certificate (findBLS5Certificate_some_spec hcert).2) := by
  rw [boundedBLS5SearchWithComposite_eq]
  rw [dite_eq_left hinput, hcert]
  exact
    boundedBLS5Result_prime_case certificate hinput (findBLS5Certificate_some_spec hcert).1
      (findBLS5Certificate_some_spec hcert).2

/-- Certificate-search exhaustion invokes the retained-factor discriminant branch. -/
theorem boundedBLS5SearchWithComposite_none_case {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ)
    (hinput : 1 < n) (hnone : findBLS5Certificate n params fuel bases = none) :
    boundedBLS5SearchWithComposite n params fuel bases =
      bls5DiscriminantResultFromRetainedSupply n params fuel := by
  rw [boundedBLS5SearchWithComposite_eq]
  rw [dite_eq_left hinput, hnone]

/-- On a composite input, the combined BLS5 search has no prime-certificate branch;
its result is the retained-factor discriminant classification for every base list. -/
theorem boundedBLS5SearchWithComposite_of_not_prime {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ)
    (hinput : 1 < n) (hcomp : ¬Nat.Prime n) :
    boundedBLS5SearchWithComposite n params fuel bases =
      bls5DiscriminantResultFromRetainedSupply n params fuel := by
  exact
    boundedBLS5SearchWithComposite_none_case params fuel bases hinput
      (findBLS5Certificate_eq_none_of_not_prime params fuel bases hcomp)

/-- A retained decomposition with positive quotient and a found discriminant root makes the
combined bounded search return a proof-carrying composite result. -/
theorem boundedBLS5SearchWithComposite_composite_case {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ)
    {data : PartialFactorizationData} (hinput : 1 < n)
    (hnone : findBLS5Certificate n params fuel bases = none)
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hq : 0 < bls5Quotient data.cofactor (factorProduct data.factors)) {z : ℤ}
    (hroot : findBls5DiscriminantSquareRoot data.cofactor (factorProduct data.factors) = some z) :
    ∃ hcomp : ¬Nat.Prime n,
      boundedBLS5SearchWithComposite n params fuel bases = .composite hcomp := by
  obtain ⟨hcomp, hresult⟩ :=
    bls5DiscriminantResultFromRetainedSupply_composite_of_some hinput hdata hq hroot
  exact
    ⟨hcomp, (boundedBLS5SearchWithComposite_none_case params fuel bases hinput hnone).trans hresult⟩

/-- A retained square discriminant proves that certificate search cannot succeed, so the
combined BLS5 search reaches its composite branch without a separate failure hypothesis. -/
theorem boundedBLS5SearchWithComposite_composite_of_root {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ)
    {data : PartialFactorizationData} (hinput : 1 < n)
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hq : 0 < bls5Quotient data.cofactor (factorProduct data.factors)) {z : ℤ}
    (hroot : findBls5DiscriminantSquareRoot data.cofactor (factorProduct data.factors) = some z) :
    ∃ hcomp : ¬Nat.Prime n,
      boundedBLS5SearchWithComposite n params fuel bases = .composite hcomp := by
  obtain ⟨hcomp, hresult⟩ :=
    bls5DiscriminantResultFromRetainedSupply_composite_of_some hinput hdata hq hroot
  exact
    ⟨hcomp,
      (boundedBLS5SearchWithComposite_of_not_prime params fuel bases hinput hcomp).trans hresult⟩

/-- If bounded factor supply returns nothing, both certificate and discriminant searches
remain inconclusive. -/
theorem boundedBLS5SearchWithComposite_unknown_of_no_factor {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ)
    (hinput : 1 < n) (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = none) :
    boundedBLS5SearchWithComposite n params fuel bases = .unknown := by
  have hcert : findBLS5Certificate n params fuel bases = none := by
    unfold findBLS5Certificate findBLS5CertificateFromSupply
    rw [hdata]
  rw [boundedBLS5SearchWithComposite_none_case params fuel bases hinput hcert]
  exact bls5DiscriminantResultFromRetainedSupply_unknown_of_none hinput hdata

/-- After certificate exhaustion, retained factors with zero BLS5 quotient cannot
justify either primality or the positive-quotient composite criterion. -/
theorem boundedBLS5SearchWithComposite_unknown_of_zero {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ)
    {data : PartialFactorizationData} (hinput : 1 < n)
    (hcert : findBLS5Certificate n params fuel bases = none)
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hzero : bls5Quotient data.cofactor (factorProduct data.factors) = 0) :
    boundedBLS5SearchWithComposite n params fuel bases = .unknown := by
  rw [boundedBLS5SearchWithComposite_none_case params fuel bases hinput hcert]
  exact bls5DiscriminantResultFromRetainedSupply_unknown_of_zero hinput hdata hzero

/-- After certificate exhaustion, a nonsquare BLS5 discriminant leaves the
combined search unknown even when the retained quotient is positive. -/
theorem boundedBLS5SearchWithComposite_unknown_of_root_none {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ)
    {data : PartialFactorizationData} (hinput : 1 < n)
    (hcert : findBLS5Certificate n params fuel bases = none)
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hq : 0 < bls5Quotient data.cofactor (factorProduct data.factors))
    (hroot : findBls5DiscriminantSquareRoot data.cofactor (factorProduct data.factors) = none) :
    boundedBLS5SearchWithComposite n params fuel bases = .unknown := by
  rw [boundedBLS5SearchWithComposite_none_case params fuel bases hinput hcert]
  exact bls5DiscriminantResultFromRetainedSupply_unknown_of_root_none hinput hdata hq hroot

/-- For an in-range input, the combined search is unknown exactly when certificate
search is exhausted and retained-factor classification is also unknown. This
characterizes the inconclusive branch of the public BLS5 result. -/
theorem boundedBLS5SearchWithComposite_unknown_iff {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ)
    (hinput : 1 < n) :
    boundedBLS5SearchWithComposite n params fuel bases = .unknown ↔
      findBLS5Certificate n params fuel bases = none ∧
        bls5DiscriminantResultFromRetainedSupply n params fuel = .unknown := by
  constructor
  · intro hunknown
    cases hcert : findBLS5Certificate n params fuel bases with
    | none =>
      refine ⟨rfl, ?_⟩
      exact
        (boundedBLS5SearchWithComposite_none_case params fuel bases hinput hcert).symm.trans
          hunknown
    | some
      certificate =>
      have hprime := boundedBLS5SearchWithComposite_prime_case params fuel bases hinput hcert
      rw [hprime] at hunknown
      cases hunknown
  · rintro ⟨hcert, hfallback⟩
    rw [boundedBLS5SearchWithComposite_none_case params fuel bases hinput hcert]
    exact hfallback

/-- For an in-range input, the combined search is composite exactly when
certificate search is exhausted and the retained-factor classifier proves
compositeness. The theorem exposes both finite branches to later consumers. -/
theorem boundedBLS5SearchWithComposite_composite_iff {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ)
    (hinput : 1 < n) :
    (∃ hcomp : ¬Nat.Prime n,
        boundedBLS5SearchWithComposite n params fuel bases = .composite hcomp) ↔
      findBLS5Certificate n params fuel bases = none ∧
        ∃ hcomp : ¬Nat.Prime n,
          bls5DiscriminantResultFromRetainedSupply n params fuel = .composite hcomp := by
  constructor
  · rintro ⟨hcomp, hresult⟩
    cases hcert : findBLS5Certificate n params fuel bases with
    | none =>
      refine ⟨rfl, hcomp, ?_⟩
      exact
        (boundedBLS5SearchWithComposite_none_case params fuel bases hinput hcert).symm.trans hresult
    | some
      certificate =>
      have hprime := boundedBLS5SearchWithComposite_prime_case params fuel bases hinput hcert
      rw [hprime] at hresult
      cases hresult
  · rintro ⟨hcert, hcomp, hfallback⟩
    refine ⟨hcomp, ?_⟩
    rw [boundedBLS5SearchWithComposite_none_case params fuel bases hinput hcert]
    exact hfallback

/-- With retained factors and a positive quotient, the combined BLS5 search
returns a composite proof exactly when its finite discriminant-root search
succeeds. The certificate branch cannot succeed on that composite input. -/
theorem boundedBLS5SearchWithComposite_composite_iff_root {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ)
    {data : PartialFactorizationData} (hinput : 1 < n)
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hq : 0 < bls5Quotient data.cofactor (factorProduct data.factors)) :
    (∃ hcomp : ¬Nat.Prime n,
        boundedBLS5SearchWithComposite n params fuel bases = .composite hcomp) ↔
      ∃ z, findBls5DiscriminantSquareRoot data.cofactor (factorProduct data.factors) = some z := by
  constructor
  · rintro ⟨hcomp, hresult⟩
    obtain ⟨_, hfallback⟩ :=
      (boundedBLS5SearchWithComposite_composite_iff params fuel bases hinput).mp ⟨hcomp, hresult⟩
    exact (bls5DiscriminantResultFromRetainedSupply_composite_iff_some hinput hdata hq).mp hfallback
  · intro hroot
    obtain ⟨hcomp, hfallback⟩ :=
      (bls5DiscriminantResultFromRetainedSupply_composite_iff_some hinput hdata hq).mpr hroot
    have hnone := findBLS5Certificate_eq_none_of_not_prime params fuel bases hcomp
    exact
      (boundedBLS5SearchWithComposite_composite_iff params fuel bases hinput).mpr
        ⟨hnone, hcomp, hfallback⟩

/-- For a composite input with retained factors and positive quotient, the
combined BLS5 search remains unknown exactly when no discriminant root is
found. Certificate search is impossible on this input by its soundness. -/
theorem boundedBLS5SearchWithComposite_unknown_iff_root_none_of_not_prime {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ)
    {data : PartialFactorizationData} (hinput : 1 < n) (hcomp : ¬Nat.Prime n)
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hq : 0 < bls5Quotient data.cofactor (factorProduct data.factors)) :
    boundedBLS5SearchWithComposite n params fuel bases = .unknown ↔
      findBls5DiscriminantSquareRoot data.cofactor (factorProduct data.factors) = none := by
  constructor
  · intro hunknown
    obtain ⟨_, hfallback⟩ :=
      (boundedBLS5SearchWithComposite_unknown_iff params fuel bases hinput).mp hunknown
    exact (bls5DiscriminantResultFromRetainedSupply_unknown_iff_none hinput hdata hq).mp hfallback
  · intro hroot
    apply (boundedBLS5SearchWithComposite_unknown_iff params fuel bases hinput).mpr
    exact
      ⟨findBLS5Certificate_eq_none_of_not_prime params fuel bases hcomp,
        (bls5DiscriminantResultFromRetainedSupply_unknown_iff_none hinput hdata hq).mpr hroot⟩

/-- On a composite input, a retained decomposition with zero BLS5 quotient
forces the combined search to remain unknown for every witness-base list. -/
theorem boundedBLS5SearchWithComposite_unknown_of_not_prime_of_zero {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ)
    {data : PartialFactorizationData} (hinput : 1 < n) (hcomp : ¬Nat.Prime n)
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hzero : bls5Quotient data.cofactor (factorProduct data.factors) = 0) :
    boundedBLS5SearchWithComposite n params fuel bases = .unknown := by
  apply (boundedBLS5SearchWithComposite_unknown_iff params fuel bases hinput).mpr
  refine ⟨findBLS5Certificate_eq_none_of_not_prime params fuel bases hcomp, ?_⟩
  exact bls5DiscriminantResultFromRetainedSupply_unknown_of_zero hinput hdata hzero

/-- On a composite input, a positive quotient without a found discriminant
root also leaves the combined search unknown for every witness-base list. -/
theorem boundedBLS5SearchWithComposite_unknown_of_not_prime_of_root_none {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ)
    {data : PartialFactorizationData} (hinput : 1 < n) (hcomp : ¬Nat.Prime n)
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hq : 0 < bls5Quotient data.cofactor (factorProduct data.factors))
    (hroot : findBls5DiscriminantSquareRoot data.cofactor (factorProduct data.factors) = none) :
    boundedBLS5SearchWithComposite n params fuel bases = .unknown := by
  exact
    (boundedBLS5SearchWithComposite_unknown_iff_root_none_of_not_prime params fuel bases hinput
          hcomp hdata hq).mpr
      hroot

/-- The retained-factor discriminant classifier has only composite and unknown
branches on an in-range input. It cannot manufacture a BLS5 prime certificate. -/
theorem bls5DiscriminantResultFromRetainedSupply_no_prime_branch {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (hinput : 1 < n) :
    ¬∃ hprime : Nat.Prime n,
        bls5DiscriminantResultFromRetainedSupply n params fuel = .prime hprime := by
  rintro ⟨hprime, hresult⟩
  unfold bls5DiscriminantResultFromRetainedSupply bls5DiscriminantResultFromSupply at hresult
  rw [dite_eq_left hinput] at hresult
  split at hresult
  · cases hresult
  · split at hresult
    · unfold bls5DiscriminantResult at hresult
      split at hresult <;> cases hresult
    · cases hresult

/-- For an in-range input, the combined BLS5 search returns a prime result
exactly when the finite factor-and-witness search finds a checked certificate.
The retained-factor fallback contributes only composite or unknown results. -/
theorem boundedBLS5SearchWithComposite_prime_iff_certificate {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ)
    (hinput : 1 < n) :
    (∃ hprime : Nat.Prime n, boundedBLS5SearchWithComposite n params fuel bases = .prime hprime) ↔
      ∃ certificate, findBLS5Certificate n params fuel bases = some certificate := by
  constructor
  · rintro ⟨hprime, hresult⟩
    cases hcert : findBLS5Certificate n params fuel bases with
    | none =>
      have hfallback := boundedBLS5SearchWithComposite_none_case params fuel bases hinput hcert
      exact
        False.elim
          (bls5DiscriminantResultFromRetainedSupply_no_prime_branch params fuel hinput
            ⟨hprime, hfallback.symm.trans hresult⟩)
    | some certificate => exact ⟨certificate, rfl⟩
  · rintro ⟨certificate, hcert⟩
    have hspec := findBLS5Certificate_some_spec hcert
    let hprime : Nat.Prime n := hspec.1 ▸ prime_of_valid_bls5_certificate certificate hspec.2
    exact ⟨hprime, boundedBLS5SearchWithComposite_prime_case params fuel bases hinput hcert⟩

/-- With retained factor data and finite base-list coverage, the combined
BLS5 search reaches its proof-carrying prime branch exactly when its
arithmetic criterion accepts the retained cofactor. -/
theorem boundedBLS5SearchWithComposite_prime_iff_arithmetic_of_coverage {n : ℕ} (hn5 : 5 ≤ n)
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ} {bases : List ℕ}
    {data : PartialFactorizationData}
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hEven : Even (factorProduct data.factors))
    (hcop : Nat.Coprime (factorProduct data.factors) data.cofactor)
    (hbound :
      n <
        (factorProduct data.factors + 1) *
          (2 * factorProduct data.factors ^ 2 +
            (data.cofactor % (2 * factorProduct data.factors) - 1) * factorProduct data.factors +
            1))
    (hcoverage : ∀ qe, qe ∈ data.factors → ∃ a, a ∈ bases ∧ IsBLSWitness n qe.1 a) :
    (∃ hprime : Nat.Prime n, boundedBLS5SearchWithComposite n params fuel bases = .prime hprime) ↔
      bls5PassesArithmeticCriterion data.cofactor (factorProduct data.factors) = true := by
  calc
    _ ↔ ∃ certificate, findBLS5Certificate n params fuel bases = some certificate :=
      boundedBLS5SearchWithComposite_prime_iff_certificate params fuel bases
        (lt_of_lt_of_le (by decide : 1 < 5) hn5)
    _ ↔ bls5PassesArithmeticCriterion data.cofactor (factorProduct data.factors) = true :=
      findBLS5Certificate_some_iff_arithmetic_of_coverage hn5 hdata hEven hcop hbound hcoverage

/-- With retained factor supply and explicit witness-base coverage, the
combined BLS5 search returns its prime branch exactly for prime inputs.
The factor, parity, coprimality, and expanded-bound assumptions are stated
explicitly; no claim is made about arbitrary finite search budgets. -/
theorem boundedBLS5SearchWithComposite_prime_iff_prime_of_coverage {n : ℕ} (hn5 : 5 ≤ n)
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ} {bases : List ℕ}
    {data : PartialFactorizationData}
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hEven : Even (factorProduct data.factors))
    (hcop : Nat.Coprime (factorProduct data.factors) data.cofactor)
    (hbound :
      n <
        (factorProduct data.factors + 1) *
          (2 * factorProduct data.factors ^ 2 +
            (data.cofactor % (2 * factorProduct data.factors) - 1) * factorProduct data.factors +
            1))
    (hcoverage : ∀ qe, qe ∈ data.factors → ∃ a, a ∈ bases ∧ IsBLSWitness n qe.1 a) :
    Nat.Prime n ↔
      ∃ hprime : Nat.Prime n,
        boundedBLS5SearchWithComposite n params fuel bases = .prime hprime := by
  calc
    Nat.Prime n ↔ bls5PassesArithmeticCriterion data.cofactor (factorProduct data.factors) = true :=
      prime_iff_bls5Arithmetic_of_supply_coverage hn5 hdata hEven hcop hbound hcoverage
    _ ↔
        ∃ hprime : Nat.Prime n,
          boundedBLS5SearchWithComposite n params fuel bases = .prime hprime :=
      (boundedBLS5SearchWithComposite_prime_iff_arithmetic_of_coverage hn5 hdata hEven hcop hbound
          hcoverage).symm

/-- Inputs outside the primality domain are rejected before either bounded search. -/
theorem boundedBLS5SearchWithComposite_invalidInput {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ)
    (hn : n ≤ 1) : boundedBLS5SearchWithComposite n params fuel bases = .invalidInput hn := by
  rw [boundedBLS5SearchWithComposite_eq]
  rw [dite_eq_right (Nat.not_lt.mpr hn)]

/-- Every conclusive combined BLS5 result carries its claimed primality proof. -/
theorem boundedBLS5SearchWithComposite_sound (n : ℕ)
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ) :
    (boundedBLS5SearchWithComposite n params fuel bases).sound := by exact BLSResult.sound_proof _

/-- The existing retained-factor and finite-witness coverage also reaches the prime branch
of the combined search; the composite fallback does not weaken certificate success. -/
theorem exists_boundedBLS5SearchWithComposite_prime_of_coverage {n : ℕ} (hn5 : 5 ≤ n)
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ} {bases : List ℕ}
    {data : PartialFactorizationData}
    (hdata : retainingPartialFactorizationOfNMinusOne n params fuel = some data)
    (hEven : Even (factorProduct data.factors))
    (hcop : Nat.Coprime (factorProduct data.factors) data.cofactor)
    (hbound :
      n <
        (factorProduct data.factors + 1) *
          (2 * factorProduct data.factors ^ 2 +
            (data.cofactor % (2 * factorProduct data.factors) - 1) * factorProduct data.factors +
            1))
    (harithmetic : bls5PassesArithmeticCriterion data.cofactor (factorProduct data.factors) = true)
    (hcoverage : ∀ qe, qe ∈ data.factors → ∃ a, a ∈ bases ∧ IsBLSWitness n qe.1 a) :
    ∃ hprime : Nat.Prime n, boundedBLS5SearchWithComposite n params fuel bases = .prime hprime := by
  exact
    (boundedBLS5SearchWithComposite_prime_iff_arithmetic_of_coverage hn5 hdata hEven hcop hbound
          hcoverage).mpr
      harithmetic

/-- A proper divisor contradicts primality by the prime-divisor characterization. -/
theorem not_prime_of_proper_factor {n d : ℕ} (h : NumberTheory.Factorization.ProperFactor n d) :
    ¬Nat.Prime n := by
  change 1 < d ∧ d < n ∧ d ∣ n at h
  rcases h with ⟨hlo, hhi, hdvd⟩
  intro hn
  have hd := (Nat.dvd_prime hn).mp hdvd
  rcases hd with hone | hself
  · subst d
    exact (lt_irrefl 1) hlo
  · subst d
    exact (lt_irrefl n) hhi

/-- Run the BLS certificate search and a bounded rho factor search on the original input.
The certificate branch proves primality, a discovered proper factor proves compositeness, and two
failed searches return `unknown`; inputs 0 and 1 are reported separately. -/
def boundedBLSResult (n : ℕ) (params : NumberTheory.Factorization.PollardRho.Params)
    (tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree) (bases : List ℕ) (factorFuel : ℕ) :
    BLSResult n :=
  if hinput : 1 < n then
    match hcertificate : findSquareCertificateFromBudgetTree n params tree bases with
    | some _certificate =>
      .prime
        (certificate_n_eq_input_of_findSquareCertificateFromBudgetTree hcertificate ▸
          prime_of_findSquareCertificateFromBudgetTree hcertificate)
    | none =>
      match hfactor : NumberTheory.Factorization.PollardRho.findFactor n params factorFuel with
      | some _factor =>
        .composite
          (not_prime_of_proper_factor
            (NumberTheory.Factorization.PollardRho.findFactor_sound hfactor))
      | none => .unknown
  else .invalidInput (Nat.not_lt.mp hinput)

/-- If the bounded certificate search succeeds, the result entry returns its proved prime branch.
This exposes the constructive success branch independently of the later rho fallback. -/
theorem boundedBLSResult_prime_case {n : ℕ} (params : NumberTheory.Factorization.PollardRho.Params)
    (tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree) (bases : List ℕ) (factorFuel : ℕ)
    {certificate : SquareCertificate} (hinput : 1 < n)
    (hcert : findSquareCertificateFromBudgetTree n params tree bases = some certificate) :
    boundedBLSResult n params tree bases factorFuel =
      .prime
        (certificate_n_eq_input_of_findSquareCertificateFromBudgetTree hcert ▸
          prime_of_findSquareCertificateFromBudgetTree hcert) := by
  simp only [boundedBLSResult, dite_eq_left hinput]
  split
  · case h_1 found
      hfound =>
      have hsame : found = certificate := Option.some.inj (hfound.symm.trans hcert)
      subst found
      rfl
  · case h_2 hnone =>
      rw [hnone] at hcert
      cases hcert

/-- A successful result entry exposes both its proved prime branch and the corresponding
branch-sensitive cube criterion for the exact certificate found by the same budget-tree search. -/
theorem boundedBLSResult_prime_case_with_cubeCriterion {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params)
    (tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree) (bases : List ℕ) (factorFuel : ℕ)
    {certificate : SquareCertificate} (hinput : 1 < n)
    (hcert : findSquareCertificateFromBudgetTree n params tree bases = some certificate) :
    boundedBLSResult n params tree bases factorFuel =
        .prime
          (certificate_n_eq_input_of_findSquareCertificateFromBudgetTree hcert ▸
            prime_of_findSquareCertificateFromBudgetTree hcert) ∧
      (Nat.Prime certificate.n ↔
        cubeQuotient certificate.factorization.cofactor
              (factorProduct certificate.factorization.factors) =
            0 ∨
          findCubeDiscriminantSquareRoot certificate.factorization.cofactor
              (factorProduct certificate.factorization.factors) =
            none) := by
  exact
    ⟨boundedBLSResult_prime_case params tree bases factorFuel hinput hcert,
      prime_iff_cubeDiscriminantRootSearch_none_or_quotient_zero_of_budget_tree_search hcert⟩

/-- If certificate search fails but the bounded rho search finds a proper factor, the result entry
returns its proved composite branch. Failure of the certificate search alone is not a rejection. -/
theorem boundedBLSResult_composite_case {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params)
    (tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree) (bases : List ℕ) (factorFuel : ℕ)
    (hinput : 1 < n) (hcertificate : findSquareCertificateFromBudgetTree n params tree bases = none)
    {factor : ℕ}
    (hfactor : NumberTheory.Factorization.PollardRho.findFactor n params factorFuel = some factor) :
    boundedBLSResult n params tree bases factorFuel =
      .composite
        (not_prime_of_proper_factor
          (NumberTheory.Factorization.PollardRho.findFactor_sound hfactor)) := by
  simp only [boundedBLSResult, dite_eq_left hinput]
  split
  · case h_1 found hfound =>
      rw [hfound] at hcertificate
      cases hcertificate
  · case h_2 hnone =>
      split
      · case h_1 found
          hfound =>
          have hsame : found = factor := Option.some.inj (hfound.symm.trans hfactor)
          subst found
          rfl
      · case h_2 hnoneFactor =>
          rw [hnoneFactor] at hfactor
          cases hfactor

/-- If neither bounded search finds a certificate or a proper factor, the result is `unknown`.
In particular, failure of both finite searches does not assert compositeness. -/
theorem boundedBLSResult_unknown_case {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params)
    (tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree) (bases : List ℕ) (factorFuel : ℕ)
    (hinput : 1 < n) (hcertificate : findSquareCertificateFromBudgetTree n params tree bases = none)
    (hfactor : NumberTheory.Factorization.PollardRho.findFactor n params factorFuel = none) :
    boundedBLSResult n params tree bases factorFuel = .unknown := by
  simp only [boundedBLSResult, dite_eq_left hinput]
  split
  · case h_1 found hfound =>
      rw [hfound] at hcertificate
      cases hcertificate
  · case h_2 hnone =>
      split
      · case h_1 found hfound =>
          rw [hfound] at hfactor
          cases hfactor
      · case h_2 hnoneFactor => rfl

/-- Inputs at most one are classified as out of domain before either bounded search is run. -/
theorem boundedBLSResult_invalidInput_case (n : ℕ)
    (params : NumberTheory.Factorization.PollardRho.Params)
    (tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree) (bases : List ℕ) (factorFuel : ℕ)
    (hinput : n ≤ 1) : boundedBLSResult n params tree bases factorFuel = .invalidInput hinput := by
  have hnot : ¬1 < n := Nat.not_lt_of_le hinput
  simp only [boundedBLSResult, dite_eq_right hnot]

/-- The budgeted BLS entry point always returns a result whose attached proposition is proved. -/
theorem boundedBLSResult_sound (n : ℕ) (params : NumberTheory.Factorization.PollardRho.Params)
    (tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree) (bases : List ℕ) (factorFuel : ℕ) :
    (boundedBLSResult n params tree bases factorFuel).sound :=
  BLSResult.sound_proof (boundedBLSResult n params tree bases factorFuel)

/-- For an input above one, the budget-tree BLS result has a prime branch exactly
when its square-certificate search finds a verified certificate. The rho fallback
cannot create a prime branch. -/
theorem boundedBLSResult_prime_iff_certificate {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params)
    (tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree) (bases : List ℕ) (factorFuel : ℕ)
    (hinput : 1 < n) :
    (∃ hprime : Nat.Prime n, boundedBLSResult n params tree bases factorFuel = .prime hprime) ↔
      ∃ certificate,
        findSquareCertificateFromBudgetTree n params tree bases = some certificate := by
  constructor
  · rintro ⟨hprime, hresult⟩
    cases hcert : findSquareCertificateFromBudgetTree n params tree bases with
    | some certificate => exact ⟨certificate, rfl⟩
    | none =>
      cases hfactor : NumberTheory.Factorization.PollardRho.findFactor n params factorFuel with
      | some
        factor =>
        have hcomp :=
          boundedBLSResult_composite_case params tree bases factorFuel hinput hcert hfactor
        cases hcomp.symm.trans hresult
      | none =>
        have hunk := boundedBLSResult_unknown_case params tree bases factorFuel hinput hcert hfactor
        cases hunk.symm.trans hresult
  · rintro ⟨certificate, hcert⟩
    exact ⟨_, boundedBLSResult_prime_case params tree bases factorFuel hinput hcert⟩

/-- Above one, the budget-tree BLS result is unknown precisely when both the
square-certificate search and the subsequent rho factor search fail. -/
theorem boundedBLSResult_unknown_iff {n : ℕ} (params : NumberTheory.Factorization.PollardRho.Params)
    (tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree) (bases : List ℕ) (factorFuel : ℕ)
    (hinput : 1 < n) :
    boundedBLSResult n params tree bases factorFuel = .unknown ↔
      findSquareCertificateFromBudgetTree n params tree bases = none ∧
        NumberTheory.Factorization.PollardRho.findFactor n params factorFuel = none := by
  constructor
  · intro hresult
    cases hcert : findSquareCertificateFromBudgetTree n params tree bases with
    | some
      certificate =>
      have hprime := boundedBLSResult_prime_case params tree bases factorFuel hinput hcert
      cases hprime.symm.trans hresult
    | none =>
      refine ⟨rfl, ?_⟩
      cases hfactor : NumberTheory.Factorization.PollardRho.findFactor n params factorFuel with
      | some
        factor =>
        have hcomp :=
          boundedBLSResult_composite_case params tree bases factorFuel hinput hcert hfactor
        cases hcomp.symm.trans hresult
      | none => rfl
  · rintro ⟨hcert, hfactor⟩
    exact boundedBLSResult_unknown_case params tree bases factorFuel hinput hcert hfactor

/-- Above one, the budget-tree BLS result carries a compositeness proof
precisely when certificate search fails and rho finds a proper factor. -/
theorem boundedBLSResult_composite_iff {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params)
    (tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree) (bases : List ℕ) (factorFuel : ℕ)
    (hinput : 1 < n) :
    (∃ hnot : ¬Nat.Prime n, boundedBLSResult n params tree bases factorFuel = .composite hnot) ↔
      findSquareCertificateFromBudgetTree n params tree bases = none ∧
        ∃ factor,
          NumberTheory.Factorization.PollardRho.findFactor n params factorFuel = some factor := by
  constructor
  · rintro ⟨hnot, hresult⟩
    cases hcert : findSquareCertificateFromBudgetTree n params tree bases with
    | some
      certificate =>
      have hprime := boundedBLSResult_prime_case params tree bases factorFuel hinput hcert
      cases hprime.symm.trans hresult
    | none =>
      refine ⟨rfl, ?_⟩
      cases hfactor : NumberTheory.Factorization.PollardRho.findFactor n params factorFuel with
      | some factor => exact ⟨factor, rfl⟩
      | none =>
        have hunk := boundedBLSResult_unknown_case params tree bases factorFuel hinput hcert hfactor
        cases hunk.symm.trans hresult
  · rintro ⟨hcert, factor, hfactor⟩
    exact ⟨_, boundedBLSResult_composite_case params tree bases factorFuel hinput hcert hfactor⟩

/-- The integer-budget BLS constructor returns only certificates accepted by the square verifier.
-/
theorem prime_of_findSquareCertificateFromRoundBudget {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {maxDepth roundBudget : ℕ}
    {bases : List ℕ} {certificate : SquareCertificate}
    (h :
      findSquareCertificateFromRoundBudget n params maxDepth roundBudget bases = some certificate) :
    Nat.Prime certificate.n := by exact prime_of_findSquareCertificateFromBudgetTree h

/-- The practical global-round-budget constructor inherits the branch-sensitive cube-root
characterization of every certificate it returns. -/
theorem prime_iff_cubeDiscriminantRootSearch_none_or_quotient_zero_of_round_budget_search {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {maxDepth roundBudget : ℕ}
    {bases : List ℕ} {certificate : SquareCertificate}
    (h :
      findSquareCertificateFromRoundBudget n params maxDepth roundBudget bases = some certificate) :
    Nat.Prime certificate.n ↔
      cubeQuotient certificate.factorization.cofactor
            (factorProduct certificate.factorization.factors) =
          0 ∨
        findCubeDiscriminantSquareRoot certificate.factorization.cofactor
            (factorProduct certificate.factorization.factors) =
          none := by
  exact prime_iff_cubeDiscriminantRootSearch_none_or_quotient_zero_of_budget_tree_search h

/-- For `n ≥ 5`, a successful budget-tree supply, square-root bound, and witness in the base
list for each factor key make the verified constructor succeed. Supply success is an explicit
premise; the proof collects witnesses and invokes the factor and witness checker specifications. -/
theorem exists_findSquareCertificateFromBudgetTree_of_coverage {n : ℕ} (hn5 : 5 ≤ n)
    {params : NumberTheory.Factorization.PollardRho.Params}
    {tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree} {bases : List ℕ}
    {data : PartialFactorizationData}
    (hdata : retainingPartialFactorizationOfNMinusOneByTree n params tree = some data)
    (hbound : n < factorProduct data.factors ^ 2)
    (hcoverage : ∀ qe, qe ∈ data.factors → ∃ a, a ∈ bases ∧ IsBLSWitness n qe.1 a) :
    ∃ certificate, findSquareCertificateFromBudgetTree n params tree bases = some certificate := by
  have hsome : (findBLSWitnesses n data.factors bases).isSome = true :=
    (findBLSWitnesses_isSome_iff).mpr hcoverage
  cases hwitnesses : findBLSWitnesses n data.factors bases with
  | none =>
    rw [hwitnesses] at hsome
    exact False.elim (Bool.noConfusion hsome)
  | some
    witnesses =>
    have hfactor : ValidPartialFactorization n data :=
      retainingPartialFactorizationOfNMinusOneByTree_sound hdata
    have hwitness : ValidWitnesses n data witnesses := by
      apply (checkWitnesses_eq_true_iff n data witnesses).mpr
      exact findBLSWitnesses_sound hwitnesses
    have hverify : verifySquareCertificate ⟨n, data, witnesses⟩ = true := by
      simp only [verifySquareCertificate, checkSquareCertificate, Bool.and_eq_true,
        decide_eq_true_eq]
      exact ⟨⟨⟨hn5, hbound⟩, hfactor⟩, hwitness⟩
    refine ⟨⟨n, data, witnesses⟩, ?_⟩
    simp only [findSquareCertificateFromBudgetTree, hdata, hwitnesses, hverify]
    rfl

/-- Retained factor supply, the square bound, and finite witness coverage reach
the proof-carrying prime branch of the budget-tree BLS result. The fallback
factor-search fuel can be arbitrary because the certificate branch succeeds. -/
theorem exists_boundedBLSResult_prime_of_coverage {n : ℕ} (hn5 : 5 ≤ n)
    {params : NumberTheory.Factorization.PollardRho.Params}
    {tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree} {bases : List ℕ}
    {data : PartialFactorizationData}
    (hdata : retainingPartialFactorizationOfNMinusOneByTree n params tree = some data)
    (hbound : n < factorProduct data.factors ^ 2)
    (hcoverage : ∀ qe, qe ∈ data.factors → ∃ a, a ∈ bases ∧ IsBLSWitness n qe.1 a)
    (factorFuel : ℕ) :
    ∃ hprime : Nat.Prime n, boundedBLSResult n params tree bases factorFuel = .prime hprime := by
  have hinput : 1 < n := lt_of_lt_of_le (by decide : 1 < 5) hn5
  have hcert := exists_findSquareCertificateFromBudgetTree_of_coverage hn5 hdata hbound hcoverage
  exact (boundedBLSResult_prime_iff_certificate params tree bases factorFuel hinput).mpr hcert

/-- A successful balanced supply, square-root bound, and witness coverage guarantee that the
global-round-budget BLS constructor returns a verified certificate. -/
theorem exists_findSquareCertificateFromRoundBudget_of_coverage {n : ℕ} (hn5 : 5 ≤ n)
    {params : NumberTheory.Factorization.PollardRho.Params} {maxDepth roundBudget : ℕ}
    {bases : List ℕ} {data : PartialFactorizationData}
    (hdata :
      retainingPartialFactorizationOfNMinusOneByTree n params
          (NumberTheory.Factorization.PollardRho.balancedRhoBudgetTree maxDepth roundBudget) =
        some data)
    (hbound : n < factorProduct data.factors ^ 2)
    (hcoverage : ∀ qe, qe ∈ data.factors → ∃ a, a ∈ bases ∧ IsBLSWitness n qe.1 a) :
    ∃ certificate,
      findSquareCertificateFromRoundBudget n params maxDepth roundBudget bases =
        some certificate := by
  exact exists_findSquareCertificateFromBudgetTree_of_coverage hn5 hdata hbound hcoverage

/-- Coverage for the balanced rho-budget search yields a certificate together with its complete
branch-sensitive cube-root primality criterion. -/
theorem exists_findSquareCertificateFromRoundBudget_with_cube_criterion {n : ℕ} (hn5 : 5 ≤ n)
    {params : NumberTheory.Factorization.PollardRho.Params} {maxDepth roundBudget : ℕ}
    {bases : List ℕ} {data : PartialFactorizationData}
    (hdata :
      retainingPartialFactorizationOfNMinusOneByTree n params
          (NumberTheory.Factorization.PollardRho.balancedRhoBudgetTree maxDepth roundBudget) =
        some data)
    (hbound : n < factorProduct data.factors ^ 2)
    (hcoverage : ∀ qe, qe ∈ data.factors → ∃ a, a ∈ bases ∧ IsBLSWitness n qe.1 a) :
    ∃ certificate,
      findSquareCertificateFromRoundBudget n params maxDepth roundBudget bases = some certificate ∧
        (Nat.Prime certificate.n ↔
          cubeQuotient certificate.factorization.cofactor
                (factorProduct certificate.factorization.factors) =
              0 ∨
            findCubeDiscriminantSquareRoot certificate.factorization.cofactor
                (factorProduct certificate.factorization.factors) =
              none) := by
  obtain ⟨certificate, hcertificate⟩ :=
    exists_findSquareCertificateFromRoundBudget_of_coverage hn5 hdata hbound hcoverage
  exact
    ⟨certificate, hcertificate,
      prime_iff_cubeDiscriminantRootSearch_none_or_quotient_zero_of_round_budget_search
        hcertificate⟩

/-- The round-budget Coverage interface characterizes the input `n` itself, since every
certificate returned by the constructor embeds that same input. -/
theorem exists_findSquareCertificateFromRoundBudget_with_input_cube_criterion {n : ℕ} (hn5 : 5 ≤ n)
    {params : NumberTheory.Factorization.PollardRho.Params} {maxDepth roundBudget : ℕ}
    {bases : List ℕ} {data : PartialFactorizationData}
    (hdata :
      retainingPartialFactorizationOfNMinusOneByTree n params
          (NumberTheory.Factorization.PollardRho.balancedRhoBudgetTree maxDepth roundBudget) =
        some data)
    (hbound : n < factorProduct data.factors ^ 2)
    (hcoverage : ∀ qe, qe ∈ data.factors → ∃ a, a ∈ bases ∧ IsBLSWitness n qe.1 a) :
    ∃ certificate,
      findSquareCertificateFromRoundBudget n params maxDepth roundBudget bases = some certificate ∧
        (Nat.Prime n ↔
          cubeQuotient certificate.factorization.cofactor
                (factorProduct certificate.factorization.factors) =
              0 ∨
            findCubeDiscriminantSquareRoot certificate.factorization.cofactor
                (factorProduct certificate.factorization.factors) =
              none) := by
  obtain ⟨certificate, hcertificate, hcriterion⟩ :=
    exists_findSquareCertificateFromRoundBudget_with_cube_criterion hn5 hdata hbound hcoverage
  have hembedded : certificate.n = n := by
    unfold findSquareCertificateFromRoundBudget at hcertificate
    unfold findSquareCertificateFromBudgetTree at hcertificate
    simp only [hdata] at hcertificate
    cases hwitnesses : findBLSWitnesses n data.factors bases with
    | none =>
      simp only [hwitnesses] at hcertificate
      cases hcertificate
    | some witnesses =>
      by_cases hverify : verifySquareCertificate ⟨n, data, witnesses⟩ = true
      · have hsome : some (⟨n, data, witnesses⟩ : SquareCertificate) = some certificate := by
          simpa only [hwitnesses, hverify, ite_true] using hcertificate
        have hcert : (⟨n, data, witnesses⟩ : SquareCertificate) = certificate :=
          Option.some.inj hsome
        cases hcert
        rfl
      · simp only [hwitnesses] at hcertificate
        rw [ite_eq_right hverify] at hcertificate
        cases hcertificate
  rw [hembedded] at hcriterion
  exact ⟨certificate, hcertificate, hcriterion⟩

/-- Run the proof-carrying BLS result entry with a balanced rho budget tree.
The global round budget is distributed by
    `NumberTheory.Factorization.PollardRho.balancedRhoBudgetTree`; the separate
factor fuel applies only to the fallback search after certificate failure. -/
def boundedBLSResultFromRoundBudget (n : ℕ) (params : NumberTheory.Factorization.PollardRho.Params)
    (maxDepth roundBudget : ℕ) (bases : List ℕ) (factorFuel : ℕ) : BLSResult n :=
  boundedBLSResult n params
    (NumberTheory.Factorization.PollardRho.balancedRhoBudgetTree maxDepth roundBudget) bases
    factorFuel

/-- Inputs at most one are rejected before the balanced round-budget search. -/
theorem boundedBLSResultFromRoundBudget_invalidInput (n : ℕ)
    (params : NumberTheory.Factorization.PollardRho.Params) (maxDepth roundBudget : ℕ)
    (bases : List ℕ) (factorFuel : ℕ) (hinput : n ≤ 1) :
    boundedBLSResultFromRoundBudget n params maxDepth roundBudget bases factorFuel =
      .invalidInput hinput := by
  exact
    boundedBLSResult_invalidInput_case n params
      (NumberTheory.Factorization.PollardRho.balancedRhoBudgetTree maxDepth roundBudget) bases
      factorFuel hinput

/-- Every balanced round-budget result carries a proof of its reported branch. -/
theorem boundedBLSResultFromRoundBudget_sound (n : ℕ)
    (params : NumberTheory.Factorization.PollardRho.Params) (maxDepth roundBudget : ℕ)
    (bases : List ℕ) (factorFuel : ℕ) :
    (boundedBLSResultFromRoundBudget n params maxDepth roundBudget bases factorFuel).sound := by
  exact
    boundedBLSResult_sound n params
      (NumberTheory.Factorization.PollardRho.balancedRhoBudgetTree maxDepth roundBudget) bases
      factorFuel

/-- The balanced-round-budget result has a prime branch exactly when its
square-certificate constructor finds a verified certificate. -/
theorem boundedBLSResultFromRoundBudget_prime_iff_certificate {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (maxDepth roundBudget : ℕ)
    (bases : List ℕ) (factorFuel : ℕ) (hinput : 1 < n) :
    (∃ hprime : Nat.Prime n,
        boundedBLSResultFromRoundBudget n params maxDepth roundBudget bases factorFuel =
          .prime hprime) ↔
      ∃ certificate,
        findSquareCertificateFromRoundBudget n params maxDepth roundBudget bases =
          some certificate := by
  exact
    boundedBLSResult_prime_iff_certificate params
      (NumberTheory.Factorization.PollardRho.balancedRhoBudgetTree maxDepth roundBudget) bases
      factorFuel hinput

/-- The balanced-round-budget result is unknown exactly when both bounded
certificate search and fallback rho factor search return `none`. -/
theorem boundedBLSResultFromRoundBudget_unknown_iff {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (maxDepth roundBudget : ℕ)
    (bases : List ℕ) (factorFuel : ℕ) (hinput : 1 < n) :
    boundedBLSResultFromRoundBudget n params maxDepth roundBudget bases factorFuel = .unknown ↔
      findSquareCertificateFromRoundBudget n params maxDepth roundBudget bases = none ∧
        NumberTheory.Factorization.PollardRho.findFactor n params factorFuel = none := by
  exact
    boundedBLSResult_unknown_iff params
      (NumberTheory.Factorization.PollardRho.balancedRhoBudgetTree maxDepth roundBudget) bases
      factorFuel hinput

/-- The balanced-round-budget result is composite exactly when certificate
search fails and fallback rho search finds a proper factor. -/
theorem boundedBLSResultFromRoundBudget_composite_iff {n : ℕ}
    (params : NumberTheory.Factorization.PollardRho.Params) (maxDepth roundBudget : ℕ)
    (bases : List ℕ) (factorFuel : ℕ) (hinput : 1 < n) :
    (∃ hnot : ¬Nat.Prime n,
        boundedBLSResultFromRoundBudget n params maxDepth roundBudget bases factorFuel =
          .composite hnot) ↔
      findSquareCertificateFromRoundBudget n params maxDepth roundBudget bases = none ∧
        ∃ factor,
          NumberTheory.Factorization.PollardRho.findFactor n params factorFuel = some factor := by
  exact
    boundedBLSResult_composite_iff params
      (NumberTheory.Factorization.PollardRho.balancedRhoBudgetTree maxDepth roundBudget) bases
      factorFuel hinput

/-- Retained factor supply, the square bound, and finite witness coverage make
the balanced-round-budget result return its proof-carrying prime branch,
independently of the fallback rho fuel. -/
theorem exists_boundedBLSResultFromRoundBudget_prime_of_coverage {n : ℕ} (hn5 : 5 ≤ n)
    {params : NumberTheory.Factorization.PollardRho.Params} {maxDepth roundBudget : ℕ}
    {bases : List ℕ} {data : PartialFactorizationData}
    (hdata :
      retainingPartialFactorizationOfNMinusOneByTree n params
          (NumberTheory.Factorization.PollardRho.balancedRhoBudgetTree maxDepth roundBudget) =
        some data)
    (hbound : n < factorProduct data.factors ^ 2)
    (hcoverage : ∀ qe, qe ∈ data.factors → ∃ a, a ∈ bases ∧ IsBLSWitness n qe.1 a)
    (factorFuel : ℕ) :
    ∃ hprime : Nat.Prime n,
      boundedBLSResultFromRoundBudget n params maxDepth roundBudget bases factorFuel =
        .prime hprime := by
  exact exists_boundedBLSResult_prime_of_coverage hn5 hdata hbound hcoverage factorFuel

end PseudoPrime.PrimeTest.BLS
