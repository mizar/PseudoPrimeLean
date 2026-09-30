/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.NumberTheory.Factorization.PrimeLeafPolicy
import PseudoPrime.NumberTheory.Factorization.Partial
import PseudoPrime.NumberTheory.Factorization.PollardRho.Budget
import PseudoPrime.NumberTheory.Factorization.PollardRho.Search

/-!
# Bounded factor supply with caller-supplied leaf certification

Rho budgets count search rounds only; the cost of the certification policy is separate.
-/

namespace PseudoPrime.NumberTheory.Factorization

namespace PollardRho

/-- Recursively split a natural number with a bounded rho schedule, returning only prime leaves.
The fuel is a maximum split depth: every internal node receives that many rho rounds. -/
def primeFactorListFuel (policy : PrimeLeafPolicy) (params : Params) : ℕ → ℕ → Option (List ℕ)
  | 0, n => if policy.accepts n then some [n] else none
  | fuel + 1, n =>
    if policy.accepts n then some [n]
    else
      match findFactor n params (fuel + 1) with
      | none => none
      | some d =>
        match primeFactorListFuel policy params fuel d,
          primeFactorListFuel policy params fuel (n / d) with
        | some left, some right => some (left ++ right)
        | _, _ => none
termination_by fuel _ => fuel

/-- On an even composite input above two, positive split depth factors by the immediate factor two
branch. This exposes the exact recursive result without unfolding any rho trajectory. -/
theorem primeFactorListFuel_even_eq_split {policy : PrimeLeafPolicy} {params : Params} {fuel n : ℕ}
    (hn : 2 < n) (hprime : ¬policy.accepts n) (heven : n % 2 = 0) :
    primeFactorListFuel policy params (fuel + 1) n =
      (match primeFactorListFuel policy params fuel 2,
        primeFactorListFuel policy params fuel (n / 2) with
      | some left, some right => some (left ++ right)
      | _, _ => none) := by
  simp only [primeFactorListFuel, ite_eq_right hprime,
    findFactor_eq_some_two_of_even params (Nat.succ_pos fuel) hn heven]

/-- At zero split depth, success is exactly policy acceptance and the singleton factor list. -/
theorem primeFactorListFuel_zero_iff {policy : PrimeLeafPolicy} {params : Params} {n : ℕ}
    {factors : List ℕ} :
    primeFactorListFuel policy params 0 n = some factors ↔ policy.accepts n ∧ factors = [n] := by
  simp only [primeFactorListFuel]
  by_cases hn : policy.accepts n
  · rw [ite_eq_left hn]
    simp only [Option.some.injEq]
    constructor
    · intro h
      exact ⟨hn, h.symm⟩
    · rintro ⟨_, h⟩
      exact h.symm
  · rw [ite_eq_right hn]
    simp only [hn, reduceCtorEq, false_iff, not_and]
    intro h
    exact h.elim

/-- An accepted input is returned immediately at every split-depth bound. -/
theorem primeFactorListFuel_of_accepts {policy : PrimeLeafPolicy} {params : Params} {fuel n : ℕ}
    (hn : policy.accepts n) : primeFactorListFuel policy params fuel n = some [n] := by
  cases fuel with
  | zero => simp only [primeFactorListFuel, hn, ite_true]
  | succ fuel => simp only [primeFactorListFuel, hn, ite_true]

/-- A successful recursive rho factorization consists of primes whose product is the input. -/
theorem primeFactorListFuel_sound {policy : PrimeLeafPolicy} {params : Params} {fuel n : ℕ}
    {factors : List ℕ} (hn : 1 < n) (h : primeFactorListFuel policy params fuel n = some factors) :
    (∀ p, p ∈ factors → Nat.Prime p) ∧ factors.prod = n := by
  induction fuel generalizing n factors with
  | zero =>
    by_cases hp : policy.accepts n
    · have hsome : some [n] = some factors := by
        simpa only [primeFactorListFuel, hp, ite_true] using h
      have hEq : factors = [n] := Option.some.inj hsome.symm
      rw [hEq]
      constructor
      · intro p hp
        simp only [List.mem_singleton] at hp
        subst p
        exact policy.sound n ‹policy.accepts n›
      · simp only [List.prod_cons, List.prod_nil, mul_one]
    · simp only [primeFactorListFuel, hp, ite_false, reduceCtorEq] at h
  | succ fuel ih =>
    by_cases hp : policy.accepts n
    · have hsome : some [n] = some factors := by
        simpa only [primeFactorListFuel, hp, ite_true] using h
      have hEq : factors = [n] := Option.some.inj hsome.symm
      rw [hEq]
      exact
        ⟨by
          intro p hp
          simp only [List.mem_singleton] at hp
          subst p
          exact policy.sound n ‹policy.accepts n›, by
          simp only [List.prod_cons, List.prod_nil, mul_one]⟩
    · cases hfind : findFactor n params (fuel + 1) with
      | none => simp only [primeFactorListFuel, hp, hfind, ite_false, reduceCtorEq] at h
      | some
        d =>
        have hroot :
          (match primeFactorListFuel policy params fuel d,
              primeFactorListFuel policy params fuel (n / d) with
            | some left, some right => some (left ++ right)
            | _, _ => none) =
            some factors := by
          simpa only [primeFactorListFuel, hp, hfind, ite_false] using h
        have hsplit := findFactor_sound hfind
        change 1 < d ∧ d < n ∧ d ∣ n at hsplit
        have hmul : d * (n / d) = n := Nat.mul_div_cancel' hsplit.2.2
        have hrpos : 0 < n / d := by
          by_contra hzero
          have hz : n / d = 0 := Nat.eq_zero_of_not_pos hzero
          rw [hz, mul_zero] at hmul
          have hnpos : 0 < n := Nat.lt_trans Nat.zero_lt_one (lt_trans hsplit.1 hsplit.2.1)
          exact (Nat.ne_of_gt hnpos) hmul.symm
        have hrgt : 1 < n / d := by
          by_contra hsmall
          have hone : n / d = 1 :=
            Nat.le_antisymm (Nat.le_of_not_gt hsmall) (Nat.succ_le_iff.mpr hrpos)
          rw [hone, mul_one] at hmul
          exact (Nat.ne_of_lt hsplit.2.1) hmul
        have hrlt : n / d < n := by
          have hlt := Nat.mul_lt_mul_of_pos_right hsplit.1 hrpos
          rw [one_mul, hmul] at hlt
          exact hlt
        cases hleft : primeFactorListFuel policy params fuel d with
        | none =>
          have hnone : (none : Option (List ℕ)) = some factors := by simpa only [hleft] using hroot
          cases hnone
        | some left =>
          cases hright : primeFactorListFuel policy params fuel (n / d) with
          | none =>
            have hnone : (none : Option (List ℕ)) = some factors := by
              simpa only [hleft, hright] using hroot
            cases hnone
          | some
            right =>
            have hconcat : left ++ right = factors := by
              have hsome : some (left ++ right) = some factors := by
                simpa only [hleft, hright] using hroot
              exact Option.some.inj hsome
            rw [← hconcat]
            have hleftSpec := ih hsplit.1 hleft
            have hrightSpec := ih hrgt hright
            refine ⟨?_, ?_⟩
            · intro p hp
              rcases List.mem_append.mp hp with hp | hp
              · exact hleftSpec.1 p hp
              · exact hrightSpec.1 p hp
            · rw [List.prod_append, hleftSpec.2, hrightSpec.2, hmul]

/-- Recursively split with bounded rho attempts, retaining unresolved values in `remainder`. -/
def partialPrimeFactorSupply (policy : PrimeLeafPolicy) (params : Params) :
    ℕ → ℕ → PartialPrimeFactorSupply
  | 0, n => if policy.accepts n then ⟨[n], 1⟩ else ⟨[], n⟩
  | fuel + 1, n =>
    if policy.accepts n then ⟨[n], 1⟩
    else
      match findFactor n params (fuel + 1) with
      | none => ⟨[], n⟩
      | some d =>
        let left := partialPrimeFactorSupply policy params fuel d
        let right := partialPrimeFactorSupply policy params fuel (n / d)
        ⟨left.factors ++ right.factors, left.remainder * right.remainder⟩
termination_by fuel _ => fuel

/-- Every retained factor is prime, and the known factors times the residual cofactor equal the
input. The identity remains valid when rho stops at any unresolved composite leaf. -/
theorem partialPrimeFactorSupply_sound (policy : PrimeLeafPolicy) (params : Params) (fuel : ℕ) :
    ∀ n : ℕ,
      (∀ p, p ∈ (partialPrimeFactorSupply policy params fuel n).factors → Nat.Prime p) ∧
        (partialPrimeFactorSupply policy params fuel n).factors.prod *
            (partialPrimeFactorSupply policy params fuel n).remainder =
          n := by
  induction fuel with
  | zero =>
    intro n
    by_cases hprime : policy.accepts n
    · simp only [partialPrimeFactorSupply, hprime, ite_true]
      constructor
      · intro p hp
        have hpn : p = n := List.mem_singleton.mp hp
        simpa only [hpn] using policy.sound n hprime
      · simp only [List.prod_cons, List.prod_nil, Nat.mul_one]
    · simp only [partialPrimeFactorSupply, hprime, ite_false]
      constructor
      · intro p hp
        exact False.elim (List.not_mem_nil hp)
      · rw [List.prod_nil, Nat.one_mul]
  | succ fuel ih =>
    intro n
    by_cases hprime : policy.accepts n
    · simp only [partialPrimeFactorSupply, hprime, ite_true]
      constructor
      · intro p hp
        have hpn : p = n := List.mem_singleton.mp hp
        simpa only [hpn] using policy.sound n hprime
      · simp only [List.prod_cons, List.prod_nil, Nat.mul_one]
    · cases hfind : findFactor n params (fuel + 1) with
      | none =>
        simp only [partialPrimeFactorSupply, hprime, ite_false, hfind]
        constructor
        · intro p hp
          exact False.elim (List.not_mem_nil hp)
        · rw [List.prod_nil, Nat.one_mul]
      | some divisor =>
        have hdivisor := findFactor_sound hfind
        change 1 < divisor ∧ divisor < n ∧ divisor ∣ n at hdivisor
        have hsplit : divisor * (n / divisor) = n := Nat.mul_div_cancel' hdivisor.2.2
        have hleft := ih divisor
        have hright := ih (n / divisor)
        simp only [partialPrimeFactorSupply, ite_eq_right hprime, hfind, List.prod_append]
        constructor
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hleft.1 p hp
          · exact hright.1 p hp
        · calc
            (partialPrimeFactorSupply policy params fuel divisor).factors.prod *
                  (partialPrimeFactorSupply policy params fuel (n / divisor)).factors.prod *
                  ((partialPrimeFactorSupply policy params fuel divisor).remainder *
                    (partialPrimeFactorSupply policy params fuel (n / divisor)).remainder) =
                ((partialPrimeFactorSupply policy params fuel divisor).factors.prod *
                    (partialPrimeFactorSupply policy params fuel divisor).remainder) *
                  ((partialPrimeFactorSupply policy params fuel (n / divisor)).factors.prod *
                    (partialPrimeFactorSupply policy params fuel (n / divisor)).remainder) :=
              by ac_rfl
            _ = divisor * (n / divisor) := by rw [hleft.2, hright.2]
            _ = n := hsplit

/-- Execute a partial factor supply according to an explicit whole-tree budget. -/
def partialPrimeFactorSupplyByTree (policy : PrimeLeafPolicy) (params : Params) :
    RhoBudgetTree → ℕ → PartialPrimeFactorSupply
  | .leaf, n => if policy.accepts n then ⟨[n], 1⟩ else ⟨[], n⟩
  | .split fuel left right, n =>
    if policy.accepts n then ⟨[n], 1⟩
    else
      match findFactor n params fuel with
      | none => ⟨[], n⟩
      | some d =>
        let leftSupply := partialPrimeFactorSupplyByTree policy params left d
        let rightSupply := partialPrimeFactorSupplyByTree policy params right (n / d)
        ⟨leftSupply.factors ++ rightSupply.factors, leftSupply.remainder * rightSupply.remainder⟩

/-- A tree-guided supply retains only prime leaves and preserves the represented input exactly. -/
theorem partialPrimeFactorSupplyByTree_sound (policy : PrimeLeafPolicy) (params : Params)
    (tree : RhoBudgetTree) :
    ∀ n : ℕ,
      (∀ p, p ∈ (partialPrimeFactorSupplyByTree policy params tree n).factors → Nat.Prime p) ∧
        (partialPrimeFactorSupplyByTree policy params tree n).factors.prod *
            (partialPrimeFactorSupplyByTree policy params tree n).remainder =
          n := by
  induction tree with
  | leaf =>
    intro n
    by_cases hprime : policy.accepts n
    · simp only [partialPrimeFactorSupplyByTree, hprime, ite_true]
      constructor
      · intro p hp
        have hpn : p = n := List.mem_singleton.mp hp
        simpa only [hpn] using policy.sound n hprime
      · simp only [List.prod_cons, List.prod_nil, Nat.mul_one]
    · simp only [partialPrimeFactorSupplyByTree, hprime, ite_false]
      constructor
      · intro p hp
        exact False.elim (List.not_mem_nil hp)
      · rw [List.prod_nil, Nat.one_mul]
  | split fuel left right ihLeft ihRight =>
    intro n
    by_cases hprime : policy.accepts n
    · simp only [partialPrimeFactorSupplyByTree, hprime, ite_true]
      constructor
      · intro p hp
        have hpn : p = n := List.mem_singleton.mp hp
        simpa only [hpn] using policy.sound n hprime
      · simp only [List.prod_cons, List.prod_nil, Nat.mul_one]
    · cases hfind : findFactor n params fuel with
      | none =>
        simp only [partialPrimeFactorSupplyByTree, hprime, ite_false, hfind]
        constructor
        · intro p hp
          exact False.elim (List.not_mem_nil hp)
        · rw [List.prod_nil, Nat.one_mul]
      | some divisor =>
        have hdivisor := findFactor_sound hfind
        change 1 < divisor ∧ divisor < n ∧ divisor ∣ n at hdivisor
        have hsplit : divisor * (n / divisor) = n := Nat.mul_div_cancel' hdivisor.2.2
        have hleft := ihLeft divisor
        have hright := ihRight (n / divisor)
        simp only [partialPrimeFactorSupplyByTree, ite_eq_right hprime, hfind, List.prod_append]
        constructor
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hleft.1 p hp
          · exact hright.1 p hp
        · calc
            (partialPrimeFactorSupplyByTree policy params left divisor).factors.prod *
                  (partialPrimeFactorSupplyByTree policy params right (n / divisor)).factors.prod *
                  ((partialPrimeFactorSupplyByTree policy params left divisor).remainder *
                    (partialPrimeFactorSupplyByTree policy params right (n / divisor)).remainder) =
                ((partialPrimeFactorSupplyByTree policy params left divisor).factors.prod *
                    (partialPrimeFactorSupplyByTree policy params left divisor).remainder) *
                  ((partialPrimeFactorSupplyByTree policy params right (n / divisor)).factors.prod *
                    (partialPrimeFactorSupplyByTree policy params right (n / divisor)).remainder) :=
              by ac_rfl
            _ = divisor * (n / divisor) := by rw [hleft.2, hright.2]
            _ = n := hsplit

/-- Count actual Floyd rounds used by a tree-guided partial factor supply. -/
def partialPrimeFactorSupplyByTreeRounds (policy : PrimeLeafPolicy) (params : Params) :
    RhoBudgetTree → ℕ → ℕ
  | .leaf, _ => 0
  | .split fuel left right, n =>
    if policy.accepts n then 0
    else
      let used := findFactorRounds n params fuel
      match findFactor n params fuel with
      | none => used
      | some d =>
        used + partialPrimeFactorSupplyByTreeRounds policy params left d +
          partialPrimeFactorSupplyByTreeRounds policy params right (n / d)

/-- Actual Floyd rounds at every reached node sum to no more than all allowances in the tree. -/
theorem partialPrimeFactorSupplyByTreeRounds_le (policy : PrimeLeafPolicy) (params : Params)
    (tree : RhoBudgetTree) (n : ℕ) :
    partialPrimeFactorSupplyByTreeRounds policy params tree n ≤ tree.totalFuel := by
  induction tree generalizing n with
  | leaf => exact Nat.zero_le _
  | split fuel left right ihLeft
    ihRight =>
    by_cases hprime : policy.accepts n
    · simp only [partialPrimeFactorSupplyByTreeRounds, RhoBudgetTree.totalFuel, ite_eq_left hprime,
        Nat.zero_le]
    · cases hfind : findFactor n params fuel with
      | none =>
        have hused := findFactorRounds_le n params fuel
        simp only [partialPrimeFactorSupplyByTreeRounds, RhoBudgetTree.totalFuel,
          ite_eq_right hprime, hfind]
        calc
          _ ≤ fuel := hused
          _ ≤ fuel + left.totalFuel := Nat.le_add_right _ _
          _ ≤ fuel + left.totalFuel + right.totalFuel := Nat.le_add_right _ _
      | some divisor =>
        have hused := findFactorRounds_le n params fuel
        have hleft := ihLeft divisor
        have hright := ihRight (n / divisor)
        simp only [partialPrimeFactorSupplyByTreeRounds, RhoBudgetTree.totalFuel,
          ite_eq_right hprime, hfind]
        exact Nat.add_le_add (Nat.add_le_add hused hleft) hright

end PollardRho

end PseudoPrime.NumberTheory.Factorization
