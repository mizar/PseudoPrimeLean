/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Factorization.PollardRho.Orbit

/-!
# Pollard rho retry schedules and fuel accounting

This file specifies retry failure/success and proves that the executed Floyd rounds are bounded by
the sum of the caller-provided fuel budgets.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory.Factorization.PollardRho

/-- The configured total round budget of a retry schedule. -/
def fuelBudget : List Attempt → ℕ
  | [] => 0
  | attempt :: attempts => attempt.fuel + fuelBudget attempts

/-- Number of Floyd rounds taken by the bounded search state, counting the round that stops it. -/
def searchRounds (n c fuel : ℕ) (x y : ZMod n) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
    let x' := step n c x
    let y' := step n c (step n c y)
    let d := Nat.gcd (x' - y').val n
    if d = 1 then searchRounds n c fuel x' y' + 1 else 1
termination_by fuel

/-- Floyd never uses more rounds than the supplied fuel. -/
theorem searchRounds_le_fuel (n c fuel : ℕ) (x y : ZMod n) : searchRounds n c fuel x y ≤ fuel := by
  induction fuel generalizing x y with
  | zero => simp only [searchRounds, Nat.zero_le]
  | succ fuel ih =>
    simp only [searchRounds]
    let x' := step n c x
    let y' := step n c (step n c y)
    let d := Nat.gcd (x' - y').val n
    by_cases hd : d = 1
    · simp only [x', y', d, ite_eq_left hd]
      exact Nat.add_le_add_right (ih x' y') 1
    · simp only [x', y', d, ite_eq_right hd]
      exact Nat.succ_le_succ (Nat.zero_le fuel)

/-- Round count for one public attempt; input prechecks consume no Floyd rounds. -/
def findFactorRounds (n : ℕ) (params : Params) (fuel : ℕ) : ℕ :=
  if n ≤ 2 then 0
  else
    if n % 2 = 0 then 0
    else searchRounds n params.c fuel (params.seed : ZMod n) (params.seed : ZMod n)

/-- One public attempt stays within its own round budget. -/
theorem findFactorRounds_le (n : ℕ) (params : Params) (fuel : ℕ) :
    findFactorRounds n params fuel ≤ fuel := by
  by_cases hn : n ≤ 2
  · simp only [findFactorRounds, hn, ite_true, Nat.zero_le]
  · by_cases he : n % 2 = 0
    · simp only [findFactorRounds, hn, he, ite_false, ite_true, Nat.zero_le]
    · simp only [findFactorRounds, ite_eq_right hn, ite_eq_right he]
      exact searchRounds_le_fuel n params.c fuel (params.seed : ZMod n) (params.seed : ZMod n)

/-- Round count of a retry schedule, including attempts through the first success. -/
def findFactorManyRounds (n : ℕ) : List Attempt → ℕ
  | [] => 0
  | attempt :: attempts =>
    let used := findFactorRounds n attempt.params attempt.fuel
    match findFactor n attempt.params attempt.fuel with
    | some _ => used
    | none => used + findFactorManyRounds n attempts

/-- The actual retry prefix is bounded by the sum of all configured fuel budgets. -/
theorem findFactorManyRounds_le (n : ℕ) (attempts : List Attempt) :
    findFactorManyRounds n attempts ≤ fuelBudget attempts := by
  induction attempts with
  | nil => rfl
  | cons attempt attempts ih =>
    simp only [findFactorManyRounds, fuelBudget]
    let used := findFactorRounds n attempt.params attempt.fuel
    have hu : used ≤ attempt.fuel := findFactorRounds_le n attempt.params attempt.fuel
    cases h : findFactor n attempt.params attempt.fuel with
    | some d =>
      change used ≤ attempt.fuel + fuelBudget attempts
      exact Nat.le_trans hu (Nat.le_add_right _ _)
    | none =>
      change used + findFactorManyRounds n attempts ≤ attempt.fuel + fuelBudget attempts
      exact Nat.add_le_add hu ih

/-- A retry schedule returns `none` exactly when every listed attempt returns `none`. -/
theorem findFactorMany_eq_none_iff (n : ℕ) (attempts : List Attempt) :
    findFactorMany n attempts = none ↔
      ∀ attempt, attempt ∈ attempts → findFactor n attempt.params attempt.fuel = none := by
  induction attempts with
  | nil =>
    constructor
    · intro _ attempt hmem
      cases hmem
    · intro _
      rfl
  | cons head tail ih =>
    simp only [findFactorMany]
    cases h : findFactor n head.params head.fuel with
    | none => simp only [h, ih, List.forall_mem_cons, true_and]
    | some d => simp only [h, List.forall_mem_cons, Option.some_ne_none, false_and]

/-- If some listed attempt succeeds, the whole schedule returns some factor. -/
theorem findFactorMany_some_of_mem (n : ℕ) (attempts : List Attempt)
    (h : ∃ attempt, attempt ∈ attempts ∧ ∃ d, findFactor n attempt.params attempt.fuel = some d) :
    ∃ d, findFactorMany n attempts = some d := by
  induction attempts with
  | nil =>
    rcases h with ⟨attempt, hmem, d, hd⟩
    cases hmem
  | cons head tail ih =>
    obtain ⟨attempt, hmem, d, hd⟩ := h
    simp only [List.mem_cons] at hmem
    cases hhead : findFactor n head.params head.fuel with
    | some factor => exact ⟨factor, by simp only [findFactorMany, hhead]⟩
    | none =>
      have htail : ∃ d, findFactorMany n tail = some d := by
        apply ih
        by_cases heq : attempt = head
        · subst attempt
          simp only [hhead] at hd
          cases hd
        · exact ⟨attempt, hmem.resolve_left heq, d, hd⟩
      obtain ⟨factor, hfactor⟩ := htail
      exact ⟨factor, by simp only [findFactorMany, hhead, hfactor]⟩

end PseudoPrime.NumberTheory.Factorization.PollardRho
