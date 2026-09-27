import PseudoPrime.PrimeTest.MillerRabin.Computation.Small
import PseudoPrime.PrimeTest.MillerRabin.Prime
import PseudoPrime.PrimeTest.Result
/-!
# Certified primality from bases two and three below 3000
Extract the finite classification without importing logarithmic estimates or GRH.
The runtime checker uses only the existing Miller-Rabin computations, with direct cases below four.
-/
namespace PseudoPrime.PrimeTest.MillerRabin
/-- An odd input between one and 3000 passing both bases is prime.
The finite composite-rejection theorem rules out non-primality by contradiction.
The bound is strict and belongs to the existing finite certificate, not a general MR bound. -/
theorem prime_of_basesTwoThree_of_lt_3000 {n : ℕ} (hn : 1 < n) (hodd : Odd n)
    (hlt : n < 3000) (h2 : strongMillerRabinWithBase n 2 = true)
    (h3 : strongMillerRabinWithBase n 3 = true) : Nat.Prime n := by
  by_contra hnot
  rcases base_two_or_three_rejects_of_lt_3000 hn hodd hnot hlt with h | h
  · exact Bool.noConfusion (h.symm.trans h2)
  · exact Bool.noConfusion (h.symm.trans h3)
/-- Compare bases two and three after handling zero through three and rejecting even inputs.
This is a probable-prime comparison at arbitrary n; its converse is proved only below 3000.
The small branch also avoids rejecting the prime three at a base equal to itself. -/
def checkBasesTwoThree (n : ℕ) : Bool :=
  if n ≤ 3 then decide (Nat.Prime n)
  else decide (Odd n) && strongMillerRabinWithBase n 2 && strongMillerRabinWithBase n 3
/-- Below 3000, acceptance proves primality, including the direct cases two and three.
For larger odd inputs the extracted two-base theorem supplies the proof. -/
theorem checkBasesTwoThree_sound {n : ℕ} (hlt : n < 3000)
    (h : checkBasesTwoThree n = true) : Nat.Prime n := by
  unfold checkBasesTwoThree at h
  split at h
  · exact of_decide_eq_true h
  · rename_i hn
    obtain ⟨hleft, h3⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hodd, h2⟩ := Bool.and_eq_true_iff.mp hleft
    exact prime_of_basesTwoThree_of_lt_3000
      (lt_trans (by decide : 1 < 3) (Nat.lt_of_not_ge hn))
      (of_decide_eq_true hodd) hlt h2 h3
/-- Every prime passes the two-base checker, with no size restriction.
Above three both bases are coprime to the prime; the smaller cases are handled directly. -/
theorem checkBasesTwoThree_of_prime {n : ℕ} (hp : Nat.Prime n) :
    checkBasesTwoThree n = true := by
  unfold checkBasesTwoThree
  split
  · exact decide_eq_true hp
  · rename_i hn
    have hgt : 3 < n := Nat.lt_of_not_ge hn
    have h2 : n ≠ 2 := Nat.ne_of_gt (lt_trans (by decide : 2 < 3) hgt)
    have h3 : Nat.Coprime 3 n :=
      (Nat.coprime_primes (by decide : Nat.Prime 3) hp).mpr (Nat.ne_of_lt hgt)
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true (hp.odd_of_ne_two h2),
        strongMillerRabinBase2_of_prime_of_ne_two hp h2⟩,
        strongMillerRabinWithBase_of_prime hp h3⟩

/-- In the certified finite range the executable comparison is equivalent to primality.
This is the exact finite decision contract, independent of trial division at runtime above three. -/
theorem checkBasesTwoThree_iff {n : ℕ} (hlt : n < 3000) :
    checkBasesTwoThree n = true ↔ Nat.Prime n := by
  exact ⟨checkBasesTwoThree_sound hlt, checkBasesTwoThree_of_prime⟩
/-- Decide primality below 3000 using bases two and three and attach the corresponding proof.
Inputs zero and one are notPrime, two and three are prime; inputs at least 3000 are unknown.
The upper guard runs before either modular test and does not extrapolate the finite certificate. -/
def decideBasesTwoThree (n : ℕ) : Decision n :=
  if hlt : n < 3000 then
    if h : checkBasesTwoThree n = true then .prime (checkBasesTwoThree_sound hlt h)
    else .notPrime (fun hp ↦ h (checkBasesTwoThree_of_prime hp))
  else .unknown
/-- The finite entry gives the exact primality Boolean below 3000 and none outside that range.
The proof-side Nat.Prime decision specifies the result; runtime uses the two-base checker. -/
theorem decideBasesTwoThree_toOption (n : ℕ) :
    (decideBasesTwoThree n).toOption =
      if n < 3000 then some (decide (Nat.Prime n)) else none := by
  unfold decideBasesTwoThree
  split
  · rename_i hlt
    split
    · rename_i hc
      simp only [Decision.toOption,
        checkBasesTwoThree_sound hlt hc, decide_true]
    · rename_i hc
      have hn : ¬ Nat.Prime n := fun hp ↦ hc (checkBasesTwoThree_of_prime hp)
      simp only [Decision.toOption, hn, decide_false]
  · rfl
end PseudoPrime.PrimeTest.MillerRabin
