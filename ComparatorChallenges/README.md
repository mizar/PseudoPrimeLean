# Comparator challenges

Run the four-ninths criterion challenge from the project root with Lean 4.35's
built-in comparator on Linux with `bwrap` available:

```sh
lake comparator --config=ComparatorChallenges/PrimeMillerRabinFourNinthsCriterion.json
```

The challenge states the GRH-conditional criterion independently of the library proof. The
solution repeats the challenge declarations under the same names and applies the proof from
`PrimeTestBounds/MillerRabin/FourNinthsCriterion.lean`. Comparator checks the two modules in
separate environments; do not import the challenge into the solution. The challenge theorem's
`sorry` is a placeholder and is not part of the solution's proof.

The allowed axioms are `propext`, `Quot.sound`, and `Classical.choice`. GRH is an explicit
assumption in the statement, not an allowed axiom. The configuration contains no definition
holes: the definitions used in the statement are part of the fixed challenge.
