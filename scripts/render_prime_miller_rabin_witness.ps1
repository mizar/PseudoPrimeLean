$projectRoot = Split-Path -Parent $PSScriptRoot
$inputFile = Join-Path $projectRoot 'ComparatorChallenges/PrimeMillerRabinWitness/PrimeMillerRabinWitnessCriterion.md'
$outputFile = Join-Path $projectRoot 'ComparatorChallenges/PrimeMillerRabinWitness/PrimeMillerRabinWitnessCriterion.png'

& npx -y '@marp-team/marp-cli' --images png $inputFile --html --allow-local-files --image-scale 2 -o $outputFile
exit $LASTEXITCODE
