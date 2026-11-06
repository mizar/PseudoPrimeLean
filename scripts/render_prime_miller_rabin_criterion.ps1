$projectRoot = Split-Path -Parent $PSScriptRoot
$inputFile = Join-Path $projectRoot 'ComparatorChallenges/PrimeMillerRabinCriterion.md'
$outputFile = Join-Path $projectRoot 'ComparatorChallenges/PrimeMillerRabinCriterion.png'

& npx -y '@marp-team/marp-cli' --images png $inputFile --html --allow-local-files --image-scale 2 -o $outputFile
exit $LASTEXITCODE
