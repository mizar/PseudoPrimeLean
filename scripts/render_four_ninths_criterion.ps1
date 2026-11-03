$projectRoot = Split-Path -Parent $PSScriptRoot
$inputFile = Join-Path $projectRoot 'ComparatorChallenges/PrimeMillerRabinFourNinthsCriterion.md'
$outputFile = Join-Path $projectRoot 'ComparatorChallenges/PrimeMillerRabinFourNinthsCriterion.png'

& npx -y '@marp-team/marp-cli' --images png $inputFile --html --allow-local-files --image-scale 2 -o $outputFile
exit $LASTEXITCODE
