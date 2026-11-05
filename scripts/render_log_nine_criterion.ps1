$projectRoot = Split-Path -Parent $PSScriptRoot
$inputFile = Join-Path $projectRoot 'ComparatorChallenges/PrimeMillerRabinLogNineCriterion.md'
$outputFile = Join-Path $projectRoot 'ComparatorChallenges/PrimeMillerRabinLogNineCriterion.png'

& npx -y '@marp-team/marp-cli' --images png $inputFile --html --allow-local-files --image-scale 2 -o $outputFile
exit $LASTEXITCODE
