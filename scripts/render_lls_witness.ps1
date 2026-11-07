param([string] $MarpCli)

$projectRoot = Split-Path -Parent $PSScriptRoot
$inputFile = Join-Path $projectRoot 'ComparatorChallenges/LLSWitness/LLSWitnessCriterion.md'
$outputFile = Join-Path $projectRoot 'ComparatorChallenges/LLSWitness/LLSWitnessCriterion.png'
$marpArgs = @('--images', 'png', $inputFile, '--html', '--allow-local-files', '--image-scale', '2', '-o', $outputFile)

if ($MarpCli) {
    & $MarpCli @marpArgs
} else {
    & npx -y '@marp-team/marp-cli' @marpArgs
}
exit $LASTEXITCODE
