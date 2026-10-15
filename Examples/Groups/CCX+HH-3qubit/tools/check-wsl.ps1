param([string[]]$Targets)

$ErrorActionPreference = 'Stop'
$taskRepo = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../..'))
Set-Location -LiteralPath $taskRepo
$development = 'Examples/Groups/CCX+HH-3qubit'
$libraryList = "$development/tools/libraries-wsl"
$checkLogs = Join-Path $taskRepo 'local/ccxhh-3qubit-checks'
New-Item -ItemType Directory -Path $checkLogs -Force | Out-Null

if (-not $Targets) {
    $Targets = @("$development/CircuitLemmas.agda")
    $Targets += @(Get-ChildItem "$development/MissingK/Evaluations/E*.agda" |
        ForEach-Object { $_.FullName.Substring($taskRepo.Length + 1).Replace('\', '/') })
    $Targets += @("$development/MissingK.agda", "$development/Repaired/Encoding.agda",
        "$development/Repaired/Soundness.agda", "$development/Repaired/EncodingMatrices.agda")
    $Targets += @('r1a', 'r1b', 'r1c', 'r2a', 'r2b', 'r2c', 'r2d', 'r2e', 'r2f',
        'r3a', 'r3b', 'r3c', 'r3d', 'r3e', 'r3f', 'r3g', 'r4a', 'r4b', 'r4c', 'r5a', 'r6a') |
        ForEach-Object { "$development/Transport/$_.agda" }
    $Targets += "$development/TwoLevel.agda"
    foreach ($pattern in @('FrameEvaluation/E*.agda', 'DecodeMatrices/*.agda')) {
        $Targets += @(Get-ChildItem "$development/$pattern" |
            ForEach-Object { $_.FullName.Substring($taskRepo.Length + 1).Replace('\', '/') })
    }
    $Targets += @("$development/Repaired/DecodingMatrices.agda",
        "$development/Repaired/DyadicCompleteness.agda")
    $Targets += @(Get-ChildItem "$development/HadamardRelations/*.agda" |
        ForEach-Object { $_.FullName.Substring($taskRepo.Length + 1).Replace('\', '/') })
    $Targets += @("$development/Repaired/TwoLevelScaled.agda",
        "$development/Repaired/Presentation.agda", "$development/Theorems.agda",
        'MainTheorems.agda')
}

foreach ($target in $Targets) {
    $logPath = Join-Path $checkLogs ($target.Replace('/', '-') + '.log')
    $attempt = 0
    while ($true) {
        $attempt++
        Write-Output "Checking $target (attempt $attempt)"
        # Keep the supervising process outside WSL: a WSL restart kills
        # the compiler, but it must not kill the rest of the check list.
        $ErrorActionPreference = 'Continue'
        & wsl --exec /usr/bin/agda "--library-file=$libraryList" $target `
            '+RTS' '-M3G' '-c' '-RTS' 2>&1 | Out-File -LiteralPath $logPath -Encoding utf8
        $checkExit = $LASTEXITCODE
        $ErrorActionPreference = 'Stop'
        if ($checkExit -eq 0) {
            Add-Content -LiteralPath (Join-Path $checkLogs 'passed.log') `
                -Value "Passed $target" -Encoding utf8
            break
        }
        $diagnostic = Get-Content -LiteralPath $logPath -Raw -Encoding utf8
        if ($diagnostic -match 'error:|UnsolvedMetaVariables|Heap exhausted') {
            Get-Content -LiteralPath $logPath -Tail 30 -Encoding utf8 | Write-Output
            throw "Agda failed on $target (exit $checkExit)"
        }
        if ($attempt -ge 5) {
            Get-Content -LiteralPath $logPath -Tail 20 -Encoding utf8 | Write-Output
            throw "The check of $target was interrupted five times (exit $checkExit)"
        }
        Write-Output "Compiler interrupted (exit $checkExit); retrying from saved interfaces."
        Start-Sleep -Seconds 10
    }
}
