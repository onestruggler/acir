param([string[]]$Targets, [string]$Heap = '8G')

$ErrorActionPreference = 'Stop'
$taskRepo = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../..'))
Set-Location -LiteralPath $taskRepo
$development = 'Examples/Groups/CCX+HH-3qubit'
$libraryList = "$development/tools/libraries-wsl"
$checkLogs = Join-Path $taskRepo 'local/ccxhh-3qubit-checks'
New-Item -ItemType Directory -Path $checkLogs -Force | Out-Null

if (-not $Targets) {
    # These seven reach every module of the directory; Theorems reaches
    # the transport, the decoding, dyadic completeness, the Hadamard
    # relations and the presentation, in one process (peak about 6.5 GB).
    $Targets = @('CircuitLemmas', 'MissingK', 'Theorems',
        'FrameChecks', 'RepresentativeChecks', 'StrictMatrix', 'TransportCaseChecks') |
        ForEach-Object { "$development/$_.agda" }
    $Targets += 'MainTheorems.agda'
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
            '+RTS' "-M$Heap" '-c' '-RTS' 2>&1 | Out-File -LiteralPath $logPath -Encoding utf8
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
