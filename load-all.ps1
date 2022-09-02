#!/usr/bin/pwsh

$sourceFiles = Get-ChildItem -Path ./src  -Filter *.agda -Recurse -File
$testFiles   = Get-ChildItem -Path ./test -Filter *.agda -Recurse -File

function Load-Agda-File {
  param (
      [Parameter(Mandatory,
                 Position=0,
                 ValueFromPipeline,
                 HelpMessage="The path of the Agda file to load.")]
      [ValidateNotNullOrEmpty()]
      [string[]]
      $File
  )

  PROCESS {
    $fileName = Split-Path -Leaf $File
    Write-Host ("Loading $fileName ($File)") -ForegroundColor Cyan
    Push-Location
    Set-Location (Split-Path $File)
    agda $File
    if ($LastExitCode -ne 0) {
      Write-Host 'Non-zero exit code detected!' -ForegroundColor Red
    }
    Pop-Location
  }
}

Write-Host 'Loading source files' -ForegroundColor Magenta
$sourceFiles | Load-Agda-File
Write-Host 'Loading test files' -ForegroundColor Magenta
$testFiles   | Load-Agda-File
