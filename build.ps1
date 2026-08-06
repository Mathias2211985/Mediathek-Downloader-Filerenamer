# ============================================================
#  Mediathek Downloader – Build-Skript
#  Erstellt eine standalone .exe (kein Python nötig)
# ============================================================

$ErrorActionPreference = "Stop"
$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
Set-Location $ScriptDir

Write-Host ""
Write-Host "========================================" -ForegroundColor Cyan
Write-Host "  Mediathek Downloader  –  Build" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
Write-Host ""

# ── Python prüfen ────────────────────────────────────────────
try {
    $pyVer = python --version 2>&1
    Write-Host "[OK] $pyVer" -ForegroundColor Green
} catch {
    Write-Host "[FEHLER] Python nicht gefunden!" -ForegroundColor Red
    Write-Host "         Bitte installieren: https://python.org" -ForegroundColor Yellow
    Read-Host "Enter drücken zum Beenden"
    exit 1
}

# ── pip-Pakete installieren ───────────────────────────────────
Write-Host ""
Write-Host "[1/3] Installiere Abhängigkeiten (requests, pyinstaller)..." -ForegroundColor Yellow
python -m pip install --upgrade pip --quiet
python -m pip install requests pyinstaller tkinterdnd2 Pillow --quiet

if ($LASTEXITCODE -ne 0) {
    Write-Host "[FEHLER] pip install fehlgeschlagen." -ForegroundColor Red
    Read-Host "Enter drücken zum Beenden"
    exit 1
}
Write-Host "      fertig." -ForegroundColor Green

# ── Alte Build-Artefakte aufräumen ────────────────────────────
Write-Host ""
Write-Host "[2/3] Räume alte Build-Dateien auf..." -ForegroundColor Yellow
if (Test-Path "build")              { Remove-Item -Recurse -Force "build" }
if (Test-Path "dist")               { Remove-Item -Recurse -Force "dist"  }
if (Test-Path "Mediathek Downloader.spec") { Remove-Item -Force "Mediathek Downloader.spec" }
Write-Host "      fertig." -ForegroundColor Green

# ── PyInstaller ausführen ────────────────────────────────────
Write-Host ""
Write-Host "[3/3] Baue .exe (kann 1-2 Minuten dauern)..." -ForegroundColor Yellow
Write-Host ""

pyinstaller `
    --onefile `
    --windowed `
    --name "Mediathek Downloader" `
    --clean `
    mediathek_downloader.py

if ($LASTEXITCODE -ne 0) {
    Write-Host ""
    Write-Host "[FEHLER] Build fehlgeschlagen." -ForegroundColor Red
    Read-Host "Enter drücken zum Beenden"
    exit 1
}

# ── Ergebnis ─────────────────────────────────────────────────
$exePath = Join-Path $ScriptDir "dist\Mediathek Downloader.exe"
$exeSize = [math]::Round((Get-Item $exePath).Length / 1MB, 1)

Write-Host ""
Write-Host "========================================" -ForegroundColor Green
Write-Host "  Fertig!" -ForegroundColor Green
Write-Host "========================================" -ForegroundColor Green
Write-Host ""
Write-Host "  Datei: dist\Mediathek Downloader.exe" -ForegroundColor White
Write-Host "  Größe: $exeSize MB" -ForegroundColor White
Write-Host ""
Write-Host "  Die .exe läuft auf jedem Windows-PC" -ForegroundColor Gray
Write-Host "  ohne Python-Installation." -ForegroundColor Gray
Write-Host ""

# Aufräumen (build-Ordner und .spec werden nicht mehr gebraucht)
Remove-Item -Recurse -Force "build" -ErrorAction SilentlyContinue
Remove-Item -Force "Mediathek Downloader.spec" -ErrorAction SilentlyContinue

Read-Host "Enter drücken zum Beenden"
