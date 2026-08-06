@echo off
cd /d "%~dp0"
echo Baue Mediathek Downloader.exe ...
pyinstaller "Mediathek Downloader.spec" --noconfirm
echo.
if exist "dist\Mediathek Downloader.exe" (
    echo FERTIG! EXE liegt in: dist\Mediathek Downloader.exe
) else (
    echo FEHLER beim Bauen!
)
pause
