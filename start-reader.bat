@echo off
cd /d "%~dp0"
py -3 docs\start_reader.py %*
if errorlevel 1 pause
