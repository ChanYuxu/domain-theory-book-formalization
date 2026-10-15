#!/usr/bin/env python3
"""Build a self-contained Windows read-only reader from `_site`."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import shutil


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SITE = ROOT / "_site"
DEFAULT_OUTPUT = ROOT / "downloads" / "DomainTheory-Reader-Windows"


BAT = r"""@echo off
setlocal
cd /d "%~dp0"
powershell.exe -NoProfile -ExecutionPolicy Bypass -File "%~dp0Start Reader.ps1"
if errorlevel 1 pause
"""


POWERSHELL = r"""$ErrorActionPreference = "Stop"

$siteRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot "reader"))
if (-not (Test-Path (Join-Path $siteRoot "index.html"))) {
    throw "reader\index.html is missing. Re-copy the complete package."
}

$listener = $null
$port = $null
foreach ($candidate in 8080..8099) {
    try {
        $probe = [Net.Sockets.TcpListener]::new([Net.IPAddress]::Loopback, $candidate)
        $probe.Start()
        $listener = $probe
        $port = $candidate
        break
    } catch {
        if ($probe) { $probe.Stop() }
    }
}
if (-not $listener) {
    throw "No free reader port was found in the range 8080-8099."
}

function Get-ContentType([string]$path) {
    switch ([IO.Path]::GetExtension($path).ToLowerInvariant()) {
        ".html" { "text/html; charset=utf-8" }
        ".css"  { "text/css; charset=utf-8" }
        ".js"   { "text/javascript; charset=utf-8" }
        ".mjs"  { "text/javascript; charset=utf-8" }
        ".json" { "application/json; charset=utf-8" }
        ".pdf"  { "application/pdf" }
        ".wasm" { "application/wasm" }
        default { "application/octet-stream" }
    }
}

function Send-Response($stream, [int]$status, [string]$reason, [string]$contentType, [byte[]]$body) {
    $header = "HTTP/1.1 $status $reason`r`nContent-Type: $contentType`r`nContent-Length: $($body.Length)`r`nCache-Control: no-store`r`nX-Content-Type-Options: nosniff`r`nConnection: close`r`n`r`n"
    $headerBytes = [Text.Encoding]::ASCII.GetBytes($header)
    $stream.Write($headerBytes, 0, $headerBytes.Length)
    if ($body.Length -gt 0) { $stream.Write($body, 0, $body.Length) }
    $stream.Flush()
}

$url = "http://127.0.0.1:$port/"
Write-Host "Domain Theory reader: $url"
Write-Host "Press Ctrl+C in this window to stop the reader."
Start-Process $url

try {
    while ($true) {
        $client = $listener.AcceptTcpClient()
        try {
            $stream = $client.GetStream()
            $reader = [IO.StreamReader]::new($stream, [Text.Encoding]::ASCII, $false, 1024, $true)
            $requestLine = $reader.ReadLine()
            while (($line = $reader.ReadLine()) -ne $null -and $line -ne "") { }

            if (-not $requestLine -or $requestLine -notmatch "^(GET|HEAD) ([^ ]+) HTTP/") {
                Send-Response $stream 400 "Bad Request" "text/plain; charset=utf-8" ([Text.Encoding]::UTF8.GetBytes("Bad request"))
                continue
            }

            $method = $Matches[1]
            $rawPath = ($Matches[2] -split "\?", 2)[0]
            $decodedPath = [Uri]::UnescapeDataString($rawPath).Replace("/", [IO.Path]::DirectorySeparatorChar)
            if ($decodedPath -eq [IO.Path]::DirectorySeparatorChar) {
                $decodedPath = [IO.Path]::DirectorySeparatorChar + "index.html"
            }
            $relativePath = $decodedPath.TrimStart([IO.Path]::DirectorySeparatorChar)
            $fullPath = [IO.Path]::GetFullPath((Join-Path $siteRoot $relativePath))
            $rootPrefix = $siteRoot.TrimEnd([IO.Path]::DirectorySeparatorChar) + [IO.Path]::DirectorySeparatorChar

            if (-not $fullPath.StartsWith($rootPrefix, [StringComparison]::OrdinalIgnoreCase) -or -not (Test-Path $fullPath -PathType Leaf)) {
                Send-Response $stream 404 "Not Found" "text/plain; charset=utf-8" ([Text.Encoding]::UTF8.GetBytes("Not found"))
                continue
            }

            $body = if ($method -eq "HEAD") { [byte[]]::new(0) } else { [IO.File]::ReadAllBytes($fullPath) }
            Send-Response $stream 200 "OK" (Get-ContentType $fullPath) $body
        } catch {
            try {
                Send-Response $stream 500 "Internal Server Error" "text/plain; charset=utf-8" ([Text.Encoding]::UTF8.GetBytes("Reader server error"))
            } catch { }
        } finally {
            $client.Close()
        }
    }
} finally {
    $listener.Stop()
}
"""


README = """DOMAIN THEORY LEAN 4 READER - WINDOWS OFFLINE PACKAGE

Open the reader
---------------
1. Keep this folder intact.
2. Double-click "Start Reader.bat".
3. Your default browser opens the local reader automatically.
4. Choose Chapters 2-9 and click a Lean marker in the PDF to view its code.
5. Press Ctrl+C in the terminal window to stop the reader.

Requirements
------------
- Windows 10 or Windows 11 with Windows PowerShell.
- No Python, Lean, TeX installation, network connection, or textbook PDF is required.

Scope and privacy
-----------------
- This package is read-only. It cannot edit Lean files or run the Lean compiler.
- It contains project-generated companion PDFs, mapped Lean declarations, and PDF.js.
- It does not contain the original Domain Theory PDF, OCR extracts, or private local paths.

Integrity
---------
SHA256SUMS.txt lists every packaged file and can be used to check that a copy is complete.
"""


def ensure_safe_output(output: Path) -> None:
    output = output.resolve()
    if output == ROOT or ROOT not in output.parents:
        raise SystemExit(f"Refusing unsafe output path: {output}")


def checksum(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_checksums(output: Path) -> None:
    files = sorted(
        path for path in output.rglob("*")
        if path.is_file() and path.name != "SHA256SUMS.txt"
    )
    lines = [f"{checksum(path)}  {path.relative_to(output).as_posix()}" for path in files]
    (output / "SHA256SUMS.txt").write_text("\n".join(lines) + "\n", encoding="ascii")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--site", type=Path, default=DEFAULT_SITE)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--no-zip", action="store_true")
    args = parser.parse_args()

    site = args.site.expanduser().resolve()
    output = args.output.expanduser().resolve()
    ensure_safe_output(output)
    if not (site / "index.html").is_file():
        raise SystemExit(f"Missing built public site: {site}; run docs/build_public_site.py")

    if output.exists():
        shutil.rmtree(output)
    output.mkdir(parents=True)
    shutil.copytree(
        site,
        output / "reader",
        ignore=shutil.ignore_patterns("*.tex", ".nojekyll"),
    )
    (output / "Start Reader.bat").write_text(BAT, encoding="ascii", newline="\r\n")
    (output / "Start Reader.ps1").write_text(POWERSHELL, encoding="ascii", newline="\r\n")
    (output / "README.txt").write_text(README, encoding="ascii", newline="\r\n")
    write_checksums(output)
    print(f"Built {output.relative_to(ROOT)}")

    if not args.no_zip:
        archive = output.with_suffix(".zip")
        if archive.exists():
            archive.unlink()
        shutil.make_archive(str(output), "zip", root_dir=output.parent, base_dir=output.name)
        print(f"Built {archive.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
