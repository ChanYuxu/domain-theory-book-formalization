#!/usr/bin/env python3
"""Compatibility launcher for the shared editable book reader server.

Usage:
    DOMAIN_THEORY_PDF="/path/to/Domain Theory.pdf" python3 docs/serve_chapter4.py

This launcher uses the shared transactional declaration editor for Chapters 2-9.
"""

from __future__ import annotations

from serve_chapter2 import main


if __name__ == "__main__":
    main()
