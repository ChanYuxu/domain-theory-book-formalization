#!/usr/bin/env python3
"""Compatibility launcher for the shared editable book reader server.

Usage:
    DOMAIN_THEORY_PDF="/path/to/Domain Theory.pdf" python3 docs/serve_chapter4.py

Chapter 4 uses the same transactional declaration editor as Chapters 2 and 3.
"""

from __future__ import annotations

from serve_chapter2 import main


if __name__ == "__main__":
    main()
