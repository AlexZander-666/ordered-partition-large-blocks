#!/usr/bin/env python3
"""Rebuild the manuscript with the same deterministic PDF metadata."""

import argparse
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

SOURCE_DATE = "1795737600"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path, help="destination PDF")
    parser.add_argument("--expect", help="expected SHA-256")
    parser.add_argument("--log", type=Path, help="save the complete two-pass TeX transcript")
    args = parser.parse_args()

    source = Path(__file__).resolve().parent / "main.tex"
    pdflatex = os.environ.get("PDFLATEX") or shutil.which("pdflatex")
    if not pdflatex:
        candidate = (Path.home() / ".cache/spark-math-research/texlive/2026/bin"
                     / "aarch64-linux/pdflatex")
        if candidate.is_file():
            pdflatex = str(candidate)
    if not pdflatex:
        parser.error("install TeX Live or point PDFLATEX to pdflatex")

    env = dict(os.environ, SOURCE_DATE_EPOCH=SOURCE_DATE, FORCE_SOURCE_DATE="1", TZ="UTC")
    log = []
    with tempfile.TemporaryDirectory(prefix="linear-prefix-tex-") as tmp:
        work = Path(tmp)
        shutil.copyfile(source, work / "main.tex")
        for pass_number in (1, 2):
            command = [pdflatex, "-interaction=nonstopmode", "-halt-on-error", "-file-line-error",
                       "main.tex"]
            result = subprocess.run(command, cwd=work, env=env, check=False, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            log.append(f"Pass {pass_number}, exit {result.returncode}\n{result.stdout}")
            if result.returncode:
                if args.log:
                    args.log.write_text("\n".join(log))
                raise SystemExit(result.stdout)
        final_log = log[-1]
        if "undefined references" in final_log or "Citation " in final_log:
            raise SystemExit(final_log)
        result_pdf = (work / "main.pdf").read_bytes()

    if args.log:
        args.log.write_text("\n".join(log))
    digest = hashlib.sha256(result_pdf).hexdigest()
    if args.expect and digest != args.expect:
        raise SystemExit(f"PDF SHA-256 mismatch: expected {args.expect}, got {digest}")
    args.output.write_bytes(result_pdf)
    print(f"{digest}  {args.output.name}")


if __name__ == "__main__":
    main()
