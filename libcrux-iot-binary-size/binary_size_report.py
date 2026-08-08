#!/usr/bin/env python3
"""Compile every ML-KEM / ML-DSA variant+operation for each release profile and
report binary section sizes and `cargo bloat` breakdowns.

For each scheme variant (e.g. mlkem768), each operation (keygen / encaps /
decaps / sign / verify) and each profile (release, release-small) this script:

  1. builds the `libcrux-iot-binary-size` firmware with the matching cargo
     features,
  2. records the ELF section sizes via `rust-size -A` (llvm-size),
  3. runs `cargo bloat` for a per-function and a per-crate breakdown.

Results are printed as summary tables and written to an output directory:
  - summary.md   : human-readable section-size tables
  - results.json : machine-readable section sizes for every build
  - bloat/*.txt  : raw `cargo bloat` output per build

Usage:
    python3 binary_size_report.py [--out DIR] [--bloat-n N] [--clean]
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

CRATE_DIR = Path(__file__).resolve().parent
BIN_NAME = "libcrux-iot-binary-size"
TARGET = "thumbv7em-none-eabihf"

PROFILES = ["release", "release-small"]

# scheme -> (variant features, operation features)
SCHEMES = {
    "ml-kem": {
        "variants": ["mlkem512", "mlkem768", "mlkem1024"],
        "operations": ["mlkem-keygen", "mlkem-encaps", "mlkem-decaps"],
    },
    "ml-dsa": {
        "variants": ["mldsa44", "mldsa65", "mldsa87"],
        "operations": ["mldsa-keygen", "mldsa-sign", "mldsa-verify"],
    },
}


@dataclass
class Build:
    scheme: str
    variant: str
    operation: str
    profile: str

    @property
    def features(self) -> str:
        return f"{self.variant},{self.operation}"

    @property
    def name(self) -> str:
        return f"{self.variant}_{self.operation}_{self.profile}"

    @property
    def elf_path(self) -> Path:
        return CRATE_DIR / "target" / TARGET / self.profile / BIN_NAME


@dataclass
class Result:
    build: Build
    sections: dict[str, int] = field(default_factory=dict)
    total: int = 0
    bloat_functions: str = ""
    bloat_crates: str = ""
    error: str = ""


def all_builds() -> list[Build]:
    builds = []
    for scheme, cfg in SCHEMES.items():
        for variant in cfg["variants"]:
            for operation in cfg["operations"]:
                for profile in PROFILES:
                    builds.append(Build(scheme, variant, operation, profile))
    return builds


def run(cmd: list[str]) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd,
        cwd=CRATE_DIR,
        capture_output=True,
        text=True,
    )


def cargo_build(build: Build) -> subprocess.CompletedProcess:
    return run(
        [
            "cargo",
            "build",
            "--profile",
            build.profile,
            "--no-default-features",
            "--features",
            build.features,
        ]
    )


def parse_size(elf: Path) -> tuple[dict[str, int], int]:
    """Return (section -> size, total) from `rust-size -A`."""
    proc = run(["rust-size", "-A", str(elf)])
    if proc.returncode != 0:
        raise RuntimeError(f"rust-size failed: {proc.stderr.strip()}")
    sections: dict[str, int] = {}
    total = 0
    for line in proc.stdout.splitlines():
        parts = line.split()
        # lines look like: ".text   62292   134218752"  or  "Total   63769"
        if len(parts) >= 2 and parts[0].startswith("."):
            try:
                sections[parts[0]] = int(parts[1])
            except ValueError:
                continue
        elif len(parts) == 2 and parts[0] == "Total":
            total = int(parts[1])
    if total == 0:
        total = sum(sections.values())
    return sections, total


def cargo_bloat(build: Build, extra: list[str]) -> str:
    proc = run(
        [
            "cargo",
            "bloat",
            "--profile",
            build.profile,
            "--no-default-features",
            "--features",
            build.features,
            *extra,
        ]
    )
    out = proc.stdout
    if proc.returncode != 0:
        out += "\n[stderr]\n" + proc.stderr
    # Strip the noisy compile/analyze lines for readability.
    keep = [
        ln
        for ln in out.splitlines()
        if not re.match(r"\s*(Compiling|Finished|Analyzing|Building)\b", ln)
    ]
    return "\n".join(keep).strip()


# Sections that make up flash (code + read-only data) vs RAM.
FLASH_SECTIONS = {".vector_table", ".text", ".rodata", ".gnu.sgstubs"}
RAM_SECTIONS = {".data", ".bss", ".uninit"}


def flash_size(sections: dict[str, int]) -> int:
    return sum(v for k, v in sections.items() if k in FLASH_SECTIONS)


def ram_size(sections: dict[str, int]) -> int:
    return sum(v for k, v in sections.items() if k in RAM_SECTIONS)


def fmt(n: int) -> str:
    return f"{n:,}"


def build_summary_table(results: list[Result], scheme: str) -> str:
    rows = [r for r in results if r.build.scheme == scheme and not r.error]
    if not rows:
        return ""
    header = (
        "| variant | operation | profile | .text | .rodata | flash total | RAM | size total |\n"
        "|---|---|---|---:|---:|---:|---:|---:|\n"
    )
    lines = []
    for r in rows:
        s = r.sections
        lines.append(
            "| {v} | {op} | {p} | {text} | {rodata} | {flash} | {ram} | {total} |".format(
                v=r.build.variant,
                op=r.build.operation,
                p=r.build.profile,
                text=fmt(s.get(".text", 0)),
                rodata=fmt(s.get(".rodata", 0)),
                flash=fmt(flash_size(s)),
                ram=fmt(ram_size(s)),
                total=fmt(r.total),
            )
        )
    return f"### {scheme}\n\n" + header + "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=Path,
        default=CRATE_DIR / "binary-size-report",
        help="output directory (default: ./binary-size-report)",
    )
    parser.add_argument(
        "--bloat-n",
        type=int,
        default=20,
        help="number of functions to show in cargo bloat (default: 20)",
    )
    parser.add_argument(
        "--clean",
        action="store_true",
        help="run `cargo clean` before starting",
    )
    args = parser.parse_args()

    out_dir: Path = args.out
    bloat_dir = out_dir / "bloat"
    bloat_dir.mkdir(parents=True, exist_ok=True)

    if args.clean:
        print("cargo clean ...")
        run(["cargo", "clean"])

    builds = all_builds()
    results: list[Result] = []

    for i, build in enumerate(builds, 1):
        print(f"[{i}/{len(builds)}] {build.name} (features: {build.features})")
        result = Result(build)

        proc = cargo_build(build)
        if proc.returncode != 0:
            result.error = f"build failed:\n{proc.stderr.strip()}"
            print(f"    BUILD FAILED\n{proc.stderr.strip()}")
            results.append(result)
            continue

        try:
            result.sections, result.total = parse_size(build.elf_path)
        except RuntimeError as e:
            result.error = str(e)
            print(f"    {e}")
            results.append(result)
            continue

        print(
            f"    .text={fmt(result.sections.get('.text', 0))}  "
            f"flash={fmt(flash_size(result.sections))}  "
            f"total={fmt(result.total)} bytes"
        )

        result.bloat_functions = cargo_bloat(build, ["-n", str(args.bloat_n)])
        result.bloat_crates = cargo_bloat(build, ["--crates"])

        bloat_file = bloat_dir / f"{build.name}.txt"
        bloat_file.write_text(
            f"# {build.name}\n# features: {build.features}\n\n"
            f"## functions (cargo bloat -n {args.bloat_n})\n\n{result.bloat_functions}\n\n"
            f"## crates (cargo bloat --crates)\n\n{result.bloat_crates}\n"
        )

        results.append(result)

    # ---- write JSON ----
    json_data = [
        {
            "scheme": r.build.scheme,
            "variant": r.build.variant,
            "operation": r.build.operation,
            "profile": r.build.profile,
            "features": r.build.features,
            "sections": r.sections,
            "flash_total": flash_size(r.sections),
            "ram_total": ram_size(r.sections),
            "size_total": r.total,
            "error": r.error,
        }
        for r in results
    ]
    (out_dir / "results.json").write_text(json.dumps(json_data, indent=2))

    # ---- write markdown summary ----
    md = ["# libcrux-iot binary size report", ""]
    md.append(
        "Section sizes (bytes) of the `libcrux-iot-binary-size` firmware "
        f"built for `{TARGET}`.\n"
    )
    md.append(
        "`flash total` = "
        + " + ".join(sorted(FLASH_SECTIONS))
        + "; `RAM` = "
        + " + ".join(sorted(RAM_SECTIONS))
        + ".\n"
    )
    for scheme in SCHEMES:
        table = build_summary_table(results, scheme)
        if table:
            md.append(table)

    errors = [r for r in results if r.error]
    if errors:
        md.append("## errors\n")
        for r in errors:
            md.append(f"- **{r.build.name}**: {r.error.splitlines()[0]}")
        md.append("")

    md.append("Per-build `cargo bloat` output is in the `bloat/` directory.\n")
    (out_dir / "summary.md").write_text("\n".join(md))

    # ---- print summary to console ----
    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    for scheme in SCHEMES:
        print("\n" + build_summary_table(results, scheme))

    print(f"Report written to: {out_dir}")
    print(f"  - {out_dir / 'summary.md'}")
    print(f"  - {out_dir / 'results.json'}")
    print(f"  - {bloat_dir}/")

    if errors:
        print(f"\n{len(errors)} build(s) failed; see summary.md.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
