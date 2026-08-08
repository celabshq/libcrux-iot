#!/usr/bin/env python3
"""
Parse a libcrux IoT cycle-benchmark .dat file.

Each measured iteration is logged as a pair of lines:

    [INFO ] b,r,bench_keygen,0           (... src/logger.rs:59)   <- run marker
    [INFO ] b,d,bench_keygen,0,4427634   (... src/logger.rs:59)   <- data line

This script looks at the *data* lines (the "second line" of each pair). The
numeric value sitting right before the trailing file-path "( ... )" is the
measured cycle count.

Consecutive data lines that share the same `bench_` key are grouped together,
and the average of their values is reported per group. A group ends whenever
the key changes or a non-data line (e.g. a header or "Firmware exited
successfully") interrupts the run -- this is the literal meaning of grouping
"subsequent lines that contain the same bench_ key".
"""

import argparse
import re
import sys

# Any benchmark line (run-marker "b,r,..." or data "b,d,...") carries a key.
# We use this to decide group membership.
BENCH_KEY = re.compile(r"b,[rd],(?P<key>bench_\w+)\b")

# A data line additionally carries the measured value sitting right before the
# trailing file-path "( ... )". Example matched text:
#   [INFO ] b,d,bench_keygen,0,4427634 (libcrux_iot_testutil .../logger.rs:59)
DATA_VALUE = re.compile(
    r"""
    b,d,                       # data-line marker
    bench_\w+                  # the bench_ key
    ,                          #
    \d+                        # iteration index
    ,                          #
    (?P<value>-?\d+(?:\.\d+)?) # the numeric value right before the file path
    \s*\(                      # start of the trailing "( ...file path... )"
    """,
    re.VERBOSE,
)


# Header line looks like: "l,0,16000000,ML-KEM Benchmark (libcrux_iot ...)".
# Each such header marks the start of a new run (= one parameter set).
SCHEME_HEADER = re.compile(r"l,\d+,\d+,(?P<scheme>[\w-]+)\s+Benchmark")


def parse(path):
    """Return the file's runs, each as a list of (key, [values]) groups.

    A new run begins at each "<scheme> Benchmark" header line, so the Nth run
    corresponds to the Nth parameter set regardless of which operations each
    run happens to contain -- a run missing an operation does not shift the
    values of later runs into the wrong row.

    Within a run, a group is a maximal span of consecutive benchmark lines
    (both run-markers and data lines) that share one bench_ key. Run-marker
    lines keep the group alive but contribute no value; only data lines
    contribute a value. A group ends when the bench_ key changes or a
    non-benchmark line (e.g. "Firmware exited successfully") interrupts it.
    """
    runs = []
    cur_run = None
    cur_key = None
    cur_vals = None

    def flush_group():
        nonlocal cur_key, cur_vals
        if cur_key is not None:
            cur_run.append((cur_key, cur_vals))
            cur_key, cur_vals = None, None

    with open(path, "r", encoding="utf-8", errors="replace") as fh:
        for line in fh:
            if SCHEME_HEADER.search(line):
                # A benchmark header starts a new run.
                flush_group()
                cur_run = []
                runs.append(cur_run)
                continue

            key_m = BENCH_KEY.search(line)
            if not key_m:
                # A non-benchmark line (separator) ends the current group.
                flush_group()
                continue

            if cur_run is None:
                # Benchmark data before any header: start an implicit run.
                cur_run = []
                runs.append(cur_run)

            key = key_m.group("key")
            if key != cur_key:
                flush_group()
                cur_key, cur_vals = key, []

            val_m = DATA_VALUE.search(line)
            if val_m:
                cur_vals.append(float(val_m.group("value")))

    flush_group()
    return runs


# The successive runs in the file correspond to a scheme's parameter sets,
# in order. The scheme is auto-detected from the "<scheme> Benchmark" header.
PARAM_SETS = {
    "ML-DSA": ["ML-DSA-44", "ML-DSA-65", "ML-DSA-87"],
    "ML-KEM": ["ML-KEM-512", "ML-KEM-768", "ML-KEM-1024"],
}

# Friendly column headers for the bench_ keys (raw key -> display name).
OP_LABELS = {
    "bench_keygen": "Key generation",
    "bench_sign": "Signing",
    "bench_verify": "Verification",
    "bench_encaps": "Encapsulation",
    "bench_decaps": "Decapsulation",
}


def detect_scheme(path):
    """Return the scheme name from the file's Benchmark header, or None."""
    with open(path, "r", encoding="utf-8", errors="replace") as fh:
        for line in fh:
            m = SCHEME_HEADER.search(line)
            if m:
                return m.group("scheme")
    return None


def fmt_cycles(avg):
    """Thousands-separated; drop the decimals when the average is whole."""
    return f"{avg:,.0f}" if avg == int(avg) else f"{avg:,.2f}"


# Time units to choose from, largest first: (suffix, seconds-per-unit).
TIME_UNITS = [("s", 1.0), ("ms", 1e-3), ("\u00b5s", 1e-6), ("ns", 1e-9)]


def pick_time_unit(max_seconds):
    """Pick the largest unit whose value for max_seconds is >= 1 (else ns)."""
    for suffix, scale in TIME_UNITS:
        if max_seconds >= scale:
            return suffix, scale
    return TIME_UNITS[-1]


def fmt_time(seconds, scale):
    return f"{seconds / scale:,.3f}"


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("file", help="path to the benchmark .dat file")
    ap.add_argument("-c", "--clock-mhz", type=float, default=None,
                    help="clock speed in MHz; if given, add real-time columns "
                         "(time = cycles / (clock_mhz * 1e6))")
    ap.add_argument("--param-sets", default=None,
                    help="comma-separated parameter-set names to label the runs "
                         "(overrides auto-detection from the file header)")
    args = ap.parse_args(argv)

    if args.clock_mhz is not None and args.clock_mhz <= 0:
        ap.error("--clock-mhz must be a positive number")

    parsed_runs = parse(args.file)

    # Decide how to label each run. Priority: explicit --param-sets, then the
    # scheme detected from the file header, then a generic "Run N" fallback.
    if args.param_sets is not None:
        param_labels = [s.strip() for s in args.param_sets.split(",")]
    else:
        scheme = detect_scheme(args.file)
        param_labels = PARAM_SETS.get(scheme, [])

    # Pivot each run's keygen/sign/verify groups into one row per run (= per
    # parameter set), with a column per operation. A group with no data values
    # (e.g. a benchmark whose data lines were dropped or the firmware crashed
    # mid-run) is skipped with a warning rather than averaged over nothing.
    runs = {}          # run index -> {key: average cycles}
    col_order = []     # operation keys, in first-seen order
    for run_idx, run in enumerate(parsed_runs):
        for key, vals in run:
            if not vals:
                print(f"warning: benchmark '{key}' in run {run_idx + 1} has no "
                      f"data values; skipping", file=sys.stderr)
                continue
            runs.setdefault(run_idx, {})[key] = sum(vals) / len(vals)
            if key not in col_order:
                col_order.append(key)

    if not runs:
        print("No data lines found.", file=sys.stderr)
        return 1

    clock_hz = args.clock_mhz * 1e6 if args.clock_mhz is not None else None

    # Choose a single time unit for the whole table, based on the largest time.
    unit_suffix = unit_scale = None
    if clock_hz is not None:
        max_seconds = max(c for r in runs.values() for c in r.values()) / clock_hz
        unit_suffix, unit_scale = pick_time_unit(max_seconds)

    # Build headers: one cycle column per op, plus a time column when a clock
    # speed was supplied.
    headers = ["Parameter set"]
    for k in col_order:
        op = OP_LABELS.get(k, k)
        headers.append(f"{op} (cycles)")
        if clock_hz is not None:
            headers.append(f"{op} ({unit_suffix})")

    print("| " + " | ".join(headers) + " |")
    print("| " + " | ".join("---" for _ in headers) + " |")

    for run_idx in sorted(runs):
        label = param_labels[run_idx] if run_idx < len(param_labels) else f"Run {run_idx + 1}"
        cells = [label]
        for k in col_order:
            if k in runs[run_idx]:
                cycles = runs[run_idx][k]
                cells.append(fmt_cycles(cycles))
                if clock_hz is not None:
                    cells.append(fmt_time(cycles / clock_hz, unit_scale))
            else:
                cells.append("-")
                if clock_hz is not None:
                    cells.append("-")
        print("| " + " | ".join(cells) + " |")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
