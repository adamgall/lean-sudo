#!/usr/bin/env python3
import collections
import json
import pathlib
import sys


def read_run(directory, name):
    data = json.loads((directory / f"{name}.results.json").read_text())
    inventory = {
        line.removesuffix(": test")
        for line in (directory / f"{name}.inventory.txt").read_text().splitlines()
        if line.endswith(": test")
    }
    outcomes = {}
    diagnostics = {}
    for result in data["tests"]:
        test, status = result["test"], result["status"]
        if test in outcomes or status not in ("ok", "FAILED", "TIMEOUT"):
            raise ValueError(f"{name}: duplicate outcome or infrastructure failure: {test}")
        outcomes[test] = status
        if status != "ok":
            text = (directory / result["log"]).read_text(errors="replace")
            diagnostics[test] = f"Verbatim log: {result['log']}\n{text}"
            if status == "TIMEOUT":
                diagnostics[test] = (
                    f"Exceeded {data['timeout_seconds']} seconds; process group terminated.\n"
                    + diagnostics[test]
                )
    status = int((directory / f"{name}.exit").read_text())
    if not outcomes or outcomes.keys() != inventory or status not in (0, 1):
        raise ValueError(f"{name}: incomplete suite or infrastructure failure (exit {status})")
    counts = collections.Counter(outcomes.values())
    if counts != data["counts"] or (status == 0) != (counts["ok"] == len(outcomes)):
        raise ValueError(f"{name}: result counts disagree with completion status")
    summary = (f"{counts['ok']} passed; {counts['FAILED']} failed; "
               f"{counts['TIMEOUT']} timed out; {len(outcomes)} total")
    (directory / f"{name}.tsv").write_text(
        "".join(f"{test}\t{outcomes[test]}\n" for test in sorted(outcomes))
    )
    return outcomes, diagnostics, summary


def main():
    directory = pathlib.Path(sys.argv[1])
    reference, reference_details, reference_summary = read_run(directory, "reference")
    lean, lean_details, lean_summary = read_run(directory, "lean")
    if reference.keys() != lean.keys():
        raise ValueError("reference and lean runs selected different tests")
    findings = sorted(test for test in reference if reference[test] == "ok"
                      and lean[test] != "ok")
    baseline = sorted(test for test in reference if reference[test] != "ok")
    changes = sorted(test for test in reference if reference[test] != lean[test])
    report = {
        "revision": (directory / "reference.pin").read_text().splitlines()[0],
        "reference_summary": reference_summary,
        "lean_summary": lean_summary,
        "test_count": len(reference),
        "findings": [
            {"test": test, "reference": reference[test], "lean": lean[test],
             "diagnostic": lean_details.get(test, "See lean.log for process output")}
            for test in findings
        ],
        "baseline_failures": [
            {"test": test, "reference": reference[test], "lean": lean[test],
             "diagnostic": reference_details.get(test, "See reference.log for process output")}
            for test in baseline
        ],
    }
    (directory / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    (directory / "outcomes.diff.tsv").write_text(
        "test\treference\tlean\n" + "".join(
            f"{test}\t{reference[test]}\t{lean[test]}\n" for test in changes
        )
    )
    lines = [f"sudo-rs revision: {report['revision']}",
             f"reference: {reference_summary}", f"lean: {lean_summary}",
             f"Reference-pass / lean-fail findings: {len(findings)}",
             f"Excluded reference failures: {len(baseline)}", ""]
    for finding in report["findings"]:
        lines.extend([finding["test"], finding["diagnostic"], ""])
    (directory / "findings.txt").write_text("\n".join(lines) + "\n")
    for line in lines[:5]:
        print(line)
    for test in findings:
        print(f"FINDING {test}")
    print(f"Verbatim logs, per-test outcomes and diagnostics: {directory}")
    return int(bool(findings))


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError) as error:
        print(f"external suite: {error}", file=sys.stderr)
        sys.exit(2)
