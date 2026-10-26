#!/usr/bin/env python3
import collections
import concurrent.futures
import json
import os
import pathlib
import re
import signal
import subprocess
import time


def execute(index, name, binary, directory, timeout):
    case = directory / f"{index:04d}"
    case.mkdir(parents=True, exist_ok=True)
    environment = dict(os.environ, SUDO_UNDER_TEST="theirs", SUDO_EXTERNAL_CASE_DIR=str(case))
    command = [str(binary), "--exact", name, "--include-ignored", "--nocapture", "--color", "never"]
    started = time.monotonic()
    with (case / "output.log").open("wb") as output:
        process = subprocess.Popen(command, stdout=output, stderr=subprocess.STDOUT,
                                   env=environment, start_new_session=True)
        try:
            status = process.wait(timeout=timeout)
            result = "ok" if status == 0 else "FAILED"
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            status = 124
            result = "TIMEOUT"
    cleanup_errors = []
    containers = case.glob("*.cid") if status not in (0, 101) else ()
    for cidfile in containers:
        cid = cidfile.read_text().strip()
        if not re.fullmatch(r"[0-9a-f]{64}", cid):
            cleanup_errors.append(f"invalid owned container id in {cidfile}")
            continue
        cleanup = subprocess.run(["/usr/bin/docker", "rm", "-f", cid],
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if cleanup.returncode and b"No such container" not in cleanup.stdout:
            cleanup_errors.append(cleanup.stdout.decode(errors="replace"))
    if cleanup_errors:
        result = "ERROR"
    text = (case / "output.log").read_text(errors="replace")
    if result in ("ok", "FAILED"):
        expected = "1 passed; 0 failed; 0 ignored" if status == 0 else "0 passed; 1 failed; 0 ignored"
        if expected not in text or status not in (0, 101):
            result = "ERROR"
    return {"test": name, "status": result, "exit": status,
            "seconds": round(time.monotonic() - started, 3),
            "log": str(case.relative_to(pathlib.Path("/out"))) + "/output.log",
            "cleanup_errors": cleanup_errors}


def main():
    implementation = os.environ["IMPLEMENTATION"]
    directory = pathlib.Path("/out") / f"{implementation}.cases"
    candidates = [path for path in pathlib.Path("target/debug/deps").glob("sudo_compliance_tests-*")
                  if path.is_file() and os.access(path, os.X_OK)]
    if len(candidates) != 1:
        raise RuntimeError(f"expected one compliance executable, found {candidates}")
    binary = candidates[0].resolve()
    listing = subprocess.check_output([str(binary), "--list", "--format", "terse"], text=True)
    names = [line.removesuffix(": test") for line in listing.splitlines() if line.endswith(": test")]
    if not names or len(names) != len(set(names)):
        raise RuntimeError("invalid upstream test inventory")
    pathlib.Path(f"/out/{implementation}.inventory.txt").write_text(listing)
    timeout = float(os.environ.get("CASE_TIMEOUT", "120"))
    results = []
    with pathlib.Path(f"/out/{implementation}.log").open("wb") as aggregate:
        with concurrent.futures.ThreadPoolExecutor(
            max_workers=int(os.environ.get("SUITE_THREADS", "4"))
        ) as pool:
            futures = [pool.submit(execute, index, name, binary, directory, timeout)
                       for index, name in enumerate(names)]
            for future in concurrent.futures.as_completed(futures):
                result = future.result()
                results.append(result)
                aggregate.write((pathlib.Path("/out") / result["log"]).read_bytes())
                aggregate.flush()
                print(f"test {result['test']} ... {result['status']}", flush=True)
    results.sort(key=lambda result: result["test"])
    counts = collections.Counter(result["status"] for result in results)
    pathlib.Path(f"/out/{implementation}.results.json").write_text(
        json.dumps({"tests": results, "counts": counts, "timeout_seconds": timeout}, indent=2) + "\n"
    )
    status = 2 if counts["ERROR"] else int(bool(counts["FAILED"] or counts["TIMEOUT"]))
    pathlib.Path(f"/out/{implementation}.exit").write_text(f"{status}\n")
    print(f"{implementation}: {dict(counts)}", flush=True)


if __name__ == "__main__":
    main()
