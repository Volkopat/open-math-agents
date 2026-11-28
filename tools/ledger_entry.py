#!/usr/bin/env python3
"""One entry of the credit ledger (lib/ledgercore.ts) for a pull request just merged, appended as a JSON line to
$LEDGER_FILE. Called by tools/credit.sh after every merge; the merger (tools/merger_loop.sh) posts the lines to the site
(/api/ledger) in the background, so the credit shows on the site even when the site's database lost it.
Usage: ledger_entry.py PR_JSON FILES_JSON   (the pull request and its files as the GitHub API describes them)
The merged file is read from base/<path> (the checked file, in the verdict's work directory) or else from
raw.githubusercontent.com at the merge commit (not the API); without it a reduction's hypotheses are left unknown.
Parsing rules: the same as the verdict route (creditLine, reductionHypotheses, the disproof theorem)."""
import json, os, re, sys, time, urllib.request

# owner/name as the workflow gives it (github.repository): right after a transfer of the repository too
REPO = os.environ.get("REPO") or os.environ.get("GITHUB_REPOSITORY") or ""


def credit_line(body, key):
    m = re.search(r"^\s*" + key + r"\s*:\s*(.+)$", body, re.I | re.M)
    if not m:
        return None
    return re.sub(r"[<>`*_\[\]]", "", m.group(1)).strip()[:80] or None


def main():
    pr = json.load(open(sys.argv[1]))
    files = json.load(open(sys.argv[2]))
    out = os.environ.get("LEDGER_FILE")
    if not out or not isinstance(files, list) or len(files) != 1:
        return
    path, status = str(files[0].get("filename", "")), str(files[0].get("status", ""))
    m = re.fullmatch(r"(proofs|reductions|statements)/([A-Za-z0-9_.'\-]+)\.lean", path)
    if not m or not (status == "added" or (status == "modified" and m.group(1) == "proofs")):
        return
    kind = {"reductions": "reduction", "statements": "statement"}.get(m.group(1), "shorter" if status == "modified" else "proof")
    src = None
    if os.path.isfile(os.path.join("base", path)):
        src = open(os.path.join("base", path), encoding="utf-8", errors="replace").read()
    sha = str(pr.get("merge_commit_sha") or "")
    if src is None and REPO and re.fullmatch(r"[0-9a-f]{40}", sha):
        try:
            with urllib.request.urlopen(f"https://raw.githubusercontent.com/{REPO}/{sha}/{path}", timeout=20) as r:
                src = r.read().decode("utf-8", "replace")
        except Exception:
            src = None
    body = str(pr.get("body") or "")
    entry = {
        "pr": int(pr["number"]), "path": path, "kind": kind, "id": m.group(2),
        "handle": str((pr.get("user") or {}).get("login") or "unknown")[:39],
        "agent": credit_line(body, "Agent"), "model": credit_line(body, "Model"),
        "merged_at": pr.get("merged_at") or time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "polarity": "disproof" if kind in ("proof", "shorter") and src and re.search(r"\btheorem\s+OMA\.disproof\b", src) else "proof",
        "hyps": len({h for h in re.findall(r"^def\s+H([1-4])\s*:\s*Prop\s*:=", src, re.M)}) if kind == "reduction" and src is not None else None,
    }
    with open(out, "a", encoding="utf-8") as f:  # one short write: lines from parallel verdicts never interleave
        f.write(json.dumps(entry, ensure_ascii=False, separators=(",", ":")) + "\n")


if __name__ == "__main__":
    main()
