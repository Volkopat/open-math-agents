#!/usr/bin/env python3
"""Build data/catalog.json from google-deepmind/formal-conjectures (+ teorth/erdosproblems metadata).

Usage:
  python3 -I scripts/ingest.py <formal-conjectures checkout> <erdosproblems checkout> [out.json]

Every entry is one Lean declaration that is still `sorry` upstream: a precise, machine-checkable
target. Nothing here is hand-written; rerun the script to refresh.
"""
import json
import math
import os
import re
import subprocess
import sys

FC, EP = sys.argv[1], sys.argv[2]
OUT = sys.argv[3] if len(sys.argv) > 3 else os.path.join(os.path.dirname(__file__), "..", "data", "catalog.json")

SOURCES = {
    "ErdosProblems": "Erdős Problems",
    "Wikipedia": "Wikipedia",
    "OEIS": "OEIS",
    "Mathoverflow": "MathOverflow",
    "Kourovka": "Kourovka Notebook",
    "GreensOpenProblems": "Green's 100 Open Problems",
    "Millennium": "Millennium Prize",
    "HilbertProblems": "Hilbert's Problems",
    "Arxiv": "arXiv papers",
    "Books": "Books",
    "Paper": "Papers",
    "LittProblems": "Litt's Problems",
    "OpenQuantumProblems": "Open Quantum Problems",
    "OptimizationConstants": "Optimization Constants",
    "WrittenOnTheWallII": "Written on the Wall II",
    "Subsets": "Subsets",
    "Other": "Other",
}

# AMS MSC 2020 top-level classes (the ones that appear upstream).
AMS = {
    0: "General", 1: "History", 3: "Logic & Foundations", 5: "Combinatorics", 6: "Order & Lattices",
    8: "General Algebra", 11: "Number Theory", 12: "Field Theory", 13: "Commutative Algebra",
    14: "Algebraic Geometry", 15: "Linear Algebra", 16: "Associative Rings", 17: "Nonassociative Rings",
    18: "Category Theory", 19: "K-Theory", 20: "Group Theory", 22: "Topological Groups",
    26: "Real Functions", 28: "Measure & Integration", 30: "Complex Analysis", 31: "Potential Theory",
    32: "Several Complex Variables", 33: "Special Functions", 34: "ODEs", 35: "PDEs",
    37: "Dynamical Systems", 39: "Difference Equations", 40: "Sequences & Series", 41: "Approximation",
    42: "Harmonic Analysis", 43: "Abstract Harmonic Analysis", 44: "Integral Transforms",
    45: "Integral Equations", 46: "Functional Analysis", 47: "Operator Theory", 49: "Calculus of Variations",
    51: "Geometry", 52: "Convex & Discrete Geometry", 53: "Differential Geometry", 54: "General Topology",
    55: "Algebraic Topology", 57: "Manifolds", 58: "Global Analysis", 60: "Probability", 62: "Statistics",
    65: "Numerical Analysis", 68: "Computer Science", 70: "Mechanics", 74: "Mechanics of Solids",
    76: "Fluid Mechanics", 78: "Optics", 80: "Thermodynamics", 81: "Quantum Theory",
    82: "Statistical Mechanics", 83: "Relativity", 85: "Astronomy", 86: "Geophysics",
    90: "Operations Research", 91: "Game Theory & Economics", 92: "Biology", 93: "Control Theory",
    94: "Information & Communication", 97: "Mathematics Education",
}

DECL_RE = re.compile(r"^(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma)\s+([^\s:({\[]+)")
NS_RE = re.compile(r"^namespace\s+(\S+)")
END_RE = re.compile(r"^end(?:\s+(\S+))?\s*$")
SECTION_RE = re.compile(r"^(?:noncomputable\s+)?section(?:\s+(\S+))?")


def erdos_meta():
    path = os.path.join(EP, "data", "problems.yaml")
    meta = {}
    cur = None
    block = None
    with open(path, encoding="utf-8") as f:
        for raw in f:
            line = raw.rstrip("\n")
            m = re.match(r'^- number: "?(\d+)"?', line)
            if m:
                cur = {"tags": [], "prize": None, "state": None, "posts": 0, "proofClaims": 0}
                meta[int(m.group(1))] = cur
                block = None
                continue
            if cur is None:
                continue
            m = re.match(r"^  (\w+):(.*)$", line)
            if m:
                block = m.group(1)
                val = m.group(2).strip()
                if block == "prize":
                    v = val.strip('"')
                    cur["prize"] = None if v in ("", "no") else v
                elif block == "tags":
                    cur["tags"] = re.findall(r'"([^"]+)"', val)
                continue
            m = re.match(r"^    (\w+):\s*(.*)$", line)
            if m:
                k, v = m.group(1), m.group(2).strip().strip('"')
                if block == "status" and k == "state":
                    cur["state"] = v
                elif block == "forum" and k == "posts":
                    cur["posts"] = int(v or 0)
                elif block == "forum" and k == "proof_claims":
                    cur["proofClaims"] = int(v or 0)
    return meta


def prize_usd(p):
    if not p:
        return 0
    s = p.replace(",", "")
    m = re.search(r"[$£](\d+)", s)
    if not m:
        m = re.search(r"(\d+)\s*(?:rupees|Rs)", s)
        return int(m.group(1)) // 80 if m else 0
    v = int(m.group(1))
    return int(v * 1.25) if "£" in s else v


def clean_doc(doc):
    doc = doc.strip()
    doc = re.sub(r"^/--\s?", "", doc)
    doc = re.sub(r"-/\s*$", "", doc)
    return "\n".join(l.rstrip() for l in doc.strip().splitlines()).strip()


def file_title(text):
    m = re.search(r"/-!\s*\n\s*#\s+(.+)", text)
    return m.group(1).strip() if m else None


def file_refs(text):
    m = re.search(r"/-!(.*?)-/", text, re.S)
    if not m:
        return []
    return list(dict.fromkeys(re.findall(r"https?://[^\s)\]>]+", m.group(1))))[:6]


def parse_file(path, rel):
    text = open(path, encoding="utf-8").read()
    lines = text.splitlines()
    module = "FormalConjectures." + ".".join(
        "«%s»" % p if re.match(r"^\d", p) else p for p in rel[len("FormalConjectures/"):-5].split("/")
    )
    title = file_title(text)
    refs = file_refs(text)
    out = []
    ns = []  # stack of (kind, name)
    i = 0
    n = len(lines)
    pending_doc = None
    pending_attr = None
    while i < n:
        line = lines[i]
        s = line.strip()
        m = NS_RE.match(s)
        if m:
            for part in m.group(1).split("."):
                ns.append(("ns", part))
            i += 1
            continue
        m = SECTION_RE.match(s)
        if m and not s.startswith("section_"):
            ns.append(("sec", m.group(1) or ""))
            i += 1
            continue
        m = END_RE.match(s)
        if m:
            name = m.group(1)
            if name:
                parts = name.split(".")
                for _ in parts:
                    if ns:
                        ns.pop()
            elif ns:
                ns.pop()
            i += 1
            continue
        if s.startswith("/--"):
            buf = [line]
            if "-/" not in s[3:]:
                while i + 1 < n:
                    i += 1
                    buf.append(lines[i])
                    if "-/" in lines[i]:
                        break
            pending_doc = clean_doc("\n".join(buf))
            i += 1
            continue
        if s.startswith("@["):
            buf = [s]
            depth = s.count("[") - s.count("]")
            while depth > 0 and i + 1 < n:
                i += 1
                buf.append(lines[i].strip())
                depth += lines[i].count("[") - lines[i].count("]")
            attr = " ".join(buf)
            # an attribute line may be followed by the declaration on the same line
            close = attr.rfind("]")
            rest = attr[close + 1:].strip()
            pending_attr = attr[: close + 1]
            if rest:
                lines[i] = rest
                continue
            i += 1
            continue
        m = DECL_RE.match(s)
        if m and pending_attr and "category" in pending_attr:
            name = m.group(2)
            # statement: up to the ":=" that opens the proof. Statements can contain ":=" themselves
            # (let x := …), so look for the proof opener ":= by sorry" / ":= sorry" first, and only fall
            # back to the first ":=" when the proof is something else.
            j = i
            buf = [line]
            while j + 1 < n and len(buf) < 120:
                chunk = "\n".join(buf)
                if re.search(r":=\s*(by\s+)?sorry\b", chunk) or (lines[j + 1].strip() == "" and ":=" in chunk):
                    break
                j += 1
                buf.append(lines[j])
            stmt_full = "\n".join(buf)
            mproof = re.search(r":=\s*(by\s+)?sorry\b", stmt_full)
            if mproof:
                head, body_txt = stmt_full[:mproof.start()], "sorry"
            else:
                head, _, tail = stmt_full.partition(":=")
                body_txt = tail.strip()
            k = j
            is_sorry = body_txt == "sorry" or re.fullmatch(r"(by\s+)?sorry", body_txt.strip()) is not None
            cat = re.search(r"category\s+(research open|research solved|research formally solved|textbook|test|undergraduate|graduate|high_school|API)", pending_attr)
            category = cat.group(1) if cat else "other"
            ams = [int(x) for x in re.findall(r"\b(\d{1,2})\b", (re.search(r"AMS([\d\s]+)", pending_attr) or [None, ""])[1])] if "AMS" in pending_attr else []
            nsname = ".".join(p for k_, p in ns if k_ == "ns" and p)
            full = name if name.startswith("_root_") else (nsname + "." + name if nsname else name)
            full = full.replace("_root_.", "")
            formal_proof = "formal_proof" in pending_attr
            disproof = "disproof" in pending_attr
            out.append({
                "decl": full,
                "name": name,
                "module": module,
                "file": rel,
                "line": i + 1,
                "title": title,
                "refs": refs,
                "category": category,
                "ams": ams,
                "doc": pending_doc or "",
                "lean": head.rstrip(),
                "sorry": is_sorry,
                "formalProofLinked": formal_proof,
            })
            pending_attr = None
            pending_doc = None
            i = k + 1
            continue
        if s and not s.startswith("--"):
            if not s.startswith("set_option"):
                pending_attr = None if not s.startswith("@[") else pending_attr
                if not DECL_RE.match(s):
                    pending_doc = None if not s.startswith("/--") else pending_doc
        i += 1
    return out


def slugify(decl):
    s = decl.replace("«", "").replace("»", "")
    s = re.sub(r"[^A-Za-z0-9_.']+", "-", s).strip("-")
    return s.replace("'", "-prime")


def difficulty(e, em):
    base = {"research open": 58, "research solved": 42, "research formally solved": 30, "graduate": 30,
            "undergraduate": 20, "textbook": 16, "high_school": 10, "test": 6, "API": 8}.get(e["category"], 30)
    bonus = 0
    src = e["source"]
    if src in ("Millennium Prize",):
        bonus += 28
    elif src in ("Hilbert's Problems",):
        bonus += 18
    if src in ("Millennium Prize",):
        bonus += 14
    if em and em.get("prize"):
        bonus += min(26, 6 * math.log10(1 + prize_usd(em["prize"])))
    if em and (em.get("state") or "").split(" ")[0] in ("falsifiable", "decidable", "verifiable"):
        bonus -= 10  # a finite search could settle it
    if ".variants." in e["decl"] or "variant" in e["name"]:
        bonus -= 12
    if src in ("OEIS",) and e["category"] == "research open":
        bonus -= 6  # usually numerically explorable
    L = len(e["lean"])
    bonus += min(6, L / 180)
    if em:
        bonus += min(4, em.get("posts", 0) / 6)
    return max(1, min(100, round(base + bonus)))


def kind_of(cat):
    if cat == "research open":
        return "open"
    if cat in ("research solved", "research formally solved", "textbook"):
        return "known"  # known result, formal proof missing ("textbook" = a known theorem, not an easy exercise)
    return "warmup"


def main():
    sha = subprocess.run(["git", "-C", FC, "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    em_all = erdos_meta()
    entries = []
    root = os.path.join(FC, "FormalConjectures")
    for dirpath, _, files in os.walk(root):
        for fn in sorted(files):
            if not fn.endswith(".lean"):
                continue
            path = os.path.join(dirpath, fn)
            rel = os.path.relpath(path, FC)
            try:
                entries += parse_file(path, rel)
            except Exception as ex:  # one bad file must not kill the catalogue
                print("skip", rel, ex, file=sys.stderr)
    seen = set()
    catalog = []
    for e in entries:
        if not e["sorry"] or e["formalProofLinked"]:
            continue
        folder = e["file"].split("/")[1]
        e["source"] = SOURCES.get(folder, folder)
        em = None
        num = None
        if folder == "ErdosProblems":
            m = re.match(r"(\d+)", os.path.basename(e["file"]))
            if m:
                num = int(m.group(1))
                em = em_all.get(num)
        slug = slugify(e["decl"])
        if slug in seen:
            slug = slug + "-" + str(e["line"])
        seen.add(slug)
        title = e["title"] or e["decl"]
        bold = re.match(r"^\*\*([^*\n]{3,80})\*\*", e["doc"] or "")
        if bold:
            title = bold.group(1).strip().rstrip(":")
        elif ".variants." in e["decl"] or e["name"].count(".") >= 1:
            suffix = e["decl"].split(".")[-1].replace("_", " ")
            if suffix and suffix not in title.lower():
                title = f"{title} — {suffix}"
        fields = sorted({AMS[a] for a in e["ams"] if a in AMS})
        if em and em.get("tags"):
            tags = em["tags"]
        else:
            tags = []
        ref = e["refs"][0] if e["refs"] else (f"https://www.erdosproblems.com/{num}" if num else None)
        item = {
            "id": slug,
            "decl": e["decl"],
            "title": title,
            "source": e["source"],
            "kind": kind_of(e["category"]),
            "category": e["category"],
            "fields": fields or ["Uncategorised"],
            "tags": tags,
            "statement": e["doc"],
            "lean": e["lean"],
            "module": e["module"],
            "file": e["file"],
            "line": e["line"],
            "ref": ref,
            "prize": (em or {}).get("prize"),
            "erdos": num,
            "erdosState": (em or {}).get("state"),
            "forumPosts": (em or {}).get("posts", 0),
        }
        item["difficulty"] = difficulty({**e, "source": e["source"]}, em)
        catalog.append(item)
    # Disambiguate repeated titles with the declaration's last segment.
    from collections import Counter
    tc = Counter(c["title"] for c in catalog)
    for c in catalog:
        if "." in c["title"] and " " not in c["title"].split(" — ")[0]:
            c["title"] = (c["title"].split(" — ")[0].split(".")[0]) + (" — " + c["title"].split(" — ")[1] if " — " in c["title"] else "")
        if tc[c["title"]] > 1 or c["title"] == c["decl"]:
            seg = c["decl"].split(".")[-1].replace("_", " ")
            if seg.lower() not in c["title"].lower():
                c["title"] = f"{c['title']} — {seg}"
    catalog.sort(key=lambda x: ({"open": 0, "known": 1, "warmup": 2}[x["kind"]], -x["difficulty"], x["id"]))
    meta = {
        "upstream": "https://github.com/google-deepmind/formal-conjectures",
        "upstreamCommit": sha,
        "license": "Apache-2.0 (statements from formal-conjectures)",
        "counts": {k: sum(1 for c in catalog if c["kind"] == k) for k in ("open", "known", "warmup")},
        "total": len(catalog),
    }
    os.makedirs(os.path.dirname(os.path.abspath(OUT)), exist_ok=True)
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump({"meta": meta, "problems": catalog}, f, ensure_ascii=False, separators=(",", ":"))
    print(json.dumps(meta, indent=1))


if __name__ == "__main__":
    main()
