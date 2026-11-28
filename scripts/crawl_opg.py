#!/usr/bin/env python3
"""Collect Open Problem Garden problem METADATA (title, authors, subject, importance, link) from its subject tables.
Statements are not copied: the site links to the original. Spam pages (outside subject tables, or without
authors) are ignored. Usage: python3 -I scripts/crawl_opg.py <out.json>   (polite: one request every 1.5 s)"""
import html, json, re, sys, time, urllib.request

BASE = "https://www.openproblemgarden.org"
UA = "OpenMathAgentsCatalog/0.2 (https://github.com/lefttosolve2/open-math-agents)"
SUBJECTS = ["algebra", "analysis", "combinatorics", "geometry", "graph_theory", "group_theory", "logic",
            "number_theory_0", "pdes", "probability", "theoretical_computer_science", "topology", "unsorted"]

def get(path):
    time.sleep(1.5)
    req = urllib.request.Request(BASE + path, headers={"User-Agent": UA})
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            return r.read().decode("utf-8", "replace")
    except Exception as e:
        print("fail", path, e, file=sys.stderr)
        return ""

def rows(page):
    out = []
    for tr in re.findall(r"<tr class=\"(?:odd|even)[^\"]*\">(.*?)</tr>", page, re.S):
        title = re.search(r'view-field-node-title"><a href="(/op/[^"]+)">(.*?)</a>', tr, re.S)
        if not title:
            continue
        authors = re.search(r'field-last-names-value">(.*?)</td>', tr, re.S)
        stars = re.search(r'field-stars1-value">(.*?)</td>', tr, re.S)
        topic = re.search(r'top-sub-short[^"]*">(.*?)</td>', tr, re.S)
        clean = lambda s: html.unescape(re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", s or ""))).strip()
        out.append({
            "slug": title.group(1), "title": clean(title.group(2)),
            "authors": [a.strip() for a in clean(authors.group(1) if authors else "").split(";") if a.strip()],
            "stars": (stars.group(1) if stars else "").count("✭"),
            "topic": clean(topic.group(1) if topic else ""),
            "author_links": re.findall(r'href="(/category/[a-z0-9_]+)"', authors.group(1)) if authors else [],
        })
    return out

seen, todo, done = {}, [f"/category/{s}" for s in SUBJECTS], set()
author_cats = set()
while todo:
    path = todo.pop(0)
    if path in done:
        continue
    done.add(path)
    page = get(path)
    rs = rows(page)
    for r in rs:
        author_cats.update(r.pop("author_links"))
    subject = path.rsplit("/", 1)[1]
    for r in rs:
        if not r["authors"]:
            continue  # spam and stubs have no authors
        r.setdefault("areas", [])
        if r["slug"] in seen:
            if subject not in seen[r["slug"]]["areas"]:
                seen[r["slug"]]["areas"].append(subject)
        else:
            r["areas"] = [subject]
            seen[r["slug"]] = r
    # sub-categories: category links on the page that are not authors, not feeds, not sorts
    for c in set(re.findall(r'href="(/category/[a-z0-9_]+)"', page)):
        if c not in author_cats and c not in done and c not in todo and len(done) < 300:
            todo.append(c)
    print(f"{path}: rows {len(rs)} total {len(seen)}", file=sys.stderr)

json.dump(sorted(seen.values(), key=lambda r: r["slug"]), open(sys.argv[1], "w"), ensure_ascii=False, indent=0)
print(len(seen))
