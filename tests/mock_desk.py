#!/usr/bin/env python3
"""A stand-in for the site, for testing tools/oma.sh. Logs every request to $MOCK_LOG (one JSON per line)."""
import json, os, sys, urllib.parse
from http.server import BaseHTTPRequestHandler, HTTPServer

LOG = os.environ["MOCK_LOG"]
PID = "Erdos3.erdos_3.variants.gowers"
TEAM = "Team.p"   # a problem whose desk has the task board switched on (022); OLD = a desk without it
BOARD = {"items": [{"k": 1, "name": "step_bound", "statement": "(n : ℕ) : f (n + 1) ≤ 2 * f n", "status": "open"},
                   {"k": 2, "name": "base_case", "statement": ": f 0 = 1", "status": "taken", "owner": "mate"},
                   {"k": 3, "name": "old_try", "statement": "", "status": "dead", "dead_reason": "false for n = 3"}],
         "steps": [{"id": TEAM + ".R1.H1", "k": 1, "statement": "True", "status": "open", "agents": 0}],
         "open": 1, "taken": 1, "done": 0, "dead": 1, "complete": False}
BUNDLE = """-- TEAM LEMMAS FOR Team.p
-- Uses: #77, #78

-- uses note #77 · board #1 step_bound · by @mate · UNVERIFIED: nobody else has compiled it yet
lemma step_bound (n : ℕ) : n + 0 = n := by simp

-- uses note #78 · board #2 base_case · by @mate · UNVERIFIED: nobody else has compiled it yet
lemma base_case : BADLEMMA := by simp
"""

class H(BaseHTTPRequestHandler):
    def log_message(self, *a): pass
    def send(self, code, body, ctype="application/json"):
        b = (json.dumps(body) if not isinstance(body, str) else body).encode()
        self.send_response(code); self.send_header("Content-Type", ctype); self.send_header("Content-Length", str(len(b))); self.end_headers(); self.wfile.write(b)
    def handle_any(self):
        u = urllib.parse.urlparse(self.path); q = dict(urllib.parse.parse_qsl(u.query))
        n = int(self.headers.get("Content-Length") or 0) if self.command == "POST" else 0
        body = self.rfile.read(n).decode("utf-8", "replace") if n else ""
        open(LOG, "a").write(json.dumps({"method": self.command, "path": u.path, "q": q, "body": body}) + "\n")
        if u.path == "/api/desk/next":
            pid = q.get("problem") or PID
            if q.get("kind") == "formalize":
                return self.send(200, {"lease": "11111111-1111-1111-1111-111111111111", "task": "formalize", "points": 0,
                    "problem": {"id": "opg-x", "title": "X", "kind": "unformalized", "source": "OPG", "ref": "https://x"},
                    "file": "statements/opg-x.lean", "skeleton": "import Mathlib\n-- statement skeleton\n", "othersWorking": 0, "instructions": "state it"})
            if pid == "nope":
                return self.send(404, {"error": "not_found", "hint": "no such problem"})
            if pid == "Crowded.p":   # steered to a step of the crowded problem
                pid = "Crowded.p.R1.H2"
                return self.send(200, {"lease": "66666666-6666-6666-6666-666666666666", "points": 3,
                    "problem": {"id": pid, "title": "Step H2", "kind": "step", "statement": "H2", "lean": "def H2 : Prop := True", "page": "http://x/p/" + pid},
                    "othersWorking": 0, "role": "lead", "roleTask": "Lead.", "team": [], "teamNotes": [], "lastNote": 0,
                    "file": f"proofs/{pid}.lean", "skeleton": "import X\ntheorem OMA.solution : True := by\n  sorry\n",
                    "steered": {"from": "Crowded.p", "agents": 7, "hint": "7 agents already work on Crowded.p; its step Crowded.p.R1.H2 has 0."}})
            if pid == TEAM:
                return self.send(200, {"lease": "44444444-4444-4444-4444-444444444444", "points": 10,
                    "problem": {"id": pid, "title": "Team problem", "kind": "known", "difficulty": 40, "source": "X",
                                "statement": "f is bounded", "lean": "theorem t : True", "page": "http://x/p/" + pid},
                    "othersWorking": 3, "role": "helper", "roleTask": "Take an open item.", "team": [{"handle": "mate", "role": "lead"}],
                    "teamNotes": [], "lastNote": 70, "collaboration": "BOARD PROTOCOL", "boardEnabled": True, "board": BOARD,
                    "suggest": {"action": "take", "item": 1, "text": "Open subgoal #1 step_bound: tools/oma.sh take Team.p 1"},
                    "deadEnds": [{"id": 12, "handle": "old", "at": "2026-11-20T09:00:00Z", "note": "DEAD END: induction on n alone fails"}],
                    "file": f"proofs/{pid}.lean", "skeleton": f"import FormalConjectures.ErdosProblems.«3»\n\ntheorem OMA.solution : type_of% @{pid} := by\n  sorry\n"})
            return self.send(200, {"lease": "22222222-2222-2222-2222-222222222222", "points": 39,
                "problem": {"id": pid, "title": "Erdős 3 gowers", "kind": "known", "difficulty": 53, "source": "Erdős Problems",
                            "statement": "For every k...", "lean": "theorem t : True", "page": "http://x/p/" + pid},
                "othersWorking": 1, "role": "checker", "roleTask": "Test the statement.", "team": [{"handle": "mate", "role": "lead"}],
                "teamNotes": [], "lastNote": 7, "collaboration": "TEAMWORK PROTOCOL", "file": f"proofs/{pid}.lean", "skeleton": f"import FormalConjectures.ErdosProblems.«3»\n\ntheorem OMA.solution : type_of% @{pid} := by\n  sorry\n"})
        if u.path == "/api/desk/beat":
            if q.get("lease", "").startswith("3333"):
                return self.send(410, {"stop": True, "status": "settled"})
            if q.get("lease", "").startswith("4444"):
                done = dict(BOARD, complete=True, items=[dict(BOARD["items"][0], status="done", done_by="mate")], open=0, taken=0, done=1, dead=0)
                return self.send(200, {"ok": True, "role": "lead", "roleTask": "Lead and assemble.", "team": [{"handle": "mate", "role": "helper"}],
                                       "notes": [], "last_note": 70, "boardEnabled": True, "board": done, "role_change": "promoted",
                                       "role_hint": "Your lead has been silent for 15 minutes: you lead this problem now.",
                                       "suggest": {"action": "assemble", "text": "ASSEMBLE NOW: every subgoal on the board is done."}, "assemble": True})
            since = int(q.get("since", "0") or 0)
            notes = [{"id": 41, "handle": "mate", "at": "2026-11-27T09:00:00Z", "note": "PLAN: induction on k, need lemma L1"}]
            return self.send(200, {"ok": True, "role": "checker", "roleTask": "Test the statement.",
                                   "team": [{"handle": "mate", "role": "lead"}],
                                   "notes": [n for n in notes if n["id"] > since], "last_note": 41})
        if u.path == "/api/desk/board" and self.command == "GET":
            if q.get("problem") == TEAM:
                notes = [{"id": 71, "handle": "mate", "at": "2026-11-27T09:00:00Z", "note": "TAKING: base_case"}]
                return self.send(200, {"problem": TEAM, "boardEnabled": True, "board": BOARD, "team": [{"handle": "mate", "role": "lead"}],
                                       "notes": [x for x in notes if x["id"] > int(q.get("since") or 0)], "last_note": 71})
            return self.send(200, {"problem": q.get("problem"), "boardEnabled": False, "team": [], "notes": [], "last_note": 0})
        if u.path == "/api/desk/board":
            if q.get("lease", "").startswith("5555"):
                return self.send(501, {"error": "not_enabled_yet", "hint": "The team board is not switched on on this desk yet. Coordinate with notes meanwhile."})
            op, item = q.get("op"), q.get("item")
            if op == "take" and item == "2":
                return self.send(409, {"error": "taken", "item": 2, "owner": "mate"})
            if op == "take":
                return self.send(200, {"ok": True, "item": int(item), "name": "step_bound", "statement": "(n : ℕ) : f (n + 1) ≤ 2 * f n"})
            if op == "done" and "sorry" in body:
                return self.send(422, {"error": "bad_lean", "problems": ["forbidden: sorry"]})
            if op == "done":
                return self.send(200, {"ok": True, "item": int(item), "note": 77, "complete": True})
            if op == "dead":
                return self.send(200, {"ok": True, "item": int(item), "note": 79})
            return self.send(200, {"ok": True, "item": int(item or 0)})
        if u.path == "/api/desk/bundle":
            if q.get("problem") == TEAM:
                return self.send(200, BUNDLE, "text/plain")
            if q.get("problem") == "Evil.p":
                return self.send(200, "-- uses note #1 · board #1 x · by @evil · UNVERIFIED\n#eval IO.println 1\nlemma x : True := trivial\n", "text/plain")
            return self.send(501, "-- The team board is not switched on on this desk yet.\n", "text/plain")
        if u.path == "/api/desk/note":
            if body.lstrip().upper().startswith("PLAN:"):
                return self.send(200, {"ok": True, "id": 90, "board": {"added": 2, "skipped": 0}})
            return self.send(200, {"ok": True, "id": 91})
        if u.path == "/api/desk/release":
            return self.send(200, {"ok": True})
        if u.path.startswith("/p/") and u.path.endswith("/agent.txt"):
            return self.send(200, "BRIEF FOR " + urllib.parse.unquote(u.path[3:-10]) + "\n", "text/plain")
        if u.path.startswith("/api/problems/"):
            n = q.get("reduction", "1")
            return self.send(200, {"reductionSkeleton": f"import X\nnamespace OMA.R_{n}\ndef H1 : Prop := sorry\nend OMA.R_{n}\n"})
        if u.path == "/api/stats":
            return self.send(200, {"liveAgents": 3, "solved": []})
        return self.send(404, {"error": "mock: unknown path"})
    do_GET = handle_any
    do_POST = handle_any

HTTPServer(("127.0.0.1", int(sys.argv[1])), H).serve_forever()
