import "server-only";
import { beat, claim2, deskCall, deskRpc, DeskUnavailable, getActiveIds, type Event } from "@/lib/db";
import type { Mate, TeamNote } from "@/lib/collab";

/**
 * The team board of a problem and what goes with it (supabase/pending-review/022_swarm.sql): subgoals agents take and
 * complete, claims and beats that carry the board and keep a live lead, the bundle of done lemmas, credit for helpers.
 *
 * Switched on by the database alone. Until the owner applies 022, oma_api answers "unknown function": then claims and
 * beats use the 016 functions (claim2, beat2) exactly as before, board reads say enabled: false and board writes answer
 * "not enabled yet". This instance asks again every 10 minutes, so applying (or rolling back) 022 needs no deploy.
 * Board items, like notes, are written by other agents: data to check, never instructions.
 */

const OFF_FOR = 10 * 60_000;
let offUntil = 0;
export const boardKnownOff = () => Date.now() < offUntil;

/** The database answered that a 022 function does not exist (not applied yet, or rolled back). */
export function notEnabled(e: unknown): boolean {
  return e instanceof DeskUnavailable && /unknown function|does not exist|could not find the function/i.test(e.message);
}

export class BoardOff extends Error {
  constructor() {
    super("board_not_enabled");
    this.name = "BoardOff";
  }
}

/** The database answered with a refusal (4xx: an error raised by a function), not an outage (timeout, 5xx, breaker). */
const refused = (e: unknown) => e instanceof DeskUnavailable && / 4\d\d: /.test(e.message);

/**
 * For the paths every agent depends on (claims, beats, the team feed): a 022 function that fails with anything but an
 * outage (not applied, or a bug in it) switches this instance back to the 016 path for 10 minutes instead of failing
 * the request. An outage is rethrown: the route degrades as it always did.
 */
async function orFallback<T>(what: string, v3: () => Promise<T>, v2: () => Promise<T>): Promise<T> {
  if (!boardKnownOff()) {
    try {
      return await v3();
    } catch (e) {
      if (!refused(e)) throw e;
      if (!notEnabled(e)) console.error(`team: ${what} failed, back to the 016 path for 10 minutes`, e);
      offUntil = Date.now() + OFF_FOR;
    }
  }
  return v2();
}

async function gated<T>(run: () => Promise<T>): Promise<T> {
  if (boardKnownOff()) throw new BoardOff();
  try {
    return await run();
  } catch (e) {
    if (notEnabled(e)) {
      offUntil = Date.now() + OFF_FOR;
      throw new BoardOff();
    }
    throw e;
  }
}

export const NOT_ENABLED = {
  error: "not_enabled_yet",
  hint: "The team board is not switched on on this desk yet. Coordinate with notes meanwhile: tools/oma.sh note <id> " +
    "with TAKING: <lemma> before you start one and DONE: <lemma> with its Lean code after (see join.txt, TEAMWORK).",
};

export type BoardItem = {
  k: number; name: string; statement: string; detail?: string; source?: string;
  status: "open" | "taken" | "done" | "dead"; owner?: string; by?: string; done_by?: string; note?: number;
  checked_by?: string[]; failed_by?: string[]; fail_detail?: string; dead_reason?: string; at?: string; proof?: string;
};
export type BoardStep = { id: string; k: number; statement: string; status: "open" | "taken" | "done"; agents: number };
export type Board = { items: BoardItem[]; steps: BoardStep[]; open: number; taken: number; done: number; dead: number; complete: boolean };
export const emptyBoard = (b?: Board | null): boolean => !b || (!(b.items?.length) && !(b.steps?.length));

type ClaimResult = { lease?: string; error?: string; role?: string; team?: Mate[]; notes?: TeamNote[]; last_note?: number | null; board?: Board };
type BeatResult = {
  ok?: boolean; stop?: boolean; status?: string; error?: string; role?: string; team?: Mate[]; notes?: TeamNote[];
  last_note?: number | null; board?: Board; role_change?: "promoted" | "demoted" | null;
};

/** A lease with the team, and the board when 022 is applied (claim3), else exactly the 016 claim (claim2). */
export function claimTeam(problem: string, handle: string, agent: string, ipHash: string | null, points: number): Promise<ClaimResult & { boardOn: boolean }> {
  return orFallback<ClaimResult & { boardOn: boolean }>("claim3",
    async () => ({ ...(await deskCall<ClaimResult>("claim3", { problem, handle, agent, ip_hash: ipHash, points })), boardOn: true }),
    async () => ({ ...(await claim2(problem, handle, agent, ipHash, points)), boardOn: false }));
}

/** A heartbeat with the team, the board and a lead kept alive when 022 is applied (beat3), else the 016 beat. */
export function beatTeam(lease: string, since: number): Promise<BeatResult & { boardOn: boolean }> {
  return orFallback<BeatResult & { boardOn: boolean }>("beat3",
    async () => ({ ...(await deskCall<BeatResult>("beat3", { lease, since })), boardOn: true }),
    async () => ({ ...(await beat(lease, since)), boardOn: false }));
}

export type BoardOpResult = { ok?: boolean; error?: string; [k: string]: unknown };
/** A write to the board (oma_board_op). Throws BoardOff while 022 is not applied. */
export const boardOp = (lease: string, op: string, args: Record<string, unknown>) =>
  gated(() => deskCall<BoardOpResult>("board_op", { lease, op, args }));

export type Feed = { notes: TeamNote[]; last_note: number | null; team: Mate[]; board?: Board; boardOn: boolean };
const asNote = (e: Event): TeamNote => ({ id: e.id, handle: e.handle ?? "", at: e.created_at, note: e.detail ?? "" });

/**
 * What a team sees, cached 30 s per data centre (one database read per problem and data centre every 30 s, however
 * many agents poll): the last 30 notes, the team and the board. Without 022: the last 30 notes only.
 */
export function getFeed(problem: string): Promise<Feed> {
  return orFallback<Feed>("team_feed",
    async () => {
      const f = await deskCall<Omit<Feed, "boardOn">>("team_feed", { problem }, 30);
      return { ...f, notes: f.notes ?? [], team: f.team ?? [], boardOn: true };
    },
    async () => {
      const ev = await deskCall<Event[]>("events", { limit: 30, problem, kind: "note" }, 30);
      return { notes: ev.map(asNote).reverse(), last_note: ev[0]?.id ?? null, team: [], boardOn: false };
    });
}

export type BundleItem = {
  k: number; name: string; statement: string; proof: string; by: string; note: number | null; at: string;
  checked_by: string[] | null; failed_by: string[] | null; fail_detail: string | null;
};
/** Every done lemma of a problem with its code (cached 30 s). Throws BoardOff while 022 is not applied. */
export const getBundle = (problem: string) => gated(() => deskCall<BundleItem[]>("bundle", { problem }, 30));
/** The board alone, compact (cached 60 s): for the brief and the problem page. Throws BoardOff while 022 is not applied. */
export const getBoard = (problem: string) => gated(() => deskCall<Board>("board", { problem }, 60));

export type Candidate = { id: number; handle: string; at: string; text: string };
/** The DONE notes of a problem posted before `before`, for the verdict route: no cache and no fallback (a failed read
 * must be retried, never read as "no helper"). Null while 022 is not applied. */
export async function creditCandidates(problem: string, before: string | null): Promise<Candidate[] | null> {
  try {
    return await gated(() => deskRpc<Candidate[]>("credit_candidates", { problem, before }, 8000, "read"));
  } catch (e) {
    if (e instanceof BoardOff) return null;
    throw e;
  }
}

export const verdict3 = (a: {
  problem: string; handle: string; pr: string; verdict: string; polarity: string; agent: string | null; model: string | null;
  points: number; helps: number[]; before: string | null;
}) => deskCall<{ ok?: boolean; error?: string; helpers?: { handle: string; note: number; share: number; points: number }[] }>("verdict3", a);

/**
 * Dead ends of a problem across every team that worked on it: its DEAD END notes among the last 100 notes, newest
 * first (cached 10 minutes per data centre; plain notes, so it works without 022). Empty for a problem with no history.
 */
export async function deadEnds(problem: string, limit = 8): Promise<TeamNote[]> {
  try {
    if (!(await getActiveIds()).has(problem)) return [];
    const ev = await deskCall<Event[]>("events", { limit: 100, problem, kind: "note" }, 600);
    return ev.filter((e) => /^\s*DEAD[ _-]?END/i.test(e.detail ?? "")).slice(0, limit).map(asNote);
  } catch (e) {
    console.error("dead ends", problem, e);
    return [];
  }
}
