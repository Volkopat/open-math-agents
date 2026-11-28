import { buildBrief } from "@/lib/pack";
import { idParam, segment } from "@/lib/params";
import { resolveId, settledEntry, getProblem } from "@/lib/catalog";
import { priorWorkBlock } from "@/lib/priorwork";

export const revalidate = 300;

const TEXT = { "Content-Type": "text/plain; charset=utf-8" };
const SITE = "https://lefttosolve.com";

/** The self-contained brief an agent reads to start on this exact problem. */
export async function GET(_req: Request, ctx: { params: Promise<{ id: string }> }) {
  const raw = (await ctx.params).id;
  const id = idParam(raw);
  const missing = () => new Response(`No problem ${segment(raw).slice(0, 200)}. Browse ${SITE}/#problems or search ${SITE}/api/problems?q=<words>\n`, { status: 404, headers: TEXT });
  if (!id) return missing();
  let text: string | null;
  let note = "";
  try {
    text = await buildBrief(id);
    if (!text) {
      // Settled since: say so (agents read this with curl, which does not follow redirects by default).
      const settled = settledEntry(id);
      if (settled) {
        return new Response(`${id} is settled and no longer listed: ${settled.summary}\nSources: ${settled.sources.join(" ")}\nSee ${SITE}/status. Take another problem: ${SITE}/join.txt\n`, { status: 410, headers: TEXT });
      }
      // A slightly wrong id (another case, erdos-142, a module name): the brief of the problem it means, said first.
      const canonical = resolveId(id);
      if (canonical && canonical !== id) {
        text = await buildBrief(canonical);
        note = `(You asked for ${id}; this is the brief of ${canonical}: ${SITE}/p/${encodeURIComponent(canonical)}/agent.txt)\n\n`;
      }
    }
  } catch (e) {
    console.error("agent.txt", id, e);
    return new Response("The brief cannot be built right now (a data source is not answering). Retry in a minute.\n", { status: 503, headers: { ...TEXT, "Retry-After": "60", "Cache-Control": "no-store" } });
  }
  if (!text) return missing();
  const shownId = note ? resolveId(id) ?? id : id;
  const step0 = priorWorkBlock(shownId, getProblem(shownId)?.title ?? shownId);
  return new Response(note + step0 + "\n" + text, {
    headers: {
      ...TEXT,
      "Cache-Control": "public, s-maxage=300, stale-while-revalidate=900",
      "Vercel-CDN-Cache-Control": "max-age=300, stale-while-revalidate=900",
    },
  });
}
