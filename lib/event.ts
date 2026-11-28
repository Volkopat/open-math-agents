import EVENT from "@/content/event.json";
import PLACEHOLDERS from "@/data/placeholders.json";
import GUIDES from "@/content/event_guides.json";

/** The live event (content/event.json), with the helpers the desk uses. `stepsOf` may be one prefix or several;
 * `excludeSteps` lists step ids (or prefixes ending in ".") the event does not hand out, e.g. steps already settled
 * elsewhere; `problems` the catalogue problems of the event. */
type Ev = typeof EVENT & { stepsOf: string | string[]; excludeSteps?: string[]; payout?: string };
export const EV = EVENT as Ev;
const prefixes = (): string[] => (Array.isArray(EV.stepsOf) ? EV.stepsOf : [EV.stepsOf]).filter(Boolean);
export const eventOnAt = (t = Date.now()) => t >= Date.parse(EV.start) && t < Date.parse(EV.end);
/** A step of the event (under one of its prefixes) that the event does not exclude. */
export const isEventStep = (id: string) =>
  prefixes().some((p) => id.startsWith(p)) && !(EV.excludeSteps ?? []).some((x) => id === x || (x.endsWith(".") && id.startsWith(x)));
/** Part of the event: one of its problems, or a step under one of its prefixes (excluded steps included: an agent
 * already on one is not stopped, it is just no longer handed out). */
export const inEvent = (id: string) => EV.problems.includes(id) || prefixes().some((p) => id.startsWith(p));

/** Event problems that ask for a value (placeholder := sorry): nothing an agent submits on them can be accepted
 * automatically (a formula goes to a person), so during the event they are neither handed out nor kept: agents on them
 * are sent to the open steps. */
export const valueOnly = (id: string) => EV.problems.includes(id) && id in (PLACEHOLDERS as Record<string, string[]>);
type Guide = { guide: string; sources?: string[] };
/** Strategy notes for the event's open steps (content/event_guides.json), by longest matching id prefix. */
export function guideFor(id: string): Guide | undefined {
  const g = GUIDES as Record<string, Guide>;
  let best = "";
  for (const k of Object.keys(g)) if ((id === k || id.startsWith(k + ".")) && k.length > best.length) best = k;
  return best ? g[best] : undefined;
}
