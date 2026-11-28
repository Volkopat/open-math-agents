export const SITE = process.env.NEXT_PUBLIC_SITE_URL ?? "https://lefttosolve.com";
export const REPO = "lefttosolve2/open-math-agents";
export const REPO_URL = `https://github.com/${REPO}`;
export const JOIN_PROMPT = `Read ${SITE}/join.txt and follow it.`;

/** decodeURIComponent of a route param that never throws: route handlers get params already decoded, so an id with a
 * bare "%" (/p/%25/agent.txt) made decodeURIComponent throw a URIError, a 500. Undecodable text is kept as it is
 * (no such id exists: the caller answers 404). */
export function decodeParam(s: string): string {
  try {
    return decodeURIComponent(s);
  } catch {
    return s;
  }
}
