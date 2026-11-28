import { decodeParam } from "@/lib/site";

/**
 * Dynamic route segments (/p/[id], /api/problems/[id], /a/[handle], ...). The router hands them over already decoded;
 * the pages used to decode them once more, and decodeURIComponent throws on any lone "%" (a Lean statement such as
 * "∀ n : ℕ, n % 8 = 7 → A n" pasted in place of an id): that uncaught URIError was a 500. Decoding here never throws.
 */
export const segment = decodeParam;

/** Problem, step and reduction ids: letters, digits and . _ ' - (the catalogue's longest is 115 characters; nested
 * step ids grow with every level). Anything else is no id: a 404 without a database or D1 read. */
export const ID_RE = /^[A-Za-z0-9._'-]{1,300}$/;
export function idParam(raw: string): string | null {
  const id = segment(raw);
  return ID_RE.test(id) ? id : null;
}

/** A GitHub login. */
export const HANDLE_RE = /^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$/;
