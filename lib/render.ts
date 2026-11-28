import "server-only";
import katex from "katex";
import { preload } from "react-dom";
import katexMain from "katex/dist/fonts/KaTeX_Main-Regular.woff2?url";
import katexMath from "katex/dist/fonts/KaTeX_Math-Italic.woff2?url";

const esc = (s: string) => s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");

function tex(src: string, display: boolean) {
  try {
    const html = katex.renderToString(src, { displayMode: display, throwOnError: false, strict: "ignore", trust: false, output: "html" });
    // KaTeX's @font-face rules have no font-display: typeset math stays invisible until its font arrives, and the
    // browser asks for that font only once the page is laid out. A page that renders math preloads its two main fonts
    // (React sends each preload once per page; outside a render this does nothing).
    for (const href of [katexMain, katexMath]) preload(href, { as: "font", type: "font/woff2", crossOrigin: "" });
    return html;
  } catch {
    return `<code>${esc(src)}</code>`;
  }
}

/** Upstream docstrings: Markdown-lite with $…$ / $$…$$ math. Output is escaped except KaTeX HTML. */
export function renderStatement(src: string): string {
  const parts: string[] = [];
  // pull math and code out first so their contents are never touched by markdown rules
  const re = /\$\$([\s\S]+?)\$\$|\\\[([\s\S]+?)\\\]|\$([^$\n]+?)\$|`([^`\n]+)`/g;
  let last = 0;
  let m: RegExpExecArray | null;
  const slots: string[] = [];
  let text = "";
  while ((m = re.exec(src))) {
    text += src.slice(last, m.index);
    const html = m[1] ?? m[2] ? tex((m[1] ?? m[2])!, true) : m[3] !== undefined ? tex(m[3], false) : `<code>${esc(m[4]!)}</code>`;
    slots.push(html);
    text += `\u0000${slots.length - 1}\u0000`;
    last = m.index + m[0].length;
  }
  text += src.slice(last);
  let html = esc(text)
    .replace(/\*\*([^*]+)\*\*/g, "<strong>$1</strong>")
    .replace(/(^|[\s(])\*([^*\n]+)\*(?=[\s).,;:]|$)/g, "$1<em>$2</em>")
    .replace(/\[([^\]]+)\]\((https?:\/\/[^)\s]+)\)/g, '<a href="$2" target="_blank" rel="noreferrer">$1</a>');
  html = html
    .split(/\n{2,}/)
    .map((para) => `<p>${para.replace(/\n/g, " ")}</p>`)
    .join("");
  html = html.replace(/\u0000(\d+)\u0000/g, (_, i) => slots[Number(i)]);
  parts.push(html);
  return parts.join("");
}

/** A one-line title: $…$ math rendered inline with KaTeX, everything else escaped (no paragraphs, no links). */
export function renderTitle(src: string): string {
  const re = /\$\$([^$]+?)\$\$|\$([^$\n]+?)\$/g;
  let out = "";
  let last = 0;
  let m: RegExpExecArray | null;
  while ((m = re.exec(src))) {
    out += esc(src.slice(last, m.index)) + tex((m[1] ?? m[2])!, false);
    last = m.index + m[0].length;
  }
  return out + esc(src.slice(last));
}

/** Plain text for meta descriptions. */
export function plain(src: string, max = 200) {
  const t = src.replace(/\$\$?([^$]+)\$\$?/g, "$1").replace(/[*`\\]/g, "").replace(/\s+/g, " ").trim();
  return t.length > max ? t.slice(0, max - 1) + "…" : t;
}
