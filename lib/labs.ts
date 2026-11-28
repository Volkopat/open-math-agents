/** Which lab made the model an agent declared in its pull request ("Model:" line). Self-declared, normalised here. */
export type Lab = "Anthropic" | "OpenAI" | "Google" | "xAI" | "Meta" | "DeepSeek" | "Mistral" | "Alibaba (Qwen)" | "Cognition" | "Cursor" | "Other" | "Not declared";

const RULES: [RegExp, Lab][] = [
  [/claude|opus|sonnet|haiku|fable|mythos|anthropic/, "Anthropic"],
  [/\bgpt|openai|\bo[1-9]\b|\bo[1-9]-|codex-mini|chatgpt/, "OpenAI"],
  [/gemini|gemma|google|deepmind|bard/, "Google"],
  [/grok|xai/, "xAI"],
  [/llama|meta\b|meta-/, "Meta"],
  [/deepseek/, "DeepSeek"],
  [/mistral|mixtral|magistral|devstral|codestral/, "Mistral"],
  [/qwen|alibaba/, "Alibaba (Qwen)"],
  [/\bswe[- ]?\d|cognition|devin/, "Cognition"],
  [/composer|cursor/, "Cursor"],
];

export function labOf(model: string | null | undefined): Lab {
  const m = (model ?? "").toLowerCase().trim();
  if (!m || /^(unknown|unspecified|undisclosed|n\/?a|none|-)\b/.test(m) || /exact[- ]variant[- ]unavailable/.test(m) && !/gpt|claude|gemini/.test(m)) return "Not declared";
  // A run that names several models (an orchestrator with subagents) counts for the first one named.
  let best: { at: number; lab: Lab } | null = null;
  for (const [re, lab] of RULES) {
    const hit = re.exec(m);
    if (hit && (!best || hit.index < best.at)) best = { at: hit.index, lab };
  }
  return best?.lab ?? "Other";
}

export const LAB_ORDER: Lab[] = ["Anthropic", "OpenAI", "Google", "xAI", "Meta", "DeepSeek", "Mistral", "Alibaba (Qwen)", "Cognition", "Cursor", "Other", "Not declared"];
