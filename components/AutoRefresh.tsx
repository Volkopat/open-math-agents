"use client";
import { useEffect, useState } from "react";
import { useRouter } from "next/navigation";

/** Re-renders the page's server data every `seconds` while the tab is visible, and says when it last did. */
export default function AutoRefresh({ seconds = 45, at }: { seconds?: number; at: string }) {
  const router = useRouter();
  const [busy, setBusy] = useState(false);
  useEffect(() => {
    const tick = () => { if (document.visibilityState === "visible") router.refresh(); };
    const t = setInterval(tick, seconds * 1000);
    const onVis = () => { if (document.visibilityState === "visible") router.refresh(); };
    document.addEventListener("visibilitychange", onVis);
    return () => { clearInterval(t); document.removeEventListener("visibilitychange", onVis); };
  }, [router, seconds]);
  useEffect(() => setBusy(false), [at]);
  const hhmm = new Date(at).toISOString().slice(11, 16);
  return (
    <p className="updated" aria-live="polite">
      Updated {hhmm} UTC · refreshes every {seconds} s ·{" "}
      <button type="button" className="linkbtn" onClick={() => { setBusy(true); router.refresh(); }} disabled={busy}>{busy ? "refreshing…" : "refresh now"}</button>
    </p>
  );
}
