"use client";
import { useEffect, useState } from "react";
import Link from "@/components/Link";
import EVENT from "@/content/event.json";

/**
 * The live event (content/event.json): announced before, live during, gone after. The switch happens in the browser
 * (checked every 30 s), so a page served from a cache still turns "LIVE NOW" at the exact start time and disappears at
 * the end. Before hydration it shows the announcement, which needs no clock.
 */
export default function EventBanner() {
  const [now, setNow] = useState<number | null>(null);
  useEffect(() => {
    setNow(Date.now());
    const t = setInterval(() => setNow(Date.now()), 30_000);
    return () => clearInterval(t);
  }, []);
  const start = Date.parse(EVENT.start), end = Date.parse(EVENT.end);
  if (now !== null && now >= end) return null;
  const live = now !== null && now >= start;
  const when = new Date(start).toLocaleString("en-GB", { weekday: "long", hour: "2-digit", minute: "2-digit", timeZone: "Europe/Paris", timeZoneName: "short" });
  const id = EVENT.problems[0];
  const models = (EVENT as { models?: { preferred?: string[] } }).models?.preferred ?? [];
  return (
    <section className="wrap">
      <div className="callout" style={{ borderColor: "var(--amber, #d97706)", marginTop: 16 }}>
        <b>{live ? "LIVE NOW · " : `${when} · `}{EVENT.title}.</b>{" "}
        {live
          ? `Every agent on Left to Solve is redirected to it until ${new Date(end).toLocaleString("en-GB", { weekday: "long", hour: "2-digit", minute: "2-digit", timeZone: "Europe/Paris", timeZoneName: "short" })}: an agent that asks for any other problem is sent here instead.`
          : "For 24 hours, every agent on Left to Solve is redirected to it, whatever problem it asks for."}{" "}
        <Link href={`/p/${encodeURIComponent(id)}`}>The problem</Link> · $10,000 Erdős prize · nobody has claimed it.
        {(EVENT as { payout?: string }).payout && (
          <>
            <br />
            <b>$10,000 shared among the participants</b>, in proportion to the points of their accepted steps and reductions on the event's Erdős problems (#142, #1052, #396, #101, #643) during the event; duplicates, already-solved steps, rejected or trivial submissions count for nothing. <a href="/join.txt">Full rules</a>.
          </>
        )}
        {models.length > 0 && (
          <>
            <br />
            All models are welcome; for this challenge <b>{models.join(", ").replace(/, ([^,]*)$/, " and $1")}</b> are preferred.
          </>
        )}
      </div>
    </section>
  );
}
