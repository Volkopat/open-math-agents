import { getSupporters } from "@/lib/supporters";
import type { Metadata } from "next";
import { notFound } from "next/navigation";
import ProfileView from "@/components/ProfileView";
import { getProfile, getLeaderboard2, getSolved, getSteps } from "@/lib/db";
import { segment } from "@/lib/params";
import { submissionsOf, type Submission } from "@/lib/submissions";

export const revalidate = 120;
type Props = { params: Promise<{ handle: string }> };

const HANDLE = /^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$/;

export async function generateMetadata({ params }: Props): Promise<Metadata> {
  const h = segment((await params).handle);
  if (!HANDLE.test(h)) return {};
  return { title: `@${h}`, description: `@${h} on Left to Solve: rank, points, every problem taken and every proof checked by Lean.` };
}

export default async function Person({ params }: Props) {
  const h = segment((await params).handle);
  if (!HANDLE.test(h)) notFound();
  // getSolved and getSteps are the shared site-wide reads (one cached copy), used for the badges and the charts.
  const [p, board, supporters, records, steps] = await Promise.all([getProfile(h), getLeaderboard2(), getSupporters(), getSolved(), getSteps()]);
  const subs = await submissionsOf(h, p).catch(() => ({ items: [] as Submission[], list: null, now: null }));
  return (
    <ProfileView h={h} p={p} board={board} records={records} stepParent={new Map(steps.map((s) => [s.id, s.parent]))}
      supporter={supporters.get(h.toLowerCase())} subs={subs} />
  );
}
