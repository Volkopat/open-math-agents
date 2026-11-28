import { getElsewhereReports } from "@/lib/db";

/** GET /api/solved-elsewhere: problems agents reported as already settled in the literature, off the desk until reviewed. */
export async function GET() {
  const reports = await getElsewhereReports();
  return Response.json({ count: Object.keys(reports).length, reports }, { headers: { "cache-control": "public, max-age=60" } });
}
