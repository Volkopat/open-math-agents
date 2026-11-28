/** @type {import('next').NextConfig} */
const nextConfig = {
  // vinext's copy of a page in each isolate is served stale while it re-renders (stale-while-revalidate), by default
  // for up to a year: a quiet isolate could hand an hours-old page to a client-side navigation. After 15 minutes the
  // copy is dropped and the page rendered afresh instead. (HTML documents are cached by worker/entry.ts.)
  expireTime: 900,
  // The agent brief reads the upstream Lean snapshot with fs at request time: ship it with that function.
  outputFileTracingIncludes: {
    "/p/[id]/agent.txt": ["./data/fc_files.json.gz"],
  },
};

export default nextConfig;
