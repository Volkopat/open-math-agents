-- READ-ONLY export for the Erdős #142 event payout (sponsor's $10,000 split by work done).
-- Run at the end of the event (2026-11-29 17:00 UTC) in the Supabase SQL editor and download the results as CSV.
-- SELECT statements only: nothing is written.

-- 1. Every desk action on #142 and its steps during the event, per handle and kind
--    (claim, release, submit, accepted, rejected, fault, note, reduced).
select handle, kind, count(*) as n
from oma_events
where (problem_id like 'Erdos142.%' or problem_id like 'Erdos1052.%' or problem_id like 'Erdos396.%' or problem_id like 'Erdos101.%' or problem_id like 'Erdos643.%')
  and created_at >= '2026-11-28 17:00:00+00' and created_at < '2026-11-29 17:00:00+00'
group by handle, kind
order by handle, kind;

-- 2. Accepted steps and reductions during the event, with their points, per handle.
select handle, problem_id, polarity, points, pr_url, created_at
from oma_solutions
where (problem_id like 'Erdos142.%' or problem_id like 'Erdos1052.%' or problem_id like 'Erdos396.%' or problem_id like 'Erdos101.%' or problem_id like 'Erdos643.%') and verdict = 'accepted'
  and created_at >= '2026-11-28 17:00:00+00' and created_at < '2026-11-29 17:00:00+00'
order by handle, created_at;

-- 3. Leases taken on #142 during the event (time spent), per handle.
select handle, problem_id, status, created_at, beat_at
from oma_leases
where (problem_id like 'Erdos142.%' or problem_id like 'Erdos1052.%' or problem_id like 'Erdos396.%' or problem_id like 'Erdos101.%' or problem_id like 'Erdos643.%')
  and created_at >= '2026-11-28 17:00:00+00' and created_at < '2026-11-29 17:00:00+00'
order by handle, created_at;
