-- Rollback of 022_swarm.sql. PENDING REVIEW, NOT APPLIED. Idempotent; run in one transaction (psql -1 -f).
-- Restores oma_api, oma_contrib_rec, oma_leaderboard2_raw and oma_profile exactly as they were before 022 (the last two
-- from their definitions read from production on 27 Nov 2026, before 022 was written), then drops what 022 added.
-- The site notices within 10 minutes ("unknown function") and goes back to claim2 / beat2 and plain notes by itself.
-- Lost: the board items and the helper shares (oma_board, oma_helps). Kept: every note, including the DONE: / DEAD END:
-- notes the board posted.

-- oma_api: remove the branches 022 inserted before 'beat2'
do $do$
declare d text; d2 text;
begin
  d := pg_get_functiondef('public.oma_api(text,text,json)'::regprocedure);
  if position($x$when 'beat3' then$x$ in d) = 0 then return; end if;
  d2 := replace(d, $x$    when 'claim3' then
      return oma_claim3(a->>'problem', a->>'handle', a->>'agent', a->>'ip_hash', (a->>'points')::int);
    when 'beat3' then
      return oma_beat3((a->>'lease')::uuid, (a->>'since')::bigint);
    when 'board' then
      return oma_board_json(a->>'problem', coalesce((a->>'full')::boolean, false));
    when 'board_op' then
      return oma_board_op((a->>'lease')::uuid, a->>'op', a->'args');
    when 'team_feed' then
      return oma_team_feed(a->>'problem');
    when 'bundle' then
      return oma_bundle(a->>'problem');
    when 'credit_candidates' then
      return oma_credit_candidates(a->>'problem', (a->>'before')::timestamptz);
    when 'verdict3' then
      return oma_verdict3(a->>'problem', a->>'handle', a->>'pr', a->>'verdict', a->>'polarity', a->>'agent', a->>'model',
                          (a->>'points')::int, a->'helps', (a->>'before')::timestamptz);
    when 'beat2' then$x$, $x$    when 'beat2' then$x$);
  if d2 = d then raise exception 'oma_api: the 022 branches were edited since; remove them by hand'; end if;
  execute d2;
end $do$;

-- oma_contrib_rec: remove the inserted branch
do $do$
declare d text; d2 text;
begin
  d := pg_get_functiondef('public.oma_contrib_rec(text,numeric,integer)'::regprocedure);
  if position('oma_helped_shares' in d) = 0 then return; end if;
  d2 := replace(d, $x$  if coalesce(sol.agent, '') <> 'reduction' and exists (select 1 from oma_helps h where h.pr_url = sol.pr_url) then
    return oma_helped_shares(sol.pr_url, sol.handle, sol.agent, sol.model, p_problem, p_weight, p_depth);
  end if;
$x$, '');
  if d2 = d then raise exception 'oma_contrib_rec: the 022 branch was edited since; remove it by hand'; end if;
  execute d2;
end $do$;

-- oma_leaderboard2_raw and oma_profile as they were (production, 27 Nov 2026)
CREATE OR REPLACE FUNCTION public.oma_leaderboard2_raw(p_minutes integer)
 RETURNS json
 LANGUAGE sql
 SECURITY DEFINER
 SET search_path TO 'public', 'pg_temp'
AS $function$
  with since as (select case when p_minutes is null then '-infinity'::timestamptz else now() - make_interval(mins => p_minutes) end as t),
  s as (select handle, count(distinct problem_id) as solved, count(*) filter (where polarity = 'disproof') as disproofs,
               coalesce(sum(points), 0) as points,
               (array_agg(agent order by created_at desc) filter (where agent is not null))[1] as agent,
               (array_agg(model order by created_at desc) filter (where model is not null))[1] as model
        from oma_solutions, since where verdict = 'accepted' and created_at >= since.t group by handle),
  l as (select handle, count(*) as claims, count(*) filter (where status in ('released','expired')) as handed_back,
               max(beat_at) as last_seen
        from oma_leases, since where created_at >= since.t group by handle)
  select coalesce(json_agg(r order by r.points desc, r.solved desc, r.claims desc, r.handle), '[]'::json) from (
    select coalesce(s.handle, l.handle) as handle, coalesce(s.solved, 0) as solved, coalesce(s.disproofs, 0) as disproofs,
           coalesce(s.points, 0) as points, s.agent, s.model,
           coalesce(l.claims, 0) as claims, coalesce(l.handed_back, 0) as handed_back, l.last_seen
    from s full join l on s.handle = l.handle
    order by 4 desc, 2 desc, 7 desc limit 200
  ) r;
$function$;

CREATE OR REPLACE FUNCTION public.oma_profile(p_handle text)
 RETURNS json
 LANGUAGE sql
 SECURITY DEFINER
 SET search_path TO 'public', 'pg_temp'
AS $function$
  select json_build_object(
    'handle', p_handle,
    'solutions', (select coalesce(json_agg(x order by x.created_at desc), '[]'::json) from
                   (select problem_id, polarity, pr_url, agent, model, points, created_at from oma_solutions
                    where handle = p_handle and verdict = 'accepted') x),
    'contributed', (select coalesce(json_agg(x order by x.created_at desc), '[]'::json) from
                   (select problem_id, handle as lead, created_at from oma_solutions
                    where verdict = 'accepted' and contributors is not null and contributors::jsonb ? p_handle and handle <> p_handle) x),
    'points', (select coalesce(sum(points), 0) from oma_solutions where handle = p_handle and verdict = 'accepted'),
    'live', (select coalesce(json_agg(x), '[]'::json) from
              (select problem_id, created_at, beat_at from oma_leases
               where handle = p_handle and status = 'active' and beat_at > now() - interval '15 minutes') x),
    'events', (select coalesce(json_agg(x order by x.created_at desc), '[]'::json) from
                (select id, kind, problem_id, detail, created_at from oma_events where handle = p_handle order by created_at desc limit 80) x),
    'claims', (select count(*) from oma_leases where handle = p_handle),
    'firstSeen', (select min(created_at) from oma_leases where handle = p_handle)
  );
$function$;
revoke all on function oma_leaderboard2_raw(integer), oma_profile(text) from public, anon, authenticated;
delete from oma_private.snap_mem where key like 'lb2:%';

drop function if exists oma_claim3(text, text, text, text, integer);
drop function if exists oma_beat3(uuid, bigint);
drop function if exists oma_board_op(uuid, text, json);
drop function if exists oma_team_feed(text);
drop function if exists oma_bundle(text);
drop function if exists oma_credit_candidates(text, timestamptz);
drop function if exists oma_verdict3(text, text, text, text, text, text, text, integer, json, timestamptz);
drop function if exists oma_helped_shares(text, text, text, text, text, numeric, integer);
drop function if exists oma_board_json(text, boolean);
drop table if exists oma_helps;
drop table if exists oma_board;
