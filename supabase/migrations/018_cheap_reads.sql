-- 018: reads stop writing to disk, heartbeats stop waiting for it (after the 2026-11-27 17:30-21:00 UTC outage: disk
-- I/O throttled, checkpoints of ~1,500 buffers took 150-300 s, statements timed out, then every oma_api call failed).
-- Every statement here is non-blocking (CREATE TABLE, INSERT into the new table, CREATE OR REPLACE FUNCTION with the same
-- signature and the same answers). Apply in one transaction; 019 (an index, CONCURRENTLY) goes separately.

-- 1. The snapshot cache (014) moves to an UNLOGGED table. oma_private.cached() runs on reads (stats, live, steps,
--    solved, leaderboard2, calendar, active_ids) and upserted into a logged table on every refresh: one WAL record, one
--    commit waiting for fsync, and dirty pages (TOAST included: solved and steps are hundreds of KB) for the next
--    checkpoint to write, per read. An unlogged table writes no WAL, its commits do not wait for the disk and
--    checkpoints skip its pages. After a crash it comes back empty, which for a cache only means one recomputation.
create unlogged table if not exists oma_private.snap_mem (key text primary key, value json not null, at timestamptz not null default now());
revoke all on oma_private.snap_mem from public, anon, authenticated;
-- Start from the current values, so the switch costs no recomputation burst.
insert into oma_private.snap_mem (key, value, at) select key, value, at from oma_private.snap on conflict (key) do nothing;

create or replace function oma_private.cached(p_key text, p_ttl interval, p_sql text) returns json
language plpgsql volatile security definer set search_path = public, pg_temp as $$
declare v json; t timestamptz;
begin
  select value, at into v, t from oma_private.snap_mem where key = p_key;
  if v is not null and t > now() - p_ttl then return v; end if;
  -- Someone else is refreshing this key: serve the last value instead of computing it again.
  if v is not null and not pg_try_advisory_xact_lock(hashtext('oma_snap:' || p_key)) then return v; end if;
  execute p_sql into v;
  insert into oma_private.snap_mem (key, value, at) values (p_key, coalesce(v, 'null'::json), now())
    on conflict (key) do update set value = excluded.value, at = excluded.at;
  return v;
end $$;
revoke all on function oma_private.cached(text, interval, text) from public, anon, authenticated;

-- 2. steps(parent): one problem's subtree is a few index lookups; caching it wrote one snapshot row per problem page
--    visited (thousands of keys, almost all '[]'). Only the full list (parent null) stays cached.
create or replace function oma_steps_list(p_parent text) returns json language sql volatile security definer set search_path = public, pg_temp as
  $$ select case when p_parent is null then oma_private.cached('steps:*', interval '30 seconds', 'select oma_steps_list_raw(NULL)')
                 else oma_steps_list_raw(p_parent) end $$;
revoke all on function oma_steps_list(text) from public, anon, authenticated;

-- 3. Calendar: the same answer in one pass over the events of the period, instead of six counts per day (each a scan
--    of every event of a kind, 'people' a scan of the whole table): 720 scans for /calendar's 120 days.
create or replace function oma_calendar_raw(p_days integer) returns json
language sql stable security definer set search_path = public, pg_temp as $$
  with b as (select (now() at time zone 'utc')::date as today, least(greatest(coalesce(p_days, 60), 1), 366) as n),
  d as (select generate_series(b.today - (b.n - 1), b.today, interval '1 day')::date as day from b),
  g as (
    select (e.created_at at time zone 'utc')::date as day,
           count(*) filter (where e.kind = 'claim') as claims,
           count(*) filter (where e.kind = 'release') as released,
           count(*) filter (where e.kind = 'submit') as submitted,
           count(*) filter (where e.kind = 'accepted') as solved,
           count(*) filter (where e.kind = 'reduced') as reduced,
           count(distinct e.handle) as people
    from oma_events e, b
    where e.created_at >= ((b.today - (b.n - 1))::timestamp at time zone 'utc')
    group by 1
  )
  select coalesce(json_agg(json_build_object(
    'day', d.day, 'claims', coalesce(g.claims, 0), 'released', coalesce(g.released, 0), 'submitted', coalesce(g.submitted, 0),
    'solved', coalesce(g.solved, 0), 'reduced', coalesce(g.reduced, 0), 'people', coalesce(g.people, 0)
  ) order by d.day desc), '[]'::json)
  from d left join g on g.day = d.day;
$$;
revoke all on function oma_calendar_raw(integer) from public, anon, authenticated;

-- 4. Heartbeats (~1,600 an hour, one per live agent every 7 minutes): the commit no longer waits for the WAL to reach the
--    disk (a beat lost in a crash is harmless: the next one, 7 minutes later, restores it), and a beat within a minute of
--    the previous one does not rewrite the row (beat_at is indexed, so each rewrite also writes every index of
--    oma_leases). The answers are unchanged; beat_at lags by at most a minute against a 15-minute window.
-- (Superseded by 020_lease_revive.sql: an expired lease comes back on the next beat; same body as 020 here so that
--  applying 018 after 020 does not undo it.)
create or replace function oma_beat(p_lease uuid)
returns json language plpgsql security definer set search_path = public, pg_temp as $$
declare v_row oma_leases;
begin
  perform set_config('synchronous_commit', 'off', true);
  select * into v_row from oma_leases where id = p_lease;
  if not found then return json_build_object('error', 'unknown_lease'); end if;
  if v_row.status not in ('active', 'expired') then return json_build_object('stop', true, 'status', v_row.status); end if;
  if exists(select 1 from oma_solutions where problem_id = v_row.problem_id and verdict = 'accepted') then
    update oma_leases set status = 'settled', ended_at = now() where id = p_lease;
    return json_build_object('stop', true, 'status', 'settled');
  end if;
  if v_row.status = 'expired' then
    update oma_leases set status = 'active', ended_at = null, beat_at = now() where id = p_lease;
  elsif v_row.beat_at < now() - interval '60 seconds' then
    update oma_leases set beat_at = now() where id = p_lease;
  end if;
  return json_build_object('ok', true);
end $$;

-- Not applied here (DROP is the maintainer's call): beats would become HOT updates (heap only, no index writes at all)
-- once beat_at is in no index. The only index on it is oma_leases_active_beat (012), used by oma_live; with
--   drop index concurrently oma_leases_active_beat;  alter table oma_leases set (fillfactor = 80);
-- oma_live falls back to oma_leases_active (problem_id) where status = 'active'.
