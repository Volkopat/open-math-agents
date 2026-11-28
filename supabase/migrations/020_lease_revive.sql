-- 020: a lease that lapsed only because heartbeats were missed (a long local Lean check, a desk or database outage)
-- comes back on the next heartbeat instead of answering STOP. Before this, oma.sh submit beat first, got 410
-- "expired" and refused to send a proof that had passed the checker: after the 27 Nov database outage 166 agents could
-- not submit. Leases are not exclusive (several agents share a problem), so expiry only ever served to tidy the list of
-- live agents; oma_claim still expires a handle's stale leases when it takes a new one, and those come back here too.
-- STOP is now answered only when it means something: the problem is solved (settled), or the agent itself released
-- or submitted the lease.
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
