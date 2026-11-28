-- Heartbeat answers which problem the lease is on (owner's rule for the Erdős #142 event: every agent on the event).
-- Same function as in 016_teams.sql, with one added field, 'problem'. Read-only for the lease row; nothing else changes.
-- With it, /api/desk/beat can tell an agent still holding an older lease on another problem to move to the event, even
-- when its tool does not pass ?problem= (app/api/desk/beat/route.ts already reads r.problem when present).
create or replace function oma_beat2(p_lease uuid, p_since bigint) returns json
language plpgsql volatile security definer set search_path = public, pg_temp as $$
declare r json; v_row oma_leases;
begin
  r := oma_beat(p_lease);
  if (r->>'ok') is null then return r; end if;
  select * into v_row from oma_leases where id = p_lease;
  return json_build_object('ok', true, 'problem', v_row.problem_id, 'role', coalesce(v_row.role, 'helper'), 'team', oma_team(v_row.problem_id, p_lease),
                           'notes', oma_notes_since(v_row.problem_id, p_since, 12),
                           'last_note', (select max(id) from oma_events where problem_id = v_row.problem_id and kind = 'note'));
end $$;
