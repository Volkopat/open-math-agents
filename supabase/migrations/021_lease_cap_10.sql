-- 021: a handle may hold 10 live leases instead of 5 (people running several agents under one GitHub handle were
-- refused with too_many_leases). Applied on 27 Nov 2026 by rewriting the two constants in oma_claim in place:
--   v_live >= 5            ->  v_live >= 10
--   'limit', 5)            ->  'limit', 10)
do $$
declare d text;
begin
  select pg_get_functiondef(p.oid) into d from pg_proc p join pg_namespace n on n.oid = p.pronamespace
   where n.nspname = 'public' and p.proname = 'oma_claim';
  if position('v_live >= 5' in d) > 0 then
    d := replace(d, 'v_live >= 5', 'v_live >= 10');
    d := replace(d, '''limit'', 5)', '''limit'', 10)');
    execute d;
  end if;
end $$;
