-- Supabase performance advisor (2026-11-28): oma_steps has two identical indexes, oma_steps_parent and
-- oma_steps_parent2. Keep one. Safe to run at any time; no data change. Review, then run in the SQL editor.
drop index if exists public.oma_steps_parent2;
