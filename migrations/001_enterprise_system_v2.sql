CREATE EXTENSION IF NOT EXISTS pgcrypto;

CREATE TABLE IF NOT EXISTS enterprise_exercises (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  client_id TEXT, scenario_id TEXT, title TEXT NOT NULL,
  status TEXT NOT NULL DEFAULT 'draft',
  started_at TIMESTAMPTZ, ended_at TIMESTAMPTZ,
  created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

CREATE TABLE IF NOT EXISTS enterprise_participants (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  exercise_id UUID REFERENCES enterprise_exercises(id) ON DELETE CASCADE,
  participant_key TEXT NOT NULL, display_name TEXT, email TEXT, role TEXT,
  observer BOOLEAN DEFAULT FALSE, joined_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  UNIQUE(exercise_id, participant_key)
);

CREATE TABLE IF NOT EXISTS enterprise_decision_records (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  exercise_id UUID REFERENCES enterprise_exercises(id) ON DELETE CASCADE,
  participant_id UUID REFERENCES enterprise_participants(id) ON DELETE CASCADE,
  decision_id TEXT NOT NULL, selected_option TEXT,
  is_validated BOOLEAN DEFAULT FALSE, is_borderline BOOLEAN DEFAULT FALSE,
  risk_impact TEXT DEFAULT 'medium', business_impact TEXT,
  response_time_ms INTEGER, submitted_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  UNIQUE(exercise_id, participant_id, decision_id)
);

CREATE TABLE IF NOT EXISTS enterprise_audit_events (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  exercise_id UUID REFERENCES enterprise_exercises(id) ON DELETE CASCADE,
  actor_key TEXT, actor_role TEXT, event_type TEXT NOT NULL,
  event_payload JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

CREATE TABLE IF NOT EXISTS enterprise_playbook_expectations (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  exercise_id UUID REFERENCES enterprise_exercises(id) ON DELETE CASCADE,
  decision_id TEXT NOT NULL, expected_action TEXT NOT NULL,
  owner_role TEXT, severity TEXT DEFAULT 'medium',
  created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  UNIQUE(exercise_id, decision_id)
);

CREATE INDEX IF NOT EXISTS idx_enterprise_decisions_exercise ON enterprise_decision_records(exercise_id);
CREATE INDEX IF NOT EXISTS idx_enterprise_participants_exercise ON enterprise_participants(exercise_id);
CREATE INDEX IF NOT EXISTS idx_enterprise_audit_exercise ON enterprise_audit_events(exercise_id, created_at);
