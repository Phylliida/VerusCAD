#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LOOPER_URL="${LOOPER_URL:-http://127.0.0.1:3456/run}"
LOOPER_API_TOKEN="${LOOPER_API_TOKEN:-}"
DEFAULT_MESSAGE='Codex task triggered from run-codex-task.sh'

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  cat <<'EOF'
usage: ./scripts/run-codex-task.sh [zulip_message]

POSTs to the looper server (/run) to:
1) send a Zulip DM
2) kill existing VS Code windows/processes
3) open a fresh Codex window/panel
4) send a prompt to the Codex composer (defined by looper/server.py)

environment:
  LOOPER_URL        default: http://127.0.0.1:3456/run
  LOOPER_API_TOKEN  optional bearer token for looper auth

arguments:
  zulip_message     optional DM text; default is an auto status line

optional passthrough fields:
  VSCODE_PASSWORD_STORE
  VSCODE_STARTUP_DELAY_SECONDS
  VSCODE_SIDEBAR_DELAY_SECONDS
  VSCODE_NEW_TASK_DELAY_SECONDS
  PROMPT_SEND_DELAY_SECONDS
EOF
  exit 0
fi

if [[ "$#" -gt 1 ]]; then
  echo "error: expected zero or one argument: [zulip_message]"
  exit 1
fi

if ! command -v curl >/dev/null 2>&1; then
  echo "error: curl is not installed or not in PATH"
  exit 1
fi

json_escape() {
  local input="${1:-}"
  input="${input//\\/\\\\}"
  input="${input//\"/\\\"}"
  input="${input//$'\n'/\\n}"
  input="${input//$'\r'/\\r}"
  input="${input//$'\t'/\\t}"
  printf '%s' "$input"
}

add_string_field() {
  local key="$1"
  local value="$2"
  local escaped_value
  escaped_value="$(json_escape "$value")"
  append_json_field "\"$key\":\"$escaped_value\""
}

add_number_field_if_set() {
  local key="$1"
  local value="$2"

  if [[ -z "$value" ]]; then
    return 0
  fi

  if [[ ! "$value" =~ ^[0-9]+([.][0-9]+)?$ ]]; then
    echo "error: $key must be numeric when set (got '$value')"
    exit 1
  fi

  append_json_field "\"$key\":$value"
}

append_json_field() {
  local fragment="$1"
  if (( JSON_FIELD_COUNT > 0 )); then
    JSON_PAYLOAD+=",${fragment}"
  else
    JSON_PAYLOAD+="$fragment"
  fi
  JSON_FIELD_COUNT=$((JSON_FIELD_COUNT + 1))
}

MESSAGE="${1:-$DEFAULT_MESSAGE}"

JSON_PAYLOAD="{"
JSON_FIELD_COUNT=0
add_string_field "zulip_message" "$MESSAGE"
add_string_field "workspace" "$ROOT_DIR"

if [[ -n "${VSCODE_PASSWORD_STORE:-}" ]]; then
  add_string_field "password_store" "$VSCODE_PASSWORD_STORE"
fi
add_number_field_if_set "startup_delay_seconds" "${VSCODE_STARTUP_DELAY_SECONDS:-}"
add_number_field_if_set "sidebar_delay_seconds" "${VSCODE_SIDEBAR_DELAY_SECONDS:-}"
add_number_field_if_set "new_task_delay_seconds" "${VSCODE_NEW_TASK_DELAY_SECONDS:-}"
add_number_field_if_set "prompt_send_delay_seconds" "${PROMPT_SEND_DELAY_SECONDS:-}"
JSON_PAYLOAD+="}"

CURL_ARGS=(
  -sS
  --fail
  -X POST
  "$LOOPER_URL"
  -H
  "Content-Type: application/json"
  --data
  "$JSON_PAYLOAD"
)

if [[ -n "$LOOPER_API_TOKEN" ]]; then
  CURL_ARGS+=(-H "Authorization: Bearer $LOOPER_API_TOKEN")
fi

curl "${CURL_ARGS[@]}"
echo
