#!/usr/bin/env bash
#
# Build the QNF Verso blueprint locally and publish it to a remote
# 1Panel-managed site directory over SSH. All real values come from
# .env.local at the repo root; this script contains no real hosts,
# paths, users, or keys. See .env.example for the variable list.
#
# Required .env.local variables:
#   VPS_SSH_TARGET       rsync-style target, e.g. an alias from
#                        ~/.ssh/config or "user@host".
#   VPS_TARGET_DIR       remote directory that should hold the built
#                        site (an existing 1Panel site folder).
#
# Optional .env.local variables:
#   VPS_SSH_OPTIONS      extra `ssh` options, e.g. "-p 2222 -i ~/.ssh/id_ed25519".
#   VPS_TARGET_OWNER     "user:group" passed to a post-publish chown
#                        (only needed if the SSH login is not the
#                        1Panel web-server user).
#   VPS_TARGET_MODE      chmod mode applied to directories after the
#                        publish, default 755.
#   SKIP_RENDER          "1" to skip the slow Verso HTML render. The
#                        existing _out/site/html-multi/ is reused.
#                        `lake build QNFBlueprint` still runs (fast if
#                        the .olean files are up to date).
#   SKIP_BUILD           "1" to skip the local build step and publish
#                        whatever is already under _out/site/html-multi.
#                        Overrides SKIP_RENDER.
#   DRY_RUN              "1" to rsync --dry-run only; nothing is
#                        written on the remote.
#
# Exit codes:
#   0  success
#   1  configuration / environment error
#   2  local build failed
#   3  remote publish (rsync) failed
#   4  post-publish chown/chmod failed

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
ENV_FILE="$REPO_DIR/.env.local"
ENV_EXAMPLE="$REPO_DIR/.env.example"

log()  { printf '[%s] %s\n' "$(date -u +%FT%TZ)" "$*"; }
die()  { log "ERROR: $*"; exit 1; }
warn() { log "WARN: $*"; }

# --- configuration -------------------------------------------------------

[ -f "$ENV_FILE" ]    || die ".env.local not found at $ENV_FILE (copy $ENV_EXAMPLE to .env.local and fill in real values)"
[ -r "$ENV_FILE" ]    || die ".env.local exists but is not readable"
[ -f "$ENV_EXAMPLE" ] || warn ".env.example missing at $ENV_EXAMPLE (template drift)"

# Source the env file in `set -a` mode so every variable it defines
# is auto-exported to the commands we run below.
set -a
# shellcheck disable=SC1090
. "$ENV_FILE"
set +a

[ -n "${VPS_SSH_TARGET:-}" ] || die "VPS_SSH_TARGET is empty in .env.local"
[ -n "${VPS_TARGET_DIR:-}"  ] || die "VPS_TARGET_DIR is empty in .env.local"

VPS_SSH_OPTIONS="${VPS_SSH_OPTIONS:-}"
VPS_TARGET_OWNER="${VPS_TARGET_OWNER:-}"
VPS_TARGET_MODE="${VPS_TARGET_MODE:-755}"
SKIP_BUILD="${SKIP_BUILD:-}"
DRY_RUN="${DRY_RUN:-}"

# Sanity check on the target dir value: refuse to run if it looks like
# the script accidentally inherited a shell word.
case "$VPS_TARGET_DIR" in
  *' '*|*';'*|*'$'*) die "VPS_TARGET_DIR contains unsafe characters; quote it in .env.local" ;;
esac

# --- tooling preflight ---------------------------------------------------

command -v rsync >/dev/null 2>&1 || die "rsync not on PATH"
command -v ssh   >/dev/null 2>&1 || die "ssh not on PATH"
command -v git   >/dev/null 2>&1 || die "git not on PATH"

# `lake` is only required when we are about to run the build.
if [ -z "$SKIP_BUILD" ]; then
  command -v lake >/dev/null 2>&1 || die "lake not on PATH (install elan + activate, or set SKIP_BUILD=1)"
fi

# --- build ---------------------------------------------------------------

if [ -n "$SKIP_BUILD" ]; then
  log "SKIP_BUILD=1, reusing existing _out/site/html-multi"
else
  cd "$REPO_DIR/blueprint-verso"
  log "rendering blueprint (ci-pages.sh)"
  if ! ./scripts/ci-pages.sh; then
    log "build failed"
    exit 2
  fi
fi

LOCAL_BUILD="$REPO_DIR/blueprint-verso/_out/site/html-multi"
[ -d "$LOCAL_BUILD" ]      || die "expected build output at $LOCAL_BUILD (ci-pages.sh did not produce it)"
[ -f "$LOCAL_BUILD/index.html" ] || die "build output missing index.html"

# --- publish -------------------------------------------------------------

REMOTE="${VPS_SSH_TARGET}:${VPS_TARGET_DIR}/"
RSYNC_FLAGS=(-a --delete -e "ssh ${VPS_SSH_OPTIONS}")
[ -n "$DRY_RUN" ] && RSYNC_FLAGS+=(--dry-run)

log "rsync $LOCAL_BUILD/ -> $REMOTE"
if ! rsync "${RSYNC_FLAGS[@]}" "$LOCAL_BUILD/" "$REMOTE"; then
  log "rsync failed"
  exit 3
fi

# --- post-publish --------------------------------------------------------

# Optional ownership / permission fix for 1Panel: only run if explicitly
# configured. The SSH login is often not the 1Panel web-server user.
if [ -z "$DRY_RUN" ] && [ -n "$VPS_TARGET_OWNER" ]; then
  log "chown -R $VPS_TARGET_OWNER on $VPS_TARGET_DIR"
  if ! ssh $VPS_SSH_OPTIONS "$VPS_SSH_TARGET" \
       "chown -R $VPS_TARGET_OWNER '$VPS_TARGET_DIR' && \
        find '$VPS_TARGET_DIR' -type d -exec chmod $VPS_TARGET_MODE {} +"; then
    log "post-publish chown/chmod failed"
    exit 4
  fi
fi

# Mark a sentinel file with the last successful deploy.
if [ -z "$DRY_RUN" ]; then
  commit="$(git -C "$REPO_DIR" rev-parse --short HEAD 2>/dev/null || echo unknown)"
  if printf 'commit=%s\npublished=%s\n' "$commit" "$(date -u +%FT%TZ)" \
       | ssh $VPS_SSH_OPTIONS "$VPS_SSH_TARGET" \
           "cat > '$VPS_TARGET_DIR/.last-deploy'"; then
    log "deploy complete (commit $commit) -> $REMOTE"
  else
    warn "deploy reached the server but .last-deploy marker could not be written (non-fatal)"
  fi
else
  log "DRY_RUN=1, nothing was written remotely"
fi
