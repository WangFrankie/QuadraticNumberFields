# Blueprint Remote Publishing

The QNF Verso blueprint builds to a static site under
`blueprint-verso/_out/site/html-multi/`. This project publishes the
build to two destinations, both driven by the same render:

| Destination | URL | Trigger | Tool |
|---|---|---|---|
| 1Panel site on a VPS | `https://<your-domain>/QuadraticNumberFields/` | local script | [`blueprint-verso/scripts/publish.sh`](../blueprint-verso/scripts/publish.sh) |
| GitHub Pages | `https://<owner>.github.io/QuadraticNumberFields/` | push to `blueprint-verso` or manual | [`.github/workflows/blueprint-pages.yml`](../.github/workflows/blueprint-pages.yml) |

The two routes share the same `ci-pages.sh` render and produce
byte-identical sites; they are independent URLs that can be served at
the same time. Use the VPS route for a custom domain and the GitHub
Pages route as a public, free, version-controlled mirror.

## VPS Route — `publish.sh`

```text
local checkout
└── blueprint-verso/scripts/publish.sh
        │
        │  reads:   .env.local (VPS_SSH_TARGET, VPS_TARGET_DIR, …)
        │  builds:  blueprint-verso/_out/site/html-multi/
        │  pushes:  rsync --delete over ssh
        ▼
VPS (1Panel)
└── /opt/1panel/www/sites/<domain>/QuadraticNumberFields/
        served by 1Panel's nginx at https://<domain>/QuadraticNumberFields/
```

The script contains **no real hosts, paths, users, or keys** — every
real value is read from `.env.local` at the repo root. A template
lives in [`.env.example`](../.env.example); `.env.local` is
git-ignored. The build runs locally so the cheap VPS does not need
`lake`, `mathlib`, or any of the Lean toolchain.

## One-Time Setup

### 1. Configure an SSH alias for the VPS

In `~/.ssh/config` on the machine that runs the deploy:

```sshconfig
Host replace-with-your-alias
    HostName replace-with-vps-ip-or-hostname
    User replace-with-ssh-user
    Port 22
    IdentityFile ~/.ssh/replace-with-key
```

This is the recommended form because it keeps `VPS_SSH_TARGET` in
`.env.local` to a short alias and means the script never has to know
the real host, port, user, or key path.

### 2. Verify the 1Panel target directory is reachable

The script writes into whatever `VPS_TARGET_DIR` points at. The
expected layout is the 1Panel default:

```text
/opt/1panel/www/sites/<your-domain>/
    QuadraticNumberFields/   <- VPS_TARGET_DIR points here
        index.html           <- rendered blueprint
        …
```

The 1Panel site must already be created in the panel and configured
to serve `QuadraticNumberFields/` at the URL you want. The
publishing script does not create sites or edit 1Panel state; it
only writes files.

### 3. Create `.env.local` from the template

```bash
cp .env.example .env.local
$EDITOR .env.local
```

Minimum required values:

```dotenv
VPS_SSH_TARGET=replace-with-your-alias
VPS_TARGET_DIR=/opt/1panel/www/sites/replace-with-domain/QuadraticNumberFields
```

Optional values worth setting for a 1Panel site whose web server
user is not your SSH login user:

```dotenv
VPS_TARGET_OWNER=www-data:www-data   # or 1panel:1panel, depending on panel version
VPS_TARGET_MODE=755
```

### 4. Smoke-test

```bash
DRY_RUN=1 ./blueprint-verso/scripts/publish.sh
```

This runs the full pipeline — including the local `lake build` — but
passes `--dry-run` to `rsync`, so no files are written on the
remote. Check the rsync "would send" / "would delete" lines look
sane.

If the dry-run is clean, run it for real:

```bash
./blueprint-verso/scripts/publish.sh
```

## Day-to-Day Use

| Goal | Command |
|---|---|
| Publish a fresh build | `./blueprint-verso/scripts/publish.sh` |
| Re-render but skip the slow HTML generation, reusing the previous site | `SKIP_RENDER=1 ./blueprint-verso/scripts/publish.sh` |
| Re-publish the previous build without rebuilding | `SKIP_BUILD=1 ./blueprint-verso/scripts/publish.sh` |
| See what would change | `DRY_RUN=1 ./blueprint-verso/scripts/publish.sh` |
| Publish without rebuilding and without writing | `SKIP_BUILD=1 DRY_RUN=1 ./blueprint-verso/scripts/publish.sh` |

The render step (`lake env lean --run QNFBlueprintMain.lean`) is the slow
part of the build: it walks the entire blueprint, regenerates the
dependency graph, and re-emits every HTML page. It is also the only
step whose output is purely the static site under
`_out/site/html-multi/`, so it is safe to skip when that directory
already has a recent build.

The script writes a `QuadraticNumberFields/.last-deploy` sentinel
on success with the git commit hash and UTC timestamp. This makes it
easy to confirm a deploy from the panel's file manager or `ssh`.

## GitHub Pages Route — `blueprint-pages.yml`

The workflow
[`.github/workflows/blueprint-pages.yml`](../.github/workflows/blueprint-pages.yml)
re-renders the blueprint inside a GitHub Actions runner and ships
the result to GitHub Pages.

### Triggers

- **Push to `blueprint-verso`.** Push any commit to that branch and
  the workflow rebuilds + deploys.
- **`workflow_dispatch`.** Manual "rebuild and republish" button
  from the Actions tab.

### One-time setup (already done in this repo)

1. Repository Settings → Pages → Source = **GitHub Actions**. The
   workflow assumes this.
2. The first push to `blueprint-verso` will create the
   `github-pages` environment and a deploy URL like
   `https://<owner>.github.io/QuadraticNumberFields/`. The
   environment URL is exposed in the workflow run summary.

### "Update the branch and republish" flow

The workflow intentionally does **not** merge `dev` into
`blueprint-verso` for you. Doing that on the GitHub web is a
one-click PR merge:

1. On GitHub web, open a PR from `dev` → `blueprint-verso`.
2. Click **Merge pull request**. The merge commit lands on
   `blueprint-verso`.
3. The push to `blueprint-verso` automatically triggers the
   workflow. ~3–5 minutes later, the new build is live on GitHub
   Pages.

The `workflow_dispatch` trigger is for the rare case where you
want to republish the *current* `blueprint-verso` HEAD without
merging in anything new (e.g. flaky run, or a Pages-side cache
glitch).

### Why a dedicated publish branch

`blueprint-verso` is the long-lived publish branch. `dev` is the
day-to-day development branch. The promotion path is

```
dev  ─── merge PR ───►  blueprint-verso  ─── auto workflow ───►  GitHub Pages
                                ▲
                                └── manual: ./blueprint-verso/scripts/publish.sh  ───►  VPS
```

This decouples "what is being worked on" from "what is published":
the Pages site and the 1Panel site are always built from
`blueprint-verso`, never from `dev` or `main` directly.

## Cron / Webhook (VPS route)

The `publish.sh` script is idempotent and exits non-zero on real
failure, so it is safe to run from a cron job:

```cron
*/15 * * * *  cd /path/to/QuadraticNumberFields && ./blueprint-verso/scripts/publish.sh >> /tmp/qnf-publish.log 2>&1
```

A push-triggered workflow via a small webhook receiver (e.g.
`adnanh/webhook`) is also fine: have the receiver run the same
command. The script refuses to act on a dirty working tree, so a
concurrent local edit will not be clobbered.

## Rollback

The script always `rsync --delete`s into the live directory, so the
last good build is overwritten in place. Two ways back:

1. **Re-publish a previous commit:**

   ```bash
   git checkout <known-good-sha>
   ./blueprint-verso/scripts/publish.sh
   git checkout -
   ```

2. **Pin a snapshot directory** (e.g.
   `/opt/1panel/www/sites/<domain>/QuadraticNumberFields-<date>/`)
   and flip the panel site root in 1Panel. The script supports this
   with a one-line env override: `VPS_TARGET_DIR=…/QuadraticNumberFields-<date>`.

## Troubleshooting

| Symptom | Likely cause | Fix |
|---|---|---|
| `ERROR: .env.local not found` | file missing or wrong path | `cp .env.example .env.local` at the repo root |
| `ERROR: VPS_SSH_TARGET is empty` | `.env.local` not sourced correctly | Make sure the variable is uncommented; do not quote it as `""` |
| `Permission denied (publickey)` | SSH alias not in `~/.ssh/config`, or key not loaded | `ssh <alias>` interactively to confirm; `ssh-add ~/.ssh/<key>` if needed |
| `ERROR: chown … failed` (exit 4) | `VPS_TARGET_OWNER` set to a user the SSH login cannot chown to | Either drop the variable, or `sudo` the SSH user into the relevant group on the VPS |
| 1Panel site shows 404 | panel site root is not pointed at the path in `VPS_TARGET_DIR` | In 1Panel, edit the site → document root → match the path |
| 1Panel site shows old content | browser cache, not the deploy | hard-refresh, or check `.last-deploy` on the server |
| `lake: command not found` | elan not on `PATH` for the shell that runs the script | `source ~/.elan/env` once, or add the `.elan/env` line to `~/.bashrc`; or `SKIP_BUILD=1` |
| `expected build output missing index.html` | `ci-pages.sh` exited 0 but wrote elsewhere | Re-run without `SKIP_BUILD=1` and read its output |
