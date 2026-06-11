# QuadraticNumberFields Verso Blueprint

This directory is a self-contained [Verso Blueprint](https://github.com/leanprover/verso-blueprint)
package for the `QuadraticNumberFields` project. It is a nested Lake package: it
has its own `lakefile.toml`, `lean-toolchain`, and `.lake/`, and it does **not**
modify the repository's top-level `lakefile.toml`.

## Layout

```text
blueprint-verso/
  lakefile.toml
  lean-toolchain
  QNFBlueprint.lean
  QNFBlueprint/
    Blueprint.lean
    Chapters/
      Overview.lean
      QuadraticCore.lean
      RingOfIntegers.lean
      Discriminant.lean
      IdealsSplitting.lean
      Units.lean
      ClassGroupChecks.lean
      BakerHeegnerStark.lean
      MathlibUpstream.lean
  QNFBlueprintMain.lean
  scripts/
    ci-pages.sh
    serve.sh
    publish.sh
```

## Version pin note

The initial plan suggested `VersoBlueprint` revision `v4.30.0`, but that branch
uses Lean `v4.30.0` while this repository and its mathlib dependency use
`v4.30.0-rc2`. The nested package therefore pins `VersoBlueprint` to commit
`af54e3eedd11e4a7604544712e70d447b6dc55aa`, the upstream compatibility commit
that keeps the `v4.30.0-rc2` toolchain.

## Building

```bash
cd blueprint-verso
lake update
lake exe cache get
lake build QNFBlueprint
lake exe blueprint-gen --output _out/site
```

The generated HTML is written under `_out/site/html-multi/`. Note that the
`lake exe blueprint-gen` path may build the native generator executable on first
use, which can be slow. The CI-equivalent `lake env lean --run` path below avoids
that native executable build. Use the CI-equivalent render path:

```bash
./scripts/ci-pages.sh
```

which runs:

```bash
lake env lean --run QNFBlueprintMain.lean --output _out/site
```

## Local preview

```bash
cd blueprint-verso
lake env lean --run QNFBlueprintMain.lean --output _out/site
cd _out/site/html-multi
python3 -m http.server 8000
```

or equivalently:

```bash
cd blueprint-verso
./scripts/serve.sh
```

Then open <http://localhost:8000/>.

## Review checklist

- Every `complete` node links to a Lean declaration when a declaration already
  exists.
- Every future node is tagged `future` or `external-assumption`.
- No theorem is marked `complete` unless the Lean declaration exists and is
  proved.
- No project-only theorem is described as a mathlib theorem.
- Baker--Heegner--Stark material is explicitly conditional at this stage.

## Publishing

The build artifact in `_out/site/html-multi/` is a static site. The project
publishes the same render to two destinations:

| Destination | URL | Trigger | Tool |
|---|---|---|---|
| 1Panel VPS site | `https://<your-domain>/QuadraticNumberFields/` | local script | [`scripts/publish.sh`](scripts/publish.sh) |
| GitHub Pages | `https://<owner>.github.io/QuadraticNumberFields/` | push to `blueprint-verso` or manual | [`.github/workflows/blueprint-pages.yml`](../.github/workflows/blueprint-pages.yml) |

Full one-time setup, branch model (`dev` → `blueprint-verso` → Pages),
rollback, and the `SKIP_RENDER` / `SKIP_BUILD` / `DRY_RUN` flags are
in [`docs/blueprint-vps-deploy.md`](../docs/blueprint-vps-deploy.md).

```bash
# VPS route
cp .env.example .env.local
$EDITOR .env.local          # fill in VPS_SSH_TARGET and VPS_TARGET_DIR
./blueprint-verso/scripts/publish.sh

# GitHub Pages route: nothing to do — push to blueprint-verso, or click
# "Run workflow" on .github/workflows/blueprint-pages.yml
```
