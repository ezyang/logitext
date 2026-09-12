# Building Logitext on autobox

A record of the working setup on `autobox`, built 2026-09-11. Logitext needs a
2012-era toolchain (GHC 7.6, OCaml 4.01, MLton, and a patched Coq), so
everything is built and run inside an Ubuntu 14.04 container; nothing is
installed on the host. `README` describes the original native build — this file
describes what actually runs here.

Served on port 8080 of the build host.

## Layout

Build scaffolding lives outside this repo, in `~/Dev/logitext-deps/`:

    ~/Dev/logitext-deps/
      Dockerfile      the 14.04 toolchain image (tag: logitext-build)
      run.sh          build and/or serve the app in that image
      nginx.conf      static assets at /logitext/, proxy to the app
      coq/            git clone of github.com/ezyang/coq  (PGIP fork)
      urweb/          Ur/Web 2013 source
      urweb-install/  Ur/Web install prefix
      smoketest/      ProofSmoke.hs, end-to-end proof backend test

Both the repo and the scaffolding sit under `~/Dev`, which is bind-mounted into
the container at the same path, so paths are identical inside and out.

## The image

    FROM ubuntu:14.04
    RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
          build-essential git curl ca-certificates inotify-tools nginx-light \
          ocaml-nox camlp5 libgmp-dev \
          mlton libssl-dev libpq-dev libsqlite3-dev automake autoconf libtool \
          ghc libghc-aeson-dev libghc-split-dev libghc-xml-dev libghc-parsec3-dev \
          libghc-attoparsec-dev libghc-quickcheck2-dev libghc-unordered-containers-dev \
          libghc-vector-dev libghc-text-dev libghc-syb-dev libghc-mtl-dev \
          libghc-utf8-string-dev \
        && rm -rf /var/lib/apt/lists/*
    WORKDIR /work

    docker build -t logitext-build ~/Dev/logitext-deps

## Dependencies

Clone the two sources (the Coq fork is a single squashed commit on `trunk`,
`d29ffa5 "PGIP support"` — that is the right revision, there is no `pgip`
branch):

    git clone https://github.com/ezyang/coq   ~/Dev/logitext-deps/coq
    git clone <ur/web 2013 tarball or repo>   ~/Dev/logitext-deps/urweb

Configure once:

    # in coq/
    ./configure -local -coqide no -nodoc -usecamlp5 -no-native-compiler
    # in urweb/
    ./configure --prefix=$HOME/Dev/logitext-deps/urweb-install

**Build them one at a time, with memory caps.** autobox has 40 cores but only
16 GB of RAM, and other services on the box hold roughly half of it:

    docker run --rm --user $(id -u):$(id -g) -e HOME=/tmp \
        --memory=5g --memory-swap=6g \
        -v $HOME/Dev:$HOME/Dev -w $HOME/Dev/logitext-deps/urweb \
        logitext-build bash -c 'make && make install'

    docker run --rm --user $(id -u):$(id -g) -e HOME=/tmp \
        --memory=4g --memory-swap=5g \
        -v $HOME/Dev:$HOME/Dev -w $HOME/Dev/logitext-deps/coq \
        logitext-build bash -c 'make -j4 world'

Do not run these concurrently, and do not raise `-j`. Building Coq at `-j16`
*while* MLton compiled Ur/Web exhausted all 16 GB and rebooted the host. Both
builds are incremental, so a killed build resumes without `make clean`.

## Build and run the app

    ~/Dev/logitext-deps/run.sh build    # compile only
    ~/Dev/logitext-deps/run.sh          # compile, then serve on :8080

`run.sh` compiles the Haskell FFI modules with GHC, runs `urweb logitext`, then
starts nginx plus `logitext.exe -p 8081`. It uses `--network host`, a 4 GB
container memory cap, and `LANG=C.UTF-8`.

Check it:

    curl -s -o /dev/null -w '%{http_code}\n' http://localhost:8080/main
    curl -s -o /dev/null -w '%{http_code}\n' http://localhost:8080/logitext/ffi.js

## Proof backend smoke test

Exercises parsing plus a real Coq refinement without a browser:

    docker exec logitext bash -c '
      export PATH=$HOME/Dev/logitext-deps/coq/bin:$PATH; mkdir -p /tmp/smoke
      cd $HOME/Dev/logitext-deps/smoketest
      ghc -v0 -i$HOME/Dev/logitext -outputdir /tmp/smoke -o /tmp/smoke/smoke ProofSmoke.hs
      cd $HOME/Dev/logitext && /tmp/smoke/smoke "Γ, A |- A"'

Expected: the sequent parses to `hyps = [Γ, A], cons = [A]` and refines OK.
Passing a goal with non-ASCII logic symbols also covers the locale trap below.

## Traps

Each of these produced a confusing failure at least once.

**MLton sizes its GC heap from host RAM and cannot see a cgroup limit.** Both
`mlton` and `urweb` are MLton programs, so inside a memory-capped container
they see all 16 GB, grow past the cap, and get OOM-killed. `urweb logitext`
peaked over 7 GB uncapped; under an explicit cap the same compile fits in
well under 2.5 GB. Hence `urweb @MLton max-heap 2500m -- logitext` in `run.sh`.
The instinct after an OOM is to raise the limit, which here makes it worse.

**The container must run in a UTF-8 locale.** The proof backend writes tactics
to stderr and to coqtop's stdin, and those tactics contain logic symbols like
Γ. Under the default POSIX locale GHC gives those handles ASCII encoding and
any such proof dies with `hPutChar: invalid argument (invalid character)`.
`run.sh` sets `LANG=C.UTF-8` (already present in the image; nothing to
generate).

**Asset URLs must be site-relative.** `js.urp` and `common.ur` used to hardcode
`http://localhost/logitext/...`, which Ur/Web emits verbatim — so a browser on
any other machine fetched them from *its own* localhost, and the page failed
with `tip is not defined` and no styling. They are now `/logitext/...`, which
works from any hostname. Both the `script` directive and `allow url` patterns
accept relative paths.

**`nginx-light` has no uwsgi or scgi modules.** `uwsgi_temp_path` /
`scgi_temp_path` in `nginx.conf` are a fatal `unknown directive`, which kills
nginx while the Ur/Web app keeps answering on :8081 — so the symptom is a
connection refused on :8080 with a healthy-looking container.

**nginx 1.4 has no `-e` flag.** It always logs one non-fatal `[alert]` about
the unwritable compiled-in default error log before it reads `error_log` from
the config. Harmless; do not try to silence it with `-e`.

**The app's entry point is `/main`, not `/Logitext/main`.** `logitext.urp` has
`rewrite all Logitext/*`, which strips the module prefix.

**`urweb -debug` is unusable with this toolchain.** It passes `-g` to GHC 7.6,
which rejects it. Use `@MLton max-heap` plus the phase trace instead if you
need to debug a compile.

**Coq is run with `-boot`, not installed.** `CoqTop.hs` invokes
`coqtop -boot -l ClassicalFOL.v -pgip`, so `ClassicalFOL.v` is loaded from
source at startup and never needs `coqc`. `run.sh` puts
`logitext-deps/coq/bin` on `PATH`.
