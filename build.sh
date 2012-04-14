#!/bin/bash
# Continuous build script
while true
do
    pkill logitext.exe
    reset
    ghc --make -c ClassicalFOLFFI.hs haskell.c && \
        urweb logitext && \
        (./logitext.exe &) && \
        sleep 1 && \
        (curl "http://localhost:8080/main" &> /dev/null)
    inotifywait -e modify $(git ls-files)
done
