#!/bin/bash
# Continuous build script
pkill logitext.exe
while true
do
    reset
    (
        ghc --make -c ClassicalFOLFFI.hs haskell.c && \
        urweb logitext && \
        (./logitext.exe &) && \
        sleep 1 && \
        (curl "http://localhost:8080/main" &> /dev/null)
    ) &
    PID=$!
    inotifywait -e modify $(git ls-files) 2> /dev/null
    kill $PID
done
